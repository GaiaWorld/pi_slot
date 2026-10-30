//! Deterministic interleavings on the actual shell -> inner protocol paths.
use super::*;
use std::cell::{Cell, RefCell};
#[cfg(feature = "rc")]
use std::rc::Rc as Shared;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
use std::sync::Arc;
#[cfg(not(feature = "rc"))]
use std::sync::Arc as Shared;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Stage {
    ClaimBeforeCas,
    ClaimCasFailed,
    PopHead,
    PopLink,
    PopCasFailed,
    RemoveMoved,
    RemoveFree,
    RemoveLinked,
    LenBetweenReads,
}
type Hook = Box<dyn FnMut(Stage, u64)>;
thread_local! {
    static HOOK: RefCell<Option<Hook>> = RefCell::new(None);
    static FAILURE: RefCell<Option<Box<dyn std::any::Any + Send>>> = RefCell::new(None);
    static SECONDARY_FAILURES: Cell<usize> = const { Cell::new(0) };
    static KEY_CALLS: Cell<usize> = const { Cell::new(0) };
}

// Remove the callback before invoking it: same-thread rc reentry must not fire
// the outer operation's hook. Catch and defer panic so a moved-out LIVE slot
// can never unwind into map Drop before FREE/chain/count restoration.
pub(super) fn pause(stage: Stage, value: u64) {
    let hook = HOOK.with(|cell| cell.borrow_mut().take());
    if let Some(mut hook) = hook {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| hook(stage, value)));
        if let Err(payload) = result {
            FAILURE.with(|cell| {
                if cell.borrow().is_none() {
                    *cell.borrow_mut() = Some(payload);
                } else {
                    SECONDARY_FAILURES.with(|count| count.set(count.get() + 1));
                    // A panic_any payload can have a panicking destructor.
                    // Never drop a secondary payload in a moved-out LIVE slot
                    // window: retain the first failure and intentionally leak
                    // later payloads, just like the map's final-drop strategy.
                    std::mem::forget(payload);
                }
            });
        }
        HOOK.with(|cell| *cell.borrow_mut() = Some(hook));
    }
}
struct Installed;
impl Installed {
    fn new(hook: Hook) -> Self {
        HOOK.with(|cell| assert!(cell.borrow_mut().replace(hook).is_none()));
        SECONDARY_FAILURES.with(|count| count.set(0));
        Self
    }
    fn finish(self) {
        let failure = FAILURE.with(|cell| cell.borrow_mut().take());
        drop(self);
        if let Some(payload) = failure {
            std::panic::resume_unwind(payload);
        }
    }
}
impl Drop for Installed {
    fn drop(&mut self) {
        HOOK.with(|cell| {
            cell.borrow_mut().take();
        });
        FAILURE.with(|cell| {
            if let Some(payload) = cell.borrow_mut().take() {
                // Cleanup may itself be running during unwind. Do not execute
                // an arbitrary payload destructor here; finish takes ownership
                // of the first payload before invoking this cleanup.
                std::mem::forget(payload);
            }
        });
        SECONDARY_FAILURES.with(|count| count.set(0));
    }
}

#[cfg(not(feature = "rc"))]
fn interleave(operation: impl FnOnce() + Send, mut observe: impl FnMut(Stage, u64) + 'static) {
    use std::sync::mpsc;
    use std::time::Duration;
    let (events_tx, events_rx) = mpsc::channel();
    let (resume_tx, resume_rx) = mpsc::channel();
    std::thread::scope(|scope| {
        let worker = scope.spawn(move || {
            let installed = Installed::new(Box::new(move |stage, value| {
                events_tx.send((stage, value)).expect("observer alive");
                resume_rx
                    .recv_timeout(Duration::from_secs(5))
                    .expect("observer resume timeout");
            }));
            operation();
            installed.finish();
        });
        loop {
            match events_rx.recv_timeout(Duration::from_secs(10)) {
                Ok((stage, value)) => {
                    observe(stage, value);
                    resume_tx.send(()).expect("worker alive");
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
                Err(mpsc::RecvTimeoutError::Timeout) => panic!("protocol event timeout"),
            }
        }
        worker.join().expect("protocol worker succeeded");
    });
}
#[cfg(feature = "rc")]
fn interleave(operation: impl FnOnce(), observe: impl FnMut(Stage, u64) + 'static) {
    let installed = Installed::new(Box::new(observe));
    operation();
    installed.finish();
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct CountingKey(KeyData);
impl From<KeyData> for CountingKey {
    fn from(data: KeyData) -> Self {
        KEY_CALLS.with(|count| count.set(count.get() + 1));
        Self(data)
    }
}
impl pi_null::Null for CountingKey {
    fn null() -> Self {
        Self(KeyData::new(u32::MAX, 0))
    }
    fn is_null(&self) -> bool {
        self.0.index() == u32::MAX
    }
}
impl Key for CountingKey {
    fn with(index: usize) -> Self {
        Self::from(KeyData::new(index as u32, 0))
    }
    fn data(&self) -> KeyData {
        KEY_CALLS.with(|count| count.set(count.get() + 1));
        self.0
    }
    fn index(&self) -> usize {
        self.0.index() as usize
    }
}

fn claim_race(change: u8) {
    let map = Shared::new(SlotMap::<DefaultKey, u64, 3>::new());
    let key = map.insert(41);
    let data = key.data();
    let identity = KeyData::new(data.index(), data.version() & !7);
    let expected_error = match change {
        0 => ClaimMetadataError::Claimed,
        1 => ClaimMetadataError::BitsMismatch { actual_bits: 2 },
        _ => ClaimMetadataError::Stale,
    };
    let phases = Shared::new(RefCell::new(Vec::new()));
    // RefCell is deliberately only used by the observer, never sent to worker.
    let seen = phases.clone();
    let observed_map = map.clone();
    let worker_map = map.clone();
    interleave(
        move || {
            assert!(
                matches!(worker_map.claim_metadata(identity, 0, 4), Err(e) if e == expected_error)
            );
        },
        move |stage, actual| {
            seen.borrow_mut().push(stage);
            if stage == Stage::ClaimBeforeCas {
                match change {
                    0 => {
                        let token = observed_map.claim_metadata(identity, 0, 4).unwrap();
                        // Keep CLAIMED without creating any T reference. The map
                        // still owns initialized T and final Drop cleans it up.
                        std::mem::forget(token);
                    }
                    1 => {
                        observed_map.compare_exchange_bits(key, 0, 2).unwrap();
                    }
                    _ => {
                        let token = observed_map.claim_metadata(identity, 0, 4).unwrap();
                        // SAFETY: same map, unique token, no T references have
                        // ever been constructed. Returned ownership is plain u64.
                        let (value, _) = unsafe { token.remove(&observed_map) };
                        assert_eq!(value, 41);
                        observed_map.insert(99);
                    }
                }
            } else if stage == Stage::ClaimCasFailed {
                let slot = observed_map.slots.get(data.index() as usize).unwrap();
                assert_eq!(actual as u32, slot.version.load(Ordering::Acquire));
            } else {
                panic!("unexpected claim phase: {stage:?}");
            }
        },
    );
    assert_eq!(
        *phases.borrow(),
        [Stage::ClaimBeforeCas, Stage::ClaimCasFailed]
    );
    let slot = map.slots.get(data.index() as usize).unwrap();
    let actual = slot.version.load(Ordering::Acquire);
    match change {
        0 => assert_eq!(actual, identity.version() | 4),
        1 => assert_eq!(actual, identity.version() | 2),
        _ => assert_ne!(actual & !7, identity.version()),
    }
}
#[test]
fn claim_cas_failure_reports_actual_claimed_without_retry() {
    claim_race(0);
}
#[test]
fn claim_cas_failure_reports_actual_bits_without_retry() {
    claim_race(1);
}
#[test]
fn claim_cas_failure_reports_actual_next_generation_without_retry() {
    claim_race(2);
}

#[test]
fn late_pop_reads_live_arbitrary_link_then_rejects_old_head() {
    for arbitrary in [u64::MAX, 0xfeed_beef_ffff_fffe] {
        let mut initial = SlotMap::<DefaultKey, u64, 3>::new();
        let old_key = initial.insert(7);
        assert_eq!(initial.remove(old_key), Some(7));
        let map = Shared::new(initial);
        let old_head = map.free_head.load(Ordering::Acquire);
        let seen = Shared::new(RefCell::new(Vec::new()));
        let phases = seen.clone();
        let observer = map.clone();
        let worker = map.clone();
        interleave(
            move || assert_eq!(worker.pop_free(), None),
            move |stage, value| {
                phases.borrow_mut().push(stage);
                match stage {
                    Stage::PopHead => {
                        assert_eq!(value, old_head);
                        let key = observer.insert_with_link(88, arbitrary);
                        assert_eq!(key.data().index(), old_key.data().index());
                        assert_ne!(key.data().version(), old_key.data().version());
                        assert_eq!(observer.free_head.load(Ordering::Acquire), NULL);
                    }
                    Stage::PopLink => assert_eq!(value, arbitrary),
                    Stage::PopCasFailed => assert_eq!(value, old_head),
                    _ => panic!("unexpected pop phase: {stage:?}"),
                }
            },
        );
        assert_eq!(
            *seen.borrow(),
            [Stage::PopHead, Stage::PopLink, Stage::PopCasFailed]
        );
        assert_eq!(map.free_head.load(Ordering::Acquire), NULL);
        assert_eq!(map.len(), 1);
        // Metadata and link observations above never create a T reference.
    }
}

struct Payload {
    id: u64,
    drops: Arc<AtomicUsize>,
}

#[test]
fn len_read_window_observes_old_free_then_new_alloc_without_underflow() {
    let map = Shared::new(SlotMap::<DefaultKey, (), 3>::new());
    let observer = map.clone();
    let worker = map.clone();
    let pauses = Shared::new(Cell::new(0));
    let seen = pauses.clone();
    interleave(
        move || {
            // Initially both counters are zero. The observer completes an
            // insert+remove between these two loads: the correct read pair is
            // free=0, alloc=1. This intentionally is not a snapshot length.
            assert_eq!(worker.len(), 1, "len must use old free and new alloc");
        },
        move |stage, value| {
            assert_eq!(stage, Stage::LenBetweenReads);
            assert_eq!(value, 0);
            seen.set(seen.get() + 1);
            assert_eq!(observer.alloc_count(), 0);
            assert_eq!(observer.free_count(), 0);
            let data = observer.insert(()).data();
            let token = observer.claim_metadata(data, 0, 4).unwrap();
            // SAFETY: same map, unique claimed token, and no T reference was
            // created. Removal consumes the token and returns owned unit.
            let (_, link) = unsafe { token.remove(&observer) };
            assert_eq!(link, 0);
            assert_eq!(observer.alloc_count(), 1);
            assert_eq!(observer.free_count(), 1);
        },
    );
    assert_eq!(pauses.get(), 1);
    assert_eq!(map.len(), 0);
    // Mutation sensitivity: alloc=0 -> pause -> free=1 produces usize::MAX.
    // If a mutation keeps the hook literally after free instead, both loads
    // happen before the observer and yield 0. Either result fails exact len=1.
}

struct PanickingSecondaryPayload(Arc<AtomicUsize>);
impl Drop for PanickingSecondaryPayload {
    fn drop(&mut self) {
        self.0.fetch_add(1, AtomicOrdering::SeqCst);
        panic!("secondary payload destructor must not execute");
    }
}
impl Drop for Payload {
    fn drop(&mut self) {
        self.drops.fetch_add(1, AtomicOrdering::SeqCst);
    }
}

#[test]
fn hook_panic_is_deferred_until_removal_restores_storage_invariants() {
    let drops = Arc::new(AtomicUsize::new(0));
    let secondary_drops = Arc::new(AtomicUsize::new(0));
    let secondary_for_hook = secondary_drops.clone();
    let map = SlotMap::<DefaultKey, Payload, 3>::new();
    let data = map
        .insert(Payload {
            id: 9,
            drops: drops.clone(),
        })
        .data();
    let token = map.claim_metadata(data, 0, 4).unwrap();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let installed = Installed::new(Box::new(move |stage, _| {
            if stage == Stage::RemoveMoved {
                panic!("injected observer failure");
            } else if matches!(stage, Stage::RemoveFree | Stage::RemoveLinked) {
                std::panic::panic_any(PanickingSecondaryPayload(secondary_for_hook.clone()));
            }
        }));
        // SAFETY: token belongs to map, remains unique, and no T reference
        // exists. A test observer panic is caught inside pause, not here.
        let (value, _) = unsafe { token.remove(&map) };
        assert_eq!(map.free_count(), 1);
        assert_eq!(map.len(), 0);
        assert_eq!(SECONDARY_FAILURES.with(Cell::get), 2);
        assert_eq!(secondary_drops.load(AtomicOrdering::SeqCst), 0);
        drop(value);
        installed.finish();
    }));
    let payload = result.expect_err("first observer panic must be propagated");
    assert_eq!(
        payload.downcast_ref::<&'static str>(),
        Some(&"injected observer failure")
    );
    assert_eq!(secondary_drops.load(AtomicOrdering::SeqCst), 0);
    assert_eq!(map.pop_free(), Some(data.index()));
    assert_eq!(map.pop_free(), None);
    drop(map);
    assert_eq!(drops.load(AtomicOrdering::SeqCst), 1);
}

#[test]
fn claimed_remove_orders_move_free_link_count_without_callbacks_or_drops() {
    let drops = Arc::new(AtomicUsize::new(0));
    let map = Shared::new(SlotMap::<CountingKey, Payload, 3>::new());
    let key = map.insert_with_link(
        Payload {
            id: 57,
            drops: drops.clone(),
        },
        0xabc,
    );
    let data = key.0;
    let identity = KeyData::new(data.index(), data.version() & !7);
    let seen = Shared::new(RefCell::new(Vec::new()));
    let phases = seen.clone();
    let observer = map.clone();
    let worker = map.clone();
    let observer_drops = drops.clone();
    let worker_drops = drops.clone();
    interleave(
        move || {
            let token = worker.claim_metadata(identity, 0, 4).unwrap();
            KEY_CALLS.with(|count| count.set(0));
            // SAFETY: same map, successful unique token, and no T references
            // were constructed. The operation returns the sole payload owner.
            let (value, link) = unsafe { token.remove(&worker) };
            assert_eq!(KEY_CALLS.with(Cell::get), 0);
            assert_eq!(value.id, 57);
            assert_eq!(link, 0xabc);
            assert_eq!(worker.free_count(), 1);
            assert_eq!(worker_drops.load(AtomicOrdering::SeqCst), 0);
            drop(value);
            assert_eq!(worker_drops.load(AtomicOrdering::SeqCst), 1);
        },
        move |stage, _| {
            // Claim events precede removal; removal events occur after ptr::read
            // and never expose the moved-out slot as a T reference.
            if stage == Stage::ClaimBeforeCas {
                return;
            }
            phases.borrow_mut().push(stage);
            assert_eq!(observer_drops.load(AtomicOrdering::SeqCst), 0);
            assert_eq!(observer.free_count(), 0);
            let slot = observer.slots.get(data.index() as usize).unwrap();
            let version = slot.version.load(Ordering::Acquire);
            match stage {
                Stage::RemoveMoved => {
                    assert_eq!(version, identity.version() | 4);
                    assert!(matches!(
                        observer.claim_metadata(identity, 0, 4),
                        Err(ClaimMetadataError::Claimed)
                    ));
                    assert_eq!(observer.free_head.load(Ordering::Acquire), NULL);
                }
                Stage::RemoveFree => {
                    assert!(!live::<3>(version));
                    assert!(matches!(
                        observer.claim_metadata(identity, 0, 4),
                        Err(ClaimMetadataError::Stale)
                    ));
                    assert_eq!(observer.free_head.load(Ordering::Acquire), NULL);
                    assert_eq!(observer.pop_free(), None);
                }
                Stage::RemoveLinked => {
                    assert!(!live::<3>(version));
                    assert!(matches!(
                        observer.claim_metadata(identity, 0, 4),
                        Err(ClaimMetadataError::Stale)
                    ));
                    assert_eq!(
                        observer.free_head.load(Ordering::Acquire),
                        encode(data.index(), version)
                    );
                    assert_eq!(slot.link.load(Ordering::Relaxed), NULL);
                }
                _ => panic!("unexpected removal phase: {stage:?}"),
            }
        },
    );
    assert_eq!(
        *seen.borrow(),
        [Stage::RemoveMoved, Stage::RemoveFree, Stage::RemoveLinked]
    );
    assert_eq!(map.free_count(), 1);
    assert_eq!(map.pop_free(), Some(data.index()));
    assert_eq!(map.pop_free(), None); // exactly one chain entry, no self-cycle
    assert_eq!(map.len(), 0);
    drop(map);
    assert_eq!(drops.load(AtomicOrdering::SeqCst), 1);
}
