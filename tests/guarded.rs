#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use pi_slot::{DefaultKey, GuardedAccessError as Error, GuardedSlotMap, Key, KeyData};
use std::cell::{Cell, RefCell};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

fn error<T>(result: Result<T, Error>, expected: Error) {
    match result {
        Err(actual) => assert_eq!(actual, expected),
        Ok(_) => panic!("unexpected success; expected {expected:?}"),
    }
}

#[test]
fn priority_claimed_cas_and_explicit_expected_bits() {
    let map = GuardedSlotMap::<DefaultKey, String>::with_capacity(2);
    assert!(map.is_empty());
    let key = map.insert_with_link("value".into(), 81, 1);
    let noisy = KeyData::new(key.data().index(), key.data().version() | 7).into();
    let mut guard = map.try_get(noisy, 1).unwrap();
    assert_eq!(guard.key(), key);
    guard.set_bits(3);
    for expected in [0, 1, 3] {
        error(map.try_get(key, expected), Error::Busy);
        error(map.try_remove(key, expected), Error::Busy);
        error(map.compare_exchange_bits(key, expected, 0), Error::Busy);
    }
    for (expected, desired) in [(4, 0), (1, 4)] {
        assert!(catch_unwind(AssertUnwindSafe(
            || map.compare_exchange_bits(key, expected, desired)
        ))
        .is_err());
        error(map.try_get(key, 1), Error::Busy);
    }
    assert!(catch_unwind(AssertUnwindSafe(|| map.try_get(key, 4))).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| map.try_remove(key, 4))).is_err());
    assert_eq!(
        (
            guard.value().as_str(),
            guard.link(),
            guard.original_bits(),
            guard.bits()
        ),
        ("value", 81, 1, 3)
    );
    drop(guard);
    error(
        map.try_get(noisy, 1),
        Error::BitsMismatch { actual_bits: 3 },
    );
    error(
        map.try_remove(noisy, 1),
        Error::BitsMismatch { actual_bits: 3 },
    );
    error(
        map.compare_exchange_bits(noisy, 1, 0),
        Error::BitsMismatch { actual_bits: 3 },
    );
    assert_eq!(map.compare_exchange_bits(noisy, 3, 0), Ok(key));
    assert_eq!(map.try_get(key, 0).unwrap().original_bits(), 0);
    assert_eq!(map.try_remove(key, 0).unwrap(), ("value".into(), 81));
    let next = map.insert("next".into(), 1);
    assert_eq!(next.data().index(), key.data().index());
    assert_ne!(next, key);
    let held = map.try_get(next, 1).unwrap();
    error(map.try_get(key, 0), Error::Stale);
    error(map.try_remove(key, 0), Error::Stale);
    error(map.compare_exchange_bits(key, 0, 0), Error::Stale);
    for invalid in [
        DefaultKey::default(),
        KeyData::new(u32::MAX, key.data().version()).into(),
    ] {
        error(map.try_get(invalid, 0), Error::Stale);
        error(map.try_remove(invalid, 0), Error::Stale);
        error(map.compare_exchange_bits(invalid, 0, 0), Error::Stale);
    }
    drop(held);
}

#[test]
fn update_once_or_zero_and_unwind_publishes_last_legal_pending() {
    let map = GuardedSlotMap::<DefaultKey, String>::new();
    let key = map.insert("a".into(), 1);
    let calls = Cell::new(0);
    let held = map.try_get(key, 1).unwrap();
    error(
        map.try_update(key, 0, |_| calls.set(calls.get() + 1)),
        Error::Busy,
    );
    drop(held);
    error(
        map.try_update(key, 0, |_| calls.set(calls.get() + 1)),
        Error::BitsMismatch { actual_bits: 1 },
    );
    error(
        map.try_update(DefaultKey::default(), 1, |_| calls.set(calls.get() + 1)),
        Error::Stale,
    );
    assert_eq!(calls.get(), 0);
    assert_eq!(
        map.try_update(key, 1, |g| {
            calls.set(calls.get() + 1);
            g.value().len()
        }),
        Ok(1)
    );
    assert_eq!(calls.get(), 1);
    assert!(
        catch_unwind(AssertUnwindSafe(|| map.try_update(key, 1, |g| {
            calls.set(calls.get() + 1);
            g.value_mut().push('!');
            g.set_link(92);
            g.set_bits(2);
            assert!(catch_unwind(AssertUnwindSafe(|| g.set_bits(4))).is_err());
            assert_eq!((g.original_bits(), g.bits()), (1, 2));
            error(map.try_get(key, 2), Error::Busy);
            panic!("update unwind");
        })))
        .is_err()
    );
    assert_eq!(calls.get(), 2);
    let g = map.try_get(key, 2).unwrap();
    assert_eq!(
        (g.value().as_str(), g.link(), g.bits(), g.original_bits()),
        ("a!", 92, 2, 2)
    );
}

#[derive(Debug)]
struct Tracked {
    id: u32,
    drops: Arc<AtomicUsize>,
}
impl Drop for Tracked {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}
fn tracked(id: u32, drops: &Arc<AtomicUsize>) -> Tracked {
    Tracked {
        id,
        drops: drops.clone(),
    }
}

#[test]
fn consuming_removal_transfers_ownership_and_free_is_reused_once() {
    for direct in [true, false] {
        let drops = Arc::new(AtomicUsize::new(0));
        let map = GuardedSlotMap::<DefaultKey, Tracked>::new();
        let key = map.insert_with_link(tracked(7, &drops), u64::MAX, 3);
        let (value, link) = if direct {
            map.try_get(key, 3).unwrap().remove()
        } else {
            map.try_remove(key, 3).unwrap()
        };
        assert_eq!((value.id, link, map.len()), (7, u64::MAX, 0));
        assert_eq!(drops.load(Ordering::SeqCst), 0);
        error(map.try_remove(key, 3), Error::Stale);
        let next = map.insert_with_link(tracked(8, &drops), 19, 0);
        assert_eq!(next.data().index(), key.data().index());
        let held = map.try_get(next, 0).unwrap();
        let extra = map.insert(tracked(9, &drops), 2);
        assert_ne!(extra.data().index(), next.data().index());
        error(map.try_get(next, 0), Error::Busy);
        assert_eq!((held.value().id, held.link(), held.bits()), (8, 19, 0));
        drop(value);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        drop(held);
        drop(map);
        assert_eq!(drops.load(Ordering::SeqCst), 3);
    }
}

#[test]
fn reuse_initializes_all_bits_links_and_self_key_before_publication() {
    let map = GuardedSlotMap::<DefaultKey, (DefaultKey, u32)>::new();
    let first = map.insert_with_link((DefaultKey::default(), 1), u64::MAX, 3);
    map.try_remove(first, 3).unwrap();
    let calls = Cell::new(0);
    let next = map.insert_with_key(0, |key| {
        calls.set(calls.get() + 1);
        assert_eq!(key.data().version() & 7, 0);
        assert_eq!(map.len(), 0);
        error(map.try_get(key, 0), Error::Stale);
        (key, 2)
    });
    assert_eq!(calls.get(), 1);
    assert_eq!(first.data().index(), next.data().index());
    let g = map.try_get(next, 0).unwrap();
    assert_eq!((*g.value(), g.link(), g.bits()), ((next, 2), 0, 0));
    g.remove();
    let last = map.insert_with_link((next, 3), 62, 3);
    let g = map.try_get(last, 3).unwrap();
    assert_eq!(
        (*g.value(), g.link(), g.original_bits()),
        ((next, 3), 62, 3)
    );
}

#[test]
fn constructor_panic_consumes_identity_without_publication() {
    let map = GuardedSlotMap::<DefaultKey, DefaultKey>::new();
    let candidate = Cell::new(None);
    let calls = Cell::new(0);
    assert!(
        catch_unwind(AssertUnwindSafe(|| map.insert_with_key(3, |key| {
            calls.set(calls.get() + 1);
            candidate.set(Some(key));
            error(map.try_get(key, 3), Error::Stale);
            panic!("constructor");
        })))
        .is_err()
    );
    let rejected = candidate.get().unwrap();
    assert_eq!((calls.get(), map.len(), map.is_empty()), (1, 0, true));
    error(map.try_get(rejected, 3), Error::Stale);
    let next = map.insert_with_key(1, |key| key);
    assert_eq!(next.data().index(), rejected.data().index());
    assert_ne!(next, rejected);
    assert_eq!(*map.try_get(next, 1).unwrap().value(), next);
}

#[test]
fn forgotten_guard_is_busy_until_map_destroys_live_value_once() {
    let drops = Arc::new(AtomicUsize::new(0));
    let map = GuardedSlotMap::<DefaultKey, Tracked>::new();
    let key = map.insert(tracked(1, &drops), 1);
    let mut g = map.try_get(key, 1).unwrap();
    g.set_bits(2);
    std::mem::forget(g);
    error(map.try_get(key, 0), Error::Busy);
    error(map.try_remove(key, 1), Error::Busy);
    error(map.compare_exchange_bits(key, 1, 0), Error::Busy);
    assert_eq!(map.len(), 1);
    let next = map.insert(tracked(2, &drops), 0);
    assert_ne!(key.data().index(), next.data().index());
    assert_eq!(map.len(), 2);
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    drop(map);
    assert_eq!(drops.load(Ordering::SeqCst), 2);
}

#[test]
fn zero_and_thirty_bit_boundaries_and_documented_generation_wrap() {
    let map = GuardedSlotMap::<DefaultKey, u32, 0>::new();
    let key = map.insert_with_link(7, 88, 0);
    let mut g = map.try_get(key, 0).unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| g.set_bits(1))).is_err());
    assert_eq!((g.bits(), g.original_bits()), (0, 0));
    error(map.try_get(key, 0), Error::Busy);
    error(map.try_remove(key, 0), Error::Busy);
    error(map.compare_exchange_bits(key, 0, 0), Error::Busy);
    for (a, b) in [(1, 0), (0, 1)] {
        assert!(catch_unwind(AssertUnwindSafe(|| map.compare_exchange_bits(key, a, b))).is_err());
    }
    drop(g);
    assert!(catch_unwind(AssertUnwindSafe(|| map.insert(8, 1))).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| map.insert_with_link(8, 9, 1))).is_err());
    let constructors = Cell::new(0);
    assert!(
        catch_unwind(AssertUnwindSafe(|| map.insert_with_key(1, |_| {
            constructors.set(constructors.get() + 1);
            8
        })))
        .is_err()
    );
    assert_eq!(constructors.get(), 0);
    assert_eq!(map.len(), 1);
    assert_eq!(map.compare_exchange_bits(key, 0, 0), Ok(key));
    assert_eq!(map.try_remove(key, 0).unwrap(), (7, 88));
    let next = map.insert(9, 0);
    assert_ne!(next, key);
    error(map.try_get(key, 0), Error::Stale);

    const MAX: u32 = (1 << 30) - 1;
    let map = GuardedSlotMap::<DefaultKey, u32, 30>::new();
    let key = map.insert_with_link(1, u64::MAX, MAX);
    let mut g = map.try_get(key, MAX).unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| g.set_bits(1 << 30))).is_err());
    assert_eq!(g.bits(), MAX);
    g.remove();
    let repeated = map.insert_with_link(2, 17, 0);
    assert_eq!(repeated, key); // N=30 has no generation bits: documented ABA boundary.
    let g = map.try_get(key, 0).unwrap();
    assert_eq!((*g.value(), g.link(), g.original_bits()), (2, 17, 0));
    drop(g);
    assert_eq!(map.compare_exchange_bits(key, 0, MAX), Ok(key));
    assert!(catch_unwind(AssertUnwindSafe(|| map.compare_exchange_bits(
        key,
        MAX,
        1 << 30
    )))
    .is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| map.compare_exchange_bits(
        key,
        1 << 30,
        0
    )))
    .is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| map.insert(3, 1 << 30))).is_err());
    assert_eq!(*map.try_get(key, MAX).unwrap().value(), 2);
    assert!(catch_unwind(GuardedSlotMap::<DefaultKey, (), 31>::new).is_err());
    assert!(catch_unwind(|| GuardedSlotMap::<DefaultKey, (), 32>::with_capacity(1)).is_err());
}

// All callback state is thread-local, including in the atomic build. The scope
// helper below permits a hook to borrow a map and a guard container without leaks.
type Hook = Box<dyn FnOnce()>;
thread_local! {
    static HOOK: RefCell<Option<(u8, usize, Hook)>> = const { RefCell::new(None) };
    static COUNTS: Cell<[usize; 2]> = const { Cell::new([0; 2]) };
}
fn callback(stage: u8) {
    COUNTS.with(|c| {
        let mut n = c.get();
        n[stage as usize] += 1;
        c.set(n);
    });
    let hook = HOOK.with(|cell| {
        let mut slot = cell.borrow_mut();
        if let Some((s, remaining, _)) = slot.as_mut() {
            if *s == stage {
                if *remaining == 0 {
                    return slot.take();
                }
                *remaining -= 1;
            }
        }
        None
    });
    if let Some((_, _, f)) = hook {
        f();
    }
}
fn with_hook<R>(stage: u8, occurrence: usize, hook: impl FnOnce(), body: impl FnOnce() -> R) -> R {
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            HOOK.with(|h| {
                h.borrow_mut().take();
            });
        }
    }
    let hook: Box<dyn FnOnce() + '_> = Box::new(hook);
    // SAFETY: TLS never crosses threads. Reset removes/drops the hook before
    // either borrowed closure leaves this function, including on unwind. callback
    // removes the hook before invoking it; recursive calls cannot invoke it twice.
    let hook: Hook = unsafe { std::mem::transmute(hook) };
    HOOK.with(|h| {
        assert!(h.borrow().is_none());
        *h.borrow_mut() = Some((stage, occurrence, hook));
    });
    let _reset = Reset;
    body()
}
fn counts() -> [usize; 2] {
    COUNTS.with(Cell::get)
}
fn reset_counts() {
    COUNTS.with(|c| c.set([0; 2]));
}

#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct CallbackKey(DefaultKey);
impl From<KeyData> for CallbackKey {
    fn from(data: KeyData) -> Self {
        callback(0);
        Self(data.into())
    }
}
impl pi_null::Null for CallbackKey {
    fn null() -> Self {
        Self(DefaultKey::default())
    }
    fn is_null(&self) -> bool {
        self.0 == DefaultKey::default()
    }
}
impl Key for CallbackKey {
    fn with(index: usize) -> Self {
        Self(DefaultKey::with(index))
    }
    fn index(&self) -> usize {
        self.0.index()
    }
    fn data(&self) -> KeyData {
        callback(1);
        self.0.data()
    }
}

#[derive(Clone, Copy, Debug)]
enum Operation {
    Get,
    Remove,
    Cas,
}
fn attempt(
    map: &GuardedSlotMap<CallbackKey, u32>,
    key: CallbackKey,
    op: Operation,
) -> Result<(), Error> {
    match op {
        Operation::Get => map.try_get(key, 1).map(drop),
        Operation::Remove => map.try_remove(key, 1).map(drop),
        Operation::Cas => map.compare_exchange_bits(key, 1, 0).map(drop),
    }
}
fn callback_shape(op: Operation) -> [usize; 2] {
    let map = GuardedSlotMap::<CallbackKey, u32>::new();
    let key = map.insert(11, 1);
    reset_counts();
    attempt(&map, key, op).unwrap();
    let n = counts();
    assert!(
        n[0] > 0 && n[1] > 0,
        "both key conversion stages must be exercised"
    );
    n
}

#[test]
fn every_key_callback_stage_reentry_preserves_inner_claim_bits_or_deletion() {
    for op in [Operation::Get, Operation::Remove, Operation::Cas] {
        // Discover only callback occurrence count, never expected state semantics.
        // Every data/from occurrence on the successful public path gets its own case.
        let shape = callback_shape(op);
        for stage in [0, 1] {
            for occurrence in 0..shape[stage as usize] {
                for action in 0..4 {
                    for panic_after in [false, true] {
                        let map = GuardedSlotMap::<CallbackKey, u32>::new();
                        let key = map.insert_with_link(11, 71, 1);
                        let held = RefCell::new(None);
                        let replacement = Cell::new(None);
                        let fired = Cell::new(0);
                        let result = catch_unwind(AssertUnwindSafe(|| {
                            with_hook(
                                stage,
                                occurrence,
                                || {
                                    fired.set(fired.get() + 1);
                                    match action {
                                        0 => {
                                            *held.borrow_mut() = Some(map.try_get(key, 1).unwrap());
                                        }
                                        1 => {
                                            map.compare_exchange_bits(key, 1, 2).unwrap();
                                        }
                                        2 | 3 => {
                                            assert_eq!(map.try_remove(key, 1).unwrap(), (11, 71));
                                            if action == 3 {
                                                replacement
                                                    .set(Some(map.insert_with_link(22, 82, 3)));
                                            }
                                        }
                                        _ => unreachable!(),
                                    }
                                    if panic_after {
                                        panic!("key callback after inner mutation");
                                    }
                                },
                                || attempt(&map, key, op),
                            )
                        }));
                        assert_eq!(
                            fired.get(),
                            1,
                            "{op:?}, stage={stage}, occurrence={occurrence}"
                        );
                        if panic_after {
                            assert!(result.is_err());
                        } else {
                            error(
                                result.unwrap(),
                                match action {
                                    0 => Error::Busy,
                                    1 => Error::BitsMismatch { actual_bits: 2 },
                                    _ => Error::Stale,
                                },
                            );
                        }
                        match action {
                            0 => {
                                error(map.try_get(key, 0), Error::Busy);
                                let mut slot = held.borrow_mut();
                                let g = slot.as_mut().unwrap();
                                assert_eq!((*g.value(), g.link(), g.bits()), (11, 71, 1));
                                g.set_bits(3);
                                drop(slot);
                                drop(held.borrow_mut().take());
                                assert_eq!(*map.try_get(key, 3).unwrap().value(), 11);
                            }
                            1 => {
                                let g = map.try_get(key, 2).unwrap();
                                assert_eq!((*g.value(), g.link()), (11, 71));
                            }
                            2 => {
                                assert!(map.is_empty());
                                error(map.try_get(key, 1), Error::Stale);
                            }
                            3 => {
                                let new = replacement.get().unwrap();
                                assert_eq!(new.0.data().index(), key.0.data().index());
                                assert_ne!(new, key);
                                let g = map.try_get(new, 3).unwrap();
                                assert_eq!((*g.value(), g.link(), g.bits()), (22, 82, 3));
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn key_panics_never_claim_and_guard_key_drop_remove_do_not_call_key() {
    for op in [Operation::Get, Operation::Remove, Operation::Cas] {
        let shape = callback_shape(op);
        for stage in [0, 1] {
            for occurrence in 0..shape[stage as usize] {
                let map = GuardedSlotMap::<CallbackKey, u32>::new();
                let key = map.insert_with_link(11, 71, 1);
                assert!(catch_unwind(AssertUnwindSafe(|| with_hook(
                    stage,
                    occurrence,
                    || panic!("key panic"),
                    || attempt(&map, key, op)
                )))
                .is_err());
                let g = map.try_get(key, 1).unwrap();
                assert_eq!((*g.value(), g.link(), map.len()), (11, 71, 1));
            }
        }
    }
    for (remove, stage) in [(false, 0), (false, 1), (true, 0), (true, 1)] {
        let drops = Arc::new(AtomicUsize::new(0));
        let map = GuardedSlotMap::<CallbackKey, Tracked>::new();
        let key = map.insert_with_link(tracked(8, &drops), 91, 1);
        let g = map.try_get(key, 1).unwrap();
        reset_counts();
        for stage in [0, 1] {
            // key() is cached; hooks are removed uncalled at scope exit.
            with_hook(
                stage,
                0,
                || panic!("guard key callback"),
                || assert_eq!(g.key(), key),
            );
        }
        with_hook(
            stage,
            0,
            || panic!("release/remove key callback"),
            || finish_guard(remove, g, &drops),
        );
        assert_eq!(counts(), [0, 0]);
        drop(map);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
    }
}

// Both conversion stages are armed independently; counts cover the whole operation.
fn finish_guard(
    remove: bool,
    g: pi_slot::SlotGuard<'_, CallbackKey, Tracked>,
    drops: &Arc<AtomicUsize>,
) {
    if remove {
        let (v, link) = g.remove();
        assert_eq!((v.id, link, drops.load(Ordering::SeqCst)), (8, 91, 0));
        drop(v);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
    } else {
        drop(g);
        assert_eq!(drops.load(Ordering::SeqCst), 0);
    }
}

#[test]
fn insertion_key_panic_rolls_back_each_entry_without_constructing_or_double_drop() {
    for entry in 0..3 {
        // Count stages using a completed insertion, independently for each entry.
        let probe = GuardedSlotMap::<CallbackKey, Tracked>::new();
        let drops = Arc::new(AtomicUsize::new(0));
        reset_counts();
        match entry {
            0 => {
                probe.insert(tracked(1, &drops), 1);
            }
            1 => {
                probe.insert_with_link(tracked(1, &drops), 9, 1);
            }
            _ => {
                probe.insert_with_key(1, |_| tracked(1, &drops));
            }
        }
        let shape = counts();
        drop(probe);
        for stage in [0, 1] {
            assert!(shape[stage as usize] > 0);
            for occurrence in 0..shape[stage as usize] {
                let drops = Arc::new(AtomicUsize::new(0));
                let map = GuardedSlotMap::<CallbackKey, Tracked>::new();
                let constructors = Cell::new(0);
                let result = catch_unwind(AssertUnwindSafe(|| {
                    with_hook(
                        stage,
                        occurrence,
                        || panic!("insertion key panic"),
                        || match entry {
                            0 => {
                                map.insert(tracked(7, &drops), 1);
                            }
                            1 => {
                                map.insert_with_link(tracked(7, &drops), 99, 1);
                            }
                            _ => {
                                map.insert_with_key(1, |key| {
                                    constructors.set(constructors.get() + 1);
                                    let _ = key;
                                    tracked(7, &drops)
                                });
                            }
                        },
                    )
                }));
                assert!(
                    result.is_err(),
                    "entry={entry} stage={stage} occurrence={occurrence}"
                );
                assert!(map.is_empty());
                assert_eq!(
                    constructors.get(),
                    0,
                    "all key callbacks must finish before f"
                );
                assert_eq!(drops.load(Ordering::SeqCst), usize::from(entry != 2));
                let next = map.insert(tracked(8, &drops), 2);
                assert_eq!(next.0.data().index(), 0);
                // First reserved identity has LIVE bit 3, clear low 3 bits.
                let reserved = CallbackKey(KeyData::new(0, 8).into());
                assert_ne!(next, reserved);
                error(map.try_get(reserved, 1), Error::Stale);
                assert_eq!(map.len(), 1);
                drop(map);
                assert_eq!(drops.load(Ordering::SeqCst), 1 + usize::from(entry != 2));
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Frame {
    sequence: u64,
    inverse: u64,
    lanes: [u64; 8],
}
impl Frame {
    fn new(n: u64) -> Self {
        Self {
            sequence: n,
            inverse: !n,
            lanes: [n.wrapping_mul(37); 8],
        }
    }
}

#[cfg(not(feature = "rc"))]
#[test]
fn concurrent_reader_sees_only_fully_initialized_first_publication() {
    use std::sync::mpsc;
    use std::time::{Duration, Instant};
    let map = GuardedSlotMap::<DefaultKey, Frame>::new();
    std::thread::scope(|scope| {
        let (candidate_tx, candidate_rx) = mpsc::channel();
        let (ready_tx, ready_rx) = mpsc::channel();
        let reader_map = &map;
        let reader = scope.spawn(move || {
            let map = reader_map;
            let key = candidate_rx.recv_timeout(Duration::from_secs(10)).unwrap();
            error(map.try_get(key, 3), Error::Stale);
            ready_tx.send(()).unwrap();
            let deadline = Instant::now() + Duration::from_secs(10);
            loop {
                match map.try_get(key, 3) {
                    Ok(g) => {
                        assert_eq!(*g.value(), Frame::new(997));
                        assert_eq!((g.link(), g.original_bits(), g.bits()), (0, 3, 3));
                        break;
                    }
                    Err(Error::Stale) => {
                        assert!(Instant::now() < deadline, "initial publication timed out");
                        std::thread::yield_now();
                    }
                    Err(e) => panic!("unexpected publication error {e:?}"),
                }
            }
        });
        let key = map.insert_with_key(3, |key| {
            candidate_tx.send(key).unwrap();
            ready_rx.recv_timeout(Duration::from_secs(10)).unwrap();
            // Construct after the last writer-to-reader channel message. Only
            // LIVE publication can make these non-atomic writes visible.
            Frame::new(997)
        });
        reader.join().unwrap();
        assert_eq!(map.try_get(key, 3).unwrap().key(), key);
    });
}

#[cfg(not(feature = "rc"))]
fn wait_claim<'a>(
    map: &'a GuardedSlotMap<DefaultKey, Frame>,
    key: DefaultKey,
    bits: u32,
) -> pi_slot::SlotGuard<'a, DefaultKey, Frame> {
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
    loop {
        match map.try_get(key, bits) {
            Ok(g) => return g,
            Err(Error::Busy | Error::BitsMismatch { .. }) => {
                assert!(
                    std::time::Instant::now() < deadline,
                    "handoff timed out waiting for bits={bits}"
                );
                std::thread::yield_now();
            }
            Err(e) => panic!("unexpected handoff error {e:?}"),
        }
    }
}

#[cfg(not(feature = "rc"))]
#[test]
fn concurrent_reuse_publishes_new_value_nonzero_link_and_complete_bits() {
    use std::sync::mpsc;
    use std::time::{Duration, Instant};
    let map = GuardedSlotMap::<DefaultKey, Frame>::new();
    let old = map.insert_with_link(Frame::new(11), u64::MAX, 3);
    assert_eq!(map.try_remove(old, 3).unwrap(), (Frame::new(11), u64::MAX));
    // Default N=2: CLAIMED=4, LIVE=8, so one remove/reuse cycle
    // advances the stable generation by 16. No complete generation wrap.
    let expected: DefaultKey =
        KeyData::new(old.data().index(), old.data().version().wrapping_add(16)).into();
    std::thread::scope(|scope| {
        let (ready_tx, ready_rx) = mpsc::channel();
        let reader_map = &map;
        let reader = scope.spawn(move || {
            error(reader_map.try_get(expected, 1), Error::Stale);
            ready_tx.send(()).unwrap();
            let deadline = Instant::now() + Duration::from_secs(10);
            loop {
                match reader_map.try_get(expected, 1) {
                    Ok(g) => {
                        assert_eq!(*g.value(), Frame::new(997));
                        assert_eq!(
                            (g.key(), g.link(), g.original_bits(), g.bits()),
                            (expected, 0x1234_5678_9abc_def0, 1, 1)
                        );
                        break;
                    }
                    Err(Error::Stale) => {
                        assert!(Instant::now() < deadline, "reuse publication timed out");
                        std::thread::yield_now();
                    }
                    Err(e) => panic!("unexpected reuse error {e:?}"),
                }
            }
        });
        ready_rx.recv_timeout(Duration::from_secs(10)).unwrap();
        // New payload construction and publication follow the only handshake;
        // no writer-to-reader channel/flag publishes these new writes.
        let new = map.insert_with_link(Frame::new(997), 0x1234_5678_9abc_def0, 1);
        reader.join().unwrap();
        assert_eq!(new, expected);
        assert_eq!(new.data().index(), old.data().index());
        error(map.try_get(old, 3), Error::Stale);
        assert_eq!(map.len(), 1);
    });
}

#[test]
fn release_acquire_publishes_non_atomic_value_link_and_bits_each_round() {
    let map = GuardedSlotMap::<DefaultKey, Frame>::new();
    let key = map.insert(Frame::new(0), 0);
    #[cfg(not(feature = "rc"))]
    std::thread::scope(|scope| {
        let reader = scope.spawn(|| {
            for n in 1..=128 {
                let mut g = wait_claim(&map, key, 1);
                assert_eq!(*g.value(), Frame::new(n));
                assert_eq!((g.link(), g.original_bits(), g.bits()), (n, 1, 1));
                g.set_bits(0);
            }
        });
        for n in 1..=128 {
            let mut g = wait_claim(&map, key, 0);
            *g.value_mut() = Frame::new(n);
            g.set_link(n);
            g.set_bits(1);
        }
        reader.join().unwrap();
    });
    #[cfg(feature = "rc")]
    for n in 1..=128 {
        let mut writer = map.try_get(key, 0).unwrap();
        *writer.value_mut() = Frame::new(n);
        writer.set_link(n);
        writer.set_bits(1);
        drop(writer);
        let mut reader = map.try_get(key, 1).unwrap();
        assert_eq!(*reader.value(), Frame::new(n));
        assert_eq!(
            (reader.link(), reader.original_bits(), reader.bits()),
            (n, 1, 1)
        );
        reader.set_bits(0);
    }
    assert_eq!(map.try_get(key, 0).unwrap().value().sequence, 128);
}

#[cfg(not(feature = "rc"))]
#[test]
fn two_competitors_have_one_winner_held_until_both_attempts_finish() {
    use std::sync::mpsc;
    use std::time::Duration;
    let map = GuardedSlotMap::<DefaultKey, u32>::new();
    let key = map.insert(42, 1);
    std::thread::scope(|scope| {
        let (result_tx, result_rx) = mpsc::channel();
        let (ready_tx, ready_rx) = mpsc::channel();
        let mut starts = Vec::new();
        let (release_tx, release_rx) = mpsc::channel();
        // Separate bounded release channels avoid any barrier stranded by panic.
        let (release2_tx, release2_rx) = mpsc::channel();
        for release in [release_rx, release2_rx] {
            let tx = result_tx.clone();
            let ready = ready_tx.clone();
            let (start_tx, start_rx) = mpsc::channel();
            starts.push(start_tx);
            let map = &map;
            scope.spawn(move || {
                ready.send(()).unwrap();
                start_rx.recv_timeout(Duration::from_secs(10)).unwrap();
                match map.try_get(key, 1) {
                    Ok(g) => {
                        tx.send(Ok(())).unwrap();
                        release.recv_timeout(Duration::from_secs(10)).unwrap();
                        assert_eq!(*g.value(), 42);
                    }
                    Err(e) => {
                        tx.send(Err(e)).unwrap();
                    }
                }
            });
        }
        drop(ready_tx);
        let readiness: Vec<_> = (0..2)
            .map(|_| ready_rx.recv_timeout(Duration::from_secs(10)))
            .collect();
        for start in starts {
            let _ = start.send(());
        }
        drop(result_tx);
        let a = result_rx.recv_timeout(Duration::from_secs(10));
        let b = result_rx.recv_timeout(Duration::from_secs(10));
        let _ = release_tx.send(());
        let _ = release2_tx.send(());
        for ready in readiness {
            ready.unwrap();
        }
        let results = [a.unwrap(), b.unwrap()];
        assert_eq!(results.iter().filter(|r| r.is_ok()).count(), 1);
        for result in results {
            if let Err(e) = result {
                assert_eq!(e, Error::Busy);
            }
        }
    });
}
