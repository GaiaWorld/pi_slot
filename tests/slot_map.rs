use pi_slot::{
    CompareExchangeBitsError, DefaultKey, Key, KeyData, ReserveError, ShareU64, SlotMap,
};
use std::collections::HashSet;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

fn key(index: u32, version: u32) -> DefaultKey {
    KeyData::new(index, version).into()
}

#[test]
fn writer_exposes_key_before_insertion() {
    let map = SlotMap::<DefaultKey, (DefaultKey, u32)>::new();
    let writer = map.try_insert_if(|_| true).unwrap();
    let key = writer.key();
    assert_eq!(writer.key(), key);
    assert!(map.get(key).is_none());
    assert_eq!(writer.insert((key, 42)), key);
    assert_eq!(map.get(key).unwrap().0, &(key, 42));
}

#[test]
fn insert_with_key_constructs_self_referential_value_before_publication() {
    let map = SlotMap::<DefaultKey, (DefaultKey, u32)>::new();
    let first = map.insert_with_key(|key| {
        assert!(map.get(key).is_none());
        (key, 10)
    });
    assert_eq!(map.get(first).unwrap().0, &(first, 10));

    let second = map
        .try_insert_with_key::<()>(|key| {
            assert!(map.get(key).is_none());
            Ok((key, 20))
        })
        .unwrap();
    assert_eq!(map.get(second).unwrap().0, &(second, 20));
}

#[test]
fn fallible_key_insertion_rolls_back_without_publishing_value() {
    let map = SlotMap::<DefaultKey, DefaultKey>::new();
    let rejected = std::cell::Cell::new(None);
    assert_eq!(
        map.try_insert_with_key(|key| {
            rejected.set(Some(key));
            Err::<DefaultKey, _>("rejected")
        }),
        Err("rejected")
    );
    let rejected = rejected.get().unwrap();
    assert!(map.get(rejected).is_none());
    assert_eq!((map.max(), map.len()), (1, 0));
    let accepted = map.insert_with_key(|key| key);
    assert_eq!(accepted.data().index(), rejected.data().index());
    assert_eq!(accepted.data().version(), rejected.data().version() + 2);
    assert_eq!(map.get(accepted).unwrap().0, &accepted);
}

#[test]
fn rejected_reservation_does_not_construct_payload_or_consume_index() {
    let map = SlotMap::<DefaultKey, DropValue>::new();
    let constructed = AtomicUsize::new(0);
    let drops = Arc::new(AtomicUsize::new(0));
    let result = map.try_insert_if(|index| {
        assert_eq!(index, 0);
        false
    });
    match result {
        Ok(writer) => {
            constructed.fetch_add(1, Ordering::Relaxed);
            writer.insert(DropValue(drops.clone()));
            panic!("rejection must not return a writer");
        }
        Err(error) => assert_eq!(error, ReserveError::IndexRejected),
    }
    assert_eq!(constructed.load(Ordering::Relaxed), 0);
    assert_eq!(drops.load(Ordering::Relaxed), 0);
    assert_eq!((map.max(), map.len()), (0, 0));
}

#[cfg(feature = "rc")]
#[test]
fn rc_predicate_reentry_cannot_overwrite_initialized_slot() {
    let drops = Arc::new(AtomicUsize::new(0));
    let map = SlotMap::<DefaultKey, DropValue>::new();
    let mut nested = None;
    let result = map.try_insert_if(|index| {
        assert_eq!(index, 0);
        nested = Some(map.insert(DropValue(drops.clone())));
        true
    });
    assert!(matches!(result, Err(ReserveError::IndexRejected)));
    drop(result);
    assert_eq!((map.max(), map.len()), (1, 1));
    assert!(map.get(nested.unwrap()).is_some());
    drop(map);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[test]
fn writer_rollback_and_free_reuse_bypass_limit_without_statistics() {
    let mut map = SlotMap::<DefaultKey, String>::new();
    let writer = map.try_insert_if(|index| index < 1).unwrap();
    assert_eq!((map.len(), map.max(), map.iter().count()), (0, 1, 0));
    assert!(matches!(
        map.try_insert_if(|index| index < 1),
        Err(ReserveError::IndexRejected)
    ));
    drop(writer);
    assert_eq!((map.len(), map.max()), (0, 1));
    let first = map
        .try_insert_if(|_| panic!("FREE must bypass predicate"))
        .unwrap()
        .insert_with_link("first".into(), u64::MAX);
    assert_eq!((first.data().index(), first.data().version()), (0, 3));
    assert_eq!(map.get(first).unwrap().1.load(Ordering::Relaxed), u64::MAX);
    assert_eq!(map.remove(first), Some("first".into()));
    let second = map
        .try_insert_if(|_| false)
        .unwrap()
        .insert("second".into());
    assert_eq!(second.data().version(), 5);
    assert_eq!(map.get(second).unwrap().1.load(Ordering::Relaxed), 0);
    assert!(map.get(first).is_none());
    assert_eq!(map.remove(second), Some("second".into()));
    assert_eq!((map.len(), map.max()), (0, 1));
}

#[test]
fn predicate_panic_and_payload_constructor_panic_restore_empty_slot() {
    let map = SlotMap::<DefaultKey, String>::new();
    assert!(catch_unwind(AssertUnwindSafe(|| {
        let _ = map.try_insert_if(|_| panic!("predicate"));
    }))
    .is_err());
    assert_eq!((map.len(), map.max()), (0, 0));
    assert!(catch_unwind(AssertUnwindSafe(|| {
        let _writer = map.try_insert_if(|index| index < 1).unwrap();
        panic!("constructor before commit");
    }))
    .is_err());
    assert_eq!((map.len(), map.max()), (0, 1));
    let key = map
        .try_insert_if(|_| false)
        .unwrap()
        .insert("restored".into());
    assert_eq!(key.data().version(), 3);
    assert_eq!(map[key], "restored");
}

#[test]
fn forgotten_writer_is_an_empty_uncounted_safe_leak() {
    let drops = Arc::new(AtomicUsize::new(0));
    let map = SlotMap::<DefaultKey, DropValue>::new();
    std::mem::forget(map.try_insert_if(|_| true).unwrap());
    assert_eq!((map.len(), map.max(), map.iter().count()), (0, 1, 0));
    map.try_insert_if(|_| true)
        .unwrap()
        .insert(DropValue(drops.clone()));
    assert_eq!(map.len(), 1);
    drop(map);
    assert_eq!(drops.load(Ordering::Relaxed), 1);
}

#[cfg(not(feature = "rc"))]
#[test]
fn fresh_index_cas_retry_rechecks_limits_one_and_two() {
    use std::sync::mpsc;
    use std::time::Duration;
    for limit in [1, 2] {
        let map = SlotMap::<DefaultKey, u32>::new();
        let calls = AtomicUsize::new(0);
        std::thread::scope(|scope| {
            let (arrived_tx, arrived_rx) = mpsc::channel();
            let mut releases = Vec::new();
            let mut handles = Vec::new();
            for value in 0..4 {
                let (release_tx, release_rx) = mpsc::channel();
                releases.push(release_tx);
                let arrived = arrived_tx.clone();
                let map = &map;
                let calls = &calls;
                handles.push(scope.spawn(move || {
                    let mut first = true;
                    map.try_insert_if(|index| {
                        calls.fetch_add(1, Ordering::Relaxed);
                        if first {
                            first = false;
                            arrived.send(index).unwrap();
                            release_rx.recv_timeout(Duration::from_secs(10)).unwrap();
                        }
                        index < limit
                    })
                    .map(|writer| writer.insert(value))
                }));
            }
            drop(arrived_tx);
            let arrivals: Vec<_> = (0..4)
                .map(|_| arrived_rx.recv_timeout(Duration::from_secs(10)))
                .collect();
            // Unblock every participant before inspecting any assertion or join.
            for release in releases {
                let _ = release.send(());
            }
            let results: Vec<_> = handles.into_iter().map(|h| h.join()).collect();
            for arrival in arrivals {
                assert_eq!(arrival.unwrap(), 0);
            }
            let mut committed = 0;
            for result in results {
                match result.unwrap() {
                    Ok(key) => {
                        committed += 1;
                        assert!(key.data().index() < limit);
                    }
                    Err(error) => assert_eq!(error, ReserveError::IndexRejected),
                }
            }
            assert_eq!(committed, limit);
        });
        assert_eq!((map.max(), map.len()), (limit, limit as usize));
        assert!(calls.load(Ordering::Relaxed) > 4);
    }
}

#[test]
fn pi_key_preserves_full_generation_encoding() {
    for version in [0, 1, 2, 3, 4, 1 << 21, u32::MAX - 1, u32::MAX] {
        let encoded = (u64::from(version) << 32) | 17;
        let data = KeyData::from_ffi(encoded);
        assert_eq!((data.index(), data.version()), (17, version));
        assert_eq!(data.as_ffi(), encoded);
        let default: DefaultKey = data.into();
        assert_eq!(default.data(), data);
    }
}

#[cfg(not(feature = "rc"))]
#[test]
fn concurrent_length_stays_bounded_by_successful_insertions() {
    use std::sync::mpsc;
    use std::time::Duration;

    let map = SlotMap::<DefaultKey, usize>::new();
    std::thread::scope(|scope| {
        let (phase_tx, phase_rx) = mpsc::channel();
        let (sampled_tx, sampled_rx) = mpsc::channel();
        let map_ref = &map;
        let worker = scope.spawn(move || {
            for n in 0..1_000 {
                let key = map_ref.insert(n);
                phase_tx.send(true).unwrap();
                sampled_rx.recv_timeout(Duration::from_secs(10)).unwrap();
                // Only len is sampled by the observer: no value/link references
                // or scans overlap this shared removal. Handshakes schedule
                // counter observations, not a test of value publication.
                let removed = unsafe { map_ref.remove_shared(key) };
                phase_tx.send(false).unwrap();
                sampled_rx.recv_timeout(Duration::from_secs(10)).unwrap();
                assert_eq!(removed, Some(n));
            }
        });
        let mut nonzero = 0;
        let mut empty = 0;
        let mut samples = Vec::new();
        for _ in 0..2_000 {
            let live = phase_rx.recv_timeout(Duration::from_secs(10)).unwrap();
            for _ in 0..5 {
                let len = map.len();
                nonzero += usize::from(len != 0);
                empty += usize::from(len == 0);
                samples.push((live, len));
            }
            sampled_tx.send(()).unwrap();
        }
        worker.join().unwrap();
        for (live, len) in samples {
            assert!(len <= 1_000);
            assert_eq!(len, usize::from(live));
        }
        assert_eq!((nonzero, empty), (5_000, 5_000));
    });
    assert_eq!(
        (map.len(), map.alloc_count(), map.free_count()),
        (0, 1_000, 1_000)
    );
}

#[cfg(not(feature = "rc"))]
#[test]
fn default_build_has_atomic_thread_traits() {
    fn assert_traits<T: Send + Sync>() {}
    assert_traits::<SlotMap<DefaultKey, String>>();
}

#[cfg(feature = "rc")]
#[test]
fn rc_build_is_not_sync() {
    // Actual RC fields must prevent Sync; Send is not forbidden.
    trait NotSync<A> {
        fn check() {}
    }
    impl<T: ?Sized> NotSync<()> for T {}
    struct SyncMarker;
    impl<T: ?Sized + Sync> NotSync<SyncMarker> for T {}
    let _ = <SlotMap<DefaultKey, String> as NotSync<_>>::check;
}

#[test]
fn crud_stale_reuse_and_invalid_keys() {
    let mut map = SlotMap::<DefaultKey, String>::with_capacity(10);
    let a = map.insert("a".into());
    let b = map.set("b".into());
    assert_eq!((map.len(), map.max()), (2, 2));
    assert_eq!(a.data().version(), 1);
    map[a].push('!');
    map.get_mut(b).unwrap().0.push('?');
    assert_eq!(map.replace(a, "new".into()), Ok("a!".into()));
    assert_eq!(map.remove(a), Some("new".into()));
    assert_eq!(map.remove(a), None);
    let c = map.insert("reuse".into());
    assert_eq!(c.data().index(), a.data().index());
    assert_eq!(c.data().version(), 3);
    assert_eq!((map.len(), map.max()), (2, 2));
    assert!(map.get(a).is_none());
    for invalid in [
        DefaultKey::default(),
        key(0, 0),
        key(0, 1),
        key(0, 2),
        key(9, 2),
        key(u32::MAX, 2),
    ] {
        assert!(map.get(invalid).is_none());
        assert!(map.get_mut(invalid).is_none());
        assert!(map.remove(invalid).is_none());
        assert_eq!(
            map.replace(invalid, "original".into()),
            Err("original".into())
        );
        // 单线程，没有任何引用或迭代器存活。
        unsafe {
            assert!(map.get_shared(invalid).is_none());
            assert!(map.remove_shared(invalid).is_none());
        }
    }
    assert!(format!("{map:?}").contains("reuse"));
    assert_eq!(map.remove(b), Some("b?".into()));
    assert_eq!(map.remove(c), Some("reuse".into()));
    assert!(map.is_empty());
    assert_eq!(map.max(), 2);
}

#[test]
fn shared_unsafe_with_exclusive_slot_contract() {
    let map = SlotMap::<DefaultKey, String>::new();
    let k = map.insert("a".into());
    // 所有引用均在下一次操作前结束；没有并发 reader/writer 或扫描。
    unsafe {
        map.get_shared(k).unwrap().0.push('b');
        map.get_shared_unchecked(k).0.push('c');
        assert_eq!(
            map.replace_shared(k, "replacement".into()),
            Ok("abc".into())
        );
        assert_eq!(map.get_unchecked(k).0, "replacement");
        assert_eq!(map.remove_shared(k), Some("replacement".into()));
        assert_eq!(
            map.replace_shared(k, "rejected".into()),
            Err("rejected".into())
        );
    }
}

#[test]
fn all_link_apis_preserve_or_return_snapshots() {
    let mut map = SlotMap::<DefaultKey, String>::new();
    let plain = map.insert("plain".into());
    let alias = map.set("alias".into());
    assert_eq!(map.get(plain).unwrap().1.load(Ordering::Relaxed), 0);
    assert_eq!(map.get(alias).unwrap().1.load(Ordering::Relaxed), 0);
    let a = map.insert_with_link("a".into(), u64::MAX);
    let b = map.set_with_link("b".into(), 23);
    let address = map.get(a).unwrap().1 as *const ShareU64;
    map.get(a).unwrap().1.store(41, Ordering::Relaxed);
    assert_eq!(map.replace(a, "a2".into()), Ok("a".into()));
    assert_eq!(map.get(a).unwrap().1.load(Ordering::Relaxed), 41);
    assert_eq!(
        map.replace_with_link(a, "a3".into(), 42),
        Ok(("a2".into(), 41))
    );
    assert_eq!(address, map.get(a).unwrap().1 as *const ShareU64);
    assert_eq!(map.remove_with_link(a), Some(("a3".into(), 42)));
    assert_eq!(
        map.replace_with_link(a, "rejected".into(), 77),
        Err(("rejected".into(), 77))
    );
    assert!(map.remove_with_link(a).is_none());
    // No user references survive each unsafe operation; no concurrent readers.
    unsafe {
        let (value, link) = map.get_shared(b).unwrap();
        value.push('!');
        link.store(24, Ordering::Relaxed);
        let (value, link) = map.get_shared_unchecked(b);
        value.push('?');
        assert_eq!(link.load(Ordering::Relaxed), 24);
        assert_eq!(map.replace_shared(b, "b2".into()), Ok("b!?".into()));
        assert_eq!(map.get_unchecked(b).1.load(Ordering::Relaxed), 24);
        assert_eq!(
            map.replace_shared_with_link(b, "b3".into(), 25),
            Ok(("b2".into(), 24))
        );
        assert_eq!(map.remove_shared_with_link(b), Some(("b3".into(), 25)));
        assert_eq!(
            map.replace_shared_with_link(b, "failed".into(), 88),
            Err(("failed".into(), 88))
        );
        assert!(map.remove_shared_with_link(b).is_none());
    }
    assert_eq!(map.remove(plain), Some("plain".into()));
    assert_eq!(map.remove(alias), Some("alias".into()));
    assert_eq!(map.len(), 0);
}

#[test]
fn exclusive_field_replacement_keeps_free_link_initialized() {
    let drops = Arc::new(AtomicUsize::new(0));
    let mut map = SlotMap::<DefaultKey, DropValue>::new();
    let a = map.insert(DropValue(drops.clone()));
    let b = map.insert(DropValue(drops.clone()));
    let old = std::mem::replace(map.get_mut(a).unwrap().0, DropValue(drops.clone()));
    drop(old);
    *map.get_mut(b).unwrap().1 = ShareU64::new(29);
    for (_, tuple) in map.iter_mut() {
        *tuple.1 = ShareU64::new(39);
    }
    assert_eq!(
        map.iter()
            .map(|(_, tuple)| tuple.1.load(Ordering::Relaxed))
            .collect::<Vec<_>>(),
        [39, 39]
    );
    drop(map.remove_with_link(a).unwrap());
    drop(map.remove_with_link(b).unwrap());
    let reused = map.insert_with_link(DropValue(drops.clone()), 49);
    assert_eq!(map.get(reused).unwrap().1.load(Ordering::Relaxed), 49);
    drop(map);
    assert_eq!(drops.load(Ordering::SeqCst), 4);
    #[cfg(feature = "rc")]
    {
        let _: ShareU64 = pi_share::atomic::AtomicCell::new(1u64);
        assert_eq!(
            std::mem::needs_drop::<ShareU64>(),
            std::mem::needs_drop::<pi_share::atomic::AtomicCell<u64>>()
        );
    }
}

type KeyCallback = Option<(u8, Box<dyn FnOnce()>)>;

thread_local! {
    static KEY_CALLBACK: std::cell::RefCell<KeyCallback> = const { std::cell::RefCell::new(None) };
}

fn key_callback(stage: u8) {
    let callback = KEY_CALLBACK.with(|cell| {
        let mut callback = cell.borrow_mut();
        if callback
            .as_ref()
            .is_some_and(|(expected, _)| *expected == stage)
        {
            callback.take()
        } else {
            None
        }
    });
    if let Some((_, callback)) = callback {
        callback();
    }
}

#[derive(Copy, Clone, Default, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct CallbackKey(DefaultKey);
impl From<KeyData> for CallbackKey {
    fn from(data: KeyData) -> Self {
        key_callback(1);
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
        key_callback(2);
        self.0.data()
    }
}

#[test]
fn key_callbacks_reenter_and_unwind_without_payload_or_candidate_loss() {
    for stage in [1, 2] {
        let drops = Arc::new(AtomicUsize::new(0));
        let map = std::rc::Rc::new(SlotMap::<CallbackKey, DropValue>::new());
        let inner = map.clone();
        let inner_drops = drops.clone();
        KEY_CALLBACK.with(|cell| {
            *cell.borrow_mut() = Some((
                stage,
                Box::new(move || {
                    assert_eq!((inner.len(), inner.max()), (0, 1));
                    assert_eq!(inner.iter().count(), 0);
                    let unpublished = CallbackKey(key(0, 2));
                    assert!(inner.get(unpublished).is_none());
                    let nested = inner.insert(DropValue(inner_drops));
                    assert_eq!(nested.data().index(), 1);
                    panic!("key callback unwind");
                }),
            ))
        });
        assert!(catch_unwind(AssertUnwindSafe(|| map.insert(DropValue(drops.clone())))).is_err());
        assert_eq!((map.len(), map.max()), (1, 2));
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        let recovered = map.insert(DropValue(drops.clone()));
        assert_eq!(
            (recovered.data().index(), recovered.data().version()),
            (0, 3)
        );
        assert_eq!(map.iter().count(), 2);
        drop(map);
        assert_eq!(drops.load(Ordering::SeqCst), 3);
    }
}

#[test]
fn bits_cas_key_callbacks_cannot_overwrite_reentrant_changes_or_panic_mutations() {
    for stage in [1, 2] {
        let map = std::rc::Rc::new(SlotMap::<CallbackKey, u32, 2>::new());
        let key = map.insert(7);
        let inner = map.clone();
        KEY_CALLBACK.with(|cell| {
            *cell.borrow_mut() = Some((
                stage,
                Box::new(move || {
                    inner.compare_exchange_bits(key, 0, 2).unwrap();
                }),
            ));
        });
        assert_eq!(
            map.compare_exchange_bits(key, 0, 1),
            Err(CompareExchangeBitsError::Mismatch { actual_bits: 2 })
        );
        assert_eq!(map.get_key_bits(0), Some(2));
        assert_eq!(map.len(), 1);
        KEY_CALLBACK.with(|cell| {
            *cell.borrow_mut() = Some((stage, Box::new(|| panic!("key callback before CAS"))));
        });
        assert!(catch_unwind(AssertUnwindSafe(|| map.compare_exchange_bits(key, 2, 3))).is_err());
        assert_eq!(map.get_key_bits(0), Some(2));
        assert_eq!(map.len(), 1);
    }
}

#[cfg(not(feature = "rc"))]
#[test]
fn small_mpmc_transfers_unique_keys_before_shared_removal() {
    use std::sync::{mpsc, Barrier};
    let map = Arc::new(SlotMap::<DefaultKey, (usize, usize)>::new());
    let start = Barrier::new(4);
    std::thread::scope(|scope| {
        let mut workers = Vec::new();
        for producer in 0..2 {
            let (send, receive) = mpsc::sync_channel(8);
            let map = &map;
            let start = &start;
            workers.push(scope.spawn(move || {
                start.wait();
                for item in 0..200 {
                    let key =
                        map.insert_with_link((producer, item), (producer * 200 + item) as u64);
                    send.send((key, item)).unwrap();
                }
            }));
            workers.push(scope.spawn(move || {
                start.wait();
                for (key, item) in receive {
                    // Channel transfers each key to exactly one remover after
                    // insertion. No payload/link references or iterators overlap.
                    let removed = unsafe { map.remove_shared_with_link(key) };
                    assert_eq!(
                        removed,
                        Some(((producer, item), (producer * 200 + item) as u64))
                    );
                }
            }));
        }
        for worker in workers {
            worker.join().unwrap();
        }
    });
    assert_eq!(map.len(), 0);
    assert_eq!(map.iter().count(), 0);
    let key = map.insert_with_link((9, 9), u64::MAX);
    assert_eq!(map[key], (9, 9));
    assert_eq!(map.get(key).unwrap().1.load(Ordering::Relaxed), u64::MAX);
}

#[test]
fn iter_mut_unique_references_and_frozen_upper_bound() {
    let mut map = SlotMap::<DefaultKey, String>::with_capacity(3);
    let keys: Vec<_> = (0..200).map(|i| map.insert(i.to_string())).collect();
    map.remove(keys[10]);
    let mut seen = HashSet::new();
    {
        let entries: Vec<_> = map.iter_mut().collect();
        assert_eq!(entries.len(), 199);
        for (k, value) in entries {
            assert!(seen.insert(k));
            value.0.push('!');
        }
    }
    for (k, value) in map.iter() {
        assert!(seen.contains(&k));
        assert!(value.0.ends_with('!'));
    }
    let filled = map.insert("filled hole".into());
    assert_eq!(filled.data().index(), keys[10].data().index());
    assert_eq!(map.len(), map.max() as usize);
    let mut iterator = map.iter();
    let end = map.max();
    let outside = map.insert("outside".into());
    assert!(outside.data().index() >= end);
    let mut visited = 0;
    assert!(iterator.all(|(k, _)| {
        visited += 1;
        assert_ne!(k, outside);
        k.data().index() < end
    }));
    assert_eq!(visited, end as usize);
    // 独占表，键有效。
    unsafe {
        map.get_unchecked_mut(keys[0]).0.push('?');
    }
    assert_eq!(map[keys[0]], "0!?");
}

#[test]
fn iter_mut_preserves_keys_across_sparse_buckets() {
    let mut map = SlotMap::<DefaultKey, usize>::new();
    let keys: Vec<_> = (0..260).map(|value| map.insert(value)).collect();
    for key in &keys[0..258] {
        map.remove(*key);
    }
    let mut entries: Vec<_> = map.iter_mut().collect();
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].0, keys[258]);
    assert_eq!(entries[1].0, keys[259]);
    *entries[0].1 .0 = 42;
    *entries[1].1 .0 = 43;
    assert_eq!((map[keys[258]], map[keys[259]]), (42, 43));
}

struct DropValue(Arc<AtomicUsize>);

struct TrackedDrop {
    dropped: Arc<AtomicUsize>,
    panic: bool,
}
impl Drop for TrackedDrop {
    fn drop(&mut self) {
        self.dropped.fetch_add(1, Ordering::SeqCst);
        if self.panic {
            std::panic::panic_any("first tracked drop panic");
        }
    }
}

#[test]
fn map_drop_forgets_secondary_payload_with_panicking_destructor() {
    struct DangerousPayload(Arc<AtomicUsize>);
    impl Drop for DangerousPayload {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
            panic!("secondary payload must not be dropped");
        }
    }
    struct Panics {
        index: usize,
        dropped: Arc<AtomicUsize>,
        payload_drops: Arc<AtomicUsize>,
    }
    impl Drop for Panics {
        fn drop(&mut self) {
            self.dropped.fetch_add(1, Ordering::SeqCst);
            match self.index {
                0 => std::panic::panic_any("first payload"),
                32 => std::panic::panic_any(DangerousPayload(self.payload_drops.clone())),
                _ => {}
            }
        }
    }
    let dropped = Arc::new(AtomicUsize::new(0));
    let payload_drops = Arc::new(AtomicUsize::new(0));
    let map = SlotMap::<DefaultKey, Panics>::new();
    for index in 0..65 {
        map.insert(Panics {
            index,
            dropped: dropped.clone(),
            payload_drops: payload_drops.clone(),
        });
    }
    let payload = catch_unwind(AssertUnwindSafe(|| drop(map))).unwrap_err();
    assert_eq!(payload.downcast_ref::<&str>(), Some(&"first payload"));
    assert_eq!(dropped.load(Ordering::SeqCst), 65);
    assert_eq!(payload_drops.load(Ordering::SeqCst), 0);
}

#[test]
fn map_drop_visits_later_buckets_after_single_value_panic() {
    // 无连续预分配，33 个 LIVE 值跨过首桶的 32 槽边界。
    for panic in [false, true] {
        let made = AtomicUsize::new(0);
        let dropped = Arc::new(AtomicUsize::new(0));
        let map = SlotMap::<DefaultKey, TrackedDrop>::new();
        for index in 0..33 {
            made.fetch_add(1, Ordering::SeqCst);
            map.insert(TrackedDrop {
                dropped: dropped.clone(),
                panic: panic && index == 0,
            });
        }
        let result = catch_unwind(AssertUnwindSafe(|| drop(map)));
        assert_eq!(dropped.load(Ordering::SeqCst), made.load(Ordering::SeqCst));
        if panic {
            assert_eq!(
                result.unwrap_err().downcast_ref::<&str>(),
                Some(&"first tracked drop panic")
            );
        } else {
            assert!(result.is_ok());
        }
    }
}
impl Drop for DropValue {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn non_default_non_copy_drop_and_rejected_lossy_key() {
    let drops = Arc::new(AtomicUsize::new(0));
    let mut map = SlotMap::<DefaultKey, DropValue>::default();
    let a = map.insert(DropValue(drops.clone()));
    let b = map.insert(DropValue(drops.clone()));
    let old = map.replace(a, DropValue(drops.clone())).ok().unwrap();
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    drop(old);
    drop(map.remove(b));
    drop(map);
    assert_eq!(drops.load(Ordering::SeqCst), 3);
    let bad = SlotMap::<usize, DropValue>::default();
    for expected in 4..=5 {
        assert!(catch_unwind(AssertUnwindSafe(|| bad.insert(DropValue(drops.clone())))).is_err());
        assert_eq!(drops.load(Ordering::SeqCst), expected);
        assert_eq!((bad.len(), bad.max()), (0, 1));
    }
}

#[test]
fn reserved_bits_are_strict_preserved_and_visible_to_iteration() {
    let mut map = SlotMap::<DefaultKey, String, 2>::new();
    let old = map.insert_with_link("value".into(), 99);
    assert_eq!(old.data().version(), 4);
    assert_eq!(map.get_key_bits(0), Some(0));
    let updated = map.compare_exchange_bits(old, 0, 3).unwrap();
    assert_eq!(updated.data().version(), 7);
    assert!(map.get(old).is_none());
    assert!(map.remove(old).is_none());
    assert_eq!(
        map.compare_exchange_bits(old, 0, 0),
        Err(CompareExchangeBitsError::Mismatch { actual_bits: 3 })
    );
    // key 的低业务位不参与身份比较；显式 expected 才是状态前提。
    assert_eq!(map.compare_exchange_bits(old, 3, 3), Ok(updated));
    assert_eq!(map.get_key_bits(0), Some(3));
    assert_eq!(map.iter().next().unwrap().0, updated);
    assert_eq!(map.iter_mut().next().unwrap().0, updated);
    assert!(catch_unwind(AssertUnwindSafe(|| map.compare_exchange_bits(updated, 3, 4))).is_err());
    assert_eq!(map.get(updated).unwrap().0, "value");
    assert_eq!(map.remove_with_link(updated), Some(("value".into(), 99)));
    assert_eq!(map.get_key_bits(0), None);
    let reused = map.insert("next".into());
    assert_eq!(reused.data().version(), 15);
    assert_eq!(map.get_key_bits(0), Some(3));
    let reset = map.compare_exchange_bits(reused, 3, 0).unwrap();
    assert_eq!(map.compare_exchange_bits(reset, 0, 3), Ok(reused));
    assert_eq!(
        map.compare_exchange_bits(updated, 3, 0),
        Err(CompareExchangeBitsError::Stale)
    );
    assert_eq!(map.get_key_bits(u32::MAX), None);
}

#[test]
fn zero_bits_and_invalid_n_are_checked() {
    let map = SlotMap::<DefaultKey, ()>::new();
    let key = map.insert(());
    assert_eq!(key.data().version(), 1);
    assert_eq!(map.compare_exchange_bits(key, 0, 0), Ok(key));
    assert!(catch_unwind(AssertUnwindSafe(|| map.compare_exchange_bits(key, 0, 1))).is_err());
    assert!(map.get(key).is_some());
}

#[test]
fn invalid_n_is_rejected_without_executing_design_stubs() {
    assert!(catch_unwind(SlotMap::<DefaultKey, (), 32>::new).is_err());
    assert!(catch_unwind(SlotMap::<DefaultKey, (), 33>::default).is_err());
}

#[test]
fn high_n_wraps_with_bits_and_writer_rollback() {
    let mut map = SlotMap::<DefaultKey, String, 31>::new();
    let first = map.insert("first".into());
    assert_eq!(first.data().version(), 1 << 31);
    let last = map.compare_exchange_bits(first, 0, 0x7fff_ffff).unwrap();
    assert_eq!(last.data().version(), u32::MAX);
    assert_eq!(map.remove(last), Some("first".into()));
    let writer = map.try_insert_if(|_| false).unwrap();
    assert_eq!(writer.key(), last);
    assert!(map.get(last).is_none());
    drop(writer);
    let repeated = map.insert("repeated".into());
    assert_eq!(repeated, last);
    assert_eq!(map[repeated], "repeated");
    map.shrink_to_fit();
    assert_eq!(map[repeated], "repeated");
}

#[test]
fn compact_orders_free_slots_without_moving_live_values() {
    let mut map = SlotMap::<DefaultKey, u32, 2>::with_capacity(100);
    let keys: Vec<_> = (0..8)
        .map(|value| map.insert_with_link(value, value as u64 + 50))
        .collect();
    let live = map.compare_exchange_bits(keys[3], 0, 3).unwrap();
    let address = map.get(live).unwrap().0 as *const u32;
    for index in [1, 6, 0, 7] {
        map.remove(keys[index]);
    }
    let counts = (map.alloc_count(), map.free_count());
    map.compact();
    assert_eq!(map.get(live).unwrap().0 as *const u32, address);
    assert_eq!(map.get(live).unwrap().1.load(Ordering::Relaxed), 53);
    assert_eq!((map.max(), map.len()), (8, 4));
    assert_eq!((map.alloc_count(), map.free_count()), counts);
    for index in [0, 1, 6, 7] {
        let reused = map.insert(42);
        assert_eq!(
            (reused.data().index(), reused.data().version()),
            (index, 12)
        );
    }
    assert_eq!(map.insert(9).data().index(), 8);
}

#[test]
fn shrinking_preserves_keys_values_links_and_statistics() {
    let drops = Arc::new(AtomicUsize::new(0));
    let mut map = SlotMap::<DefaultKey, DropValue, 3>::with_capacity(1024);
    let keys: Vec<_> = (0..100)
        .map(|index| map.insert_with_link(DropValue(drops.clone()), index))
        .collect();
    let live = map.compare_exchange_bits(keys[40], 0, 5).unwrap();
    for (index, key) in keys.iter().enumerate() {
        if index != 40 {
            drop(map.remove(*key));
        }
    }
    let counts = (map.alloc_count(), map.free_count());
    for _ in 0..2 {
        map.shrink_to_fit();
        assert_eq!((map.max(), map.len()), (100, 1));
        assert!(map.get(live).is_some());
        assert_eq!(map.get(live).unwrap().1.load(Ordering::Relaxed), 40);
        assert_eq!(map.get_key_bits(40), Some(5));
        assert_eq!((map.alloc_count(), map.free_count()), counts);
        assert_eq!(drops.load(Ordering::SeqCst), 99);
    }
    map.shrink_to_last_occupied();
    assert_eq!((map.max(), map.len()), (41, 1));
    assert_eq!(map.iter().next().unwrap().0, live);
    assert_eq!(drops.load(Ordering::SeqCst), 99);
    for index in 0..40 {
        let key = map.insert(DropValue(drops.clone()));
        assert_eq!((key.data().index(), key.data().version()), (index, 24));
    }
    let appended = map.insert(DropValue(drops.clone()));
    assert_eq!(appended, keys[41]); // 截尾丢失历史，允许重现旧 key。
    drop(map);
    assert_eq!(drops.load(Ordering::SeqCst), 141);
}

#[test]
fn maintenance_recovers_forgotten_writer_without_reissuing_its_generation() {
    for shrink in [false, true] {
        let mut map = SlotMap::<DefaultKey, String, 2>::new();
        let writer = map.try_insert_if(|_| true).unwrap();
        let abandoned = writer.key();
        std::mem::forget(writer);
        if shrink {
            map.shrink_to_fit();
        } else {
            map.compact();
        }
        assert!(map.get(abandoned).is_none());
        let key = map.insert("recovered".into());
        assert_eq!(key.data().index(), abandoned.data().index());
        assert_eq!(key.data().version(), abandoned.data().version() + 8);
        assert_eq!((map.len(), map.alloc_count(), map.free_count()), (1, 1, 0));
    }
}

#[test]
fn empty_maintenance_and_truncation_remain_reusable() {
    let mut map = SlotMap::<DefaultKey, String>::with_capacity(4096);
    map.compact();
    map.shrink_to_fit();
    map.shrink_to_last_occupied();
    let first = map.insert("first".into());
    map.remove(first);
    map.shrink_to_fit();
    assert_eq!(map.max(), 1);
    let next = map.insert("next".into());
    assert_ne!(next, first);
    map.remove(next);
    map.shrink_to_last_occupied();
    assert_eq!((map.max(), map.len()), (0, 0));
    assert_eq!(map.insert("reset".into()), first);
}

#[test]
fn rc_and_default_growth_preserve_existing_borrows_and_writers() {
    let map = SlotMap::<DefaultKey, String, 1>::with_capacity(1);
    let key = map.insert("stable".into());
    let reference = map.get(key).unwrap().0;
    let writer = map.try_insert_if(|_| true).unwrap();
    for _ in 0..200 {
        map.insert("growth".into());
    }
    assert_eq!(reference, "stable");
    let key = writer.insert("writer".into());
    assert_eq!(map[key], "writer");
}

static ZST_DROPS: AtomicUsize = AtomicUsize::new(0);
struct Zst;
impl Drop for Zst {
    fn drop(&mut self) {
        ZST_DROPS.fetch_add(1, Ordering::SeqCst);
    }
}
#[repr(align(128))]
struct Aligned(u8);

#[test]
fn zst_small_value_and_high_alignment() {
    let mut map = SlotMap::<DefaultKey, Zst>::with_capacity(8);
    let k = map.insert(Zst);
    drop(map.remove(k));
    map.insert(Zst);
    drop(map);
    assert_eq!(ZST_DROPS.load(Ordering::SeqCst), 2);
    let mut small = SlotMap::<DefaultKey, u8>::new();
    for i in 0..100 {
        let k = small.insert(i);
        assert_eq!(small.remove(k), Some(i));
    }
    let mut aligned = SlotMap::<DefaultKey, Aligned>::new();
    let k = aligned.insert(Aligned(7));
    let reference = aligned.get(k).unwrap();
    assert_eq!(reference.0 as *const Aligned as usize % 128, 0);
    assert_eq!(aligned.remove(k).unwrap().0, 7);
}

#[test]
fn public_custom_key_identity_and_index_panics() {
    pi_key::new_key_type! { struct MessageKey; }
    let mut map = SlotMap::<MessageKey, u32>::new();
    let k = map.insert(7);
    assert_eq!(map[k], 7);
    assert_eq!(map.remove(k), Some(7));
    assert!(catch_unwind(AssertUnwindSafe(|| map[k])).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| map[k] = 9)).is_err());
    let full = SlotMap::<u64, u32>::new();
    let k = full.insert(8);
    assert_eq!(full[k], 8);
}

#[cfg(not(feature = "rc"))]
#[test]
fn parallel_insert_and_iteration_publish_complete_strings() {
    use std::sync::{atomic::AtomicBool, mpsc};
    use std::time::{Duration, Instant};
    let map = Arc::new(SlotMap::<DefaultKey, String>::with_capacity(7));
    // Keep the same concurrent protocol under interpretation without the stress volume.
    let per_writer = if cfg!(miri) { 8 } else { 500 };
    let value_len = if cfg!(miri) { 64 } else { 4096 };
    let done = AtomicBool::new(false);
    std::thread::scope(|scope| {
        let (started_tx, started_rx) = mpsc::channel();
        let (observed_tx, observed_rx) = mpsc::channel();
        let reader_map = &map;
        let reader_done = &done;
        let reader = scope.spawn(move || {
            let map = reader_map;
            let deadline = Instant::now() + Duration::from_secs(10);
            let mut observed = 0;
            let mut reported = false;
            started_tx.send(()).unwrap();
            loop {
                let mut indices = HashSet::new();
                for (k, value) in map.iter() {
                    assert!(indices.insert(k.data().index()));
                    assert_eq!(value.0.len(), value_len);
                    assert!(value.0.bytes().all(|byte| byte == b'x'));
                    assert_eq!(value.1.load(Ordering::Relaxed), 987);
                    observed += 1;
                }
                assert!(map.len() <= map.max() as usize);
                if observed > 0 && !reported {
                    observed_tx.send(()).unwrap();
                    reported = true;
                }
                // Relaxed termination cannot publish writer data to this reader.
                // A completed scan and nonzero observation are mandatory even
                // if all writers finished before the reader was rescheduled.
                if observed > 0 && reader_done.load(Ordering::Relaxed) {
                    break;
                }
                assert!(Instant::now() < deadline, "publication reader timed out");
                std::thread::yield_now();
            }
            assert!(observed > 0);
        });
        started_rx.recv_timeout(Duration::from_secs(10)).unwrap();
        let writers: Vec<_> = (0..4)
            .map(|_| {
                scope.spawn(|| {
                    (0..per_writer)
                        .map(|_| map.insert_with_link("x".repeat(value_len), 987))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        let mut unique = HashSet::new();
        for writer in writers {
            for k in writer.join().unwrap() {
                assert!(unique.insert(k));
            }
        }
        let observation = observed_rx.recv_timeout(Duration::from_secs(10));
        done.store(true, Ordering::Relaxed);
        reader.join().unwrap();
        observation.unwrap();
        assert_eq!(unique.len(), 4 * per_writer);
    });
    assert_eq!(
        (map.len(), map.max() as usize),
        (4 * per_writer, 4 * per_writer)
    );
    assert_eq!(map.iter().count(), 4 * per_writer);
}
