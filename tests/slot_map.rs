use pi_slot::{DefaultKey, Key, KeyData, ShareU64, SlotMap};
use std::collections::HashSet;
use std::mem::size_of;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

fn key(index: u32, version: u32) -> DefaultKey {
    KeyData::from_ffi((u64::from(version) << 32) | u64::from(index)).into()
}

#[test]
fn pi_key_preserves_even_live_and_full_generation_encoding() {
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
fn default_build_has_atomic_thread_traits() {
    fn assert_traits<T: Send + Sync>() {}
    assert_traits::<SlotMap<DefaultKey, String>>();
}

#[cfg(feature = "rc")]
#[test]
fn rc_build_has_no_thread_traits() {
    // 若存在目标 trait，两种实现令推导歧义，从而编译失败。
    trait NotSend<A> {
        fn check() {}
    }
    impl<T: ?Sized> NotSend<()> for T {}
    struct SendMarker;
    impl<T: ?Sized + Send> NotSend<SendMarker> for T {}
    let _ = <SlotMap<DefaultKey, String> as NotSend<_>>::check;
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
    assert_eq!(a.data().version(), 2);
    map[a].0.push('!');
    map.get_mut(b).unwrap().0.push('?');
    assert_eq!(map.replace(a, "new".into()), Ok("a!".into()));
    assert_eq!(map.remove(a), Some("new".into()));
    assert_eq!(map.remove(a), None);
    let c = map.insert("reuse".into());
    assert_eq!(c.data().index(), a.data().index());
    assert_eq!(c.data().version(), 4);
    assert_eq!((map.len(), map.max()), (2, 2));
    assert!(map.get(a).is_none());
    for invalid in [
        DefaultKey::default(),
        key(0, 0),
        key(0, 1),
        key(0, 3),
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
    assert_eq!(map[plain].1.load(Ordering::Relaxed), 0);
    assert_eq!(map[alias].1.load(Ordering::Relaxed), 0);
    let a = map.insert_with_link("a".into(), u64::MAX);
    let b = map.set_with_link("b".into(), 23);
    let address = &map[a].1 as *const ShareU64;
    map.get(a).unwrap().1.store(41, Ordering::Relaxed);
    assert_eq!(map.replace(a, "a2".into()), Ok("a".into()));
    assert_eq!(map[a].1.load(Ordering::Relaxed), 41);
    assert_eq!(
        map.replace_with_link(a, "a3".into(), 42),
        Ok(("a2".into(), 41))
    );
    assert_eq!(address, &map[a].1 as *const ShareU64);
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
fn exclusive_tuple_replacement_keeps_free_link_initialized() {
    let drops = Arc::new(AtomicUsize::new(0));
    let mut map = SlotMap::<DefaultKey, DropValue>::new();
    let a = map.insert(DropValue(drops.clone()));
    let b = map.insert(DropValue(drops.clone()));
    let old = std::mem::replace(
        map.get_mut(a).unwrap(),
        (DropValue(drops.clone()), ShareU64::new(19)),
    );
    drop(old);
    map[b].1 = ShareU64::new(29);
    for (_, tuple) in map.iter_mut() {
        tuple.1 = ShareU64::new(39);
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
    assert_eq!(map[reused].1.load(Ordering::Relaxed), 49);
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

thread_local! {
    static KEY_CALLBACK: std::cell::RefCell<Option<(u8, Box<dyn FnOnce()>)>> = const { std::cell::RefCell::new(None) };
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
            (0, 4)
        );
        assert_eq!(map.iter().count(), 2);
        drop(map);
        assert_eq!(drops.load(Ordering::SeqCst), 3);
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
    assert_eq!(map[key].0, (9, 9));
    assert_eq!(map[key].1.load(Ordering::Relaxed), u64::MAX);
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
    let mut iterator = map.iter();
    let end = map.max();
    map.insert("outside".into());
    assert!(iterator.all(|(k, _)| k.data().index() < end));
    // 独占表，键有效。
    unsafe {
        map.get_unchecked_mut(keys[0]).0.push('?');
    }
    assert_eq!(map[keys[0]].0, "0!?");
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
    assert_eq!(&reference.0 as *const Aligned as usize % 128, 0);
    assert_eq!(aligned.remove(k).unwrap().0, 7);
}

#[test]
fn memory_counts_allocated_segments_not_logical_len() {
    let empty = SlotMap::<DefaultKey, u64>::new();
    assert_eq!(empty.mem_size(), size_of::<SlotMap<DefaultKey, u64>>());
    let preallocated = SlotMap::<DefaultKey, u64>::with_capacity(13);
    let baseline = preallocated.mem_size();
    assert!(baseline > empty.mem_size());
    preallocated.insert(1);
    assert_eq!(preallocated.mem_size(), baseline);
    empty.insert(1);
    assert!(empty.mem_size() > size_of::<SlotMap<DefaultKey, u64>>());
}

#[test]
fn public_custom_key_identity_and_index_panics() {
    pi_key::new_key_type! { struct MessageKey; }
    let mut map = SlotMap::<MessageKey, u32>::new();
    let k = map.insert(7);
    assert_eq!(map[k].0, 7);
    assert_eq!(map.remove(k), Some(7));
    assert!(catch_unwind(AssertUnwindSafe(|| map[k].0)).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| map[k].0 = 9)).is_err());
    let full = SlotMap::<u64, u32>::new();
    let k = full.insert(8);
    assert_eq!(full[k].0, 8);
}

#[cfg(not(feature = "rc"))]
#[test]
fn parallel_insert_and_iteration_publish_complete_strings() {
    use std::sync::atomic::AtomicBool;
    let map = Arc::new(SlotMap::<DefaultKey, String>::with_capacity(7));
    // Keep the same concurrent protocol under interpretation without the stress volume.
    let per_writer = if cfg!(miri) { 8 } else { 500 };
    let value_len = if cfg!(miri) { 64 } else { 4096 };
    let done = AtomicBool::new(false);
    std::thread::scope(|scope| {
        let reader = scope.spawn(|| {
            while !done.load(Ordering::Acquire) {
                let mut indices = HashSet::new();
                for (k, value) in map.iter() {
                    assert!(indices.insert(k.data().index()));
                    assert_eq!(value.0.len(), value_len);
                    assert!(value.0.bytes().all(|byte| byte == b'x'));
                    assert_eq!(value.1.load(Ordering::Relaxed), 987);
                }
                let _ = map.mem_size();
                assert!(map.len() <= map.max() as usize);
            }
        });
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
        done.store(true, Ordering::Release);
        reader.join().unwrap();
        assert_eq!(unique.len(), 4 * per_writer);
    });
    assert_eq!(
        (map.len(), map.max() as usize),
        (4 * per_writer, 4 * per_writer)
    );
    assert_eq!(map.iter().count(), 4 * per_writer);
}
