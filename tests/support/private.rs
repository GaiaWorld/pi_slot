// Private protocol boundaries cannot be exercised through valid public keys.
// @inline-test-exception: externally stored tests for private FREE/CAS invariants.
use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn generation_exhaustion_never_wraps_or_reuses() {
    let mut map = SlotMap::<DefaultKey, String>::new();
    let first = map.insert("last".into());
    map.slots
        .get(0)
        .unwrap()
        .version
        .store(MAX_LIVE_VERSION - 2, Ordering::Release);
    let penultimate = checked_key(0, MAX_LIVE_VERSION - 2);
    assert_eq!(map.remove(penultimate), Some("last".into()));
    let last = map.insert("last".into());
    assert_eq!(last.data().version(), MAX_LIVE_VERSION);
    assert_eq!(map.remove(last), Some("last".into()));
    #[cfg(feature = "stats")]
    assert_eq!((map.alloc_count(), map.free_count(), map.len()), (2, 2, 0));
    let exhausted = map.slots.get(0).unwrap();
    assert_eq!(
        exhausted.version.load(Ordering::Relaxed),
        MAX_LIVE_VERSION + 1
    );
    assert!(map.get(last).is_none());
    assert!(map.get(first).is_none());
    assert_eq!(
        map.free_head.load(Ordering::Relaxed),
        encode(0, MAX_LIVE_VERSION + 1)
    );
    let next = map.insert("fresh".into());
    assert_eq!((next.data().index(), next.data().version()), (1, 2));
    assert_eq!((map.len(), map.max()), (1, 2));
    #[cfg(feature = "stats")]
    assert_eq!((map.alloc_count(), map.free_count()), (3, 2));
    assert_eq!(map.free_head.load(Ordering::Relaxed), NULL);
}

#[cfg(feature = "stats")]
#[test]
fn cumulative_counters_wrap_without_losing_quiescent_difference() {
    let mut map = SlotMap::<DefaultKey, String>::new();
    map.alloc.store(usize::MAX, Ordering::Relaxed);
    map.free.store(usize::MAX, Ordering::Relaxed);
    let writer = map.try_insert_if(|_| true).unwrap();
    assert_eq!(
        (map.len(), map.alloc_count(), map.free_count()),
        (0, usize::MAX, usize::MAX)
    );
    let key = writer.insert("alive".into());
    #[cfg(feature = "stats")]
    assert_eq!((map.alloc_count(), map.len()), (0, 1));
    assert_eq!(map.remove(key), Some("alive".into()));
    #[cfg(feature = "stats")]
    assert_eq!((map.free_count(), map.len()), (0, 0));
}

#[test]
fn index_saturates_but_free_reuse_remains_available() {
    let mut map = SlotMap::<DefaultKey, String>::new();
    let key = map.insert("old".into());
    map.remove(key);
    map.next_index.store(MAX_ENTRIES as u32, Ordering::Relaxed);
    let reused = map.insert("reuse".into());
    assert_eq!(reused.data().index(), 0);
    assert!(catch_unwind(AssertUnwindSafe(|| map.insert("full".into()))).is_err());
    assert_eq!(map[reused], "reuse");
    assert_eq!(map.max(), MAX_ENTRIES as u32);
}

#[test]
fn stale_pop_reads_arbitrary_live_link_but_cannot_publish_old_id() {
    let map = SlotMap::<DefaultKey, u32>::new();
    let old = map.insert(7);
    // No public reference or iterator survives removal. The retained Slot/link
    // below represents only the internal late observer, not a user borrow.
    unsafe {
        assert_eq!(map.remove_shared(old), Some(7));
    }
    let stale = map.free_head.load(Ordering::Acquire);
    let slot = map.slots.get(stale as u32 as usize).unwrap();
    let link_address = &slot.link as *const ShareU64;
    let current = map.insert_with_link(8, 0xdead_beef_ffff_fffe);
    assert_eq!(link_address, map.get(current).unwrap().1 as *const ShareU64);
    assert_eq!(slot.link.load(Ordering::Relaxed), 0xdead_beef_ffff_fffe);
    let arbitrary = slot.link.load(Ordering::Relaxed);
    assert_eq!(arbitrary, 0xdead_beef_ffff_fffe);
    assert!(map
        .free_head
        .compare_exchange(stale, arbitrary, Ordering::AcqRel, Ordering::Acquire)
        .is_err());
    assert_eq!(map.free_head.load(Ordering::Acquire), NULL);
    unsafe {
        assert_eq!(map.remove_shared(current), Some(8));
    }
    let next_id = map.free_head.load(Ordering::Acquire);
    assert_eq!(next_id as u32, stale as u32);
    assert_ne!(next_id, stale);
    assert!(map
        .free_head
        .compare_exchange(stale, arbitrary, Ordering::AcqRel, Ordering::Acquire)
        .is_err());
    let fresh = map.insert(9);
    assert_eq!(fresh.data().version(), 6);
    assert_eq!(map[fresh], 9);
}

#[test]
fn rollback_never_republishes_detached_free_id() {
    let map = SlotMap::<DefaultKey, ()>::new();
    let key = map.insert(());
    unsafe {
        map.remove_shared(key);
    }
    let old = map.free_head.load(Ordering::Acquire);
    let candidate = map.claim(|_| true).unwrap();
    assert_eq!(map.free_head.load(Ordering::Acquire), NULL);
    drop(candidate);
    assert_eq!(map.free_head.load(Ordering::Acquire), encode(0, 5));
    assert!(map
        .free_head
        .compare_exchange(old, NULL, Ordering::AcqRel, Ordering::Acquire)
        .is_err());
    assert_eq!(map.insert(()).data().version(), 6);
}

#[test]
fn writer_rollback_consumes_free_id_without_changing_statistics() {
    let map = SlotMap::<DefaultKey, ()>::new();
    let key = map.insert(());
    unsafe {
        map.remove_shared(key);
    }
    let old = map.free_head.load(Ordering::Acquire);
    let writer = map.try_insert_if(|_| panic!("FREE")).unwrap();
    assert_eq!(map.len(), 0);
    #[cfg(feature = "stats")]
    assert_eq!((map.alloc_count(), map.free_count()), (1, 1));
    drop(writer);
    assert_eq!(map.len(), 0);
    assert_eq!(map.free_head.load(Ordering::Acquire), encode(0, 5));
    assert!(map
        .free_head
        .compare_exchange(old, NULL, Ordering::AcqRel, Ordering::Acquire)
        .is_err());
    assert_eq!(
        map.try_insert_if(|_| false)
            .unwrap()
            .insert(())
            .data()
            .version(),
        6
    );
}

#[test]
fn reservation_reports_library_index_exhaustion_without_panic() {
    let map = SlotMap::<DefaultKey, ()>::new();
    map.next_index.store(MAX_ENTRIES as u32, Ordering::Relaxed);
    assert!(matches!(
        map.try_insert_if(|_| panic!("exhausted")),
        Err(ReserveError::IndexExhausted)
    ));
    assert_eq!(map.len(), 0);
}

#[test]
fn allocation_exhaustion_returns_original_payload_and_link() {
    let map = SlotMap::<DefaultKey, String>::new();
    map.next_index.store(MAX_ENTRIES as u32, Ordering::Relaxed);
    assert_eq!(map.alloc("payload".into()), Err("payload".into()));
    assert_eq!(
        map.alloc_with_link("linked".into(), u64::MAX),
        Err(("linked".into(), u64::MAX))
    );
    assert_eq!(map.max(), MAX_ENTRIES as u32);
    #[cfg(feature = "stats")]
    assert_eq!((map.alloc_count(), map.free_count()), (0, 0));
}

#[test]
fn last_generation_empty_writer_rollback_is_never_reused() {
    let map = SlotMap::<DefaultKey, ()>::new();
    let key = map.insert(());
    unsafe {
        map.remove_shared(key);
    }
    let slot = map.slots.get(0).unwrap();
    slot.version.store(MAX_LIVE_VERSION - 1, Ordering::Relaxed);
    map.free_head
        .store(encode(0, MAX_LIVE_VERSION - 1), Ordering::Relaxed);
    let writer = map.try_insert_if(|_| false).unwrap();
    drop(writer);
    assert_eq!(slot.version.load(Ordering::Relaxed), MAX_LIVE_VERSION + 1);
    #[cfg(feature = "stats")]
    assert_eq!((map.alloc_count(), map.free_count(), map.len()), (1, 1, 0));
    let fresh = map.insert(());
    assert_eq!((fresh.data().index(), fresh.data().version()), (1, 2));
}

#[cfg(not(feature = "rc"))]
#[test]
fn retry_error_comes_from_last_fetch_update_callback() {
    use std::sync::Barrier;

    let map = SlotMap::<DefaultKey, u32>::new();
    let barrier = Barrier::new(2);
    std::thread::scope(|scope| {
        let worker = scope.spawn(|| {
            let mut calls = 0;
            let result = map.try_insert_if(|index| {
                calls += 1;
                if calls == 1 {
                    assert_eq!(index, 0);
                    barrier.wait();
                    barrier.wait();
                    true
                } else {
                    assert_eq!(index, 1);
                    false
                }
            });
            assert!(matches!(result, Err(ReserveError::IndexRejected)));
            assert_eq!(calls, 2);
        });
        barrier.wait();
        let key = map.insert(17);
        assert_eq!(key.data().index(), 0);
        barrier.wait();
        worker.join().unwrap();
    });
    assert_eq!((map.max(), map.len()), (1, 1));
}

#[test]
fn committed_candidate_zero_does_not_recycle_live_slot() {
    let map = SlotMap::<DefaultKey, String>::new();
    let key = map.try_insert_if(|_| true).unwrap().insert("live".into());
    assert_eq!(map.free_head.load(Ordering::Relaxed), NULL);
    assert_eq!(map.slots.get(0).unwrap().version.load(Ordering::Relaxed), 2);
    assert_eq!(map[key], "live");
}
