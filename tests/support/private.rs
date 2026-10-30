// Private protocol boundaries cannot be exercised through valid public keys.
#[test]
fn shrink_releases_preallocated_storage_and_preserves_unallocated_holes() {
    let mut map = SlotMap::<DefaultKey, String, 2>::with_capacity(4096);
    let key = map.insert_with_link("retained".into(), 77);
    map.shrink_to_fit();
    assert_eq!(map.slots.contiguous_len(), 1);
    assert_eq!(map.get(key).unwrap().0, "retained");
    assert_eq!(map.get(key).unwrap().1.load(Ordering::Relaxed), 77);
    map.remove(key);
    map.shrink_to_last_occupied();
    assert_eq!(map.slots.contiguous_len(), 0);
    assert!(map.slots.get(0).is_none());

    // 模拟高水位已认领而中间桶尚未分配；读取迭代必须越过缺失桶。
    let mut sparse = SlotMap::<DefaultKey, String>::new();
    sparse.next_index.store(32, Ordering::Relaxed);
    let live = sparse.insert("later bucket".into());
    assert!(sparse.slots.get(0).is_none());
    assert_eq!(sparse.iter().next().unwrap().0, live);
    sparse.shrink_to_fit();
    assert_eq!(sparse[live], "later bucket");
    assert_eq!(sparse.insert("hole".into()).data().index(), 0);
}
// @inline-test-exception: externally stored tests for private FREE/CAS invariants.
use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn guarded_zero_business_bits_last_generation_claim_release_remove_wraps() {
    // Guarded N=0 uses SlotMap N=1: CLAIMED=1, LIVE=2. Inject only
    // metadata of an initialized, unborrowed LIVE value in a quiescent map.
    // This avoids 2^30 public remove/reuse cycles and never fabricates a token.
    let map = SlotMap::<DefaultKey, String, 1>::new();
    let first = map.insert_with_bits(0, 99, |_| "last generation".into());
    let last_version = u32::MAX - 1;
    map.slots
        .get(0)
        .unwrap()
        .version
        .store(last_version, Ordering::Release);
    let last = KeyData::new(0, last_version);
    assert!(matches!(
        map.claim_metadata(first, 0, 1),
        Err(ClaimMetadataError::Stale)
    ));
    let mut token = map.claim_metadata(last, 0, 1).unwrap();
    assert!(matches!(
        map.claim_metadata(last, 0, 1),
        Err(ClaimMetadataError::Claimed)
    ));
    // SAFETY: this is the unique valid claim; all value borrows end before release.
    unsafe {
        token.value_mut().push('!');
    }
    assert_eq!(unsafe { token.value() }, "last generation!");
    assert_eq!(token.link(), 99);
    unsafe {
        token.release(0);
    }
    assert_eq!(
        map.slots.get(0).unwrap().version.load(Ordering::Acquire),
        last_version
    );
    let token = map.claim_metadata(last, 0, 1).unwrap();
    // SAFETY: same map, live claim, no outstanding value references.
    assert_eq!(
        unsafe { token.remove(&map) },
        ("last generation!".into(), 99)
    );
    let free_id = map.free_head.load(Ordering::Acquire);
    assert_eq!(free_id as u32, 0);
    // FREE may retain low reserved history; only LIVE/generation must wrap.
    assert_eq!((free_id >> 32) as u32 & !1, 0);
    assert_eq!((map.len(), map.alloc_count(), map.free_count()), (0, 1, 1));
    assert!(matches!(
        map.claim_metadata(last, 0, 1),
        Err(ClaimMetadataError::Stale)
    ));
    let repeated = map.insert_with_bits(0, 17, |_| "new cycle".into());
    assert_eq!(repeated, first);
    let token = map.claim_metadata(repeated, 0, 1).unwrap();
    assert_eq!(unsafe { token.value() }, "new cycle");
    assert_eq!(token.link(), 17);
    unsafe {
        token.release(0);
    }
    assert_eq!((map.len(), map.alloc_count(), map.free_count()), (1, 2, 1));
}

#[test]
fn generation_wraps_and_reuses_the_same_slot() {
    let mut map = SlotMap::<DefaultKey, String>::new();
    let first = map.insert("last".into());
    map.slots
        .get(0)
        .unwrap()
        .version
        .store(u32::MAX, Ordering::Release);
    let last = checked_key(0, u32::MAX);
    assert_eq!(map.remove(last), Some("last".into()));
    assert_eq!(map.free_head.load(Ordering::Relaxed), encode(0, 0));
    assert!(map.get(last).is_none());
    let next = map.insert("fresh".into());
    assert_eq!(next, first);
    assert_eq!(map[next], "fresh");
    assert_eq!((map.len(), map.max()), (1, 1));
    assert_eq!((map.alloc_count(), map.free_count()), (2, 1));
}

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
    assert_eq!((map.alloc_count(), map.len()), (0, 1));
    assert_eq!(map.remove(key), Some("alive".into()));
    assert_eq!((map.free_count(), map.len()), (0, 0));
}

#[test]
fn high_water_mark_does_not_imply_slot_is_allocated() {
    let map = SlotMap::<DefaultKey, u32>::new();
    // A successful index claim advances next_index before load_alloc_ptr
    // allocates the slot. The same state can be observed during shared reads.
    map.next_index.store(1, Ordering::Release);
    assert!(map.slots.get(0).is_none());
    assert!(map.get(checked_key(0, 2)).is_none());
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
    assert_eq!(fresh.data().version(), 5);
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
    assert_eq!(map.free_head.load(Ordering::Acquire), encode(0, 4));
    assert!(map
        .free_head
        .compare_exchange(old, NULL, Ordering::AcqRel, Ordering::Acquire)
        .is_err());
    assert_eq!(map.insert(()).data().version(), 5);
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
    assert_eq!((map.alloc_count(), map.free_count()), (1, 1));
    drop(writer);
    assert_eq!(map.len(), 0);
    assert_eq!(map.free_head.load(Ordering::Acquire), encode(0, 4));
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
        5
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
    assert_eq!((map.alloc_count(), map.free_count()), (0, 0));
}

#[test]
fn last_generation_writer_rollback_wraps_and_remains_reusable() {
    let map = SlotMap::<DefaultKey, ()>::new();
    let key = map.insert(());
    unsafe {
        map.remove_shared(key);
    }
    let slot = map.slots.get(0).unwrap();
    slot.version.store(u32::MAX - 1, Ordering::Relaxed);
    map.free_head
        .store(encode(0, u32::MAX - 1), Ordering::Relaxed);
    let writer = map.try_insert_if(|_| false).unwrap();
    assert_eq!(writer.key().data().version(), u32::MAX);
    drop(writer);
    assert_eq!(slot.version.load(Ordering::Relaxed), 0);
    assert_eq!((map.alloc_count(), map.free_count(), map.len()), (1, 1, 0));
    let fresh = map.insert(());
    assert_eq!((fresh.data().index(), fresh.data().version()), (0, 1));
}

#[cfg(not(feature = "rc"))]
#[test]
fn retry_error_comes_from_last_fetch_update_callback() {
    use std::sync::mpsc;
    use std::time::Duration;

    let map = SlotMap::<DefaultKey, u32>::new();
    std::thread::scope(|scope| {
        let (arrived_tx, arrived_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let worker_map = &map;
        let worker = scope.spawn(move || {
            let mut indices = Vec::new();
            let result = worker_map.try_insert_if(|index| {
                indices.push(index);
                if indices.len() == 1 {
                    arrived_tx.send(()).unwrap();
                    release_rx.recv_timeout(Duration::from_secs(10)).unwrap();
                    true
                } else {
                    false
                }
            });
            (result.map(|writer| writer.insert(99)), indices)
        });
        let arrived = arrived_rx.recv_timeout(Duration::from_secs(10));
        // If insertion unwinds the sender is dropped and the worker exits;
        // it cannot remain stranded at a second barrier.
        let inserted = catch_unwind(AssertUnwindSafe(|| map.insert(17)));
        let _ = release_tx.send(());
        let joined = worker.join();
        arrived.unwrap();
        assert_eq!(inserted.unwrap().data().index(), 0);
        let (result, indices) = joined.unwrap();
        assert!(matches!(result, Err(ReserveError::IndexRejected)));
        assert_eq!(indices.len(), 2);
        assert_eq!(indices, [0, 1]);
    });
    assert_eq!((map.max(), map.len()), (1, 1));
}

#[test]
fn committed_candidate_marker_does_not_recycle_live_slot() {
    let map = SlotMap::<DefaultKey, String>::new();
    let key = map.try_insert_if(|_| true).unwrap().insert("live".into());
    assert_eq!(map.free_head.load(Ordering::Relaxed), NULL);
    assert_eq!(map.slots.get(0).unwrap().version.load(Ordering::Relaxed), 1);
    assert_eq!(map[key], "live");
}
