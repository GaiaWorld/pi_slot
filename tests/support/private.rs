// Private protocol boundaries cannot be exercised through valid public keys.
// @inline-test-exception: externally stored tests for private FREE/CAS invariants.
use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn generation_exhaustion_retires_without_wrap() {
    let mut map = SlotMap::<DefaultKey, String>::new();
    let first = map.insert("last".into());
    map.slots
        .get(0)
        .unwrap()
        .version
        .store(MAX_LIVE - 2, Ordering::Release);
    let penultimate = checked_key(0, MAX_LIVE - 2);
    assert_eq!(map.remove(penultimate), Some("last".into()));
    let last = map.insert("last".into());
    assert_eq!(last.data().version(), MAX_LIVE);
    assert_eq!(map.remove(last), Some("last".into()));
    assert!(map.get(first).is_none());
    assert_eq!(map.head.load(Ordering::Relaxed), NULL_FULL);
    let next = map.insert("fresh".into());
    assert_eq!((next.data().index(), next.data().version()), (1, 2));
    assert_eq!((map.len(), map.max()), (1, 2));
}

#[test]
fn counter_exhaustion_rolls_back_empty_candidate_and_consumes_generation() {
    let mut map = SlotMap::<DefaultKey, String>::new();
    let key = map.insert("alive".into());
    map.count.store(u64::MAX, Ordering::Relaxed);
    assert!(catch_unwind(AssertUnwindSafe(|| map.insert("rejected".into()))).is_err());
    assert_eq!(map[key].0, "alive");
    assert_eq!(map.max(), 2);
    assert_eq!(map.head.load(Ordering::Acquire), full_id(1, 3));
    assert!(!live(
        map.slots.get(1).unwrap().version.load(Ordering::Relaxed)
    ));
    map.count.store(1, Ordering::Relaxed);
    let reused = map.insert("reuse".into());
    assert_eq!((reused.data().index(), reused.data().version()), (1, 4));
    assert_eq!(map.remove(key), Some("alive".into()));
    assert_eq!(map.remove(reused), Some("reuse".into()));
    assert_eq!(map.len(), 0);
}

#[test]
fn index_saturates_but_free_reuse_remains_available() {
    let mut map = SlotMap::<DefaultKey, String>::new();
    let key = map.insert("old".into());
    map.remove(key);
    map.nextindex.store(MAX_SLOTS, Ordering::Relaxed);
    let reused = map.insert("reuse".into());
    assert_eq!(reused.data().index(), 0);
    assert!(catch_unwind(AssertUnwindSafe(|| map.insert("full".into()))).is_err());
    assert_eq!(map[reused].0, "reuse");
    assert_eq!(map.max(), MAX_SLOTS);
}

#[test]
fn stale_pop_reads_arbitrary_live_link_but_cannot_publish_it() {
    let map = SlotMap::<DefaultKey, u32>::new();
    let old = map.insert(7);
    // No public reference or iterator survives removal. The retained Slot/link
    // below represents only the internal late observer, not a user borrow.
    unsafe {
        assert_eq!(map.remove_shared(old), Some(7));
    }
    let stale = map.head.load(Ordering::Acquire);
    let slot = map.slots.get(stale as u32 as usize).unwrap();
    let link_address = slot.link() as *const ShareU64;
    let current = map.insert_with_link(8, 0xdead_beef_ffff_fffe);
    assert_eq!(link_address, &map[current].1 as *const ShareU64);
    let arbitrary = slot.link().load(Ordering::Relaxed);
    assert_eq!(arbitrary, 0xdead_beef_ffff_fffe);
    assert!(map
        .head
        .compare_exchange(stale, arbitrary, Ordering::AcqRel, Ordering::Acquire)
        .is_err());
    assert_eq!(map.head.load(Ordering::Acquire), NULL_FULL);
    unsafe {
        assert_eq!(map.remove_shared(current), Some(8));
    }
    let next_id = map.head.load(Ordering::Acquire);
    assert_eq!(next_id as u32, stale as u32);
    assert_ne!(next_id, stale);
    assert!(map
        .head
        .compare_exchange(stale, arbitrary, Ordering::AcqRel, Ordering::Acquire)
        .is_err());
    let fresh = map.insert(9);
    assert_eq!(fresh.data().version(), 6);
    assert_eq!(map[fresh].0, 9);
}

#[test]
fn rollback_never_republishes_detached_free_id() {
    let map = SlotMap::<DefaultKey, ()>::new();
    let key = map.insert(());
    unsafe {
        map.remove_shared(key);
    }
    let old = map.head.load(Ordering::Acquire);
    let candidate = map.claim();
    assert_eq!(map.head.load(Ordering::Acquire), NULL_FULL);
    drop(candidate);
    assert_eq!(map.head.load(Ordering::Acquire), full_id(0, 5));
    assert!(map
        .head
        .compare_exchange(old, NULL_FULL, Ordering::AcqRel, Ordering::Acquire)
        .is_err());
    assert_eq!(map.insert(()).data().version(), 6);
}

#[test]
fn slot_uses_real_tuple_layout_with_only_version_metadata() {
    fn check<T>() {
        let slot = Slot::<T>::default();
        let base = slot.entry_ptr();
        let link = slot.link() as *const ShareU64 as usize;
        assert_eq!(link - base as usize, std::mem::offset_of!((T, ShareU64), 1));
        assert_eq!(
            slot.value_ptr() as usize - base as usize,
            std::mem::offset_of!((T, ShareU64), 0)
        );
        assert_eq!(link % std::mem::align_of::<ShareU64>(), 0);
        assert_eq!(slot.link().load(Ordering::Relaxed), NULL_FULL);
        let align = std::mem::align_of::<Slot<T>>();
        let expected = (size_of::<(T, ShareU64)>() + size_of::<ShareU32>()).next_multiple_of(align);
        assert_eq!(size_of::<Slot<T>>(), expected);
        assert_eq!(
            size_of::<MaybeUninit<(T, ShareU64)>>(),
            size_of::<(T, ShareU64)>()
        );
    }
    check::<()>();
    check::<u8>();
    check::<u32>();
    check::<u64>();
    check::<String>();
    #[repr(align(128))]
    struct Aligned;
    check::<Aligned>();
}
