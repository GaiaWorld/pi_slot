//! 槽表行为实现；公共契约与核心流程单源位于 slotmap.rs。
use super::*;

#[cfg(test)]
#[path = "slotmap_inner_test.rs"]
mod tests;

pub(super) fn writer_key<'a, K: Key, T, const N: u32>(writer: &SlotWriter<'a, K, T, N>) -> K {
    writer.key
}

pub(super) fn writer_insert<'a, K: Key, T, const N: u32>(
    writer: SlotWriter<'a, K, T, N>,
    value: T,
) -> K {
    writer.insert_with_link(value, 0)
}

pub(super) fn writer_insert_with_link<'a, K: Key, T, const N: u32>(
    mut writer: SlotWriter<'a, K, T, N>,
    value: T,
    link: u64,
) -> K {
    // SAFETY: candidate exclusively owns uninitialized T, all callbacks done.
    unsafe { ptr::write(writer.candidate.slot.value_ptr(), value) };
    writer.candidate.slot.link.store(link, Ordering::Relaxed);
    // 先计数再发布 LIVE，删除方只有观察到 LIVE 才能递增 free。
    writer.candidate.map.alloc.fetch_add(1, Ordering::SeqCst);
    writer
        .candidate
        .slot
        .version
        .store(writer.candidate.version, Ordering::Release);
    writer.candidate.version = 0;
    writer.key
}

pub(super) fn candidate_drop<'a, K: Key, T, const N: u32>(candidate: &mut Candidate<'a, K, T, N>) {
    if candidate.version != 0 {
        candidate
            .slot
            .version
            .store(candidate.version.wrapping_add(1u32 << N), Ordering::Release);
        candidate.map.push_free(candidate.index, candidate.slot);
    }
}

pub(super) fn map_default<'a, K: Key, T, const N: u32>() -> SlotMap<K, T, N> {
    SlotMap::<K, T, N>::new()
}

pub(super) fn map_drop<'a, K: Key, T, const N: u32>(map: &mut SlotMap<K, T, N>) {
    let mut first_panic = None;
    for segment in map.slots.segments(0..MAX_ENTRIES + 1) {
        for slot in segment {
            if !live::<N>(slot.version.fetch_and(!(1u32 << N), Ordering::Relaxed)) {
                continue;
            }
            // SAFETY: exclusive final owner; revoke LIVE before moving T out.
            let value = unsafe { ptr::read(slot.value_ptr()) };
            if let Err(payload) =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(value)))
            {
                if first_panic.is_none() {
                    first_panic = Some(payload);
                } else {
                    std::mem::forget(payload);
                }
            }
        }
    }
    // All slot versions are non-LIVE; normal field drop cannot drop T twice.
    if let Some(payload) = first_panic {
        std::panic::resume_unwind(payload);
    }
}

pub(super) fn map_new<'a, K: Key, T, const N: u32>() -> SlotMap<K, T, N> {
    SlotMap::<K, T, N>::with_capacity(0)
}

pub(super) fn map_with_capacity<'a, K: Key, T, const N: u32>(capacity: usize) -> SlotMap<K, T, N> {
    assert!(N < 32, "reserved version bits must be less than 32");
    assert!(
        capacity <= MAX_ENTRIES,
        "SlotMap capacity exceeds index limit"
    );
    SlotMap {
        free_head: CachePadded::new(ShareU64::new(NULL)),
        slots: Arr::with_capacity(capacity),
        alloc: CachePadded::new(ShareUsize::new(0)),
        free: CachePadded::new(ShareUsize::new(0)),
        next_index: ShareU32::new(0),
        key_type: PhantomData,
    }
}

pub(super) fn map_pop_free<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> Option<u32> {
    loop {
        let head = map.free_head.load(Ordering::Acquire);
        if head == NULL {
            return None;
        }
        #[cfg(test)]
        tests::pause(tests::Stage::PopHead, head);
        let index = head as u32;
        let slot = map.slots.get(index as usize).expect("FREE slot allocated");
        // A late observer may read arbitrary LIVE user bits. Never dereference
        // next or validate its target before the full-id CAS succeeds. Every
        // detached id is consumed; this excludes ABA only before a full version cycle.
        let next = slot.link.load(Ordering::Relaxed);
        #[cfg(test)]
        tests::pause(tests::Stage::PopLink, next);
        if map
            .free_head
            .compare_exchange(head, next, Ordering::AcqRel, Ordering::Acquire)
            .is_ok()
        {
            return Some(index);
        }
        #[cfg(test)]
        tests::pause(tests::Stage::PopCasFailed, head);
    }
}

pub(super) fn map_claim<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    mut predicate: impl FnMut(u32) -> bool,
) -> Result<Candidate<'a, K, T, N>, ReserveError> {
    if let Some(index) = map.pop_free() {
        let slot = map.slots.get(index as usize).expect("popped FREE slot");
        let version = slot.version.load(Ordering::Relaxed);
        let occupied = version.wrapping_add(1u32 << N);
        // 提前消耗预定代际，维护时回收 forget 的 writer 也不会立即重发其 key。
        slot.version
            .store(occupied.wrapping_add(1u32 << N), Ordering::Relaxed);
        return Ok(Candidate {
            map,
            slot,
            index,
            version: occupied,
        });
    }
    let result = map
        .next_index
        .try_update(Ordering::AcqRel, Ordering::Acquire, |index| {
            if index as usize >= MAX_ENTRIES {
                return None;
            }
            if !predicate(index) {
                return None;
            }
            // The rc backend updates from a saved value after the callback;
            // reentry must not overwrite an index claimed by the callback.
            #[cfg(feature = "rc")]
            if map.next_index.load(Ordering::Relaxed) != index {
                return None;
            }
            Some(index + 1)
        });
    match result {
        Ok(index) => {
            // SAFETY: next_index 成功更新赋予当前调用对该新索引的唯一认领权；
            // 回调仅检查准入，不分配槽。load_alloc_ptr 为该索引分配稳定槽并返回有效指针，
            // 表的共享借用保证存储存活，因此这里可解引用取得槽引用。
            let slot = unsafe { &*map.slots.load_alloc_ptr(index as usize) };
            slot.version
                .store(2u32.wrapping_mul(1u32 << N), Ordering::Relaxed);
            Ok(Candidate {
                map,
                slot,
                index,
                version: 1u32 << N,
            })
        }
        Err(index) if index as usize >= MAX_ENTRIES => Err(ReserveError::IndexExhausted),
        Err(_) => Err(ReserveError::IndexRejected),
    }
}

pub(super) fn map_push_free<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    index: u32,
    slot: &Slot<T, N>,
) {
    let id = encode(index, slot.version.load(Ordering::Relaxed));
    let mut head = map.free_head.load(Ordering::Acquire);
    loop {
        slot.link.store(head, Ordering::Relaxed);
        match map
            .free_head
            .compare_exchange_weak(head, id, Ordering::Release, Ordering::Relaxed)
        {
            Ok(_) => break,
            Err(current) => head = current,
        }
    }
}

pub(super) fn map_try_insert_if<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    predicate: impl FnMut(u32) -> bool,
) -> Result<SlotWriter<'a, K, T, N>, ReserveError> {
    let candidate = map.claim(predicate)?;
    let key = checked_key(candidate.index, candidate.version);
    Ok(SlotWriter { candidate, key })
}

pub(super) fn map_insert<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>, value: T) -> K {
    map.insert_with_link(value, 0)
}

pub(super) fn map_insert_with_key<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    f: impl FnOnce(K) -> T,
) -> K {
    let writer = map
        .try_insert_if(|_| true)
        .unwrap_or_else(|_| panic!("SlotMap index limit exhausted"));
    let value = f(writer.key);
    writer.insert(value)
}

pub(super) fn map_try_insert_with_key<'a, K: Key, T, const N: u32, E>(
    map: &'a SlotMap<K, T, N>,
    f: impl FnOnce(K) -> Result<T, E>,
) -> Result<K, E> {
    let writer = map
        .try_insert_if(|_| true)
        .unwrap_or_else(|_| panic!("SlotMap index limit exhausted"));
    let value = f(writer.key)?;
    Ok(writer.insert(value))
}

pub(super) fn map_insert_with_link<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    value: T,
    link: u64,
) -> K {
    map.try_insert_if(|_| true)
        .unwrap_or_else(|_| panic!("SlotMap index limit exhausted"))
        .insert_with_link(value, link)
}

pub(super) fn map_alloc<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    value: T,
) -> Result<K, T> {
    map.alloc_with_link(value, 0).map_err(|(value, _)| value)
}

pub(super) fn map_alloc_with_link<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    value: T,
    link: u64,
) -> Result<K, (T, u64)> {
    match map.try_insert_if(|_| true) {
        Ok(writer) => Ok(writer.insert_with_link(value, link)),
        Err(_) => Err((value, link)),
    }
}

pub(super) fn map_set<'a, K: Key, T, const N: u32>(map: &'a mut SlotMap<K, T, N>, value: T) -> K {
    map.insert(value)
}

pub(super) fn map_set_with_link<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    value: T,
    link: u64,
) -> K {
    map.insert_with_link(value, link)
}

pub(super) fn map_len<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> usize {
    // 先读 free 再读 alloc：配合插入先计数后发布 LIVE，
    // 避免并发删除使新 free 与旧 alloc 配对，产生虚假的巨大长度。
    let free = map.free.load(Ordering::SeqCst);
    // Keep this test boundary between the two reads. Reversing their order
    // must still be caught even if this hook follows the free read instead.
    #[cfg(test)]
    tests::pause(tests::Stage::LenBetweenReads, free as u64);
    let alloc = map.alloc.load(Ordering::SeqCst);
    alloc.wrapping_sub(free)
}

pub(super) fn map_is_empty<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> bool {
    map.len() == 0
}

pub(super) fn map_alloc_count<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> usize {
    map.alloc.load(Ordering::Relaxed)
}

pub(super) fn map_free_count<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> usize {
    map.free.load(Ordering::Relaxed)
}

pub(super) fn map_max<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> u32 {
    map.next_index.load(Ordering::Acquire)
}

pub(super) fn map_compact<'a, K: Key, T, const N: u32>(map: &'a mut SlotMap<K, T, N>) {
    let mut head = NULL;
    let mut previous: Option<&mut ShareU64> = None;
    for (index, slot) in map
        .slots
        .slice_mut(0..map.next_index.load(Ordering::Relaxed) as usize)
    {
        let version = *slot.version.get_mut();
        if live::<N>(version) {
            continue;
        }
        let id = encode(index as u32, version);
        *slot.link.get_mut() = NULL;
        if let Some(previous) = previous {
            *previous.get_mut() = id;
        } else {
            head = id;
        }
        previous = Some(&mut slot.link);
    }
    map.free_head.store(head, Ordering::Relaxed);
}

pub(super) fn map_shrink_to_fit<'a, K: Key, T, const N: u32>(map: &'a mut SlotMap<K, T, N>) {
    map.rebuild(map.max());
}

pub(super) fn map_shrink_to_last_occupied<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
) {
    let end = map
        .slots
        .slice_mut(0..map.max() as usize)
        .filter(|(_, slot)| live::<N>(slot.version.load(Ordering::Relaxed)))
        .map(|(index, _)| index as u32 + 1)
        .last()
        .unwrap_or(0);
    map.rebuild(end);
}

pub(super) fn map_rebuild<'a, K: Key, T, const N: u32>(map: &'a mut SlotMap<K, T, N>, end: u32) {
    // 先完成全部分配；迁移阶段仅交换所有权，不调用 T 的构造或析构。
    let mut slots = Arr::with_capacity(end as usize);
    for (index, slot) in map.slots.slice_mut(0..end as usize) {
        std::mem::swap(slot, slots.get_mut(index).expect("new prefix initialized"));
    }
    map.slots = slots;
    map.next_index.store(end, Ordering::Relaxed);
    map.compact();
}

pub(super) fn map_get_key_bits<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    index: u32,
) -> Option<u32> {
    if index >= map.max() {
        return None;
    }
    let version = map
        .slots
        .get(index as usize)?
        .version
        .load(Ordering::Acquire);
    live::<N>(version).then_some(version & ((1u32 << N) - 1))
}

pub(super) fn map_compare_exchange_bits<K: Key, T, const N: u32>(
    map: &SlotMap<K, T, N>,
    key: K,
    expected_bits: u32,
    new_bits: u32,
) -> Result<K, CompareExchangeBitsError> {
    let mask = (1u32 << N) - 1;
    assert_eq!(expected_bits & !mask, 0, "expected bits out of range");
    assert_eq!(new_bits & !mask, 0, "new bits out of range");
    let data = key.data();
    let identity = data.version() & !mask;
    // Complete even the returned key's validation before observing the slot:
    // from/data may reenter and change or remove precisely this slot.
    let result = checked_key::<K>(data.index(), identity | new_bits);
    if !live::<N>(identity) || data.index() >= map.max() {
        return Err(CompareExchangeBitsError::Stale);
    }
    let Some(slot) = map.slots.get(data.index() as usize) else {
        return Err(CompareExchangeBitsError::Stale);
    };
    match slot.version.compare_exchange(
        identity | expected_bits,
        identity | new_bits,
        Ordering::AcqRel,
        Ordering::Acquire,
    ) {
        Ok(_) => Ok(result),
        Err(actual) if actual & !mask == identity => Err(CompareExchangeBitsError::Mismatch {
            actual_bits: actual & mask,
        }),
        Err(_) => Err(CompareExchangeBitsError::Stale),
    }
}

pub(super) fn map_find<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    data: KeyData,
) -> Option<&'a Slot<T, N>> {
    if !live::<N>(data.version()) || data.index() >= map.max() {
        return None;
    }
    // next_index 在 load_alloc_ptr 分配槽位之前递增；高水位内仍可能未分配。
    let slot = map.slots.get(data.index() as usize)?;
    (slot.version.load(Ordering::Acquire) == data.version()).then_some(slot)
}

pub(super) fn map_get<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> Option<(&'a T, &'a ShareU64)> {
    let slot = map.find(key.data())?;
    // SAFETY: LIVE Acquire observes T; safe removal needs exclusive map.
    Some((unsafe { &*slot.value_ptr() }, &slot.link))
}

pub(super) fn map_get_mut<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
) -> Option<(&'a mut T, &'a mut ShareU64)> {
    let data = key.data();
    map.find(data)?;
    let slot = map.slots.get_mut(data.index() as usize)?;
    // SAFETY: exclusive slot and LIVE proves initialized T.
    Some((
        unsafe { slot.entry.get_mut().assume_init_mut() },
        &mut slot.link,
    ))
}

pub(super) unsafe fn map_get_shared<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> Option<(&'a mut T, &'a ShareU64)> {
    let slot = map.find(key.data())?;
    // SAFETY: caller excludes conflicting T accesses; permanent link shared.
    Some((unsafe { &mut *slot.value_ptr() }, &slot.link))
}

pub(super) unsafe fn map_get_unchecked<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> (&'a T, &'a ShareU64) {
    // SAFETY: valid LIVE key required by caller.
    let slot = unsafe { map.slots.get_unchecked(key.data().index() as usize) };
    slot.version.load(Ordering::Acquire);
    // SAFETY: caller guarantees a valid LIVE key and no overlapping removal;
    // the Acquire observes initialization and map's borrow retains storage.
    (unsafe { &*slot.value_ptr() }, &slot.link)
}

pub(super) unsafe fn map_get_unchecked_mut<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
) -> (&'a mut T, &'a mut ShareU64) {
    // SAFETY: caller supplies valid key, map is exclusive.
    let slot = map
        .slots
        .get_mut(key.data().index() as usize)
        .expect("valid LIVE key");
    // SAFETY: caller guarantees initialized LIVE storage; exclusive map borrow
    // excludes other T/link references for the returned borrow's duration.
    unsafe { (slot.entry.get_mut().assume_init_mut(), &mut slot.link) }
}

pub(super) unsafe fn map_get_shared_unchecked<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> (&'a mut T, &'a ShareU64) {
    // SAFETY: caller guarantees an allocated LIVE index in this map; the map
    // borrow retains the stable slot, with removal excluded by the caller.
    let slot = unsafe { map.slots.get_unchecked(key.data().index() as usize) };
    slot.version.load(Ordering::Acquire);
    // SAFETY: caller excludes all conflicting T accesses; Acquire observes
    // initialization. link remains shared to allow late atomic FREE readers.
    (unsafe { &mut *slot.value_ptr() }, &slot.link)
}

pub(super) fn map_remove<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
) -> Option<T> {
    // SAFETY: exclusive map borrow ends all safe references to the target;
    // the delegated operation checks full LIVE identity before moving T out.
    unsafe { map.remove_shared(key) }
}

pub(super) fn map_remove_with_link<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
) -> Option<(T, u64)> {
    // SAFETY: exclusive map borrow excludes conflicting target references;
    // the delegated operation checks full LIVE identity before moving T out.
    unsafe { map.remove_shared_with_link(key) }
}

pub(super) unsafe fn map_remove_shared<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> Option<T> {
    // SAFETY: caller's exclusion of conflicting references/removal is exactly
    // the delegated operation's precondition; only its owned result is mapped.
    unsafe { map.remove_shared_with_link(key) }.map(|(value, _)| value)
}

pub(super) unsafe fn map_remove_shared_with_link<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> Option<(T, u64)> {
    let data = key.data();
    let slot = map.find(data)?;
    if slot
        .version
        .compare_exchange(
            data.version(),
            data.version().wrapping_add(1u32 << N),
            Ordering::AcqRel,
            Ordering::Acquire,
        )
        .is_err()
    {
        return None;
    }
    let link = slot.link.load(Ordering::Relaxed);
    // SAFETY: caller excludes all conflicting references; unique CAS owns T.
    let value = unsafe { ptr::read(slot.value_ptr()) };
    map.push_free(data.index(), slot);
    map.free.fetch_add(1, Ordering::SeqCst);
    Some((value, link))
}

pub(super) fn map_replace<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
    value: T,
) -> Result<T, T> {
    // SAFETY: exclusive map borrow excludes every conflicting value access;
    // the delegated operation validates initialization via full LIVE identity.
    unsafe { map.replace_shared(key, value) }
}

pub(super) fn map_replace_with_link<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
    value: T,
    link: u64,
) -> Result<(T, u64), (T, u64)> {
    // SAFETY: exclusive map borrow excludes conflicting value/link access;
    // the delegated operation validates full LIVE identity before replacement.
    unsafe { map.replace_shared_with_link(key, value, link) }
}

pub(super) unsafe fn map_replace_shared<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
    value: T,
) -> Result<T, T> {
    let Some(slot) = map.find(key.data()) else {
        return Err(value);
    };
    // SAFETY: caller ensures initialized T is exclusively accessed.
    Ok(unsafe { ptr::replace(slot.value_ptr(), value) })
}

pub(super) unsafe fn map_replace_shared_with_link<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
    value: T,
    link: u64,
) -> Result<(T, u64), (T, u64)> {
    let Some(slot) = map.find(key.data()) else {
        return Err((value, link));
    };
    let old_link = slot.link.load(Ordering::Relaxed);
    // SAFETY: full LIVE identity proves initialized T; caller guarantees
    // exclusive target access and excludes removal for this operation.
    let old = unsafe { ptr::replace(slot.value_ptr(), value) };
    slot.link.store(link, Ordering::Relaxed);
    Ok((old, old_link))
}

pub(super) fn map_iter<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
) -> Iter<'a, K, T, N> {
    Iter {
        map,
        next: 0,
        end: map.max(),
    }
}

pub(super) fn map_iter_mut<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
) -> IterMut<'a, K, T, N> {
    IterMut {
        slots: map.slots.slice_mut(0..map.max() as usize),
        borrow: PhantomData,
    }
}

pub(super) fn map_index<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>, key: K) -> &'a T {
    map.get(key).expect("invalid SlotMap key").0
}

pub(super) fn map_index_mut<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
) -> &'a mut T {
    map.get_mut(key).expect("invalid SlotMap key").0
}

pub(super) fn map_fmt<'a, K: Key, T: Debug, const N: u32>(
    map: &SlotMap<K, T, N>,
    formatter: &mut Formatter<'_>,
) -> fmt::Result {
    formatter.debug_map().entries(map.iter()).finish()
}

pub(super) fn iter_next<'a, K: Key, T, const N: u32>(
    iter: &mut Iter<'a, K, T, N>,
) -> Option<(K, (&'a T, &'a ShareU64))> {
    while iter.next < iter.end {
        let index = iter.next;
        iter.next += 1;
        let Some(slot) = iter.map.slots.get(index as usize) else {
            continue;
        };
        let version = slot.version.load(Ordering::Acquire);
        if live::<N>(version) {
            let key = checked_key(index, version);
            // SAFETY: LIVE published T; removal cannot overlap this scan.
            return Some((key, (unsafe { &*slot.value_ptr() }, &slot.link)));
        }
    }
    None
}

pub(super) fn iter_size_hint<'a, K: Key, T, const N: u32>(
    iter: &Iter<'a, K, T, N>,
) -> (usize, Option<usize>) {
    (0, Some((iter.end - iter.next) as usize))
}

pub(super) fn iter_mut_next<'a, K: Key, T, const N: u32>(
    iter: &mut IterMut<'a, K, T, N>,
) -> Option<(K, (&'a mut T, &'a mut ShareU64))> {
    for (index, slot) in iter.slots.by_ref() {
        let version = slot.version.load(Ordering::Acquire);
        if live::<N>(version) {
            let key = checked_key(index as u32, version);
            return Some((
                key,
                (
                    // SAFETY: LIVE proves initialization; the exclusive slot
                    // iterator yields each slot once, retaining map ownership
                    // and excluding conflicting references for this lifetime.
                    unsafe { slot.entry.get_mut().assume_init_mut() },
                    &mut slot.link,
                ),
            ));
        }
    }
    None
}

pub(super) fn iter_mut_size_hint<'a, K: Key, T, const N: u32>(
    iter: &IterMut<'a, K, T, N>,
) -> (usize, Option<usize>) {
    (0, iter.slots.size_hint().1)
}

pub(super) fn claim_metadata<K: Key, T, const N: u32>(
    map: &SlotMap<K, T, N>,
    data: KeyData,
    expected_bits: u32,
    claimed_mask: u32,
) -> Result<ClaimedSlot<'_, T, N>, ClaimMetadataError> {
    let mask = (1u32 << N) - 1;
    let identity = data.version() & !mask;
    // These internal arguments are prevalidated by the guarded shell's caller.
    // Classify both the initial observation and a failed CAS using the same
    // identity-first, then CLAIMED-first rule. Never retry a failed claim.
    let classify = |actual: u32| {
        if !live::<N>(identity) || actual & !mask != identity {
            Err(ClaimMetadataError::Stale)
        } else if actual & claimed_mask != 0 {
            Err(ClaimMetadataError::Claimed)
        } else if actual & mask != expected_bits {
            Err(ClaimMetadataError::BitsMismatch {
                actual_bits: actual & mask,
            })
        } else {
            Ok(())
        }
    };
    if !live::<N>(identity) || data.index() >= map.max() {
        return Err(ClaimMetadataError::Stale);
    }
    let Some(slot) = map.slots.get(data.index() as usize) else {
        return Err(ClaimMetadataError::Stale);
    };
    let expected = identity | expected_bits;
    classify(slot.version.load(Ordering::Acquire))?;
    let version = expected | claimed_mask;
    #[cfg(test)]
    tests::pause(tests::Stage::ClaimBeforeCas, u64::from(expected));
    match slot
        .version
        .compare_exchange(expected, version, Ordering::AcqRel, Ordering::Acquire)
    {
        Ok(_) => Ok(ClaimedSlot {
            slot,
            index: data.index(),
            version,
        }),
        Err(actual) => {
            #[cfg(test)]
            tests::pause(tests::Stage::ClaimCasFailed, u64::from(actual));
            // A strong CAS cannot fail with exactly expected; classify thus
            // necessarily yields an error, without a panic or a second CAS.
            match classify(actual) {
                Err(error) => Err(error),
                Ok(()) => Err(ClaimMetadataError::BitsMismatch {
                    actual_bits: actual & mask,
                }),
            }
        }
    }
}
pub(super) fn insert_with_bits<K: Key, T, const N: u32>(
    map: &SlotMap<K, T, N>,
    bits: u32,
    link: u64,
    f: impl FnOnce(KeyData) -> T,
) -> KeyData {
    let mask = (1u32 << N) - 1;
    assert_eq!(bits & !mask, 0, "initial bits out of range");
    let mut candidate = map
        .claim(|_| true)
        .unwrap_or_else(|_| panic!("SlotMap index limit exhausted"));
    // Leave the rollback version intact until commit, but erase every old
    // reserved bit from the version that will actually be published.
    let version = (candidate.version & !mask) | bits;
    let data = KeyData::new(candidate.index, version);
    let value = f(data);
    // SAFETY: candidate uniquely owns uninitialized storage. f and every key
    // callback have finished; no T reference exists before LIVE publication.
    unsafe { ptr::write(candidate.slot.value_ptr(), value) };
    candidate.slot.link.store(link, Ordering::Relaxed);
    map.alloc.fetch_add(1, Ordering::SeqCst);
    candidate.slot.version.store(version, Ordering::Release);
    candidate.version = 0;
    data
}
pub(super) unsafe fn claimed_value<'a, 'b, T, const N: u32>(
    token: &'b ClaimedSlot<'a, T, N>,
) -> &'b T {
    // SAFETY: the caller retains the successful CLAIMED token and excludes
    // conflicting mutable access. Its slot borrow keeps storage alive, and
    // the successful Acquire CAS observed initialization. Bind T to this borrow.
    unsafe { &*token.slot.value_ptr() }
}
pub(super) unsafe fn claimed_value_mut<'a, 'b, T, const N: u32>(
    token: &'b mut ClaimedSlot<'a, T, N>,
) -> &'b mut T {
    // SAFETY: the caller has exclusive use of the still-claimed token and no
    // conflicting T references; Acquire claim observed initialized storage.
    // The result cannot outlive the mutable token borrow.
    unsafe { &mut *token.slot.value_ptr() }
}
pub(super) fn claimed_link<'a, 'b, T, const N: u32>(token: &'b ClaimedSlot<'a, T, N>) -> u64 {
    token.slot.link.load(Ordering::Relaxed)
}
pub(super) fn claimed_set_link<'a, 'b, T, const N: u32>(
    token: &'b mut ClaimedSlot<'a, T, N>,
    link: u64,
) -> () {
    token.slot.link.store(link, Ordering::Relaxed);
}
pub(super) unsafe fn claimed_release<'a, 'b, T, const N: u32>(
    token: ClaimedSlot<'a, T, N>,
    final_bits: u32,
) -> () {
    // The caller validated final_bits and ended all derived references. The
    // consumed token uniquely owns this version; no read/modify/key callback
    // is needed. Release publishes T/link writes to the next acquiring claim.
    let mask = (1u32 << N) - 1;
    token
        .slot
        .version
        .store((token.version & !mask) | final_bits, Ordering::Release);
}
pub(super) unsafe fn claimed_remove<'a, 'b, K: Key, T, const N: u32>(
    token: ClaimedSlot<'a, T, N>,
    map: &SlotMap<K, T, N>,
) -> (T, u64) {
    let link = token.slot.link.load(Ordering::Relaxed);
    // SAFETY: caller ended all T references, retains unique CLAIMED ownership,
    // and supplies the very map that produced the token. Its stable slot is
    // initialized and remains LIVE until after ownership of T is moved out.
    let value = unsafe { ptr::read(token.slot.value_ptr()) };
    // Test-only pauses never receive a T reference. Their harness defers any
    // callback panic until the operation has restored the storage invariant.
    #[cfg(test)]
    tests::pause(tests::Stage::RemoveMoved, u64::from(token.version));
    token
        .slot
        .version
        .store(token.version.wrapping_add(1u32 << N), Ordering::Release);
    #[cfg(test)]
    tests::pause(tests::Stage::RemoveFree, u64::from(token.version));
    // Same-map/index membership is the unsafe shell precondition, discharged
    // by SlotGuard's saved map. push_free uses only this stable slot and atomics.
    map.push_free(token.index, token.slot);
    #[cfg(test)]
    tests::pause(tests::Stage::RemoveLinked, u64::from(token.version));
    map.free.fetch_add(1, Ordering::SeqCst);
    (value, link)
}
