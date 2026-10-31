//! 槽表行为实现；公共契约与核心流程单源位于 slotmap.rs。
use super::*;

pub(super) fn writer_key<'a, K: Key, T, const N: u32>(writer: &SlotWriter<'a, K, T, N>) -> K {
    todo!("TODO-DECL: slotmap::writer_key");
}

pub(super) fn writer_insert<'a, K: Key, T, const N: u32>(
    writer: SlotWriter<'a, K, T, N>,
    value: T,
) -> K {
    todo!("TODO-DECL: slotmap::writer_insert");
}

pub(super) fn writer_insert_with_link<'a, K: Key, T, const N: u32>(
    mut writer: SlotWriter<'a, K, T, N>,
    value: T,
    link: u64,
) -> K {
    todo!("TODO-DECL: slotmap::writer_insert_with_link");
}

pub(super) fn candidate_drop<'a, K: Key, T, const N: u32>(candidate: &mut Candidate<'a, K, T, N>) {
    todo!("TODO-DECL: slotmap::candidate_drop");
}

pub(super) fn map_default<'a, K: Key, T, const N: u32>() -> SlotMap<K, T, N> {
    todo!("TODO-DECL: slotmap::map_default");
}

pub(super) fn map_drop<'a, K: Key, T, const N: u32>(map: &mut SlotMap<K, T, N>) {
    todo!("TODO-DECL: slotmap::map_drop");
}

pub(super) fn map_new<'a, K: Key, T, const N: u32>() -> SlotMap<K, T, N> {
    todo!("TODO-DECL: slotmap::map_new");
}

pub(super) fn map_with_capacity<'a, K: Key, T, const N: u32>(capacity: usize) -> SlotMap<K, T, N> {
    todo!("TODO-DECL: slotmap::map_with_capacity");
}

pub(super) fn map_pop_free<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> Option<u32> {
    todo!("TODO-DECL: slotmap::map_pop_free");
}

pub(super) fn map_claim<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    mut predicate: impl FnMut(u32) -> bool,
) -> Result<Candidate<'a, K, T, N>, ReserveError> {
    todo!("TODO-DECL: slotmap::map_claim");
}

pub(super) fn map_push_free<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    index: u32,
    slot: &Slot<T, N>,
) {
    todo!("TODO-DECL: slotmap::map_push_free");
}

pub(super) fn map_try_insert_if<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    predicate: impl FnMut(u32) -> bool,
) -> Result<SlotWriter<'a, K, T, N>, ReserveError> {
    todo!("TODO-DECL: slotmap::map_try_insert_if");
}

pub(super) fn map_insert<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>, value: T) -> K {
    todo!("TODO-DECL: slotmap::map_insert");
}

pub(super) fn map_insert_with_key<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    f: impl FnOnce(K) -> T,
) -> K {
    todo!("TODO-DECL: slotmap::map_insert_with_key");
}

pub(super) fn map_try_insert_with_key<'a, K: Key, T, const N: u32, E>(
    map: &'a SlotMap<K, T, N>,
    f: impl FnOnce(K) -> Result<T, E>,
) -> Result<K, E> {
    todo!("TODO-DECL: slotmap::map_try_insert_with_key");
}

pub(super) fn map_insert_with_link<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    value: T,
    link: u64,
) -> K {
    todo!("TODO-DECL: slotmap::map_insert_with_link");
}

pub(super) fn map_alloc<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    value: T,
) -> Result<K, T> {
    todo!("TODO-DECL: slotmap::map_alloc");
}

pub(super) fn map_alloc_with_link<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    value: T,
    link: u64,
) -> Result<K, (T, u64)> {
    todo!("TODO-DECL: slotmap::map_alloc_with_link");
}

pub(super) fn map_set<'a, K: Key, T, const N: u32>(map: &'a mut SlotMap<K, T, N>, value: T) -> K {
    todo!("TODO-DECL: slotmap::map_set");
}

pub(super) fn map_set_with_link<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    value: T,
    link: u64,
) -> K {
    todo!("TODO-DECL: slotmap::map_set_with_link");
}

pub(super) fn map_len<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> usize {
    todo!("TODO-DECL: slotmap::map_len");
}

pub(super) fn map_is_empty<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> bool {
    todo!("TODO-DECL: slotmap::map_is_empty");
}

pub(super) fn map_alloc_count<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> usize {
    todo!("TODO-DECL: slotmap::map_alloc_count");
}

pub(super) fn map_free_count<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> usize {
    todo!("TODO-DECL: slotmap::map_free_count");
}

pub(super) fn map_max<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>) -> u32 {
    todo!("TODO-DECL: slotmap::map_max");
}

pub(super) fn map_compact<'a, K: Key, T, const N: u32>(map: &'a mut SlotMap<K, T, N>) {
    todo!("TODO-DECL: slotmap::map_compact");
}

pub(super) fn map_shrink_to_fit<'a, K: Key, T, const N: u32>(map: &'a mut SlotMap<K, T, N>) {
    todo!("TODO-DECL: slotmap::map_shrink_to_fit");
}

pub(super) fn map_shrink_to_last_occupied<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
) {
    todo!("TODO-DECL: slotmap::map_shrink_to_last_occupied");
}

pub(super) fn map_rebuild<'a, K: Key, T, const N: u32>(map: &'a mut SlotMap<K, T, N>, end: u32) {
    todo!("TODO-DECL: slotmap::map_rebuild");
}

pub(super) fn map_get_key_bits<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    index: u32,
) -> Option<u32> {
    todo!("TODO-DECL: slotmap::map_get_key_bits");
}

pub(super) fn map_compare_exchange_bits<K: Key, T, const N: u32>(
    map: &SlotMap<K, T, N>,
    key: K,
    expected_bits: u32,
    new_bits: u32,
) -> Result<K, CompareExchangeBitsError> {
    todo!("TODO-DECL: slotmap::map_compare_exchange_bits");
}

pub(super) fn map_find<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    data: KeyData,
) -> Option<&'a Slot<T, N>> {
    todo!("TODO-DECL: slotmap::map_find");
}

pub(super) fn map_get<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> Option<(&'a T, &'a ShareU64)> {
    todo!("TODO-DECL: slotmap::map_get");
}

pub(super) fn map_get_mut<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
) -> Option<(&'a mut T, &'a mut ShareU64)> {
    todo!("TODO-DECL: slotmap::map_get_mut");
}

pub(super) unsafe fn map_get_shared<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> Option<(&'a mut T, &'a ShareU64)> {
    todo!("TODO-DECL: slotmap::map_get_shared");
}

pub(super) unsafe fn map_get_unchecked<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> (&'a T, &'a ShareU64) {
    todo!("TODO-DECL: slotmap::map_get_unchecked");
}

pub(super) unsafe fn map_get_unchecked_mut<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
) -> (&'a mut T, &'a mut ShareU64) {
    todo!("TODO-DECL: slotmap::map_get_unchecked_mut");
}

pub(super) unsafe fn map_get_shared_unchecked<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> (&'a mut T, &'a ShareU64) {
    todo!("TODO-DECL: slotmap::map_get_shared_unchecked");
}

pub(super) fn map_remove<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
) -> Option<T> {
    todo!("TODO-DECL: slotmap::map_remove");
}

pub(super) fn map_remove_with_link<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
) -> Option<(T, u64)> {
    todo!("TODO-DECL: slotmap::map_remove_with_link");
}

pub(super) unsafe fn map_remove_shared<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> Option<T> {
    todo!("TODO-DECL: slotmap::map_remove_shared");
}

pub(super) unsafe fn map_remove_shared_with_link<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
) -> Option<(T, u64)> {
    todo!("TODO-DECL: slotmap::map_remove_shared_with_link");
}

pub(super) fn map_replace<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
    value: T,
) -> Result<T, T> {
    todo!("TODO-DECL: slotmap::map_replace");
}

pub(super) fn map_replace_with_link<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
    value: T,
    link: u64,
) -> Result<(T, u64), (T, u64)> {
    todo!("TODO-DECL: slotmap::map_replace_with_link");
}

pub(super) unsafe fn map_replace_shared<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
    value: T,
) -> Result<T, T> {
    todo!("TODO-DECL: slotmap::map_replace_shared");
}

pub(super) unsafe fn map_replace_shared_with_link<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
    key: K,
    value: T,
    link: u64,
) -> Result<(T, u64), (T, u64)> {
    todo!("TODO-DECL: slotmap::map_replace_shared_with_link");
}

pub(super) fn map_iter<'a, K: Key, T, const N: u32>(
    map: &'a SlotMap<K, T, N>,
) -> Iter<'a, K, T, N> {
    todo!("TODO-DECL: slotmap::map_iter");
}

pub(super) fn map_iter_mut<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
) -> IterMut<'a, K, T, N> {
    todo!("TODO-DECL: slotmap::map_iter_mut");
}

pub(super) fn map_index<'a, K: Key, T, const N: u32>(map: &'a SlotMap<K, T, N>, key: K) -> &'a T {
    todo!("TODO-DECL: slotmap::map_index");
}

pub(super) fn map_index_mut<'a, K: Key, T, const N: u32>(
    map: &'a mut SlotMap<K, T, N>,
    key: K,
) -> &'a mut T {
    todo!("TODO-DECL: slotmap::map_index_mut");
}

pub(super) fn map_fmt<'a, K: Key, T: Debug, const N: u32>(
    map: &SlotMap<K, T, N>,
    formatter: &mut Formatter<'_>,
) -> fmt::Result {
    todo!("TODO-DECL: slotmap::map_fmt");
}

pub(super) fn iter_next<'a, K: Key, T, const N: u32>(
    iter: &mut Iter<'a, K, T, N>,
) -> Option<(K, (&'a T, &'a ShareU64))> {
    todo!("TODO-DECL: slotmap::iter_next");
}

pub(super) fn iter_size_hint<'a, K: Key, T, const N: u32>(
    iter: &Iter<'a, K, T, N>,
) -> (usize, Option<usize>) {
    todo!("TODO-DECL: slotmap::iter_size_hint");
}

pub(super) fn iter_mut_next<'a, K: Key, T, const N: u32>(
    iter: &mut IterMut<'a, K, T, N>,
) -> Option<(K, (&'a mut T, &'a mut ShareU64))> {
    todo!("TODO-DECL: slotmap::iter_mut_next");
}

pub(super) fn iter_mut_size_hint<'a, K: Key, T, const N: u32>(
    iter: &IterMut<'a, K, T, N>,
) -> (usize, Option<usize>) {
    todo!("TODO-DECL: slotmap::iter_mut_size_hint");
}

pub(super) fn claim_metadata<K: Key, T, const N: u32>(
    map: &SlotMap<K, T, N>,
    data: KeyData,
    expected_bits: u32,
    claimed_mask: u32,
) -> Result<ClaimedSlot<'_, T, N>, ClaimMetadataError> {
    todo!("TODO-DECL: slotmap::claim_metadata");
}
pub(super) fn insert_with_bits<K: Key, T, const N: u32>(
    map: &SlotMap<K, T, N>,
    bits: u32,
    link: u64,
    f: impl FnOnce(KeyData) -> T,
) -> KeyData {
    todo!("TODO-DECL: slotmap::insert_with_bits");
}
pub(super) unsafe fn claimed_value<'a, 'b, T, const N: u32>(
    token: &'b ClaimedSlot<'a, T, N>,
) -> &'b T {
    todo!("TODO-DECL: slotmap::claimed_value");
}
pub(super) unsafe fn claimed_value_mut<'a, 'b, T, const N: u32>(
    token: &'b mut ClaimedSlot<'a, T, N>,
) -> &'b mut T {
    todo!("TODO-DECL: slotmap::claimed_value_mut");
}
pub(super) fn claimed_link<'a, 'b, T, const N: u32>(token: &'b ClaimedSlot<'a, T, N>) -> u64 {
    todo!("TODO-DECL: slotmap::claimed_link");
}
pub(super) fn claimed_set_link<'a, 'b, T, const N: u32>(
    token: &'b mut ClaimedSlot<'a, T, N>,
    link: u64,
) -> () {
    todo!("TODO-DECL: slotmap::claimed_set_link");
}
pub(super) unsafe fn claimed_release<'a, 'b, T, const N: u32>(
    token: ClaimedSlot<'a, T, N>,
    final_bits: u32,
) -> () {
    todo!("TODO-DECL: slotmap::claimed_release");
}
pub(super) unsafe fn claimed_remove<'a, 'b, K: Key, T, const N: u32>(
    token: ClaimedSlot<'a, T, N>,
    map: &SlotMap<K, T, N>,
) -> (T, u64) {
    todo!("TODO-DECL: slotmap::claimed_remove");
}

pub(super) fn slot_value_ptr<T, const N: u32>(slot: &Slot<T, N>) -> *mut T {
    todo!("TODO-DECL: slotmap::slot_value_ptr");
}

pub(super) fn slot_default<T, const N: u32>() -> Slot<T, N> {
    todo!("TODO-DECL: slotmap::slot_default");
}

pub(super) fn slot_drop<T, const N: u32>(slot: &mut Slot<T, N>) {
    todo!("TODO-DECL: slotmap::slot_drop");
}

pub(super) fn live<const N: u32>(version: u32) -> bool {
    todo!("TODO-DECL: slotmap::live");
}

pub(super) fn encode(index: u32, version: u32) -> u64 {
    todo!("TODO-DECL: slotmap::encode");
}

pub(super) fn checked_key<K: Key>(index: u32, version: u32) -> K {
    todo!("TODO-DECL: slotmap::checked_key");
}
