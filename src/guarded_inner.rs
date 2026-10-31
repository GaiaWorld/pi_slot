//! 独占守卫实现；仅经 SlotMap/ClaimedSlot 壳访问底层。
use crate::{GuardedAccessError, GuardedSlotMap, Key, SlotGuard};

pub(super) fn map_new<'a, 'b, K: Key, T, const N: u32>() -> GuardedSlotMap<K, T, N>
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::map_new");
}
pub(super) fn map_with_capacity<'a, 'b, K: Key, T, const N: u32>(
    capacity: usize,
) -> GuardedSlotMap<K, T, N>
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::map_with_capacity");
}
pub(super) fn map_insert<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
    value: T,
    bits: u32,
) -> K
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::map_insert");
}
pub(super) fn map_insert_with_link<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
    value: T,
    link: u64,
    bits: u32,
) -> K
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::map_insert_with_link");
}
pub(super) fn map_insert_with_key<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
    bits: u32,
    f: impl FnOnce(K) -> T,
) -> K
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::map_insert_with_key");
}
pub(super) fn map_len<'a, 'b, K: Key, T, const N: u32>(this: &'b GuardedSlotMap<K, T, N>) -> usize
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::map_len");
}
pub(super) fn map_is_empty<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
) -> bool
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::map_is_empty");
}
pub(super) fn map_try_get<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
    key: K,
    expected_bits: u32,
) -> Result<SlotGuard<'b, K, T, N>, GuardedAccessError>
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::map_try_get");
}
pub(super) fn map_compare_exchange_bits<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
    key: K,
    expected_bits: u32,
    new_bits: u32,
) -> Result<K, GuardedAccessError>
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::map_compare_exchange_bits");
}
pub(super) fn map_try_remove<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
    key: K,
    expected_bits: u32,
) -> Result<(T, u64), GuardedAccessError>
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::map_try_remove");
}
pub(super) fn map_try_update<'a, 'b, K: Key, T, const N: u32, R, F>(
    this: &'b GuardedSlotMap<K, T, N>,
    key: K,
    expected_bits: u32,
    f: F,
) -> Result<R, GuardedAccessError>
where
    [(); (N + 1) as usize]:,
    F: for<'g, 'm> FnOnce(&'g mut SlotGuard<'m, K, T, N>) -> R,
{
    todo!("TODO-DECL: guarded::map_try_update");
}
pub(super) fn guard_key<'a, 'b, K: Key, T, const N: u32>(this: &'b SlotGuard<'a, K, T, N>) -> K
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::guard_key");
}
pub(super) fn guard_value<'a, 'b, K: Key, T, const N: u32>(
    this: &'b SlotGuard<'a, K, T, N>,
) -> &'b T
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::guard_value");
}
pub(super) fn guard_value_mut<'a, 'b, K: Key, T, const N: u32>(
    this: &'b mut SlotGuard<'a, K, T, N>,
) -> &'b mut T
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::guard_value_mut");
}
pub(super) fn guard_link<'a, 'b, K: Key, T, const N: u32>(this: &'b SlotGuard<'a, K, T, N>) -> u64
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::guard_link");
}
pub(super) fn guard_set_link<'a, 'b, K: Key, T, const N: u32>(
    this: &'b mut SlotGuard<'a, K, T, N>,
    link: u64,
) -> ()
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::guard_set_link");
}
pub(super) fn guard_bits<'a, 'b, K: Key, T, const N: u32>(this: &'b SlotGuard<'a, K, T, N>) -> u32
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::guard_bits");
}
pub(super) fn guard_original_bits<'a, 'b, K: Key, T, const N: u32>(
    this: &'b SlotGuard<'a, K, T, N>,
) -> u32
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::guard_original_bits");
}
pub(super) fn guard_set_bits<'a, 'b, K: Key, T, const N: u32>(
    this: &'b mut SlotGuard<'a, K, T, N>,
    bits: u32,
) -> ()
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::guard_set_bits");
}
pub(super) fn guard_remove<'a, 'b, K: Key, T, const N: u32>(
    mut this: SlotGuard<'a, K, T, N>,
) -> (T, u64)
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::guard_remove");
}
pub(super) fn guard_drop<K: Key, T, const N: u32>(guard: &mut SlotGuard<'_, K, T, N>)
where
    [(); (N + 1) as usize]:,
{
    todo!("TODO-DECL: guarded::guard_drop");
}
