//! 独占守卫实现；仅经 SlotMap/ClaimedSlot 壳访问底层。
use crate::slotmap::{ClaimMetadataError, CompareExchangeBitsError, KeyData, SlotMap};
use crate::{GuardedAccessError, GuardedSlotMap, Key, SlotGuard};
use std::marker::PhantomData;

fn business_mask<const N: u32>() -> u32 {
    assert!(N <= 30, "business bit count must not exceed 30");
    (1u32 << N) - 1
}

fn check_bits<const N: u32>(bits: u32) {
    assert_eq!(
        bits & !business_mask::<N>(),
        0,
        "business bits out of range"
    );
}

// Complete from/data validation before entering any state-changing operation.
fn identity_key<K: Key, const N: u32>(data: KeyData) -> (KeyData, K) {
    let reserved = business_mask::<N>() | (1u32 << N);
    let identity = KeyData::new(data.index(), data.version() & !reserved);
    let key = K::from(identity);
    assert_eq!(
        key.data(),
        identity,
        "GuardedSlotMap Key must preserve identity"
    );
    (identity, key)
}

pub(super) fn map_new<'a, 'b, K: Key, T, const N: u32>() -> GuardedSlotMap<K, T, N>
where
    [(); (N + 1) as usize]:,
{
    GuardedSlotMap::with_capacity(0)
}
pub(super) fn map_with_capacity<'a, 'b, K: Key, T, const N: u32>(
    capacity: usize,
) -> GuardedSlotMap<K, T, N>
where
    [(); (N + 1) as usize]:,
{
    business_mask::<N>();
    GuardedSlotMap {
        inner: SlotMap::with_capacity(capacity),
    }
}
pub(super) fn map_insert<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
    value: T,
    bits: u32,
) -> K
where
    [(); (N + 1) as usize]:,
{
    this.insert_with_link(value, 0, bits)
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
    check_bits::<N>(bits);
    let mut result = None;
    this.inner.insert_with_bits(bits, link, |data| {
        let (_, key) = identity_key::<K, N>(data);
        result = Some(key);
        value
    });
    // The synchronous FnOnce above always runs on successful insertion; this
    // extracts only a Copy key, without invoking any user key callback.
    result.expect("successful insertion constructed its identity key")
}
pub(super) fn map_insert_with_key<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
    bits: u32,
    f: impl FnOnce(K) -> T,
) -> K
where
    [(); (N + 1) as usize]:,
{
    check_bits::<N>(bits);
    let mut result = None;
    this.inner.insert_with_bits(bits, 0, |data| {
        let (_, key) = identity_key::<K, N>(data);
        result = Some(key);
        f(key)
    });
    result.expect("successful insertion constructed its identity key")
}
pub(super) fn map_len<'a, 'b, K: Key, T, const N: u32>(this: &'b GuardedSlotMap<K, T, N>) -> usize
where
    [(); (N + 1) as usize]:,
{
    this.inner.len()
}
pub(super) fn map_is_empty<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
) -> bool
where
    [(); (N + 1) as usize]:,
{
    this.inner.is_empty()
}
pub(super) fn map_try_get<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
    key: K,
    expected_bits: u32,
) -> Result<SlotGuard<'b, K, T, N>, GuardedAccessError>
where
    [(); (N + 1) as usize]:,
{
    check_bits::<N>(expected_bits);
    let (data, key) = identity_key::<K, N>(key.data());
    let token = this
        .inner
        .claim_metadata(data, expected_bits, 1u32 << N)
        .map_err(|error| match error {
            ClaimMetadataError::Stale => GuardedAccessError::Stale,
            ClaimMetadataError::Claimed => GuardedAccessError::Busy,
            ClaimMetadataError::BitsMismatch { actual_bits } => {
                GuardedAccessError::BitsMismatch { actual_bits }
            }
        })?;
    // CLAIMED has succeeded, but no T reference is constructed or stored here.
    Ok(SlotGuard {
        map: this,
        key,
        token: Some(token),
        original_bits: expected_bits,
        final_bits: expected_bits,
        not_sync: PhantomData,
    })
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
    check_bits::<N>(expected_bits);
    check_bits::<N>(new_bits);
    let (_, stable_key) = identity_key::<K, N>(key.data());
    // The bottom shell precomputes its own full return key (and all data
    // callbacks) before its single CAS. Never convert that key after success.
    match this
        .inner
        .compare_exchange_bits(stable_key, expected_bits, new_bits)
    {
        Ok(_) => Ok(stable_key),
        Err(CompareExchangeBitsError::Stale) => Err(GuardedAccessError::Stale),
        Err(CompareExchangeBitsError::Mismatch { actual_bits }) => {
            if actual_bits & (1u32 << N) != 0 {
                Err(GuardedAccessError::Busy)
            } else {
                Err(GuardedAccessError::BitsMismatch { actual_bits })
            }
        }
    }
}
pub(super) fn map_try_remove<'a, 'b, K: Key, T, const N: u32>(
    this: &'b GuardedSlotMap<K, T, N>,
    key: K,
    expected_bits: u32,
) -> Result<(T, u64), GuardedAccessError>
where
    [(); (N + 1) as usize]:,
{
    Ok(this.try_get(key, expected_bits)?.remove())
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
    let mut guard = this.try_get(key, expected_bits)?;
    let result = f(&mut guard);
    drop(guard);
    Ok(result)
}
pub(super) fn guard_key<'a, 'b, K: Key, T, const N: u32>(this: &'b SlotGuard<'a, K, T, N>) -> K
where
    [(); (N + 1) as usize]:,
{
    this.key
}
pub(super) fn guard_value<'a, 'b, K: Key, T, const N: u32>(
    this: &'b SlotGuard<'a, K, T, N>,
) -> &'b T
where
    [(); (N + 1) as usize]:,
{
    let token = this.token.as_ref().expect("active guard has its token");
    // SAFETY: only a successful CLAIMED CAS creates this guard. The token is
    // retained for the whole returned borrow, and &self excludes value_mut or
    // consumption. The closed map offers no unclaimed T access.
    unsafe { token.value() }
}
pub(super) fn guard_value_mut<'a, 'b, K: Key, T, const N: u32>(
    this: &'b mut SlotGuard<'a, K, T, N>,
) -> &'b mut T
where
    [(); (N + 1) as usize]:,
{
    let token = this.token.as_mut().expect("active guard has its token");
    // SAFETY: guard uniquely owns the successful CLAIMED token. Its mutable
    // borrow excludes every other guard-derived T reference and prevents
    // release/remove until the returned mutable borrow ends.
    unsafe { token.value_mut() }
}
pub(super) fn guard_link<'a, 'b, K: Key, T, const N: u32>(this: &'b SlotGuard<'a, K, T, N>) -> u64
where
    [(); (N + 1) as usize]:,
{
    this.token
        .as_ref()
        .expect("active guard has its token")
        .link()
}
pub(super) fn guard_set_link<'a, 'b, K: Key, T, const N: u32>(
    this: &'b mut SlotGuard<'a, K, T, N>,
    link: u64,
) -> ()
where
    [(); (N + 1) as usize]:,
{
    this.token
        .as_mut()
        .expect("active guard has its token")
        .set_link(link);
}
pub(super) fn guard_bits<'a, 'b, K: Key, T, const N: u32>(this: &'b SlotGuard<'a, K, T, N>) -> u32
where
    [(); (N + 1) as usize]:,
{
    this.final_bits
}
pub(super) fn guard_original_bits<'a, 'b, K: Key, T, const N: u32>(
    this: &'b SlotGuard<'a, K, T, N>,
) -> u32
where
    [(); (N + 1) as usize]:,
{
    this.original_bits
}
pub(super) fn guard_set_bits<'a, 'b, K: Key, T, const N: u32>(
    this: &'b mut SlotGuard<'a, K, T, N>,
    bits: u32,
) -> ()
where
    [(); (N + 1) as usize]:,
{
    check_bits::<N>(bits);
    this.final_bits = bits;
}
pub(super) fn guard_remove<'a, 'b, K: Key, T, const N: u32>(
    mut this: SlotGuard<'a, K, T, N>,
) -> (T, u64)
where
    [(); (N + 1) as usize]:,
{
    // Safe construction always installs Some; taking it suppresses Drop's
    // release even if another thread immediately reuses the freed slot.
    // SAFETY: every successfully constructed guard contains Some(token).
    // Only this consuming operation and Drop take it; neither can have run
    // on this still-owned guard. No user code can access or replace the field.
    let token = unsafe { this.token.take().unwrap_unchecked() };
    // SAFETY: consuming the guard ends all derived references. Its token came
    // from this exact saved map, whose borrow keeps the stable slot alive;
    // CLAIMED still grants exclusive ownership. Removal has no key callbacks.
    unsafe { token.remove(&this.map.inner) }
}
pub(super) fn guard_drop<K: Key, T, const N: u32>(guard: &mut SlotGuard<'_, K, T, N>)
where
    [(); (N + 1) as usize]:,
{
    if let Some(token) = guard.token.take() {
        // SAFETY: Drop runs after all guard-derived references end. The token
        // still owns CLAIMED, and final_bits was range-checked before assignment.
        // The shell only performs a Release store; no callbacks or assertions.
        unsafe { token.release(guard.final_bits) };
    }
}
