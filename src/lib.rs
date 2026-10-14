//! 版本化槽表。FREE link 保存完整标识，LIVE link 属于用户。
//! 删除前必须终止所有目标槽引用；本库不提供 EBR 或两阶段退休。
//! 默认 len/is_empty 扫描版本，复杂度 O(max)，并发时不是一致性快照。
//! ```compile_fail
//! use pi_slot::{DefaultKey, SlotMap};
//! let map = SlotMap::<DefaultKey, u32>::new();
//! let key = map.insert(1);
//! *map.get(key).unwrap().0 = 2;
//! ```
//! ```compile_fail
//! use pi_slot::{DefaultKey, SlotMap};
//! let mut map = SlotMap::<DefaultKey, u32>::new();
//! let key = map.insert(1);
//! let value = map.get(key).unwrap();
//! map.remove(key);
//! println!("{value:?}");
//! ```

#[cfg(test)]
#[path = "../tests/support/private.rs"]
mod private_tests;

#[cfg(feature = "stats")]
use crossbeam_utils::CachePadded;
use pi_arr::Arr;
pub use pi_key::{DefaultKey, Key, KeyData};
use pi_share::ShareU32;
pub use pi_share::ShareU64;
#[cfg(feature = "stats")]
use pi_share::ShareUsize;
use std::cell::UnsafeCell;
use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::{Index, IndexMut};
use std::ptr;
use std::sync::atomic::Ordering;

const MAX_ENTRIES: usize = u32::MAX as usize - 32;
const MAX_LIVE_VERSION: u32 = u32::MAX - 1;
const NULL: u64 = u32::MAX as u64;

#[repr(C)]
struct Slot<T> {
    link: ShareU64,
    entry: UnsafeCell<MaybeUninit<T>>,
    version: ShareU32,
}

// SAFETY: publication initializes T; unsafe mutation/removal requires external
// exclusivity. The generic tuple bound checks the actual version atomic's Sync
// even under upstream feature union; ThreadSync/serial cannot weaken it.
// SlotMap derives its thread traits from its actual fields, with no blanket impl.
unsafe impl<T: Send + Sync> Sync for Slot<T> where (T, ShareU32): Sync {}

impl<T> Slot<T> {
    fn value_ptr(&self) -> *mut T {
        self.entry.get().cast::<T>()
    }
}
impl<T> Default for Slot<T> {
    fn default() -> Self {
        Self {
            link: ShareU64::new(NULL),
            entry: UnsafeCell::new(MaybeUninit::uninit()),
            version: ShareU32::new(1),
        }
    }
}
impl<T> Drop for Slot<T> {
    fn drop(&mut self) {
        if live(*self.version.get_mut()) {
            *self.version.get_mut() = u32::MAX;
            // SAFETY: final exclusive owner; LIVE proves initialization. Ordinary
            // field drop glue still destroys link if the value destructor unwinds.
            unsafe { self.entry.get_mut().assume_init_drop() };
        }
    }
}
fn live(version: u32) -> bool {
    version != 0 && version & 1 == 0 && version <= MAX_LIVE_VERSION
}
fn encode(index: u32, version: u32) -> u64 {
    (u64::from(version) << 32) | u64::from(index)
}
fn checked_key<K: Key>(index: u32, version: u32) -> K {
    let data = KeyData::from_ffi(encode(index, version));
    assert_eq!(
        (data.index(), data.version()),
        (index, version),
        "KeyData encoding must preserve full generation"
    );
    let key = K::from(data);
    assert_eq!(
        key.data(),
        data,
        "SlotMap Key must preserve both index and version"
    );
    key
}

/// 版本化槽表，完整 index32/version32 key 仅属于原表。
/// 初始 FREE=1，LIVE=2,4,..,MAX-1；FREE=3,5,..,MAX；MAX 永久耗尽。
#[repr(C)]
pub struct SlotMap<K: Key = DefaultKey, T = ()> {
    free_head: ShareU64,
    slots: Arr<Slot<T>>,
    #[cfg(feature = "stats")]
    alloc: CachePadded<ShareUsize>,
    #[cfg(feature = "stats")]
    free: CachePadded<ShareUsize>,
    next_index: ShareU32,
    key_type: PhantomData<K>,
}
struct Candidate<'a, K: Key, T> {
    map: &'a SlotMap<K, T>,
    slot: &'a Slot<T>,
    index: u32,
    // Zero means committed. Every abandoned candidate consumes its generation.
    version: u32,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReserveError {
    IndexRejected,
    IndexExhausted,
}
/// 空槽唯一写入者；所有用户回调和键校验在写 T 之前完成。
/// 放弃消耗 generation；forget 只泄漏未初始化空槽。
/// ```compile_fail
/// use pi_slot::{DefaultKey, SlotMap};
/// let writer = {
///     let map = SlotMap::<DefaultKey, u32>::new();
///     map.try_reserve_if(|_| true).unwrap()
/// };
/// writer.insert(1);
/// ```
pub struct SlotWriter<'a, K: Key, T> {
    candidate: Candidate<'a, K, T>,
    key: K,
}
impl<K: Key, T> SlotWriter<'_, K, T> {
    pub fn insert(self, value: T) -> K {
        self.insert_with_link(value, 0)
    }
    pub fn insert_with_link(mut self, value: T, link: u64) -> K {
        // SAFETY: candidate exclusively owns uninitialized T, all callbacks done.
        unsafe { ptr::write(self.candidate.slot.value_ptr(), value) };
        self.candidate.slot.link.store(link, Ordering::Relaxed);
        self.candidate
            .slot
            .version
            .store(self.candidate.version, Ordering::Release);
        self.candidate.version = 0;
        #[cfg(feature = "stats")]
        self.candidate.map.alloc.fetch_add(1, Ordering::Relaxed);
        self.key
    }
}
impl<K: Key, T> Drop for Candidate<'_, K, T> {
    fn drop(&mut self) {
        if self.version != 0 {
            self.slot.version.store(self.version + 1, Ordering::Release);
            self.map.push_free(self.index, self.slot);
        }
    }
}
impl<K: Key, T> Default for SlotMap<K, T> {
    fn default() -> Self {
        Self::new()
    }
}
impl<K: Key, T> Drop for SlotMap<K, T> {
    fn drop(&mut self) {
        let mut first_panic = None;
        for segment in self.slots.segments(0..MAX_ENTRIES + 1) {
            for slot in segment {
                if !live(slot.version.swap(u32::MAX, Ordering::Relaxed)) {
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
}
impl<K: Key, T> SlotMap<K, T> {
    pub fn new() -> Self {
        Self::with_capacity(0)
    }
    pub fn with_capacity(capacity: usize) -> Self {
        assert!(
            capacity <= MAX_ENTRIES,
            "SlotMap capacity exceeds index limit"
        );
        Self {
            free_head: ShareU64::new(NULL),
            slots: Arr::with_capacity(capacity),
            #[cfg(feature = "stats")]
            alloc: CachePadded::new(ShareUsize::new(0)),
            #[cfg(feature = "stats")]
            free: CachePadded::new(ShareUsize::new(0)),
            next_index: ShareU32::new(0),
            key_type: PhantomData,
        }
    }
    fn pop_free(&self) -> Option<u32> {
        loop {
            let head = self.free_head.load(Ordering::Acquire);
            if head == NULL {
                return None;
            }
            let index = head as u32;
            let slot = self.slots.get(index as usize).expect("FREE slot allocated");
            // A late observer may read arbitrary LIVE user bits. Never dereference
            // next or validate its target before the full-id CAS succeeds. Every
            // detached id is consumed, so this stale CAS must fail without ABA.
            let next = slot.link.load(Ordering::Relaxed);
            if self
                .free_head
                .compare_exchange(head, next, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                return Some(index);
            }
        }
    }
    fn claim(
        &self,
        mut predicate: impl FnMut(u32) -> bool,
    ) -> Result<Candidate<'_, K, T>, ReserveError> {
        while let Some(index) = self.pop_free() {
            let slot = self.slots.get(index as usize).expect("popped FREE slot");
            let version = slot.version.load(Ordering::Relaxed);
            if version == u32::MAX {
                continue;
            }
            return Ok(Candidate {
                map: self,
                slot,
                index,
                version: version + 1,
            });
        }
        let result = self
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
                if self.next_index.load(Ordering::Relaxed) != index {
                    return None;
                }
                Some(index + 1)
            });
        match result {
            Ok(index) => {
                // SAFETY: last successful callback allocated this stable shell;
                let slot = unsafe { &*self.slots.load_alloc_ptr(index as usize) };
                Ok(Candidate {
                    map: self,
                    slot,
                    index,
                    version: 2,
                })
            }
            Err(index) if index as usize >= MAX_ENTRIES => Err(ReserveError::IndexExhausted),
            Err(_) => Err(ReserveError::IndexRejected),
        }
    }
    fn push_free(&self, index: u32, slot: &Slot<T>) {
        let id = encode(index, slot.version.load(Ordering::Relaxed));
        let mut head = self.free_head.load(Ordering::Acquire);
        loop {
            slot.link.store(head, Ordering::Relaxed);
            match self.free_head.compare_exchange_weak(
                head,
                id,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(current) => head = current,
            }
        }
    }
    pub fn try_reserve_if(
        &self,
        predicate: impl FnMut(u32) -> bool,
    ) -> Result<SlotWriter<'_, K, T>, ReserveError> {
        let candidate = self.claim(predicate)?;
        let key = checked_key(candidate.index, candidate.version);
        Ok(SlotWriter { candidate, key })
    }
    pub fn insert(&self, value: T) -> K {
        self.insert_with_link(value, 0)
    }
    pub fn insert_with_link(&self, value: T, link: u64) -> K {
        self.try_reserve_if(|_| true)
            .unwrap_or_else(|_| panic!("SlotMap index limit exhausted"))
            .insert_with_link(value, link)
    }
    pub fn alloc(&self, value: T) -> Result<K, T> {
        self.alloc_with_link(value, 0).map_err(|(value, _)| value)
    }
    pub fn alloc_with_link(&self, value: T, link: u64) -> Result<K, (T, u64)> {
        match self.try_reserve_if(|_| true) {
            Ok(writer) => Ok(writer.insert_with_link(value, link)),
            Err(_) => Err((value, link)),
        }
    }
    pub fn set(&mut self, value: T) -> K {
        self.insert(value)
    }
    pub fn set_with_link(&mut self, value: T, link: u64) -> K {
        self.insert_with_link(value, link)
    }
    /// O(max) version scan, not a consistent concurrent snapshot. No key callbacks.
    pub fn len(&self) -> usize {
        self.slots
            .segments(0..self.max() as usize)
            .flat_map(|segment| segment.iter())
            .filter(|slot| live(slot.version.load(Ordering::Acquire)))
            .count()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    #[cfg(feature = "stats")]
    pub fn alloc_count(&self) -> usize {
        self.alloc.load(Ordering::Relaxed)
    }
    #[cfg(feature = "stats")]
    pub fn free_count(&self) -> usize {
        self.free.load(Ordering::Relaxed)
    }
    pub fn max(&self) -> u32 {
        self.next_index.load(Ordering::Acquire)
    }
    fn find(&self, data: KeyData) -> Option<&Slot<T>> {
        if !live(data.version()) || data.index() >= self.max() {
            return None;
        }
        let slot = self.slots.get(data.index() as usize)?;
        (slot.version.load(Ordering::Acquire) == data.version()).then_some(slot)
    }
    pub fn get(&self, key: K) -> Option<(&T, &ShareU64)> {
        let slot = self.find(key.data())?;
        // SAFETY: LIVE Acquire observes T; safe removal needs exclusive map.
        Some((unsafe { &*slot.value_ptr() }, &slot.link))
    }
    pub fn get_mut(&mut self, key: K) -> Option<(&mut T, &mut ShareU64)> {
        let data = key.data();
        self.find(data)?;
        let slot = self.slots.get_mut(data.index() as usize)?;
        // SAFETY: exclusive slot and LIVE proves initialized T.
        Some((
            unsafe { slot.entry.get_mut().assume_init_mut() },
            &mut slot.link,
        ))
    }
    /// # Safety
    /// T must be exclusively borrowed; all returned references must end before
    /// removal, reuse or destruction. External synchronization is required.
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn get_shared(&self, key: K) -> Option<(&mut T, &ShareU64)> {
        let slot = self.find(key.data())?;
        // SAFETY: caller excludes conflicting T accesses; permanent link shared.
        Some((unsafe { &mut *slot.value_ptr() }, &slot.link))
    }
    /// # Safety
    /// Valid initialized LIVE key; no conflicting mutation/removal until refs end.
    pub unsafe fn get_unchecked(&self, key: K) -> (&T, &ShareU64) {
        // SAFETY: valid LIVE key required by caller.
        let slot = unsafe { self.slots.get_unchecked(key.data().index() as usize) };
        slot.version.load(Ordering::Acquire);
        (unsafe { &*slot.value_ptr() }, &slot.link)
    }
    /// # Safety
    /// Valid initialized LIVE key in this exclusively borrowed map.
    pub unsafe fn get_unchecked_mut(&mut self, key: K) -> (&mut T, &mut ShareU64) {
        // SAFETY: caller supplies valid key, map is exclusive.
        let slot = self
            .slots
            .get_mut(key.data().index() as usize)
            .expect("valid LIVE key");
        unsafe { (slot.entry.get_mut().assume_init_mut(), &mut slot.link) }
    }
    /// # Safety
    /// Valid LIVE key and the complete get_shared exclusivity/lifetime contract.
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn get_shared_unchecked(&self, key: K) -> (&mut T, &ShareU64) {
        let slot = unsafe { self.slots.get_unchecked(key.data().index() as usize) };
        slot.version.load(Ordering::Acquire);
        (unsafe { &mut *slot.value_ptr() }, &slot.link)
    }
    pub fn remove(&mut self, key: K) -> Option<T> {
        unsafe { self.remove_shared(key) }
    }
    pub fn remove_with_link(&mut self, key: K) -> Option<(T, u64)> {
        unsafe { self.remove_shared_with_link(key) }
    }
    /// # Safety
    /// All target T/link references must have ended; exclude conflicting access
    /// and scans, synchronize across threads. Internal late FREE observers allowed.
    pub unsafe fn remove_shared(&self, key: K) -> Option<T> {
        unsafe { self.remove_shared_with_link(key) }.map(|(value, _)| value)
    }
    /// # Safety
    /// Same exclusivity and ended-reference contract as remove_shared.
    pub unsafe fn remove_shared_with_link(&self, key: K) -> Option<(T, u64)> {
        let data = key.data();
        let slot = self.find(data)?;
        if slot
            .version
            .compare_exchange(
                data.version(),
                data.version() + 1,
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
        self.push_free(data.index(), slot);
        #[cfg(feature = "stats")]
        self.free.fetch_add(1, Ordering::Relaxed);
        Some((value, link))
    }
    pub fn replace(&mut self, key: K, value: T) -> Result<T, T> {
        unsafe { self.replace_shared(key, value) }
    }
    pub fn replace_with_link(&mut self, key: K, value: T, link: u64) -> Result<(T, u64), (T, u64)> {
        unsafe { self.replace_shared_with_link(key, value, link) }
    }
    /// # Safety
    /// Exclude all conflicting T references, mutation, deletion and scanning.
    pub unsafe fn replace_shared(&self, key: K, value: T) -> Result<T, T> {
        let Some(slot) = self.find(key.data()) else {
            return Err(value);
        };
        // SAFETY: caller ensures initialized T is exclusively accessed.
        Ok(unsafe { ptr::replace(slot.value_ptr(), value) })
    }
    /// # Safety
    /// replace_shared contract plus no concurrent user link operations. Late
    /// internal FREE observers may still load the permanent link's arbitrary bits.
    pub unsafe fn replace_shared_with_link(
        &self,
        key: K,
        value: T,
        link: u64,
    ) -> Result<(T, u64), (T, u64)> {
        let Some(slot) = self.find(key.data()) else {
            return Err((value, link));
        };
        let old_link = slot.link.load(Ordering::Relaxed);
        let old = unsafe { ptr::replace(slot.value_ptr(), value) };
        slot.link.store(link, Ordering::Relaxed);
        Ok((old, old_link))
    }
    pub fn iter(&self) -> Iter<'_, K, T> {
        Iter {
            map: self,
            next: 0,
            end: self.max(),
        }
    }
    pub fn iter_mut(&mut self) -> IterMut<'_, K, T> {
        IterMut {
            slots: self.slots.slice_mut(0..self.max() as usize),
            borrow: PhantomData,
        }
    }
}
impl<K: Key, T> Index<K> for SlotMap<K, T> {
    type Output = T;
    fn index(&self, key: K) -> &T {
        self.get(key).expect("invalid SlotMap key").0
    }
}
impl<K: Key, T> IndexMut<K> for SlotMap<K, T> {
    fn index_mut(&mut self, key: K) -> &mut T {
        self.get_mut(key).expect("invalid SlotMap key").0
    }
}
impl<K: Key, T: Debug> Debug for SlotMap<K, T> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.debug_map().entries(self.iter()).finish()
    }
}
pub struct Iter<'a, K: Key, T> {
    map: &'a SlotMap<K, T>,
    next: u32,
    end: u32,
}
impl<'a, K: Key, T> Iterator for Iter<'a, K, T> {
    type Item = (K, (&'a T, &'a ShareU64));
    fn next(&mut self) -> Option<Self::Item> {
        while self.next < self.end {
            let index = self.next;
            self.next += 1;
            let slot = self.map.slots.get(index as usize)?;
            let version = slot.version.load(Ordering::Acquire);
            if live(version) {
                let key = checked_key(index, version);
                // SAFETY: LIVE published T; removal cannot overlap this scan.
                return Some((key, (unsafe { &*slot.value_ptr() }, &slot.link)));
            }
        }
        None
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some((self.end - self.next) as usize))
    }
}
pub struct IterMut<'a, K: Key, T> {
    slots: pi_arr::IterMut<'a, Slot<T>>,
    borrow: PhantomData<&'a mut SlotMap<K, T>>,
}
impl<'a, K: Key, T> Iterator for IterMut<'a, K, T> {
    type Item = (K, (&'a mut T, &'a mut ShareU64));
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((index, slot)) = self.slots.next() {
            let version = slot.version.load(Ordering::Acquire);
            if live(version) {
                let key = checked_key(index as u32, version);
                return Some((
                    key,
                    (
                        unsafe { slot.entry.get_mut().assume_init_mut() },
                        &mut slot.link,
                    ),
                ));
            }
        }
        None
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.slots.size_hint().1)
    }
}
