//! 支持通过共享引用插入的版本化槽表。
//! FREE 槽的 link 保存空闲链标识；LIVE 槽的 link 由用户使用。
//! 共享插入不意味着可以并发删除或修改 T：删除前必须终止目标槽的所有引用，
//! 本库不提供 EBR 或两阶段退休。
//! len/is_empty 扫描已有槽位，复杂度 O(max)，并发时不提供一致性快照。
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
    let data = KeyData::new(index, version);
    let key = K::from(data);
    assert_eq!(
        key.data(),
        data,
        "SlotMap Key must preserve both index and version"
    );
    key
}

/// 可通过共享引用插入的版本化槽表。键由 32 位索引和 32 位版本组成。
///
/// 使用保留完整索引与版本的键类型（如 DefaultKey）；仅保存索引的键类型
/// 无法表示本表的版本，生成键时会 panic。不同表的键不具备实例身份校验。
/// 初始空槽版本为 1，存活版本为 2、4、...、u32::MAX - 1；耗尽后不再复用该槽。
/// 共享插入可与读取并行；安全删除、替换与可变借用依赖 &mut self，
/// 共享引用上的删除和替换仅在调用者满足各自的安全前提时可用。
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
/// 认领空槽失败的原因。
pub enum ReserveError {
    /// 新索引未通过 predicate；已有的空闲槽不会调用 predicate。
    IndexRejected,
    /// 新索引已达上限且没有可复用的空闲槽。
    IndexExhausted,
}
/// 已认领但尚未写入值的槽位写入者。
///
/// 可先通过 key 取得预定键来构造含自身键的值；提交前该键不可用于读取值。
/// 放弃写入者会消耗一代版本；forget 只泄漏未初始化的空槽。
/// ```compile_fail
/// use pi_slot::{DefaultKey, SlotMap};
/// let writer = {
///     let map = SlotMap::<DefaultKey, u32>::new();
///     map.try_insert_if(|_| true).unwrap()
/// };
/// writer.insert(1);
/// ```
pub struct SlotWriter<'a, K: Key, T> {
    candidate: Candidate<'a, K, T>,
    key: K,
}
impl<K: Key, T> SlotWriter<'_, K, T> {
    /// 返回预定键的副本；调用 insert 前该键尚不可读取值。
    pub fn key(&self) -> K {
        self.key
    }

    /// 以默认 link=0 提交值并返回该键。
    pub fn insert(self, value: T) -> K {
        self.insert_with_link(value, 0)
    }
    /// 提交值及用户 link，并返回该键。提交后其他线程可经同步读取值。
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
    /// 创建空槽表，不预分配槽位。
    pub fn new() -> Self {
        Self::with_capacity(0)
    }
    /// 按给定容量创建空槽表；超过支持的索引范围时 panic。
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
    /// 认领一个空槽并返回写入者；仅分配新索引时调用 predicate。
    ///
    /// 空闲槽复用不经过 predicate。返回 IndexRejected 表示新索引被拒绝，
    /// IndexExhausted 表示索引已耗尽。放弃写入者会消耗该槽的一代版本；
    /// 对新索引，放弃写入者后高水位不会回退，即使值尚未插入。
    pub fn try_insert_if(
        &self,
        predicate: impl FnMut(u32) -> bool,
    ) -> Result<SlotWriter<'_, K, T>, ReserveError> {
        let candidate = self.claim(predicate)?;
        let key = checked_key(candidate.index, candidate.version);
        Ok(SlotWriter { candidate, key })
    }
    /// 通过共享引用插入值并返回键；无可用槽位时 panic。
    pub fn insert(&self, value: T) -> K {
        self.insert_with_link(value, 0)
    }
    /// 先将预定键传给闭包构造值，再提交到槽位。
    ///
    /// 闭包执行期间键尚未存活，不能通过它读取值；闭包 panic 时不提交值，
    /// 但已认领槽位会消耗一代版本。索引耗尽时 panic。
    pub fn insert_with_key(&self, f: impl FnOnce(K) -> T) -> K {
        let writer = self.try_insert_if(|_| true)
            .unwrap_or_else(|_| panic!("SlotMap index limit exhausted"));
        let value = f(writer.key);
        writer.insert(value)
    }
    /// 将预定键传给闭包；成功时插入值并返回键，闭包报错时返回原错误。
    ///
    /// 闭包报错时不提交值，但会消耗一代版本，并可能推进新索引的高水位；
    /// 索引耗尽时与 insert 一样 panic，而不是返回 E。
    pub fn try_insert_with_key<E>(
        &self,
        f: impl FnOnce(K) -> Result<T, E>,
    ) -> Result<K, E> {
        let writer = self.try_insert_if(|_| true)
            .unwrap_or_else(|_| panic!("SlotMap index limit exhausted"));
        let value = f(writer.key)?;
        Ok(writer.insert(value))
    }
    /// 插入值并设置用户 link；无可用槽位时 panic。
    pub fn insert_with_link(&self, value: T, link: u64) -> K {
        self.try_insert_if(|_| true)
            .unwrap_or_else(|_| panic!("SlotMap index limit exhausted"))
            .insert_with_link(value, link)
    }
    /// 尝试插入值，失败时返回未消耗的原值。
    pub fn alloc(&self, value: T) -> Result<K, T> {
        self.alloc_with_link(value, 0).map_err(|(value, _)| value)
    }
    /// 尝试插入值和 link，失败时返回两项原输入。
    pub fn alloc_with_link(&self, value: T, link: u64) -> Result<K, (T, u64)> {
        match self.try_insert_if(|_| true) {
            Ok(writer) => Ok(writer.insert_with_link(value, link)),
            Err(_) => Err((value, link)),
        }
    }
    /// insert 的独占引用别名；不替换已有键对应的值。
    pub fn set(&mut self, value: T) -> K {
        self.insert(value)
    }
    /// insert_with_link 的独占引用别名。
    pub fn set_with_link(&mut self, value: T, link: u64) -> K {
        self.insert_with_link(value, link)
    }
    /// 扫描存活版本计数，复杂度 O(max)；并发时不是一致性快照。
    /// 不调用键类型的回调。
    pub fn len(&self) -> usize {
        self.slots
            .segments(0..self.max() as usize)
            .flat_map(|segment| segment.iter())
            .filter(|slot| live(slot.version.load(Ordering::Acquire)))
            .count()
    }
    /// 判断槽表是否为空；同 len 一样需要扫描，并发时不是一致性快照。
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    #[cfg(feature = "stats")]
    /// 返回累计成功插入次数；仅启用 stats 时可用，计数可能回绕。
    pub fn alloc_count(&self) -> usize {
        self.alloc.load(Ordering::Relaxed)
    }
    #[cfg(feature = "stats")]
    /// 返回累计成功删除次数；仅启用 stats 时可用，计数可能回绕。
    pub fn free_count(&self) -> usize {
        self.free.load(Ordering::Relaxed)
    }
    /// 返回已认领新索引的高水位；删除不会降低该值。
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
    /// 用键查询存活值及其用户 link；键无效或已删除时返回 None。
    pub fn get(&self, key: K) -> Option<(&T, &ShareU64)> {
        let slot = self.find(key.data())?;
        // SAFETY: LIVE Acquire observes T; safe removal needs exclusive map.
        Some((unsafe { &*slot.value_ptr() }, &slot.link))
    }
    /// 独占借用存活值及其用户 link；键无效或已删除时返回 None。
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
    /// 通过共享引用取得值的可变引用和 link 的共享引用。
    ///
    /// # Safety
    /// 调用者必须排除目标 T 的所有冲突访问，且在删除、复用或销毁前终止
    /// 返回的全部引用；跨线程使用时必须自行同步。
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn get_shared(&self, key: K) -> Option<(&mut T, &ShareU64)> {
        let slot = self.find(key.data())?;
        // SAFETY: caller excludes conflicting T accesses; permanent link shared.
        Some((unsafe { &mut *slot.value_ptr() }, &slot.link))
    }
    /// 不验证键的边界和版本，返回值及 link 的共享引用。
    ///
    /// # Safety
    /// 键必须属于本表的已初始化存活槽；引用存活期间不得冲突修改或删除。
    pub unsafe fn get_unchecked(&self, key: K) -> (&T, &ShareU64) {
        // SAFETY: valid LIVE key required by caller.
        let slot = unsafe { self.slots.get_unchecked(key.data().index() as usize) };
        slot.version.load(Ordering::Acquire);
        (unsafe { &*slot.value_ptr() }, &slot.link)
    }
    /// 不验证键的边界和版本，返回值及 link 的可变引用。
    ///
    /// # Safety
    /// 键必须属于本表的已初始化存活槽；调用者须持有表的独占借用。
    pub unsafe fn get_unchecked_mut(&mut self, key: K) -> (&mut T, &mut ShareU64) {
        // SAFETY: caller supplies valid key, map is exclusive.
        let slot = self
            .slots
            .get_mut(key.data().index() as usize)
            .expect("valid LIVE key");
        unsafe { (slot.entry.get_mut().assume_init_mut(), &mut slot.link) }
    }
    /// 不验证键的边界和版本，取得共享表中的可变值引用。
    ///
    /// # Safety
    /// 除键必须有效且存活外，还须满足 get_shared 的全部排他和引用生命周期前提。
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn get_shared_unchecked(&self, key: K) -> (&mut T, &ShareU64) {
        let slot = unsafe { self.slots.get_unchecked(key.data().index() as usize) };
        slot.version.load(Ordering::Acquire);
        (unsafe { &mut *slot.value_ptr() }, &slot.link)
    }
    /// 删除存活键并返回值；键无效时返回 None。调用需要独占借用表。
    pub fn remove(&mut self, key: K) -> Option<T> {
        unsafe { self.remove_shared(key) }
    }
    /// 删除存活键并返回值及用户 link 的当前快照；键无效时返回 None。
    pub fn remove_with_link(&mut self, key: K) -> Option<(T, u64)> {
        unsafe { self.remove_shared_with_link(key) }
    }
    /// 通过共享引用删除存活键并返回值；键无效时返回 None。
    ///
    /// # Safety
    /// 目标 T 和 link 的所有引用必须已终止；调用者须排除冲突的访问和扫描，
    /// 跨线程还须自行同步。内部迟到的空闲链观察者由实现处理。
    pub unsafe fn remove_shared(&self, key: K) -> Option<T> {
        unsafe { self.remove_shared_with_link(key) }.map(|(value, _)| value)
    }
    /// 通过共享引用删除键并返回值及用户 link 快照。
    ///
    /// # Safety
    /// 与 remove_shared 相同：目标引用均已终止且不存在冲突访问或扫描。
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
    /// 替换存活键的值并返回旧值；无效键返回未消耗的新值。
    /// 不改变键的版本和用户 link。
    pub fn replace(&mut self, key: K, value: T) -> Result<T, T> {
        unsafe { self.replace_shared(key, value) }
    }
    /// 同时替换值与用户 link；失败时返回未消耗的新值及 link。
    /// 成功时返回旧值及旧 link 快照，不改变键的版本。
    pub fn replace_with_link(&mut self, key: K, value: T, link: u64) -> Result<(T, u64), (T, u64)> {
        unsafe { self.replace_shared_with_link(key, value, link) }
    }
    /// 通过共享引用替换存活键的值；失败时返回原新值。
    ///
    /// # Safety
    /// 必须排除目标 T 的冲突引用、修改、删除与扫描。
    pub unsafe fn replace_shared(&self, key: K, value: T) -> Result<T, T> {
        let Some(slot) = self.find(key.data()) else {
            return Err(value);
        };
        // SAFETY: caller ensures initialized T is exclusively accessed.
        Ok(unsafe { ptr::replace(slot.value_ptr(), value) })
    }
    /// 通过共享引用同时替换值与用户 link；失败时返回原输入。
    ///
    /// # Safety
    /// 除 replace_shared 的排他前提外，不得有并发的用户 link 操作；
    /// 内部迟到的空闲链观察者仍可能读取 link 的任意位。
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
    /// 按索引顺序遍历存活槽，返回键、值及用户 link 的共享引用。
    /// 并发插入时不保证是同一时刻的快照；删除须遵守独占借用要求。
    pub fn iter(&self) -> Iter<'_, K, T> {
        Iter {
            map: self,
            next: 0,
            end: self.max(),
        }
    }
    /// 独占遍历存活槽，返回键、值及用户 link 的可变引用。
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
/// 按索引扫描存活槽的共享迭代器；元素为 (K, (&T, &ShareU64))。
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
/// 独占遍历存活槽的迭代器；元素为 (K, (&mut T, &mut ShareU64))。
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
