//! 支持通过共享引用插入的版本化槽表。
//! FREE 槽的 link 保存空闲链标识；LIVE 槽的 link 由用户使用。
//! 共享插入不意味着可以并发删除或修改 T：删除前必须终止目标槽的所有引用，
//! 本库不提供 EBR 或两阶段退休。
//! len/is_empty 通过累计插入、删除次数计算，复杂度 O(1)；并发时不提供一致性快照。
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

#[path = "slotmap_inner.rs"]
mod inner;

use crossbeam_utils::CachePadded;
use pi_arr::SegmentedArr as Arr;
pub use pi_key::{DefaultKey, Key, KeyData};
use pi_share::ShareU32;
pub use pi_share::ShareU64;
use pi_share::ShareUsize;
use std::cell::UnsafeCell;
use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::{Index, IndexMut};
use std::ptr;
use std::sync::atomic::Ordering;

// 新索引的排他上限；保留原有边界余量。
const MAX_ENTRIES: usize = u32::MAX as usize - 32;
// 空闲链结束标识；高 32 位为零，低 32 位为无效索引。
const NULL: u64 = u32::MAX as u64;

/// 稳定地址的槽表示；仅 LIVE 版本对应已初始化的 T，字段顺序保持 C 布局。
#[repr(C)]
struct Slot<T, const N: u32 = 0> {
    // FREE 时为下一空闲槽完整标识，LIVE 时为用户 link；地址不随复用改变。
    link: ShareU64,
    // 由版本占用位决定是否初始化的值存储；不隐含共享可变访问许可。
    entry: UnsafeCell<MaybeUninit<T>>,
    // 低 N 位为用户 bits，第 N 位为 LIVE，其余位与占用位共同形成代际。
    version: ShareU32,
}

// SAFETY: 发布 LIVE 前初始化 T；共享修改和删除由调用者保证排他。
// 元组约束检查实际 ShareU32 的 Sync，上游特征合并不能放宽此条件。
// SlotMap 的线程特征由真实字段推导，不添加无条件实现。
unsafe impl<T: Send + Sync, const N: u32> Sync for Slot<T, N> where (T, ShareU32): Sync {}

impl<T, const N: u32> Slot<T, N> {
    // self 可未初始化；返回值存储的裸指针，解引用前必须另证 LIVE 与排他条件。
    fn value_ptr(&self) -> *mut T {
        self.entry.get().cast::<T>()
    }
}
impl<T, const N: u32> Default for Slot<T, N> {
    // 返回版本为零、link 为空、T 尚未初始化的槽，不构造 T。
    fn default() -> Self {
        Self {
            link: ShareU64::new(NULL),
            entry: UnsafeCell::new(MaybeUninit::uninit()),
            version: ShareU32::new(0),
        }
    }
}
impl<T, const N: u32> Drop for Slot<T, N> {
    // self 为最终独占槽；先清 LIVE 再析构值，析构 panic 时字段仍由 drop glue 清理。
    fn drop(&mut self) {
        if live::<N>(*self.version.get_mut()) {
            *self.version.get_mut() &= !(1u32 << N);
            // SAFETY: 最终独占所有者且 LIVE 证明已初始化；先撤销占用避免重复析构。
            unsafe { self.entry.get_mut().assume_init_drop() };
        }
    }
}
// version 为完整版本，N 必须小于 32；返回占用位是否置位，不修改状态。
fn live<const N: u32>(version: u32) -> bool {
    version & (1u32 << N) != 0
}
// index 为槽索引，version 为完整版本；返回高版本、低索引的 64 位空闲链标识。
fn encode(index: u32, version: u32) -> u64 {
    (u64::from(version) << 32) | u64::from(index)
}
// index 与 version 组成完整键；返回无损的 K，转换不保留任一部分时 panic。
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
/// 低 N 位为用户 bits，第 N 位为占用位；释放与复用以回绕加法增加 1 << N。
/// 相同 bits 下，代际经过 2^(31-N) 个周期重复。N 必须小于 32。
/// 并发空闲链操作不得跨越目标槽的完整代际循环；不处理该极端 ABA 情形。
/// 共享插入可与读取并行；安全删除、替换与可变借用依赖 &mut self，
/// 共享引用上的删除和替换仅在调用者满足各自的安全前提时可用。
#[repr(C)]
pub struct SlotMap<K: Key = DefaultKey, T = (), const N: u32 = 0> {
    // 空闲链头的完整索引与版本，NULL 表示空链；独立缓存行减少争用。
    free_head: CachePadded<ShareU64>,
    // 分段稳定地址存储；高水位范围内也可能存在尚未分配的洞。
    slots: Arr<Slot<T, N>>,
    // 累计成功插入次数；先计数后发布 LIVE，按 usize 回绕。
    alloc: CachePadded<ShareUsize>,
    // 累计成功删除次数；先归还空闲链再计数，按 usize 回绕。
    free: CachePadded<ShareUsize>,
    // 已认领新索引的高水位，不等同于已分配容量或实时存活数。
    next_index: ShareU32,
    // 保持键类型及其自动特征关系，不存储实际键。
    key_type: PhantomData<K>,
}
/// 独占认领的未初始化槽；未提交时析构消耗预定代际并归还空闲链。
struct Candidate<'a, K: Key, T, const N: u32 = 0> {
    // 所属表的共享借用，保证槽存储在借用期间存活。
    map: &'a SlotMap<K, T, N>,
    // 已由空闲链或新索引认领的槽；当前候选独占其未初始化值存储。
    slot: &'a Slot<T, N>,
    // 已认领的槽索引，用于构造键与回滚归链。
    index: u32,
    // 预定 LIVE 版本；零表示已提交，非零候选放弃时消耗一代。
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

/// 元数据 CAS 失败，不代表获得值的任何访问权限。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CompareExchangeBitsError {
    /// 索引缺失、非 LIVE 或代际身份不符。
    Stale,
    /// 同代当前业务位与显式 expected_bits 不同。
    Mismatch {
        /// CAS 失败时观察到的低 N 位，不是后续状态保证。
        actual_bits: u32,
    },
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
pub struct SlotWriter<'a, K: Key, T, const N: u32 = 0> {
    // 持有认领和回滚责任；写入完成后清除其版本标记。
    candidate: Candidate<'a, K, T, N>,
    // 已验证无损的预定键；提交前不可据此读取值。
    key: K,
}
impl<K: Key, T, const N: u32> SlotWriter<'_, K, T, N> {
    /// 返回预定键的副本；调用 insert 前该键尚不可读取值。
    /// self 为尚未提交的写入者；返回预定键副本，不改变认领状态。
    pub fn key(&self) -> K {
        inner::writer_key(self)
    }

    /// value 为交付槽表所有权的值；消费已认领的 self，返回预定键，默认 link 为零。
    /// 此处不再分配或转换键；发布顺序与状态转移见 SlotWriter::insert_with_link。
    pub fn insert(self, value: T) -> K {
        inner::writer_insert(self, value)
    }
    /// 提交值及用户 link，并返回该键。提交后其他线程可经同步读取值。
    /// value 为交付槽表所有权的值，link 为完整 64 位用户数据；返回已发布的键。
    /// 消费已认领的 self，不再分配或转换键；返回前完成发布并取消候选回滚。
    /// 成功发布后才可读取该键；中间写入操作不运行用户代码。
    pub fn insert_with_link(self, value: T, link: u64) -> K {
        // 设计已确认（仅保持既有行为的转换）：沿用既有发布顺序。
        // 伪码：写入未初始化 T → 写用户 link → 累加插入计数 → Release 发布 LIVE
        // → 清候选版本以取消回滚 → 返回预定键；不在初始化前运行用户回调。
        inner::writer_insert_with_link(self, value, link)
    }
}
impl<K: Key, T, const N: u32> Drop for Candidate<'_, K, T, N> {
    // self 未提交时消耗预定代际并归链；已提交时无操作，不改统计，返回 ()。
    fn drop(&mut self) {
        inner::candidate_drop(self)
    }
}
impl<K: Key, T, const N: u32> Default for SlotMap<K, T, N> {
    /// 返回 SlotMap::new 创建的空表；N >= 32 时 panic。
    fn default() -> Self {
        inner::map_default::<K, T, N>()
    }
}
impl<K: Key, T, const N: u32> Drop for SlotMap<K, T, N> {
    /// self 为最终独占所有者；析构全部 LIVE 值后传播首个析构 panic，返回 ()。
    fn drop(&mut self) {
        // 设计已确认（仅保持既有行为的转换）：沿用既有析构传播策略。
        // 伪码：遍历已分配槽 → 撤销 LIVE 后移出并析构 T；捕获首个 panic，
        // 后续 panic 载荷按原实现遗忘 → 全部槽处理后恢复首个 panic，避免二次析构。
        inner::map_drop(self)
    }
}
impl<K: Key, T, const N: u32> SlotMap<K, T, N> {
    /// 创建空槽表，不预分配槽位。
    /// 返回空表；N 必须小于 32，否则 panic。
    pub fn new() -> Self {
        inner::map_new::<K, T, N>()
    }
    /// 按给定容量创建空槽表；超过支持的索引范围时 panic。
    /// capacity 为预分配容量，不增加高水位或长度；返回空表。
    /// N >= 32 或 capacity > MAX_ENTRIES 时 panic；底层分配失败遵循分配器行为。
    pub fn with_capacity(capacity: usize) -> Self {
        inner::map_with_capacity::<K, T, N>(capacity)
    }
    // self 允许共享插入；返回成功摘取的空闲索引，空链返回 None。
    // 迟到观察者在完整链头 CAS 成功前不解引用 next；不覆盖完整版本回绕的 ABA。
    fn pop_free(&self) -> Option<u32> {
        // 设计已确认（仅保持既有行为的转换）：沿用完整 id 空闲链协议。
        // 伪码：循环 Acquire 读取链头；NULL 表示空链，立即返回 None；
        // 否则读取链头槽的 link 作为 next，仅按原始位保存，不提前解引用或校验 next 目标；
        // 对完整 id（索引与版本）执行 head → next 的 CAS；成功返回摘取索引，
        // 失败重新读取链头并重试，重试时仍可能遇到空链；不处理完整代际回绕 ABA。
        inner::map_pop_free(self)
    }
    // predicate 接收待分配的新索引，返回是否允许认领；复用空闲槽时不调用它。
    // 返回独占候选；索引耗尽返回 IndexExhausted，最后一次回调拒绝或 rc 重入检查失败返回 IndexRejected。
    // 回调可能因竞争重试；回调 panic 不由本方法捕获。候选放弃不回退高水位，不增加插入计数。
    fn claim(
        &self,
        predicate: impl FnMut(u32) -> bool,
    ) -> Result<Candidate<'_, K, T, N>, ReserveError> {
        // 设计已确认（仅保持既有行为的转换）：下述仅还原既有算法，不推定新设计决定。
        // 伪码：先尝试摘取 FREE → 成功则预消耗代际并返回候选；
        // 否则重试认领新索引（上限 → predicate → rc 原有重入校验）；
        // 成功后分配槽、预消耗代际；失败区分耗尽与拒绝。
        // 候选放弃由 Candidate::drop 消耗预定代际并归链；提交见 SlotWriter::insert_with_link。
        inner::map_claim(self, predicate)
    }
    // index 与 slot 必须属于本表同一已释放槽，且没有其他归链者；slot 版本已为 FREE。
    // 将完整标识以 Release 发布到链头；竞争时重试，不修改统计计数，返回 ()。
    fn push_free(&self, index: u32, slot: &Slot<T, N>) {
        inner::map_push_free(self, index, slot)
    }
    /// 认领一个空槽并返回写入者；仅分配新索引时调用 predicate。
    ///
    /// 空闲槽复用不经过 predicate。返回 IndexRejected 表示新索引被拒绝，
    /// IndexExhausted 表示索引已耗尽。放弃写入者会消耗该槽的一代版本；
    /// 对新索引，放弃写入者后高水位不会回退，即使值尚未插入。
    /// predicate 为新索引准入回调，允许重试与重入；返回未初始化的写入者。
    /// 认领、拒绝、耗尽与回滚规则见 SlotMap::claim；键转换失败会 panic 并释放候选。
    pub fn try_insert_if(
        &self,
        predicate: impl FnMut(u32) -> bool,
    ) -> Result<SlotWriter<'_, K, T, N>, ReserveError> {
        inner::map_try_insert_if(self, predicate)
    }
    /// 通过共享引用插入值并返回键；无可用槽位时 panic。
    /// value 为交付槽表所有权的值；返回新键，默认用户 link 为零。
    /// 分配耗尽或键转换不保留完整索引与版本时 panic；已认领候选按回滚规则处理。
    /// 认领与提交顺序见 SlotMap::claim、SlotWriter::insert_with_link。
    pub fn insert(&self, value: T) -> K {
        inner::map_insert(self, value)
    }
    /// 先将预定键传给闭包构造值，再提交到槽位。
    ///
    /// 闭包执行期间键尚未存活，不能通过它读取值；闭包 panic 时不提交值，
    /// 但已认领槽位会消耗一代版本。索引耗尽时 panic。
    /// f 接收预定键并构造 value；返回提交后的键，默认 link 为零。
    /// 认领流程见 SlotMap::claim，提交流程见 SlotWriter::insert_with_link；f 可重入表但不能读取尚未提交的值。
    /// 自定义键转换不保留完整索引与版本时 panic，候选会回滚。
    pub fn insert_with_key(&self, f: impl FnOnce(K) -> T) -> K {
        inner::map_insert_with_key(self, f)
    }
    /// 将预定键传给闭包；成功时插入值并返回键，闭包报错时返回原错误。
    ///
    /// 闭包报错时不提交值，但会消耗一代版本，并可能推进新索引的高水位；
    /// 索引耗尽时与 insert 一样 panic，而不是返回 E。
    /// f 接收预定键，返回要提交的值或 E；成功返回新键，失败原样返回 E。
    /// 认领流程见 SlotMap::claim，提交流程见 SlotWriter::insert_with_link；f 可重入，返回错误或 panic 时候选回滚。
    /// 自定义键转换不保留完整索引与版本时 panic。
    pub fn try_insert_with_key<E>(&self, f: impl FnOnce(K) -> Result<T, E>) -> Result<K, E> {
        inner::map_try_insert_with_key(self, f)
    }
    /// 插入值并设置用户 link；无可用槽位时 panic。
    /// value 为交付槽表所有权的值，link 为完整 64 位用户数据；返回已发布的键。
    /// 表入口分配耗尽或键转换失败时 panic；写入者入口消费 self，仅提交已认领槽。
    /// 成功发布后才可读取该键；认领流程见 SlotMap::claim。
    pub fn insert_with_link(&self, value: T, link: u64) -> K {
        inner::map_insert_with_link(self, value, link)
    }
    /// 尝试插入值，失败时返回未消耗的原值。
    /// value 为待交付值；返回新键，默认 link 为零。
    /// 只将认领拒绝或耗尽映射为 Err(value)，原值不丢失；键转换失败仍 panic。
    /// 认领与提交流程见 SlotMap::claim、SlotWriter::insert_with_link。
    pub fn alloc(&self, value: T) -> Result<K, T> {
        inner::map_alloc(self, value)
    }
    /// 尝试插入值和 link，失败时返回两项原输入。
    /// value 为待交付值，link 为用户数据；成功返回新键。
    /// 认领拒绝或耗尽返回 Err((value, link))，保留两项输入；键转换失败仍 panic。
    /// 认领与提交流程见 SlotMap::claim、SlotWriter::insert_with_link。
    pub fn alloc_with_link(&self, value: T, link: u64) -> Result<K, (T, u64)> {
        inner::map_alloc_with_link(self, value, link)
    }
    /// insert 的独占引用别名；不替换已有键对应的值。
    /// self 为独占表，value 为待插入值；返回新键，默认 link 为零。
    /// 继承 SlotMap::insert 的 panic、认领与提交规则。
    pub fn set(&mut self, value: T) -> K {
        inner::map_set(self, value)
    }
    /// insert_with_link 的独占引用别名。
    /// self 为独占表，value 为待插入值，link 为用户数据；返回新键。
    /// 继承 SlotMap::insert_with_link 的 panic、认领与提交规则。
    pub fn set_with_link(&mut self, value: T, link: u64) -> K {
        inner::map_set_with_link(self, value, link)
    }
    /// 从累计成功插入和删除次数计算长度，复杂度 O(1)。
    /// 并发时两次读取不构成一致性快照，结果可能暂时不等于存活槽数；
    /// 计数回绕时使用模 usize 的差值。读取顺序防止计数对倒挂，
    /// 但空闲槽可能先被复用，旧删除才增加 free，此时结果甚至可大于 max()。
    /// 并发观测不能替代迭代或同步后的精确长度。
    /// self 可被共享插入；返回 free 先读、alloc 后读的模 usize 差值，不修改状态。
    pub fn len(&self) -> usize {
        inner::map_len(self)
    }
    /// 判断槽表是否为空；同 len 一样不保证并发一致性快照。
    /// 返回 SlotMap::len 是否为零，不修改状态；并发时不可作为同步或精确空表证明。
    pub fn is_empty(&self) -> bool {
        inner::map_is_empty(self)
    }
    /// 返回累计成功插入次数；计数可能回绕。
    /// 返回累计提交次数的 Relaxed 观测值，不修改状态，不构成同步屏障。
    pub fn alloc_count(&self) -> usize {
        inner::map_alloc_count(self)
    }
    /// 返回累计成功删除次数；计数可能回绕。
    /// 返回累计删除次数的 Relaxed 观测值，不修改状态，不构成同步屏障。
    pub fn free_count(&self) -> usize {
        inner::map_free_count(self)
    }
    /// 返回已认领新索引的高水位；删除不会降低该值。
    /// 返回新索引高水位的 Acquire 观测值，不修改状态；不保证此前所有槽已分配。
    pub fn max(&self) -> u32 {
        inner::map_max(self)
    }
    /// 按索引升序重建空闲链，不搬迁元素、不改变版本或高水位。
    /// 独占维护也会回收已 forget 的 writer；其预定代际已在认领时消耗。
    /// self 必须独占；返回 ()，仅重建 FREE 槽 link 和链头，存活值及用户 link 不变。
    pub fn compact(&mut self) {
        // 设计已确认（仅保持既有行为的转换）：独占重建空闲链。
        // 伪码：以 NULL 初始化新链头，按索引升序扫描高水位内已分配槽，跳过 LIVE；
        // 对 FREE 槽编码完整 id，先令其 link=NULL，再接到前一个 FREE 槽之后；
        // 首个 FREE 槽成为链头，最后一个 FREE 槽保持 NULL 尾终止；
        // 扫描结束写回新链头，无 FREE 槽则为空链，不改版本、存活值或高水位。
        inner::map_compact(self)
    }

    /// 保留高水位内的槽与完整版本，重建存储以释放额外容量。
    /// 存活 key、索引、值及用户 link 不变；所有地址缓存必须重新获取。
    /// self 必须独占；返回 ()，迁移期间不调用 T 的构造或析构。
    /// 底层分配失败遵循分配器行为；重建与空闲链维护见 SlotMap::rebuild、SlotMap::compact。
    pub fn shrink_to_fit(&mut self) {
        inner::map_shrink_to_fit(self)
    }

    /// 丢弃尾部空闲槽及其版本、bits，重建空闲链并缩容；空表高水位为零。
    /// 存活 key 不变，但地址可能改变；后续插入可能重现被截槽的旧 key。
    /// self 必须独占；返回 ()，先找最后存活索引，再按 SlotMap::rebuild 重建。
    /// 底层分配失败遵循分配器行为；截断版本的后续键重现是保留的既有行为。
    pub fn shrink_to_last_occupied(&mut self) {
        inner::map_shrink_to_last_occupied(self)
    }

    // self 必须独占，end 为保留前缀的排他上界，不得越过当前高水位或截断存活值。
    // 返回 ()；先分配再交换所有权，将高水位置为 end，最后调用 SlotMap::compact。
    // 分配失败遵循分配器行为；不调用保留值的构造或析构，所有地址缓存失效。
    fn rebuild(&mut self, end: u32) {
        // 设计已确认（仅保持既有行为的转换）：先分配后迁移，保持值所有权。
        // 伪码：先分配 end 容量的新存储；分配完成后逐槽交换保留前缀的所有权，
        // 不调用保留值的构造或析构；替换表存储，更新高水位为 end，
        // 最后调用 SlotMap::compact 重链（流程单源见该壳），旧地址缓存失效。
        inner::map_rebuild(self, end)
    }

    /// 按索引读取存活槽的用户 bits，不校验代际；不能用于恢复过期 key。
    /// index 为槽索引；存活时返回低 N 位，否则返回 None；不修改状态。
    pub fn get_key_bits(&self, index: u32) -> Option<u32> {
        inner::map_get_key_bits(self, index)
    }

    /// 对业务元数据做一次完整版本强 CAS，不授予或改变 T 的访问权限。
    /// key 提供索引、LIVE 与代际，低 N 位被忽略；expected_bits/new_bits 是显式比较/写入的低 N 位。
    /// 成功返回包含 new_bits 的完整键；同代比较失败返回 Mismatch { actual_bits }，
    /// 非 LIVE、索引缺失或代际改变返回 Stale；失败不修改槽位，不自动重试。
    /// 两个 bits 参数越界时 panic。K::data、K::from 及无损校验可能重入或 panic，
    /// 必须全部在 CAS 前完成；预计算返回键后再对实际完整版本 CAS，不能用回调前观测直接写入。
    /// 成功使用 AcqRel，失败使用 Acquire；仅同步元数据，不能代替值的排他借用。
    pub fn compare_exchange_bits(
        &self,
        key: K,
        expected_bits: u32,
        new_bits: u32,
    ) -> Result<K, CompareExchangeBitsError> {
        // 设计已确认：校验 bits → 提取身份并预计算/验证结果 K（全部用户回调在此完成）
        // → 按索引读取当前完整版本，拒绝 FREE/代际不符为 Stale；
        // 以身份+expected_bits 对完整 version 强 CAS 一次，成功返回预计算 K；
        // 失败按 CAS 返回的版本区分 Stale 或同代 Mismatch，不再运行用户回调或重试。
        inner::map_compare_exchange_bits(self, key, expected_bits, new_bits)
    }

    // data 为完整索引与版本；仅在占用位、已分配槽与完整版本均匹配时返回槽引用。
    // 否则返回 None，不修改状态；高水位内尚未分配的洞也返回 None。
    fn find(&self, data: KeyData) -> Option<&Slot<T, N>> {
        inner::map_find(self, data)
    }
    /// 用键查询存活值及其用户 link；键无效或已删除时返回 None。
    /// key 为完整版本键；返回 (值共享引用, 用户 link 共享引用)，无效时返回 None。
    /// 不修改状态；共享插入可并行，删除与替换仍须遵守各自排他前提。
    pub fn get(&self, key: K) -> Option<(&T, &ShareU64)> {
        inner::map_get(self, key)
    }
    /// 独占借用存活值及其用户 link；键无效或已删除时返回 None。
    /// self 必须独占，key 为完整版本键；返回 (值可变引用, 用户 link 可变引用)。
    /// 无效键返回 None 且不修改状态；取得引用本身不修改值、版本或计数。
    pub fn get_mut(&mut self, key: K) -> Option<(&mut T, &mut ShareU64)> {
        inner::map_get_mut(self, key)
    }
    /// 通过共享引用取得值的可变引用和 link 的共享引用。
    ///
    /// # Safety
    /// 调用者必须排除目标 T 的所有冲突访问，且在删除、复用或销毁前终止
    /// 返回的全部引用；跨线程使用时必须自行同步。
    #[allow(clippy::mut_from_ref)]
    /// key 为完整版本键；匹配时返回 (值可变引用, 用户 link 共享引用)，否则返回 None。
    /// 取得引用本身不修改状态；self 为共享表，排他性完全由调用者负责。
    pub unsafe fn get_shared(&self, key: K) -> Option<(&mut T, &ShareU64)> {
        unsafe { inner::map_get_shared(self, key) }
    }
    /// 不验证键的边界和版本，返回值及 link 的共享引用。
    ///
    /// # Safety
    /// 键必须属于本表的已初始化存活槽；引用存活期间不得冲突修改或删除。
    /// key 为调用者保证有效的完整键；返回 (值共享引用, 用户 link 共享引用)，不修改状态。
    pub unsafe fn get_unchecked(&self, key: K) -> (&T, &ShareU64) {
        unsafe { inner::map_get_unchecked(self, key) }
    }
    /// 不验证键的边界和版本，返回值及 link 的可变引用。
    ///
    /// # Safety
    /// 键必须属于本表的已初始化存活槽；调用者须持有表的独占借用。
    /// self 必须独占，key 为调用者保证有效的完整键；返回 (值可变引用, 用户 link 可变引用)。
    /// 取得引用本身不修改状态；本方法不提供无效键的恢复保证。
    pub unsafe fn get_unchecked_mut(&mut self, key: K) -> (&mut T, &mut ShareU64) {
        unsafe { inner::map_get_unchecked_mut(self, key) }
    }
    /// 不验证键的边界和版本，取得共享表中的可变值引用。
    ///
    /// # Safety
    /// 除键必须有效且存活外，还须满足 get_shared 的全部排他和引用生命周期前提。
    #[allow(clippy::mut_from_ref)]
    /// key 为调用者保证有效的完整键；返回 (值可变引用, 用户 link 共享引用)，不修改状态。
    pub unsafe fn get_shared_unchecked(&self, key: K) -> (&mut T, &ShareU64) {
        unsafe { inner::map_get_shared_unchecked(self, key) }
    }
    /// 删除存活键并返回值；键无效时返回 None。调用需要独占借用表。
    /// self 必须独占，key 为完整版本键；成功返回值的所有权，link 不作为结果返回。
    /// 无效键返回 None；状态转移与统计顺序见 SlotMap::remove_shared_with_link。
    pub fn remove(&mut self, key: K) -> Option<T> {
        inner::map_remove(self, key)
    }
    /// 删除存活键并返回值及用户 link 的当前快照；键无效时返回 None。
    /// self 必须独占，key 为完整版本键；成功返回 (值所有权, 用户 link 快照)。
    /// 无效键返回 None；状态转移与统计顺序见 SlotMap::remove_shared_with_link。
    pub fn remove_with_link(&mut self, key: K) -> Option<(T, u64)> {
        inner::map_remove_with_link(self, key)
    }
    /// 通过共享引用删除存活键并返回值；键无效时返回 None。
    ///
    /// # Safety
    /// 目标 T 和 link 的所有引用必须已终止；调用者须排除冲突的访问和扫描，
    /// 跨线程还须自行同步。内部迟到的空闲链观察者由实现处理。
    /// key 为完整版本键；成功返回值所有权，丢弃结果中的 link 快照；无效键返回 None。
    /// 状态转移与统计顺序见 SlotMap::remove_shared_with_link。
    pub unsafe fn remove_shared(&self, key: K) -> Option<T> {
        unsafe { inner::map_remove_shared(self, key) }
    }
    /// 通过共享引用删除键并返回值及用户 link 快照。
    ///
    /// # Safety
    /// 与 remove_shared 相同：目标引用均已终止且不存在冲突访问或扫描。
    /// key 为完整版本键；成功返回 (值所有权, 用户 link 快照)，键不匹配或既有 CAS 失败返回 None。
    /// None 不归链、不增加删除计数；成功先撤销 LIVE，再取值、归链，最后增加删除计数。
    pub unsafe fn remove_shared_with_link(&self, key: K) -> Option<(T, u64)> {
        // 设计已确认（仅保持既有行为的转换）：沿用既有删除顺序与调用者排他责任。
        // 伪码：完整键查槽 → 原有 CAS 撤销 LIVE；任一步失败返回 None
        // → 读取 link 快照 → 移出 T → 归还空闲链 → 累加删除计数 → 返回值和快照。
        unsafe { inner::map_remove_shared_with_link(self, key) }
    }
    /// 替换存活键的值并返回旧值；无效键返回未消耗的新值。
    /// 不改变键的版本和用户 link。
    /// self 必须独占，key 为完整版本键，value 为新值；成功返回旧值，失败返回原 value。
    /// 成功不改变键、版本、link 或统计；失败不修改槽位。
    pub fn replace(&mut self, key: K, value: T) -> Result<T, T> {
        inner::map_replace(self, key, value)
    }
    /// 同时替换值与用户 link；失败时返回未消耗的新值及 link。
    /// 成功时返回旧值及旧 link 快照，不改变键的版本。
    /// self 必须独占，key 为完整版本键，value 为新值，link 为新用户数据。
    /// 成功返回 (旧值, 旧 link 快照)，失败返回 (原 value, 原 link)，不修改键或统计。
    pub fn replace_with_link(&mut self, key: K, value: T, link: u64) -> Result<(T, u64), (T, u64)> {
        inner::map_replace_with_link(self, key, value, link)
    }
    /// 通过共享引用替换存活键的值；失败时返回原新值。
    ///
    /// # Safety
    /// 必须排除目标 T 的冲突引用、修改、删除与扫描。
    /// key 为完整版本键，value 为新值；成功返回旧值，失败返回未消耗的 value。
    /// 不修改键、版本、link 或统计；失败不修改槽位。
    pub unsafe fn replace_shared(&self, key: K, value: T) -> Result<T, T> {
        unsafe { inner::map_replace_shared(self, key, value) }
    }
    /// 通过共享引用同时替换值与用户 link；失败时返回原输入。
    ///
    /// # Safety
    /// 除 replace_shared 的排他前提外，不得有并发的用户 link 操作；
    /// 内部迟到的空闲链观察者仍可能读取 link 的任意位。
    /// key 为完整版本键，value 为新值，link 为新用户数据；成功返回 (旧值, 旧 link 快照)。
    /// 无效键返回 Err((value, link)) 且不修改槽位；成功先取旧 link、替换值，再写新 link，不修改版本或统计。
    pub unsafe fn replace_shared_with_link(
        &self,
        key: K,
        value: T,
        link: u64,
    ) -> Result<(T, u64), (T, u64)> {
        unsafe { inner::map_replace_shared_with_link(self, key, value, link) }
    }
    /// 按索引顺序遍历存活槽，返回键、值及用户 link 的共享引用。
    /// 并发插入时不保证是同一时刻的快照；删除须遵守独占借用要求。
    /// 返回共享迭代器；self 为共享表，创建时固定高水位，按索引升序跳过洞与 FREE 槽。
    /// 返回元素的元组依次为完整键、(值引用, 用户 link 引用)；不修改表。键转换失败时迭代会 panic。
    pub fn iter(&self) -> Iter<'_, K, T, N> {
        inner::map_iter(self)
    }
    /// 独占遍历存活槽，返回键、值及用户 link 的可变引用。
    /// self 必须独占；返回前缀的独占迭代器，按索引升序跳过 FREE 槽。
    /// 返回元素依次为完整键、(值可变引用, 用户 link 可变引用)；创建迭代器不修改值。键转换失败时迭代会 panic。
    pub fn iter_mut(&mut self) -> IterMut<'_, K, T, N> {
        inner::map_iter_mut(self)
    }
}
impl<K: Key, T, const N: u32> Index<K> for SlotMap<K, T, N> {
    type Output = T;
    /// key 为完整版本键；返回值共享引用，无效键 panic，不修改表。
    fn index(&self, key: K) -> &T {
        inner::map_index(self, key)
    }
}
impl<K: Key, T, const N: u32> IndexMut<K> for SlotMap<K, T, N> {
    /// self 必须独占，key 为完整版本键；返回值可变引用，无效键 panic。
    fn index_mut(&mut self, key: K) -> &mut T {
        inner::map_index_mut(self, key)
    }
}
impl<K: Key, T: Debug, const N: u32> Debug for SlotMap<K, T, N> {
    /// formatter 为输出目标；按迭代顺序格式化键值，返回格式化结果或输出错误。
    /// 不修改表；迭代的键转换及 T::fmt 的 panic 原样传播。
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        inner::map_fmt(self, formatter)
    }
}
/// 按索引扫描存活槽的共享迭代器；元素为 (K, (&T, &ShareU64))。
pub struct Iter<'a, K: Key, T, const N: u32 = 0> {
    // 所属表的共享借用，保证槽存储在借用期间存活。
    map: &'a SlotMap<K, T, N>,
    // 下一待扫描索引，扫描后递增；不回访已越过的洞。
    next: u32,
    // 创建迭代器时截取的高水位，不追踪之后新增的索引。
    end: u32,
}
impl<'a, K: Key, T, const N: u32> Iterator for Iter<'a, K, T, N> {
    type Item = (K, (&'a T, &'a ShareU64));
    /// self 为待继续扫描的迭代器；返回下一存活键及 (值引用, link 引用)，耗尽返回 None。
    /// 推进扫描位置，不修改表；自定义键转换失败时 panic，已越过的位置不回退。
    fn next(&mut self) -> Option<Self::Item> {
        // 设计已确认（仅保持既有行为的转换）：存活槽扫描的共享主体。
        // 伪码：在固定 end 前取 next 索引并先推进位置；跳过未分配洞，Acquire 读版本；
        // FREE 则继续，LIVE 则用 checked_key 转换完整索引与版本，
        // 再返回键及 (值共享引用, link 共享引用)；范围耗尽返回 None。
        // key 转换在位置推进之后、生成返回引用之前；若 panic，扫描位置不回退。
        inner::iter_next(self)
    }
    /// 返回 (保证剩余数零, 剩余扫描范围的可选上界)，不推进扫描或修改表。
    fn size_hint(&self) -> (usize, Option<usize>) {
        inner::iter_size_hint(self)
    }
}
/// 独占遍历存活槽的迭代器；元素为 (K, (&mut T, &mut ShareU64))。
pub struct IterMut<'a, K: Key, T, const N: u32 = 0> {
    // 高水位前缀的独占分段迭代，确保各返回槽的可变借用互不重叠。
    slots: pi_arr::SegmentedIterMut<'a, Slot<T, N>>,
    // 将键类型与表的独占借用生命周期绑定到迭代器。
    borrow: PhantomData<&'a mut SlotMap<K, T, N>>,
}
impl<'a, K: Key, T, const N: u32> Iterator for IterMut<'a, K, T, N> {
    type Item = (K, (&'a mut T, &'a mut ShareU64));
    /// self 为待继续扫描的迭代器；返回下一存活键及 (值引用, link 引用)，耗尽返回 None。
    /// 推进扫描位置，不修改表；自定义键转换失败时 panic，已越过的位置不回退。
    fn next(&mut self) -> Option<Self::Item> {
        // 设计已确认（仅保持既有行为的转换）：扫描主体见 Iter::next。
        // 伪码差异：由独占分段迭代器取得并消耗下一槽位置，不手动维护 next/end；
        // 对取得的槽执行主体的版本读取、跳过 FREE 和 key 转换，再返回互不重叠的
        // (值可变引用, link 可变引用)；分段范围耗尽返回 None。
        // checked_key 在底层迭代器已推进后、生成返回引用前调用；panic 不回退位置。
        inner::iter_mut_next(self)
    }
    /// 返回 (保证剩余数零, 剩余扫描范围的可选上界)，不推进扫描或修改表。
    fn size_hint(&self) -> (usize, Option<usize>) {
        inner::iter_mut_size_hint(self)
    }
}

/// 底层元数据认领失败；不依赖任何封装层错误或业务类型。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ClaimMetadataError {
    /// 索引不存在、非 LIVE 或代际身份不匹配。
    Stale,
    /// 同代占用位已置位，优先于业务位不匹配。
    Claimed,
    /// 同代未占用，但显式业务位比较失败。
    BitsMismatch {
        /// 失败时观察到的业务位，不包含 claimed_mask。
        actual_bits: u32,
    },
}

impl<K: Key, T, const N: u32> SlotMap<K, T, N> {
    // data 为已由调用者提取且清业务位的身份；调用者须验证 N<32、claimed_mask 为有效单一保留位，expected_bits 无占用位且不越界；expected_bits 不含 claimed_mask，后者为保留区内单一占用位。返回持槽引用、索引和成功完整版本的令牌。先验证同代，再优先报告 Claimed、其次 BitsMismatch；仅完整版本 AcqRel 强 CAS 成功才认领。全部 K 回调必须在调用前结束，函数无用户回调，失败不修改槽。
    pub(crate) fn claim_metadata(
        &self,
        data: KeyData,
        expected_bits: u32,
        claimed_mask: u32,
    ) -> Result<ClaimedSlot<'_, T, N>, ClaimMetadataError> {
        // 设计已确认；伪码：身份校验 → 检查占用/业务 bits → 完整版本强 CAS 一次（成功 AcqRel，失败 Acquire）；成功创建令牌，失败按实际版本区分 Stale/Claimed/BitsMismatch，不重试。
        inner::claim_metadata(self, data, expected_bits, claimed_mask)
    }
}
impl<K: Key, T, const N: u32> SlotMap<K, T, N> {
    // bits 为完整初始低 N 位，link 为初始用户 link，f 接收预定完整元数据并构造 T；返回已发布元数据，不执行 K 转换。越界、耗尽及 f panic 均不得发布值；认领后失败消耗预定代际。f 在发布前执行且允许重入，封装层必须在 f 内预计算并校验对外 K；提交重写全部 bits，不继承 FREE 业务状态。
    pub(crate) fn insert_with_bits(
        &self,
        bits: u32,
        link: u64,
        f: impl FnOnce(KeyData) -> T,
    ) -> KeyData {
        // 设计已确认；伪码：校验 bits → 认领候选 → 组合预定 LIVE 版本与初始 bits → 调用 f（先构造外部键后构造值）→ 写 T/指定 link → 计数 → Release 发布完整版本 → 取消回滚。
        inner::insert_with_bits(self, bits, link, f)
    }
}

/// 内部已认领元数据令牌；不含 K，不运行自定义键回调，不自行解锁。
/// 仅 claim_metadata 成功创建；字段私有，不能从封装芯伪造或跨表使用。
pub(crate) struct ClaimedSlot<'a, T, const N: u32> {
    // 已分配稳定槽的借用；不保存 T 引用，解引用仅发生在持令牌的方法内部。
    slot: &'a Slot<T, N>,
    // 归链使用的预校验索引。
    index: u32,
    // 成功认领的完整 LIVE 版本，含 CLAIMED 位。
    version: u32,
}
impl<T, const N: u32> ClaimedSlot<'_, T, N> {
    // 返回 T 的共享引用，生命周期绑定令牌借用。Safety：令牌仍持有 CLAIMED 且未释放/删除，不得有冲突可变引用。
    pub(crate) unsafe fn value(&self) -> &T {
        unsafe { inner::claimed_value(self) }
    }
}
impl<T, const N: u32> ClaimedSlot<'_, T, N> {
    // 返回 T 的独占引用，生命周期绑定令牌可变借用。Safety：令牌仍独占且未释放/删除，无冲突引用。
    pub(crate) unsafe fn value_mut(&mut self) -> &mut T {
        unsafe { inner::claimed_value_mut(self) }
    }
}
impl<T, const N: u32> ClaimedSlot<'_, T, N> {
    // 返回 link 的 Relaxed 快照，无用户回调、不返回原子引用；只由持有 CLAIMED 的 guard 调用。
    pub(crate) fn link(&self) -> u64 {
        inner::claimed_link(self)
    }
}
impl<T, const N: u32> ClaimedSlot<'_, T, N> {
    // link 为新用户数据；原子 Relaxed 写入，不创建 &mut ShareU64，允许迟到 FREE pop 读取；无用户回调。
    pub(crate) fn set_link(&mut self, link: u64) -> () {
        inner::claimed_set_link(self, link)
    }
}
impl<T, const N: u32> ClaimedSlot<'_, T, N> {
    // final_bits 为已校验且不含 CLAIMED 的低 N 位；Release 写回同代最终状态并清 CLAIMED，保留 LIVE 与代际。Safety：目标引用均结束、令牌未释放且身份匹配。本接口禁止用户回调、分配、断言和 panic，返回 ()。
    pub(crate) unsafe fn release(self, final_bits: u32) -> () {
        unsafe { inner::claimed_release(self, final_bits) }
    }
}
impl<T, const N: u32> ClaimedSlot<'_, T, N> {
    // map 为认领时同一表；返回移出的 T 与 link 快照。Safety：目标引用均结束且令牌仍独占。先移出 T/link，再下一代 FREE 归链并增加删除计数；不执行 K::data/from、用户回调、分配或可 panic 检查；归链不得 panic。
    pub(crate) unsafe fn remove<K: Key>(self, map: &SlotMap<K, T, N>) -> (T, u64) {
        unsafe { inner::claimed_remove(self, map) }
    }
}
