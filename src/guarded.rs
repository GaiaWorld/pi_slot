//! 独占槽守卫的设计壳；新增方法尚未实现，不可运行。
#[path = "guarded_inner.rs"]
mod guarded_inner;
use crate::slotmap::{ClaimedSlot, DefaultKey, Key, SlotMap};
use std::cell::Cell;
use std::marker::PhantomData;

/// 新增声明仅供编译检查；以下示例只编译不执行。
/// ```no_run
/// #![feature(generic_const_exprs)]
/// #![allow(incomplete_features)]
/// use pi_slot::{DefaultKey, GuardedSlotMap};
/// fn generic<const N: u32>() where [(); (N + 1) as usize]: {
///     let _: GuardedSlotMap<DefaultKey, String, N> = GuardedSlotMap::new();
/// }
/// let map = GuardedSlotMap::<DefaultKey, String>::new();
/// let key = map.insert_with_key(0, |key| format!("{key:?}"));
/// let len = map.try_update(key, 0, |guard| guard.value().len());
/// ```
/// 封闭的槽表：N 为业务位数（<=30），低 N 位业务、位 N 为 CLAIMED、位 N+1 为 LIVE。
/// 对外键清除业务与 CLAIMED，保留 LIVE/代际；无表实例身份。无底层转换、扫描或未认领引用入口。
/// forget guard 永久占用直到最终表析构；不提供自动解锁、截尾或代际重置。Ready/Empty 为业务概念。
/// 同业务 bits 下代际以 2^(30-N) 个释放/复用周期回绕；继承底层完整代际循环 ABA 边界。
pub struct GuardedSlotMap<K: Key = DefaultKey, T = (), const N: u32 = 2>
where
    [(); (N + 1) as usize]:,
{
    // 完全私有的底层表，额外一位用于 CLAIMED；不实现 Deref/as_inner/转换。
    inner: SlotMap<K, T, { N + 1 }>,
}

/// 独占访问错误；失败未获得值引用，也未改写目标槽。
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GuardedAccessError {
    /// FREE、索引不存在或代际身份过期。
    Stale,
    /// 同代槽已被 guard 占用，优先于业务位不匹配。
    Busy,
    /// 同代未占用，但业务位不同。
    BitsMismatch {
        /// 失败时观察到的 N 个业务位，不承诺后续不变。
        actual_bits: u32,
    },
}

/// 值引用不能逃逸 guard 借用；以下仅编译：
/// ```compile_fail,E0515
/// #![feature(generic_const_exprs)]
/// #![allow(incomplete_features)]
/// use pi_slot::{DefaultKey, SlotGuard};
/// fn escape<'a>(guard: SlotGuard<'a, DefaultKey, String>) -> &'a String {
///     guard.value()
/// }
/// ```
/// try_update 的 HRTB 阻止回调返回值借用：
/// ```compile_fail
/// #![feature(generic_const_exprs)]
/// #![allow(incomplete_features)]
/// use pi_slot::{DefaultKey, GuardedAccessError, GuardedSlotMap};
/// fn escape<'a>(map: &'a GuardedSlotMap<DefaultKey, String>, key: DefaultKey)
///     -> Result<&'a String, GuardedAccessError> {
///     map.try_update(key, 0, |guard| guard.value())
/// }
/// ```
/// guard 不可 Sync，即使 T 与默认原子可跨线程：
/// ```compile_fail,E0277
/// #![feature(generic_const_exprs)]
/// #![allow(incomplete_features)]
/// use pi_slot::{DefaultKey, SlotGuard};
/// fn sync<T: Sync>() {}
/// sync::<SlotGuard<'static, DefaultKey, String>>();
/// ```
/// 可变值引用也不能逃逸 guard：
/// ```compile_fail,E0515
/// #![feature(generic_const_exprs)]
/// #![allow(incomplete_features)]
/// use pi_slot::{DefaultKey, SlotGuard};
/// fn escape<'a>(mut guard: SlotGuard<'a, DefaultKey, String>) -> &'a mut String {
///     guard.value_mut()
/// }
/// ```
/// HRTB 同样拒绝 try_update 返回可变值引用：
/// ```compile_fail
/// #![feature(generic_const_exprs)]
/// #![allow(incomplete_features)]
/// use pi_slot::{DefaultKey, GuardedAccessError, GuardedSlotMap};
/// fn escape<'a>(map: &'a GuardedSlotMap<DefaultKey, String>, key: DefaultKey)
///     -> Result<&'a mut String, GuardedAccessError> {
///     map.try_update(key, 0, |guard| guard.value_mut())
/// }
/// ```
/// CLAIMED 成功后唯一持有者；不自引用，不保存 T 或 link 裸引用。
/// value/value_mut 的生命周期绑定 guard 借用；Drop 发布最终业务 bits 并清 CLAIMED。
/// panic 不回滚值/link；forget 永久占用，最终表 Drop 仍销毁该 LIVE 值。
/// Cell marker 使 guard 默认 !Sync；Send 由真实表引用、令牌及 K/原子能力推导，无宽泛手写实现。
pub struct SlotGuard<'a, K: Key, T, const N: u32 = 2>
where
    [(); (N + 1) as usize]:,
{
    // 被借用的封闭表，保证底层稳定槽存活。
    map: &'a GuardedSlotMap<K, T, N>,
    // CAS 前完成用户回调后缓存的对外身份键；释放不调用它的任何方法。
    key: K,
    // 成功认领的槽/索引/完整版本令牌；remove 取走后为 None，避免 Drop 再发布。
    token: Option<ClaimedSlot<'a, T, { N + 1 }>>,
    // 认领时业务状态，仅用于快照，后续不变。
    original_bits: u32,
    // set_bits 校验后待 Drop 发布的业务状态，不含 CLAIMED。
    final_bits: u32,
    // 禁止共享 guard 跨线程使用，Send 仍依实际字段推导。
    not_sync: PhantomData<Cell<()>>,
}

impl<K: Key, T, const N: u32> GuardedSlotMap<K, T, N>
where
    [(); (N + 1) as usize]:,
{
    /// 返回未分配的空表；N 为业务位数，必须 <=30，否则 panic。当前是设计桩，不可执行。
    pub fn new() -> Self {
        guarded_inner::map_new::<K, T, N>()
    }
    /// capacity 为预分配容量；返回空表，长度为零。N>30、容量越界时 panic；分配失败遵循分配器行为。
    pub fn with_capacity(capacity: usize) -> Self {
        guarded_inner::map_with_capacity::<K, T, N>(capacity)
    }
    /// value 为新值，bits 为初始 N 个业务位；返回清除业务及 CLAIMED 位的稳定身份键，link 默认零。
    /// bits 越界、容量耗尽或自定义 Key 转换 panic 时不发布值；认领后失败消耗预定代际。流程见 insert_with_key。
    pub fn insert(&self, value: T, bits: u32) -> K {
        guarded_inner::map_insert(self, value, bits)
    }
    /// value 为新值，link 为初始用户数据，bits 为初始业务位；返回稳定身份键。
    /// 失败/回滚遵循 insert；初始 link 和完整 bits 在 LIVE 发布前设置，不继承 FREE bits。流程见 insert_with_key。
    pub fn insert_with_link(&self, value: T, link: u64, bits: u32) -> K {
        guarded_inner::map_insert_with_link(self, value, link, bits)
    }
    /// bits 为初始业务位；f 在发布前接收预计算且校验完毕的稳定身份键，恰好调用一次，返回 T。
    /// 成功返回同一键；越界/耗尽/键转换或 f panic 时不发布成功值，已认领槽消耗预定代际。
    /// f 可重入本表但不能读取尚未提交值；所有 Key::from/data 回调完成后才可发布 LIVE。
    pub fn insert_with_key(&self, bits: u32, f: impl FnOnce(K) -> T) -> K {
        // 设计已确认；伪码：校验 N/bits → 调 SlotMap::insert_with_bits 认领；其构造回调中先清业务+CLAIMED 生成并校验外部 K，再调用 f；全部成功后底层写值/link、覆盖初始 bits 并 Release 发布 LIVE；返回缓存 K，不在发布后调用 Key 回调。
        guarded_inner::map_insert_with_key(self, bits, f)
    }
    /// 返回底层 O(1) 累计插入减删除的观测值；并发非一致性快照，可能暂时大于高水位，不修改状态。
    pub fn len(&self) -> usize {
        guarded_inner::map_len(self)
    }
    /// 返回 len()==0；与 len 一样并发非快照，不能作为同步证明。
    pub fn is_empty(&self) -> bool {
        guarded_inner::map_is_empty(self)
    }
    /// key 提供稳定索引+代际身份，忽略低业务及 CLAIMED 位；expected_bits 为显式期望业务位。
    /// 同代已 CLAIMED 返回 Busy，否则业务位不同返回 BitsMismatch；FREE/代际不符/缺槽返回 Stale。
    /// bits 越界或 Key 回调 panic 不得认领；所有用户键回调在 CAS 前完成，成功 CAS 后才可产生引用。
    /// 只做一次认领，不自动重试；成功返回唯一 guard。无表实例身份，不能用它鉴别跨表键。
    pub fn try_get(
        &self,
        key: K,
        expected_bits: u32,
    ) -> Result<SlotGuard<'_, K, T, N>, GuardedAccessError> {
        // 设计已确认；伪码：检查业务范围 → 提取并校验 K，缓存完整元数据/外部身份 K（可重入回调全部结束）→ SlotMap::claim_metadata 按身份检查后优先 Busy、其次 bits，不匹配不修改 → 强 CAS CLAIMED；成功仅保存 map、预校验键、令牌、原/最终 bits，不存 T 引用。
        guarded_inner::map_try_get(self, key, expected_bits)
    }
    /// key 为稳定身份；expected_bits/new_bits 仅为 N 个业务位，二者内部 CLAIMED 必须为零。
    /// 只做元数据 CAS，不授予 T 权限；成功返回稳定身份键，不自动重试。
    /// 身份无效返回 Stale，同代已占用返回 Busy（优先于业务不符），否则 BitsMismatch { actual_bits }；失败不修改状态。
    /// 越界或自定义键回调 panic 不得修改；完整返回键及所有 data 回调必须在底层 CAS 前完成。
    pub fn compare_exchange_bits(
        &self,
        key: K,
        expected_bits: u32,
        new_bits: u32,
    ) -> Result<K, GuardedAccessError> {
        // 设计已确认；伪码：校验参数并预计算全部 K 回调 → 调 SlotMap::compare_exchange_bits，期望/目标均不含 CLAIMED → 成功返回预缓存身份键；Stale 原样映射，Mismatch 依 CLAIMED 位映射 Busy 或业务 BitsMismatch，绝不能清除其他 guard 占用。
        guarded_inner::map_compare_exchange_bits(self, key, expected_bits, new_bits)
    }
    /// key/expected_bits 与 try_get 相同；成功返回移出的值与 link 快照。
    /// 先按 try_get 同一认领协议获得 guard，再消费 guard.remove；错误、panic 前提及忙优先级同 try_get。
    pub fn try_remove(&self, key: K, expected_bits: u32) -> Result<(T, u64), GuardedAccessError> {
        guarded_inner::map_try_remove(self, key, expected_bits)
    }
    /// key/expected_bits 遵循 try_get；仅成功认领后调用 f 一次，返回 R，不自动重试。
    /// f 为对 guard 借用及其 map 生命周期高阶约束的 FnOnce；R 不依赖任一借用，不能逃逸值引用。
    /// 失败不调用 f；f panic 时 guard Drop 发布待发布 bits，不回滚已改 value/link。
    pub fn try_update<R, F>(
        &self,
        key: K,
        expected_bits: u32,
        f: F,
    ) -> Result<R, GuardedAccessError>
    where
        F: for<'g, 'm> FnOnce(&'g mut SlotGuard<'m, K, T, N>) -> R,
    {
        // 设计已确认；伪码：按 try_get 单次认领 → 成功后调用 f(&mut guard) 一次 → 释放 guard（Release 发布最终 bits）→ 返回 R；panic 走同一 Drop，失败直接返回错误。
        guarded_inner::map_try_update(self, key, expected_bits, f)
    }
}

impl<'a, K: Key, T, const N: u32> SlotGuard<'a, K, T, N>
where
    [(); (N + 1) as usize]:,
{
    /// 返回预先校验并缓存的稳定身份键副本；不调用 Key::data/from，不改变状态。
    pub fn key(&self) -> K {
        guarded_inner::guard_key(self)
    }
    /// 返回值共享引用，生命周期仅绑定本次 guard 借用，不能超过 guard 或与 value_mut 冲突。
    pub fn value(&self) -> &T {
        guarded_inner::guard_value(self)
    }
    /// 返回独占值引用，生命周期仅绑定本次 guard 可变借用；不会产生 map 生命周期的裸引用。
    pub fn value_mut(&mut self) -> &mut T {
        guarded_inner::guard_value_mut(self)
    }
    /// 返回用户 link 的 u64 快照，不暴露 &ShareU64 或 &mut ShareU64；允许内部迟到 FREE pop 原子读取。
    pub fn link(&self) -> u64 {
        guarded_inner::guard_link(self)
    }
    /// link 为新用户数据；仅以底层原子写入，不产生可变原子引用；panic 不回滚已经写入的 link。
    pub fn set_link(&mut self, link: u64) -> () {
        guarded_inner::guard_set_link(self, link)
    }
    /// 返回本 guard 当前待发布业务 bits；set_bits 之前等于认领时原状态，不包括 CLAIMED。
    pub fn bits(&self) -> u32 {
        guarded_inner::guard_bits(self)
    }
    /// 返回认领时原业务 bits，set_bits 不改变该快照；不包括 CLAIMED。
    pub fn original_bits(&self) -> u32 {
        guarded_inner::guard_original_bits(self)
    }
    /// bits 为最终待发布的 N 个业务位；越界 panic 且保持原待发布状态。
    /// 只更新 guard 本地待发布状态，直到 Drop 才 Release 发布；不立即清 CLAIMED。
    pub fn set_bits(&mut self, bits: u32) -> () {
        guarded_inner::guard_set_bits(self, bits)
    }
    /// 消费 guard，先移出 T/link 快照，再发布下一代 FREE 并归链、增加删除计数，返回两项所有权/快照。
    /// 调用前所有 guard 派生引用必须结束；不再调用自定义 Key::data/from 或任何用户回调，归链不可 panic。
    /// 取出令牌使后续 Drop 不解锁已删除槽；forget guard 则永久占用，不触发本操作。
    pub fn remove(self) -> (T, u64) {
        // 设计已确认；伪码：取出预校验令牌 → 经 ClaimedSlot::remove 同一底层删除协议移出 T/link → 下一代 FREE → 归链 → 删除计数；guard token=None，Drop 无动作，不在释放阶段执行用户代码。
        guarded_inner::guard_remove(self)
    }
}

impl<K: Key, T, const N: u32> Drop for SlotGuard<'_, K, T, N>
where
    [(); (N + 1) as usize]:,
{
    /// 无返回值；令牌仍在时 Release 发布已校验 final_bits 并清 CLAIMED，不回滚值/link。
    /// 正式实现禁止分配、断言、用户回调及 panic；remove 后 token=None 不操作。当前显式设计桩会 panic，严禁运行。
    fn drop(&mut self) {
        // 设计已确认；伪码：取出 token；无则返回；否则以令牌调用 release(final_bits)，不调用 Key 方法。
        guarded_inner::guard_drop(self)
    }
}
