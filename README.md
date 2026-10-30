# pi_slot

元数据 CAS 与 GuardedSlotMap/SlotGuard 的全部 30 个实现桩已完成，包括 guard Drop。当前实现与验证状态见下方“验证”。既有转换的独立 convert 复审结论保留为历史证据。

使用固定 nightly-2026-08-17；新增泛型表达式依赖 generic_const_exprs，下游泛型调用需启用该 nightly feature 并携带 `[(); (N + 1) as usize]:` 约束。

支持通过共享引用并发插入的版本化槽表 SlotMap<K: Key = DefaultKey, T = (), const N: u32 = 0>。
这不代表值可以并发修改或删除：安全删除与可变访问需要独占借用；
共享引用上的删除、修改仅在调用者满足对应 unsafe 前提时可用。

## 快速使用

~~~rust
use pi_slot::{DefaultKey, SlotMap};

let mut map = SlotMap::<DefaultKey, (DefaultKey, u32)>::new();
let writer = map.try_insert_if(|index| index < 10).unwrap();
let key = writer.key(); // 尚未提交，map.get(key) 为 None。
let inserted = writer.insert((key, 42));
assert_eq!(inserted, key);
assert_eq!(map.get(key).unwrap().0, &(key, 42));
assert_eq!(map.remove(key), Some((key, 42)));
~~~

也可以用 insert_with_key(|key| ...) 构造含自身键的值；
try_insert_with_key(|key| -> Result<T, E> { ... }) 可返回业务错误。
后者失败时不会发布值，但已认领的槽位会消耗一代版本；索引耗尽时会 panic。

## 精确布局

两层均为 #[repr(C)]，字段按以下顺序；alloc/free 是常驻的累计计数器，
不含 owned、stamp、next_free、线程 marker 或 tuple 存储：

~~~rust
struct Slot<T, const N: u32 = 0> {
    link: ShareU64,
    entry: UnsafeCell<MaybeUninit<T>>,
    version: ShareU32,
}
struct SlotMap<K: Key, T, const N: u32 = 0> {
    free_head: CachePadded<ShareU64>,
    slots: SegmentedArr<Slot<T, N>>,
    alloc: CachePadded<ShareUsize>,
    free: CachePadded<ShareUsize>,
    next_index: ShareU32,
    key_type: PhantomData<K>,
}
~~~

初始 FREE=0；N=0 时首次 LIVE=1，释放 FREE=2，复用 LIVE=3。低 N 位为用户 bits，第 N 位为占用位；释放与复用各以 wrapping_add(1 << N) 推进，保留 bits，不永久停用耗尽槽。Candidate 仅 map/slot/index/version；预定 LIVE 版本不为零，version=0 表示已提交。认领时提前把槽内版本置为预定版本的下一 FREE 状态，因此 writer 尚未提交时始终不可读取；放弃 writer 不再额外推进，维护回收 forget 的 writer 也不会立即重发其预定 key（完整版本循环除外）。

FREE link 是下一节点完整 index32/version32 标识，NULL=u32::MAX as u64；LIVE link 为任意用户位。迟到 pop 可以读到任意 LIVE 用户位；在完整版本循环前，旧 id 的 CAS 会失败。单次未完成摘链跨越目标槽完整代际循环的极端 ABA 不在支持范围内；这不仅是旧 key 再次匹配的限制，还涉及内部空闲链安全。CAS 成功前绝不解引用或校验 next 指向的槽，不另外采样下一槽版本重建链边。free_head Acquire/Release 发布边，version Release/Acquire 发布 T；用户 link 额外同步由用户选择内存序。

新索引通过 fetch_update 饱和认领：回调先检查上限与 predicate，返回 Some(index+1) 并成功推进高水位后，才分配稳定空壳。高水位内暂时可能有尚未分配的槽位，不能仅凭 index < max 使用无检查访问。所有键转换/校验在写 T 之前完成。predicate panic 不认领索引；writer 放弃消耗 generation，在完整版本循环前不重新发布已摘下的旧完整 id；forget(writer) 只泄漏空槽，独占整理可回收。默认与 rc 均显式使用现有 SegmentedArr，增长不搬迁已分配槽；rc 的原子字段仍为单线程后端，表不实现 Sync。


## 版本保留位与回绕

N 必须小于 32。所有查询比较完整版本，包括用户 bits；相同 bits 下经过 2^(31-N) 个完整释放/复用周期，旧 key 可能再次匹配。N=31 时一个周期就重复，不适用于可能让一次摘链跨越该周期的并发使用。

旧 set_key_bits 已移除；替代接口为 compare_exchange_bits(&self, key, expected_bits, new_bits) -> Result<K, CompareExchangeBitsError>。它忽略 key 低 N 位，以显式 expected 比较完整版本强 CAS；成功仅更改元数据，不授予 T 访问权。同代失败 Mismatch { actual_bits }，失效身份 Stale。参数越界 panic；所有自定义 Key 回调在修改前完成，失败不意外修改。get 等既有查询仍要求完整版本匹配。

修改 bits 后底层完整 key 需要更新；改回原 bits 可能使同代旧 key 再次匹配。get_key_bits 不能恢复过期代际。

## 整理与缩容

维护方法均需 &mut self，不自动触发，不填平中间空洞，不改变存活 key、索引、用户 link 或累计插入/删除计数。compact 保留地址；两种缩容先分配新存储，再按原索引迁移槽并释放旧存储，应用必须重新获取所有地址缓存。迁移不要求 T: Clone 或 Default，不调用存活 T 的析构。分配失败发生在迁移前（分配器也可能直接终止进程）；成功缩容的临时峰值包含新旧两份槽存储。

shrink_to_fit 保留尾部空闲槽的版本和 bits；shrink_to_last_occupied 只保留最后存活槽及其之前的槽，空表高水位归零。截掉的版本和 bits 不保留，后续追加可能重新产生旧 key，应用负责清理旧 key 和关联数据。三种维护都会回收已分配但因 forget(writer) 而脱链的空槽。

维护按高水位范围内已分配槽扫描；两种缩容还会分配、默认初始化高水位对应的连续槽，因此时间与新高水位线性相关，稀疏高水位可能消耗较多内存。

## API

| 接口 | 返回/行为 |
| --- | --- |
| get | Option<(&T, &ShareU64)> |
| get_mut | Option<(&mut T, &mut ShareU64)> |
| unsafe get_shared | Option<(&mut T, &ShareU64)> |
| get_unchecked / get_unchecked_mut / get_shared_unchecked | 对应引用对，跳过键验证 |
| iter / iter_mut | (K, (&T, &ShareU64)) / (K, (&mut T, &mut ShareU64)) |
| Index / IndexMut | 只返回 T；无效键 panic |
| insert / insert_with_link / set / set_with_link | 返回 K，默认 link=0；set 为独占别名 |
| insert_with_key | 将预定 K 传给 FnOnce(K) -> T，提交后返回 K；键在回调期间尚未 LIVE |
| try_insert_with_key | 将预定 K 传给 FnOnce(K) -> Result<T,E>，返回 Result<K,E>；Err 不提交值但消耗 generation；索引耗尽会 panic |
| alloc / alloc_with_link | Result<K,T> / Result<K,(T,u64)>，耗尽保留原输入 |
| try_insert_if | 按 predicate 认领新索引，返回 Result<SlotWriter,ReserveError>；FREE 复用跳过 predicate；放弃 writer 消耗 generation |
| SlotWriter::key / insert / insert_with_link | 提交前读取预定 K；提交时设置值与可选 link（默认 0），返回同一 K |
| remove / remove_with_link | Option<T> / Option<(T,u64)> |
| unsafe remove_shared / remove_shared_with_link | 同上，调用方证明引用终止与排他 |
| replace / replace_with_link | 返回旧值/旧位，失败保留新输入，generation 不变 |
| unsafe replace_shared / replace_shared_with_link | 同上，调用方证明冲突排除 |
| len / is_empty | O(1)；累计插入数减累计删除数，不调用键回调，并发时不是一致性快照，可能暂时大于 max() |
| max | 新索引高水位，删除不缩小；截尾缩容可降低 |
| get_key_bits | 按索引返回存活槽 bits，不检查代际；不存在或空闲返回 None |
| compare_exchange_bits | key 仅比较身份，显式 expected/new bits；完整 version 强 CAS；Result<K, CompareExchangeBitsError>，不授予值权限 |
| compact | &mut self；按索引升序重建空闲链，不搬迁、不丢版本 |
| shrink_to_fit | &mut self；保留高水位内槽及版本，重建连续存储并释放旧存储，地址可能变化 |
| shrink_to_last_occupied | &mut self；截尾并重建存储和空闲链，丢弃被截槽版本及 bits，地址可能变化 |
| alloc_count / free_count | 始终提供，累计 usize 模计数 |

没有 get_live/try_retire/reclaim，也不提供 EBR。安全删除需 &mut self；unsafe 删除前全部 T/link 引用须终止，排除冲突扫描和操作，跨线程须外部同步。永久 link 不是允许用户引用跨复用的许可。仅 T 的共享修改可与纯原子 link 操作共存；with_link 替换另须排除并发用户 link 操作。引用对不是把 separate fields 强转为 tuple。

SlotMap Drop 先撤销 LIVE、移出 T，逐值 catch_unwind 清理全部实际分配槽，最后恢复首个 panic。次级 panic payload 有意 forget，防止其析构再次 panic。Slot Drop 只处理残余 LIVE T，link 由普通字段 drop glue 清理，不能手动再 drop link。

## GuardedSlotMap

- GuardedSlotMap<K,T,const N:u32=2> 完全封闭底层 SlotMap<K,T,{N+1}>。N<=30：低 N 位业务，第 N 位 CLAIMED，第 N+1 位 LIVE；Ready/Empty 由业务定义。对外键清业务及 CLAIMED，保留稳定索引/代际身份，不含表实例身份。
- 插入接口：new、with_capacity、insert(value,bits)、insert_with_link(value,link,bits)、insert_with_key(bits,f)。完整初始 bits/link 在 LIVE 发布前写入，预计算外部键；失败消耗预定代际。
- try_get(key,expected_bits) 先强 CAS 取得唯一 CLAIMED，再允许通过 SlotGuard 访问。错误依次区分 Stale、同代 Busy、未占用 BitsMismatch { actual_bits }。业务 compare_exchange_bits 期望/目标 CLAIMED 均为零，不能清其他 guard 的占用。
- guard.value/value_mut 仅绑定 guard 借用；link 仅 u64 快照与 set_link 原子写，不暴露原子引用。bits/original_bits 分别为待发布/原始状态，set_bits 只修改待发布状态。
- Drop Release 发布最终 bits 并清 CLAIMED；panic 不回滚值/link，forget 永久占用，不自动解锁复用，最终 map Drop 仍销毁 LIVE T。remove(self) 移出值/link 后推进 FREE 代际、归链、计数；释放和归链不得回调用户或 panic。
- try_remove 使用同一认领/删除协议；try_update 的 HRTB FnOnce 只调用一次且引用不可逃逸，不自动重试。guard 通过 Cell marker 保持 !Sync，Send 由真实字段自动推导。
- 不提供 Deref/as_inner、底层转换、未占用引用、raw link/裸引用扫描、截尾和代际重置；仅提供 O(1) 非快照 len/is_empty。

声明与契约见 src/guarded.rs、src/slotmap.rs；整体设计、保留的验收方案与历史证据见 design/guarded-slot-map/design.md。文档样例包含 no_run/compile_fail，运行行为另由 unit 与集成测试覆盖。

## 验证

最新已有测试结果：默认配置在 debug、release 下各通过 80 项（21 unit + 14 guarded + 1 types + 35 slot_map + 9 doc）；rc 两种构建各通过 73 项（20 + 11 + 1 + 32 + 9），均为 0 warning、0 ignored。独立功能静态审查未发现具体缺陷；测试审查最后的 len 读窗口覆盖已补齐，两种读序反转 mutation 在默认与 rc 下均实际失败，随后已恢复。

TSan **尚未验证**：当前 Windows 不支持，WSL disabled、Docker 不存在。现有脚本仅实测了 `bash -n scripts/test-tsan.sh` 和 Windows 环境保护退出码 2，不能据此称 TSan 通过。须在真实 Linux x86_64（具备 rustup、cc 及脚本所需工具）执行 `bash scripts/test-tsan.sh`；脚本使用固定 nightly 与 `-Zbuild-std` 插桩标准库及目标侧 Rust 依赖，在默认配置 debug/release 下运行 `--lib`、`guarded`、`slot_map`，以超时、严格测试 summary 校验和同步日志确认执行，日志位于 `target/tsan/run-*`。

design/guarded-slot-map/design-check.json 是历史设计阶段证据，不能代表当前实现新鲜度。
