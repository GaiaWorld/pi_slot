# pi_slot

稳定地址槽表 SlotMap<K: Key = DefaultKey, T = ()>，版本 **1.0.0**。
从 0.4.2 到 1.0.0 是破坏性 API 重构：读取返回真正原位的 (T, ShareU64)，永久链接同时服务 LIVE 用户数据和 FREE 链。不要求 T: Default，不使用 Mutex 或 union 复用 T 空间。

FREE 链和索引认领使用 CAS，但整个容器**不是严格 lock-free**：pi_arr/pi_buckets 分桶分配仍可能使用锁，分配器、用户键回调和析构也没有无阻塞保证。下文性能数据仅限指定预分配微基准，不宣称普遍性能提升。

## 接口

ShareU64 重导出自 pi_share，不提供单独 Link 入口。

| 方法 | 返回与行为 |
| --- | --- |
| new / with_capacity / Default | 创建表及空槽，不调用 T::default |
| insert(&self, T) / set(&mut self, T) | K，默认 link=0；set 是独占别名 |
| insert_with_link(&self, T, u64) / set_with_link(&mut self, T, u64) | K，设置用户 link 位 |
| remove(&mut self, K) | Option<T>，移出值并使旧键失效 |
| remove_with_link(&mut self, K) | Option<(T, u64)>，移出值及删除前 link 快照 |
| unsafe remove_shared(&self, K) | Option<T>，调用方保证槽排他 |
| unsafe remove_shared_with_link(&self, K) | Option<(T, u64)>，同上并返回快照 |
| get(&self, K) | Option<&(T, ShareU64)>，检查 LIVE 版本 |
| get_mut(&mut self, K) | Option<&mut (T, ShareU64)>，仅表独占时返回整个可变 tuple |
| unsafe get_shared(&self, K) | Option<(&mut T, &ShareU64)>，仅 T 可变，不暴露整个可变 tuple |
| replace(&mut self, K, T) | Result<T, T>，成功旧值/失败新值；保留 link 和版本 |
| replace_with_link(&mut self, K, T, u64) | Result<(T, u64), (T, u64)>，成功旧 pair/失败新 pair；版本不变 |
| unsafe replace_shared(&self, K, T) | Result<T, T>，仅替换 T，保留 link |
| unsafe replace_shared_with_link(&self, K, T, u64) | Result<(T, u64), (T, u64)>，另修改 link 位；禁止并发用户 link 操作 |
| iter(&self) | (K, &(T, ShareU64))，冻结 max 上界的弱一致扫描 |
| iter_mut(&mut self) | (K, &mut (T, ShareU64))，每个索引一次，引用可共存 |
| unsafe get_unchecked(&self, K) | &(T, ShareU64)，跳过键校验 |
| unsafe get_unchecked_mut(&mut self, K) | &mut (T, ShareU64)，表独占，跳过键校验 |
| unsafe get_shared_unchecked(&self, K) | (&mut T, &ShareU64)，共享表，跳过键校验 |
| len / max / is_empty | LIVE 近似数 / 索引高水位 / 是否为空；静止时精确 |
| mem_size | 实际分配槽切片加 Self，不计 allocator 元数据和 T 间接堆内存 |
| Index / IndexMut / Debug | 索引返回 tuple，无效键 panic；Debug 为弱一致列表 |

迁移示例：原 map[key].push(...) 改为 map[key].0.push(...)；原 get_mut(key).unwrap() 改为 get_mut(key).unwrap().0；用户 link 使用 map[key].1.load/store(Ordering)。删除仍返回 T，需要 link 快照时使用 remove_with_link。

旧辅助键表、两阶段分配/设置、范围迭代、整理及单独 Link 入口不提供。iter/iter_mut 是 O(max) 扫描，不实现 ExactSizeIterator。mem_size 扫描实际分配分段，非 O(1)，包含预分配空槽，并发扩容时近似。

## 原位所有权

- Slot 使用 UnsafeCell<MaybeUninit<(T, ShareU64)>>，另有 ShareU32 版本及零大小线程模式标记，没有 owned 字段或独立 FREE 边字段。使用真实 Rust tuple 布局和 padding，不将 separate fields 强转为 tuple。
- 默认空壳仅用 addr_of_mut!(tuple.1) 初始化 ShareU64::new(u64::MAX)。T 未初始化时不 assume 整个 tuple、不创建 tuple 引用。空壳可在底层桶发布前随默认构造移动；发布后地址稳定。
- 认领和全部键/统计校验成功后，仅对 tuple.0 ptr::write(T)。LIVE 发布后才创建 tuple 引用。remove 仅 ptr::read(T)，replace 仅替换 T。with_link 方法修改原子位，不重建、移动或析构永久 atomic。LIVE 时不建立 &mut Slot。
- 表独占的 get_mut/IndexMut/iter_mut/get_unchecked_mut 可以替换整个 tuple 或 ShareU64。此时没有并发迟到 pop 观察者；安全 Rust 替换保持字段初始化。后续删除仍向当前原子对象写 FREE 边。
- version 是唯一 payload 所有权标记：偶数 >=2 为 LIVE，奇数为空。首次 LIVE=2，删除 FREE=3，复用 LIVE=4；版本不回绕。最后 LIVE=u32::MAX-1 删除或空候选回滚后永久 DEAD=u32::MAX，不回 FREE 链。
- Slot 析构只销毁 LIVE T，然后单独 drop_in_place 永久 link。MaybeUninit 不自动析构字段，不能因默认 AtomicU64 没有 Drop 工作而省略 RC 原子对象析构。当前 AtomicCell<u64> 也无资源型自定义 Drop。

## 发布协议

    claim FREE: Acquire head -> atomic read edge -> CAS head
                CAS success -> validate unchanged FREE version -> empty candidate
    insert:     checked key -> reserve count -> write T/store link -> Release LIVE
    remove:     revoke LIVE -> read T -> decrement count -> full FREE edge -> CAS push
    rollback:   empty candidate -> consume generation -> different FREE id (or DEAD)

- head 是 ShareU64，低 32 位完整 index，高 32 位完整 FREE version。每条 FREE edge 也是完整下一节点 id，NULL=u64::MAX。FREE id 摘下后绝不以相同 generation 再发布。
- pop 只按 head 定位稳定槽，读取永久 atomic；head CAS 成功之前**不解引用 edge 指向的 next**。迟到读取可能遇到 LIVE 用户写的任意 u64，包括越界 index，只将它当 CAS 候选位。该 incarnation 已摘下则旧完整 id CAS 必败，不按这些任意位访问槽。
- head Acquire 与 push AcqRel CAS 同步 FREE 边和版本；pop AcqRel CAS 保持链发布 release sequence。成功后版本必然仍等于 head 的 FREE generation，不在 CAS 前用版本读取冒充排他证明。
- link/FREE edge load/store 为 Relaxed。T/link 初始化先于 version Release LIVE，get/iter 以 version Acquire 观察发布。用户以 link 同步额外数据时须自行选择 Acquire/Release 等内存序。
- 新索引先分桶分配，再饱和 CAS 认领。高水位最多 u32::MAX-32 个槽，不回绕、不因删除缩小。分配 unwind 不消耗未分配索引。
- 摘下后的空 Candidate RAII 保护键转换、键回读校验及统计异常。键回调可重入：候选仍为空，不可读取，T 留在调用栈，panic 后正常析构。回滚消耗 generation，不重新发布摘下旧 id。失败新索引可能留下可复用空槽，max 可增长。
- count 是单个 ShareU64，计 LIVE 加短暂发布前预留，不是累计 alloc/free。键成功之后、T 初始化之前有界 CAS 加一；失败先回滚空候选，不在提交后 overflow panic。每次 LIVE 删除只减一次，先减再 push FREE，避免复用先增后减超界。有限槽数约束 count<=MAX_SLOTS，不会 u64 溢出/underflow。静止时精确，发布/删除期间 len/is_empty 为近似观察，不是事务快照。

## Unsafe 契约

键校验不是借用保护。unsafe 共享修改须外部保证目标 T 在整个操作或返回引用生命周期内排他，无冲突 T 引用、reader/writer 或扫描目标槽的迭代器；跨线程须同步。仅原子 link 引用/操作可与仅 T 的共享修改共存，不能持整个共享 tuple 后同时修改 T。

remove_shared[_with_link] 必须等待所有用户引用（**包含 link 引用**）终止，排除目标槽的冲突扫描和操作。永久 atomic 不代表用户 link 引用可以跨删除/复用；仅内部迟到 FREE 观察者可跨状态过渡。replace_shared_with_link 还须排除并发用户 link 操作，旧 T/link 快照不是两个字段的并发事务。unchecked 要求本表当前有效且已初始化的 LIVE 键及对应生命周期契约。

安全共享 insert 可与安全 get/iter 并发。iter 冻结 max 上界，可能观察或漏掉范围内并发插入，不是快照。并发 unsafe 删除测试仅用 channel 把唯一键交给唯一消费者，不并行 iter/get 或保留用户 link 引用。

## 键与依赖

- 重导出本地 pi_key 的 Key/KeyData/DefaultKey，自定义键可用 pi_key::new_key_type!，调用方需直接依赖 pi_null 0.1。不同表可能生成相同编码，键仅在原表使用。旧 pi_key_alloter 类型不具备类型身份兼容性。
- pi_key 使用 version =0.1.0、path ../pi_key、default-features=false，禁用默认 bits21_version 掩码。完整 KeyData/K 往返校验拒绝截断代际；Cargo feature 合并意外开启掩码时明确 panic。usize 等丢版本键会被拒绝。
- pi_arr 0.31.1 显式 SegmentedArr 不依赖 Arr 的 RC 别名，使用修复后的 boxed-slice owner，避免 0.31.0 预分配后 Box 移动使缓存 pointer tag 失效。pi_share 0.6 默认 ShareU32/ShareU64 是真实原子。默认跨线程共享要求相应 K trait 和 T: Send + Sync。
- rc 或 Cargo 合并开启上游 pi_share/rc 后，实际 ShareU32 类型选择 Rc 标记，阻止 SlotMap 的 Send/Sync，不信任上游非原子 AtomicCell 的线程 trait。RC 仅单线程使用。
- 依赖需要 nightly，本机为 nightly-2026-08-17-i686-pc-windows-gnu。相邻本地依赖为 pi_arr（version 0.31.1、path ../pi_arr）及 pi_key，无 root patch。本次按授权修复相邻 pi_arr；pi_arr 0.31.1 与 pi_slot 1.0.0 尚未发布。本地验证不代表 registry 构建或独立分发已可用，发布 pi_slot 前须先提供匹配的上游版本。

## 析构与验证

SlotMap 析构扫描全部实际分配槽，对 LIVE 撤销标记并移出 T，逐值 catch_unwind；首桶 T::drop panic 后继续清理后续桶，最后恢复首个 panic。字段析构随后只销毁空槽和永久 atomic，不重复 Drop T。次级 panic payload 有意 forget，避免其 Drop 再 panic 中断清理，这是明确的次级 payload 泄漏策略。已有栈展开期间再 panic、panic=abort 或 panic hook 失败可能 abort，不保证恢复。

    cargo fmt --check
    cargo test
    cargo test --release
    cargo test --features rc
    cargo check --all-targets
    cargo check --all-targets --features rc
    git diff --check

测试覆盖全部 CRUD/with_link 快照与保留、tuple 原位布局/ZST/高对齐、永久 link 地址、独占原子替换、键回调重入与 unwind、generation/索引/计数边界、确定性 stale pop/ABA、共享插入迭代发布、小型 MPMC 唯一键交接、RC 类型与线程 trait、跨桶 Drop panic。默认/rc 的 Debug、Release 均通过。Miri 另发现计数 Relaxed 发布不能保证 len 观察到此前索引认领，现改为预留 CAS Release、len Acquire，不改变近似统计契约。

Miri 使用同一 nightly 工具链，默认配置为 6 个内部测试、16 个集成测试和 2 个 compile-fail 文档测试；rc 为 6 + 14 + 2。Stacked Borrows 和 Tree Borrows 全量运行因上文既有次级 panic payload 有意泄漏而使用 `-Zmiri-ignore-leaks`；该选项关闭全局泄漏检查，未禁用别名检查。无 ignore-leaks 的默认全量运行全部断言通过后报告该 payload Box 与其 Arc 分配泄漏；默认配置排除该单一用例后，严格泄漏检测也通过。

共享插入扫描压力测试原规模为 4×500 个 4096 字节字符串，Miri 下曾超过 600 秒；仅在 cfg!(miri) 下使用 4×8 个 64 字节字符串，保持四个写线程及全部发布、唯一键、link、计数断言。普通 Debug/Release 保留原规模。未运行百万 benchmark 或 Loom；下文另列预分配微基准。两种实验借用模型测试通过不等于 unsafe 无 UB 的形式证明。

## 性能（预分配微基准）

2026-10-11 本地测量：Windows，Intel Core i7-6700K @ 4.00GHz（4 核 / 8 逻辑线程），`rustc 1.100.0-nightly (34baba539 2026-08-16)`，LLVM 23.1.0，`i686-pc-windows-gnu`，Cargo release 默认优化。类型为 `DefaultKey/u64`，`rc` 关闭，`pi_key` 的 `default-features=false`，运行时验证完整 32 位 generation 未被掩码截断。

CAS 副本匹配当前生产源（count 预留 CAS Release、len Acquire），生产 `src/lib.rs` SHA256 为 `7b8b3979aa4540c68283b7e270a89a118c80304aa3d0b562eb2646c54db7c74a`。依赖匹配生产锁文件：本地 path `pi_arr 0.31.1`、`pi_buckets 0.3.1`、`pi_vec_remain 0.2.2`、`pi_key 0.1.0`；registry `pi_share 0.6.0`、`pi_null 0.1.11`。修复前 pi_arr 0.31.0 / count Relaxed 的旧测量不与本轮合并。

### 对照定义

主对照是当前源的临时副本，只将 FREE 链同步改为全局 `Mutex<()>`，称为**锁式空闲链参考**，不是原历史 Mutex 实现，也不是旧 union 基线。两者保持同一永久 `(T, ShareU64)`、版本元数据、分段存储及键校验；Mutex 覆盖 head/edge 读取、摘链、FREE 版本核验与回链版本/edge/head 发布，head 更新改为锁内 load/store，**不保留 head CAS 再叠加锁**。fresh-index CAS、count CAS/原子序及 LIVE 发布保持相同，fresh-index 分配和用户键回调在锁外，避免回调重入死锁。

本平台 `size_of::<u64>()=8 B`，tuple 为 16 B，两者 `Slot<u64>` 均为 24 B；CAS map 本体 144 B，Mutex 参考 152 B。槽布局相同，Mutex 本体额外 8 B，不将不同空间布局的结果当作同步机制收益。生产仍不是严格 lock-free 容器。

### 方法与结果

- 每组 1/2/4/8 个 worker，每线程固定 20,000 次 insert 或 20,000 个 remove->insert pair。每组交错轮换对照顺序运行 5 轮，组之间串行，不并行运行不同组；下表为 5 轮 median。
- 每个 map 预分配 `threads * 20,000` 个空槽，最多 160,000。仅测预分配路径，不含初始化、分配/扩容和 map/value drop 成本。worker 启动、结果 Vec 分配在 ready/start 屏障前；done 屏障后停止计时，再 join 和验证。屏障调度、结果 key 写入及 churn checksum 仍计入。
- `insert_only` 每次 insert 算 1 op，计时后验证全部值、key、link=0、len/max。空闲链为空，因此主要包含空链检查的同步成本，而非回收链 pop/push 收益。
- `churn` 每个 remove->insert pair 算 2 op；ns/pair 是表中 ns/op 的两倍。每线程独占自己的当前 key，用 unsafe remove_shared，无并发引用或迭代。计时前设置每线程一个 LIVE 和一个备用 FREE 槽，避免空链竞争造成 fresh-index 增长；最终验证删除值 checksum、全部最终值/link=0、len，max 始终固定为 2/4/8/16，确认实际复用。

吞吐是所有线程合计，Mops/s 为百万次操作/秒；ns/op 由总耗时除以总操作数计算，并非单线程延迟。

| 场景 | 线程 | CAS median ms | Mutex median ms | CAS ns/op | Mutex ns/op | CAS Mops/s | Mutex Mops/s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| insert_only | 1 | 0.4507 | 0.6536 | 22.535000 | 32.680000 | 44.375416 | 30.599755 |
| insert_only | 2 | 2.3359 | 4.7378 | 58.397500 | 118.445000 | 17.124021 | 8.442737 |
| insert_only | 4 | 5.8961 | 11.5268 | 73.701250 | 144.085000 | 13.568291 | 6.940348 |
| insert_only | 8 | 15.4976 | 22.9219 | 96.860000 | 143.261875 | 10.324179 | 6.980224 |
| churn | 1 | 0.6990 | 0.8747 | 17.475000 | 21.867500 | 57.224607 | 45.729965 |
| churn | 2 | 5.6241 | 8.5488 | 70.301250 | 106.860000 | 14.224498 | 9.358039 |
| churn | 4 | 13.6027 | 17.1533 | 85.016875 | 107.208125 | 11.762371 | 9.327651 |
| churn | 8 | 34.0054 | 34.0325 | 106.266875 | 106.351562 | 9.410270 | 9.402777 |

单线程另测 simplified `Mutex<VecSlab>`：insert_only median 0.3944 ms / 19.720000 ns/op / 50.709939 Mops/s，churn 0.5906 ms / 14.765000 ns/op / 67.727735 Mops/s。它锁住整个简化 slab 操作，没有永久用户 link、同样的地址/计数协议或完整生产语义，**不是严格 ablation，也不是历史基线**；不把其结果归因于仅 Mutex/CAS 差异。

### 波动与边界

8 线程 churn 的 5 轮原始 ms：CAS 为 `36.0105, 34.0054, 40.9331, 32.6828, 33.0147`，Mutex 为 `34.0325, 33.6884, 34.1170, 34.1425, 33.8809`。CAS 有三轮更慢，median 仅低约 0.08%，不能认为有可靠优势，更不能推导“无锁总是更快”。增加线程也未带来吞吐扩展。未绑核、未隔离 CPU、无独立 warmup 或置信区间；5 个样本不能证明统计显著性。未测 String、增长分配、真实业务混合负载或单独 pi_arr 基准；验证通过不构成并发正确性的形式证明。

本轮 90 个样本（含单线程简化参考）全部验证通过，最长单次 40.9331 ms，小于 10 秒。诊断 crate 位于 `C:\Users\zmax\AppData\Local\Temp\opencode\slot-perf-20261011`，原始结果为 `raw-results-arr0311-count-release.csv`；`src/cas.rs` / `src/locked.rs` 为源副本，`src/main.rs` 为屏障计时与验证入口，未向生产添加 bench。复跑命令（在该临时目录执行）：

```powershell
cargo build --release --target i686-pc-windows-gnu --locked
cargo tree -e features --locked
& "./target/i686-pc-windows-gnu/release/slot_perf_diag.exe"
```

## License

MIT OR Apache-2.0，与 Cargo.toml 一致。
