# 独占守卫槽表整体设计

实现根为 src/；src/lib.rs 仅保留 crate 属性、最简文档、模块声明与完整 public 重导出；私有测试接入 slotmap 模块，tests/support/private.rs 内容保持。

底层壳 src/slotmap.rs 配对 src/slotmap_inner.rs（slotmap::inner），封装壳 src/guarded.rs 配对子模块 src/guarded_inner.rs。两芯零依赖；封装层只经 SlotMap 与 ClaimedSlot 壳交互。中文逐字段/参数/失败契约及算法伪码单源在源码，术语见 concepts.md。

## 范围与已确认决定

设计阶段仅写类型、契约、真实薄委托与显式 todo!("尚未实现…")，当时所有新增方法（含 guard Drop）均为不可执行的失败桩，依赖与 Cargo.toml 当时不改。当前全部 30 桩已实现；底层已有功能除明确移除 set_key_bits 外保留，普通 get 等继续完整 version 匹配。当前验证状态见文末。

固定 nightly-2026-08-17、minimal profile；开启 generic_const_exprs 与其必要的 incomplete_features 接受。GuardedSlotMap<K,T,const N:u32=2> 私有 inner: SlotMap<K,T,{N+1}>，where [();(N+1) as usize]:；构造时校验 N<=30。N 是业务位数，CLAIMED 位 N，LIVE 位 N+1。业务 Ready/Empty 不属于库。位布局、回绕与跨表身份限制见 concepts.md。

封装层无 Deref/as_inner/转换、未占用引用、raw link、裸引用扫描或截尾代际重置入口，仅必要插入、状态 CAS、try_get/try_remove/try_update 和 len/is_empty。没有额外公开 GuardedSlotWriter。

## 声明闭包与技术路径

- SlotMap::compare_exchange_bits 替代已移除 set_key_bits 及其旧芯：忽略键低保留位，显式 expected/new bits 对完整版本单次强 CAS；成功 AcqRel，失败 Acquire，同代 Mismatch/身份 Stale。仅元数据，不授予 T 权限。所有 K::data/from/无损校验回调（包括可重入 data）在修改前完成并缓存返回键，CAS 失败后无新用户回调。
- 封装 compare_exchange_bits 的两端 CLAIMED=0，不能清其他 guard 占用；错误为 Stale / 同代 Busy / 未占用 BitsMismatch，Busy 优先。所有失败与键回调 panic 不得意外认领或写状态。
- try_get 通过新增最小 pub(crate) SlotMap::claim_metadata，底层返回独立 ClaimMetadataError（Stale/Claimed/BitsMismatch），封装芯负责映射为 GuardedAccessError（Stale/Busy/BitsMismatch），actual_bits 原样保留；底层不引用 guarded。映射入口与认领入口现已实现。成功 CAS 后取得 ClaimedSlot 令牌才可生成引用。令牌保存稳定 Slot 引用、index、成功完整 version，不含 K、不自引用；guard 保存 map 引用、预校验 K、Option 令牌、原/最终 bits、Cell marker。None 表示 remove 已消费认领。
- ClaimedSlot 的 value/value_mut、link/set_link、release/remove 是底层壳接口，芯已实现；借用绑定令牌借用。令牌字段私有，安全前提要求认领有效、目标引用结束且删除时使用同一表。release/remove 不重新查键，不能回调用户、分配、可 panic 断言；归链使用已验证槽/索引。没有将私有表示伪装重导出来跨芯调用。
- SlotGuard 借用绑定 value/value_mut，不暴露 link 引用；link 只原子快照/set。original_bits 不变，bits 为待发布值，set_bits 只改待发布。Drop 经令牌 Release 发布最终业务位、清 CLAIMED；panic 不回滚已改值/link。forget 永久占用不自动解锁复用，最终 map Drop 仍析构 LIVE 值。Cell marker 保持 !Sync，Send 由真实字段推导，无手写 auto trait。
- remove(self) 消费令牌，移出 T/link 后下一代 FREE 归链并计数；try_remove 复用同一 claim/removal 协议。try_update 为 for<'g,'m> FnOnce(&'g mut SlotGuard<'m,...>)->R，R 不依赖任何 guard 借用，成功后一次回调，不自动 retry。
- SlotMap::insert_with_bits(bits,link,f) 是发布前初始化的最小内部入口；KeyData 回调预计算外部清位身份 K 并构造 T，覆盖初始完整 bits/link 后才发布 LIVE，FREE 历史 bits 不泄漏。回调/键转换失败消耗预定代际，不产生成功假象；insert_with_key 满足已知消费者自键构造。

## 转换审查边界与参照

旧实现转换已获独立 convert 复审通过；该通过范围为新增设计之前的源码及对应证据，不自动覆盖后续新增接口与实现。conversion-before.json、conversion-check.json、baseline.json 保留原转换参照与结果，本轮不重写。baseline 来源是主对话/前序代理转换前实际运行结果。

原基线：默认 13 unit + 33 integration + 3 doc；rc 12 + 30 + 3 全过。当时新增设计的证据单独写入 design-check.json，不能混称当时新增功能已可用；该文件保留为历史设计证据，不能代表当前实现新鲜度。

## 设计阶段暂停记录与保留验收

设计阶段曾将 5 个原测试逐点替换为 CAS 场景并标记 ignore，仅因当时实际会执行新 CAS 桩（当前均已恢复运行）：

1. reserved_bits_are_strict_preserved_and_visible_to_iteration
2. zero_bits_and_invalid_n_are_checked
3. high_n_wraps_with_bits_and_writer_rollback
4. compact_orders_free_slots_without_moving_live_values
5. shrinking_preserves_keys_values_links_and_statistics

当时新增 1 个暂停验收 bits_cas_key_callbacks_cannot_overwrite_reentrant_changes_or_panic_mutations，覆盖 Key::from/data 重入改变 bits 导致 Mismatch、回调 panic 不修改状态。当时合计默认/rc 均 6 个 ignore，保留原维护、回绕、link/值/统计断言，并新增同代显式 expected、忽略 key bits 与 Stale 断言。原非法 N 断言拆入 invalid_n_is_rejected_without_executing_design_stubs 继续运行，没有删除风险覆盖。

设计阶段 tests/guarded_types.rs 定义非执行函数验证 N+1 泛型、N=0/30、默认 N、try_update HRTB 正向调用与默认原子下 guard Send；仅运行获取函数项的测试，不调用任何设计桩。Rustdoc 新增 1 个 no_run 与 5 个 compile_fail：共享/可变引用不可逃逸 guard 或 try_update，guard !Sync；加原 3 个 doc 共 9 个。无桩 panic 充当验收成功。

## Guarded 行为验收设计与风险分工

以下保留原实现后验收方案；这些行为验收当前已落实，设计阶段当时未编写或执行这些业务测试。主要经 src/guarded.rs 的真实公开 GuardedSlotMap / SlotGuard 壳验证，不用私有测试替代跨调用语义。默认原子配置运行跨线程编排；rc 配置按同样状态序列单线程执行，不强行赋予其 Sync。类型约束继续由现有 tests/guarded_types.rs 与 no_run/compile_fail 覆盖。

### 公开入口的编排与可观察断言

1. **同槽竞争与错误优先级**：插入 bits=1；默认配置两线程用 Barrier 同时调用 GuardedSlotMap::try_get(key,1)，成功者用第二道屏障/通道持有 guard，等另一方完成后再释放，保证两个尝试重叠且不允许顺序双成功。断言恰好一个成功、另一方 Busy；持 guard 期间再次 try_get(key,0)、try_remove(key,0) 与 compare_exchange_bits(key,0,0) 均为 Busy，验证优先于 bits 不符。释放后错误 expected 为 BitsMismatch { actual_bits:1 }。用 try_remove 后复用同索引产生的新代键，拿旧键调用三个入口，均 Stale，即便新槽正被占用也不得报 Busy。只比较错误分支，不要求 guard 实现 Debug。
2. **业务 CAS 不清 CLAIMED**：持有 guard 时调用 GuardedSlotMap::compare_exchange_bits(key,1,0)，断言 Busy 且第二次 try_get 仍 Busy；guard 内 value/link/bits 不受影响。释放后同一 CAS 才可成功，重新 try_get(key,0) 观察新业务位。key 低业务位的输入副本不代替显式 expected，越界 desired/expected panic 不能解锁他人。此场景同时验证 GuardedAccessError 映射，不能仅测底层错误枚举。
3. **Release/Acquire 完整发布**：通过 SlotGuard::value_mut 写含多字段校验关系的非原子值（序号、派生校验），set_link 写关联序号，set_bits 写下一合法状态后 Drop；另一线程只用 GuardedSlotMap::try_get 的 Acquire 认领循环等待最终状态，不用额外释放后通道建立替代数据发布的同步边。启动屏障只用于释放前启动读者。成功后断言 value 所有字段、link 快照、original_bits/bits 均属于同次发布，无旧新混合。读者遇 Busy/旧 BitsMismatch 只在测试驱动层重试，库 try_get 不自动 retry；交替状态交接多轮，防止第一次初始化掩盖释放发布。rc 用顺序交接检查状态语义。
4. **update panic 与非法 pending**：catch_unwind 包住 GuardedSlotMap::try_update；回调先改 value 和 link，再 set_bits(合法状态 A)，随后 catch_unwind 一个越界 set_bits，回调内断言 bits 仍 A、original_bits 未变，最后主动 panic。外层捕获后 try_get(key,A) 必须成功，观察已改 value/link（不回滚）与 A，说明 Drop 已解锁并发布最后合法状态。用回调计数断言成功路径恰好一次、Busy/Stale/BitsMismatch 失败路径零次；panic 后不能自动重跑回调。
5. **消费删除恰好一次**：为 T 安装析构计数，分别通过 SlotGuard::remove 与 GuardedSlotMap::try_remove 返回 (T,link)，断言精确原值、link、len 减一；未 drop 返回值前析构计数不增，显式 drop 后只增一次，最终 map Drop 不再增该值。重复旧键删除返回 Stale；插入复用后取得新 guard，断言旧 guard remove 之后的自动 Drop 不解锁新槽、不改其 bits/value/link，且该槽只复用一次。通过 CallbackKey 回调计数，在 try_get 已完成后将 data/from 回调设置为 panic，再直接 guard.remove 或 Drop，断言不触发回调；归链阶段也不能调用 T 析构（析构由返回值所有者控制）。try_remove 的键回调只允许在认领前，回调后进入移出/归链阶段计数不得再增。
6. **初始完整发布与自键**：先插入非零 bits/link 后删除，在同索引插入不同初始 bits/link，try_get 必须只看到新值、新 link、显式新 bits，不继承 FREE 历史状态；覆盖零和最大合法业务位。GuardedSlotMap::insert_with_key 回调断言预定键的低业务+CLAIMED 位为零，保存该键于 T，提交后返回键与内嵌键一致，回调期间 try_get 只能 Stale、len 不增加。默认配置并发读者仅经 try_get 观察发布后初始化完整的值/link/bits；无底层引用或未初始化读取。
7. **键/构造 panic 回滚**：对 insert/insert_with_link/insert_with_key 安装分别在 Key::from、Key::data 和值构造处 panic 的回调，捕获后断言 len 未增加、不可读取未提交键、已创建输入值只析构一次；后续插入可复用槽，但在完整代际循环前不得重发该预定身份。回调未到达时构造函数调用次数为零。公开结果验证候选回滚；稳定定位“认领后、发布前”的内部顺序才由下述私有用例补充。
8. **forget 的永久占用与最终析构**：插入带析构计数的 T，取得 guard 后 mem::forget；重复 try_get/try_remove/业务 CAS 均 Busy，len 仍含该 LIVE 值；后续插入不得取得其索引，不能借业务 CAS 或维护隐式解锁。结束所有表借用后 drop map，断言被遗忘 guard 的 T 恰好析构一次；不要求库返回泄漏的 guard，也不存在自动恢复入口。
9. **N=0/30 与回绕边界**：N=0 只允许 bits=0，set_bits/CAS/插入的非零参数 panic 不改变可观察状态；CLAIMED 与 LIVE 仍独立，竞争/Drop/removal 同上。N=30 允许最大业务值 (1<<30)-1，越界位不允许；同槽一次完整删除/复用周期已使身份代际回绕，断言旧稳定身份可能等于新键并再次匹配（不是永久 Stale 保证），初始化业务 bits/link 仍必须重写。不让并发空闲链操作跨完整代际循环；N=0 的 2^30 周期不以巨量运行代替证明，版本位运算/边界由底层已存在回绕测试及必要私有定点状态覆盖。两端都实际编译 N+1，N>30 构造失败也纳入运行验收。
10. **Guarded 键回调重入**：对 try_get、try_remove、compare_exchange_bits 分别在 Key::from 与每个可能的 Key::data 阶段设置一次性回调（调用前先摘掉钩子，避免递归钩子），重入同表同槽三种操作：保存内层 guard 使其持续占用、业务 CAS 改成另一个 bits、删除后保持 FREE 或立即复用成新代。外层回调返回后分别断言 Busy、BitsMismatch（实际新业务位）、Stale；外层绝不能覆盖内层已改的值/link/bits 或认领权。占用场景内层 guard 存在外部测试容器并在断言后正常释放，不用 forget 污染其他场景；设置回调自身 panic 时外层不增加认领或修改，内层已生效状态保持。N 选默认 2，删除复用不跨回绕，避免 N=30 固有限制混淆预期；已验证 stable key 缓存必须确保 CAS 成功后不再运行用户键回调。

### 私有确定性测试仅补公开不可控制的时点

- tests/support/private.rs 接于 slotmap 模块，仅为 SlotMap::claim_metadata、SlotMap::compare_exchange_bits 及 ClaimedSlot::release/remove 稳定制造“已读取版本而 CAS 前被改变”的调度，断言失败分类取自 CAS 实际返回版本、零额外认领和无自动重试。使用实现期测试专用屏障/钩子控制时点，不向公开 API 增加调试或原子引用出口；Guarded 端到端错误映射仍由上述公开用例验证。
- 通过确定性暂停点覆盖 ClaimedSlot::remove 的移出、下一代 FREE、归链、删除计数顺序，以及迟到 FREE pop 在 LIVE 用户 link 上的读取。断言只有预校验完整 id 能发布、next 未提前解引用、释放/归链区间无 Key 回调和 T 析构，FREE 只归链一次、旧 token 不再发布。公开测试只断言最终所有权/复用结果，不能声称靠压力测试已证明这些中间顺序。
- 仅在公开无法以合理周期达到的 N=0 代际回绕附近注入底层元数据状态，补掩码/回绕运算和 Stale 边界；不把它解释为超出既定完整代际 ABA 支持边界的保证。沿用既有有效私有断言，不逐私有函数凑测试。
- 运行证据分开记录：类型检查证明签名/借用约束，公开行为验收证明跨调用可观察契约，私有定点测试证明协议中间时点；任何一层通过都不能替代另两层。设计阶段这些新增行为当时均为桩，以上当时仅为验收设计；当前实现与测试结论见下节。

## 当前检查状态与未决

历史设计轮次执行了 cargo fmt、cargo fmt -- --check、cargo check --all-targets（默认与 --features rc）、cargo test（两配置，仅未 ignore 用例）；更早轮次的 cargo test --no-run 编译覆盖未冒充该轮新执行。该轮原始命令、退出码与 normalized LF 文件指纹写入 design-check.json。checkRound 当时导入被工具依赖解析阻断，后用已获授权的 bash 后备记录事实。当时私有字段/接口未被桩消费，存在 dead_code 警告；这些记录保留历史语态，design-check.json 不重写，也不能代表当前实现新鲜度。

原独立审查会话已明确：完整范围 design 独立复审通过，13 个文件指纹匹配；底层反向依赖与 Guarded 行为验收设计不足两项原阻塞均已闭合，无已知未闭合待设计项。此处记录独立复审结论，不是自审结论。

设计阶段曾有 30 个显式桩（底层 9 个、Guarded 21 个）、6 项暂停验收与 20 项 dead_code 警告。当前 30 桩均已实现，暂停验收已恢复，上述行为验收已落实。最新已有默认 debug/release 各通过 80 项（21 unit + 14 guarded + 1 types + 35 slot_map + 9 doc），rc 各通过 73 项（20 + 11 + 1 + 32 + 9）；0 warning、0 ignored。独立功能静态审查无具体缺陷；测试审查最后的 len 读窗口已补齐，两种读序反转 mutation 在默认与 rc 下均实际失败后恢复。

TSan 尚未验证：Windows 不支持，WSL disabled、Docker 不存在。scripts/test-tsan.sh 需要真实 Linux x86_64，插桩标准库与目标侧 Rust 依赖，在默认 debug/release 执行 --lib、guarded、slot_map，包含 timeout、严格 summary 校验及同步日志。现有实测仅为 bash -n 与 Windows 保护 exit 2，不能视为 TSan 通过。使用方式及环境边界见 README.md 的“验证”。
