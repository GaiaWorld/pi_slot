# 独占守卫槽表整体设计

实现根为 src/；src/lib.rs 仅保留 crate 属性、最简文档、模块声明与完整 public 重导出；私有测试接入 slotmap 模块，tests/support/private.rs 内容保持。

底层壳 src/slotmap.rs 配对 src/slotmap_inner.rs（slotmap::inner），封装壳 src/guarded.rs 配对子模块 src/guarded_inner.rs。两芯零依赖；封装层只经 SlotMap 与 ClaimedSlot 壳交互。中文逐字段/参数/失败契约及算法伪码单源在源码，术语见 concepts.md。

本轮实际检查：`cargo fmt --all -- --check`、`cargo check --all-targets`、`cargo check --all-targets --features rc` 均通过；`cargo test` 默认 debug 通过 80 项（21 unit + 14 guarded + 1 types + 35 slot_map + 9 doc），`cargo test --features rc` debug 通过 73 项（20 + 11 + 1 + 32 + 9）；均无 warning，测试 0 failed、0 ignored。原始输出保留于本轮工具记录，本轮未运行 release 或 TSan；业务 bits CAS 临界窗口定点验收尚未落实。

## 范围与已确认决定

元数据 CAS 与独占守卫均已有运行实现。底层已有功能除明确移除 set_key_bits 外保留，普通 get 等继续完整 version 匹配；实现存在不代表全部验收时点已覆盖，缺口见下文。

固定 nightly-2026-08-17、minimal profile；开启 generic_const_exprs 与其必要的 incomplete_features 接受。GuardedSlotMap<K,T,const N:u32=2> 私有 inner: SlotMap<K,T,{N+1}>，where [();(N+1) as usize]:；构造时校验 N<=30。N 是业务位数，CLAIMED 位 N，LIVE 位 N+1。业务 Ready/Empty 不属于库。位布局、回绕与跨表身份限制见 concepts.md。

封装层无 Deref/as_inner/转换、未占用引用、raw link、裸引用扫描或截尾代际重置入口，仅必要插入、状态 CAS、try_get/try_remove/try_update 和 len/is_empty。没有额外公开 GuardedSlotWriter。

## 声明闭包与技术路径

- **模块关系**：src/guarded.rs 定义封闭访问面与 GuardedAccessError；src/guarded_inner.rs 仅经 src/slotmap.rs 的 SlotMap、ClaimedSlot 壳协作。底层 ClaimMetadataError 不依赖封装业务类型，错误映射归封装层，私有表示不穿越芯边界。
- **封闭访问与令牌边界**：GuardedSlotMap 的私有底层表不对外转换；SlotMap::compare_exchange_bits 只处理元数据，SlotMap::claim_metadata 才授予 ClaimedSlot 认领令牌。令牌字段私有且不含 K，SlotGuard 管理其所有权，值借用不能越过 guard；ClaimedSlot 的释放/删除安全前提及 SlotGuard 的字段不变量以源码声明为准。
- **协作入口**：插入经 SlotMap::insert_with_bits；访问经 GuardedSlotMap::try_get 与 ClaimedSlot::value/value_mut；释放及删除经 ClaimedSlot::release/remove。GuardedSlotMap::try_remove、GuardedSlotMap::try_update 复用认领边界。各方法核心流程仅保留在对应源码壳注释。
- **取舍**：以封闭访问和一次认领失败返回换取明确的独占责任，不引入扫描裸引用、自动重试或泄漏 guard 恢复入口。元数据令牌把无用户键回调的释放责任与可重入键转换分离；link 使用快照/原子写而非可变原子引用，以兼容迟到 FREE pop。有限版本位仍保留完整代际循环的 ABA 边界，未扩展为永久身份保证。

## 历史证据来源

转换参照与旧基线来自 conversion-before.json、conversion-check.json、baseline.json 及前序实际命令记录；design-check.json 保留设计轮次原始命令、退出码与文件指纹。当时新增入口为失败桩，相关测试曾暂停、存在未消费声明的 dead_code 警告，检查 API 导入受阻后以获授权的 bash 记录事实；后续实现已替换桩并恢复暂停测试。旧 convert/design 独立复审及既有 debug/release、mutation 检查只证明各自当时范围，不代表当前实现或全部验收的新鲜证据；历史 JSON 保持原样。

## Guarded 行为验收设计与风险分工

以下十组公开行为验收已有 tests/guarded.rs 对应用例，保留具体编排与可观察断言作为验收要求；这不代表下述私有临界窗口需求全部落实。主要经 src/guarded.rs 的真实公开 GuardedSlotMap / SlotGuard 壳验证，不用私有测试替代跨调用语义。默认原子配置运行跨线程编排；rc 配置按同样状态序列单线程执行，不强行赋予其 Sync。类型约束继续由现有 tests/guarded_types.rs 与 no_run/compile_fail 覆盖。

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

- **已落实的认领窗口**：src/slotmap_inner_test.rs 的 claim_cas_failure_reports_actual_* 用例通过 Stage::ClaimBeforeCas / ClaimCasFailed 控制 SlotMap::claim_metadata 预读版本到强 CAS 的窗口，覆盖占用、bits 改变与删除复用，断言按 CAS 实际返回版本分类、零额外认领且不重试。ClaimBeforeCas 仅接在 claim_metadata，不覆盖业务 bits CAS。
- **尚未落实的底层业务 bits CAS 临界窗口验收**：SlotMap::compare_exchange_bits 不预读槽版本，需确定性控制全部键回调完成、目标槽定位之后到强 CAS 之前的窗口，分别插入同代 bits 改变、CLAIMED 占用与删除/复用；断言依据 CAS 返回版本得到 Mismatch（含实际低位，供封装映射 Busy）或 Stale、失败不覆盖新状态且无重试。当前没有该入口的 CAS 临界窗口定点测试；键回调重入发生在更早阶段，不能替代此验收。后续测试须使用内部测试专用钩子/屏障，不增加公开调试或原子引用出口，Guarded 错误映射仍须公开用例验证。
- **已落实的删除/摘链窗口**：src/slotmap_inner_test.rs 通过确定性暂停点覆盖 ClaimedSlot::remove 的移出、下一代 FREE、归链、删除计数顺序，以及迟到 FREE pop 在 LIVE 用户 link 上的读取。断言只有预校验完整 id 能发布、next 未提前解引用、释放/归链区间无 Key 回调和 T 析构，FREE 只归链一次、旧 token 不再发布。公开测试只断言最终所有权/复用结果，不能声称靠压力测试已证明这些中间顺序。
- **已落实的回绕定点**：tests/support/private.rs 的 guarded_zero_business_bits_last_generation_claim_release_remove_wraps 仅在公开无法以合理周期达到的 N=0 代际回绕附近注入底层元数据状态，补掩码/回绕运算和 Stale 边界；不把它解释为超出既定完整代际 ABA 支持边界的保证。沿用既有有效私有断言，不逐私有函数凑测试。
- 运行证据分开记录：类型检查证明签名/借用约束，公开行为验收证明跨调用可观察契约，私有定点测试证明协议中间时点；任何一层通过都不能替代另两层。已落实测试与待补业务 CAS 窗口须分别评价，不能以当前全套测试通过声称全部验收已完成。

## 当前检查与未决

本轮限定为注释、文档及类型测试名称说明的自修；实际检查结果汇总在文首。十组公开行为验收的现有测试、认领/删除/摘链及回绕定点测试均有源码落点；底层 SlotMap::compare_exchange_bits 的 CAS 临界窗口确定性验收仍待补，不能称全部已测。

TSan 尚未验证：当前 Windows 不支持。scripts/test-tsan.sh 须在具备所需工具的真实 Linux x86_64 上执行；脚本对标准库与目标侧 Rust 依赖插桩，默认配置 debug/release 运行 --lib、guarded、slot_map。既有 bash -n 与 Windows 保护退出码 2 仅为脚本/环境证据，不代表 TSan 通过；环境和执行方式见 README.md“验证”。
