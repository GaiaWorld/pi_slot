# 槽身份、业务状态与独占占用

入口 src/lib.rs 仅装配与重导出；底层壳 src/slotmap.rs 配对 src/slotmap_inner.rs，封装壳 src/guarded.rs 经 crate::slotmap 壳访问内部能力。

- **底层 SlotMap 的 N**：低 N 位是元数据保留区，第 N 位是 LIVE；完整版本仍用于普通 get/删除匹配。
- **GuardedSlotMap 的 N**：业务位数，范围 0..=30。底层实例使用 N+1 个保留位；位 N 是库内 CLAIMED，位 N+1 是 LIVE。
- **业务 bits**：调用方含义，不由库定义 Ready/Empty。FREE 遗留 bits 不得作为新插入初始状态泄漏。
- **稳定身份键**：索引与 LIVE/代际，清业务及 CLAIMED。它不是表实例身份；不同表不能凭该键相互鉴别。同业务状态下完整释放/复用周期数 2^(30-N) 后代际回绕，继承底层极端 ABA 限制。
- **CLAIMED**：同代独占占用，只有强 CAS 成功后 guard 才可产生值引用。单纯业务 bits CAS 不授予 T 权限。Busy 优先于同代业务位不同；代际不符则 Stale。
- **预校验元数据令牌 ClaimedSlot**：底层壳持有稳定 Slot 引用、索引及成功完整版本；无自定义 K，不保存 T 自引用。封装芯仅调用令牌壳，不依赖另一芯。
- **原状态与待发布状态**：guard.original_bits 为认领快照，guard.bits 为最终待发布值；set_bits 仅更新后者，Drop Release 发布并清 CLAIMED。
- **forget**：永远遗失该 guard，保留 LIVE+CLAIMED；封装层无维护接口自动回收。最终表销毁仍析构值。
- **删除**：guard 派生引用结束后移出 T/link，再推进下一代 FREE、归链、计数。释放/归链不用键回调或可 panic 检查。

新增行为的全部 30 个实现桩现已完成，相关验收已落实，当前为 0 warning、0 ignored；TSan 仍未验证。当前验证状态及历史设计证据边界见 design.md，本文件保留上述概念与契约。
