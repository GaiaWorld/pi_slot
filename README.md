# pi_slot

支持通过共享引用并发插入的版本化槽表 SlotMap<K: Key = DefaultKey, T = ()>。
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

两层均为 #[repr(C)]，字段按以下顺序，不含 count、owned、stamp、next_free、线程 marker 或 tuple 存储：

~~~rust
struct Slot<T> {
    link: ShareU64,
    entry: UnsafeCell<MaybeUninit<T>>,
    version: ShareU32,
}
struct SlotMap<K: Key, T> {
    free_head: ShareU64,
    slots: Arr<Slot<T>>,
    #[cfg(feature = "stats")]
    alloc: CachePadded<ShareUsize>,
    #[cfg(feature = "stats")]
    free: CachePadded<ShareUsize>,
    next_index: ShareU32,
    key_type: PhantomData<K>,
}
~~~

初始 FREE=1，首次 LIVE=2，FREE=3，复用 LIVE=4。最后 LIVE=u32::MAX-1；删除或末代 writer 回滚后 FREE=u32::MAX，下次摘链永久退出复用，不回绕 generation。Candidate 仅 map/slot/index/version，version=0 表示已提交。

FREE link 是下一节点完整 index32/version32 标识，NULL=u32::MAX as u64；LIVE link 为任意用户位。迟到 pop 可以读到任意 LIVE 用户位，完整旧 id 的 CAS 必须失败。CAS 成功前绝不解引用或校验 next 指向的槽，不另外采样下一槽版本重建链边。free_head Acquire/Release 发布边，version Release/Acquire 发布 T；用户 link 额外同步由用户选择内存序。

新索引通过 fetch_update 饱和认领：回调先检查上限、predicate、分配稳定空壳，再返回 Some(index+1)。所有键转换/校验在写 T 之前完成。predicate panic 不认领索引；writer 放弃消耗 generation，不重新发布已摘下的旧完整 id；forget(writer) 只泄漏空槽。


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
| len / is_empty | O(max) 扫描 LIVE 版本，不调用键回调，不是并发一致性快照 |
| max | 新索引高水位，删除不缩小 |
| alloc_count / free_count | 仅 stats feature 提供，累计 usize 模计数 |

没有 get_live/try_retire/reclaim，也不提供 EBR。安全删除需 &mut self；unsafe 删除前全部 T/link 引用须终止，排除冲突扫描和操作，跨线程须外部同步。永久 link 不是允许用户引用跨复用的许可。仅 T 的共享修改可与纯原子 link 操作共存；with_link 替换另须排除并发用户 link 操作。引用对不是把 separate fields 强转为 tuple。

SlotMap Drop 先撤销 LIVE、移出 T，逐值 catch_unwind 清理全部实际分配槽，最后恢复首个 panic。次级 panic payload 有意 forget，防止其析构再次 panic。Slot Drop 只处理残余 LIVE T，link 由普通字段 drop glue 清理，不能手动再 drop link。
