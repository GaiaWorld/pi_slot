#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use pi_slot::{DefaultKey, GuardedAccessError, GuardedSlotMap, SlotGuard, SlotMap};

// 以下辅助函数不直接作为测试执行，由编译器验证泛型签名与调用约束。
fn generic_surface<const N: u32>(map: &GuardedSlotMap<DefaultKey, String, N>, key: DefaultKey)
where
    [(); (N + 1) as usize]:,
{
    let _: Result<SlotGuard<'_, DefaultKey, String, N>, GuardedAccessError> = map.try_get(key, 0);
    let _: Result<usize, GuardedAccessError> = map.try_update(key, 0, |guard| {
        guard.value_mut().push('!');
        guard.set_link(42);
        guard.set_bits(1);
        guard.value().len()
    });
}

// N+1 的实际类型必须能在上限与零位处实例化；构造调用仅编译不运行。
fn concrete_surface() {
    let _: GuardedSlotMap<DefaultKey, (), 0> = GuardedSlotMap::new();
    let _: GuardedSlotMap<DefaultKey, (), 30> = GuardedSlotMap::with_capacity(4);
    let _: GuardedSlotMap<DefaultKey, ()> = GuardedSlotMap::new();
    let _: SlotMap<DefaultKey, (), 31> = SlotMap::new();
    let _ = generic_surface::<2>;
}

#[cfg(not(feature = "rc"))]
fn atomic_send_capability() {
    fn send<T: Send>() {}
    send::<SlotGuard<'static, DefaultKey, String>>();
}

// 保持这些类型检查函数可达，但仅获取函数项，不调用构造/访问/Drop。
#[test]
fn type_surface_is_compiled_without_calling_helpers() {
    let _ = concrete_surface;
    #[cfg(not(feature = "rc"))]
    let _ = atomic_send_capability;
}
