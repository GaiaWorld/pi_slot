#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

//! 版本化槽表与独占守卫槽表。

mod guarded;
mod slotmap;

pub use guarded::{GuardedAccessError, GuardedSlotMap, SlotGuard};
pub use slotmap::{
    CompareExchangeBitsError, DefaultKey, Iter, IterMut, Key, KeyData, ReserveError, ShareU64,
    SlotMap, SlotWriter,
};
