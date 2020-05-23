//! Re-export core/std facilities under a unified name.

#[cfg(not(feature = "with-std"))]
pub use core::{
    alloc, borrow, cell, cmp, fmt, hash, hint, iter, marker, mem, ops, ptr, result, slice, sync,
};

#[cfg(feature = "with-std")]
pub use std::{
    alloc, borrow, cell, cmp, fmt, hash, hint, iter, marker, mem, ops, ptr, result, slice, sync,
};

#[cfg(feature = "with-std")]
pub use std::error;

#[cfg(not(feature = "with-std"))]
pub mod error {

pub trait Error : super::fmt::Debug + super::fmt::Display {}

}
