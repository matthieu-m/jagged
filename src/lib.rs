#![cfg_attr(not(feature = "with-std"), no_std)]
//  Lints
#![allow(clippy::module_inception)]

//! #   The Jagged Library
//!
//! A collection of wait-free concurrent data-structures.
//! -   The `Vector`: an append-only `Vec`.
//! -   The `HashMap`: an insert-only `HashMap`.
//! -   The `HashSet`: an insert-only `HashSet`.
//!
//! The set of concurrent write operations is limited, in exchange for performance and wait-freedom.

pub mod allocator;
pub mod failure;
pub mod hashmap;
pub mod hashset;
pub mod vector;

mod hashcore;
mod utils;

use self::utils::atomic;
use self::utils::raw;
use self::utils::root;
