//! Internal definition of HashMap and HashSet buckets.

pub mod buckets;
pub mod buckets_api;
pub mod capacity;
pub mod key;

mod element;
mod hooks;

pub use self::hooks::HashHooks;

#[cfg(feature = "with-std")]
pub use self::hooks::DefaultHashHooks;

use super::allocator;
use super::atomic;
use super::failure;
use super::raw;
use super::root;
