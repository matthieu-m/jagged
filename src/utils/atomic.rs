//! A collection of specialized atomics.
//!
//! In theory, it is perfectly possible to use a mixed of Ordering on the same
//! instance of an Atomic, depending on the situation.
//!
//! In practice, it is the author's experience that this is a rarely needed
//! capability which only makes auditing/reviewing harder.
//!
//! Thus, these little types come with pre-established memory ordering.

use super::root::sync::atomic::{AtomicUsize, Ordering};

macro_rules! atomic {
    ($name:ident, $underlying:ident, $raw:ident, $load_ordering:expr, $store_ordering:expr) => {
        pub struct $name($underlying);

        impl $name {
            pub fn new(v: $raw) -> Self { Self($underlying::new(v)) }
            pub fn load(&self) -> $raw { self.0.load($load_ordering) }
            pub fn store(&self, v: $raw) { self.0.store(v, $store_ordering); }
        }
    }
}

atomic!{ AcqRelUsize, AtomicUsize, usize, Ordering::Acquire, Ordering::Release }

atomic!{ RelaxedUsize, AtomicUsize, usize, Ordering::Relaxed, Ordering::Relaxed }
