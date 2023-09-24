//! Hooks of the HashMap and HashSet.

#[cfg(feature = "with-std")]
use std::collections::hash_map;

use super::allocator;
use super::root::hash;

/// HashHooks
///
/// There are three important hooks for a HashMap and HashSet:
/// -   The maximum number of buckets, which defines the capacity and the memory footprint.
/// -   The hashing algorithm.
/// -   The allocator and deallocator functions.
///
/// The HashHooks trait allows customizing allocation, but unfortunately does not allow customizing the size, as this
/// does not quite yet work...
///
/// Also see DefaultHashHooks for the default, when the `alloc` feature is used.
pub trait HashHooks: allocator::Allocator + hash::BuildHasher {}

/// DefaultHashHooks
///
/// Default hooks for the HashMap and HashSet:
/// -   deferring allocation and deallocation to `DefaultAllocator`.
#[cfg(feature = "with-std")]
#[derive(Clone, Debug, Default)]
pub struct DefaultHashHooks(allocator::DefaultAllocator, hash_map::RandomState);

#[cfg(feature = "with-std")]
impl allocator::Allocator for DefaultHashHooks {
    unsafe fn allocate(&self, layout: allocator::Layout) -> *mut u8 {
        //  Safety:
        //  -   Forwarding.
        unsafe { self.0.allocate(layout) }
    }

    unsafe fn deallocate(&self, ptr: *mut u8, layout: allocator::Layout) {
        //  Safety:
        //  -   Forwarding.
        unsafe { self.0.deallocate(ptr, layout) }
    }
}

#[cfg(feature = "with-std")]
impl hash::BuildHasher for DefaultHashHooks {
    type Hasher = hash_map::DefaultHasher;

    fn build_hasher(&self) -> Self::Hasher {
        self.1.build_hasher()
    }
}

#[cfg(feature = "with-std")]
impl HashHooks for DefaultHashHooks {}
