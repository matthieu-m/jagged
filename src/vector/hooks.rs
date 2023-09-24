//! Hooks of the Vector.

use super::allocator;

/// VectorHooks
///
/// There are two important hooks for a Vector:
/// -   The maximum number of buckets, which defines the capacity and the memory footprint.
/// -   The allocator and deallocator functions.
///
/// The VectorHooks trait allows customizing allocation, but unfortunately does not allow customizing the size, as this
/// does not quite yet work...
///
/// Also see DefaultVectorHooks for the default, when the `alloc` feature is used.
pub trait VectorHooks: allocator::Allocator {}

/// DefaultVectorHooks
///
/// Default hooks for the Vector:
/// -   deferring allocation and deallocation to `DefaultAllocator`.
#[cfg(feature = "with-std")]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DefaultVectorHooks(allocator::DefaultAllocator);

#[cfg(feature = "with-std")]
impl allocator::Allocator for DefaultVectorHooks {
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
impl VectorHooks for DefaultVectorHooks {}
