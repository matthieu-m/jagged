//! Allocator.
//!
//! The `Allocator` trait allows a user to customize allocation on a per instance basis, without depending on the
//! `alloc` crate.
use super::root::alloc;

/// Layout, re-exported.
pub type Layout = alloc::Layout;

/// Allocator
pub trait Allocator {
    /// Allocates memory as per the size and alignment requirements.
    ///
    /// May return a null pointer if the allocation cannot be satisfied.
    ///
    /// #   Safety
    ///
    /// -   Assumes that the size of the Layout is non-zero.
    unsafe fn allocate(&self, layout: Layout) -> *mut u8;

    /// Deallocates memory.
    ///
    /// #   Safety
    ///
    /// -   Assumes that `ptr` was allocated by `self.alloc`.
    /// -   Assumes that `ptr` was not already deallocated.
    /// -   Assumes that `layout` matches the layout with which `ptr` was allocated.
    unsafe fn deallocate(&self, ptr: *mut u8, layout: Layout);
}

/// DefaultAllocator
///
/// A default implementation of the `Allocator` trait, relying on the `alloc` crate global allocator.
#[cfg(feature = "with-std")]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DefaultAllocator;

#[cfg(feature = "with-std")]
impl Allocator for DefaultAllocator {
    unsafe fn allocate(&self, layout: Layout) -> *mut u8 {
        alloc::alloc(layout)
    }

    unsafe fn deallocate(&self, ptr: *mut u8, layout: Layout) {
        alloc::dealloc(ptr, layout)
    }
}
