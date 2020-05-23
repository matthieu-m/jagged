//! Internal testing utilities

use crate::allocator::{Allocator, DefaultAllocator, Layout};
use crate::root::{cell, ptr};
use crate::root::sync::atomic::{AtomicUsize, Ordering};

//  Allocation
//
//  Description of an allocation.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct Allocation {
    //  The size of the allocation, in bytes.
    pub size: usize,
    //  The alignment of the allocation, in bytes.
    pub alignment: usize,
    //  The pointer allocated.
    pub pointer: *mut u8,
}

impl Allocation {
    pub fn new(pointer: *mut u8, layout: Layout) -> Self {
        Allocation {
            size: layout.size(),
            alignment: layout.align(),
            pointer,
        }
    }

    pub fn layout(&self) -> Layout {
        Layout::from_size_align(self.size, self.alignment).unwrap()
    }
}

//  Test Allocator
//
//  An allocator specifically for testing:
//  -   Allows injecting allocation failures.
//  -   Checks that allocations and deallocations match.
#[derive(Default)]
pub struct TestAllocator {
    //  The actual allocator.
    pub allocator: DefaultAllocator,
    //  The number of allocations allowed.
    pub allowed: cell::Cell<usize>,
    //  The allocations performed; to check deallocation requests.
    pub allocations: cell::RefCell<Vec<Allocation>>,
}

impl TestAllocator {
    pub fn allocations(&self) -> Vec<Allocation> {
        self.allocations.borrow().clone()
    }

    pub fn allocation_sizes(&self) -> Vec<usize> {
        self.allocations.borrow().iter()
            .map(|&a| a.size)
            .collect()
    }

    pub fn clear(&self) {
        for a in self.allocations.borrow().iter() {
            //  Safety:
            //  -   Were allocated, and not deallocated.
            unsafe { self.allocator.deallocate(a.pointer, a.layout()) };
        }
    }

    fn locate(&self, allocation: Allocation) -> Option<usize> {
        self.allocations.borrow().iter().position(|a| *a == allocation)
    }
}

impl Allocator for TestAllocator {
    unsafe fn allocate(&self, layout: Layout) -> *mut u8 {
        if self.allowed.get() == 0 {
            return ptr::null_mut();
        }

        self.allowed.set(self.allowed.get() - 1);

        let result = self.allocator.allocate(layout);
        assert_ne!(ptr::null_mut(), result);

        let allocation = Allocation::new(result, layout);
        self.allocations.borrow_mut().push(allocation);

        result
    }

    unsafe fn deallocate(&self, ptr: *mut u8, layout: Layout) {
        let allocation = Allocation::new(ptr, layout);

        if let Some(index) = self.locate(allocation) {
            self.allocations.borrow_mut().remove(index);
        } else {
            panic!("Could not find {:?} in {:?}",
                allocation, &*self.allocations.borrow());
        }

        self.allocator.deallocate(ptr, layout)
    }
}

impl Drop for TestAllocator {
    fn drop(&mut self) { self.clear() }
}

//  SpyCount
//
//  A counter of the number of instances of elements.
pub struct SpyCount(AtomicUsize);

impl SpyCount {
    pub fn zero() -> Self { SpyCount(AtomicUsize::new(0)) }

    pub fn get(&self) -> usize { self.0.load(Ordering::Relaxed) }

    fn decrement(&self) { self.0.fetch_sub(1, Ordering::Relaxed); }

    fn increment(&self) { self.0.fetch_add(1, Ordering::Relaxed); }
}

//  Spy Element
//
//  An element tracking the number of instances, helpful to ensure proper drop.
pub struct SpyElement<'a> {
    count: &'a SpyCount,
}

impl<'a> SpyElement<'a> {
    pub fn new(count: &'a SpyCount) -> Self {
        count.increment();
        SpyElement { count }
    }
}

impl<'a> Drop for SpyElement<'a> {
    fn drop(&mut self) {
        self.count.decrement();
    }
}