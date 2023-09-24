//! Internal testing utilities

use crate::root::sync::atomic::{AtomicUsize, Ordering};
use crate::root::{cell, fmt, hash, iter, ops, ptr};

use crate::allocator::{Allocator, DefaultAllocator, Layout};
use crate::hashcore::key::Key;

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
    pub fn new(allowed: usize) -> TestAllocator {
        let allocator = TestAllocator::default();
        allocator.allowed.set(allowed);
        allocator
    }

    pub fn unlimited() -> TestAllocator {
        TestAllocator::new(usize::MAX)
    }

    pub fn allocations(&self) -> Vec<Allocation> {
        self.allocations.borrow().clone()
    }

    pub fn allocation_sizes(&self) -> Vec<usize> {
        self.allocations.borrow().iter().map(|&a| a.size).collect()
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

        //  Safety:
        //  -   Forward.
        let result = unsafe { self.allocator.allocate(layout) };
        assert_ne!(ptr::null_mut(), result);

        let allocation = Allocation::new(result, layout);
        self.allocations.borrow_mut().push(allocation);

        result
    }

    unsafe fn deallocate(&self, ptr: *mut u8, layout: Layout) {
        //  Safety:
        //  -   Forward.
        unsafe { self.allocator.deallocate(ptr, layout) };

        let allocation = Allocation::new(ptr, layout);

        if let Some(index) = self.locate(allocation) {
            self.allocations.borrow_mut().remove(index);
        } else {
            panic!("Could not find {:?} in {:?}", allocation, &*self.allocations.borrow());
        }
    }
}

impl Drop for TestAllocator {
    fn drop(&mut self) {
        self.clear()
    }
}

//  Test Hooks
//
//  An allocator specifically for testing:
//  -   Allows injecting allocation failures.
//  -   Checks that allocations and deallocations match.
//
//  Combined with a hasher allowing to insert any hash.
pub struct TestHooks {
    hash: u64,
    panic_hash: cell::Cell<u64>,
    allocator: TestAllocator,
}

impl TestHooks {
    pub fn new(allowed: usize) -> TestHooks {
        let hooks = TestHooks::default();
        hooks.allowed.set(allowed);
        hooks
    }

    pub fn unlimited() -> TestHooks {
        TestHooks::new(usize::MAX)
    }

    pub fn set_panic_hash(&self, count: u64) {
        self.panic_hash.set(count);
    }
}

impl Default for TestHooks {
    fn default() -> Self {
        Self {
            hash: 0,
            panic_hash: cell::Cell::new(u64::MAX),
            allocator: TestAllocator::default(),
        }
    }
}

impl ops::Deref for TestHooks {
    type Target = TestAllocator;

    fn deref(&self) -> &Self::Target {
        &self.allocator
    }
}

impl Allocator for TestHooks {
    unsafe fn allocate(&self, layout: Layout) -> *mut u8 {
        //  Safety:
        //  -   Forward.
        unsafe { self.allocator.allocate(layout) }
    }

    unsafe fn deallocate(&self, ptr: *mut u8, layout: Layout) {
        //  Safety:
        //  -   Forward.
        unsafe { self.allocator.deallocate(ptr, layout) }
    }
}

impl hash::BuildHasher for TestHooks {
    type Hasher = TestHasher;

    fn build_hasher(&self) -> TestHasher {
        let count = self.panic_hash.get();
        assert_ne!(0, count);

        self.panic_hash.set(count - 1);

        TestHasher(self.hash)
    }
}

//  A very "poor" hasher, in a sense, however controlling the hash is very useful for functional testing.
pub struct TestHasher(u64);

impl hash::Hasher for TestHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, _: &[u8]) {}
}

//  SpyCount
//
//  A counter of the number of instances of elements.
pub struct SpyCount(AtomicUsize);

impl SpyCount {
    pub fn zero() -> Self {
        SpyCount(AtomicUsize::new(0))
    }

    pub fn get(&self) -> usize {
        self.0.load(Ordering::Relaxed)
    }

    fn decrement(&self) {
        self.0.fetch_sub(1, Ordering::Relaxed);
    }

    fn increment(&self) {
        self.0.fetch_add(1, Ordering::Relaxed);
    }
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

//  Spy Key
//
//  A SpyElement combined with a key.
pub struct SpyKey<'a>(u64, SpyElement<'a>);

impl<'a> SpyKey<'a> {
    pub fn new(key: u64, count: &'a SpyCount) -> Self {
        Self(key, SpyElement::new(count))
    }
}

impl<'a> fmt::Debug for SpyKey<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SpyKey({})", self.0)
    }
}

impl<'a> Key for SpyKey<'a> {
    type Key = u64;

    fn key(&self) -> &Self::Key {
        &self.0
    }
}

//  An Allocator which panics when failing to allocate or deallocate.
#[derive(Default)]
pub struct PanickyAllocator(TestAllocator);

impl ops::Deref for PanickyAllocator {
    type Target = TestAllocator;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Allocator for PanickyAllocator {
    unsafe fn allocate(&self, layout: Layout) -> *mut u8 {
        //  Safety:
        //  -   Forward.
        let result = unsafe { self.0.allocate(layout) };

        assert!(!result.is_null());

        result
    }

    unsafe fn deallocate(&self, ptr: *mut u8, layout: Layout) {
        //  Safety:
        //  -   Forward.
        unsafe { self.0.deallocate(ptr, layout) };
    }
}

//  A value which may panic on drop.
#[derive(Eq, Hash, PartialEq)]
pub struct PanickyDrop<T>(T, bool);

impl<T> PanickyDrop<T> {
    //  Creates a normal instance.
    pub fn new(value: T) -> Self {
        Self(value, false)
    }

    //  Creates a panicky instance.
    pub fn panicky(value: T) -> Self {
        Self(value, true)
    }
}

impl<T> Drop for PanickyDrop<T> {
    fn drop(&mut self) {
        if self.1 {
            panic!("Oh No!")
        }
    }
}

impl<T> Key for PanickyDrop<T> {
    type Key = T;

    fn key(&self) -> &Self::Key {
        &self.0
    }
}

//  An Iterator which panics when reaching the configured count.
pub struct PanickyIterator(u32, u32);

impl PanickyIterator {
    //  Creates an instance configured to panic after yielding `count` elements.
    pub fn new(count: u32) -> PanickyIterator {
        PanickyIterator(0, count)
    }
}

impl iter::Iterator for PanickyIterator {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        assert_ne!(self.0, self.1);

        let result = self.0;
        self.0 += 1;
        Some(result)
    }
}
