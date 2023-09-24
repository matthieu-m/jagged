//! The Vector

use super::root::{fmt, iter, ops};

use super::{VectorReader, VectorSnapshot};

use super::atomic::AcqRelUsize;
use super::buckets_api::{BucketArray, BucketsExclusiveWriter, BucketsSharedReader, BucketsSharedWriter};
use super::capacity::{BucketIndex, Capacity, ElementIndex, Length};
use super::failure::{Failure, Result};
use super::hooks::VectorHooks;

#[cfg(feature = "with-std")]
use super::hooks::DefaultVectorHooks;

//
//  Public Interface
//

pub use super::buckets::DEFAULT_BUCKETS;

/// `Vector`
#[cfg(not(feature = "with-std"))]
pub struct Vector<T, const N: usize, H: VectorHooks> {
    hooks: H,
    capacity: Capacity,
    length: AcqRelUsize,
    buckets: BucketArray<T, N>,
}

/// `Vector`
#[cfg(feature = "with-std")]
pub struct Vector<T, const N: usize = DEFAULT_BUCKETS, H: VectorHooks = DefaultVectorHooks> {
    //  Hooks of the Vector.
    hooks: H,
    //  Capacity of the first bucket.
    capacity: Capacity,
    //  The number of elements in the vector:
    //
    //  -   Should be loaded before reading any element.
    //  -   Should be stored into after writing any element.
    //
    //  The Acquire/Release semantics are used to guarantee that when an element is read it reflects the last write.
    length: AcqRelUsize,
    buckets: BucketArray<T, N>,
}

impl<T, const N: usize, H: VectorHooks + Default> Vector<T, N, H> {
    /// Creates a new instance of the `Vector` with a maximum capacity of 1 for the first bucket.
    ///
    /// No memory is allocated.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    ///
    /// assert_eq!(0, vec.len());
    /// assert_eq!(0, vec.capacity());
    /// assert_eq!(2 * 1024 * 1024, vec.max_capacity());
    /// ```
    pub fn new() -> Self {
        Self::with_hooks(H::default())
    }

    /// Creates a new instace of the `Vector` with a capacity of at least `capacity_of_0` for the first bucket.
    ///
    /// If `capacity_of_0` is not a power of 2, it is rounded up.
    ///
    /// No memory is allocated.
    ///
    /// #   Panics
    ///
    /// Panics if `capacity_of_0` is strictly greater than `usize::MAX / 2 + 1`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::with_max_capacity(4);
    ///
    /// assert_eq!(0, vec.len());
    /// assert_eq!(0, vec.capacity());
    /// assert_eq!(8 * 1024 * 1024, vec.max_capacity());
    /// ```
    pub fn with_max_capacity(capacity_of_0: usize) -> Self {
        Self::with_max_capacity_and_hooks(capacity_of_0, H::default())
    }
}

impl<T, const N: usize, H: VectorHooks> Vector<T, N, H> {
    /// Creates a new instance of the `Vector` with a capacity of 1 for the first bucket.
    ///
    /// No memory is allocated.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::{Vector, DefaultVectorHooks};
    /// let vec: Vector<i32> = Vector::with_hooks(DefaultVectorHooks::default());
    ///
    /// assert_eq!(0, vec.len());
    /// assert_eq!(0, vec.capacity());
    /// assert_eq!(2 * 1024 * 1024, vec.max_capacity());
    /// ```
    pub fn with_hooks(hooks: H) -> Self {
        Self::with_max_capacity_and_hooks(1, hooks)
    }

    /// Creates a new instace of the `Vector` with a capacity of at least `capacity_of_0` for the first bucket.
    ///
    /// If `capacity_of_0` is not a power of 2, it is rounded up.
    ///
    /// No memory is allocated.
    ///
    /// #   Panics
    ///
    /// Panics if `capacity_of_0` is strictly greater than `usize::MAX / 2 + 1`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::{Vector, DefaultVectorHooks};
    /// let hooks = DefaultVectorHooks::default();
    /// let vec: Vector<i32> = Vector::with_max_capacity_and_hooks(4, hooks);
    ///
    /// assert_eq!(0, vec.len());
    /// assert_eq!(0, vec.capacity());
    /// assert_eq!(8 * 1024 * 1024, vec.max_capacity());
    /// ```
    pub fn with_max_capacity_and_hooks(capacity_of_0: usize, hooks: H) -> Self {
        Self {
            hooks,
            capacity: BucketArray::<T>::capacity(capacity_of_0),
            length: AcqRelUsize::new(0),
            buckets: Default::default(),
        }
    }
}

impl<T, const N: usize, H: VectorHooks> Vector<T, N, H> {
    /// Creates a `VectorReader`.
    ///
    /// A `VectorReader` is a read-only view of the `Vector` instance it is created from which it reflects updates.
    ///
    /// Reflecting updates comes at the small synchronization cost of having to read one atomic variable for each access.
    ///
    /// If synchronization is unnecessary, consider using a `VectorSnapshot` instead.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let reader = vec.reader();
    ///
    /// vec.push(1);
    /// assert_eq!(1, reader[0]);
    /// ```
    pub fn reader(&self) -> VectorReader<'_, T> {
        VectorReader::new(self.capacity, &self.length, self.buckets.as_slice())
    }

    /// Creates a `VectorSnapshot`.
    ///
    /// A `VectorSnapshot` is a read-only view of the `Vector` instance it is created from which it does not reflect
    /// updates. Once created, it is immutable.
    ///
    /// A `VectorSnapshot` can also be created from a `VectorReader`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let snapshot = vec.snapshot();
    ///
    /// vec.push(1);
    /// assert_eq!(None, snapshot.get(0));
    /// ```
    pub fn snapshot(&self) -> VectorSnapshot<'_, T> {
        VectorSnapshot::new(self.shared_reader())
    }

    /// Returns whether the instance contains any element, or not.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// assert!(vec.is_empty());
    ///
    /// vec.push(1);
    /// assert!(!vec.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.shared_reader().is_empty()
    }

    /// Returns the number of elements contained in the instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// assert_eq!(0, vec.len());
    ///
    /// vec.push(1);
    /// assert_eq!(1, vec.len());
    /// ```
    pub fn len(&self) -> usize {
        self.shared_reader().len()
    }

    /// Returns the current capacity of the instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// assert_eq!(0, vec.capacity());
    ///
    /// vec.extend([1, 2, 3, 4, 5].iter().copied());
    /// assert_eq!(8, vec.capacity());
    /// ```
    pub fn capacity(&self) -> usize {
        let number_buckets = self.buckets.as_slice().number_buckets();
        self.capacity.before_bucket(BucketIndex(number_buckets.0)).0
    }

    /// Returns the maximum capacity achievable by the instance.
    ///
    /// The maximum capacity depends:
    ///
    /// -   On the capacity of the first bucket, 1 by default.
    /// -   On the maximum number of buckets, at most N, but possibly less if the capacity of the first bucket is really
    ///     large.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// assert_eq!(2 * 1024 * 1024, vec.max_capacity());
    /// ```
    pub fn max_capacity(&self) -> usize {
        self.shared_reader().max_capacity()
    }

    /// Returns the number of buckets currently used.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// assert_eq!(0, vec.number_buckets());
    ///
    /// vec.extend([1, 2, 3, 4, 5].iter().copied());
    /// assert_eq!(4, vec.number_buckets());
    /// ```
    pub fn number_buckets(&self) -> usize {
        self.shared_reader().number_buckets()
    }

    /// Returns the maximum number of buckets.
    ///
    /// In general, this method should return N.
    ///
    /// If the capacity of the first bucket is large enough that having N buckets would result in `max_capacity`
    /// overflowing `usize`, then the maximum number of buckets will be just as low as necessary to avoid this fate.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// assert_eq!(22, vec.max_buckets());
    ///
    /// let vec: Vector<i32> = Vector::with_max_capacity(usize::MAX / 8);
    /// assert_eq!(3, vec.max_buckets());
    /// ```
    pub fn max_buckets(&self) -> usize {
        self.shared_reader().max_buckets()
    }

    /// Returns a reference to the ith element, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// vec.push(1);
    ///
    /// assert_eq!(Some(1), vec.get(0).copied());
    /// assert_eq!(None, vec.get(1));
    /// ```
    pub fn get(&self, i: usize) -> Option<&T> {
        self.shared_reader().get(ElementIndex(i))
    }

    /// Returns a reference to the ith element.
    ///
    /// #   Safety
    ///
    /// -   Assumes that i is a valid index.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// vec.push(1);
    ///
    /// assert_eq!(1, unsafe { *vec.get_unchecked(0) });
    /// ```
    pub unsafe fn get_unchecked(&self, i: usize) -> &T {
        debug_assert!(i < self.length.load());

        //  Safety:
        //  -   `i` is within bounds, as per pre-condition.
        //  -   `self.capacity` is the capacity of `self`.
        unsafe { self.buckets.as_slice().get_unchecked(ElementIndex(i), self.capacity) }
    }

    /// Returns a reference to the ith element, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let mut vec: Vector<i32> = Vector::new();
    /// vec.push(1);
    ///
    /// if let Some(e) = vec.get_mut(0) {
    ///     *e = 3;
    /// }
    /// assert_eq!(3, vec[0]);
    /// ```
    pub fn get_mut(&mut self, i: usize) -> Option<&mut T> {
        let length = Length(self.length.load());
        //  Safety:
        //  -   length is less than the current length of the vector.
        unsafe { self.buckets.get_mut(ElementIndex(i), length, self.capacity) }
    }

    /// Returns a reference to the ith element.
    ///
    /// #   Safety
    ///
    /// -   Assumes that i is a valid index.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let mut vec: Vector<i32> = Vector::new();
    /// vec.push(1);
    ///
    /// unsafe { *vec.get_unchecked_mut(0) = 3 };
    /// assert_eq!(3, vec[0]);
    /// ```
    pub unsafe fn get_unchecked_mut(&mut self, i: usize) -> &mut T {
        debug_assert!(i < self.length.load());

        //  Safety:
        //  -   `i` is within bounds, as per pre-conditions.
        //  -   `self.capacity` is the capacity of `self`.
        unsafe { self.buckets.get_unchecked_mut(ElementIndex(i), self.capacity) }
    }

    /// Returns the ith bucket, if initialized, or an empty bucket otherwise.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::with_max_capacity(2);
    /// vec.extend([1, 2, 3, 4, 5].iter().copied());
    ///
    /// assert_eq!(&[1, 2], vec.bucket(0));
    /// assert_eq!(&[3, 4], vec.bucket(1));
    /// assert_eq!(&[5], vec.bucket(2));
    /// assert!(vec.bucket(3).is_empty());
    /// ```
    pub fn bucket(&self, i: usize) -> &[T] {
        self.shared_reader().bucket(BucketIndex(i))
    }

    /// Returns the ith bucket, if initialized, or an empty bucket otherwise.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let mut vec: Vector<i32> = Vector::new();
    /// vec.push(1);
    ///
    /// vec.bucket_mut(0)[0] = 3;
    /// assert_eq!(3, vec[0]);
    ///
    /// assert!(vec.bucket_mut(1).is_empty());
    /// ```
    pub fn bucket_mut(&mut self, i: usize) -> &mut [T] {
        let length = Length(self.length.load());

        //  Safety:
        //  -   length exactly matches the length of the vector.
        //  -   length does not increase between creation and use.
        let exclusive = unsafe { BucketsExclusiveWriter::new(&mut self.buckets, length, self.capacity) };

        exclusive.bucket_mut(BucketIndex(i))
    }

    /// Clears the instance.
    ///
    /// The instance is then empty, although it retains previously allocated memory.
    ///
    /// Use `shrink` to release excess memory.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let mut vec: Vector<i32> = Vector::new();
    /// vec.extend([1, 2, 3].iter().copied());
    ///
    /// vec.clear();
    /// assert_eq!(0, vec.len());
    /// assert_eq!(4, vec.capacity());
    /// ```
    pub fn clear(&mut self) {
        let length = Length(self.length.load());

        //  Pre-pooping our pants in case a Drop panics.
        self.length.store(0);

        //  Safety:
        //  -   length exactly matches the length of the vector.
        //  -   length does not increase between creation and use.
        let exclusive = unsafe { BucketsExclusiveWriter::new(&mut self.buckets, length, self.capacity) };

        exclusive.clear();
    }

    /// Shrinks the instance.
    ///
    /// This method releases excess capacity, retaining just enough to accomodate the current elements.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// vec.reserve(8);
    /// assert_eq!(8, vec.capacity());
    ///
    /// vec.extend([1, 2, 3].iter().copied());
    ///
    /// vec.shrink();
    /// assert_eq!(4, vec.capacity());
    /// ```
    pub fn shrink(&self) {
        //  Safety:
        //  -   length does not increase between creation and use.
        unsafe { self.shared_writer() }.shrink(&self.hooks);
    }

    /// Reserves buckets for up to `extra` elements.
    ///
    /// Calling this method reserves enough capacity to be able to push `extra` more elements into the instance without
    /// allocation failure.
    ///
    /// Calling this method has no effect if there is already sufficient capacity for `extra` elements.
    ///
    /// More capacity than strictly necessary may be allocated.
    ///
    /// #   Errors
    ///
    /// Returns an error if sufficient space cannot be reserved to accomodate `extra` elements.
    ///
    /// The behavior is not transactional, so that even in the case an error is returned, extra capacity may have been
    /// reserved.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::failure::Failure;
    /// #   use jagged::vector::Vector;
    /// //  BytesOverflow signals that the size of the bucket to allocate, in  bytes, overflows `usize`.
    /// let vec: Vector<i32> = Vector::with_max_capacity(usize::MAX / 2);
    /// assert_eq!(Err(Failure::BytesOverflow), vec.try_reserve(1));
    ///
    /// //  ElementsOverflow signals that the total number of elements overflows `usize`.
    /// let vec: Vector<i32> = Vector::new();
    /// vec.push(1);
    /// assert_eq!(Err(Failure::ElementsOverflow), vec.try_reserve(usize::MAX));
    ///
    /// //  OutOfBuckets signals that the maximum number of buckets has been reached, and no further bucket can be
    /// //  reserved.
    /// let vec: Vector<i32> = Vector::new();
    /// assert_eq!(Err(Failure::OutOfBuckets), vec.try_reserve(usize::MAX));
    ///
    /// //  OutOfMemory signals that the allocator failed to provide the requested memory; here because the amount
    /// //  requested is too large.
    /// let vec: Vector<i32> = Vector::with_max_capacity(usize::MAX / 8);
    /// assert_eq!(Err(Failure::OutOfMemory), vec.try_reserve(1));
    ///
    /// //  Fortunately, in general, `try_reserve` should succeed.
    /// let vec: Vector<i32> = Vector::new();
    /// assert_eq!(Ok(()), vec.try_reserve(6));
    /// assert_eq!(8, vec.capacity());
    /// ```
    pub fn try_reserve(&self, extra: usize) -> Result<()> {
        //  Safety:
        //  -   length does not increase between creation and use.
        unsafe { self.shared_writer() }.try_reserve(Length(extra), &self.hooks)

        //  Note:   The writes are sequenced with a store to `self.length`, this is unnecessary here as there will be no
        //          read before `self.length` increases to cover the new buckets.
    }

    /// Reserves buckets for up to `extra` elements.
    ///
    /// Calling this method is equivalent to calling `try_reserve` and panicking on error.
    ///
    /// #   Panics
    ///
    /// Panics if sufficient space cannot be reserve to accomodate `extra` elements.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// vec.reserve(6);
    /// assert_eq!(8, vec.capacity());
    /// ```
    pub fn reserve(&self, extra: usize) {
        self.try_reserve(extra).unwrap_or_else(panic_from_failure);
    }

    /// Appends an element to the back.
    ///
    /// #   Errors
    ///
    /// Returns an error if the value cannot be pushed, which may happen either:
    ///
    /// -   If `capacity` is already equal to `max_capacity`.
    /// -   Or if the allocator fails to allocate memory.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// assert_eq!(Ok(()), vec.try_push(3));
    /// assert_eq!(3, vec[0]);
    /// ```
    pub fn try_push(&self, value: T) -> Result<()> {
        //  Safety:
        //  -   length does not increase between creation and use.
        let length = unsafe { self.shared_writer() }.try_push(value, &self.hooks)?;

        self.length.store(length.0);

        Ok(())
    }

    /// Appends an element to the back.
    ///
    /// Calling this method is equivalent to calling `try_push` and panicking on error.
    ///
    /// #   Panics
    ///
    /// Panics if the value cannot be pushed.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// vec.push(3);
    /// assert_eq!(3, vec[0]);
    /// ```
    pub fn push(&self, value: T) {
        self.try_push(value).unwrap_or_else(panic_from_failure);
    }

    /// Appends multiple elements to the back.
    ///
    /// #   Errors
    ///
    /// Returns an error if any of the values cannot be pushed, which may happen either:
    ///
    /// -   If `capacity` reaches `max_capacity`.
    /// -   Or if the allocator fails to allocate memory.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// assert_eq!(Ok(()), vec.try_extend([1, 2, 3].iter().copied()));
    /// assert_eq!(3, vec.len());
    /// ```
    pub fn try_extend<C>(&self, collection: C) -> Result<()>
    where
        C: IntoIterator<Item = T>,
    {
        //  Safety:
        //  -   length does not increase between creation and use.
        let (length, failure) = unsafe { self.shared_writer() }.try_extend(collection, &self.hooks);

        self.length.store(length.0);

        if let Some(failure) = failure {
            Err(failure)
        } else {
            Ok(())
        }
    }

    /// Appends multiple elements to the back.
    ///
    /// Calling this method is equivalent to calling `try_extend` and panicking on error.
    ///
    /// #   Panics
    ///
    /// Panics if any of the values cannot be pushed.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// vec.extend([1, 2, 3].iter().copied());
    /// assert_eq!(3, vec.len());
    /// ```
    pub fn extend<C>(&self, collection: C)
    where
        C: IntoIterator<Item = T>,
    {
        self.try_extend(collection).unwrap_or_else(panic_from_failure);
    }

    //  Returns a SharedReader.
    fn shared_reader(&self) -> BucketsSharedReader<'_, T> {
        let length = Length(self.length.load());
        //  Safety:
        //  -   length is less than the length of the vector.
        unsafe { BucketsSharedReader::new(self.buckets.as_slice(), length, self.capacity) }
    }

    //  Returns a SharedWriter.
    //
    //  #   Safety
    //
    //  -   Assumes that self.length will not increase outside of this instance.
    unsafe fn shared_writer(&self) -> BucketsSharedWriter<'_, T> {
        let length = Length(self.length.load());
        //  Safety:
        //  -   length exactly matches the length of the vector.
        //  -   single writer thread.
        unsafe { BucketsSharedWriter::new(self.buckets.as_slice(), length, self.capacity) }
    }
}

/// A `Vector<T>` can be `Send` across threads whenever a `Vec<T>` can, unlike a `Vec<T>` it is never `Sync` however.
///
/// #   Example of Send.
///
/// With most types, it is possible to send a `Vector` across threads.
///
/// ```
/// # use jagged::vector::Vector;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let vec: Vector<_> = Vector::new();
/// vec.push("Hello".to_string());
///
/// ensure_send(vec);
/// ```
///
/// #   Example of not Send.
///
/// Types that are not Send, however, prevent from sending `Vector` across threads.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::vector::Vector;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let vec: Vector<_> = Vector::new();
/// vec.push(Rc::new(3));
///
/// ensure_send(vec);
/// ```
///
/// #   Example of not Sync.
///
/// It is never possible to share a reference to `Vector<T>` across threads.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::vector::Vector;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let vec: Vector<_> = Vector::new();
/// vec.push(1);
///
/// ensure_sync(vec);
/// ```
unsafe impl<T: Send, const N: usize, H: VectorHooks + Send> Send for Vector<T, N, H> {}

/// A `Vector<T>` is always safe to use across panics.
///
/// #   Example of UnwindSafe.
///
/// ```
/// # use std::panic::UnwindSafe;
/// # use std::rc::Rc;
/// # use jagged::vector::Vector;
/// fn ensure_unwind_safe<T: UnwindSafe>(_: T) {}
///
/// let vec: Vector<_> = Vector::new();
/// vec.push(Rc::new(4));
///
/// ensure_unwind_safe(vec);
/// ```
#[cfg(feature = "with-std")]
impl<T, const N: usize, H: VectorHooks> std::panic::UnwindSafe for Vector<T, N, H> {}

#[cfg(feature = "with-std")]
impl<T, const N: usize, H: VectorHooks> std::panic::RefUnwindSafe for Vector<T, N, H> {}

impl<T, const N: usize, H: VectorHooks> Drop for Vector<T, N, H> {
    fn drop(&mut self) {
        self.clear();
        self.shrink();
    }
}

impl<T, const N: usize, H: VectorHooks + Default> Default for Vector<T, N, H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: fmt::Debug, const N: usize, H: VectorHooks> fmt::Debug for Vector<T, N, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.shared_reader().debug("Vector", f)
    }
}

impl<T, const N: usize, H: VectorHooks + Default> iter::FromIterator<T> for Vector<T, N, H> {
    fn from_iter<C>(collection: C) -> Self
    where
        C: IntoIterator<Item = T>,
    {
        let result: Vector<_, N, _> = Vector::with_hooks(H::default());
        result.extend(collection);
        result
    }
}

impl<T, const N: usize, H: VectorHooks> ops::Index<usize> for Vector<T, N, H> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get(index).expect("Valid index")
    }
}

impl<T, const N: usize, H: VectorHooks> ops::IndexMut<usize> for Vector<T, N, H> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(index).expect("Valid index")
    }
}

#[cold]
#[inline(never)]
fn panic_from_failure(failure: Failure) {
    panic!("{}", failure);
}

#[cfg(test)]
mod tests {

    use std::mem;

    use super::Vector;

    use crate::utils::tester::*;

    #[test]
    fn size_of() {
        const PTR_SIZE: usize = mem::size_of::<usize>();

        assert_eq!(24 * PTR_SIZE, mem::size_of::<Vector<u8>>());
    }

    #[test]
    fn trait_debug() {
        use std::fmt::Write;

        let vec: Vector<_> = Vector::new();
        vec.extend([1, 2, 3, 4, 5].iter().copied());

        let mut sink = String::new();
        let _ = write!(sink, "{:?}", vec);

        assert_eq!(
            "Vector { capacity: 8, length: 5, buckets: [[1], [2], [3, 4], [5]] }",
            sink
        );
    }

    #[test]
    fn trait_from_iterator() {
        let vec: Vector<_> = [1, 2, 3, 4, 5].iter().copied().collect();

        assert_eq!(5, vec.len());
    }

    #[test]
    fn panic_drop() {
        use std::panic::{catch_unwind, AssertUnwindSafe};

        let collection = vec![
            PanickyDrop::new(0),
            PanickyDrop::new(1),
            PanickyDrop::panicky(2),
            PanickyDrop::new(3),
        ];

        let mut vec: Vector<_> = Vector::default();
        vec.extend(collection);

        let panicked = catch_unwind(AssertUnwindSafe(|| {
            vec.clear();
        }));
        assert!(panicked.is_err());

        assert_eq!(0, vec.len());
    }
} //  mod tests
