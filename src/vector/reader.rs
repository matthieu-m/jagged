//! A Reader of the Vector.
//!
//! The `VectorReader` is read-only, and reflects updates to the referred
//! `Vector`.

use super::root::{fmt, ops};

use super::VectorSnapshot;

use super::atomic::AcqRelUsize;
use super::buckets_api::{BucketArray, BucketsSharedReader};
use super::capacity::{Capacity, BucketIndex, ElementIndex, Length};

/// `VectorReader`
///
/// A `VectorReader` is an up-to-date read-only view of the `Vector` it was
/// created from.
///
/// It always reflects updates to the underlying instance.
pub struct VectorReader<'a, T> {
    //  Capacity of the first bucket.
    capacity: Capacity,
    length: &'a AcqRelUsize,
    buckets: &'a BucketArray<T>,
}

impl<'a, T> VectorReader<'a, T> {
    //  Creates a new instance.
    pub(crate) fn new(
        capacity: Capacity,
        length: &'a AcqRelUsize,
        buckets: &'a BucketArray<T>,
    )
        -> Self
    {
        Self { capacity, length, buckets }
    }

    /// Creates a `VectorSnapshot`.
    ///
    /// A `VectorSnapshot` is a read-only view of the `VectorReader` instance it
    /// is created from which it does not reflect updates. Once created, it is
    /// immutable.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let reader = vec.reader();
    /// let snapshot = reader.snapshot();
    ///
    /// vec.push(1);
    /// assert_eq!(1, reader[0]);
    /// assert_eq!(None, snapshot.get(0));
    /// ```
    pub fn snapshot(&self) -> VectorSnapshot<'a, T> {
        VectorSnapshot::new(self.shared_reader())
    }

    /// Returns whether the `Vector` instance contains any element, or not.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let reader = vec.reader();
    /// assert!(reader.is_empty());
    ///
    /// vec.push(1);
    /// assert!(!reader.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.shared_reader().is_empty() }

    /// Returns the number of elements contained in the `Vector` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let reader = vec.reader();
    /// assert_eq!(0, reader.len());
    ///
    /// vec.push(1);
    /// assert_eq!(1, reader.len());
    /// ```
    pub fn len(&self) -> usize { self.shared_reader().len() }

    /// Returns the maximum capacity achievable by the `Vector` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// let reader = vec.reader();
    /// assert_eq!(2 * 1024 * 1024, reader.max_capacity());
    /// ```
    pub fn max_capacity(&self) -> usize { self.shared_reader().max_capacity() }

    /// Returns the number of buckets currently used by the `Vector` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// let reader = vec.reader();
    /// assert_eq!(0, reader.number_buckets());
    ///
    /// vec.extend([1, 2, 3, 4, 5].iter().copied());
    /// assert_eq!(4, reader.number_buckets());
    /// ```
    pub fn number_buckets(&self) -> usize {
        self.shared_reader().number_buckets()
    }

    /// Returns the maximum number of buckets.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// let reader = vec.reader();
    /// assert_eq!(22, reader.max_buckets());
    /// ```
    pub fn max_buckets(&self) -> usize { self.shared_reader().max_buckets() }

    /// Returns a reference to the ith element, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let reader = vec.reader();
    /// assert_eq!(None, reader.get(0));
    ///
    /// vec.push(1);
    /// assert_eq!(Some(1), reader.get(0).copied());
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        self.shared_reader().get(ElementIndex(index))
    }

    /// Returns a reference to the ith element, with no bounds check.
    ///
    /// #   Safety
    ///
    /// `i` must be less than `self.len()`.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let reader = vec.reader();
    ///
    /// vec.push(1);
    /// assert_eq!(1, unsafe { *reader.get_unchecked(0) });
    /// ```
    pub unsafe fn get_unchecked(&self, i: usize) -> &T {
        self.buckets.get_unchecked(ElementIndex(i), self.capacity)
    }

    /// Returns the ith bucket, if any, or an empty bucket otherwise.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let reader = vec.reader();
    ///
    /// vec.extend([1, 2, 3, 4, 5].iter().copied());
    /// assert_eq!(&[1], reader.bucket(0));
    /// assert_eq!(&[2], reader.bucket(1));
    /// assert_eq!(&[3, 4], reader.bucket(2));
    /// assert_eq!(&[5], reader.bucket(3));
    /// assert!(reader.bucket(4).is_empty());
    /// ```
    pub fn bucket(&self, i: usize) -> &[T] {
        self.shared_reader().bucket(BucketIndex(i))
    }

    //  Returns a SharedReader.
    fn shared_reader(&self) -> BucketsSharedReader<'a, T> {
        let length = Length(self.length.load());
        //  Safety:
        //  -   length is less than the length of the vector.
        unsafe {
            BucketsSharedReader::new(self.buckets, length, self.capacity)
        }
    }
}

/// A `VectorReader<T>` can be `Send` across threads whenever a `&[T]` can.
///
/// #   Example of Send.
///
/// With most types, it is possible to send a `VectorReader` across threads.
///
/// ```
/// # use jagged::vector::Vector;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let vec: Vector<_> = Vector::new();
/// vec.push("Hello".to_string());
///
/// ensure_send(vec.reader());
/// ```
///
/// #   Example of not Send.
///
/// Types that are not Sync, however, cannot share their references across
/// threads.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::vector::Vector;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let vec: Vector<_> = Vector::new();
/// vec.push(Rc::new(3));
///
/// ensure_send(vec.reader());
/// ```
unsafe impl<'a, T: Sync> Send for VectorReader<'a, T> {}

/// A `VectorReader<T>` can be shared across threads whenver `&[T]` can.
///
/// #   Example of Sync.
///
/// With most types, it is possible to share a `VectorReader` across threads.
///
/// ```
/// # use jagged::vector::Vector;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let vec: Vector<_> = Vector::new();
/// vec.push("Hello".to_string());
///
/// ensure_sync(vec.reader());
/// ```
///
/// #   Example of not Sync.
///
/// Types that are not Sync, however, cannot share their references across
/// threads.
///
/// ```compile_fail
/// # use std::rc::Rc;
/// # use jagged::vector::Vector;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let vec: Vector<_> = Vector::new();
/// vec.push(Rc::new(3));
///
/// ensure_sync(vec.reader());
/// ```
unsafe impl<'a, T: Sync> Sync for VectorReader<'a, T> {}

impl<'a, T> Clone for VectorReader<'a, T> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T> Copy for VectorReader<'a, T> {}

impl<'a, T: fmt::Debug> fmt::Debug for VectorReader<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.shared_reader().debug("VectorReader", f)
    }
}

impl<'a, T> ops::Index<usize> for VectorReader<'a, T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get(index).expect("Valid index")
    }
}

#[cfg(test)]
mod tests {

use vector::Vector;

#[test]
fn trait_clone() {
    #[derive(Debug)]
    struct NotClonable(u8);

    let vec: Vector<_> = Vector::new();
    vec.push(NotClonable(0));

    let reader = vec.reader();
    std::mem::drop(reader.clone());
}

#[test]
fn trait_copy() {
    let vec: Vector<_> = Vector::new();
    vec.push("Hello, World".to_string());

    let reader = vec.reader();
    let other = reader;
    std::mem::drop(reader);
    std::mem::drop(other);
}

#[test]
fn trait_debug() {
    use std::fmt::Write;

    let vec: Vector<_> = Vector::new();
    vec.extend([1, 2, 3, 4, 5].iter().copied());

    let mut sink = String::new();
    let _ = write!(sink, "{:?}", vec.reader());

    assert_eq!(
        "VectorReader { capacity: 8, length: 5, buckets: [[1], [2], [3, 4], [5]] }",
        sink
    );
}

}
