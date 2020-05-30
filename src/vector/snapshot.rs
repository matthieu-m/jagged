//! A Snapshot of the Vector.
//!
//! The Snapshot is synchronization-free, and does not reflect updates to the
//! referred Vector.

use super::root::{cmp, fmt, hash, iter, ops};

use super::buckets_api::{BucketsSharedReader, BucketIterator, ElementIterator};
use super::capacity::{BucketIndex, ElementIndex};

/// `VectorSnapshot`
///
/// A `VectorSnapshot` is a snapshot of the state of the underlying `Vector` at
/// the moment the instance is created.
///
/// It never reflects further updates to the `Vector` instance it was created
/// from.
pub struct VectorSnapshot<'a, T> {
    reader: BucketsSharedReader<'a, T>,
}

impl<'a, T> VectorSnapshot<'a, T> {
    //  Creates a new instance.
    pub(crate) fn new(reader: BucketsSharedReader<'a, T>) -> Self {
        Self { reader }
    }

    /// Returns whether the `Vector` instance contained any element, or not.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let snapshot = vec.snapshot();
    /// assert!(snapshot.is_empty());
    ///
    /// vec.push(1);
    ///
    /// //  Push not reflected in previous instance.
    /// assert!(snapshot.is_empty());
    ///
    /// //  Push reflected in new instance.
    /// let snapshot = vec.snapshot();
    /// assert!(!snapshot.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.reader.is_empty() }

    /// Returns the number of elements contained in the `Vector` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let snapshot = vec.snapshot();
    /// assert_eq!(0, snapshot.len());
    ///
    /// vec.push(1);
    ///
    /// //  Push not reflected in previous instance.
    /// assert_eq!(0, snapshot.len());
    ///
    /// //  Push reflected in new instance.
    /// let snapshot = vec.snapshot();
    /// assert_eq!(1, snapshot.len());
    /// ```
    pub fn len(&self) -> usize { self.reader.len() }

    /// Returns the maximum capacity achievable by the `Vector` instance.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// let snapshot = vec.snapshot();
    /// assert_eq!(2 * 1024 * 1024, snapshot.max_capacity());
    /// ```
    pub fn max_capacity(&self) -> usize { self.reader.max_capacity() }

    /// Returns the number of buckets currently used.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// let snapshot = vec.snapshot();
    /// assert_eq!(0, snapshot.number_buckets());
    ///
    /// vec.extend([1, 2, 3, 4, 5].iter().copied());
    ///
    /// //  Extend not reflected in previous instance.
    /// assert_eq!(0, snapshot.number_buckets());
    ///
    /// //  Extend reflected in new instance.
    /// let snapshot = vec.snapshot();
    /// assert_eq!(4, snapshot.number_buckets());
    /// ```
    pub fn number_buckets(&self) -> usize { self.reader.number_buckets() }

    /// Returns the maximum number of buckets.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<i32> = Vector::new();
    /// let snapshot = vec.snapshot();
    /// assert_eq!(22, snapshot.max_buckets());
    /// ```
    pub fn max_buckets(&self) -> usize { self.reader.max_buckets() }

    ///  Returns a reference to the ith element, if any.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let snapshot = vec.snapshot();
    /// assert_eq!(None, snapshot.get(0));
    ///
    /// vec.push(1);
    ///
    /// //  Push not reflected in previous instance.
    /// assert_eq!(None, snapshot.get(0));
    ///
    /// //  Push reflected in new instance.
    /// let snapshot = vec.snapshot();
    /// assert_eq!(Some(1), snapshot.get(0).copied());
    /// ```
    pub fn get(&self, i: usize) -> Option<&T> {
        self.reader.get(ElementIndex(i))
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
    /// vec.push(1);
    ///
    /// let snapshot = vec.snapshot();
    /// assert_eq!(1, unsafe { *snapshot.get_unchecked(0) });
    /// ```
    pub unsafe fn get_unchecked(&self, i: usize) -> &T {
        self.reader.get_unchecked(ElementIndex(i))
    }

    /// Returns the ith bucket, if any, or an empty bucket otherwise.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    /// let snapshot = vec.snapshot();
    ///
    /// vec.extend([1, 2, 3, 4, 5].iter().copied());
    ///
    /// //  Extend not reflected in previous instance.
    /// assert!(snapshot.bucket(0).is_empty());
    ///
    /// //  Extend reflected in new instance.
    /// let snapshot = vec.snapshot();
    /// assert_eq!(&[1], snapshot.bucket(0));
    /// assert_eq!(&[2], snapshot.bucket(1));
    /// assert_eq!(&[3, 4], snapshot.bucket(2));
    /// assert_eq!(&[5], snapshot.bucket(3));
    /// assert!(snapshot.bucket(4).is_empty());
    /// ```
    pub fn bucket(&self, i: usize) -> &[T] {
        self.reader.bucket(BucketIndex(i))
    }

    /// Returns an iterator to iterate over the buckets, yielding slices.
    ///
    /// In general, this iterator should be used when performance dictates it,
    /// otherwise the element-wise iterator should be more convenient.
    ///
    /// #   Example
    ///
    /// ```
    /// #   use jagged::vector::Vector;
    /// let vec: Vector<_> = Vector::new();
    ///
    /// vec.extend([1, 2, 3, 4, 5].iter().copied());
    ///
    /// let snapshot = vec.snapshot();
    /// let mut iterator = snapshot.iter_buckets();
    ///
    /// assert_eq!(Some(&[1][..]), iterator.next());
    /// assert_eq!(Some(&[2][..]), iterator.next());
    /// assert_eq!(Some(&[3, 4][..]), iterator.next());
    /// assert_eq!(Some(&[5][..]), iterator.next());
    /// assert_eq!(None, iterator.next());
    /// ```
    pub fn iter_buckets(&self) -> BucketIterator<'a, T> {
        self.reader.iter_buckets()
    }
}

/// A `VectorSnapshot<T>` can be `Send` across threads whenever a `&[T]` can.
///
/// #   Example of Send.
///
/// With most types, it is possible to send a `VectorSnapshot` across threads.
///
/// ```
/// # use jagged::vector::Vector;
/// fn ensure_send<T: Send>(_: T) {}
///
/// let vec: Vector<_> = Vector::new();
/// vec.push("Hello".to_string());
///
/// ensure_send(vec.snapshot());
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
/// ensure_send(vec.snapshot());
/// ```
unsafe impl<'a, T: Sync> Send for VectorSnapshot<'a, T> {}

/// A `VectorSnapshot<T>` can be shared across threads whenever `&[T]` can.
///
/// #   Example of Sync.
///
/// With most types, it is possible to share a `VectorSnapshot` across threads.
///
/// ```
/// # use jagged::vector::Vector;
/// fn ensure_sync<T: Sync>(_: T) {}
///
/// let vec: Vector<_> = Vector::new();
/// vec.push("Hello".to_string());
///
/// ensure_sync(vec.snapshot());
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
/// ensure_sync(vec.snapshot());
/// ```
unsafe impl<'a, T: Sync> Sync for VectorSnapshot<'a, T> {}

#[cfg(feature = "with-std")]
impl<'a, T> std::panic::UnwindSafe for VectorSnapshot<'a, T> {}

#[cfg(feature = "with-std")]
impl<'a, T> std::panic::RefUnwindSafe for VectorSnapshot<'a, T> {}

impl<'a, T> Clone for VectorSnapshot<'a, T> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T> Copy for VectorSnapshot<'a, T> {}

impl<'a, T: fmt::Debug> fmt::Debug for VectorSnapshot<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.reader.debug("VectorSnapshot", f)
    }
}

impl<'a, T: hash::Hash> hash::Hash for VectorSnapshot<'a, T> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.reader.hash(state);
    }
}

impl<'a, T: Eq> Eq for VectorSnapshot<'a, T> {}

impl<'a, T: PartialEq> PartialEq for VectorSnapshot<'a, T> {
    fn eq(&self, other: &Self) -> bool { self.reader.eq(&other.reader) }
}

impl<'a, T: Ord> Ord for VectorSnapshot<'a, T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.reader.cmp(&other.reader)
    }
}

impl<'a, T: PartialOrd> PartialOrd for VectorSnapshot<'a, T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.reader.partial_cmp(&other.reader)
    }
}

impl<'a, T> iter::IntoIterator for VectorSnapshot<'a, T> {
    type Item = &'a T;
    type IntoIter = ElementIterator<'a, T>;

    fn into_iter(self) -> ElementIterator<'a, T> {
        self.reader.into_iter()
    }
}

impl<'a, 'b, T> iter::IntoIterator for &'b VectorSnapshot<'a, T> {
    type Item = &'a T;
    type IntoIter = ElementIterator<'a, T>;

    fn into_iter(self) -> ElementIterator<'a, T> {
        self.reader.into_iter()
    }
}

impl<'a, T> ops::Index<usize> for VectorSnapshot<'a, T> {
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

    let snapshot = vec.snapshot();
    std::mem::drop(snapshot.clone());
}

#[test]
fn trait_copy() {
    let vec: Vector<_> = Vector::new();
    vec.push("Hello, World".to_string());

    let snapshot = vec.snapshot();
    let other = snapshot;
    std::mem::drop(snapshot);
    std::mem::drop(other);
}

#[test]
fn trait_debug() {
    use std::fmt::Write;

    let vec: Vector<_> = Vector::new();
    vec.extend([1, 2, 3, 4, 5].iter().copied());

    let mut sink = String::new();
    let _ = write!(sink, "{:?}", vec.snapshot());

    assert_eq!(
        "VectorSnapshot { capacity: 8, length: 5, buckets: [[1], [2], [3, 4], [5]] }",
        sink
    );
}

#[test]
fn trait_hash() {
    fn ensure_hash<T: std::hash::Hash>(_: T) {}

    let vec: Vector<_> = Vector::new();
    vec.push(1);

    ensure_hash(vec.snapshot());
}

#[test]
fn trait_partial_eq() {
    let left: Vector<_> = Vector::new();
    left.push(1.0);

    let right: Vector<_> = Vector::new();
    right.push(1.0);

    assert_eq!(left.snapshot(), right.snapshot());

    left.push(2.0);

    assert_ne!(left.snapshot(), right.snapshot());
}

#[test]
fn trait_partial_ord() {
    use std::cmp::Ordering;

    fn partial_cmp(left: f32, right: f32) -> Option<Ordering> {
        let leftv: Vector<_> = Vector::new();
        leftv.push(left);

        let rightv: Vector<_> = Vector::new();
        rightv.push(right);

        leftv.snapshot().partial_cmp(&rightv.snapshot())
    }

    assert_eq!(None, partial_cmp(1.0, std::f32::NAN));
    assert_eq!(Some(Ordering::Less), partial_cmp(1.0, 2.0));
    assert_eq!(Some(Ordering::Equal), partial_cmp(2.0, 2.0));
    assert_eq!(Some(Ordering::Greater), partial_cmp(3.0, 2.0));
}

#[test]
fn trait_ord() {
    use std::cmp::Ordering;

    fn total_cmp(left: i32, right: i32) -> Ordering {
        let leftv: Vector<_> = Vector::new();
        leftv.push(left);

        let rightv: Vector<_> = Vector::new();
        rightv.push(right);

        leftv.snapshot().cmp(&rightv.snapshot())
    }

    assert_eq!(Ordering::Less, total_cmp(1, 2));
    assert_eq!(Ordering::Equal, total_cmp(2, 2));
    assert_eq!(Ordering::Greater, total_cmp(3, 2));
}

#[test]
fn trait_into_iterator() {
    let vec: Vector<_> = Vector::new();
    vec.push(1);

    for &i in vec.snapshot() {
        assert_eq!(1, i);
    }

    for &i in &vec.snapshot() {
        assert_eq!(1, i);
    }
}

}
