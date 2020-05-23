//! #   The Vector.
//!
//! The `Vector` is the concurrent equivalent of `Vec`, albeit it only supports
//! concurrently appending from a single writer thread.
//!
//! ##  Under the covers.
//!
//! Under the covers the `Vector` is a fixed-size array of buckets: dynamically
//! sized arrays of exponential capacity.
//!
//! The main consequences are:
//!
//! -   Once constructed, the maximum capacity is fixed and cannot be
//!     increased.
//! -   The storage is not quite contiguous, and is instead constituted of
//!     a small number of contiguous sections.
//!
//! When constructing a new `Vector`, pay attention to the capacity!
//!
//! #   Example: basic
//!
//! General usage of `Vector` involve pushing elements, either using `push`, to
//! push one element at a time, or `extend`, to push multiple elements at once.
//!
//! The faillible equivalent exist too: `try_push` and `try_extend` will return
//! a `Result` indicating whether the operation succeeded, and the cause of its
//! failure if it did not.
//!
//! ```
//! use jagged::vector::Vector;
//!
//! let vec: Vector<_> = Vector::new();
//! vec.push(1);
//! vec.push(2);
//!
//! assert_eq!(2, vec.len());
//! assert_eq!(1, vec[0]);
//!
//! vec.extend([3, 4, 5].iter().copied());
//!
//! assert_eq!(5, vec.len());
//! assert_eq!(4, vec[3]);
//!
//! for x in vec.snapshot() {
//!     println!("{}", x);
//! }
//! ```
//!
//! #   Example: accessing elements
//!
//! `Vector` provides multiple ways to access elements:
//!
//! -   The `get` and `get_mut` methods allow faillible scalar access.
//! -   The `unsafe` `get_unchecked` and `get_unchecked_mut` methods allow
//!     infaillible and unchecked scalar access.
//! -   The `Index` and `IndexMut` traits are implemented to provide infaillible
//!     checked scalar access.
//! -   The `bucket` and `bucket_mut` methods allow faillible vector access.
//!
//! ```
//! use jagged::vector::Vector;
//!
//! let mut vec: Vector<_> = Vector::new();
//! vec.extend([1, 2, 3, 4, 5].iter().copied());
//!
//! assert_eq!(Some(1), vec.get(0).copied());
//! assert_eq!(Some(2), vec.get_mut(1).copied());
//!
//! assert_eq!(None, vec.get(5));
//! assert_eq!(None, vec.get_mut(5));
//!
//! assert_eq!(1, unsafe { *vec.get_unchecked(0) });
//! assert_eq!(2, unsafe { *vec.get_unchecked_mut(1) });
//!
//! assert_eq!(3, vec[2]);
//! vec[2] = 9;
//! assert_eq!(9, vec[2]);
//!
//! assert_eq!(&[1], vec.bucket(0));
//!
//! let slice = vec.bucket_mut(2);
//! slice[0] = 3;
//! assert_eq!(&[3, 4], vec.bucket(2));
//! ```
//!
//! #   Example: managing capacity
//!
//! `Vector` provides multiple ways to manage the capacity available:
//!
//! -   The constructors `with_max_capacity` and `with_max_capacity_and_hooks`
//!     allow specifying the capacity of the first bucket, with each subsequent
//!     doubling the overall capacity of the `Vector`.
//! -   The `reserve` and `try_reserve` calls allow pre-allocating buckets in
//!     advance.
//! -   The `shrink` calls allows de-allocating excess capacity.
//!
//! ```
//! use jagged::failure::Failure;
//! use jagged::vector::Vector;
//!
//! //  The capacity requested is rounded-up to the closest power of 2.
//! let vec: Vector<_> = Vector::with_max_capacity(3);
//!
//! //  No capacity is reserved from the constructor, but `max_capacity` is now
//! //  set in stone.
//! assert_eq!(8 * 1024 * 1024, vec.max_capacity());
//! assert_eq!(0, vec.capacity());
//!
//! //  Attempting to reserve more than `max_capacity` is not possible, but
//! //  allocation proceeded as far as possible.
//! assert_eq!(Err(Failure::OutOfBuckets), vec.try_reserve(usize::MAX));
//! assert_eq!(vec.max_capacity(), vec.capacity());
//!
//! vec.extend([1, 2, 3, 4, 5].iter().copied());
//!
//! //  Shrinking sheds excess capacity.
//! vec.shrink();
//! assert_eq!(8, vec.capacity());
//! ```
//!
//! #   Example: sharing is caring
//!
//! The core property of `Vector` is its ability to be written to from thread,
//! while being read from another, with a minimum amount of synchronization.
//!
//! The `Vector` itself is not `Sync`, so cannot be shared across threads,
//! however it is possible to create:
//!
//! -   A `VectorReader`, a read-only view of the `Vector` which reflects
//!     updates made to the `Vector` on the writer thread at the small
//!     synchronization cost of one atomic read per access.
//! -   A `VectorSnapshot`, a read-only view of the `Vector` which does not
//!     reflect updates made to the `Vector` on the writer thread, and as a
//!     result is synchronization-free.
//!
//! Since a `VectorSnapshot` can be created from a `VectorReader` at the cost of
//! a single atomic read, the most flexible usage is to send a `VectorReader` to
//! another thread and create instances of `VectorSnapshot` every so often.
//!
//! ```
//! use jagged::vector::Vector;
//!
//! let vec: Vector<_> = Vector::new();
//! vec.extend([1, 2, 3].iter().copied());
//!
//! let reader = vec.reader();
//! let snapshot = vec.snapshot();  // could be reader.snapshot()
//!
//! vec.push(4);
//!
//! assert_eq!(4, reader.len());
//! assert_eq!(3, snapshot.len());
//! ```

mod buckets;
mod buckets_api;
mod capacity;
mod hooks;
mod reader;
mod snapshot;
mod vector;

pub use self::hooks::VectorHooks;
pub use self::reader::VectorReader;
pub use self::snapshot::VectorSnapshot;
pub use self::vector::Vector;

#[cfg(feature = "with-std")]
pub use self::hooks::DefaultVectorHooks;

use super::allocator;
use super::atomic;
use super::failure;
use super::raw;
use super::root;
