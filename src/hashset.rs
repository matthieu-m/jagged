//! #   The HashSet.
//!
//! The `HashSet` is the concurrent equivalent of the standard `HashSet`,
//! albeit it only supports concurrently inserting from a single writer thread.
//!
//! ##  Under the covers.
//!
//! Under the covers the `HashSet` is a fixed-size array of buckets: dynamically
//! sized arrays of exponential capacity.
//!
//! The main consequences are:
//!
//! -   Once constructed, the maximum capacity is fixed and cannot be
//!     increased.
//! -   The storage is not quite contiguous, and is instead constituted of
//!     a small number of contiguous sections.
//!
//! When constructing a new `HashSet`, pay attention to the capacity!
//!
//! #   Example: basic
//!
//! General usage of `HashSet` involve inserting key-value pairs, either using
//! `insert`, to insert one pair at a time, or `extend`, to insert multiple
//! pairs at once.
//!
//! The faillible equivalent exist too: `try_push` and `try_extend` will return
//! a `Result` indicating whether the operation succeeded, and the cause of its
//! failure if it did not.
//!
//! ```
//! use jagged::hashset::HashSet;
//!
//! let set: HashSet<_> = HashSet::new();
//! set.insert(1);
//! set.insert(2);
//!
//! assert_eq!(2, set.len());
//! assert_eq!(Some(&1), set.get(&1));
//!
//! set.extend([3, 4, 5].iter().copied());
//!
//! assert_eq!(5, set.len());
//! assert_eq!(Some(&4), set.get(&4));
//!
//! for e in set.snapshot() {
//!     println!("{}", e);
//! }
//! ```
//!
//! #   Example: accessing elements
//!
//! `HashSet` provides a single way to access elements: the `get` method.
//!
//! ```
//! use jagged::hashset::HashSet;
//!
//! let mut set: HashSet<_> = HashSet::new();
//! set.extend([1, 2, 3, 4, 5].iter().copied());
//!
//! assert_eq!(Some(&1), set.get(&1));
//! assert_eq!(None, set.get(&6));
//! ```
//!
//! #   Example: managing capacity
//!
//! `HashSet` provides multiple ways to manage the capacity available:
//!
//! -   The constructors `with_max_capacity` and `with_max_capacity_and_hooks`
//!     allow specifying the capacity of the first bucket, with each subsequent
//!     doubling the overall capacity of the `HashSet`.
//! -   The `reserve` and `try_reserve` calls allow pre-allocating buckets in
//!     advance.
//! -   The `shrink` calls allows de-allocating excess capacity.
//!
//! ```
//! use jagged::failure::Failure;
//! use jagged::hashset::HashSet;
//!
//! //  The capacity requested is rounded-up to the closest power of 2.
//! let set: HashSet<_> = HashSet::with_max_capacity(3);
//!
//! //  No capacity is reserved from the constructor, but `max_capacity` is now
//! //  set in stone.
//! assert_eq!(1024 * 1024, set.max_capacity());
//! assert_eq!(0, set.capacity());
//!
//! //  Attempting to reserve more than `max_capacity` is not possible, but
//! //  allocation proceeded as far as possible.
//! assert_eq!(Err(Failure::OutOfBuckets), set.try_reserve(usize::MAX));
//! assert_eq!(set.max_capacity(), set.capacity());
//!
//! set.extend([1, 2, 3, 4, 5].iter().copied());
//!
//! //  Shrinking sheds excess capacity.
//! set.shrink();
//! assert_eq!(8, set.capacity());
//! ```
//!
//! #   Example: sharing is caring
//!
//! The core property of `HashSet` is its ability to be written to from thread,
//! while being read from another, with a minimum amount of synchronization.
//!
//! The `HashSet` itself is not `Sync`, so cannot be shared across threads,
//! however it is possible to create:
//!
//! -   A `HashSetReader`, a read-only view of the `HashSet` which reflects
//!     updates made to the `HashSet` on the writer thread at the small
//!     synchronization cost of one atomic read per access.
//! -   A `HashSetSnapshot`, a read-only view of the `HashSet` which does not
//!     reflect updates made to the `HashSet` on the writer thread, and as a
//!     result is synchronization-free.
//!
//! Since a `HashSetSnapshot` can be created from a `HashSetReader` at the cost of
//! a single atomic read, the most flexible usage is to send a `HashSetReader` to
//! another thread and create instances of `HashSetSnapshot` every so often.
//!
//! ```
//! use jagged::hashset::HashSet;
//!
//! let set: HashSet<_> = HashSet::new();
//! set.extend([1, 2, 3].iter().copied());
//!
//! let reader = set.reader();
//! let snapshot = set.snapshot();  // could be reader.snapshot()
//!
//! set.insert(4);
//!
//! assert_eq!(4, reader.len());
//! assert_eq!(3, snapshot.len());
//! ```

pub mod iterator;

mod entry;
mod hashset;
mod reader;
mod snapshot;

pub use super::hashcore::HashHooks;
pub use self::hashset::HashSet;
pub use self::reader::HashSetReader;
pub use self::snapshot::HashSetSnapshot;

#[cfg(feature = "with-std")]
pub use super::hashcore::DefaultHashHooks;

use super::atomic;
use super::failure;
use super::hashcore;
use super::root;
