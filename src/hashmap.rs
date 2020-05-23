//! #   The HashMap.
//!
//! The `HashMap` is the concurrent equivalent of the standard `HashMap`,
//! albeit it only supports concurrently inserting from a single writer thread.
//!
//! ##  Under the covers.
//!
//! Under the covers the `HashMap` is a fixed-size array of buckets: dynamically
//! sized arrays of exponential capacity.
//!
//! The main consequences are:
//!
//! -   Once constructed, the maximum capacity is fixed and cannot be
//!     increased.
//! -   The storage is not quite contiguous, and is instead constituted of
//!     a small number of contiguous sections.
//!
//! When constructing a new `HashMap`, pay attention to the capacity!
//!
//! #   Example: basic
//!
//! General usage of `HashMap` involve inserting key-value pairs, either using
//! `insert`, to insert one pair at a time, or `extend`, to insert multiple
//! pairs at once.
//!
//! The faillible equivalent exist too: `try_push` and `try_extend` will return
//! a `Result` indicating whether the operation succeeded, and the cause of its
//! failure if it did not.
//!
//! ```
//! use jagged::hashmap::HashMap;
//!
//! let map: HashMap<_, _> = HashMap::new();
//! map.insert(1, false);
//! map.insert(2, true);
//!
//! assert_eq!(2, map.len());
//! assert_eq!(Some(&false), map.get(&1));
//!
//! map.extend([(3, false), (4, true), (5, false)].iter().copied());
//!
//! assert_eq!(5, map.len());
//! assert_eq!(Some(&true), map.get(&4));
//!
//! for (&k, &v) in map.snapshot() {
//!     println!("{} => {}", k, v);
//! }
//! ```
//!
//! #   Example: accessing elements
//!
//! `HashMap` provides multiple ways to access elements:
//!
//! -   The `get` and `get_mut` methods allow accessing the value.
//! -   The `get_key_value` method allows accessing both key and value.
//!
//! ```
//! use jagged::hashmap::HashMap;
//!
//! let mut map: HashMap<_, _> = HashMap::new();
//! map.extend([(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)].iter().copied());
//!
//! assert_eq!(Some(&2), map.get(&1));
//! assert_eq!(Some(2), map.get_mut(&1).copied());
//!
//! if let Some(v) = map.get_mut(&2) {
//!     *v = 33;
//! }
//! assert_eq!(Some(&33), map.get(&2));
//!
//! assert_eq!(None, map.get(&6));
//! assert_eq!(None, map.get_mut(&6));
//!
//! assert_eq!(Some((&3, &4)), map.get_key_value(&3));
//! ```
//!
//! #   Example: managing capacity
//!
//! `HashMap` provides multiple ways to manage the capacity available:
//!
//! -   The constructors `with_max_capacity` and `with_max_capacity_and_hooks`
//!     allow specifying the capacity of the first bucket, with each subsequent
//!     doubling the overall capacity of the `HashMap`.
//! -   The `reserve` and `try_reserve` calls allow pre-allocating buckets in
//!     advance.
//! -   The `shrink` calls allows de-allocating excess capacity.
//!
//! ```
//! use jagged::failure::Failure;
//! use jagged::hashmap::HashMap;
//!
//! //  The capacity requested is rounded-up to the closest power of 2.
//! let map: HashMap<_,_> = HashMap::with_max_capacity(3);
//!
//! //  No capacity is reserved from the constructor, but `max_capacity` is now
//! //  set in stone.
//! assert_eq!(1024 * 1024, map.max_capacity());
//! assert_eq!(0, map.capacity());
//!
//! //  Attempting to reserve more than `max_capacity` is not possible, but
//! //  allocation proceeded as far as possible.
//! assert_eq!(Err(Failure::OutOfBuckets), map.try_reserve(usize::MAX));
//! assert_eq!(map.max_capacity(), map.capacity());
//!
//! map.extend([(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)].iter().copied());
//!
//! //  Shrinking sheds excess capacity.
//! map.shrink();
//! assert_eq!(8, map.capacity());
//! ```
//!
//! #   Example: sharing is caring
//!
//! The core property of `HashMap` is its ability to be written to from thread,
//! while being read from another, with a minimum amount of synchronization.
//!
//! The `HashMap` itself is not `Sync`, so cannot be shared across threads,
//! however it is possible to create:
//!
//! -   A `HashMapReader`, a read-only view of the `HashMap` which reflects
//!     updates made to the `HashMap` on the writer thread at the small
//!     synchronization cost of one atomic read per access.
//! -   A `HashMapSnapshot`, a read-only view of the `HashMap` which does not
//!     reflect updates made to the `HashMap` on the writer thread, and as a
//!     result is synchronization-free.
//!
//! Since a `HashMapSnapshot` can be created from a `HashMapReader` at the cost of
//! a single atomic read, the most flexible usage is to send a `HashMapReader` to
//! another thread and create instances of `HashMapSnapshot` every so often.
//!
//! ```
//! use jagged::hashmap::HashMap;
//!
//! let map: HashMap<_, _> = HashMap::new();
//! map.extend([(1, false), (2, true), (3, false)].iter().copied());
//!
//! let reader = map.reader();
//! let snapshot = map.snapshot();  // could be reader.snapshot()
//!
//! map.insert(4, true);
//!
//! assert_eq!(4, reader.len());
//! assert_eq!(3, snapshot.len());
//! ```

pub mod iterator;

mod entry;
mod hashmap;
mod reader;
mod snapshot;

pub use super::hashcore::HashHooks;
pub use self::hashmap::HashMap;
pub use self::reader::HashMapReader;
pub use self::snapshot::HashMapSnapshot;

#[cfg(feature = "with-std")]
pub use super::hashcore::DefaultHashHooks;

use super::atomic;
use super::failure;
use super::hashcore;
use super::root;
