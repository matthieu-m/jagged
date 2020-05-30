#   Jagged

Jagged is a collection of wait-free concurrent data-structures.

The data-structures in this collection exploit the same central idea, the
jagged array, and as a result exhibit the same guarantees, and limitations.

##  Goals/Non-Goals

What Jagged intends to offer:

-   A convenient & safe API.
-   No synchronization between readers.
-   Minimum synchronization overhead between reader and writer.
-   Maximum portability -- including minimum dependencies.

What Jagged does NOT intend to offer:

-   A hotbed of experimental features. No nightly here, and thus no const
    generics.

##  Safety.

**Unproven.**

Subjective:

-   Confident in correctness of memory ordering.
-   Less confident in proper use of `unsafe`, and there's a LOT of it.

Objective:

-   Not fuzzed.
-   Not audited.
-   Not proven.

Use at your own risks, reviews are welcome.

##  The data-structures.

This crate contains 3 sets of data-structures:

-   `Vector<T>`, and its accompanying `Reader` and `Snapshot`.
-   `HashMap<K, V>`, and its accompanying `Reader` and `Snapshot`.
-   `HashSet<T>`, and its accompanying `Reader` and `Snapshot`.

Each set follows the same pattern:

-   The main data-structure allows concurrent writes.
-   The `Reader` allows concurrent reads, and reflects updates.
-   The `Snapshot` allows concurrent reads, but does not reflect updates.

##  Properties of Jagged data-structures.

All Jagged data-structures share the same core properties -- guarantees and
limitations:

-   _Wait-free_: insertion and reads are wait-free, and it possible to take a
    snapshot of the data-structure in O(1) to eschew part of or all of the
    synchronization based on the data-structure.
-   _Contention-free reads_: readers only contend with the writer, and not with
    any other reader.
-   _Single writer_: only the main data-structure allows concurrent insertions,
    and it cannot be accessed from multiple threads concurrently.
-   _Multiple readers_: multiple references and snapshots can be created from
    the main data-structure, and allow wait-free concurrent read access.

Those properties are supported by _memory stability_. Once inserted into a
Jagged data-structure, an element will never move. This allows keeping
references to the element while simultaneously inserting more elements.

##  Portability

The Jagged library intends to be maximally portable, whilst still being
convenient to use.

In order to so, two compilation modes are supported:

-   By default, the Jagged library depends on `std`.
-   By NOT specifying the `with-std` feature, the Jagged library only depends
    on `core`.

*Note: ideally, it would also optionally depend on `alloc`, unfortunately this
crate is still nightly-only.*

The Jagged library has no non-dev dependencies, and intends to remain
lightweight.

##  Jagged Array.

Memory stability is a key concept for efficient sharing. While wrapping an
element in an `Arc` allows sharing it effortlessly, it incurs a cost: an atomic
increment and decrement each time the `Arc` is cloned and dropped.

While a single increment/decrement is relatively inexpensive, by itself, it does
lead to contention on the cache-lines. Having readers contend between them
is unfortunate, and limits scaling to multiple cores and, especially, multiple
sockets.

The key insights behind the Jagged Array are:

-   _Memory stability_: all the way down, even internals should be stable in
    memory.
-   _Amortized allocations_: arrays are good for your cache.

This is achieved by using two layers of arrays:

-   An outer array of static size. Something like: `[InnerArray<T>; N]`.
-   An inner array of fixed dynamic size. Something like:
    `&[UnsafeCell<MaybeUninit<T>>]`.

And having each new inner array doubling the capacity of the whole structure.
That is, the capacities of the inner arrays follow the pattern
`[1, 1, 2, 4, 8, 16, 32, ...]`.

An `N` of 22 means that the maximum capacity that can be achieved is `2**21`
times the capacity of the first inner array, or about 2 millions.

The exact value of `N` depends on the data-structure, and is an implementation
detail.

##  FAQ

### Where does the name Jagged comes from?

The representation of the memory layout is jagged.
