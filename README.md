# alot

A set of collections for storing values in a map-like structure using generated
unique keys. The base collection type, `Lots<T>`, returns a `LotId` for each
stored value. The stored values can be retrieved or removed using their `LotId`.

This collection provides insert and read performance comparable to `Vec<T>`, but
does not guarantee anything about the order of the contained values.

If ordering is needed, `OrderedLots<T>` is provided which tracks the order of
elements while still allowing lookups by `LotId`. Removing a value by its
`LotId` becomes an O(n) operation with this collection.

## `Lots<T>`: Unordered collection of T

```rust
use alot::Lots;

let mut map = Lots::new();
// Similar to a Vec, push adds a new value to the collection.
let greeting = map.push("hello, world");
// Prints: Greeting: LotId { generation: 1, index: 0 }
println!("Greeting: {greeting:?}");
// Values can be retrieved by their LotId.
assert_eq!(map[greeting], "hello, world");
```

## `OrderedLots<T>`: Ordered collection of T

```rust
use alot::OrderedLots;

let mut map = OrderedLots::new();
// Values stored in OrderedLots can be accessed by index or by their LotId.
let c = map.push("c");
let a = map.push("a");

assert_eq!(map[c], map[0]);

// With OrderedLots, values can be inserted as well as pushed.
let b = map.insert(1, "b");
assert_eq!(map, &["c", "b", "a"]);

// OrderedLots also provides sorting functions.
map.sort();
assert_eq!(map, &["a", "b", "c"]);
```

## What separates this crate from others?

There are several approaches to "slot maps" or "generational arenas" or other
similarly named structures. This crate takes two approaches that make it unique:

- No unsafe code.
- `LotId` is a single `usize`. Most slot maps use `usize` for indicies, and an
  additional `usize` for the generation.
- Internally, the storage for each value only has an additional 2 bytes of
  overhead, excluding padding the compiler may add. Most generational maps must
  store a `usize` for the generation, and many incur an additional byte of
  overhead due to using `Option<T>`.
- The free list is a `Vec<usize>`, rather than attempting to reuse the empty
  slot's space. This was chosen for these advantages:
  - Without unsafe, it's impossible to fit 48 bits of index data in the Empty
    state without causing the `SlotData` enum to take up more space than it
    currently does when `size_of::<T>()` is less than the size of a `usize`. For
    example, the internal slot storage for `Lots<u16>` uses 4 bytes per value.
  - Unless the collection is drained or undergoes large numbers of removals, the
    free list is usually short.

These design choices cause these limitations on this implementation:

- Collections are limited to 75% of the maximum `usize`. In general, this isn't
  a real limitation as allocating a contiguous region of memory that spans 75%
  of the target architecture's RAM isn't practical. On a 64-bit platform,
  `Lots<T>` can hold 2^48 items -- 281 trillion items.
- Compared to implementations that utilize a full `usize` for generations, this
  implementation will be more likely to return data for a stale ID due to the
  generation rotating.
- Collections that grow large and then shrink very small again in most
  situations will utilize more RAM than alternate solutions that use a
  linked-list approach to keeping track of free slots.
