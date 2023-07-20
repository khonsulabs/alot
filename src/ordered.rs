use alloc::vec::Vec;
use alloc::{slice, vec};
use core::cmp::Ordering;
use core::fmt::Debug;
use core::ops::{Index, IndexMut};

use crate::unordered::{DrainAll, DrainFilter, Lots};
use crate::LotId;

/// A collection of `T` values that maintains the order of elements.
///
/// This collection can be accessed by index (`usize`) or the [`LotId`] it is
/// assigned upon insertion or pushing.
///
/// This collection has Vec-like performance except when removing elements by
/// [`LotId`], which is an O(n) operation.
#[derive(Clone)]
#[allow(clippy::module_name_repetitions)]
pub struct OrderedLots<T> {
    slots: Lots<T>,
    order: Vec<LotId>,
}

impl<T> Default for OrderedLots<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> OrderedLots<T> {
    /// Returns a new, empty collection.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: Lots::new(),
            order: Vec::new(),
        }
    }

    /// Returns an empty collection that can hold `initial_capacity` values
    /// without reallocation.
    #[inline]
    #[must_use]
    pub fn with_capacity(initial_capacity: usize) -> Self {
        Self {
            slots: Lots::with_capacity(initial_capacity),
            order: Vec::with_capacity(initial_capacity),
        }
    }

    /// Adds `value` to the end of the collection, returning the value's unique
    /// [`LotId`].
    #[inline]
    pub fn push(&mut self, value: T) -> LotId {
        let slot_id = self.slots.push(value);
        self.order.push(slot_id);
        slot_id
    }

    /// Removes the last element of the collection, if one is present.
    #[inline]
    #[must_use]
    pub fn pop(&mut self) -> Option<T> {
        self.pop_entry().map(|(_, v)| v)
    }

    /// Removes the last element of the collection, if one is present.
    #[inline]
    #[must_use]
    pub fn pop_entry(&mut self) -> Option<(LotId, T)> {
        self.order
            .pop()
            .and_then(|id| self.slots.remove(id).map(|v| (id, v)))
    }

    /// Inserts `value` at `offset` inside of the collection.
    ///
    /// # Panics
    ///
    /// This funciton panics if offset is greater than the length of the
    /// collection.
    #[inline]
    pub fn insert(&mut self, offset: usize, value: T) -> LotId {
        // Before modifying the map, check the only logic condition that will
        // panic.
        assert!(offset <= self.order.len());
        let slot_id = self.slots.push(value);
        self.order.insert(offset, slot_id);
        slot_id
    }

    /// Removes the value with the associated [`LotId`], if found.
    ///
    /// Note: It is possible, but unlikely, for a [`LotId`] that has been
    /// removed to be reused.
    #[inline]
    pub fn remove(&mut self, lot: LotId) -> Option<T> {
        let value = self.slots.remove(lot)?;
        if let Some((index, _)) = self.order.iter().enumerate().find(|(_, id)| **id == lot) {
            self.order.remove(index);
        }
        Some(value)
    }

    /// Removes the value at `index`, returning the [`LotId`] and value if
    /// found.
    #[inline]
    #[allow(clippy::must_use_candidate)]
    pub fn remove_by_index(&mut self, index: usize) -> Option<(LotId, T)> {
        let id = *self.order.get(index)?;

        self.remove(id).map(|value| (id, value))
    }

    /// Orders the elements in this collection leveraging the standard library's
    /// sorting implementation. See [`slice::sort()`] for more information.
    #[inline]
    pub fn sort(&mut self)
    where
        T: Ord,
    {
        self.order.sort_by_key(|id| &self.slots[*id]);
    }

    /// Orders the elements in this collection leveraging the standard library's
    /// sorting implementation. See [`slice::sort_by()`] for more information.
    #[inline]
    pub fn sort_by<F: Fn(&T, &T) -> Ordering>(&mut self, comparison: F) {
        self.order
            .sort_by(|a, b| comparison(&self.slots[*a], &self.slots[*b]));
    }

    /// Orders the elements in this collection leveraging the standard library's
    /// sorting implementation. See [`slice::sort_by_key()`] for more information.
    #[inline]
    pub fn sort_by_key<K, F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.order.sort_by_key(|id| f(&self.slots[*id]));
    }

    /// Orders the elements in this collection leveraging the standard library's
    /// sorting implementation. See [`slice::sort_by_cached_key()`] for more information.
    #[inline]
    pub fn sort_by_cached_key<K, F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.order.sort_by_cached_key(|id| f(&self.slots[*id]));
    }

    /// Orders the elements in this collection leveraging the standard library's
    /// sorting implementation. See [`slice::sort_unstable()`] for more information.
    #[inline]
    pub fn sort_unstable(&mut self)
    where
        T: Ord,
    {
        self.order.sort_unstable_by_key(|id| &self.slots[*id]);
    }

    /// Orders the elements in this collection leveraging the standard library's
    /// sorting implementation. See [`slice::sort_unstable_by()`] for more
    /// information.
    #[inline]
    pub fn sort_unstable_by<F: Fn(&T, &T) -> Ordering>(&mut self, comparison: F) {
        self.order
            .sort_unstable_by(|a, b| comparison(&self.slots[*a], &self.slots[*b]));
    }

    /// Orders the elements in this collection leveraging the standard library's
    /// sorting implementation. See [`slice::sort_unstable_by_key()`] for more
    /// information.
    #[inline]
    pub fn sort_unstable_by_key<K, F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.order.sort_unstable_by_key(|id| f(&self.slots[*id]));
    }

    /// Looks up a previously stored value by its [`LotId`]. If the value hasn't
    /// been removed, a reference will be returned.
    ///
    /// Note: It is possible, but unlikely, for a [`LotId`] that has been
    /// removed to be reused.
    #[inline]
    #[must_use]
    pub fn get(&self, id: LotId) -> Option<&T> {
        self.slots.get(id)
    }

    /// Looks up a previously stored value by its [`LotId`]. If the value hasn't
    /// been removed, a mutable reference will be returned.
    ///
    /// Note: It is possible, but unlikely, for a [`LotId`] that has been
    /// removed to be reused.
    #[inline]
    #[must_use]
    pub fn get_mut(&mut self, id: LotId) -> Option<&mut T> {
        self.slots.get_mut(id)
    }

    /// Looks up a value by index. If `index` is greater than or equal to the
    /// collections length, `None` will be returned.
    #[inline]
    #[must_use]
    pub fn get_by_index(&self, index: usize) -> Option<&T> {
        self.order
            .get(index)
            .and_then(|index| self.slots.get(*index))
    }

    /// Looks up a mutable reference to a value by index. If `index` is greater
    /// than or equal to the collections length, `None` will be returned.
    #[inline]
    #[must_use]
    pub fn get_mut_by_index(&mut self, index: usize) -> Option<&mut T> {
        self.order
            .get(index)
            .and_then(|index| self.slots.get_mut(*index))
    }

    /// Returns the index of `id`, or None if the id is not contained in this
    /// collection.
    #[inline]
    #[must_use]
    pub fn index_of_id(&self, id: LotId) -> Option<usize> {
        self.order
            .iter()
            .enumerate()
            .find_map(|(index, &stored)| (stored == id).then_some(index))
    }

    /// Returns the id of the entry at `index`, or None if `index` is outside of
    /// the bounds of this collection.
    #[must_use]
    pub fn id(&self, index: usize) -> Option<LotId> {
        self.order.get(index).copied()
    }

    /// Returns the [`LotId`] associated with a given index. Returns `None` if
    /// `index` is greater than or equal to the collections length.
    #[inline]
    #[must_use]
    pub fn key(&self, index: usize) -> Option<LotId> {
        self.order.get(index).copied()
    }

    /// Returns an iterator that returns all the contained values in this
    /// collection as they're removed from the collection.
    ///
    /// Dropping the iterator will still result in the elements being removed.
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, T, DrainAll> {
        Drain {
            map: self,
            index: 0,
            filter: DrainAll,
        }
    }

    /// Returns an iterator that invokes `filter` for each item in the
    /// collection. If `filter` returns true for that value, it will be removed
    /// and returned from the iterator. When false is returned, the value is
    /// kept in the collection.
    ///
    /// Dropping the iterator will still result in the filtered elements being
    /// removed.
    #[inline]
    pub fn drain_filter<Filter>(&mut self, filter: Filter) -> Drain<'_, T, Filter>
    where
        Filter: FnMut(&mut T) -> bool,
    {
        Drain {
            map: self,
            index: 0,
            filter,
        }
    }

    /// Returns the number of values contained in this collection.
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.order.len()
    }

    /// Returns true if this collection has no values.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.order.is_empty()
    }

    /// Returns an iterator of references to all contained values.
    #[inline]
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        self.into_iter()
    }

    /// Returns an `Iterator<Item = (LotId, &T)>` for all contained values.
    #[inline]
    #[must_use]
    pub fn entries(&self) -> EntryIter<'_, T> {
        EntryIter {
            order: self.order.iter(),
            map: &self.slots,
        }
    }

    /// Returns the first entry in this collection, or None if the collection is
    /// empty.
    #[must_use]
    pub fn first(&self) -> Option<&T> {
        self.get_by_index(0)
    }

    /// Returns a mutable reference to the first entry in this collection, or
    /// None if the collection is empty.
    #[must_use]
    pub fn first_mut(&mut self) -> Option<&mut T> {
        self.get_mut_by_index(0)
    }

    /// Returns the last entry in this collection, or None if the collection is
    /// empty.
    #[must_use]
    pub fn last(&self) -> Option<&T> {
        self.order.last().map(|&index| &self.slots[index])
    }

    /// Returns a mutable reference to the last entry in this collection, or
    /// None if the collection is empty.
    #[must_use]
    pub fn last_mut(&mut self) -> Option<&mut T> {
        self.order.last().map(|&index| &mut self.slots[index])
    }

    /// Swaps the elements at index `a` and `b`.
    ///
    /// Internally, this only moves a `LotId`. The underlying data does not
    /// change, and its each value's associated `LotId` does not change.
    pub fn swap(&mut self, a: usize, b: usize) {
        self.order.swap(a, b);
    }
}

impl<T> Index<LotId> for OrderedLots<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: LotId) -> &Self::Output {
        self.get(index).expect("invalid lot id")
    }
}

impl<T> IndexMut<LotId> for OrderedLots<T> {
    #[inline]
    fn index_mut(&mut self, index: LotId) -> &mut Self::Output {
        self.get_mut(index).expect("invalid lot id")
    }
}

impl<T> Index<usize> for OrderedLots<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.get_by_index(index).expect("invalid index")
    }
}

impl<T> IndexMut<usize> for OrderedLots<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_mut_by_index(index).expect("invalid index")
    }
}
impl<T> FromIterator<T> for OrderedLots<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let size_hint = iter.size_hint().0;
        let mut map = Self::with_capacity(size_hint);
        for item in iter {
            map.push(item);
        }
        map
    }
}

/// An iterator over all values contained in an [`OrderedLots<T>`].
#[derive(Clone)]
pub struct Iter<'a, T> {
    order: slice::Iter<'a, LotId>,
    map: &'a Lots<T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let id = self.order.next()?;
        Some(&self.map[*id])
    }
}

/// An iterator over an [`OrderedLots<T>`] that returns each contained value and
/// its associated [`LotId`].
#[derive(Clone)]
pub struct EntryIter<'a, T> {
    order: slice::Iter<'a, LotId>,
    map: &'a Lots<T>,
}

impl<'a, T> Iterator for EntryIter<'a, T> {
    type Item = (LotId, &'a T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let id = self.order.next()?;
        Some((*id, &self.map[*id]))
    }
}

/// An iterator over values being remoed from a [`OrderedLots<T>`].
pub struct Drain<'a, T, Filter>
where
    Filter: DrainFilter<T>,
{
    map: &'a mut OrderedLots<T>,
    index: usize,
    filter: Filter,
}

impl<'a, T, Filter> Iterator for Drain<'a, T, Filter>
where
    Filter: DrainFilter<T>,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let id = *self.map.order.get(self.index)?;
            let lot = self.map.slots.get_mut(id)?;
            if self.filter.filter(lot) {
                self.map.order.remove(self.index);
                return self.map.slots.remove(id);
            }

            self.index += 1;
        }
    }
}

impl<'a, T, Filter> Drop for Drain<'a, T, Filter>
where
    Filter: DrainFilter<T>,
{
    #[inline]
    fn drop(&mut self) {
        // Exhaust the iterator on drop to ensure we fully execute the drain.
        for _ in self {}
    }
}

impl<'a, T> IntoIterator for &'a OrderedLots<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            order: self.order.iter(),
            map: &self.slots,
        }
    }
}

/// An iterator that removes all values from the collection and frees the
/// underlying collection.
pub struct IntoIter<T> {
    order: vec::IntoIter<LotId>,
    slots: Lots<T>,
}

impl<T> IntoIterator for OrderedLots<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            order: self.order.into_iter(),
            slots: self.slots,
        }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let id = self.order.next()?;
        self.slots.remove(id)
    }
}

impl<T> Eq for OrderedLots<T> where T: Eq {}

impl<T> PartialEq for OrderedLots<T>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a.eq(b))
    }
}

impl<T> PartialEq<[T]> for OrderedLots<T>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &[T]) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a.eq(b))
    }
}

impl<'a, T> PartialEq<&'a [T]> for OrderedLots<T>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &&'a [T]) -> bool {
        self == *other
    }
}

impl<T, const N: usize> PartialEq<[T; N]> for OrderedLots<T>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &[T; N]) -> bool {
        self.eq(&other[0..N])
    }
}

impl<'a, T, const N: usize> PartialEq<&'a [T; N]> for OrderedLots<T>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &&'a [T; N]) -> bool {
        self.eq(*other)
    }
}

impl<T> Debug for OrderedLots<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut map = f.debug_map();

        for (key, value) in self.entries() {
            map.entry(&key, value);
        }

        map.finish()
    }
}

#[test]
fn ordered_tests() {
    fn test_sorting_callback(cb: impl FnOnce(&mut OrderedLots<i32>)) {
        let mut ordered = OrderedLots::new();
        let three = ordered.push(3);
        let one = ordered.push(1);
        let two = ordered.push(2);
        cb(&mut ordered);
        assert_eq!(ordered[one], 1);
        assert_eq!(ordered[two], 2);
        assert_eq!(ordered[three], 3);
        ordered.remove(one);
        assert_eq!(ordered[0], 2);
        assert_eq!(ordered[1], 3);
        ordered.insert(0, 1);
        assert_eq!(ordered[0], 1);
        assert_eq!(ordered[1], 2);
        assert_eq!(ordered[2], 3);
    }

    test_sorting_callback(OrderedLots::sort);
    test_sorting_callback(OrderedLots::sort_unstable);
    test_sorting_callback(|ordered| ordered.sort_by(Ord::cmp));
    test_sorting_callback(|ordered| ordered.sort_unstable_by(Ord::cmp));
    test_sorting_callback(|ordered| ordered.sort_by_key(|a| *a));
    test_sorting_callback(|ordered| ordered.sort_by_cached_key(|a| *a));
    test_sorting_callback(|ordered| ordered.sort_unstable_by_key(|a| *a));
}

#[test]
fn basics() {
    let mut map = OrderedLots::new();
    let first = map.push(1);
    assert_eq!(map.len(), 1);
    assert_eq!(map[first], 1);
    assert_eq!(map.key(0), Some(first));
    map[first] = 2;
    assert_eq!(map[first], 2);
    map[0] = 3;
    // PartialEq for array
    assert_eq!(map, &[3]);
    // PartialEq for slice
    assert_eq!(map, &[3][..]);
    let drain = map.drain().collect::<Vec<_>>();
    assert_eq!(drain, &[3]);
    assert!(map.is_empty());

    assert!(map.get(first).is_none());
    assert!(map.get_mut(first).is_none());
    assert!(map.remove(first).is_none());
    let second = map.push(1);
    assert_eq!(map.remove(second), Some(1));

    map.push(2);
    assert_eq!(map.pop(), Some(2));
    let fourth = map.push(3);
    assert_eq!(map.pop_entry(), Some((fourth, 3)));
}

#[test]
fn iteration() {
    let mut map = OrderedLots::default();
    map.push(1);
    let two = map.push(2);
    map.push(3);
    map.push(4);

    // Create a gap for the iterator.
    map.remove(two);

    let values = map.iter().copied().collect::<Vec<_>>();
    assert_eq!(values, &[1, 3, 4]);
    let values = map.into_iter().collect::<Vec<_>>();
    assert_eq!(values, &[1, 3, 4]);
}

#[test]
fn drain_filter() {
    let mut map = OrderedLots::default();
    map.push(1_i32);
    map.push(2);
    map.push(3);
    map.push(4);
    let odd = map.drain_filter(|v| *v % 2 == 1).collect::<Vec<_>>();
    assert_eq!(odd, &[1, 3]);
    assert_eq!(map.into_iter().collect::<Vec<_>>(), &[2, 4]);
}

#[test]
fn dbg() {
    let mut map = OrderedLots::from_iter([1, 2, 3]);
    let _: Option<i32> = map.pop();
    assert_eq!(alloc::format!("{map:?}"), "{LotId(0g1): 1, LotId(1g1): 2}");
}

#[test]
fn clone_and_eq() {
    let map = OrderedLots::from_iter([2, 1]);
    let mut map2 = map.clone();
    assert_eq!(map, map2);
    map2.sort();
    assert_ne!(map, map2);
}

#[test]
fn index_ops() {
    let mut map = OrderedLots::new();
    let one = map.push(1);
    let two = map.push(2);
    assert_eq!(map.id(0), Some(one));
    assert_eq!(map.index_of_id(two), Some(1));

    assert_eq!(map.first(), Some(&1));
    assert_eq!(map.last(), Some(&2));
    assert_eq!(map.first_mut(), Some(&mut 1));
    assert_eq!(map.last_mut(), Some(&mut 2));

    map.swap(0, 1);

    assert_eq!(map.remove_by_index(0), Some((two, 2)));
    assert_eq!(map.index_of_id(one), Some(0));
    assert_eq!(map.index_of_id(two), None);
}
