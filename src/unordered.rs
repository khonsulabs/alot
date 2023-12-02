use alloc::vec::{self, Vec};
use core::fmt::Debug;
use core::ops::{Index, IndexMut};
use core::{mem, slice};

use crate::{Assert, Generation, LotId};

/// A collection of `T`, organized by generational [`LotId`]s.
///
/// This data type allows storing data of any type and receiving a [`LotId`]
/// that can later be used to look up the data.
///
/// This data type cannot hold more than 2^48 items, due how [`LotId`]s are
/// allocated.
///
/// ## Generation Checks
///
/// A [`LotId`] contains 16 bits representing a lot's generation. Each time a
/// lot is updated, the lot's generation is incremented (with wrapping).
///
/// The lot's generation is checked when retrieving data using a [`LotId`]. If a
/// generation mismatch is found, the data will not be returned.
///
/// While the chances of generation collision may be low, this is not a perfect
/// check. Care should still be taken to ensure stale [`LotId`]s aren't used
/// when other ways of validating the data don't exist.
#[derive(Clone)]
pub struct Lots<T> {
    slots: Vec<SlotData<T>>,
    free_indicies: Vec<usize>,
}

impl<T> Eq for Lots<T> where T: Eq {}

impl<T> PartialEq for Lots<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.slots == other.slots
    }
}

impl<T> Default for Lots<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Debug for Lots<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut map = f.debug_map();
        for (id, value) in self.entries() {
            map.entry(&id, &value);
        }
        map.finish()
    }
}

impl<T> Lots<T> {
    /// Returns a new, empty collection.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: Vec::new(),
            free_indicies: Vec::new(),
        }
    }

    /// Returns an empty collection that can hold `initial_capacity` values
    /// without reallocation.
    #[inline]
    #[must_use]
    pub fn with_capacity(initial_capacity: usize) -> Self {
        Self {
            slots: Vec::with_capacity(initial_capacity),
            free_indicies: Vec::new(),
        }
    }

    /// Adds `value` to the collection, returning the value's unique [`LotId`].
    #[inline]
    #[allow(clippy::must_use_candidate)]
    pub fn push(&mut self, value: T) -> LotId {
        if let Some((index, SlotData::Empty { generation })) = self
            .free_indicies
            .pop()
            .and_then(|index| self.slots.get(index).map(|lot| (index, lot)))
        {
            let generation = generation.next();
            self.slots[index] = SlotData::Populated {
                generation,
                contents: value,
            };
            LotId::new(generation, index).assert("invalid lot id")
        } else {
            let index = self.slots.len();
            let generation = Generation::first();
            self.slots.push(SlotData::Populated {
                generation,
                contents: value,
            });

            LotId::new(generation, index).assert("invalid lot id")
        }
    }

    /// Removes all values from the collection.
    #[inline]
    pub fn clear(&mut self) {
        self.drain();
    }

    /// Looks up a previously stored value by its [`LotId`]. If the value hasn't
    /// been removed, a reference will be returned.
    ///
    /// Note: It is possible, but unlikely, for a [`LotId`] that has been
    /// removed to be reused.
    #[inline]
    #[must_use]
    pub fn get(&self, id: LotId) -> Option<&T> {
        match self.slots.get(id.index()) {
            Some(SlotData::Populated {
                generation,
                contents,
            }) if *generation == id.generation() => Some(contents),
            _ => None,
        }
    }

    /// Looks up a previously stored value by its [`LotId`]. If the value hasn't
    /// been removed, a mutable reference will be returned.
    ///
    /// Note: It is possible, but unlikely, for a [`LotId`] that has been
    /// removed to be reused.
    #[inline]
    #[must_use]
    pub fn get_mut(&mut self, id: LotId) -> Option<&mut T> {
        match self.slots.get_mut(id.index()) {
            Some(SlotData::Populated {
                generation,
                contents,
            }) if *generation == id.generation() => Some(contents),
            _ => None,
        }
    }

    /// Removes a previously stored value by its [`LotId`]. If the value is
    /// present, it will be removed and returned.
    ///
    /// Note: It is possible, but unlikely, for a [`LotId`] that has been
    /// removed to be reused.
    #[inline]
    pub fn remove(&mut self, id: LotId) -> Option<T> {
        match self.slots.get_mut(id.index()) {
            Some(lot) if lot.generation() == id.generation() => {
                if let SlotData::Populated { .. } = lot {
                    let generation = lot.generation();
                    let SlotData::Populated { contents, .. } =
                        mem::replace(lot, SlotData::Empty { generation })
                    else {
                        unreachable!()
                    };
                    self.free_indicies.push(id.index());
                    return Some(contents);
                }
            }
            _ => {}
        }

        None
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
        self.slots.len() - self.free_indicies.len()
    }

    /// Returns true if this collection has no values.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.slots.len() == self.free_indicies.len()
    }

    /// Returns an iterator of references to all contained values.
    #[inline]
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        self.into_iter()
    }

    /// Returns an iterator of exclusive references to all contained values.
    #[inline]
    #[must_use]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        self.into_iter()
    }

    /// Returns an `Iterator<Item = (LotId, &T)>` for all contained values.
    #[inline]
    #[must_use]
    pub fn entries(&self) -> EntryIter<'_, T> {
        EntryIter(self.slots.iter().enumerate())
    }
}

impl<T> Index<LotId> for Lots<T> {
    type Output = T;

    #[inline]
    fn index(&self, id: LotId) -> &Self::Output {
        self.get(id).expect("id is not valid")
    }
}

impl<T> IndexMut<LotId> for Lots<T> {
    #[inline]
    fn index_mut(&mut self, id: LotId) -> &mut Self::Output {
        self.get_mut(id).expect("id is not valid")
    }
}

impl<T> FromIterator<T> for Lots<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut map = Self::with_capacity(iter.size_hint().0);
        for item in iter {
            map.push(item);
        }
        map
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum SlotData<T> {
    Empty { generation: Generation },
    Populated { generation: Generation, contents: T },
}

impl<T> SlotData<T> {
    #[inline]
    pub const fn generation(&self) -> Generation {
        match self {
            SlotData::Empty { generation } | SlotData::Populated { generation, .. } => *generation,
        }
    }
}

/// An iterator over all values contained in a [`Lots<T>`].
#[derive(Clone)]
pub struct Iter<'a, T>(slice::Iter<'a, SlotData<T>>);

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next()? {
                SlotData::Empty { .. } => {}
                SlotData::Populated { contents, .. } => return Some(contents),
            }
        }
    }
}

/// An iterator providing exclusive access to all values contained in a
/// [`Lots<T>`].
pub struct IterMut<'a, T>(slice::IterMut<'a, SlotData<T>>);

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next()? {
                SlotData::Empty { .. } => {}
                SlotData::Populated { contents, .. } => return Some(contents),
            }
        }
    }
}

/// An iterator over a [`Lots<T>`] that returns each contained value and its
/// associated [`LotId`].
#[derive(Clone)]
pub struct EntryIter<'a, T>(core::iter::Enumerate<slice::Iter<'a, SlotData<T>>>);

impl<'a, T> Iterator for EntryIter<'a, T> {
    type Item = (LotId, &'a T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next()? {
                (_, SlotData::Empty { .. }) => {}
                (
                    index,
                    SlotData::Populated {
                        generation,
                        contents,
                    },
                ) => {
                    return Some((
                        LotId::new(*generation, index).expect("stored lots have valid ids"),
                        contents,
                    ))
                }
            }
        }
    }
}

/// An iterator over values being remoed from a [`Lots<T>`].
pub struct Drain<'a, T, Filter>
where
    Filter: DrainFilter<T>,
{
    map: &'a mut Lots<T>,
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
            let lot = self.map.slots.get_mut(self.index)?;
            if let SlotData::Populated {
                generation,
                contents,
            } = lot
            {
                if self.filter.filter(contents) {
                    let generation = *generation;
                    let SlotData::Populated { contents, .. } =
                        mem::replace(lot, SlotData::Empty { generation })
                    else {
                        unreachable!("just matched")
                    };
                    self.map.free_indicies.push(self.index);
                    return Some(contents);
                }
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

/// A filter for a [`Drain`] iterator.
pub trait DrainFilter<T> {
    /// Return true if the value should be removed from the collection and
    /// returned from the [`Drain`] iterator.
    fn filter(&mut self, value: &mut T) -> bool;
}

impl<T, F> DrainFilter<T> for F
where
    F: FnMut(&mut T) -> bool,
{
    #[inline]
    fn filter(&mut self, value: &mut T) -> bool {
        self(value)
    }
}

/// A [`DrainFilter`] that drains all elements from a collection.
pub struct DrainAll;

impl<T> DrainFilter<T> for DrainAll {
    #[inline]
    fn filter(&mut self, _value: &mut T) -> bool {
        true
    }
}

impl<'a, T> IntoIterator for &'a Lots<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter(self.slots.iter())
    }
}

impl<'a, T> IntoIterator for &'a mut Lots<T> {
    type IntoIter = IterMut<'a, T>;
    type Item = &'a mut T;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IterMut(self.slots.iter_mut())
    }
}

/// An iterator that removes all values from the collection and frees the
/// underlying collection.
pub struct IntoIter<T>(vec::IntoIter<SlotData<T>>);

impl<T> IntoIterator for Lots<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.slots.into_iter())
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next()? {
                SlotData::Populated { contents, .. } => return Some(contents),
                SlotData::Empty { .. } => {}
            }
        }
    }
}

#[test]
fn slot_data_size() {
    assert_eq!(mem::size_of::<SlotData<u16>>(), 4);
}

#[test]
fn basics() {
    let mut map = Lots::new();
    let first = map.push(1);
    assert_eq!(map[first], 1);
    assert_eq!(map.len(), 1);
    map[first] = 2;
    assert_eq!(map[first], 2);
    let drain = map.drain().collect::<Vec<_>>();
    assert_eq!(drain, &[2]);
    assert!(map.is_empty());

    assert!(map.get(first).is_none());
    assert!(map.get_mut(first).is_none());
    assert!(map.remove(first).is_none());
    let second = map.push(1);
    assert_eq!(map.remove(second), Some(1));
}

#[test]
fn slot_reuse() {
    let mut map = Lots::default();
    let first = map.push(1);
    assert_eq!(first.generation().get(), 1);
    assert_eq!(first.index(), 0);
    assert_eq!(map.get(first), Some(&1));
    assert_eq!(map.remove(first), Some(1));
    assert_eq!(map.get(first), None);

    let second = map.push(2);
    assert_eq!(second.index(), 0);
    assert_eq!(second.generation().get(), 2);
    assert_eq!(map.get(second), Some(&2));
    map.clear();

    let third = map.push(3);
    assert_eq!(third.index(), 0);
    assert_eq!(third.generation().get(), 3);
    assert_eq!(map.get(third), Some(&3));
}

#[test]
#[allow(clippy::explicit_iter_loop)] // this was chosen for code coverage
fn iteration() {
    let mut map = Lots::default();
    map.push(1);
    let two = map.push(2);
    map.push(3);
    map.push(4);

    // Create a gap for the iterator.
    map.remove(two);

    let values = map.iter().copied().collect::<Vec<_>>();
    assert_eq!(values, &[1, 3, 4]);
    for value in map.iter_mut() {
        *value += 1;
    }
    let values = map.into_iter().collect::<Vec<_>>();
    assert_eq!(values, &[2, 4, 5]);
}

#[test]
fn drain_filter() {
    let mut map = Lots::default();
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
    let mut map = Lots::from_iter([1, 2, 3]);
    map.remove(map.entries().last().unwrap().0);
    assert_eq!(alloc::format!("{map:?}"), "{LotId(0g1): 1, LotId(1g1): 2}");
}

#[test]
fn clone_and_eq() {
    let map = Lots::from_iter([1, 2]);
    let mut map2 = map.clone();
    assert_eq!(map, map2);
    map2.push(3);
    assert_ne!(map, map2);
}

#[test]
fn out_of_bounds_id() {
    let mut map = Lots::new();
    let bad_key = map.push(1);
    assert!(Lots::<i32>::new().remove(bad_key).is_none());
}
