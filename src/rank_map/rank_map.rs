use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::ops::{Index, IndexMut};

use crate::binary_heap;

use indexmap::{map::Entry as IndexMapEntry, IndexMap};

/// A hash map that supports key ranking. The rank can be used to get the element with the
/// lowest rank in *O*(1) time, iterate over map's keys and values from the lowest rank
/// to the highest in *O*(N) or remove the element with the lowest rank in *O*(log(N)).
///
/// # Implementation details:
///
/// Rank map is implemented using bi-directional references from the hash-table
/// to the binary-heap and back which helps to get rid of hash-table lookups during
/// binary-heap sift ups and downs:
///
/// ```text
///              MAP                                        HEAP
/// ╔═══╤══════╤═════════════════╗                 ╔═══╤════════════════╗
/// ║idx│ key  │(value, heap-idx)║                 ║idx│(value, map-idx)║
/// ╠═══╪══════╪═════════════════╣                 ╠═══╪════════════════╣
/// ║ 0 │ key0 │   (value0, 0)   ║ ◀━━━━━━━━━━━━━▶ ║ 0 │   (rank0, 0)   ║
/// ╟───┼──────┼─────────────────╢                 ╟───┼────────────────╢
/// ║ 1 │ key1 │   (value1, 3)   ║ ◀━━━━┓  ┏━━━━━▶ ║ 1 │   (rank1, 2)   ║
/// ╟───┼──────┼─────────────────╢      ┃  ┃       ╟───┼────────────────╢
/// ║ 2 │ key2 │   (value2, 1)   ║ ◀━━━━━━━┛  ┏━━▶ ║ 2 │   (rank2, 3)   ║
/// ╟───┼──────┼─────────────────╢      ┃     ┃    ╟───┼────────────────╢
/// ║ 3 │ key3 │   (value3, 2)   ║ ◀━┓  ┗━━━━━━━━▶ ║ 3 │   (rank3, 1)   ║
/// ╟───┼──────┼─────────────────╢   ┃        ┃    ╟───┼────────────────╢
/// ╏               ...          ╏   ┗━━━━━━━━┛    ╏          ...       ╏
/// ╟───┼──────┼─────────────────╢                 ╟───┼────────────────╢
/// ║ N │ keyN │  (valueN, ...)  ║                 ║ N │  (rankN, ...)  ║
/// ╚═══╧══════╧═════════════════╝                 ╚═══╧════════════════╝
/// ```                 
#[derive(Debug)]
pub struct RankMap<K, V, R, S = RandomState> {
    pub(super) map: IndexMap<K, (V, usize), S>,
    pub(super) heap: Vec<(R, usize)>,
}

impl<K, V, R> RankMap<K, V, R> {
    /// Creates an empty `RankMap`.
    pub fn new() -> Self {
        RankMap {
            map: IndexMap::new(),
            heap: Vec::new(),
        }
    }

    /// Creates an empty `RankMap` pre-allocating memory for the specified number of elements.
    pub fn with_capacity(capacity: usize) -> Self {
        RankMap {
            map: IndexMap::with_capacity(capacity),
            heap: Vec::with_capacity(capacity),
        }
    }
}

impl<K, V, R, S> RankMap<K, V, R, S> {
    /// Creates an empty `RankMap` pre-allocating memory for the specified number of elements,
    /// using `hash_builder` to hash the keys.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        RankMap {
            map: IndexMap::with_capacity_and_hasher(capacity, hash_builder),
            heap: Vec::with_capacity(capacity),
        }
    }

    /// Creates an empty `RankMap` which will use the given hash builder to hash keys.
    pub fn with_hasher(hash_builder: S) -> Self {
        RankMap {
            map: IndexMap::with_hasher(hash_builder),
            heap: Vec::new(),
        }
    }

    /// Returns a reference to the map’s `BuildHasher`.
    pub fn hasher(&self) -> &S {
        self.map.hasher()
    }
}

impl<K, V, R, S> RankMap<K, V, R, S> {
    /// Returns the number of elements the map can hold without reallocation.
    pub fn capacity(&self) -> usize {
        std::cmp::min(self.map.capacity(), self.heap.capacity())
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        debug_assert_eq!(self.map.len(), self.heap.len());
        self.map.len()
    }

    /// Returns true if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        debug_assert_eq!(self.map.is_empty(), self.heap.is_empty());
        self.len() == 0
    }
}

impl<K, V, R, S> RankMap<K, V, R, S>
where
    K: Hash + Eq,
    S: BuildHasher,
{
    /// Returns a reference to the value stored by the provided key if it is present,
    /// otherwise returns `None`.
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) on average.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.get(key).and_then(|(value, _)| Some(value))
    }

    /// Returns a mutable reference to the value stored by the provided key if it is present,
    /// otherwise returns `None`.
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) on average.
    pub fn get_mut<Q>(&mut self, k: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.get_mut(k).and_then(|(value, _)| Some(value))
    }

    /// Checks if the item with the provided key exists in the map.
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) on average.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.contains_key(key)
    }

    /// Shrink the capacity of the map as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
        self.heap.shrink_to_fit();

        debug_assert_eq!(self.map.capacity(), self.heap.capacity());
    }

    /// Shrinks the capacity of the map with a lower limit.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.map.shrink_to(min_capacity);
        self.heap.shrink_to(min_capacity);

        debug_assert_eq!(self.map.capacity(), self.heap.capacity());
    }

    /// Clears the map.
    ///
    /// **Note**: that this method has no effect on the map capacity.
    /// ```
    pub fn clear(&mut self) {
        self.heap.clear();
        self.map.clear();
    }
}

impl<K, V, R, S> RankMap<K, V, R, S>
where
    K: Hash + Eq,
    R: PartialOrd + Copy,
    S: BuildHasher,
{
    /// Returns a reference to the value and the rank stored by the provided key if it is present,
    /// otherwise returns `None`.
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) on average.
    pub fn get_with_rank<Q>(&self, key: &Q) -> Option<(&V, R)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.get(key).and_then(|(value_ref, heap_idx_ref)| {
            let rank = self.heap[*heap_idx_ref].0;
            Some((value_ref, rank))
        })
    }

    /// Inserts the item in the map and returns `None` or replaces the item
    /// with the same key returning it.
    ///
    /// # Time complexity
    ///
    /// Takes *O*(log(N)) on average.
    pub fn insert(&mut self, key: K, value: V, rank: R) -> Option<(V, R)> {
        let prev = match self.map.entry(key) {
            IndexMapEntry::Occupied(mut entry) => {
                let (prev_value_ref, heap_idx_ref) = entry.get_mut();
                let heap_idx = *heap_idx_ref;

                let (prev_rank_ref, map_idx_ref) = self
                    .heap
                    .get_mut(heap_idx)
                    .expect("map index must point to a heap element");
                let map_idx = *map_idx_ref;

                let prev_value = std::mem::replace(prev_value_ref, value);
                let prev_rank = std::mem::replace(prev_rank_ref, rank);
                debug_assert_eq!(map_idx, entry.index());

                let map = &mut self.map;
                let end_idx = self.heap.len();
                if rank > prev_rank {
                    binary_heap::sift_up(&mut self.heap, heap_idx, end_idx, |heap_idx, (_, map_idx_ref)| {
                        map.index_mut(*map_idx_ref).1 = heap_idx;
                    });
                } else {
                    binary_heap::sift_down(&mut self.heap, heap_idx, |heap_idx, (_, map_idx_ref)| {
                        map.index_mut(*map_idx_ref).1 = heap_idx;
                    });
                }

                Some((prev_value, prev_rank))
            }
            IndexMapEntry::Vacant(entry) => {
                let heap_idx = self.heap.len();
                let map_idx = entry.index();

                entry.insert((value, heap_idx));
                self.heap.push((rank, map_idx));

                let map = &mut self.map;
                binary_heap::sift_down(&mut self.heap, heap_idx, |heap_idx, (_, map_idx_ref)| {
                    map.index_mut(*map_idx_ref).1 = heap_idx;
                });

                None
            }
        };

        debug_assert_eq!(self.heap.len(), self.map.len());
        return prev;
    }

    /// Removes the item from the map by the key and returns it, or `None` if it is not found.
    ///
    /// # Time complexity
    ///
    /// Takes *O*(log(N)) on average.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<(V, R)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some((_, heap_idx_ref)) = self.map.get(key) {
            let heap_idx = *heap_idx_ref;
            let (_, value, rank) = self.remove_element(heap_idx);
            Some((value, rank))
        } else {
            None
        }
    }

    /// Removes the smallest item from the map and returns it, or `None` if it is empty.
    ///
    /// # Time complexity
    ///
    /// Takes *O*(log(N)) on average.
    pub fn pop(&mut self) -> Option<(K, V, R)> {
        if !self.heap.is_empty() {
            Some(self.remove_element(0))
        } else {
            None
        }
    }

    /// Returns the smallest item in the map, or `None` if it is empty.
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1).
    pub fn top(&self) -> Option<(&K, &V, R)> {
        if let Some((rank_ref, map_idx_ref)) = self.heap.get(0) {
            let (key_ref, (value_ref, heap_idx_ref)) = self
                .map
                .get_index(*map_idx_ref)
                .expect("heap index must point to a map element");
            debug_assert_eq!(*heap_idx_ref, 0);

            Some((key_ref, value_ref, *rank_ref))
        } else {
            None
        }
    }
}

impl<K, V, R, S> RankMap<K, V, R, S>
where
    K: Hash + Eq,
    R: PartialOrd + Copy,
    S: BuildHasher,
{
    fn remove_element(&mut self, heap_idx: usize) -> (K, V, R) {
        debug_assert!(heap_idx < self.heap.len());

        self.swap_heap_elements(heap_idx, self.heap.len() - 1);

        let map_idx = self.heap.last().unwrap().1;
        self.swap_map_elements(map_idx, self.map.len() - 1);

        let rank = self.heap.pop().unwrap().0;
        let (key, (value, map_heap_idx)) = self.map.pop().unwrap();
        debug_assert_eq!(map_heap_idx, self.heap.len());

        let map = &mut self.map;
        let end_idx = self.heap.len();
        if heap_idx < self.heap.len() {
            binary_heap::sift_down(&mut self.heap, heap_idx, |heap_idx, (_, map_idx_ref)| {
                map.index_mut(*map_idx_ref).1 = heap_idx;
            });
            binary_heap::sift_up(&mut self.heap, heap_idx, end_idx, |heap_idx, (_, map_idx_ref)| {
                map.index_mut(*map_idx_ref).1 = heap_idx;
            });
        }

        self.try_shrink_map();

        debug_assert_eq!(self.heap.len(), self.map.len());

        return (key, value, rank);
    }

    fn swap_heap_elements(&mut self, heap_idx1: usize, heap_idx2: usize) {
        debug_assert!(heap_idx1 < self.heap.len());
        debug_assert!(heap_idx2 < self.heap.len());

        let map_idx1 = self.heap[heap_idx1].1;
        let map_idx2 = self.heap[heap_idx2].1;

        self.heap.swap(heap_idx1, heap_idx2);
        self.map.index_mut(map_idx1).1 = heap_idx2;
        self.map.index_mut(map_idx2).1 = heap_idx1;
    }

    fn swap_map_elements(&mut self, map_idx1: usize, map_idx2: usize) {
        debug_assert!(map_idx1 < self.map.len());
        debug_assert!(map_idx2 < self.map.len());

        let heap_idx1 = self.map.get_index(map_idx1).unwrap().1 .1;
        let heap_idx2 = self.map.get_index(map_idx2).unwrap().1 .1;

        self.map.swap_indices(map_idx1, map_idx2);
        self.heap[heap_idx1].1 = map_idx2;
        self.heap[heap_idx2].1 = map_idx1;
    }

    fn try_shrink_map(&mut self) -> bool {
        if self.map.len() < self.map.capacity() / 2 {
            self.map.shrink_to(self.map.len() / 3 * 4);
            true
        } else {
            false
        }
    }
}

impl<Q, K, V, R> Index<&Q> for RankMap<K, V, R>
where
    K: Hash + Eq + Borrow<Q>,
    Q: Hash + Eq + ?Sized,
{
    type Output = V;

    fn index(&self, index: &Q) -> &Self::Output {
        &self.map[index].0
    }
}

impl<Q, K, V, R> IndexMut<&Q> for RankMap<K, V, R>
where
    K: Hash + Eq + Borrow<Q>,
    Q: Hash + Eq + ?Sized,
{
    fn index_mut(&mut self, index: &Q) -> &mut Self::Output {
        &mut self.map[index].0
    }
}

impl<K, V, R> Extend<(K, V, R)> for RankMap<K, V, R>
where
    K: Hash + Eq,
    R: PartialOrd + Copy,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = (K, V, R)>,
    {
        let iter = iterable.into_iter();
        let additional_size = iter.size_hint().0;

        self.heap.reserve(additional_size);
        self.map.reserve(additional_size);

        for (key, value, rank) in iter {
            self.insert(key, value, rank);
        }
    }
}

impl<K, V, R> Default for RankMap<K, V, R> {
    fn default() -> Self {
        RankMap {
            map: IndexMap::default(),
            heap: Vec::default(),
        }
    }
}

impl<K, V, R, S> Clone for RankMap<K, V, R, S>
where
    K: Clone,
    V: Clone,
    S: Clone,
    R: Clone,
{
    fn clone(&self) -> Self {
        RankMap {
            map: self.map.clone(),
            heap: self.heap.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::RankMap;

    #[test]
    fn test_insert() {
        let mut rhm: RankMap<char, &str, i32> = RankMap::new();
        let items = [('c', "C", 3), ('a', "A", 1), ('b', "B", 2), ('d', "D", 4)];

        for (key, value, rank) in items.iter() {
            rhm.insert(*key, value, *rank);
        }

        assert_eq!(rhm.len(), items.len());

        for (key, _, _) in items.iter() {
            assert!(rhm.contains_key(key));
        }
    }

    #[test]
    fn test_insert_duplicate() {
        let mut rhm: RankMap<char, &str, i32> = RankMap::new();

        assert_eq!(rhm.insert('c', "C", 3), None);
        assert_eq!(rhm.insert('a', "A", 1), None);
        assert_eq!(rhm.insert('b', "B", 2), None);
        assert_eq!(rhm.len(), 3);

        assert_eq!(rhm.insert('a', "AA", -1), Some(("A", 1)));
        assert_eq!(rhm.insert('b', "BB", -2), Some(("B", 2)));
        assert_eq!(rhm.len(), 3);
    }

    #[test]
    fn test_contains_key() {
        let mut rhm: RankMap<String, (), i32> = RankMap::new();

        rhm.insert(String::from("a"), (), 1);

        assert_eq!(rhm.contains_key("a"), true);
        assert_eq!(rhm.contains_key(&String::from("a")), true);
        assert_eq!(rhm.contains_key("b"), false);
    }

    #[test]
    fn test_get_methods() {
        let mut rhm: RankMap<&str, &str, i32> = RankMap::new();

        rhm.insert("a", "A", 1);
        assert_eq!(rhm.get("a"), Some(&"A"));
        assert_eq!(rhm.get_with_rank("a"), Some((&"A", 1)));

        *rhm.get_mut("a").unwrap() = "AA";
        assert_eq!(rhm.get("a"), Some(&"AA"));
    }

    #[test]
    fn test_index() {
        let mut rhm: RankMap<&str, &str, i32> = RankMap::new();

        rhm.insert("a", "A", 1);
        assert_eq!(rhm["a"], "A");

        rhm["a"] = "AA";
        assert_eq!(rhm["a"], "AA");
    }

    #[test]
    fn test_top() {
        let mut rhm = RankMap::new();

        rhm.insert('c', "C", 3);
        assert_eq!(rhm.top(), Some((&'c', &"C", 3)));

        rhm.insert('a', "A", 1);
        assert_eq!(rhm.top(), Some((&'a', &"A", 1)));

        rhm.insert('b', "B", 2);
        assert_eq!(rhm.top(), Some((&'a', &"A", 1)));

        assert_eq!(rhm.pop(), Some(('a', "A", 1)));
        assert_eq!(rhm.top(), Some((&'b', &"B", 2)));

        assert_eq!(rhm.pop(), Some(('b', "B", 2)));
        assert_eq!(rhm.top(), Some((&'c', &"C", 3)));

        assert_eq!(rhm.pop(), Some(('c', "C", 3)));
        assert_eq!(rhm.top(), None);

        assert_eq!(rhm.pop(), None);
    }

    #[test]
    fn test_insert_pop() {
        let mut rhm = RankMap::new();

        let ranks = [0, 2, 1, 4, 3, 5, 6, 7, 8, 12, 11, 10, 9];
        let mut items: Vec<_> = ranks
            .iter()
            .map(|rank| (rank.to_string(), rank.to_string(), *rank))
            .collect();
        for (key, value, rank) in items.iter() {
            rhm.insert(key.clone(), value.clone(), *rank);
        }

        let mut actual_result = Vec::new();
        while let Some(item) = rhm.pop() {
            actual_result.push(item);
        }

        items.sort_by_key(|item| item.2);
        assert_eq!(actual_result, items);
        assert_eq!(rhm.pop(), None);
        assert!(rhm.is_empty());
    }

    #[test]
    fn test_remove() {
        let mut rhm = RankMap::new();

        rhm.insert("a", "A", 1);
        assert_eq!(rhm.remove("a"), Some(("A", 1)));
        assert_eq!(rhm.len(), 0);

        rhm.insert("a", "A", 1);
        rhm.insert("b", "B", 2);
        rhm.insert("c", "C", 3);
        rhm.insert("d", "D", 4);

        assert_eq!(rhm.remove("b"), Some(("B", 2)));
        assert_eq!(rhm.pop(), Some(("a", "A", 1)));
        assert_eq!(rhm.pop(), Some(("c", "C", 3)));

        assert_eq!(rhm.remove("d"), Some(("D", 4)));
        assert!(rhm.is_empty());
    }

    #[test]
    fn test_clear() {
        let mut rhm = RankMap::new();

        assert_eq!(rhm.insert('a', "A", 1), None);
        assert_eq!(rhm.insert('b', "B", 2), None);
        assert_eq!(rhm.insert('c', "C", 3), None);

        rhm.clear();
        assert!(rhm.is_empty());
    }

    #[test]
    fn test_capacity() {
        let mut rhm = RankMap::new();
        assert_eq!(rhm.capacity(), 0);

        let items_cnt = 16;
        for item in 0..items_cnt {
            rhm.insert(item, item, item);
        }
        assert_eq!(rhm.len(), items_cnt);
        assert_eq!(rhm.capacity(), 16);

        for _ in 0..items_cnt / 2 + 1 {
            rhm.pop();
        }
        assert_eq!(rhm.len(), items_cnt / 2 - 1);
        assert_eq!(rhm.capacity(), 8);

        for _ in 0..items_cnt / 2 - 1 {
            rhm.pop();
        }
        assert_eq!(rhm.len(), 0);
        assert_eq!(rhm.capacity(), 1);
    }

    #[test]
    fn test_shrink_capacity() {
        let mut rhm = RankMap::new();
        assert_eq!(rhm.capacity(), 0);

        let items_cnt = 15;
        for item in 0..items_cnt {
            rhm.insert(item, item, item);
        }
        assert_eq!(rhm.capacity(), 16);

        rhm.shrink_to_fit();
        assert_eq!(rhm.capacity(), 15);

        for _ in 0..items_cnt / 2 {
            rhm.pop();
        }
        rhm.shrink_to(9);
        assert_eq!(rhm.capacity(), 9);
    }

    #[test]
    fn test_default() {
        let rhm: RankMap<i32, i32, i32> = RankMap::default();
        assert!(rhm.is_empty());
    }

    #[test]
    fn test_extend() {
        let mut rhm = RankMap::new();

        let items = [
            ('c', "C", 3),
            ('a', "A", 1),
            ('d', "D", 9),
            ('b', "B", 2),
            ('c', "C", 3),
            ('d', "D", 4),
        ];

        rhm.extend(items);

        let mut actual_result = Vec::new();
        while let Some(item) = rhm.pop() {
            actual_result.push(item);
        }

        let expected_result = vec![('a', "A", 1), ('b', "B", 2), ('c', "C", 3), ('d', "D", 4)];

        assert_eq!(actual_result, expected_result);
    }
}
