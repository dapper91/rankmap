//! `RankMap` iterators.

use std::hash::{BuildHasher, Hash};

use super::rank_map::RankMap;
use crate::binary_heap;

/// An iterator over the keys of a `RankMap`.
pub struct Keys<'m, K, V, R, S> {
    rank_map: &'m RankMap<K, V, R, S>,
    index_iter: std::vec::IntoIter<(R, usize)>,
}

impl<'m, K, V, R, S> Keys<'m, K, V, R, S>
where
    R: PartialOrd + Copy,
{
    fn new(rank_map: &'m RankMap<K, V, R, S>) -> Keys<'m, K, V, R, S> {
        let index_iter = binary_heap::into_sorted_vec(&rank_map.heap).into_iter();
        Keys { rank_map, index_iter }
    }
}

impl<'m, K, V, R, S> Iterator for Keys<'m, K, V, R, S> {
    type Item = &'m K;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((_, idx)) = self.index_iter.next() {
            let (key_ref, _) = self.rank_map.map.get_index(idx).unwrap();
            Some(key_ref)
        } else {
            None
        }
    }
}

/// An owning iterator over the keys of a `RankMap`.
pub struct IntoKeys<K> {
    keys_iter: std::vec::IntoIter<K>,
}

impl<K> IntoKeys<K>
where
    K: Hash + Eq,
{
    fn new<V, R, S>(mut rank_map: RankMap<K, V, R, S>) -> Self
    where
        R: PartialOrd + Copy,
        S: BuildHasher,
    {
        let mut keys = Vec::with_capacity(rank_map.len());
        while let Some((key, _, _)) = rank_map.pop() {
            keys.push(key);
        }

        return IntoKeys {
            keys_iter: keys.into_iter(),
        };
    }
}

impl<K> Iterator for IntoKeys<K> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.keys_iter.next()
    }
}

/// An iterator over the values of a `RankMap`.
pub struct Values<'m, K, V, R, S> {
    rank_map: &'m RankMap<K, V, R, S>,
    index_iter: std::vec::IntoIter<(R, usize)>,
}

impl<'m, K, V, R, S> Values<'m, K, V, R, S>
where
    R: PartialOrd + Copy,
{
    fn new(rank_map: &'m RankMap<K, V, R, S>) -> Values<'m, K, V, R, S> {
        let index_iter = binary_heap::into_sorted_vec(&rank_map.heap).into_iter();
        Values { rank_map, index_iter }
    }
}

impl<'m, K, V, R, S> Iterator for Values<'m, K, V, R, S> {
    type Item = &'m V;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((_, idx)) = self.index_iter.next() {
            let (_, (value_ref, _)) = self.rank_map.map.get_index(idx).unwrap();
            Some(value_ref)
        } else {
            None
        }
    }
}

/// A mutable iterator over the values of a `RankMap`.
pub struct ValuesMut<'m, K, V, R, S> {
    rank_map: &'m mut RankMap<K, V, R, S>,
    index_iter: std::vec::IntoIter<(R, usize)>,
}

impl<'m, K, V, R, S> ValuesMut<'m, K, V, R, S>
where
    R: PartialOrd + Copy,
{
    fn new(rank_map: &'m mut RankMap<K, V, R, S>) -> ValuesMut<'m, K, V, R, S> {
        let index_iter = binary_heap::into_sorted_vec(&rank_map.heap).into_iter();
        ValuesMut { rank_map, index_iter }
    }
}

impl<'m, K, V, R, S> Iterator for ValuesMut<'m, K, V, R, S>
where
    R: PartialOrd + Copy,
{
    type Item = &'m mut V;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((_, idx)) = self.index_iter.next() {
            let (_, (value_ref, _)) = self.rank_map.map.get_index_mut(idx).unwrap();
            // Ties the lifetime of value to the map.
            let value_ref: &'m mut V = unsafe { std::mem::transmute(value_ref) };
            Some(value_ref)
        } else {
            None
        }
    }
}

/// An owning iterator over the values of a `RankMap`.
pub struct IntoValues<V> {
    values_iter: std::vec::IntoIter<V>,
}

impl<V> IntoValues<V> {
    fn new<K, R, S>(mut rank_map: RankMap<K, V, R, S>) -> Self
    where
        K: Hash + Eq,
        R: PartialOrd + Copy,
        S: BuildHasher,
    {
        let mut values = Vec::with_capacity(rank_map.len());
        while let Some((_, value, _)) = rank_map.pop() {
            values.push(value);
        }

        return IntoValues {
            values_iter: values.into_iter(),
        };
    }
}

impl<V> Iterator for IntoValues<V> {
    type Item = V;

    fn next(&mut self) -> Option<Self::Item> {
        self.values_iter.next()
    }
}

/// An iterator over the entries of a `RankMap`.
pub struct Iter<'m, K, V, R, S> {
    index_iter: std::vec::IntoIter<(R, usize)>,
    rank_map: &'m RankMap<K, V, R, S>,
}

impl<'m, K, V, R, S> Iter<'m, K, V, R, S>
where
    R: PartialOrd + Copy,
{
    fn new(rank_map: &'m RankMap<K, V, R, S>) -> Self {
        let index_iter = binary_heap::into_sorted_vec(&rank_map.heap).into_iter();
        Iter { index_iter, rank_map }
    }
}

impl<'m, K, V, R, S> Iterator for Iter<'m, K, V, R, S> {
    type Item = (&'m K, &'m V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((_, idx)) = self.index_iter.next() {
            let (key_ref, (value_ref, _)) = self.rank_map.map.get_index(idx).unwrap();
            Some((key_ref, value_ref))
        } else {
            None
        }
    }
}

/// A mutable iterator over the entries of a `RankMap`.
pub struct IterMut<'m, K, V, R, S> {
    rank_map: &'m mut RankMap<K, V, R, S>,
    index_iter: std::vec::IntoIter<(R, usize)>,
}

impl<'m, K, V, R, S> IterMut<'m, K, V, R, S>
where
    R: PartialOrd + Copy,
{
    fn new(rank_map: &'m mut RankMap<K, V, R, S>) -> Self {
        let index_iter = binary_heap::into_sorted_vec(&rank_map.heap).into_iter();
        IterMut { rank_map, index_iter }
    }
}

impl<'m, K, V, R, S> Iterator for IterMut<'m, K, V, R, S> {
    type Item = (&'m K, &'m mut V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((_, idx)) = self.index_iter.next() {
            let (key_ref, (value_ref, _)) = self.rank_map.map.get_index_mut(idx).unwrap();
            // Ties the lifetime of key, value to the map.
            let value: (&'m K, &'m mut V) = unsafe { std::mem::transmute((key_ref, value_ref)) };
            Some(value)
        } else {
            None
        }
    }
}

/// An owning iterator over the entries of a `RankMap`.
pub struct IntoIter<K, V> {
    key_value_iter: std::vec::IntoIter<(K, V)>,
}

impl<K, V> IntoIter<K, V> {
    fn new<R, S>(mut rank_map: RankMap<K, V, R, S>) -> Self
    where
        K: Hash + Eq,
        R: PartialOrd + Copy,
        S: BuildHasher,
    {
        let mut keys_values = Vec::with_capacity(rank_map.len());
        while let Some((key, value, _)) = rank_map.pop() {
            keys_values.push((key, value));
        }

        return IntoIter {
            key_value_iter: keys_values.into_iter(),
        };
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.key_value_iter.next()
    }
}

impl<K, V, R, S> RankMap<K, V, R, S>
where
    R: PartialOrd + Copy,
{
    /// Returns an iterator visiting all keys from the lowest rank to the highest.
    pub fn keys(&self) -> Keys<'_, K, V, R, S> {
        Keys::new(&self)
    }

    /// Returns an iterator visiting all values from the lowest rank to the highest.
    pub fn values(&self) -> Values<'_, K, V, R, S> {
        Values::new(&self)
    }

    /// Returns a mutable iterator visiting all values from the lowest rank to the highest.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, R, S> {
        ValuesMut::new(self)
    }

    /// An iterator visiting all key-value pairs from the lowest rank to the highest.
    pub fn iter(&self) -> Iter<'_, K, V, R, S> {
        Iter::new(&self)
    }

    /// Returns a mutable iterator visiting all key-value pairs from the lowest rank to the highest.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V, R, S> {
        IterMut::new(self)
    }
}

impl<K, V, R, S> RankMap<K, V, R, S>
where
    K: Hash + Eq,
    R: PartialOrd + Copy,
    S: BuildHasher,
{
    ///
    pub fn into_keys(self) -> IntoKeys<K> {
        IntoKeys::new(self)
    }

    ///
    pub fn into_values(self) -> IntoValues<V> {
        IntoValues::new(self)
    }
}

impl<'m, K, V, R, S> IntoIterator for &'m RankMap<K, V, R, S>
where
    R: PartialOrd + Copy,
{
    type Item = (&'m K, &'m V);
    type IntoIter = Iter<'m, K, V, R, S>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'m, K, V, R, S> IntoIterator for &'m mut RankMap<K, V, R, S>
where
    R: PartialOrd + Copy,
{
    type Item = (&'m K, &'m mut V);
    type IntoIter = IterMut<'m, K, V, R, S>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K, V, R, S> IntoIterator for RankMap<K, V, R, S>
where
    K: Hash + Eq,
    R: PartialOrd + Copy,
    S: BuildHasher,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

#[cfg(test)]
mod tests {
    use super::RankMap;

    #[test]
    fn test_keys_iterator() {
        let mut rhm = RankMap::new();

        rhm.insert("c", "C", 3);
        rhm.insert("d", "D", 4);
        rhm.insert("b", "B", 2);
        rhm.insert("a", "A", 1);

        let actual_result: Vec<&&str> = rhm.keys().collect();
        let expected_result = vec![&"a", &"b", &"c", &"d"];
        assert_eq!(actual_result, expected_result);
    }

    #[test]
    fn test_values_iterator() {
        let mut rhm = RankMap::new();

        rhm.insert("c", "C", 3);
        rhm.insert("d", "D", 4);
        rhm.insert("b", "B", 2);
        rhm.insert("a", "A", 1);

        let actual_result: Vec<&&str> = rhm.values().collect();
        let expected_result = vec![&"A", &"B", &"C", &"D"];
        assert_eq!(actual_result, expected_result);
    }

    #[test]
    fn test_values_mut_iterator() {
        let mut rhm = RankMap::new();

        rhm.insert("c", String::from("C"), 3);
        rhm.insert("d", String::from("D"), 4);
        rhm.insert("b", String::from("B"), 2);
        rhm.insert("a", String::from("A"), 1);

        for value_ref in rhm.values_mut() {
            *value_ref = value_ref.to_lowercase();
        }

        let actual_result: Vec<String> = rhm.into_values().collect();
        let expected_result = vec![
            String::from("a"),
            String::from("b"),
            String::from("c"),
            String::from("d"),
        ];
        assert_eq!(actual_result, expected_result);
    }

    #[test]
    fn test_iter_iterator() {
        let mut rhm = RankMap::new();

        rhm.insert("c", "C", 3);
        rhm.insert("d", "D", 4);
        rhm.insert("b", "B", 2);
        rhm.insert("a", "A", 1);

        let actual_result: Vec<(&&str, &&str)> = rhm.iter().collect();
        let expected_result = vec![(&"a", &"A"), (&"b", &"B"), (&"c", &"C"), (&"d", &"D")];
        assert_eq!(actual_result, expected_result);
    }

    #[test]
    fn test_iter_mut_iterator() {
        let mut rhm = RankMap::new();

        rhm.insert("c", String::from("C"), 3);
        rhm.insert("d", String::from("D"), 4);
        rhm.insert("b", String::from("B"), 2);
        rhm.insert("a", String::from("A"), 1);

        for (_, value_ref) in rhm.iter_mut() {
            *value_ref = value_ref.to_lowercase();
        }

        let actual_result: Vec<(&str, String)> = rhm.into_iter().collect();
        let expected_result = vec![
            ("a", String::from("a")),
            ("b", String::from("b")),
            ("c", String::from("c")),
            ("d", String::from("d")),
        ];
        assert_eq!(actual_result, expected_result);
    }
}
