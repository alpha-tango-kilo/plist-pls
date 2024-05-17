use std::fmt;

use delegate::delegate;
use derive_more::{Index, IndexMut, IntoIterator};
// derive(IntoIterator) uses this type
pub use indexmap::map::IntoIter;
use indexmap::IndexMap;

use crate::Value;

/// The plist dictionary type
///
/// Retains insertion order
#[derive(Clone, Default, PartialEq, IntoIterator, Index, IndexMut)]
pub struct Dictionary<'a>(
    #[index]
    #[index_mut]
    #[into_iterator(owned, ref, ref_mut)]
    IndexMap<&'a str, Value<'a>>,
);

impl<'a> Dictionary<'a> {
    delegate! {
        // Documentation copied from indexmap
        to self.0 {
            /// Clears the dictionary, removing all values.
            pub fn clear(&mut self);

            /// Return a reference to the value stored for `key`, if it is
            /// present, else `None`
            ///
            /// Computes in **O(1)** time (average)
            pub fn get(&self, key: &str) -> Option<&Value<'a>>;

            /// Return `true` if an equivalent to `key` exists in the map
            ///
            /// Computes in **O(1)** time (average)
            pub fn contains_key(&self, key: &str) -> bool;

            /// Returns a mutable reference to the value stored for `key`, if it is
            /// present, else `None`
            ///
            /// Computes in **O(1)** time (average)
            pub fn get_mut(&mut self, key: &str);

            /// Insert a key-value pair in the map
            ///
            /// If an equivalent key already exists in the map: the key remains
            /// and retains in its place in the order, its corresponding value
            /// is updated with `value`, and the older value is returned inside
            /// `Some(_)`
            ///
            /// If no equivalent key existed in the map: the new key-value pair
            /// is inserted, last in order, and `None` is returned
            ///
            /// Computes in **O(1)** time (amortized average)
            pub fn insert(&mut self, key: &'a str, value: Value<'a>) -> Option<Value<'a>>;

            /// Remove the key-value pair equivalent to `key` and return
            /// its value
            ///
            /// Like [`Vec::remove`], the pair is removed by shifting all of
            /// the elements that follow it, preserving their relative order
            ///
            /// Return `None` if `key` is not in map
            ///
            /// Computes in **O(n)** time (average)
            ///
            /// Note: this behaviour differs from the `plist` crate, which
            /// instead swap-removes - disturbing the order of elements for
            /// sake of increased speed
            #[call(shift_remove)]
            pub fn remove(&mut self, key: &str) -> Option<Value<'a>>;

            /// Scan through each key-value pair in the map and keep those
            /// where the closure `keep` returns `true`
            ///
            /// The elements are visited in order, and remaining elements keep
            /// their order
            ///
            /// Computes in **O(n)** time (average)
            pub fn retain<F>(&mut self, keep: F)
            where
                F: FnMut(&&str, &mut Value<'a>) -> bool;

            /// Sort the map's key-value pairs by the default ordering of the
            /// keys, but may not preserve the order of equal elements
            ///
            /// This function is useful if you are serializing and wish to
            /// ensure a consistent key order
            ///
            /// Note: this behaviour differs from the `plist` crate, which
            /// instead opts for a stable sort. Given there is no API offered
            /// which allows for ordering-equal keys (as far as I'm aware),
            /// then I'm opting into the speed-up in the sorting
            #[call(sort_unstable_keys)]
            pub fn sort_keys(&mut self);

            /// Return the number of key-value pairs in the map
            ///
            /// Computes in **O(1)** time
            pub fn len(&self) -> usize;

            /// Returns true if the map contains no elements
            ///
            /// Computes in **O(1)** time
            pub fn is_empty(&self) -> bool;

            // Where are keys & iter(_mut)? Manually impl'd, as the keys are
            // copied to avoid &&str

            /// Return an iterator over the values of the map, in their order
            pub fn values(&self) -> impl Iterator<Item = &Value<'a>>;

            /// Return an iterator over mutable references to the values of the
            /// map, in their order
            pub fn values_mut(&mut self) -> impl Iterator<Item = &mut Value<'a>>;

            /// Return an owning iterator over the values of the map, in their
            /// order
            pub fn into_values(self) -> impl Iterator<Item = Value<'a>>;
        }
    }

    /// Makes a new empty `Dictionary`
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new map with capacity for `n` key-value pairs. (Does not
    /// allocate if `n` is zero.)
    ///
    /// Computes in **O(n)** time
    #[inline]
    pub fn with_capacity(n: usize) -> Self {
        Dictionary(IndexMap::with_capacity(n))
    }

    /// Return an iterator over the key-value pairs of the map, in their order
    pub fn iter(&self) -> impl Iterator<Item = (&str, &Value<'a>)> {
        self.0.iter().map(|(key, val)| (*key, val))
    }

    /// Return an iterator over the key-value pairs of the map, in their order
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&str, &mut Value<'a>)> {
        self.0.iter_mut().map(|(key, val)| (*key, val))
    }

    /// Return an iterator over the keys of the map, in their order
    pub fn keys(&self) -> impl Iterator<Item = &str> {
        self.0.keys().copied()
    }
}

impl fmt::Debug for Dictionary<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
