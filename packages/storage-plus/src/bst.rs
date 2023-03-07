use std::{any::type_name, marker::PhantomData, str::FromStr};

use serde::{de::DeserializeOwned, Serialize};

use cosmwasm_std::{StdError, StdResult, Storage};
use cosmwasm_storage::to_length_prefixed;
use secret_toolkit::serialization::{Json, Serde};

const LEFT: u8 = 1;
const RIGHT: u8 = 2;

pub struct BinarySearchTree<'a, T, Ser = Json>
where
    T: Serialize + DeserializeOwned + PartialEq + PartialOrd,
    Ser: Serde,
{
    key: &'a [u8],
    prefix: Option<Vec<u8>>,
    item_type: PhantomData<T>,
    serialization_type: PhantomData<Ser>,
}

impl<'a, T, Ser> BinarySearchTree<'a, T, Ser>
where
    T: Serialize + DeserializeOwned + PartialEq + PartialOrd,
    Ser: Serde,
{
    pub const fn new(name: &'a [u8]) -> Self {
        Self {
            key: name,
            prefix: None,
            item_type: PhantomData,
            serialization_type: PhantomData,
        }
    }

    pub fn add_suffix(&self, suffix: &[u8]) -> Self {
        let suffix = to_length_prefixed(suffix);
        let prefix = self.prefix.as_deref().unwrap_or(self.key);
        let prefix = [prefix, suffix.as_slice()].concat();
        Self {
            key: self.key,
            prefix: Some(prefix),
            item_type: self.item_type,
            serialization_type: self.serialization_type,
        }
    }

    fn as_slice(&self) -> &[u8] {
        if let Some(prefix) = &self.prefix {
            prefix
        } else {
            self.key
        }
    }

    /// Returns a copy of self
    fn clone(&self) -> Self {
        Self {
            key: self.key,
            prefix: self.prefix.clone(),
            item_type: self.item_type,
            serialization_type: self.serialization_type,
        }
    }

    /// Returns a BST representation of the left-hand child
    pub fn left(&self) -> Self {
        let suffix = &[LEFT];
        let prefix = if let Some(prefix) = &self.prefix {
            [prefix.clone(), suffix.to_vec()].concat()
        } else {
            [self.key.to_vec(), suffix.to_vec()].concat()
        };
        Self {
            key: self.key,
            prefix: Some(prefix),
            item_type: self.item_type,
            serialization_type: self.serialization_type,
        }
    }

    /// Returns a BST representation of the right-hand child
    pub fn right(&self) -> Self {
        let suffix = &[RIGHT];
        let prefix = if let Some(prefix) = &self.prefix {
            [prefix.clone(), suffix.to_vec()].concat()
        } else {
            [self.key.to_vec(), suffix.to_vec()].concat()
        };
        Self {
            key: self.key,
            prefix: Some(prefix),
            item_type: self.item_type,
            serialization_type: self.serialization_type,
        }
    }

    /// Checks to see if node is empty
    pub fn is_empty(&self, storage: &dyn Storage) -> bool {
        storage.get(self.as_slice()).is_none()
    }

    pub fn may_load(&self, storage: &dyn Storage) -> StdResult<Option<T>> {
        match storage.get(self.as_slice()) {
            Some(value) => Ser::deserialize(&value).map(Some),
            None => Ok(None),
        }
    }

    pub fn load(&self, storage: &dyn Storage) -> StdResult<T> {
        Ser::deserialize(
            &storage
                .get(self.as_slice())
                .ok_or_else(|| StdError::not_found(type_name::<T>()))?,
        )
    }

    pub fn save(&self, storage: &mut dyn Storage, value: &T) -> StdResult<()> {
        storage.set(self.as_slice(), &Ser::serialize(value)?);
        Ok(())
    }

    /// Finds `elem` in the tree, returning a tuple of the storage key and a boolean
    /// value `true` if the value exists at key position or `false` if not
    pub fn find(&self, storage: &dyn Storage, elem: &T) -> StdResult<(Vec<u8>, bool)> {
        let mut node = self.clone();

        loop {
            let current_item = node.may_load(storage)?;
            let current_elem = match current_item {
                Some(i) => i,
                // empty node, insert here
                None => break,
            };
            node = if elem == &current_elem {
                return Ok((node.as_slice().to_vec(), true));
            } else if elem < &current_elem {
                node.left()
            } else {
                node.right()
            };
        }

        Ok((node.as_slice().to_vec(), false))
    }

    /// Inserts `elem` into tree, returning an error if item already exists or on
    /// parsing errors.
    pub fn insert(&self, storage: &mut dyn Storage, elem: &T) -> StdResult<Vec<u8>> {
        let key = match self.find(storage, elem) {
            Ok((k, false)) => Ok(k),
            Ok((k, true)) => Err(StdError::GenericErr {
                msg: format!("Item already exists at {:#?}", k),
            }),
            Err(e) => Err(e),
        }?;
        storage.set(&key, &Ser::serialize(elem)?);
        Ok(key.to_vec())
    }

    /// Traverses the tree upwards to find the key with the next biggest element.
    /// Called when there is no right-hand child at `key`.
    fn backtrack(&self, key: Vec<u8>) -> StdResult<Vec<u8>> {
        // Checks the edge case where `key` is in the right-most position (largest element in tree)
        if key
            .clone()
            .iter()
            .filter(|b| **b == LEFT || **b == RIGHT)
            .all(|r| *r == RIGHT)
        {
            return Ok(key);
        }
        let mut current = key;
        loop {
            if let Some((relation, parent)) = current.split_last() {
                if *relation == LEFT {
                    // Found the next biggest element
                    current = parent.to_vec();
                    break;
                } else if *relation == RIGHT {
                    current = parent.to_vec()
                } else {
                    // We're at the root
                    break;
                }
            } else {
                return Err(StdError::generic_err("Key is empty."));
            }
        }
        Ok(current)
    }

    /// Finds the key of the next biggest element after the supplied key.
    pub fn next<'b>(&self, storage: &'b dyn Storage, key: Vec<u8>) -> StdResult<Vec<u8>> {
        let mut current = key.clone();
        if let Some(k) = storage.get(&[current.clone(), vec![RIGHT]].concat()) {
            current.push(RIGHT);
            loop {
                match storage.get(&[current.clone(), vec![LEFT]].concat()) {
                    Some(j) => current.push(LEFT),
                    None => return Ok(current),
                }
            }
        }
        self.backtrack(key)
    }

    // Return the largest element in the (sub-)tree.
    pub fn largest<'b>(&self, storage: &'b dyn Storage) -> StdResult<T> {
        let mut current = self.clone();
        while !current.right().is_empty(storage) {
            current = current.right();
        }
        current.load(storage)
    }

    // Return the smallest element in the (sub-)tree.
    pub fn smallest<'b>(&self, storage: &'b dyn Storage) -> StdResult<T> {
        let mut current = self.clone();
        while !current.left().is_empty(storage) {
            current = current.left();
        }
        current.load(storage)
    }

    /// Returns a sorted iter of self, lazily evaluated
    pub fn iter<'b>(&self, storage: &'b dyn Storage) -> BinarySearchTreeIterator<'a, 'b, T, Ser> {
        BinarySearchTreeIterator::new(self.clone(), storage)
    }

    /// Stringifies the node key for easier reading.
    /// Useful for debugging.
    pub fn key_to_string(&self) -> String {
        self.as_slice()
            .iter()
            .map(|b| {
                if *b > 31 {
                    String::from_utf8(vec![*b]).unwrap()
                } else if *b == LEFT {
                    String::from_str(".L").unwrap()
                } else if *b == RIGHT {
                    String::from_str(".R").unwrap()
                } else {
                    String::from_str(" ").unwrap()
                }
            })
            .collect()
    }

    /// Iterates from a specified starting element. Emulates the `Inclusive` and `Exclusive` `Bound`
    /// behavior in vanilla *cw-storage-plus*, but only on the left side of the range, i.e. the start.
    ///
    /// The `exclusive` boolean argument enables this feature. If set to `true`, iteration will start
    /// *after* the supplied starting element `elem`, as opposed to *at* `elem`.
    ///
    /// When `elem` is not found, iteration starts from the next element in order, regardless of what
    /// `exclusive` is set to.
    ///
    /// In both cases, if the resulting starting element is the largest in the tree, an empty iterator
    /// will be returned.
    pub fn iter_from<'b>(
        &self,
        storage: &'b dyn Storage,
        elem: &T,
        exclusive: bool,
    ) -> StdResult<BinarySearchTreeIterator<'a, 'b, T, Ser>> {
        let start = match self.find(storage, elem) {
            // Element found
            Ok((key, true)) => {
                if exclusive {
                    // If lower limit of the iteration range is exclusive, we need to find the biggest element
                    self.next(storage, key)
                } else {
                    Ok(key)
                }
            }
            // Element not found in the tree
            Ok((key, false)) => {
                // If the root is empty, the whole tree is empty
                if key == self.key {
                    return Ok(BinarySearchTreeIterator::empty(storage));
                }
                // Find the next biggest (existing) element and iterate from there
                self.next(storage, key)
            }
            // Probably a storage error
            Err(e) => Err(e),
        }?;
        Ok(self.iter_from_key(storage, &start))
    }

    fn iter_from_key<'b>(
        &self,
        storage: &'b dyn Storage,
        start_key: &[u8],
    ) -> BinarySearchTreeIterator<'a, 'b, T, Ser> {
        let mut stack = vec![];
        for i in self.key.len()..start_key.len() + 1 {
            let key = &start_key[0..i];
            if let Some(next_branch) = start_key.get(i) {
                // if next node is to the right
                // current node is smaller and should not be included
                if *next_branch == RIGHT {
                    continue;
                }
            }
            let node = Self {
                key: self.key,
                prefix: Some(key.to_vec()),
                item_type: self.item_type,
                serialization_type: self.serialization_type,
            };
            stack.push(node);
        }
        BinarySearchTreeIterator {
            current: BinarySearchTree::new(b"iter_root"),
            storage,
            stack,
        }
    }
}

pub struct BinarySearchTreeIterator<'a, 'b, T, Ser = Json>
where
    T: Serialize + DeserializeOwned + PartialEq + PartialOrd,
    Ser: Serde,
{
    current: BinarySearchTree<'a, T, Ser>,
    storage: &'b dyn Storage,
    stack: Vec<BinarySearchTree<'a, T, Ser>>,
}

impl<'a, 'b, T, Ser> BinarySearchTreeIterator<'a, 'b, T, Ser>
where
    T: Serialize + DeserializeOwned + PartialEq + PartialOrd,
    Ser: Serde,
{
    pub const fn new(root: BinarySearchTree<'a, T, Ser>, storage: &'b dyn Storage) -> Self {
        let stack: Vec<BinarySearchTree<'a, T, Ser>> = vec![];
        Self {
            current: root,
            storage,
            stack,
        }
    }

    pub(self) const fn empty(storage: &'b dyn Storage) -> Self {
        Self::new(BinarySearchTree::new(b"iter_root"), storage)
    }
}

impl<'a, 'b, T, Ser> Iterator for BinarySearchTreeIterator<'a, 'b, T, Ser>
where
    T: Serialize + DeserializeOwned + PartialEq + PartialOrd,
    Ser: Serde,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let mut item: Option<T> = None;
        while !self.stack.is_empty() || !self.current.is_empty(self.storage) {
            if !self.current.is_empty(self.storage) {
                self.stack.push(self.current.clone());
                self.current = self.current.left();
            } else {
                // unwrap because stack cannot be empty here
                self.current = self.stack.pop().unwrap();
                item = match self.current.load(self.storage) {
                    Ok(i) => Some(i),
                    Err(_) => None,
                };
                self.current = self.current.right();
                // return item and resume traversal on future call
                break;
            }
        }
        item
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use cosmwasm_std::{testing::mock_dependencies, Addr};

    #[test]
    fn bst_iter() {
        let mut deps = mock_dependencies();
        let storage = deps.as_mut().storage;
        let bst: BinarySearchTree<Addr> = BinarySearchTree::new(b"test");
        let mut items: Vec<Addr> = vec!["def", "secret", "ghi", "deadbeef", "abc", "lol", "test"]
            .iter_mut()
            .map(|s| Addr::unchecked(s.to_string()))
            .collect();
        for item in &items {
            let res = bst.insert(storage, &item);
            assert!(res.is_ok());
        }
        let sorted = bst.iter(storage).collect::<Vec<_>>();
        items.sort();
        assert_eq!(sorted, items)
    }

    #[test]
    fn bst_iter_from_exclusive() {
        let mut deps = mock_dependencies();
        let storage = deps.as_mut().storage;
        let bst: BinarySearchTree<Addr> = BinarySearchTree::new(b"test");
        let mut items: Vec<Addr> = vec!["def", "secret", "ghi", "deadbeef", "abc", "lol", "test"]
            .iter_mut()
            .map(|s| Addr::unchecked(s.to_string()))
            .collect();
        for item in &items {
            let res = bst.insert(storage, &item);
            assert!(res.is_ok());
        }
        items.sort();
        let sorted = bst
            .iter_from(storage, &items[3], true)
            .unwrap()
            .collect::<Vec<_>>();
        assert_eq!(sorted, (&items[4..]).to_vec())
    }

    #[test]
    fn bst_iter_from_inclusive() {
        let mut deps = mock_dependencies();
        let storage = deps.as_mut().storage;
        let bst: BinarySearchTree<Addr> = BinarySearchTree::new(b"test");
        let mut items: Vec<Addr> = vec!["def", "secret", "ghi", "deadbeef", "abc", "lol", "test"]
            .iter_mut()
            .map(|s| Addr::unchecked(s.to_string()))
            .collect();
        for item in &items {
            let res = bst.insert(storage, &item);
            assert!(res.is_ok());
        }
        items.sort();
        let sorted = bst
            .iter_from(storage, &items[3], false)
            .unwrap()
            .collect::<Vec<_>>();
        assert_eq!(sorted, (&items[3..]).to_vec())
    }

    #[test]
    fn bst_keys() {
        let mut deps = mock_dependencies();
        let storage = deps.as_mut().storage;
        let bst: BinarySearchTree<Addr> = BinarySearchTree::new(b"test");
        let items: Vec<Addr> = vec!["def", "secret", "ghi", "deadbeef", "abc", "lol", "test"]
            .iter_mut()
            .map(|s| Addr::unchecked(s.to_string()))
            .collect();
        let mut last_key: Vec<u8> = vec![];
        for item in &items {
            let res = bst.insert(storage, &item);
            assert!(res.is_ok());
            let unwrapped = res.unwrap();
            assert_ne!(unwrapped, last_key);
            last_key = unwrapped;
        }
    }

    #[test]
    fn bst_find() {
        let mut deps = mock_dependencies();
        let storage = deps.as_mut().storage;
        let bst: BinarySearchTree<Addr> = BinarySearchTree::new(b"test");
        let items: Vec<Addr> = vec!["def", "secret", "ghi", "deadbeef", "abc", "lol", "test"]
            .iter_mut()
            .map(|s| Addr::unchecked(s.to_string()))
            .collect();
        for item in &items {
            let res = bst.insert(storage, &item);
            assert!(res.is_ok());
        }
        for item in &items {
            let res = bst.find(storage, &item);
            assert!(res.is_ok());
            let (_, found) = res.unwrap();
            assert_eq!(found, true);
        }
        let item = Addr::unchecked("new");
        let res = bst.find(storage, &item);
        assert!(res.is_ok());
        let (_, found) = res.unwrap();
        assert_eq!(found, false);
    }

    #[test]
    fn bst_insert() {
        let mut deps = mock_dependencies();
        let storage = deps.as_mut().storage;
        let bst: BinarySearchTree<Addr> = BinarySearchTree::new(b"test");
        let item = Addr::unchecked("new");

        let res = bst.insert(storage, &item);
        assert!(res.is_ok());
        let key = res.unwrap();

        let res = bst.insert(storage, &item);
        assert!(res.is_err());
        assert_eq!(
            res.unwrap_err(),
            StdError::GenericErr {
                msg: format!("Item already exists at {:#?}", key),
            }
        );
    }
}
