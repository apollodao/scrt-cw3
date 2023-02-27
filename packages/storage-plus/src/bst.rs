use std::{any::type_name, iter, marker::PhantomData};

use serde::{de::DeserializeOwned, Serialize};

use secret_cosmwasm_std::{StdError, StdResult, Storage};
use secret_cosmwasm_storage::to_length_prefixed;
use secret_toolkit::serialization::{Json, Serde};

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

    /// Returns a BST representation of the left node
    pub fn left(&self) -> Self {
        let suffix = b"L";
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

    /// Returns a BST representation of the right node
    pub fn right(&self) -> Self {
        let suffix = b"R";
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

    /// Checks to see if root node is empty
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
    /// parsing errors
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

    /// Returns a sorted iter of self, lazily evaluated
    pub fn iter<'b>(&self, storage: &'b dyn Storage) -> BinarySearchTreeIterator<'a, 'b, T, Ser> {
        BinarySearchTreeIterator::new(self.clone(), storage)
    }

    pub fn iter_from<'b>(
        &self,
        storage: &'b dyn Storage,
        elem: &T,
    ) -> StdResult<BinarySearchTreeIterator<'a, 'b, T, Ser>> {
        let start = match self.find(storage, elem) {
            // Element found
            Ok((key, true)) => Ok(key),
            // Element not found in the tree
            Ok((key, false)) => {
                // If the root is empty, the whole tree is empty
                if key == self.key {
                    return Ok(BinarySearchTreeIterator::empty(storage));
                }
                if let Some(last) = key.last() {
                    // If the suggested insert position is a left node, start iterating from the parent
                    if *last == b'L' {
                        // We can unwrap() here because we already know `key` isn't empty
                        return self.iter_from_key(storage, key.split_last().unwrap().1);
                    // If it's a right node, there is no larger element in the tree
                    } else {
                        return Ok(BinarySearchTreeIterator::empty(storage));
                    }
                } else {
                    // What does it mean if key is empty? Can it happen?
                    todo!()
                }
            }
            // Probably a storage error
            Err(e) => Err(e),
        }?;
        self.iter_from_key(storage, &start)
    }

    fn iter_from_key<'b>(
        &self,
        storage: &'b dyn Storage,
        start_key: &[u8],
    ) -> StdResult<BinarySearchTreeIterator<'a, 'b, T, Ser>> {
        let mut stack = vec![];
        for i in self.key.len()..start_key.len() + 1 {
            let key = &start_key[0..i];
            if let Some(next_branch) = start_key.get(i) {
                // if next node is to the right
                // current node is smaller and should not be included
                if *next_branch == b'R' {
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
        let iter = BinarySearchTreeIterator {
            current: BinarySearchTree::new(b"iter_root"),
            storage,
            stack,
        };
        Ok(iter)
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
    use secret_cosmwasm_std::{testing::mock_dependencies, Addr};

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
    fn bst_iter_from() {
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
            .iter_from(storage, &items[3])
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
