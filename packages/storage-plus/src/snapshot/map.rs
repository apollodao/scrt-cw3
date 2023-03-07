use serde::de::DeserializeOwned;
use serde::Serialize;

use cosmwasm_std::{StdError, StdResult, Storage};

use crate::snapshot::{ChangeSet, Snapshot};
use crate::{BinarySearchTree, BinarySearchTreeIterator, Strategy};

use secret_toolkit::serialization::{Json, Serde};
use secret_toolkit::storage::Keymap as Map;

/// Map that maintains a snapshots of one or more checkpoints.
/// We can query historical data as well as current state.
/// What data is snapshotted depends on the Strategy.
pub struct SnapshotMap<'a, K, T, S = Json>
where
    K: Serialize + DeserializeOwned + PartialOrd,
    T: Serialize + DeserializeOwned,
    S: Serde,
{
    primary: Map<'a, K, T, S>,
    snapshots: Snapshot<'a, T>,
    key_index: BinarySearchTree<'a, K, S>,
    primary_key: &'a [u8],
}

impl<'a, K, T, S> SnapshotMap<'a, K, T, S>
where
    K: Serialize + DeserializeOwned + PartialOrd,
    T: Serialize + DeserializeOwned,
    S: Serde,
{
    /// Example:
    ///
    /// ```rust
    /// use cw_storage_plus::{SnapshotMap, Strategy};
    ///
    /// SnapshotMap::<u64, String>::new(
    ///     b"never",
    ///     b"never__key",
    ///     b"never__check",
    ///     b"never__change",
    ///     b"never__height",
    ///     Strategy::Never
    /// );
    /// ```
    pub const fn new(
        primary_key: &'a [u8],
        key_index: &'a [u8],
        checkpoints: &'a [u8],
        changelog: &'a [u8],
        height_index: &'a [u8],
        strategy: Strategy,
    ) -> Self {
        Self {
            primary: Map::new(primary_key),
            snapshots: Snapshot::new(checkpoints, changelog, height_index, strategy),
            key_index: BinarySearchTree::new(key_index),
            primary_key,
        }
    }

    pub fn changelog(&self) -> &Map<'a, u64, ChangeSet<T>, Json> {
        &self.snapshots.changelog
    }

    fn serialize_key(&self, key: &K) -> StdResult<Vec<u8>> {
        S::serialize(key)
    }

    fn deserialize_key(&self, key_data: &[u8]) -> StdResult<K> {
        S::deserialize(key_data)
    }

    fn clone_primary(&self) -> Map<'a, K, T, S> {
        Map::new(self.primary_key)
    }
}

impl<'a, K, T> SnapshotMap<'a, K, T>
where
    K: Serialize + DeserializeOwned + PartialOrd,
    T: Serialize + DeserializeOwned,
{
    pub fn add_checkpoint(&self, store: &mut dyn Storage, height: u64) -> StdResult<()> {
        self.snapshots.add_checkpoint(store, height)
    }

    pub fn remove_checkpoint(&self, store: &mut dyn Storage, height: u64) -> StdResult<()> {
        self.snapshots.remove_checkpoint(store, height)
    }
}

impl<'a, K, T> SnapshotMap<'a, K, T>
where
    K: Serialize + DeserializeOwned + PartialOrd + Clone,
    T: Serialize + DeserializeOwned,
{
    /// load old value and store changelog
    fn write_change(&self, store: &mut dyn Storage, k: K, height: u64) -> StdResult<()> {
        // if there is already data in the changelog for this key and block, do not write more
        // @todo we need to serialize the key like in KeyMap
        if self
            .snapshots
            .has_changelog(store, &self.serialize_key(&k)?, height)?
        {
            return Ok(());
        }
        // otherwise, store the previous value
        let old = self.may_load(store, k.clone())?;
        self.snapshots
            .write_changelog(store, &self.serialize_key(&k)?, height, old)
    }

    pub fn save(&self, store: &mut dyn Storage, k: K, data: &T, height: u64) -> StdResult<()> {
        if self
            .snapshots
            .should_checkpoint(store, &self.serialize_key(&k)?)?
        {
            self.write_change(store, k.clone(), height)?;
        }
        self.primary.insert(store, &k, &data)?;
        match self.key_index.insert(store, &k) {
            Err(StdError::GenericErr { .. }) => Ok(()), // just means element already exists
            Err(e) => Err(e),                           // real error
            Ok(_) => Ok(()),
        }
    }

    pub fn remove(&self, store: &mut dyn Storage, k: K, height: u64) -> StdResult<()> {
        if self
            .snapshots
            .should_checkpoint(store, &self.serialize_key(&k)?)?
        {
            self.write_change(store, k.clone(), height)?;
        }
        self.primary.remove(store, &k)
        // Here we would like to remove the corresponding entry in our key index BST, but that
        // operation doesn't exist so we will just leave it. In extreme cases it will slow down
        // iteration, but in practice it's probably negligible.
    }

    /// load will return an error if no data is set at the given key, or on parse error
    pub fn load(&self, store: &dyn Storage, k: K) -> StdResult<T> {
        self.primary
            .get(store, &k)
            .ok_or(StdError::not_found("key"))
    }

    /// may_load will parse the data stored at the key if present, returns Ok(None) if no data there.
    /// returns an error on issues parsing
    pub fn may_load(&self, store: &dyn Storage, k: K) -> StdResult<Option<T>> {
        Ok(self.primary.get(store, &k))
    }

    pub fn may_load_at_height(
        &self,
        store: &dyn Storage,
        k: K,
        height: u64,
    ) -> StdResult<Option<T>> {
        let snapshot =
            self.snapshots
                .may_load_at_height(store, &self.serialize_key(&k)?, height)?;

        if let Some(r) = snapshot {
            Ok(r)
        } else {
            // otherwise, return current value
            self.may_load(store, k)
        }
    }

    pub fn assert_checkpointed(&self, store: &dyn Storage, height: u64) -> StdResult<()> {
        self.snapshots.assert_checkpointed(store, height)
    }

    /// Loads the data, perform the specified action, and store the result
    /// in the database. This is shorthand for some common sequences, which may be useful.
    ///
    /// If the data exists, `action(Some(value))` is called. Otherwise `action(None)` is called.
    ///
    /// This is a bit more customized than needed to only read "old" value 1 time, not 2 per naive approach
    pub fn update<A, E>(
        &self,
        store: &mut dyn Storage,
        k: K,
        height: u64,
        action: A,
    ) -> Result<T, E>
    where
        A: FnOnce(Option<T>) -> Result<T, E>,
        E: From<StdError>,
    {
        let input = self.may_load(store, k.clone())?;
        let output = action(input)?;
        self.save(store, k, &output, height)?;
        Ok(output)
    }

    // @todo add iter() function
    //pub fn iter(&self) -> StdResult<>
}

impl<'a, K, T, S> SnapshotMap<'a, K, T, S>
where
    K: Serialize + DeserializeOwned + PartialOrd,
    T: Serialize + DeserializeOwned,
    S: Serde,
{
    pub fn iter<'b>(&self, store: &'b dyn Storage) -> SnapshotMapIterator<'a, 'b, K, T, S> {
        SnapshotMapIterator::new(store, self.clone_primary(), self.key_index.iter(store))
    }

    pub fn iter_from<'b>(
        &self,
        store: &'b dyn Storage,
        key: K,
        exclusive: bool,
    ) -> StdResult<SnapshotMapIterator<'a, 'b, K, T, S>> {
        Ok(SnapshotMapIterator::new(
            store,
            self.clone_primary(),
            self.key_index.iter_from(store, &key, exclusive)?,
        ))
    }
}

pub struct SnapshotMapIterator<'a, 'b, K, T, S>
where
    K: Serialize + DeserializeOwned + PartialOrd,
    T: Serialize + DeserializeOwned,
    S: Serde,
{
    store: &'b dyn Storage,
    map: Map<'a, K, T, S>,
    index_iter: BinarySearchTreeIterator<'a, 'b, K, S>,
}

impl<'a, 'b, K, T, S> SnapshotMapIterator<'a, 'b, K, T, S>
where
    K: Serialize + DeserializeOwned + PartialOrd,
    T: Serialize + DeserializeOwned,
    S: Serde,
{
    pub const fn new(
        store: &'b dyn Storage,
        map: Map<'a, K, T, S>,
        index_iter: BinarySearchTreeIterator<'a, 'b, K, S>,
    ) -> Self {
        Self {
            store,
            map,
            index_iter,
        }
    }
}

impl<'a, 'b, K, T, S> Iterator for SnapshotMapIterator<'a, 'b, K, T, S>
where
    K: Serialize + DeserializeOwned + PartialOrd,
    T: Serialize + DeserializeOwned,
    S: Serde,
{
    type Item = (K, T);

    fn next(&mut self) -> Option<Self::Item> {
        // Because we don't remove keys from the index when they are removed from the primary map,
        // we need to keep iterating until we get a hit if the key is missing from the primary
        let mut item = None;
        while item.is_none() {
            if let Some(k) = self.index_iter.next() {
                item = self.map.get(self.store, &k).map(|t| (k, t));
            } else {
                return None;
            }
        }
        item
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cosmwasm_std::testing::MockStorage;

    type TestMap = SnapshotMap<'static, String, u64>;
    type TestMapCompositeKey<'a> = SnapshotMap<'static, (String, String), u64>;

    static NEVER: TestMap = SnapshotMap::new(
        b"never",
        b"never__key",
        b"never__check",
        b"never__change",
        b"never__height",
        Strategy::Never,
    );
    const EVERY: TestMap = SnapshotMap::new(
        b"every",
        b"every__key",
        b"every__check",
        b"every__change",
        b"every__height",
        Strategy::EveryBlock,
    );
    const EVERY_COMPOSITE_KEY: TestMapCompositeKey = SnapshotMap::new(
        b"every",
        b"every__key",
        b"every__check",
        b"every__change",
        b"every__height",
        Strategy::EveryBlock,
    );
    const SELECT: TestMap = SnapshotMap::new(
        b"select",
        b"select__key",
        b"select__check",
        b"select__change",
        b"select__height",
        Strategy::Selected,
    );

    // Fills a map &[u8] -> u64 with the following writes:
    // 1: A = 5
    // 2: B = 7
    // 3: C = 1, A = 8
    // 4: B = None, C = 13
    // 5: A = None, D = 22
    // Final values -> C = 13, D = 22
    // Values at beginning of 3 -> A = 5, B = 7
    // Values at beginning of 5 -> A = 8, C = 13
    fn init_data(map: &TestMap, storage: &mut dyn Storage) {
        map.save(storage, "A".to_string().to_string(), &5, 1)
            .unwrap();
        map.save(storage, "B".to_string(), &7, 2).unwrap();

        // checkpoint 3
        map.add_checkpoint(storage, 3).unwrap();

        // also use update to set - to ensure this works
        map.save(storage, "C".to_string(), &1, 3).unwrap();
        map.update(storage, "A".to_string(), 3, |_| -> StdResult<u64> { Ok(8) })
            .unwrap();

        map.remove(storage, "B".to_string(), 4).unwrap();
        map.save(storage, "C".to_string(), &13, 4).unwrap();

        // checkpoint 5
        map.add_checkpoint(storage, 5).unwrap();
        map.remove(storage, "A".to_string(), 5).unwrap();
        map.update(storage, "D".to_string(), 5, |_| -> StdResult<u64> {
            Ok(22)
        })
        .unwrap();
        // and delete it later (unknown if all data present)
        map.remove_checkpoint(storage, 5).unwrap();
    }

    const FINAL_VALUES: &[(&str, Option<u64>)] =
        &[("A", None), ("B", None), ("C", Some(13)), ("D", Some(22))];

    const VALUES_START_3: &[(&str, Option<u64>)] =
        &[("A", Some(5)), ("B", Some(7)), ("C", None), ("D", None)];

    const VALUES_START_5: &[(&str, Option<u64>)] =
        &[("A", Some(8)), ("B", None), ("C", Some(13)), ("D", None)];

    // Same as `init_data`, but we have a composite key for testing range.
    fn init_data_composite_key(map: &TestMapCompositeKey, storage: &mut dyn Storage) {
        map.save(storage, ("A".to_string(), "B".to_string()), &5, 1)
            .unwrap();
        map.save(storage, ("B".to_string(), "A".to_string()), &7, 2)
            .unwrap();

        // checkpoint 3
        map.add_checkpoint(storage, 3).unwrap();

        // also use update to set - to ensure this works
        map.save(storage, ("B".to_string(), "B".to_string()), &1, 3)
            .unwrap();
        map.update(
            storage,
            ("A".to_string(), "B".to_string()),
            3,
            |_| -> StdResult<u64> { Ok(8) },
        )
        .unwrap();

        map.remove(storage, ("B".to_string(), "A".to_string()), 4)
            .unwrap();
        map.save(storage, ("B".to_string(), "B".to_string()), &13, 4)
            .unwrap();

        // checkpoint 5
        map.add_checkpoint(storage, 5).unwrap();
        map.remove(storage, ("A".to_string(), "B".to_string()), 5)
            .unwrap();
        map.update(
            storage,
            ("C".to_string(), "A".to_string()),
            5,
            |_| -> StdResult<u64> { Ok(22) },
        )
        .unwrap();
        // and delete it later (unknown if all data present)
        map.remove_checkpoint(storage, 5).unwrap();
    }

    fn assert_final_values(map: &TestMap, storage: &dyn Storage) {
        for (k, v) in FINAL_VALUES.iter().cloned() {
            assert_eq!(v, map.may_load(storage, k.to_string()).unwrap());
        }
    }

    fn assert_values_at_height(
        map: &TestMap,
        storage: &dyn Storage,
        height: u64,
        values: &[(&str, Option<u64>)],
    ) {
        for (k, v) in values.iter().cloned() {
            assert_eq!(
                v,
                map.may_load_at_height(storage, k.to_string(), height)
                    .unwrap()
            );
        }
    }

    fn assert_missing_checkpoint(map: &TestMap, storage: &dyn Storage, height: u64) {
        for k in &["A", "B", "C", "D"] {
            assert!(map
                .may_load_at_height(storage, (*k).to_string(), height)
                .is_err());
        }
    }

    #[test]
    fn never_works_like_normal_map() {
        let mut storage = MockStorage::new();
        init_data(&NEVER, &mut storage);
        assert_final_values(&NEVER, &storage);

        // historical queries return error
        assert_missing_checkpoint(&NEVER, &storage, 3);
        assert_missing_checkpoint(&NEVER, &storage, 5);
    }

    #[test]
    fn every_blocks_stores_present_and_past() {
        let mut storage = MockStorage::new();
        init_data(&EVERY, &mut storage);
        assert_final_values(&EVERY, &storage);

        // historical queries return historical values
        assert_values_at_height(&EVERY, &storage, 3, VALUES_START_3);
        assert_values_at_height(&EVERY, &storage, 5, VALUES_START_5);
    }

    //#[test]
    fn selected_shows_3_not_5() {
        let mut storage = MockStorage::new();
        init_data(&SELECT, &mut storage);
        assert_final_values(&SELECT, &storage);

        // historical queries return historical values
        assert_values_at_height(&SELECT, &storage, 3, VALUES_START_3);
        // never checkpointed
        assert_missing_checkpoint(&NEVER, &storage, 1);
        // deleted checkpoint
        assert_missing_checkpoint(&NEVER, &storage, 5);
    }

    #[test]
    fn handle_multiple_writes_in_one_block() {
        let mut storage = MockStorage::new();

        EVERY.save(&mut storage, "A".to_string(), &5, 1).unwrap();
        EVERY.save(&mut storage, "B".to_string(), &7, 2).unwrap();
        EVERY.save(&mut storage, "C".to_string(), &2, 2).unwrap();

        // update and save - A query at 3 => 5, at 4 => 12
        EVERY
            .update(&mut storage, "A".to_string(), 3, |_| -> StdResult<u64> {
                Ok(9)
            })
            .unwrap();
        EVERY.save(&mut storage, "A".to_string(), &12, 3).unwrap();
        assert_eq!(
            Some(5),
            EVERY
                .may_load_at_height(&storage, "A".to_string(), 2)
                .unwrap()
        );
        assert_eq!(
            Some(5),
            EVERY
                .may_load_at_height(&storage, "A".to_string(), 3)
                .unwrap()
        );
        assert_eq!(
            Some(12),
            EVERY
                .may_load_at_height(&storage, "A".to_string(), 4)
                .unwrap()
        );

        // save and remove - B query at 4 => 7, at 5 => None
        EVERY.save(&mut storage, "B".to_string(), &17, 4).unwrap();
        EVERY.remove(&mut storage, "B".to_string(), 4).unwrap();
        assert_eq!(
            Some(7),
            EVERY
                .may_load_at_height(&storage, "B".to_string(), 3)
                .unwrap()
        );
        assert_eq!(
            Some(7),
            EVERY
                .may_load_at_height(&storage, "B".to_string(), 4)
                .unwrap()
        );
        assert_eq!(
            None,
            EVERY
                .may_load_at_height(&storage, "B".to_string(), 5)
                .unwrap()
        );

        // remove and update - C query at 5 => 2, at 6 => 16
        EVERY.remove(&mut storage, "C".to_string(), 5).unwrap();
        EVERY
            .update(&mut storage, "C".to_string(), 5, |_| -> StdResult<u64> {
                Ok(16)
            })
            .unwrap();
        assert_eq!(
            Some(2),
            EVERY
                .may_load_at_height(&storage, "C".to_string(), 4)
                .unwrap()
        );
        assert_eq!(
            Some(2),
            EVERY
                .may_load_at_height(&storage, "C".to_string(), 5)
                .unwrap()
        );
        assert_eq!(
            Some(16),
            EVERY
                .may_load_at_height(&storage, "C".to_string(), 6)
                .unwrap()
        );
    }

    #[test]
    #[cfg(feature = "iterator")]
    fn changelog_range_works() {
        use cosmwasm_std::Order;

        let mut store = MockStorage::new();

        // simple data for testing
        EVERY.save(&mut store, "A", &5, 1).unwrap();
        EVERY.save(&mut store, "B", &7, 2).unwrap();
        EVERY
            .update(&mut store, "A", 3, |_| -> StdResult<u64> { Ok(8) })
            .unwrap();
        EVERY.remove(&mut store, "B", 4).unwrap();

        // let's try to iterate over the changelog
        let all: StdResult<Vec<_>> = EVERY
            .changelog()
            .range(&store, None, None, Order::Ascending)
            .collect();
        let all = all.unwrap();
        assert_eq!(4, all.len());
        assert_eq!(
            all,
            vec![
                (("A".into(), 1), ChangeSet { old: None }),
                (("A".into(), 3), ChangeSet { old: Some(5) }),
                (("B".into(), 2), ChangeSet { old: None }),
                (("B".into(), 4), ChangeSet { old: Some(7) })
            ]
        );

        // let's try to iterate over a changelog key/prefix
        let all: StdResult<Vec<_>> = EVERY
            .changelog()
            .prefix("B")
            .range(&store, None, None, Order::Ascending)
            .collect();
        let all = all.unwrap();
        assert_eq!(2, all.len());
        assert_eq!(
            all,
            vec![
                (2, ChangeSet { old: None }),
                (4, ChangeSet { old: Some(7) })
            ]
        );

        // let's try to iterate over a changelog prefixed range
        let all: StdResult<Vec<_>> = EVERY
            .changelog()
            .prefix("A")
            .range(&store, Some(Bound::inclusive(3u64)), None, Order::Ascending)
            .collect();
        let all = all.unwrap();
        assert_eq!(1, all.len());
        assert_eq!(all, vec![(3, ChangeSet { old: Some(5) }),]);
    }

    #[test]
    #[cfg(feature = "iterator")]
    fn range_simple_string_key() {
        use cosmwasm_std::Order;

        let mut store = MockStorage::new();
        init_data(&EVERY, &mut store);

        // let's try to iterate!
        let all: StdResult<Vec<_>> = EVERY.range(&store, None, None, Order::Ascending).collect();
        let all = all.unwrap();
        assert_eq!(2, all.len());
        assert_eq!(all, vec![("C".into(), 13), ("D".into(), 22)]);

        // let's try to iterate over a range
        let all: StdResult<Vec<_>> = EVERY
            .range(&store, Some(Bound::inclusive("C")), None, Order::Ascending)
            .collect();
        let all = all.unwrap();
        assert_eq!(2, all.len());
        assert_eq!(all, vec![("C".into(), 13), ("D".into(), 22)]);

        // let's try to iterate over a more restrictive range
        let all: StdResult<Vec<_>> = EVERY
            .range(&store, Some(Bound::inclusive("D")), None, Order::Ascending)
            .collect();
        let all = all.unwrap();
        assert_eq!(1, all.len());
        assert_eq!(all, vec![("D".into(), 22)]);
    }

    #[test]
    #[cfg(feature = "iterator")]
    fn range_composite_key() {
        use cosmwasm_std::Order;

        let mut store = MockStorage::new();
        init_data_composite_key(&EVERY_COMPOSITE_KEY, &mut store);

        // let's try to iterate!
        let all: StdResult<Vec<_>> = EVERY_COMPOSITE_KEY
            .range(&store, None, None, Order::Ascending)
            .collect();
        let all = all.unwrap();
        assert_eq!(2, all.len());
        assert_eq!(
            all,
            vec![
                (("B".into(), "B".into()), 13),
                (("C".into(), "A".into()), 22)
            ]
        );
    }

    #[test]
    #[cfg(feature = "iterator")]
    fn prefix_range_composite_key() {
        use cosmwasm_std::Order;

        let mut store = MockStorage::new();
        init_data_composite_key(&EVERY_COMPOSITE_KEY, &mut store);

        // let's prefix-range and iterate
        let all: StdResult<Vec<_>> = EVERY_COMPOSITE_KEY
            .prefix_range(
                &store,
                None,
                Some(PrefixBound::exclusive("C")),
                Order::Descending,
            )
            .collect();
        let all = all.unwrap();
        assert_eq!(1, all.len());
        assert_eq!(all, vec![(("B".into(), "B".into()), 13)]);
    }

    #[test]
    #[cfg(feature = "iterator")]
    fn prefix_composite_key() {
        use cosmwasm_std::Order;

        let mut store = MockStorage::new();
        init_data_composite_key(&EVERY_COMPOSITE_KEY, &mut store);

        // let's prefix and iterate
        let all: StdResult<Vec<_>> = EVERY_COMPOSITE_KEY
            .prefix("C")
            .range(&store, None, None, Order::Ascending)
            .collect();
        let all = all.unwrap();
        assert_eq!(1, all.len());
        assert_eq!(all, vec![("A".into(), 22),]);
    }

    #[test]
    #[cfg(feature = "iterator")]
    fn sub_prefix_composite_key() {
        use cosmwasm_std::Order;

        let mut store = MockStorage::new();
        init_data_composite_key(&EVERY_COMPOSITE_KEY, &mut store);

        // Let's sub-prefix and iterate.
        // This is similar to calling range() directly, but added here for completeness /
        // sub_prefix type checks
        let all: StdResult<Vec<_>> = EVERY_COMPOSITE_KEY
            .sub_prefix(())
            .range(&store, None, None, Order::Ascending)
            .collect();
        let all = all.unwrap();
        assert_eq!(2, all.len());
        assert_eq!(
            all,
            vec![
                (("B".into(), "B".into()), 13),
                (("C".into(), "A".into()), 22)
            ]
        );
    }
}
