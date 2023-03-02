mod map;

pub use map::SnapshotMap;

use secret_cosmwasm_std::{StdError, StdResult, Storage};
use secret_toolkit::serialization::Json;
use secret_toolkit::storage::Keymap as Map;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::BinarySearchTree;

/// Structure holding a map of checkpoints composited from
/// height (as u64) and counter of how many times it has
/// been checkpointed (as u32).
/// Stores all changes in changelog.
pub(crate) struct Snapshot<'a, T>
where
    T: Serialize + DeserializeOwned,
{
    checkpoints: Map<'a, u64, u32, Json>,

    // this stores all changes (key, height). Must differentiate between no data written,
    // and explicit None (just inserted)
    changelog: Map<'a, u64, ChangeSet<T>, Json>,
    height_index: BinarySearchTree<'a, u64, Json>,

    // How aggressive we are about checkpointing all data
    strategy: Strategy,
}

impl<'a, T> Snapshot<'a, T>
where
    T: Serialize + DeserializeOwned,
{
    pub const fn new(
        checkpoints: &'a [u8],
        changelog: &'a [u8],
        height_index: &'a [u8],
        strategy: Strategy,
    ) -> Snapshot<'a, T> {
        Snapshot {
            checkpoints: Map::new(checkpoints),
            changelog: Map::new(changelog),
            height_index: BinarySearchTree::new(height_index),
            strategy,
        }
    }

    pub fn add_checkpoint(&self, store: &mut dyn Storage, height: u64) -> StdResult<()> {
        let count = self.checkpoints.get(store, &height).unwrap_or_default() + 1;
        self.checkpoints.insert(store, &height, &count)
    }

    pub fn remove_checkpoint(&self, store: &mut dyn Storage, height: u64) -> StdResult<()> {
        // soft removes checkpoint to preserve order
        // so this is just for show
        match self.checkpoints.get(store, &height).unwrap_or_default() {
            count if count > 0 => self.checkpoints.insert(store, &height, &(count - 1)),
            0 => Ok(()),
            _ => unreachable!("Should never happen"),
        }
    }
}

impl<'a, T> Snapshot<'a, T>
where
    T: Serialize + DeserializeOwned,
{
    /// should_checkpoint looks at the strategy and determines if we want to checkpoint
    pub fn should_checkpoint(&self, store: &dyn Storage, k: &[u8]) -> StdResult<bool> {
        match self.strategy {
            Strategy::EveryBlock => Ok(true),
            Strategy::Never => Ok(false),
            Strategy::Selected => self.should_checkpoint_selected(store, k),
        }
    }

    /// this is just pulled out from above for the selected block
    fn should_checkpoint_selected(&self, _store: &dyn Storage, _k: &[u8]) -> StdResult<bool> {
        // This is never called in either of the cw4 contracts due to the EveryBlock strategy being
        // chosen, so we'll just ignore this for now
        unimplemented!()
        /*
        // most recent checkpoint
        let checkpoint = self
            .checkpoints
            .range(store, None, None, Order::Descending)
            .next()
            .transpose()?;
        if let Some((height, _)) = checkpoint {
            // any changelog for the given key since then?
            let start = Bound::inclusive(height);
            let first = self
                .changelog
                .prefix(k.clone())
                .range_raw(store, Some(start), None, Order::Ascending)
                .next()
                .transpose()?;
            if first.is_none() {
                // there must be at least one open checkpoint and no changelog for the given height since then
                return Ok(true);
            }
        }
        // otherwise, we don't save this
        Ok(false)
        */
    }

    // If there is no checkpoint for that height, then we return StdError::NotFound
    pub fn assert_checkpointed(&self, store: &dyn Storage, height: u64) -> StdResult<()> {
        let has = match self.strategy {
            Strategy::EveryBlock => true,
            Strategy::Never => false,
            Strategy::Selected => self.checkpoints.contains(store, &height),
        };
        match has {
            true => Ok(()),
            false => Err(StdError::not_found("checkpoint")),
        }
    }

    pub fn has_changelog(
        &self,
        store: &mut dyn Storage,
        key: &[u8],
        height: u64,
    ) -> StdResult<bool> {
        Ok(self.changelog.add_suffix(key).contains(store, &height))
    }

    pub fn write_changelog(
        &self,
        store: &mut dyn Storage,
        key: &[u8],
        height: u64,
        old: Option<T>,
    ) -> StdResult<()> {
        self.height_index.add_suffix(key).insert(store, &height)?;
        self.changelog
            .add_suffix(key)
            .insert(store, &height, &ChangeSet { old })
    }

    // may_load_at_height reads historical data from given checkpoints.
    // Returns StdError::NotFound if we have no checkpoint, and can give no data.
    // Returns Ok(None) if there is a checkpoint, but no cached data (no changes since the
    // checkpoint. Caller should query current state).
    // Return Ok(Some(x)) if there is a checkpoint and data written to changelog, returning the state at that time
    pub fn may_load_at_height(
        &self,
        store: &dyn Storage,
        key: &[u8],
        height: u64,
    ) -> StdResult<Option<Option<T>>> {
        self.assert_checkpointed(store, height)?;

        // this will look for the first snapshot of height >= given height
        // If None, there is no snapshot since that time.
        let first = self
            .height_index
            .add_suffix(key)
            .iter_from(store, &height, false)?
            .next();

        if let Some(h) = first {
            let snap = self.changelog.add_suffix(key).get(store, &h);
            // if we found a match, return this last one
            if let Some(c) = snap {
                return Ok(Some(c.old));
            }
        }
        Ok(None)
    }
}

#[derive(Clone, Copy, PartialEq, Debug, Serialize, Deserialize)]
pub enum Strategy {
    EveryBlock,
    Never,
    /// Only writes for linked blocks - does a few more reads to save some writes.
    /// Probably uses more gas, but less total disk usage.
    ///
    /// Note that you need a trusted source (eg. own contract) to set/remove checkpoints.
    /// Useful when the checkpoint setting happens in the same contract as the snapshotting.
    Selected,
}

#[derive(Clone, Copy, PartialEq, Debug, Serialize, Deserialize)]
pub struct ChangeSet<T> {
    pub old: Option<T>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use secret_cosmwasm_std::testing::MockStorage;

    type TestSnapshot = Snapshot<'static, u64>;

    const NEVER: TestSnapshot = Snapshot::new(
        b"never__check",
        b"never__change",
        b"never__index",
        Strategy::Never,
    );
    const EVERY: TestSnapshot = Snapshot::new(
        b"every__check",
        b"every__change",
        b"every__index",
        Strategy::EveryBlock,
    );
    /*  const SELECT: TestSnapshot = Snapshot::new(
        b"select__check",
        b"select__change",
        b"select__index",
        Strategy::Selected,
    ); */

    const DUMMY_KEY: &[u8] = b"dummy";

    #[test]
    fn should_checkpoint() {
        let storage = MockStorage::new();

        assert_eq!(NEVER.should_checkpoint(&storage, &DUMMY_KEY), Ok(false));
        assert_eq!(EVERY.should_checkpoint(&storage, &DUMMY_KEY), Ok(true));
        ////        assert_eq!(SELECT.should_checkpoint(&storage, &DUMMY_KEY), Ok(false));
    }

    #[test]
    fn assert_checkpointed() {
        let mut storage = MockStorage::new();

        assert_eq!(
            NEVER.assert_checkpointed(&storage, 1),
            Err(StdError::not_found("checkpoint"))
        );
        assert_eq!(EVERY.assert_checkpointed(&storage, 1), Ok(()));
        //assert_eq!(
        //    SELECT.assert_checkpointed(&storage, 1),
        //    Err(StdError::not_found("checkpoint"))
        //);

        // Add a checkpoint at 1
        NEVER.add_checkpoint(&mut storage, 1).unwrap();
        EVERY.add_checkpoint(&mut storage, 1).unwrap();
        //        SELECT.add_checkpoint(&mut storage, 1).unwrap();

        assert_eq!(
            NEVER.assert_checkpointed(&storage, 1),
            Err(StdError::not_found("checkpoint"))
        );
        assert_eq!(EVERY.assert_checkpointed(&storage, 1), Ok(()));
        //        assert_eq!(SELECT.assert_checkpointed(&storage, 1), Ok(()));

        // Remove checkpoint
        NEVER.remove_checkpoint(&mut storage, 1).unwrap();
        EVERY.remove_checkpoint(&mut storage, 1).unwrap();
        //        SELECT.remove_checkpoint(&mut storage, 1).unwrap();

        assert_eq!(
            NEVER.assert_checkpointed(&storage, 1),
            Err(StdError::not_found("checkpoint"))
        );
        assert_eq!(EVERY.assert_checkpointed(&storage, 1), Ok(()));
        //assert_eq!(
        //    SELECT.assert_checkpointed(&storage, 1),
        //    Err(StdError::not_found("checkpoint"))
        //);
    }

    #[test]
    fn has_changelog() {
        let mut storage = MockStorage::new();

        assert_eq!(NEVER.has_changelog(&mut storage, DUMMY_KEY, 1), Ok(false));
        assert_eq!(EVERY.has_changelog(&mut storage, DUMMY_KEY, 1), Ok(false));
        //        assert_eq!(SELECT.has_changelog(&mut storage, DUMMY_KEY, 1), Ok(false));

        assert_eq!(NEVER.has_changelog(&mut storage, DUMMY_KEY, 2), Ok(false));
        assert_eq!(EVERY.has_changelog(&mut storage, DUMMY_KEY, 2), Ok(false));
        //        assert_eq!(SELECT.has_changelog(&mut storage, DUMMY_KEY, 2), Ok(false));

        assert_eq!(NEVER.has_changelog(&mut storage, DUMMY_KEY, 3), Ok(false));
        assert_eq!(EVERY.has_changelog(&mut storage, DUMMY_KEY, 3), Ok(false));
        //        assert_eq!(SELECT.has_changelog(&mut storage, DUMMY_KEY, 3), Ok(false));

        // Write a changelog at 2
        NEVER
            .write_changelog(&mut storage, DUMMY_KEY, 2, Some(3))
            .unwrap();
        EVERY
            .write_changelog(&mut storage, DUMMY_KEY, 2, Some(4))
            .unwrap();
        //SELECT
        //    .write_changelog(&mut storage, DUMMY_KEY, 2, Some(5))
        //    .unwrap();

        assert_eq!(NEVER.has_changelog(&mut storage, DUMMY_KEY, 1), Ok(false));
        assert_eq!(EVERY.has_changelog(&mut storage, DUMMY_KEY, 1), Ok(false));
        //        assert_eq!(SELECT.has_changelog(&mut storage, DUMMY_KEY, 1), Ok(false));

        assert_eq!(NEVER.has_changelog(&mut storage, DUMMY_KEY, 2), Ok(true));
        assert_eq!(EVERY.has_changelog(&mut storage, DUMMY_KEY, 2), Ok(true));
        //        assert_eq!(SELECT.has_changelog(&mut storage, DUMMY_KEY, 2), Ok(true));

        assert_eq!(NEVER.has_changelog(&mut storage, DUMMY_KEY, 3), Ok(false));
        assert_eq!(EVERY.has_changelog(&mut storage, DUMMY_KEY, 3), Ok(false));
        //        assert_eq!(SELECT.has_changelog(&mut storage, DUMMY_KEY, 3), Ok(false));
    }

    #[test]
    fn may_load_at_height() {
        let mut storage = MockStorage::new();

        assert_eq!(
            NEVER.may_load_at_height(&storage, DUMMY_KEY, 3),
            Err(StdError::not_found("checkpoint"))
        );
        assert_eq!(EVERY.may_load_at_height(&storage, DUMMY_KEY, 3), Ok(None));
        //assert_eq!(
        //    SELECT.may_load_at_height(&storage, DUMMY_KEY, 3),
        //    Err(StdError::not_found("checkpoint"))
        //);

        // Add a checkpoint at 3
        NEVER.add_checkpoint(&mut storage, 3).unwrap();
        EVERY.add_checkpoint(&mut storage, 3).unwrap();
        //        SELECT.add_checkpoint(&mut storage, 3).unwrap();

        assert_eq!(
            NEVER.may_load_at_height(&storage, DUMMY_KEY, 3),
            Err(StdError::not_found("checkpoint"))
        );
        assert_eq!(EVERY.may_load_at_height(&storage, DUMMY_KEY, 3), Ok(None));
        //        assert_eq!(SELECT.may_load_at_height(&storage, DUMMY_KEY, 3), Ok(None));

        // Write a changelog at 3
        NEVER
            .write_changelog(&mut storage, DUMMY_KEY, 3, Some(100))
            .unwrap();
        EVERY
            .write_changelog(&mut storage, DUMMY_KEY, 3, Some(101))
            .unwrap();
        //SELECT
        //    .write_changelog(&mut storage, DUMMY_KEY, 3, Some(102))
        //    .unwrap();

        assert_eq!(
            NEVER.may_load_at_height(&storage, DUMMY_KEY, 3),
            Err(StdError::not_found("checkpoint"))
        );
        assert_eq!(
            EVERY.may_load_at_height(&storage, DUMMY_KEY, 3),
            Ok(Some(Some(101)))
        );
        //assert_eq!(
        //    SELECT.may_load_at_height(&storage, DUMMY_KEY, 3),
        //    Ok(Some(Some(102)))
        //);
        // Check that may_load_at_height at a previous value will return the first change after that.
        // (Only with EVERY).
        assert_eq!(
            NEVER.may_load_at_height(&storage, DUMMY_KEY, 2),
            Err(StdError::not_found("checkpoint"))
        );
        assert_eq!(
            EVERY.may_load_at_height(&storage, DUMMY_KEY, 2),
            Ok(Some(Some(101)))
        );
        //assert_eq!(
        //    SELECT.may_load_at_height(&storage, DUMMY_KEY, 2),
        //    Err(StdError::not_found("checkpoint"))
        //);

        // Write a changelog at 4, removing the value
        NEVER
            .write_changelog(&mut storage, DUMMY_KEY, 4, None)
            .unwrap();
        EVERY
            .write_changelog(&mut storage, DUMMY_KEY, 4, None)
            .unwrap();
        //SELECT
        //    .write_changelog(&mut storage, DUMMY_KEY, 4, None)
        //    .unwrap();
        // And add a checkpoint at 4
        NEVER.add_checkpoint(&mut storage, 4).unwrap();
        EVERY.add_checkpoint(&mut storage, 4).unwrap();
        //        SELECT.add_checkpoint(&mut storage, 4).unwrap();

        assert_eq!(
            NEVER.may_load_at_height(&storage, DUMMY_KEY, 4),
            Err(StdError::not_found("checkpoint"))
        );
        assert_eq!(
            EVERY.may_load_at_height(&storage, DUMMY_KEY, 4),
            Ok(Some(None))
        );
        //assert_eq!(
        //    SELECT.may_load_at_height(&storage, DUMMY_KEY, 4),
        //    Ok(Some(None))
        //);

        // Confirm old value at 3
        assert_eq!(
            NEVER.may_load_at_height(&storage, DUMMY_KEY, 3),
            Err(StdError::not_found("checkpoint"))
        );
        assert_eq!(
            EVERY.may_load_at_height(&storage, DUMMY_KEY, 3),
            Ok(Some(Some(101)))
        );
        //assert_eq!(
        //    SELECT.may_load_at_height(&storage, DUMMY_KEY, 3),
        //    Ok(Some(Some(102)))
        //);
    }
}
