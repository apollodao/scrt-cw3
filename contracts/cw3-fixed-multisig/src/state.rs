use std::{any::type_name, marker::PhantomData};

use schemars::JsonSchema;
use serde::{de::DeserializeOwned, Deserialize, Serialize};

use cosmwasm_std::{
    Addr, Binary, BlockInfo, CosmosMsg, Decimal, Empty, OverflowError, OverflowOperation, StdError,
    StdResult, Storage, Uint128,
};

use cw3::{Status, Vote};
//use cw_storage_plus::{Item, Map};
use cw_utils::{Duration, Expiration, Threshold};
use secret_toolkit::{
    serialization::{Bincode2, Serde},
    storage::{AppendStore, Item, Keymap as Map},
};

// we multiply by this when calculating needed_votes in order to round up properly
// Note: `10u128.pow(9)` fails as "u128::pow` is not yet stable as a const fn"
const PRECISION_FACTOR: u128 = 1_000_000_000;

#[derive(Serialize, Deserialize, Clone, PartialEq, JsonSchema, Debug)]
pub struct Config {
    pub threshold: Threshold,
    pub total_weight: u64,
    pub max_voting_period: Duration,
}

#[derive(Serialize, Deserialize, Clone, PartialEq, JsonSchema, Debug)]
pub struct Proposal {
    pub title: String,
    pub description: String,
    pub start_height: u64,
    pub expires: Expiration,
    pub msgs: Vec<CosmosMsg<Empty>>,
    pub status: Status,
    /// pass requirements
    pub threshold: Threshold,
    // the total weight when the proposal started (used to calculate percentages)
    pub total_weight: u64,
    // summary of existing votes
    pub votes: Votes,
}

impl Proposal {
    /// current_status is non-mutable and returns what the status should be.
    /// (designed for queries)
    pub fn current_status(&self, block: &BlockInfo) -> Status {
        let mut status = self.status;

        // if open, check if voting is passed or timed out
        if status == Status::Open && self.is_passed(block) {
            status = Status::Passed;
        }
        if status == Status::Open && (self.is_rejected(block) || self.expires.is_expired(block)) {
            status = Status::Rejected;
        }

        status
    }

    /// update_status sets the status of the proposal to current_status.
    /// (designed for handler logic)
    pub fn update_status(&mut self, block: &BlockInfo) {
        self.status = self.current_status(block);
    }

    /// Returns true if this proposal is sure to pass (even before expiration, if no future
    /// sequence of possible votes could cause it to fail).
    pub fn is_passed(&self, block: &BlockInfo) -> bool {
        match self.threshold {
            Threshold::AbsoluteCount {
                weight: weight_needed,
            } => self.votes.yes >= weight_needed,
            Threshold::AbsolutePercentage {
                percentage: percentage_needed,
            } => {
                self.votes.yes
                    >= votes_needed(self.total_weight - self.votes.abstain, percentage_needed)
            }
            Threshold::ThresholdQuorum { threshold, quorum } => {
                // we always require the quorum
                if self.votes.total() < votes_needed(self.total_weight, quorum) {
                    return false;
                }
                if self.expires.is_expired(block) {
                    // If expired, we compare vote_count against the total number of votes (minus abstain).
                    let opinions = self.votes.total() - self.votes.abstain;
                    self.votes.yes >= votes_needed(opinions, threshold)
                } else {
                    // If not expired, we must assume all non-votes will be cast against
                    let possible_opinions = self.total_weight - self.votes.abstain;
                    self.votes.yes >= votes_needed(possible_opinions, threshold)
                }
            }
        }
    }

    /// Returns true if this proposal is sure to be rejected (even before expiration, if
    /// no future sequence of possible votes could cause it to pass).
    pub fn is_rejected(&self, block: &BlockInfo) -> bool {
        match self.threshold {
            Threshold::AbsoluteCount {
                weight: weight_needed,
            } => {
                let weight = self.total_weight - weight_needed;
                self.votes.no > weight
            }
            Threshold::AbsolutePercentage {
                percentage: percentage_needed,
            } => {
                self.votes.no
                    > votes_needed(
                        self.total_weight - self.votes.abstain,
                        Decimal::one() - percentage_needed,
                    )
            }
            Threshold::ThresholdQuorum {
                threshold,
                quorum: _,
            } => {
                if self.expires.is_expired(block) {
                    // If expired, we compare vote_count against the total number of votes (minus abstain).
                    let opinions = self.votes.total() - self.votes.abstain;
                    self.votes.no > votes_needed(opinions, Decimal::one() - threshold)
                } else {
                    // If not expired, we must assume all non-votes will be cast for
                    let possible_opinions = self.total_weight - self.votes.abstain;
                    self.votes.no > votes_needed(possible_opinions, Decimal::one() - threshold)
                }
            }
        }
    }
}

// weight of votes for each option
#[derive(Serialize, Deserialize, Clone, PartialEq, JsonSchema, Debug)]
pub struct Votes {
    pub yes: u64,
    pub no: u64,
    pub abstain: u64,
    pub veto: u64,
}

impl Votes {
    /// sum of all votes
    pub fn total(&self) -> u64 {
        self.yes + self.no + self.abstain + self.veto
    }

    /// create it with a yes vote for this much
    pub fn yes(init_weight: u64) -> Self {
        Votes {
            yes: init_weight,
            no: 0,
            abstain: 0,
            veto: 0,
        }
    }

    pub fn add_vote(&mut self, vote: Vote, weight: u64) {
        match vote {
            Vote::Yes => self.yes += weight,
            Vote::Abstain => self.abstain += weight,
            Vote::No => self.no += weight,
            Vote::Veto => self.veto += weight,
        }
    }
}

// this is a helper function so Decimal works with u64 rather than Uint128
// also, we must *round up* here, as we need 8, not 7 votes to reach 50% of 15 total
fn votes_needed(weight: u64, percentage: Decimal) -> u64 {
    let applied = percentage * Uint128::new(PRECISION_FACTOR * weight as u128);
    // Divide by PRECISION_FACTOR, rounding up to the nearest integer
    ((applied.u128() + PRECISION_FACTOR - 1) / PRECISION_FACTOR) as u64
}

// we cast a ballot with our chosen vote and a given weight
// stored under the key that voted
#[derive(Serialize, Deserialize, Clone, PartialEq, JsonSchema, Debug)]
pub struct Ballot {
    pub weight: u64,
    pub vote: Vote,
}

type ProposalID = u64;
type VoterWeight = u64;

// unique items
pub const CONFIG: Item<Config> = Item::new(b"config");
pub const PROPOSAL_COUNT: Item<u64> = Item::new(b"proposal_count");

// binary search tree (heap)
pub static VOTER_ADDRESSES: BinarySearchTree<Addr> = BinarySearchTree::new(b"voter_addresses");

// maps
pub const PROPOSALS: Map<ProposalID, Proposal> = Map::new(b"proposals");
pub const VOTERS: Map<Addr, VoterWeight> = Map::new(b"voters");
// suffixed map
pub const BALLOTS: Map<Addr, Ballot> = Map::new(b"votes");

pub fn next_id(store: &mut dyn Storage) -> StdResult<u64> {
    let id: u64 = PROPOSAL_COUNT.may_load(store)?.unwrap_or_default() + 1;
    PROPOSAL_COUNT.save(store, &id)?;
    Ok(id)
}

#[derive(Debug)]
pub struct BinarySearchTree<'a, T, Ser = Bincode2>
where
    T: Serialize + DeserializeOwned + PartialEq + PartialOrd + std::fmt::Debug,
    Ser: Serde,
{
    key: &'a [u8],
    prefix: Option<Vec<u8>>,
    item_type: PhantomData<T>,
    serialization_type: PhantomData<Ser>,
}

pub struct BinarySearchTreeIterator<'a, T, Ser = Bincode2>
where
    T: Serialize + DeserializeOwned + PartialEq + PartialOrd + std::fmt::Debug,
    Ser: Serde,
{
    current: BinarySearchTree<'a, T, Ser>,
    storage: &'a dyn Storage,
    stack: Vec<BinarySearchTree<'a, T, Ser>>,
}

impl<'a, T, Ser> BinarySearchTree<'a, T, Ser>
where
    T: Serialize + DeserializeOwned + PartialEq + PartialOrd + std::fmt::Debug,
    Ser: Serde + std::fmt::Debug,
{
    pub const fn new(name: &'a [u8]) -> Self {
        Self {
            key: name,
            prefix: None,
            item_type: PhantomData,
            serialization_type: PhantomData,
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
    pub fn iter(&self, storage: &'a dyn Storage) -> BinarySearchTreeIterator<'a, T, Ser> {
        BinarySearchTreeIterator::new(self.clone(), storage)
    }

    // @next figure out how/if possible to iterate from specified starting node
    // idea: check if node is right or left of parent - add is_left()/is_right()
    pub fn iter_from(
        &self,
        storage: &'a dyn Storage,
        elem: &T,
    ) -> StdResult<BinarySearchTreeIterator<'a, T, Ser>> {
        let start = match self.find(storage, elem) {
            Ok((key, true)) => Ok(key),
            Ok((_, false)) => Err(StdError::GenericErr {
                msg: "Starting element not found".to_string(),
            }),
            Err(e) => Err(e),
        }?;
        let mut stack = vec![];
        for i in self.key.len()..start.len() + 1 {
            let key = &start[0..i];
            if let Some(next_branch) = start.get(i) {
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
        println!(
            "STACK GOING INTO ITERATOR {:#?}",
            stack
                .iter()
                .map(|n| n.load(storage).unwrap())
                .collect::<Vec<_>>()
        );
        let iter = BinarySearchTreeIterator {
            current: BinarySearchTree::new(b"iter_root"),
            storage,
            stack,
        };
        println!("Current before start: {:#?}", iter.current);
        Ok(iter)
    }
}

impl<'a, T, Ser> BinarySearchTreeIterator<'a, T, Ser>
where
    T: Serialize + DeserializeOwned + PartialEq + PartialOrd + std::fmt::Debug,
    Ser: Serde,
{
    pub fn new(root: BinarySearchTree<'a, T, Ser>, storage: &'a dyn Storage) -> Self {
        let stack: Vec<BinarySearchTree<'a, T, Ser>> = vec![];
        Self {
            current: root,
            storage,
            stack,
        }
    }
}

impl<'a, T, Ser> Iterator for BinarySearchTreeIterator<'a, T, Ser>
where
    T: Serialize + DeserializeOwned + PartialEq + PartialOrd + std::fmt::Debug,
    Ser: Serde + std::fmt::Debug,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let mut item: Option<T> = None;
        while !self.stack.is_empty() || !self.current.is_empty(self.storage) {
            println!(
                "stack before {:#?}",
                self.stack
                    .iter()
                    .map(|n| n.load(self.storage).unwrap())
                    .collect::<Vec<_>>()
            );
            if !self.current.is_empty(self.storage) {
                self.stack.push(self.current.clone());
                println!(
                    "stack inbetween {:#?}",
                    self.stack
                        .iter()
                        .map(|n| n.load(self.storage).unwrap())
                        .collect::<Vec<_>>()
                );
                self.current = self.current.left();
            } else {
                // unwrap because stack cannot be empty here
                self.current = self.stack.pop().unwrap();
                println!(
                    "stack after {:#?}",
                    self.stack
                        .iter()
                        .map(|n| n.load(self.storage).unwrap())
                        .collect::<Vec<_>>()
                );
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
    use cosmwasm_std::testing::{mock_dependencies, mock_env};

    #[test]
    fn count_votes() {
        let mut votes = Votes::yes(5);
        votes.add_vote(Vote::No, 10);
        votes.add_vote(Vote::Veto, 20);
        votes.add_vote(Vote::Yes, 30);
        votes.add_vote(Vote::Abstain, 40);

        assert_eq!(votes.total(), 105);
        assert_eq!(votes.yes, 35);
        assert_eq!(votes.no, 10);
        assert_eq!(votes.veto, 20);
        assert_eq!(votes.abstain, 40);
    }

    #[test]
    // we ensure this rounds up (as it calculates needed votes)
    fn votes_needed_rounds_properly() {
        // round up right below 1
        assert_eq!(1, votes_needed(3, Decimal::permille(333)));
        // round up right over 1
        assert_eq!(2, votes_needed(3, Decimal::permille(334)));
        assert_eq!(11, votes_needed(30, Decimal::permille(334)));

        // exact matches don't round
        assert_eq!(17, votes_needed(34, Decimal::percent(50)));
        assert_eq!(12, votes_needed(48, Decimal::percent(25)));
    }

    fn setup_prop(
        threshold: Threshold,
        votes: Votes,
        total_weight: u64,
        is_expired: bool,
    ) -> (Proposal, BlockInfo) {
        let block = mock_env().block;
        let expires = match is_expired {
            true => Expiration::AtHeight(block.height - 5),
            false => Expiration::AtHeight(block.height + 100),
        };
        let prop = Proposal {
            title: "Demo".to_string(),
            description: "Info".to_string(),
            start_height: 100,
            expires,
            msgs: vec![],
            status: Status::Open,
            threshold,
            total_weight,
            votes,
        };

        (prop, block)
    }

    fn check_is_passed(
        threshold: Threshold,
        votes: Votes,
        total_weight: u64,
        is_expired: bool,
    ) -> bool {
        let (prop, block) = setup_prop(threshold, votes, total_weight, is_expired);
        prop.is_passed(&block)
    }

    fn check_is_rejected(
        threshold: Threshold,
        votes: Votes,
        total_weight: u64,
        is_expired: bool,
    ) -> bool {
        let (prop, block) = setup_prop(threshold, votes, total_weight, is_expired);
        prop.is_rejected(&block)
    }

    #[test]
    fn proposal_passed_absolute_count() {
        let fixed = Threshold::AbsoluteCount { weight: 10 };
        let mut votes = Votes::yes(7);
        votes.add_vote(Vote::Veto, 4);
        // same expired or not, total_weight or whatever
        assert!(!check_is_passed(fixed.clone(), votes.clone(), 30, false));
        assert!(!check_is_passed(fixed.clone(), votes.clone(), 30, true));
        // a few more yes votes and we are good
        votes.add_vote(Vote::Yes, 3);
        assert!(check_is_passed(fixed.clone(), votes.clone(), 30, false));
        assert!(check_is_passed(fixed, votes, 30, true));
    }

    #[test]
    fn proposal_rejected_absolute_count() {
        let fixed = Threshold::AbsoluteCount { weight: 10 };
        let mut votes = Votes::yes(0);
        votes.add_vote(Vote::Veto, 4);
        votes.add_vote(Vote::No, 7);
        // In order to reject the proposal we need no votes > 30 - 10, currently it is not rejected
        assert!(!check_is_rejected(fixed.clone(), votes.clone(), 30, false));
        assert!(!check_is_rejected(fixed.clone(), votes.clone(), 30, true));
        // 7 + 14 = 21 > 20, we can now reject
        votes.add_vote(Vote::No, 14);
        assert!(check_is_rejected(fixed.clone(), votes.clone(), 30, false));
        assert!(check_is_rejected(fixed, votes, 30, true));
    }

    #[test]
    fn proposal_passed_absolute_percentage() {
        let percent = Threshold::AbsolutePercentage {
            percentage: Decimal::percent(50),
        };
        let mut votes = Votes::yes(7);
        votes.add_vote(Vote::No, 4);
        votes.add_vote(Vote::Abstain, 2);
        // same expired or not, if yes >= ceiling(0.5 * (total - abstained))
        // 7 of (15-2) passes
        assert!(check_is_passed(percent.clone(), votes.clone(), 15, false));
        assert!(check_is_passed(percent.clone(), votes.clone(), 15, true));
        // but 7 of (17-2) fails
        assert!(!check_is_passed(percent.clone(), votes.clone(), 17, false));

        // if the total were a bit lower, this would pass
        assert!(check_is_passed(percent.clone(), votes.clone(), 14, false));
        assert!(check_is_passed(percent, votes, 14, true));
    }

    #[test]
    fn proposal_rejected_absolute_percentage() {
        let percent = Threshold::AbsolutePercentage {
            percentage: Decimal::percent(60),
        };

        // 4 YES, 7 NO, 2 ABSTAIN
        let mut votes = Votes::yes(4);
        votes.add_vote(Vote::No, 7);
        votes.add_vote(Vote::Abstain, 2);

        // 15 total voting power
        // we need no votes > 0.4 * 15, no votes > 6
        assert!(check_is_rejected(percent.clone(), votes.clone(), 15, false));
        assert!(check_is_rejected(percent.clone(), votes.clone(), 15, true));

        // 17 total voting power
        // we need no votes > 0.4 * 17, no votes > 6.8
        // still rejected
        assert!(check_is_rejected(percent.clone(), votes.clone(), 17, false));
        assert!(check_is_rejected(percent.clone(), votes.clone(), 17, true));

        // Not rejected if total weight is 20
        // as no votes > 0.4 * 18, no votes > 8
        assert!(!check_is_rejected(
            percent.clone(),
            votes.clone(),
            20,
            false
        ));
        assert!(!check_is_rejected(percent, votes.clone(), 20, true));
    }

    #[test]
    fn proposal_passed_quorum() {
        let quorum = Threshold::ThresholdQuorum {
            threshold: Decimal::percent(50),
            quorum: Decimal::percent(40),
        };
        // all non-yes votes are counted for quorum
        let passing = Votes {
            yes: 7,
            no: 3,
            abstain: 2,
            veto: 1,
        };
        // abstain votes are not counted for threshold => yes / (yes + no + veto)
        let passes_ignoring_abstain = Votes {
            yes: 6,
            no: 4,
            abstain: 5,
            veto: 2,
        };
        // fails any way you look at it
        let failing = Votes {
            yes: 6,
            no: 5,
            abstain: 2,
            veto: 2,
        };

        // first, expired (voting period over)
        // over quorum (40% of 30 = 12), over threshold (7/11 > 50%)
        assert!(check_is_passed(quorum.clone(), passing.clone(), 30, true));
        // under quorum it is not passing (40% of 33 = 13.2 > 13)
        assert!(!check_is_passed(quorum.clone(), passing.clone(), 33, true));
        // over quorum, threshold passes if we ignore abstain
        // 17 total votes w/ abstain => 40% quorum of 40 total
        // 6 yes / (6 yes + 4 no + 2 votes) => 50% threshold
        assert!(check_is_passed(
            quorum.clone(),
            passes_ignoring_abstain.clone(),
            40,
            true
        ));
        // over quorum, but under threshold fails also
        assert!(!check_is_passed(quorum.clone(), failing, 20, true));

        // now, check with open voting period
        // would pass if closed, but fail here, as remaining votes no -> fail
        assert!(!check_is_passed(quorum.clone(), passing.clone(), 30, false));
        assert!(!check_is_passed(
            quorum.clone(),
            passes_ignoring_abstain.clone(),
            40,
            false
        ));
        // if we have threshold * total_weight as yes votes this must pass
        assert!(check_is_passed(quorum.clone(), passing.clone(), 14, false));
        // all votes have been cast, some abstain
        assert!(check_is_passed(
            quorum.clone(),
            passes_ignoring_abstain,
            17,
            false
        ));
        // 3 votes uncast, if they all vote no, we have 7 yes, 7 no+veto, 2 abstain (out of 16)
        assert!(check_is_passed(quorum, passing, 16, false));
    }

    #[test]
    fn proposal_rejected_quorum() {
        let quorum = Threshold::ThresholdQuorum {
            threshold: Decimal::percent(60),
            quorum: Decimal::percent(40),
        };
        // all non-yes votes are counted for quorum
        let rejecting = Votes {
            yes: 3,
            no: 7,
            abstain: 2,
            veto: 1,
        };
        // abstain votes are not counted for threshold => yes / (yes + no + veto)
        let rejected_ignoring_abstain = Votes {
            yes: 4,
            no: 6,
            abstain: 5,
            veto: 2,
        };
        // fails any way you look at it
        let failing = Votes {
            yes: 5,
            no: 5,
            abstain: 2,
            veto: 3,
        };

        // first, expired (voting period over)
        // over quorum (40% of 30 = 12, 13 votes casted)
        // 13 - 2 abstains = 11
        // we need no votes > 0.4 * 11, no votes > 4.4
        // We can reject this
        assert!(check_is_rejected(
            quorum.clone(),
            rejecting.clone(),
            30,
            true
        ));

        // Under quorum and cannot reject as it is not expired
        assert!(!check_is_rejected(
            quorum.clone(),
            rejecting.clone(),
            50,
            false
        ));
        // Can reject when expired.
        assert!(check_is_rejected(
            quorum.clone(),
            rejecting.clone(),
            50,
            true
        ));

        // Check edgecase where quorum is not met but we can reject
        // 35% vote no
        let quorum_edgecase = Threshold::ThresholdQuorum {
            threshold: Decimal::percent(67),
            quorum: Decimal::percent(40),
        };
        assert!(check_is_rejected(
            quorum_edgecase,
            Votes {
                yes: 15,
                no: 35,
                abstain: 0,
                veto: 10
            },
            100,
            true
        ));

        // over quorum, threshold passes if we ignore abstain
        // 17 total votes > 40% quorum
        // 6 no > 0.4 * (6 no + 4 yes + 2 votes)
        // 6 > 4.8
        // we can reject
        assert!(check_is_rejected(
            quorum.clone(),
            rejected_ignoring_abstain.clone(),
            40,
            true
        ));

        // over quorum
        // total opinions due to abstains: 13
        // no votes > 0.4 * 13, no votes > 5 to reject, we have 5 exactly so cannot reject
        assert!(!check_is_rejected(quorum.clone(), failing, 20, true));

        // voting period on going
        // over quorum (40% of 14 = 5, 13 votes casted)
        // 13 - 2 abstains = 11
        // we need no votes > 0.4 * 11, no votes > 4.4
        // We can reject this even when it hasn't expired
        assert!(check_is_rejected(
            quorum.clone(),
            rejecting.clone(),
            14,
            false
        ));
        // all votes have been cast, some abstain
        // voting period on going
        // over quorum (40% of 17 = 7, 17 casted_
        // 17 - 5 = 12 total opinions
        // we need no votes > 0.4 * 12, no votes > 4.8
        // We can reject this even when it hasn't expired
        assert!(check_is_rejected(
            quorum.clone(),
            rejected_ignoring_abstain,
            17,
            false
        ));

        // 3 votes uncast, if they all vote yes, we have 7 no, 7 yes+veto, 2 abstain (out of 16)
        assert!(check_is_rejected(quorum, rejecting, 16, false));
    }

    #[test]
    fn quorum_edge_cases() {
        // when we pass absolute threshold (everyone else voting no, we pass), but still don't hit quorum
        let quorum = Threshold::ThresholdQuorum {
            threshold: Decimal::percent(60),
            quorum: Decimal::percent(80),
        };

        // try 9 yes, 1 no (out of 15) -> 90% voter threshold, 60% absolute threshold, still no quorum
        // doesn't matter if expired or not
        let missing_voters = Votes {
            yes: 9,
            no: 1,
            abstain: 0,
            veto: 0,
        };
        assert!(!check_is_passed(
            quorum.clone(),
            missing_voters.clone(),
            15,
            false
        ));
        assert!(!check_is_passed(quorum.clone(), missing_voters, 15, true));

        // 1 less yes, 3 vetos and this passes only when expired
        let wait_til_expired = Votes {
            yes: 8,
            no: 1,
            abstain: 0,
            veto: 3,
        };
        assert!(!check_is_passed(
            quorum.clone(),
            wait_til_expired.clone(),
            15,
            false
        ));
        assert!(check_is_passed(quorum.clone(), wait_til_expired, 15, true));

        // 9 yes and 3 nos passes early
        let passes_early = Votes {
            yes: 9,
            no: 3,
            abstain: 0,
            veto: 0,
        };
        assert!(check_is_passed(
            quorum.clone(),
            passes_early.clone(),
            15,
            false
        ));
        assert!(check_is_passed(quorum, passes_early, 15, true));
    }

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
            //println!("Item: {:?}", storage.get(&res.unwrap()).unwrap());
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
            //println!("Item: {:?}", storage.get(&res.unwrap()).unwrap());
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
