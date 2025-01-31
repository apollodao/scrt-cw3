use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

use cosmwasm_std::{to_binary, Binary, CosmosMsg, StdResult, WasmMsg};

/// MemberDiff shows the old and new states for a given cw4 member
/// They cannot both be None.
/// old = None, new = Some -> Insert
/// old = Some, new = Some -> Update
/// old = Some, new = None -> Delete
#[derive(Serialize, Deserialize, Clone, PartialEq, JsonSchema, Debug)]
pub struct MemberDiff {
    pub key: String,
    pub old: Option<u64>,
    pub new: Option<u64>,
}

impl MemberDiff {
    pub fn new<T: Into<String>>(addr: T, old_weight: Option<u64>, new_weight: Option<u64>) -> Self {
        MemberDiff {
            key: addr.into(),
            old: old_weight,
            new: new_weight,
        }
    }
}

/// MemberChangedHookMsg should be de/serialized under `MemberChangedHook()` variant in a ExecuteMsg.
/// This contains a list of all diffs on the given transaction.
#[derive(Serialize, Deserialize, Clone, PartialEq, JsonSchema, Debug)]
#[serde(rename_all = "snake_case")]
pub struct MemberChangedHookMsg {
    pub diffs: Vec<MemberDiff>,
}

impl MemberChangedHookMsg {
    pub fn one(diff: MemberDiff) -> Self {
        MemberChangedHookMsg { diffs: vec![diff] }
    }

    pub fn new(diffs: Vec<MemberDiff>) -> Self {
        MemberChangedHookMsg { diffs }
    }

    /// serializes the message
    pub fn into_binary(self) -> StdResult<Binary> {
        let msg = MemberChangedExecuteMsg::MemberChangedHook(self);
        to_binary(&msg)
    }

    /// creates a cosmos_msg sending this struct to the named contract
    pub fn into_cosmos_msg<T: Into<String>>(
        self,
        receiver_hash: String,
        contract_addr: T,
    ) -> StdResult<CosmosMsg> {
        let msg = self.into_binary()?;
        let execute = WasmMsg::Execute {
            contract_addr: contract_addr.into(),
            code_hash: receiver_hash,
            msg,
            funds: vec![],
        };
        Ok(execute.into())
    }
}

// This is just a helper to properly serialize the above message
#[derive(Serialize, Deserialize, Clone, PartialEq, JsonSchema, Debug)]
#[serde(rename_all = "snake_case")]
enum MemberChangedExecuteMsg {
    MemberChangedHook(MemberChangedHookMsg),
}
