use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::ops::Deref;

use cosmwasm_std::{to_binary, Addr, CosmosMsg, StdResult, WasmMsg};
use cw4::{Cw4Contract, Member};

use crate::msg::ExecuteMsg;

/// Cw4GroupContract is a wrapper around Cw4Contract that provides a lot of helpers
/// for working with cw4-group contracts.
///
/// It extends Cw4Contract to add the extra calls from cw4-group.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, JsonSchema)]
pub struct Cw4GroupContract(pub Cw4Contract);

impl Deref for Cw4GroupContract {
    type Target = Cw4Contract;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Cw4GroupContract {
    pub fn new(addr: Addr, code_hash: String) -> Self {
        Cw4GroupContract(Cw4Contract { addr, code_hash })
    }

    fn encode_msg(&self, msg: ExecuteMsg) -> StdResult<CosmosMsg> {
        Ok(WasmMsg::Execute {
            contract_addr: self.addr().into(),
            code_hash: self.code_hash.clone(),
            msg: to_binary(&msg)?,
            funds: vec![],
        }
        .into())
    }

    pub fn update_members(
        &self,
        remove: Vec<String>,
        add: Vec<Member>,
        callback_code_hash: Option<String>,
    ) -> StdResult<CosmosMsg> {
        let msg = ExecuteMsg::UpdateMembers {
            remove,
            add,
            callback_code_hash,
        };
        self.encode_msg(msg)
    }
}
