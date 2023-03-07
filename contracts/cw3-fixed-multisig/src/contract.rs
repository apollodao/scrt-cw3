use std::cmp::Ordering;

use cosmwasm_std::entry_point;
use cosmwasm_std::{
    to_binary, Addr, Binary, BlockInfo, CosmosMsg, Deps, DepsMut, Empty, Env, MessageInfo,
    Response, StdError, StdResult, Storage,
};
use secret_toolkit::permit::validate;
use secret_toolkit::utils::{pad_handle_result, pad_query_result};

use cw3::{
    ProposalListResponse, ProposalResponse, Status, Vote, VoteInfo, VoteListResponse, VoteResponse,
    VoterDetail, VoterListResponse, VoterResponse,
};
use cw_utils::{Expiration, ThresholdResponse};

use crate::error::ContractError;
use crate::msg::{ExecuteMsg, InstantiateMsg, QueryMsg};
use crate::state::{
    next_id, Ballot, Config, Proposal, Votes, BALLOTS, CONFIG, PREFIX_REVOKED_PERMITS, PROPOSALS,
    RESPONSE_BLOCK_SIZE, VOTERS, VOTER_ADDRESSES,
};

#[entry_point]
pub fn instantiate(
    deps: DepsMut,
    _env: Env,
    _info: MessageInfo,
    msg: InstantiateMsg,
) -> Result<Response, ContractError> {
    if msg.voters.is_empty() {
        return Err(ContractError::NoVoters {});
    }
    let total_weight = msg.voters.iter().map(|v| v.weight).sum();

    msg.threshold.validate(total_weight)?;

    let cfg = Config {
        threshold: msg.threshold,
        total_weight,
        max_voting_period: msg.max_voting_period,
    };
    CONFIG
        .save(deps.storage, &cfg)
        .map_err(|e| ContractError::Std(e))?;

    // add all voters
    for voter in msg.voters.iter() {
        let key = deps.api.addr_validate(&voter.addr)?;
        VOTERS.insert(deps.storage, &key, &voter.weight)?;
        VOTER_ADDRESSES.insert(deps.storage, &key)?;
    }
    Ok(Response::default())
}

#[entry_point]
pub fn execute(
    deps: DepsMut,
    env: Env,
    info: MessageInfo,
    msg: ExecuteMsg,
) -> Result<Response<Empty>, ContractError> {
    let response = match msg {
        ExecuteMsg::Propose {
            title,
            description,
            msgs,
            latest,
        } => execute_propose(deps, env, info, title, description, msgs, latest),
        ExecuteMsg::Vote { proposal_id, vote } => execute_vote(deps, env, info, proposal_id, vote),
        ExecuteMsg::Execute { proposal_id } => execute_execute(deps, env, info, proposal_id),
        ExecuteMsg::Close { proposal_id } => execute_close(deps, env, info, proposal_id),
    };
    pad_handle_result(response, RESPONSE_BLOCK_SIZE)
}

pub fn execute_propose(
    deps: DepsMut,
    env: Env,
    info: MessageInfo,
    title: String,
    description: String,
    msgs: Vec<CosmosMsg>,
    // we ignore earliest
    latest: Option<Expiration>,
) -> Result<Response<Empty>, ContractError> {
    // only members of the multisig can create a proposal
    let vote_power = VOTERS
        .get(deps.storage, &info.sender)
        .ok_or(ContractError::Unauthorized {})?;

    let cfg = CONFIG.load(deps.storage)?;

    // max expires also used as default
    let max_expires = cfg.max_voting_period.after(&env.block);
    let mut expires = latest.unwrap_or(max_expires);
    let comp = expires.partial_cmp(&max_expires);
    if let Some(Ordering::Greater) = comp {
        expires = max_expires;
    } else if comp.is_none() {
        return Err(ContractError::WrongExpiration {});
    }

    // create a proposal
    let mut prop = Proposal {
        title,
        description,
        start_height: env.block.height,
        expires,
        msgs,
        status: Status::Open,
        votes: Votes::yes(vote_power),
        threshold: cfg.threshold,
        total_weight: cfg.total_weight,
    };
    prop.update_status(&env.block);
    let id = next_id(deps.storage)?;
    PROPOSALS.insert(deps.storage, &id, &prop)?;

    // add the first yes vote from voter
    let ballot = Ballot {
        weight: vote_power,
        vote: Vote::Yes,
    };
    BALLOTS
        .add_suffix(&id.to_ne_bytes())
        .insert(deps.storage, &info.sender, &ballot)?;

    Ok(Response::new()
        .add_attribute("action", "propose")
        .add_attribute("sender", info.sender)
        .add_attribute("proposal_id", id.to_string())
        .add_attribute("status", format!("{:?}", prop.status)))
}

pub fn execute_vote(
    deps: DepsMut,
    env: Env,
    info: MessageInfo,
    proposal_id: u64,
    vote: Vote,
) -> Result<Response<Empty>, ContractError> {
    // only members of the multisig with weight >= 1 can vote
    let vote_power = match VOTERS.get(deps.storage, &info.sender) {
        Some(power) if power >= 1 => power,
        _ => return Err(ContractError::Unauthorized {}),
    };

    // ensure proposal exists and can be voted on
    let mut prop = get_proposal(deps.storage, &proposal_id)?;
    if prop.status != Status::Open {
        return Err(ContractError::NotOpen {});
    }
    if prop.expires.is_expired(&env.block) {
        return Err(ContractError::Expired {});
    }

    // cast vote if no vote previously cast
    let suffix = proposal_id.to_ne_bytes();
    let ballot = match BALLOTS.add_suffix(&suffix).get(deps.storage, &info.sender) {
        Some(_) => Err(ContractError::AlreadyVoted {}),
        None => Ok(Ballot {
            weight: vote_power,
            vote,
        }),
    }?;
    BALLOTS
        .add_suffix(&suffix)
        .insert(deps.storage, &info.sender, &ballot)?;

    // update vote tally
    prop.votes.add_vote(vote, vote_power);
    prop.update_status(&env.block);
    PROPOSALS.insert(deps.storage, &proposal_id, &prop)?;

    Ok(Response::new()
        .add_attribute("action", "vote")
        .add_attribute("sender", info.sender)
        .add_attribute("proposal_id", proposal_id.to_string())
        .add_attribute("status", format!("{:?}", prop.status)))
}

pub fn execute_execute(
    deps: DepsMut,
    _env: Env,
    info: MessageInfo,
    proposal_id: u64,
) -> Result<Response, ContractError> {
    // anyone can trigger this if the vote passed

    let mut prop = get_proposal(deps.storage, &proposal_id)?;
    // we allow execution even after the proposal "expiration" as long as all vote come in before
    // that point. If it was approved on time, it can be executed any time.
    if prop.status != Status::Passed {
        return Err(ContractError::WrongExecuteStatus {});
    }

    // set it to executed
    prop.status = Status::Executed;
    PROPOSALS.insert(deps.storage, &proposal_id, &prop)?;

    // dispatch all proposed messages
    Ok(Response::new()
        .add_messages(prop.msgs)
        .add_attribute("action", "execute")
        .add_attribute("sender", info.sender)
        .add_attribute("proposal_id", proposal_id.to_string()))
}

pub fn execute_close(
    deps: DepsMut,
    env: Env,
    info: MessageInfo,
    proposal_id: u64,
) -> Result<Response<Empty>, ContractError> {
    // anyone can trigger this if the vote passed

    let mut prop = get_proposal(deps.storage, &proposal_id)?;
    if [Status::Executed, Status::Rejected, Status::Passed]
        .iter()
        .any(|x| *x == prop.status)
    {
        return Err(ContractError::WrongCloseStatus {});
    }
    if !prop.expires.is_expired(&env.block) {
        return Err(ContractError::NotExpired {});
    }

    // set it to failed
    prop.status = Status::Rejected;
    PROPOSALS.insert(deps.storage, &proposal_id, &prop)?;

    Ok(Response::new()
        .add_attribute("action", "close")
        .add_attribute("sender", info.sender)
        .add_attribute("proposal_id", proposal_id.to_string()))
}

#[entry_point]
pub fn query(deps: Deps, env: Env, msg: QueryMsg) -> StdResult<Binary> {
    let response = if let QueryMsg::WithPermit { permit, msg } = msg {
        let addr = deps.api.addr_validate(
            validate(deps, PREFIX_REVOKED_PERMITS, &permit, String::new(), None)?.as_str(),
        )?;
        if is_voter(deps, &addr)? {
            perform_query(deps, env, *msg)
        } else {
            Err(StdError::generic_err(
                format!(
                    "Address '{}' is not a registerd voter and thus not permitted to query.",
                    addr
                )
                .as_str(),
            ))
        }
    } else {
        Err(StdError::generic_err(
            "A permit is required to make queries.",
        ))
    };
    pad_query_result(response, RESPONSE_BLOCK_SIZE)
}

fn perform_query(deps: Deps, env: Env, msg: QueryMsg) -> StdResult<Binary> {
    match msg {
        QueryMsg::Threshold {} => to_binary(&query_threshold(deps)?),
        QueryMsg::Proposal { proposal_id } => to_binary(&query_proposal(deps, env, proposal_id)?),
        QueryMsg::Vote { proposal_id, voter } => to_binary(&query_vote(deps, proposal_id, voter)?),
        QueryMsg::ListProposals { start_after, limit } => {
            let reverse = false;
            to_binary(&list_proposals(deps, env, reverse, start_after, limit)?)
        }
        QueryMsg::ReverseProposals {
            start_before,
            limit,
        } => {
            let reverse = true;
            to_binary(&list_proposals(deps, env, reverse, start_before, limit)?)
        }
        QueryMsg::ListVotes {
            proposal_id,
            start_after,
            limit,
        } => to_binary(&list_votes(deps, proposal_id, start_after, limit)?),
        QueryMsg::Voter { address } => to_binary(&query_voter(deps, address)?),
        QueryMsg::ListVoters { start_after, limit } => {
            to_binary(&list_voters(deps, start_after, limit)?)
        },
        _ => Err(StdError::generic_err("Recursive query message. A 'with_permit' message cannot contain a 'with_permit' message.")),
    }
}

fn query_threshold(deps: Deps) -> StdResult<ThresholdResponse> {
    let cfg = CONFIG.load(deps.storage)?;
    Ok(cfg.threshold.to_response(cfg.total_weight))
}

fn query_proposal(deps: Deps, env: Env, id: u64) -> StdResult<ProposalResponse> {
    let prop = get_proposal(deps.storage, &id)?;
    let status = prop.current_status(&env.block);
    let threshold = prop.threshold.to_response(prop.total_weight);
    Ok(ProposalResponse {
        id,
        title: prop.title,
        description: prop.description,
        msgs: prop.msgs,
        status,
        expires: prop.expires,
        threshold,
    })
}

// settings for pagination
const MAX_LIMIT: u32 = 30;
const DEFAULT_LIMIT: u32 = 10;

fn list_proposals(
    deps: Deps,
    env: Env,
    reverse: bool,
    starting_point: Option<u64>,
    limit: Option<u32>,
) -> StdResult<ProposalListResponse> {
    let limit = limit.unwrap_or(DEFAULT_LIMIT).min(MAX_LIMIT) as usize;
    let start = match starting_point {
        Some(u) => u + 1,
        None => 0,
    } as usize;

    let page_keys: Vec<u64> = {
        if reverse {
            PROPOSALS
                .iter_keys(deps.storage)?
                .rev()
                .skip(start)
                .take(limit)
                .collect::<StdResult<Vec<_>>>()
        } else {
            PROPOSALS
                .iter_keys(deps.storage)?
                .skip(start)
                .take(limit)
                .collect::<StdResult<Vec<_>>>()
        }?
    };

    let page = page_keys
        .iter()
        .map(|id| {
            Ok(proposal_to_response(
                &env.block,
                (*id, get_proposal(deps.storage, &id)?),
            ))
        })
        .collect::<StdResult<Vec<_>>>()?;

    Ok(ProposalListResponse { proposals: page })
}

fn query_vote(deps: Deps, proposal_id: u64, voter: String) -> StdResult<VoteResponse> {
    let voter = deps.api.addr_validate(&voter)?;
    let ballot = BALLOTS
        .add_suffix(&proposal_id.to_ne_bytes())
        .get(deps.storage, &voter);
    let vote = ballot.map(|b| VoteInfo {
        proposal_id,
        voter: voter.into(),
        vote: b.vote,
        weight: b.weight,
    });
    Ok(VoteResponse { vote })
}

fn list_votes(
    deps: Deps,
    proposal_id: u64,
    start_after: Option<String>,
    limit: Option<u32>,
) -> StdResult<VoteListResponse> {
    let limit = limit.unwrap_or(DEFAULT_LIMIT).min(MAX_LIMIT) as usize;
    let start_address = start_after.map(|addr| Addr::unchecked(addr));

    let suffix = proposal_id.to_ne_bytes();
    let ballots = BALLOTS.add_suffix(&suffix);
    let addresses = match start_address {
        Some(addr) => VOTER_ADDRESSES.iter_from(deps.storage, &addr, true)?,
        None => VOTER_ADDRESSES.iter(deps.storage),
    };

    let mut votes = vec![];
    let mut ctr = 0;
    for addr in addresses {
        let ballot = match ballots.get(deps.storage, &addr) {
            Some(ballot) => ballot,
            None => continue,
        };
        votes.push(VoteInfo {
            proposal_id,
            voter: addr.into(),
            vote: ballot.vote,
            weight: ballot.weight,
        });
        ctr += 1;
        if ctr == limit {
            break;
        }
    }

    Ok(VoteListResponse { votes })
}

fn query_voter(deps: Deps, voter: String) -> StdResult<VoterResponse> {
    let voter = deps.api.addr_validate(&voter)?;
    let weight = VOTERS.get(deps.storage, &voter);
    Ok(VoterResponse { weight })
}

fn list_voters(
    deps: Deps,
    start_after: Option<String>,
    limit: Option<u32>,
) -> StdResult<VoterListResponse> {
    let limit = limit.unwrap_or(DEFAULT_LIMIT).min(MAX_LIMIT) as usize;
    let start_address = start_after.map(|addr| Addr::unchecked(addr));

    let addresses = match start_address {
        Some(addr) => VOTER_ADDRESSES.iter_from(deps.storage, &addr, true)?,
        None => VOTER_ADDRESSES.iter(deps.storage),
    };

    let mut voters = vec![];
    let mut ctr = 0;
    for addr in addresses {
        let weight = VOTERS
            .get(deps.storage, &addr)
            // If this error is returned, `VOTERS` is out of sync with `VOTER_ADDRESSES`, which shouldn't be possible
            .ok_or_else(|| StdError::not_found("Voter weight"))?;
        voters.push(VoterDetail {
            addr: addr.to_string(),
            weight,
        });
        ctr += 1;
        if ctr == limit {
            break;
        }
    }

    Ok(VoterListResponse { voters })
}

// Utils

pub fn is_voter(deps: Deps, addr: &Addr) -> StdResult<bool> {
    Ok(VOTER_ADDRESSES.find(deps.storage, addr)?.1)
}

fn proposal_to_response(block: &BlockInfo, item: (u64, Proposal)) -> ProposalResponse {
    let (id, prop) = item;
    let status = prop.current_status(block);
    let threshold = prop.threshold.to_response(prop.total_weight);
    ProposalResponse {
        id,
        title: prop.title,
        description: prop.description,
        msgs: prop.msgs,
        status,
        expires: prop.expires,
        threshold,
    }
}

fn get_proposal(store: &dyn Storage, id: &u64) -> StdResult<Proposal> {
    PROPOSALS
        .get(store, id)
        .ok_or_else(|| StdError::not_found("Proposal"))
}

#[cfg(test)]
mod tests {
    use cosmwasm_std::testing::{mock_dependencies, mock_env, mock_info};
    use cosmwasm_std::{coin, from_binary, BankMsg, Decimal};

    use cw2::{get_contract_version, ContractVersion};
    use cw_utils::{Duration, Threshold};

    use crate::msg::Voter;

    use super::*;

    fn mock_env_height(height_delta: u64) -> Env {
        let mut env = mock_env();
        env.block.height += height_delta;
        env
    }

    fn mock_env_time(time_delta: u64) -> Env {
        let mut env = mock_env();
        env.block.time = env.block.time.plus_seconds(time_delta);
        env
    }

    const OWNER: &str = "admin0001";
    const VOTER1: &str = "voter0001";
    const VOTER2: &str = "voter0002";
    const VOTER3: &str = "voter0003";
    const VOTER4: &str = "voter0004";
    const VOTER5: &str = "voter0005";
    const NOWEIGHT_VOTER: &str = "voterxxxx";
    const SOMEBODY: &str = "somebody";

    fn voter<T: Into<String>>(addr: T, weight: u64) -> Voter {
        Voter {
            addr: addr.into(),
            weight,
        }
    }

    // this will set up the instantiation for other tests
    #[track_caller]
    fn setup_test_case(
        deps: DepsMut,
        info: MessageInfo,
        threshold: Threshold,
        max_voting_period: Duration,
    ) -> Result<Response<Empty>, ContractError> {
        // Instantiate a contract with voters
        let voters = vec![
            voter(&info.sender, 1),
            voter(VOTER1, 1),
            voter(VOTER2, 2),
            voter(VOTER3, 3),
            voter(VOTER4, 4),
            voter(VOTER5, 5),
            voter(NOWEIGHT_VOTER, 0),
        ];

        let instantiate_msg = InstantiateMsg {
            voters,
            threshold,
            max_voting_period,
        };
        instantiate(deps, mock_env(), info, instantiate_msg)
    }

    fn get_tally(deps: Deps, proposal_id: u64) -> u64 {
        // Get all the voters on the proposal
        let voters = QueryMsg::ListVotes {
            proposal_id,
            start_after: None,
            limit: None,
        };
        let votes: VoteListResponse =
            from_binary(&query(deps, mock_env(), voters).unwrap()).unwrap();
        // Sum the weights of the Yes votes to get the tally
        votes
            .votes
            .iter()
            .filter(|&v| v.vote == Vote::Yes)
            .map(|v| v.weight)
            .sum()
    }

    #[test]
    fn test_instantiate_works() {
        let mut deps = mock_dependencies();
        let info = mock_info(OWNER, &[]);

        let max_voting_period = Duration::Time(1234567);

        // No voters fails
        let instantiate_msg = InstantiateMsg {
            voters: vec![],
            threshold: Threshold::ThresholdQuorum {
                threshold: Decimal::zero(),
                quorum: Decimal::percent(1),
            },
            max_voting_period,
        };
        let err = instantiate(
            deps.as_mut(),
            mock_env(),
            info.clone(),
            instantiate_msg.clone(),
        )
        .unwrap_err();
        assert_eq!(err, ContractError::NoVoters {});

        // Zero required weight fails
        let instantiate_msg = InstantiateMsg {
            voters: vec![voter(OWNER, 1)],
            ..instantiate_msg
        };
        let err =
            instantiate(deps.as_mut(), mock_env(), info.clone(), instantiate_msg).unwrap_err();
        assert_eq!(
            err,
            ContractError::Threshold(cw_utils::ThresholdError::InvalidThreshold {})
        );

        // Total weight less than required weight not allowed
        let threshold = Threshold::AbsoluteCount { weight: 100 };
        let err =
            setup_test_case(deps.as_mut(), info.clone(), threshold, max_voting_period).unwrap_err();
        assert_eq!(
            err,
            ContractError::Threshold(cw_utils::ThresholdError::UnreachableWeight {})
        );

        // All valid
        let threshold = Threshold::AbsoluteCount { weight: 1 };
        setup_test_case(deps.as_mut(), info, threshold, max_voting_period).unwrap();
    }

    // TODO: query() tests

    #[test]
    fn zero_weight_member_cant_vote() {
        let mut deps = mock_dependencies();

        let threshold = Threshold::AbsoluteCount { weight: 4 };
        let voting_period = Duration::Time(2000000);

        let info = mock_info(OWNER, &[]);
        setup_test_case(deps.as_mut(), info, threshold, voting_period).unwrap();

        let bank_msg = BankMsg::Send {
            to_address: SOMEBODY.into(),
            amount: vec![coin(1, "BTC")],
        };
        let msgs = vec![CosmosMsg::Bank(bank_msg)];

        // Voter without voting power still can create proposal
        let info = mock_info(NOWEIGHT_VOTER, &[]);
        let proposal = ExecuteMsg::Propose {
            title: "Rewarding somebody".to_string(),
            description: "Do we reward her?".to_string(),
            msgs,
            latest: None,
        };
        let res = execute(deps.as_mut(), mock_env(), info, proposal).unwrap();

        // Get the proposal id from the logs
        let proposal_id: u64 = res.attributes[2].value.parse().unwrap();

        // Cast a No vote
        let no_vote = ExecuteMsg::Vote {
            proposal_id,
            vote: Vote::No,
        };
        // Only voters with weight can vote
        let info = mock_info(NOWEIGHT_VOTER, &[]);
        let err = execute(deps.as_mut(), mock_env(), info, no_vote).unwrap_err();
        assert_eq!(err, ContractError::Unauthorized {});
    }

    #[test]
    fn test_propose_works() {
        let mut deps = mock_dependencies();

        let threshold = Threshold::AbsoluteCount { weight: 4 };
        let voting_period = Duration::Time(2000000);

        let info = mock_info(OWNER, &[]);
        setup_test_case(deps.as_mut(), info, threshold, voting_period).unwrap();

        let bank_msg = BankMsg::Send {
            to_address: SOMEBODY.into(),
            amount: vec![coin(1, "BTC")],
        };
        let msgs = vec![CosmosMsg::Bank(bank_msg)];

        // Only voters can propose
        let info = mock_info(SOMEBODY, &[]);
        let proposal = ExecuteMsg::Propose {
            title: "Rewarding somebody".to_string(),
            description: "Do we reward her?".to_string(),
            msgs: msgs.clone(),
            latest: None,
        };
        let err = execute(deps.as_mut(), mock_env(), info, proposal.clone()).unwrap_err();
        assert_eq!(err, ContractError::Unauthorized {});

        // Wrong expiration option fails
        let info = mock_info(OWNER, &[]);
        let proposal_wrong_exp = ExecuteMsg::Propose {
            title: "Rewarding somebody".to_string(),
            description: "Do we reward her?".to_string(),
            msgs,
            latest: Some(Expiration::AtHeight(123456)),
        };
        let err = execute(deps.as_mut(), mock_env(), info, proposal_wrong_exp).unwrap_err();
        assert_eq!(err, ContractError::WrongExpiration {});

        // Proposal from voter works
        let info = mock_info(VOTER3, &[]);
        let res = execute(deps.as_mut(), mock_env(), info, proposal.clone()).unwrap();

        // Verify
        assert_eq!(
            res,
            Response::new()
                .add_attribute("action", "propose")
                .add_attribute("sender", VOTER3)
                .add_attribute("proposal_id", 1.to_string())
                .add_attribute("status", "Open")
        );

        // Proposal from voter with enough vote power directly passes
        let info = mock_info(VOTER4, &[]);
        let res = execute(deps.as_mut(), mock_env(), info, proposal).unwrap();

        // Verify
        assert_eq!(
            res,
            Response::new()
                .add_attribute("action", "propose")
                .add_attribute("sender", VOTER4)
                .add_attribute("proposal_id", 2.to_string())
                .add_attribute("status", "Passed")
        );
    }

    #[test]
    fn test_vote_works() {
        let mut deps = mock_dependencies();

        let threshold = Threshold::AbsoluteCount { weight: 3 };
        let voting_period = Duration::Time(2000000);

        let info = mock_info(OWNER, &[]);
        setup_test_case(deps.as_mut(), info.clone(), threshold, voting_period).unwrap();

        // Propose
        let bank_msg = BankMsg::Send {
            to_address: SOMEBODY.into(),
            amount: vec![coin(1, "BTC")],
        };
        let msgs = vec![CosmosMsg::Bank(bank_msg)];
        let proposal = ExecuteMsg::Propose {
            title: "Pay somebody".to_string(),
            description: "Do I pay her?".to_string(),
            msgs,
            latest: None,
        };
        let res = execute(deps.as_mut(), mock_env(), info.clone(), proposal).unwrap();

        // Get the proposal id from the logs
        let proposal_id: u64 = res.attributes[2].value.parse().unwrap();

        // Owner cannot vote (again)
        let yes_vote = ExecuteMsg::Vote {
            proposal_id,
            vote: Vote::Yes,
        };
        let err = execute(deps.as_mut(), mock_env(), info, yes_vote.clone()).unwrap_err();
        assert_eq!(err, ContractError::AlreadyVoted {});

        // Only voters can vote
        let info = mock_info(SOMEBODY, &[]);
        let err = execute(deps.as_mut(), mock_env(), info, yes_vote.clone()).unwrap_err();
        assert_eq!(err, ContractError::Unauthorized {});

        // But voter1 can
        let info = mock_info(VOTER1, &[]);
        let res = execute(deps.as_mut(), mock_env(), info, yes_vote.clone()).unwrap();

        // Verify
        assert_eq!(
            res,
            Response::new()
                .add_attribute("action", "vote")
                .add_attribute("sender", VOTER1)
                .add_attribute("proposal_id", proposal_id.to_string())
                .add_attribute("status", "Open")
        );

        // No/Veto votes have no effect on the tally
        // Get the proposal id from the logs
        let proposal_id: u64 = res.attributes[2].value.parse().unwrap();

        // Compute the current tally
        let tally = get_tally(deps.as_ref(), proposal_id);

        // Cast a No vote
        let no_vote = ExecuteMsg::Vote {
            proposal_id,
            vote: Vote::No,
        };
        let info = mock_info(VOTER2, &[]);
        execute(deps.as_mut(), mock_env(), info, no_vote.clone()).unwrap();

        // Cast a Veto vote
        let veto_vote = ExecuteMsg::Vote {
            proposal_id,
            vote: Vote::Veto,
        };
        let info = mock_info(VOTER3, &[]);
        execute(deps.as_mut(), mock_env(), info.clone(), veto_vote).unwrap();

        // Verify
        assert_eq!(tally, get_tally(deps.as_ref(), proposal_id));

        // Once voted, votes cannot be changed
        let err = execute(deps.as_mut(), mock_env(), info.clone(), yes_vote.clone()).unwrap_err();
        assert_eq!(err, ContractError::AlreadyVoted {});
        assert_eq!(tally, get_tally(deps.as_ref(), proposal_id));

        // Expired proposals cannot be voted
        let env = match voting_period {
            Duration::Time(duration) => mock_env_time(duration + 1),
            Duration::Height(duration) => mock_env_height(duration + 1),
        };
        let err = execute(deps.as_mut(), env, info, no_vote).unwrap_err();
        assert_eq!(err, ContractError::Expired {});

        // Vote it again, so it passes
        let info = mock_info(VOTER4, &[]);
        let res = execute(deps.as_mut(), mock_env(), info, yes_vote.clone()).unwrap();

        // Verify
        assert_eq!(
            res,
            Response::new()
                .add_attribute("action", "vote")
                .add_attribute("sender", VOTER4)
                .add_attribute("proposal_id", proposal_id.to_string())
                .add_attribute("status", "Passed")
        );

        // non-Open proposals cannot be voted
        let info = mock_info(VOTER5, &[]);
        let err = execute(deps.as_mut(), mock_env(), info, yes_vote).unwrap_err();
        assert_eq!(err, ContractError::NotOpen {});

        // Propose
        let info = mock_info(OWNER, &[]);
        let bank_msg = BankMsg::Send {
            to_address: SOMEBODY.into(),
            amount: vec![coin(1, "BTC")],
        };
        let msgs = vec![CosmosMsg::Bank(bank_msg)];
        let proposal = ExecuteMsg::Propose {
            title: "Pay somebody".to_string(),
            description: "Do I pay her?".to_string(),
            msgs,
            latest: None,
        };
        let res = execute(deps.as_mut(), mock_env(), info, proposal).unwrap();

        // Get the proposal id from the logs
        let proposal_id: u64 = res.attributes[2].value.parse().unwrap();

        // Cast a No vote
        let no_vote = ExecuteMsg::Vote {
            proposal_id,
            vote: Vote::No,
        };
        // Voter1 vote no, weight 1
        let info = mock_info(VOTER1, &[]);
        let res = execute(deps.as_mut(), mock_env(), info, no_vote.clone()).unwrap();

        // Verify it is not enough to reject yet
        assert_eq!(
            res,
            Response::new()
                .add_attribute("action", "vote")
                .add_attribute("sender", VOTER1)
                .add_attribute("proposal_id", proposal_id.to_string())
                .add_attribute("status", "Open")
        );

        // Voter 4 votes no, weight 4, total weight for no so far 5, need 14 to reject
        let info = mock_info(VOTER4, &[]);
        let res = execute(deps.as_mut(), mock_env(), info, no_vote.clone()).unwrap();

        // Verify it is still open as we actually need no votes > 16 - 3
        assert_eq!(
            res,
            Response::new()
                .add_attribute("action", "vote")
                .add_attribute("sender", VOTER4)
                .add_attribute("proposal_id", proposal_id.to_string())
                .add_attribute("status", "Open")
        );

        // Voter 3 votes no, weight 3, total weight for no far 8, need 14
        let info = mock_info(VOTER3, &[]);
        let _res = execute(deps.as_mut(), mock_env(), info, no_vote.clone()).unwrap();

        // Voter 5 votes no, weight 5, total weight for no far 13, need 14
        let info = mock_info(VOTER5, &[]);
        let res = execute(deps.as_mut(), mock_env(), info, no_vote.clone()).unwrap();

        // Verify it is still open as we actually need no votes > 16 - 3
        assert_eq!(
            res,
            Response::new()
                .add_attribute("action", "vote")
                .add_attribute("sender", VOTER5)
                .add_attribute("proposal_id", proposal_id.to_string())
                .add_attribute("status", "Open")
        );

        // Voter 2 votes no, weight 2, total weight for no so far 15, need 14.
        // Can now reject
        let info = mock_info(VOTER2, &[]);
        let res = execute(deps.as_mut(), mock_env(), info, no_vote).unwrap();

        // Verify it is rejected as, 15 no votes > 16 - 3
        assert_eq!(
            res,
            Response::new()
                .add_attribute("action", "vote")
                .add_attribute("sender", VOTER2)
                .add_attribute("proposal_id", proposal_id.to_string())
                .add_attribute("status", "Rejected")
        );
    }

    #[test]
    fn test_execute_works() {
        let mut deps = mock_dependencies();

        let threshold = Threshold::AbsoluteCount { weight: 3 };
        let voting_period = Duration::Time(2000000);

        let info = mock_info(OWNER, &[]);
        setup_test_case(deps.as_mut(), info.clone(), threshold, voting_period).unwrap();

        // Propose
        let bank_msg = BankMsg::Send {
            to_address: SOMEBODY.into(),
            amount: vec![coin(1, "BTC")],
        };
        let msgs = vec![CosmosMsg::Bank(bank_msg)];
        let proposal = ExecuteMsg::Propose {
            title: "Pay somebody".to_string(),
            description: "Do I pay her?".to_string(),
            msgs: msgs.clone(),
            latest: None,
        };
        let res = execute(deps.as_mut(), mock_env(), info.clone(), proposal).unwrap();

        // Get the proposal id from the logs
        let proposal_id: u64 = res.attributes[2].value.parse().unwrap();

        // Only Passed can be executed
        let execution = ExecuteMsg::Execute { proposal_id };
        let err = execute(deps.as_mut(), mock_env(), info, execution.clone()).unwrap_err();
        assert_eq!(err, ContractError::WrongExecuteStatus {});

        // Vote it, so it passes
        let vote = ExecuteMsg::Vote {
            proposal_id,
            vote: Vote::Yes,
        };
        let info = mock_info(VOTER3, &[]);
        let res = execute(deps.as_mut(), mock_env(), info.clone(), vote).unwrap();

        // Verify
        assert_eq!(
            res,
            Response::new()
                .add_attribute("action", "vote")
                .add_attribute("sender", VOTER3)
                .add_attribute("proposal_id", proposal_id.to_string())
                .add_attribute("status", "Passed")
        );

        // In passing: Try to close Passed fails
        let closing = ExecuteMsg::Close { proposal_id };
        let err = execute(deps.as_mut(), mock_env(), info, closing).unwrap_err();
        assert_eq!(err, ContractError::WrongCloseStatus {});

        // Execute works. Anybody can execute Passed proposals
        let info = mock_info(SOMEBODY, &[]);
        let res = execute(deps.as_mut(), mock_env(), info.clone(), execution).unwrap();

        // Verify
        assert_eq!(
            res,
            Response::new()
                .add_messages(msgs)
                .add_attribute("action", "execute")
                .add_attribute("sender", SOMEBODY)
                .add_attribute("proposal_id", proposal_id.to_string())
        );

        // In passing: Try to close Executed fails
        let closing = ExecuteMsg::Close { proposal_id };
        let err = execute(deps.as_mut(), mock_env(), info, closing).unwrap_err();
        assert_eq!(err, ContractError::WrongCloseStatus {});
    }

    #[test]
    fn test_close_works() {
        let mut deps = mock_dependencies();

        let threshold = Threshold::AbsoluteCount { weight: 3 };
        let voting_period = Duration::Height(2000000);

        let info = mock_info(OWNER, &[]);
        setup_test_case(deps.as_mut(), info.clone(), threshold, voting_period).unwrap();

        // Propose
        let bank_msg = BankMsg::Send {
            to_address: SOMEBODY.into(),
            amount: vec![coin(1, "BTC")],
        };
        let msgs = vec![CosmosMsg::Bank(bank_msg)];
        let proposal = ExecuteMsg::Propose {
            title: "Pay somebody".to_string(),
            description: "Do I pay her?".to_string(),
            msgs: msgs.clone(),
            latest: None,
        };
        let res = execute(deps.as_mut(), mock_env(), info, proposal).unwrap();

        // Get the proposal id from the logs
        let proposal_id: u64 = res.attributes[2].value.parse().unwrap();

        let closing = ExecuteMsg::Close { proposal_id };

        // Anybody can close
        let info = mock_info(SOMEBODY, &[]);

        // Non-expired proposals cannot be closed
        let err = execute(deps.as_mut(), mock_env(), info, closing).unwrap_err();
        assert_eq!(err, ContractError::NotExpired {});

        // Expired proposals can be closed
        let info = mock_info(OWNER, &[]);

        let proposal = ExecuteMsg::Propose {
            title: "(Try to) pay somebody".to_string(),
            description: "Pay somebody after time?".to_string(),
            msgs,
            latest: Some(Expiration::AtHeight(123456)),
        };
        let res = execute(deps.as_mut(), mock_env(), info.clone(), proposal).unwrap();

        // Get the proposal id from the logs
        let proposal_id: u64 = res.attributes[2].value.parse().unwrap();

        let closing = ExecuteMsg::Close { proposal_id };

        // Close expired works
        let env = mock_env_height(1234567);
        let res = execute(
            deps.as_mut(),
            env,
            mock_info(SOMEBODY, &[]),
            closing.clone(),
        )
        .unwrap();

        // Verify
        assert_eq!(
            res,
            Response::new()
                .add_attribute("action", "close")
                .add_attribute("sender", SOMEBODY)
                .add_attribute("proposal_id", proposal_id.to_string())
        );

        // Trying to close it again fails
        let err = execute(deps.as_mut(), mock_env(), info, closing).unwrap_err();
        assert_eq!(err, ContractError::WrongCloseStatus {});
    }
}
