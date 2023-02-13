use cw4::TOTAL_KEY;
use cw_controllers::{Admin, Hooks};
use cw_storage_plus::{Item, SnapshotMap, Strategy};
use secret_cosmwasm_std::Addr;

pub const ADMIN: Admin = Admin::new("admin");
pub const HOOKS: Hooks = Hooks::new("cw4-hooks");

pub const TOTAL: Item<u64> = Item::new(TOTAL_KEY);

pub const MEMBERS: SnapshotMap<Addr, u64> = SnapshotMap::new(
    cw4::MEMBERS_KEY,
    cw4::MEMBERS_INDEX,
    cw4::MEMBERS_CHECKPOINTS,
    cw4::MEMBERS_CHANGELOG,
    cw4::MEMBERS_HEIGHT_INDEX,
    Strategy::EveryBlock,
);
