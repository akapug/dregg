//! The external `cosmos-settlement` query interface this contract CONSUMES.
//!
//! Redefined locally (not depended-on) so the escrow crate stays a standalone
//! workspace; the JSON shapes below are byte-identical to
//! `cosmos-settlement/src/msg.rs` (`QueryMsg::IsProvenRoot { root }` →
//! `BoolResponse { value }`), which is all a `query_wasm_smart` needs to match.

use cosmwasm_schema::cw_serde;

/// The subset of `cosmos-settlement`'s `QueryMsg` we call: the rung-8 accept-path.
#[cw_serde]
pub enum SettlementQueryMsg {
    /// True iff `root` (a `packLanes` hex key) has ever been proven by the
    /// settlement contract. `bytes32(0)` / the zero root is never proven.
    IsProvenRoot { root: String },
}

/// The settlement contract's boolean response shape.
#[cw_serde]
pub struct BoolResponse {
    pub value: bool,
}
