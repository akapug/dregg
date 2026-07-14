//! # The MULTICHAIN / MULTINODE integration-test harness — the flow-builder.
//!
//! This module is the SHARED SCAFFOLD the multichain integration tests
//! (`tests/multichain_flows.rs`) drive. It is NOT a unit test of one brick: it
//! COMPOSES the landed composition pieces into END-TO-END flows that cross two
//! (local) chains and settle a shielded token through the OCIP socket.
//!
//! ## What it composes (the REAL landed pieces — not new mocks)
//!
//!   * **REAL Poseidon2 notes** — every `BoundNote` is the exact `hash_fact`
//!     value-binding / leaf / nullifier the shielded spend circuit binds and the
//!     three composition bricks (`shielded_{deposit_glue,clearing_note_order,
//!     settle_back}_poc.rs`) use. `dregg_circuit::poseidon2::hash_fact`.
//!   * **REAL LC holding-identity binding** — the deposit attestation's holding
//!     hash is the in-AIR `mpt_holding_hash_felt` (`circuit-prove/src/
//!     mpt_holding_leaf.rs`), the exact P0 fold-leaf binding. `ConsensusProven`
//!     stands for the verified chain that RUNS in the separate binary
//!     `eth-lightclient/src/bin/verify_holding.rs` (real mainnet period-1800 BLS
//!     397/512, EIP-1186 MPT, forged "+1 wei" REFUSED) — the same posture the
//!     landed deposit-glue brick takes.
//!   * **REAL fhEgg clearing** — `fhegg_solver::clearing::{Order, clear,
//!     allocate}`, the uniform-price fold + volume-maximising crossing + conserving
//!     pro-rata allocation. The multi-asset ring and the single-asset clear both
//!     run the REAL engine.
//!   * **REAL Price-Cert** — `fhegg_solver::pricecert::{Market, solve_price_cert}`,
//!     the state-price LP + certificate the derivatives flow settles as a note.
//!   * **REAL InterchainCustody gates** — `MirrorState` (`recordEscrow`/`drawMint`/
//!     `release`, `supply ≤ locked`) faithful to `metatheory/Market/
//!     InterchainCustody.lean`, per the bricks.
//!
//! ## What is SIMULATED (labelled — never called "live")
//!
//!   * **The "two chains" = two local [`Chain`] instances** (two custody ledgers +
//!     two verifier deployments in-process). The genuine cross-chain message is the
//!     LC attestation (chain A) + the OCIP socket verify (chain B); the two chains
//!     themselves are local, NOT two live networks.
//!   * **The OCIP socket verify** — the socket's ACCEPTANCE GATE (BabyBear
//!     canonicity on every lane + the WHICH-dregg genesis-anchor trust check +
//!     accept-iff-the-proof-attests-the-statement) is modelled faithfully off
//!     `chain/contracts/socket/{DreggVerifier,TrustsADreggClearing}.sol`. The
//!     real BN254 Groth16 pairing is STOOD IN by a Poseidon2 statement-binding
//!     digest ([`WrapProof`]): a proof attests exactly one 25-lane statement, and a
//!     tampered statement is genuinely refused. The real pairing + the Solidity
//!     deploy (`chain/DEPLOYMENTS.md`, dev-ceremony VK) are the on-chain path,
//!     ember-gated.
//!   * **The multinode / federation** — the n-party clearing ([`MpcClearing`]) is
//!     an IN-PROCESS decomposition of the REAL fhEgg engine: each party folds ONLY
//!     its own orders into aggregate curves, the curves sum, the crossing is
//!     computed on the sum — no party publishes an individual order. This exercises
//!     the n-party split + result-agreement with the single-party clear. The
//!     cryptographic no-peek summation (curves summed under encryption) + n real
//!     node processes are the persistent-federation deploy, ember-gated.

pub use dregg_circuit::field::BABYBEAR_P;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit_prove::mpt_holding_leaf::mpt_holding_hash_felt;
use fhegg_solver::clearing::{Order, Side, allocate, clear, crossing, fold_curves};
use std::collections::BTreeMap;

/// Map a `u64` into BabyBear (note/attestation fields are conceptually field elems).
pub fn felt(v: u64) -> BabyBear {
    BabyBear::new((v % (BABYBEAR_P as u64)) as u32)
}

/// The honest no-inflation window (matches `shielded::attest::RANGE_BITS`): a note
/// value must lie in `[0, 2^30)`.
pub const RANGE_BITS: u32 = 30;

// ===========================================================================
// REAL Poseidon2 pool notes — the exact `hash_fact` shape the bricks use.
// ===========================================================================

/// A shielded pool note: a hidden `(value, asset)` bound under Poseidon2. Identical
/// shape to the three composition bricks' `BoundNote`.
#[derive(Clone, Debug)]
#[allow(dead_code)] // leaf/owner/key document the real note shape (mirror the bricks)
pub struct BoundNote {
    /// Leaf commitment (C6): `hash_fact(value, [asset, owner, randomness])`.
    pub leaf: BabyBear,
    /// PQ value-binding (C7 / `RealCrypto §1.3`): `hash_fact(value,[asset,rand,0])`.
    pub value_binding: BabyBear,
    /// Spend nullifier: `hash_fact(leaf, [key, 0, 0, 0])`.
    pub nullifier: BabyBear,
    /// The hidden amount (witness; never published in the clear).
    pub value: u64,
    /// The asset class.
    pub asset: u64,
    pub owner: u64,
    pub randomness: u64,
    pub key: u64,
}

/// Compute the REAL Poseidon2 facts for a note `(asset, value)` blinded by
/// `(owner, randomness)` and keyed by `key` — identical to the bricks.
pub fn mint_note(asset: u64, value: u64, owner: u64, randomness: u64, key: u64) -> BoundNote {
    let v = felt(value);
    let a = felt(asset);
    let o = felt(owner);
    let r = felt(randomness);
    let leaf = hash_fact(v, &[a, o, r]);
    let value_binding = hash_fact(v, &[a, r, BabyBear::ZERO]);
    let nullifier = hash_fact(
        leaf,
        &[felt(key), BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    );
    BoundNote {
        leaf,
        value_binding,
        nullifier,
        value,
        asset,
        owner,
        randomness,
        key,
    }
}

impl BoundNote {
    /// Re-derive the value-binding for the note's claimed value+asset and check it
    /// matches the published commitment (binding under HashCR:
    /// `RealCrypto.mint_forces_collision`).
    pub fn value_binding_opens(&self) -> bool {
        let expect = hash_fact(
            felt(self.value),
            &[felt(self.asset), felt(self.randomness), BabyBear::ZERO],
        );
        expect == self.value_binding
    }
}

// ===========================================================================
// The LC attestation of a locked token — the `verify_holding` leaf-adapter output.
// ===========================================================================

/// How much this attestation is trusted — the `HoldingTrust` of the LC output.
/// Only `ConsensusProven` (the full `verify_holding` chain) can back a mint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HoldingTrust {
    ConsensusProven,
    Unproven,
}

/// The attested lock of a real public-chain token — the shape `verify_holding`
/// (via the `mpt_holding_leaf` adapter) produces. The HOLDING IDENTITY is the REAL
/// in-AIR `mpt_holding_hash_felt` binding.
#[derive(Clone, Debug)]
pub struct AttestedLock {
    pub state_root: [BabyBear; 8],
    pub token: BabyBear,
    pub holder: BabyBear,
    pub slot: BabyBear,
    pub locked_value: u64,
    pub holding_hash: BabyBear,
    pub trust: HoldingTrust,
    pub asset: u64,
    /// A public-chain tag (e.g. Ethereum-mainnet = 1, an L2 = 8453). Carried into
    /// the deposit dedup so the SAME token on two chains gives distinct nullifiers.
    pub chain: u64,
}

impl AttestedLock {
    /// The REAL in-AIR holding identity over this attestation's pinned fields.
    pub fn recompute_holding_hash(&self) -> BabyBear {
        mpt_holding_hash_felt(
            &self.state_root,
            self.token,
            self.holder,
            self.slot,
            felt(self.locked_value),
        )
    }

    /// **A VALID LOCK** — `verify_holding`'s `ConsensusProven` fail-closed check,
    /// mirrored: the published holding identity must recompute from the pinned
    /// fields (a forged/tampered balance breaks it) AND trust is `ConsensusProven`.
    pub fn is_valid_lock(&self) -> bool {
        self.trust == HoldingTrust::ConsensusProven
            && self.recompute_holding_hash() == self.holding_hash
    }

    /// The deposit dedup identity — keyed on the lock's identity + chain.
    pub fn deposit_nullifier(&self) -> BabyBear {
        hash_fact(
            self.holding_hash,
            &[self.slot, felt(self.chain), BabyBear::ZERO],
        )
    }
}

/// Build an HONEST attested lock (published holding hash matches the fields) — the
/// shape `verify_holding` → `mpt_holding_leaf` yields for a real lock on `chain`.
pub fn honest_attestation(
    asset: u64,
    locked_value: u64,
    token: u64,
    holder: u64,
    slot: u64,
    chain: u64,
) -> AttestedLock {
    let state_root = [
        felt(0xE71 ^ slot ^ chain),
        felt(0x100),
        felt(0x200),
        felt(0x300),
        felt(0x400),
        felt(0x500),
        felt(0x600),
        felt(0x700 ^ token),
    ];
    let holding_hash = mpt_holding_hash_felt(
        &state_root,
        felt(token),
        felt(holder),
        felt(slot),
        felt(locked_value),
    );
    AttestedLock {
        state_root,
        token: felt(token),
        holder: felt(holder),
        slot: felt(slot),
        locked_value,
        holding_hash,
        trust: HoldingTrust::ConsensusProven,
        asset,
        chain,
    }
}

// ===========================================================================
// The custody MirrorState — faithful to `InterchainCustody.lean`.
// ===========================================================================

/// The dregg-side custody ledger of one mirrored token on ONE chain: `locked`
/// (external escrow) and `supply` (mirror circulating). `MirrorState.backed` is
/// `supply ≤ locked`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MirrorState {
    pub locked: u64,
    pub supply: u64,
}

impl MirrorState {
    pub fn init() -> Self {
        MirrorState {
            locked: 0,
            supply: 0,
        }
    }
    pub fn seeded(locked: u64, supply: u64) -> Self {
        MirrorState { locked, supply }
    }
    /// The invariant `supply ≤ locked`.
    pub fn backed(&self) -> bool {
        self.supply <= self.locked
    }
    /// The redeemability slack `locked − supply`.
    pub fn gap(&self) -> i128 {
        self.locked as i128 - self.supply as i128
    }
    /// `recordEscrow a` — raise `locked` (always succeeds).
    pub fn record_escrow(&self, a: u64) -> MirrorState {
        MirrorState {
            locked: self.locked + a,
            supply: self.supply,
        }
    }
    /// `drawMint a` — raise `supply` IFF `supply + a ≤ locked`, else REFUSE.
    pub fn draw_mint(&self, a: u64) -> Option<MirrorState> {
        if self.supply + a <= self.locked {
            Some(MirrorState {
                locked: self.locked,
                supply: self.supply + a,
            })
        } else {
            None
        }
    }
    /// `release a` — lower BOTH registers by `a`, gated on `a ≤ supply`.
    pub fn release(&self, a: u64) -> Option<MirrorState> {
        if a <= self.supply {
            Some(MirrorState {
                locked: self.locked - a,
                supply: self.supply - a,
            })
        } else {
            None
        }
    }
}

// ===========================================================================
// The shielded pool — faithful to `ShieldedValue.lean unshieldK`.
// ===========================================================================

/// The shielded pool state: live notes (by nullifier), consumed nullifiers, and the
/// per-asset transparent balance (= Σ live-note value). This pool SPANS chains — the
/// shielded layer is where value moves from chain A to chain B.
#[derive(Clone, Debug, Default)]
pub struct ShieldedPool {
    pub live: Vec<BoundNote>,
    pub consumed: Vec<BabyBear>,
    pub balance: BTreeMap<u64, i128>,
}

/// Why an unshield fails-closed.
#[derive(Debug, PartialEq, Eq)]
pub enum UnshieldError {
    NoteNotBound,
    NoteNotInPool,
    DoubleSettle,
}

/// The transparent result of an unshield: the amount that left (= the note's value)
/// and its asset.
#[derive(Debug, Clone, Copy)]
pub struct Unshielded {
    pub amount: u64,
    pub asset: u64,
}

impl ShieldedPool {
    /// Insert a live note (credit its asset's pool balance) — `PoolInvariant`.
    pub fn insert(&mut self, note: BoundNote) {
        *self.balance.entry(note.asset).or_insert(0) += note.value as i128;
        self.live.push(note);
    }
    pub fn with_live(notes: &[BoundNote]) -> Self {
        let mut p = ShieldedPool::default();
        for n in notes {
            p.insert(n.clone());
        }
        p
    }
    /// `unshield` — the Rust mirror of `unshieldK`: look up by nullifier
    /// (fail-closed if absent), refuse a consumed nullifier, consume it, debit the
    /// pool by exactly the note's value. The amount is the note's value BY
    /// CONSTRUCTION (`unshield_value_binding`).
    pub fn unshield(&mut self, note: &BoundNote) -> Result<Unshielded, UnshieldError> {
        if !note.value_binding_opens() {
            return Err(UnshieldError::NoteNotBound);
        }
        let Some(idx) = self.live.iter().position(|n| n.nullifier == note.nullifier) else {
            return Err(UnshieldError::NoteNotInPool);
        };
        if self.consumed.contains(&note.nullifier) {
            return Err(UnshieldError::DoubleSettle);
        }
        let n = self.live.remove(idx);
        self.consumed.push(n.nullifier);
        *self.balance.entry(n.asset).or_insert(0) -= n.value as i128;
        Ok(Unshielded {
            amount: n.value,
            asset: n.asset,
        })
    }
}

// ===========================================================================
// A CHAIN — a local EVM instance (a custody ledger + optional OCIP consumer).
// ===========================================================================

/// One (local) chain: a per-asset custody ledger, the dregg instance this chain
/// anchors to (its genesis, for the socket's WHICH-dregg check), and — on the
/// SETTLE chain — the deployed OCIP consumer contract that gates on a dregg proof.
///
/// The "two chains" of a cross-chain flow are two of these, in-process. Labelled:
/// NOT two live networks — the genuine cross-chain link is the LC attestation
/// (source) + the socket verify (destination).
pub struct Chain {
    pub name: String,
    pub custody: BTreeMap<u64, MirrorState>,
    /// The genesis anchor of the dregg instance this chain settles against.
    pub genesis_anchor: [u32; 8],
    /// The deployed OCIP consumer (the `TrustsADreggClearing` mirror), if any.
    pub trusts: Option<TrustsClearing>,
}

impl Chain {
    pub fn new(name: &str, genesis_anchor: [u32; 8]) -> Self {
        Chain {
            name: name.to_string(),
            custody: BTreeMap::new(),
            genesis_anchor,
            trusts: None,
        }
    }
    /// Seed a chain's per-asset custody (e.g. the bridged backing that arrived on
    /// the destination chain).
    pub fn seed_custody(&mut self, asset: u64, m: MirrorState) {
        self.custody.insert(asset, m);
    }
    /// Deploy the OCIP consumer on this chain, trusting THIS chain's dregg anchor.
    pub fn deploy_socket(&mut self, socket: DreggSocket) {
        self.trusts = Some(TrustsClearing::new(socket, self.genesis_anchor));
    }
}

// ===========================================================================
// The OCIP socket — modelled off DreggVerifier.sol + TrustsADreggClearing.sol.
// ===========================================================================

/// A DREGG settlement statement — the 25 public inputs of the wrap proof
/// (`IGroth16Verifier25`, `DreggAttestation.Statement`): genesis_root(8),
/// final_root(8), num_turns, chain_digest(8).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SettlementStatement {
    pub genesis_root: [u32; 8],
    pub final_root: [u32; 8],
    pub num_turns: u32,
    pub chain_digest: [u32; 8],
}

/// A non-canonical lane makes the statement ILL-FORMED (not a forgery) — the
/// socket's `_canonical` revert (`NonCanonicalLane`).
#[derive(Debug, PartialEq, Eq)]
pub struct NonCanonicalLane {
    pub lane: usize,
    pub value: u32,
}

impl SettlementStatement {
    /// `DreggAttestation.encode` — assemble + enforce BabyBear canonicity on every
    /// lane. An out-of-range lane reverts (ill-formed), distinct from a well-formed
    /// statement whose proof fails to verify.
    pub fn encode(&self) -> Result<[u32; 25], NonCanonicalLane> {
        let mut inputs = [0u32; 25];
        let mut set = |i: usize, v: u32, out: &mut [u32; 25]| -> Result<(), NonCanonicalLane> {
            if v as u64 >= BABYBEAR_P as u64 {
                return Err(NonCanonicalLane { lane: i, value: v });
            }
            out[i] = v;
            Ok(())
        };
        for i in 0..8 {
            set(i, self.genesis_root[i], &mut inputs)?;
        }
        for i in 0..8 {
            set(8 + i, self.final_root[i], &mut inputs)?;
        }
        set(16, self.num_turns, &mut inputs)?;
        for i in 0..8 {
            set(17 + i, self.chain_digest[i], &mut inputs)?;
        }
        Ok(inputs)
    }

    /// The Poseidon2 binding digest of the 25 lanes — the value a [`WrapProof`]
    /// commits to. STANDS IN for the BN254 pairing binding: the proof attests
    /// exactly the statement whose lanes hash to this digest. A tampered lane gives
    /// a different digest ⇒ the proof no longer attests it.
    pub fn binding_digest(&self) -> BabyBear {
        let inputs = self.encode().expect("digest of a canonical statement");
        let mut acc = felt(0xD9E6); // domain tag
        for &lane in inputs.iter() {
            acc = hash_fact(acc, &[felt(lane as u64), BabyBear::ZERO, BabyBear::ZERO]);
        }
        acc
    }
}

/// A DREGG wrap proof — modelled. It commits to exactly ONE statement's binding
/// digest. `prove_settlement` mints it for an honest statement; `attests` checks a
/// presented statement is the one proven.
///
/// LABEL: the real proof is a Groth16(BN254) wrap of the whole-history STARK apex;
/// the BN254 pairing that enforces this statement-binding on-chain is the separate
/// gnark/Solidity path. Here the Poseidon2 `binding_digest` is the genuine
/// integrity tie — a tampered statement is refused — standing in for that pairing.
#[derive(Clone, Debug)]
pub struct WrapProof {
    pub bound_digest: BabyBear,
}

/// Mint a wrap proof for an honestly-computed settlement statement.
pub fn prove_settlement(stmt: &SettlementStatement) -> WrapProof {
    WrapProof {
        bound_digest: stmt.binding_digest(),
    }
}

impl WrapProof {
    /// The proof attests `stmt` iff its bound digest matches `stmt`'s digest.
    pub fn attests(&self, stmt: &SettlementStatement) -> bool {
        self.bound_digest == stmt.binding_digest()
    }
}

/// `DreggVerifier` — the VK-rotation-absorbing socket. `verify_statement` = the
/// canonicity gate + the pairing (modelled as `proof.attests`).
#[derive(Clone, Debug)]
pub struct DreggSocket {
    pub current_epoch: u64,
}

impl DreggSocket {
    pub fn new(epoch: u64) -> Self {
        DreggSocket {
            current_epoch: epoch,
        }
    }
    /// `verifyStatement` — encode (canonicity) then verify (the pairing, modelled).
    /// Fail-closed: `Err` on a non-canonical statement (revert), `Ok(false)` on a
    /// well-formed statement the proof does not attest.
    pub fn verify_statement(
        &self,
        proof: &WrapProof,
        stmt: &SettlementStatement,
    ) -> Result<bool, NonCanonicalLane> {
        stmt.encode()?; // canonicity revert
        Ok(proof.attests(stmt))
    }
}

/// `TrustsADreggClearing` — a DEMO third-party consumer gating its own logic on a
/// dregg attestation. Trusts ONE dregg instance (`trusted_anchor`); accepts a
/// clearing iff (1) the attestation is about that instance and (2) the proof
/// verifies through the socket.
#[derive(Clone)]
pub struct TrustsClearing {
    pub socket: DreggSocket,
    pub trusted_anchor: [u32; 8],
    pub accepted: Vec<[u32; 8]>,
}

/// Why an `accept_clearing` was refused.
#[derive(Debug, PartialEq, Eq)]
pub enum AcceptError {
    /// The attestation is about a dregg instance this contract does not trust.
    UntrustedDreggInstance,
    /// The statement is ill-formed (a non-canonical lane) — reverts.
    NonCanonical(NonCanonicalLane),
    /// The proof failed to verify (forged / tampered — the pairing returned false).
    AttestationRejected,
}

impl TrustsClearing {
    pub fn new(socket: DreggSocket, trusted_anchor: [u32; 8]) -> Self {
        TrustsClearing {
            socket,
            trusted_anchor,
            accepted: Vec::new(),
        }
    }
    /// THE SECURITY-PROVIDER GATE (`acceptClearing`). Accept a dregg-attested
    /// clearing iff (1) `genesis_root == trusted_anchor` (WHICH dregg) and (2) the
    /// socket verifies the proof. On accept, record the attested `final_root`.
    pub fn accept_clearing(
        &mut self,
        proof: &WrapProof,
        stmt: &SettlementStatement,
    ) -> Result<[u32; 8], AcceptError> {
        // 1. WHICH dregg — must be the instance we trust (checked BEFORE the pairing).
        if stmt.genesis_root != self.trusted_anchor {
            return Err(AcceptError::UntrustedDreggInstance);
        }
        // 2. IS IT VALID — verify through the socket against the current VK epoch.
        let ok = self
            .socket
            .verify_statement(proof, stmt)
            .map_err(AcceptError::NonCanonical)?;
        if !ok {
            return Err(AcceptError::AttestationRejected);
        }
        self.accepted.push(stmt.final_root);
        Ok(stmt.final_root)
    }
    /// Whether a final root has been accepted as a trusted clearing.
    pub fn is_accepted(&self, root: &[u32; 8]) -> bool {
        self.accepted.contains(root)
    }
}

/// Fold a `MirrorState` (post-settle custody) into 8 canonical BabyBear lanes — the
/// destination-chain `final_root` the settlement statement attests. Uses the same
/// Poseidon2 the custody turn commits with.
pub fn custody_root_lanes(m: &MirrorState) -> [u32; 8] {
    let base = hash_fact(
        felt(m.locked),
        &[felt(m.supply), BabyBear::ZERO, BabyBear::ZERO],
    );
    let mut lanes = [0u32; 8];
    let mut acc = base;
    for lane in lanes.iter_mut() {
        acc = hash_fact(acc, &[BabyBear::ONE, BabyBear::ZERO, BabyBear::ZERO]);
        // `as_u32()` is the raw inner; reduce to a canonical residue < p (a hash
        // output is already reduced, but be explicit so the lane is canonical).
        *lane = acc.as_u32() % BABYBEAR_P;
    }
    lanes
}

// ===========================================================================
// The n-party MPC clearing sim — an in-process decomposition of the REAL engine.
// ===========================================================================

/// An n-party clearing computed the way the federation MPC would: each party folds
/// ONLY its own orders into aggregate curves (the fhEgg `fold_curves`), the parties'
/// curves sum, and the crossing is computed on the sum. No party publishes an
/// individual order — only its aggregate demand/supply histogram.
///
/// LABEL: this is a STRUCTURAL n-party decomposition of the real fhEgg engine (the
/// fold+scan+crossing is genuinely additive over disjoint order sets). It exercises
/// the n-party split + agreement with the single-party clear. The cryptographic
/// no-peek (curves summed under encryption) + n real node processes are the
/// persistent-federation deploy — ember-gated.
pub struct MpcClearing {
    pub k: usize,
    /// Each party's private order share (a disjoint slice of the book).
    pub parties: Vec<Vec<Order>>,
}

/// The result of an n-party MPC clear.
#[derive(Debug)]
pub struct MpcResult {
    pub cleared_volume: u64,
    pub clearing_price: usize,
    pub n_parties: usize,
    /// The largest number of orders any single party saw (must be < the whole book
    /// when n > 1 — no party sees the full order flow).
    pub max_party_view: usize,
    pub total_orders: usize,
}

impl MpcClearing {
    pub fn new(k: usize) -> Self {
        MpcClearing {
            k,
            parties: Vec::new(),
        }
    }
    /// Give party `p` its private order share.
    pub fn party(mut self, orders: Vec<Order>) -> Self {
        self.parties.push(orders);
        self
    }
    /// Run the n-party clear: each party folds its own curves locally, the curves
    /// sum, the crossing is on the sum. Returns the joint `V*` + the leakage bound.
    pub fn run(&self) -> MpcResult {
        let mut demand = vec![0u64; self.k];
        let mut supply = vec![0u64; self.k];
        let mut max_view = 0usize;
        let mut total = 0usize;
        for share in &self.parties {
            // Each party folds ONLY its own orders (its private curve).
            let (d, s) = fold_curves(share, self.k);
            for j in 0..self.k {
                demand[j] += d[j];
                supply[j] += s[j];
            }
            max_view = max_view.max(share.len());
            total += share.len();
        }
        let (_crossed, price, vstar) = crossing(&demand, &supply);
        MpcResult {
            cleared_volume: vstar,
            clearing_price: price,
            n_parties: self.parties.len(),
            max_party_view: max_view,
            total_orders: total,
        }
    }
    /// The reference single-party clear over the WHOLE book (the oracle the MPC
    /// result must agree with).
    pub fn reference(&self) -> u64 {
        let all: Vec<Order> = self.parties.iter().flatten().copied().collect();
        clear(&all, self.k).cleared_volume
    }
}

// ===========================================================================
// The composed adapters — deposit / clear / transfer / settle over REAL notes.
// ===========================================================================

/// Why a deposit fails-closed (the deposit-glue teeth).
#[derive(Debug, PartialEq, Eq)]
pub enum DepositError {
    NoValidLock,
    MintBeyondLock,
    DoubleMint,
    OutOfRange,
}

/// A cleared fill + change output pair, summing EXACTLY to the input's value.
pub struct FillOutput {
    pub fill_note: BoundNote,
    pub change_note: BoundNote,
}

/// A single sealed pool note as a REAL fhEgg order.
#[derive(Clone)]
pub struct SealedNote {
    pub order: Order,
    pub note: BoundNote,
}

/// Seal a pool note as an fhEgg order (`note_to_order`).
pub fn note_to_order(note: &BoundNote, side: Side, limit: u32) -> SealedNote {
    assert!(
        note.value_binding_opens(),
        "note_to_order: the note must open its value-binding"
    );
    SealedNote {
        order: Order {
            side,
            qty: note.value,
            limit,
        },
        note: note.clone(),
    }
}

/// `order_to_note` — mint the cleared fill + change as fresh conserving output notes.
pub fn order_to_note(sealed: &SealedNote, fill: u64) -> FillOutput {
    assert!(fill <= sealed.note.value, "no over-fill");
    let change = sealed.note.value - fill;
    let fill_note = mint_note(
        sealed.note.asset,
        fill,
        sealed.note.owner ^ 0xF11,
        sealed.note.randomness ^ 0xF11,
        sealed.note.key ^ 0xF11,
    );
    let change_note = mint_note(
        sealed.note.asset,
        change,
        sealed.note.owner ^ 0xC00,
        sealed.note.randomness ^ 0xC00,
        sealed.note.key ^ 0xC00,
    );
    FillOutput {
        fill_note,
        change_note,
    }
}

// ===========================================================================
// THE FLOW-BUILDER — the reusable scaffold the integration tests share.
// ===========================================================================

/// One recorded stage of a flow: [chain A event] → [shielded op] → [clear] →
/// [chain B settle/verify]. `ok` gates the flow's overall verdict.
#[derive(Debug)]
pub struct Stage {
    pub name: String,
    pub ok: bool,
    pub detail: String,
}

/// A flow report — the trace of a composed end-to-end flow. `all_ok()` is the
/// flow's verdict; the tests assert on it and on individual stages.
pub struct FlowReport {
    pub label: String,
    pub stages: Vec<Stage>,
}

impl FlowReport {
    pub fn new(label: &str) -> Self {
        println!("\n=== FLOW: {label} ===");
        FlowReport {
            label: label.to_string(),
            stages: Vec::new(),
        }
    }
    /// Record a stage; returns `ok` so callers can branch. Prints the stage line.
    pub fn record(&mut self, name: &str, ok: bool, detail: &str) -> bool {
        let mark = if ok { "ok" } else { "REJECTED" };
        println!("  [{mark}] {name}: {detail}");
        self.stages.push(Stage {
            name: name.to_string(),
            ok,
            detail: detail.to_string(),
        });
        ok
    }
    /// Every recorded stage passed.
    pub fn all_ok(&self) -> bool {
        self.stages.iter().all(|s| s.ok)
    }
    /// The number of recorded stages (positive-polarity flow steps).
    pub fn stage_count(&self) -> usize {
        self.stages.len()
    }
}

/// The multichain harness — the flow-builder object. Owns the shared shielded pool
/// (which spans chains) + the deposit dedup ledger. The tests thread `Chain`s
/// through its stage methods to compose flows.
pub struct MultichainHarness {
    pub pool: ShieldedPool,
    /// Consumed deposit nullifiers (one lock ⇒ one note, across all chains).
    pub deposit_nullifiers: Vec<BabyBear>,
    /// Minted deposit commitments (the pool set).
    pub commitments: Vec<BabyBear>,
}

impl Default for MultichainHarness {
    fn default() -> Self {
        MultichainHarness {
            pool: ShieldedPool::default(),
            deposit_nullifiers: Vec::new(),
            commitments: Vec::new(),
        }
    }
}

impl MultichainHarness {
    pub fn new() -> Self {
        Self::default()
    }

    /// STAGE — DEPOSIT on a (source) chain: `deposit_to_note = attest ∘ shieldK`.
    /// Mint a shielded note from an attested lock, gated on a valid ConsensusProven
    /// lock + range + `value ≤ locked` (the custody `drawMint`) + one-lock-one-note.
    /// The minted note enters the shared shielded pool.
    pub fn deposit(
        &mut self,
        chain: &mut Chain,
        lock: &AttestedLock,
        value: u64,
        owner: u64,
        randomness: u64,
        key: u64,
    ) -> Result<BoundNote, DepositError> {
        if !lock.is_valid_lock() {
            return Err(DepositError::NoValidLock);
        }
        if value >= (1u64 << RANGE_BITS) {
            return Err(DepositError::OutOfRange);
        }
        let dep_nf = lock.deposit_nullifier();
        if self.deposit_nullifiers.contains(&dep_nf) {
            return Err(DepositError::DoubleMint);
        }
        let custody = chain
            .custody
            .entry(lock.asset)
            .or_insert_with(MirrorState::init);
        let escrowed = custody.record_escrow(lock.locked_value);
        let post = match escrowed.draw_mint(value) {
            Some(p) => p,
            None => return Err(DepositError::MintBeyondLock),
        };
        let note = mint_note(lock.asset, value, owner, randomness, key);
        *custody = post;
        self.commitments.push(note.leaf);
        self.deposit_nullifiers.push(dep_nf);
        self.pool.insert(note.clone());
        Ok(note)
    }

    /// STAGE — a shielded TRANSFER (note → note): spend an input note out of the
    /// pool and mint fresh output notes carrying the SAME total value (a private
    /// payment, no clearing). Conservation (Σ in = Σ out), nullifier consumed, value
    /// hidden. `splits` are the output values; they must sum to the input's value.
    pub fn shielded_transfer(
        &mut self,
        input: &BoundNote,
        splits: &[(u64, u64, u64, u64)], // (value, owner, randomness, key)
    ) -> Result<Vec<BoundNote>, TransferError> {
        // Consume the input (fail-closed on unbound / not-in-pool / double-spend).
        let un = self.pool.unshield(input).map_err(TransferError::Unshield)?;
        let sum_out: u64 = splits.iter().map(|s| s.0).sum();
        if sum_out != un.amount {
            // NO-MINT: outputs must sum exactly to the input (conservation).
            return Err(TransferError::NotConserving {
                in_value: un.amount,
                out_value: sum_out,
            });
        }
        let mut outs = Vec::new();
        for &(v, o, r, k) in splits {
            if v >= (1u64 << RANGE_BITS) {
                return Err(TransferError::OutOfRange);
            }
            let n = mint_note(un.asset, v, o, r, k);
            self.pool.insert(n.clone());
            outs.push(n);
        }
        Ok(outs)
    }

    /// STAGE — a single-asset shielded CLEAR: seal two pool notes as a bid + ask,
    /// run the REAL fhEgg engine, mint the fills back as conserving output notes.
    /// Returns `(outputs, V*, conserves)`. The output fill/change notes enter the pool.
    pub fn clear_pair(
        &mut self,
        bid: &BoundNote,
        bid_limit: u32,
        ask: &BoundNote,
        ask_limit: u32,
        k: usize,
    ) -> (Vec<FillOutput>, u64, bool) {
        let sealed = vec![
            note_to_order(bid, Side::Bid, bid_limit),
            note_to_order(ask, Side::Ask, ask_limit),
        ];
        let orders: Vec<Order> = sealed.iter().map(|s| s.order).collect();
        let clearing = clear(&orders, k);
        let alloc = allocate(&orders, &clearing);
        let vstar = clearing.cleared_volume;
        let outputs: Vec<FillOutput> = sealed
            .iter()
            .zip(alloc.fills.iter())
            .map(|(s, &fill)| order_to_note(s, fill))
            .collect();
        // Conservation: Σ in = Σ out (per output the fill+change = the input value),
        // and the fhEgg allocation itself conserves (buy == sell == V*).
        let sum_in: u64 = sealed.iter().map(|s| s.note.value).sum();
        let sum_out: u64 = outputs
            .iter()
            .map(|o| o.fill_note.value + o.change_note.value)
            .sum();
        let conserves = alloc.conserves() && sum_in == sum_out;
        for o in &outputs {
            self.pool.insert(o.fill_note.clone());
            self.pool.insert(o.change_note.clone());
        }
        (outputs, vstar, conserves)
    }

    /// STAGE — SETTLE on a (destination) chain: a cleared output note exits the pool
    /// (`unshield`, consuming its nullifier) and releases exactly its value from the
    /// destination chain's custody (gated on `supply ≤ locked`). Returns the
    /// post-settle custody so the caller can build the settlement statement.
    pub fn settle(
        &mut self,
        chain: &mut Chain,
        asset: u64,
        note: &BoundNote,
    ) -> Result<MirrorState, SettleError> {
        let un = self.pool.unshield(note).map_err(SettleError::Unshield)?;
        assert_eq!(un.asset, asset, "settle asset matches the note");
        let custody = chain
            .custody
            .get(&asset)
            .copied()
            .ok_or(SettleError::NoCustody)?;
        let post = custody
            .release(un.amount)
            .ok_or(SettleError::InsufficientLocked)?;
        chain.custody.insert(asset, post);
        Ok(post)
    }
}

/// Why a shielded transfer fails-closed.
#[derive(Debug, PartialEq, Eq)]
pub enum TransferError {
    Unshield(UnshieldError),
    NotConserving { in_value: u64, out_value: u64 },
    OutOfRange,
}

/// Why a settle fails-closed.
#[derive(Debug, PartialEq, Eq)]
pub enum SettleError {
    Unshield(UnshieldError),
    NoCustody,
    InsufficientLocked,
}

// ===========================================================================
// The multi-asset RING — the cross-asset price-carrying clear over shielded notes.
// ===========================================================================

/// One leg of a multi-asset ring: a shielded note offering its asset, sealed as a
/// priced fhEgg order on that asset's book. Mirror of `ShieldedClearing.lean`'s
/// `ShieldedLeg` — the matched claim (the priced order) bound to the note that backs
/// it.
pub struct RingLeg {
    pub note: BoundNote,
    pub side: Side,
    pub limit: u32,
}

/// The verdict of a multi-asset ring clear: per-asset conservation + crossing, and
/// the whole ring's balance (every leg spends a real member note, distinct
/// nullifiers).
#[derive(Debug)]
pub struct RingReport {
    /// Per-asset `(Σin, Σout, bid_fill, ask_fill, V*)`.
    pub per_asset: BTreeMap<u64, (u64, u64, u64, u64, u64)>,
    pub all_bound: bool,
    pub nullifiers_distinct: bool,
}

impl RingReport {
    /// The ring conserves iff every asset conserves (Σin=Σout, bid=ask=V*), every
    /// note is bound, and every leg's nullifier is distinct.
    pub fn conserves(&self) -> bool {
        self.all_bound
            && self.nullifiers_distinct
            && self
                .per_asset
                .values()
                .all(|&(i, o, b, a, v)| i == o && b == a && b == v)
    }
}

/// Clear a multi-asset ring: each asset's legs run the REAL fhEgg engine on their
/// own book; the fills mint back as conserving output notes; the report recomputes
/// per-asset conservation + crossing + distinct nullifiers over the whole cycle.
pub fn clear_ring(legs: &[RingLeg], k: usize) -> (Vec<FillOutput>, RingReport) {
    // FAIL-CLOSED first: a leg whose note does not open its value-binding is not a
    // real committed note — the ring cannot form over it (mirrors the note↔order
    // seal precondition). Report it rejected WITHOUT sealing (which would be
    // malformed), so a tampered leg is caught, not panicked.
    let all_bound = legs.iter().all(|l| l.note.value_binding_opens());
    let mut seen0: Vec<BabyBear> = Vec::new();
    let mut distinct0 = true;
    for leg in legs {
        if seen0.contains(&leg.note.nullifier) {
            distinct0 = false;
        } else {
            seen0.push(leg.note.nullifier);
        }
    }
    if !all_bound {
        return (
            Vec::new(),
            RingReport {
                per_asset: BTreeMap::new(),
                all_bound: false,
                nullifiers_distinct: distinct0,
            },
        );
    }

    // Group legs by asset (each asset is its own book).
    let mut by_asset: BTreeMap<u64, Vec<usize>> = BTreeMap::new();
    for (i, leg) in legs.iter().enumerate() {
        by_asset.entry(leg.note.asset).or_default().push(i);
    }
    let mut outputs: Vec<Option<FillOutput>> = (0..legs.len()).map(|_| None).collect();
    let mut per_asset: BTreeMap<u64, (u64, u64, u64, u64, u64)> = BTreeMap::new();

    for (asset, idxs) in &by_asset {
        let sealed: Vec<SealedNote> = idxs
            .iter()
            .map(|&i| note_to_order(&legs[i].note, legs[i].side, legs[i].limit))
            .collect();
        let orders: Vec<Order> = sealed.iter().map(|s| s.order).collect();
        let clearing = clear(&orders, k);
        let alloc = allocate(&orders, &clearing);
        let vstar = clearing.cleared_volume;
        let (mut in_sum, mut out_sum, mut bid_fill, mut ask_fill) = (0u64, 0u64, 0u64, 0u64);
        for (slot, (&i, (s, &fill))) in idxs
            .iter()
            .zip(sealed.iter().zip(alloc.fills.iter()))
            .enumerate()
        {
            let _ = slot;
            let out = order_to_note(s, fill);
            in_sum += s.note.value;
            out_sum += out.fill_note.value + out.change_note.value;
            match s.order.side {
                Side::Bid => bid_fill += out.fill_note.value,
                Side::Ask => ask_fill += out.fill_note.value,
            }
            outputs[i] = Some(out);
        }
        per_asset.insert(*asset, (in_sum, out_sum, bid_fill, ask_fill, vstar));
    }

    // Every input note bound + distinct nullifiers across the whole ring.
    let all_bound = legs.iter().all(|l| l.note.value_binding_opens());
    let mut seen: Vec<BabyBear> = Vec::new();
    let mut distinct = true;
    for leg in legs {
        if seen.contains(&leg.note.nullifier) {
            distinct = false;
        } else {
            seen.push(leg.note.nullifier);
        }
    }
    let outputs: Vec<FillOutput> = outputs
        .into_iter()
        .map(|o| o.expect("every leg cleared"))
        .collect();
    (
        outputs,
        RingReport {
            per_asset,
            all_bound,
            nullifiers_distinct: distinct,
        },
    )
}
