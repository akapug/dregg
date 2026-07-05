//! `verified` — the **pg-dregg-backed verified conserving store**: the durable,
//! verifiable replacement for the in-process [`ConservingLedger`](crate::ConservingLedger)
//! twin, built on breadstuffs' real `pg-dregg` verified store (the dregg-in-Postgres
//! Tier-C core).
//!
//! ## What this is (and what stays S3-gated)
//!
//! The in-process [`ConservingLedger`](crate::ConservingLedger) is an *honestly-labelled
//! twin* of a dregg `Payable`: a conserving, exactly-once value ledger that lives only in
//! one process's memory. This module replaces it with a store whose state is a **verified
//! hash chain** — the SAME anti-substitution discipline `pg-dregg`'s `dregg.commit_log`
//! gate runs (`pg_dregg::mirror::{MirrorBatch, RootChain, verify_chain_step}`), persisted
//! to a real Postgres on the shared `duroxide-pg` pool. Each settled `(lease, period)`
//! becomes one **verified turn**: a [`MirrorBatch`](pg_dregg::mirror::MirrorBatch) whose
//! cell post-images are the payer/beneficiary balance cells (Σδ = 0), chained so turn N's
//! `ledger_root` is turn N+1's `prev_root`. A tampered / reordered / replayed settlement
//! row is **refused by the chain tooth on re-validation** — the store re-validates, it
//! does not trust (`pg-dregg` README, "a store that re-validates instead of trusting").
//!
//! Two clearly-separated halves, per `docs/STAND-INS-CENSUS.md` #7 / #16:
//!
//! - **UN-GATED (this module):** the verified store + the conserving, exactly-once,
//!   crash-resumable settlement *semantics*, persisted as a `pg-dregg`-shaped verified
//!   hash chain re-validated on read. This is real, durable, and `pg-dregg`-backed.
//! - **S3-GATED (the swarm's `pg-dregg` S3 circuit flip — NOT done here):**
//!     1. the per-turn `ledger_root` being the kernel's real **Poseidon2** commitment a
//!        light client witnesses (here it is a deterministic blake3 content-binding
//!        stand-in — the census #4/#5 content-root, named not faked); and
//!     2. the settlement being a **proof-attested** on-chain dregg `Payable`
//!        (`Effect::Transfer`) whose receipt `dregg_attest_range` verifies against a pinned
//!        VK. Until S3 flips the `tier-c` proof verifier from its fail-closed stub, the
//!        attestation half attests *nothing* — the only safe default.
//!
//! See [`S3_GATED_SEAM`] for the exact, machine-readable note of what flips on with S3.
//!
//! ## The shape
//!
//! - [`VerifiedChain`] — the **postgres-free pure core**: produces + gates the verified
//!   settlement turns over the real `pg-dregg` `MirrorBatch`/`RootChain` types, computes
//!   the conserving balances, enforces exactly-once on `(lease, period)`, and re-validates
//!   a loaded chain (catching tamper/reorder/gap). Proven offline by `cargo test --features
//!   pg-dregg` — no postgres needed.
//! - [`VerifiedConservingStore`] — the **pg persistence layer**: the same core, with the
//!   chain + balances durably stored in Postgres on the shared pool, authoritative across a
//!   restart (the crash-resume / cross-instance exactly-once guarantee). Its live test is
//!   `#[ignore]` + `DATABASE_URL`-gated, exactly like the `dreggnet_meter` outbox tests.

use std::collections::HashMap;

use pg_dregg::mirror::{
    CellRow, ChainLink, ChainRefusal, MirrorBatch, RootChain, TurnRow, revalidate_replicated_chain,
};

use crate::settle::{LeaseCharge, SettleError, SettleReceipt};

/// The genesis pre-state root the settlement chain pins (all-zero: the chain's ordinal-0
/// turn declares this as its `prev_root`, matching `RootChain::new()`'s genesis acceptance).
pub const GENESIS_ROOT: [u8; 32] = [0u8; 32];

/// A precise, machine-readable note of what the `pg-dregg` **S3 circuit flip** (owned by
/// the circuit/metatheory swarm) turns on for this store — the verified-proof / on-chain
/// half this module deliberately does NOT fake. Surfaced as a constant so the seam is
/// greppable and queue-able to MORNING-REVIEW rather than buried in prose.
pub const S3_GATED_SEAM: &str = "\
pg-dregg S3 circuit flip (swarm-owned) turns on, for the verified settlement store:\n\
  1. the per-turn ledger_root becomes the kernel's real Poseidon2 commitment a light \
client witnesses (here: a blake3 content-binding stand-in, census #4/#5 content-root);\n\
  2. each settled period becomes a proof-attested on-chain dregg Payable (Effect::Transfer) \
whose receipt dregg_attest_range verifies against a pinned VK (here: the conserving move is \
real + durable + chain-gated, but NOT yet a real on-chain transfer nor proof-attested).\n\
Until then this store is the verified-hash-chain backing store with conserving, \
exactly-once, crash-resumable semantics — the un-gated half (STAND-INS-CENSUS #7/#16).";

// ---------------------------------------------------------------------------
// Content binding — the per-turn root (the S3 stand-in for Poseidon2).
// ---------------------------------------------------------------------------

/// The commitment of one holder's balance cell (the leaf of a turn's `ledger_root`).
/// Domain-separated so a balance cell can never alias a turn root. This is the blake3
/// content-binding STAND-IN for the cell's real Poseidon2 `cell_root` (S3-gated).
fn cell_root(asset: &str, holder: &str, balance: i64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dreggnet-settle/cell/v1\0");
    h.update(&(asset.len() as u64).to_le_bytes());
    h.update(asset.as_bytes());
    h.update(&(holder.len() as u64).to_le_bytes());
    h.update(holder.as_bytes());
    h.update(&balance.to_le_bytes());
    *h.finalize().as_bytes()
}

/// The post-state root of a settlement turn: binds the pre-state root, the ordinal, and the
/// full conserving post-image (both balance cell roots + the charge terms). Tampering with
/// ANY field changes this root, so the next turn's stored `prev_root` no longer chains —
/// which is exactly how [`VerifiedChain::revalidate`] / the `pg-dregg` chain tooth detects a
/// forged row. The blake3 here is the deterministic content-binding stand-in for the
/// kernel's Poseidon2 `ledger_root` (S3-gated; see [`S3_GATED_SEAM`]).
#[allow(clippy::too_many_arguments)]
fn ledger_root(
    prev_root: &[u8; 32],
    ordinal: u64,
    charge: &LeaseCharge,
    payer_cell_root: &[u8; 32],
    beneficiary_cell_root: &[u8; 32],
) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dreggnet-settle/turn/v1\0");
    h.update(prev_root);
    h.update(&ordinal.to_le_bytes());
    h.update(&(charge.lease_id.len() as u64).to_le_bytes());
    h.update(charge.lease_id.as_bytes());
    h.update(&charge.period.to_le_bytes());
    h.update(&(charge.asset.len() as u64).to_le_bytes());
    h.update(charge.asset.as_bytes());
    h.update(&charge.amount.to_le_bytes());
    h.update(payer_cell_root);
    h.update(beneficiary_cell_root);
    *h.finalize().as_bytes()
}

/// A deterministic 32-byte cell id for a `(asset, holder)` balance cell (the universal
/// `addr` projection — see `pg_dregg::mirror`). Stable so the same holder maps to the same
/// `pg-dregg` `CellRow.cell_id` across turns.
fn cell_id(asset: &str, holder: &str) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dreggnet-settle/cell-id/v1\0");
    h.update(&(asset.len() as u64).to_le_bytes());
    h.update(asset.as_bytes());
    h.update(holder.as_bytes());
    *h.finalize().as_bytes()
}

// ---------------------------------------------------------------------------
// One settled turn — the persisted unit (and the offline-test witness).
// ---------------------------------------------------------------------------

/// One settled `(lease, period)` as a verified-turn row in the chain: the conserving
/// post-image (both balances) plus the `pg-dregg` chain roots (`prev_root` ⟶ `ledger_root`)
/// the anti-substitution tooth links. This is exactly the row [`VerifiedConservingStore`]
/// persists, and the unit [`VerifiedChain::revalidate`] re-walks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SettledTurn {
    /// Dense chain ordinal (0-based, global across the store).
    pub ordinal: u64,
    pub charge: LeaseCharge,
    /// Payer balance after the conserving move (the post-image).
    pub payer_balance: i64,
    /// Beneficiary balance after the conserving move (the post-image).
    pub beneficiary_balance: i64,
    /// The chain pre-state root this turn declares (== the prior head).
    pub prev_root: [u8; 32],
    /// The chain post-state root after this turn (the next turn's `prev_root`).
    pub ledger_root: [u8; 32],
}

impl SettledTurn {
    /// Build the real `pg-dregg` [`MirrorBatch`] this turn projects to — the verified-turn
    /// post-image the chain tooth gates. The two cells are the payer + beneficiary balance
    /// post-images; the `TurnRow` carries the `prev_root`/`ledger_root` the chain links.
    /// This is what makes the store a genuine `pg-dregg` verified-turn producer, not a
    /// parallel re-implementation.
    pub fn to_mirror_batch(&self) -> Result<MirrorBatch, String> {
        let c = &self.charge;
        let payer_cell = balance_cell_row(&c.asset, &c.payer, self.payer_balance, self.ordinal);
        let benef_cell = balance_cell_row(
            &c.asset,
            &c.beneficiary,
            self.beneficiary_balance,
            self.ordinal,
        );
        let turn = TurnRow {
            ordinal: self.ordinal,
            height: self.ordinal,
            block_id: [0u8; 32],
            block_executed_up_to: self.ordinal,
            turn_hash: self.ledger_root,
            creator: cell_id(&c.asset, &c.payer),
            receipt_hash: self.ledger_root,
            ledger_root: self.ledger_root,
            prev_root: self.prev_root,
        };
        MirrorBatch::from_parts(turn, vec![payer_cell, benef_cell], vec![], vec![])
    }

    /// The `pg-dregg` chain link this turn contributes (`ordinal`, `prev_root`,
    /// `ledger_root`) — the minimal projection [`revalidate_replicated_chain`] re-walks.
    fn link(&self) -> ChainLink {
        ChainLink {
            ordinal: self.ordinal,
            prev_root: self.prev_root,
            ledger_root: self.ledger_root,
        }
    }
}

/// Project a holder's balance post-image into a `pg-dregg` [`CellRow`] (mode `balance`).
/// `last_ordinal` is re-stamped authoritatively by `MirrorBatch::from_parts`.
fn balance_cell_row(asset: &str, holder: &str, balance: i64, ordinal: u64) -> CellRow {
    CellRow {
        cell_id: cell_id(asset, holder),
        mode: "balance".to_string(),
        balance,
        nonce: 0,
        fields: balance.to_le_bytes().to_vec(),
        fields_json: Some(format!("{{\"asset\":{asset:?},\"balance\":{balance}}}")),
        heap: None,
        program: None,
        verification_key: None,
        permissions_json: None,
        delegate: None,
        lifecycle: "active".to_string(),
        last_ordinal: ordinal,
        cell_root: cell_root(asset, holder, balance),
    }
}

// ---------------------------------------------------------------------------
// VerifiedChain — the postgres-free pure core (offline-proven).
// ---------------------------------------------------------------------------

/// The postgres-free verified conserving store core. Produces + gates verified settlement
/// turns over the real `pg-dregg` `MirrorBatch`/`RootChain` types, keeps the conserving
/// balances (Σδ = 0), and enforces exactly-once on `(lease, period)`. This is the faithful
/// twin of [`ConservingLedger`](crate::ConservingLedger) — same semantics, now carried by a
/// verified hash chain that re-validates instead of trusting.
#[derive(Debug)]
pub struct VerifiedChain {
    /// The `pg-dregg` anti-substitution chain head (the SAME tooth `dregg.commit_log` runs).
    chain: RootChain,
    /// `(asset, holder) -> balance` — the materialized conserving state.
    balances: HashMap<(String, String), i64>,
    /// `(lease_id, period) -> receipt` — the exactly-once idempotency record.
    settled: HashMap<(String, i64), SettleReceipt>,
    /// The chain of settled turns, in ordinal order (the audit log / persistence unit).
    turns: Vec<SettledTurn>,
}

impl Default for VerifiedChain {
    fn default() -> Self {
        Self::new()
    }
}

impl VerifiedChain {
    /// A fresh chain expecting genesis (ordinal 0, head [`GENESIS_ROOT`]).
    pub fn new() -> VerifiedChain {
        VerifiedChain {
            chain: RootChain::new(),
            balances: HashMap::new(),
            settled: HashMap::new(),
            turns: Vec::new(),
        }
    }

    /// Credit `holder` with `amount` of `asset` (fund the lessee's reserve — the lease
    /// budget). Funding is the reserve mint, exactly as [`ConservingLedger::fund`]; it is
    /// NOT a conserving turn (it changes `total_supply`), so it is recorded in the balance
    /// state but not the settlement chain.
    pub fn fund(&mut self, asset: &str, holder: &str, amount: i64) -> i64 {
        let e = self
            .balances
            .entry((asset.to_string(), holder.to_string()))
            .or_insert(0);
        *e += amount;
        *e
    }

    /// `holder`'s balance of `asset` (`0` if none).
    pub fn balance(&self, asset: &str, holder: &str) -> i64 {
        *self
            .balances
            .get(&(asset.to_string(), holder.to_string()))
            .unwrap_or(&0)
    }

    /// The sum of every holder's balance of `asset` — the conservation witness. Funding
    /// aside, every settlement leaves this unchanged (Σδ = 0).
    pub fn total_supply(&self, asset: &str) -> i64 {
        self.balances
            .iter()
            .filter(|((a, _), _)| a == asset)
            .map(|(_, v)| *v)
            .sum()
    }

    /// The current chain head (the post-state root of the last settled turn), or
    /// [`GENESIS_ROOT`] before any settlement.
    pub fn head(&self) -> [u8; 32] {
        self.chain.head().unwrap_or(GENESIS_ROOT)
    }

    /// The next ordinal the chain expects (== the number of settled turns).
    pub fn next_ordinal(&self) -> u64 {
        self.chain.next_ordinal()
    }

    /// The settled turns in ordinal order (the persistence / audit unit).
    pub fn turns(&self) -> &[SettledTurn] {
        &self.turns
    }

    /// The total amount settled for a lease across all its periods.
    pub fn settled_total(&self, lease_id: &str) -> i64 {
        self.settled
            .iter()
            .filter(|((l, _), _)| l == lease_id)
            .map(|(_, r)| r.amount)
            .sum()
    }

    /// Settle one period's charge as a verified, chained, conserving turn.
    ///
    /// Conserving (debit payer == credit beneficiary, Σδ = 0), exactly-once on
    /// `(lease, period)` (a re-settle returns the recorded receipt with `replayed`), and
    /// **chain-gated**: the produced [`MirrorBatch`] must extend the `pg-dregg` [`RootChain`]
    /// (the anti-substitution tooth) or the settle is refused. On success the head advances
    /// to the turn's `ledger_root` and the [`SettledTurn`] is appended (for persistence).
    pub fn settle(&mut self, charge: &LeaseCharge) -> Result<SettleReceipt, SettleError> {
        let (receipt, _turn) = self.settle_turn(charge)?;
        Ok(receipt)
    }

    /// Like [`settle`](Self::settle) but also returns the [`SettledTurn`] row to persist
    /// (the pg layer needs it; the offline path can ignore it). On a replay the returned
    /// turn is the already-recorded one.
    pub fn settle_turn(
        &mut self,
        charge: &LeaseCharge,
    ) -> Result<(SettleReceipt, SettledTurn), SettleError> {
        if charge.amount <= 0 {
            return Err(SettleError::NonPositiveAmount(charge.amount));
        }
        let key = (charge.lease_id.clone(), charge.period);

        // Exactly-once: a settled key replays its recorded receipt; a conflicting re-use is
        // a programming error.
        if let Some(prior) = self.settled.get(&key) {
            if prior.amount != charge.amount || prior.asset != charge.asset {
                return Err(SettleError::Conflict {
                    lease_id: charge.lease_id.clone(),
                    period: charge.period,
                });
            }
            let mut replay = prior.clone();
            replay.replayed = true;
            let turn = self
                .turns
                .iter()
                .find(|t| t.charge.lease_id == charge.lease_id && t.charge.period == charge.period)
                .cloned()
                .expect("a settled receipt has a recorded turn");
            return Ok((replay, turn));
        }

        // The conserving move, computed but not yet committed to balances (we commit only
        // after the chain tooth accepts the turn, so a refused turn moves nothing).
        let payer_key = (charge.asset.clone(), charge.payer.clone());
        let payer_balance = *self.balances.get(&payer_key).unwrap_or(&0);
        if payer_balance < charge.amount {
            return Err(SettleError::InsufficientFunds {
                payer: charge.payer.clone(),
                asset: charge.asset.clone(),
                balance: payer_balance,
                needed: charge.amount,
            });
        }
        let new_payer = payer_balance - charge.amount;
        let benef_key = (charge.asset.clone(), charge.beneficiary.clone());
        let new_benef = *self.balances.get(&benef_key).unwrap_or(&0) + charge.amount;

        // Build the verified turn + gate it through the real pg-dregg chain tooth.
        let ordinal = self.chain.next_ordinal();
        let prev_root = self.head();
        let pcr = cell_root(&charge.asset, &charge.payer, new_payer);
        let bcr = cell_root(&charge.asset, &charge.beneficiary, new_benef);
        let root = ledger_root(&prev_root, ordinal, charge, &pcr, &bcr);
        let turn = SettledTurn {
            ordinal,
            charge: charge.clone(),
            payer_balance: new_payer,
            beneficiary_balance: new_benef,
            prev_root,
            ledger_root: root,
        };
        let batch = turn
            .to_mirror_batch()
            .map_err(|e| SettleError::Backend(format!("malformed settlement turn: {e}")))?;
        self.chain
            .extend(&batch)
            .map_err(|r| SettleError::Backend(format!("chain tooth refused settlement: {r}")))?;

        // Accepted: commit the conserving move + record exactly-once + append the turn.
        self.balances.insert(payer_key, new_payer);
        self.balances.insert(benef_key, new_benef);
        let receipt = SettleReceipt {
            lease_id: charge.lease_id.clone(),
            period: charge.period,
            asset: charge.asset.clone(),
            amount: charge.amount,
            payer_balance: new_payer,
            beneficiary_balance: new_benef,
            replayed: false,
        };
        self.settled.insert(key, receipt.clone());
        self.turns.push(turn.clone());
        Ok((receipt, turn))
    }

    /// Re-validate a chain of [`SettledTurn`] rows (e.g. loaded from Postgres) through the
    /// real `pg-dregg` anti-substitution tooth, AND rebuild the conserving balances + the
    /// exactly-once record from them. This is the store's "re-validate, don't trust" load
    /// path: a tampered / reordered / gapped / truncated chain is refused HERE, locally,
    /// before any balance is trusted.
    ///
    /// The tamper-detection is two-layered, both real `pg-dregg` mechanics:
    /// 1. each row's stored `ledger_root` must equal the root RECOMPUTED from its content
    ///    (a balance/amount tamper changes the recompute ⇒ caught);
    /// 2. the recomputed roots must form a dense hash chain from genesis
    ///    ([`revalidate_replicated_chain`] — the subscriber-side tooth), so a reorder /
    ///    substitution / gap is caught even if a row's own self-binding still held.
    pub fn revalidate(turns: Vec<SettledTurn>) -> Result<VerifiedChain, ChainRefusal> {
        // Layer 1: each row self-binds (stored root == recomputed root from content).
        let mut links: Vec<ChainLink> = Vec::with_capacity(turns.len());
        for t in &turns {
            let c = &t.charge;
            let pcr = cell_root(&c.asset, &c.payer, t.payer_balance);
            let bcr = cell_root(&c.asset, &c.beneficiary, t.beneficiary_balance);
            let recomputed = ledger_root(&t.prev_root, t.ordinal, c, &pcr, &bcr);
            if recomputed != t.ledger_root {
                return Err(ChainRefusal::Malformed(format!(
                    "turn ordinal {} ledger_root does not bind its content (tampered post-image)",
                    t.ordinal
                )));
            }
            links.push(t.link());
        }
        // Layer 2: the recomputed roots form a dense chain from genesis.
        let count = links.len() as u64;
        revalidate_replicated_chain(GENESIS_ROOT, &links, Some(count))?;

        // The chain re-validates — replay it into a live core (balances + exactly-once +
        // head). Funding is NOT in the chain, so balances reconstructed here are the
        // *settlement deltas*; a caller that needs absolute balances re-applies funding.
        let mut vc = VerifiedChain::new();
        for t in turns {
            let c = &t.charge;
            *vc.balances
                .entry((c.asset.clone(), c.payer.clone()))
                .or_insert(0) -= c.amount;
            *vc.balances
                .entry((c.asset.clone(), c.beneficiary.clone()))
                .or_insert(0) += c.amount;
            let batch = t.to_mirror_batch().map_err(ChainRefusal::Malformed)?;
            vc.chain.extend(&batch)?;
            vc.settled.insert(
                (c.lease_id.clone(), c.period),
                SettleReceipt {
                    lease_id: c.lease_id.clone(),
                    period: c.period,
                    asset: c.asset.clone(),
                    amount: c.amount,
                    payer_balance: t.payer_balance,
                    beneficiary_balance: t.beneficiary_balance,
                    replayed: true,
                },
            );
            vc.turns.push(t);
        }
        Ok(vc)
    }

    /// Recompute the conserving balances implied by `turns` (a re-validated chain)
    /// plus the recorded `funded` reserves, and verify the claimed `stored` balance
    /// table matches — the **balance cross-check** (#4 / S9-1).
    ///
    /// The stored `dreggnet_settle_balances` table is NOT an independent authority:
    /// it is a materialized cache of `funding + Σ settlement-deltas`. Because every
    /// chain post-image self-binds its `amount` into the `ledger_root`
    /// ([`revalidate`](Self::revalidate)'s layer 1), the per-`(asset,holder)` delta
    /// is trustworthy once the chain re-validates; and funding is its own authority.
    /// So a balance the table claims that does NOT equal `funded + Σ deltas` is a
    /// tamper — a DB-write attacker who `UPDATE`s a balance to spend value it was
    /// never funded for breaks the conservation identity here and the load is
    /// **refused**, rather than the inflated balance being trusted to gate a spend.
    ///
    /// (The residual — an adversary who rechains the unkeyed chain AND the funding
    /// AND the balance table all-consistently — is the design-declared S3 ceiling,
    /// [`S3_GATED_SEAM`]: a keyed/anchored root. This cross-check closes the
    /// single-table tamper the unchained balance table previously allowed.)
    pub fn reconcile_balances(
        turns: &[SettledTurn],
        funded: &HashMap<(String, String), i64>,
        stored: &HashMap<(String, String), i64>,
    ) -> Result<HashMap<(String, String), i64>, ChainRefusal> {
        let mut expected = funded.clone();
        for t in turns {
            let c = &t.charge;
            *expected
                .entry((c.asset.clone(), c.payer.clone()))
                .or_insert(0) -= c.amount;
            *expected
                .entry((c.asset.clone(), c.beneficiary.clone()))
                .or_insert(0) += c.amount;
        }
        // Every holder named in either map must agree (absent ⇒ 0): a balance the
        // table carries that the chain + funding do not imply (or vice-versa) is the
        // tamper.
        let mut keys: std::collections::BTreeSet<(String, String)> = expected
            .keys()
            .cloned()
            .chain(stored.keys().cloned())
            .collect();
        for k in std::mem::take(&mut keys) {
            let e = expected.get(&k).copied().unwrap_or(0);
            let s = stored.get(&k).copied().unwrap_or(0);
            if e != s {
                return Err(ChainRefusal::Malformed(format!(
                    "balance for ({}, {}) is {s} in the stored table but the re-validated \
                     chain + funding imply {e} (tampered/unchained balance table)",
                    k.0, k.1
                )));
            }
        }
        Ok(expected)
    }
}

// ---------------------------------------------------------------------------
// VerifiedConservingStore — the Postgres persistence layer (durable, restart-safe).
// ---------------------------------------------------------------------------

/// The pg-dregg-backed verified conserving store, persisting the [`VerifiedChain`] (the
/// settlement turn chain + the conserving balances) to a real Postgres on the shared
/// `duroxide-pg` pool. This is the durable, cross-restart, cross-instance twin of
/// [`ConservingLedger`](crate::ConservingLedger): the chain head + balances are
/// authoritative IN POSTGRES, so a settler restart (or a second instance on the same DB)
/// sees prior settlements and never double-charges — the exactly-once property is the
/// Postgres `UNIQUE (lease_id, period)` constraint, not an in-memory map.
///
/// The settlement chain is **scoped per lease**: each lease's settled periods form their
/// own `pg-dregg` hash chain (turn N's `ledger_root` is turn N+1's `prev_root`), so
/// re-validation is tenant-isolated and a per-lease advisory lock lets distinct leases
/// settle concurrently. The conserving **balances** are cross-lease (a payer pays across
/// many leases), so they live in their own materialized table.
///
/// Each [`settle`](Self::settle) is ONE Postgres transaction (per-lease-advisory-lock
/// serialized so the dense per-lease ordinals + the anti-substitution chaining hold under
/// concurrency): it reads that lease's chain head, computes the conserving post-image, gates
/// the produced [`MirrorBatch`] through the real `pg-dregg` chain tooth, and commits the turn
/// row + the balance moves together. [`revalidate`](Self::revalidate) re-walks one lease's
/// persisted chain through the same tooth — the store re-validates its own Postgres state, it
/// does not trust it.
///
/// **S3-gated half (NOT here):** see [`S3_GATED_SEAM`] — the real Poseidon2 `ledger_root` a
/// light client witnesses, and the proof-attested on-chain `Payable`, flip on with the
/// swarm's `pg-dregg` S3 circuit flip.
#[cfg(feature = "pg")]
pub struct VerifiedConservingStore {
    pool: sqlx::PgPool,
}

#[cfg(feature = "pg")]
impl VerifiedConservingStore {
    /// The chain table — the verified settlement turn log (the `pg-dregg` mirror shape).
    pub const CHAIN_TABLE: &'static str = "dreggnet_settle_chain";
    /// The materialized conserving balances (`(asset, holder) -> balance`).
    pub const BALANCE_TABLE: &'static str = "dreggnet_settle_balances";
    /// The **funding authority** (`(asset, holder) -> total funded reserve`). Written
    /// only by [`fund`](Self::fund) (never by a settlement), it is the independent
    /// baseline the balance cross-check ([`revalidate_balances`](Self::revalidate_balances),
    /// #4 / S9-1) reconciles against: `balance` must equal `funded + Σ chain-deltas`,
    /// so a tampered `BALANCE_TABLE` row no longer authorizes a spend on its own.
    pub const FUNDING_TABLE: &'static str = "dreggnet_settle_funding";
    /// The per-lease **head authority** (`lease_id -> (next_ordinal, head_root)`).
    /// Advanced in the same transaction as each settle, it is the INDEPENDENT
    /// expected-count source the truncation guard ([`revalidate`](Self::revalidate),
    /// #5 / S9-2) feeds to `revalidate_expecting` — so a `DELETE` of the chain tail
    /// no longer derives its own (always-matching) expected count from the truncated
    /// read.
    pub const HEAD_TABLE: &'static str = "dreggnet_settle_heads";

    /// A per-lease advisory-lock key, so settles WITHIN a lease serialize (dense per-lease
    /// ordinals + intact chaining) while DISTINCT leases settle concurrently. Domain-mixed
    /// with a balance-table key so the chain lock never aliases the schema lock.
    fn settle_lock_key(lease_id: &str) -> i64 {
        let mut h = blake3::Hasher::new();
        h.update(b"dreggnet-settle/lock/v1\0");
        h.update(lease_id.as_bytes());
        i64::from_le_bytes(h.finalize().as_bytes()[..8].try_into().unwrap())
    }

    /// Open the store on `pool`, creating its tables if absent. Idempotent; safe on every
    /// startup. The tables live alongside the `duroxide-pg` checkpoint schema + the
    /// `dreggnet_meter` outbox in the same database, so a real dregg `Payable` settlement
    /// (the S3-gated half) reads them in the same Postgres.
    pub async fn open(pool: sqlx::PgPool) -> anyhow::Result<VerifiedConservingStore> {
        let mut tx = pool.begin().await?;
        // Serialize concurrent creators against the system catalogs (parallel tests).
        sqlx::query("SELECT pg_advisory_xact_lock($1)")
            .bind(0x6452_6547_5343_4830_i64) // "dRegSCH0"
            .execute(&mut *tx)
            .await?;
        sqlx::query(&format!(
            "CREATE TABLE IF NOT EXISTS {} (
                 lease_id            TEXT        NOT NULL,
                 ordinal             BIGINT      NOT NULL,
                 period              BIGINT      NOT NULL,
                 asset               TEXT        NOT NULL,
                 payer               TEXT        NOT NULL,
                 beneficiary         TEXT        NOT NULL,
                 amount              BIGINT      NOT NULL,
                 payer_balance       BIGINT      NOT NULL,
                 beneficiary_balance BIGINT      NOT NULL,
                 prev_root           BYTEA       NOT NULL,
                 ledger_root         BYTEA       NOT NULL,
                 settled_at          TIMESTAMPTZ NOT NULL DEFAULT now(),
                 PRIMARY KEY (lease_id, ordinal),
                 UNIQUE (lease_id, period)
             )",
            Self::CHAIN_TABLE
        ))
        .execute(&mut *tx)
        .await?;
        sqlx::query(&format!(
            "CREATE TABLE IF NOT EXISTS {} (
                 asset   TEXT   NOT NULL,
                 holder  TEXT   NOT NULL,
                 balance BIGINT NOT NULL,
                 PRIMARY KEY (asset, holder)
             )",
            Self::BALANCE_TABLE
        ))
        .execute(&mut *tx)
        .await?;
        // The funding authority — the independent baseline for the #4 balance
        // cross-check. Written only on fund, never by a settlement.
        sqlx::query(&format!(
            "CREATE TABLE IF NOT EXISTS {} (
                 asset  TEXT   NOT NULL,
                 holder TEXT   NOT NULL,
                 funded BIGINT NOT NULL,
                 PRIMARY KEY (asset, holder)
             )",
            Self::FUNDING_TABLE
        ))
        .execute(&mut *tx)
        .await?;
        // The per-lease head authority — the independent expected-count source for
        // the #5 truncation guard. One row per lease, advanced with each settle.
        sqlx::query(&format!(
            "CREATE TABLE IF NOT EXISTS {} (
                 lease_id     TEXT   NOT NULL,
                 next_ordinal BIGINT NOT NULL,
                 head_root    BYTEA  NOT NULL,
                 PRIMARY KEY (lease_id)
             )",
            Self::HEAD_TABLE
        ))
        .execute(&mut *tx)
        .await?;
        tx.commit().await?;
        Ok(VerifiedConservingStore { pool })
    }

    /// The pool this store persists onto (so a caller can share it with the meter outbox /
    /// the duroxide-pg provider).
    pub fn pool(&self) -> &sqlx::PgPool {
        &self.pool
    }

    /// Credit `holder` with `amount` of `asset` — the lessee's funded reserve. Upsert, one
    /// transaction. Funding is the reserve (it changes `total_supply`), not a conserving
    /// chain turn — exactly as [`VerifiedChain::fund`].
    pub async fn fund(&self, asset: &str, holder: &str, amount: i64) -> anyhow::Result<i64> {
        let mut tx = self.pool.begin().await?;
        // The spendable balance (the cache the settle path reads + moves).
        let row: (i64,) = sqlx::query_as(&format!(
            "INSERT INTO {} (asset, holder, balance) VALUES ($1, $2, $3)
                 ON CONFLICT (asset, holder) DO UPDATE SET balance = {0}.balance + EXCLUDED.balance
             RETURNING balance",
            Self::BALANCE_TABLE
        ))
        .bind(asset)
        .bind(holder)
        .bind(amount)
        .fetch_one(&mut *tx)
        .await?;
        // The funding authority (the independent #4 baseline): kept in lock-step with
        // the reserve, but NEVER touched by a settlement — so `balance` provably
        // equals `funded + Σ chain-deltas`, and a lone `UPDATE` of the balance table
        // breaks that identity on re-validation.
        sqlx::query(&format!(
            "INSERT INTO {} (asset, holder, funded) VALUES ($1, $2, $3)
                 ON CONFLICT (asset, holder) DO UPDATE SET funded = {0}.funded + EXCLUDED.funded",
            Self::FUNDING_TABLE
        ))
        .bind(asset)
        .bind(holder)
        .bind(amount)
        .execute(&mut *tx)
        .await?;
        tx.commit().await?;
        Ok(row.0)
    }

    /// `holder`'s persisted balance of `asset` (`0` if none).
    pub async fn balance(&self, asset: &str, holder: &str) -> anyhow::Result<i64> {
        let row: Option<(i64,)> = sqlx::query_as(&format!(
            "SELECT balance FROM {} WHERE asset = $1 AND holder = $2",
            Self::BALANCE_TABLE
        ))
        .bind(asset)
        .bind(holder)
        .fetch_optional(&self.pool)
        .await?;
        Ok(row.map(|r| r.0).unwrap_or(0))
    }

    /// The sum of every holder's balance of `asset` — the conservation witness.
    pub async fn total_supply(&self, asset: &str) -> anyhow::Result<i64> {
        let row: (i64,) = sqlx::query_as(&format!(
            "SELECT COALESCE(SUM(balance), 0)::BIGINT FROM {} WHERE asset = $1",
            Self::BALANCE_TABLE
        ))
        .bind(asset)
        .fetch_one(&self.pool)
        .await?;
        Ok(row.0)
    }

    /// Settle one period's charge as a verified, chained, conserving turn, persisted in ONE
    /// Postgres transaction. Conserving (Σδ = 0), exactly-once on the `UNIQUE (lease_id,
    /// period)` constraint (a re-settle — a crash re-dispatch, a second instance — returns
    /// the recorded receipt, no second move), and chain-gated through the real `pg-dregg`
    /// anti-substitution tooth before the row commits.
    pub async fn settle(&self, charge: &LeaseCharge) -> Result<SettleReceipt, SettleError> {
        if charge.amount <= 0 {
            return Err(SettleError::NonPositiveAmount(charge.amount));
        }
        let mut tx = self
            .pool
            .begin()
            .await
            .map_err(|e| SettleError::Backend(format!("settle: begin: {e}")))?;

        // Serialize settles WITHIN this lease so its chain ordinals stay dense + the chaining
        // holds under concurrent settlers (the conserving move + the chain extend are one
        // critical section, exactly as the in-process ledger's lock-across-the-move
        // discipline). Distinct leases take distinct lock keys, so they settle concurrently.
        sqlx::query("SELECT pg_advisory_xact_lock($1)")
            .bind(Self::settle_lock_key(&charge.lease_id))
            .execute(&mut *tx)
            .await
            .map_err(|e| SettleError::Backend(format!("settle: lock: {e}")))?;

        // Exactly-once: a settled (lease, period) replays its recorded receipt; a
        // conflicting re-use (different terms) is a programming error.
        let existing: Option<(i64, i64, String, i64, i64)> = sqlx::query_as(&format!(
            "SELECT amount, period, asset, payer_balance, beneficiary_balance
                 FROM {} WHERE lease_id = $1 AND period = $2",
            Self::CHAIN_TABLE
        ))
        .bind(&charge.lease_id)
        .bind(charge.period)
        .fetch_optional(&mut *tx)
        .await
        .map_err(|e| SettleError::Backend(format!("settle: select existing: {e}")))?;
        if let Some((amount, _period, asset, payer_balance, beneficiary_balance)) = existing {
            if amount != charge.amount || asset != charge.asset {
                return Err(SettleError::Conflict {
                    lease_id: charge.lease_id.clone(),
                    period: charge.period,
                });
            }
            return Ok(SettleReceipt {
                lease_id: charge.lease_id.clone(),
                period: charge.period,
                asset: charge.asset.clone(),
                amount,
                payer_balance,
                beneficiary_balance,
                replayed: true,
            });
        }

        // Read THIS LEASE's chain head (the last accepted turn) — the prev_root the new turn
        // chains onto, and the next dense per-lease ordinal.
        let head: Option<(i64, Vec<u8>)> = sqlx::query_as(&format!(
            "SELECT ordinal, ledger_root FROM {} WHERE lease_id = $1 ORDER BY ordinal DESC LIMIT 1",
            Self::CHAIN_TABLE
        ))
        .bind(&charge.lease_id)
        .fetch_optional(&mut *tx)
        .await
        .map_err(|e| SettleError::Backend(format!("settle: select head: {e}")))?;
        let (next_ordinal, prev_root) = match head {
            Some((ord, root)) => {
                let r: [u8; 32] = root
                    .try_into()
                    .map_err(|_| SettleError::Backend("settle: head root not 32 bytes".into()))?;
                ((ord + 1) as u64, r)
            }
            None => (0u64, GENESIS_ROOT),
        };

        // The conserving move on the persisted balances.
        let payer_balance = self
            .balance_in_tx(&mut tx, &charge.asset, &charge.payer)
            .await?;
        if payer_balance < charge.amount {
            return Err(SettleError::InsufficientFunds {
                payer: charge.payer.clone(),
                asset: charge.asset.clone(),
                balance: payer_balance,
                needed: charge.amount,
            });
        }
        let new_payer = payer_balance - charge.amount;
        let beneficiary_prior = self
            .balance_in_tx(&mut tx, &charge.asset, &charge.beneficiary)
            .await?;
        let new_benef = beneficiary_prior + charge.amount;

        // Build the verified turn + gate it through the real pg-dregg chain tooth before
        // anything commits.
        let pcr = cell_root(&charge.asset, &charge.payer, new_payer);
        let bcr = cell_root(&charge.asset, &charge.beneficiary, new_benef);
        let root = ledger_root(&prev_root, next_ordinal, charge, &pcr, &bcr);
        let turn = SettledTurn {
            ordinal: next_ordinal,
            charge: charge.clone(),
            payer_balance: new_payer,
            beneficiary_balance: new_benef,
            prev_root,
            ledger_root: root,
        };
        let batch = turn
            .to_mirror_batch()
            .map_err(|e| SettleError::Backend(format!("settle: malformed turn: {e}")))?;
        let mut chain = if next_ordinal == 0 {
            RootChain::new()
        } else {
            RootChain::resume(prev_root, next_ordinal)
        };
        chain
            .extend(&batch)
            .map_err(|r| SettleError::Backend(format!("settle: chain tooth refused: {r}")))?;

        // Persist the turn row.
        sqlx::query(&format!(
            "INSERT INTO {} (ordinal, lease_id, period, asset, payer, beneficiary, amount,
                 payer_balance, beneficiary_balance, prev_root, ledger_root)
             VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11)",
            Self::CHAIN_TABLE
        ))
        .bind(next_ordinal as i64)
        .bind(&charge.lease_id)
        .bind(charge.period)
        .bind(&charge.asset)
        .bind(&charge.payer)
        .bind(&charge.beneficiary)
        .bind(charge.amount)
        .bind(new_payer)
        .bind(new_benef)
        .bind(&prev_root[..])
        .bind(&root[..])
        .execute(&mut *tx)
        .await
        .map_err(|e| SettleError::Backend(format!("settle: insert turn: {e}")))?;

        // Commit the conserving balance moves in the same transaction.
        self.upsert_balance(&mut tx, &charge.asset, &charge.payer, new_payer)
            .await?;
        self.upsert_balance(&mut tx, &charge.asset, &charge.beneficiary, new_benef)
            .await?;

        // Advance the INDEPENDENT per-lease head authority (the #5 truncation guard's
        // expected-count source) in the same transaction as the turn row. After this
        // turn the lease has `next_ordinal + 1` dense turns; a later `DELETE` of the
        // chain tail leaves this count behind, so re-validation refuses the short read.
        sqlx::query(&format!(
            "INSERT INTO {} (lease_id, next_ordinal, head_root) VALUES ($1, $2, $3)
                 ON CONFLICT (lease_id) DO UPDATE SET
                     next_ordinal = EXCLUDED.next_ordinal,
                     head_root    = EXCLUDED.head_root",
            Self::HEAD_TABLE
        ))
        .bind(&charge.lease_id)
        .bind((next_ordinal + 1) as i64)
        .bind(&root[..])
        .execute(&mut *tx)
        .await
        .map_err(|e| SettleError::Backend(format!("settle: advance head: {e}")))?;

        tx.commit()
            .await
            .map_err(|e| SettleError::Backend(format!("settle: commit: {e}")))?;

        Ok(SettleReceipt {
            lease_id: charge.lease_id.clone(),
            period: charge.period,
            asset: charge.asset.clone(),
            amount: charge.amount,
            payer_balance: new_payer,
            beneficiary_balance: new_benef,
            replayed: false,
        })
    }

    /// The total amount settled for a lease across all its persisted periods.
    pub async fn settled_total(&self, lease_id: &str) -> anyhow::Result<i64> {
        let row: (i64,) = sqlx::query_as(&format!(
            "SELECT COALESCE(SUM(amount), 0)::BIGINT FROM {} WHERE lease_id = $1",
            Self::CHAIN_TABLE
        ))
        .bind(lease_id)
        .fetch_one(&self.pool)
        .await?;
        Ok(row.0)
    }

    /// Load one lease's persisted settlement chain and re-validate it through the real
    /// `pg-dregg` anti-substitution tooth ([`VerifiedChain::revalidate_expecting`]). Returns
    /// the re-validated in-memory [`VerifiedChain`] (settlement-delta balances + head) on
    /// success, or the [`ChainRefusal`] naming the first row that does not chain — a
    /// tampered / reordered / gapped / truncated persisted chain is caught HERE, before the
    /// store is trusted. This is the store re-validating its own Postgres state, per lease.
    pub async fn revalidate(
        &self,
        lease_id: &str,
    ) -> anyhow::Result<Result<VerifiedChain, ChainRefusal>> {
        // The INDEPENDENT expected count (#5 / S9-2): the per-lease head authority's
        // `next_ordinal` is the count of dense turns the store committed, advanced in
        // each settle's transaction and NEVER derived from the chain read. A `DELETE`
        // of the chain tail does not move it, so the truncation guard below bites.
        // (Deriving the count from the truncated read itself — the bug — made the
        // guard `rows.len() != rows.len()`, always false.)
        let expect: Option<(i64,)> = sqlx::query_as(&format!(
            "SELECT next_ordinal FROM {} WHERE lease_id = $1",
            Self::HEAD_TABLE
        ))
        .bind(lease_id)
        .fetch_optional(&self.pool)
        .await?;
        let expect_count = expect.map(|r| r.0 as u64).unwrap_or(0);

        let rows = sqlx::query_as::<_, ChainRowSql>(&format!(
            "SELECT ordinal, lease_id, period, asset, payer, beneficiary, amount,
                 payer_balance, beneficiary_balance, prev_root, ledger_root
                 FROM {} WHERE lease_id = $1 ORDER BY ordinal",
            Self::CHAIN_TABLE
        ))
        .bind(lease_id)
        .fetch_all(&self.pool)
        .await?;
        let turns: Result<Vec<SettledTurn>, anyhow::Error> =
            rows.into_iter().map(|r| r.into_turn()).collect();
        Ok(VerifiedChain::revalidate_expecting(turns?, expect_count))
    }

    /// Re-validate every lease's chain AND cross-check the stored conserving balances
    /// against them (#4 / S9-1). The store-wide companion to [`revalidate`](Self::revalidate):
    ///
    /// 1. each lease's persisted chain re-validates through the anti-substitution
    ///    tooth (self-binding + dense-chain + the independent truncation count), so
    ///    every settlement `amount` is trustworthy;
    /// 2. the materialized `BALANCE_TABLE` must equal `funded + Σ chain-deltas` for
    ///    every `(asset, holder)` ([`VerifiedChain::reconcile_balances`]).
    ///
    /// A DB-write attacker who `UPDATE`s a `BALANCE_TABLE` row to grant themselves
    /// spendable value (S9-1) breaks (2) — the load is **refused** here rather than
    /// the forged balance being trusted to authorize a charge.
    pub async fn revalidate_balances(&self) -> anyhow::Result<Result<(), ChainRefusal>> {
        // The leases present in the chain — re-validate each (proves every amount).
        let leases: Vec<(String,)> = sqlx::query_as(&format!(
            "SELECT DISTINCT lease_id FROM {}",
            Self::CHAIN_TABLE
        ))
        .fetch_all(&self.pool)
        .await?;
        for (lease_id,) in &leases {
            if let Err(r) = self.revalidate(lease_id).await? {
                return Ok(Err(r));
            }
        }

        // Σ settlement-deltas per (asset, holder), from the (now re-validated) chain.
        let turn_rows: Vec<(String, String, String, i64)> = sqlx::query_as(&format!(
            "SELECT asset, payer, beneficiary, amount FROM {}",
            Self::CHAIN_TABLE
        ))
        .fetch_all(&self.pool)
        .await?;
        let turns: Vec<SettledTurn> = turn_rows
            .into_iter()
            .map(|(asset, payer, beneficiary, amount)| SettledTurn {
                ordinal: 0,
                charge: LeaseCharge::new(payer, beneficiary, asset, String::new(), 0, amount),
                payer_balance: 0,
                beneficiary_balance: 0,
                prev_root: GENESIS_ROOT,
                ledger_root: GENESIS_ROOT,
            })
            .collect();

        // The independent funding baseline + the stored (cache) balances.
        let funded_rows: Vec<(String, String, i64)> = sqlx::query_as(&format!(
            "SELECT asset, holder, funded FROM {}",
            Self::FUNDING_TABLE
        ))
        .fetch_all(&self.pool)
        .await?;
        let funded: HashMap<(String, String), i64> = funded_rows
            .into_iter()
            .map(|(a, h, f)| ((a, h), f))
            .collect();
        let stored_rows: Vec<(String, String, i64)> = sqlx::query_as(&format!(
            "SELECT asset, holder, balance FROM {}",
            Self::BALANCE_TABLE
        ))
        .fetch_all(&self.pool)
        .await?;
        let stored: HashMap<(String, String), i64> = stored_rows
            .into_iter()
            .map(|(a, h, b)| ((a, h), b))
            .collect();

        Ok(VerifiedChain::reconcile_balances(&turns, &funded, &stored).map(|_| ()))
    }

    /// One lease's persisted chain head (post-state root of its last settled turn), or
    /// [`GENESIS_ROOT`] before any settlement on that lease.
    pub async fn head(&self, lease_id: &str) -> anyhow::Result<[u8; 32]> {
        let row: Option<(Vec<u8>,)> = sqlx::query_as(&format!(
            "SELECT ledger_root FROM {} WHERE lease_id = $1 ORDER BY ordinal DESC LIMIT 1",
            Self::CHAIN_TABLE
        ))
        .bind(lease_id)
        .fetch_optional(&self.pool)
        .await?;
        match row {
            Some((root,)) => root
                .try_into()
                .map_err(|_| anyhow::anyhow!("head root not 32 bytes")),
            None => Ok(GENESIS_ROOT),
        }
    }

    async fn balance_in_tx(
        &self,
        tx: &mut sqlx::Transaction<'_, sqlx::Postgres>,
        asset: &str,
        holder: &str,
    ) -> Result<i64, SettleError> {
        let row: Option<(i64,)> = sqlx::query_as(&format!(
            "SELECT balance FROM {} WHERE asset = $1 AND holder = $2",
            Self::BALANCE_TABLE
        ))
        .bind(asset)
        .bind(holder)
        .fetch_optional(&mut **tx)
        .await
        .map_err(|e| SettleError::Backend(format!("settle: read balance: {e}")))?;
        Ok(row.map(|r| r.0).unwrap_or(0))
    }

    async fn upsert_balance(
        &self,
        tx: &mut sqlx::Transaction<'_, sqlx::Postgres>,
        asset: &str,
        holder: &str,
        balance: i64,
    ) -> Result<(), SettleError> {
        sqlx::query(&format!(
            "INSERT INTO {} (asset, holder, balance) VALUES ($1, $2, $3)
                 ON CONFLICT (asset, holder) DO UPDATE SET balance = EXCLUDED.balance",
            Self::BALANCE_TABLE
        ))
        .bind(asset)
        .bind(holder)
        .bind(balance)
        .execute(&mut **tx)
        .await
        .map_err(|e| SettleError::Backend(format!("settle: write balance: {e}")))?;
        Ok(())
    }
}

/// The SQL projection of one persisted chain row (for [`VerifiedConservingStore::revalidate`]).
#[cfg(feature = "pg")]
#[derive(sqlx::FromRow)]
struct ChainRowSql {
    ordinal: i64,
    lease_id: String,
    period: i64,
    asset: String,
    payer: String,
    beneficiary: String,
    amount: i64,
    payer_balance: i64,
    beneficiary_balance: i64,
    prev_root: Vec<u8>,
    ledger_root: Vec<u8>,
}

#[cfg(feature = "pg")]
impl ChainRowSql {
    fn into_turn(self) -> anyhow::Result<SettledTurn> {
        let prev_root: [u8; 32] = self
            .prev_root
            .try_into()
            .map_err(|_| anyhow::anyhow!("prev_root not 32 bytes"))?;
        let ledger_root: [u8; 32] = self
            .ledger_root
            .try_into()
            .map_err(|_| anyhow::anyhow!("ledger_root not 32 bytes"))?;
        Ok(SettledTurn {
            ordinal: self.ordinal as u64,
            charge: LeaseCharge::new(
                self.payer,
                self.beneficiary,
                self.asset,
                self.lease_id,
                self.period,
                self.amount,
            ),
            payer_balance: self.payer_balance,
            beneficiary_balance: self.beneficiary_balance,
            prev_root,
            ledger_root,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn charge(lease: &str, period: i64, amount: i64) -> LeaseCharge {
        LeaseCharge::new("lessee", "provider", "USD", lease, period, amount)
    }

    #[test]
    fn settle_moves_value_and_conserves_over_the_chain() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        assert_eq!(vc.total_supply("USD"), 100);
        assert_eq!(vc.head(), GENESIS_ROOT, "no turns yet ⇒ genesis head");

        let r = vc.settle(&charge("lease-1", 1, 7)).expect("settle");
        assert!(!r.replayed);
        assert_eq!(r.payer_balance, 93);
        assert_eq!(r.beneficiary_balance, 7);
        assert_eq!(vc.balance("USD", "provider"), 7);
        assert_eq!(vc.total_supply("USD"), 100, "Σδ = 0 across the transfer");
        // The chain advanced: head is now this turn's ledger_root, ordinal 1 next.
        assert_ne!(vc.head(), GENESIS_ROOT);
        assert_eq!(vc.next_ordinal(), 1);
        assert_eq!(vc.turns().len(), 1);
    }

    #[test]
    fn settle_is_exactly_once_per_period() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        let first = vc.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(!first.replayed);
        let again = vc.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(again.replayed, "re-settling a period replays");
        assert_eq!(vc.balance("USD", "provider"), 5, "value moved only once");
        assert_eq!(vc.settled_total("lease-1"), 5);
        assert_eq!(vc.next_ordinal(), 1, "a replay does not extend the chain");
    }

    #[test]
    fn distinct_periods_chain_and_accumulate() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        vc.settle(&charge("lease-1", 1, 3)).unwrap();
        let h1 = vc.head();
        vc.settle(&charge("lease-1", 2, 4)).unwrap();
        assert_ne!(vc.head(), h1, "second turn advances the head");
        assert_eq!(vc.settled_total("lease-1"), 7);
        assert_eq!(vc.balance("USD", "provider"), 7);
        assert_eq!(vc.next_ordinal(), 2);
        // The turns chain: turn 0's ledger_root is turn 1's prev_root.
        let t = vc.turns();
        assert_eq!(
            t[0].ledger_root, t[1].prev_root,
            "post-state root N == pre-state root N+1"
        );
    }

    #[test]
    fn insufficient_funds_refuses_and_does_not_advance_the_chain() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 2);
        assert!(matches!(
            vc.settle(&charge("lease-1", 1, 5)),
            Err(SettleError::InsufficientFunds { .. })
        ));
        assert_eq!(vc.total_supply("USD"), 2, "nothing moved");
        assert_eq!(
            vc.next_ordinal(),
            0,
            "a refused settle does not extend the chain"
        );
        assert_eq!(vc.turns().len(), 0);
    }

    #[test]
    fn same_key_different_terms_is_a_conflict() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        vc.settle(&charge("lease-1", 1, 5)).unwrap();
        assert!(matches!(
            vc.settle(&charge("lease-1", 1, 9)),
            Err(SettleError::Conflict { .. })
        ));
    }

    #[test]
    fn revalidate_accepts_a_genuine_chain() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        vc.settle(&charge("lease-1", 1, 3)).unwrap();
        vc.settle(&charge("lease-1", 2, 4)).unwrap();
        vc.settle(&charge("lease-2", 1, 5)).unwrap();
        let turns = vc.turns().to_vec();

        let reloaded = VerifiedChain::revalidate(turns).expect("a genuine chain re-validates");
        assert_eq!(reloaded.next_ordinal(), 3);
        assert_eq!(
            reloaded.head(),
            vc.head(),
            "re-validation reaches the same head"
        );
        // The settlement deltas reconstruct: provider gained 12, lessee lost 12.
        assert_eq!(reloaded.balance("USD", "provider"), 12);
        assert_eq!(reloaded.balance("USD", "lessee"), -12);
        assert_eq!(reloaded.settled_total("lease-1"), 7);
    }

    #[test]
    fn revalidate_refuses_a_tampered_post_image() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        vc.settle(&charge("lease-1", 1, 3)).unwrap();
        vc.settle(&charge("lease-1", 2, 4)).unwrap();
        let mut turns = vc.turns().to_vec();
        // Tamper: inflate the beneficiary's balance on the first turn (steal value).
        turns[0].beneficiary_balance += 1_000;
        let err = VerifiedChain::revalidate(turns).expect_err("a tampered post-image is refused");
        assert!(
            matches!(err, ChainRefusal::Malformed(_)),
            "tamper caught by self-binding"
        );
    }

    #[test]
    fn revalidate_refuses_a_reordered_chain() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        vc.settle(&charge("lease-1", 1, 3)).unwrap();
        vc.settle(&charge("lease-1", 2, 4)).unwrap();
        vc.settle(&charge("lease-1", 3, 5)).unwrap();
        let mut turns = vc.turns().to_vec();
        turns.swap(1, 2); // reorder turns 1 and 2
        let err = VerifiedChain::revalidate(turns).expect_err("a reordered chain is refused");
        // Reorder breaks the dense ordinal / root chain.
        assert!(matches!(
            err,
            ChainRefusal::OrdinalGap { .. } | ChainRefusal::RootMismatch { .. }
        ));
    }

    #[test]
    fn revalidate_refuses_a_truncated_chain() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        vc.settle(&charge("lease-1", 1, 3)).unwrap();
        vc.settle(&charge("lease-1", 2, 4)).unwrap();
        let mut turns = vc.turns().to_vec();
        turns.pop(); // drop the tail
        // The expect_count guard catches a truncation the per-link chaining alone would not.
        let err = VerifiedChain::revalidate_expecting(turns, 2)
            .expect_err("a truncated chain is refused");
        assert!(matches!(err, ChainRefusal::Malformed(_)));
    }

    // ---- #5 / S9-2: the truncation guard needs an INDEPENDENT count ----

    /// The PoC: a `DELETE` of the chain tail leaves a dense, genesis-anchored prefix
    /// that re-validates clean IF the expected count is derived from the (truncated)
    /// read itself. The fix feeds the independent per-lease head ordinal as the
    /// expected count, so the short read is refused.
    #[test]
    fn truncation_is_undetected_by_a_self_derived_count_but_caught_by_the_independent_one() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        vc.settle(&charge("lease-1", 1, 3)).unwrap();
        vc.settle(&charge("lease-1", 2, 4)).unwrap();
        vc.settle(&charge("lease-1", 3, 5)).unwrap();
        let full = vc.turns().to_vec();
        // The head authority's count BEFORE the tamper (the independent authority).
        let independent_count = full.len() as u64; // == 3, persisted in HEAD_TABLE

        // The attacker DELETEs the tail row → the read returns a dense prefix [0,1].
        let mut truncated = full.clone();
        truncated.pop();

        // THE BUG: deriving the expected count from the truncated read (`rows.len()`)
        // makes the guard `2 != 2` — always false — so the truncation re-validates clean.
        VerifiedChain::revalidate_expecting(truncated.clone(), truncated.len() as u64)
            .expect("the self-derived count fails to catch the tail deletion (the bug)");

        // THE FIX: feeding the INDEPENDENT head count (3) refuses the short read.
        let err = VerifiedChain::revalidate_expecting(truncated, independent_count)
            .expect_err("the independent expected-count catches the truncation");
        assert!(matches!(err, ChainRefusal::Malformed(_)));
    }

    // ---- #4 / S9-1: the balance table must reconcile against the chain + funding ----

    /// A genuine store reconciles: the materialized balance == `funded + Σ deltas`.
    #[test]
    fn reconcile_accepts_genuine_balances() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        vc.settle(&charge("lease-1", 1, 3)).unwrap();
        vc.settle(&charge("lease-1", 2, 4)).unwrap();
        let turns = vc.turns().to_vec();

        // The honest funding authority + the honest materialized balances.
        let funded: HashMap<(String, String), i64> = [(("USD".into(), "lessee".into()), 100)]
            .into_iter()
            .collect();
        // lessee: 100 - 7 = 93; provider: +7.
        let stored: HashMap<(String, String), i64> = [
            (("USD".into(), "lessee".into()), 93),
            (("USD".into(), "provider".into()), 7),
        ]
        .into_iter()
        .collect();

        let reconciled = VerifiedChain::reconcile_balances(&turns, &funded, &stored)
            .expect("a genuine balance table reconciles");
        assert_eq!(reconciled.get(&("USD".into(), "lessee".into())), Some(&93));
        assert_eq!(reconciled.get(&("USD".into(), "provider".into())), Some(&7));
    }

    /// The PoC: a DB-write attacker `UPDATE`s their balance to spend value they were
    /// never funded for. The chain + funding do not imply the inflated number, so the
    /// cross-check refuses the load rather than trusting it to gate a spend.
    #[test]
    fn reconcile_refuses_a_tampered_balance_table() {
        let mut vc = VerifiedChain::new();
        vc.fund("USD", "lessee", 100);
        vc.settle(&charge("lease-1", 1, 3)).unwrap();
        let turns = vc.turns().to_vec();

        let funded: HashMap<(String, String), i64> = [(("USD".into(), "lessee".into()), 100)]
            .into_iter()
            .collect();
        // The attacker grants themselves a huge spendable balance the funding +
        // chain never produced (the `UPDATE dreggnet_settle_balances` attack).
        let tampered: HashMap<(String, String), i64> = [
            (("USD".into(), "attacker".into()), 1_000_000),
            (("USD".into(), "lessee".into()), 97),
            (("USD".into(), "provider".into()), 3),
        ]
        .into_iter()
        .collect();

        let err = VerifiedChain::reconcile_balances(&turns, &funded, &tampered)
            .expect_err("an unfunded balance is refused");
        assert!(matches!(err, ChainRefusal::Malformed(_)));
    }
}

impl VerifiedChain {
    /// [`revalidate`](Self::revalidate) with an explicit expected turn count — the
    /// truncation guard (`revalidate_replicated_chain`'s `expect_count`): a subscriber that
    /// knows how many turns it should have received refuses a short stream even if the
    /// prefix chains. Used by the pg layer, which knows the row count it read.
    pub fn revalidate_expecting(
        turns: Vec<SettledTurn>,
        expect: u64,
    ) -> Result<VerifiedChain, ChainRefusal> {
        if turns.len() as u64 != expect {
            return Err(ChainRefusal::Malformed(format!(
                "expected {expect} settled turns, got {} (truncated or over-long)",
                turns.len()
            )));
        }
        VerifiedChain::revalidate(turns)
    }
}
