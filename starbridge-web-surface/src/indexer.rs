//! **The reactive-read INDEXER — the missing middle** (docs/GAME-STRATEGY.md
//! Phase 1: "a MINIMAL reactive-read/INDEXER (WELD receipt_stream.rs [verified
//! live stream] + dregg-query [EDB+CALM+MMR non-omission] into a materialized
//! per-cell view)"; docs/GAME-STRATEGY.md build-vs-adopt: "the reactive indexer
//! <- Torii; indexer rows carry NON-OMISSION certificates ... no Torii offers
//! this").
//!
//! ## What this is (the Torii/MUD shape, welded from two halves that EXIST)
//!
//! A game client cannot render off a raw receipt stream — it needs the CURRENT
//! state of each cell/field, and to be told WHEN that state changes. That
//! materialized, per-cell, reactive-read view is the "missing middle" between
//! the node and the client. This module builds it by WELDING, not reinventing:
//!
//!  * the VERIFIED INGEST half is [`crate::receipt_stream::ReceiptStream`] — the
//!    live `/api/events/stream` subscription that admits a receipt IFF it is
//!    in-order (dense `chain_index`) AND un-forged (its body re-hashes to the
//!    canonical [`dregg_turn::TurnReceipt::receipt_hash`]). A forged or omitted
//!    frame is REJECTED there; the indexer only ever folds what that gate
//!    admitted, so the view is a fold of the ATTESTED stream;
//!  * the ATTESTED QUERY half is [`dregg_query`] — the EDB fact schema
//!    (`created`/`transfer`/`balance`/`field`/`lifecycle`/…), the conjunctive
//!    query evaluator, the CALM monotone/finalized-dependent classifier, and the
//!    MMR non-omission certificate (`server_cannot_omit_position`).
//!
//! The indexer folds the first into the second and adds the two things a game
//! client needs on top:
//!
//! 1. **A materialized current-state view** ([`MaterializedView`]) — per-cell
//!    rows keyed for query: field slots -> current committed value, asset ->
//!    current balance, lifecycle state. A field read returns the CURRENT
//!    committed value (dense-order fold, latest wins).
//! 2. **Reactive subscriptions** ([`Indexer::subscribe`]) — a client registers a
//!    [`dregg_query::Query`]; every committed receipt whose effects touch a
//!    predicate the query reads re-evaluates it, and a CHANGE in the answer set
//!    (rows added, or — for a finalized-dependent query — retracted) fires a
//!    [`SubscriptionEvent`] into that subscription's queue. This is the
//!    reactive-read path the client renders off, without polling the whole view.
//! 3. **Local tx simulation** ([`Indexer::simulate`]) — given a proposed turn's
//!    effects, predict its effect on the view for the NEXT dense position
//!    WITHOUT a remote round-trip (optimistic render). When the real receipt for
//!    that turn commits at that position, the committed view MATCHES the
//!    prediction.
//! 4. **The non-omission certificate** ([`Indexer::attested_answer`]) — any query
//!    can be answered with a [`dregg_query::AttestedAnswer`] carrying the
//!    whole-log MMR range opening, so a client can PROVE the indexer hid no
//!    state change (a dropped receipt breaks the dense count; a forged one breaks
//!    the root or the row re-derivation).
//!
//! ## What is real vs. the named seam
//!
//! REAL (driven by the tests below): the fold into the EDB + the materialized
//! per-cell view; the reactive subscription firing on a matching state change;
//! the local-simulation-then-confirm loop; the whole-log non-omission
//! certificate; and the forge/omission REJECTION riding [`ReceiptStream`]'s
//! gate.
//!
//! THE SEAM (named, not faked):
//!  * **the WIRE TRANSPORT** — serving the view / subscriptions / certificate
//!    over GraphQL/gRPC/SSE, and a client library. This module is the pure,
//!    runtime-free CORE (exactly [`ReceiptStream`]'s + [`dregg_query`]'s
//!    discipline): a client feeds it [`ReceiptEnvelope`]s and reads the view /
//!    drains subscriptions / requests certificates synchronously. The byte-pull
//!    and the push channel are the transport lane's, above this boundary.
//!  * **the typed-effect ENRICHMENT** — the per-effect [`EffectSummary`] the fold
//!    materializes (transfer endpoints/amounts, field writes, balances) is
//!    DISCLOSED by the node alongside the receipt (bound into the receipt's
//!    `effects_hash`, but not independently re-derivable from `receipt_hash`
//!    alone). This is the SAME trust boundary [`dregg_query::client`] documents
//!    for `/api/receipts/index/range` (the `push_committed_event_enriched`
//!    enrichment): the receipt's ORDER + INTEGRITY is verified here; the typed
//!    effect DISCLOSURE is node-attested. The non-omission certificate proves the
//!    receipt SET is complete; the enrichment faithfulness is that named node
//!    disclosure.
//!
//! ## How a game client consumes it
//!
//! On connect: request an [`Indexer::attested_answer`] for the queries it renders
//! (verify once against the trusted root — proof the initial state omitted
//! nothing), read the [`MaterializedView`] for current cell/field values, and
//! [`Indexer::subscribe`] to the queries it wants live. Per turn it wants to
//! play: [`Indexer::simulate`] to render optimistically, submit the turn, and on
//! the committed receipt the subscription fires with the confirmed delta (which
//! equals the prediction). The trusted root itself is pinned via the existing
//! [`dregg_query::client::SignedIndexHead`] / `CommitBindsMMR` anchor — the
//! caller-side trust seam this crate already names.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use dregg_query::receipt::extract_receipt_facts;
use dregg_query::{
    answer_whole_log, eval, AttestedAnswer, AttestedSlice, Bindings, Blake3Mmr, EffectSummary,
    FactBase, Mmr, Pred, Query, QueryError, RangeCertificate, ReceiptRecord,
};

use crate::receipt_stream::{Admitted, Cursor, IngestError, ReceiptEnvelope, ReceiptStream};

// ───────────────────────────────────────────────────────────────────────────────
// The materialized per-cell current-state view.
// ───────────────────────────────────────────────────────────────────────────────

/// The current committed state of one cell — the per-cell row a client renders.
/// Folded from the effect stream in dense `chain_index` order, so each slot holds
/// the value the LATEST receipt that wrote it committed ("current committed
/// value").
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CellView {
    /// State-field slots: index -> current value (hex of the 32-byte field
    /// element), from `Effect::SetField` (`field` facts). The star of a game
    /// view — HP / position / flags live here.
    pub fields: BTreeMap<u64, String>,
    /// Current balance per asset, from `balance` observations (the stamped
    /// post-state observation the EDB records; NOT re-derived from transfer
    /// deltas — the FACT/FICTION line of `dregg_query::fact`).
    pub balances: BTreeMap<String, u64>,
    /// Current lifecycle state (`sealed`/`unsealed`/`destroyed`/`sovereign`),
    /// from lifecycle transitions; latest wins.
    pub lifecycle: Option<String>,
    /// The agent that created this cell, if a `created` effect was observed.
    pub created_by: Option<String>,
    /// The dense `chain_index` of the last receipt that touched this cell.
    pub last_touched: u64,
}

/// The materialized view: cell id -> its current [`CellView`]. This is the
/// queryable, reactive-read surface a client renders off.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MaterializedView {
    cells: BTreeMap<String, CellView>,
}

impl MaterializedView {
    /// Fold one receipt's effects into the view at dense position `chain_index`
    /// (latest-wins overwrite — dense order makes this the current committed
    /// value). Only the view-materialized effect families move a cell row;
    /// edge-shaped effects (transfer/grant/revoke/burn) are query FACTS, not
    /// per-cell state, so they do not overwrite a cell's materialized value.
    fn apply(&mut self, effects: &[EffectSummary], chain_index: u64) {
        for e in effects {
            match e {
                EffectSummary::Created { agent, cell } => {
                    let cv = self.cells.entry(cell.clone()).or_default();
                    cv.created_by = Some(agent.clone());
                    cv.last_touched = chain_index;
                }
                EffectSummary::Balance {
                    cell,
                    asset,
                    amount,
                } => {
                    let cv = self.cells.entry(cell.clone()).or_default();
                    cv.balances.insert(asset.clone(), *amount);
                    cv.last_touched = chain_index;
                }
                EffectSummary::Field { cell, index, value } => {
                    let cv = self.cells.entry(cell.clone()).or_default();
                    cv.fields.insert(*index, value.clone());
                    cv.last_touched = chain_index;
                }
                EffectSummary::Lifecycle { cell, state } => {
                    let cv = self.cells.entry(cell.clone()).or_default();
                    cv.lifecycle = Some(state.clone());
                    cv.last_touched = chain_index;
                }
                // Edge/flow effects: recorded as facts (queryable), not
                // per-cell materialized state.
                EffectSummary::Transfer { .. }
                | EffectSummary::Granted { .. }
                | EffectSummary::Revoked { .. }
                | EffectSummary::Burned { .. }
                | EffectSummary::Other { .. } => {}
            }
        }
    }

    /// The current [`CellView`] of `cell`, if the indexer has seen it.
    pub fn cell(&self, cell: &str) -> Option<&CellView> {
        self.cells.get(cell)
    }

    /// The current committed value of field slot `index` of `cell` (hex of the
    /// 32-byte field element) — the reactive-read a client renders. `None` if
    /// the cell or slot has never been written.
    pub fn field(&self, cell: &str, index: u64) -> Option<&str> {
        self.cells.get(cell)?.fields.get(&index).map(String::as_str)
    }

    /// The current committed balance of `asset` held by `cell`.
    pub fn balance(&self, cell: &str, asset: &str) -> Option<u64> {
        self.cells.get(cell)?.balances.get(asset).copied()
    }

    /// The current lifecycle state of `cell`.
    pub fn lifecycle(&self, cell: &str) -> Option<&str> {
        self.cells.get(cell)?.lifecycle.as_deref()
    }

    /// How many cells the view materializes.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether the view is empty.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }
}

/// The view-materialized cells an effect set touches (the cells whose
/// [`CellView`] would move) — the "touched" set a simulation predicts and a
/// reactive delta reports. Edge effects (transfer/grant/revoke/burn) touch no
/// materialized cell row.
fn touched_cells(effects: &[EffectSummary]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    let mut push = |c: &String, seen: &mut BTreeSet<String>, out: &mut Vec<String>| {
        if seen.insert(c.clone()) {
            out.push(c.clone());
        }
    };
    for e in effects {
        match e {
            EffectSummary::Created { cell, .. }
            | EffectSummary::Balance { cell, .. }
            | EffectSummary::Field { cell, .. }
            | EffectSummary::Lifecycle { cell, .. } => push(cell, &mut seen, &mut out),
            _ => {}
        }
    }
    out
}

/// The EDB predicate an effect contributes a fact to (for the reactive
/// touched-predicate gate). `Other` contributes none.
fn effect_pred(e: &EffectSummary) -> Option<Pred> {
    Some(match e {
        EffectSummary::Created { .. } => Pred::Created,
        EffectSummary::Transfer { .. } => Pred::Transfer,
        EffectSummary::Balance { .. } => Pred::Balance,
        EffectSummary::Granted { .. } => Pred::Granted,
        EffectSummary::Revoked { .. } => Pred::Revoked,
        EffectSummary::Burned { .. } => Pred::Burned,
        EffectSummary::Field { .. } => Pred::Field,
        EffectSummary::Lifecycle { .. } => Pred::Lifecycle,
        EffectSummary::Other { .. } => return None,
    })
}

// ───────────────────────────────────────────────────────────────────────────────
// Reactive subscriptions.
// ───────────────────────────────────────────────────────────────────────────────

/// A subscription handle — an opaque id a client holds to drain its events.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SubId(pub u64);

/// A reactive notification: the answer set of a subscribed query CHANGED at
/// `chain_index`. Carries the delta (rows `added`, rows `retracted`) and the
/// full current `rows` — a client can either apply the delta or re-render off
/// the full answer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubscriptionEvent {
    /// The dense position of the receipt whose fold produced this change.
    pub chain_index: u64,
    /// Rows now present that were not before (monotone growth, or a group whose
    /// aggregate moved).
    pub added: Vec<Bindings>,
    /// Rows now absent that were present before — only possible for a
    /// finalized-dependent (negated / aggregated) query (e.g. a revocation
    /// retracting a "granted and not revoked" row).
    pub retracted: Vec<Bindings>,
    /// The full current answer set after the change.
    pub rows: Vec<Bindings>,
}

/// One registered subscription: the query, the predicates it reads (the
/// touched-predicate gate), its last-seen answer set, and its pending event
/// queue.
struct Subscription {
    id: SubId,
    query: Query,
    preds: BTreeSet<Pred>,
    last_rows: BTreeSet<Bindings>,
    pending: VecDeque<SubscriptionEvent>,
}

// ───────────────────────────────────────────────────────────────────────────────
// Local tx simulation.
// ───────────────────────────────────────────────────────────────────────────────

/// The predicted effect of a proposed turn on the view — the optimistic render
/// a client draws before the turn commits. [`SimulatedTurn::predicted`] holds
/// the post-turn [`CellView`] of each touched cell, computed for the NEXT dense
/// position; when the real receipt commits at that position with these effects,
/// the committed view equals this prediction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SimulatedTurn {
    /// The dense `chain_index` this turn would commit at (the current head).
    pub at_index: u64,
    /// Touched cell -> its predicted post-turn [`CellView`].
    pub predicted: BTreeMap<String, CellView>,
    /// The touched cells, in first-touch order.
    pub touched: Vec<String>,
}

// ───────────────────────────────────────────────────────────────────────────────
// The indexer.
// ───────────────────────────────────────────────────────────────────────────────

/// **The reactive-read indexer.** Feed it the verified live receipt stream via
/// [`Indexer::ingest`]; it folds each committed receipt into a materialized
/// per-cell view + the query EDB + the receipt-index MMR, fires reactive
/// subscriptions, and can answer any query with a whole-log non-omission
/// certificate. The verification core is pure (no runtime) — the transport is
/// the named seam above it.
pub struct Indexer {
    /// The verified ingest half — every frame passes its in-order + un-forged
    /// gate before the indexer folds it.
    stream: ReceiptStream,
    /// The materialized per-cell current-state view.
    view: MaterializedView,
    /// The query EDB — folded incrementally, kept identical to
    /// `extract_facts(&self.records)` by construction (asserted in tests).
    facts: FactBase,
    /// The receipt-index MMR over the committed receipt hashes, dense by
    /// `chain_index` — the non-omission commitment.
    mmr: Mmr<Blake3Mmr>,
    /// The committed receipt records (with enrichment), dense by `chain_index` —
    /// the certified EDB a whole-log answer opens.
    records: Vec<ReceiptRecord>,
    /// Registered reactive subscriptions.
    subs: BTreeMap<SubId, Subscription>,
    /// Next subscription id.
    next_sub: u64,
}

/// The outcome of an [`Indexer::ingest`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IngestOutcome {
    /// A new committed receipt was folded at `chain_index`; `fired` names the
    /// subscriptions whose answer changed (a reactive notification is now
    /// queued for each).
    Committed { chain_index: u64, fired: Vec<SubId> },
    /// A benign at-least-once re-delivery of an already-folded receipt — the
    /// stream verified it again and deduplicated; the view/EDB are unchanged.
    Duplicate,
}

impl Indexer {
    /// A fresh indexer tailing the stream from genesis (first expected receipt is
    /// `chain_index == 0`), retaining the last `stream_cap` verified receipts in
    /// the underlying stream's tail.
    pub fn new(stream_cap: usize) -> Self {
        Indexer {
            stream: ReceiptStream::new(stream_cap),
            view: MaterializedView::default(),
            facts: FactBase::new(),
            mmr: Mmr::new(Blake3Mmr),
            records: Vec::new(),
            subs: BTreeMap::new(),
            next_sub: 0,
        }
    }

    /// **Fold one live receipt frame into the view.** The `env` is the verified
    /// SSE envelope (the receipt + its claimed hash); `effects` is the node's
    /// typed per-effect enrichment (the named disclosure seam). The frame first
    /// passes [`ReceiptStream::ingest`]'s gate — a forged or out-of-order frame
    /// is REJECTED ([`IngestError`]) and NOTHING is folded — then, on a new
    /// admit, the indexer folds it into the view, the EDB, the MMR, and the
    /// certified record log, and fires any subscription whose answer changed.
    pub fn ingest(
        &mut self,
        env: ReceiptEnvelope,
        effects: Vec<EffectSummary>,
    ) -> Result<IngestOutcome, IngestError> {
        match self.stream.ingest(env)? {
            Admitted::Duplicate => Ok(IngestOutcome::Duplicate),
            Admitted::New => {
                // The stream just admitted (verified in-order + un-forged) this
                // receipt; pull the VERIFIED fields it exposes (the recomputed
                // canonical `receipt_hash`, the dense `chain_index`, height, the
                // agent cell).
                let (chain_index, receipt_hash, height, agent) = {
                    let sr = self
                        .stream
                        .latest()
                        .expect("Admitted::New => a latest receipt exists");
                    (
                        sr.chain_index,
                        sr.receipt_hash,
                        sr.height,
                        sr.cells.first().cloned().unwrap_or_default(),
                    )
                };
                let record = ReceiptRecord {
                    chain_index,
                    receipt_hash: hex32(&receipt_hash),
                    height,
                    agent,
                    effects,
                };
                let touched: BTreeSet<Pred> =
                    record.effects.iter().filter_map(effect_pred).collect();
                // Fold: materialized view + EDB + MMR (leaf = the verified hash) +
                // certified record log.
                self.view.apply(&record.effects, chain_index);
                extract_receipt_facts(&record, &mut self.facts);
                self.mmr.push(receipt_hash);
                self.records.push(record);
                // Reactive: re-evaluate every subscription the fold could have
                // moved; fire on a changed answer set.
                let fired = self.fire(chain_index, &touched);
                Ok(IngestOutcome::Committed { chain_index, fired })
            }
        }
    }

    /// Re-evaluate every subscription whose read-predicates intersect the
    /// just-folded receipt's `touched` predicates; push a [`SubscriptionEvent`]
    /// for each whose answer set changed. Returns the subscriptions that fired.
    fn fire(&mut self, chain_index: u64, touched: &BTreeSet<Pred>) -> Vec<SubId> {
        // Disjoint field borrows: read `self.facts`, mutate `self.subs`.
        let facts = &self.facts;
        let mut fired = Vec::new();
        for sub in self.subs.values_mut() {
            if sub.preds.is_disjoint(touched) {
                continue; // the fold cannot have changed this query's answer
            }
            let rows = match eval(facts, &sub.query) {
                Ok(r) => r,
                Err(_) => continue,
            };
            let rowset: BTreeSet<Bindings> = rows.iter().cloned().collect();
            if rowset == sub.last_rows {
                continue; // touched the predicate but the answer is unchanged
            }
            let added: Vec<Bindings> = rowset.difference(&sub.last_rows).cloned().collect();
            let retracted: Vec<Bindings> = sub.last_rows.difference(&rowset).cloned().collect();
            sub.pending.push_back(SubscriptionEvent {
                chain_index,
                added,
                retracted,
                rows,
            });
            sub.last_rows = rowset;
            fired.push(sub.id);
        }
        fired
    }

    // ── Reactive subscriptions ──────────────────────────────────────────────

    /// Register a reactive subscription for `query`. The query is validated
    /// (arity + safety) up front; the subscription starts from the CURRENT
    /// answer set (so its first event fires on the next matching change). A
    /// client renders the initial state off [`Indexer::query`] /
    /// [`Indexer::view`], then drains this subscription for live deltas.
    pub fn subscribe(&mut self, query: Query) -> Result<SubId, QueryError> {
        // Validate + seed the current answer (also surfaces a bad query early).
        let rows = eval(&self.facts, &query)?;
        let last_rows: BTreeSet<Bindings> = rows.into_iter().collect();
        let mut preds: BTreeSet<Pred> = query.atoms.iter().map(|a| a.pred).collect();
        preds.extend(query.negated.iter().map(|a| a.pred));
        let id = SubId(self.next_sub);
        self.next_sub += 1;
        self.subs.insert(
            id,
            Subscription {
                id,
                query,
                preds,
                last_rows,
                pending: VecDeque::new(),
            },
        );
        Ok(id)
    }

    /// Drain all queued [`SubscriptionEvent`]s for `id` (oldest first). Empty if
    /// the subscription has not fired since the last drain. `None` if `id` is
    /// unknown.
    pub fn drain_subscription(&mut self, id: SubId) -> Option<Vec<SubscriptionEvent>> {
        let sub = self.subs.get_mut(&id)?;
        Some(sub.pending.drain(..).collect())
    }

    /// Pull the next queued [`SubscriptionEvent`] for `id`, oldest first (`None`
    /// if the queue is empty or `id` is unknown).
    pub fn poll_subscription(&mut self, id: SubId) -> Option<SubscriptionEvent> {
        self.subs.get_mut(&id)?.pending.pop_front()
    }

    /// Cancel a subscription. Returns whether it existed.
    pub fn unsubscribe(&mut self, id: SubId) -> bool {
        self.subs.remove(&id).is_some()
    }

    // ── Local tx simulation ─────────────────────────────────────────────────

    /// **Predict a proposed turn's effect on the view** WITHOUT committing it —
    /// the optimistic render. Applies `effects` to a COPY of the touched cells'
    /// current [`CellView`]s at the next dense position and returns the predicted
    /// post-turn views. Nothing in the indexer changes. When the real receipt for
    /// this turn commits at [`SimulatedTurn::at_index`] with these effects, the
    /// committed view equals [`SimulatedTurn::predicted`].
    pub fn simulate(&self, effects: &[EffectSummary]) -> SimulatedTurn {
        let at_index = self.mmr.len();
        let touched = touched_cells(effects);
        // Seed a scratch view with clones of just the touched cells' current
        // state, then apply the proposed effects.
        let mut scratch = MaterializedView::default();
        for c in &touched {
            if let Some(cv) = self.view.cell(c) {
                scratch.cells.insert(c.clone(), cv.clone());
            }
        }
        scratch.apply(effects, at_index);
        let predicted = touched
            .iter()
            .filter_map(|c| scratch.cells.get(c).map(|v| (c.clone(), v.clone())))
            .collect();
        SimulatedTurn {
            at_index,
            predicted,
            touched,
        }
    }

    // ── Reads ────────────────────────────────────────────────────────────────

    /// The materialized current-state view — per-cell current field/balance/
    /// lifecycle values a client renders.
    pub fn view(&self) -> &MaterializedView {
        &self.view
    }

    /// Answer `query` directly over the current EDB (no certificate) — the fast
    /// reactive read. For a PROOF the answer omitted nothing, use
    /// [`Indexer::attested_answer`].
    pub fn query(&self, query: &Query) -> Result<Vec<Bindings>, QueryError> {
        eval(&self.facts, query)
    }

    // ── The non-omission certificate ─────────────────────────────────────────

    /// The receipt-index MMR root over every folded receipt — the value a client
    /// pins (via the existing `dregg_query::client::SignedIndexHead` /
    /// `CommitBindsMMR` anchor) and passes as the trusted root to
    /// [`AttestedAnswer::verify`].
    pub fn index_root(&self) -> [u8; 32] {
        self.mmr.root()
    }

    /// The number of committed receipts the indexer has folded (the dense log
    /// length).
    pub fn committed_len(&self) -> u64 {
        self.mmr.len()
    }

    /// The certified WHOLE-LOG slice: every folded receipt + the MMR range
    /// opening over `[0, len-1]`. The input to a whole-log [`AttestedAnswer`].
    pub fn attested_slice(&self) -> AttestedSlice {
        let len = self.mmr.len();
        let hi = len.saturating_sub(1);
        let (_values, opening) = self.mmr.open_range(0, hi);
        AttestedSlice {
            receipts: self.records.clone(),
            cert: RangeCertificate {
                root: self.mmr.root(),
                lo: 0,
                hi,
                opening,
            },
        }
    }

    /// **Answer `query` with a whole-log non-omission certificate.** The returned
    /// [`AttestedAnswer`] carries the query, the rows, the CALM grade, and the
    /// MMR opening over the whole committed log; a client calls
    /// [`AttestedAnswer::verify`] against [`Indexer::index_root`] to prove the
    /// answer was computed from EXACTLY the committed receipt set — the indexer
    /// hid no state change (a dropped receipt breaks the dense count; a forged
    /// one breaks the root or the row re-derivation).
    pub fn attested_answer(&self, query: Query) -> Result<AttestedAnswer, QueryError> {
        answer_whole_log(self.attested_slice(), query)
    }

    // ── Stream plumbing passthrough ──────────────────────────────────────────

    /// The resume [`Cursor`] — the `Last-Event-ID` a reconnecting client replays
    /// so the fold resumes losslessly from where it left off.
    pub fn resume_cursor(&self) -> Cursor {
        self.stream.resume_cursor()
    }
}

/// Lowercase-hex-encode a 32-byte hash — the node's `receipt_hash` wire
/// convention (matching `dregg_query::ReceiptRecord::receipt_hash_bytes`'s
/// `hex::decode`). Kept local so this module adds no `hex` dep of its own,
/// exactly the minimalism [`crate::receipt_stream`] keeps.
fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push(char::from_digit((b >> 4) as u32, 16).unwrap());
        s.push(char::from_digit((b & 0x0f) as u32, 16).unwrap());
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_query::{CmpOp, Term};
    use dregg_turn::TurnReceipt;

    // ── Fixtures: a real, distinctly-hashed TurnReceipt + honest/enriched
    //    frames, mirroring `receipt_stream`'s test fixtures. ──

    fn receipt(seed: u8) -> TurnReceipt {
        let mut agent = [0u8; 32];
        agent[0] = 0xA0;
        agent[1] = seed;
        TurnReceipt {
            turn_hash: [seed; 32],
            forest_hash: [seed.wrapping_add(1); 32],
            pre_state_hash: [seed.wrapping_add(2); 32],
            post_state_hash: [seed.wrapping_add(3); 32],
            effects_hash: [seed.wrapping_add(4); 32],
            timestamp: 1_718_000_000 + seed as i64,
            computrons_used: 100 + seed as u64,
            action_count: 1 + seed as usize,
            agent: dregg_types::CellId::derive_raw(&agent, &[0u8; 32]),
            ..Default::default()
        }
    }

    /// An honest envelope at dense `idx` carrying `receipt(seed)`, whose agent
    /// cell (`cells[0]`) is `agent_hex`.
    fn env(idx: u64, seed: u8) -> (ReceiptEnvelope, String) {
        let r = receipt(seed);
        let agent_hex = hex32(r.agent.as_bytes());
        let e = ReceiptEnvelope::honest(idx, 1880 + idx, r);
        (e, agent_hex)
    }

    /// A convenient honest ingest of `effects` at `idx`/`seed`.
    fn feed(
        ix: &mut Indexer,
        idx: u64,
        seed: u8,
        effects: Vec<EffectSummary>,
    ) -> Result<IngestOutcome, IngestError> {
        let (e, _agent) = env(idx, seed);
        ix.ingest(e, effects)
    }

    fn field(cell: &str, index: u64, value: &str) -> EffectSummary {
        EffectSummary::Field {
            cell: cell.into(),
            index,
            value: value.into(),
        }
    }
    fn balance(cell: &str, asset: &str, amount: u64) -> EffectSummary {
        EffectSummary::Balance {
            cell: cell.into(),
            asset: asset.into(),
            amount,
        }
    }

    // ── (1) The fold: a stream of receipts folds into a correct materialized
    //    per-cell view; a field read returns the CURRENT committed value. ──

    #[test]
    fn the_fold_materializes_a_correct_per_cell_view() {
        let mut ix = Indexer::new(64);
        // Hero cell's HP (slot 0) is written across three turns; latest wins.
        feed(&mut ix, 0, 0, vec![field("hero", 0, "0a")]).unwrap();
        feed(
            &mut ix,
            1,
            1,
            vec![field("hero", 0, "08"), field("hero", 1, "ff")],
        )
        .unwrap();
        feed(
            &mut ix,
            2,
            2,
            vec![field("hero", 0, "05"), balance("hero", "gold", 42)],
        )
        .unwrap();

        // A field read returns the CURRENT committed value (the latest write).
        assert_eq!(
            ix.view().field("hero", 0),
            Some("05"),
            "HP is the latest write"
        );
        assert_eq!(
            ix.view().field("hero", 1),
            Some("ff"),
            "slot 1 retains its write"
        );
        assert_eq!(ix.view().balance("hero", "gold"), Some(42));
        assert_eq!(ix.view().cell("hero").unwrap().last_touched, 2);
        assert_eq!(ix.committed_len(), 3);

        // The EDB the view is folded from equals a from-scratch extraction over
        // the certified records (drift guard: the incremental fold == the batch).
        let batch = dregg_query::extract_facts(&ix.records);
        let q = Query::new().atom(
            Pred::Field,
            vec![
                Term::sym("hero"),
                Term::var("I"),
                Term::var("V"),
                Term::var("H"),
            ],
        );
        assert_eq!(
            eval(&batch, &q).unwrap(),
            ix.query(&q).unwrap(),
            "incremental EDB == batch extraction"
        );
    }

    // ── (2) A reactive subscription FIRES on a matching state change. ──

    #[test]
    fn a_reactive_subscription_fires_on_a_matching_change() {
        let mut ix = Indexer::new(64);
        feed(&mut ix, 0, 0, vec![field("hero", 0, "0a")]).unwrap();

        // Subscribe: "every field write to the hero cell". Seeded from the
        // current answer (one row) — the first fire is the NEXT change.
        let sub = ix
            .subscribe(Query::new().atom(
                Pred::Field,
                vec![
                    Term::sym("hero"),
                    Term::var("I"),
                    Term::var("V"),
                    Term::var("H"),
                ],
            ))
            .unwrap();
        assert!(
            ix.drain_subscription(sub).unwrap().is_empty(),
            "no event before a change"
        );

        // A receipt that DOESN'T touch a field (a transfer) must NOT fire the sub.
        feed(
            &mut ix,
            1,
            1,
            vec![EffectSummary::Transfer {
                from: "hero".into(),
                to: "shop".into(),
                asset: "gold".into(),
                amount: 3,
            }],
        )
        .unwrap();
        assert!(
            ix.drain_subscription(sub).unwrap().is_empty(),
            "transfer does not touch `field`"
        );

        // A field write to hero: the sub FIRES with the new row.
        let out = feed(&mut ix, 2, 2, vec![field("hero", 2, "77")]).unwrap();
        match out {
            IngestOutcome::Committed { chain_index, fired } => {
                assert_eq!(chain_index, 2);
                assert_eq!(fired, vec![sub], "the field-write fired exactly this sub");
            }
            other => panic!("expected Committed, got {other:?}"),
        }
        let events = ix.drain_subscription(sub).unwrap();
        assert_eq!(events.len(), 1, "one queued notification");
        let ev = &events[0];
        assert_eq!(ev.chain_index, 2);
        assert_eq!(ev.added.len(), 1, "the new (hero, 2, 77, h) row was added");
        assert!(ev.retracted.is_empty(), "monotone query never retracts");
        assert_eq!(
            ev.rows.len(),
            2,
            "two field rows now: slot 0 @idx0, slot 2 @idx2"
        );
    }

    // ── (2b) A finalized-dependent sub RETRACTS on a revocation. ──

    #[test]
    fn a_finalized_dependent_subscription_retracts_on_revocation() {
        let mut ix = Indexer::new(64);
        feed(
            &mut ix,
            0,
            0,
            vec![EffectSummary::Granted {
                from: "root".into(),
                to: "player".into(),
                cap: "play".into(),
            }],
        )
        .unwrap();
        // "granted-and-not-revoked" — the canonical CALM finalized-dependent query.
        let q = Query::new()
            .atom(
                Pred::Granted,
                vec![
                    Term::var("F"),
                    Term::var("T"),
                    Term::sym("play"),
                    Term::var("H"),
                ],
            )
            .not_atom(Pred::Revoked, vec![Term::sym("play"), Term::Wild]);
        let sub = ix.subscribe(q).unwrap();
        assert!(ix.drain_subscription(sub).unwrap().is_empty());

        // A revocation lands: the row RETRACTS (absence is not stable — the
        // classifier's finalized-dependent case).
        feed(
            &mut ix,
            1,
            1,
            vec![EffectSummary::Revoked { cap: "play".into() }],
        )
        .unwrap();
        let events = ix.drain_subscription(sub).unwrap();
        assert_eq!(events.len(), 1);
        assert_eq!(
            events[0].retracted.len(),
            1,
            "the grant row retracted on revoke"
        );
        assert!(events[0].rows.is_empty(), "no live grant remains");
    }

    // ── (3) Local tx simulation predicts a turn that MATCHES the real commit. ──

    #[test]
    fn local_simulation_predicts_the_committed_result() {
        let mut ix = Indexer::new(64);
        feed(
            &mut ix,
            0,
            0,
            vec![field("hero", 0, "0a"), balance("hero", "gold", 10)],
        )
        .unwrap();

        // Optimistically render a turn that takes 4 damage (HP 0a->06) and spends
        // 3 gold (10->7) — WITHOUT a round-trip.
        let proposed = vec![field("hero", 0, "06"), balance("hero", "gold", 7)];
        let sim = ix.simulate(&proposed);
        assert_eq!(sim.at_index, 1, "predicted for the next dense position");
        let predicted = sim.predicted.get("hero").expect("hero touched");
        assert_eq!(predicted.fields.get(&0).map(String::as_str), Some("06"));
        assert_eq!(predicted.balances.get("gold").copied(), Some(7));
        // Simulation did NOT mutate the live view.
        assert_eq!(
            ix.view().field("hero", 0),
            Some("0a"),
            "sim is non-mutating"
        );

        // The real receipt for that turn commits at index 1 with those effects.
        feed(&mut ix, 1, 1, proposed).unwrap();
        // The committed view MATCHES the prediction, cell-for-cell.
        assert_eq!(
            ix.view().cell("hero"),
            Some(predicted),
            "commit matches optimistic render"
        );
    }

    // ── (4) The non-omission certificate proves completeness; a dropped update
    //    is caught. ──

    #[test]
    fn the_non_omission_certificate_proves_completeness_and_catches_a_drop() {
        let mut ix = Indexer::new(64);
        feed(&mut ix, 0, 0, vec![field("hero", 0, "0a")]).unwrap();
        feed(&mut ix, 1, 1, vec![field("hero", 0, "08")]).unwrap();
        feed(&mut ix, 2, 2, vec![field("hero", 0, "05")]).unwrap();

        let q = Query::new().atom(
            Pred::Field,
            vec![
                Term::sym("hero"),
                Term::var("I"),
                Term::var("V"),
                Term::var("H"),
            ],
        );
        let answer = ix.attested_answer(q).unwrap();
        let root = ix.index_root();
        // The answer VERIFIES against the published root — the rows are exactly
        // those derivable from the WHOLE committed log (nothing hidden).
        answer
            .verify(&Blake3Mmr, &root)
            .expect("whole-log answer omitted nothing");

        // Now model the indexer HIDING a state change: drop a receipt from the
        // certified slice. Re-verification FAILS — the dense count is broken
        // (`server_cannot_omit_position`).
        let mut tampered = answer.clone();
        tampered.slice.receipts.remove(1);
        assert!(
            tampered.verify(&Blake3Mmr, &root).is_err(),
            "a dropped receipt is caught by the non-omission certificate"
        );

        // And a WRONG trusted root (a client pinned a different head) fails closed.
        let mut wrong = [0u8; 32];
        wrong[0] = 0xFF;
        assert!(
            answer.verify(&Blake3Mmr, &wrong).is_err(),
            "wrong root fails closed"
        );
    }

    // ── (5) A forged / out-of-order stream update is REJECTED (rides the
    //    ReceiptStream gate); nothing is folded. ──

    #[test]
    fn a_forged_stream_update_is_rejected_and_nothing_is_folded() {
        let mut ix = Indexer::new(64);
        feed(&mut ix, 0, 0, vec![field("hero", 0, "0a")]).unwrap();

        // A FORGED frame: claim index 1, but the claimed receipt_hash is a
        // DIFFERENT receipt's (the body does not hash to it).
        let honest_other = hex32(&receipt(99).receipt_hash());
        let forged = ReceiptEnvelope::new(1, honest_other, 1881, vec![], vec![], receipt(7));
        let err = ix.ingest(forged, vec![field("hero", 0, "de")]).unwrap_err();
        assert_eq!(err, IngestError::Forged { chain_index: 1 });
        // NOTHING was folded: the view, the EDB, and the MMR are all unchanged.
        assert_eq!(
            ix.view().field("hero", 0),
            Some("0a"),
            "forged effect not applied"
        );
        assert_eq!(
            ix.committed_len(),
            1,
            "the forged receipt is not in the log"
        );

        // An OUT-OF-ORDER frame (a gap): index 2 when 1 is expected → rejected.
        let (gap, _) = env(2, 2);
        let err = ix.ingest(gap, vec![field("hero", 0, "cc")]).unwrap_err();
        assert_eq!(
            err,
            IngestError::OutOfOrder {
                expected: 1,
                got: 2
            }
        );
        assert_eq!(ix.committed_len(), 1, "the gapped receipt is not folded");

        // The correct next receipt still flows, and the certificate over the
        // (un-poisoned) log still verifies.
        feed(&mut ix, 1, 1, vec![field("hero", 0, "08")]).unwrap();
        assert_eq!(ix.view().field("hero", 0), Some("08"));
        let q = Query::new().atom(
            Pred::Field,
            vec![
                Term::sym("hero"),
                Term::var("I"),
                Term::var("V"),
                Term::var("H"),
            ],
        );
        let answer = ix.attested_answer(q).unwrap();
        answer
            .verify(&Blake3Mmr, &ix.index_root())
            .expect("clean log verifies");
    }

    // ── A resume cursor threads the fold across a reconnect (dedup is a no-op
    //    fold). ──

    #[test]
    fn a_duplicate_redelivery_is_a_noop_fold() {
        let mut ix = Indexer::new(64);
        feed(&mut ix, 0, 0, vec![field("hero", 0, "0a")]).unwrap();
        feed(&mut ix, 1, 1, vec![field("hero", 0, "08")]).unwrap();
        // The stream re-delivers the last position on reconnect (at-least-once).
        let out = feed(&mut ix, 1, 1, vec![field("hero", 0, "08")]).unwrap();
        assert_eq!(out, IngestOutcome::Duplicate, "re-delivery deduplicated");
        assert_eq!(ix.committed_len(), 2, "no double-fold");
        assert_eq!(ix.view().field("hero", 0), Some("08"));
        assert_eq!(ix.resume_cursor(), Cursor::delivered_through(1));
    }

    // ── A filtered query over the view (a game read: "who is below 10 HP") ──

    #[test]
    fn a_filtered_query_reads_the_current_state() {
        let mut ix = Indexer::new(64);
        // Two heroes' HP in slot 0 (as Nat values via balance-style facts is
        // awkward; use the `balance` predicate which carries Nat amounts).
        feed(&mut ix, 0, 0, vec![balance("alice", "hp", 8)]).unwrap();
        feed(&mut ix, 1, 1, vec![balance("bob", "hp", 20)]).unwrap();
        feed(&mut ix, 2, 2, vec![balance("alice", "hp", 3)]).unwrap(); // alice took damage

        // "cells whose current hp observation is < 10" — a conjunctive query with
        // a filter. Note: monotone EDB keeps ALL observations; the LATEST per cell
        // is the view's job, the query sees the stamped history.
        let q = Query::new()
            .atom(
                Pred::Balance,
                vec![
                    Term::var("C"),
                    Term::sym("hp"),
                    Term::var("A"),
                    Term::var("H"),
                ],
            )
            .filter(Term::var("A"), CmpOp::Lt, Term::nat(10));
        let rows = ix.query(&q).unwrap();
        // alice@8 (h0) and alice@3 (h2) are both < 10; bob@20 is not.
        assert_eq!(rows.len(), 2);
        // The VIEW gives the CURRENT hp (latest): alice=3, bob=20.
        assert_eq!(ix.view().balance("alice", "hp"), Some(3));
        assert_eq!(ix.view().balance("bob", "hp"), Some(20));
    }
}
