//! THE TEMPORAL COCKPIT model — the gpui-free brain behind the "⏳ TIME" tab.
//!
//! The headline livability surface of deos: time-travel + suspend + fractal
//! meta-debug, as ONE control panel. This module is the pure projection the
//! cockpit's TIME tab renders — exactly the `reflect::Inspectable` /
//! [`crate::ui_snapshot`] / [`crate::meta_debug`] pattern: a gpui-free model the
//! view paints, so it is `cargo test`-able without a window.
//!
//! It REUSES the real models, never a parallel one:
//!
//!   * the REWIND SCRUBBER reads [`World::recorded_turns`] — the live world's own
//!     canonical [`crate::replay::History`] — and lands each tick by ROOT-VERIFIED
//!     [`History::replay_to`](crate::replay::History::replay_to). The
//!     [`Liveness`](crate::ui_snapshot::Liveness) badge is the rehydration model's
//!     honest trichotomy: [`Liveness::Live`] at the head, [`Liveness::ReplayedDeterministic`]
//!     in the past (the camera re-ran from the witnessed log).
//!   * the SUSPEND readout reads the M5 gate on [`World`] directly
//!     ([`World::is_suspended`], [`World::pending_turns`]) — the head is FROZEN and
//!     the staged continuation is the real pending queue.
//!   * the METASTACK breadcrumb reads [`crate::meta_debug::MetaStack`] — the
//!     lazily-materialized reflective tower (BASE → meta¹ → meta² …).
//!
//! The cockpit owns the mutable state (the scrubber cursor, the `MetaStack`) and
//! drives the real `World` gate (`suspend`/`resume`); this module turns a snapshot
//! of that state into a model. `present` stays pure: building a model NEVER mutates
//! the world.

use crate::meta_debug::{MetaLevelId, MetaStack};
use crate::replay::{History, RecordedStep, ScrubSource, StateDiff};
use crate::ui_snapshot::Liveness;
use crate::world::World;
use dregg_cell::{CellId, Ledger};
use dregg_turn::action::Effect;
use dregg_turn::reversible::{ReversibleHistory, ReversibleStep};
use dregg_turn::turn::TurnResult;
use std::sync::Arc;

// ===========================================================================
// The scrubber-tick model — one landing point on the rewind timeline.
// ===========================================================================

/// One tick on the rewind scrubber — a landing point in history (`step` in
/// `0..=history.len()`). The scrubber ticks ARE the turns (plus the genesis
/// installs and the empty-pre-genesis root). Dragging the scrubber to a tick
/// re-derives the focused views at that past point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScrubTick {
    /// The history step this tick lands on (`0` = empty pre-genesis ledger).
    pub step: usize,
    /// The canonical [`dregg_cell::Ledger::root`] recorded at this landing (the
    /// root tooth replay verifies against).
    pub root: [u8; 32],
    /// A short human label for the tick — the receipt/turn (or genesis) here.
    pub label: String,
    /// `true` iff this tick is a committed TURN (vs a genesis install or the
    /// empty root) — the scrubber draws turns as the "real" ticks.
    pub is_turn: bool,
    /// Whether the turn AT this tick can be UN-TURNED (the reversibility organ's
    /// verdict, `dregg_turn::Turn::is_reversible` over the pre-state): `Some(true)`
    /// = a reversible step (clean/contextual — rewinding past it restores state
    /// modulo the monotone nonce); `Some(false)` = a COMMITTED boundary (a spend /
    /// burn / revoke / terminal lifecycle — the scrubber cannot un-turn past it);
    /// `None` for genesis / the empty root (nothing to invert). This is the
    /// per-step reversibility the rewind UI draws so you SEE where the un-turn
    /// frontier is, not just where the cursor sits.
    pub reversible: Option<bool>,
}

// ===========================================================================
// The whole TIME-tab model.
// ===========================================================================

/// THE TEMPORAL COCKPIT MODEL — the full state the "⏳ TIME" tab paints, built
/// fresh each frame from the live [`World`] + the cockpit's scrubber cursor + the
/// [`MetaStack`]. Every field is RE-DERIVED from the real models (the verified
/// history, the suspend gate, the reflective tower); nothing is a parallel cache.
#[derive(Clone, Debug)]
pub struct TimeCockpitModel {
    // --- the REWIND SCRUBBER ------------------------------------------------
    /// Every landing point on the timeline (genesis → head), in order.
    pub ticks: Vec<ScrubTick>,
    /// Where the scrubber cursor sits (a step in `0..=history.len()`).
    pub cursor: usize,
    /// The head step (the live present — `history.len()`).
    pub head: usize,
    /// The verified reconstruction AT the cursor: the cells (id, balance, caps),
    /// sorted by id, re-derived by root-verified replay. Empty iff the replay
    /// failed (surfaced via `cursor_verified = false`, never faked).
    pub cursor_cells: Vec<(CellId, i64, usize)>,
    /// `true` iff the cursor's reconstruction root-verified against the recorded
    /// tooth (the anti-substitution tooth — `false` is a surfaced bug, not a panic).
    pub cursor_verified: bool,
    /// The canonical root at the cursor.
    pub cursor_root: [u8; 32],
    /// `true` iff the cursor's image was restored via the UMEM BOUNDARY (the O(1)
    /// `reify_ledger` inverse fold — the umem time-travel revolution), `false` iff
    /// the scrub fell back to genesis replay for a cell outside the faithful class.
    pub cursor_via_umem: bool,
    /// The honest liveness of the cursor view: [`Liveness::Live`] at the head,
    /// [`Liveness::ReplayedDeterministic`] in the past (the image rewound, the
    /// camera re-ran from the witnessed log).
    pub liveness: Liveness,
    /// The diff from the previous step to the cursor (what the cursor's turn did),
    /// `None` at genesis (step 0).
    pub diff_from_prev: Option<StateDiff>,

    // --- the ⏸ SUSPEND gate (M5) -------------------------------------------
    /// `true` iff the live loop is HALTED (the head is frozen). Distinct from the
    /// scrubber being in the past: suspend stops the REAL loop.
    pub suspended: bool,
    /// The live (head) turn-height — what the running loop is at.
    pub live_height: u64,
    /// The staged continuation — the pending turns queued while suspended, in
    /// arrival order (one label per queued turn). Empty unless suspended-with-work.
    pub pending: Vec<String>,

    // --- the METASTACK navigator (the fractal meta-debug) -------------------
    /// The reflective tower as a breadcrumb: BASE → meta¹ → meta² … . Empty iff
    /// no meta-level is materialized (the live system runs, un-reflected).
    pub metastack: Vec<MetaCrumb>,
}

/// One crumb in the METASTACK breadcrumb — a materialized meta-level.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetaCrumb {
    /// The level depth (`0` = BASE, the first suspend; higher = a meta-frame on a
    /// meta-frame — "debug the debugger").
    pub level: usize,
    /// The frozen head-height this level was captured at.
    pub frozen_height: u64,
    /// `true` iff this is the innermost (top) level — the one the operator is
    /// currently debugging (the focus of "debug the debugger").
    pub is_top: bool,
}

impl TimeCockpitModel {
    /// Build the model for `world` with the scrubber at `cursor`, over the cockpit's
    /// `stack`. Performs the VERIFIED replay at the cursor (and the prev-step diff);
    /// a replay error is surfaced as an unverified cursor, never a panic. PURE — it
    /// never mutates the world.
    pub fn build(world: &World, cursor: usize, stack: &MetaStack) -> Self {
        let history: &History = world.recorded_turns();
        let head = history.len();
        let cursor = cursor.min(head);

        // The scrubber ticks — every landing (the empty root + each genesis/turn).
        // Reversibility is classified for ALL steps in ONE forward pass (O(N)); the
        // old per-tick `replay_to(step-1)` was O(N²) and — rebuilt every frame on the
        // paint path — is what hung the TIME tab as the history grew.
        let revs = history.reversibility_classification();
        let mut ticks: Vec<ScrubTick> = Vec::with_capacity(head + 1);
        for cp in history.checkpoints() {
            let (label, is_turn, reversible) = if cp.step == 0 {
                ("genesis (empty image)".to_string(), false, None)
            } else {
                let step = &history.steps()[cp.step - 1];
                match step {
                    crate::replay::RecordedStep::Committed { .. } => {
                        (step.label(), true, revs.get(cp.step - 1).copied().flatten())
                    }
                    crate::replay::RecordedStep::Genesis { .. }
                    | crate::replay::RecordedStep::GenesisBatch { .. }
                    | crate::replay::RecordedStep::GenesisUpdate { .. }
                    | crate::replay::RecordedStep::FactoryDeployment { .. } => {
                        (step.label(), false, None)
                    }
                }
            };
            ticks.push(ScrubTick {
                step: cp.step,
                root: cp.root,
                label,
                is_turn,
                reversible,
            });
        }

        // The verified reconstruction at the cursor — restored via the UMEM BOUNDARY
        // (`History::reify_to`: the O(1) `reify_ledger` inverse fold, root-verified),
        // falling back to genesis replay only for a cell outside the faithful class.
        let (cursor_cells, cursor_verified, cursor_via_umem) = match history.reify_to(cursor) {
            Ok((ledger, source)) => {
                let mut cells: Vec<(CellId, i64, usize)> = ledger
                    .iter()
                    .map(|(id, c)| (*id, c.state.balance(), c.capabilities.len()))
                    .collect();
                cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
                (cells, true, source == ScrubSource::UmemBoundary)
            }
            Err(_) => (Vec::new(), false, false),
        };
        let cursor_root = history.root_at(cursor).unwrap_or_default();

        // The liveness badge: Live iff the cursor names the head (the live present);
        // ReplayedDeterministic once it falls into the past (the image rewound).
        let liveness = if cursor == head {
            Liveness::Live
        } else {
            Liveness::ReplayedDeterministic
        };

        // The diff from the previous step — what the cursor's turn did.
        let diff_from_prev = if cursor > 0 {
            history.diff(cursor - 1, cursor).ok()
        } else {
            None
        };

        // The suspend gate (M5) — read straight off the world.
        let suspended = world.is_suspended();
        let live_height = world.height();
        let pending: Vec<String> = world
            .pending_turns()
            .enumerate()
            .map(|(i, t)| {
                format!(
                    "queued #{i} · agent {} · {} root action(s)",
                    crate::reflect::short_hex(t.agent.as_bytes()),
                    t.call_forest.roots.len()
                )
            })
            .collect();

        // The metastack breadcrumb — the reflective tower (BASE → meta¹ → …).
        let depth = stack.depth();
        let metastack: Vec<MetaCrumb> = (0..depth)
            .filter_map(|d| {
                let view = stack.get(MetaLevelId(d))?;
                Some(MetaCrumb {
                    level: d,
                    frozen_height: view.cursor.height,
                    is_top: d + 1 == depth,
                })
            })
            .collect();

        TimeCockpitModel {
            ticks,
            cursor,
            head,
            cursor_cells,
            cursor_verified,
            cursor_root,
            cursor_via_umem,
            liveness,
            diff_from_prev,
            suspended,
            live_height,
            pending,
            metastack,
        }
    }

    /// `true` iff the scrubber cursor is at the live head (the present) — the badge
    /// reads `Live`, the image is the running state.
    pub fn at_head(&self) -> bool {
        self.cursor == self.head
    }

    /// The UN-TURN FLOOR: the highest step that is a COMMITTED boundary (a turn the
    /// reversibility organ classifies irreversible — a spend / burn / revoke /
    /// terminal). `undo_to` reverses a contiguous suffix most-recent-first, so it
    /// can rewind the image down to (but NOT past) this floor; `0` iff the whole
    /// history is reversible. The headline "you can rewind to k{floor}, not past the
    /// committed move there."
    pub fn undo_floor(&self) -> usize {
        self.ticks
            .iter()
            .filter(|t| t.reversible == Some(false))
            .map(|t| t.step)
            .max()
            .unwrap_or(0)
    }

    /// A human badge for the un-turn floor: where the rewind frontier is, in
    /// reversibility terms (the cockpit's TIME tab draws this above the scrubber).
    pub fn undo_floor_badge(&self) -> String {
        let floor = self.undo_floor();
        if floor == 0 {
            "↺ fully reversible — the whole image can be un-turned to genesis".to_string()
        } else {
            format!(
                "⊘ un-turn floor at k{floor} — a committed move (spend/burn/revoke/terminal) \
                 there cannot be reversed; the image rewinds to k{floor}, not past it"
            )
        }
    }

    /// The human badge text for the cursor's liveness (the operator reads "am I
    /// looking at the live present, or a re-derived past?").
    pub fn liveness_badge(&self) -> String {
        match self.liveness {
            Liveness::Live => "● LIVE · at the head (the present)".to_string(),
            Liveness::ReplayedDeterministic => format!(
                "⟲ REPLAYED · re-derived @k{} (root-verified from the log)",
                self.cursor
            ),
            Liveness::ReconstructedApproximate => {
                "≈ APPROXIMATE · the log does not reach this point".to_string()
            }
        }
    }
}

// ===========================================================================
// ⑂ FORK THE PAST — wiring `ReversibleHistory::fork_at` into the rewind UI.
//
// The rewind scrubber above LANDS the image on a past step `k` (root-verified
// replay). This block adds the second half of the FIRST-CLASS-REVERSIBILITY
// §3.3 rung: *branch* the past. The cockpit mirrors the live world's recorded
// history into a `dregg_turn::reversible::ReversibleHistory`, then `fork_at(k)`s
// the event-structure config-lattice DOWN-SET — an `Arc`-handle clone of the
// `[0,k]` prefix, NOT a re-execution (`Arc::ptr_eq` witnesses each shared step)
// — and drives a DIVERGENT verified turn from `k` forward. The parent timeline
// is structurally immune: the fork only ever PUSHES fresh steps onto its own
// vector, never mutating the shared prefix it inherited. This is the temporal
// dual of branch-and-stitch's spatial `World::fork` (`branch_stitch_session`).
// ===========================================================================

/// Build a [`ReversibleHistory`] mirror of the live world's recorded history, so
/// the cockpit can [`ReversibleHistory::fork_at`] / [`ReversibleHistory::undo_to`]
/// the verified turn log. Births, setup replacements and turns retain their
/// exact order. Original costs, factories and per-turn clocks are reused, and
/// every receipt and boundary must match before this mirror is returned.
pub fn reversible_mirror(world: &World) -> Result<ReversibleHistory, BranchError> {
    reversible_mirror_steps(world, world.recorded_turns().steps())
}

// Roots and execution configuration remain bound to `world`; accepting a step
// slice lets tests corrupt copied evidence without mutating the live history.
fn reversible_mirror_steps(
    world: &World,
    steps: &[RecordedStep],
) -> Result<ReversibleHistory, BranchError> {
    let history: &History = world.recorded_turns();
    let floor = steps
        .iter()
        .filter_map(|step| match step {
            RecordedStep::Committed { timestamp, .. } => Some(*timestamp),
            _ => None,
        })
        .min()
        .unwrap_or(world.timestamp())
        .min(world.timestamp());
    let mut rh = ReversibleHistory::with_costs(floor, world.replay_costs());
    let mut ledger = Ledger::new();
    let mut ex = rh.fresh_executor();
    for (index, step) in steps.iter().enumerate() {
        match step {
            RecordedStep::FactoryDeployment { deployment } => {
                rh.record_factory_deployment(&mut ex, &mut ledger, *deployment.clone())
                    .map_err(|error| BranchError::ReplayRefused {
                        step: index,
                        reason: error.to_string(),
                    })?;
            }
            RecordedStep::Genesis { cell } => {
                if ledger.contains(&cell.id()) {
                    return Err(BranchError::ReplayRefused {
                        step: index,
                        reason: "duplicate birth".to_string(),
                    });
                }
                rh.record_genesis(&mut ledger, (**cell).clone());
            }
            RecordedStep::GenesisBatch { cells } => {
                if cells.len() < 2 {
                    return Err(BranchError::ReplayRefused {
                        step: index,
                        reason: "recorded birth batch has fewer than two cells".to_string(),
                    });
                }
                rh.record_genesis_batch(&mut ledger, cells.clone())
                    .map_err(|error| BranchError::ReplayRefused {
                        step: index,
                        reason: error.to_string(),
                    })?;
            }
            RecordedStep::GenesisUpdate { cell } => {
                rh.record_genesis_update(&mut ledger, (**cell).clone())
                    .map_err(|error| BranchError::ReplayRefused {
                        step: index,
                        reason: error.to_string(),
                    })?;
            }
            RecordedStep::Committed {
                turn,
                receipt,
                timestamp,
                post_root,
            } => {
                if *timestamp != receipt.timestamp {
                    return Err(BranchError::ReplayRefused {
                        step: index,
                        reason: "recorded timestamp differs from receipt".to_string(),
                    });
                }
                if turn.previous_receipt_hash != ex.get_last_receipt_hash(&turn.agent) {
                    return Err(BranchError::ReplayRefused {
                        step: index,
                        reason: "receipt chain head differs".to_string(),
                    });
                }
                ex.set_timestamp(*timestamp);
                let actual = rh
                    .record_commit(&ex, &mut ledger, (**turn).clone())
                    .ok_or_else(|| BranchError::ReplayRefused {
                        step: index,
                        reason: "recorded turn did not commit".to_string(),
                    })?;
                if actual.receipt_hash() != receipt.receipt_hash() {
                    return Err(BranchError::ReplayRefused {
                        step: index,
                        reason: "recorded receipt differs".to_string(),
                    });
                }
                if ledger.root() != *post_root {
                    return Err(BranchError::ReplayRefused {
                        step: index,
                        reason: "embedded post-state root differs".to_string(),
                    });
                }
            }
        }
        if history.root_at(index + 1) != Some(ledger.root()) {
            return Err(BranchError::ReplayRefused {
                step: index,
                reason: "recorded root differs".to_string(),
            });
        }
    }
    Ok(rh)
}

/// Why a [`TimeBranch`] could not be formed (fail-closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BranchError {
    /// The source history could not be reproduced exactly, including setup.
    ReplayRefused { step: usize, reason: String },
    /// The reconstructed fork-point ledger did NOT match the recorded root tooth
    /// at `k` — the anti-substitution catch (a dishonest prefix replay would
    /// land on a different root than the one the live history committed).
    ForkRootMismatch {
        step: usize,
        got: [u8; 32],
        want: [u8; 32],
    },
    /// The divergent turn was REJECTED by the executor on the fork (e.g. the
    /// agent lacked authority, or the move broke conservation) — the same
    /// verification the live world enforces, firing on the branch.
    DriveRejected { step: usize },
}

impl std::fmt::Display for BranchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BranchError::ReplayRefused { step, reason } => {
                write!(f, "history replay refused at step {step}: {reason}")
            }
            BranchError::ForkRootMismatch { step, .. } => {
                write!(f, "fork-point root mismatch at k{step} (fail-closed)")
            }
            BranchError::DriveRejected { step } => {
                write!(
                    f,
                    "the divergent turn at k{step} was rejected by the executor"
                )
            }
        }
    }
}

impl std::error::Error for BranchError {}

/// The RESULT of forking the past at step `k` and driving a divergent verified
/// turn from it — the pure model the cockpit's "⑂ BRANCH HERE" affordance paints.
/// Built fresh by [`TimeBranch::fork_and_drive`]; every field is a fact about the
/// real [`ReversibleHistory`] fork (the shared prefix, the verified divergent
/// root, the untouched parent), never a parallel cache.
#[derive(Clone, Debug)]
pub struct TimeBranch {
    /// The past step the branch forked from (the scrubber cursor `k`).
    pub fork_step: usize,
    /// The parent timeline's head at fork time (the live present it stands at).
    pub parent_head: usize,
    /// The divergent timeline's head after driving the divergent turn.
    pub branch_head: usize,
    /// The number of prefix steps SHARED with the parent — witnessed by
    /// [`Arc::ptr_eq`] (the fork's prefix step IS the parent's, not a re-run).
    pub shared_prefix: usize,
    /// The verified root the fork lands on at `k` (== the parent's recorded tooth).
    pub fork_root: [u8; 32],
    /// The verified root the divergent branch head landed on.
    pub branch_root: [u8; 32],
    /// The parent's recorded root one step above the fork (`k+1`), if the parent
    /// had a turn there — the timeline the branch DIVERGES from.
    pub parent_next_root: Option<[u8; 32]>,
    /// `true` iff the branch root differs from the parent's next root (a genuine
    /// divergent future), or the fork was at/above the parent head (divergent by
    /// existence — a fresh future off the present).
    pub diverged: bool,
    /// `true` iff the divergent turn committed + root-verified on the fork.
    pub verified: bool,
    /// `true` iff the parent timeline stands untouched (same head, same root) —
    /// the shared down-set is immutable, so this must hold.
    pub parent_untouched: bool,
    /// The reconstructed branch-head cells (id, balance, caps), sorted by id —
    /// the DIVERGENT image, built ON the past state, not the live head.
    pub cells: Vec<(CellId, i64, usize)>,
    /// A human narrative of what happened (the cockpit prints it under the panel).
    pub log: Vec<String>,
}

impl TimeBranch {
    /// **Fork the past at step `k` and drive a divergent verified turn from it.**
    ///
    /// Mirrors the live world into a [`ReversibleHistory`], [`ReversibleHistory::fork_at`]s
    /// the shared `[0,k]` down-set, reconstructs the fork-point ledger (root-verified
    /// against the recorded tooth, fail-closed on mismatch), then drives `effects`
    /// as a bare verified turn authored by `agent` at the PAST freshness nonce. The
    /// parent mirror is never mutated — the fork pushes only onto its own vector.
    pub fn fork_and_drive(
        world: &World,
        k: usize,
        agent: CellId,
        effects: Vec<Effect>,
    ) -> Result<TimeBranch, BranchError> {
        let mirror = reversible_mirror(world)?;
        let parent_head = mirror.len();
        let k = k.min(parent_head);
        let parent_head_root_before = mirror.root_at(parent_head);
        let parent_next_root = (k < parent_head).then(|| mirror.root_at(k + 1));

        // ⑂ FORK THE SHARED DOWN-SET — Arc-handle prefix clone, lands on roots[k].
        let mut fork = mirror.fork_at(k);
        let fork_root = fork.root_at(k);

        // WITNESS the sharing: every prefix step IS the parent's (ptr-equal).
        let shared_prefix = (0..k)
            .filter(|&i| Arc::ptr_eq(&fork.steps()[i], &mirror.steps()[i]))
            .count();

        // Reconstruct the fork-point ledger AND prime the executor chain-heads to
        // `k`, so the divergent turn chains as a fresh forward turn in the agent's
        // chain (the same warm-replay `undo_to` does before walking backward).
        let mut ex = fork.fresh_executor();
        let mut working = Ledger::new();
        for (index, step) in fork.steps().iter().enumerate() {
            match step.as_ref() {
                ReversibleStep::FactoryDeployment { deployment } => {
                    deployment
                        .apply(&mut ex)
                        .map_err(|reason| BranchError::ReplayRefused {
                            step: index,
                            reason,
                        })?;
                }
                ReversibleStep::Genesis { cell } => {
                    working.insert_cell(cell.clone()).map_err(|error| {
                        BranchError::ReplayRefused {
                            step: index,
                            reason: format!("{error:?}"),
                        }
                    })?;
                }
                ReversibleStep::GenesisBatch { cells } => {
                    // This ledger is a private reconstruction. No cursor or
                    // projection is published until every batch member exists.
                    for cell in cells {
                        working.insert_cell(cell.clone()).map_err(|error| {
                            BranchError::ReplayRefused {
                                step: index,
                                reason: format!("{error:?}"),
                            }
                        })?;
                    }
                }
                ReversibleStep::GenesisUpdate { before, cell } => {
                    let current =
                        working
                            .get(&cell.id())
                            .ok_or_else(|| BranchError::ReplayRefused {
                                step: index,
                                reason: "setup replacement cell is absent".to_string(),
                            })?;
                    if current != before {
                        return Err(BranchError::ReplayRefused {
                            step: index,
                            reason: "setup preimage differs".to_string(),
                        });
                    }
                    working.replace_cell(cell.clone()).map_err(|error| {
                        BranchError::ReplayRefused {
                            step: index,
                            reason: error.to_string(),
                        }
                    })?;
                }
                ReversibleStep::Committed { turn, receipt, .. } => {
                    ex.set_timestamp(receipt.timestamp);
                    match ex.execute(turn, &mut working) {
                        TurnResult::Committed {
                            receipt: actual, ..
                        } if actual.receipt_hash() == receipt.receipt_hash() => {
                            ex.set_last_receipt_hash(actual.agent, actual.receipt_hash());
                        }
                        result => {
                            return Err(BranchError::ReplayRefused {
                                step: index,
                                reason: format!("recorded turn differs: {result:?}"),
                            })
                        }
                    }
                }
            }
            if working.root() != fork.root_at(index + 1) {
                return Err(BranchError::ForkRootMismatch {
                    step: index + 1,
                    got: working.root(),
                    want: fork.root_at(index + 1),
                });
            }
        }
        // Anti-substitution: the reconstructed past MUST equal the recorded tooth.
        let got = working.root();
        if got != fork_root {
            return Err(BranchError::ForkRootMismatch {
                step: k,
                got,
                want: fork_root,
            });
        }

        // Drive the DIVERGENT turn at the PAST freshness nonce (not the head's) —
        // a bare unchecked turn; the executor's conservation / ocap guarantees
        // still gate it exactly as on the live line.
        let nonce = working.get(&agent).map(|c| c.state.nonce()).unwrap_or(0);
        let turn = crate::world::bare_turn(agent, nonce, effects);
        let verified = fork.record_commit(&ex, &mut working, turn).is_some();
        if !verified {
            return Err(BranchError::DriveRejected { step: k });
        }

        let branch_head = fork.len();
        let branch_root = fork.root_at(branch_head);

        // The PARENT stands untouched — the shared prefix is immutable; the fork
        // only ever pushed a fresh step onto its OWN vector.
        let parent_untouched =
            mirror.len() == parent_head && mirror.root_at(parent_head) == parent_head_root_before;

        // Divergence: a different root than the parent's next step (or a fresh
        // future off the head/genesis, divergent by existence).
        let diverged = match parent_next_root {
            Some(pr) => pr != branch_root,
            None => true,
        };

        let mut cells: Vec<(CellId, i64, usize)> = working
            .iter()
            .map(|(id, c)| (*id, c.state.balance(), c.capabilities.len()))
            .collect();
        cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));

        let short = |r: &[u8; 32]| crate::reflect::short_hex(r);
        let log = vec![
            format!("⑂ forked the past at k{k} (parent head k{parent_head})"),
            format!("shared {shared_prefix} prefix step(s) — Arc down-set, no re-execution"),
            format!(
                "the fork lands on roots[k{k}] = {} (recorded tooth)",
                short(&fork_root)
            ),
            format!(
                "drove a DIVERGENT verified turn → branch head k{branch_head} root {}",
                short(&branch_root)
            ),
            if diverged {
                "the branch root DIFFERS from the parent timeline — a genuine divergent future"
                    .to_string()
            } else {
                "the branch reproduced the parent's next root (it replayed the same move)"
                    .to_string()
            },
            if parent_untouched {
                format!("the parent timeline STANDS UNTOUCHED at k{parent_head}")
            } else {
                "WARNING: the parent timeline changed (the down-set should be immutable)"
                    .to_string()
            },
        ];

        Ok(TimeBranch {
            fork_step: k,
            parent_head,
            branch_head,
            shared_prefix,
            fork_root,
            branch_root,
            parent_next_root,
            diverged,
            verified,
            parent_untouched,
            cells,
            log,
        })
    }

    /// A one-line headline for the branch banner.
    pub fn headline(&self) -> String {
        format!(
            "⑂ branched at k{} · parent head k{} untouched · branch head k{} (verified{})",
            self.fork_step,
            self.parent_head,
            self.branch_head,
            if self.diverged { ", divergent" } else { "" }
        )
    }
}

// ===========================================================================
// TESTS — gpui-free, exactly as replay.rs / ui_snapshot.rs / meta_debug.rs are.
// `cargo test --features embedded-executor`
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{transfer, ResumeMode, World};

    /// A small world: a treasury (1_000) and a sink (0), three committed turns.
    fn fixture() -> (World, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        for amt in [100u64, 200, 50] {
            let t = w.turn(treasury, vec![transfer(treasury, sink, amt)]);
            assert!(w.commit_turn(t).is_committed());
        }
        (w, treasury, sink)
    }

    #[test]
    fn reversible_mirror_refuses_corrupt_clock_and_embedded_root_evidence() {
        let (world, _, _) = fixture();
        let source_root = world.state_root();
        let recorded = world.recorded_turns().steps().to_vec();
        let second_turn = recorded
            .iter()
            .enumerate()
            .filter_map(|(index, step)| {
                matches!(step, RecordedStep::Committed { .. }).then_some(index)
            })
            .nth(1)
            .expect("fixture has a second turn");

        let mut bad_clock = recorded.clone();
        let RecordedStep::Committed {
            timestamp, receipt, ..
        } = &mut bad_clock[second_turn]
        else {
            unreachable!("selected a committed step");
        };
        // A backward clock update is ignored by the executor. Without checking
        // the stored field itself, the original receipt can still reproduce.
        *timestamp = receipt.timestamp.saturating_sub(1);
        assert!(matches!(reversible_mirror_steps(&world, &bad_clock),
            Err(BranchError::ReplayRefused { step, reason })
                if step == second_turn && reason == "recorded timestamp differs from receipt"));

        let mut bad_root = recorded;
        let RecordedStep::Committed { post_root, .. } = &mut bad_root[second_turn] else {
            unreachable!("selected a committed step");
        };
        post_root[0] ^= 1;
        assert!(matches!(reversible_mirror_steps(&world, &bad_root),
            Err(BranchError::ReplayRefused { step, reason })
                if step == second_turn && reason == "embedded post-state root differs"));

        assert!(reversible_mirror(&world).is_ok());
        assert_eq!(
            world.state_root(),
            source_root,
            "copied corruptions never modify the live source"
        );
    }

    #[test]
    fn atomic_birth_batches_have_one_tick_and_one_fork_boundary() {
        let mut world = World::new();
        let cells = vec![
            crate::world::make_open_cell(0x11, 1_000),
            crate::world::make_open_cell(0x22, 0),
        ];
        let ids = world
            .try_genesis_install_batch(cells)
            .expect("atomic pair birth");
        assert_eq!(world.recorded_turns().len(), 1);
        let batch_root = world.ledger().clone().root();
        let turn = world.turn(ids[0], vec![transfer(ids[0], ids[1], 10)]);
        assert!(world.commit_turn(turn).is_committed());
        let mirror = reversible_mirror(&world).expect("mirror complete birth batch");
        assert_eq!(mirror.len(), 2);
        assert!(
            matches!(mirror.steps()[0].as_ref(), ReversibleStep::GenesisBatch { cells } if cells.len() == 2)
        );
        assert!(mirror.replay_to(0).unwrap().iter().next().is_none());
        let at_birth = mirror.replay_to(1).unwrap();
        assert!(ids.iter().all(|id| at_birth.contains(id)));
        let model = TimeCockpitModel::build(&world, 1, &MetaStack::new());
        assert_eq!(model.ticks.len(), 3, "empty, whole batch, one turn");
        assert!(!model.ticks[1].is_turn);
        assert_eq!(model.cursor_cells.len(), 2);
        assert_eq!(model.ticks[1].root, batch_root);
        let branch =
            TimeBranch::fork_and_drive(&world, 1, ids[0], vec![transfer(ids[0], ids[1], 20)])
                .expect("fork after the complete batch");
        assert_eq!(branch.fork_root, batch_root);
        assert_eq!(branch.shared_prefix, 1);
        assert_eq!(branch.cells.len(), 2);
        assert!(branch.parent_untouched);
    }

    #[test]
    fn setup_updates_remain_distinct_in_ticks_mirrors_and_forks() {
        let mut world = World::new();
        let treasury = world.genesis_cell(0x11, 1_000);
        let sink = world.genesis_cell(0x22, 0);
        let before_setup = world.recorded_turns().len();
        let before = world.ledger().get(&treasury).unwrap().clone();
        assert!(world.genesis_grant_cap(&treasury, sink).is_some());
        let after_setup = world.recorded_turns().len();
        let turn = world.turn(treasury, vec![transfer(treasury, sink, 10)]);
        assert!(world.commit_turn(turn).is_committed());

        let mirror = reversible_mirror(&world).expect("exact mirror with setup update");
        assert_eq!(mirror.len(), world.recorded_turns().len());
        assert!(matches!(
            mirror.steps()[before_setup].as_ref(),
            ReversibleStep::GenesisUpdate { .. }
        ));
        assert_eq!(
            mirror.replay_to(before_setup).unwrap().get(&treasury),
            Some(&before)
        );
        for step in 0..=mirror.len() {
            assert_eq!(
                Some(mirror.root_at(step)),
                world.recorded_turns().root_at(step)
            );
        }
        let model = TimeCockpitModel::build(&world, after_setup, &MetaStack::new());
        assert!(!model.ticks[after_setup].is_turn);
        assert!(model.ticks[after_setup].label.starts_with("setup update"));
        assert_eq!(model.ticks[after_setup].reversible, None);
        let branch = TimeBranch::fork_and_drive(
            &world,
            after_setup,
            treasury,
            vec![transfer(treasury, sink, 20)],
        )
        .expect("fork retains setup update");
        assert_eq!(branch.fork_root, mirror.root_at(after_setup));
        assert!(branch.parent_untouched);
        assert!(branch.verified);
    }

    #[test]
    fn reversible_mirror_uses_the_worlds_actual_costs() {
        let mut costs = dregg_turn::ComputronCosts::zero();
        costs.action_base = 1;
        let mut world = World::with_costs_and_timestamp(costs, 1_700_000_000);
        let treasury = world.genesis_cell(0x11, 1_000);
        let sink = world.genesis_cell(0x22, 0);
        let mut turn = world.turn(treasury, vec![transfer(treasury, sink, 10)]);
        turn.fee = 10;
        assert!(world.commit_turn(turn).is_committed());
        let mirror = reversible_mirror(&world).expect("metered receipt must be reproduced");
        assert_eq!(
            mirror.replay_to(mirror.len()).unwrap().root(),
            world.ledger().clone().root()
        );
    }

    // ── the SCRUBBER classifies per-step REVERSIBILITY (the un-turn frontier) ─

    #[test]
    fn the_scrubber_classifies_per_step_reversibility() {
        use crate::world::burn;
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        // A reversible transfer, then an IRREVERSIBLE burn (a committed boundary).
        let t1 = w.turn(treasury, vec![transfer(treasury, sink, 10)]);
        assert!(w.commit_turn(t1).is_committed());
        let t2 = w.turn(treasury, vec![burn(treasury, 5)]);
        assert!(w.commit_turn(t2).is_committed(), "the burn commits");

        let stack = MetaStack::new();
        let m = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        let turns: Vec<_> = m.ticks.iter().filter(|t| t.is_turn).collect();
        assert_eq!(turns.len(), 2, "two committed turns");
        // The REAL Turn::is_reversible verdict, per step — not a transcription.
        assert_eq!(turns[0].reversible, Some(true), "transfer reverses (clean)");
        assert_eq!(
            turns[1].reversible,
            Some(false),
            "burn is a committed boundary"
        );
        // The un-turn floor sits AT the burn step — the rewind can't go past it.
        assert_eq!(m.undo_floor(), turns[1].step);
        assert!(m.undo_floor_badge().contains("un-turn floor"));
        // Genesis / empty-root ticks have nothing to invert → None.
        assert!(m
            .ticks
            .iter()
            .filter(|t| !t.is_turn)
            .all(|t| t.reversible.is_none()));
    }

    #[test]
    fn a_fully_reversible_history_has_a_zero_undo_floor() {
        let (w, _t, _s) = fixture(); // three transfers — all reversible
        let stack = MetaStack::new();
        let m = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert!(m
            .ticks
            .iter()
            .filter(|t| t.is_turn)
            .all(|t| t.reversible == Some(true)));
        assert_eq!(
            m.undo_floor(),
            0,
            "no committed boundary → rewind to genesis"
        );
        assert!(m.undo_floor_badge().contains("fully reversible"));
    }

    // ── the SCRUBBER ticks span genesis → head, turns flagged ────────────────

    #[test]
    fn the_scrubber_spans_genesis_to_head_with_turns_flagged() {
        let (w, _t, _s) = fixture();
        let stack = MetaStack::new();
        let head = w.recorded_turns().len(); // 2 genesis + 3 turns = 5
        let m = TimeCockpitModel::build(&w, head, &stack);
        assert_eq!(m.head, head);
        // One tick per landing (empty root + each step).
        assert_eq!(m.ticks.len(), head + 1);
        assert_eq!(
            m.ticks[0].step, 0,
            "the first tick is the empty pre-genesis root"
        );
        assert!(!m.ticks[0].is_turn, "the empty root is not a turn");
        // Exactly three ticks are committed TURNS.
        assert_eq!(m.ticks.iter().filter(|t| t.is_turn).count(), 3);
    }

    // ── the REWIND: dragging to the past re-derives the historical balance ───

    #[test]
    fn dragging_the_scrubber_rewinds_the_verified_image() {
        let (w, treasury, _sink) = fixture();
        let stack = MetaStack::new();
        let head = w.recorded_turns().len();

        // At the head: LIVE, treasury = 1000 − 100 − 200 − 50 = 650.
        let live = TimeCockpitModel::build(&w, head, &stack);
        assert!(live.at_head());
        assert_eq!(live.liveness, Liveness::Live);
        assert!(live.cursor_verified, "the head reconstruction verifies");
        let live_bal = live
            .cursor_cells
            .iter()
            .find(|(id, ..)| *id == treasury)
            .unwrap()
            .1;
        assert_eq!(live_bal, 650, "the head shows the live balance");

        // Rewind ONE turn (step head-1): the image rewinds, the badge says REPLAYED.
        let past = TimeCockpitModel::build(&w, head - 1, &stack);
        assert!(!past.at_head());
        assert_eq!(
            past.liveness,
            Liveness::ReplayedDeterministic,
            "the past is re-derived"
        );
        assert!(
            past.cursor_verified,
            "the past reconstruction root-verifies"
        );
        let past_bal = past
            .cursor_cells
            .iter()
            .find(|(id, ..)| *id == treasury)
            .unwrap()
            .1;
        assert_eq!(past_bal, 700, "rewound one turn: 1000 − 100 − 200 = 700");

        // The prev-step diff names what that turn did.
        assert!(
            past.diff_from_prev.is_some(),
            "a mid-history cursor has a prev-step diff"
        );
    }

    // ── the live scrub RESTORES VIA THE UMEM BOUNDARY (not genesis replay) ───

    #[test]
    fn the_live_scrub_restores_via_the_umem_boundary() {
        let (w, treasury, _sink) = fixture();
        let stack = MetaStack::new();
        let head = w.recorded_turns().len();

        // Drag to a PAST step: the cockpit model's image is restored by the umem
        // boundary (`reify_ledger`), not O(history) genesis replay — and it is
        // still root-verified and value-correct.
        let past = TimeCockpitModel::build(&w, head - 1, &stack);
        assert!(
            past.cursor_via_umem,
            "the live cockpit scrub restores via the umem boundary (the revolution, live)"
        );
        assert!(past.cursor_verified, "the umem restore root-verifies");
        let past_bal = past
            .cursor_cells
            .iter()
            .find(|(id, ..)| *id == treasury)
            .unwrap()
            .1;
        assert_eq!(
            past_bal, 700,
            "rewound one turn via umem: 1000 − 100 − 200 = 700"
        );

        // The head is also umem-restored.
        let live = TimeCockpitModel::build(&w, head, &stack);
        assert!(live.cursor_via_umem, "the head image is umem-restored too");
        assert!(live.at_head());
    }

    // ── the SUSPEND gate: the head freezes, the continuation is staged ───────

    #[test]
    fn suspend_freezes_the_head_and_stages_the_continuation() {
        let (mut w, treasury, sink) = fixture();
        let mut stack = MetaStack::new();
        let head = w.recorded_turns().len();

        // Not suspended: the gate readout is clear.
        let running = TimeCockpitModel::build(&w, head, &stack);
        assert!(!running.suspended);
        assert!(running.pending.is_empty());

        // SUSPEND, then stage a turn — it queues, the head freezes.
        w.suspend();
        let staged = w.turn(treasury, vec![transfer(treasury, sink, 10)]);
        assert!(w.commit_turn(staged).is_queued());

        let suspended = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert!(suspended.suspended, "the gate readout shows SUSPENDED");
        assert_eq!(
            suspended.pending.len(),
            1,
            "the staged continuation is shown"
        );
        assert_eq!(
            suspended.live_height,
            head as u64 - 2,
            "head frozen (3 turns done, 2 genesis)"
        );

        // RESUME drains: the queue commits, the readout clears.
        let outcomes = w.resume(ResumeMode::Drain);
        assert!(outcomes.iter().all(|o| o.is_committed()));
        let resumed = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert!(!resumed.suspended);
        assert!(resumed.pending.is_empty());
        let _ = &mut stack;
    }

    // ── the METASTACK breadcrumb: BASE → meta¹, top flagged ──────────────────

    #[test]
    fn the_metastack_breadcrumb_climbs_and_descends() {
        let (mut w, _t, _s) = fixture();
        let mut stack = MetaStack::new();

        // No level materialized: the breadcrumb is empty (the live system runs).
        let m0 = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert!(m0.metastack.is_empty());

        // Suspend & push BASE.
        w.suspend();
        stack.push(&w);
        let m1 = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert_eq!(m1.metastack.len(), 1);
        assert_eq!(m1.metastack[0].level, 0);
        assert!(
            m1.metastack[0].is_top,
            "the lone level is the top (currently debugging)"
        );

        // Push meta¹ — DEBUG THE DEBUGGER. The breadcrumb climbs.
        stack.push(&w);
        let m2 = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert_eq!(m2.metastack.len(), 2);
        assert_eq!(m2.metastack[0].level, 0);
        assert_eq!(m2.metastack[1].level, 1);
        assert!(!m2.metastack[0].is_top, "BASE is no longer the top");
        assert!(m2.metastack[1].is_top, "meta¹ is the innermost debugger");

        // Pop descends back to BASE.
        stack.pop();
        let m3 = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert_eq!(m3.metastack.len(), 1);
        assert!(m3.metastack[0].is_top);
    }

    // ── ⑂ FORK THE PAST: branch a divergent VERIFIED future, parent untouched ─

    #[test]
    fn fork_at_branches_the_past_into_a_divergent_verified_future() {
        // The fixture: treasury(1000) → sink, three transfers (100, 200, 50). Steps:
        // [Genesis, Genesis, Turn1, Turn2, Turn3] → head k5. After k3 (Turn1 of 100)
        // the treasury holds 900. We fork the PAST at k3 and drive a DIVERGENT
        // transfer the live line never made (777), building a separate verified
        // future ON the past state — the parent timeline standing untouched.
        let (w, treasury, sink) = fixture();
        let head = w.recorded_turns().len();
        assert_eq!(head, 5);
        let k = 3;

        let branch =
            TimeBranch::fork_and_drive(&w, k, treasury, vec![transfer(treasury, sink, 777)])
                .expect("the past forks and the divergent turn commits");

        // The fork shares the WHOLE [0,k) prefix as the Arc down-set (no re-run).
        assert_eq!(branch.fork_step, k);
        assert_eq!(branch.parent_head, head);
        assert_eq!(
            branch.shared_prefix, k,
            "the whole prefix is the Arc down-set"
        );
        assert_eq!(
            branch.branch_head,
            k + 1,
            "one divergent turn above the fork"
        );

        // The fork LANDED on the parent's recorded root at k (no re-execution drift).
        assert_eq!(
            branch.fork_root,
            w.recorded_turns().root_at(k).unwrap(),
            "fork_at lands on the recorded tooth"
        );

        // The divergent turn root-VERIFIED on the fork, and its root DIFFERS from the
        // parent's next root — a genuine divergent verified future.
        assert!(
            branch.verified,
            "the divergent turn root-verified on the fork"
        );
        assert!(
            branch.diverged,
            "the branch root differs from the parent's next root"
        );
        assert_ne!(
            Some(branch.branch_root),
            branch.parent_next_root,
            "the branch left the parent timeline"
        );

        // The divergent image is built ON THE PAST: treasury = 900 − 777 = 123 (not
        // the live head's 650).
        let tre = branch
            .cells
            .iter()
            .find(|(id, ..)| *id == treasury)
            .expect("the treasury is in the divergent image");
        assert_eq!(
            tre.1,
            900 - 777,
            "the divergent future is built on the past state"
        );

        // THE PARENT STANDS UNTOUCHED — the live head is exactly as before the branch.
        assert!(branch.parent_untouched, "the parent timeline is immutable");
        let live = TimeCockpitModel::build(&w, head, &MetaStack::new());
        let live_tre = live
            .cursor_cells
            .iter()
            .find(|(id, ..)| *id == treasury)
            .unwrap();
        assert_eq!(
            live_tre.1, 650,
            "the live timeline (1000−100−200−50) is untouched by the branch"
        );
        assert_eq!(
            w.recorded_turns().len(),
            head,
            "the live world's history did not grow"
        );
    }

    // ── the liveness badge text reads honestly ───────────────────────────────

    #[test]
    fn the_liveness_badge_reads_live_at_head_and_replayed_in_the_past() {
        let (w, _t, _s) = fixture();
        let stack = MetaStack::new();
        let head = w.recorded_turns().len();
        assert!(TimeCockpitModel::build(&w, head, &stack)
            .liveness_badge()
            .contains("LIVE"));
        assert!(TimeCockpitModel::build(&w, 0, &stack)
            .liveness_badge()
            .contains("REPLAYED"));
    }
}
