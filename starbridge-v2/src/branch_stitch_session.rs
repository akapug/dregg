//! **Branch-and-stitch multiplayer as a reusable primitive** — the distributed-Houyhnhnm
//! synthesis (distributed · reversible · capability-secure · witnessed) lifted out of the
//! transport-gated [`crate::shared_fork::ForkMembraneHost`] into a transport-free,
//! `World`-native API a plain demo can call.
//!
//! Two participants fork ONE shared verified world, diverge on their own independent
//! branches, and stitch back through a SINGLE gated door:
//!
//! * compatible (disjoint-address) edits MERGE — conservation + authority preserved (the
//!   field-granular pushout [`crate::umem_membrane::stitch_projections`]);
//! * a genuine same-address clash is REFUSED fail-closed — both attributed readings live,
//!   never a silent last-writer-wins;
//! * a capability REVOKED on main between branch and settlement cannot ride the stitch —
//!   it is LINEAR-DROPPED while the disjoint state still settles (the operable shadow of
//!   `Metatheory.SettlementSoundness.settlement_soundness` /
//!   `revoke_before_tip_unsettleable`, read at the SETTLEMENT TIP).
//!
//! This is the GUTS of [`crate::shared_fork::ForkMembraneHost::stitch_pair`] (steps 1-6 of
//! its body) re-homed against [`World`]/[`Branch`] instead of the deos-matrix `ForkHandle`/
//! registry — composition only, calling exclusively the already-public surface of
//! [`crate::world`], [`crate::shared_fork`], and [`crate::umem_membrane`]. It does NOT edit
//! those modules; it is purely additive. The settlement gate predicate, the conferred-cap
//! gather, the [`settlement_held_at_tip`] read, and the [`SettledUmemStitch::settles`]
//! decision are all UNCHANGED from the production path — so the slice-1 adapter can express
//! `stitch_pair` as a thin wrapper over this session with no behavioral change.
//!
//! gpui-free, deos-matrix-free, no GPU. `embedded-executor`-gated.

use dregg_cell::CellId;
use dregg_turn::turn::{Turn, TurnReceipt};
use dregg_turn::umem::UKey;

use crate::umem_membrane::{
    settle_umem_stitch, settlement_held_at_tip, stitch_projections, ConferredCap, UmemBranch,
};
use crate::world::{CommitOutcome, World};

/// **A shared verified world participants fork, diverge in, and stitch back** — the
/// operable distributed-Houyhnhnm primitive. Transport-free: no deos-matrix, no wire
/// types, no GPU. The settlement-sound authority gate is [`settle_umem_stitch`], read at
/// the settlement tip ([`settlement_held_at_tip`] over [`Self::base`]).
pub struct BranchStitchSession {
    /// The live main world — the settlement tip every conferred authority is evaluated at.
    base: World,
    /// The cap-bounded cull centre (anti-amplification by omission): exactly the focus's
    /// reach defines the in-view subgraph each branch carries.
    focus: CellId,
    /// The cull depth (hops along capability edges from `focus`).
    max_depth: u8,
}

/// **One participant's divergent branch** — a real independent [`World`] fork plus the
/// shared-ancestor baseline ([`UmemBranch`]) it stitches against. A fork deep-clones the
/// live world (carrying the executor signing key + factories + receipt-chain heads), so a
/// driven turn produces a receipt verifiable under the SAME executor key, and committing on
/// the branch mutates ONLY the branch — divergence stays imaginary until a verdict is
/// applied.
pub struct Branch {
    /// The independent verified fork the participant drives.
    world: World,
    /// The shared-ancestor projection both branches stitch against (minted from `base` at
    /// fork time — the pre-divergence baseline of the state pushout).
    baseline: UmemBranch,
}

/// **The verdict of a stitch** — the field-granular state pushout PLUS the settlement-sound
/// authority gate, surfaced transport-free.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StitchVerdict {
    /// The settled merged-umem root — `Some` iff the state pushout has NO live conflict
    /// (fail-closed: a same-address clash withholds the root until explicitly resolved).
    pub settled_root: Option<[u8; 32]>,
    /// The universal-memory addresses that folded CLEAN relative to the baseline (each
    /// side's disjoint edits, both kept — co-drive, never last-writer-wins).
    pub merged: Vec<UKey>,
    /// Same-address `ValueCollision`s held fail-closed (the stitch does not settle until
    /// each is explicitly resolved). Empty ⟺ a clean merge.
    pub state_conflicts: Vec<UKey>,
    /// Conferred caps HELD AT THE SETTLEMENT TIP — they ride the stitch into main.
    pub admitted_authority: Vec<ConferredCap>,
    /// Conferred caps NOT held at the tip (revoked between branch and settlement) — the
    /// linear DROP. "A cap I have since revoked cannot ride a stitch into my real world."
    pub dropped_authority: Vec<ConferredCap>,
}

impl StitchVerdict {
    /// **Does the stitch settle?** Fail-closed: settles only when the state pushout is
    /// conflict-free. Linear-dropped authority does NOT block settlement (a revoked cap was
    /// simply not conferred) — authority and state are orthogonal, exactly the proven shape.
    pub fn settles(&self) -> bool {
        self.state_conflicts.is_empty()
    }
}

/// The fail-closed paths driving a branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BranchError {
    /// The real executor REJECTED the driven turn (unauthorized effect, non-conservation,
    /// broken receipt chain, …) — the ocap/verification guarantees firing.
    DriveRejected {
        reason: String,
        at_action: Vec<usize>,
    },
    /// The branch world was SUSPENDED, so the turn was staged rather than committed (not a
    /// path the session uses — surfaced fail-closed rather than silently swallowed).
    DriveQueued,
}

impl std::fmt::Display for BranchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BranchError::DriveRejected { reason, .. } => {
                write!(f, "the branch executor refused the driven turn: {reason}")
            }
            BranchError::DriveQueued => {
                write!(
                    f,
                    "the branch world is suspended — the turn was staged, not committed"
                )
            }
        }
    }
}

impl std::error::Error for BranchError {}

impl BranchStitchSession {
    /// Open a session over a live world, culling each branch in view of `focus` to
    /// `max_depth` hops (the anti-amplification cull — a cell outside the focus's reach is
    /// structurally absent from every branch).
    pub fn open(base: World, focus: CellId, max_depth: u8) -> Self {
        BranchStitchSession {
            base,
            focus,
            max_depth,
        }
    }

    /// The live main / settlement tip (read-only).
    pub fn base(&self) -> &World {
        &self.base
    }

    /// **Advance the main tip** — e.g. commit a real verified `RevokeCapability` turn
    /// between branch and settlement (the non-monotone revocation distributed time-travel
    /// turns on). The stitch reads authority HERE, at the tip, not at branch time.
    pub fn base_mut(&mut self) -> &mut World {
        &mut self.base
    }

    /// **Mint a cap-bounded fork for a participant.** Deep-clones the live world into an
    /// independent verified [`World`] (the fork), then records the shared-ancestor
    /// projection ([`UmemBranch::mint`] over the focus cull) as the branch's stitch
    /// baseline. The cull is pinned to `focus`: the participant gets the focus's reach and
    /// nothing beyond it.
    pub fn fork(&self) -> Branch {
        let world = self.base.fork();
        let baseline = UmemBranch::mint(&self.base, self.focus, self.max_depth);
        Branch { world, baseline }
    }

    /// **Stitch two diverged branches under the settlement-sound gate.** The body of
    /// [`crate::shared_fork::ForkMembraneHost::stitch_pair`] (steps 1-6), re-homed against
    /// [`Branch`] instead of the deos-matrix registry:
    ///
    /// 1. the shared-ancestor baseline is `a.baseline` (both branches forked from the same
    ///    tip, so `a.baseline == b.baseline` — the pre-divergence projection);
    /// 2. each driven branch is RE-PROJECTED and folded with [`stitch_projections`] (the
    ///    field-granular STATE pushout — disjoint addresses merge clean, a same-address
    ///    clash surfaces a held conflict);
    /// 3. the authority each branch would confer back = the focus's live caps in the driven
    ///    forks;
    /// 4. authority is read AT THE TIP via [`settlement_held_at_tip`] over [`Self::base`]
    ///    (after any revocation committed between branch and settlement);
    /// 5. [`settle_umem_stitch`] admits held caps and LINEAR-DROPS revoked-before-tip ones;
    /// 6. the verdict surfaces clean folds, held conflicts, and admitted/dropped authority.
    ///
    /// The state pushout and the authority gate are ORTHOGONAL: the disjoint edits fold /
    /// the clash holds REGARDLESS of authority, and a conferred cap rides ONLY if held at
    /// the tip.
    pub fn stitch(&self, a: &Branch, b: &Branch) -> StitchVerdict {
        // (1)+(2) THE STATE PUSHOUT — field-granular, orthogonal to authority.
        let base = &a.baseline;
        let proj_a = UmemBranch::mint(&a.world, base.focus, base.max_depth);
        let proj_b = UmemBranch::mint(&b.world, base.focus, base.max_depth);
        let stitch = stitch_projections(&base.umem, &proj_a.umem, &proj_b.umem);

        // (3) THE CONFERRED AUTHORITY — the focus's held caps in the driven branches (the
        // authority a stitch would confer back into main), deduped across both branches.
        let mut conferred: Vec<ConferredCap> = Vec::new();
        for driven in [&a.world, &b.world] {
            if let Some(cell) = driven.ledger().get(&self.focus) {
                for cap in cell.capabilities.iter() {
                    if cap.permissions != dregg_cell::AuthRequired::Impossible {
                        let cc = ConferredCap {
                            target: cap.target,
                            debit_reach: true,
                        };
                        if !conferred.contains(&cc) {
                            conferred.push(cc);
                        }
                    }
                }
            }
        }

        // (4)+(5) THE SETTLEMENT-SOUND AUTHORITY GATE — authority read at the TIP.
        let settlement_held = settlement_held_at_tip(&self.base, self.focus);
        let settled = settle_umem_stitch(stitch, &conferred, &settlement_held);

        // (6) SURFACE: clean folds (changed vs baseline) + held conflicts + dropped authority.
        let merged: Vec<UKey> = settled
            .stitch
            .merged
            .iter()
            .filter(|(k, v)| base.umem.get(k) != Some(v))
            .map(|(k, _)| k.clone())
            .collect();
        let state_conflicts: Vec<UKey> = settled
            .stitch
            .conflicts
            .iter()
            .map(|c| c.key.clone())
            .collect();
        let settled_root = settled.settled_root();
        StitchVerdict {
            settled_root,
            merged,
            state_conflicts,
            admitted_authority: settled.admitted.clone(),
            dropped_authority: settled.dropped.clone(),
        }
    }
}

impl Branch {
    /// The branch's independent verified world (read-only — for inspecting the diverged
    /// state).
    pub fn world(&self) -> &World {
        &self.world
    }

    /// Build a turn against this branch's chain head (delegates to [`World::turn`]).
    pub fn turn(&self, agent: CellId, effects: Vec<dregg_turn::action::Effect>) -> Turn {
        self.world.turn(agent, effects)
    }

    /// **Drive a real verified turn on this branch.** Commits through the branch's embedded
    /// executor (identical conservation / ocap / program guarantees the live world enforces),
    /// mutating ONLY the branch. Returns the real signed [`TurnReceipt`] on commit; refuses
    /// fail-closed if the executor rejects.
    pub fn drive(&mut self, turn: Turn) -> Result<TurnReceipt, BranchError> {
        match self.world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => Ok(*receipt),
            CommitOutcome::Rejected { reason, at_action } => {
                Err(BranchError::DriveRejected { reason, at_action })
            }
            CommitOutcome::Queued { .. } => Err(BranchError::DriveQueued),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{make_open_cell, revoke_capability, set_field, World};
    use dregg_cell::AuthRequired;

    /// A shared world mirroring the production multiplayer setup: a `room` focus reaching two
    /// distinct principals `ada`/`boris`, a shared `board`, each their own `doc`, plus a
    /// `gift` cap held by the room (the conferrable authority later revoked) and an
    /// `offstage` cell granted to nobody (the confinement foil). Returns
    /// `(world, room, ada, boris, board, doc_ada, doc_boris, gift, offstage)`.
    #[allow(clippy::type_complexity)]
    fn shared_world() -> (
        World,
        CellId,
        CellId,
        CellId,
        CellId,
        CellId,
        CellId,
        CellId,
        CellId,
    ) {
        let mut w = World::new().with_executor_signing_key([0x42u8; 32]);
        let board = w.genesis_cell(0x5D, 0);
        let doc_ada = w.genesis_cell(0xA1, 0);
        let doc_boris = w.genesis_cell(0xB2, 0);
        let gift = w.genesis_cell(0x91, 0);
        let offstage = w.genesis_cell(0xEE, 0);

        let mut ada = make_open_cell(0x0A, 0);
        ada.capabilities.grant(board, AuthRequired::None).unwrap();
        ada.capabilities.grant(doc_ada, AuthRequired::None).unwrap();
        let ada_id = w.genesis_install(ada);

        let mut boris = make_open_cell(0x0B, 0);
        boris.capabilities.grant(board, AuthRequired::None).unwrap();
        boris
            .capabilities
            .grant(doc_boris, AuthRequired::None)
            .unwrap();
        let boris_id = w.genesis_install(boris);

        let mut room = make_open_cell(0x40, 0);
        room.capabilities.grant(ada_id, AuthRequired::None).unwrap();
        room.capabilities
            .grant(boris_id, AuthRequired::None)
            .unwrap();
        room.capabilities.grant(board, AuthRequired::None).unwrap();
        room.capabilities
            .grant(gift, AuthRequired::None)
            .expect("the room holds the gift cap at branch time");
        let room_id = w.genesis_install(room);

        (
            w, room_id, ada_id, boris_id, board, doc_ada, doc_boris, gift, offstage,
        )
    }

    /// BEAT A — disjoint edits MERGE clean; no authority dropped; main untouched.
    #[test]
    fn beat_a_disjoint_edits_merge_clean() {
        let (world, room, ada, boris, board, doc_ada, doc_boris, _gift, offstage) = shared_world();
        let session = BranchStitchSession::open(world, room, 3);

        // The cull is cap-bounded: the offstage cell (granted to nobody) is NOT in view.
        let branch = session.fork();
        assert!(
            !branch.baseline.cells.contains(&offstage),
            "anti-amplification: offstage never rides the cap-bounded cull"
        );

        let mut br_ada = session.fork();
        br_ada
            .drive(br_ada.turn(ada, vec![set_field(doc_ada, 0, [0x11; 32])]))
            .expect("ada drives her own doc");
        // ada also touches her half of the shared board (a disjoint field).
        br_ada
            .drive(br_ada.turn(ada, vec![set_field(board, 0, [0xAA; 32])]))
            .expect("ada drives board.field[0]");

        let mut br_boris = session.fork();
        br_boris
            .drive(br_boris.turn(boris, vec![set_field(doc_boris, 0, [0x22; 32])]))
            .expect("boris drives his own doc");
        br_boris
            .drive(br_boris.turn(boris, vec![set_field(board, 1, [0xBB; 32])]))
            .expect("boris drives board.field[1]");

        let v = session.stitch(&br_ada, &br_boris);
        assert!(
            v.settles(),
            "disjoint edits settle: {:?}",
            v.state_conflicts
        );
        assert!(
            v.settled_root.is_some(),
            "a settled stitch has a binding root"
        );
        assert!(
            v.dropped_authority.is_empty(),
            "no authority dropped (gift still held at tip): {:?}",
            v.dropped_authority
        );
        for key in [
            UKey::Field {
                cell: doc_ada,
                slot: 0,
            },
            UKey::Field {
                cell: doc_boris,
                slot: 0,
            },
            UKey::Field {
                cell: board,
                slot: 0,
            },
            UKey::Field {
                cell: board,
                slot: 1,
            },
        ] {
            assert!(v.merged.contains(&key), "merged names {key:?}");
        }
        // Main is pristine — divergence stayed imaginary.
        assert!(
            session.base().ledger().get(&board).unwrap().state.fields[0] == [0u8; 32],
            "main untouched until a verdict is applied"
        );
    }

    /// BEAT B — same-address clash is REFUSED fail-closed; both readings preserved.
    #[test]
    fn beat_b_same_address_conflict_refused() {
        let (world, room, ada, boris, board, _da, _db, _gift, _off) = shared_world();
        let session = BranchStitchSession::open(world, room, 3);

        let mut br_ada = session.fork();
        br_ada
            .drive(br_ada.turn(ada, vec![set_field(board, 0, [0x11; 32])]))
            .expect("ada writes board.field[0]");
        let mut br_boris = session.fork();
        br_boris
            .drive(br_boris.turn(boris, vec![set_field(board, 0, [0x22; 32])]))
            .expect("boris writes board.field[0]");

        let v = session.stitch(&br_ada, &br_boris);
        assert!(
            !v.settles(),
            "a same-address clash does NOT settle (fail-closed)"
        );
        assert!(
            v.settled_root.is_none(),
            "no settled root while a conflict is live"
        );
        assert_eq!(
            v.state_conflicts,
            vec![UKey::Field {
                cell: board,
                slot: 0
            }],
            "the conflict names the EXACT diverged address"
        );
    }

    /// BEAT C — a `gift` cap revoked on main between fork and settlement is LINEAR-DROPPED
    /// while the disjoint state still settles. Non-vacuous BOTH ways.
    #[test]
    fn beat_c_revoked_cap_dropped_settlement_sound() {
        let (world, room, ada, boris, board, _da, _db, gift, _off) = shared_world();
        let mut session = BranchStitchSession::open(world, room, 3);

        // Both branches make DISJOINT board edits (the state settles, orthogonal to authority).
        let mut br_ada = session.fork();
        br_ada
            .drive(br_ada.turn(ada, vec![set_field(board, 0, [0xAA; 32])]))
            .expect("ada drives board.field[0]");
        let mut br_boris = session.fork();
        br_boris
            .drive(br_boris.turn(boris, vec![set_field(board, 1, [0xBB; 32])]))
            .expect("boris drives board.field[1]");

        // BEFORE the revoke: gift is held at the tip → it RIDES (nothing authority-dropped).
        let before = session.stitch(&br_ada, &br_boris);
        assert!(
            !before.dropped_authority.iter().any(|c| c.target == gift),
            "before the revoke gift is held at the tip — nothing dropped: {:?}",
            before.dropped_authority
        );
        assert!(
            before.settles(),
            "the disjoint state settles before the revoke"
        );
        assert!(
            before.admitted_authority.iter().any(|c| c.target == gift),
            "gift is admitted before the revoke (the gate is non-vacuous)"
        );

        // THE REVOCATION (non-monotone, on MAIN / the settlement tip): the room revokes its
        // own gift cap with a real verified turn.
        let slot = session
            .base()
            .ledger()
            .get(&room)
            .unwrap()
            .capabilities
            .iter()
            .find(|c| c.target == gift)
            .map(|c| c.slot)
            .expect("the room's gift cap slot");
        let revoke_turn = session
            .base()
            .turn(room, vec![revoke_capability(room, slot)]);
        assert!(
            session.base_mut().commit_turn(revoke_turn).is_committed(),
            "the room revokes gift on main with a real verified turn"
        );

        // AFTER the revoke: the SAME stitch drops gift (settlement-sound) while state settles.
        let after = session.stitch(&br_ada, &br_boris);
        assert!(
            after.dropped_authority.iter().any(|c| c.target == gift),
            "after the revoke gift is LINEAR-DROPPED (revoke_before_tip_unsettleable): {:?}",
            after.dropped_authority
        );
        assert!(
            !after.admitted_authority.iter().any(|c| c.target == gift),
            "the revoked gift is no longer admitted"
        );
        assert!(
            after.settles(),
            "the disjoint state pushout still settles — authority drop is orthogonal"
        );
        assert!(
            after.settled_root.is_some(),
            "the state stitch is still binding (pushout-correct)"
        );
        // The merged board edits survive the drop.
        assert!(
            after.merged.contains(&UKey::Field {
                cell: board,
                slot: 0
            }) && after.merged.contains(&UKey::Field {
                cell: board,
                slot: 1
            }),
            "the disjoint board edits still fold clean"
        );
        // Non-vacuity: the drop is the revocation, not a blanket refusal.
        assert_ne!(
            before.dropped_authority, after.dropped_authority,
            "the drop appeared only AFTER the revoke (non-vacuous both ways)"
        );
    }
}
