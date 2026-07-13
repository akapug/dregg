//! # `bloodgate` — "The Bloodgate Trial": a STAKES-FORWARD universe (you can LOSE)
//!
//! Every other universe in this crate proves a *rule-as-tooth* but has **no downside
//! risk**: a killing blow is REFUSED by the `FieldGte(hp, 1)` floor
//! ([`crate::dice_combat::reverify_draw`]'s `a_lethal_dice_blow_is_refused_by_the_hp_floor`),
//! so HP-zero is impossible and a run cannot be lost — you retry until you win. The
//! Bloodgate Trial is the fix the fun-plan (Track A #1-2) names: **real loss + forking
//! dilemmas**, every fix riding a tooth the executor already proves.
//!
//! Three stakes mechanics, each an executor-enforced [`StateConstraint`], all additive:
//!
//! ## 1. REAL LOSS — a lethal position routes to a committed DEFEAT passage
//!
//! The Warden hits back. Each exchange (`bloodgate/trade`) costs the player HP AND the
//! Warden HP; a survivable trade is admitted by the compiler-lifted `FieldGte(hp, 1)`
//! floor, but a trade you could not survive (`hp < 21`) is REFUSED — and, crucially,
//! so is felling the not-yet-beaten Warden (`FieldLte(warden_hp, 0)`). A player who
//! traded recklessly (skipping the heal) reaches a state where **every move except
//! defeat is refused by the kernel**: the only committing turn is `[Fall to the
//! Warden's glaive]`, gated `FieldLte(hp, 20)`, which sets a [`WriteOnce`] `downed`
//! flag and navigates to the terminal `downed` passage (`-> END`). So a run can be
//! genuinely LOST — HP-low ends it in a real committed DEFEAT, not a refused retry.
//! The loss is FORCED by the executor (see [`bloodgate_tests::the_loss_is_forced_by_the_kernel`]),
//! and both a LOST run and a WON run re-verify by replay ([`spween_dregg::verify_by_replay`]).
//!
//! ## 2. A RISK-IT GAMBLE — a provably-fair d20-vs-DC that gates a shortcut
//!
//! `[Force the warded sally-door]` skips the whole fight — IF a real d20 skill check
//! passes. The check is the [`crate::skills`] shape: a `dregg-dice` d20 + the
//! character's committed `stat`, bound into the real [`TurnReceipt`] via an
//! `EmitEvent`, recorded as `check_total`. The door's case carries
//! [`StateConstraint::FieldLteField`]`{ dc, check_total }` — `dc <= total` ⟺ the check
//! passed. Pass → the door commits and routes past the fight; fail → the door is a real
//! [`WorldError::Refused`] and the player is left to the fight (the cost). A forged
//! pass (rewriting the bound roll) is caught on replay by [`reverify_risk`].
//!
//! ## 3. AN OPPORTUNITY COST — a shared `WriteOnce` slot: the crown OR the key
//!
//! Past the Warden, a reliquary chamber holds a jeweled CROWN and an iron KEY, and your
//! bloodied `hands` carry ONE: both claims write the SAME `hands` slot (crown → 1,
//! key → 2) under a [`WriteOnce`] tooth, so taking one REFUSES the other. The hoard-
//! stair is gated `FieldGte(hands, 2)` — it opens for the key, not the crown. So the
//! choice is a real tradeoff the kernel enforces: the provable flex (crown) or the
//! hoard (key), never both.
//!
//! ## Honest scope
//!
//! - The combat is FIXED-damage (deterministic), so a WON/LOST run reproduces exactly
//!   on replay; the win/loss is decided by the player's CHOICES (heal-and-survive vs
//!   over-trade-and-fall), not hidden state. Wiring the [`crate::dice_combat`] *rolled*
//!   damage into the same fall-routing (a random blow that downs you) is a named
//!   follow-up — the routing tooth here is damage-source-agnostic.
//! - The risk check's integrity is the SAME O(N) replay model as [`crate::skills`]: the
//!   on-chain door gate trusts the recorded `check_total`; [`reverify_risk`] catches a
//!   forged roll on replay. A succinct proof is the separate light-client workstream.
//! - What a fuller stakes design adds (named, not built here): run-ending consequences
//!   carried into a persistent character (hardcore death — see
//!   `dreggnet_offerings::character`), meta-progression on death, a daily-procgen
//!   roguelite flagship, and a no-cheat leaderboard over survived-depth / no-death streak.

use std::sync::Arc;

use dregg_app_framework::{
    CellId, Effect, Event, FieldElement, StateConstraint, TurnReceipt, field_from_u64, symbol,
};
use dregg_dice::source::Deterministic;
use dregg_dice::{
    DrawError, DrawStream, RandomnessEvidence, RandomnessRequest, RandomnessSource, VerifyError,
};
use spween::Scene;
use spween_dregg::{
    CompiledStory, WorldCell, WorldError, choice_method, compile_scene, field_to_u64, parse,
};

use crate::{add_case, augment_case, keep_slot};

/// The stakes-forward dungeon — "The Bloodgate Trial" — in the spween DSL. The Warden
/// hits BACK (each trade costs the player HP), so the fight is a resource race a
/// reckless line LOSES; a warded sally-door offers a risk-it bypass; and the reliquary
/// chamber past the Warden forces the crown-or-key opportunity cost.
pub const BLOODGATE: &str = r#"---
id: bloodgate-trial
title: The Bloodgate Trial
weight: 1
---

=== bloodgate

~ hp = 50
~ warden_hp = 60
~ draughts_held = 1
~ dc = 15
~ stat = 3
~ check_total = 0

The Bloodgate Warden bars the trial with a notched glaive. There is no retreat from the
Bloodgate — only through, or under it. Every exchange draws blood from BOTH of you, and
the Warden does not tire. You carry one draught of iron-wine, and no more.

* [Trade a measured blow] { hp >= 16 }
  ~ hp -= 15
  ~ warden_hp -= 15
  -> bloodgate

* [Trade a reckless all-out blow] { hp >= 31 }
  ~ hp -= 30
  ~ warden_hp -= 15
  -> bloodgate

* [Drink your one draught of iron-wine]
  ~ draughts_drunk += 1
  ~ hp += 25
  -> bloodgate

* [Land the finishing blow on the reeling Warden] { warden_hp <= 0 }
  -> reliquary

* [Force the warded sally-door and slip past the fight]
  -> reliquary

* [Fall to the Warden's glaive] { hp <= 20 }
  ~ downed = 1
  -> downed

=== downed

The glaive slips your guard and you fall at the Bloodgate. The trial is over — no crown,
no key, no hoard. Your run ends here, in the dark, and cannot be retried.

* [The Bloodgate closes over you]
  -> END

=== reliquary

Past the Warden, a reliquary chamber: a jeweled CROWN rests on a plinth, an iron KEY
hangs on a hook. Your bloodied hands can carry only ONE.

* [Take the jeweled crown — a provable flex]
  ~ hands = 1
  -> reliquary

* [Take the iron key — it alone opens the hoard-stair]
  ~ hands = 2
  -> reliquary

* [Descend the hoard-stair] { hands >= 2 }
  ~ gold += 1000
  -> END

* [Leave the trial with what you carry]
  -> END
"#;

// ── Room / choice coordinates (the driver + verifier speak in these) ──────────────

/// The Bloodgate combat room (HP race, the risk-it door, the fall-to-defeat).
pub const ROOM_BLOODGATE: &str = "bloodgate";
/// The terminal DEFEAT passage — a real committed loss (`downed = 1`, then `-> END`).
pub const ROOM_DOWNED: &str = "downed";
/// The reliquary chamber past the Warden (the crown-or-key opportunity cost).
pub const ROOM_RELIQUARY: &str = "reliquary";

/// `bloodgate`: a MEASURED blow — costs 15 HP, deals 15 to the Warden; gated `{hp>=16}`
/// so a blow you could not survive is refused (lifts to `FieldGte(hp, 1)`).
pub const BG_MEASURED: usize = 0;
/// `bloodgate`: a RECKLESS all-out blow — costs 30 HP for the SAME 15 to the Warden (a
/// trap: it burns your HP for no extra progress); gated `{hp>=31}` (lifts to
/// `FieldGte(hp, 1)`). A reckless opener strands you into a forced defeat.
pub const BG_RECKLESS: usize = 1;
/// `bloodgate`: drink the one draught (+25 HP) — bounded by the `FieldLteField` budget.
pub const BG_DRINK: usize = 2;
/// `bloodgate`: land the finishing blow — gated `FieldLte(warden_hp, 0)` (Warden felled).
pub const BG_FINISH: usize = 3;
/// `bloodgate`: force the warded sally-door — the RISK-IT shortcut, gated
/// `FieldLteField(dc <= check_total)` (a passed d20 check).
pub const BG_FORCE_DOOR: usize = 4;
/// `bloodgate`: fall to the Warden — the DEFEAT move, gated `FieldLte(hp, 20)` (you can
/// only fall once too hurt to fight on); sets `WriteOnce` `downed = 1`, routes to `-> END`.
pub const BG_FALL: usize = 5;

/// `downed`: the sole terminal move — the defeat room's only exit is `-> END`.
pub const BG_DOWNED_END: usize = 0;

/// `reliquary`: take the crown (`hands = 1`) — a `WriteOnce` claim; refuses the key after.
pub const BG_TAKE_CROWN: usize = 0;
/// `reliquary`: take the key (`hands = 2`) — a `WriteOnce` claim; refuses the crown after.
pub const BG_TAKE_KEY: usize = 1;
/// `reliquary`: descend the hoard-stair — gated `FieldGte(hands, 2)` (needs the KEY).
pub const BG_DESCEND: usize = 2;
/// `reliquary`: leave with what you carry (ungated, ends the run).
pub const BG_LEAVE: usize = 3;

/// Parse the Bloodgate Trial scene.
pub fn bloodgate_scene() -> Scene {
    parse(BLOODGATE, "bloodgate-trial.scene").expect("the bloodgate scene parses")
}

/// **Compile the Bloodgate AND augment its program with the stakes teeth.** The HP floor
/// (`FieldGte(hp, 1)`), the finish gate (`FieldLte(warden_hp, 0)`), the fall gate
/// (`FieldLte(hp, 20)`) and the hoard-stair gate (`FieldGte(hands, 2)`) are all
/// compiler-emitted from the scene conditions; this adds the cross-slot / WriteOnce
/// shapes the v0 compiler cannot express:
///
/// - `WriteOnce { downed }` on the fall move — a run is downed ONCE and it is final.
/// - `WriteOnce { hands }` on both claim moves — the crown OR the key, never both.
/// - `FieldLteField { drunk <= held }` on the drink — the one held draught bounds heals.
/// - `FieldLteField { dc <= check_total }` on the sally-door — the risk-it pass gate.
/// - a bare case for [`RISK_CHECK_METHOD`] — the d20 check turn writes `check_total`.
pub fn bloodgate_compiled() -> CompiledStory {
    let mut story = compile_scene(&bloodgate_scene()).expect("the bloodgate compiles");

    let downed = keep_slot(&story, "downed");
    let hands = keep_slot(&story, "hands");
    let drunk = keep_slot(&story, "draughts_drunk");
    let held = keep_slot(&story, "draughts_held");
    let dc = keep_slot(&story, "dc");
    let total = keep_slot(&story, "check_total");

    // REAL LOSS: the fall move is the only path out of a lethal position, and being
    // downed is WriteOnce — a run cannot be un-downed or downed twice.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BLOODGATE, BG_FALL),
        vec![StateConstraint::WriteOnce { index: downed }],
    );

    // OPPORTUNITY COST: both claims write the SAME `hands` slot under WriteOnce, so
    // taking the crown (0→1) refuses the key (1→2) and vice-versa.
    let write_once_hands = || vec![StateConstraint::WriteOnce { index: hands }];
    augment_case(
        &mut story.program,
        &choice_method(ROOM_RELIQUARY, BG_TAKE_CROWN),
        write_once_hands(),
    );
    augment_case(
        &mut story.program,
        &choice_method(ROOM_RELIQUARY, BG_TAKE_KEY),
        write_once_hands(),
    );

    // The heal is bounded by the one held draught (`drunk <= held`): a second drink
    // over-spends (1→2 > 1) and is refused.
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BLOODGATE, BG_DRINK),
        vec![StateConstraint::FieldLteField {
            left_index: drunk,
            right_index: held,
        }],
    );

    // THE RISK-IT GATE: the sally-door opens IFF `dc <= check_total` (a passed d20 check).
    augment_case(
        &mut story.program,
        &choice_method(ROOM_BLOODGATE, BG_FORCE_DOOR),
        vec![StateConstraint::FieldLteField {
            left_index: dc,
            right_index: total,
        }],
    );

    // The d20-check turn (a raw turn that records `check_total`) needs an admitting case
    // (a `Cases` program is default-deny). Its integrity is the recorded EmitEvent +
    // `reverify_risk` on replay, exactly the skills-module model.
    add_case(&mut story.program, RISK_CHECK_METHOD, Vec::new());

    story
}

/// Deploy the augmented Bloodgate Trial as a real world-cell (the stakes teeth installed
/// as executor predicates). Deterministic in `seed` (re-deploy reproduces identity + hashes).
pub fn deploy_bloodgate(seed: u8) -> WorldCell {
    WorldCell::deploy_compiled(Arc::new(bloodgate_compiled()), seed).expect("the bloodgate deploys")
}

// ═══════════════════════════════════════════════════════════════════════════════════
// THE RISK-IT ROLL — a provably-fair d20 skill check bound into the real turn
// ═══════════════════════════════════════════════════════════════════════════════════
//
// Mirrors `crate::skills` (a d20 + committed `stat`, bound via `EmitEvent`, reproduced
// on replay). Here the check records `check_total` on the Bloodgate cell so the sally-
// door's `FieldLteField(dc <= check_total)` gate can read the outcome.

/// The die a Bloodgate risk-it check rolls.
pub const RISK_DIE_SIDES: u64 = 20;
/// The topic the risk-it draw's binding rides on the real receipt.
pub const RISK_TOPIC: &str = "dungeon-on-dregg/bloodgate-risk-commitment-v1";
/// The `dregg-dice` `event_kind` domain-separating Bloodgate risk-it draws.
pub const RISK_EVENT_KIND: &str = "bloodgate/risk";
/// The method the risk-it check turn presents (writes `check_total`, binds the d20).
pub const RISK_CHECK_METHOD: &str = "bloodgate/risk_check";
/// The committed game identity folded into every risk request's `game_binding`.
const GAME_BINDING: &[u8] = b"dungeon-on-dregg/bloodgate-trial/risk/v1";

/// A resolved risk-it check: the request + evidence the d20 was derived from, the roll,
/// the committed `stat`, and the total (`stat + roll`, the recorded outcome).
#[derive(Clone, Debug)]
pub struct RiskDraw {
    /// The randomness request binding the check's context (its `EventId` seeds the d20).
    pub request: RandomnessRequest,
    /// The recorded evidence a verifier re-derives the seed from.
    pub evidence: RandomnessEvidence,
    /// The d20 face rolled (`1..=20`).
    pub roll: u64,
    /// The character's committed ability stat (folded into the request's pre-state root).
    pub stat: u64,
    /// The check total `stat + roll` — the recorded OUTCOME the door gate reads.
    pub total: u64,
}

/// A committed risk-it check: the real receipt plus the [`RiskDraw`] and the committed total.
#[derive(Clone, Debug)]
pub struct RiskReceipt {
    /// The real committed turn receipt (binds the draw in `effects_hash`/`turn_hash`).
    pub receipt: TurnReceipt,
    /// The draw the check was resolved from.
    pub draw: RiskDraw,
    /// The committed `check_total` after the check.
    pub total_after: u64,
}

/// The fields bound into a risk receipt's `EmitEvent`, read back off the receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundRisk {
    /// The draw's `EventId` bytes.
    pub event_id: FieldElement,
    /// The draw-transcript commitment.
    pub transcript: FieldElement,
    /// The d20 face bound into the turn.
    pub roll: u64,
    /// The total (`stat + roll`) bound into the turn.
    pub total: u64,
}

/// Why re-verifying a bound risk-it check failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RiskReplayError {
    /// The receipt bound no risk event under [`RISK_TOPIC`].
    NoBinding,
    /// The recorded evidence did not verify against the recorded request.
    Evidence(VerifyError),
    /// Re-deriving the draw from the verified seed failed.
    Draw(DrawError),
    /// The bound `EventId` is not the recorded request's (the context was retconned).
    EventIdMismatch,
    /// The bound transcript commitment is not the recorded evidence's.
    TranscriptMismatch,
    /// The bound roll is not the one re-derived from the seed — a FORGED roll.
    RollMismatch {
        /// The roll bound into the receipt.
        bound: u64,
        /// The roll re-derived from the recorded request + evidence.
        rederived: u64,
    },
    /// The bound total is not `stat + roll` — a forged outcome (a faked passed check).
    TotalMismatch {
        /// The total bound into the receipt.
        bound: u64,
        /// The total `stat + re-derived roll` fixes.
        expected: u64,
    },
}

impl std::fmt::Display for RiskReplayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RiskReplayError::NoBinding => write!(f, "the receipt bound no risk-it check"),
            RiskReplayError::Evidence(e) => write!(f, "the risk evidence did not verify: {e:?}"),
            RiskReplayError::Draw(e) => write!(f, "re-deriving the draw failed: {e:?}"),
            RiskReplayError::EventIdMismatch => {
                write!(f, "the bound EventId is not the recorded request's")
            }
            RiskReplayError::TranscriptMismatch => {
                write!(f, "the bound transcript is not the recorded evidence's")
            }
            RiskReplayError::RollMismatch { bound, rederived } => write!(
                f,
                "forged roll: the receipt binds {bound} but the seed re-derives {rederived}"
            ),
            RiskReplayError::TotalMismatch { bound, expected } => write!(
                f,
                "forged outcome: the receipt binds total {bound} but stat + roll fixes {expected}"
            ),
        }
    }
}

impl std::error::Error for RiskReplayError {}

/// Whether a risk-it check passed against a DC (a pure decision over the recorded outcome).
pub fn risk_succeeds(total: u64, dc: u64) -> bool {
    total >= dc
}

/// A deterministic (reproducible) draw context derived from the request's `EventId`.
fn risk_context(req: &RandomnessRequest) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/bloodgate/context/v1");
    h.update(req.event_id().as_bytes());
    *h.finalize().as_bytes()
}

/// The pre-state root a risk draw binds: the character's committed ability stat.
fn stat_root(stat: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/bloodgate/pre-state/v1");
    h.update(&stat.to_le_bytes());
    *h.finalize().as_bytes()
}

/// A commitment to the finalized check action (the method + die).
fn action_hash(sides: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dungeon-on-dregg/bloodgate/action/v1");
    h.update(RISK_CHECK_METHOD.as_bytes());
    h.update(&sides.to_le_bytes());
    *h.finalize().as_bytes()
}

/// Build the [`RandomnessRequest`] for a risk-it check at sequence `seq` over `stat`.
pub fn risk_request(stat: u64, seq: u64) -> RandomnessRequest {
    RandomnessRequest {
        game_binding: GAME_BINDING.to_vec(),
        seq,
        pre_state_root: stat_root(stat),
        action_hash: action_hash(RISK_DIE_SIDES),
        event_kind: RISK_EVENT_KIND.to_string(),
        draw_count: 1,
    }
}

/// **Roll a risk-it check** — derive the request from the cell's committed `stat`,
/// produce `dregg-dice` evidence + a verified seed, and read the d20 off the real
/// [`DrawStream`]. No world mutation yet — [`resolve_risk`] commits it.
pub fn roll_risk(world: &WorldCell, seq: u64) -> RiskDraw {
    let stat = world.read_var("stat");
    let request = risk_request(stat, seq);
    let source = Deterministic {
        context: risk_context(&request),
    };
    let evidence = source.evidence(&request);
    let seed =
        Deterministic::seed(&request, &evidence).expect("freshly-produced risk evidence verifies");
    let roll = DrawStream::new(seed, request.draw_count)
        .draw_die(0, RISK_DIE_SIDES)
        .expect("draw_count = 1, so index 0 is in range");
    RiskDraw {
        request,
        evidence,
        roll,
        stat,
        total: stat + roll,
    }
}

/// The `EmitEvent` binding a risk draw into the turn: `[event_id ‖ transcript ‖ roll ‖
/// total]` under [`RISK_TOPIC`].
fn risk_event_effect(cell: CellId, draw: &RiskDraw) -> Effect {
    let data = vec![
        *draw.request.event_id().as_bytes(),
        draw.evidence.draw_transcript_commitment,
        field_from_u64(draw.roll),
        field_from_u64(draw.total),
    ];
    Effect::EmitEvent {
        cell,
        event: Event::new(symbol(RISK_TOPIC), data),
    }
}

/// **Commit a rolled risk-it check as ONE real cap-bounded turn.** Writes `check_total =
/// stat + roll` (the outcome the door gate reads) and binds the d20 into the SAME
/// receipt via an `EmitEvent`.
pub fn resolve_risk(world: &WorldCell, draw: &RiskDraw) -> Result<RiskReceipt, WorldError> {
    let cell = world.cell_id();
    let total_slot = *world
        .story()
        .var_slots
        .get("check_total")
        .expect("the bloodgate compiles a `check_total` slot");
    let effects = vec![
        Effect::SetField {
            cell,
            index: total_slot,
            value: field_from_u64(draw.total),
        },
        risk_event_effect(cell, draw),
    ];
    let receipt = world.apply_raw(RISK_CHECK_METHOD, effects)?;
    Ok(RiskReceipt {
        receipt,
        draw: draw.clone(),
        total_after: world.read_var("check_total"),
    })
}

/// **Roll AND commit a risk-it check** in one call: [`roll_risk`] then [`resolve_risk`].
pub fn make_risk(world: &WorldCell, seq: u64) -> Result<RiskReceipt, WorldError> {
    let draw = roll_risk(world, seq);
    resolve_risk(world, &draw)
}

/// Read the bound risk draw off a committed receipt — the exact path a replayer uses.
pub fn bound_risk(receipt: &TurnReceipt) -> Option<BoundRisk> {
    let topic = symbol(RISK_TOPIC);
    let e = receipt.emitted_events.iter().find(|e| e.topic == topic)?;
    if e.data.len() < 4 {
        return None;
    }
    Some(BoundRisk {
        event_id: e.data[0],
        transcript: e.data[1],
        roll: field_to_u64(&e.data[2]),
        total: field_to_u64(&e.data[3]),
    })
}

/// **The replay tooth — re-derive the d20 and catch a forgery.** Re-derive the seed from
/// the RECORDED `(request, evidence)`, re-derive the roll, recompute `total = stat +
/// roll`, and confirm the roll AND total BOUND into the receipt match. Returns the
/// re-derived roll on success. A rewritten roll or total — a faked passed check — is a
/// [`RiskReplayError`].
pub fn reverify_risk(committed: &RiskReceipt) -> Result<u64, RiskReplayError> {
    let seed = Deterministic::seed(&committed.draw.request, &committed.draw.evidence)
        .map_err(RiskReplayError::Evidence)?;
    let rederived = DrawStream::new(seed, committed.draw.request.draw_count)
        .draw_die(0, RISK_DIE_SIDES)
        .map_err(RiskReplayError::Draw)?;
    let bound = bound_risk(&committed.receipt).ok_or(RiskReplayError::NoBinding)?;
    if bound.event_id != *committed.draw.request.event_id().as_bytes() {
        return Err(RiskReplayError::EventIdMismatch);
    }
    if bound.transcript != committed.draw.evidence.draw_transcript_commitment {
        return Err(RiskReplayError::TranscriptMismatch);
    }
    if bound.roll != rederived {
        return Err(RiskReplayError::RollMismatch {
            bound: bound.roll,
            rederived,
        });
    }
    let expected_total = committed.draw.stat + rederived;
    if bound.total != expected_total {
        return Err(RiskReplayError::TotalMismatch {
            bound: bound.total,
            expected: expected_total,
        });
    }
    Ok(rederived)
}

#[cfg(test)]
mod bloodgate_tests {
    //! The three stakes mechanics, each DRIVEN on the real `WorldCell`: a run can be
    //! genuinely LOST into a committed defeat passage; a provably-fair risk roll gates a
    //! shortcut (pass AND fail); an opportunity-cost WriteOnce refuses taking both.
    use super::*;
    use crate::choice_at;
    use spween_dregg::{
        Driver, StepPos, Value, VerifyBreak, verify, verify_by_replay, verify_chain_linkage,
    };

    /// Every stakes rule is a REAL kernel predicate: introspect the installed program and
    /// confirm the HP floor, the finish gate, the fall gate + WriteOnce(downed), the
    /// crown/key WriteOnce(hands), the hoard gate, the heal budget, and the risk-door gate.
    #[test]
    fn stakes_teeth_are_real_kernel_predicates() {
        let story = bloodgate_compiled();
        let hp = keep_slot(&story, "hp");
        let warden = keep_slot(&story, "warden_hp");
        let downed = keep_slot(&story, "downed");
        let hands = keep_slot(&story, "hands");
        let drunk = keep_slot(&story, "draughts_drunk");
        let held = keep_slot(&story, "draughts_held");
        let dc = keep_slot(&story, "dc");
        let total = keep_slot(&story, "check_total");

        for (m, label) in [(BG_MEASURED, "measured"), (BG_RECKLESS, "reckless")] {
            let trade = crate::case_constraints(&story, &choice_method(ROOM_BLOODGATE, m));
            assert!(
                trade.iter().any(|c| matches!(
                    c,
                    StateConstraint::FieldGte { index, value }
                        if *index == hp && *value == field_from_u64(1)
                )),
                "the {label} blow lifts to FieldGte(hp, 1) — a blow you could not survive is refused; got {trade:?}"
            );
        }

        let finish = crate::case_constraints(&story, &choice_method(ROOM_BLOODGATE, BG_FINISH));
        assert!(
            finish.iter().any(|c| matches!(
                c,
                StateConstraint::FieldLte { index, value }
                    if *index == warden && *value == field_from_u64(0)
            )),
            "finish is gated FieldLte(warden_hp, 0); got {finish:?}"
        );

        let fall = crate::case_constraints(&story, &choice_method(ROOM_BLOODGATE, BG_FALL));
        assert!(
            fall.iter().any(|c| matches!(
                c, StateConstraint::FieldLte { index, value } if *index == hp && *value == field_from_u64(20)
            )),
            "fall is gated FieldLte(hp, 20); got {fall:?}"
        );
        assert!(
            fall.iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == downed)),
            "fall sets WriteOnce(downed) — a run is downed once and it is final; got {fall:?}"
        );

        for m in [
            choice_method(ROOM_RELIQUARY, BG_TAKE_CROWN),
            choice_method(ROOM_RELIQUARY, BG_TAKE_KEY),
        ] {
            let claim = crate::case_constraints(&story, &m);
            assert!(
                claim
                    .iter()
                    .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == hands)),
                "claim `{m}` is WriteOnce(hands) — the crown OR the key; got {claim:?}"
            );
        }

        let descend = crate::case_constraints(&story, &choice_method(ROOM_RELIQUARY, BG_DESCEND));
        assert!(
            descend.iter().any(|c| matches!(
                c, StateConstraint::FieldGte { index, value } if *index == hands && *value == field_from_u64(2)
            )),
            "hoard-stair is gated FieldGte(hands, 2) — needs the KEY; got {descend:?}"
        );

        let drink = crate::case_constraints(&story, &choice_method(ROOM_BLOODGATE, BG_DRINK));
        assert!(
            drink.iter().any(|c| matches!(
                c, StateConstraint::FieldLteField { left_index, right_index }
                    if *left_index == drunk && *right_index == held
            )),
            "drink is FieldLteField(drunk <= held); got {drink:?}"
        );

        let door = crate::case_constraints(&story, &choice_method(ROOM_BLOODGATE, BG_FORCE_DOOR));
        assert!(
            door.iter().any(|c| matches!(
                c, StateConstraint::FieldLteField { left_index, right_index }
                    if *left_index == dc && *right_index == total
            )),
            "sally-door is gated FieldLteField(dc <= check_total); got {door:?}"
        );
    }

    /// REAL LOSS — DRIVEN. A reckless line strands the player: an all-out opener burns HP
    /// for no extra progress, the one draught cannot cover the deficit, and the player is
    /// left below the fight threshold with the Warden still standing — the run FALLS into
    /// the terminal `downed` DEFEAT room (a real committed defeat: `downed = 1`, the scene
    /// ENDS). The lost run re-verifies by replay — a stranger can prove the run was lost.
    #[test]
    fn a_run_can_be_genuinely_lost_into_a_defeat_passage() {
        let s = bloodgate_scene();
        let mut driver = Driver::start(deploy_bloodgate(60), &s).expect("start the trial");

        driver
            .advance(BG_RECKLESS)
            .expect("a reckless opener (hp 50→20, warden 60→45)");
        driver
            .advance(BG_MEASURED)
            .expect("a measured blow (hp 20→5, warden 45→30)");
        driver
            .advance(BG_DRINK)
            .expect("drink the one draught (hp 5→30)");
        driver
            .advance(BG_MEASURED)
            .expect("a measured blow (hp 30→15, warden 30→15)");
        // hp 15: too hurt to trade (< 16), the Warden still stands (15 > 0), the draught is
        // spent — the ONLY committing move is the fall (see the forced-loss test).
        assert_eq!(driver.world().read_var("hp"), 15);
        assert_eq!(driver.world().read_var("warden_hp"), 15);

        driver
            .advance(BG_FALL)
            .expect("fall to the Warden — a real committed defeat");
        assert_eq!(
            driver.current_passage().as_deref(),
            Some(ROOM_DOWNED),
            "in the defeat room"
        );
        assert_eq!(
            driver.world().read_var("downed"),
            1,
            "the downed flag is set"
        );
        driver
            .advance(BG_DOWNED_END)
            .expect("the Bloodgate closes over you → END");
        assert!(
            driver.is_ended(),
            "the run is OVER — lost into the defeat passage"
        );
        assert_eq!(
            driver.world().read_var("gold"),
            0,
            "no hoard — the run was lost"
        );

        // A LOST run is a real, replay-verifiable record.
        let play = driver.playthrough();
        assert_eq!(
            play.receipts().len(),
            7,
            "genesis + 4 combat moves + the fall + the end"
        );
        verify_chain_linkage(&play).expect("the lost-run receipt chain links");
        verify(deploy_bloodgate(60), &s, &play)
            .expect("the LOST run re-verifies (verify + replay)");
        verify_by_replay(deploy_bloodgate(60), &s, &play)
            .expect("the LOST run passes verify_by_replay");
    }

    /// THE LOSS IS FORCED BY THE KERNEL (non-vacuous). From an exhausted position — hurt
    /// below the fight threshold, the Warden still standing, the one draught already spent
    /// — the executor REFUSES every move: a measured blow (`hp < 16`), a reckless blow
    /// (`hp < 31`), the finishing blow (`warden_hp > 0`), and a second drink (over the
    /// `drunk <= held` budget). The ONLY committing move is the fall into defeat: the
    /// player is checkmated into a loss by the real teeth, not by choice.
    #[test]
    fn the_loss_is_forced_by_the_kernel() {
        let s = bloodgate_scene();
        let mut world = deploy_bloodgate(61);
        // Seed the exhausted position directly at the executor (the Driver reaches it by
        // play; a direct deploy seeds it, exactly as the Keep tests seed hp=50).
        world.seed_var("hp", Value::Int(15));
        world.seed_var("warden_hp", Value::Int(15));
        world.seed_var("draughts_held", Value::Int(1));
        world.seed_var("draughts_drunk", Value::Int(1)); // the draught is spent.

        for (ci, why) in [
            (
                BG_MEASURED,
                "a measured blow (hp 15 < 16 ⇒ would drop below 1)",
            ),
            (BG_RECKLESS, "a reckless blow (hp 15 < 31)"),
            (BG_FINISH, "the finishing blow (warden_hp 15 > 0)"),
            (BG_DRINK, "a second drink (drunk 1→2 > held 1)"),
        ] {
            let ch = choice_at(&s, ROOM_BLOODGATE, ci);
            let refused = world.apply_choice(ROOM_BLOODGATE, ci, &ch);
            assert!(
                matches!(refused, Err(WorldError::Refused(_))),
                "{why} is refused by the kernel, got {refused:?}"
            );
        }
        assert_eq!(
            world.read_var("hp"),
            15,
            "anti-ghost: HP unchanged by the refusals"
        );

        // The ONLY committing move is the fall into defeat — the loss is forced.
        let fall = choice_at(&s, ROOM_BLOODGATE, BG_FALL);
        world
            .apply_choice(ROOM_BLOODGATE, BG_FALL, &fall)
            .expect("the fall is the only path out");
        assert_eq!(world.read_var("downed"), 1, "downed — the run is lost");
        let downed_idx = *world
            .story()
            .passage_index
            .get(ROOM_DOWNED)
            .expect("downed passage");
        assert_eq!(
            world.read_passage(),
            Some(downed_idx),
            "routed INTO the terminal defeat room"
        );
    }

    /// A CAREFUL run is WON — DRIVEN. Measured blows and a well-timed heal survive the
    /// fight, fell the Warden, take the KEY (giving up the crown), and descend to the
    /// hoard. The won run re-verifies by replay. Same universe, same teeth, IDENTICAL
    /// genesis as the lost run — the difference is the player's CHOICES (careful vs
    /// reckless), which is the whole point of stakes.
    #[test]
    fn a_careful_run_is_won_and_reverifies() {
        let s = bloodgate_scene();
        let mut driver = Driver::start(deploy_bloodgate(60), &s).expect("start the trial");

        driver
            .advance(BG_MEASURED)
            .expect("measured (hp 50→35, warden 60→45)");
        driver
            .advance(BG_MEASURED)
            .expect("measured (hp 35→20, warden 45→30)");
        driver
            .advance(BG_MEASURED)
            .expect("measured (hp 20→5, warden 30→15)");
        driver
            .advance(BG_DRINK)
            .expect("drink the draught (hp 5→30)");
        driver
            .advance(BG_MEASURED)
            .expect("measured (hp 30→15, warden 15→0)");
        assert_eq!(
            driver.world().read_var("warden_hp"),
            0,
            "the Warden is felled"
        );
        driver
            .advance(BG_FINISH)
            .expect("land the finishing blow → reliquary");
        assert_eq!(driver.current_passage().as_deref(), Some(ROOM_RELIQUARY));

        driver
            .advance(BG_TAKE_KEY)
            .expect("take the iron key (giving up the crown)");
        driver
            .advance(BG_DESCEND)
            .expect("descend the hoard-stair (needs the key)");
        assert!(driver.is_ended(), "the trial is cleared — a WIN");
        assert_eq!(
            driver.world().read_var("gold"),
            1000,
            "the hoard is claimed"
        );
        assert_eq!(driver.world().read_var("hp"), 15, "survived at 15 HP");

        let play = driver.playthrough();
        verify_chain_linkage(&play).expect("the won-run receipt chain links");
        verify(deploy_bloodgate(60), &s, &play).expect("the WON run re-verifies (verify + replay)");
        verify_by_replay(deploy_bloodgate(60), &s, &play)
            .expect("the WON run passes verify_by_replay");
    }

    /// A retconned LOST run FAILS replay: forge the reckless opener into a measured one
    /// (so HP stays high enough that the later fall gate `hp <= 20` is refused), and the
    /// forged loss cannot pass replay.
    #[test]
    fn a_retconned_lost_run_fails_replay() {
        let s = bloodgate_scene();
        let mut driver = Driver::start(deploy_bloodgate(62), &s).expect("start");
        driver.advance(BG_RECKLESS).expect("reckless opener");
        driver.advance(BG_MEASURED).expect("measured");
        driver.advance(BG_DRINK).expect("drink");
        driver.advance(BG_MEASURED).expect("measured");
        driver.advance(BG_FALL).expect("fall into defeat");
        let play = driver.playthrough();
        verify(deploy_bloodgate(62), &s, &play).expect("the honest lost run re-verifies");

        // Forge step 0: a MEASURED opener instead of the reckless one. HP now stays far
        // above 20, so the recorded FALL (gated hp<=20) is refused on replay.
        let mut forged = play.clone();
        forged.steps[0].choice_index = BG_MEASURED;
        let out = verify_by_replay(deploy_bloodgate(62), &s, &forged);
        assert!(
            matches!(
                out,
                Err(VerifyBreak::RefusedOnReplay { .. })
                    | Err(VerifyBreak::PassageOutOfOrder { .. })
                    | Err(VerifyBreak::StateMismatch {
                        step: StepPos::Step(_)
                    })
            ),
            "a retconned loss fails replay, got {out:?}"
        );
    }

    /// THE RISK-IT GAMBLE (both directions, provably-fair, non-vacuous). A real d20 + stat
    /// check is rolled and bound into a real receipt; the SAME sally-door is REFUSED when
    /// the check fails (DC one above the total) and ADMITTED when it passes (DC at the
    /// total) — the only difference is the DC either side of the identical rolled total.
    /// A failed gamble leaves the player in the fight (the cost); a passed one skips it.
    #[test]
    fn the_risk_roll_gates_the_shortcut_pass_and_fail() {
        let s = bloodgate_scene();

        // Probe the roll (bound only to `stat`, independent of the DC).
        let probe = deploy_bloodgate(70);
        let mut probe = probe;
        probe.seed_var("stat", Value::Int(3));
        let roll = roll_risk(&probe, 0).roll;
        let total = 3 + roll;

        // FAIL world: DC one above the total — the check cannot meet it.
        let mut fail = deploy_bloodgate(70);
        fail.seed_var("stat", Value::Int(3));
        fail.seed_var("dc", Value::Int((total + 1) as i64));
        let committed = make_risk(&fail, 0).expect("the risk check commits (records the total)");
        assert_eq!(fail.read_var("check_total"), total);
        assert!(!risk_succeeds(total, total + 1), "the gamble FAILED");
        let door = choice_at(&s, ROOM_BLOODGATE, BG_FORCE_DOOR);
        let refused = fail.apply_choice(ROOM_BLOODGATE, BG_FORCE_DOOR, &door);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a failed gamble does NOT open the sally-door (FieldLteField), got {refused:?}"
        );
        assert_eq!(
            fail.read_passage(),
            Some(0),
            "the cost: still at the Bloodgate, left to the fight"
        );
        // The failed check is itself an honest, replay-verifiable roll.
        reverify_risk(&committed).expect("the risk roll re-verifies");

        // PASS world: DC exactly the total — the check meets it, the door opens.
        let mut pass = deploy_bloodgate(70);
        pass.seed_var("stat", Value::Int(3));
        pass.seed_var("dc", Value::Int(total as i64));
        make_risk(&pass, 0).expect("the risk check commits");
        assert!(risk_succeeds(total, total), "the gamble PASSED");
        pass.apply_choice(ROOM_BLOODGATE, BG_FORCE_DOOR, &door)
            .expect("a passed gamble opens the sally-door and skips the fight");
        let reliquary_idx = *pass
            .story()
            .passage_index
            .get(ROOM_RELIQUARY)
            .expect("reliquary passage");
        assert_eq!(
            pass.read_passage(),
            Some(reliquary_idx),
            "the shortcut lands past the fight, in the reliquary"
        );
    }

    /// THE FORGED-GAMBLE TOOTH (non-vacuous): forge a passed check by rewriting the bound
    /// roll+total to a natural-20. Replay re-derives the TRUE roll from the recorded
    /// evidence and CATCHES the forgery. The honest roll passes the same tooth.
    #[test]
    fn a_forged_risk_roll_is_caught_on_replay() {
        let mut world = deploy_bloodgate(71);
        world.seed_var("stat", Value::Int(3));
        let honest = make_risk(&world, 0).expect("an honest risk check commits");
        reverify_risk(&honest).expect("the honest roll re-verifies");

        // FORGE a better roll (fake a pass): rewrite the bound roll+total to a DIFFERENT
        // face than the honest one (a natural 20 unless the honest roll already is 20).
        let forged_roll = if honest.draw.roll >= 20 { 1 } else { 20 };
        let forged_total = honest.draw.stat + forged_roll;
        let mut forged = honest.clone();
        let topic = symbol(RISK_TOPIC);
        let event = forged
            .receipt
            .emitted_events
            .iter_mut()
            .find(|e| e.topic == topic)
            .expect("the risk event to rewrite");
        event.data[2] = field_from_u64(forged_roll);
        event.data[3] = field_from_u64(forged_total);
        forged.draw.roll = forged_roll;
        forged.draw.total = forged_total;

        let out = reverify_risk(&forged);
        assert_eq!(
            out,
            Err(RiskReplayError::RollMismatch {
                bound: forged_roll,
                rederived: honest.draw.roll,
            }),
            "the forged (passed) roll is caught on replay, got {out:?}"
        );
    }

    /// THE OPPORTUNITY COST — DRIVEN. In the reliquary the crown and the key write the
    /// SAME `hands` slot under WriteOnce: taking the crown (0→1) then reaching for the key
    /// (1→2) is a REAL executor refusal — you cannot carry both. And the hoard-stair is
    /// gated on the KEY, so the crown-taker is locked out of the hoard: the tradeoff bites.
    #[test]
    fn opportunity_cost_take_one_refuses_both() {
        let s = bloodgate_scene();

        // Reach the reliquary via the risk-it shortcut (a passed gamble) so we start clean.
        let mut world = deploy_bloodgate(80);
        world.seed_var("stat", Value::Int(10));
        world.seed_var("dc", Value::Int(1)); // trivially passable — this test is about `hands`.
        make_risk(&world, 0).expect("the check commits");
        let door = choice_at(&s, ROOM_BLOODGATE, BG_FORCE_DOOR);
        world
            .apply_choice(ROOM_BLOODGATE, BG_FORCE_DOOR, &door)
            .expect("the shortcut opens into the reliquary");

        // Take the crown (hands 0→1) — a real committed claim.
        let crown = choice_at(&s, ROOM_RELIQUARY, BG_TAKE_CROWN);
        world
            .apply_choice(ROOM_RELIQUARY, BG_TAKE_CROWN, &crown)
            .expect("taking the crown commits");
        assert_eq!(world.read_var("hands"), 1, "the crown is in hand");

        // Reaching for the key too (hands 1→2) is REFUSED — you carry ONE.
        let key = choice_at(&s, ROOM_RELIQUARY, BG_TAKE_KEY);
        let refused = world.apply_choice(ROOM_RELIQUARY, BG_TAKE_KEY, &key);
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "taking the key after the crown is refused (WriteOnce hands), got {refused:?}"
        );
        assert_eq!(
            world.read_var("hands"),
            1,
            "anti-ghost: still just the crown"
        );

        // And the crown locks you out of the hoard-stair (it needs the key).
        let descend = choice_at(&s, ROOM_RELIQUARY, BG_DESCEND);
        let locked = world.apply_choice(ROOM_RELIQUARY, BG_DESCEND, &descend);
        assert!(
            matches!(locked, Err(WorldError::Refused(_))),
            "the crown-taker cannot descend the hoard-stair (needs the key), got {locked:?}"
        );
        assert_eq!(
            world.read_var("gold"),
            0,
            "anti-ghost: no hoard for the crown-taker"
        );

        // The MIRROR: a fresh run that takes the KEY instead reaches the hoard — proving
        // the tradeoff is a real fork (the crown gave up exactly this).
        let mut keyed = deploy_bloodgate(81);
        keyed.seed_var("stat", Value::Int(10));
        keyed.seed_var("dc", Value::Int(1));
        make_risk(&keyed, 0).expect("check");
        keyed
            .apply_choice(ROOM_BLOODGATE, BG_FORCE_DOOR, &door)
            .expect("shortcut into the reliquary");
        keyed
            .apply_choice(ROOM_RELIQUARY, BG_TAKE_KEY, &key)
            .expect("take the key instead");
        assert_eq!(keyed.read_var("hands"), 2, "the key is in hand");
        keyed
            .apply_choice(ROOM_RELIQUARY, BG_DESCEND, &descend)
            .expect("the key opens the hoard-stair");
        assert_eq!(
            keyed.read_var("gold"),
            1000,
            "the key-taker claims the hoard"
        );
    }
}
