//! # The reimagined Descent, DRIVEN — the Lean-authored rules on the real executor.
//!
//! Every test here drives the REAL `EmbeddedExecutor` through
//! [`dungeon_on_dregg::descent`]: the installed `CellProgram` is LOADED from the
//! Lean-emitted artifact (`program/dungeon_program.json` — source of truth:
//! `metatheory/Dregg2/Games/DungeonProgram.lean :: dungeonProgram`); there is no
//! hand-rolled Rust tooth anywhere in the path.
//!
//! The battery mirrors the Lean `#guard` battery (same crowned run, same attacks) so
//! the two referees — the Lean `Exec` evaluator the theorems run against, and the
//! deployed Rust executor — are DRIVEN over the same transitions and agree.

use dregg_app_framework::{CellProgram, StateConstraint, TransitionGuard, symbol};
use dungeon_on_dregg::descent::{
    BANKED, CARRIED, DELVE, Descent, FLEE, GENESIS, LOOT, PROGRAM_JSON, SCENE_ID, SMITE, Sim,
    UNLOCK,
};
use spween_dregg::WorldError;

fn refused(r: Result<dregg_app_framework::TurnReceipt, WorldError>) -> bool {
    matches!(r, Err(WorldError::Refused(_)))
}

/// The artifact is the Lean emission: it parses, names OUR scene, and the loaded
/// program is `Cases` with the six verb arms + six riders — and the genesis arm
/// carries the spween one-shot sentinel teeth (so the world births + injects the
/// sentinel; a genesis replay is structurally unsatisfiable).
#[test]
fn loaded_program_is_the_lean_object() {
    assert!(PROGRAM_JSON.contains(&format!("\"scene\": \"{SCENE_ID}\"")));
    let dep = dungeon_on_dregg::descent::Deployment::new();
    let program = dep.program();
    let CellProgram::Cases(cases) = &program else {
        panic!("descent program must be Cases");
    };
    assert_eq!(cases.len(), 13, "6 verb arms + 6 riders + genesis");
    // The genesis arm is MethodIs("genesis") and carries a HeapField tooth on the
    // genesis sentinel (spween keys the sentinel machinery off exactly this shape).
    let genesis = cases
        .iter()
        .find(|c| matches!(c.guard, TransitionGuard::MethodIs { method } if method == symbol(GENESIS)))
        .expect("genesis arm");
    assert!(
        genesis.constraints.iter().any(|c| matches!(
            c,
            StateConstraint::HeapField { key, .. } if *key == spween_dregg::GENESIS_DONE_EXT_KEY
        )),
        "genesis arm carries the one-shot sentinel teeth"
    );
    // At least one rider is a SlotChanged-guarded AllOf (the stapleable-slot fix is
    // deployed structure, not doc prose).
    assert!(
        cases.iter().any(|c| matches!(
            &c.guard,
            TransitionGuard::AllOf(children)
                if children.iter().any(|g| matches!(g, TransitionGuard::SlotChanged { .. }))
        )),
        "the SlotChanged riders are installed"
    );
}

/// THE CROWNED RUN — the same 17-verb script the Lean model proves legal and the Lean
/// `#guard` battery proves admitted — commits end-to-end on the real executor: 18 real
/// receipts (genesis + 17), non-zero and chain-linked, ending banked with the prize
/// and the three keys banked (bank = 4, the `crowned_bank_le_four` bound met with
/// equality) and 2 breath to spare.
#[test]
fn crowned_run_commits_with_real_receipts() {
    let mut d = Descent::deploy(7).expect("deploy + genesis");
    let mut receipts = Vec::new();
    receipts.push(None); // genesis receipt is inside deploy; re-verify via state below.

    let push = |r: Result<dregg_app_framework::TurnReceipt, WorldError>| {
        let r = r.expect("legal verb commits");
        assert_ne!(r.turn_hash, [0u8; 32]);
        Some(r)
    };

    // Floor 1: slay (hp 1), win the key to way 2, exercise it.
    receipts.push(push(d.delve()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.loot(1)));
    receipts.push(push(d.unlock(2)));
    // Floor 2.
    receipts.push(push(d.delve()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.loot(2)));
    receipts.push(push(d.unlock(3)));
    // Floor 3 (guardian hp 2).
    receipts.push(push(d.delve()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.loot(3)));
    receipts.push(push(d.unlock(4)));
    // Floor 4 — the bottom: THE PRIZE.
    receipts.push(push(d.delve()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.loot(0)));
    receipts.push(push(d.flee()));

    // The receipt chain links (each pre-state is the predecessor's post-state).
    let committed: Vec<_> = receipts.into_iter().flatten().collect();
    for w in committed.windows(2) {
        assert_eq!(
            w[0].post_state_hash, w[1].pre_state_hash,
            "receipt chain links"
        );
    }

    // The committed world agrees with the model's crowned end-state.
    assert_eq!(d.read_reg("fate"), 1);
    assert_eq!(d.read_reg("bank"), 4, "prize + three keys banked");
    assert_eq!(d.read_reg("pack"), 0);
    assert_eq!(d.read_reg("spent"), 24, "the perfect run costs 24 breath");
    assert_eq!(d.read_reg("depth"), 4);
    assert_eq!(d.read_relic(0), BANKED, "THE PRIZE is banked");
    assert_eq!(d.read_relic(4), 1, "an unlooted treasure stays in the deep");
}

/// A keyless descent is a REAL executor refusal that commits nothing (anti-ghost).
#[test]
fn keyless_descent_is_refused_and_commits_nothing() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("way 1 is always open");
    // The mover itself refuses (way 2 shut) — now FORGE the projection at the raw
    // seam so the EXECUTOR is the referee under test, not the mover.
    let sim = d.sim().clone();
    let mut forged = sim.clone();
    forged.depth = 2;
    forged.wounds = 0;
    forged.spent += 1;
    let effects = d.effects_for(&forged);
    assert!(
        refused(d.commit_raw(DELVE, effects)),
        "keyless descent refused by the Lean-sourced teeth"
    );
    // Anti-ghost: nothing committed.
    assert_eq!(d.read_reg("depth"), 1);
    assert_eq!(d.read_reg("spent"), sim.spent);
}

/// DUPE: a loot-shaped turn that mints a pack relic out of nothing (pack +1 with no
/// hoard debit) breaks the conservation tooth and is refused.
#[test]
fn dupe_relic_is_refused() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("smite");
    let sim = d.sim().clone();
    let effects = vec![
        d.reg_effect("pack", sim.pack() + 1),
        d.reg_effect("spent", sim.spent + 1),
    ];
    assert!(
        refused(d.commit_raw(LOOT, effects)),
        "a minted relic breaks SumEquals and is refused"
    );
    assert_eq!(d.read_reg("pack"), 0);
}

/// KEYLESS WAY: flipping `way_2` without the carried key-relic is refused — the
/// SlotChanged rider demands the exhibited key on EVERY verb.
#[test]
fn keyless_way_flip_is_refused_on_any_verb() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    let sim = d.sim().clone();
    for method in [UNLOCK, SMITE, LOOT, DELVE] {
        let effects = vec![
            d.reg_effect("way_2", 1),
            d.reg_effect("spent", sim.spent + 2),
        ];
        assert!(
            refused(d.commit_raw(method, effects)),
            "keyless way flip refused under {method}"
        );
    }
    assert_eq!(d.read_reg("way_2"), 0);
}

/// With the key genuinely CARRIED, the same way-flip is admitted — the rider tooth is
/// a key-exercise gate, not a blanket freeze (the non-vacuity pole of the rider).
#[test]
fn carried_key_opens_the_way() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("slay guardian 1");
    d.loot(1).expect("win the key to way 2");
    assert_eq!(d.read_relic(1), CARRIED);
    d.unlock(2)
        .expect("exercising the carried key opens the way");
    assert_eq!(d.read_reg("way_2"), 1);
}

/// STAPLE: a loot turn that ALSO descends is refused (the loot frame freezes depth;
/// the depth rider would demand the delve law on top).
#[test]
fn stapled_loot_plus_descend_is_refused() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("smite");
    let sim = d.sim().clone();
    let mut forged = sim.clone();
    forged.custody[1] = CARRIED; // the legitimate loot half…
    forged.spent += 1;
    forged.depth += 1; // …stapled to a descent.
    let effects = d.effects_for(&forged);
    assert!(refused(d.commit_raw(LOOT, effects)));
    assert_eq!(d.read_reg("depth"), 1);
}

/// TOMB: after banking, EVERY verb is refused (the run is a frozen tomb) — driven
/// twin of the Lean `banked_run_frozen` / `banked_tomb_refuses`.
#[test]
fn banked_tomb_is_frozen() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.flee().expect("bank the empty pack");
    assert_eq!(d.read_reg("fate"), 1);
    assert!(refused(d.delve()));
    assert!(refused(d.smite()));
    assert!(refused(d.flee()));
    // And a FORGED resurrection (write fate back to 0) is refused: fate transitions
    // are pinned to {0→0, 0→1}.
    let sim = d.sim().clone();
    let effects = vec![
        d.reg_effect("fate", 0),
        d.reg_effect("spent", sim.spent + 1),
    ];
    assert!(refused(d.commit_raw(DELVE, effects)), "no resurrection");
}

/// FAKE FLEE: banking while KEEPING the pack (fate flips but pack stays) is refused —
/// `pack' = 0` is the flee law, re-demanded by the fate rider.
#[test]
fn fake_flee_keeping_the_pack_is_refused() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("smite");
    d.loot(1).expect("loot the key");
    let sim = d.sim().clone();
    assert_eq!(sim.pack(), 1);
    let mut forged = sim.clone();
    forged.fate = 1; // bank…
    forged.spent += 1; // …but never empty the pack (custody stays CARRIED).
    let effects = d.effects_for(&forged);
    assert!(refused(d.commit_raw(FLEE, effects)));
    assert_eq!(d.read_reg("fate"), 0);
}

/// RELIC TELEPORT: moving a relic's custody floor→floor (code 1 → 2) is refused — the
/// provenance ratchet's `memberOf {home, CARRIED, BANKED}` admits no other floor.
#[test]
fn relic_teleport_is_refused() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    let sim = d.sim().clone();
    let effects = vec![
        d.relic_effect(4, 2), // treasure minted on floor 1 "moves" to floor 2
        d.reg_effect("hoard_1", sim.hoard_at(1) - 1),
        d.reg_effect("hoard_2", sim.hoard_at(2) + 1),
        d.reg_effect("wounds", sim.wounds + 1),
        d.reg_effect("spent", sim.spent + 2),
    ];
    assert!(refused(d.commit_raw(SMITE, effects)));
    assert_eq!(d.read_relic(4), 1);
}

/// GENESIS REPLAY: re-running the mint after deploy is refused — the sentinel one-shot
/// (`Equals 1 ∧ DeltaEquals 1`) is jointly unsatisfiable from `old = 1`. The universal
/// write-hatch is closed at the root.
#[test]
fn genesis_replay_is_refused() {
    let d = Descent::deploy(3).expect("deploy");
    let effects = d.effects_for(&Sim::genesis());
    assert!(refused(d.commit_raw(GENESIS, effects)));
}

/// UNKNOWN METHOD: a verb outside the six is default-denied even with lawful-looking
/// writes (the riders carry a method disjunct, so they cannot be ridden in from an
/// unknown method) — driven twin of the Lean `unknown_method_refused`.
#[test]
fn unknown_method_is_default_denied() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    let sim = d.sim().clone();
    let effects = vec![d.reg_effect("spent", sim.spent + 1)];
    assert!(refused(d.commit_raw("plunder", effects)));
}

/// CAPACITY ATTENUATION, driven: at floor 1 the pack may hold up to 7 (CAP − 1); a
/// forged loot pushing pack past the attenuated bound is refused even with a
/// conservation-consistent hoard debit.
#[test]
fn overpacking_past_attenuated_capacity_is_refused() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("smite");
    // Legally loot all three floor-1 relics (pack 3, depth 1 — well within CAP).
    d.loot(1).expect("key 2");
    d.loot(4).expect("treasure");
    d.loot(5).expect("treasure");
    let sim = d.sim().clone();
    // Forge: pack jumps to 8 with a "consistent" hoard debit — but 8 + 1 > CAP.
    let mut forged = sim.clone();
    forged.spent += 1;
    let effects: Vec<_> = d.effects_for(&forged).into_iter().collect();
    let mut effects = effects;
    effects.push(d.reg_effect("pack", 8));
    effects.push(d.reg_effect("hoard_2", 0));
    effects.push(d.reg_effect("hoard_3", 0));
    effects.push(d.reg_effect("hoard_4", 0));
    assert!(refused(d.commit_raw(LOOT, effects)));
}

/// THE LIGHT: burning breath past BREATH is refused (fieldLte spent) and every verb
/// must strictly spend (a free verb — spent unchanged — is refused too).
#[test]
fn the_clock_binds() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    let sim = d.sim().clone();
    // A free smite (no breath paid) is refused.
    let mut forged = sim.clone();
    forged.wounds += 1;
    let effects = d.effects_for(&forged);
    assert!(refused(d.commit_raw(SMITE, effects)), "no free exertion");
    // A clock jump past BREATH is refused.
    let mut forged = sim.clone();
    forged.wounds += 1;
    forged.spent = 27;
    let effects = d.effects_for(&forged);
    assert!(
        refused(d.commit_raw(SMITE, effects)),
        "the light caps at 26"
    );
}
