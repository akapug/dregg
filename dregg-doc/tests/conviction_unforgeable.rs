//! CONVICTION-GATING IS TRUE BY CONSTRUCTION — the slash cannot be conjured
//! without a genuine `evaluate` detection.
//!
//! The hole this closes: `Conviction` used to be a `pub struct` with `pub` fields
//! over a `pub enum ConvictionEvidence`, so any caller could FABRICATE a
//! conviction and mint a `SlashOutcome` with no genuine detection. Now
//! `Conviction`'s fields are private (no public constructor) and
//! `ConvictionEvidence`'s variants are `#[non_exhaustive]` (non-constructible
//! outside the crate), so a `Conviction` — and hence a `SlashOutcome` — can ONLY
//! come from `CiAssurance::evaluate` genuinely detecting a lie.
//!
//! Three poles:
//! (i)   a GENUINE `ReExecuted` divergence through `evaluate` yields a `Convicted`
//!       whose `Conviction` mints a valid `SlashOutcome` (the real path still works);
//! (ii)  UNFORGEABILITY — an external caller cannot fabricate a `Conviction` /
//!       `SlashOutcome` (the `compile_fail` doctest on `Conviction` is the type-level
//!       proof; here we show the only handle is the accessor surface and that a
//!       conviction for a different bond mints nothing);
//! (iii) a Satisfied / Unmet `evaluate` yields NO conviction (no slash).
#![cfg(feature = "substrate")]

use dregg_cell::CellId;
use dregg_doc::{
    AssuranceInput, AssuranceOutcome, BondRef, CiAssurance, CiVerdict, ConvictionEvidence,
    GovernedKeySet, SlashBeneficiary, SlashOutcome, StakedBond, run_ci_verdict,
};

const CI_EDITOR: u8 = 7;
const CI_REGION: u8 = 8;
const COMMAND: [u8; 32] = [0x11; 32];
const CONFINEMENT: [u8; 32] = [0xC0; 32];
const OUTPUT: [u8; 32] = [0xD1; 32];
const DIVERGENT: [u8; 32] = [0xEE; 32];
const INPUT: [u8; 32] = [0x22; 32];
const BOND: BondRef = BondRef([0xB0; 32]);
const OTHER_BOND: BondRef = BondRef([0xB9; 32]);
const AMOUNT: i64 = 100;

const S1: [u8; 32] = [1; 32];
const S2: [u8; 32] = [2; 32];

fn vk(seed: [u8; 32]) -> [u8; 32] {
    ed25519_dalek::SigningKey::from_bytes(&seed)
        .verifying_key()
        .to_bytes()
}

fn verdict(output: [u8; 32]) -> CiVerdict {
    CiVerdict {
        input_root: INPUT,
        command_id: COMMAND,
        confinement_id: CONFINEMENT,
        exit_code: 0,
        output_digest: output,
    }
}

fn run(seed: [u8; 32], output: [u8; 32]) -> (dregg_turn::TurnReceipt, CiVerdict) {
    let v = verdict(output);
    let r = run_ci_verdict(CI_EDITOR, CI_REGION, seed, &v).expect("CI run commits");
    (r, v)
}

fn staked_policy() -> CiAssurance {
    CiAssurance::Staked {
        bond_ref: BOND,
        inner: Box::new(CiAssurance::ReExecuted {
            keys: GovernedKeySet::operator([vk(S1), vk(S2)]),
            quorum: 1,
        }),
    }
}

fn bond() -> StakedBond {
    StakedBond::burned(
        BOND,
        AMOUNT,
        CellId::from_bytes([0xA1; 32]),
        CellId::from_bytes([0x0A; 32]),
    )
    .to_beneficiary(SlashBeneficiary::Burn)
}

// ── POLE (i): a GENUINE divergence mints a valid SlashOutcome (regression). ────
#[test]
fn genuine_divergence_mints_a_valid_slash() {
    let (primary, pv) = run(S1, OUTPUT);
    let (div_r, div_v) = run(S2, DIVERGENT);
    let attestations = [(div_r, div_v)];
    let input = AssuranceInput {
        receipt: &primary,
        verdict: &pv,
        attestations: &attestations,
        proof: None,
        challenge: None,
        editor_seed: CI_EDITOR,
        region_seed: CI_REGION,
    };

    // A real detection: the Staked policy convicts and binds the bond.
    let conviction = match staked_policy().evaluate(&input) {
        AssuranceOutcome::Convicted(c) => c,
        other => panic!("expected a genuine conviction, got {other:?}"),
    };
    // The evidence is what evaluate ACTUALLY verified (its own divergence view).
    assert_eq!(conviction.bond_ref(), Some(BOND));
    match conviction.evidence() {
        // NOTE the required `..`: `ReExecDivergence` is `#[non_exhaustive]`, so this
        // external test crate cannot exhaustively destructure it — the same fence
        // that makes it non-CONSTRUCTIBLE here.
        ConvictionEvidence::ReExecDivergence {
            claimed,
            divergent,
            signer,
            ..
        } => {
            assert_eq!(*claimed, OUTPUT, "the claimed output evaluate saw");
            assert_eq!(*divergent, DIVERGENT, "the divergent output evaluate saw");
            assert_eq!(*signer, vk(S2), "the signer evaluate verified");
        }
        other => panic!("expected ReExecDivergence, got {other:?}"),
    }

    // That genuine conviction mints a valid SlashOutcome for this bond.
    let slash = SlashOutcome::from_conviction(&bond(), &conviction)
        .expect("a genuine conviction naming this bond mints a slash");
    assert_eq!(slash.bond_ref, BOND);
    assert_eq!(slash.amount, AMOUNT);
}

// ── POLE (ii): UNFORGEABILITY. The compile_fail doctest on `Conviction` is the ─
//    type-level proof a caller cannot fabricate one. Here: the only handles are
//    read-only accessors, and a genuine conviction naming a DIFFERENT bond mints
//    nothing — the caller cannot redirect a real conviction to an arbitrary bond.
#[test]
fn a_real_conviction_cannot_be_redirected_to_an_arbitrary_bond() {
    let (primary, pv) = run(S1, OUTPUT);
    let (div_r, div_v) = run(S2, DIVERGENT);
    let attestations = [(div_r, div_v)];
    let input = AssuranceInput {
        receipt: &primary,
        verdict: &pv,
        attestations: &attestations,
        proof: None,
        challenge: None,
        editor_seed: CI_EDITOR,
        region_seed: CI_REGION,
    };
    let conviction = match staked_policy().evaluate(&input) {
        AssuranceOutcome::Convicted(c) => c,
        other => panic!("expected a conviction, got {other:?}"),
    };

    // The genuine conviction names BOND; a StakedBond for a DIFFERENT bond mints
    // no slash — `from_conviction` is the only constructor and it checks the ref.
    let other = StakedBond::burned(
        OTHER_BOND,
        AMOUNT,
        CellId::from_bytes([0xA1; 32]),
        CellId::from_bytes([0x0A; 32]),
    );
    assert!(
        SlashOutcome::from_conviction(&other, &conviction).is_none(),
        "a conviction cannot be redirected to a bond it does not name"
    );

    // The conviction exposes only read-only accessors (no field mutation / no
    // public constructor — enforced at compile time; see the compile_fail doctest
    // on `Conviction`). Reading is all a caller can do:
    assert_eq!(conviction.bond_ref(), Some(BOND));
}

// ── POLE (iii): a Satisfied / Unmet evaluate yields NO conviction (no slash). ──
#[test]
fn satisfied_or_unmet_yields_no_conviction() {
    // Satisfied: primary + an AGREEING re-execution (quorum 1 met).
    let (primary, pv) = run(S1, OUTPUT);
    let (agree_r, agree_v) = run(S2, OUTPUT);
    let agree = [(agree_r, agree_v)];
    let sat_input = AssuranceInput {
        receipt: &primary,
        verdict: &pv,
        attestations: &agree,
        proof: None,
        challenge: None,
        editor_seed: CI_EDITOR,
        region_seed: CI_REGION,
    };
    assert!(
        matches!(
            staked_policy().evaluate(&sat_input),
            AssuranceOutcome::Satisfied
        ),
        "an agreeing re-execution satisfies — no conviction"
    );

    // Unmet: NO attestations at all (short quorum) — Unmet, never a conviction.
    let none: [(dregg_turn::TurnReceipt, CiVerdict); 0] = [];
    let unmet_input = AssuranceInput {
        receipt: &primary,
        verdict: &pv,
        attestations: &none,
        proof: None,
        challenge: None,
        editor_seed: CI_EDITOR,
        region_seed: CI_REGION,
    };
    match staked_policy().evaluate(&unmet_input) {
        AssuranceOutcome::Unmet(_) => {}
        other => panic!("expected Unmet (no lie proven), got {other:?}"),
    }
}
