//! THE STAKED-BOND SLASH BITES — the four poles proving the forfeiture behind
//! `CiAssurance::Staked` is REAL, conserving, one-shot, and conviction-gated.
//!
//! Each pole drives a GENUINE inner conviction (a `ReExecuted` divergence) or a
//! genuine satisfaction through `CiAssurance::bond_disposition`, then fires the
//! resulting bond movement over real `dregg_cell::Cell` balances:
//!
//! (i)   inner `ReExecuted` conviction → a conserving forfeiture moving EXACTLY
//!       the bond amount to the beneficiary (`Σδ=0`), the host's stake reduced;
//! (ii)  a SECOND slash of the same bond → refused (one-shot);
//! (iii) inner Satisfied → NO forfeiture, the bond releasable to the host;
//! (iv)  conservation: the total across {host, bond-cell, beneficiary} is
//!       invariant across the whole post→slash lifecycle.
#![cfg(feature = "substrate")]

use dregg_cell::{Cell, CellId};
use dregg_doc::BondRef;
use dregg_doc::{
    AssuranceInput, AssuranceOutcome, BondDisposition, BondError, BondState, BondStatus,
    CiAssurance, CiVerdict, GovernedKeySet, SlashBeneficiary, SlashOutcome, StakedBond,
    bond_disposition, post_bond, release_bond, run_ci_verdict, slash_bond,
};

// The CI-run region cell identity (repo policy; the verifier rebuilds it).
const CI_EDITOR: u8 = 7;
const CI_REGION: u8 = 8;
const COMMAND: [u8; 32] = [0x11; 32];
const CONFINEMENT: [u8; 32] = [0xC0; 32];
const OUTPUT: [u8; 32] = [0xD1; 32];
const DIVERGENT: [u8; 32] = [0xEE; 32];
const INPUT: [u8; 32] = [0x22; 32];
const BOND: BondRef = BondRef([0xB0; 32]);
const AMOUNT: i64 = 100;

// Two distinct executor signing seeds → two distinct trusted keys.
const S1: [u8; 32] = [1; 32];
const S2: [u8; 32] = [2; 32];

// Distinct cell ids for the host (poster), the bond-holding cell, and the
// beneficiary (the challenger who proved the lie).
fn host_id() -> CellId {
    CellId::from_bytes([0xA1; 32])
}
fn bond_cell_id() -> CellId {
    CellId::from_bytes([0xB1; 32])
}
fn challenger_id() -> CellId {
    CellId::from_bytes([0xC1; 32])
}
fn asset_id() -> CellId {
    CellId::from_bytes([0x0A; 32])
}

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

/// A `Staked{inner: ReExecuted{quorum:1}}` policy over the two trusted keys.
fn staked_policy() -> CiAssurance {
    CiAssurance::Staked {
        bond_ref: BOND,
        inner: Box::new(CiAssurance::ReExecuted {
            keys: GovernedKeySet::operator([vk(S1), vk(S2)]),
            quorum: 1,
        }),
    }
}

/// The bond descriptor: `AMOUNT` posted by the host, forfeit to the challenger.
fn bond() -> StakedBond {
    StakedBond::burned(BOND, AMOUNT, host_id(), asset_id())
        .to_beneficiary(SlashBeneficiary::Challenger(challenger_id()))
}

fn host_cell(balance: i64) -> Cell {
    Cell::remote_stub_with_id_and_balance(host_id(), balance)
}
fn bond_holding_cell() -> Cell {
    Cell::remote_stub_with_id_and_balance(bond_cell_id(), 0)
}
fn challenger_cell() -> Cell {
    Cell::remote_stub_with_id_and_balance(challenger_id(), 0)
}

// ── POLE (i): a genuine inner conviction slashes exactly the bond amount. ──────
#[test]
fn conviction_slashes_exactly_the_bond_conservingly() {
    let mut host = host_cell(1_000);
    let mut bond_cell = bond_holding_cell();
    let mut beneficiary = challenger_cell();
    let b = bond();

    // Host POSTS the bond at job-start: a conserving transfer host -> bond cell.
    post_bond(&mut host, &mut bond_cell, &b).expect("host posts the bond");
    assert_eq!(host.state.balance(), 900, "the stake left the host");
    assert_eq!(
        bond_cell.state.balance(),
        100,
        "the stake is locked in the bond cell"
    );
    assert_eq!(
        BondState::read(&bond_cell).unwrap().status,
        BondStatus::Posted
    );

    // A GENUINE inner conviction: primary (S1, OUTPUT) + a divergent re-execution
    // (S2, DIFFERENT output) over the same work.
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

    // The disposition is a SLASH naming this bond (the conviction-gate fired).
    let disposition = staked_policy().bond_disposition(&input, &b);
    let outcome = match disposition {
        BondDisposition::Slash(s) => {
            assert_eq!(s.bond_ref, BOND);
            assert_eq!(s.amount, AMOUNT);
            s
        }
        other => panic!("expected a Slash disposition, got {other:?}"),
    };

    // Fire the forfeiture: a conserving transfer bond cell -> beneficiary.
    let bond_before = bond_cell.state.balance();
    let bene_before = beneficiary.state.balance();
    let moved = slash_bond(&mut bond_cell, &mut beneficiary, &b, &outcome).expect("slash fires");
    assert_eq!(moved, AMOUNT, "exactly the bond amount is forfeit");

    // Σδ = 0 across {bond cell, beneficiary}: nothing leaked or appeared.
    let delta =
        (bond_cell.state.balance() - bond_before) + (beneficiary.state.balance() - bene_before);
    assert_eq!(delta, 0, "the slash conserves value (Σδ=0)");
    assert_eq!(
        bond_cell.state.balance(),
        0,
        "the bonded stake left the host's cell"
    );
    assert_eq!(
        beneficiary.state.balance(),
        100,
        "the challenger received the forfeit"
    );
    // The host's stake is reduced: it never got the bond back.
    assert_eq!(host.state.balance(), 900);
    assert_eq!(
        BondState::read(&bond_cell).unwrap().status,
        BondStatus::Consumed
    );
}

// ── POLE (ii): a second slash of the same bond is refused (one-shot). ──────────
#[test]
fn second_slash_is_refused_one_shot() {
    let mut host = host_cell(1_000);
    let mut bond_cell = bond_holding_cell();
    let mut beneficiary = challenger_cell();
    let b = bond();
    post_bond(&mut host, &mut bond_cell, &b).unwrap();

    // Build a slash outcome from a genuine conviction.
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
    let outcome = match bond_disposition(&staked_policy().evaluate(&input), &b) {
        BondDisposition::Slash(s) => s,
        other => panic!("expected Slash, got {other:?}"),
    };

    // First slash succeeds.
    assert_eq!(
        slash_bond(&mut bond_cell, &mut beneficiary, &b, &outcome),
        Ok(AMOUNT)
    );
    // A SECOND slash of the same (now consumed) bond is refused.
    assert_eq!(
        slash_bond(&mut bond_cell, &mut beneficiary, &b, &outcome),
        Err(BondError::AlreadyConsumed),
        "a bond can be slashed AT MOST once"
    );
    // The beneficiary was not double-paid.
    assert_eq!(beneficiary.state.balance(), 100);
    // And a release-after-slash is refused too (the one-shot flag is shared).
    assert_eq!(
        release_bond(&mut bond_cell, &mut host, &b),
        Err(BondError::AlreadyConsumed)
    );
}

// ── POLE (iii): a satisfied inner leaves the bond untouched + releasable. ──────
#[test]
fn satisfied_inner_releases_the_bond_to_the_host() {
    let mut host = host_cell(1_000);
    let mut bond_cell = bond_holding_cell();
    let beneficiary = challenger_cell();
    let b = bond();
    post_bond(&mut host, &mut bond_cell, &b).unwrap();
    assert_eq!(host.state.balance(), 900);

    // A GENUINE satisfaction: primary (S1, OUTPUT) + one AGREEING re-execution
    // (S2, SAME output) → quorum 1 met → Satisfied.
    let (primary, pv) = run(S1, OUTPUT);
    let (agree_r, agree_v) = run(S2, OUTPUT);
    let attestations = [(agree_r, agree_v)];
    let input = AssuranceInput {
        receipt: &primary,
        verdict: &pv,
        attestations: &attestations,
        proof: None,
        challenge: None,
        editor_seed: CI_EDITOR,
        region_seed: CI_REGION,
    };
    assert_eq!(
        staked_policy().evaluate(&input),
        AssuranceOutcome::Satisfied
    );

    // The disposition is RELEASE, not a slash: no forfeiture on satisfaction.
    match staked_policy().bond_disposition(&input, &b) {
        BondDisposition::Release(r) => {
            assert_eq!(r.bond_ref, BOND);
            assert_eq!(r.amount, AMOUNT);
            assert_eq!(r.poster, host_id());
        }
        other => panic!("expected a Release disposition, got {other:?}"),
    }

    // Nothing went to the beneficiary; the bond returns to the host.
    assert_eq!(
        beneficiary.state.balance(),
        0,
        "a satisfied inner slashes nothing"
    );
    let returned = release_bond(&mut bond_cell, &mut host, &b).expect("the bond releases");
    assert_eq!(returned, AMOUNT);
    assert_eq!(
        host.state.balance(),
        1_000,
        "the host's stake is made whole"
    );
    assert_eq!(bond_cell.state.balance(), 0);
}

// ── POLE (iv): the total across all three parties is invariant. ────────────────
#[test]
fn slash_conserves_the_total_across_all_parties() {
    let mut host = host_cell(1_000);
    let mut bond_cell = bond_holding_cell();
    let mut beneficiary = challenger_cell();
    let b = bond();

    let total = |h: &Cell, c: &Cell, ben: &Cell| {
        h.state.balance() + c.state.balance() + ben.state.balance()
    };
    let start = total(&host, &bond_cell, &beneficiary);

    // Post the bond (host -> bond cell) — total unchanged.
    post_bond(&mut host, &mut bond_cell, &b).unwrap();
    assert_eq!(
        total(&host, &bond_cell, &beneficiary),
        start,
        "post conserves"
    );

    // Slash on a genuine conviction (bond cell -> beneficiary) — total unchanged.
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
    let outcome =
        SlashOutcome::from_conviction(&b, &conviction).expect("the conviction names this bond");

    slash_bond(&mut bond_cell, &mut beneficiary, &b, &outcome).unwrap();
    assert_eq!(
        total(&host, &bond_cell, &beneficiary),
        start,
        "the slash creates/destroys no value — only moves it"
    );
}
