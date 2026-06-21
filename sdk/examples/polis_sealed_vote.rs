//! Polis sealed vote — a runnable UNLINKABLE governance election in one binary.
//!
//! This is the sealed-governance app over the REAL wired SDK surface
//! (`dregg_sdk::sealed_governance` + `dregg_sdk::council_seal`, declared in
//! `sdk/src/lib.rs`) PLUS the unbiasable beacon (`dregg_sdk::beacon_cell` →
//! `dregg_federation::beacon::BeaconDraw`) for sortition. Every guarantee you
//! see below is carried by the threshold seal and the nullifier binding, not by
//! any honest-collector assumption.
//!
//! The polis:
//!   - a 3-of-5 tally COUNCIL is born by a genuine genesis DKG — NO party ever
//!     holds the council secret `f(0)`, so no official can peek a ballot;
//!   - eligible citizens each hold a private eligibility secret. They derive an
//!     anonymous per-election NULLIFIER (a one-time eligibility spend token that
//!     does NOT name them), seal `choice ‖ nullifier` to the council, and cast;
//!   - the window CLOSES; the quorum opens every ballot together and tallies;
//!   - a separate beacon cell draws unbiasable randomness to seat a tie-break
//!     juror / break an exact tie — randomness fixed AFTER the seals commit, so
//!     no voter could aim a tie to their advantage.
//!
//! The teeth, all fail-closed and all demonstrated in the run:
//!   - an INELIGIBLE voter (not on the roster) is rejected at cast;
//!   - a DOUBLE VOTE (nullifier reuse) is rejected at cast;
//!   - an EARLY PEEK (sub-quorum tally before close) opens NOTHING (the cliff);
//!   - a BALLOT SUBSTITUTION (a valid borrowed nullifier paired with a seal
//!     binding a different nullifier + a forged choice) is rejected at tally.
//!
//! Run:
//!   cargo run -p dregg-sdk --example polis_sealed_vote

use dregg_federation::beacon::BeaconDraw;
use dregg_sdk::beacon_cell::BeaconCell;
use dregg_sdk::{
    Ballot, Council, CouncilSealError, GovernanceError, PolisElection, SealedBallot,
    UnlinkableSubmission, eligibility_nullifier, seal_unlinkable_ballot,
};

/// A citizen: a human-readable name (for the demo printout only — the vote is
/// NOT linked to it) and a private 32-byte eligibility secret.
struct Citizen {
    name: &'static str,
    secret: [u8; 32],
}

fn main() {
    let election_label: &[u8] = b"polis:budget-allocation-2026";

    // ── 1. The eligible citizens + the 3-of-5 tally council ─────────────────
    // choice 0 = "fund parks", choice 1 = "fund transit".
    let roll = [
        Citizen { name: "Ada",   secret: [0x10; 32] },
        Citizen { name: "Bao",   secret: [0x20; 32] },
        Citizen { name: "Cyra",  secret: [0x30; 32] },
        Citizen { name: "Dmitri", secret: [0x40; 32] },
    ];
    let choices = [0u32, 1, 0, 1]; // a deliberate 2–2 tie

    // The roster commits H(secret) per eligible voter — never the secrets.
    let roster: Vec<[u8; 32]> = roll
        .iter()
        .map(|c| PolisElection::roster_commit(&c.secret))
        .collect();

    // No party holds f(0); a sealer needs ONLY the public committee.
    let council = Council::genesis(5, 3, [0x51; 32]).expect("genesis DKG");
    println!("tally council        : 3-of-5 (genesis DKG, no party holds f(0))");
    let mut election = PolisElection::new(council, election_label, roster);
    println!("election label       : {}", String::from_utf8_lossy(election_label));
    println!("eligible roster      : {} citizens (by H(secret) commitment)", roll.len());
    println!("mode                 : UNLINKABLE roster-gated sealed ballots\n");

    // ── 2. An INELIGIBLE voter is refused at cast (the roster tooth) ────────
    let stranger = [0xEE; 32]; // not on the roster
    match election.cast(&stranger, 0, [0x77; 32]) {
        Err(GovernanceError::Ineligible) => {
            println!("ineligible voter     : REJECTED (no roster commitment) ✓")
        }
        other => panic!("expected Ineligible, got {other:?}"),
    }

    // ── 3. Cast: each eligible citizen casts an unlinkable sealed vote ──────
    println!("\ncasting (each seals choice ‖ anonymous nullifier; council can't peek):");
    for (i, (c, &choice)) in roll.iter().zip(choices.iter()).enumerate() {
        election
            .cast(&c.secret, choice, [(i as u8) + 1; 32])
            .expect("eligible first-time vote");
        // We print the name only to narrate the demo — the SEALED ballot carries
        // ONLY the anonymous nullifier, unlinkable to `c.name`/`c.secret`.
        let nullifier = eligibility_nullifier(&c.secret, election_label);
        println!(
            "  {:>6} casts a sealed ballot (nullifier {}…, choice hidden)",
            c.name,
            hex8(&nullifier)
        );
    }

    // ── 4. A DOUBLE VOTE is rejected (the nullifier tooth) ──────────────────
    match election.cast(&roll[0].secret, 1, [0x99; 32]) {
        Err(GovernanceError::DoubleVote) => {
            println!("\ndouble-vote attempt  : REJECTED (nullifier reuse) ✓")
        }
        other => panic!("expected DoubleVote, got {other:?}"),
    }

    // ── 5. An EARLY PEEK (sub-quorum tally) opens NOTHING — the cliff ────────
    // Close the window first; then a 2-of-5 sub-quorum tries to tally.
    election.close().expect("close the window");
    match election.tally(&[0, 1]) {
        Err(GovernanceError::Seal(CouncilSealError::BelowThreshold)) => {
            println!("early-peek (2-of-5)  : REJECTED (below threshold; no early tally) ✓")
        }
        other => panic!("expected BelowThreshold cliff, got {other:?}"),
    }

    // ── 6. The quorum tallies at close ──────────────────────────────────────
    let outcome = election.tally(&[0, 1, 2]).expect("quorum tally");
    println!(
        "\nquorum tally (3-of-5): {} ballots opened, counts = {:?}",
        outcome.counted, outcome.tallies
    );
    let parks = *outcome.tallies.get(&0).unwrap_or(&0);
    let transit = *outcome.tallies.get(&1).unwrap_or(&0);
    println!("  fund parks (0)     : {parks}");
    println!("  fund transit (1)   : {transit}");

    // ── 7. Beacon sortition breaks the exact tie (unbiasable) ───────────────
    if parks == transit {
        println!("\nexact tie ({parks}-{transit}) — drawing an UNBIASABLE beacon to break it:");
        // A real beacon cell: genesis DKG + threshold-BLS, ticking out a value
        // no sub-quorum could predict or steer. The draw is seeded by a tick
        // produced AFTER the ballots sealed, so no voter could aim the tie.
        let mut beacon = BeaconCell::genesis(5, 3, 1, [0xBE; 32]).expect("beacon genesis");
        let tick = beacon.tick().expect("beacon tick");
        assert!(beacon.anchor().verify_beacon(&tick.output), "light-client verifies the draw");
        let mut draw = BeaconDraw::new(&tick.randomness());
        let winner = draw.draw(2).expect("draw from {0,1}");
        let names = ["fund parks", "fund transit"];
        println!(
            "  beacon randomness  : {}… (light-client-verified against genesis anchor)",
            hex8(&tick.randomness())
        );
        println!("  tie-break winner   : choice {winner} ({})", names[winner as usize]);
    } else if parks > transit {
        println!("\nwinner               : choice 0 (fund parks)");
    } else {
        println!("\nwinner               : choice 1 (fund transit)");
    }

    // ── 8. A BALLOT SUBSTITUTION is rejected at tally (the binding tooth) ────
    // A fresh election: an attacker pairs a VALID (dedup-passing) public
    // nullifier with a seal that binds a DIFFERENT nullifier and a forged
    // choice 999. Collection accepts the public token; tally opens the seal and
    // sees the bound nullifier disagrees ⇒ the whole tally fail-closes.
    {
        let sub_council = Council::genesis(5, 3, [0x52; 32]).expect("genesis DKG");
        let mut attacked = SealedBallot::new_unlinkable(sub_council, election_label);
        let acommittee = attacked.committee().clone();
        let valid_nullifier = eligibility_nullifier(&[0x77; 32], election_label);
        let forged = seal_unlinkable_ballot(
            &acommittee,
            election_label,
            Ballot { choice: 999 },
            [0xAB; 32], // bound nullifier INSIDE the seal: not valid_nullifier
            [0x09; 32],
        );
        let attack = UnlinkableSubmission {
            submission: forged.submission, // seal binds 0xAB…
            nullifier: valid_nullifier,    // public claim: a valid token
        };
        attacked.collect_unlinkable(attack).expect("dedup passes (public token valid)");
        attacked.close().expect("close");
        match attacked.tally(&[0, 1, 2]) {
            Err(GovernanceError::NullifierMismatch) => {
                println!("\nballot substitution  : REJECTED (sealed nullifier ≠ claimed token; choice 999 never counts) ✓")
            }
            other => panic!("expected NullifierMismatch, got {other:?}"),
        }
    }

    println!("\nall sealed-governance teeth fail-closed; the tally is provable from the opened ballots.");
}

/// First 4 bytes of a 32-byte value as hex, for a compact demo printout.
fn hex8(b: &[u8; 32]) -> String {
    b[..4].iter().map(|x| format!("{x:02x}")).collect()
}
