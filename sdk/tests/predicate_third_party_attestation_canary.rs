//! THE THIRD-PARTY ATTESTATION CANARY — the falsifier for the last fail-closed hole in the
//! predicate stack.
//!
//! ## The statement under test
//!
//! `dregg_bridge::verify_predicate_proof_third_party(proof, facts_root, state_root)` proves, to a
//! verifier holding NO trusted state and NOT knowing the value:
//!
//! > "some fact of the token committed at `facts_root` has a value satisfying `proof.predicate`."
//!
//! Three legs carry that:
//!
//! * the descriptor's value↔fact WELD forces the compared value to be the one the presented
//!   `fact_commitment` covers (`circuit/tests/predicate_arith_fact_weld_canary.rs`);
//! * the ATTESTATION (`dregg-attested-fact-membership::v1`) forces that same commitment to be the
//!   blinded image of a `fact_hash` that is a MEMBER of `facts_root`;
//! * the JOIN — both descriptors compute the commitment by the identical arity-4 absorb of
//!   `[fact_hash, state_root, blinding, 0]`, pinned byte-equal by
//!   `dregg_circuit::attested_fact_membership_witness::tests::the_commitment_is_byte_equal_to_the_predicate_familys`.
//!
//! Before the attestation existed, leg 2 was missing and there was NO sound source for the expected
//! commitment: `sdk/src/verify.rs::verify_disclosure_presentation` had to fail closed on every
//! predicate proof (honest, but a third party simply could not verify one), and the trusted-state
//! path was the only thing that worked — for verifiers who already knew the value.
//!
//! ## The canary shape
//!
//! [`third_party_verifies_honest_and_refuses_prover_chosen_commitment`] drives BOTH poles over ONE
//! forged proof, so neither can pass vacuously and the canary runs on every invocation rather than
//! by hand — the shape `predicate_gate_forged_commitment_canary.rs` established.

use dregg_circuit::attested_fact_membership_witness::attested_facts_root;
use dregg_circuit::field::BabyBear;
use dregg_circuit::predicate_arith_witness::{Blinding, FactBinding};
use dregg_sdk::AgentCipherclerk;
use dregg_trace::{Fact as TraceFact, Term};

/// The predicate symbol shared by every fact here.
fn pred_sym() -> [u8; 32] {
    *blake3::hash(b"has-credit-score").as_bytes()
}

/// The token-state root the commitments are taken against.
fn state_root() -> BabyBear {
    BabyBear::new(0x57A7E)
}

/// A single-`Int`-term fact — the shape the arithmetic predicate path proves about.
fn score_fact(score: i64) -> TraceFact {
    TraceFact {
        predicate: pred_sym(),
        terms: vec![Term::Int(score)],
    }
}

/// The co-path of the token's facts tree. In production the ISSUER builds this tree and the
/// presentation attests its root; here it stands in for that, since what is under test is the
/// ATTESTATION, not the tree build.
fn siblings() -> Vec<[BabyBear; 3]> {
    vec![
        [
            BabyBear::new(0xA1),
            BabyBear::new(0xA2),
            BabyBear::new(0xA3),
        ],
        [
            BabyBear::new(0xB1),
            BabyBear::new(0xB2),
            BabyBear::new(0xB3),
        ],
    ]
}

/// The value the token ACTUALLY holds. The prover cannot prove `>= 900` about it honestly.
const TRUE_SCORE: i64 = 300;
/// The value the prover INVENTS: it satisfies the bound, but no fact of the token covers it.
const FORGED_SCORE: i64 = 999;
/// The bound. `TRUE_SCORE` fails it; `FORGED_SCORE` passes it — that gap is the forgery's payload.
const THRESHOLD: u32 = 900;

fn binding_of(fact: &TraceFact) -> FactBinding {
    AgentCipherclerk::fact_binding(fact, state_root())
}

fn fact_hash_of(fact: &TraceFact) -> BabyBear {
    let value = AgentCipherclerk::extract_fact_value(fact).expect("value");
    binding_of(fact).fact_hash_of(BabyBear::new(value))
}

/// The `facts_root` a THIRD PARTY reads out of the presentation's public inputs: the root of the
/// tree the TRUE fact sits in. The verifier trusts this and nothing else.
fn trusted_facts_root() -> BabyBear {
    attested_facts_root(fact_hash_of(&score_fact(TRUE_SCORE)), &siblings())
        .expect("the trusted facts root builds")
}

/// Build an ATTESTED predicate proof about `fact` under `root_siblings` — the third-party shape
/// (no decommitment, carries an attestation).
fn prove_attested(
    fact: &TraceFact,
    predicate: &dregg_bridge::Predicate,
    root_siblings: &[[BabyBear; 3]],
) -> dregg_bridge::BridgePredicateProof {
    let value = AgentCipherclerk::extract_fact_value(fact).expect("value");
    let blinding = dregg_bridge::fresh_predicate_blinding();
    dregg_bridge::prove_predicate_for_fact_attested(
        value,
        binding_of(fact),
        blinding,
        predicate,
        root_siblings,
    )
    .expect("a TRUE statement about a member fact must prove")
}

/// ⚑ **THE HEADLINE + ITS OWN CANARY.**
///
/// A THIRD PARTY — no trusted state, no knowledge of any value — verifies an honest predicate proof,
/// and REFUSES a proof whose fact commitment the prover chose. Both poles, one test.
///
/// The forged proof is GENUINE in every internal respect: the weld holds, `999 >= 900` is true, the
/// attestation it carries is itself a valid STARK. Its only lie is about WHICH TREE the fact lives
/// in — and that is precisely what the trusted `facts_root` parameter catches.
#[test]
fn third_party_verifies_honest_and_refuses_prover_chosen_commitment() {
    let trusted_root = trusted_facts_root();

    // ---- POLE 1: HONEST. A member fact, a true statement, verified by a third party.
    let honest = prove_attested(
        &score_fact(TRUE_SCORE),
        &dregg_bridge::Predicate::Gte(100),
        &siblings(),
    );
    let accepted =
        dregg_bridge::verify_predicate_proof_third_party(&honest, trusted_root, state_root());
    println!("THIRD PARTY on the HONEST proof:  accepted = {accepted}");
    assert!(
        accepted,
        "COMPLETENESS BROKEN: a third party must verify an honest predicate proof about a member \
         fact — without this, refusing everything would score as a pass"
    );
    // The third party never saw the value, and the proof carries no opening to recover it with.
    assert!(
        honest.blinding.is_none(),
        "the third-party shape must carry NO decommitment"
    );

    // ---- POLE 2: FORGED. The prover invents `score = 999`, proves `999 >= 900`, and attests it
    // ---- under a tree OF ITS OWN — the only tree in which its invented fact is a member.
    let forged = prove_attested(
        &score_fact(FORGED_SCORE),
        &dregg_bridge::Predicate::Gte(THRESHOLD),
        &siblings(),
    );
    let prover_chosen_root = forged
        .attestation
        .as_ref()
        .expect("the forged proof carries its own attestation")
        .facts_root;
    assert_ne!(
        prover_chosen_root, trusted_root,
        "the prover's tree must differ from the token's, or the test is vacuous"
    );

    // 2a. THE NEUTERED GATE — what a verifier does if it reads the root off the PROOF instead of
    //     the presentation. This is the `x != x` collapse one level up, and it ACCEPTS the forgery.
    //     It is the canary: if this stops accepting, the REFUSED pole below proves nothing.
    let neutered =
        dregg_bridge::verify_predicate_proof_third_party(&forged, prover_chosen_root, state_root());
    println!("NEUTERED (prover-chosen root) on the FORGED proof: accepted = {neutered}");
    assert!(
        neutered,
        "CANARY BROKEN: a verifier feeding the PROVER's own root is supposed to accept the forgery \
         — if it does not, this test is no longer demonstrating the hole it exists to close"
    );

    // 2b. THE REAL GATE — the root comes from the presentation the verifier trusts. REFUSED.
    let refused =
        dregg_bridge::verify_predicate_proof_third_party(&forged, trusted_root, state_root());
    println!("THIRD PARTY (trusted root) on the FORGED proof:    accepted = {refused}");
    assert!(
        !refused,
        "THE HOLE IS OPEN: a predicate proof over a fact that is NOT a member of the token's \
         attested facts tree was accepted by a third party"
    );

    // 2c. A proof with NO attestation at all is refused — the pre-attestation shape must not sneak
    //     through as "nothing to check".
    let unattested = {
        let fact = score_fact(FORGED_SCORE);
        let value = AgentCipherclerk::extract_fact_value(&fact).expect("value");
        dregg_bridge::prove_predicate_for_fact(
            value,
            binding_of(&fact),
            dregg_bridge::fresh_predicate_blinding(),
            &dregg_bridge::Predicate::Gte(THRESHOLD),
        )
        .expect("proves")
    };
    assert!(
        unattested.attestation.is_none(),
        "the trusted-state shape carries no attestation"
    );
    assert!(
        !dregg_bridge::verify_predicate_proof_third_party(&unattested, trusted_root, state_root()),
        "a proof with NO attestation must FAIL CLOSED for a third party — nothing binds its \
         commitment to the token"
    );
}

/// The attestation cannot be RE-POINTED: a valid attestation for one fact does not verify against a
/// root it was not built under, and swapping an honest proof's attestation onto a forged proof
/// breaks the JOIN.
#[test]
fn an_attestation_cannot_be_repointed_or_transplanted() {
    let trusted_root = trusted_facts_root();

    let honest = prove_attested(
        &score_fact(TRUE_SCORE),
        &dregg_bridge::Predicate::Gte(100),
        &siblings(),
    );
    let mut forged = prove_attested(
        &score_fact(FORGED_SCORE),
        &dregg_bridge::Predicate::Gte(THRESHOLD),
        &siblings(),
    );

    // TRANSPLANT: give the forged proof the HONEST proof's attestation. The attestation verifies
    // against the trusted root — but it attests the HONEST commitment, not the forged one, so the
    // JOIN fails.
    forged.attestation = honest.attestation.clone();
    assert!(
        dregg_bridge::verify_fact_attestation(
            forged.attestation.as_ref().expect("attestation"),
            trusted_root,
            state_root()
        )
        .is_some(),
        "the transplanted attestation is itself valid under the trusted root — so what refuses the \
         proof below must be the JOIN, not a broken attestation"
    );
    assert!(
        !dregg_bridge::verify_predicate_proof_third_party(&forged, trusted_root, state_root()),
        "an attestation for a DIFFERENT fact must not carry a forged predicate proof — the \
         attested commitment and the proof's pinned commitment must be the same felt"
    );

    // RE-POINT: the honest attestation does not verify against a root it was not built under.
    let other_root = BabyBear::new(0xDEAD);
    assert!(
        dregg_bridge::verify_fact_attestation(
            honest.attestation.as_ref().expect("attestation"),
            other_root,
            state_root()
        )
        .is_none(),
        "an attestation must not verify against a root it does not name"
    );
    // Nor against a different state root.
    assert!(
        dregg_bridge::verify_fact_attestation(
            honest.attestation.as_ref().expect("attestation"),
            trusted_root,
            BabyBear::new(0xBEEF)
        )
        .is_none(),
        "an attestation must not verify against a state root it does not name"
    );
}

/// ⚑ **UNLINKABILITY SURVIVES CONTACT WITH THE THIRD-PARTY VERIFIER.**
///
/// This is what the membership design buys over re-derive. Two showings of the SAME fact publish
/// different commitments, and BOTH verify to a third party under the SAME root — without either
/// showing handing over an opening. Under the re-derive path the verifier could only accept by
/// being given the blinding, which is exactly the decommitment this shape does not send.
#[test]
fn two_showings_of_one_fact_are_unlinkable_yet_both_verify() {
    let trusted_root = trusted_facts_root();
    let fact = score_fact(TRUE_SCORE);
    let predicate = dregg_bridge::Predicate::Gte(100);

    let first = prove_attested(&fact, &predicate, &siblings());
    let second = prove_attested(&fact, &predicate, &siblings());

    println!(
        "UNLINKABLE: two showings of score={TRUE_SCORE} -> commitments {} vs {}",
        first.fact_commitment.as_u32(),
        second.fact_commitment.as_u32()
    );
    assert_ne!(
        first.fact_commitment, second.fact_commitment,
        "two showings of the same fact must not be correlatable by commitment"
    );

    for (name, proof) in [("first", &first), ("second", &second)] {
        assert!(
            dregg_bridge::verify_predicate_proof_third_party(proof, trusted_root, state_root()),
            "{name}: must verify to a third party under the attested root"
        );
        assert!(
            proof.blinding.is_none(),
            "{name}: unlinkability is only real if no opening travels"
        );
    }

    // The attestations agree on the ROOT (same token) and disagree on the COMMITMENT (unlinkable).
    let a = first.attestation.as_ref().expect("a");
    let b = second.attestation.as_ref().expect("b");
    assert_eq!(a.facts_root, b.facts_root, "same token, same attested root");
    assert_ne!(
        a.fact_commitment, b.fact_commitment,
        "different showings, different commitments"
    );
}

/// ⚑ **THE BRUTE-FORCE LEAK, DRIVEN CLOSED.**
///
/// The re-derive path must publish the `blinding` as a decommitment, and a proof-holder then
/// recovers a low-entropy value by grinding: guess `v`, recompute
/// `hash_4_to_1([hash_fact(sym, [v, …]), state_root, blinding, 0])`, compare. This test runs that
/// exact falsifier against BOTH shapes:
///
/// * the TRUSTED-STATE proof (`blinding: Some`) — the falsifier RECOVERS the value. That is not a
///   regression, it is the honest cost of an opening, and it is why an opening is now opt-in.
/// * the ATTESTED third-party proof (`blinding: None`) — the falsifier has nothing to grind
///   against and recovers NOTHING, while the proof still verifies.
///
/// Both poles in one test: if the first stops recovering, the second proves nothing.
#[test]
fn the_brute_force_falsifier_recovers_the_opened_proof_and_not_the_attested_one() {
    /// The falsifier. Sweeps a small domain, testing each candidate against the proof's commitment.
    /// It needs the DECOMMITMENT — with no opening there is no candidate commitment to compute.
    fn brute_force(
        proof: &dregg_bridge::BridgePredicateProof,
        domain: std::ops::Range<i64>,
    ) -> Option<(i64, usize)> {
        let blinding = Blinding(proof.blinding?);
        for (tries, v) in domain.enumerate() {
            let candidate = score_fact(v);
            let value = AgentCipherclerk::extract_fact_value(&candidate).ok()?;
            if binding_of(&candidate).commitment_of(BabyBear::new(value), blinding)
                == proof.fact_commitment
            {
                return Some((v, tries + 1));
            }
        }
        None
    }

    let fact = score_fact(TRUE_SCORE);
    let predicate = dregg_bridge::Predicate::Gte(100);
    let domain = 0..1000;

    // ---- POLE 1: the OPENED (trusted-state) proof. The falsifier RECOVERS the value.
    let opened = dregg_bridge::prove_predicate_for_fact(
        AgentCipherclerk::extract_fact_value(&fact).expect("value"),
        binding_of(&fact),
        dregg_bridge::fresh_predicate_blinding(),
        &predicate,
    )
    .expect("proves");
    let recovered = brute_force(&opened, domain.clone());
    println!("BRUTE-FORCE on the OPENED proof:   {recovered:?}");
    assert_eq!(
        recovered.map(|(v, _)| v),
        Some(TRUE_SCORE),
        "CANARY BROKEN: the falsifier is supposed to recover the value from a proof carrying a \
         decommitment — if it does not, the closed pole below proves nothing"
    );

    // ---- POLE 2: the ATTESTED (third-party) proof. Nothing to grind.
    let attested = prove_attested(&fact, &predicate, &siblings());
    let recovered = brute_force(&attested, domain);
    println!("BRUTE-FORCE on the ATTESTED proof: {recovered:?}");
    assert_eq!(
        recovered, None,
        "THE LEAK IS OPEN: the falsifier recovered the value from an attested third-party proof"
    );

    // …and the attested proof still VERIFIES. Closing the leak by breaking the proof would be no
    // closure at all.
    assert!(
        dregg_bridge::verify_predicate_proof_third_party(
            &attested,
            trusted_facts_root(),
            state_root()
        ),
        "the attested proof must still verify — a leak closed by refusing everything is not closed"
    );
}
