//! Adversarial tests against CapTP: swiss-table confinement (Lean B1 /
//! `Exec/CapTP` confinement), handoff non-amplification (Lean
//! `handoff_non_amplifying` / B3), handoff unforgeability (B2), and a
//! resource-griefing finding on the validation ordering.
//!
//! Adversary model: a "malicious agent holding a (weaker) capability" who tries
//! to amplify it, plus a network attacker who intercepts a handoff certificate.

use dregg_captp::handoff::{HandoffCertificate, HandoffError, HandoffPresentation, validate_handoff};
use dregg_captp::sturdy::{EnlivenError, SwissTable};
use dregg_cell::AuthRequired;
use dregg_redteam::{flip_bit, mint_dalek_keypair, AttackOutcome};
use dregg_types::{generate_keypair, CellId, FederationId, SigningKey};

// --- shared scenario builders ----------------------------------------------

fn introducer() -> (SigningKey, FederationId) {
    let (sk, pk) = generate_keypair();
    (sk, FederationId(pk.0))
}

/// Build a target swiss table with the introducer holding `held` authority on
/// `cell` and return (swiss, target_cell, target_fed).
fn target_with_held(
    table: &mut SwissTable,
    held: AuthRequired,
    held_effects: Option<u32>,
) -> ([u8; 32], CellId, FederationId) {
    let target_cell = CellId([0xEE; 32]);
    let target_fed = FederationId([0xDD; 32]);
    let swiss = table.export_with_options(target_cell, held, 100, None, held_effects, None);
    (swiss, target_cell, target_fed)
}

// ===========================================================================
// ATTACK 1 — confinement: enliven a cap WITHOUT the swiss number (B1)
// Lean claims: a cap is unreachable without its 256-bit bearer secret.
// ===========================================================================

#[test]
fn attack_confinement_guess_swiss_number_is_rejected() {
    let mut table = SwissTable::new();
    let real = table.export(CellId([1; 32]), AuthRequired::Signature, 100, None);

    // Adversary guesses: all-zeros, all-ones, bit-flips of a leaked URI prefix.
    let mut guesses: Vec<[u8; 32]> = vec![[0u8; 32], [0xff; 32]];
    for byte in 0..32 {
        for bit in 0..8 {
            let mut g = real;
            flip_bit(&mut g, byte, bit);
            guesses.push(g); // a single-bit-different swiss number
        }
    }

    let mut any_break = AttackOutcome::Defended;
    for g in &guesses {
        if *g == real {
            continue;
        }
        if table.enliven(g, 100).is_ok() {
            any_break = AttackOutcome::Broken;
        }
    }
    // EVIDENCE: no near-miss guess enlivens. Confinement = entropy of the secret.
    assert_eq!(any_break, AttackOutcome::Defended);
    // Sanity: the *real* secret still works (the table is not just always-deny).
    assert!(table.enliven(&real, 100).is_ok());
    eprintln!("[ATTACK 1] confinement vs {} guesses: {}", guesses.len(), any_break);
}

// ===========================================================================
// ATTACK 2 — non-amplification: granted MORE than held (B3 / Granovetter)
// Lean `handoff_non_amplifying`: granted.rights ≤ held.rights (where held is
// the target's authoritative swiss entry, NOT the cert's self-asserted field).
// ===========================================================================

#[test]
fn attack_amplify_permissions_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();

    let mut table = SwissTable::new();
    // The introducer only HOLDS `Signature` on the cell...
    let (swiss, target_cell, target_fed) =
        target_with_held(&mut table, AuthRequired::Signature, None);

    // ...but forges a cert claiming to GRANT `None` (strictly weaker requirement
    // = strictly MORE authority; an amplification).
    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        AuthRequired::None, // <-- amplification: easier-to-satisfy than held Signature
        None,
        None,
        None,
        swiss,
    );
    let pres = HandoffPresentation::create(cert, &recip_sk);

    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 100);
    // EVIDENCE: the target reads `held` from its OWN swiss entry and rejects.
    assert_eq!(res.err(), Some(HandoffError::Amplification));
    eprintln!("[ATTACK 2] permission amplification: {}", AttackOutcome::Defended);
}

#[test]
fn attack_amplify_effect_mask_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();

    let mut table = SwissTable::new();
    // Held: only effect bits 0b0011.
    let (swiss, target_cell, target_fed) =
        target_with_held(&mut table, AuthRequired::Signature, Some(0b0011));

    // Grant a SUPERSET 0b1111 (adds bits 2,3 the introducer never held).
    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        AuthRequired::Signature,
        Some(0b1111),
        None,
        None,
        swiss,
    );
    let pres = HandoffPresentation::create(cert, &recip_sk);
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 100);
    assert_eq!(res.err(), Some(HandoffError::Amplification));

    // Also: held restricted, grant `None` (= unrestricted = all effects) → amplify.
    let mut table2 = SwissTable::new();
    let (swiss2, tc2, tf2) = target_with_held(&mut table2, AuthRequired::Signature, Some(0b0011));
    let cert2 = HandoffCertificate::create(
        &intro_sk, intro_fed, tf2, tc2, recip_pk.0, AuthRequired::Signature, None, None, None, swiss2,
    );
    let pres2 = HandoffPresentation::create(cert2, &recip_sk);
    let res2 = validate_handoff(&pres2, &intro_pk, &mut table2, &[intro_fed], 100);
    assert_eq!(res2.err(), Some(HandoffError::Amplification));
    eprintln!("[ATTACK 2b] effect-mask amplification (both forms): {}", AttackOutcome::Defended);
}

// ===========================================================================
// ATTACK 3 — unforgeability: forge / tamper the introducer signature (B2)
// ===========================================================================

#[test]
fn attack_forge_introducer_signature_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();

    let mut table = SwissTable::new();
    let (swiss, target_cell, target_fed) =
        target_with_held(&mut table, AuthRequired::Signature, None);

    let mut cert = HandoffCertificate::create(
        &intro_sk, intro_fed, target_fed, target_cell, recip_pk.0,
        AuthRequired::Signature, None, None, None, swiss,
    );
    // Tamper a content field AFTER signing (target_cell) — sig no longer covers it.
    cert.target_cell = CellId([0x99; 32]);
    let pres = HandoffPresentation::create(cert, &recip_sk);
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 100);
    assert_eq!(res.err(), Some(HandoffError::InvalidIntroducerSignature));
    eprintln!("[ATTACK 3] post-sign field tamper: {}", AttackOutcome::Defended);
}

#[test]
fn attack_intercept_cert_present_as_wrong_recipient_is_rejected() {
    // Network attacker intercepts a cert in transit and tries to present it as
    // themselves (they do NOT own recipient_pk).
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (_legit_recip_sk, legit_recip_pk) = generate_keypair();
    let (attacker_sk, _attacker_pk) = generate_keypair();

    let mut table = SwissTable::new();
    let (swiss, target_cell, target_fed) =
        target_with_held(&mut table, AuthRequired::Signature, None);

    let cert = HandoffCertificate::create(
        &intro_sk, intro_fed, target_fed, target_cell, legit_recip_pk.0,
        AuthRequired::Signature, None, None, None, swiss,
    );
    // Attacker signs the presentation with THEIR key, not legit_recip's.
    let pres = HandoffPresentation::create(cert, &attacker_sk);
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 100);
    assert_eq!(res.err(), Some(HandoffError::InvalidRecipientSignature));
    eprintln!("[ATTACK 3b] cert-interception replay: {}", AttackOutcome::Defended);
}

// ===========================================================================
// ATTACK 4 — FINDING: validate_handoff enlivens (consumes a use / advances
// state) BEFORE the non-amplification check. An attacker who can present
// amplifying certs against a known swiss number can EXHAUST the introducer's
// max_uses budget without ever succeeding — a resource-griefing / DoS vector.
//
// This is NOT a confinement or amplification break (those hold). It is an
// operational gap: the Lean spec models a pure accept/reject decision; the Rust
// has a SIDE EFFECT on reject. We assert the bad behavior precisely so it is
// logged, not hidden.
// ===========================================================================

#[test]
fn finding_amplifying_handoff_consumes_a_use_on_rejection() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();

    let mut table = SwissTable::new();
    let target_cell = CellId([0xEE; 32]);
    let target_fed = FederationId([0xDD; 32]);
    // The introducer registered a swiss entry with max_uses = 1 (single handoff).
    let swiss = table.export_with_options(
        target_cell,
        AuthRequired::Signature,
        100,
        None,
        None,
        Some(1), // <-- one-shot
    );

    // Attacker presents an AMPLIFYING cert (will be rejected for amplification),
    // but the rejection path already enlivened the swiss entry (use_count -> 1).
    let bad_cert = HandoffCertificate::create(
        &intro_sk, intro_fed, target_fed, target_cell, recip_pk.0,
        AuthRequired::None, // amplifies
        None, None, None, swiss,
    );
    let bad_pres = HandoffPresentation::create(bad_cert, &recip_sk);
    let bad = validate_handoff(&bad_pres, &intro_pk, &mut table, &[intro_fed], 100);
    assert_eq!(bad.err(), Some(HandoffError::Amplification));

    // Now the LEGITIMATE recipient presents a valid (non-amplifying) cert.
    // Because the attacker already burned the single use, the honest handoff
    // fails with MaxUsesExhausted: the cap was griefed.
    let good_cert = HandoffCertificate::create(
        &intro_sk, intro_fed, target_fed, target_cell, recip_pk.0,
        AuthRequired::Signature, // legitimate, non-amplifying
        None, None, None, swiss,
    );
    let good_pres = HandoffPresentation::create(good_cert, &recip_sk);
    let good = validate_handoff(&good_pres, &intro_pk, &mut table, &[intro_fed], 100);

    // FINDING: the honest handoff is denied because the attacker consumed the use.
    assert_eq!(
        good.err(),
        Some(HandoffError::MaxUsesExhausted),
        "expected the griefed-out state; if this changed, the ordering was fixed"
    );
    eprintln!(
        "[ATTACK 4 / FINDING] amplifying-cert rejection still consumed a use: {}",
        AttackOutcome::Broken
    );
}

// ===========================================================================
// ATTACK 5 — FINDING (metadata leak): SwissTable::peek and the EnlivenError
// taxonomy are an ORACLE. enliven distinguishes NotFound vs Expired vs
// ExhaustedUses, so a prober learns whether a guessed swiss number EXISTS
// (Expired/Exhausted) vs is absent (NotFound) — a membership/metadata oracle
// on the secret-keyed table, weaker than full confinement but a real leak.
// ===========================================================================

#[test]
fn finding_enliven_error_taxonomy_is_a_membership_oracle() {
    let mut table = SwissTable::new();
    // An EXPIRED entry (still present in the table).
    let present_expired = table.export(CellId([7; 32]), AuthRequired::Signature, 10, Some(20));
    let absent = [0x55u8; 32];

    let on_present = table.enliven(&present_expired, 999).unwrap_err(); // Expired
    let on_absent = table.enliven(&absent, 999).unwrap_err(); // NotFound

    // The two distinct errors let an attacker DISTINGUISH "this 32-byte value is
    // a (dead) swiss number we know" from "unknown". With 256-bit secrets this
    // is not a practical confinement break, but it IS an information leak that a
    // constant "EnlivenError::Denied" would not give.
    assert_eq!(on_present, EnlivenError::Expired);
    assert_eq!(on_absent, EnlivenError::NotFound);
    assert_ne!(on_present, on_absent);
    eprintln!(
        "[ATTACK 5 / FINDING] enliven error taxonomy distinguishes present-vs-absent: {}",
        AttackOutcome::Leak
    );
}

// ===========================================================================
// ATTACK 6 — untrusted introducer (B2 trust path): a validly-signed cert from
// a federation NOT in known_federations must be rejected.
// ===========================================================================

#[test]
fn attack_untrusted_introducer_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let mut table = SwissTable::new();
    let (swiss, target_cell, target_fed) =
        target_with_held(&mut table, AuthRequired::Signature, None);

    let cert = HandoffCertificate::create(
        &intro_sk, intro_fed, target_fed, target_cell, recip_pk.0,
        AuthRequired::Signature, None, None, None, swiss,
    );
    let pres = HandoffPresentation::create(cert, &recip_sk);
    // known_federations is EMPTY: even a perfectly valid signature is untrusted.
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[], 100);
    assert_eq!(res.err(), Some(HandoffError::UntrustedIntroducer));

    // BUT NOTE: the trust check is step 3, AFTER signature verification but the
    // amplification/enliven side effects are step 5. UntrustedIntroducer fires
    // before enliven, so this path does NOT grief the use budget. Good.
    let _ = mint_dalek_keypair; // (silence unused import on some toolchains)
    eprintln!("[ATTACK 6] untrusted introducer: {}", AttackOutcome::Defended);
}
