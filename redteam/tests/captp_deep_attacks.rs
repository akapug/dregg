//! DEEP adversarial tests against CapTP handoff + swiss confinement, going past
//! the first-pass `captp_attacks.rs`. These target the SEAMS the code documents
//! or implies but does not fully enforce:
//!
//!  - the `HandoffError::ReplayDetected` variant that `validate_handoff` never
//!    actually checks (no nonce registry is consulted) → a cert with unlimited
//!    `max_uses` is replayable; the ONLY replay bound is the swiss entry's
//!    `max_uses`, NOT the cert nonce. We pin this precisely.
//!  - the `AuthRequired::Custom { vk_hash }` lattice corner: cross-vk grants and
//!    Custom-over-concrete grants must be rejected as incomparable (Lean
//!    `handoff_non_amplifying` over the rights lattice).
//!  - swiss confinement under revoke/expire boundaries (off-by-one + post-revoke).
//!  - the presentation message binding: does the recipient signature bind the
//!    recipient_pk, or can a cert be re-bound to a different recipient?

use dregg_captp::handoff::{validate_handoff, HandoffCertificate, HandoffError, HandoffPresentation};
use dregg_captp::sturdy::{EnlivenError, SwissTable};
use dregg_cell::AuthRequired;
use dregg_types::{generate_keypair, CellId, FederationId, PublicKey, SigningKey};

fn introducer() -> (SigningKey, FederationId) {
    let (sk, pk) = generate_keypair();
    (sk, FederationId(pk.0))
}

// ===========================================================================
// DEEP ATTACK 1 — FINDING: nonce replay is NOT prevented by validate_handoff.
//
// The cert carries a `nonce` and the error taxonomy has `ReplayDetected`, but
// `validate_handoff` consults NO nonce registry. With an unlimited-use swiss
// entry (max_uses = None), the SAME presentation validates again and again.
// The "swiss numbers are pre-registered, preventing replay after revocation"
// doc claim only bounds replay via swiss max_uses / revoke — the cert nonce
// itself is decorative at this layer. We present the IDENTICAL presentation
// twice and assert BOTH succeed → replayable.
// ===========================================================================

#[test]
fn finding_handoff_nonce_replay_is_not_prevented() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let target_cell = CellId([0xEE; 32]);
    let target_fed = FederationId([0xDD; 32]);

    let mut table = SwissTable::new();
    // Unlimited uses (max_uses = None) — the common "durable handoff" case.
    let swiss = table.export(target_cell, AuthRequired::Signature, 100, None);

    let cert = HandoffCertificate::create(
        &intro_sk, intro_fed, target_fed, target_cell, recip_pk.0,
        AuthRequired::Signature, None, None, None, swiss,
    );
    let pres = HandoffPresentation::create(cert, &recip_sk);

    // First presentation: accepted.
    let r1 = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 150);
    assert!(r1.is_ok(), "first presentation should validate");

    // EXACT SAME presentation (same nonce) replayed: still accepted.
    let r2 = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 151);
    let r3 = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 152);

    // FINDING: the identical cert/nonce validated 3x. ReplayDetected never fires.
    assert!(
        r2.is_ok() && r3.is_ok(),
        "if these now fail, a nonce registry was wired into validate_handoff (fix landed)"
    );
    eprintln!(
        "[CAPTP DEEP 1 / FINDING] handoff nonce replay NOT prevented (3 accepts on one nonce); only swiss max_uses bounds replay: BROKEN (DoS/over-grant if swiss is unlimited-use)"
    );
}

// ===========================================================================
// DEEP ATTACK 2 — Custom-vs-Custom cross-vk grant must be rejected.
//
// Held = Custom{A}; granted = Custom{B} with B != A. The rights lattice
// (`is_narrower_or_equal`) makes distinct Customs incomparable, so this is an
// amplification (granting an authority the introducer does not hold). Verify
// the running validator rejects it.
// ===========================================================================

#[test]
fn deep_custom_cross_vk_grant_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let target_cell = CellId([0xEE; 32]);
    let target_fed = FederationId([0xDD; 32]);

    let vk_a = [0xA1u8; 32];
    let vk_b = [0xB2u8; 32];

    let mut table = SwissTable::new();
    let swiss = table.export_with_options(
        target_cell,
        AuthRequired::Custom { vk_hash: vk_a },
        100,
        None,
        None,
        None,
    );
    // Grant a DIFFERENT custom verifier.
    let cert = HandoffCertificate::create(
        &intro_sk, intro_fed, target_fed, target_cell, recip_pk.0,
        AuthRequired::Custom { vk_hash: vk_b }, None, None, None, swiss,
    );
    let pres = HandoffPresentation::create(cert, &recip_sk);
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 150);
    assert_eq!(
        res.err(),
        Some(HandoffError::Amplification),
        "FINDING: cross-vk Custom grant accepted (distinct Customs must be incomparable)"
    );
    eprintln!("[CAPTP DEEP 2] custom cross-vk grant: DEFENDED");
}

// ===========================================================================
// DEEP ATTACK 3 — Custom held, concrete granted (and vice versa) is incomparable.
//
// Held = Custom{A}; granted = Signature. Custom and Signature are incomparable
// in the lattice (you cannot satisfy a Custom requirement with a plain sig, and
// you cannot derive a sig-cap from a custom-cap). Both directions must reject.
// ===========================================================================

#[test]
fn deep_custom_vs_concrete_both_directions_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let target_cell = CellId([0xEE; 32]);
    let target_fed = FederationId([0xDD; 32]);
    let vk = [0xCCu8; 32];

    // (a) held Custom, granted Signature.
    {
        let mut table = SwissTable::new();
        let swiss = table.export_with_options(
            target_cell, AuthRequired::Custom { vk_hash: vk }, 100, None, None, None,
        );
        let cert = HandoffCertificate::create(
            &intro_sk, intro_fed, target_fed, target_cell, recip_pk.0,
            AuthRequired::Signature, None, None, None, swiss,
        );
        let pres = HandoffPresentation::create(cert, &recip_sk);
        let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 150);
        assert_eq!(res.err(), Some(HandoffError::Amplification));
    }
    // (b) held Signature, granted Custom.
    {
        let mut table = SwissTable::new();
        let swiss = table.export_with_options(
            target_cell, AuthRequired::Signature, 100, None, None, None,
        );
        let cert = HandoffCertificate::create(
            &intro_sk, intro_fed, target_fed, target_cell, recip_pk.0,
            AuthRequired::Custom { vk_hash: vk }, None, None, None, swiss,
        );
        let pres = HandoffPresentation::create(cert, &recip_sk);
        let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 150);
        assert_eq!(res.err(), Some(HandoffError::Amplification));
    }
    eprintln!("[CAPTP DEEP 3] custom<->concrete incomparability: DEFENDED (both directions)");
}

// ===========================================================================
// DEEP ATTACK 4 — Proof-held cannot grant Signature, and vice versa.
//
// Proof and Signature are siblings under Either; neither is narrower than the
// other. A Proof-gated introducer must NOT be able to gift a Signature-gated
// cap (different authority channel), and vice versa. Both reject.
// ===========================================================================

#[test]
fn deep_proof_signature_sibling_grants_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let target_cell = CellId([0xEE; 32]);
    let target_fed = FederationId([0xDD; 32]);

    for (held, granted) in [
        (AuthRequired::Proof, AuthRequired::Signature),
        (AuthRequired::Signature, AuthRequired::Proof),
    ] {
        let mut table = SwissTable::new();
        let swiss = table.export_with_options(target_cell, held.clone(), 100, None, None, None);
        let cert = HandoffCertificate::create(
            &intro_sk, intro_fed, target_fed, target_cell, recip_pk.0,
            granted.clone(), None, None, None, swiss,
        );
        let pres = HandoffPresentation::create(cert, &recip_sk);
        let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 150);
        assert_eq!(
            res.err(),
            Some(HandoffError::Amplification),
            "FINDING: {held:?}->{granted:?} sibling grant accepted (should be incomparable)"
        );
    }
    eprintln!("[CAPTP DEEP 4] proof<->signature sibling grants: DEFENDED");
}

// ===========================================================================
// DEEP ATTACK 5 — confinement holds across revoke (no resurrection).
//
// After revoke(), enliven must fail NotFound. And a fresh export of the SAME
// cell mints a NEW swiss number; the OLD swiss must not enliven the new entry.
// (Confinement is per-secret, not per-cell.)
// ===========================================================================

#[test]
fn deep_revoked_swiss_does_not_resurrect() {
    let mut table = SwissTable::new();
    let cell = CellId([0x42; 32]);
    let old = table.export(cell, AuthRequired::Signature, 100, None);
    assert!(table.enliven(&old, 100).is_ok());

    assert!(table.revoke(&old), "revoke must succeed");
    assert_eq!(table.enliven(&old, 100).unwrap_err(), EnlivenError::NotFound);

    // Re-export the same cell: new secret. Old secret still dead.
    let new = table.export(cell, AuthRequired::Signature, 100, None);
    assert_ne!(old, new, "a fresh export must mint a fresh swiss secret");
    assert_eq!(
        table.enliven(&old, 100).unwrap_err(),
        EnlivenError::NotFound,
        "FINDING: a revoked swiss resurrected against a same-cell re-export"
    );
    assert!(table.enliven(&new, 100).is_ok());
    eprintln!("[CAPTP DEEP 5] revoke/resurrection: DEFENDED (confinement is per-secret)");
}

// ===========================================================================
// DEEP ATTACK 6 — expiration boundary is exact (off-by-one probe).
//
// enliven rejects strictly past expires_at (height > exp). At height == exp it
// must still succeed; at exp+1 it must fail Expired. A loose `>=` would shrink
// the validity window (a liveness bug) and a loose `<` would extend it (a
// safety bug — using a cap past its sunset). Pin both edges.
// ===========================================================================

#[test]
fn deep_expiration_boundary_is_exact() {
    let mut table = SwissTable::new();
    let cell = CellId([0x43; 32]);
    let swiss = table.export(cell, AuthRequired::Signature, 10, Some(50));

    // At expiry height: valid.
    assert!(table.enliven(&swiss, 50).is_ok(), "height==exp must be valid");
    // One past: expired.
    assert_eq!(
        table.enliven(&swiss, 51).unwrap_err(),
        EnlivenError::Expired,
        "FINDING: cap usable past its expiration height"
    );
    eprintln!("[CAPTP DEEP 6] expiration boundary: DEFENDED (== valid, +1 expired)");
}

// ===========================================================================
// DEEP ATTACK 7 — recipient re-binding: a cert minted FOR recipient R cannot be
// validated by a presentation that the attacker signs while LYING about
// recipient_pk. The recipient_pk lives INSIDE the introducer-signed cert, so
// changing it after signing breaks the introducer signature; and the
// presentation's recipient signature is verified against cert.recipient_pk. We
// mutate recipient_pk post-sign and confirm rejection.
// ===========================================================================

#[test]
fn deep_recipient_rebind_after_sign_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = PublicKey(intro_fed.0);
    let (_legit_recip_sk, legit_recip_pk) = generate_keypair();
    let (attacker_sk, attacker_pk) = generate_keypair();
    let target_cell = CellId([0xEE; 32]);
    let target_fed = FederationId([0xDD; 32]);

    let mut table = SwissTable::new();
    let swiss = table.export(target_cell, AuthRequired::Signature, 100, None);

    let mut cert = HandoffCertificate::create(
        &intro_sk, intro_fed, target_fed, target_cell, legit_recip_pk.0,
        AuthRequired::Signature, None, None, None, swiss,
    );
    // Attacker rewrites recipient_pk to themselves so their own presentation sig
    // would verify — but this mutates a SIGNED field, breaking the introducer sig.
    cert.recipient_pk = attacker_pk.0;
    let pres = HandoffPresentation::create(cert, &attacker_sk);
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 150);
    assert_eq!(
        res.err(),
        Some(HandoffError::InvalidIntroducerSignature),
        "FINDING: recipient_pk re-bind survived (recipient not bound by introducer sig)"
    );
    eprintln!("[CAPTP DEEP 7] recipient re-bind: DEFENDED (recipient_pk in signed cert)");
}

// ===========================================================================
// DEEP ATTACK 8 — swiss-number swap: a cert is amplified by pointing it at a
// DIFFERENT, more-powerful swiss entry the attacker happens to know, while the
// cert claims a weak target_cell. The §5b target-binding check reads the cell
// from the swiss entry, so a mismatched (cert target_cell vs swiss cell) is
// caught. Here the attacker swaps the swiss field post-sign → introducer sig
// breaks (swiss is signed). Confirm rejection.
// ===========================================================================

#[test]
fn deep_swiss_swap_after_sign_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let weak_cell = CellId([0x01; 32]);
    let powerful_cell = CellId([0x02; 32]);
    let target_fed = FederationId([0xDD; 32]);

    let mut table = SwissTable::new();
    // The introducer's legitimate (weak) entry.
    let weak_swiss = table.export(weak_cell, AuthRequired::Signature, 100, None);
    // A more-powerful entry the attacker learned the secret of.
    let powerful_swiss = table.export(powerful_cell, AuthRequired::None, 100, None);

    let mut cert = HandoffCertificate::create(
        &intro_sk, intro_fed, target_fed, weak_cell, recip_pk.0,
        AuthRequired::Signature, None, None, None, weak_swiss,
    );
    // Swap the swiss to the powerful entry after signing.
    cert.swiss = powerful_swiss;
    let pres = HandoffPresentation::create(cert, &recip_sk);
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 150);
    assert_eq!(
        res.err(),
        Some(HandoffError::InvalidIntroducerSignature),
        "FINDING: post-sign swiss swap survived (swiss not in signed message)"
    );
    eprintln!("[CAPTP DEEP 8] swiss-number swap: DEFENDED (swiss in signed message)");
}
