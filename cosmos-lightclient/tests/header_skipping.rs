//! Non-adjacent (skipping) header verification, BOTH polarities, default-run.
//!
//! ACCEPT: a genuine cosmoshub-4 header ~95 blocks past the trusted anchor
//! verifies WITHOUT the intermediate headers, by the Tendermint trust-threshold
//! overlap rule: validators from the trusted `next_validators` set carrying at
//! least `trust_threshold` of that set's power signed the skip-target commit
//! (in addition to the full >= 2/3 rule over the target's own set).
//!
//! REJECT (fail-closed): insufficient trust overlap refuses with
//! `NotEnoughVotingPower` (the bisection signal); a trusted state whose
//! validator set does not hash to its own commitment refuses BEFORE any tally
//! (`TrustedStateCorrupt` — the overlap base must be the committed set, not
//! whatever a relayer delivered).

mod common;

use cosmos_lightclient::{verify_cosmos_header, HeaderVerifyError};
use tendermint::validator::{Info, Set as ValidatorSet};
use tendermint::vote::Power;
use tendermint::PublicKey;
use tendermint_light_client_verifier::types::TrustThreshold;

// ---------------------------------------------------------------- ACCEPT KAT

#[test]
fn accept_non_adjacent_skip_with_trust_overlap() {
    let trusted = common::bank_trusted_state();
    let ush = common::skip_signed_header();
    let vals = common::skip_validators();

    let skip_height = ush.header.height.value();
    assert!(
        skip_height > trusted.height.value() + 1,
        "fixture must be genuinely non-adjacent: {} vs trusted {}",
        skip_height,
        trusted.height.value()
    );

    let verified = verify_cosmos_header(
        &trusted,
        &ush,
        &vals,
        None,
        TrustThreshold::ONE_THIRD, // the canonical skipping threshold
        common::trusting_period(),
        common::now_after(&ush),
    )
    .expect("genuine non-adjacent header verifies by trust overlap");

    assert_eq!(verified.chain_id(), "cosmoshub-4");
    assert_eq!(verified.height(), skip_height);
    assert_eq!(verified.app_hash(), ush.header.app_hash.as_bytes());
}

// -------------------------------------------- REJECT: overlap below threshold

#[test]
fn reject_skip_below_trust_overlap_threshold() {
    // A SELF-CONSISTENT trusted state (its next_validators hash to its
    // next_validators_hash) that genuinely lacks overlap: the real validators
    // plus one fabricated validator holding 20x the total power, who of course
    // never signed the skip-target commit. Real signers then carry < 1/21 of
    // the trusted set's power — below even the 1/3 floor. This models a trusted
    // anchor whose voting power moved away: the light client MUST refuse and
    // demand bisection, never skip on stale trust.
    let real = common::bank_validators_h1();
    let total: u64 = real.total_voting_power.value();
    let fake_key = PublicKey::from_raw_ed25519(&[0x42u8; 32]).expect("32 bytes is a key");
    let fake = Info::new(fake_key, Power::try_from(total * 20).unwrap());

    let mut infos: Vec<Info> =
        serde_json::from_str(&common::read("bank_validators_h1.json")).unwrap();
    infos.push(fake);
    let doctored = ValidatorSet::without_proposer(infos);

    let mut trusted = common::bank_trusted_state();
    trusted.next_validators_hash = doctored.hash(); // self-consistent anchor
    trusted.next_validators = doctored;

    let ush = common::skip_signed_header();
    let r = verify_cosmos_header(
        &trusted,
        &ush,
        &common::skip_validators(),
        None,
        TrustThreshold::ONE_THIRD,
        common::trusting_period(),
        common::now_after(&ush),
    );
    assert!(
        matches!(r, Err(HeaderVerifyError::NotEnoughVotingPower(_))),
        "sub-threshold trust overlap must refuse with the bisection signal, got {r:?}"
    );
}

// ------------------------------------------- REJECT: corrupt trusted state

#[test]
fn reject_trusted_set_that_does_not_match_its_commitment() {
    // Same doctored set, but the next_validators_hash is left as the REAL
    // commitment from the trusted header: the relayer-delivered set is not the
    // set the chain committed to. Refused before any overlap tally — otherwise
    // a fake overlap base could vouch for a fake chain.
    let mut infos: Vec<Info> =
        serde_json::from_str(&common::read("bank_validators_h1.json")).unwrap();
    let fake_key = PublicKey::from_raw_ed25519(&[0x42u8; 32]).unwrap();
    infos.push(Info::new(fake_key, Power::try_from(1_000_000u64).unwrap()));

    let mut trusted = common::bank_trusted_state();
    trusted.next_validators = ValidatorSet::without_proposer(infos);
    // trusted.next_validators_hash stays the genuine header commitment.

    let ush = common::skip_signed_header();
    let r = verify_cosmos_header(
        &trusted,
        &ush,
        &common::skip_validators(),
        None,
        TrustThreshold::ONE_THIRD,
        common::trusting_period(),
        common::now_after(&ush),
    );
    assert!(
        matches!(r, Err(HeaderVerifyError::TrustedStateCorrupt(_))),
        "a trusted set that does not hash to its commitment must refuse, got {r:?}"
    );
}

// ------------------------------------- ACCEPT+REJECT: threshold has teeth

/// A self-consistent anchor whose trusted set is the real one DILUTED to
/// exactly 50% overlap: one fabricated validator holding power equal to the
/// whole real total (the fake never signs, so real signers carry exactly 1/2 of
/// the trusted power — every real validator signed the skip-target commit, the
/// fixture was checked).
fn half_overlap_anchor() -> cosmos_lightclient::TrustedCosmosState {
    let real = common::bank_validators_h1();
    let total: u64 = real.total_voting_power.value();
    let fake_key = PublicKey::from_raw_ed25519(&[0x42u8; 32]).unwrap();
    let mut infos: Vec<Info> =
        serde_json::from_str(&common::read("bank_validators_h1.json")).unwrap();
    infos.push(Info::new(fake_key, Power::try_from(total).unwrap()));
    let doctored = ValidatorSet::without_proposer(infos);
    let mut trusted = common::bank_trusted_state();
    trusted.next_validators_hash = doctored.hash();
    trusted.next_validators = doctored;
    trusted
}

#[test]
fn trust_threshold_parameter_has_teeth_at_the_boundary() {
    // Identical anchor + identical skip target; ONLY the threshold differs.
    // 50% overlap: above 1/3 -> verifies; below 2/3 -> refuses.
    let ush = common::skip_signed_header();
    let run = |tt: TrustThreshold| {
        verify_cosmos_header(
            &half_overlap_anchor(),
            &ush,
            &common::skip_validators(),
            None,
            tt,
            common::trusting_period(),
            common::now_after(&ush),
        )
    };
    let at_one_third = run(TrustThreshold::ONE_THIRD);
    assert!(
        at_one_third.is_ok(),
        "50% overlap must satisfy the 1/3 threshold, got {at_one_third:?}"
    );
    let at_two_thirds = run(TrustThreshold::TWO_THIRDS);
    assert!(
        matches!(
            at_two_thirds,
            Err(HeaderVerifyError::NotEnoughVotingPower(_))
        ),
        "50% overlap must refuse the 2/3 threshold, got {at_two_thirds:?}"
    );
}
