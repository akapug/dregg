//! Shared loaders for the genuine cosmoshub-4 fixtures (see `tests/fixtures/`).
//!
//! The fixtures are REAL mainnet data pulled from `cosmos-rpc.publicnode.com`:
//!   - `commit_h.json`      — SignedHeader at height 31989760 (the trusted anchor)
//!   - `commit_h1.json`     — SignedHeader at height 31989761 (the untrusted advance)
//!   - `validators_h1.json` — the full 180-validator set at height 31989761
//!   - `membership_proof.json` — a genuine ICS-23 proof (uatom bank supply) at
//!     height 31989760, whose app_hash is committed in commit_h1's header.
#![allow(dead_code)]

use base64::engine::general_purpose::STANDARD;
use base64::Engine;
use core::time::Duration;

use cosmos_lightclient::{decode_commitment_proof, CosmosMembershipProof, TrustedCosmosState};
use tendermint::block::signed_header::SignedHeader;
use tendermint::validator::{Info, Set as ValidatorSet};
use tendermint::Time;

const DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures");

pub fn read(name: &str) -> String {
    std::fs::read_to_string(format!("{DIR}/{name}")).expect("fixture present")
}

/// The genuine untrusted SignedHeader at height 31989761 (parses as raw JSON so
/// individual reject tests can also tamper it).
pub fn untrusted_value() -> serde_json::Value {
    serde_json::from_str(&read("commit_h1.json")).unwrap()
}

pub fn signed_header_from(v: &serde_json::Value) -> SignedHeader {
    serde_json::from_value(v.clone()).expect("SignedHeader parses")
}

pub fn untrusted_signed_header() -> SignedHeader {
    signed_header_from(&untrusted_value())
}

pub fn trusted_signed_header() -> SignedHeader {
    serde_json::from_str(&read("commit_h.json")).expect("SignedHeader parses")
}

/// The full validator set at height 31989761 (both the untrusted validators AND
/// the trusted `next_validators`, because 31989761 = 31989760 + 1 is adjacent).
pub fn validators_h1() -> ValidatorSet {
    let infos: Vec<Info> = serde_json::from_str(&read("validators_h1.json")).expect("validators");
    ValidatorSet::without_proposer(infos)
}

/// The trusted anchor state derived from the genuine header at height 31989760.
pub fn trusted_state() -> TrustedCosmosState {
    let th = trusted_signed_header();
    TrustedCosmosState {
        chain_id: th.header.chain_id.clone(),
        header_time: th.header.time,
        height: th.header.height,
        next_validators: validators_h1(),
        next_validators_hash: th.header.next_validators_hash,
    }
}

/// A deterministic `now` shortly after the untrusted header's block time (so the
/// trusting-period / clock-drift checks are anchored to the fixture, not the wall
/// clock).
pub fn now_after_untrusted() -> Time {
    untrusted_signed_header()
        .header
        .time
        .checked_add(Duration::from_secs(60))
        .unwrap()
}

/// A generous trusting period (the fixture header is verified as within it).
pub fn trusting_period() -> Duration {
    Duration::from_secs(14 * 24 * 60 * 60) // 14 days
}

// ---- membership fixtures ----

pub struct MembershipFixture {
    pub app_hash: Vec<u8>,
    pub proof: CosmosMembershipProof,
    pub key: Vec<u8>,
    pub value: Vec<u8>,
}

fn membership_fixture_from(name: &str) -> MembershipFixture {
    let v: serde_json::Value = serde_json::from_str(&read(name)).unwrap();
    let b64 = |k: &str| STANDARD.decode(v[k].as_str().unwrap()).unwrap();
    let app_hash = hex::decode(v["app_hash_hex"].as_str().unwrap()).unwrap();
    let iavl_proof = decode_commitment_proof(&b64("iavl_proof_b64")).unwrap();
    let store_proof = decode_commitment_proof(&b64("simple_proof_b64")).unwrap();
    MembershipFixture {
        app_hash,
        proof: CosmosMembershipProof {
            store_key: v["store_key"].as_str().unwrap().as_bytes().to_vec(),
            iavl_proof,
            store_proof,
        },
        key: b64("iavl_key_b64"),
        value: b64("value_b64"),
    }
}

pub fn membership_fixture() -> MembershipFixture {
    membership_fixture_from("membership_proof.json")
}

// ---- bank-balance + skipping fixture set (a second, self-consistent capture:
// anchor H, adjacent H+1 + its validators, a non-adjacent skip target, and a
// REAL bonded_tokens_pool uatom balance proof at H whose root is the H+1
// app_hash; see each file's `_source`) ----

/// The genuine ICS-23 bank-balance proof (bonded_tokens_pool, uatom) captured
/// at the anchor height; its root is committed as the H+1 header's app_hash.
pub fn bank_balance_fixture() -> MembershipFixture {
    membership_fixture_from("bank_balance_proof.json")
}

pub fn validators_from(name: &str) -> ValidatorSet {
    let infos: Vec<Info> = serde_json::from_str(&read(name)).expect("validators");
    ValidatorSet::without_proposer(infos)
}

fn signed_header(name: &str) -> SignedHeader {
    serde_json::from_str(&read(name)).expect("SignedHeader parses")
}

/// The untrusted adjacent SignedHeader (anchor height + 1) of the bank set.
pub fn bank_untrusted_signed_header() -> SignedHeader {
    signed_header("bank_commit_h1.json")
}

/// The validator set at anchor height + 1 of the bank set (the untrusted
/// adjacent validators AND the anchor's `next_validators`).
pub fn bank_validators_h1() -> ValidatorSet {
    validators_from("bank_validators_h1.json")
}

/// The non-adjacent skip-target SignedHeader (~95 blocks past the anchor).
pub fn skip_signed_header() -> SignedHeader {
    signed_header("skip_commit.json")
}

/// The validator set at the skip-target height.
pub fn skip_validators() -> ValidatorSet {
    validators_from("skip_validators.json")
}

/// The trusted anchor derived from the genuine bank-set anchor header.
pub fn bank_trusted_state() -> TrustedCosmosState {
    let th = signed_header("bank_commit_h.json");
    TrustedCosmosState {
        chain_id: th.header.chain_id.clone(),
        header_time: th.header.time,
        height: th.header.height,
        next_validators: bank_validators_h1(),
        next_validators_hash: th.header.next_validators_hash,
    }
}

/// A deterministic `now` shortly after the given header's block time.
pub fn now_after(sh: &SignedHeader) -> Time {
    sh.header.time.checked_add(Duration::from_secs(60)).unwrap()
}
