//! Bank-balance decode KATs, BOTH polarities, all default-run.
//!
//! ACCEPT: a REAL cosmoshub-4 bank-balance membership (the bonded_tokens_pool
//! module account's uatom balance, captured live with `prove=true`) flows the
//! whole socket: genuine header advance (>= 2/3 Ed25519-verified voting power)
//! -> app_hash -> ICS-23 proof -> `ProvenCosmosFact` -> decoded
//! `ForeignHoldingFields` with the exact on-chain amount.
//!
//! REJECT (fail-closed): a tampered value never binds a fact; an over-u128
//! amount REFUSES (never truncates); a supply key is not a balance; wrong
//! store; malformed keys/addresses/denoms/amounts; a legacy `Coin` value with a
//! mismatched denom; a fact from the wrong chain id.

mod common;

use cosmos_lightclient::{
    cosmos_denom_asset_id, decode_bank_balance_kv, foreign_holding_fields, prove_cosmos_fact,
    verify_cosmos_header, BankBalanceError, MembershipError, ProvenCosmosFact, COSMOS_CHAIN_TAG,
};
use prost::Message;
use tendermint_light_client_verifier::types::TrustThreshold;

/// The bonded_tokens_pool account (cosmos1fl48vsnmsdzcv85q5d2q4z5ajdha8yu34mf0eh).
const HOLDER_ADDR: [u8; 20] = [
    0x4f, 0xea, 0x76, 0x42, 0x7b, 0x83, 0x45, 0x86, 0x1e, 0x80, 0xa3, 0x54, 0x0a, 0x8a, 0x9d, 0x93,
    0x6f, 0xd3, 0x93, 0x91,
];

fn balance_key(addr: &[u8], denom: &str) -> Vec<u8> {
    let mut k = vec![0x02, addr.len() as u8];
    k.extend_from_slice(addr);
    k.extend_from_slice(denom.as_bytes());
    k
}

/// Verify the REAL adjacent header advance of the bank fixture set and bind the
/// REAL balance proof into a fact — the only way a `ProvenCosmosFact` can exist.
fn real_balance_fact() -> ProvenCosmosFact {
    let ush = common::bank_untrusted_signed_header();
    let header = verify_cosmos_header(
        &common::bank_trusted_state(),
        &ush,
        &common::bank_validators_h1(),
        None,
        TrustThreshold::TWO_THIRDS,
        common::trusting_period(),
        common::now_after(&ush),
    )
    .expect("genuine cosmoshub-4 header verifies");
    let f = common::bank_balance_fixture();
    assert_eq!(
        header.app_hash(),
        f.app_hash.as_slice(),
        "the H+1 header commits the state the balance proof opens"
    );
    prove_cosmos_fact(&header, &f.proof, &f.key, &f.value)
        .expect("genuine bank-balance proof binds a fact")
}

// ---------------------------------------------------------------- ACCEPT KAT

#[test]
fn accept_real_bank_balance_decodes_to_holding_fields() {
    let fact = real_balance_fact();
    assert_eq!(fact.chain_id(), "cosmoshub-4");
    assert_eq!(fact.store_key(), b"bank");
    // The REAL on-chain value: the canonical math.Int decimal string.
    assert_eq!(fact.value(), b"331305561223899");

    let fields = foreign_holding_fields(&fact, "cosmoshub-4").expect("balance fact decodes");

    assert_eq!(fields.chain_tag, COSMOS_CHAIN_TAG);
    assert_eq!(
        fields.chain_tag, 2,
        "the dregg-governance ChainId::Cosmos tag"
    );
    // holder = the 20-byte account address zero-left-padded to 32.
    let mut expect_holder = [0u8; 32];
    expect_holder[12..].copy_from_slice(&HOLDER_ADDR);
    assert_eq!(fields.holder, expect_holder);
    // asset = the documented denom commitment.
    assert_eq!(fields.asset, cosmos_denom_asset_id("uatom"));
    assert_ne!(fields.asset, [0u8; 32]);
    assert_ne!(
        fields.asset,
        cosmos_denom_asset_id("uosmo"),
        "distinct denoms are distinct assets"
    );
    // The exact proven amount, and the verified header height as the snapshot.
    assert_eq!(fields.amount, 331_305_561_223_899u128);
    assert_eq!(fields.snapshot, fact.height());
    assert_eq!(fields.snapshot, 31_992_690);
    assert!(fields.consensus_proven);
}

// ------------------------------------------------- REJECT: tampered value

#[test]
fn reject_tampered_balance_value_never_binds() {
    let ush = common::bank_untrusted_signed_header();
    let header = verify_cosmos_header(
        &common::bank_trusted_state(),
        &ush,
        &common::bank_validators_h1(),
        None,
        TrustThreshold::TWO_THIRDS,
        common::trusting_period(),
        common::now_after(&ush),
    )
    .unwrap();
    let f = common::bank_balance_fixture();
    let mut inflated = f.value.clone();
    inflated[0] = b'9'; // claim a bigger balance than the chain committed
    let r = prove_cosmos_fact(&header, &f.proof, &f.key, &inflated);
    assert_eq!(
        r,
        Err(MembershipError::IavlProofInvalid),
        "an inflated balance value must never bind a fact"
    );
}

// ---------------------------------------------- REJECT: wrong chain pinned

#[test]
fn reject_fact_from_unpinned_chain_id() {
    let fact = real_balance_fact();
    let r = foreign_holding_fields(&fact, "osmosis-1");
    assert!(
        matches!(r, Err(BankBalanceError::ChainIdMismatch { .. })),
        "a cosmoshub-4 fact must not decode under an osmosis-1 pin, got {r:?}"
    );
}

// -------------------------------------------------- kv decoder: boundaries

#[test]
fn accept_u128_max_boundary() {
    let key = balance_key(&HOLDER_ADDR, "uatom");
    let v = u128::MAX.to_string();
    let b = decode_bank_balance_kv(b"bank", &key, v.as_bytes()).expect("u128::MAX is in range");
    assert_eq!(b.amount, u128::MAX);
    assert_eq!(b.address, HOLDER_ADDR.to_vec());
    assert_eq!(b.denom, "uatom");
}

#[test]
fn reject_over_u128_amount_never_truncates() {
    let key = balance_key(&HOLDER_ADDR, "uatom");
    // u128::MAX + 1 — one past the boundary.
    let over = "340282366920938463463374607431768211456";
    assert_eq!(
        decode_bank_balance_kv(b"bank", &key, over.as_bytes()),
        Err(BankBalanceError::AmountOverflow)
    );
    // A absurdly wide amount refuses the same way (not truncated mod 2^128).
    let huge = "9".repeat(80);
    assert_eq!(
        decode_bank_balance_kv(b"bank", &key, huge.as_bytes()),
        Err(BankBalanceError::AmountOverflow)
    );
}

// ------------------------------------------------ kv decoder: malformations

#[test]
fn reject_malformed_amounts() {
    let key = balance_key(&HOLDER_ADDR, "uatom");
    for bad in [
        &b""[..],      // empty
        b"+123",       // sign
        b"-1",         // sign
        b"12 3",       // whitespace
        b"0123",       // leading zero (non-canonical Int)
        b"00",         // leading zero
        b"12a4",       // non-digit, and not a decodable legacy Coin
        b"\xffnot-pb", // garbage bytes
    ] {
        let r = decode_bank_balance_kv(b"bank", &key, bad);
        assert_eq!(
            r,
            Err(BankBalanceError::MalformedAmount),
            "value {bad:?} must refuse"
        );
    }
}

#[test]
fn reject_supply_key_as_balance() {
    // The REAL uatom supply key from the supply fixture: 0x00 ‖ "uatom" — a
    // supply record must never decode as someone's balance.
    let supply = common::membership_fixture();
    assert_eq!(supply.key[0], 0x00);
    let r = decode_bank_balance_kv(b"bank", &supply.key, &supply.value);
    assert_eq!(r, Err(BankBalanceError::NotBalanceKey));
}

#[test]
fn reject_wrong_store_key() {
    let key = balance_key(&HOLDER_ADDR, "uatom");
    assert_eq!(
        decode_bank_balance_kv(b"staking", &key, b"123"),
        Err(BankBalanceError::NotBankStore)
    );
}

#[test]
fn reject_bad_address_lengths() {
    // Zero-length address.
    let mut k0 = vec![0x02, 0x00];
    k0.extend_from_slice(b"uatom");
    assert_eq!(
        decode_bank_balance_kv(b"bank", &k0, b"1"),
        Err(BankBalanceError::BadAddressLength(0))
    );
    // 33-byte address exceeds the 32-byte holder field: REFUSE, never crop.
    let addr33 = [7u8; 33];
    let k33 = balance_key(&addr33, "uatom");
    assert_eq!(
        decode_bank_balance_kv(b"bank", &k33, b"1"),
        Err(BankBalanceError::BadAddressLength(33))
    );
    // Length byte pointing past the key end.
    let short = vec![0x02, 0x14, 0xAA, 0xBB];
    assert_eq!(
        decode_bank_balance_kv(b"bank", &short, b"1"),
        Err(BankBalanceError::MalformedKey)
    );
}

#[test]
fn reject_bad_denoms() {
    for bad in ["ab", "u@tom", "1atom", " uatom"] {
        let key = balance_key(&HOLDER_ADDR, bad);
        assert_eq!(
            decode_bank_balance_kv(b"bank", &key, b"1"),
            Err(BankBalanceError::BadDenom),
            "denom {bad:?} must refuse"
        );
    }
    // Missing denom entirely.
    let mut k = vec![0x02, 20];
    k.extend_from_slice(&HOLDER_ADDR);
    assert_eq!(
        decode_bank_balance_kv(b"bank", &k, b"1"),
        Err(BankBalanceError::MalformedKey)
    );
}

#[test]
fn accept_ibc_voucher_denom_hashes_into_asset() {
    // A real-shaped IBC voucher denom (longer than 32 bytes -> the hash
    // convention is load-bearing, not a padding).
    let denom = "ibc/27394FB092D2ECCD56123C74F36E4C1F926001CEADA9CA97EA622B25F41E5EB2";
    assert!(denom.len() > 32);
    let key = balance_key(&HOLDER_ADDR, denom);
    let b = decode_bank_balance_kv(b"bank", &key, b"5").expect("ibc denom decodes");
    assert_eq!(b.denom, denom);
    assert_eq!(cosmos_denom_asset_id(denom).len(), 32);
}

// ------------------------------------------------ kv decoder: legacy sdk.Coin

/// The legacy (SDK < v0.46) bank value: protobuf `cosmos.base.v1beta1.Coin`.
/// (An encoder for building test INPUT bytes; the crate's decoder is the
/// system under test.)
#[derive(Clone, PartialEq, Message)]
struct CoinEnc {
    #[prost(string, tag = "1")]
    denom: String,
    #[prost(string, tag = "2")]
    amount: String,
}

fn coin_bytes(denom: &str, amount: &str) -> Vec<u8> {
    CoinEnc {
        denom: denom.to_string(),
        amount: amount.to_string(),
    }
    .encode_to_vec()
}

#[test]
fn accept_legacy_coin_value() {
    let key = balance_key(&HOLDER_ADDR, "uatom");
    let b = decode_bank_balance_kv(b"bank", &key, &coin_bytes("uatom", "123456"))
        .expect("legacy Coin decodes");
    assert_eq!(b.amount, 123_456);
    assert_eq!(b.denom, "uatom");
}

#[test]
fn reject_legacy_coin_denom_mismatch() {
    let key = balance_key(&HOLDER_ADDR, "uatom");
    let r = decode_bank_balance_kv(b"bank", &key, &coin_bytes("uosmo", "123456"));
    assert_eq!(
        r,
        Err(BankBalanceError::DenomMismatch),
        "a Coin whose denom disagrees with the key must refuse"
    );
}

#[test]
fn reject_legacy_coin_over_u128() {
    let key = balance_key(&HOLDER_ADDR, "uatom");
    let over = "340282366920938463463374607431768211456"; // u128::MAX + 1
    let r = decode_bank_balance_kv(b"bank", &key, &coin_bytes("uatom", over));
    assert_eq!(r, Err(BankBalanceError::AmountOverflow));
}
