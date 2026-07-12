//! The **bank-balance edge**: decode a verified Cosmos `bank`-store membership
//! fact into the minimal chain-agnostic foreign-holding fields the governance
//! layer consumes.
//!
//! A Cosmos-SDK account balance lives in the `bank` module store under
//!
//! ```text
//! key   = 0x02 ‖ len(address):u8 ‖ address ‖ denom          (BalancesPrefix)
//! value = the amount — either
//!         · SDK >= v0.46: a `math.Int`, marshalled as its canonical ASCII
//!           decimal string (e.g. b"331305561223899"), or
//!         · SDK <  v0.46 (legacy): a protobuf `sdk.Coin { denom, amount }`
//!           whose `amount` is the same canonical decimal string.
//! ```
//!
//! [`decode_bank_balance_kv`] parses exactly that shape, fail-closed: wrong
//! store, wrong key prefix (a supply key `0x00 ‖ denom` is NOT a balance), an
//! oversized or empty address, a non-SDK denom, a non-canonical amount (empty,
//! signs, leading zeros, non-digits), an amount over `u128` (**refused, never
//! truncated**), or a legacy `Coin` whose denom disagrees with the key's denom.
//!
//! The two value encodings cannot be confused: a marshalled `math.Int` is all
//! ASCII digits, while a protobuf `Coin` always begins with the `0x0a` field-1
//! tag (not a digit) — the digit check routes deterministically.
//!
//! [`foreign_holding_fields`] is the provenance-carrying wrapper: it consumes a
//! [`ProvenCosmosFact`] — which can ONLY exist by passing full Tendermint header
//! verification AND an ICS-23 membership proof (its constructor is private) —
//! pins the expected chain id (two Cosmos chains must never alias into one
//! fact), and produces plain-primitive [`ForeignHoldingFields`]. This crate is
//! standalone: the governance crate's `ProvenForeignHolding` is built from these
//! primitives at its own edge, no dependency in either direction.

use prost::Message;
use sha2::{Digest, Sha256};

use crate::ProvenCosmosFact;

/// The stable one-byte Cosmos chain tag, matching
/// `dregg-governance::proven_foreign_holding::ChainId::Cosmos.tag()` (Solana =
/// 0, Evm = 1, **Cosmos = 2**). Duplicated here as a plain primitive because
/// this crate is standalone; the governance crate's `chain_tags_are_distinct`
/// test pins the enum side. Never reuse or renumber.
pub const COSMOS_CHAIN_TAG: u8 = 2;

/// The bank module's multistore key.
pub const BANK_STORE_KEY: &[u8] = b"bank";

/// The bank store's balances key prefix (`banktypes.BalancesPrefix`). The
/// supply prefix is `0x00` — a supply key is refused by the balance decoder.
pub const BALANCES_PREFIX: u8 = 0x02;

/// Why a bank-balance decode was refused. A refusal NEVER yields holding
/// fields (fail closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BankBalanceError {
    /// The fact's store key is not `bank`.
    NotBankStore,
    /// The key does not begin with the balances prefix `0x02` (e.g. a supply
    /// key `0x00 ‖ denom`, or some other bank index).
    NotBalanceKey,
    /// The key is too short to carry `prefix ‖ len ‖ address ‖ denom`.
    MalformedKey,
    /// The embedded address length is 0 or exceeds 32 bytes (the widest
    /// Cosmos-SDK account address; `holder` is a 32-byte field).
    BadAddressLength(usize),
    /// The denom is not a valid Cosmos-SDK denom
    /// (`[a-zA-Z][a-zA-Z0-9/:._-]{2,127}`).
    BadDenom,
    /// The value is not a canonical amount: empty, non-digit bytes where a
    /// `math.Int` decimal was expected, a leading zero, or an undecodable
    /// legacy `Coin` protobuf.
    MalformedAmount,
    /// The amount is a well-formed decimal that exceeds `u128::MAX` — REFUSED,
    /// never truncated.
    AmountOverflow,
    /// A legacy `sdk.Coin` value whose denom disagrees with the denom in the
    /// key — an inconsistent record is refused, not resolved.
    DenomMismatch,
    /// The fact was proven on a different chain id than the caller pinned
    /// (cross-chain aliasing defense; e.g. a theta-testnet fact presented as
    /// cosmoshub-4).
    ChainIdMismatch { expected: String, actual: String },
}

impl core::fmt::Display for BankBalanceError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BankBalanceError::NotBankStore => f.write_str("fact is not from the bank store"),
            BankBalanceError::NotBalanceKey => f.write_str("key is not a balances-prefix key"),
            BankBalanceError::MalformedKey => f.write_str("malformed bank balance key"),
            BankBalanceError::BadAddressLength(n) => {
                write!(f, "bad address length {n} (must be 1..=32)")
            }
            BankBalanceError::BadDenom => f.write_str("invalid denom in balance key"),
            BankBalanceError::MalformedAmount => f.write_str("malformed balance amount"),
            BankBalanceError::AmountOverflow => {
                f.write_str("balance amount exceeds u128 (refused, never truncated)")
            }
            BankBalanceError::DenomMismatch => {
                f.write_str("legacy Coin denom disagrees with the key's denom")
            }
            BankBalanceError::ChainIdMismatch { expected, actual } => {
                write!(f, "fact chain id {actual:?} is not the pinned {expected:?}")
            }
        }
    }
}

impl std::error::Error for BankBalanceError {}

/// A decoded bank balance: at some proven key, `address` holds `amount` atomic
/// units of `denom`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BankBalance {
    /// The raw account address bytes from the key (1..=32 bytes; 20 for the
    /// usual secp256k1 account, 32 for module/ICA accounts).
    pub address: Vec<u8>,
    /// The denom string from the key (e.g. `uatom`, `ibc/27394FB0...`).
    pub denom: String,
    /// The balance in atomic units. Decoded exactly; an over-`u128` amount was
    /// refused upstream.
    pub amount: u128,
}

/// The minimal chain-agnostic proven-holding fields, as PLAIN PRIMITIVES (this
/// crate deliberately has no governance dependency). Field conventions match
/// `dregg-governance::ProvenForeignHolding`'s Cosmos column:
///
/// - `holder`: the account address, **left-padded with zeros to 32 bytes**
///   (same convention as the EVM 20-byte address padding).
/// - `asset`: the denom commitment — `SHA-256("dregg-cosmos-denom-v1:" ‖ denom)`
///   (denoms can exceed 32 bytes, e.g. `ibc/…` voucher denoms, so a hash, not a
///   padding; see [`cosmos_denom_asset_id`]).
/// - `snapshot`: the VERIFIED header height. The header at height `h` commits
///   the app state produced by executing block `h - 1`, so this is the height
///   whose `app_hash` the balance proof opened into.
/// - `consensus_proven`: `true` — see [`foreign_holding_fields`]; there is no
///   structure-only rung in this crate, a [`ProvenCosmosFact`] cannot exist
///   without full header + membership verification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForeignHoldingFields {
    /// [`COSMOS_CHAIN_TAG`] (= 2), the governance `ChainId::Cosmos` tag.
    pub chain_tag: u8,
    /// The holder identity: the account address, zero-left-padded to 32 bytes.
    pub holder: [u8; 32],
    /// The asset identity: the domain-separated SHA-256 denom commitment.
    pub asset: [u8; 32],
    /// The proven balance in atomic units (an over-`u128` chain value refuses
    /// instead of arriving truncated here).
    pub amount: u128,
    /// The verified header height the balance was proven under.
    pub snapshot: u64,
    /// `true` iff a genuinely header-verified fact backed this — always `true`
    /// for a value produced by [`foreign_holding_fields`], by construction.
    pub consensus_proven: bool,
}

/// The 32-byte asset id for a Cosmos denom:
/// `SHA-256("dregg-cosmos-denom-v1:" ‖ denom)`.
///
/// A hash, not a padding, because IBC voucher denoms (`ibc/<64-hex>`) exceed 32
/// bytes. Domain-separated so a denom commitment can never alias another
/// chain's raw-key asset convention. Deterministic and stable — never change
/// the tag without a new version string.
pub fn cosmos_denom_asset_id(denom: &str) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"dregg-cosmos-denom-v1:");
    h.update(denom.as_bytes());
    h.finalize().into()
}

/// A valid Cosmos-SDK denom: `[a-zA-Z][a-zA-Z0-9/:._-]{2,127}` (the SDK's
/// `reDnmString`).
fn valid_denom(d: &[u8]) -> bool {
    if d.len() < 3 || d.len() > 128 {
        return false;
    }
    if !d[0].is_ascii_alphabetic() {
        return false;
    }
    d[1..]
        .iter()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, b'/' | b':' | b'.' | b'_' | b'-'))
}

/// Parse a canonical `math.Int` decimal: nonempty, ASCII digits only (no sign,
/// no whitespace), no leading zero (except `"0"` itself). Over-`u128` REFUSES.
fn parse_canonical_decimal(b: &[u8]) -> Result<u128, BankBalanceError> {
    if b.is_empty() || !b.iter().all(u8::is_ascii_digit) {
        return Err(BankBalanceError::MalformedAmount);
    }
    if b.len() > 1 && b[0] == b'0' {
        return Err(BankBalanceError::MalformedAmount);
    }
    // All-digits is guaranteed valid UTF-8; `parse::<u128>` on an all-digit
    // string can only fail by overflow — the refuse-never-truncate rule.
    core::str::from_utf8(b)
        .expect("ascii digits are utf-8")
        .parse::<u128>()
        .map_err(|_| BankBalanceError::AmountOverflow)
}

/// The legacy (SDK < v0.46) bank-balance value: a protobuf `cosmos.base.v1beta1.Coin`.
#[derive(Clone, PartialEq, Message)]
struct CoinPb {
    #[prost(string, tag = "1")]
    denom: String,
    #[prost(string, tag = "2")]
    amount: String,
}

/// Decode a bank-balance `(store_key, key, value)` triple into a
/// [`BankBalance`]. Pure parsing over the PROVEN bytes — provenance is the
/// caller's job ([`foreign_holding_fields`] is the fact-consuming wrapper).
/// Every malformation refuses; see [`BankBalanceError`].
pub fn decode_bank_balance_kv(
    store_key: &[u8],
    key: &[u8],
    value: &[u8],
) -> Result<BankBalance, BankBalanceError> {
    if store_key != BANK_STORE_KEY {
        return Err(BankBalanceError::NotBankStore);
    }
    // key = 0x02 ‖ len(address):u8 ‖ address ‖ denom
    if key.is_empty() {
        return Err(BankBalanceError::MalformedKey);
    }
    if key[0] != BALANCES_PREFIX {
        return Err(BankBalanceError::NotBalanceKey);
    }
    if key.len() < 2 {
        return Err(BankBalanceError::MalformedKey);
    }
    let alen = key[1] as usize;
    if alen == 0 || alen > 32 {
        return Err(BankBalanceError::BadAddressLength(alen));
    }
    if key.len() < 2 + alen + 1 {
        return Err(BankBalanceError::MalformedKey);
    }
    let address = key[2..2 + alen].to_vec();
    let denom_bytes = &key[2 + alen..];
    if !valid_denom(denom_bytes) {
        return Err(BankBalanceError::BadDenom);
    }
    let denom = core::str::from_utf8(denom_bytes)
        .expect("valid_denom admits only ascii")
        .to_string();

    // Value: all-ASCII-digits => modern math.Int; otherwise it must be a legacy
    // protobuf Coin (which always starts with the 0x0a field tag, not a digit).
    // An empty value is neither (prost would "decode" it to an empty Coin).
    if value.is_empty() {
        return Err(BankBalanceError::MalformedAmount);
    }
    let amount = if value.iter().all(u8::is_ascii_digit) {
        parse_canonical_decimal(value)?
    } else {
        let coin = CoinPb::decode(value).map_err(|_| BankBalanceError::MalformedAmount)?;
        if coin.denom != denom {
            return Err(BankBalanceError::DenomMismatch);
        }
        parse_canonical_decimal(coin.amount.as_bytes())?
    };

    Ok(BankBalance {
        address,
        denom,
        amount,
    })
}

/// Convert a header-verified bank-balance [`ProvenCosmosFact`] into
/// [`ForeignHoldingFields`], pinning the expected chain id.
///
/// Fail-closed on every edge:
/// - `expected_chain_id` must equal the fact's proven chain id — a fact proven
///   on any other Cosmos chain refuses ([`BankBalanceError::ChainIdMismatch`]).
///   The one-byte `chain_tag` alone cannot distinguish two Cosmos chains, so
///   the pin happens HERE, before the chain-id string is dropped.
/// - the `(store_key, key, value)` decode refuses every malformation,
///   including an over-`u128` amount (never truncated).
///
/// `consensus_proven` is `true` by construction: a [`ProvenCosmosFact`] has a
/// private constructor and can only be produced by
/// [`prove_cosmos_fact`](crate::prove_cosmos_fact), which requires a
/// [`VerifiedHeader`](crate::VerifiedHeader) (>= 2/3-signed, trust-checked) AND
/// a valid ICS-23 membership proof under its `app_hash`. There is no
/// structure-only path through this function.
pub fn foreign_holding_fields(
    fact: &ProvenCosmosFact,
    expected_chain_id: &str,
) -> Result<ForeignHoldingFields, BankBalanceError> {
    if fact.chain_id() != expected_chain_id {
        return Err(BankBalanceError::ChainIdMismatch {
            expected: expected_chain_id.to_string(),
            actual: fact.chain_id().to_string(),
        });
    }
    let bal = decode_bank_balance_kv(fact.store_key(), fact.key(), fact.value())?;
    let mut holder = [0u8; 32];
    holder[32 - bal.address.len()..].copy_from_slice(&bal.address);
    Ok(ForeignHoldingFields {
        chain_tag: COSMOS_CHAIN_TAG,
        holder,
        asset: cosmos_denom_asset_id(&bal.denom),
        amount: bal.amount,
        snapshot: fact.height(),
        consensus_proven: true,
    })
}
