//! Content addressing (43 §9 `hash.rs`).
//!
//! Two hash roles, both BLAKE3-256:
//! - [`ContentHash::of_bytes`] — a raw CAS blob key, equals `b3sum < file`. REAL
//!   here (it's the one piece with no external dependency on a frozen codec).
//! - [`ContentHash::of_dcbor`] — a domain-separated *structured* id over the dCBOR
//!   canonical encoding of a serde value. The dCBOR codec itself is the named
//!   residual: it must be cross-language-deterministic (JVM/CakeML recompute the
//!   same id, 43 §2), owned by the spec/orchestrator unit. Body is a deferred seam.

use serde::Serialize;

/// BLAKE3-256 content hash. `Ord` so it can key `BTreeMap`s in the corpus index.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ContentHash([u8; 32]);

/// Domain-separation tags so an `Input` hash can never collide with a `Vector`
/// hash even on identical bytes (43 §9).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HashDomain {
    Input,
    Vector,
    Golden,
    Projection,
    Spec,
}

impl HashDomain {
    fn tag(self) -> u8 {
        match self {
            HashDomain::Input => 1,
            HashDomain::Vector => 2,
            HashDomain::Golden => 3,
            HashDomain::Projection => 4,
            HashDomain::Spec => 5,
        }
    }
}

/// The pinned-forever corpus magic + format version (43 §9). Bumping `VERSION`
/// forces a migration that preserves `legacy_ids`.
pub const CORPUS_MAGIC: [u8; 4] = *b"DNVC";
pub const CORPUS_FORMAT_VERSION: u16 = 1;

impl ContentHash {
    /// CAS blob key: raw bytes, no domain tag ⇒ equals `b3sum < file`. REAL.
    pub fn of_bytes(b: &[u8]) -> Self {
        ContentHash(*blake3::hash(b).as_bytes())
    }

    /// Structured id: `H(domain_tag ++ CORPUS_MAGIC ++ version_le ++ dcbor(value))`.
    ///
    /// The dCBOR encode is the cross-language hash preimage codec ([`to_dcbor`]);
    /// its frozen `Canonical` impl is owned by the spec/orchestrator unit (48
    /// residual open question #1). Deferred seam.
    pub fn of_dcbor<T: Serialize>(d: HashDomain, v: &T) -> Self {
        let mut h = blake3::Hasher::new();
        h.update(&[d.tag()]);
        h.update(&CORPUS_MAGIC);
        h.update(&CORPUS_FORMAT_VERSION.to_le_bytes());
        h.update(&to_dcbor(v));
        ContentHash(*h.finalize().as_bytes())
    }

    /// 64-char lowercase hex.
    pub fn to_hex(&self) -> String {
        let mut s = String::with_capacity(64);
        for b in &self.0 {
            s.push(char::from_digit((b >> 4) as u32, 16).unwrap());
            s.push(char::from_digit((b & 0xf) as u32, 16).unwrap());
        }
        s
    }

    /// Parse 64-char lowercase hex.
    pub fn from_hex(s: &str) -> Result<Self, HashParseError> {
        if s.len() != 64 {
            return Err(HashParseError::BadLength(s.len()));
        }
        let mut out = [0u8; 32];
        for (i, byte) in out.iter_mut().enumerate() {
            let hi =
                u8::from_str_radix(&s[2 * i..2 * i + 1], 16).map_err(|_| HashParseError::NotHex)?;
            let lo = u8::from_str_radix(&s[2 * i + 1..2 * i + 2], 16)
                .map_err(|_| HashParseError::NotHex)?;
            *byte = (hi << 4) | lo;
        }
        Ok(ContentHash(out))
    }

    /// First 12 hex chars, for `_blobs/<short>/…` filenames.
    pub fn short(&self) -> String {
        self.to_hex()[..12].to_string()
    }
}

#[derive(Debug)]
pub enum HashParseError {
    BadLength(usize),
    NotHex,
}

/// dCBOR (RFC 8949 §4.2.1 core-deterministic) — the CROSS-LANGUAGE hash preimage
/// codec. The body is the single named residual the JVM (external oracle) and CakeML
/// (model) must reproduce bit-for-bit (43 §2; 48 residual #2). DEFERRED SEAM.
pub fn to_dcbor<T: Serialize>(_v: &T) -> Vec<u8> {
    // The frozen, cross-language-deterministic dCBOR `Canonical` impl is owned by
    // the spec/orchestrator unit. Until it lands, `of_dcbor` ids are unstable —
    // every `VectorId` referencing a `Spec` is at risk of drift (48 open q #1).
    todo!("dCBOR canonical encode — owned by the spec/orchestrator unit (43 §2, 48 residual #1/#2)")
}

// ── the dual hash-role aliases (43 §9) ──────────────────────────────────────────
pub type InputHash = ContentHash; // == of_bytes(raw input)
pub type GoldenHash = ContentHash; // == of_bytes(dcbor(Observation))
pub type SpecId = ContentHash;
pub type ProjectionId = ContentHash;

/// `of_dcbor(Vector, semantic-core)` — EXCLUDES keys/meta so re-keying is
/// identity-stable (43 §2). Loaders MUST NOT trust the stored id; it is recomputed
/// and verified on load ([`Vector::verify_id`](crate::vector::Vector::verify_id)).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct VectorId(pub ContentHash);
