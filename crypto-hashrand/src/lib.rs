//! # `crypto-hashrand` — a REFERENCE post-quantum randomness beacon.
//!
//! A HashRand-style hash-based random beacon (Bandarupalli, Bhat, Bagchi,
//! Kate, Reiter — *"HashRand: Efficient Asynchronous Random Beacon without
//! Threshold Cryptographic Setup"*, IACR eprint **2023/1755**, ACM CCS 2024),
//! replacing the classical BLS threshold beacon. It needs only a
//! collision-resistant hash and pairwise secure channels — NO threshold
//! signature, NO distributed key generation, NO pairing, NO group-public key —
//! so it is post-quantum secure under a programmable-QROM model of the hash.
//!
//! This crate is the EXECUTABLE reference for the machine-checked security
//! framework in `metatheory/Dregg2/Crypto/RandomnessBeacon.lean`, which proves
//! the two beacon safety properties (UNBIASABILITY + UNPREDICTABILITY) and
//! reduces both to the single named carrier `HashCR` (hash collision-resistance)
//! — the same carrier the Hermine concurrent-signature argument uses.
//!
//! ## What is implemented — the SYNCHRONOUS commit-then-reveal safety CORE
//!
//! * [`beacon`] — the primitive: `cmᵢ = H(i, cᵢ)` commitments, opening
//!   verification (commit-binding), and the order-free `H(sorted[(i, cᵢ)])`
//!   output combine over the committed contribution multiset. This carries the
//!   two safety properties, matching the Lean framework:
//!   - **Unbiasability** — the output is a deterministic function of the
//!     committed set, and the honest slot is collision-resistant, so an honest
//!     unpredictable contribution the adversary cannot predict makes the output
//!     unbiasable (a coalition below threshold cannot steer it; a bias would be
//!     a hash collision).
//!   - **Unpredictability** — commit-then-reveal: without a revealed honest
//!     `cᵢ` the adversary is reduced to inverting/colliding the hash to predict
//!     the output.
//! * [`channel`] — the pairwise-secure-channel transport seam plus an in-memory
//!   `n`-party reference network with a per-round barrier.
//! * [`ceremony`] — the beacon as a message-passing protocol: a commit round
//!   then a reveal round, the barrier enforcing commit-before-reveal, with
//!   equivocation caught and named.
//!
//! ## HONEST BOUNDARY — what is FLAGGED, not faked
//!
//! This is the SYNCHRONOUS commit-reveal CORE — the unbiasability +
//! unpredictability SAFETY properties, exactly the scope of the Lean framework.
//! It is **not** the full ASYNCHRONOUS HashRand protocol. HashRand's deployment
//! machinery — batched **asynchronous weak Verifiable Secret Sharing**, the
//! **Gather** primitive, and **Approximate Agreement** run Monte-Carlo (a fixed
//! number of rounds, terminating with a tiny tunable AA-`ε` disagreement /
//! failure probability `δ` per beacon) — is the harder ASYNCHRONOUS-AGREEMENT
//! and LIVENESS layer. That layer is deliberately NOT implemented here; it is
//! flagged as the next deployment step, matching the Lean file's documented
//! "Monte-Carlo boundary" (a liveness/agreement boundary of the transport,
//! orthogonal to the two safety properties, which hold whenever a beacon output
//! is produced at all).
//!
//! The programmable-QROM assumption on the hash is the honest cryptographic
//! floor (the beacon's PQ-security rests on it; blake3 is the concrete CR hash
//! — sha3 is an equally valid drop-in carrier). Reference parameters,
//! reference PRNG-derived contributions in tests, not constant-time —
//! **pre-audit, NOT deployment-grade**. The proofs live in, and are cited from,
//! `RandomnessBeacon.lean`.

pub mod beacon;
pub mod ceremony;
pub mod channel;

pub use beacon::{combine, commit, verify_opening, BeaconOutput, Commitment, Contribution};
pub use ceremony::{run_beacon_ceremony, BeaconError, CommitMsg, RevealMsg};
pub use channel::{Channel, ChannelError, LocalChannel, LocalNetwork};
