//! # Gate the deployer *without doxxing* — the dreggic differentiator
//!
//! A whitelist gate learns *who* you are. A token-gate learns *what you hold*.
//! The dreggic gate learns **only "gated: true"**. This module is the
//! reveal-nothing layer: the interview arm carries a **hiding commitment** to
//! the verdict, and the launchpad authorizes on *membership* of that commitment
//! in the trusted passed-and-attested set — never seeing the interview content,
//! the transcript, the deployer's identity, or (at the full rung) *which*
//! interview.
//!
//! ## What is REAL in this PoC (the commitment layer)
//!
//! [`verdict_commitment`] is a real hiding commitment: a domain-separated
//! SHA-256 over `(pass, session_nonce, endpoint_binding)`. The nonce hides the
//! verdict (a `PASS`/`FAIL` bit is otherwise trivially guessable), and the
//! endpoint binding pins *which* Opus endpoint conducted the interview. The gate
//! (`GateArm::Interview`) checks the commitment against the trusted set and
//! learns nothing else — [`membership_only_reveals_gated`] demonstrates that the
//! authorization decision is a pure function of "is this commitment in the
//! passed set", carrying no other bit about the interview.
//!
//! This is the same shape as the reveal-nothing property the rest of dregg
//! proves as `View ≈ Sim∘Q` (a verifier's view is simulatable from the
//! public query alone): here the launchpad's view of an interview-gated deploy
//! is simulatable from the single bit "gated", plus the public commitment it was
//! already given.
//!
//! ## What is the NAMED WELD (the full unlinkable ZK)
//!
//! Two sharpenings are designed, not built here, and reuse machinery the repo
//! already has — see [`zktls`]:
//!
//! 1. **Unlinkability across deploys.** Today the gate sees the raw commitment,
//!    so two deploys by the same passed interview are *linkable* by equal
//!    commitments. The weld: prove *membership* of the commitment in the trusted
//!    Merkle set in zero knowledge (a nullifier per deploy for sybil-resistance)
//!    so the gate sees neither the commitment nor a link — exactly
//!    `chain/contracts/DreggCredentialGate.sol`'s anonymous-credential flow
//!    (ring membership + predicate, unlinkable presentations, per-action
//!    nullifier), with predicate = `keccak256("interview-passed")`.
//!
//! 2. **Attestation the interview was real.** A commitment alone is a bare
//!    assertion. The weld: a **zkTLS/DECO** proof that the interview session ran
//!    against the *real* Opus endpoint and the verdict channel returned PASS,
//!    revealing nothing about the transcript — reusing the repo's DECO/TLSNotary
//!    carrier (`zkoracle-prove`). See [`zktls`].

use sha2::{Digest, Sha256};

/// A 32-byte hiding commitment to an interview verdict.
pub type VerdictCommitment = [u8; 32];

/// Compute the hiding commitment carried by [`crate::GateArm::Interview`].
///
/// - `pass` — the verdict bit. Only `true` (PASS) is ever admitted to the
///   trusted set; a FAIL commits to a value the operator will never trust.
/// - `session_nonce` — high-entropy per-interview randomness. Without it the
///   commitment of a `PASS` would be a guessable constant; with it the
///   commitment reveals nothing about the verdict to anyone lacking the nonce.
/// - `endpoint_binding` — pins the Opus endpoint / model id that conducted the
///   interview (e.g. a hash of the served TLS cert + model header). This is the
///   handle the zkTLS attestation ([`zktls`]) binds to, so a commitment cannot
///   be minted from an interview with a *pushover* model.
pub fn verdict_commitment(
    pass: bool,
    session_nonce: &[u8; 32],
    endpoint_binding: &[u8],
) -> VerdictCommitment {
    let mut h = Sha256::new();
    h.update(b"dregg-deployer-gate/interview-verdict/v1");
    h.update([pass as u8]);
    h.update(session_nonce);
    h.update((endpoint_binding.len() as u64).to_le_bytes());
    h.update(endpoint_binding);
    h.finalize().into()
}

/// The gate's *entire* view of an interview-gated deploy: one bit. Given the
/// trusted set and a presented commitment, the authorization decision is
/// `set.contains(commitment)` — it is a pure function of membership and carries
/// no other information about the interview (content, score, identity). This is
/// the `View ≈ Sim∘Q` shape at the commitment rung: the view is simulatable
/// from "gated" alone.
pub fn membership_only_reveals_gated(
    trusted_passed: &std::collections::HashSet<VerdictCommitment>,
    presented: &VerdictCommitment,
) -> bool {
    trusted_passed.contains(presented)
}

/// # zkTLS / DECO attestation — the named weld (the private-attestation carrier)
///
/// The commitment layer above proves the deployer *holds* a passed-interview
/// handle without revealing its content. The remaining weld is proving the
/// handle is **genuine** — that the interview truly happened against the real
/// Opus 4.8 endpoint and returned PASS — *without* revealing the transcript.
/// That is precisely what the repo's DECO/TLSNotary carrier does for any TLS
/// session, and it is reused here rather than reinvented.
///
/// ## The carrier that exists (`zkoracle-prove`)
///
/// `zkoracle-prove` (a root-workspace crate) already proves facts about a real
/// HTTPS response under MPC-TLS / TLSNotary, revealing only a committed span:
/// - `zkoracle_prove::attestation::prove_zkoracle(..) -> ZkOracleAttestation`
/// - `zkoracle_prove::attestation::verify_zkoracle(..) -> VerifiedZkOracle`
/// - `zkoracle_prove::attestation::content_commitment(response_body) -> BabyBear`
/// - `FieldSpan::extract` selectively opens *only* the verdict field of the
///   response, keeping the rest of the transcript hidden.
/// - the STARK leg (`prove_zkoracle_with_stark`) folds it into the dregg proof
///   tower (the memory's "DECO-proven custom-leaf fold").
///
/// ## The wire (design)
///
/// 1. The deployer runs the interview against the operator's Opus-4.8 endpoint
///    over TLS, with a TLSNotary/DECO session in the loop.
/// 2. The verdict channel returns the structured block (`VERDICT: PASS ...`).
/// 3. `prove_zkoracle` attests the session: the response came from the pinned
///    endpoint (`endpoint_binding`) and a `FieldSpan` over the `VERDICT:` field
///    opens to `PASS` — **revealing nothing else** about the transcript.
/// 4. The attestation's `content_commitment` becomes the
///    [`verdict_commitment`]'s attested handle; the operator admits it to the
///    trusted set. On-chain, the same fact rides `DreggCredentialGate`.
///
/// This module is intentionally documentation + type-shape only: wiring the
/// live MPC-TLS session to the Opus endpoint is the named build, and pulling the
/// full `tlsn` stack into this standalone PoC crate is deliberately deferred so
/// the capability-gate PoC stays light and self-contained. The carrier is real
/// and cited; the interview→attestation wire is the honest weld.
pub mod zktls {
    /// The shape of a zkTLS-attested interview handle, mirroring what
    /// `zkoracle_prove::attestation::ZkOracleAttestation` carries. Constructing
    /// one from a live session is the named weld; verifying its shape is real.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct AttestedInterview {
        /// Pins the Opus endpoint the DECO session ran against (cert+model hash).
        pub endpoint_binding: Vec<u8>,
        /// The opened verdict field — must be `PASS` to be admissible.
        pub verdict_field: String,
        /// The DECO/TLSNotary content commitment over the (hidden) transcript,
        /// the handle admitted to the trusted set. In the built system this is
        /// `zkoracle_prove::attestation::content_commitment(..)`.
        pub content_commitment: [u8; 32],
    }

    impl AttestedInterview {
        /// A zkTLS-attested interview is admissible iff its opened verdict field
        /// is `PASS`. (Endpoint-binding validity is checked by `verify_zkoracle`
        /// in the built carrier.)
        pub fn is_admissible(&self) -> bool {
            self.verdict_field.trim() == "PASS"
        }
    }
}
