//! # dregg-redteam — adversarial harness
//!
//! This crate property-tests the **running Rust** against the invariants that
//! `Dregg2/` (Lean) *proves* about the abstract model. The thesis (per the
//! threat-model doc) is: a divergence between "Lean proves X" and "the Rust
//! enforces X" is a real bug. So each module here picks a proven invariant,
//! constructs an adversary that tries to *break it on the concrete code*, and
//! asserts the outcome.
//!
//! Outcome semantics (deliberately ruthless):
//! - An attack that **succeeds** at violating a claimed invariant is a FINDING
//!   (a failing test, or a test asserting the bad outcome with a `// FINDING`).
//! - An attack that **fails** is EVIDENCE the property holds operationally
//!   (a passing test asserting the safe rejection).
//!
//! The shared helpers below are the adversary's toolkit: keypair minting,
//! tampering primitives, and the ed25519 malleability gadget used by the
//! blocklace equivocation-framing attack.

use ed25519_dalek::SigningKey as DalekSigningKey;

/// Mint a fresh ed25519 keypair as raw 32-byte seed material + the dalek key.
///
/// Returns the dalek signing key (for direct low-level signing in the
/// malleability attack) alongside the 32-byte verifying-key bytes.
pub fn mint_dalek_keypair() -> (DalekSigningKey, [u8; 32]) {
    let mut seed = [0u8; 32];
    getrandom::fill(&mut seed).expect("getrandom");
    let sk = DalekSigningKey::from_bytes(&seed);
    let vk = sk.verifying_key().to_bytes();
    (sk, vk)
}

/// Flip a single bit in a byte buffer (in place). Used to tamper ciphertext /
/// signatures / certificate fields and observe whether the verifier rejects.
pub fn flip_bit(buf: &mut [u8], byte: usize, bit: u8) {
    if byte < buf.len() {
        buf[byte] ^= 1 << (bit & 7);
    }
}

/// Classify an attack outcome for the summary table the harness prints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AttackOutcome {
    /// The invariant held: the system rejected/no-op'd the attack. Evidence.
    Defended,
    /// The attack succeeded in violating a claimed invariant. A FINDING.
    Broken,
    /// The attack revealed an information leak (not a safety break, but a
    /// confidentiality/metadata observation).
    Leak,
}

impl std::fmt::Display for AttackOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AttackOutcome::Defended => write!(f, "DEFENDED (evidence property holds)"),
            AttackOutcome::Broken => write!(f, "BROKEN (FINDING)"),
            AttackOutcome::Leak => write!(f, "LEAK (FINDING)"),
        }
    }
}
