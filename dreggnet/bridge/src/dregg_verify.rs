//! The named wire to a REAL dregg lease — the light-client verified read of a
//! dregg node's committed receipt log (funded execution-lease grants → a
//! [`crate::Lease`]).
//!
//! At this rung the [`crate::Lease`] is a MOCK struct fed by the local feeds
//! ([`crate::watch`]). The verified on-chain read — decode a funded
//! execution-lease grant from a dregg node's receipt log, after attesting the
//! whole log against its committed MMR root (fail-closed) — is a **named SEAM**.
//!
//! # Status: an honest, fail-closed seam
//!
//! The verified-read wire binds against the dregg verified-core surface (the
//! cap-gate `gate_effect_set`, the chained `witness_receipt`, and the
//! non-omitting `query_shadow_attest_whole_log` whole-log attestation). An
//! earlier iteration reached that surface through an EXTERNAL adapter that
//! re-exported the pinned `emberian/dregg` crates; that external engine is no
//! longer part of DreggNet.
//!
//! The wire is now an OWNED `dregg-verify` dependency to be brought in directly
//! (a first-party dep on the dregg verified core, not an external submodule
//! re-export). Until that lands, [`DREGG_VERIFY_ENABLED`] is `false` and the
//! verified read fails closed — the bridge fulfills leases from the local feeds
//! only, never from an un-verified on-chain read. See `docs/COMPUTE-TIERS.md`.
//!
//! # LICENSE
//!
//! `emberian/dregg` is **AGPL-3.0-or-later**; DreggNet is itself AGPL-3.0, so an
//! owned dep on the dregg verified core is an AGPL combined work (compatible, but
//! the AGPL obligation attaches). The verified-read wire is the deliberate,
//! documented flip-on step, not a silent default dependency.

/// Whether this build links the dregg verified-core read surface. `false` today:
/// the verified on-chain lease read is an honest, fail-closed named seam (the
/// owned `dregg-verify` dep is future work). The bridge fulfills leases from the
/// local feeds only until this flips true.
pub const DREGG_VERIFY_ENABLED: bool = false;

/// The pinned `emberian/dregg` rev the owned verified-read wire would bind
/// against — recorded so the version the bridge meets is explicit even before the
/// dep is taken.
pub const DREGG_BRIDGE_REV: &str = "a0a0a019692870d9ec992744042de2df8c19be0c";

/// The dregg verified-core surface functions the owned verified-read wire lands
/// on. (Documentation constant — the actual symbols become available once the
/// owned `dregg-verify` dep is taken.)
pub const DREGG_BRIDGE_SURFACE: &[&str] = &[
    "gate_effect_set",  // cap-grade attenuation check (the real GradeBelowFloor gate)
    "gate_auth",        // auth-kind attenuation
    "witness_receipt",  // witness a metered step as a chained dregg receipt
    "attest_whole_log", // build a verifiable attestation over the receipt log
    "answer_whole_log", // answer a query over the attested log
    "query_shadow_attest_whole_log", // read+attest committed lease state (the lease read)
];

#[cfg(test)]
mod tests {
    use super::*;

    /// The verified-read wire is an honest, fail-closed seam on every build: no
    /// on-chain lease is trusted without the owned verified-core dep.
    #[test]
    fn verified_read_is_a_fail_closed_seam() {
        assert!(!DREGG_VERIFY_ENABLED);
        assert!(DREGG_BRIDGE_SURFACE.contains(&"query_shadow_attest_whole_log"));
    }
}
