//! # `dregg-analyzer` — the forensic/observability lens on a running dregg.
//!
//! A debugging, auditing, and demonstration tool: it ingests CAPTURED TRACES of
//! a running dregg system and analyzes them. Four capture sources, each with a
//! per-source analysis returning a structured [`AnalysisReport`]:
//!
//!   1. **Blocklace** ([`blocklace`]) — the DAG of blocks. Reconstructs causal
//!      order, detects equivocation, surfaces finality progress and
//!      supermajority quorum formation.
//!   2. **Receipts** ([`receipts`]) — the attested who-did-what strand. Verifies
//!      chain integrity and surfaces conservation across the turn history.
//!   3. **WAL** ([`wal`]) — the durable commit log. Replay/recovery + crash
//!      overlay analysis.
//!   4. **Network** ([`network`], optional) — gossip behavior + eclipse-risk.
//!
//! ## The dregg-shaped differentiator: it ATTESTS, it does not just describe.
//!
//! Every analysis that CAN be checked is checked **against the real verifiers**
//! — the same code the running node trusts, not a re-implementation:
//!
//!   * blocklace block signatures, causal closure, and equivocation →
//!     `dregg_blocklace::finality::Blocklace::from_checkpoint` (the node's own
//!     authenticating loader);
//!   * finality / total order → the real `dregg_blocklace::ordering::tau`;
//!   * the quorum threshold → the unified `supermajority_threshold` (#170);
//!   * receipt-chain integrity → the real `dregg_turn::TurnReceipt::receipt_hash`;
//!   * a captured turn forest's conservation / non-amplification →
//!     `dregg_userspace_verify`'s real static-assurance checks.
//!
//! Findings carry an [`findings::Attestation`] so a reader can tell an attested
//! verdict (`Verified { by }`) from a structural observation (`Observed`).

pub mod blocklace;
pub mod findings;
pub mod forest;
pub mod network;
pub mod receipts;
pub mod wal;

#[cfg(test)]
mod tests;

pub use findings::{AnalysisReport, Attestation, Finding, Severity};

/// A captured trace to be analyzed. Tagged so a single `<capture-file>` can be
/// any of the four sources, and `analyze` dispatches on it.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
#[serde(tag = "source", rename_all = "snake_case")]
pub enum Capture {
    Blocklace(blocklace::BlocklaceCapture),
    Receipts(receipts::ReceiptStrandCapture),
    Wal(wal::WalCapture),
    Network(network::NetworkCapture),
    Forest(forest::ForestCapture),
}

/// The forensic analyzer. A thin dispatcher over the per-source analyses; the
/// substance lives in each module (which reuses the real dregg verifiers).
pub struct TraceAnalyzer;

impl TraceAnalyzer {
    /// Analyze any tagged [`Capture`], returning its structured report.
    pub fn analyze(capture: &Capture) -> AnalysisReport {
        match capture {
            Capture::Blocklace(c) => blocklace::analyze(c),
            Capture::Receipts(c) => receipts::analyze(c),
            Capture::Wal(c) => wal::analyze(c),
            Capture::Network(c) => network::analyze(c),
            Capture::Forest(c) => forest::analyze(c),
        }
    }

    pub fn analyze_blocklace(c: &blocklace::BlocklaceCapture) -> AnalysisReport {
        blocklace::analyze(c)
    }
    pub fn analyze_receipts(c: &receipts::ReceiptStrandCapture) -> AnalysisReport {
        receipts::analyze(c)
    }
    pub fn analyze_wal(c: &wal::WalCapture) -> AnalysisReport {
        wal::analyze(c)
    }
    pub fn analyze_network(c: &network::NetworkCapture) -> AnalysisReport {
        network::analyze(c)
    }
    pub fn analyze_forest(c: &forest::ForestCapture) -> AnalysisReport {
        forest::analyze(c)
    }
}
