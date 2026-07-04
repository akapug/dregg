//! The shared finding/verdict vocabulary every per-source analysis speaks.
//!
//! An analysis does not *describe* — it *attests*. Each [`Finding`] carries a
//! [`Severity`] and, crucially, an [`Attestation`] saying whether the claim was
//! checked against a REAL dregg verifier (the same code the running node uses)
//! or is a structural observation the analyzer derived itself. The
//! differentiator of this tool is that the load-bearing verdicts are
//! `Attestation::Verified` — backed by `dregg_blocklace`'s real signature /
//! `tau` / quorum code, `dregg_turn`'s real `receipt_hash()`, and
//! `dregg_userspace_verify`'s real conservation/amplification checks.

use serde::{Deserialize, Serialize};

/// How serious a finding is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Severity {
    /// Informational summary — no problem, just a surfaced fact.
    Info,
    /// A soft signal worth a human's attention (e.g. an eclipse-risk hint).
    Notice,
    /// A genuine integrity violation: tampering, equivocation, non-conservation,
    /// a torn WAL. The capture is NOT clean.
    Critical,
}

/// Whether a finding is backed by a real dregg verifier or is the analyzer's
/// own structural derivation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Attestation {
    /// Checked by REUSING the running system's own verifier — the same code the
    /// node trusts. This is the tool's whole point: it does not re-implement the
    /// check, it runs it.
    Verified {
        /// The verifier reused, e.g. `"dregg_blocklace::finality::Block::verify_signature"`.
        by: String,
    },
    /// A structural observation the analyzer derived itself (causal-order
    /// reconstruction, an eclipse-risk heuristic). Honest about not being a
    /// cryptographic attestation.
    Observed,
}

/// One finding from an analysis: what, how serious, and whether attested.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Finding {
    pub severity: Severity,
    pub attestation: Attestation,
    /// A short machine-stable code, e.g. `"blocklace.equivocation"`.
    pub code: String,
    /// Human-readable explanation.
    pub message: String,
}

impl Finding {
    pub fn verified(
        severity: Severity,
        by: impl Into<String>,
        code: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Finding {
            severity,
            attestation: Attestation::Verified { by: by.into() },
            code: code.into(),
            message: message.into(),
        }
    }

    pub fn observed(
        severity: Severity,
        code: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Finding {
            severity,
            attestation: Attestation::Observed,
            code: code.into(),
            message: message.into(),
        }
    }

    /// Whether this finding is `Verified` (backed by a real dregg verifier).
    pub fn is_verified(&self) -> bool {
        matches!(self.attestation, Attestation::Verified { .. })
    }
}

/// The structured result of analyzing one capture source.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnalysisReport {
    /// Which source this report covers, e.g. `"blocklace"`.
    pub source: String,
    /// Key/value summary facts (block count, quorum threshold, chain length…).
    pub summary: Vec<(String, String)>,
    /// All findings (anomalies + verified verdicts + info).
    pub findings: Vec<Finding>,
}

impl AnalysisReport {
    pub fn new(source: impl Into<String>) -> Self {
        AnalysisReport {
            source: source.into(),
            summary: Vec::new(),
            findings: Vec::new(),
        }
    }

    pub fn summarize(&mut self, key: impl Into<String>, value: impl ToString) {
        self.summary.push((key.into(), value.to_string()));
    }

    pub fn push(&mut self, f: Finding) {
        self.findings.push(f);
    }

    /// The most severe severity across findings (`Info` if none).
    pub fn worst(&self) -> Severity {
        self.findings
            .iter()
            .map(|f| f.severity)
            .max()
            .unwrap_or(Severity::Info)
    }

    /// `true` iff no `Critical` finding is present — i.e. the capture passed
    /// every integrity check.
    pub fn is_clean(&self) -> bool {
        self.worst() < Severity::Critical
    }

    /// Count of findings backed by a real dregg verifier (the attested core).
    pub fn verified_count(&self) -> usize {
        self.findings.iter().filter(|f| f.is_verified()).count()
    }

    /// A one-line verdict for a human / CLI footer.
    pub fn verdict_line(&self) -> String {
        let critical = self
            .findings
            .iter()
            .filter(|f| f.severity == Severity::Critical)
            .count();
        if critical == 0 {
            format!(
                "CLEAN — {} finding(s), {} verified against real dregg verifiers",
                self.findings.len(),
                self.verified_count()
            )
        } else {
            format!(
                "ANOMALOUS — {critical} critical finding(s) ({} total, {} verified)",
                self.findings.len(),
                self.verified_count()
            )
        }
    }
}

/// Short hex of a 32-byte id (first 8 bytes), the consistent way the analyzer
/// names blocks/cells/hashes in messages.
pub fn short_hex(b: &[u8]) -> String {
    let n = b.len().min(8);
    let mut s = String::with_capacity(n * 2);
    for byte in &b[..n] {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}
