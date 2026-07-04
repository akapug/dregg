//! `takedown` — the abuse-report intake + the suspended-resource registry.
//!
//! The moderation MECHANISM (the live report intake form, the operator-review UI,
//! and the actual moderation POLICY are reviewed-go — ember/legal's call). This
//! module is the enforceable state:
//!
//! - an [`AbuseReport`] is the typed intake (who reported what, and why);
//! - the [`SuspensionRegistry`] tracks which resources are suspended and the
//!   owner-readable reason, so the data plane can ask `is_suspended(id)` and stop
//!   serving/running a taken-down resource.
//!
//! The act of suspending is sealed as a receipted governance turn by the
//! [`crate::Guard`] (the [`crate::governance::GovernanceLog`]); this module holds
//! only the fast-path enforcement state the serving loop reads.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::quota::Countable;

/// A filed abuse report — the intake record. Recording one takes no action by
/// itself; review (operator or an automated signal) decides whether to suspend.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AbuseReport {
    /// The resource reported (a site/server/agent/bucket/domain id).
    pub resource_id: String,
    /// What kind of resource it is.
    pub kind: Countable,
    /// The owning account (`dga1_`-derived subject), if known at report time.
    pub subject: Option<String>,
    /// Who/what filed it: a reporter label (an email-hash, a user subject, or an
    /// `automated:<signal>` source). Free-form — the intake is mechanism, not policy.
    pub reporter: String,
    /// The stated reason / category (e.g. "phishing", "malware", "csam", "spam").
    pub reason: String,
    /// When it was filed (unix seconds).
    pub at: i64,
}

/// The live suspension state of one resource.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Suspension {
    /// The owning account subject.
    pub subject: String,
    /// The owner-readable reason the resource was taken down.
    pub reason: String,
    /// Who took it down (operator subject or `automated:<signal>`).
    pub actor: String,
    /// When (unix seconds).
    pub at: i64,
}

/// The suspended-resource registry: the fast-path state the serving/running loop
/// consults to refuse a taken-down resource. Holds the filed reports too (for
/// the operator-review queue — the reviewed-go UI renders these).
#[derive(Default)]
pub struct SuspensionRegistry {
    suspended: HashMap<String, Suspension>,
    reports: Vec<AbuseReport>,
}

impl SuspensionRegistry {
    /// A fresh registry.
    pub fn new() -> SuspensionRegistry {
        SuspensionRegistry::default()
    }

    /// File an abuse report (intake only — no enforcement). Returns the report's
    /// index in the review queue.
    pub fn file_report(&mut self, report: AbuseReport) -> usize {
        self.reports.push(report);
        self.reports.len() - 1
    }

    /// The pending review queue (every filed report).
    pub fn reports(&self) -> &[AbuseReport] {
        &self.reports
    }

    /// Mark a resource suspended (it stops serving/running). Idempotent — a
    /// second suspend overwrites the reason/actor.
    pub fn suspend(&mut self, resource_id: impl Into<String>, suspension: Suspension) {
        self.suspended.insert(resource_id.into(), suspension);
    }

    /// Lift a suspension (reinstate the resource). Returns whether it was suspended.
    pub fn reinstate(&mut self, resource_id: &str) -> bool {
        self.suspended.remove(resource_id).is_some()
    }

    /// Whether a resource is currently suspended — the data plane's gate.
    pub fn is_suspended(&self, resource_id: &str) -> bool {
        self.suspended.contains_key(resource_id)
    }

    /// The owner-readable reason a resource was taken down (for the console).
    pub fn reason(&self, resource_id: &str) -> Option<&str> {
        self.suspended.get(resource_id).map(|s| s.reason.as_str())
    }

    /// The full suspension record for a resource.
    pub fn suspension(&self, resource_id: &str) -> Option<&Suspension> {
        self.suspended.get(resource_id)
    }

    /// How many resources are currently suspended.
    pub fn suspended_count(&self) -> usize {
        self.suspended.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn report_intake_takes_no_action() {
        let mut reg = SuspensionRegistry::new();
        reg.file_report(AbuseReport {
            resource_id: "site_x".into(),
            kind: Countable::Site,
            subject: Some("dregg:a".into()),
            reporter: "automated:phish-scan".into(),
            reason: "phishing".into(),
            at: 1000,
        });
        // a report alone does NOT suspend — review is the operator's call.
        assert!(!reg.is_suspended("site_x"));
        assert_eq!(reg.reports().len(), 1);
    }

    #[test]
    fn suspend_stops_serving_and_exposes_the_reason() {
        let mut reg = SuspensionRegistry::new();
        reg.suspend(
            "site_x",
            Suspension {
                subject: "dregg:a".into(),
                reason: "confirmed phishing kit".into(),
                actor: "dregg:operator1".into(),
                at: 1100,
            },
        );
        assert!(reg.is_suspended("site_x"));
        // the owner can read why.
        assert_eq!(reg.reason("site_x"), Some("confirmed phishing kit"));
        // reinstate lifts it.
        assert!(reg.reinstate("site_x"));
        assert!(!reg.is_suspended("site_x"));
    }
}
