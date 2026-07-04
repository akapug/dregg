//! `dreggnet-guard` — the per-account **abuse-prevention** layer for a
//! permissionless (KYC-free) cloud.
//!
//! A cloud that lets anyone deploy anything with no identity check is a
//! spam/malware/phishing/illegal-content magnet *unless* the same anonymous
//! `dga1_` cap-account that grants it openness is also held to bounds. This crate
//! is that bound — the cross-cutting admission gate every resource-creating
//! surface (gateway create, webapp publish, control server create, storage
//! bucket create, agent run, domain bind) and the request-serving path consult:
//!
//! 1. **Per-account quotas** ([`quota`]) — ceilings on # sites/servers/agents/
//!    buckets/domains and on cumulative compute/bandwidth/storage. A resource
//!    over the ceiling is refused IN-BAND (the budget-`402` shape).
//! 2. **Rate-limiting** ([`rate`]) — deploy rate (N/hour/account) + request rate
//!    (per-site / per-account on the serving path). Over the ceiling is refused
//!    FAIL-CLOSED (the `429`).
//! 3. **Abuse takedown** ([`takedown`] + [`governance`]) — an abuse-report →
//!    review → suspend flow. A suspension stops the resource serving/running and
//!    is itself a RECEIPTED governance turn (auditable, not arbitrary); the owner
//!    sees the reason.
//! 4. **Account standing** ([`governance::AccountStanding`]) — good/flagged/
//!    suspended gates creation (suspended creates nothing, flagged runs under the
//!    tighter quota tier), moved only by a receipted governance action.
//!
//! [`Guard`] is the one object a surface holds. Its admission methods return a
//! [`GuardRefusal`] a caller maps onto the in-band wire code (`402` / `429` /
//! `403`); its governance methods (`flag`, `suspend_resource`, `reinstate`) seal
//! a receipted [`governance::GovernanceEvent`] and update standing + the
//! suspension registry atomically.
//!
//! Everything here is the enforceable MECHANISM. The live abuse-report *intake*
//! form, the operator-review UI, and the moderation POLICY itself are
//! deliberately out of scope (reviewed-go — ember/legal's call); this crate
//! gives them teeth.

pub mod governance;
pub mod quota;
pub mod rate;
pub mod takedown;

use std::sync::Mutex;

pub use governance::{AccountStanding, GovAction, GovernanceEvent};
pub use quota::{Countable, Metered, QuotaError, QuotaLimits, QuotaPolicy};
pub use rate::{RateClass, RateExceeded, RateLimit, RateLimiter};
pub use takedown::{AbuseReport, Suspension, SuspensionRegistry};

use governance::GovernanceLog;
use quota::QuotaLedger;
use std::collections::HashMap;

/// A cap-account subject — the stable id derived from a `dga1_` credential
/// (`dreggnet_webauth::subject_of`). The unit every bound is keyed on.
pub type Subject = String;

/// Why the guard refused an admission — mapped by the caller onto the in-band
/// wire signal. This is the abuse layer's single refusal currency.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GuardRefusal {
    /// The account is suspended (or the target resource is) — maps to `403`.
    Suspended {
        /// The owner-readable reason.
        reason: String,
    },
    /// A per-account quota ceiling was hit — maps to `402` (payment/upgrade).
    Quota(QuotaError),
    /// A rate ceiling was hit — maps to `429` (with the `Retry-After` hint).
    Rate(RateExceeded),
}

impl GuardRefusal {
    /// The HTTP status a surface should answer with (the in-band code).
    pub fn http_status(&self) -> u16 {
        match self {
            GuardRefusal::Suspended { .. } => 403,
            GuardRefusal::Quota(_) => 402,
            GuardRefusal::Rate(_) => 429,
        }
    }
}

impl std::fmt::Display for GuardRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GuardRefusal::Suspended { reason } => write!(f, "account/resource suspended: {reason}"),
            GuardRefusal::Quota(e) => write!(f, "{e}"),
            GuardRefusal::Rate(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for GuardRefusal {}

/// The rate-limit knobs a [`Guard`] enforces. Conservative defaults for an
/// anonymous account; an operator can widen them as a deployment choice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RatePolicy {
    /// Deploys (publish / server-create / agent-launch) per account per window.
    pub deploy: RateLimit,
    /// Inbound requests per account (across all its sites) per window.
    pub account_requests: RateLimit,
    /// Inbound requests per single site per window.
    pub site_requests: RateLimit,
}

impl Default for RatePolicy {
    fn default() -> Self {
        RatePolicy {
            deploy: RateLimit::per_hour(20),
            account_requests: RateLimit::new(600, 60), // 600/min/account
            site_requests: RateLimit::new(300, 60),    // 300/min/site
        }
    }
}

/// Inner mutable state, behind one lock so the guard is `Sync` and a surface can
/// hold it in an `Arc`.
#[derive(Default)]
struct Inner {
    /// Per-account standing (absent ⇒ the [`AccountStanding::default`]).
    standing: HashMap<Subject, AccountStanding>,
    quota: QuotaLedger,
    rate: RateLimiter,
    suspensions: SuspensionRegistry,
    log: Option<GovernanceLog>,
}

/// The per-account abuse-prevention gate. Hold one per provider (in an `Arc`);
/// consult [`admit_create`](Guard::admit_create) before provisioning a resource
/// and [`admit_request`](Guard::admit_request) on the serving path. Drive
/// moderation through [`file_report`](Guard::file_report) →
/// [`suspend_resource`](Guard::suspend_resource) / [`flag`](Guard::flag).
pub struct Guard {
    quota_policy: QuotaPolicy,
    rate_policy: RatePolicy,
    inner: Mutex<Inner>,
}

impl Guard {
    /// A guard with the conservative default quota + rate policy and a governance
    /// log signing under `governance_seed` (so every takedown/standing change is
    /// a receipted, re-witnessable turn).
    pub fn new(governance_seed: [u8; 32]) -> Guard {
        Guard::with_policy(
            QuotaPolicy::default(),
            RatePolicy::default(),
            governance_seed,
        )
    }

    /// A guard with explicit quota + rate policy.
    pub fn with_policy(
        quota_policy: QuotaPolicy,
        rate_policy: RatePolicy,
        governance_seed: [u8; 32],
    ) -> Guard {
        Guard {
            quota_policy,
            rate_policy,
            inner: Mutex::new(Inner {
                log: Some(GovernanceLog::from_seed(governance_seed)),
                ..Inner::default()
            }),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Inner> {
        self.inner.lock().expect("guard poisoned")
    }

    /// The public key the governance (takedown/standing) stream verifies under —
    /// the key an auditor re-witnesses the moderation history with.
    pub fn governance_pubkey(&self) -> [u8; 32] {
        self.lock()
            .log
            .as_ref()
            .map(|l| l.signer_public())
            .unwrap_or([0u8; 32])
    }

    /// The current standing of an account (default for a never-seen subject).
    pub fn standing(&self, subject: &str) -> AccountStanding {
        self.lock()
            .standing
            .get(subject)
            .copied()
            .unwrap_or_default()
    }

    // ── admission ────────────────────────────────────────────────────────────

    /// **Admit creating a resource** for `subject`. The full per-account gate, in
    /// order: standing (suspended ⇒ refuse), deploy-rate (over ⇒ `429`), quota
    /// (over ⇒ `402`). On admission it *commits* one deploy-rate token and one
    /// quota slot atomically; on any refusal nothing is consumed.
    ///
    /// `now_secs` is the verifier's clock (unix seconds).
    pub fn admit_create(
        &self,
        subject: &str,
        kind: Countable,
        now_secs: i64,
    ) -> Result<(), GuardRefusal> {
        let mut inner = self.lock();
        let standing = inner.standing.get(subject).copied().unwrap_or_default();

        // 1. Standing: a suspended account creates nothing.
        if !standing.may_create() {
            return Err(GuardRefusal::Suspended {
                reason: format!("account {subject} is suspended; resource creation is blocked"),
            });
        }

        // 2. Quota headroom (read-only) — check BEFORE consuming a rate token so a
        //    quota-refused create does not burn the account's deploy rate.
        inner
            .quota
            .would_admit_count(subject, kind, standing, &self.quota_policy)
            .map_err(GuardRefusal::Quota)?;

        // 3. Deploy rate (commits a token on success).
        let class = RateClass::Deploy {
            subject: subject.to_string(),
        };
        inner
            .rate
            .charge(&class, self.rate_policy.deploy, now_secs)
            .map_err(GuardRefusal::Rate)?;

        // 4. Commit the quota slot (headroom already confirmed in step 2).
        inner
            .quota
            .create(subject, kind, standing, &self.quota_policy)
            .map_err(GuardRefusal::Quota)?;
        Ok(())
    }

    /// **Admit serving a request** to `site_id` owned by `subject`. Refuses a
    /// suspended site/account (`403`) and enforces the per-site + per-account
    /// request rate (`429`). Charges one request against both windows on success.
    pub fn admit_request(
        &self,
        subject: &str,
        site_id: &str,
        now_secs: i64,
    ) -> Result<(), GuardRefusal> {
        let mut inner = self.lock();

        // A taken-down resource stops serving.
        if inner.suspensions.is_suspended(site_id) {
            let reason = inner
                .suspensions
                .reason(site_id)
                .unwrap_or("resource suspended")
                .to_string();
            return Err(GuardRefusal::Suspended { reason });
        }
        // A suspended account's resources stop serving too.
        let standing = inner.standing.get(subject).copied().unwrap_or_default();
        if matches!(standing, AccountStanding::Suspended) {
            return Err(GuardRefusal::Suspended {
                reason: format!("account {subject} is suspended"),
            });
        }

        // Per-site then per-account request rate.
        inner
            .rate
            .charge(
                &RateClass::SiteRequests {
                    site_id: site_id.to_string(),
                },
                self.rate_policy.site_requests,
                now_secs,
            )
            .map_err(GuardRefusal::Rate)?;
        inner
            .rate
            .charge(
                &RateClass::AccountRequests {
                    subject: subject.to_string(),
                },
                self.rate_policy.account_requests,
                now_secs,
            )
            .map_err(GuardRefusal::Rate)?;
        Ok(())
    }

    /// Return a quota slot when a resource is destroyed (so the account can
    /// create again). The lifecycle twin of [`admit_create`](Guard::admit_create).
    pub fn release(&self, subject: &str, kind: Countable) {
        self.lock().quota.release(subject, kind);
    }

    /// Charge a metered resource (compute/bandwidth/storage) against the account's
    /// cumulative ceiling. Refuses in-band (`402`) over the ceiling.
    pub fn charge_metered(
        &self,
        subject: &str,
        kind: Metered,
        amount: u64,
        now_secs: i64,
    ) -> Result<(), GuardRefusal> {
        let _ = now_secs;
        let mut inner = self.lock();
        let standing = inner.standing.get(subject).copied().unwrap_or_default();
        inner
            .quota
            .charge(subject, kind, amount, standing, &self.quota_policy)
            .map_err(GuardRefusal::Quota)
    }

    /// The live count an account holds of `kind` (for a console meter).
    pub fn count(&self, subject: &str, kind: Countable) -> u64 {
        self.lock().quota.count(subject, kind)
    }

    // ── moderation (receipted governance turns) ──────────────────────────────

    /// File an abuse report against a resource — intake only (no enforcement),
    /// recorded both in the review queue and as a receipted `Report` governance
    /// turn (the audit trail). Review is the operator's call.
    pub fn file_report(&self, report: AbuseReport) -> GovernanceEvent {
        let mut inner = self.lock();
        let subject = report.subject.clone().unwrap_or_default();
        let resource_id = report.resource_id.clone();
        let reason = report.reason.clone();
        let reporter = report.reporter.clone();
        let at = report.at;
        inner.suspensions.file_report(report);
        inner.seal(
            GovAction::Report,
            subject,
            Some(resource_id),
            None,
            reason,
            reporter,
            at,
        )
    }

    /// The pending operator-review queue (filed reports). The reviewed-go UI
    /// renders these.
    pub fn reports(&self) -> Vec<AbuseReport> {
        self.lock().suspensions.reports().to_vec()
    }

    /// **Suspend a resource** (it stops serving/running) by `actor` for `reason`,
    /// and move the owning account to `Suspended` standing. The suspension is a
    /// receipted governance turn; the resource's reason becomes owner-readable.
    /// Returns the sealed [`GovernanceEvent`].
    pub fn suspend_resource(
        &self,
        subject: &str,
        resource_id: &str,
        reason: impl Into<String>,
        actor: impl Into<String>,
        at: i64,
    ) -> GovernanceEvent {
        let reason = reason.into();
        let actor = actor.into();
        let mut inner = self.lock();
        inner.suspensions.suspend(
            resource_id,
            Suspension {
                subject: subject.to_string(),
                reason: reason.clone(),
                actor: actor.clone(),
                at,
            },
        );
        inner
            .standing
            .insert(subject.to_string(), AccountStanding::Suspended);
        inner.seal(
            GovAction::Suspend,
            subject.to_string(),
            Some(resource_id.to_string()),
            Some(AccountStanding::Suspended),
            reason,
            actor,
            at,
        )
    }

    /// **Flag an account** (tighter quota tier, still serving) by `actor` for
    /// `reason`. A receipted governance turn.
    pub fn flag(
        &self,
        subject: &str,
        reason: impl Into<String>,
        actor: impl Into<String>,
        at: i64,
    ) -> GovernanceEvent {
        let mut inner = self.lock();
        inner
            .standing
            .insert(subject.to_string(), AccountStanding::Flagged);
        inner.seal(
            GovAction::Flag,
            subject.to_string(),
            None,
            Some(AccountStanding::Flagged),
            reason,
            actor,
            at,
        )
    }

    /// **Reinstate** a resource and restore the owning account to good standing.
    /// A receipted governance turn. Returns the sealed event.
    pub fn reinstate(
        &self,
        subject: &str,
        resource_id: Option<&str>,
        reason: impl Into<String>,
        actor: impl Into<String>,
        at: i64,
    ) -> GovernanceEvent {
        let mut inner = self.lock();
        if let Some(id) = resource_id {
            inner.suspensions.reinstate(id);
        }
        inner
            .standing
            .insert(subject.to_string(), AccountStanding::Good);
        inner.seal(
            GovAction::Reinstate,
            subject.to_string(),
            resource_id.map(|s| s.to_string()),
            Some(AccountStanding::Good),
            reason,
            actor,
            at,
        )
    }

    /// Whether a resource is currently suspended (the serving-path gate).
    pub fn is_suspended(&self, resource_id: &str) -> bool {
        self.lock().suspensions.is_suspended(resource_id)
    }

    /// The owner-readable reason a resource was taken down.
    pub fn suspension_reason(&self, resource_id: &str) -> Option<String> {
        self.lock()
            .suspensions
            .reason(resource_id)
            .map(|s| s.to_string())
    }

    /// The full, sealed governance (moderation) stream — the auditable export an
    /// operator/regulator re-witnesses with [`dreggnet_receipt::verify_chain`]
    /// under [`governance_pubkey`](Guard::governance_pubkey).
    pub fn governance_log(&self) -> Vec<GovernanceEvent> {
        self.lock()
            .log
            .as_ref()
            .map(|l| l.events().to_vec())
            .unwrap_or_default()
    }
}

impl Inner {
    /// Seal a governance turn into the log (or build a bare event if no log).
    #[allow(clippy::too_many_arguments)]
    fn seal(
        &mut self,
        action: GovAction,
        subject: String,
        resource_id: Option<String>,
        standing_after: Option<AccountStanding>,
        reason: impl Into<String>,
        actor: impl Into<String>,
        at: i64,
    ) -> GovernanceEvent {
        self.log
            .as_mut()
            .expect("guard always has a governance log")
            .record(
                action,
                subject,
                resource_id,
                standing_after,
                reason,
                actor,
                at,
            )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_receipt::verify_chain;

    fn guard() -> Guard {
        Guard::new([42u8; 32])
    }

    // ── TEETH 1: a quota-exceeding create is refused in-band ──────────────────
    #[test]
    fn quota_exceeding_create_is_refused_in_band() {
        let g = guard();
        // good tier = 3 sites.
        for _ in 0..3 {
            g.admit_create("dregg:a", Countable::Site, 1000).unwrap();
        }
        let refusal = g
            .admit_create("dregg:a", Countable::Site, 1000)
            .unwrap_err();
        assert!(matches!(refusal, GuardRefusal::Quota(_)));
        assert_eq!(refusal.http_status(), 402);
    }

    // ── TEETH 2: a rate-limited deploy is 429'd ───────────────────────────────
    #[test]
    fn rate_limited_deploy_is_429d() {
        // a tight deploy rate so the burst trips it before the (larger) quota.
        let g = Guard::with_policy(
            QuotaPolicy::default(),
            RatePolicy {
                deploy: RateLimit::per_hour(2),
                ..RatePolicy::default()
            },
            [1u8; 32],
        );
        // two agent-creates admit (agent good quota = 2, rate = 2).
        g.admit_create("dregg:b", Countable::Agent, 5000).unwrap();
        g.admit_create("dregg:b", Countable::Agent, 5001).unwrap();
        // the third deploy trips the deploy RATE (429), not the quota.
        let refusal = g
            .admit_create("dregg:b", Countable::Site, 5002)
            .unwrap_err();
        assert!(matches!(refusal, GuardRefusal::Rate(_)), "{refusal:?}");
        assert_eq!(refusal.http_status(), 429);
    }

    // ── TEETH 3: a quota refusal does not burn a deploy-rate token ────────────
    #[test]
    fn quota_refusal_does_not_consume_a_rate_token() {
        // deploy rate of 5, but site quota of 3: the 4th site is a quota refusal
        // and must NOT have consumed a deploy token.
        let g = Guard::with_policy(
            QuotaPolicy::default(),
            RatePolicy {
                deploy: RateLimit::per_hour(5),
                ..RatePolicy::default()
            },
            [2u8; 32],
        );
        for _ in 0..3 {
            g.admit_create("dregg:c", Countable::Site, 1000).unwrap();
        }
        // 4th site: quota refusal.
        assert!(matches!(
            g.admit_create("dregg:c", Countable::Site, 1000),
            Err(GuardRefusal::Quota(_))
        ));
        // we used 3 deploy tokens; 2 remain → an agent create (different quota)
        // still admits twice.
        g.admit_create("dregg:c", Countable::Agent, 1000).unwrap();
        g.admit_create("dregg:c", Countable::Agent, 1000).unwrap();
    }

    // ── TEETH 4: abuse-report → suspend → stops serving + receipted + readable ─
    #[test]
    fn report_to_suspend_stops_serving_with_an_auditable_receipt() {
        let g = guard();
        // the account deploys a site and serves fine.
        g.admit_create("dregg:bad", Countable::Site, 1000).unwrap();
        assert!(g.admit_request("dregg:bad", "site_evil", 1000).is_ok());

        // someone reports it (intake only — still serving).
        g.file_report(AbuseReport {
            resource_id: "site_evil".into(),
            kind: Countable::Site,
            subject: Some("dregg:bad".into()),
            reporter: "automated:phish-scan".into(),
            reason: "phishing".into(),
            at: 1010,
        });
        assert!(g.admit_request("dregg:bad", "site_evil", 1011).is_ok());
        assert_eq!(g.reports().len(), 1);

        // operator reviews + suspends.
        g.suspend_resource(
            "dregg:bad",
            "site_evil",
            "confirmed phishing kit",
            "dregg:operator1",
            1100,
        );
        // the resource STOPS serving (403).
        let refusal = g.admit_request("dregg:bad", "site_evil", 1101).unwrap_err();
        assert!(matches!(refusal, GuardRefusal::Suspended { .. }));
        assert_eq!(refusal.http_status(), 403);
        // the owner can read why.
        assert_eq!(
            g.suspension_reason("site_evil").as_deref(),
            Some("confirmed phishing kit")
        );
        // the takedown is an auditable, re-witnessable receipt stream.
        let log = g.governance_log();
        assert_eq!(verify_chain(&log), Ok(()));
        assert!(log.iter().any(
            |e| e.action == GovAction::Suspend && e.resource_id.as_deref() == Some("site_evil")
        ));
    }

    // ── TEETH 5: a suspended account can't create ─────────────────────────────
    #[test]
    fn a_suspended_account_cannot_create() {
        let g = guard();
        g.admit_create("dregg:bad", Countable::Site, 1000).unwrap();
        g.suspend_resource("dregg:bad", "site_x", "malware", "dregg:op", 1100);
        // suspended standing now blocks ALL creation (403).
        let refusal = g
            .admit_create("dregg:bad", Countable::Agent, 1200)
            .unwrap_err();
        assert!(matches!(refusal, GuardRefusal::Suspended { .. }));
        assert_eq!(refusal.http_status(), 403);
        // reinstating restores creation.
        g.reinstate(
            "dregg:bad",
            Some("site_x"),
            "appeal upheld",
            "dregg:op",
            1300,
        );
        assert_eq!(g.standing("dregg:bad"), AccountStanding::Good);
        assert!(g.admit_create("dregg:bad", Countable::Agent, 1400).is_ok());
    }

    // ── TEETH 6: standing transitions are all receipted + ordered ─────────────
    #[test]
    fn standing_transitions_are_receipted_and_ordered() {
        let g = guard();
        assert_eq!(g.standing("dregg:x"), AccountStanding::Good);
        g.flag(
            "dregg:x",
            "suspicious deploy pattern",
            "automated:heuristic",
            1000,
        );
        assert_eq!(g.standing("dregg:x"), AccountStanding::Flagged);
        g.suspend_resource("dregg:x", "srv_1", "confirmed abuse", "dregg:op", 1100);
        assert_eq!(g.standing("dregg:x"), AccountStanding::Suspended);
        g.reinstate("dregg:x", Some("srv_1"), "resolved", "dregg:op", 1200);
        assert_eq!(g.standing("dregg:x"), AccountStanding::Good);
        // the whole standing history is one verifiable governance chain.
        let log = g.governance_log();
        assert_eq!(verify_chain(&log), Ok(()));
        assert_eq!(log.len(), 3);
        assert_eq!(
            log.iter().map(|e| e.action).collect::<Vec<_>>(),
            vec![GovAction::Flag, GovAction::Suspend, GovAction::Reinstate]
        );
    }

    // ── flagged tier tightens quotas live ─────────────────────────────────────
    #[test]
    fn flagging_tightens_quotas_live() {
        let g = guard();
        // good: 3 sites. Use 1, then get flagged → flagged tier = 1 site → already
        // at the tighter ceiling, so the next create is refused.
        g.admit_create("dregg:y", Countable::Site, 1000).unwrap();
        g.flag("dregg:y", "under review", "dregg:op", 1050);
        let refusal = g
            .admit_create("dregg:y", Countable::Site, 1100)
            .unwrap_err();
        assert!(matches!(refusal, GuardRefusal::Quota(_)));
    }
}
