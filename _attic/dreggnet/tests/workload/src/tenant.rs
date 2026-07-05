//! The lessee population — the tenants that open leases.
//!
//! Each tenant is a distinct lessee cell (a holder funded in its own balance),
//! identified so isolation can be asserted on its identity (the cap bound, the
//! per-holder debit, the per-`(lease,period)` meter key). See the plan §1.

use dreggnet_control::{CapGrade, ConservingLedger, Lease};

use crate::profile::{BudgetModel, LoadProfile, Rng, TierMix};

/// One tenant: a holder + the leases it will open.
#[derive(Debug, Clone)]
pub struct Tenant {
    /// The lessee cell id (`tenant-{i}`), distinct per tenant.
    pub id: String,
    /// The cap grade this tenant's leases run at (the isolation tier).
    pub grade: CapGrade,
    /// The leases this tenant opens over the run.
    pub leases: Vec<TenantLease>,
}

/// One lease a tenant opens — its instance id + the funded `Lease`.
#[derive(Debug, Clone)]
pub struct TenantLease {
    /// The durable instance / orchestration id (`lease-{tenant}-{seq}`), the
    /// idempotency key half. Distinct per lease.
    pub instance: String,
    pub lease: Lease,
}

/// Map a `CapTier` draw onto the `CapGrade` the lease carries. (`JitSandboxed`
/// folds onto `Sandboxed` at the grade level — both are in-process wasm.)
fn grade_for(tier: dreggnet_control::CapTier) -> CapGrade {
    use dreggnet_control::CapTier;
    match tier {
        CapTier::Sandboxed | CapTier::JitSandboxed => CapGrade::Sandboxed,
        CapTier::Caged => CapGrade::Caged,
        // Gpu is the strongest tier (a passthrough VM); until `CapGrade` grows a
        // Gpu variant it folds onto the strongest existing grade, MicroVm — the
        // same grade-level fold this function already does for JitSandboxed.
        CapTier::MicroVm | CapTier::Gpu => CapGrade::MicroVm,
    }
}

/// Build the tenant population a profile describes, and fund each in the ledger.
///
/// Funding is the isolation substrate: each tenant gets its own balance in the
/// run's asset, so the economy scenarios can assert a tenant is debited only for
/// its own work (§3 invariants, §5.2).
pub fn population(profile: &LoadProfile, ledger: &ConservingLedger) -> Vec<Tenant> {
    let mut rng = Rng::new(0xDECA_F_BAD_u64);
    let mut out = Vec::with_capacity(profile.tenants);

    for t in 0..profile.tenants {
        let id = format!("tenant-{t}");
        ledger.fund(&profile.asset, &id, profile.funding);

        // The tenant's nominal grade is drawn once from the mix; each lease may
        // refine it (the per-lease tier draw), but the grade is the isolation
        // boundary so we fix it per tenant for the isolation assertions.
        let tier = profile.tier_mix.sample(rng.next_u64());
        let grade = grade_for(tier);

        let mut leases = Vec::with_capacity(profile.leases_per_tenant);
        for s in 0..profile.leases_per_tenant {
            let instance = format!("lease-{id}-{s}");
            let lease = build_lease(profile, &mut rng, &id, grade);
            leases.push(TenantLease { instance, lease });
        }
        out.push(Tenant { id, grade, leases });
    }
    out
}

/// Build one funded lease, honoring the budget model (a `Tight` lease's budget is
/// deliberately below the metered cost so it lapses mid-run).
fn build_lease(profile: &LoadProfile, rng: &mut Rng, lessee: &str, grade: CapGrade) -> Lease {
    let per_period: i64 = 1;
    let steps = profile.steps_per_workload.max(1) as i64;
    let metered_cost = per_period * steps;

    let tight = match profile.budget_model {
        BudgetModel::Funded => false,
        BudgetModel::Tight => true,
        BudgetModel::Mixed(p) => {
            // Deterministic Bernoulli(p) from the draw.
            let draw = (rng.next_u64() % 1000) as f64 / 1000.0;
            draw < p
        }
    };

    // A funded budget covers all steps with headroom; a tight budget covers all
    // but the last step (so the over-budget tick lapses before commit).
    let budget = if tight {
        (metered_cost - per_period).max(0)
    } else {
        metered_cost
    };

    Lease::funded(lessee, grade, &profile.asset, budget, per_period)
}

/// Sample a per-lease cap-tier (for the compute-tier load generation, distinct
/// from the per-tenant grade above) from the mix.
pub fn sample_tier(mix: &TierMix, rng: &mut Rng) -> dreggnet_control::CapTier {
    mix.sample(rng.next_u64())
}
