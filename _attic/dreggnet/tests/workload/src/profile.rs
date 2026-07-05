//! The load profile — the knobs a scenario sets to describe the load it drives.
//!
//! Every field has a modest default (so the suite is runnable on a laptop) and an
//! env override (so the overnight run scales it up without code changes). See
//! `docs/WORKLOAD-TEST-PLAN.md` §1.

use std::time::Duration;

use dreggnet_control::CapTier;

/// The lease-arrival process: how leases enter the loop over time.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Arrival {
    /// All leases offered up front (drains as fast as the fleet allows).
    Burst,
    /// A steady rate of `per_sec` leases.
    Constant { per_sec: u32 },
    /// A Poisson process with mean rate `lambda` (leases/sec).
    Poisson { lambda: f64 },
}

/// How a tenant's lease budget relates to the work it runs.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BudgetModel {
    /// Budget covers every step (the lease settles in full).
    Funded,
    /// Budget lapses mid-run (the over-budget tick fails before commit).
    Tight,
    /// A fraction `p` of leases are `Tight`, the rest `Funded`.
    Mixed(f64),
}

/// The duration gate for a run.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum RunBound {
    /// Drain until every offered lease reaches a terminal state.
    Drain,
    /// Run for a wall-clock duration (the soak gate).
    Wall(Duration),
}

/// The full load description a scenario drives.
#[derive(Debug, Clone)]
pub struct LoadProfile {
    pub tenants: usize,
    pub leases_per_tenant: usize,
    pub arrival: Arrival,
    /// The distribution over cap-tiers (weights, normalized at sample time).
    pub tier_mix: TierMix,
    pub steps_per_workload: usize,
    pub budget_model: BudgetModel,
    /// (fleet size, per-backend capacity).
    pub backends: (usize, usize),
    pub bound: RunBound,
    /// The settlement asset (one ledger asset for the whole run).
    pub asset: String,
    /// Per-tenant initial funding in `asset`.
    pub funding: i64,
}

impl Default for LoadProfile {
    fn default() -> Self {
        LoadProfile {
            tenants: 100,
            leases_per_tenant: 10,
            arrival: Arrival::Burst,
            tier_mix: TierMix::realistic(),
            steps_per_workload: 2,
            budget_model: BudgetModel::Funded,
            backends: (4, 16),
            bound: RunBound::Drain,
            asset: "USD".to_string(),
            funding: 1_000_000,
        }
    }
}

impl LoadProfile {
    /// Apply the `DREGGNET_WL_*` env overrides over `self` (see the plan §1/§6).
    /// Unknown/absent vars leave the field untouched.
    pub fn with_env_overrides(mut self) -> Self {
        if let Some(v) = env_usize("DREGGNET_WL_TENANTS") {
            self.tenants = v;
        }
        if let Some(v) = env_usize("DREGGNET_WL_LEASES_PER_TENANT") {
            self.leases_per_tenant = v;
        }
        if let Some(v) = env_usize("DREGGNET_WL_STEPS") {
            self.steps_per_workload = v;
        }
        if let Some((n, cap)) = std::env::var("DREGGNET_WL_BACKENDS")
            .ok()
            .and_then(|s| parse_pair(&s))
        {
            self.backends = (n, cap);
        }
        if let Some(d) = std::env::var("DREGGNET_WL_DURATION")
            .ok()
            .and_then(|s| parse_duration(&s))
        {
            self.bound = RunBound::Wall(d);
        }
        self
    }

    /// Total leases this profile offers.
    pub fn total_leases(&self) -> usize {
        self.tenants * self.leases_per_tenant
    }
}

/// A weighted distribution over the four cap-tiers (the realistic cloud mix).
#[derive(Debug, Clone)]
pub struct TierMix {
    pub sandboxed: u32,
    pub jit: u32,
    pub caged: u32,
    pub microvm: u32,
}

impl TierMix {
    /// The realistic mix from `docs/COMPUTE-TIERS.md`: 40/30/20/10.
    pub fn realistic() -> Self {
        TierMix {
            sandboxed: 40,
            jit: 30,
            caged: 20,
            microvm: 10,
        }
    }

    /// All-wasm (the floor that runs on any host, no native runtimes/KVM).
    pub fn wasm_only() -> Self {
        TierMix {
            sandboxed: 60,
            jit: 40,
            caged: 0,
            microvm: 0,
        }
    }

    /// Sample a tier from a deterministic `u64` draw (so runs are reproducible).
    pub fn sample(&self, draw: u64) -> CapTier {
        let total = (self.sandboxed + self.jit + self.caged + self.microvm).max(1);
        let pick = (draw % total as u64) as u32;
        if pick < self.sandboxed {
            CapTier::Sandboxed
        } else if pick < self.sandboxed + self.jit {
            CapTier::JitSandboxed
        } else if pick < self.sandboxed + self.jit + self.caged {
            CapTier::Caged
        } else {
            CapTier::MicroVm
        }
    }
}

// ---- env helpers ----

fn env_usize(key: &str) -> Option<usize> {
    std::env::var(key).ok().and_then(|s| s.trim().parse().ok())
}

/// Parse `"N:CAP"` (e.g. `"8:16"`).
fn parse_pair(s: &str) -> Option<(usize, usize)> {
    let (a, b) = s.split_once(':')?;
    Some((a.trim().parse().ok()?, b.trim().parse().ok()?))
}

/// Parse a coarse duration: `"30s"`, `"10m"`, `"8h"`, or bare seconds `"45"`.
fn parse_duration(s: &str) -> Option<Duration> {
    let s = s.trim();
    let (num, unit) = s.split_at(s.find(|c: char| c.is_alphabetic()).unwrap_or(s.len()));
    let n: u64 = num.trim().parse().ok()?;
    Some(match unit {
        "" | "s" => Duration::from_secs(n),
        "m" => Duration::from_secs(n * 60),
        "h" => Duration::from_secs(n * 3600),
        _ => return None,
    })
}

/// A tiny deterministic xorshift64* — reproducible draws without a `rand` dep.
#[derive(Debug, Clone)]
pub struct Rng(pub u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed.max(1))
    }
    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
}
