//! Failure injection — the fault schedule a scenario applies to the live
//! fleet/ledger/loop during a run (the plan §5.3).
//!
//! A `Fault` is applied against the real running system: `BackendDown`/`Partition`
//! flip a live backend stub's down flag; `SettlerRestart` tears down and reopens
//! the durable store; `LeaseLapse` skews a fraction of the population over-budget.

use std::time::Duration;

/// One injected fault, scheduled at an offset into the run.
#[derive(Debug, Clone)]
pub enum Fault {
    /// Mark a named backend unreachable at `at` (it drops connections → failover).
    BackendDown { backend: String, at: Duration },
    /// The lease-source node stops answering for a window (the loop reads no new
    /// leases while down, resumes after).
    NodeDown { at: Duration, for_: Duration },
    /// A transient transport fault on `backend`: down at `at`, healed after `for_`.
    Partition {
        backend: String,
        at: Duration,
        for_: Duration,
    },
    /// Tear down + reopen the durable store mid-run (the at-most-once settlement
    /// under crash — in-flight workflows resume exactly-once).
    SettlerRestart { at: Duration },
    /// A fraction of the population goes over-budget mid-run (clean lapse → reap).
    LeaseLapse { fraction: f64 },
}

/// A schedule of faults applied over a run. Empty = the happy path.
#[derive(Debug, Clone, Default)]
pub struct FaultPlan(pub Vec<Fault>);

impl FaultPlan {
    pub fn none() -> Self {
        FaultPlan(Vec::new())
    }
    pub fn of(faults: impl IntoIterator<Item = Fault>) -> Self {
        FaultPlan(faults.into_iter().collect())
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// The faults due to fire at or before `elapsed` (the injector polls this).
    pub fn due(&self, elapsed: Duration) -> impl Iterator<Item = &Fault> {
        self.0.iter().filter(move |f| at_of(f) <= elapsed)
    }
}

fn at_of(f: &Fault) -> Duration {
    match f {
        Fault::BackendDown { at, .. }
        | Fault::NodeDown { at, .. }
        | Fault::Partition { at, .. }
        | Fault::SettlerRestart { at } => *at,
        // Budget-skew faults apply at construction (offset 0).
        Fault::LeaseLapse { .. } => Duration::ZERO,
    }
}
