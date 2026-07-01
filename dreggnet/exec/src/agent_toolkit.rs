//! `agent_toolkit` — the cloud's polyana wiring over the open-source toolkit.
//!
//! The agent toolkit itself — the [`Toolkit`] registry, the cap-gated / metered /
//! receipted tool dispatch, the witness binding, the health probe, the receipt-log
//! monitor, the injected deploy verifier — was EXTRACTED to the open-source
//! substrate crate `dregg-agent` ([`dregg_agent::toolkit`]). It depends on nothing
//! but the substrate and owns no compute engine: its compute tools take an
//! **injected runner** ([`dregg_agent::toolkit::RunFn`]).
//!
//! This module re-exports that open toolkit and adds the DreggNet-side compute
//! wiring: [`PolyanaToolkit`] injects the real polyana sandbox engine
//! ([`crate::run_workload`]) as the toolkit's `run_tests` / `run_workload` runner,
//! and [`rewitness_run_tests`] rides the same engine for the Layer-3 re-witness.
//! The open core owns the witness; the cloud owns the engine — one agent runtime,
//! the cloud as a wrapper.

pub use dregg_agent::toolkit::*;

#[cfg(feature = "polyana")]
use dregg_agent::agent::{ReWitness, WitnessedRun};
// `RunReport` and `Toolkit` come in via the `pub use dregg_agent::toolkit::*`
// glob above (re-stating them in a private `use` would shadow that re-export).

/// Map a polyana [`crate::Output`] to the open toolkit's [`RunReport`].
#[cfg(feature = "polyana")]
fn report_of(out: crate::Output) -> RunReport {
    RunReport::new(out.values, out.enforcement)
}

/// The cloud's polyana compute wiring over the open [`Toolkit`]. Injects the real
/// [`crate::run_workload`] sandbox engine as the toolkit's run_tests / run_workload
/// runner, so the witnessed binding (computed in the open core) ties to a genuine
/// sandboxed execution at `tier`.
#[cfg(feature = "polyana")]
pub trait PolyanaToolkit: Sized {
    /// Wire a **run_tests** tool whose runner is the polyana sandbox at `tier`.
    fn with_run_tests_in(
        self,
        name: impl Into<String>,
        lang: impl Into<String>,
        source: impl Into<String>,
        tier: crate::CapTier,
    ) -> Toolkit;

    /// Wire a **run_workload** tool whose runner is the polyana sandbox at `tier`.
    fn with_run_workload_in(
        self,
        name: impl Into<String>,
        lang: impl Into<String>,
        source: impl Into<String>,
        tier: crate::CapTier,
    ) -> Toolkit;
}

#[cfg(feature = "polyana")]
impl PolyanaToolkit for Toolkit {
    fn with_run_tests_in(
        self,
        name: impl Into<String>,
        lang: impl Into<String>,
        source: impl Into<String>,
        tier: crate::CapTier,
    ) -> Toolkit {
        self.with_run_tests(name, lang, source, move |l, s| {
            crate::run_workload(l, s, tier)
                .map(report_of)
                .map_err(|e| e.to_string())
        })
    }

    fn with_run_workload_in(
        self,
        name: impl Into<String>,
        lang: impl Into<String>,
        source: impl Into<String>,
        tier: crate::CapTier,
    ) -> Toolkit {
        self.with_run_workload(name, lang, source, move |l, s| {
            crate::run_workload(l, s, tier)
                .map(report_of)
                .map_err(|e| e.to_string())
        })
    }
}

/// The **re-witness oracle** for a `run_tests` binding, riding the polyana engine:
/// re-execute `source` (the code the binding's `code_root` commits to) at `tier`
/// and reproduce its `(exit, output_digest)`. Handed to
/// [`dregg_agent::agent::verify_witnessed_qa`] as the `rerun` closure. Returns
/// `None` (fail-closed) when `source` does not match the binding's `code_root` or
/// the workload could not be executed.
#[cfg(feature = "polyana")]
pub fn rewitness_run_tests(
    lang: &str,
    source: &str,
    tier: crate::CapTier,
    bound: &WitnessedRun,
) -> Option<ReWitness> {
    dregg_agent::toolkit::rewitness_run_tests(lang, source, bound, move |l, s| {
        crate::run_workload(l, s, tier)
            .map(report_of)
            .map_err(|e| e.to_string())
    })
}

#[cfg(all(test, feature = "polyana"))]
mod tests {
    use super::*;
    use dregg_agent::agent::{
        AgentAction, AgentCloud, AgentSpec, PlannedBrain, verify_agent_run, verify_witnessed_qa,
    };

    /// A core-module WAT that exports `run` returning the i32 `n` — a suite
    /// reporting `n` failures (0 = green), executed by the REAL polyana engine.
    fn wat_returning(n: i32) -> String {
        format!("(module (func (export \"run\") (result i32) (i32.const {n})))")
    }

    fn spec(id: &str, budget: i64, services: &[&str]) -> AgentSpec {
        let mut s = AgentSpec::new(id, budget);
        s.services = services.iter().map(|s| s.to_string()).collect();
        s.cells = vec!["/deploy".to_string()];
        s
    }

    /// The polyana wrapper genuinely runs a wat suite in the sandbox, binds the
    /// witness, and the whole run re-witnesses — proving the cloud's engine wiring
    /// over the open toolkit.
    #[test]
    fn polyana_run_tests_binds_a_real_sandboxed_execution() {
        let cloud = AgentCloud::from_seed([60u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:polyqa", 10, &["run_tests"]))
            .unwrap();
        let src = wat_returning(0);
        let deployed_root = code_root(&src);

        let toolkit =
            Toolkit::new().with_run_tests_in("run_tests", "wat", &src, crate::CapTier::Sandboxed);
        let plan = vec![
            AgentAction::CellWrite {
                path: "/deploy".into(),
                value: deployed_root.clone(),
            },
            AgentAction::Invoke {
                service: "run_tests".into(),
            },
        ];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);
        verify_agent_run(&report).expect("the chain + bound re-witness");

        // Layer 3: re-run the bound on the real engine — it reproduces the result.
        let v = verify_witnessed_qa(&report, &deployed_root, |w| {
            rewitness_run_tests("wat", &src, crate::CapTier::Sandboxed, w)
        })
        .expect("the witnessed execution re-witnesses on the real engine");
        assert_eq!(v.passed, 1, "the suite really passed on re-execution");
    }
}
