//! Map a fly create request onto the dregg lease vocabulary.
//!
//! This is where the public fly surface meets the dregg rail: a
//! [`CreateMachineRequest`](crate::types::CreateMachineRequest)'s guest picks the
//! isolation tier ([`cap_grade_for_guest`]) and implies a metered budget
//! ([`required_budget`]). The guest is the caller's **demand** — what it wants to
//! run. It is NOT, and must never be, evidence of funding.
//!
//! **The funding gate (LEASE-1a):** the create's lease is not synthesized here.
//! The gateway looks up the **funded** lease the chain attests for the app via a
//! [`FundingSource`](crate::funding::FundingSource) and admits the create only if
//! that real on-chain reserve covers the demand. See [`crate::funding`]. This
//! module supplies the demand (grade + required budget); funding comes from the
//! chain.

use dreggnet_bridge::CapGrade;

use crate::types::GuestConfig;

/// Map a fly guest class onto a dregg cap-grade (isolation tier).
///
/// - `performance` → [`CapGrade::MicroVm`] (hardware-isolated, the strongest
///   floor — a dedicated guest gets the firecracker tier);
/// - `shared` with `> 1` vCPU → [`CapGrade::Caged`] (native + seccomp/landlock);
/// - otherwise → [`CapGrade::Sandboxed`] (in-process wasm sandbox).
///
/// DIVERGENCE: fly runs *every* machine as a firecracker microVM; DreggNet instead
/// grades the requested guest onto the dregg cap-lattice, so a small shared
/// workload can run at the cheaper sandbox tier the bridge actually wires today
/// (wasmi). A stronger grade always satisfies a weaker floor.
pub fn cap_grade_for_guest(guest: &GuestConfig) -> CapGrade {
    match guest.cpu_kind.as_str() {
        "performance" => CapGrade::MicroVm,
        "shared" if guest.cpus > 1 => CapGrade::Caged,
        _ => CapGrade::Sandboxed,
    }
}

/// The metered budget a create request **demands** from its funded lease — derived
/// from the requested guest size.
///
/// This is the demand the on-chain funding must cover, NOT a grant of funding: a
/// bigger guest demands a bigger reserve, and the gateway admits the create only if
/// the chain attests a funded lease whose real reserve is at least this. Returns
/// `(required_budget_units, per_period_units)`: `cpus` units per period over enough
/// periods to run the guest (one period per 64 MiB, minimum 8).
pub fn required_budget(guest: &GuestConfig) -> (i64, i64) {
    let per_period_units = (guest.cpus.max(1)) as i64;
    let periods = ((guest.memory_mb / 64).max(8)) as i64;
    let budget_units = per_period_units * periods;
    (budget_units, per_period_units)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn guest_class_maps_to_cap_grade() {
        assert_eq!(
            cap_grade_for_guest(&GuestConfig {
                cpu_kind: "performance".into(),
                cpus: 1,
                memory_mb: 1024,
            }),
            CapGrade::MicroVm
        );
        assert_eq!(
            cap_grade_for_guest(&GuestConfig {
                cpu_kind: "shared".into(),
                cpus: 4,
                memory_mb: 1024,
            }),
            CapGrade::Caged
        );
        assert_eq!(
            cap_grade_for_guest(&GuestConfig::default()),
            CapGrade::Sandboxed
        );
    }

    #[test]
    fn a_bigger_guest_demands_a_bigger_budget() {
        let (small, _) = required_budget(&GuestConfig::default());
        let (big, _) = required_budget(&GuestConfig {
            cpu_kind: "performance".into(),
            cpus: 4,
            memory_mb: 4096,
        });
        assert!(big > small, "a bigger guest demands more reserve");
    }
}
