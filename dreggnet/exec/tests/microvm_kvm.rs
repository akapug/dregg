//! Real microVM proof for the `CapTier::MicroVm` (Firecracker) tier.
//!
//! This drives an ACTUAL Firecracker microVM end-to-end: boot a guest kernel +
//! Alpine rootfs, run a real CPython workload inside it over the vsock guest
//! wire, read the metered result, and tear the VM down. It needs a KVM host
//! with a provisioned image, so it self-skips unless ALL of:
//!
//!   * `/dev/kvm` exists, and
//!   * `DREGGNET_FC_BIN`, `DREGGNET_FC_KERNEL`, `DREGGNET_FC_ROOTFS` are set
//!     to a built firecracker binary + kernel + rootfs (see the
//!     firecracker-provider `image/build-image.sh`).
//!
//! On a plain macOS / no-KVM box it skips cleanly — the unconditional green
//! coverage lives in the lib unit tests. Run it for real on node-a:
//!
//! ```text
//! DREGGNET_FC_BIN=~/dregg-microvm/firecracker \
//! DREGGNET_FC_KERNEL=~/dregg-microvm/vmlinux.bin \
//! DREGGNET_FC_ROOTFS=~/dregg-microvm/rootfs.ext4 \
//!   cargo test -p dreggnet-exec --test microvm_kvm -- --ignored --nocapture
//! ```

#![cfg(feature = "firecracker")]

use dreggnet_exec::{CapTier, run_workload_with_input};

fn microvm_ready() -> bool {
    std::path::Path::new("/dev/kvm").exists()
        && std::env::var_os("DREGGNET_FC_BIN").is_some()
        && std::env::var_os("DREGGNET_FC_KERNEL").is_some()
        && std::env::var_os("DREGGNET_FC_ROOTFS").is_some()
}

/// A python workload that speaks polyana's newline-JSON wire and returns
/// `40 + 2` — REAL CPython, computed inside the microVM, not on the host.
const PY_ADD: &str = r#"import sys, json
for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    json.loads(line)
    print(json.dumps({"ok": [40 + 2]}), flush=True)
"#;

/// The headline proof: a real CPython workload runs inside a Firecracker
/// microVM and returns 42 over the vsock wire, reported at the `Container`
/// (KVM-boundary) enforcement level, then the VM is torn down.
///
/// `run_workload_with_input` is synchronous (it drives its own runtime + boots
/// and tears down the VM), so a plain `#[test]` is enough.
#[test]
#[ignore = "needs a KVM host + a provisioned firecracker image (DREGGNET_FC_*)"]
fn microvm_runs_real_cpython() {
    if !microvm_ready() {
        eprintln!("skip: no /dev/kvm or DREGGNET_FC_* image env not set");
        return;
    }
    let out = run_workload_with_input("python", PY_ADD, CapTier::MicroVm, &[])
        .expect("real microVM CPython workload should return a result");

    assert_eq!(out.values, vec!["42".to_string()], "got {out:?}");
    assert_eq!(
        out.enforcement, "Container",
        "the MicroVm tier reports the KVM-boundary enforcement level: {out:?}"
    );
}

/// The JAILED full-stack proof: the same real CPython workload, but run through
/// the firecracker **jailer** (cgroup + namespaces + chroot + privilege drop —
/// the production isolation posture) by setting `DREGGNET_FC_JAILER`. The exec
/// layer routes through `FirecrackerProvider::with_jailer`, so the run reports
/// the stronger `FullVm` enforcement level (vs `Container` for the direct path).
///
/// Needs everything `microvm_runs_real_cpython` needs PLUS root (the jailer
/// builds the cgroup/namespaces/chroot before dropping privilege) and
/// `DREGGNET_FC_JAILER` set. Run it for real on node-a:
///
/// ```text
/// sudo -E env DREGGNET_FC_JAILER=1 \
///   DREGGNET_FC_BIN=~/dregg-microvm/firecracker \
///   DREGGNET_FC_JAILER_BIN=~/dregg-microvm/jailer \
///   DREGGNET_FC_KERNEL=~/dregg-microvm/vmlinux.bin \
///   DREGGNET_FC_ROOTFS=~/dregg-microvm/rootfs.ext4 \
///   cargo test -p dreggnet-exec --test microvm_kvm jailed -- --ignored --nocapture
/// ```
#[test]
#[ignore = "needs a KVM host + ROOT + DREGGNET_FC_JAILER + a provisioned image"]
fn microvm_runs_real_cpython_jailed() {
    let jailed = std::env::var("DREGGNET_FC_JAILER")
        .ok()
        .map(|v| !v.trim().is_empty())
        .unwrap_or(false);
    if !microvm_ready() || !jailed {
        eprintln!("skip: needs /dev/kvm + DREGGNET_FC_* image env + DREGGNET_FC_JAILER set");
        return;
    }
    let out = run_workload_with_input("python", PY_ADD, CapTier::MicroVm, &[])
        .expect("real JAILED microVM CPython workload should return a result");

    assert_eq!(out.values, vec!["42".to_string()], "got {out:?}");
    assert_eq!(
        out.enforcement, "FullVm",
        "the JAILED MicroVm path reports the strongest (FullVm) enforcement: {out:?}"
    );
}

/// The MicroVm tier must NEVER silently downgrade. On a host without /dev/kvm
/// it refuses cleanly; this is the unconditional half of the no-downgrade
/// contract (the booting half is `microvm_runs_real_cpython`).
#[test]
fn microvm_refuses_without_kvm() {
    if std::path::Path::new("/dev/kvm").exists() {
        eprintln!("skip: /dev/kvm present — the refuse-cleanly path is for no-KVM hosts");
        return;
    }
    let r = run_workload_with_input("python", PY_ADD, CapTier::MicroVm, &[]);
    assert!(
        r.is_err(),
        "MicroVm must refuse without /dev/kvm, got {r:?}"
    );
}
