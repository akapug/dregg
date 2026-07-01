//! `dreggnet-exec` — DreggNet's execution surface over polyana.
//!
//! This is the thin seam where a (dregg-authorized) workload gets handed to
//! polyana's real polyglot execution engine. [`run_workload`] drives a real
//! `polyana_core::ExecutionProvider` to load, instantiate, and call a workload
//! at the sandbox grade the dregg lease authorizes, refusing to run a workload
//! whose cap-tier demands more isolation than the selected provider can
//! guarantee (never a silent downgrade).
//!
//! ## The polyana surface we drive
//!
//! polyana (Apache-2.0, pinned at `../polyana`) exposes
//! execution through the `polyana-core` crate's `ExecutionProvider` trait
//! (`src/core/src/provider.rs`):
//!
//! ```text
//! trait ExecutionProvider {
//!     fn name(&self) -> &str;
//!     fn enforcement_level(&self) -> EnforcementLevel;     // sandbox tier
//!     async fn load_component(&self, store, artifact) -> Result<Component>;
//!     async fn instantiate(&self, component) -> Result<Instance>;
//!     async fn instantiate_with_caps(&self, component, caps) -> ...;
//!     async fn call(&self, instance, name, args) -> Result<Vec<Value>>;
//! }
//! ```
//!
//! ## The wired tiers (cap-grade → provider)
//!
//! Three concrete backends are wired, each meeting a different point on
//! polyana's enforcement ladder:
//!
//! | [`CapTier`]              | lang        | provider                          | enforcement                              |
//! |--------------------------|-------------|-----------------------------------|------------------------------------------|
//! | [`CapTier::Sandboxed`]   | `wasm`/`wat`| `polyana-wasmi-provider`          | `WasmSandbox` (pure interpreter)         |
//! | [`CapTier::JitSandboxed`]| `wasm`/`wat`| `polyana-wasmtime`                | `WasmFullSandbox` (JIT + fuel + WASI P2) |
//! | [`CapTier::Caged`]       | `native`/`bin` | `polyana-native-process-provider` | `OsSandbox` (seccomp-bpf + Landlock)  |
//!
//! `WasmFullSandbox` sits strictly above `WasmSandbox` in polyana's enforcement
//! ordering, so the JIT tier is a genuinely stronger sandbox — the interpreter
//! provider does *not* satisfy the JIT tier's floor, and the floor check
//! refuses to fall back to it (proven by `jit_tier_floor_excludes_interpreter`).
//!
//! The two wasm backends consume different wasm dialects: the wasmi interpreter
//! runs a **core module**, while wasmtime runs a **component-model** binary. So
//! a `wasm`/`wat` workload's `source` is core-module WAT at `Sandboxed` and
//! component WAT at `JitSandboxed` (the two dogfood tests show each shape).
//!
//! ## The `Caged` tier (`caged` feature, OS-sandboxed native process)
//!
//! Behind the off-by-default `caged` feature, [`CapTier::Caged`] runs a
//! `native`/`bin` workload — a host binary (a shebang script today; ELF bytes
//! in a later rung that takes `&[u8]`) — as a child process under
//! `polyana-native-process-provider`, which applies a seccomp-bpf syscall
//! allowlist + a Landlock filesystem allowlist before `execve` and reports
//! `EnforcementLevel::OsSandbox`. The child speaks polyana's newline-JSON wire
//! protocol (`{"fn":"run","args":[]}` → `{"ok":[..]}`).
//!
//! This sandbox actually ENGAGES only on Linux: off-Linux the provider's
//! `instantiate` returns a clean error (never an unsandboxed run), so the live
//! end-to-end dogfood is a Linux-only `#[ignore]`d test and the wasm tiers stay
//! the default-green path. `--features caged` still *compiles* on every target
//! (verified via `cargo zigbuild --target x86_64-unknown-linux-gnu`).
//!
//! NB on the floor check: polyana's `EnforcementLevel` ladder ranks the wasm
//! tiers (`WasmSandbox`/`WasmFullSandbox`) *above* `OsSandbox` (it orders by the
//! memory-isolation axis, not host-syscall mediation), so a numeric `<` floor
//! would NOT exclude a wasm provider from the `Caged` tier. The genuine
//! exclusion is therefore by provider *identity* + lang routing: `Caged` is the
//! native-host-binary tier, reachable only via `native`/`bin`, and a native
//! binary can only execute on the OsSandbox `native-process` provider — a wasm
//! provider (which reports a non-`OsSandbox` level) is never constructed for it
//! (proven by `caged_tier_native_clears_floor_wasm_is_not_its_provider` +
//! `caged_routing_refuses_mismatched_lang`).
//!
//! ## The native-interpreter tiers (`python` / `node` features)
//!
//! Alongside the wasm + native-binary tiers, two real native-interpreter tiers
//! run a genuine language runtime as a sandboxed child (NOT a wasm costume, NOT
//! an in-process isolate pool): `lang = "python"`/`"py"` via
//! `polyana-python-provider` and `lang = "node"`/`"js"` via
//! `polyana-node-provider`. Each spawns the real interpreter (`python3` /
//! `node`), feeds real JSON args over polyana's stdin/stdout wire, engages
//! seccomp + Landlock on Linux (`OsSandbox`) and runs process-isolated on macOS
//! (`None`) — the achieved level is surfaced in [`Output::enforcement`], never
//! silently claimed. Both threads the lease's cap bundle + tenant into the cage
//! via `instantiate_with_caps` (the cap-grade → tier → provider seam).
//!
//! ## The MicroVm tier (`firecracker` feature)
//!
//! [`CapTier::MicroVm`] is the strong-isolation tier — a per-workload
//! Firecracker microVM (a separate guest kernel behind the KVM boundary) via
//! `polyana-firecracker-provider`. It is wired (default-on `firecracker`
//! feature) and routed for every lang. [`run_on_microvm`] hands the provider a
//! `{"lang","source"}` workload spec; the provider boots the VM and reaches a
//! tiny in-guest agent over **vsock** (the same newline-JSON wire the native
//! python/node tiers speak), which runs the real language runtime inside the VM
//! and returns the result. The live boot requires the `firecracker` binary +
//! `/dev/kvm` (Linux + virtualization) + a kernel/rootfs image (built by the
//! provider's `image/build-image.sh`). Where those are absent (a macOS dev box,
//! an edge instance without nested virt) it refuses cleanly and names what's
//! missing — never a silent downgrade. The image paths are taken from
//! deployment env knobs (see [`microvm_config`]). Setting `DREGGNET_FC_JAILER`
//! routes every VM through the firecracker **jailer** (cgroup + namespaces +
//! chroot + privilege drop — the production isolation posture; see
//! [`microvm_jailer_config`]); the jailed path reports the stronger
//! `EnforcementLevel::FullVm` (a separate guest kernel behind KVM *and* a jailed
//! VMM), the direct path reports `Container`. The jailed boot is proven live on
//! a KVM host (`tests/microvm_kvm.rs::microvm_runs_real_cpython_jailed` +
//! the provider's `jailed_microvm_boot` integration test).
//!
//! ## The Gpu tier (`CapTier::Gpu`)
//!
//! [`CapTier::Gpu`] is the heavy-compute / GPU tier — a hardware-isolated VM
//! with a passed-through GPU (whole device via VFIO, or an NVIDIA MIG slice),
//! metered in GPU-seconds (the [`gpu`] module: [`gpu::GpuClass`],
//! [`gpu::GpuBounds`], [`gpu::GpuMeter`]). Its floor is `FullVm` (GPU
//! passthrough is only safe behind a VM boundary). It does NOT route to
//! Firecracker (which is CPU-only — no PCI passthrough) but to a separate
//! passthrough-VM provider seam (Cloud-Hypervisor / QEMU + VFIO, or a MIG
//! partition); [`run_on_gpu`] gates on the GPU hardware + a configured VMM and
//! refuses cleanly — naming exactly what is missing — where the live passthrough
//! stack is absent (never a silent downgrade to CPU-only). The routing,
//! detection, classes, and metering are wired; the live passthrough boot is the
//! hardware-gated fleet rung. See `docs/COMPUTE-TIERS.md`.
//!
//! The dregg side has a counterpart crate, `polyana-dregg-bridge`
//! (`../polyana/src/dregg-bridge`). The *bridge* rung maps a funded dregg
//! `execution-lease` cap-grade → a [`CapTier`] → the provider + capability
//! slice, and ticks the meter. Here the cap slice passed to
//! `instantiate_with_caps` is empty and the tier→enforcement map is provisional
//! (documented at [`cap_tier_enforcement`]).
//!
//! ## Default-deny is FAIL-CLOSED (red-team SBX-1/2/3)
//!
//! An empty cap slice means **deny**, never root. polyana's providers honor
//! the slice verbatim: `WasmtimeProvider::instantiate_with_caps(&[])` builds an
//! EMPTY capability set, which projects to *no* WASI preopens and a *denied*
//! network — so an untrusted workload reaches NOTHING on the host filesystem or
//! network. (Previously the wasmtime provider discarded the slice and fell back
//! to `CapabilitySet::default() = grant_all()`, preopening host `/` read-write
//! and inheriting the network — every workload ran as root over the whole host
//! and all tenants. That escape is closed.) Filesystem grants are fail-closed:
//! a capability with no explicit host path reaches nothing, never a `/` / `/tmp`
//! fallback. The in-process `native-provider` is NOT wired here (the `Caged`
//! tier routes to `native-process-provider`); it additionally refuses to run
//! off-Linux, where it has no isolation boundary. When the bridge rung lands it
//! threads the lease's *real* caps through this same honored slice, widening
//! the deny floor to exactly what the lease granted.

use anyhow::Result;

// The §3 inner host-API spine — a workload as a cap-bounded, metered, receipted
// TRANSACTING AGENT (invoke / cell_read / cell_write over the duplex guest
// wire). Behind the explicit, non-default `host-api` feature (AGPL + link-heavy
// dregg verified-core surface). See [`host_api`].
#[cfg(feature = "host-api")]
pub mod host_api;

// The replenishing-budget cell + the unified `Meter` trait — one attenuable
// primitive under every metering surface in the control plane. EXTRACTED to the
// open-source substrate crate `dregg-agent` (the agent runtime's "bound"), which
// the cloud now WRAPS. Re-exported here so existing `dreggnet_exec::budget` /
// `::meter` call sites are unchanged. See breadstuffs `dregg-agent` +
// `docs/AGENT-RUNTIME-OPEN-SOURCE.md`.
pub use dregg_agent::{budget, meter};

// EGRESS CONTROL (audit E-5): deny-by-default outbound network for workloads. A
// workload reaches a destination ONLY if its cap bundle granted an
// `egress:<host>:<port>` (CIDR / domain / wildcard) cap; everything else is
// refused, metered like bandwidth, and logged. The wasmtime in-process
// enforcement is the `EgressPolicy::to_polyana_caps` projection (deny-all → the
// empty cap set → `WasiNetworkPolicy::Deny`; a grant → a per-destination
// `WasiNetworkPolicy::Allowlist`); the live firecracker host-netns enforcement
// is the named seam (`egress::firecracker_netns_seam`). Std-only at its core
// (the polyana projection is `polyana`-gated), so it builds under any feature
// set. See [`egress`].
pub mod egress;

// The explicit EXECUTION-MODEL descriptor: a workload-run declared as a point in
// `lifecycle × funding × authority × trigger` over the shared primitives (the
// replenishing-budget `Meter`, the cap bundle, the receipt chain), so an arbitrary
// execution model is a DECLARATION, not a bespoke code path. The five existing
// paths (lease/persistent-server/deploy/agent/orchestrated) are recovered as
// points; three new models (cron · streaming · escrow-bonded compute market) drop
// in as declarations that run over the same meter. Std-only. See [`model`] and
// `docs/EXECUTION-MODELS.md`.
pub mod model;

// The agent runtime onramp (`agent`): the braid that turns "a budget + a
// capability" into "a proof of everything the agent did + a hard bound on
// everything it could have done". EXTRACTED to the open-source `dregg-agent`
// crate (the cap bundle, the receipt chain, the brain, the harness, the toolkit
// all live there now); the cloud WRAPS it. Re-exported so existing
// `dreggnet_exec::agent` call sites are unchanged.
pub use dregg_agent::agent;

// The FLEXIBLE LIVE RUN (`live`): the `run.json` session record a real adaptive
// agent emits — an arbitrary natural-language goal + a budget + a cap bundle, the
// reason → act → observe transcript, the re-witnessable receipt chain, and the
// host-untrusted `verify_live`. This is the **hosted-agent-session contract** the
// SSH attach and the portal web attach both surface. EXTRACTED to `dregg-agent`;
// re-exported so `dreggnet_exec::live` is the one shape both faces drive.
pub use dregg_agent::live;

// The AGENT TOOLKIT shim: the open-source `dregg_agent::toolkit` (the cap-gated /
// metered / receipted invoke-able tools) re-exported, PLUS the cloud's polyana
// compute wiring ([`agent_toolkit::PolyanaToolkit`]) that injects the real
// `run_workload` sandbox engine behind the toolkit's run_tests / run_workload
// runner seam. The open core owns the witness binding; the cloud owns the engine.
pub mod agent_toolkit;

// The LIVE LLM BRAIN behind the `agent` rail — [`openai_compat::OpenAICompatBrain`]
// over ANY OpenAI-compatible chat/tool-use endpoint. EXTRACTED to `dregg-agent`
// (`brain`); re-exported here under its historical name. The live `reqwest` POST
// is behind `kimi-live` (which now pulls `dregg-agent/live-brain`).
pub use dregg_agent::brain as openai_compat;

// Back-compat alias: the brain shipped first as `kimi`.
pub use dregg_agent::brain as kimi;

// BRING-YOUR-OWN-HARNESS: run the user's already-installed agent CLI AS the
// confined brain. EXTRACTED to `dregg-agent` (`harness`); re-exported here.
pub use dregg_agent::harness;

// FEDERATION-ATTESTED QA: closes the operator-independence residual of the
// witnessed QA ([`agent::verify_witnessed_qa`]). A QA verdict is submitted to the
// live n=4 federation (`edge`/`node-a`/`node-b-lean`/`node-b-rust`); each
// INDEPENDENT operator re-executes the bound `(command, code_root)` on its OWN
// substrate, signs its result, and a 3-of-4 quorum agreeing certifies the verdict
// (a [`federation_qa::QuorumCert`], the same shape as turn-finality's QC). A lying
// operator is OUTVOTED by the honest majority AND detected (its signed-but-
// divergent vote is on-cert evidence); below-quorum is refused. So `verify` proves
// the result is operator-independent — no single substrate trusted. The deeper
// in-circuit witness (a pure light client, not the operators, sees each re-run) is
// the swarm's VK-epoch, named in the module docs. EXTRACTED to `dregg-agent`
// (`federation_qa`, the quorum core); re-exported here. The live-node read is the
// injected surface the cloud supplies.
pub use dregg_agent::federation_qa;

// THE LOG CAPTURE WIRE: where the compute-tier run produces output, write the
// real result lines into a per-tenant `dreggnet_logs::LogSink` keyed by resource
// + owner, so `dregg-cloud logs <resource>` shows a tenant their app's actual
// output rather than cached step metadata (docs/CLOUD-PROVIDER-READINESS.md, the
// LOG blocker). [`capture::run_workload_captured`] is the one-call run+capture
// wire; [`capture::capture_line`] is the general seam the deploy/server/agent
// capture sites call with their own child stdout/stderr once wired. See
// [`capture`] and the `dreggnet-logs` crate.
pub mod capture;

/// The sandbox / capability grade a workload is authorized to run at.
///
/// Maps onto polyana's `EnforcementLevel` (and ultimately the dregg
/// execution-lease cap-grade). Ordered weakest → strongest isolation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CapTier {
    /// In-process pure-interpreter wasm sandbox (`polyana-wasmi-provider`,
    /// `EnforcementLevel::WasmSandbox`) — no JIT, no fuel meter; the cheapest
    /// real sandbox. Consumes core-module wasm.
    Sandboxed,
    /// In-process JIT'd wasm sandbox (`polyana-wasmtime`,
    /// `EnforcementLevel::WasmFullSandbox`) — Cranelift codegen + a fuel meter
    /// + WASI Preview 2 preopens + cap-gated host imports. Strictly stronger
    /// than [`Sandboxed`](CapTier::Sandboxed). Consumes a component-model
    /// binary.
    JitSandboxed,
    /// Native process under seccomp + landlock (`polyana-native-process-provider`,
    /// `EnforcementLevel::OsSandbox`) — a host binary run as a child process
    /// with a seccomp-bpf syscall allowlist + a Landlock filesystem allowlist.
    /// Wired behind the off-by-default `caged` feature; the sandbox actually
    /// engages only on Linux (off-Linux `instantiate` errors cleanly). Consumes
    /// a `native`/`bin` workload, not wasm.
    Caged,
    /// Hardware-isolated microVM (`polyana-firecracker-provider`,
    /// `EnforcementLevel::Container` until the core grows a `FullVm` variant)
    /// — a per-workload Firecracker microVM with its own guest kernel behind
    /// the KVM boundary (the fly.io / AWS-Lambda model). Wired behind the
    /// default-on `firecracker` feature; the live VM boot requires the
    /// `firecracker` binary + `/dev/kvm` + a kernel/rootfs image, and refuses
    /// cleanly where those are absent (never a silent downgrade). Strongest
    /// isolation tier — the home for untrusted / low-trust workloads.
    MicroVm,
    /// GPU / heavy-compute tier — a hardware-isolated VM with a **passed-through
    /// GPU** (whole device via VFIO, or an NVIDIA MIG slice), metered in
    /// GPU-seconds. This is the one axis the Liftoff matrix flagged Akash ahead
    /// on; [`CapTier::Gpu`] is DreggNet's answer: the same cap-bounded, metered,
    /// receipted lease shape, now over a GPU.
    ///
    /// It is NOT a Firecracker microVM: Firecracker is deliberately CPU-only
    /// (no PCI device passthrough), so the GPU tier routes to a separate
    /// passthrough-VM provider seam (Cloud-Hypervisor / QEMU + VFIO, or a MIG
    /// partition) — see [`run_on_gpu`] and `docs/COMPUTE-TIERS.md`. Like
    /// [`MicroVm`](CapTier::MicroVm) it refuses cleanly (never a silent
    /// downgrade) where the GPU hardware + passthrough stack are absent, naming
    /// exactly what is missing. Strongest isolation floor ([`FullVm`]) plus a
    /// GPU; the cap-grade carries the GPU class + the GPU-seconds / GPU-memory
    /// bounds (see [`gpu`]).
    ///
    /// [`FullVm`]: polyana_core::provider::EnforcementLevel::FullVm
    Gpu,
}

/// The result of running a workload: the values the entrypoint returned.
///
/// Mirrors polyana's `ExecutionProvider::call` return (`Vec<Value>`),
/// rendered to strings so DreggNet callers don't take a polyana type in their
/// signature.
///
/// `enforcement` is the isolation grade the workload *actually* ran under,
/// as reported by the selected polyana provider. It is surfaced (never hidden)
/// so a caller that requires a hard floor can inspect it — the native-language
/// tiers run at the provider's real level rather than refusing, and this field
/// is how a downgrade is made LOUD instead of silent (e.g. the native Python
/// tier reports `OsSandbox` on Linux but `None` on macOS, where seccomp /
/// Landlock don't exist).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Output {
    pub values: Vec<String>,
    /// The polyana `EnforcementLevel` the run actually achieved (e.g.
    /// `"WasmSandbox"`, `"WasmFullSandbox"`, `"OsSandbox"`, `"None"`).
    pub enforcement: String,
}

/// A typed input value handed to a workload's entrypoint.
///
/// This is the real input convention: a workload receives actual argument
/// values (numbers / text / JSON), NOT constants spliced into its source text.
/// Each variant maps onto a `polyana_core::provider::Value` the provider's
/// `call` marshals to the guest:
///
/// - The wasm tiers (wasmi / wasmtime) accept the **numeric** variants
///   ([`Input::I32`], [`Input::I64`], [`Input::F32`], [`Input::F64`]); wasmi is
///   numeric-only and wasmtime additionally accepts [`Input::Text`] for
///   component-model `string` params.
/// - The native interpreter tiers (Python, …) accept every variant — args are
///   serialized to JSON over the provider's stdin/stdout wire, so a workload
///   gets real strings / JSON bodies, not integer-only query params.
#[derive(Debug, Clone, PartialEq)]
pub enum Input {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    Text(String),
    Json(serde_json::Value),
}

#[cfg(feature = "polyana")]
impl Input {
    /// Lower to the polyana value the provider `call` marshals.
    fn to_value(&self) -> polyana_core::provider::Value {
        use polyana_core::provider::Value;
        match self {
            Input::I32(n) => Value::I32(*n),
            Input::I64(n) => Value::I64(*n),
            Input::F32(f) => Value::F32(*f),
            Input::F64(f) => Value::F64(*f),
            Input::Text(s) => Value::String(s.clone()),
            Input::Json(j) => Value::Json(j.clone()),
        }
    }

    /// `true` for the variants the core-wasm ABI can pass directly.
    fn is_numeric(&self) -> bool {
        matches!(
            self,
            Input::I32(_) | Input::I64(_) | Input::F32(_) | Input::F64(_)
        )
    }
}

/// A typed execution error — a polyana failure surfaces as one of these clean
/// categories rather than a bare string, panic, or hang. Implements
/// [`std::error::Error`], so the back-compat [`run_workload`] (which returns
/// `anyhow::Result`) converts it with `?` for free.
#[derive(Debug)]
#[non_exhaustive]
pub enum ExecError {
    /// No provider family wired for this `lang`.
    UnsupportedLang(String),
    /// The lang is wired but not at the requested tier (or the tier isn't
    /// served by this lang's provider family).
    TierNotServed {
        lang: String,
        tier: CapTier,
        detail: String,
    },
    /// The selected provider's enforcement is below the tier's floor.
    FloorUnmet {
        provider: String,
        have: String,
        need: String,
        tier: CapTier,
    },
    /// An argument's type isn't accepted by the selected tier (e.g. a string
    /// passed to the numeric-only wasmi interpreter).
    UnsupportedArg { tier: &'static str, detail: String },
    /// WAT / source assembly failed.
    Assembly(String),
    /// Provider construction failed.
    ProviderInit(String),
    /// `load_component` failed (decode / store).
    Load(String),
    /// `instantiate` / `instantiate_with_caps` failed (e.g. the native sandbox
    /// refused to engage on this host).
    Instantiate(String),
    /// The entrypoint call failed or the guest trapped.
    Call(String),
    /// The workload ran past its wall-clock budget and was killed.
    Timeout { secs: u64 },
    /// The runtime could not be built.
    Runtime(String),
    /// Built without the engine feature for this lang.
    NotWired(String),
}

impl std::fmt::Display for ExecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExecError::UnsupportedLang(l) => write!(f, "no polyana provider wired for lang `{l}`"),
            ExecError::TierNotServed { lang, tier, detail } => {
                write!(
                    f,
                    "lang `{lang}` is not served at cap-tier {tier:?}: {detail}"
                )
            }
            ExecError::FloorUnmet {
                provider,
                have,
                need,
                tier,
            } => write!(
                f,
                "provider `{provider}` enforcement {have} is below the floor {need} required by cap-tier {tier:?}"
            ),
            ExecError::UnsupportedArg { tier, detail } => {
                write!(f, "{tier}: unsupported argument: {detail}")
            }
            ExecError::Assembly(e) => write!(f, "source assembly failed: {e}"),
            ExecError::ProviderInit(e) => write!(f, "provider init failed: {e}"),
            ExecError::Load(e) => write!(f, "load_component failed: {e}"),
            ExecError::Instantiate(e) => write!(f, "instantiate failed: {e}"),
            ExecError::Call(e) => write!(f, "workload call failed: {e}"),
            ExecError::Timeout { secs } => {
                write!(f, "workload exceeded its {secs}s budget and was killed")
            }
            ExecError::Runtime(e) => write!(f, "runtime build failed: {e}"),
            ExecError::NotWired(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for ExecError {}

/// The conventional entrypoint a DreggNet workload exports.
///
/// The workload's `source` exports `run`; with [`run_workload`] it takes no
/// args (computes internally), and with [`run_workload_with_input`] it receives
/// the supplied [`Input`] values as real call arguments.
#[cfg(feature = "polyana")]
const ENTRYPOINT: &str = "run";

/// Default wall-clock budget (seconds) for a single workload call on an
/// interruptible (native subprocess) tier.
#[cfg(feature = "polyana")]
const DEFAULT_TIMEOUT_SECS: u64 = 30;

/// Wall-clock budget for a single workload call on a tier that can be
/// interrupted (the native subprocess tiers — a runaway guest is killed and
/// surfaces as [`ExecError::Timeout`] rather than hanging the caller). The
/// in-process wasm tiers are bounded by the engine instead (wasmtime's fuel
/// meter; wasmi is unmetered — see [`run_workload_with_input`]).
///
/// Overridable at runtime via `DREGGNET_EXEC_TIMEOUT_SECS` (a deployment knob,
/// not a feature gate); falls back to [`DEFAULT_TIMEOUT_SECS`].
#[cfg(feature = "polyana")]
fn workload_timeout() -> std::time::Duration {
    let secs = std::env::var("DREGGNET_EXEC_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .filter(|s| *s > 0)
        .unwrap_or(DEFAULT_TIMEOUT_SECS);
    std::time::Duration::from_secs(secs)
}

/// Run one workload through polyana at the authorized cap tier, with no call
/// arguments (the workload computes its result internally). Back-compat entry;
/// returns `anyhow::Result` so existing callers (the durable layer, the webapp
/// router) are unchanged. For real input, use [`run_workload_with_input`].
#[cfg(feature = "polyana")]
pub fn run_workload(lang: &str, source: &str, cap_tier: CapTier) -> Result<Output> {
    Ok(run_workload_with_input(lang, source, cap_tier, &[])?)
}

/// Run one workload through polyana, passing real argument values to its
/// entrypoint.
///
/// `lang` selects the provider family, `source` is the program, `cap_tier` is
/// the sandbox grade the dregg lease authorizes, and `input` is the argument
/// vector handed to the `run` entrypoint:
///
/// - `"wasm"`/`"wat"` — wasmi at [`CapTier::Sandboxed`] (core module, numeric
///   args only), wasmtime at [`CapTier::JitSandboxed`] (component model,
///   numeric + string args). The lang+tier pair selects the provider and the
///   floor check confirms it meets the tier's enforcement floor or refuses —
///   never a silent downgrade.
/// - `"native"`/`"bin"` — a host binary at [`CapTier::Caged`] (OS-sandboxed
///   native process; `caged` feature; Linux-only sandbox).
/// - `"python"`/`"py"` — a real CPython subprocess (`python` feature). Args are
///   delivered as JSON over polyana's stdin/stdout wire, so the workload
///   receives genuine typed values. The provider engages seccomp + Landlock on
///   Linux (`OsSandbox`) and runs process-isolated only on macOS (`None`); the
///   achieved level is reported in [`Output::enforcement`] (a downgrade is
///   loud, not silent) and the call is bounded by [`WORKLOAD_TIMEOUT`].
#[cfg(feature = "polyana")]
pub fn run_workload_with_input(
    lang: &str,
    source: &str,
    cap_tier: CapTier,
    input: &[Input],
) -> std::result::Result<Output, ExecError> {
    // MicroVm is the strong-isolation tier — a per-workload Firecracker microVM
    // (separate guest kernel, KVM hardware boundary) — regardless of the guest
    // lang. Routed here BEFORE the per-lang match so every lang's MicroVm grade
    // lands on the same backend (the VM runs the language runtime inside; `lang`
    // selects the guest entrypoint over the vsock wire in firecracker slice-2).
    if cap_tier == CapTier::MicroVm {
        return run_on_microvm(lang, source, input);
    }
    // Gpu is the heavy-compute tier — a GPU-passthrough VM. Like MicroVm it is
    // lang-agnostic at the hardware boundary and routed before the per-lang
    // match (the VM runs the language runtime inside, over the same guest wire).
    if cap_tier == CapTier::Gpu {
        return run_on_gpu(lang, source, input);
    }
    match lang {
        "wasm" | "wat" => match cap_tier {
            CapTier::Sandboxed => run_on_wasmi(source, input, cap_tier),
            CapTier::JitSandboxed => run_on_wasmtime(source, input, cap_tier),
            other => Err(ExecError::TierNotServed {
                lang: lang.to_string(),
                tier: other,
                detail:
                    "Caged is the native-host-binary tier (use lang `native`/`bin`); wasm runs at \
                     Sandboxed (wasmi) or JitSandboxed (wasmtime)"
                        .into(),
            }),
        },
        #[cfg(feature = "python")]
        "python" | "py" => run_on_python(source, input),
        #[cfg(not(feature = "python"))]
        "python" | "py" => Err(ExecError::NotWired(
            "dreggnet-exec: built without the `python` feature — the native CPython tier is not \
             linked; rebuild with `--features python`"
                .into(),
        )),
        #[cfg(feature = "node")]
        "node" | "js" => run_on_node(source, input),
        #[cfg(not(feature = "node"))]
        "node" | "js" => Err(ExecError::NotWired(
            "dreggnet-exec: built without the `node` feature — the native Node.js tier is not \
             linked; rebuild with `--features node`"
                .into(),
        )),
        #[cfg(feature = "caged")]
        "native" | "bin" => match cap_tier {
            CapTier::Caged => run_on_native_process(source, input, cap_tier),
            other => Err(ExecError::TierNotServed {
                lang: lang.to_string(),
                tier: other,
                detail: "a native/bin workload only runs at the Caged tier (OS-sandboxed native \
                         process); routing it to a wasm tier would be a provider-family mismatch"
                    .into(),
            }),
        },
        other => Err(ExecError::UnsupportedLang(other.to_string())),
    }
}

/// Run a wasm/wat workload at [`CapTier::JitSandboxed`] (wasmtime) under an
/// explicit [`egress::EgressPolicy`] — the EGRESS-CONTROL entrypoint.
///
/// The policy is projected into polyana `Network` capabilities
/// ([`egress::EgressPolicy::to_polyana_caps`]) and threaded into the WASI
/// context: a **deny-all** policy projects to the EMPTY cap set, so the guest
/// gets `WasiNetworkPolicy::Deny` and CANNOT open any outbound socket; a policy
/// granting `egress:<host>:<port>` projects to a per-destination
/// `WasiNetworkPolicy::Allowlist`, so the guest reaches ONLY the granted
/// destinations. This is the in-process half of E-5; the live host-netns
/// enforcement for the microVM tier is the named seam
/// ([`egress::firecracker_netns_seam`]).
///
/// Only the wasm tiers are served here. The pure-interpreter wasmi tier
/// ([`CapTier::Sandboxed`]) has no WASI socket surface to gate (it cannot open
/// a host socket at all — deny-by-default holds vacuously), so it runs the
/// workload unchanged; every other tier is refused [`ExecError::TierNotServed`]
/// (use the firecracker host-netns seam for [`CapTier::MicroVm`]).
#[cfg(feature = "polyana")]
pub fn run_workload_with_egress(
    lang: &str,
    source: &str,
    cap_tier: CapTier,
    input: &[Input],
    policy: &egress::EgressPolicy,
) -> std::result::Result<Output, ExecError> {
    match (lang, cap_tier) {
        ("wasm" | "wat", CapTier::JitSandboxed) => {
            run_on_wasmtime_with_caps(source, input, cap_tier, &policy.to_polyana_caps())
        }
        // wasmi has no WASI socket surface — it cannot reach the network, so the
        // deny-default is already total; run it unchanged.
        ("wasm" | "wat", CapTier::Sandboxed) => run_on_wasmi(source, input, cap_tier),
        (_, tier) => Err(ExecError::TierNotServed {
            lang: lang.to_string(),
            tier,
            detail: "egress-gated execution is served on the wasmtime (JitSandboxed) tier; the \
                     native / microVM tiers enforce egress at the host-netns seam \
                     (egress::firecracker_netns_seam)"
                .into(),
        }),
    }
}

/// Drive the wasmi pure-interpreter provider (`WasmSandbox`) on a core-module
/// workload — the lightest real sandbox, the default-green tier.
///
/// NB: wasmi has no fuel meter in this provider, so a runaway core module loops
/// in-process and a wall-clock timeout cannot interrupt it (the synchronous
/// call never yields). This tier is therefore for trusted / bounded compute;
/// untrusted workloads that need a runaway bound should use the JitSandboxed
/// (wasmtime fuel-metered) or native subprocess tiers.
#[cfg(feature = "polyana")]
fn run_on_wasmi(
    source: &str,
    input: &[Input],
    cap_tier: CapTier,
) -> std::result::Result<Output, ExecError> {
    use polyana_core::artifact::{ArtifactKind, ArtifactMetadata, ArtifactStore};
    use polyana_core::provider::ExecutionProvider;
    use polyana_wasmi_provider::WasmiProvider;

    // wasmi's core-wasm ABI is numeric-only; reject string/JSON args up front
    // with a clean message rather than a deep provider error.
    if let Some(bad) = input.iter().find(|a| !a.is_numeric()) {
        return Err(ExecError::UnsupportedArg {
            tier: "wasmi (Sandboxed)",
            detail: format!(
                "core wasm accepts numeric args only; got {bad:?} — use the JitSandboxed \
                 (wasmtime) tier for string args, or the native tiers for JSON"
            ),
        });
    }
    let args: Vec<_> = input.iter().map(Input::to_value).collect();

    let provider = WasmiProvider::new();
    check_floor(&provider, cap_tier)?;
    let enforcement = format!("{:?}", provider.enforcement_level());

    // wasmi consumes a core wasm module.
    let wasm = wat::parse_str(source).map_err(|e| ExecError::Assembly(e.to_string()))?;

    let rt = build_runtime()?;
    rt.block_on(async move {
        let store = ArtifactStore::new();
        let id = store
            .store(ArtifactKind::WasmModule, wasm, ArtifactMetadata::default())
            .map_err(|e| ExecError::Load(e.to_string()))?;

        let component = provider
            .load_component(&store, id)
            .await
            .map_err(|e| ExecError::Load(e.to_string()))?;

        // Empty cap slice = deny-all at this rung (the wasmi interpreter's
        // host imports are no-op stubs regardless); the dregg lease supplies
        // real capabilities at the bridge rung.
        let mut instance = provider
            .instantiate_with_caps(&component, &[])
            .await
            .map_err(|e| ExecError::Instantiate(e.to_string()))?;

        let values = provider
            .call(&mut instance, ENTRYPOINT, &args)
            .await
            .map_err(|e| ExecError::Call(e.to_string()))?;

        Ok(Output {
            values: values.iter().map(value_to_string).collect(),
            enforcement,
        })
    })
}

/// Drive the wasmtime JIT provider (`WasmFullSandbox`) on a component-model
/// workload — the stronger tier (Cranelift codegen + fuel meter + WASI P2).
///
/// wasmtime carries a fuel meter (default 50M units even with an empty cap
/// slice), so a runaway component traps with "out of fuel" and surfaces as a
/// clean [`ExecError::Call`] rather than hanging.
#[cfg(feature = "polyana")]
fn run_on_wasmtime(
    source: &str,
    input: &[Input],
    cap_tier: CapTier,
) -> std::result::Result<Output, ExecError> {
    run_on_wasmtime_with_caps(source, input, cap_tier, &[])
}

/// `run_on_wasmtime`, but threading an explicit polyana capability slice into
/// the WASI context — the EGRESS-CONTROL wire. An EMPTY slice is the
/// deny-by-default state (no preopens, no network — `WasiNetworkPolicy::Deny`);
/// a slice carrying `Network` `allow=`/`allow_cidr=` caps (the projection of an
/// [`egress::EgressPolicy`]) installs the per-destination
/// `WasiNetworkPolicy::Allowlist` socket check. See [`run_workload_with_egress`].
#[cfg(feature = "polyana")]
fn run_on_wasmtime_with_caps(
    source: &str,
    input: &[Input],
    cap_tier: CapTier,
    extra_caps: &[polyana_core::capability::Capability],
) -> std::result::Result<Output, ExecError> {
    use polyana_core::artifact::{ArtifactKind, ArtifactMetadata, ArtifactStore};
    use polyana_core::provider::ExecutionProvider;
    use polyana_wasmtime::WasmtimeProvider;
    use std::sync::Arc;

    // wasmtime's component-model ABI accepts numeric + string args; JSON args
    // aren't representable yet (polyana lowers Value::Json to an empty string).
    if let Some(bad) = input.iter().find(|a| matches!(a, Input::Json(_))) {
        return Err(ExecError::UnsupportedArg {
            tier: "wasmtime (JitSandboxed)",
            detail: format!("component-model args are numeric or string; got {bad:?}"),
        });
    }
    let args: Vec<_> = input.iter().map(Input::to_value).collect();

    // WasmtimeProvider compiles components out of the store it was built with,
    // so the workload artifact must be stored into *this* Arc store.
    let store = Arc::new(ArtifactStore::new());
    let provider =
        WasmtimeProvider::new(store.clone()).map_err(|e| ExecError::ProviderInit(e.to_string()))?;
    check_floor(&provider, cap_tier)?;
    let enforcement = format!("{:?}", provider.enforcement_level());

    // wasmtime consumes a component-model binary.
    let wasm = wat::parse_str(source).map_err(|e| ExecError::Assembly(e.to_string()))?;

    let caps: Vec<polyana_core::capability::Capability> = extra_caps.to_vec();
    let rt = build_runtime()?;
    rt.block_on(async move {
        let id = store
            .store(
                ArtifactKind::WasmComponent,
                wasm,
                ArtifactMetadata::default(),
            )
            .map_err(|e| ExecError::Load(e.to_string()))?;

        let component = provider
            .load_component(&store, id)
            .await
            .map_err(|e| ExecError::Load(e.to_string()))?;

        // wasmtime resolves the 3-arg `ExecutionProvider::instantiate_with_caps`
        // (component, caps, tenant). An EMPTY slice is honored as a deny-all
        // capability set (SBX-1): the workload gets no preopens and no network,
        // never the old `grant_all` root that preopened host `/`. The EGRESS
        // wire supplies `Network` `allow=`/`allow_cidr=` caps here (the
        // `EgressPolicy` projection) so the WASI ctx enforces the allowlist;
        // with no egress cap the slice is empty → no outbound socket at all.
        let mut instance = provider
            .instantiate_with_caps(&component, &caps, TENANT)
            .await
            .map_err(|e| ExecError::Instantiate(e.to_string()))?;

        let values = provider
            .call(&mut instance, ENTRYPOINT, &args)
            .await
            .map_err(|e| ExecError::Call(e.to_string()))?;

        Ok(Output {
            values: values.iter().map(value_to_string).collect(),
            enforcement,
        })
    })
}

/// Drive the real CPython provider (`polyana-python-provider`) — a genuine
/// `python3` subprocess, NOT wasm. The workload `source` is a Python program
/// that speaks polyana's newline-JSON wire (loop on `sys.stdin`, reply
/// `{"ok":[...]}` / `{"err":"..."}`); `input` is delivered as the `args` array
/// of a `{"fn":"run","args":[...]}` request, so the workload receives real
/// typed values.
///
/// Resource safety: the call is wrapped in [`WORKLOAD_TIMEOUT`]; on timeout the
/// provider is dropped, which kills the child (the provider sets
/// `kill_on_drop`), so a runaway guest fails as [`ExecError::Timeout`] without
/// hanging or leaking the process.
#[cfg(feature = "python")]
fn run_on_python(source: &str, input: &[Input]) -> std::result::Result<Output, ExecError> {
    run_on_python_with_timeout(source, input, workload_timeout())
}

#[cfg(feature = "python")]
fn run_on_python_with_timeout(
    source: &str,
    input: &[Input],
    timeout: std::time::Duration,
) -> std::result::Result<Output, ExecError> {
    use polyana_core::artifact::{ArtifactKind, ArtifactMetadata, ArtifactStore};
    use polyana_core::provider::ExecutionProvider;
    use polyana_python_provider::PythonProvider;

    let args: Vec<_> = input.iter().map(Input::to_value).collect();
    let rt = build_runtime()?;
    rt.block_on(async move {
        let provider = PythonProvider::new();
        let enforcement = format!("{:?}", provider.enforcement_level());

        let store = ArtifactStore::new();
        let id = store
            .store(
                ArtifactKind::NativeBinary,
                source.as_bytes().to_vec(),
                ArtifactMetadata::default(),
            )
            .map_err(|e| ExecError::Load(e.to_string()))?;

        let component = provider
            .load_component(&store, id)
            .await
            .map_err(|e| ExecError::Load(e.to_string()))?;

        // Cap slice empty at this rung; the dregg lease supplies real caps +
        // tenant at the bridge rung (the provider already threads both into the
        // seccomp/Landlock cage when present).
        let mut instance = provider
            .instantiate_with_caps(&component, &[], TENANT)
            .await
            .map_err(|e| ExecError::Instantiate(e.to_string()))?;

        let call = provider.call(&mut instance, ENTRYPOINT, &args);
        let values = match tokio::time::timeout(timeout, call).await {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => return Err(ExecError::Call(e.to_string())),
            Err(_elapsed) => {
                // Drop the call future + instance; the provider (dropped at the
                // end of this block) kills the child via kill_on_drop.
                drop(instance);
                return Err(ExecError::Timeout {
                    secs: timeout.as_secs(),
                });
            }
        };

        Ok(Output {
            values: values.iter().map(value_to_string).collect(),
            enforcement,
        })
    })
}

/// Drive the real Node.js provider (`polyana-node-provider`) — a genuine
/// `node` subprocess, NOT the in-process V8 isolate pool. The workload `source`
/// is a JavaScript program that speaks polyana's newline-JSON wire (read
/// `sys.stdin` lines, reply `{"ok":[...]}` / `{"err":"..."}`); `input` is the
/// `args` array of a `{"fn":"run","args":[...]}` request, so the workload
/// receives real typed values.
///
/// Resource safety mirrors the Python tier: the call is wrapped in
/// [`workload_timeout`]; on timeout the provider is dropped, killing the child
/// (the provider sets `kill_on_drop`), so a runaway guest fails as
/// [`ExecError::Timeout`] without hanging. Enforcement is `OsSandbox` (seccomp
/// + Landlock) on Linux and `None` (process isolation only) on macOS; the
/// achieved level is surfaced in [`Output::enforcement`], never silently claimed.
#[cfg(feature = "node")]
fn run_on_node(source: &str, input: &[Input]) -> std::result::Result<Output, ExecError> {
    run_on_node_with_timeout(source, input, workload_timeout())
}

#[cfg(feature = "node")]
fn run_on_node_with_timeout(
    source: &str,
    input: &[Input],
    timeout: std::time::Duration,
) -> std::result::Result<Output, ExecError> {
    use polyana_core::artifact::{ArtifactKind, ArtifactMetadata, ArtifactStore};
    use polyana_core::provider::ExecutionProvider;
    use polyana_node_provider::NodeProvider;

    let args: Vec<_> = input.iter().map(Input::to_value).collect();
    let rt = build_runtime()?;
    rt.block_on(async move {
        let provider = NodeProvider::new();
        let enforcement = format!("{:?}", provider.enforcement_level());

        let store = ArtifactStore::new();
        let id = store
            .store(
                ArtifactKind::NativeBinary,
                source.as_bytes().to_vec(),
                ArtifactMetadata::default(),
            )
            .map_err(|e| ExecError::Load(e.to_string()))?;

        let component = provider
            .load_component(&store, id)
            .await
            .map_err(|e| ExecError::Load(e.to_string()))?;

        // Cap slice empty at this rung; the dregg lease supplies real caps +
        // tenant at the bridge rung (the provider threads both into the
        // seccomp/Landlock cage + the guest's `require('__polyana__')` env).
        let mut instance = provider
            .instantiate_with_caps(&component, &[], TENANT)
            .await
            .map_err(|e| ExecError::Instantiate(e.to_string()))?;

        let call = provider.call(&mut instance, ENTRYPOINT, &args);
        let values = match tokio::time::timeout(timeout, call).await {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => return Err(ExecError::Call(e.to_string())),
            Err(_elapsed) => {
                drop(instance);
                return Err(ExecError::Timeout {
                    secs: timeout.as_secs(),
                });
            }
        };

        Ok(Output {
            values: values.iter().map(value_to_string).collect(),
            enforcement,
        })
    })
}

/// Drive the Firecracker microVM provider — the [`CapTier::MicroVm`] strong-
/// isolation tier (a per-workload microVM with its own guest kernel behind the
/// KVM boundary; the fly.io / AWS-Lambda model).
///
/// The live VM boot requires three host facilities: the `firecracker` binary on
/// PATH, `/dev/kvm` (Linux + hardware virtualization), and a guest kernel +
/// rootfs image. This function gates on the first two up front and refuses
/// cleanly when either is missing — never a silent downgrade to a weaker tier.
/// Where they ARE present it constructs the provider, hands it the
/// `{"lang","source"}` workload spec, boots the VM, and drives the guest over
/// the vsock + JSON wire: the in-guest agent runs the real runtime and returns
/// the result. The VM is torn down when the provider drops (the firecracker
/// child is reaped via `kill_on_drop`).
#[cfg(feature = "firecracker")]
fn run_on_microvm(
    lang: &str,
    source: &str,
    input: &[Input],
) -> std::result::Result<Output, ExecError> {
    use polyana_core::artifact::{ArtifactKind, ArtifactMetadata, ArtifactStore};
    use polyana_core::provider::ExecutionProvider;
    use polyana_firecracker_provider::FirecrackerProvider;

    let cfg = microvm_config();
    let have_kvm = std::path::Path::new("/dev/kvm").exists();
    let have_fc = firecracker_binary_present(&cfg.firecracker_binary);
    if !have_kvm || !have_fc {
        let mut missing = Vec::new();
        if !have_fc {
            missing.push(format!("the `{}` binary", cfg.firecracker_binary.display()));
        }
        if !have_kvm {
            missing.push("/dev/kvm (Linux + hardware virtualization)".to_string());
        }
        return Err(ExecError::TierNotServed {
            lang: lang.to_string(),
            tier: CapTier::MicroVm,
            detail: format!(
                "the MicroVm (firecracker) tier needs {}; it is unavailable on this host, so the \
                 microVM was NOT booted (no silent downgrade to a weaker tier). Run untrusted \
                 MicroVm workloads on a KVM-capable node, e.g. node-a, or use Caged \
                 (native+seccomp) / Sandboxed (wasm) where hardware isolation isn't required",
                missing.join(" and ")
            ),
        });
    }

    let args: Vec<_> = input.iter().map(Input::to_value).collect();
    // Two postures: jailed (cgroup + namespaces + chroot + privilege drop, the
    // production isolation posture — reports `FullVm`) when `DREGGNET_FC_JAILER`
    // is set, else direct-spawn (the dev/CI path — reports `Container`). The
    // jailed path requires the process to start as root (the jailer's
    // precondition); where it can't build the jail it surfaces a clean
    // `Instantiate` error rather than a silent un-jailed run.
    let provider = match microvm_jailer_config() {
        Some(jc) => FirecrackerProvider::with_jailer(cfg, jc),
        None => FirecrackerProvider::new(cfg),
    };
    let enforcement = format!("{:?}", provider.enforcement_level());

    // The microVM is lang-agnostic at the KVM boundary; the guest runs the
    // language runtime inside. We hand the provider a workload spec envelope
    // — `{"lang","source"}` — as the artifact; the provider splices the call's
    // fn/args and ships it over the vsock wire to the in-guest agent, which
    // runs the real runtime (the same newline-JSON wire the host-side native
    // tiers speak, carried into the VM).
    let spec = serde_json::json!({ "lang": lang, "source": source }).to_string();

    let rt = build_runtime()?;
    rt.block_on(async move {
        let store = ArtifactStore::new();
        let id = store
            .store(
                ArtifactKind::NativeBinary,
                spec.into_bytes(),
                ArtifactMetadata::default(),
            )
            .map_err(|e| ExecError::Load(e.to_string()))?;

        let component = provider
            .load_component(&store, id)
            .await
            .map_err(|e| ExecError::Load(e.to_string()))?;

        let mut instance = provider
            .instantiate(&component)
            .await
            .map_err(|e| ExecError::Instantiate(e.to_string()))?;

        let timeout = workload_timeout();
        let call = provider.call(&mut instance, ENTRYPOINT, &args);
        let values = match tokio::time::timeout(timeout, call).await {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => return Err(ExecError::Call(e.to_string())),
            Err(_elapsed) => {
                drop(instance);
                return Err(ExecError::Timeout {
                    secs: timeout.as_secs(),
                });
            }
        };

        Ok(Output {
            values: values.iter().map(value_to_string).collect(),
            enforcement,
        })
    })
}

/// Build the Firecracker provider config, taking the image/binary paths from
/// deployment env knobs (not feature gates) and falling back to the provider's
/// defaults. These name *where the operator provisioned the image* — there is
/// no single canonical location, so they're runtime config, the same shape as
/// [`DREGGNET_EXEC_TIMEOUT_SECS`]:
///
/// - `DREGGNET_FC_BIN`        — path to the `firecracker` binary
/// - `DREGGNET_FC_KERNEL`     — guest kernel image (`vmlinux.bin`)
/// - `DREGGNET_FC_ROOTFS`     — rootfs block image (`rootfs.ext4`)
/// - `DREGGNET_FC_SOCKET_DIR` — directory for the per-VM API + vsock sockets
/// - `DREGGNET_FC_BOOT_ARGS`  — kernel cmdline (defaults boot the RO root drive)
#[cfg(feature = "firecracker")]
fn microvm_config() -> polyana_firecracker_provider::FirecrackerConfig {
    use polyana_firecracker_provider::FirecrackerConfig;
    let mut cfg = FirecrackerConfig::default();
    if let Some(v) = std::env::var_os("DREGGNET_FC_BIN") {
        cfg.firecracker_binary = v.into();
    }
    if let Some(v) = std::env::var_os("DREGGNET_FC_KERNEL") {
        cfg.kernel_image_path = v.into();
    }
    if let Some(v) = std::env::var_os("DREGGNET_FC_ROOTFS") {
        cfg.rootfs_path = v.into();
    }
    if let Some(v) = std::env::var_os("DREGGNET_FC_SOCKET_DIR") {
        cfg.socket_dir = v.into();
    }
    // The default boot args mount the root drive (firecracker exposes it as
    // /dev/vda) read-only; override wholesale via the env knob if needed.
    cfg.boot_args = std::env::var("DREGGNET_FC_BOOT_ARGS")
        .unwrap_or_else(|_| "console=ttyS0 reboot=k panic=1 pci=off root=/dev/vda ro".to_string());
    cfg
}

/// Build the jailer launch config when the operator opts into the jailed
/// (production) posture via `DREGGNET_FC_JAILER` (any non-empty value turns it
/// on). The jailer pins each microVM to a cgroup, enters fresh namespaces,
/// `chroot`s it into a private jail root, and drops privilege — so a firecracker
/// compromise is boxed by the kernel's process walls, not just KVM. Returns
/// `None` (direct spawn) when the knob is unset.
///
/// Sub-knobs (all optional, sensible defaults — the same runtime-config shape as
/// [`microvm_config`], NOT feature gates):
///
/// - `DREGGNET_FC_JAILER`        — presence (any non-empty value) turns jailing on
/// - `DREGGNET_FC_JAILER_BIN`    — path to the `jailer` binary (default `jailer`)
/// - `DREGGNET_FC_CHROOT_BASE`   — jail root base dir (default `/srv/jailer`)
/// - `DREGGNET_FC_JAILER_UID`    — unprivileged uid to drop to (default `123`)
/// - `DREGGNET_FC_JAILER_GID`    — unprivileged gid to drop to (default `100`)
#[cfg(feature = "firecracker")]
fn microvm_jailer_config() -> Option<polyana_firecracker_provider::JailerConfig> {
    use polyana_firecracker_provider::JailerConfig;
    let on = std::env::var("DREGGNET_FC_JAILER")
        .ok()
        .map(|v| !v.trim().is_empty())
        .unwrap_or(false);
    if !on {
        return None;
    }
    let mut jc = JailerConfig::default();
    if let Some(v) = std::env::var_os("DREGGNET_FC_JAILER_BIN") {
        jc.jailer_binary = v.into();
    }
    if let Some(v) = std::env::var_os("DREGGNET_FC_CHROOT_BASE") {
        jc.chroot_base = v.into();
    }
    if let Ok(v) = std::env::var("DREGGNET_FC_JAILER_UID") {
        if let Ok(uid) = v.parse() {
            jc.uid = uid;
        }
    }
    if let Ok(v) = std::env::var("DREGGNET_FC_JAILER_GID") {
        if let Ok(gid) = v.parse() {
            jc.gid = gid;
        }
    }
    Some(jc)
}

/// Honest bail when the `firecracker` feature is OFF: the MicroVm tier is not
/// linked. Fails loudly rather than downgrading to a weaker backend.
#[cfg(not(feature = "firecracker"))]
fn run_on_microvm(
    lang: &str,
    source: &str,
    input: &[Input],
) -> std::result::Result<Output, ExecError> {
    let _ = (lang, source, input);
    Err(ExecError::NotWired(
        "dreggnet-exec: built without the `firecracker` feature — the MicroVm tier is not linked; \
         rebuild with `--features firecracker`"
            .into(),
    ))
}

/// Drive the [`CapTier::Gpu`] heavy-compute tier — a hardware-isolated VM with a
/// passed-through GPU (whole device via VFIO, or an NVIDIA MIG slice), metered
/// in GPU-seconds.
///
/// This is the one axis the Liftoff matrix flagged Akash ahead on. The tier's
/// design + seam are wired here; the **live passthrough boot is hardware-gated**
/// (it needs a discrete GPU bound to `vfio-pci` and a passthrough-capable VMM),
/// so this function GATES and refuses cleanly — naming exactly what is missing
/// — rather than ever silently downgrading to a weaker (CPU-only / no-GPU)
/// backend:
///
/// 1. No GPU device on the host (`/dev/nvidia*` / `/dev/dri/renderD*`) → refuse,
///    naming the missing GPU hardware (the node-a / CPU-box case).
/// 2. GPU present but no passthrough-VM provider configured
///    (`DREGGNET_GPU_VMM` unset) → refuse, naming the missing provider seam —
///    the hardware-gated remaining (Cloud-Hypervisor / QEMU + VFIO, or a MIG
///    partition manager; Firecracker is CPU-only and CANNOT serve this tier).
///
/// The cap-grade carries the [`gpu::GpuClass`] + the [`gpu::GpuBounds`]
/// (GPU-seconds + GPU-memory ceiling) the live provider enforces and meters; see
/// `docs/COMPUTE-TIERS.md` for the full design and the live-fleet rung.
#[cfg(feature = "polyana")]
fn run_on_gpu(lang: &str, source: &str, input: &[Input]) -> std::result::Result<Output, ExecError> {
    let _ = (source, input);
    let gpus = gpu::host_gpu_devices();
    if gpus.is_empty() {
        return Err(ExecError::TierNotServed {
            lang: lang.to_string(),
            tier: CapTier::Gpu,
            detail: "the Gpu tier needs a GPU device (no /dev/nvidia* or /dev/dri/renderD* on this \
                     host); it is unavailable here, so NO weaker (CPU-only) backend was substituted \
                     (no silent downgrade). Run GPU workloads on a GPU node with a discrete card \
                     bound to vfio-pci"
                .into(),
        });
    }
    let vmm = std::env::var("DREGGNET_GPU_VMM")
        .ok()
        .filter(|v| !v.trim().is_empty());
    let Some(vmm) = vmm else {
        return Err(ExecError::TierNotServed {
            lang: lang.to_string(),
            tier: CapTier::Gpu,
            detail: format!(
                "a GPU is present ({} device(s)) but no passthrough-VM provider is configured \
                 (DREGGNET_GPU_VMM unset). The Gpu tier routes to a VFIO/MIG passthrough VMM \
                 (Cloud-Hypervisor / QEMU), NOT Firecracker (which is CPU-only). Wiring the live \
                 provider is the hardware-gated / reviewed-go fleet rung — see docs/COMPUTE-TIERS.md",
                gpus.len()
            ),
        });
    };
    // Hardware + VMM both named: the live passthrough boot is the reviewed-go
    // fleet rung (a real GPU bound to vfio-pci + the passthrough-VM provider
    // impl). Refuse with the exact remaining work rather than fake a run.
    Err(ExecError::TierNotServed {
        lang: lang.to_string(),
        tier: CapTier::Gpu,
        detail: format!(
            "GPU present and VMM `{vmm}` configured — the GPU-passthrough VM provider (the live \
             boot of a VFIO/MIG VM running the guest) is the hardware-gated / reviewed-go fleet \
             rung, not yet linked into this build. The tier routing, GPU detection, GpuClass, and \
             GPU-seconds metering ARE wired (see the `gpu` module); the live boot lands on real \
             GPU hardware. See docs/COMPUTE-TIERS.md"
        ),
    })
}

/// Honest bail when the `polyana` feature is OFF: the Gpu tier is not linked.
#[cfg(not(feature = "polyana"))]
fn run_on_gpu(lang: &str, source: &str, input: &[Input]) -> std::result::Result<Output, ExecError> {
    let _ = (lang, source, input);
    Err(ExecError::NotWired(
        "dreggnet-exec: built without the `polyana` feature — the Gpu tier is not linked".into(),
    ))
}

/// `true` when the configured Firecracker binary is resolvable — an absolute
/// path that exists, or a bare name found on `$PATH`.
#[cfg(feature = "firecracker")]
fn firecracker_binary_present(bin: &std::path::Path) -> bool {
    if bin.is_absolute() {
        return bin.exists();
    }
    let Some(path) = std::env::var_os("PATH") else {
        return false;
    };
    std::env::split_paths(&path).any(|dir| dir.join(bin).is_file())
}

/// Drive the native-process provider (`OsSandbox`) on a host binary — the
/// `Caged` tier. The binary runs as a child process under a seccomp-bpf syscall
/// allowlist + a Landlock filesystem allowlist (Linux), speaking polyana's
/// newline-JSON wire protocol (`{"fn":"run","args":[]}` → `{"ok":[..]}`).
///
/// Cross-platform compile, Linux-only sandbox: off-Linux the provider's
/// `instantiate` returns a clean error rather than running the binary
/// unsandboxed, so this function returns `Err` on macOS instead of a fake run.
#[cfg(feature = "caged")]
fn run_on_native_process(
    source: &str,
    input: &[Input],
    cap_tier: CapTier,
) -> std::result::Result<Output, ExecError> {
    use polyana_core::artifact::{ArtifactKind, ArtifactMetadata, ArtifactStore};
    use polyana_core::provider::ExecutionProvider;
    use polyana_native_process_provider::NativeProcessProvider;

    let args: Vec<_> = input.iter().map(Input::to_value).collect();

    let provider = NativeProcessProvider::new();
    check_floor(&provider, cap_tier)?;
    let enforcement = format!("{:?}", provider.enforcement_level());

    // The native-process provider treats artifact bytes as a raw host
    // executable (ELF, shebang script, …). `source` is text here (a shebang
    // script); a later rung takes `&[u8]` for arbitrary ELF.
    let binary = source.as_bytes().to_vec();

    let rt = build_runtime()?;
    rt.block_on(async move {
        let store = ArtifactStore::new();
        let id = store
            .store(
                ArtifactKind::NativeBinary,
                binary,
                ArtifactMetadata::default(),
            )
            .map_err(|e| ExecError::Load(e.to_string()))?;

        let component = provider
            .load_component(&store, id)
            .await
            .map_err(|e| ExecError::Load(e.to_string()))?;

        // Empty cap slice + the static tenant tag at this rung (the dregg lease
        // supplies both at the bridge rung). The native-process provider binds
        // seccomp/Landlock at fork/exec; the cage applies on Linux and errors
        // cleanly elsewhere.
        let mut instance = provider
            .instantiate_with_caps(&component, &[], TENANT)
            .await
            .map_err(|e| ExecError::Instantiate(e.to_string()))?;

        let timeout = workload_timeout();
        let call = provider.call(&mut instance, ENTRYPOINT, &args);
        let values = match tokio::time::timeout(timeout, call).await {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => return Err(ExecError::Call(e.to_string())),
            Err(_elapsed) => {
                drop(instance);
                return Err(ExecError::Timeout {
                    secs: timeout.as_secs(),
                });
            }
        };

        Ok(Output {
            values: values.iter().map(value_to_string).collect(),
            enforcement,
        })
    })
}

/// The tenant tag passed to the cap-gated instantiate path. Provisional at this
/// rung (one DreggNet exec tenant); the bridge rung derives it from the dregg
/// execution-lease principal.
#[cfg(feature = "polyana")]
const TENANT: &str = "dreggnet-exec";

/// Refuse to run if the chosen provider's enforcement is below the floor the
/// cap-tier implies. A stronger provider satisfies a weaker floor; a weaker
/// provider is never silently substituted.
#[cfg(feature = "polyana")]
fn check_floor<P: polyana_core::provider::ExecutionProvider>(
    provider: &P,
    cap_tier: CapTier,
) -> std::result::Result<(), ExecError> {
    let floor = cap_tier_enforcement(cap_tier);
    if provider.enforcement_level() < floor {
        return Err(ExecError::FloorUnmet {
            provider: provider.name().to_string(),
            have: format!("{:?}", provider.enforcement_level()),
            need: format!("{floor:?}"),
            tier: cap_tier,
        });
    }
    Ok(())
}

/// Build a current-thread tokio runtime so the async provider trait can be
/// driven from a synchronous DreggNet-facing call.
#[cfg(feature = "polyana")]
fn build_runtime() -> std::result::Result<tokio::runtime::Runtime, ExecError> {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| ExecError::Runtime(e.to_string()))
}

/// Map a DreggNet [`CapTier`] onto the polyana enforcement floor it implies.
///
/// This is the minimum isolation the selected provider must guarantee; a
/// stronger provider satisfies a weaker floor. The `Sandboxed` → `WasmSandbox`
/// and `JitSandboxed` → `WasmFullSandbox` rows are *exact* — each names the
/// floor only that tier's wired provider clears. `Caged` → `OsSandbox` is the
/// native+seccomp tier (native binary / CPython / Node). `MicroVm` →
/// `Container` is the Firecracker floor (the provider reports `Container` until
/// the core `EnforcementLevel` grows a `FullVm` variant). The faithful
/// lease-grade → tier → provider routing (with a non-empty cap slice) lands at
/// the bridge rung.
#[cfg(feature = "polyana")]
fn cap_tier_enforcement(tier: CapTier) -> polyana_core::provider::EnforcementLevel {
    use polyana_core::provider::EnforcementLevel;
    match tier {
        CapTier::Sandboxed => EnforcementLevel::WasmSandbox,
        CapTier::JitSandboxed => EnforcementLevel::WasmFullSandbox,
        CapTier::Caged => EnforcementLevel::OsSandbox,
        // The floor any *booted* microVM clears. A direct firecracker launch
        // reports exactly `Container`; the JAILED launch (production posture,
        // `DREGGNET_FC_JAILER`) reports the stronger `FullVm` — above this floor,
        // so it's never a downgrade. A caller that needs a hard `FullVm` floor
        // requests the `Gpu` tier (below) or the bridge rung maps a cap-grade
        // that requires the jailer.
        CapTier::MicroVm => EnforcementLevel::Container,
        // The GPU/heavy-compute tier requires a real hardware VM (GPU
        // passthrough is only safe behind a VM boundary), so its floor is
        // `FullVm` — cleared only by a jailed microVM-class provider, never by a
        // weaker backend.
        CapTier::Gpu => EnforcementLevel::FullVm,
    }
}

/// Render a polyana `Value` to the string surface DreggNet returns.
#[cfg(feature = "polyana")]
fn value_to_string(v: &polyana_core::provider::Value) -> String {
    use polyana_core::provider::Value;
    match v {
        Value::I32(n) => n.to_string(),
        Value::I64(n) => n.to_string(),
        Value::F32(f) => f.to_string(),
        Value::F64(f) => f.to_string(),
        Value::String(s) => s.clone(),
        Value::Bytes(b) => format!("{b:02x?}"),
        Value::Json(j) => j.to_string(),
    }
}

/// Honest stub when the `polyana` feature is OFF (`--no-default-features`).
///
/// Fails loudly so no caller can mistake an un-wired build for a real run.
#[cfg(not(feature = "polyana"))]
pub fn run_workload(lang: &str, source: &str, cap_tier: CapTier) -> Result<Output> {
    Ok(run_workload_with_input(lang, source, cap_tier, &[])?)
}

/// Honest stub when the `polyana` feature is OFF (`--no-default-features`).
#[cfg(not(feature = "polyana"))]
pub fn run_workload_with_input(
    lang: &str,
    source: &str,
    cap_tier: CapTier,
    input: &[Input],
) -> std::result::Result<Output, ExecError> {
    let _ = (lang, source, cap_tier, input);
    Err(ExecError::NotWired(
        "dreggnet-exec: built without the `polyana` feature — execution engine not linked. \
         Rebuild with the default features (or `--features polyana`)."
            .into(),
    ))
}

/// The GPU cap-tier's typed surface: the GPU class a cap-grade names, the
/// metered GPU-seconds bound, and the host GPU probe. These are the cap-bounds
/// the live passthrough provider enforces + meters. They are pure types (no
/// hardware dependency), so the GPU tier's design is exercised + tested without
/// a GPU on the box — the live passthrough boot is the hardware-gated rung (see
/// [`run_on_gpu`] and `docs/COMPUTE-TIERS.md`).
pub mod gpu {
    use std::path::Path;
    use std::time::Duration;

    /// The GPU resource a cap-grade authorizes. A workload either gets a whole
    /// physical GPU (VFIO passthrough of the PCI device) or a MIG slice (an
    /// NVIDIA A100/H100 partitioned into isolated GPU instances, each a fixed
    /// compute + memory fraction). The class fixes the GPU-memory ceiling and
    /// the metering rate the live provider binds.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum GpuClass {
        /// A MIG slice: `compute_sevenths` of the GPU (the MIG granularity is
        /// 1/7th of an A100/H100) + a fixed memory partition (GiB). The standard
        /// profiles are 1g.5gb, 2g.10gb, 3g.20gb, 7g.40gb.
        Mig {
            compute_sevenths: u8,
            memory_gib: u16,
        },
        /// A whole passed-through GPU (the full PCI device) with its total memory.
        Whole { memory_gib: u16 },
    }

    impl GpuClass {
        /// The GPU-memory ceiling (MiB) this class grants — the hard cap the
        /// passthrough provider sets on the guest's visible VRAM.
        pub fn memory_mib(self) -> u64 {
            match self {
                GpuClass::Mig { memory_gib, .. } | GpuClass::Whole { memory_gib } => {
                    memory_gib as u64 * 1024
                }
            }
        }

        /// The fraction of a physical GPU's compute this class commands, in
        /// 1/7ths (the MIG granularity); a whole GPU is 7/7.
        pub fn compute_sevenths(self) -> u8 {
            match self {
                GpuClass::Mig {
                    compute_sevenths, ..
                } => compute_sevenths,
                GpuClass::Whole { .. } => 7,
            }
        }
    }

    /// The cap-bounds a GPU lease carries: the GPU class + a hard GPU-seconds
    /// budget. The live provider refuses to start a workload whose budget is
    /// spent and tears one down when it overruns — the GPU analogue of the
    /// wall-clock timeout the CPU tiers enforce.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct GpuBounds {
        pub class: GpuClass,
        /// Hard ceiling on metered GPU-seconds for the lease.
        pub max_gpu_seconds: u64,
    }

    /// A GPU-seconds meter: GPU-time accrues while a workload holds the GPU,
    /// scaled by the class's compute fraction (a 1g MIG slice bills 1/7th the
    /// GPU-seconds of a whole GPU for the same wall-clock). It settles through
    /// the same conserving exactly-once `$DREGG` rail the CPU / hosting meters
    /// use (the bridge rung wires the settlement; this is the accounting).
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
    pub struct GpuMeter {
        gpu_seconds_milli: u64,
    }

    impl GpuMeter {
        pub fn new() -> Self {
            Self::default()
        }

        /// Accrue `wall` wall-clock at `class`'s compute fraction. Returns the
        /// running GPU-seconds (milli-resolution) so a caller can compare to the
        /// bound.
        pub fn tick(&mut self, class: GpuClass, wall: Duration) -> u64 {
            let scaled = wall.as_millis() as u64 * class.compute_sevenths() as u64 / 7;
            self.gpu_seconds_milli = self.gpu_seconds_milli.saturating_add(scaled);
            self.gpu_seconds_milli
        }

        /// Total metered GPU-seconds (whole seconds, rounded down).
        pub fn gpu_seconds(self) -> u64 {
            self.gpu_seconds_milli / 1000
        }

        /// `true` once the meter has reached `bounds.max_gpu_seconds` — the
        /// signal to refuse / tear down (the lease's GPU budget is spent).
        pub fn over_budget(self, bounds: &GpuBounds) -> bool {
            self.gpu_seconds() >= bounds.max_gpu_seconds
        }
    }

    /// Probe the host for GPU character devices: NVIDIA (`/dev/nvidia0..`) and
    /// DRM render nodes (`/dev/dri/renderD128..`). Returns the device paths
    /// found — empty on a CPU-only host (so the Gpu tier refuses cleanly there).
    pub fn host_gpu_devices() -> Vec<String> {
        let mut found = Vec::new();
        for n in 0..8 {
            let nv = format!("/dev/nvidia{n}");
            if Path::new(&nv).exists() {
                found.push(nv);
            }
        }
        for n in 128..136 {
            let dri = format!("/dev/dri/renderD{n}");
            if Path::new(&dri).exists() {
                found.push(dri);
            }
        }
        found
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn mig_class_memory_and_compute() {
            let c = GpuClass::Mig {
                compute_sevenths: 1,
                memory_gib: 5,
            };
            assert_eq!(c.memory_mib(), 5 * 1024);
            assert_eq!(c.compute_sevenths(), 1);
            let w = GpuClass::Whole { memory_gib: 40 };
            assert_eq!(w.compute_sevenths(), 7);
            assert_eq!(w.memory_mib(), 40 * 1024);
        }

        #[test]
        fn meter_scales_by_compute_fraction() {
            // A whole GPU bills full wall-clock; a 1/7 MIG slice bills 1/7th.
            let mut whole = GpuMeter::new();
            whole.tick(GpuClass::Whole { memory_gib: 40 }, Duration::from_secs(7));
            assert_eq!(whole.gpu_seconds(), 7);

            let mut mig = GpuMeter::new();
            mig.tick(
                GpuClass::Mig {
                    compute_sevenths: 1,
                    memory_gib: 5,
                },
                Duration::from_secs(7),
            );
            assert_eq!(mig.gpu_seconds(), 1);
        }

        #[test]
        fn meter_trips_budget() {
            let bounds = GpuBounds {
                class: GpuClass::Whole { memory_gib: 40 },
                max_gpu_seconds: 10,
            };
            let mut m = GpuMeter::new();
            m.tick(bounds.class, Duration::from_secs(9));
            assert!(!m.over_budget(&bounds));
            m.tick(bounds.class, Duration::from_secs(2));
            assert!(m.over_budget(&bounds));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// With the `polyana` feature OFF, `run_workload` must FAIL loudly rather
    /// than fake a success.
    #[cfg(not(feature = "polyana"))]
    #[test]
    fn run_workload_bails_without_polyana_feature() {
        assert!(run_workload("wasm", "", CapTier::Sandboxed).is_err());
    }

    /// The Sandboxed (wasmi interpreter) dogfood: `add(40, 2) == 42`.
    ///
    /// The workload exports `run`, which calls an inner `add` on the literals
    /// 40 and 2 — the `i32.add` genuinely executes inside the wasmi sandbox.
    #[cfg(feature = "polyana")]
    #[test]
    fn dogfood_add_40_2_equals_42_wasmi() {
        let source = r#"
            (module
              (func $add (param $a i32) (param $b i32) (result i32)
                local.get $a
                local.get $b
                i32.add)
              (func (export "run") (result i32)
                (call $add (i32.const 40) (i32.const 2))))
        "#;
        let out = run_workload("wat", source, CapTier::Sandboxed)
            .expect("wasmi should run the add dogfood");
        assert_eq!(out.values, vec!["42".to_string()]);
    }

    /// The JitSandboxed (wasmtime JIT) dogfood: the SAME `add(40, 2) == 42`,
    /// but through the stronger provider — a component-model workload whose
    /// `run` export lifts the inner core module's `i32.add`. The arithmetic
    /// runs under Cranelift codegen + the fuel meter, not on the host.
    #[cfg(feature = "polyana")]
    #[test]
    fn dogfood_add_40_2_equals_42_wasmtime() {
        let source = r#"
            (component
              (core module $m
                (func $add (param $a i32) (param $b i32) (result i32)
                  local.get $a
                  local.get $b
                  i32.add)
                (func (export "run") (result i32)
                  (call $add (i32.const 40) (i32.const 2))))
              (core instance $i (instantiate $m))
              (func (export "run") (result s32)
                (canon lift (core func $i "run"))))
        "#;
        let out = run_workload("wat", source, CapTier::JitSandboxed)
            .expect("wasmtime should run the add dogfood");
        assert_eq!(out.values, vec!["42".to_string()]);
    }

    /// No silent downgrade: the wasmi interpreter's enforcement level does NOT
    /// satisfy the JitSandboxed floor, so the floor check would refuse to run a
    /// JIT-tier workload on the interpreter. The wasmtime provider does clear
    /// it (exercised end-to-end by `dogfood_add_40_2_equals_42_wasmtime`).
    #[cfg(feature = "polyana")]
    #[test]
    fn jit_tier_floor_excludes_interpreter() {
        use polyana_core::provider::ExecutionProvider;
        use polyana_wasmi_provider::WasmiProvider;
        let wasmi = WasmiProvider::new();
        let jit_floor = cap_tier_enforcement(CapTier::JitSandboxed);
        assert!(
            wasmi.enforcement_level() < jit_floor,
            "wasmi ({:?}) must NOT satisfy the JitSandboxed floor ({:?}) — \
             else the stronger tier could silently downgrade to the interpreter",
            wasmi.enforcement_level(),
            jit_floor,
        );
        // And it DOES clear its own Sandboxed floor.
        assert!(wasmi.enforcement_level() >= cap_tier_enforcement(CapTier::Sandboxed));
    }

    /// An unwired language family is refused cleanly (no silent fallback).
    #[cfg(feature = "polyana")]
    #[test]
    fn unknown_lang_is_refused() {
        assert!(run_workload("python", "print(42)", CapTier::Sandboxed).is_err());
    }

    /// Cross-family / hardware-gated tiers refuse cleanly rather than running
    /// on a weaker backend. A wasm workload can't claim the native `Caged`
    /// tier, and the `MicroVm` tier refuses on a host without firecracker +
    /// `/dev/kvm` (no silent downgrade).
    #[cfg(feature = "polyana")]
    #[test]
    fn cross_family_and_gated_tiers_bail() {
        assert!(run_workload("wasm", "", CapTier::Caged).is_err());
        // MicroVm is wired (firecracker) but hardware-gated: on a box without
        // /dev/kvm + the firecracker binary it must refuse, not downgrade.
        let micro = run_workload("wasm", "", CapTier::MicroVm);
        if std::path::Path::new("/dev/kvm").exists() {
            // On a KVM box the VM may boot; the slice-1 guest plane then errors
            // on `call`. Either way it must not silently succeed on a weaker tier.
            eprintln!("MicroVm on a /dev/kvm host: {micro:?}");
        } else {
            assert!(micro.is_err(), "MicroVm must refuse without /dev/kvm");
        }
    }

    /// Malformed source surfaces the assembly error rather than panicking.
    #[cfg(feature = "polyana")]
    #[test]
    fn malformed_wat_errors() {
        assert!(run_workload("wat", "(this is not wat", CapTier::Sandboxed).is_err());
        assert!(run_workload("wat", "(this is not a component", CapTier::JitSandboxed).is_err());
    }

    // -----------------------------------------------------------------
    // Real input-passing — args reach the entrypoint as genuine values,
    // NOT constants spliced into the source text.
    // -----------------------------------------------------------------

    /// wasmi runs an `add(a, b)` whose params are filled from real call args.
    /// The source is a constant template-free module — the 40 and 2 arrive as
    /// `Input` values, proving input-passing without the templated-WAT hack.
    #[cfg(feature = "polyana")]
    #[test]
    fn wasmi_runs_with_real_args() {
        let source = r#"
            (module
              (func (export "run") (param $a i32) (param $b i32) (result i32)
                local.get $a
                local.get $b
                i32.add))
        "#;
        let out = run_workload_with_input(
            "wat",
            source,
            CapTier::Sandboxed,
            &[Input::I32(40), Input::I32(2)],
        )
        .expect("wasmi runs with real args");
        assert_eq!(out.values, vec!["42".to_string()]);
        assert_eq!(out.enforcement, "WasmSandbox");
    }

    /// wasmtime (component model) runs an `add(a, b)` from real call args.
    #[cfg(feature = "polyana")]
    #[test]
    fn wasmtime_runs_with_real_args() {
        let source = r#"
            (component
              (core module $m
                (func (export "run") (param $a i32) (param $b i32) (result i32)
                  local.get $a
                  local.get $b
                  i32.add))
              (core instance $i (instantiate $m))
              (func (export "run") (param "a" s32) (param "b" s32) (result s32)
                (canon lift (core func $i "run"))))
        "#;
        let out = run_workload_with_input(
            "wat",
            source,
            CapTier::JitSandboxed,
            &[Input::I32(40), Input::I32(2)],
        )
        .expect("wasmtime runs with real args");
        assert_eq!(out.values, vec!["42".to_string()]);
        assert_eq!(out.enforcement, "WasmFullSandbox");
    }

    /// The numeric-only wasmi tier rejects a string arg with a clean typed
    /// error rather than a deep provider failure.
    #[cfg(feature = "polyana")]
    #[test]
    fn wasmi_rejects_string_arg() {
        let source = r#"(module (func (export "run") (result i32) (i32.const 0)))"#;
        let err = run_workload_with_input(
            "wat",
            source,
            CapTier::Sandboxed,
            &[Input::Text("nope".into())],
        )
        .expect_err("string arg refused on numeric-only wasmi");
        assert!(
            matches!(err, ExecError::UnsupportedArg { .. }),
            "got {err:?}"
        );
    }

    // -----------------------------------------------------------------
    // Sandbox escape — red-team SBX-1/2/3. A workload run through `exec`
    // with NO filesystem / network capability must NOT reach the host: the
    // empty cap slice exec hands the provider is honored as DENY-ALL, never
    // the old `grant_all` root that preopened host `/` read-write. The
    // host-reach DENIAL itself (no preopens, network Deny under empty caps)
    // is proven at polyana's projection seam — the load-bearing layer — by
    // `polyana-integration-tests`' `wasmtime_capability_depth_test`
    // (`empty_capset_projects_to_no_preopen_and_deny_network`,
    // `root_grant_all_no_longer_preopens_host_root`,
    // `filesystem_cap_without_explicit_host_is_denied`,
    // `instantiate_with_caps_honors_slice_empty_denies_scoped_grants`) +
    // `polyana-wasmtime`'s `enforce::empty_capset_denies_all_imports`. The
    // tests below pin exec's own contract: the JIT tier drives that honored
    // deny-all slice, and deny-by-default does NOT break legitimate compute.
    // -----------------------------------------------------------------

    /// SBX-1 regression guard: a workload run with no cap (exec's current
    /// rung passes an empty slice) still executes pure compute correctly —
    /// the default-deny floor is closed WITHOUT breaking legitimate
    /// workloads. The arithmetic runs under the strong wasmtime sandbox.
    #[cfg(feature = "polyana")]
    #[test]
    fn jit_tier_runs_pure_compute_under_deny_all_caps() {
        let source = r#"
            (component
              (core module $m
                (func (export "run") (param $a i32) (param $b i32) (result i32)
                  local.get $a
                  local.get $b
                  i32.add))
              (core instance $i (instantiate $m))
              (func (export "run") (param "a" s32) (param "b" s32) (result s32)
                (canon lift (core func $i "run"))))
        "#;
        let out = run_workload_with_input(
            "wat",
            source,
            CapTier::JitSandboxed,
            &[Input::I32(40), Input::I32(2)],
        )
        .expect("deny-all (empty cap slice) still runs pure compute");
        assert_eq!(out.values, vec!["42".to_string()]);
        // It ran under the strong sandbox, not a downgraded/escaped tier.
        assert_eq!(out.enforcement, "WasmFullSandbox");
    }

    // -----------------------------------------------------------------
    // Real native CPython — a genuine python3 subprocess, real args, real
    // arithmetic. Skips when python3 is absent (the wasm tiers carry the
    // unconditional green coverage).
    // -----------------------------------------------------------------

    /// `true` when a usable `python3` is on PATH (or `$POLYANA_PYTHON_BIN`).
    #[cfg(feature = "python")]
    fn python3_available() -> bool {
        let bin = std::env::var("POLYANA_PYTHON_BIN").unwrap_or_else(|_| "python3".into());
        std::process::Command::new(bin)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// A guest that speaks polyana's newline-JSON wire and sums its args.
    #[cfg(feature = "python")]
    const PY_ADD_WORKLOAD: &str = r#"import sys, json
for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    req = json.loads(line)
    a = req.get("args", [])
    print(json.dumps({"ok": [a[0] + a[1]]}), flush=True)
"#;

    /// The headline native proof: REAL CPython adds REAL args (40 + 2) and
    /// returns 42 over the wire. Not wasm — a genuine `python3` child.
    #[cfg(feature = "python")]
    #[test]
    fn python_runs_real_cpython_with_args() {
        if !python3_available() {
            eprintln!("skipping: no python3 on PATH");
            return;
        }
        let out = run_workload_with_input(
            "python",
            PY_ADD_WORKLOAD,
            CapTier::Caged,
            &[Input::I64(40), Input::I64(2)],
        )
        .expect("real CPython runs the add workload");
        assert_eq!(out.values, vec!["42".to_string()]);
        // On macOS the cage can't engage (None); on Linux it's OsSandbox.
        // Either way the achieved level is surfaced, never silently claimed.
        assert!(
            out.enforcement == "OsSandbox" || out.enforcement == "None",
            "enforcement surfaced: {}",
            out.enforcement
        );
    }

    /// Real string/JSON input reaches CPython (not just integers) — the thing
    /// the templated-WAT integer hack could never do.
    #[cfg(feature = "python")]
    #[test]
    fn python_text_arg_roundtrips() {
        if !python3_available() {
            eprintln!("skipping: no python3 on PATH");
            return;
        }
        let guest = r#"import sys, json
for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    req = json.loads(line)
    name = req["args"][0]
    print(json.dumps({"ok": ["hello, " + name]}), flush=True)
"#;
        let out = run_workload_with_input(
            "python",
            guest,
            CapTier::Caged,
            &[Input::Text("ember".into())],
        )
        .expect("real CPython greets a string arg");
        assert_eq!(out.values, vec!["hello, ember".to_string()]);
    }

    /// Over-resource: a runaway guest (`while True`) is KILLED at the deadline
    /// and surfaces as a clean [`ExecError::Timeout`] — no hang, no panic.
    #[cfg(feature = "python")]
    #[test]
    fn python_runaway_times_out_cleanly() {
        if !python3_available() {
            eprintln!("skipping: no python3 on PATH");
            return;
        }
        // Never reads stdin; just spins. The provider writes the request, then
        // blocks on the reply that never comes — the deadline must fire.
        let runaway = "while True:\n    pass\n";
        let err = run_on_python_with_timeout(
            runaway,
            &[Input::I64(1)],
            std::time::Duration::from_secs(2),
        )
        .expect_err("runaway must be killed, not hang");
        assert!(matches!(err, ExecError::Timeout { .. }), "got {err:?}");
    }

    /// Malformed source: a Python syntax error exits the interpreter; the
    /// provider sees stdout EOF and we surface a clean [`ExecError::Call`]
    /// (no panic, no hang).
    #[cfg(feature = "python")]
    #[test]
    fn python_syntax_error_fails_cleanly() {
        if !python3_available() {
            eprintln!("skipping: no python3 on PATH");
            return;
        }
        let broken = "def (this is not python\n";
        let err = run_workload_with_input("python", broken, CapTier::Caged, &[])
            .expect_err("syntax error must fail cleanly");
        assert!(matches!(err, ExecError::Call(_)), "got {err:?}");
    }

    /// Built-without-`python` parity is covered by the lang router: an
    /// unknown lang is a clean typed error, never a panic.
    #[cfg(feature = "polyana")]
    #[test]
    fn unknown_lang_is_typed_error() {
        let err = run_workload_with_input("brainfuck", "+++", CapTier::Sandboxed, &[])
            .expect_err("unknown lang refused");
        assert!(matches!(err, ExecError::UnsupportedLang(_)), "got {err:?}");
    }

    /// `Caged` floor + provider identity (the `caged` feature).
    ///
    /// The native-process provider reports exactly `OsSandbox` — the `Caged`
    /// floor — so it clears `check_floor`. The wasm providers report a
    /// DIFFERENT enforcement identity, so neither is the `Caged` tier's
    /// provider. NB: polyana's `EnforcementLevel` ladder ranks the wasm tiers
    /// ABOVE `OsSandbox` (it orders on memory-isolation, not host-syscall
    /// mediation), so a numeric `<` floor would NOT exclude a wasm provider
    /// here — the exclusion is by provider identity (`!= OsSandbox`) + lang
    /// routing: only a native host binary reaches `Caged`, and that only runs
    /// on the OsSandbox native-process provider.
    #[cfg(feature = "caged")]
    #[test]
    fn caged_tier_native_clears_floor_wasm_is_not_its_provider() {
        use polyana_core::provider::{EnforcementLevel, ExecutionProvider};
        use polyana_native_process_provider::NativeProcessProvider;
        use polyana_wasmi_provider::WasmiProvider;

        let caged_floor = cap_tier_enforcement(CapTier::Caged);
        assert_eq!(caged_floor, EnforcementLevel::OsSandbox);

        // The native-process provider IS the OsSandbox tier → clears the floor.
        let native = NativeProcessProvider::new();
        assert_eq!(native.enforcement_level(), EnforcementLevel::OsSandbox);
        assert!(native.enforcement_level() >= caged_floor);

        // A wasm provider reports a different enforcement identity, so it is
        // not the Caged tier's provider (and a native binary can't run on it).
        let wasmi = WasmiProvider::new();
        assert_ne!(
            wasmi.enforcement_level(),
            EnforcementLevel::OsSandbox,
            "the wasm interpreter is not an OS-sandbox provider — it must not \
             stand in for the Caged tier's native-process backend"
        );
    }

    /// No cross-family routing: a wasm workload can't claim `Caged`, and a
    /// native workload can't claim a wasm tier (no silent provider-family swap).
    #[cfg(feature = "caged")]
    #[test]
    fn caged_routing_refuses_mismatched_lang() {
        // A wasm workload cannot claim the native-host-binary tier.
        assert!(run_workload("wasm", "", CapTier::Caged).is_err());
        // A native workload cannot claim a wasm tier.
        let script = "#!/bin/sh\nexit 0\n";
        assert!(run_workload("native", script, CapTier::Sandboxed).is_err());
        assert!(run_workload("native", script, CapTier::JitSandboxed).is_err());
    }

    /// The `Caged` dogfood: a shebang script that speaks polyana's newline-JSON
    /// wire protocol — read the `{"fn":"run","args":[]}` request, reply
    /// `{"ok":[42]}` — run as an OS-sandboxed (seccomp + Landlock) child.
    ///
    /// Linux-only and `#[ignore]`d: the seccomp/Landlock cage only engages on
    /// Linux, and even there some CI sandboxes forbid installing the filters,
    /// so this is a manual `--ignored` dogfood rather than a default-green test.
    /// The wasm tiers carry the default-green coverage.
    #[cfg(all(feature = "caged", target_os = "linux"))]
    #[test]
    #[ignore = "requires Linux with seccomp+landlock permitted; run with --ignored"]
    fn dogfood_caged_native_run_equals_42() {
        let source = "#!/bin/sh\nread _req\nprintf '{\"ok\":[42]}\\n'\n";
        let out = run_workload("native", source, CapTier::Caged)
            .expect("native-process should run the caged dogfood on Linux");
        assert_eq!(out.values, vec!["42".to_string()]);
    }

    // -----------------------------------------------------------------
    // Real native Node.js — a genuine `node` subprocess, real args, real
    // arithmetic. NOT the broken in-process V8 isolate pool. Skips when
    // `node` is absent (the wasm tiers carry the unconditional coverage).
    // -----------------------------------------------------------------

    /// `true` when a usable `node` is on PATH (or `$POLYANA_NODE_BIN`).
    #[cfg(feature = "node")]
    fn node_available() -> bool {
        let bin = std::env::var("POLYANA_NODE_BIN").unwrap_or_else(|_| "node".into());
        std::process::Command::new(bin)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// A guest that speaks polyana's newline-JSON wire and sums its args.
    #[cfg(feature = "node")]
    const JS_ADD_WORKLOAD: &str = r#"let buf = '';
process.stdin.setEncoding('utf8');
process.stdin.on('data', (chunk) => {
  buf += chunk;
  let nl;
  while ((nl = buf.indexOf('\n')) >= 0) {
    const line = buf.slice(0, nl).trim();
    buf = buf.slice(nl + 1);
    if (!line) continue;
    const req = JSON.parse(line);
    const a = req.args || [];
    process.stdout.write(JSON.stringify({ ok: [a[0] + a[1]] }) + '\n');
  }
});
"#;

    /// The headline Node proof: REAL node adds REAL args (40 + 2) → 42 over the
    /// wire. Not wasm, not an isolate pool — a genuine `node` child, metered.
    #[cfg(feature = "node")]
    #[test]
    fn node_runs_real_node_with_args() {
        if !node_available() {
            eprintln!("skipping: no node on PATH");
            return;
        }
        let out = run_workload_with_input(
            "node",
            JS_ADD_WORKLOAD,
            CapTier::Caged,
            &[Input::I64(40), Input::I64(2)],
        )
        .expect("real node runs the add workload");
        assert_eq!(out.values, vec!["42".to_string()]);
        // macOS: None (process isolation); Linux: OsSandbox. Always surfaced.
        assert!(
            out.enforcement == "OsSandbox" || out.enforcement == "None",
            "enforcement surfaced: {}",
            out.enforcement
        );
    }

    /// Real string input reaches Node (not just integers) — a genuine handler.
    #[cfg(feature = "node")]
    #[test]
    fn node_text_arg_roundtrips() {
        if !node_available() {
            eprintln!("skipping: no node on PATH");
            return;
        }
        let guest = r#"let buf = '';
process.stdin.setEncoding('utf8');
process.stdin.on('data', (chunk) => {
  buf += chunk;
  let nl;
  while ((nl = buf.indexOf('\n')) >= 0) {
    const line = buf.slice(0, nl).trim();
    buf = buf.slice(nl + 1);
    if (!line) continue;
    const req = JSON.parse(line);
    process.stdout.write(JSON.stringify({ ok: ['hello, ' + req.args[0]] }) + '\n');
  }
});
"#;
        let out = run_workload_with_input(
            "node",
            guest,
            CapTier::Caged,
            &[Input::Text("ember".into())],
        )
        .expect("real node greets a string arg");
        assert_eq!(out.values, vec!["hello, ember".to_string()]);
    }

    /// Over-resource: a runaway guest (`while(true){}`) is KILLED at the
    /// deadline → clean [`ExecError::Timeout`], no hang, no panic.
    #[cfg(feature = "node")]
    #[test]
    fn node_runaway_times_out_cleanly() {
        if !node_available() {
            eprintln!("skipping: no node on PATH");
            return;
        }
        // Spins forever without reading stdin; the provider writes the request,
        // then blocks on the reply that never comes — the deadline must fire.
        let runaway = "while (true) {}\n";
        let err =
            run_on_node_with_timeout(runaway, &[Input::I64(1)], std::time::Duration::from_secs(2))
                .expect_err("runaway must be killed, not hang");
        assert!(matches!(err, ExecError::Timeout { .. }), "got {err:?}");
    }

    /// Malformed source: a JS syntax error exits node; the provider sees stdout
    /// EOF and we surface a clean [`ExecError::Call`] (no panic, no hang).
    #[cfg(feature = "node")]
    #[test]
    fn node_syntax_error_fails_cleanly() {
        if !node_available() {
            eprintln!("skipping: no node on PATH");
            return;
        }
        let broken = "function (this is not js\n";
        let err = run_workload_with_input("node", broken, CapTier::Caged, &[])
            .expect_err("syntax error must fail cleanly");
        assert!(matches!(err, ExecError::Call(_)), "got {err:?}");
    }

    // -----------------------------------------------------------------
    // MicroVm (firecracker) tier — wired + routed; the live VM boot is
    // hardware-gated on firecracker + /dev/kvm. Prove the routing + the
    // clean refusal where the hardware is absent (no silent downgrade).
    // -----------------------------------------------------------------

    /// On a host without `/dev/kvm` + the firecracker binary, the MicroVm tier
    /// refuses cleanly and the error names the missing hardware — it never
    /// downgrades to a weaker backend. On a KVM box the VM may boot (the
    /// slice-1 guest plane then errors on `call`).
    #[cfg(feature = "firecracker")]
    #[test]
    fn microvm_tier_gates_on_kvm_without_downgrade() {
        let res = run_workload_with_input("node", "console.log(42)", CapTier::MicroVm, &[]);
        let have_kvm = std::path::Path::new("/dev/kvm").exists();
        let have_fc = firecracker_binary_present(std::path::Path::new("firecracker"));
        if have_kvm && have_fc {
            // Hardware present: routing reached the provider. slice-1 has no
            // guest wire, so a successful boot still surfaces an error on call;
            // either way it must NOT silently succeed on a weaker tier.
            eprintln!("MicroVm on a KVM+firecracker host: {res:?}");
        } else {
            let err = res.expect_err("MicroVm must refuse without firecracker + /dev/kvm");
            assert!(
                matches!(
                    err,
                    ExecError::TierNotServed {
                        tier: CapTier::MicroVm,
                        ..
                    }
                ),
                "clean hardware-gated refusal, got {err:?}"
            );
            assert!(
                format!("{err}").contains("kvm") || format!("{err}").contains("firecracker"),
                "refusal names the missing hardware: {err}"
            );
        }
    }

    /// The Gpu (heavy-compute) tier never silently downgrades: it refuses
    /// cleanly with a typed `TierNotServed` for the Gpu tier whether the host
    /// has no GPU (names the missing GPU hardware) or a GPU but no configured
    /// passthrough VMM (names the missing provider seam). Either way it must NOT
    /// run on a weaker CPU-only backend. The error message names the gate.
    #[cfg(feature = "polyana")]
    #[test]
    fn gpu_tier_refuses_without_passthrough_stack() {
        let err = run_workload_with_input("python", "print(1)", CapTier::Gpu, &[])
            .expect_err("Gpu tier must refuse without a GPU passthrough stack");
        assert!(
            matches!(
                err,
                ExecError::TierNotServed {
                    tier: CapTier::Gpu,
                    ..
                }
            ),
            "clean GPU-gated refusal, got {err:?}"
        );
        let msg = format!("{err}");
        assert!(
            msg.to_lowercase().contains("gpu"),
            "the refusal names the GPU gate: {msg}"
        );
    }

    /// The Gpu tier's floor is `FullVm` — only a real hardware VM clears it (GPU
    /// passthrough is unsafe without a VM boundary), never a weaker backend.
    #[cfg(feature = "polyana")]
    #[test]
    fn gpu_tier_floor_is_full_vm() {
        use polyana_core::provider::EnforcementLevel;
        assert_eq!(cap_tier_enforcement(CapTier::Gpu), EnforcementLevel::FullVm);
        // FullVm is the strongest tier — it clears every other floor.
        assert!(EnforcementLevel::FullVm >= cap_tier_enforcement(CapTier::MicroVm));
        assert!(EnforcementLevel::FullVm >= cap_tier_enforcement(CapTier::Caged));
    }

    /// Built-without-`firecracker`: the MicroVm tier is a clean NotWired bail.
    #[cfg(all(feature = "polyana", not(feature = "firecracker")))]
    #[test]
    fn microvm_without_feature_is_not_wired() {
        let err = run_workload_with_input("node", "", CapTier::MicroVm, &[])
            .expect_err("MicroVm not linked without the firecracker feature");
        assert!(matches!(err, ExecError::NotWired(_)), "got {err:?}");
    }
}
