//! `dreggnet-exec` — DreggNet's execution surface.
//!
//! [`run_workload`] runs a (dregg-authorized) workload at the sandbox grade the
//! dregg lease authorizes. The [`CapTier::Sandboxed`] tier is backed by an OWNED
//! wasm engine — the pure-Rust, zero-`unsafe` `wasmi` interpreter (a
//! DreggNet-owned dependency, no external submodule) — instantiated against an
//! EMPTY [`wasmi::Linker`], so the guest is offered NO host imports and reaches
//! nothing on the host. The `add(40,2)=42` dogfood genuinely executes here.
//!
//! ## The tiers
//!
//! | [`CapTier`]              | lang           | backing                                   |
//! |--------------------------|----------------|-------------------------------------------|
//! | [`CapTier::Sandboxed`]   | `wasm`/`wat`   | OWNED wasmi interpreter (real execution)  |
//! | [`CapTier::JitSandboxed`]| `wasm`/`wat`   | honest fail-closed seam (owned JIT: TODO) |
//! | [`CapTier::Caged`]       | `native`/`bin` | honest fail-closed seam (owned OS sandbox)|
//! | [`CapTier::MicroVm`]     | any            | honest fail-closed seam (owned microVM)   |
//! | [`CapTier::Gpu`]         | any            | honest fail-closed seam (owned GPU VM)    |
//!
//! Only the [`CapTier::Sandboxed`] wasm tier has an owned engine linked today.
//! Every stronger tier — and the native interpreter langs (`python`/`node`) —
//! is an honest, fail-closed SEAM: [`run_workload_with_input`] refuses it with
//! [`ExecError::TierNotServed`] / [`ExecError::NotWired`], naming exactly what an
//! owned engine would back. It is NEVER a silent downgrade to a weaker sandbox
//! and NEVER a fake success. Wiring an owned engine for each tier is future work
//! (see `docs/COMPUTE-TIERS.md`).
//!
//! ## Default-deny is FAIL-CLOSED
//!
//! The wasmi tier instantiates against an EMPTY [`wasmi::Linker`]: the guest has
//! no host imports at all, so it reaches nothing on the host filesystem or
//! network, and a module that imports anything fails to instantiate rather than
//! running unsandboxed. The cap bundle a dregg lease carries is threaded at the
//! bridge rung; here the floor is total deny.

use anyhow::Result;

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
// refused, metered like bandwidth, and logged. The [`EgressPolicy`] is a
// deny-by-default allowlist an owned sandbox engine consults per destination;
// the live microVM host-netns enforcement is the named seam
// (`egress::firecracker_netns_seam`). Std-only, so it builds under any feature
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
// metered / receipted invoke-able tools) re-exported, PLUS the cloud's owned
// compute wiring ([`agent_toolkit::SandboxToolkit`]) that injects the owned
// `run_workload` wasmi sandbox engine behind the toolkit's run_tests /
// run_workload runner seam. The open core owns the witness binding; the cloud
// owns the engine.
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
// live n=4 federation (`edge`/`persvati`/`snoopy-lean`/`snoopy-rust`); each
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
/// Maps onto the dregg execution-lease cap-grade. Ordered weakest → strongest
/// isolation. Only [`Sandboxed`](CapTier::Sandboxed) has an owned engine linked
/// today (the wasmi interpreter); the stronger tiers are honest fail-closed
/// seams (see the crate docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CapTier {
    /// In-process pure-interpreter wasm sandbox — the OWNED wasmi interpreter
    /// (`"WasmSandbox"`), no JIT, no fuel meter; the cheapest real sandbox and
    /// the one genuinely-executed tier. Consumes core-module wasm.
    Sandboxed,
    /// In-process JIT'd wasm sandbox (Cranelift-class codegen + a fuel meter +
    /// cap-gated host imports) — strictly stronger than
    /// [`Sandboxed`](CapTier::Sandboxed). No owned engine linked yet: an honest
    /// fail-closed seam. Would consume a component-model binary.
    JitSandboxed,
    /// Native process under seccomp + Landlock (`"OsSandbox"`) — a host binary
    /// run as a child process with a syscall + filesystem allowlist. No owned
    /// engine linked yet: an honest fail-closed seam. Would consume a
    /// `native`/`bin` workload, not wasm.
    Caged,
    /// Hardware-isolated microVM — a per-workload VM with its own guest kernel
    /// behind the KVM boundary (the fly.io / AWS-Lambda model). No owned engine
    /// linked yet: an honest fail-closed seam that refuses cleanly rather than
    /// downgrading. The home for untrusted / homelab workloads.
    MicroVm,
    /// GPU / heavy-compute tier — a hardware-isolated VM with a **passed-through
    /// GPU** (whole device via VFIO, or an NVIDIA MIG slice), metered in
    /// GPU-seconds. The same cap-bounded, metered, receipted lease shape, now
    /// over a GPU.
    ///
    /// It is NOT a CPU-only microVM: GPU passthrough routes to a separate
    /// passthrough-VM seam (Cloud-Hypervisor / QEMU + VFIO, or a MIG partition)
    /// — see `docs/COMPUTE-TIERS.md`. No owned engine linked yet: an honest
    /// fail-closed seam that refuses cleanly (never a silent downgrade to
    /// CPU-only). The cap-grade carries the GPU class + the GPU-seconds /
    /// GPU-memory bounds (see [`gpu`]).
    Gpu,
}

/// The result of running a workload: the values the entrypoint returned.
///
/// The entrypoint's return values are rendered to strings so DreggNet callers
/// don't take an engine type in their signature.
///
/// `enforcement` is the isolation grade the workload *actually* ran under. It is
/// surfaced (never hidden) so a caller that requires a hard floor can inspect
/// it — a downgrade is made LOUD instead of silent. The owned wasmi tier reports
/// `"WasmSandbox"`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Output {
    pub values: Vec<String>,
    /// The enforcement level the run actually achieved (e.g. `"WasmSandbox"`).
    pub enforcement: String,
}

/// A typed input value handed to a workload's entrypoint.
///
/// This is the real input convention: a workload receives actual argument
/// values (numbers / text / JSON), NOT constants spliced into its source text.
///
/// - The owned wasm tier (wasmi) accepts the **numeric** variants
///   ([`Input::I32`], [`Input::I64`], [`Input::F32`], [`Input::F64`]); it is
///   numeric-only.
/// - The [`Input::Text`] / [`Input::Json`] variants are for the native
///   interpreter tiers (an honest seam today) — they carry real strings / JSON
///   bodies, not integer-only query params.
#[derive(Debug, Clone, PartialEq)]
pub enum Input {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    Text(String),
    Json(serde_json::Value),
}

impl Input {
    /// `true` for the numeric variants the core-wasm ABI passes directly to a
    /// wasmi entrypoint. The wasm tier is numeric-only; string / JSON args are
    /// refused up front (they belong to the not-yet-owned native tiers).
    fn is_numeric(&self) -> bool {
        matches!(
            self,
            Input::I32(_) | Input::I64(_) | Input::F32(_) | Input::F64(_)
        )
    }

    /// Lower a numeric input to the [`wasmi::Val`] the entrypoint receives.
    /// Only numeric variants reach here (callers gate on [`Input::is_numeric`]).
    fn to_val(&self) -> wasmi::Val {
        match self {
            Input::I32(n) => wasmi::Val::I32(*n),
            Input::I64(n) => wasmi::Val::I64(*n),
            Input::F32(f) => wasmi::Val::F32((*f).into()),
            Input::F64(f) => wasmi::Val::F64((*f).into()),
            // Non-numeric variants are rejected before lowering.
            Input::Text(_) | Input::Json(_) => wasmi::Val::I32(0),
        }
    }
}

/// A typed execution error — an engine failure surfaces as one of these clean
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
            ExecError::UnsupportedLang(l) => write!(f, "no execution engine wired for lang `{l}`"),
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

/// The conventional entrypoint a DreggNet workload exports (`run`).
const ENTRYPOINT: &str = "run";

/// Run one workload at the authorized cap tier, with no call arguments (the
/// workload computes its result internally). Back-compat entry; returns
/// `anyhow::Result` so existing callers (the durable layer, the webapp router)
/// are unchanged. For real input, use [`run_workload_with_input`].
pub fn run_workload(lang: &str, source: &str, cap_tier: CapTier) -> Result<Output> {
    Ok(run_workload_with_input(lang, source, cap_tier, &[])?)
}

/// Run one workload, passing real argument values to its entrypoint.
///
/// `lang` selects the tier family, `source` is the program, `cap_tier` is the
/// sandbox grade the dregg lease authorizes, and `input` is the argument vector
/// handed to the `run` entrypoint.
///
/// - `"wasm"`/`"wat"` at [`CapTier::Sandboxed`] runs on the OWNED wasmi
///   interpreter (a core module, numeric args only) — the genuinely-executed
///   tier. Every stronger tier ([`CapTier::JitSandboxed`], [`CapTier::Caged`],
///   [`CapTier::MicroVm`], [`CapTier::Gpu`]) and the native interpreter langs
///   (`python`/`node`/`native`) are honest, fail-closed SEAMS: they refuse with
///   [`ExecError::TierNotServed`] / [`ExecError::NotWired`], naming exactly what
///   an owned engine would back — never a silent downgrade to a weaker sandbox
///   and never a fake run. See `docs/COMPUTE-TIERS.md`.
pub fn run_workload_with_input(
    lang: &str,
    source: &str,
    cap_tier: CapTier,
    input: &[Input],
) -> std::result::Result<Output, ExecError> {
    // The strong-isolation tiers are lang-agnostic at the hardware boundary and
    // have no owned engine linked yet — refuse cleanly before the per-lang match.
    if cap_tier == CapTier::MicroVm {
        return Err(ExecError::TierNotServed {
            lang: lang.to_string(),
            tier: cap_tier,
            detail: "the MicroVm tier (a per-workload hardware-isolated VM) has no owned engine \
                     linked; owned microVM execution is future work. No weaker tier is substituted \
                     (no silent downgrade)"
                .into(),
        });
    }
    if cap_tier == CapTier::Gpu {
        return Err(ExecError::TierNotServed {
            lang: lang.to_string(),
            tier: cap_tier,
            detail: "the Gpu tier (a GPU-passthrough VM) has no owned engine linked; owned GPU \
                     execution is future work. No CPU-only backend is substituted (no silent \
                     downgrade)"
                .into(),
        });
    }
    match lang {
        "wasm" | "wat" => match cap_tier {
            CapTier::Sandboxed => run_on_wasmi(source, input),
            CapTier::JitSandboxed => Err(ExecError::TierNotServed {
                lang: lang.to_string(),
                tier: cap_tier,
                detail: "the JitSandboxed (JIT wasm) tier has no owned engine linked; the owned \
                         Sandboxed (wasmi interpreter) tier runs core-module wasm today, and an \
                         owned JIT engine is future work — never a silent downgrade to the weaker \
                         tier"
                    .into(),
            }),
            other => Err(ExecError::TierNotServed {
                lang: lang.to_string(),
                tier: other,
                detail: "a wasm/wat workload runs at the Sandboxed tier (the owned wasmi \
                         interpreter)"
                    .into(),
            }),
        },
        "python" | "py" | "node" | "js" | "native" | "bin" => Err(ExecError::NotWired(format!(
            "dreggnet-exec: the `{lang}` tier has no owned execution engine linked (owned \
             native/interpreter sandboxed execution is future work); the owned, genuinely-executed \
             tier is `wasm`/`wat` at CapTier::Sandboxed. No unsandboxed fallback is run \
             (fail-closed)"
        ))),
        other => Err(ExecError::UnsupportedLang(other.to_string())),
    }
}

/// Run a `wasm`/`wat` workload on the OWNED wasmi interpreter — the
/// [`CapTier::Sandboxed`] tier.
///
/// wasmi is a pure-Rust, zero-`unsafe` wasm interpreter (a DreggNet-owned
/// dependency, no external submodule). The module is instantiated against an
/// EMPTY [`wasmi::Linker`]: the guest is offered NO host imports, so it reaches
/// nothing on the host filesystem or network (deny-all, fail-closed). A module
/// that imports anything fails to instantiate rather than running unsandboxed.
/// The dregg lease's real caps are threaded at the bridge rung.
fn run_on_wasmi(source: &str, input: &[Input]) -> std::result::Result<Output, ExecError> {
    use wasmi::{Engine, Linker, Module, Store, Val};

    // The core-wasm ABI is numeric-only; reject string/JSON args up front with a
    // clean message rather than a deep engine error.
    if let Some(bad) = input.iter().find(|a| !a.is_numeric()) {
        return Err(ExecError::UnsupportedArg {
            tier: "wasmi (Sandboxed)",
            detail: format!(
                "core wasm accepts numeric args only; got {bad:?} — string/JSON args belong to \
                 the not-yet-owned native tiers"
            ),
        });
    }

    // WAT text (or a wasm binary) → core-module bytes.
    let wasm = wat::parse_str(source).map_err(|e| ExecError::Assembly(e.to_string()))?;

    let engine = Engine::default();
    let module = Module::new(&engine, &wasm[..]).map_err(|e| ExecError::Load(e.to_string()))?;

    let mut store = Store::new(&engine, ());
    // Empty linker = deny-all host surface.
    let linker = Linker::<()>::new(&engine);
    let instance = linker
        .instantiate(&mut store, &module)
        .and_then(|pre| pre.start(&mut store))
        .map_err(|e| ExecError::Instantiate(e.to_string()))?;

    let func = instance
        .get_func(&store, ENTRYPOINT)
        .ok_or_else(|| ExecError::Call(format!("export `{ENTRYPOINT}` not found")))?;

    let args: Vec<Val> = input.iter().map(Input::to_val).collect();
    let n_results = func.ty(&store).results().len();
    let mut results = vec![Val::I32(0); n_results];
    func.call(&mut store, &args, &mut results)
        .map_err(|e| ExecError::Call(e.to_string()))?;

    Ok(Output {
        values: results.iter().map(val_to_string).collect(),
        enforcement: "WasmSandbox".to_string(),
    })
}

/// Render a wasmi [`wasmi::Val`] to the string surface DreggNet returns.
fn val_to_string(v: &wasmi::Val) -> String {
    match v {
        wasmi::Val::I32(n) => n.to_string(),
        wasmi::Val::I64(n) => n.to_string(),
        wasmi::Val::F32(f) => f.to_float().to_string(),
        wasmi::Val::F64(f) => f.to_float().to_string(),
        other => format!("{other:?}"),
    }
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

    /// The core-module WAT dogfood: `run` calls an inner `add` on 40 and 2 and
    /// returns 42 — the `i32.add` genuinely executes inside the OWNED wasmi
    /// sandbox.
    fn add_40_2_wat() -> &'static str {
        r#"
            (module
              (func $add (param $a i32) (param $b i32) (result i32)
                local.get $a
                local.get $b
                i32.add)
              (func (export "run") (result i32)
                (call $add (i32.const 40) (i32.const 2))))
        "#
    }

    #[test]
    fn dogfood_add_40_2_equals_42_on_owned_wasmi() {
        let out = run_workload("wat", add_40_2_wat(), CapTier::Sandboxed)
            .expect("owned wasmi should run the add dogfood");
        assert_eq!(out.values, vec!["42".to_string()]);
        assert_eq!(out.enforcement, "WasmSandbox");
    }

    #[test]
    fn wasmi_receives_real_numeric_args() {
        // `run(a, b) = a + b`, invoked with real call arguments.
        let src = r#"
            (module
              (func (export "run") (param $a i32) (param $b i32) (result i32)
                local.get $a
                local.get $b
                i32.add))
        "#;
        let out = run_workload_with_input(
            "wat",
            src,
            CapTier::Sandboxed,
            &[Input::I32(40), Input::I32(2)],
        )
        .expect("owned wasmi should pass numeric args");
        assert_eq!(out.values, vec!["42".to_string()]);
    }

    #[test]
    fn wasmi_rejects_non_numeric_args() {
        let err = run_workload_with_input(
            "wat",
            add_40_2_wat(),
            CapTier::Sandboxed,
            &[Input::Text("nope".into())],
        )
        .expect_err("wasmi is numeric-only");
        assert!(
            matches!(err, ExecError::UnsupportedArg { .. }),
            "got {err:?}"
        );
    }

    #[test]
    fn wasmi_missing_run_export_is_a_clean_error() {
        let src = r#"(module (func (export "other") (result i32) (i32.const 1)))"#;
        let err = run_workload("wat", src, CapTier::Sandboxed).expect_err("no `run` export");
        // anyhow error carries the ExecError::Call message.
        assert!(err.to_string().contains("run"), "got {err}");
    }

    #[test]
    fn wasmi_denies_all_host_imports_fail_closed() {
        // A module that imports a host function cannot instantiate against the
        // EMPTY linker — it fails closed rather than running unsandboxed.
        let src = r#"
            (module
              (import "env" "sneak" (func $sneak))
              (func (export "run") (result i32) (i32.const 0)))
        "#;
        let err =
            run_workload("wat", src, CapTier::Sandboxed).expect_err("host imports are denied");
        assert!(
            err.to_string().to_lowercase().contains("instantiate")
                || err.to_string().to_lowercase().contains("import")
                || err.to_string().to_lowercase().contains("missing"),
            "got {err}"
        );
    }

    // --- The stronger tiers are honest, fail-closed seams (no owned engine yet) ---

    #[test]
    fn jit_tier_is_an_honest_seam() {
        let err = run_workload("wat", add_40_2_wat(), CapTier::JitSandboxed)
            .expect_err("JIT tier is not wired");
        assert!(err.to_string().contains("JitSandboxed"), "got {err}");
    }

    #[test]
    fn native_langs_are_honest_seams() {
        for lang in ["python", "py", "node", "js", "native", "bin"] {
            let err = run_workload_with_input(lang, "x", CapTier::Caged, &[])
                .expect_err("native tiers are not wired");
            assert!(matches!(err, ExecError::NotWired(_)), "{lang}: got {err:?}");
        }
    }

    #[test]
    fn microvm_tier_is_an_honest_seam() {
        let err = run_workload_with_input("wat", "x", CapTier::MicroVm, &[])
            .expect_err("MicroVm is not wired");
        assert!(
            matches!(err, ExecError::TierNotServed { .. }),
            "got {err:?}"
        );
    }

    #[test]
    fn gpu_tier_is_an_honest_seam() {
        let err =
            run_workload_with_input("wat", "x", CapTier::Gpu, &[]).expect_err("Gpu is not wired");
        assert!(
            matches!(err, ExecError::TierNotServed { .. }),
            "got {err:?}"
        );
    }

    #[test]
    fn unknown_lang_is_refused() {
        let err = run_workload("ruby", "x", CapTier::Sandboxed).expect_err("no ruby tier");
        assert!(err.to_string().contains("ruby"), "got {err}");
    }
}
