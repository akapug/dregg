//! The [`Observation`] vocabulary — what every backend reports through the seam
//! (48 §4 "the Observation"; 42 §2).
//!
//! `Observation = Produced | Absent`. [`Produced`] carries every projection any
//! `(primitive × backend)` cell might observe; the [`fields`](Produced::fields)
//! mask says which are meaningful, so an unobserved field is *excluded* from the
//! differential, never laundered as equal (the field-granular CR-6 mechanism).

use crate::adapter::{BackendAbsentReason, ObservedFields};

/// Skeleton byte buffer. In the real kit this is `ntex_bytes::Bytes` (the
/// zero-copy arena type `net/httpe` already uses); aliased to `Vec<u8>` here to
/// keep the skeleton standalone (no net/httpe dependency).
pub type Bytes = Vec<u8>;

/// Skeleton small-string. Real kit uses `smol_str::SmolStr`; aliased to keep deps
/// minimal.
pub type SmolStr = String;

/// The sidecar offset base (`parsed_request.rs` `SIDECAR_OFFSET_BASE`): an arena
/// field offset `>= 0x8000_0000` points into the mutation `sidecar` union rather
/// than the immutable wire arena.
pub const SIDECAR_OFFSET_BASE: u32 = 0x8000_0000;

// ── per-unit configuration ──────────────────────────────────────────────────────
/// Per-unit configuration (the `40-LEDGER` row config). Its frozen dCBOR
/// `Canonical` impl gates [`VectorId`](crate::VectorId) stability and is owned by
/// the spec/orchestrator unit (48 residual open question #1) — a placeholder here.
pub struct Spec;

// ── shared scalar vocabulary ────────────────────────────────────────────────────
/// HTTP status (`None` in [`Produced`] for region/request, linear, shared).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Status(pub u16);

/// Canonical comparison form: lowercased names, value bytes, dup-preserving
/// multiset, sorted by `(name, value)`. The exact multi-value join rule is pinned
/// by the corpus/spec unit (48 residual open question #3).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct HeaderSet(pub Vec<(Bytes, Bytes)>);

/// The ONE error taxonomy (48 C-7: `44`'s enum wins, spine-hosted). Adapters map
/// their native errors into it so `error_class` is comparable across backends.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ErrorClass {
    Smuggling(SmuggleClass),
    ProtocolError(ProtoCode),
    FlowControl,
    HeaderListTooLarge,
    DecompressionBomb,
    BadVarint,
    MalformedFrame,
    PathEscape,
    TlsDowngradeRefused,
    ReplayRejected,
    Timeout(Phase),
    Other(SmolStr),
}

/// The six `parsed_request.rs` `SmuggleViolation` names (48 C-7).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SmuggleClass {
    ContentLengthAndTransferEncoding,
    DuplicateContentLength,
    ChunkedNotLast,
    NullByteInHeader,
    UnsupportedTransferEncoding,
    InvalidContentLength,
}

/// Protocol-error code (HTTP/2 / HTTP/3 frame-level). Skeleton numeric carrier.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ProtoCode(pub u32);

/// Which phase a timeout fired in (connect / tls / header / body / idle).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Phase {
    Connect,
    Tls,
    Header,
    Body,
    Idle,
}

// ── Event is an ENUM (48 C-18): wire bytes OR a virtual-clock tick ──────────────
/// A machine-driving event. `Timer` lets the `FormalModel` inject virtual clock
/// ticks while `CurrentNet` reads a real clock — otherwise timeout transitions
/// diverge spuriously (44 tension #8). The machine unit may extend this.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Event {
    Wire(Bytes),
    Timer(VirtualClock),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct VirtualClock(pub u64);

// ── linear: acquire → use → release-once (X-4 token discipline) ─────────────────
/// A linear-resource operation fed to `run_linear`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ResourceOp {
    Acquire(HandleId),
    Use(HandleId),
    Release(HandleId),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct HandleId(pub u64);

/// Observed linear trace (X-4: `BufRingLease` / `PooledBuf` / `DispatchDecision`,
/// `21-FORMAL-MODEL.md:95-97`). Observe: release-once held, no use-after-release.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LinearTrace {
    pub events: Vec<LinearEvent>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LinearEvent {
    Acquire(HandleId),
    Use(HandleId),
    Release(HandleId),
}

// ── shared: schedule → linearization under interleaving (Iris ranks 5-7) ────────
/// An interleaving schedule fed to `run_shared` (loom/shuttle-shaped).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Schedule {
    pub threads: Vec<Vec<OpId>>,
    pub seed: u64,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct OpId(pub u32);

/// Widened (48 C-4) so `44`'s `SharedProj` predicate diff has its inputs: the
/// `FormalModel` fills `model_allowed`; the runner checks `observed ⊆
/// model_allowed`, degrading to "invariant held ∧ linearizable" when `None`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Linearization {
    pub order: Vec<OpId>,
    pub linearizable: bool,
    pub invariant_held: bool,
    pub observed: OutcomeSet,
    pub model_allowed: Option<OutcomeSet>,
}

/// The set of admissible linearization outcomes (return-value tuples). Skeleton:
/// an opaque, comparable bag of outcome encodings.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct OutcomeSet(pub std::collections::BTreeSet<Vec<u8>>);

// ── region/view: bytes → arena-view ─────────────────────────────────────────────
/// Normalizes `ParsedRequest` (`parsed_request.rs:611-667,896`) and the HOL4
/// `wf_parsed_request` predicate (`21-FORMAL-MODEL.md:19-28`) to ONE value: an
/// immutable byte arena + `(name_tag, off, len)` triples — identical across H1
/// pointer-arithmetic, HPACK copy, and QPACK arena (the Rank-1 unification).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ArenaView {
    pub arena: Bytes,
    pub method: Method,
    pub uri: (u32, u32), // (off, len) into arena
    pub fields: Vec<ArenaField>,
    pub sidecar: Bytes, // mutation union; offsets >= SIDECAR_OFFSET_BASE
    pub wf: WellFormed,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ArenaField {
    pub name: NameTag,
    pub off: u32,
    pub len: u32,
}

/// Mirrors `HeaderName` (`parsed_request.rs:554-559`). An `off >=
/// SIDECAR_OFFSET_BASE` points into the sidecar at `off - SIDECAR_OFFSET_BASE`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NameTag {
    WellKnown(u16),
    StaticStr(&'static str),
    Custom { off: u32, len: u32 },
}

/// Method, kept opaque/numeric in the skeleton (real kit mirrors `http::Method`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Method(pub u8);

/// The arena's only open hypothesis (every `off+len <= arena.len()` or in-sidecar,
/// all ranges valid UTF-8 — discharged by the EverParse parser proof, 21-FORMAL
/// X-2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WellFormed {
    Yes,
    No { violated: &'static str },
}

// ── machine: the sans-IO fold ───────────────────────────────────────────────────
/// The `(state, event|bytes) → (state', events, out)` trace
/// (`20-ARCHITECTURE.md:170`), observed as a FOLD of the incremental tri-state —
/// the adapter (not the trait signature) owns the feed loop (42 tension #4).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Trace {
    pub steps: Vec<Step>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Step {
    pub state: StateLabel,
    pub parse: ParseClass,
    pub emitted: Bytes,
    pub events: Vec<Event>,
}

/// The universal tri-state (`socks.rs:84-92`; `response_parser.rs:41-49`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ParseClass {
    Complete { consumed: usize },
    Incomplete,
    Error,
}

/// e.g. a `ProtocolState` variant name (21-FORMAL Rank-2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct StateLabel(pub &'static str);

// ── the Observation ─────────────────────────────────────────────────────────────
/// `Produced | Absent`. The `Absent` variant is the runtime CR-6 firewall: even if
/// `supports()` said yes, a backend that errors/refuses/times out yields `Absent`,
/// which the runner counts separately and NEVER as agreement.
pub enum Observation {
    Produced(Produced),
    Absent { reason: BackendAbsentReason },
}

/// Every projection any cell might observe (48 C-3: the dedicated `linear_trace` /
/// `linearization` fields are authoritative — NOT smuggled into `state_trace`).
/// The [`fields`](Produced::fields) mask says which `Option<_>` carry signal.
pub struct Produced {
    pub fields: ObservedFields,
    pub status: Option<Status>,
    pub headers: HeaderSet, // empty unless HEADERS set
    pub body: Bytes,
    pub arena_view: Option<ArenaView>, // region
    pub state_trace: Option<Trace>,    // machine
    pub error_class: Option<ErrorClass>,
    pub consumed: Option<usize>, // None under tri-state Incomplete
    pub linear_trace: Option<LinearTrace>, // linear (X-4)
    pub linearization: Option<Linearization>, // shared (Iris)
}

impl Produced {
    /// An empty `Produced` observing nothing — a convenience for adapter stubs to
    /// fill incrementally.
    pub fn empty() -> Self {
        Produced {
            fields: ObservedFields::empty(),
            status: None,
            headers: HeaderSet(Vec::new()),
            body: Vec::new(),
            arena_view: None,
            state_trace: None,
            error_class: None,
            consumed: None,
            linear_trace: None,
            linearization: None,
        }
    }
}
