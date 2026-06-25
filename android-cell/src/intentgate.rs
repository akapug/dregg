//! **Cap-gate the INTENT.** The confined Android app's outbound `Intent` reforged
//! from ambient implicit-resolution into a cap-bounded, spotter-resolved, receipted
//! hand-off — `GRAPHIDEOS.md §1` (the intent row) made real, and the deep per-call
//! frontier `ANDROID-CELL.md §5` names ("sensor/**intent** at HAL/binder granularity")
//! taken its first concrete step.
//!
//! # What Android does (the ambient mechanism deos replaces)
//!
//! In stock Android an app fires an **implicit `Intent`** — an action
//! (`android.intent.action.VIEW`), a data URI (`https://…`, `tel:…`, `geo:…`,
//! `content://…`), maybe a MIME type — and `startActivity` hands it to the
//! framework. `PackageManager.queryIntentActivities` matches it against **every
//! installed app's `<intent-filter>`** and the system launches a handler (or shows
//! a chooser; or honours a remembered "default app"). This is **ambient authority**:
//! the originating app names no concrete target, reaches the *whole device's* handler
//! set, and the "default app" auto-pick is an invisible standing grant.
//!
//! # What graphideOS does (the cap-bounded reforge)
//!
//! `GRAPHIDEOS.md §1`: *"an 'intent' is a turn targeting a cell you hold a cap to;
//! implicit resolution is the **spotter** over cells you can reach; no ambient
//! `startActivity`."* This module is that, in the same shape as the proven
//! [`crate::netgate`] / [`crate::input`] gates:
//!
//! 1. **Resolution is over the cap-reachable neighborhood, not the device.** The
//!    [`IntentResolver`] holds exactly the handler cells the android-cell was *granted*
//!    a cap to reach (its bounded neighborhood) — it is NOT a global `PackageManager`.
//!    An intent that matches no cap-reachable handler is [`IntentDecision::RefusedNoHandler`]:
//!    **the app cannot `startActivity` to an arbitrary app it was never handed.**
//! 2. **Web data is gated by the held cap, before resolution.** For an `http(s)`
//!    data URI the held [`SurfaceCapability`]'s fetch allowlist decides the origin
//!    exactly as the net gate does; an un-allowed origin is [`IntentDecision::RefusedByCap`]
//!    before any handler is consulted.
//! 3. **A single match is a cap-bounded hand-off (a targeted turn).** Exactly one
//!    cap-reachable handler ⟹ [`IntentDecision::Resolved`] naming that one cell — the
//!    turn the framework would have fired ambiently is now a receipted hand to a named
//!    capability holder.
//! 4. **Ambiguity is an explicit chooser, never a silent default.** Multiple
//!    cap-reachable matches ⟹ [`IntentDecision::Ambiguous`] carrying the candidates for
//!    a user pick (the powerbox-style ceremony). Android's remembered "default app"
//!    auto-pick is exactly the standing ambient grant deos refuses to mint silently.
//!
//! Every decision — admit, refuse, or defer-to-chooser — leaves an [`IntentReceipt`],
//! content-addressed like the net/input receipts, so the android-cell's intent traffic
//! is auditable end to end.
//!
//! # The depth (honest, like the net + input gates')
//!
//! This is the **resolution-and-authority** layer: the gate decides, against the held
//! cap + the granted handler set, where (if anywhere) an intent may go, and records it.
//! The remaining frontier — interposing the *actual* binder `startActivity`/
//! `queryIntentActivities` transaction inside the confined runtime so the device kernel
//! itself routes only cap-admitted intents (the HAL/binder leg the net gate's deep layer
//! also names) — is the same not-yet-claimed depth. What IS real today: the resolution
//! algebra + the cap teeth + the receipt, testable on any node with no device.

use std::collections::BTreeSet;

use starbridge_web_surface::SurfaceCapability;

use dregg_firmament::CellId;

/// An outbound Android intent from the confined app — the fields implicit resolution
/// matches on (`action` · `data` URI · `mime_type` · `categories`), modelled faithfully
/// to AOSP's `Intent`. The confined runtime's `startActivity` is interposed and the
/// intent arrives here instead of the framework's `PackageManager`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AndroidIntent {
    /// The action string, e.g. `android.intent.action.VIEW` / `…SEND` / `…DIAL`.
    pub action: String,
    /// The data URI, e.g. `https://example.com/x`, `tel:+15551234`, `geo:0,0?q=cafe`.
    /// `None` is an action-only intent.
    pub data: Option<String>,
    /// The MIME type, e.g. `text/plain` (the `SEND`/share path). `None` = untyped.
    pub mime_type: Option<String>,
    /// The categories, e.g. `android.intent.category.BROWSABLE`. AOSP requires a
    /// handler's filter to declare EVERY category the intent carries.
    pub categories: BTreeSet<String>,
}

impl AndroidIntent {
    /// A bare action+data intent (no MIME, no extra categories) — the common
    /// `VIEW`-a-URI / `DIAL`-a-number shape.
    pub fn view(action: impl Into<String>, data: impl Into<String>) -> Self {
        AndroidIntent {
            action: action.into(),
            data: Some(data.into()),
            mime_type: None,
            categories: BTreeSet::new(),
        }
    }

    /// The data URI's **scheme** (`https`, `tel`, `geo`, `content`, …), lower-cased —
    /// the first component a handler filter matches on. `None` for an action-only intent
    /// or a scheme-less data string.
    pub fn scheme(&self) -> Option<String> {
        let data = self.data.as_ref()?;
        let scheme = data.split_once(':').map(|(s, _)| s)?;
        if scheme.is_empty() {
            return None;
        }
        Some(scheme.to_ascii_lowercase())
    }

    /// The **web origin** (`scheme://authority`) of an `http(s)` data URI — the unit the
    /// held [`SurfaceCapability`] fetch allowlist authorizes (the same `scheme://host`
    /// shape the net gate gates). `None` for a non-web scheme (`tel:` / `geo:` / …) or an
    /// action-only intent: those carry no fetchable origin and are gated purely by the
    /// cap-reachable handler set.
    pub fn web_origin(&self) -> Option<String> {
        let data = self.data.as_ref()?;
        let (scheme, rest) = data.split_once("://")?;
        let scheme = scheme.to_ascii_lowercase();
        if scheme != "http" && scheme != "https" {
            return None;
        }
        // authority = everything up to the first '/', '?' or '#'.
        let authority = rest
            .split(['/', '?', '#'])
            .next()
            .filter(|a| !a.is_empty())?;
        Some(format!("{scheme}://{authority}"))
    }

    /// A short tag distinguishing the intent for the receipt digest + status line.
    fn tag(&self) -> String {
        match &self.data {
            Some(d) => format!("{} {}", self.action, d),
            None => self.action.clone(),
        }
    }

    /// The `am start` argument vector that dispatches this intent into the confined
    /// runtime — the device-side `startActivity` leg. The activity manager is the
    /// device's launch tool; these are exactly its `start` flags (`-a` action, `-d`
    /// data, `-t` MIME, `-c` category). The [`AndroidIntentGate`] runs the cap +
    /// resolution teeth BEFORE this is ever built, so only a singly-resolved,
    /// cap-admitted intent reaches it.
    pub fn am_start_args(&self) -> Vec<String> {
        let mut args = vec![
            "am".into(),
            "start".into(),
            "-a".into(),
            self.action.clone(),
        ];
        if let Some(d) = &self.data {
            args.push("-d".into());
            args.push(d.clone());
        }
        if let Some(t) = &self.mime_type {
            args.push("-t".into());
            args.push(t.clone());
        }
        for c in &self.categories {
            args.push("-c".into());
            args.push(c.clone());
        }
        args
    }
}

/// What a **handler cell** declares it handles — the deos form of an AOSP
/// `<intent-filter>`. A handler matches an intent iff its action is listed, it covers
/// every category the intent carries, and (when the intent has data) its scheme is
/// listed. Held by the [`IntentResolver`] only for handlers the android-cell was granted
/// a cap to reach.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntentFilter {
    /// The actions this handler answers (`VIEW`, `SEND`, …). Empty = matches nothing.
    pub actions: BTreeSet<String>,
    /// The data schemes this handler answers (`https`, `tel`, …). Empty = the handler
    /// takes only data-less (action-only) intents.
    pub schemes: BTreeSet<String>,
    /// The categories this handler declares. AOSP: a handler matches only if it declares
    /// EVERY category the intent carries (`intent.categories ⊆ filter.categories`).
    pub categories: BTreeSet<String>,
}

impl IntentFilter {
    /// A filter answering one action over a set of schemes (the common case).
    pub fn new(
        actions: impl IntoIterator<Item = impl Into<String>>,
        schemes: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        IntentFilter {
            actions: actions.into_iter().map(Into::into).collect(),
            schemes: schemes
                .into_iter()
                .map(|s| s.into().to_ascii_lowercase())
                .collect(),
            categories: BTreeSet::new(),
        }
    }

    /// Add declared categories (builder).
    pub fn with_categories(
        mut self,
        categories: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        self.categories = categories.into_iter().map(Into::into).collect();
        self
    }

    /// **The AOSP intent-filter match algorithm** (the action + category + data legs):
    ///
    /// - **action**: the intent's action must be one this filter answers;
    /// - **category**: the filter must declare every category the intent carries
    ///   (`intent.categories ⊆ filter.categories`);
    /// - **data**: a data-bearing intent's scheme must be one this filter answers; an
    ///   action-only intent matches a filter that declares no schemes.
    pub fn matches(&self, intent: &AndroidIntent) -> bool {
        if !self.actions.contains(&intent.action) {
            return false;
        }
        if !intent.categories.is_subset(&self.categories) {
            return false;
        }
        match intent.scheme() {
            Some(scheme) => self.schemes.contains(&scheme),
            None => self.schemes.is_empty(),
        }
    }
}

/// A cap-reachable handler in the android-cell's bounded neighborhood — a cell the
/// android-cell holds a cap to, with the [`IntentFilter`] it declares. The
/// [`IntentResolver`] is the spotter over a set of THESE; it is decidedly NOT the
/// device's global `PackageManager`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntentHandler {
    /// The handler cell — the named capability holder a resolved intent hands to.
    pub cell: CellId,
    /// A short human label for the chooser / status line (e.g. "Maps", "Browser").
    pub label: String,
    /// What this handler declares it answers.
    pub filter: IntentFilter,
}

impl IntentHandler {
    pub fn new(cell: CellId, label: impl Into<String>, filter: IntentFilter) -> Self {
        IntentHandler {
            cell,
            label: label.into(),
            filter,
        }
    }
}

/// The four distinguishable ends an outbound intent can reach — the intent-side analogue
/// of [`crate::IoDecision`], with one extra arm (`Ambiguous`) for the chooser ceremony
/// that has no net-gate counterpart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IntentDecision {
    /// Exactly one cap-reachable handler matched: the intent becomes a cap-bounded
    /// hand-off (a targeted turn) to this one named cell. The receipt records the
    /// handler the authority went to.
    Resolved { handler: CellId, label: String },
    /// More than one cap-reachable handler matched: deos refuses to silently auto-pick
    /// (Android's remembered "default app" is exactly the ambient standing grant we
    /// reject) and surfaces the candidates for an explicit user chooser — itself a turn.
    Ambiguous { candidates: Vec<(CellId, String)> },
    /// NO cap-reachable handler matched: the intent reaches nothing. THIS is the
    /// no-ambient-`startActivity` property — the app cannot dispatch to an arbitrary
    /// handler it was never granted a cap to.
    RefusedNoHandler,
    /// A web (`http(s)`) data origin the held [`SurfaceCapability`] does NOT authorize —
    /// refused at the gate, before any handler is consulted (the same fetch-allowlist
    /// tooth the net gate bites with).
    RefusedByCap { origin: String },
    /// The intent resolved to one cap-admitted handler, but the device-side dispatch
    /// (`am start`) itself failed — the transport's own refusal, distinct from the cap +
    /// resolution teeth (the intent-side analogue of [`crate::InputDecision::Failed`]).
    /// Only [`AndroidIntentGate::dispatch`] produces this; [`IntentResolver::resolve`]
    /// stays pure (it never touches a device).
    DispatchFailed {
        handler: CellId,
        label: String,
        reason: String,
    },
}

impl IntentDecision {
    pub fn resolved(&self) -> bool {
        matches!(self, IntentDecision::Resolved { .. })
    }
    pub fn refused_no_handler(&self) -> bool {
        matches!(self, IntentDecision::RefusedNoHandler)
    }
    pub fn refused_by_cap(&self) -> bool {
        matches!(self, IntentDecision::RefusedByCap { .. })
    }
    pub fn ambiguous(&self) -> bool {
        matches!(self, IntentDecision::Ambiguous { .. })
    }
    pub fn dispatch_failed(&self) -> bool {
        matches!(self, IntentDecision::DispatchFailed { .. })
    }
}

/// **The receipt left by a gated intent decision.** Every act the gate decides produces
/// one, so the android-cell's intent dispatch is auditable end to end exactly like the
/// egress [`crate::IoReceipt`] and input [`crate::InputReceipt`].
///
/// Content-addressed: `decision_digest = blake3(cell? ‖ intent_tag ‖ outcome ‖ handler?)`,
/// reconstructible by a verifier. Deliberately lightweight (NOT the full kernel
/// `TurnReceipt`); an intent resolution is an authority+routing decision at the framework
/// boundary, and this is its faithful witness at the granularity this layer provides.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntentReceipt {
    /// The android-cell whose held cap + granted handler set decided this intent.
    pub cell: Option<CellId>,
    /// The intent the confined app fired.
    pub intent: AndroidIntent,
    /// The decision reached.
    pub decision: IntentDecision,
    /// `blake3(…)[..32]` — the content-addressed witness a verifier reconstructs.
    pub decision_digest: [u8; 32],
}

impl IntentReceipt {
    fn digest(cell: Option<CellId>, intent: &AndroidIntent, decision: &IntentDecision) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        if let Some(c) = cell {
            h.update(b"\x01cell");
            h.update(c.as_bytes());
        }
        h.update(intent.tag().as_bytes());
        match decision {
            IntentDecision::Resolved { handler, .. } => {
                h.update(b"\x01resolved");
                h.update(handler.as_bytes());
            }
            IntentDecision::Ambiguous { candidates } => {
                h.update(b"\x02ambiguous");
                for (c, _) in candidates {
                    h.update(c.as_bytes());
                }
            }
            IntentDecision::RefusedNoHandler => {
                h.update(b"\x03refused-no-handler");
            }
            IntentDecision::RefusedByCap { origin } => {
                h.update(b"\x04refused-by-cap");
                h.update(origin.as_bytes());
            }
            IntentDecision::DispatchFailed {
                handler, reason, ..
            } => {
                h.update(b"\x05dispatch-failed");
                h.update(handler.as_bytes());
                h.update(reason.as_bytes());
            }
        }
        *h.finalize().as_bytes()
    }

    /// A one-line audit truth for the cockpit status line — which end, named exactly.
    pub fn status_line(&self) -> String {
        match &self.decision {
            IntentDecision::Resolved { label, .. } => format!(
                "android-intent: ✔ {} → handed to «{label}» as a cap-bounded turn — a named capability holder, not an ambient startActivity",
                self.intent.tag()
            ),
            IntentDecision::Ambiguous { candidates } => format!(
                "android-intent: ◈ {} matches {} cap-reachable handlers — surfaced for an explicit chooser (no silent default-app auto-pick)",
                self.intent.tag(),
                candidates.len()
            ),
            IntentDecision::RefusedNoHandler => format!(
                "android-intent: ✖ {} REFUSED — no cap-reachable handler (the app cannot startActivity to an app it was never granted)",
                self.intent.tag()
            ),
            IntentDecision::RefusedByCap { origin } => format!(
                "android-intent: ✖ {} REFUSED at the gate — the held SurfaceCapability does not authorize the data origin {origin}",
                self.intent.tag()
            ),
            IntentDecision::DispatchFailed { label, reason, .. } => format!(
                "android-intent: ⚠ {} cap-admitted + resolved to «{label}» but the device dispatch (am start) failed ({reason})",
                self.intent.tag()
            ),
        }
    }
}

/// The cap-gated intent resolver for one android-cell — **the spotter over the cell's
/// bounded, cap-reachable handler neighborhood**, NOT a global `PackageManager`. Holds
/// the granted handler set and the cell it speaks for; holds NO ambient authority — every
/// [`resolve`](Self::resolve) is a pure function of the `surface` cap argument + the
/// granted handlers.
pub struct IntentResolver {
    /// The handlers the android-cell was granted a cap to reach (its neighborhood). An
    /// intent can resolve ONLY to one of these — a handler not in this set is, by
    /// construction, unreachable (no ambient device-wide query).
    handlers: Vec<IntentHandler>,
    /// The android-cell whose authority decides (recorded on each receipt).
    cell: Option<CellId>,
}

impl IntentResolver {
    /// Build a resolver over the granted handler neighborhood and the cell it speaks for.
    pub fn new(handlers: impl IntoIterator<Item = IntentHandler>, cell: Option<CellId>) -> Self {
        IntentResolver {
            handlers: handlers.into_iter().collect(),
            cell,
        }
    }

    /// The granted handler neighborhood (the cap-reachable set the spotter ranges over).
    pub fn handlers(&self) -> &[IntentHandler] {
        &self.handlers
    }

    /// **THE INTENT GATE.** The confined app fired `intent`. Decide against the held
    /// `surface` cap + the granted handler set, and return the decision AND its
    /// [`IntentReceipt`].
    ///
    /// Order of teeth (fail-closed, cap before handler):
    /// 1. **Cap, before resolution** — a web (`http(s)`) data origin the held cap does
    ///    not authorize is [`IntentDecision::RefusedByCap`]; no handler is consulted.
    /// 2. **Spotter over the cap-reachable set** — match the intent against the granted
    ///    handlers (AOSP action+category+data algorithm). Zero matches ⟹
    ///    [`IntentDecision::RefusedNoHandler`] (no ambient `startActivity`); one match ⟹
    ///    [`IntentDecision::Resolved`] (the cap-bounded hand-off); many ⟹
    ///    [`IntentDecision::Ambiguous`] (the explicit chooser, never a silent default).
    pub fn resolve(&self, surface: &SurfaceCapability, intent: &AndroidIntent) -> IntentReceipt {
        // TOOTH 1 — THE CAP, BEFORE THE HANDLER. A web data origin the held cap does not
        // authorize is refused here; the spotter is never run.
        if let Some(origin) = intent.web_origin() {
            if !surface.may_fetch(&origin) {
                let decision = IntentDecision::RefusedByCap { origin };
                return self.receipt(intent, decision);
            }
        }

        // TOOTH 2 — THE SPOTTER OVER THE CAP-REACHABLE NEIGHBORHOOD. Resolution ranges
        // ONLY over the granted handlers — an unreachable handler is not a candidate.
        let mut matches: Vec<(CellId, String)> = self
            .handlers
            .iter()
            .filter(|h| h.filter.matches(intent))
            .map(|h| (h.cell, h.label.clone()))
            .collect();
        // Dedup by cell (a handler granted twice is one capability holder).
        matches.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()).then(a.1.cmp(&b.1)));
        matches.dedup_by(|a, b| a.0 == b.0);

        let decision = match matches.len() {
            0 => IntentDecision::RefusedNoHandler,
            1 => {
                let (handler, label) = matches.into_iter().next().unwrap();
                IntentDecision::Resolved { handler, label }
            }
            _ => IntentDecision::Ambiguous {
                candidates: matches,
            },
        };
        self.receipt(intent, decision)
    }

    fn receipt(&self, intent: &AndroidIntent, decision: IntentDecision) -> IntentReceipt {
        let decision_digest = IntentReceipt::digest(self.cell, intent, &decision);
        IntentReceipt {
            cell: self.cell,
            intent: intent.clone(),
            decision,
            decision_digest,
        }
    }
}

// ===========================================================================
// THE TRANSPORT LEG — interpose the confined runtime's `startActivity`.
// ===========================================================================

/// Why a device-side intent dispatch failed (distinct from a cap/no-handler refusal,
/// which never reaches the device — the intent-side of [`crate::InputError`]).
#[derive(Debug)]
pub enum IntentError {
    /// A required tool (`adb`/`am`) was not found.
    ToolMissing { tool: String, looked_in: String },
    /// The device-side `am start` exited non-zero.
    CommandFailed { cmd: String, stderr: String },
    /// An I/O error invoking the tool.
    Io(std::io::Error),
}

impl std::fmt::Display for IntentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntentError::ToolMissing { tool, looked_in } => {
                write!(f, "android tool `{tool}` not found (looked in {looked_in})")
            }
            IntentError::CommandFailed { cmd, stderr } => write!(f, "`{cmd}` failed: {stderr}"),
            IntentError::Io(e) => write!(f, "io: {e}"),
        }
    }
}

impl std::error::Error for IntentError {}

impl From<std::io::Error> for IntentError {
    fn from(e: std::io::Error) -> Self {
        IntentError::Io(e)
    }
}

/// **The device-side intent sink.** A confined runtime an already-gated intent can be
/// dispatched into (the binder `startActivity` leg). The cap + resolution teeth fire in
/// [`AndroidIntentGate::dispatch`] BEFORE this is ever called — an impl here is the
/// transport, not the authority — exactly the [`crate::AndroidInputSink`] discipline.
pub trait AndroidIntentSink {
    /// Dispatch one already-resolved, cap-admitted intent into the device, named to the
    /// resolved `handler` cell (recorded for the audit; the device-side tool is
    /// `am start`). Returns `Ok(())` on a successful launch, or an error the gate turns
    /// into [`IntentDecision::DispatchFailed`].
    fn start_activity(
        &mut self,
        intent: &AndroidIntent,
        handler: CellId,
    ) -> Result<(), IntentError>;
}

/// **The host-independent intent stand-in.** A sink with no live device: it RECORDS the
/// `am_start_args` of every dispatched (gate-admitted) intent without touching a device,
/// so the gate + receipt + cap + resolution logic test on any node — the intent-side of
/// [`crate::RecordingInputSink`].
#[derive(Default)]
pub struct RecordingIntentSink {
    /// Every dispatched intent's `(am_start_args, handler)`, in order — the audit trail
    /// a test asserts on. ONLY gate-admitted (singly-resolved, cap-passed) intents land
    /// here; a refused/ambiguous intent never reaches the sink.
    pub dispatched: Vec<(Vec<String>, CellId)>,
    /// If set, `start_activity` returns this as a `CommandFailed` (to test the
    /// `DispatchFailed` arm without a device).
    pub fail_with: Option<String>,
}

impl AndroidIntentSink for RecordingIntentSink {
    fn start_activity(
        &mut self,
        intent: &AndroidIntent,
        handler: CellId,
    ) -> Result<(), IntentError> {
        if let Some(reason) = &self.fail_with {
            return Err(IntentError::CommandFailed {
                cmd: format!("adb shell {}", intent.am_start_args().join(" ")),
                stderr: reason.clone(),
            });
        }
        self.dispatched.push((intent.am_start_args(), handler));
        Ok(())
    }
}

/// **THE LIVE INTENT GATE** — a [`IntentResolver`] (the cap + spotter decision) welded to
/// an [`AndroidIntentSink`] (the device transport). This is what interposes a confined
/// app's `startActivity`: the app fires an intent, the gate decides, and ONLY a
/// singly-resolved, cap-admitted intent reaches the device's `am start`. A
/// `RefusedNoHandler` / `RefusedByCap` / `Ambiguous` intent NEVER touches the device —
/// the no-ambient-`startActivity` property, enforced at the transport, exactly as the
/// input gate refuses a cap-denied tap before `adb`.
pub struct AndroidIntentGate<S: AndroidIntentSink> {
    resolver: IntentResolver,
    sink: S,
}

impl<S: AndroidIntentSink> AndroidIntentGate<S> {
    /// Weld a resolver (the decision) to a sink (the device transport).
    pub fn new(resolver: IntentResolver, sink: S) -> Self {
        AndroidIntentGate { resolver, sink }
    }

    pub fn sink_mut(&mut self) -> &mut S {
        &mut self.sink
    }

    pub fn resolver(&self) -> &IntentResolver {
        &self.resolver
    }

    /// **DISPATCH ONE INTENT, GATED.** Resolve `intent` against the held `surface` cap +
    /// the granted handler set and, **iff it resolves to exactly one cap-admitted
    /// handler**, dispatch it into the device — returning the [`IntentReceipt`].
    ///
    /// - `Resolved` ⟹ the device sink is driven (`am start`); on a sink error the receipt
    ///   becomes [`IntentDecision::DispatchFailed`] (the transport tooth, distinct from
    ///   cap/resolution).
    /// - `RefusedNoHandler` / `RefusedByCap` / `Ambiguous` ⟹ **the device is never
    ///   touched** — the resolution receipt is returned verbatim. Ambiguity in particular
    ///   is NOT auto-dispatched: it awaits the explicit chooser (no silent default).
    pub fn dispatch(
        &mut self,
        surface: &SurfaceCapability,
        intent: AndroidIntent,
    ) -> IntentReceipt {
        let resolved = self.resolver.resolve(surface, &intent);
        match &resolved.decision {
            IntentDecision::Resolved { handler, label } => {
                let handler = *handler;
                let label = label.clone();
                match self.sink.start_activity(&intent, handler) {
                    Ok(()) => resolved, // the device launched; the Resolved receipt stands.
                    Err(e) => {
                        // Cap admitted + resolved, but the device dispatch failed — a
                        // distinct transport tooth, re-receipted (NOT a cap refusal).
                        let decision = IntentDecision::DispatchFailed {
                            handler,
                            label,
                            reason: e.to_string(),
                        };
                        let decision_digest =
                            IntentReceipt::digest(self.resolver.cell, &intent, &decision);
                        IntentReceipt {
                            cell: self.resolver.cell,
                            intent,
                            decision,
                            decision_digest,
                        }
                    }
                }
            }
            // Refused or ambiguous — the device is never touched.
            _ => resolved,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::cell_seed;
    use starbridge_web_surface::{AuthRequired, SurfaceCapability};

    fn web_cap(cell: CellId, origins: &[&str]) -> SurfaceCapability {
        SurfaceCapability::scoped(
            cell,
            AuthRequired::Either,
            origins.iter().map(|o| o.to_string()),
            [],
        )
    }

    fn maps_handler() -> IntentHandler {
        IntentHandler::new(
            cell_seed(0x21),
            "Maps",
            IntentFilter::new(["android.intent.action.VIEW"], ["geo"]),
        )
    }
    fn browser_handler() -> IntentHandler {
        IntentHandler::new(
            cell_seed(0x22),
            "Browser",
            IntentFilter::new(["android.intent.action.VIEW"], ["http", "https"]),
        )
    }
    fn dialer_handler() -> IntentHandler {
        IntentHandler::new(
            cell_seed(0x23),
            "Dialer",
            IntentFilter::new(["android.intent.action.DIAL"], ["tel"]),
        )
    }

    /// **THE LOAD-BEARING TEST: an intent with NO cap-reachable handler is refused —
    /// the app cannot `startActivity` to an arbitrary handler it was never granted.**
    #[test]
    fn intent_with_no_reachable_handler_is_refused() {
        let me = cell_seed(9);
        // The neighborhood holds a dialer only — no geo/maps handler was granted.
        let resolver = IntentResolver::new([dialer_handler()], Some(me));
        let surface = SurfaceCapability::root(me, AuthRequired::Either);

        let intent = AndroidIntent::view("android.intent.action.VIEW", "geo:37.0,-122.0?q=cafe");
        let receipt = resolver.resolve(&surface, &intent);

        assert!(
            receipt.decision.refused_no_handler(),
            "a geo VIEW with no granted maps handler reaches nothing (no ambient startActivity)"
        );
        assert_eq!(receipt.cell, Some(me));
        assert!(receipt.status_line().contains("never granted"));
        assert_eq!(
            receipt.decision_digest,
            IntentReceipt::digest(Some(me), &intent, &receipt.decision)
        );
    }

    /// Exactly one cap-reachable handler matches ⟹ a cap-bounded hand-off to that one
    /// named cell (the targeted turn that replaces the ambient dispatch).
    #[test]
    fn single_match_resolves_to_a_named_handler() {
        let me = cell_seed(9);
        let resolver = IntentResolver::new([maps_handler(), dialer_handler()], Some(me));
        let surface = SurfaceCapability::root(me, AuthRequired::Either);

        let intent = AndroidIntent::view("android.intent.action.VIEW", "geo:37.0,-122.0?q=cafe");
        let receipt = resolver.resolve(&surface, &intent);

        match &receipt.decision {
            IntentDecision::Resolved { handler, label } => {
                assert_eq!(*handler, cell_seed(0x21));
                assert_eq!(label, "Maps");
            }
            other => panic!("expected Resolved, got {other:?}"),
        }
        assert!(receipt.status_line().contains("cap-bounded turn"));
    }

    /// A web (`https`) data origin the held cap does NOT authorize is refused at the
    /// gate, before the spotter — the same fetch-allowlist tooth the net gate bites with.
    #[test]
    fn uncapped_web_origin_is_refused_before_resolution() {
        let me = cell_seed(9);
        let resolver = IntentResolver::new([browser_handler()], Some(me));
        // The cap allows example.com only; the intent points at tracker.evil.com.
        let surface = web_cap(me, &["https://example.com"]);

        let intent = AndroidIntent::view(
            "android.intent.action.VIEW",
            "https://tracker.evil.com/track?id=1",
        );
        let receipt = resolver.resolve(&surface, &intent);

        assert!(
            receipt.decision.refused_by_cap(),
            "the uncapped web origin is refused before the handler is consulted"
        );
        assert_eq!(
            receipt.decision,
            IntentDecision::RefusedByCap {
                origin: "https://tracker.evil.com".to_string()
            }
        );
        assert!(
            receipt
                .status_line()
                .contains("does not authorize the data origin")
        );
    }

    /// The other web half: a cap-authorized origin passes the cap tooth and resolves to
    /// the granted browser handler.
    #[test]
    fn capped_web_origin_resolves_to_the_browser() {
        let me = cell_seed(9);
        let resolver = IntentResolver::new([browser_handler()], Some(me));
        let surface = web_cap(me, &["https://example.com"]);

        let intent = AndroidIntent::view("android.intent.action.VIEW", "https://example.com/page");
        let receipt = resolver.resolve(&surface, &intent);

        assert!(
            receipt.decision.resolved(),
            "cap-authorized origin resolves"
        );
        match receipt.decision {
            IntentDecision::Resolved { handler, .. } => assert_eq!(handler, cell_seed(0x22)),
            other => panic!("expected Resolved, got {other:?}"),
        }
    }

    /// Two cap-reachable handlers match ⟹ an EXPLICIT chooser, never a silent
    /// default-app auto-pick (the ambient standing grant deos refuses to mint).
    #[test]
    fn multiple_matches_surface_an_explicit_chooser() {
        let me = cell_seed(9);
        // Two browsers, both granted, both answer https VIEW.
        let other_browser = IntentHandler::new(
            cell_seed(0x24),
            "Reader",
            IntentFilter::new(["android.intent.action.VIEW"], ["https"]),
        );
        let resolver = IntentResolver::new([browser_handler(), other_browser], Some(me));
        let surface = web_cap(me, &["https://example.com"]);

        let intent = AndroidIntent::view("android.intent.action.VIEW", "https://example.com/page");
        let receipt = resolver.resolve(&surface, &intent);

        match &receipt.decision {
            IntentDecision::Ambiguous { candidates } => {
                assert_eq!(candidates.len(), 2, "both granted browsers are candidates");
            }
            other => panic!("expected Ambiguous, got {other:?}"),
        }
        assert!(receipt.status_line().contains("explicit chooser"));
    }

    /// The AOSP category leg: a handler matches only if it declares EVERY category the
    /// intent carries (`intent.categories ⊆ filter.categories`).
    #[test]
    fn category_subset_is_required() {
        let intent = AndroidIntent {
            action: "android.intent.action.VIEW".into(),
            data: Some("https://example.com".into()),
            mime_type: None,
            categories: ["android.intent.category.BROWSABLE".to_string()]
                .into_iter()
                .collect(),
        };
        // A filter WITHOUT the BROWSABLE category does not match a BROWSABLE intent.
        let no_cat = IntentFilter::new(["android.intent.action.VIEW"], ["https"]);
        assert!(!no_cat.matches(&intent));
        // Declaring the category makes it match.
        let with_cat = IntentFilter::new(["android.intent.action.VIEW"], ["https"])
            .with_categories(["android.intent.category.BROWSABLE"]);
        assert!(with_cat.matches(&intent));
    }

    /// Scheme + origin extraction is faithful across web and non-web URIs.
    #[test]
    fn scheme_and_origin_extraction() {
        let web = AndroidIntent::view("a", "https://Example.com/path?x=1");
        assert_eq!(web.scheme().as_deref(), Some("https"));
        assert_eq!(web.web_origin().as_deref(), Some("https://Example.com"));

        let tel = AndroidIntent::view("a", "tel:+15551234");
        assert_eq!(tel.scheme().as_deref(), Some("tel"));
        assert_eq!(tel.web_origin(), None, "tel has no fetchable web origin");

        let geo = AndroidIntent::view("a", "geo:0,0?q=cafe");
        assert_eq!(geo.scheme().as_deref(), Some("geo"));
        assert_eq!(geo.web_origin(), None);
    }

    /// `am_start_args` is the activity-manager `start` argv (action · data · mime · cat).
    #[test]
    fn am_start_args_are_the_activity_manager_flags() {
        let intent = AndroidIntent {
            action: "android.intent.action.VIEW".into(),
            data: Some("geo:0,0?q=cafe".into()),
            mime_type: Some("text/plain".into()),
            categories: ["android.intent.category.BROWSABLE".to_string()]
                .into_iter()
                .collect(),
        };
        assert_eq!(
            intent.am_start_args(),
            vec![
                "am",
                "start",
                "-a",
                "android.intent.action.VIEW",
                "-d",
                "geo:0,0?q=cafe",
                "-t",
                "text/plain",
                "-c",
                "android.intent.category.BROWSABLE",
            ]
        );
    }

    /// **THE LIVE-GATE LOAD-BEARING TEST: a singly-resolved cap-admitted intent reaches
    /// the device (`am start`); a no-handler / cap-refused / ambiguous intent NEVER does.**
    #[test]
    fn gate_dispatches_only_a_resolved_intent_to_the_device() {
        let me = cell_seed(9);
        let resolver = IntentResolver::new(
            [maps_handler(), dialer_handler(), browser_handler()],
            Some(me),
        );
        let mut gate = AndroidIntentGate::new(resolver, RecordingIntentSink::default());
        let cap = web_cap(me, &["https://example.com"]);

        // (a) Resolved → dispatched to the device.
        let r = gate.dispatch(
            &cap,
            AndroidIntent::view("android.intent.action.VIEW", "geo:37,-122?q=cafe"),
        );
        assert!(r.decision.resolved());
        assert_eq!(gate.sink_mut().dispatched.len(), 1, "the geo VIEW launched");
        assert_eq!(
            gate.sink_mut().dispatched[0].1,
            cell_seed(0x21),
            "dispatched to the Maps handler cell"
        );

        // (b) No cap-reachable handler → refused, device untouched.
        let before = gate.sink_mut().dispatched.len();
        let r = gate.dispatch(
            &cap,
            AndroidIntent::view("android.intent.action.SEND", "mailto:x@y.z"),
        );
        assert!(r.decision.refused_no_handler());
        assert_eq!(
            gate.sink_mut().dispatched.len(),
            before,
            "no am start for an unhandleable intent"
        );

        // (c) Cap-refused web origin → refused before resolution, device untouched.
        let before = gate.sink_mut().dispatched.len();
        let r = gate.dispatch(
            &cap,
            AndroidIntent::view("android.intent.action.VIEW", "https://tracker.evil.com/x"),
        );
        assert!(r.decision.refused_by_cap());
        assert_eq!(
            gate.sink_mut().dispatched.len(),
            before,
            "no am start for a cap-refused origin"
        );

        // (d) Ambiguous → awaits the chooser, NOT auto-dispatched.
        let other_dialer = IntentHandler::new(
            cell_seed(0x33),
            "VoIP",
            IntentFilter::new(["android.intent.action.DIAL"], ["tel"]),
        );
        let resolver2 = IntentResolver::new([dialer_handler(), other_dialer], Some(me));
        let mut gate2 = AndroidIntentGate::new(resolver2, RecordingIntentSink::default());
        let r = gate2.dispatch(
            &SurfaceCapability::root(me, AuthRequired::Either),
            AndroidIntent::view("android.intent.action.DIAL", "tel:+15551234"),
        );
        assert!(r.decision.ambiguous());
        assert!(
            gate2.sink_mut().dispatched.is_empty(),
            "an ambiguous intent is never silently auto-dispatched"
        );
    }

    /// A resolved + cap-admitted intent whose device dispatch fails is `DispatchFailed`
    /// (distinct from a cap/no-handler refusal) — cap, resolution, and transport are
    /// three distinct teeth.
    #[test]
    fn dispatch_failure_is_distinct_from_refusal() {
        let me = cell_seed(9);
        let resolver = IntentResolver::new([maps_handler()], Some(me));
        let sink = RecordingIntentSink {
            fail_with: Some("device offline".into()),
            ..Default::default()
        };
        let mut gate = AndroidIntentGate::new(resolver, sink);
        let r = gate.dispatch(
            &SurfaceCapability::root(me, AuthRequired::Either),
            AndroidIntent::view("android.intent.action.VIEW", "geo:0,0?q=x"),
        );
        assert!(!r.decision.refused_by_cap());
        assert!(!r.decision.refused_no_handler());
        assert!(r.decision.dispatch_failed());
        assert!(
            r.status_line()
                .contains("device dispatch (am start) failed")
        );
        assert_eq!(
            r.decision_digest,
            IntentReceipt::digest(Some(me), &r.intent, &r.decision)
        );
    }
}
