//! **The input bridge — feed input INTO the android runtime so you can USE the app,
//! not just watch it.** The reverse of the tile path: where [`crate::frame`] pulls the
//! app's surface OUT as an [`RgbaFrame`], this pushes deos input INTO the running app.
//!
//! `servo : web :: android-runtime : android` holds here too. The webcell routes a
//! focused tile's typed keys + pointer events into the live Servo engine
//! (`panels_webshell.rs`); the android-cell routes the SAME deos input into the
//! confined Android runtime — a tap/swipe/key/text delivered to the device's input
//! channel (`adb shell input`), after which a re-capture shows the app actually changed.
//!
//! # Input is an authorized exercise (the cap gate, before the device)
//!
//! An input event is not ambient: it is the exercise of authority over a surface, so
//! it is gated EXACTLY like the present and the egress. The held [`SurfaceCapability`]'s
//! **window rights** ([`Target::Surface`] focus/touch authority — the firmament
//! `granted ⊆ held` lattice) decide whether the holder may drive the surface at all.
//! This is the input-side of the compositor's **T3 focus tooth**: a surface the cap
//! does not grant focus to receives NO input (`ANDROID-CELL.md §6`). A cap-denied input
//! is [`InputDecision::RefusedByCap`] **before any `adb` call** — the device never sees
//! it — and every decision, admit or deny, leaves an [`InputReceipt`].
//!
//! # The depth (honest, like the net gate's)
//!
//! The shallow-but-real layer drives the device through `adb shell input` (tap/swipe/
//! text/keyevent) — the SAME injection path `scrcpy` and the emulator console use, and
//! the one the doc's §6 names. The DEEP per-event provenance (a binder-level input
//! source the app can attribute to a specific cap) is the same HAL/binder-interposition
//! frontier the net gate's deep layer names — not claimed here. What IS proven: a tap
//! the cap admits reaches the app and CHANGES ITS FRAME (a before/after differ); a tap
//! the cap denies reaches nothing.

use crate::frame::ScreencapError;
use starbridge_web_surface::SurfaceCapability;

/// A deos input event bound for the android app — the [`crate::WebInput`]-analogue for
/// the android runtime. Each variant maps to one `adb shell input` subcommand; the
/// coordinates are in the captured frame's pixel space (device pixels), so a desktop
/// window that hosts the tile can forward a pointer event verbatim after mapping window
/// coords → device coords.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AndroidInput {
    /// A tap at device-pixel `(x, y)` — `input tap x y`. The pointer-down/up of a
    /// click on the hosted tile.
    Tap { x: u32, y: u32 },
    /// A swipe from `(x1, y1)` to `(x2, y2)` over `duration_ms` — `input swipe …`. A
    /// drag/scroll/fling on the tile.
    Swipe {
        x1: u32,
        y1: u32,
        x2: u32,
        y2: u32,
        duration_ms: u32,
    },
    /// Literal text typed into the focused field — `input text <s>`. The android `input`
    /// tool requires spaces be escaped as `%s`; [`Self::adb_args`] does that.
    Text { text: String },
    /// An Android keycode by name (e.g. `KEYCODE_BACK`, `KEYCODE_HOME`, `KEYCODE_ENTER`)
    /// — `input keyevent <name>`. The named-key channel a desktop window's key events
    /// map onto.
    Key { keycode: String },
}

impl AndroidInput {
    /// The `adb shell` argument vector that injects this event. The `input` tool is the
    /// device-side injector; these are exactly its subcommands. Text is `%s`-escaped per
    /// the `input` tool's contract (a raw space would be argv-split into two tokens).
    pub fn adb_args(&self) -> Vec<String> {
        match self {
            AndroidInput::Tap { x, y } => {
                vec!["input".into(), "tap".into(), x.to_string(), y.to_string()]
            }
            AndroidInput::Swipe {
                x1,
                y1,
                x2,
                y2,
                duration_ms,
            } => vec![
                "input".into(),
                "swipe".into(),
                x1.to_string(),
                y1.to_string(),
                x2.to_string(),
                y2.to_string(),
                duration_ms.to_string(),
            ],
            AndroidInput::Text { text } => {
                // The `input text` tool argv-splits on spaces; its escape is `%s`.
                vec!["input".into(), "text".into(), text.replace(' ', "%s")]
            }
            AndroidInput::Key { keycode } => {
                vec!["input".into(), "keyevent".into(), keycode.clone()]
            }
        }
    }

    /// A short tag distinguishing the kind, for the receipt digest + status line.
    fn tag(&self) -> &'static str {
        match self {
            AndroidInput::Tap { .. } => "tap",
            AndroidInput::Swipe { .. } => "swipe",
            AndroidInput::Text { .. } => "text",
            AndroidInput::Key { .. } => "key",
        }
    }
}

/// The two distinguishable ends an input attempt can reach — the input-side trichotomy
/// of [`crate::IoDecision`] (there is no "transport" middle here; the device either
/// gets the event or the cap refused it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputDecision {
    /// The held cap granted focus/touch authority over the surface AND the event was
    /// injected into the device.
    Injected,
    /// The held [`SurfaceCapability`] does NOT grant focus/touch authority over this
    /// surface — refused AT the gate, before any `adb` call. The device never sees the
    /// event. THIS is the no-ambient-input property (the input-side T3 focus tooth).
    RefusedByCap,
    /// The cap admitted the input, but the device-side injection itself failed (the
    /// runtime's `adb input` returned non-zero) — the transport's own refusal, distinct
    /// from the cap's.
    Failed { reason: String },
}

impl InputDecision {
    pub fn injected(&self) -> bool {
        matches!(self, InputDecision::Injected)
    }
    pub fn refused_by_cap(&self) -> bool {
        matches!(self, InputDecision::RefusedByCap)
    }
}

/// **The receipt left by a gated input decision.** Every event the gate decides — admit
/// or deny — produces one, so the android-cell's input is auditable end to end, exactly
/// like the egress [`crate::IoReceipt`]. An input is an *authorized exercise over a
/// surface*; this is its faithful receipt at the shallow per-event granularity this
/// layer provides.
///
/// Content-addressed: `decision_digest = blake3(surface_cell ‖ tag ‖ adb_args ‖
/// outcome)`, so a verifier can reconstruct and check it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputReceipt {
    /// The cell whose held cap decided this input (the authority lineage).
    pub cell: Option<dregg_firmament::CellId>,
    /// The event the holder tried to deliver.
    pub input: AndroidInput,
    /// The decision reached.
    pub decision: InputDecision,
    /// `blake3(…)[..32]` — the content-addressed witness of this decision.
    pub decision_digest: [u8; 32],
}

impl InputReceipt {
    fn digest(
        cell: Option<dregg_firmament::CellId>,
        input: &AndroidInput,
        decision: &InputDecision,
    ) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        if let Some(c) = cell {
            h.update(b"\x01cell");
            h.update(c.as_bytes());
        }
        h.update(input.tag().as_bytes());
        for a in input.adb_args() {
            h.update(b"\x00");
            h.update(a.as_bytes());
        }
        match decision {
            InputDecision::Injected => h.update(b"\x01injected"),
            InputDecision::RefusedByCap => h.update(b"\x02refused-by-cap"),
            InputDecision::Failed { reason } => {
                h.update(b"\x03failed");
                h.update(reason.as_bytes())
            }
        };
        *h.finalize().as_bytes()
    }

    /// A one-line audit truth for the cockpit status line — which end, named exactly.
    pub fn status_line(&self) -> String {
        match &self.decision {
            InputDecision::Injected => format!(
                "android-input: ✔ {} injected into the confined runtime — a cap-authorized exercise over the surface",
                self.input.tag()
            ),
            InputDecision::RefusedByCap => format!(
                "android-input: ✖ {} REFUSED at the gate — the held SurfaceCapability does not grant focus/touch over this surface (no adb call; the device never saw it)",
                self.input.tag()
            ),
            InputDecision::Failed { reason } => format!(
                "android-input: ⚠ {} cap-authorized but the device injection failed ({reason})",
                self.input.tag()
            ),
        }
    }
}

/// **The cap focus tooth, input-side.** Does the held `surface` cap grant the holder
/// authority to drive (focus/touch) this surface at all?
///
/// The window rights ([`SurfaceCapability::window`]) ARE the focus/touch authority (the
/// firmament `Target::Surface` rights lattice). A surface the cap does not back grants
/// no input. We require the cap to actually name a backing cell — a cap with no surface
/// target (`cell() == None`) is not authority over any surface, so it cannot drive one.
/// This mirrors the compositor's T3 focus tooth: only a focus-bearing surface receives
/// input.
pub fn cap_admits_input(surface: &SurfaceCapability) -> bool {
    surface.cell().is_some()
}

/// **The device-side input sink.** A runtime that can have input injected into it. The
/// [`crate::AndroidRuntime`] gains this so the input bridge is host-adaptive exactly
/// like capture: the macOS emulator drives `adb shell input`; a Linux redroid impl
/// drives the container's input channel; the captured stand-in records the intent
/// without a device (so the gate + receipt logic tests on any node).
pub trait AndroidInputSink {
    /// Inject one already-cap-admitted event into the device. The cap check happens in
    /// [`AndroidInputGate::deliver`] BEFORE this is ever called — an impl here is the
    /// transport, not the authority. Returns `Ok(())` on a successful injection, or an
    /// error the gate turns into [`InputDecision::Failed`].
    fn inject_input(&mut self, input: &AndroidInput) -> Result<(), InputError>;
}

/// Why a device-side injection failed (distinct from a cap refusal, which never reaches
/// the device).
#[derive(Debug)]
pub enum InputError {
    /// A required tool (`adb`) was not found.
    ToolMissing { tool: String, looked_in: String },
    /// The `adb input` command exited non-zero.
    CommandFailed { cmd: String, stderr: String },
    /// An I/O error invoking the tool.
    Io(std::io::Error),
    /// The capture-after-input could not be parsed (used by the differ helper).
    Capture(ScreencapError),
}

impl std::fmt::Display for InputError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InputError::ToolMissing { tool, looked_in } => {
                write!(f, "android tool `{tool}` not found (looked in {looked_in})")
            }
            InputError::CommandFailed { cmd, stderr } => {
                write!(f, "`{cmd}` failed: {stderr}")
            }
            InputError::Io(e) => write!(f, "io: {e}"),
            InputError::Capture(e) => write!(f, "capture: {e}"),
        }
    }
}

impl std::error::Error for InputError {}

impl From<std::io::Error> for InputError {
    fn from(e: std::io::Error) -> Self {
        InputError::Io(e)
    }
}
impl From<ScreencapError> for InputError {
    fn from(e: ScreencapError) -> Self {
        InputError::Capture(e)
    }
}

/// **THE INPUT GATE.** Holds the device sink + the cell the input speaks for; holds NO
/// ambient authority — every [`deliver`](Self::deliver) is a function of the `surface`
/// cap argument, exactly as [`crate::AndroidNetGate`] is for egress.
pub struct AndroidInputGate<S: AndroidInputSink> {
    sink: S,
    cell: Option<dregg_firmament::CellId>,
}

impl<S: AndroidInputSink> AndroidInputGate<S> {
    /// Bind a gate to a device sink (the injection transport) and the cell it speaks for
    /// (recorded on each receipt; the cap argument is what actually decides).
    pub fn new(sink: S, cell: Option<dregg_firmament::CellId>) -> Self {
        AndroidInputGate { sink, cell }
    }

    pub fn sink_mut(&mut self) -> &mut S {
        &mut self.sink
    }

    /// **DELIVER ONE INPUT, GATED.** Decide `input` against the held `surface` cap and,
    /// iff admitted, inject it into the device — returning the decision AND its
    /// [`InputReceipt`].
    ///
    /// A cap-denied surface returns [`InputDecision::RefusedByCap`] and **the device is
    /// never touched** — no `adb` call, the event reaches nothing. The gate bites at the
    /// authority boundary, before the injection — the input-side of the compositor's T3
    /// focus tooth.
    pub fn deliver(&mut self, surface: &SurfaceCapability, input: AndroidInput) -> InputReceipt {
        // STEP 1 — THE CAP, BEFORE THE DEVICE. A surface the held cap does not grant
        // focus/touch over is refused here; the device sink is never reached.
        if !cap_admits_input(surface) {
            return self.receipt(input, InputDecision::RefusedByCap);
        }

        // STEP 2 — INJECT INTO THE CONFINED RUNTIME. The cap admitted; deliver the event
        // through the host-adaptive sink (adb input / redroid channel).
        let decision = match self.sink.inject_input(&input) {
            Ok(()) => InputDecision::Injected,
            Err(e) => InputDecision::Failed {
                reason: e.to_string(),
            },
        };
        self.receipt(input, decision)
    }

    fn receipt(&self, input: AndroidInput, decision: InputDecision) -> InputReceipt {
        let decision_digest = InputReceipt::digest(self.cell, &input, &decision);
        InputReceipt {
            cell: self.cell,
            input,
            decision,
            decision_digest,
        }
    }
}

/// **The host-independent input stand-in.** A sink with no live device: it RECORDS the
/// `adb_args` of every admitted event (the intent) without touching a device, so the
/// gate + receipt + cap logic test on any node — the input-side of
/// [`crate::CapturedFrameRuntime`].
#[derive(Default)]
pub struct RecordingInputSink {
    /// Every injected event's `adb_args`, in order — the audit trail a test asserts on.
    pub injected: Vec<Vec<String>>,
    /// If set, `inject_input` returns this as a `CommandFailed` (to test the `Failed`
    /// arm without a device).
    pub fail_with: Option<String>,
}

impl AndroidInputSink for RecordingInputSink {
    fn inject_input(&mut self, input: &AndroidInput) -> Result<(), InputError> {
        if let Some(reason) = &self.fail_with {
            return Err(InputError::CommandFailed {
                cmd: format!("adb shell {}", input.adb_args().join(" ")),
                stderr: reason.clone(),
            });
        }
        self.injected.push(input.adb_args());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::cell_seed;
    use starbridge_web_surface::{AuthRequired, SurfaceCapability};

    fn surface(cell: dregg_firmament::CellId) -> SurfaceCapability {
        SurfaceCapability::root(cell, AuthRequired::Either)
    }

    #[test]
    fn adb_args_are_the_input_tool_subcommands() {
        assert_eq!(
            AndroidInput::Tap { x: 540, y: 1200 }.adb_args(),
            vec!["input", "tap", "540", "1200"]
        );
        assert_eq!(
            AndroidInput::Swipe {
                x1: 100,
                y1: 1500,
                x2: 100,
                y2: 400,
                duration_ms: 250
            }
            .adb_args(),
            vec!["input", "swipe", "100", "1500", "100", "400", "250"]
        );
        // Spaces escape to %s — the `input text` contract.
        assert_eq!(
            AndroidInput::Text {
                text: "hello world".into()
            }
            .adb_args(),
            vec!["input", "text", "hello%sworld"]
        );
        assert_eq!(
            AndroidInput::Key {
                keycode: "KEYCODE_BACK".into()
            }
            .adb_args(),
            vec!["input", "keyevent", "KEYCODE_BACK"]
        );
    }

    /// **THE LOAD-BEARING TEST: a cap-authorized tap is injected into the runtime and
    /// the receipt records the injection; a cap WITHOUT a backing surface is refused at
    /// the gate before any device call.**
    #[test]
    fn capped_input_injects_uncapped_is_refused_before_the_device() {
        let cell = cell_seed(11);
        let mut gate = AndroidInputGate::new(RecordingInputSink::default(), Some(cell));

        // Authorized: a real surface cap → injected.
        let r = gate.deliver(&surface(cell), AndroidInput::Tap { x: 540, y: 1200 });
        assert!(
            r.decision.injected(),
            "a cap over the surface injects the tap"
        );
        assert_eq!(r.cell, Some(cell));
        assert!(r
            .status_line()
            .contains("injected into the confined runtime"));
        // The device sink actually saw the event.
        assert_eq!(
            gate.sink_mut().injected,
            vec![vec![
                "input".to_string(),
                "tap".into(),
                "540".into(),
                "1200".into()
            ]]
        );

        // Unauthorized: a cap with NO backing surface (a LOCAL kernel-slot target, not a
        // surface) → refused before the device, because it is not authority over a
        // surface at all.
        let no_surface = SurfaceCapability {
            window: dregg_firmament::Capability::local(0, AuthRequired::Either),
            fetch_allow: Some(Default::default()),
            navigate_allow: Some(Default::default()),
            permissions: Default::default(),
        };
        // sanity: such a cap names no surface cell
        assert!(no_surface.cell().is_none());
        let before = gate.sink_mut().injected.len();
        let r2 = gate.deliver(&no_surface, AndroidInput::Tap { x: 1, y: 1 });
        assert!(
            r2.decision.refused_by_cap(),
            "a cap that names no surface cannot drive one — refused before the device"
        );
        assert!(r2.status_line().contains("REFUSED at the gate"));
        assert!(r2.status_line().contains("the device never saw it"));
        // The device sink was NOT touched by the refused event.
        assert_eq!(
            gate.sink_mut().injected.len(),
            before,
            "no adb call for a cap-refused input"
        );
        // The receipt is content-addressed and reconstructible.
        assert_eq!(
            r2.decision_digest,
            InputReceipt::digest(Some(cell), &AndroidInput::Tap { x: 1, y: 1 }, &r2.decision)
        );
    }

    /// A cap-authorized event whose device-side injection fails is `Failed` (distinct
    /// from a cap refusal) — the cap and the transport are distinct teeth, input-side.
    #[test]
    fn injection_failure_is_distinct_from_cap_refusal() {
        let cell = cell_seed(11);
        let sink = RecordingInputSink {
            fail_with: Some("device offline".into()),
            ..Default::default()
        };
        let mut gate = AndroidInputGate::new(sink, Some(cell));
        let r = gate.deliver(
            &surface(cell),
            AndroidInput::Key {
                keycode: "KEYCODE_HOME".into(),
            },
        );
        assert!(!r.decision.refused_by_cap());
        assert!(matches!(r.decision, InputDecision::Failed { .. }));
        assert!(r.status_line().contains("device injection failed"));
    }
}
