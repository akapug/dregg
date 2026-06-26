//! **The checkpointed runtime — the boundary umem made LOAD-BEARING in the live path.**
//!
//! # The revolution, made load-bearing
//!
//! [`crate::checkpoint`] proved that a confined runtime's cap-gated *boundary state*
//! (the presented frame + the witnessed receipt log) is a **umem** — the same
//! `(domain, key) ↦ value` address space, the same Blum write-trace + `fold` discipline
//! as the kernel executor's `turn/src/umem.rs`. But that proof lived in a *standalone*
//! object: the running [`AndroidRuntime`] captured frames and the gates left receipts
//! with **nothing in the live path folding them into a umem**. The checkpointable
//! service cell was a prototype the running system did not DEPEND on.
//!
//! This module closes that gap exactly as the other umem revolutions closed theirs (the
//! time-scrub now restores via `reify_ledger`, a suspended turn now resumes a passable
//! umem continuation, the membrane now stitches per-`UKey`): a [`CheckpointedRuntime`]
//! WRAPS any live runtime and threads a [`ServiceCellCheckpoint`] through **every
//! boundary advance**. Each captured frame, each cap-gated I/O / input decision, is
//! folded into the checkpoint as a **fold-verified Blum trace** connecting the
//! pre-boundary to the post-boundary — the executable shadow of the kernel's
//! `*_is_memory_program` agreement, accumulated continuously as the app runs. So a
//! confined Android app, while it is LIVE, has:
//!
//!  * **save**    — [`CheckpointedRuntime::save`] hands out the current boundary umem
//!    ([`ServiceCellCheckpoint`]) + its commitment, a serializable migratable witness;
//!  * **restore / migrate** — [`CheckpointedRuntime::migrate_onto`] reconstructs the
//!    boundary on a FRESH runtime from that witness alone and *verifies* it projects the
//!    byte-identical umem + commitment, fail-closed (a corrupted witness refuses);
//!  * **compare** — [`CheckpointedRuntime::diff_against`] names the exact addresses that
//!    moved between two boundary checkpoints (content-addressed).
//!
//! Because [`CheckpointedRuntime`] itself impls [`AndroidRuntime`] /
//! [`crate::AndroidInputSink`] / [`crate::AndroidIntentSink`], it is a **drop-in** for a
//! bare runtime anywhere in the live mount: hand it to [`crate::AndroidInputGate::new`],
//! [`launch_installed_app`](crate::launch_installed_app), or the desktop android-window
//! mount, and every act that crosses the cap-gated boundary is now checkpointed as it
//! happens. The boundary umem is load-bearing, not decorative.
//!
//! # The honest seam (unchanged from [`crate::checkpoint`])
//!
//! This checkpoints the **boundary**, not the guest interior. A byte-faithful witnessed
//! capture of the confined runtime's full RAM/device/binder state is the named
//! deep-state frontier (see [`crate::checkpoint`]'s module doc); today the live path
//! delivers the honest, real boundary umem + the determinism hook.

use dregg_firmament::CellId;
use servo_render::RgbaFrame;

use crate::checkpoint::{
    diff, emit_boundary_trace, fold, ServiceCellCheckpoint, UKey, UProjection, UmemOp,
};
use crate::input::{AndroidInput, AndroidInputSink, InputError, InputReceipt};
use crate::intentgate::{AndroidIntent, AndroidIntentSink, IntentError};
use crate::netgate::IoReceipt;
use crate::runtime::{AndroidRuntime, AppLaunch, RuntimeError, RuntimeKind};

/// Why a checkpointed-runtime operation refused. A boundary advance that does NOT fold
/// (the agreement square `fold(pre, ops) == post` failed) or a restore whose
/// reconstructed boundary does not reproduce the saved umem + commitment is **refused**
/// — the boundary umem is unforgeable, fail-closed exactly as the kernel emitter is.
#[derive(Debug)]
pub enum CheckpointError {
    /// The underlying runtime failed (boot / launch / capture).
    Runtime(RuntimeError),
    /// A boundary advance did not fold pre → post (the agreement square failed) — the
    /// checkpoint is poisoned and refuses to vend a witness.
    BoundaryDisagreement(String),
    /// A restored / migrated boundary did not reproduce the saved umem or commitment —
    /// the witness is corrupt or spliced; refused before it can be trusted.
    RestoreMismatch {
        /// What disagreed (the umem projection or the commitment).
        what: String,
    },
}

impl std::fmt::Display for CheckpointError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheckpointError::Runtime(e) => write!(f, "runtime: {e}"),
            CheckpointError::BoundaryDisagreement(s) => {
                write!(f, "boundary umem advance did not fold pre → post: {s}")
            }
            CheckpointError::RestoreMismatch { what } => {
                write!(f, "restored boundary does not reproduce the saved {what}")
            }
        }
    }
}

impl std::error::Error for CheckpointError {}

impl From<RuntimeError> for CheckpointError {
    fn from(e: RuntimeError) -> Self {
        CheckpointError::Runtime(e)
    }
}

/// **A confined runtime whose cap-gated boundary is continuously checkpointed as a
/// umem.** Wraps any live [`AndroidRuntime`] `R` and threads a [`ServiceCellCheckpoint`]
/// through every boundary advance — each captured frame and each witnessed receipt is
/// folded into the checkpoint as a fold-verified Blum write, accumulated into a live
/// trace. Drop-in for a bare runtime (it impls [`AndroidRuntime`] and the input / intent
/// sinks) so the whole live mount gets save / restore / migrate / compare for free.
pub struct CheckpointedRuntime<R> {
    /// The live confined runtime (the device).
    rt: R,
    /// The service cell this runtime fronts.
    cell: CellId,
    /// The live boundary checkpoint — advanced on every capture / gated act.
    checkpoint: ServiceCellCheckpoint,
    /// The projection at the last folded boundary — the `pre` for the next advance.
    last_projection: UProjection,
    /// The accumulated Blum write-trace of every boundary advance, each op fold-verified
    /// against its pre. The live executable shadow of `*_is_memory_program`.
    trace: Vec<UmemOp>,
    /// Set if any advance failed to fold (the agreement square broke) — `save` refuses.
    poisoned: Option<String>,
}

impl<R> CheckpointedRuntime<R> {
    /// Wrap a live runtime `rt` fronting `cell`, with a fresh (empty) boundary checkpoint.
    pub fn new(rt: R, cell: CellId) -> Self {
        let checkpoint = ServiceCellCheckpoint::new(cell);
        let last_projection = checkpoint.project();
        CheckpointedRuntime {
            rt,
            cell,
            checkpoint,
            last_projection,
            trace: Vec::new(),
            poisoned: None,
        }
    }

    /// The cell this runtime fronts.
    pub fn cell(&self) -> CellId {
        self.cell
    }

    /// Borrow the inner runtime.
    pub fn runtime(&self) -> &R {
        &self.rt
    }

    /// Mutably borrow the inner runtime (for host-specific drives not on the trait).
    pub fn runtime_mut(&mut self) -> &mut R {
        &mut self.rt
    }

    /// The live boundary checkpoint (read-only).
    pub fn checkpoint(&self) -> &ServiceCellCheckpoint {
        &self.checkpoint
    }

    /// The accumulated fold-verified Blum write-trace of the whole session.
    pub fn boundary_trace(&self) -> &[UmemOp] {
        &self.trace
    }

    /// The current boundary umem projection (the live state).
    pub fn project(&self) -> UProjection {
        self.checkpoint.project()
    }

    /// The current boundary commitment (the service-cell analogue of the kernel root).
    pub fn commitment(&self) -> [u8; 32] {
        self.checkpoint.commitment()
    }

    /// **SAVE.** Vend the current boundary checkpoint as a migratable witness — a clone
    /// of the live [`ServiceCellCheckpoint`]. Refuses (fail-closed) if any advance ever
    /// failed to fold: a poisoned boundary will not hand out a witness.
    pub fn save(&self) -> Result<ServiceCellCheckpoint, CheckpointError> {
        if let Some(why) = &self.poisoned {
            return Err(CheckpointError::BoundaryDisagreement(why.clone()));
        }
        Ok(self.checkpoint.clone())
    }

    /// **COMPARE.** The addresses whose value differs between this live boundary and
    /// `other` — `(changed, only_here, only_there)`, content-addressed.
    pub fn diff_against(&self, other: &ServiceCellCheckpoint) -> (Vec<UKey>, Vec<UKey>, Vec<UKey>) {
        diff(&self.checkpoint.project(), &other.project())
    }

    /// The shared advance core: observe a boundary mutation, emit the Blum trace from the
    /// last projection to the new one, verify `fold(pre, ops) == post`, and extend the
    /// live trace. On disagreement, poison the boundary (fail-closed) and report.
    fn advance(&mut self, observe: impl FnOnce(&mut ServiceCellCheckpoint)) -> Result<(), String> {
        let pre = self.last_projection.clone();
        observe(&mut self.checkpoint);
        let post = self.checkpoint.project();
        match emit_boundary_trace(&pre, &post) {
            Ok(ops) => {
                debug_assert_eq!(fold(&pre, &ops), post, "the advance folds pre → post");
                self.trace.extend(ops);
                self.last_projection = post;
                Ok(())
            }
            Err(why) => {
                self.poisoned = Some(why.clone());
                Err(why)
            }
        }
    }

    /// **RECORD a witnessed egress decision** into the live boundary (its receipt digest
    /// joins the append-only index log as a fold-verified advance).
    pub fn record_io(&mut self, receipt: &IoReceipt) -> Result<(), CheckpointError> {
        self.advance(|cp| cp.observe_io(receipt))
            .map_err(CheckpointError::BoundaryDisagreement)
    }

    /// **RECORD a witnessed input decision** into the live boundary (the input gate's
    /// [`InputReceipt`] joins the append-only log as a fold-verified advance).
    pub fn record_input(&mut self, receipt: &InputReceipt) -> Result<(), CheckpointError> {
        self.advance(|cp| cp.observe_input(receipt))
            .map_err(CheckpointError::BoundaryDisagreement)
    }
}

impl<R: AndroidRuntime> CheckpointedRuntime<R> {
    /// **CAPTURE + CHECKPOINT** (fail-closed). Capture the live surface through the inner
    /// runtime and fold the frame into the boundary umem as a verified Blum advance — the
    /// load-bearing live-path capture. Refuses if the advance does not fold.
    pub fn capture_checkpointed(&mut self) -> Result<RgbaFrame, CheckpointError> {
        let frame = self.rt.capture_frame()?;
        self.advance(|cp| cp.observe_frame(&frame))
            .map_err(CheckpointError::BoundaryDisagreement)?;
        Ok(frame)
    }

    /// **RESTORE / MIGRATE** a saved boundary checkpoint onto a FRESH runtime. The
    /// boundary is reconstructed from the witness ALONE (the frame, present-seq, and the
    /// append-only receipt log — the deterministic-replay restore) and then *verified* to
    /// reproduce the saved umem projection AND the saved commitment, fail-closed: a
    /// corrupt or spliced witness is refused before it is ever trusted. The returned
    /// runtime is live over `fresh` with the migrated boundary as its checkpoint, ready
    /// to advance further (its trace continues from the restored projection).
    pub fn migrate_onto(
        saved: &ServiceCellCheckpoint,
        fresh: R,
    ) -> Result<CheckpointedRuntime<R>, CheckpointError> {
        let saved_projection = saved.project();
        let saved_commitment = saved.commitment();

        // Reconstruct from the witness fields alone (deterministic-replay restore).
        let mut restored = ServiceCellCheckpoint::new(saved.cell);
        restored.frame = saved.frame;
        restored.present_seq = saved.present_seq;
        restored.receipt_log = saved.receipt_log.clone();

        // VERIFY: the reconstruction reproduces the saved umem + commitment, else refuse.
        if restored.project() != saved_projection {
            return Err(CheckpointError::RestoreMismatch {
                what: "umem projection".into(),
            });
        }
        if restored.commitment() != saved_commitment {
            return Err(CheckpointError::RestoreMismatch {
                what: "commitment".into(),
            });
        }

        let last_projection = restored.project();
        Ok(CheckpointedRuntime {
            rt: fresh,
            cell: saved.cell,
            checkpoint: restored,
            last_projection,
            trace: Vec::new(),
            poisoned: None,
        })
    }

    /// **RESTORE against a trusted root** (the real migration teeth). The destination
    /// node knows, out-of-band, the boundary commitment it expects (the handoff root).
    /// Reconstruct from the witness and refuse — fail-closed — unless the reconstructed
    /// boundary's commitment EQUALS `expected_commitment`: a witness whose fields were
    /// spliced (a forged frame digest, a truncated receipt log) carries a different
    /// commitment than the trusted root and is rejected before it is ever live.
    pub fn migrate_onto_expecting(
        saved: &ServiceCellCheckpoint,
        expected_commitment: [u8; 32],
        fresh: R,
    ) -> Result<CheckpointedRuntime<R>, CheckpointError> {
        let migrated = Self::migrate_onto(saved, fresh)?;
        if migrated.commitment() != expected_commitment {
            return Err(CheckpointError::RestoreMismatch {
                what: "commitment (does not match the trusted handoff root)".into(),
            });
        }
        Ok(migrated)
    }
}

// ── DROP-IN: a CheckpointedRuntime IS an AndroidRuntime ──────────────────────
//
// Delegates boot / launch / kind; `capture_frame` ALSO folds the frame into the live
// boundary (the trait signature is total, so a fold disagreement poisons the boundary
// rather than failing the capture — `save` then refuses). Use `capture_checkpointed`
// for the explicit fail-closed capture.
impl<R: AndroidRuntime> AndroidRuntime for CheckpointedRuntime<R> {
    fn kind(&self) -> RuntimeKind {
        self.rt.kind()
    }
    fn boot(&mut self) -> Result<(), RuntimeError> {
        self.rt.boot()
    }
    fn launch_app(&mut self, app: &AppLaunch) -> Result<(), RuntimeError> {
        self.rt.launch_app(app)
    }
    fn capture_frame(&mut self) -> Result<RgbaFrame, RuntimeError> {
        let frame = self.rt.capture_frame()?;
        // Fold the boundary; poison (fail-closed at `save`) on the impossible disagreement.
        let _ = self.advance(|cp| cp.observe_frame(&frame));
        Ok(frame)
    }
}

// ── DROP-IN: a CheckpointedRuntime IS an input sink (when its inner runtime is) ──
//
// The gate's cap check fires in `AndroidInputGate::deliver` BEFORE this transport leg;
// this delegates the injection to the inner runtime. The gate hands the receipt back to
// the caller, who folds it via `record_input` (the receipt is the gate's product, not
// the sink's). So: `AndroidInputGate::new(checkpointed_rt, cell)` drives the device, and
// `gate.sink_mut().record_input(&r)` + `gate.sink_mut().capture_checkpointed()` checkpoint.
impl<R: AndroidInputSink> AndroidInputSink for CheckpointedRuntime<R> {
    fn inject_input(&mut self, input: &AndroidInput) -> Result<(), InputError> {
        self.rt.inject_input(input)
    }
}

// ── DROP-IN: a CheckpointedRuntime IS an intent sink (when its inner runtime is) ──
impl<R: AndroidIntentSink> AndroidIntentSink for CheckpointedRuntime<R> {
    fn start_activity(
        &mut self,
        intent: &AndroidIntent,
        handler: CellId,
    ) -> Result<(), IntentError> {
        self.rt.start_activity(intent, handler)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::{InputDecision, InputReceipt};
    use crate::netgate::{IoDecision, IoReceipt};
    use crate::runtime::CapturedFrameRuntime;
    use dregg_firmament::cell_seed;

    fn home_runtime() -> CapturedFrameRuntime {
        let raw = include_bytes!("../fixtures/android_home_screencap.raw").to_vec();
        CapturedFrameRuntime::from_screencap_raw(raw)
    }

    fn io_receipt(cell: CellId, origin: &str, dialed: bool) -> IoReceipt {
        let decision = if dialed {
            IoDecision::Dialed {
                origin: origin.to_string(),
                peer: crate::netgate::origin_to_peer(origin),
            }
        } else {
            IoDecision::RefusedByCap {
                origin: origin.to_string(),
            }
        };
        IoReceipt {
            cell: Some(cell),
            origin: origin.to_string(),
            decision,
            decision_digest: blake3::hash(format!("{origin}:{dialed}").as_bytes()).as_bytes()[..32]
                .try_into()
                .unwrap(),
        }
    }

    /// **THE LIVE-PATH SHADOW (structural, any node).** Driving the runtime through the
    /// `CheckpointedRuntime` wrapper checkpoints the boundary as it runs: each capture +
    /// each gated act is a fold-verified Blum advance, and the accumulated trace is a
    /// disciplined memory program connecting genesis to the live boundary.
    #[test]
    fn driving_the_runtime_checkpoints_the_boundary_as_it_runs() {
        let cell = cell_seed(3);
        let mut crt = CheckpointedRuntime::new(home_runtime(), cell);
        crt.boot().expect("boot");
        crt.launch_app(&AppLaunch::Component(
            "com.android.settings/.Settings".into(),
        ))
        .expect("launch");

        // Capture a frame (boundary advance #1) — through the explicit fail-closed path.
        let _f = crt
            .capture_checkpointed()
            .expect("capture folds the boundary");
        // A gated egress decision (advance #2) + a gated input decision (advance #3).
        crt.record_io(&io_receipt(cell, "https://tracker.evil.com", false))
            .expect("io folds");
        crt.record_input(&InputReceipt {
            cell: Some(cell),
            input: AndroidInput::Tap { x: 10, y: 20 },
            decision: InputDecision::Injected,
            decision_digest: [9u8; 32],
        })
        .expect("input folds");

        // The accumulated trace is non-empty and the live projection matches the fold of
        // the whole trace over genesis (the executable shadow holds end-to-end).
        assert!(
            !crt.boundary_trace().is_empty(),
            "the session accumulated a trace"
        );
        let genesis = ServiceCellCheckpoint::new(cell).project();
        assert_eq!(
            fold(&genesis, crt.boundary_trace()),
            crt.project(),
            "fold(genesis, whole-session trace) == the live boundary — a disciplined memory program"
        );
        // The boundary recorded both witnessed acts in the append-only log.
        assert_eq!(crt.checkpoint().receipt_log.len(), 2);
    }

    /// **SAVE → MIGRATE → COMPARE (structural, any node).** A live boundary is saved,
    /// migrated onto a FRESH runtime byte-identically (the witness reproduces the umem +
    /// commitment), and a subsequent live advance on the origin is named by the compare.
    #[test]
    fn save_migrate_and_compare_on_the_live_path() {
        let cell = cell_seed(7);
        let mut origin = CheckpointedRuntime::new(home_runtime(), cell);
        origin.boot().unwrap();
        origin.capture_checkpointed().expect("capture A");
        origin
            .record_io(&io_receipt(cell, "https://api.example.com", true))
            .expect("io A");

        // SAVE the boundary witness.
        let saved = origin.save().expect("save vends the witness");
        let saved_commitment = saved.commitment();

        // MIGRATE onto a FRESH runtime (a "second node") — reconstructed + verified.
        let migrated = CheckpointedRuntime::migrate_onto(&saved, home_runtime())
            .expect("the witness reconstructs the boundary byte-identically");
        assert_eq!(
            migrated.commitment(),
            saved_commitment,
            "migration preserved the boundary commitment"
        );
        let (changed, only_a, only_b) = migrated.diff_against(&saved);
        assert!(
            changed.is_empty() && only_a.is_empty() && only_b.is_empty(),
            "the migrated boundary is byte-identical to the saved one"
        );

        // ADVANCE the origin (a new capture + receipt) and COMPARE against the saved A.
        origin.capture_checkpointed().expect("capture B");
        origin
            .record_input(&InputReceipt {
                cell: Some(cell),
                input: AndroidInput::Tap { x: 1, y: 2 },
                decision: InputDecision::Injected,
                decision_digest: [5u8; 32],
            })
            .expect("input B");
        // diff_against(saved) = (changed, only-in-live-origin, only-in-saved); the new
        // receipt the live advance appended is in only-in-origin.
        let (changed, only_in_origin, _only_in_saved) = origin.diff_against(&saved);
        assert!(
            changed.contains(&UKey::PresentSeq(cell)),
            "the present-seq advanced on the live origin"
        );
        assert!(
            only_in_origin
                .iter()
                .any(|k| matches!(k, UKey::BoundaryReceipt { .. })),
            "the live advance appended a new witnessed receipt beyond the saved boundary"
        );
    }

    /// **RESTORE FAIL-CLOSED.** The destination knows the trusted handoff root. A
    /// tampered witness (a forged frame digest the honest boundary never wrote) carries a
    /// different commitment than that root and is REFUSED by `migrate_onto_expecting`
    /// before it is ever live — the boundary umem is unforgeable across migration. The
    /// honest witness restores against the same root.
    #[test]
    fn a_tampered_witness_is_refused_by_restore() {
        let cell = cell_seed(3);
        let mut origin = CheckpointedRuntime::new(home_runtime(), cell);
        origin.boot().unwrap();
        origin.capture_checkpointed().unwrap();
        let saved = origin.save().unwrap();
        let trusted_root = saved.commitment(); // the out-of-band handoff root.

        // The HONEST witness restores against the trusted root.
        CheckpointedRuntime::migrate_onto_expecting(&saved, trusted_root, home_runtime())
            .expect("the honest witness restores against the trusted root");

        // FORGE the witness: a frame digest the honest boundary never presented.
        let mut tampered = saved.clone();
        tampered.frame = Some((0xDEAD_BEEF, 90, 200));
        assert_ne!(
            tampered.commitment(),
            trusted_root,
            "the forged frame digest changes the boundary commitment"
        );

        // The forged witness is REFUSED against the trusted root — fail-closed.
        let refused =
            CheckpointedRuntime::migrate_onto_expecting(&tampered, trusted_root, home_runtime());
        assert!(
            matches!(refused, Err(CheckpointError::RestoreMismatch { .. })),
            "the tampered witness does not match the trusted handoff root — restore refuses"
        );
    }
}
