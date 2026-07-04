//! The **reactive predicate** — the deos gate the Leptos view lights/darkens on.
//!
//! This is the load-bearing module of the prototype and the answer to MAPPING 1
//! (signals ↔ the Reactive rung): a deos cell's state is a Leptos signal, and an
//! affordance renders as a reactive view that lights iff `cap ∧ state` — the runtime
//! dual of the Lean `fireReactive` / `gatedOK` (the htmx tooth).
//!
//! THE DISCIPLINE: this module imports the GENUINE dregg gate, never a parallel one.
//! It depends ONLY on `dregg-cell` — the home of:
//!   * [`is_attenuation`] (`required ⊆ held`, the proven attenuation lattice — the
//!     SAME `cell/src/capability.rs:603` predicate the firmament runs for every
//!     capability),
//!   * [`AuthRequired`] (the real cap lattice),
//!   * [`CellState`] + [`CellProgram`] + [`StateConstraint`] (the real live-state gate
//!     — the SAME `CellProgram::evaluate` the executor runs every turn).
//!
//! Because `dregg-cell` is execution-engine-free (no `dregg-turn` / no Lean FFI), it
//! compiles to **both** the SSR (native) target AND the **WASM** client island. So the
//! reactive predicate that lights the button on the client is BYTE-FOR-BYTE the gate the
//! server's `EmbeddedExecutor` enforces — the convergence the deos thesis demands.
//!
//! The cap∧state conjunction here is the Rust twin of `Dregg2.Deos.GatedAffordance`'s
//! `gatedOK` (`metatheory/Dregg2/Deos/GatedAffordance.lean`); the WINDOW gate is the
//! twin of `Dregg2.Deos.Reactive`'s `inWindow` (`metatheory/Dregg2/Deos/Reactive.lean`).
//! We reuse the framework's own `GatedAffordance` for the server fire (mapping 3);
//! here we expose the *gate verdict* in a form the reactive view can compute every time
//! the signal changes — the runtime dual of those Lean predicates.

use dregg_cell::state::{CellState, FieldElement, STATE_SLOTS};
use dregg_cell::{is_attenuation, AuthRequired, CellProgram, StateConstraint};

/// Slot 0 of the proposal cell carries its `status` (the council exemplar's state machine).
pub const STATUS_SLOT: usize = 0;
/// Slot 1 carries the running `tally` (votes cast) — the reactive counter dimension.
pub const TALLY_SLOT: usize = 1;

/// `status` values.
pub const PENDING: u64 = 1;
pub const RESOLVED: u64 = 2;

/// A field element holding `n` big-endian in its last 8 bytes — exactly the encoding
/// the council exemplar (`app-framework/examples/deos_council_board.rs`) and the field's
/// `FieldEquals` atom read.
pub fn fe(n: u64) -> FieldElement {
    let mut b = [0u8; 32];
    b[24..32].copy_from_slice(&n.to_be_bytes());
    b
}

/// Read the `u64` packed into a field element's last 8 bytes.
pub fn fe_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// A plain, `Clone`/`PartialEq` snapshot of the load-bearing cell slots — the value a
/// Leptos signal carries (a `CellState` is large and not `PartialEq`-friendly to diff in
/// the reactive system, so the signal holds this projection; the gate still evaluates the
/// REAL `CellState`, reconstructed from these slots via [`CellSlots::to_cell_state`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CellSlots {
    /// slot 0 — the proposal status (PENDING / RESOLVED).
    pub status: u64,
    /// slot 1 — the running tally of votes.
    pub tally: u64,
    /// the executor turn height (the `EvalContext::height` the reactive WINDOW gates on).
    pub height: u64,
}

impl CellSlots {
    /// The seed state: a fresh PENDING proposal, zero tally, height 0.
    pub fn pending() -> Self {
        CellSlots {
            status: PENDING,
            tally: 0,
            height: 0,
        }
    }

    /// Project the load-bearing slots out of a REAL [`CellState`] (the read the
    /// server fn returns after a verified turn — so the signal re-seeds from the
    /// executor's own post-state).
    pub fn from_cell_state(s: &CellState) -> Self {
        let status = s.get_field(STATUS_SLOT).map(fe_u64).unwrap_or(0);
        let tally = s.get_field(TALLY_SLOT).map(fe_u64).unwrap_or(0);
        CellSlots {
            status,
            tally,
            height: 0,
        }
    }

    /// Reconstruct a REAL [`CellState`] from these slots — so the gate evaluates the
    /// GENUINE `CellProgram::evaluate` against a genuine `CellState`, never a mock.
    pub fn to_cell_state(&self) -> CellState {
        let mut st = CellState::new(0);
        st.set_field(STATUS_SLOT, fe(self.status));
        st.set_field(TALLY_SLOT, fe(self.tally));
        st
    }

    /// The slot state after a successful `vote` (tally += 1, still PENDING).
    pub fn after_vote(&self) -> Self {
        CellSlots {
            status: PENDING,
            tally: self.tally + 1,
            height: self.height,
        }
    }

    /// The slot state after a successful `resolve` (status := RESOLVED).
    pub fn after_resolve(&self) -> Self {
        CellSlots {
            status: RESOLVED,
            tally: self.tally,
            height: self.height,
        }
    }

    /// Whether the proposal is open (PENDING).
    pub fn is_pending(&self) -> bool {
        self.status == PENDING
    }
}

impl Default for CellSlots {
    fn default() -> Self {
        Self::pending()
    }
}

/// The `vote` affordance's live-state PRECONDITION as a REAL [`CellProgram`]: the
/// proposal must currently be PENDING (`slot[0] == PENDING`). The SAME predicate
/// language the executor enforces every turn — evaluated by the gate against the cell's
/// CURRENT state. (The Rust twin of the council exemplar's `pending_precondition`.)
pub fn pending_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: STATUS_SLOT as u8,
        value: fe(PENDING),
    }])
}

/// The viewer's identity, named by the authority they HOLD (the REAL `is_attenuation`
/// lattice). Three exemplar viewers, exactly as the council board:
///   * the COUNCILLOR holds `Either` (a signature OR a proof clears `vote`/`resolve`);
///   * the MEMBER holds only `Signature` (enough to `comment`, NOT to `vote`);
///   * the OUTSIDER holds an incomparable `Custom` identity (neither attenuates the
///     others — the structural no-peek that drives `membrane_two_viewers_distinct`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Viewer {
    /// A human label for the chrome.
    pub label: &'static str,
    /// The authority this viewer HOLDS — the left side of `is_attenuation(held, required)`.
    pub held: AuthRequired,
}

impl Viewer {
    pub fn councillor() -> Self {
        Viewer {
            label: "councillor",
            held: AuthRequired::Either,
        }
    }
    pub fn member() -> Self {
        Viewer {
            label: "member",
            held: AuthRequired::Signature,
        }
    }
    pub fn outsider() -> Self {
        Viewer {
            label: "outsider",
            held: AuthRequired::Custom {
                vk_hash: [0x9E; 32],
            },
        }
    }
    /// All three exemplar viewers (for the rehydration two-viewers panel).
    pub fn exemplars() -> Vec<Viewer> {
        vec![Self::councillor(), Self::member(), Self::outsider()]
    }
}

/// The **cap-gate** — `required ⊆ held` via the GENUINE [`dregg_cell::is_attenuation`].
/// This is THE gate, not a parallel role check: the same predicate `delegate.rs` runs to
/// admit a child surface and the membrane runs to compose a reshare.
pub fn cap_ok(held: &AuthRequired, required: &AuthRequired) -> bool {
    is_attenuation(held, required)
}

/// The **state-gate** — does the REAL [`CellProgram::evaluate`] admit firing in the
/// current slot state? The same evaluator the executor runs every turn. For a
/// precondition (no pending write yet) we gate on the current state as both `old` and
/// `new` — "may this button fire right now, in the state the cell is in" (exactly as the
/// framework's `DeosCell::project_gated_for` does).
pub fn state_ok(program: &CellProgram, slots: &CellSlots) -> bool {
    let st = slots.to_cell_state();
    program.evaluate(&st, Some(&st), None).is_ok()
}

/// The **window-gate** — `open ≤ height ≤ close` (the Rust twin of the Lean
/// `Reactive.inWindow`). The temporal dimension of reactivity: a `resolve` button that
/// only lights inside the `[open, close]` voting window.
pub fn in_window(height: u64, open: u64, close: u64) -> bool {
    open <= height && height <= close
}

/// **THE REACTIVE VERDICT** — the cap∧state(∧window) conjunction the Leptos button
/// computes EVERY time the cell signal changes. The runtime dual of the Lean
/// `GatedAffordance.gatedOK` / `Reactive.reactiveOK`: lit IFF the holder's authority
/// admits the cap AND the cell-program admits the state AND (if windowed) the height is
/// in range. Drop ANY conjunct and the button is dark.
///
/// This is the single function the whole prototype's reactivity rests on: the view calls
/// it inside a Leptos reactive closure over `(viewer, slots)`, so the button lights and
/// darkens as the signal moves — no manual DOM poke, the runtime tracks the dependency.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GateVerdict {
    pub cap: bool,
    pub state: bool,
    pub window: bool,
}

impl GateVerdict {
    /// All conjuncts pass — the button is LIT.
    pub fn lit(&self) -> bool {
        self.cap && self.state && self.window
    }

    /// A precise human reason for the FIRST failing tooth (the in-band refusal the
    /// chrome shows — the anti-ghost message, never a silent dark button).
    pub fn dark_reason(&self) -> Option<&'static str> {
        if !self.cap {
            Some("cap tooth: your held authority does not satisfy the required rights")
        } else if !self.state {
            Some("state tooth: the cell's live state forbids this fire right now")
        } else if !self.window {
            Some("window tooth: outside the [open, close] voting window")
        } else {
            None
        }
    }
}

/// Evaluate the cap∧state verdict (no window) for a gated affordance like `vote`/`approve`.
pub fn gated_verdict(
    held: &AuthRequired,
    required: &AuthRequired,
    program: &CellProgram,
    slots: &CellSlots,
) -> GateVerdict {
    GateVerdict {
        cap: cap_ok(held, required),
        state: state_ok(program, slots),
        window: true,
    }
}

/// Evaluate the cap∧state∧window verdict for a windowed reactive affordance like
/// `resolve` (the deadline tooth — twin of `Reactive.fireReactive_after_deadline_refuses`).
pub fn reactive_verdict(
    held: &AuthRequired,
    required: &AuthRequired,
    program: &CellProgram,
    slots: &CellSlots,
    open: u64,
    close: u64,
) -> GateVerdict {
    GateVerdict {
        cap: cap_ok(held, required),
        state: state_ok(program, slots),
        window: in_window(slots.height, open, close),
    }
}

/// A guard so the prototype notices if `STATE_SLOTS` ever shrinks below what we index.
const _: () = assert!(STATE_SLOTS > TALLY_SLOT);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cap_tooth_is_the_real_is_attenuation() {
        // councillor (Either) clears a Signature-or-Either requirement; member (Signature)
        // does NOT clear an Either requirement; outsider (Custom) is incomparable.
        assert!(cap_ok(&AuthRequired::Either, &AuthRequired::Either));
        assert!(!cap_ok(&AuthRequired::Signature, &AuthRequired::Either));
        assert!(!cap_ok(
            &AuthRequired::Custom {
                vk_hash: [0x9E; 32]
            },
            &AuthRequired::Either
        ));
        // and a Signature holder clears a Signature requirement (the `comment` baseline).
        assert!(cap_ok(&AuthRequired::Signature, &AuthRequired::Signature));
    }

    #[test]
    fn state_tooth_is_the_real_cellprogram() {
        let prog = pending_precondition();
        let pending = CellSlots::pending();
        let resolved = CellSlots {
            status: RESOLVED,
            tally: 3,
            height: 0,
        };
        // PENDING admits the fire; RESOLVED forbids it — the htmx tooth, evaluated by the
        // genuine CellProgram::evaluate.
        assert!(state_ok(&prog, &pending));
        assert!(!state_ok(&prog, &resolved));
    }

    #[test]
    fn gated_verdict_is_the_conjunction() {
        let prog = pending_precondition();
        let pending = CellSlots::pending();
        // councillor + PENDING ⇒ LIT.
        let v = gated_verdict(
            &AuthRequired::Either,
            &AuthRequired::Either,
            &prog,
            &pending,
        );
        assert!(v.lit());
        // member + PENDING ⇒ DARK on the cap tooth (right state, wrong caps).
        let v = gated_verdict(
            &AuthRequired::Signature,
            &AuthRequired::Either,
            &prog,
            &pending,
        );
        assert!(!v.lit() && v.dark_reason().unwrap().starts_with("cap tooth"));
        // councillor + RESOLVED ⇒ DARK on the state tooth (right caps, wrong state).
        let resolved = CellSlots {
            status: RESOLVED,
            tally: 1,
            height: 0,
        };
        let v = gated_verdict(
            &AuthRequired::Either,
            &AuthRequired::Either,
            &prog,
            &resolved,
        );
        assert!(!v.lit() && v.dark_reason().unwrap().starts_with("state tooth"));
    }

    #[test]
    fn window_tooth_closes_the_deadline() {
        let prog = pending_precondition();
        let mut pending = CellSlots::pending();
        pending.height = 5;
        // inside [0,10] ⇒ window passes; at height 11 ⇒ window tooth darkens.
        let v = reactive_verdict(
            &AuthRequired::Either,
            &AuthRequired::Either,
            &prog,
            &pending,
            0,
            10,
        );
        assert!(v.lit());
        pending.height = 11;
        let v = reactive_verdict(
            &AuthRequired::Either,
            &AuthRequired::Either,
            &prog,
            &pending,
            0,
            10,
        );
        assert!(!v.lit() && v.dark_reason().unwrap().starts_with("window tooth"));
    }

    #[test]
    fn slots_roundtrip_through_real_cellstate() {
        let s = CellSlots {
            status: RESOLVED,
            tally: 7,
            height: 0,
        };
        let cs = s.to_cell_state();
        let back = CellSlots::from_cell_state(&cs);
        assert_eq!(s.status, back.status);
        assert_eq!(s.tally, back.tally);
    }
}
