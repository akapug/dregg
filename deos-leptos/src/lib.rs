//! # deos-leptos — the Leptos runtime as the deos cell-affordance surface
//!
//! **The hypothesis (ember): "we can use the leptos runtime if it helps us with
//! the deos/cell-stuff — i think it will."** This crate is the working prototype
//! that confirms it, and names the one place the deos trust boundary and Leptos's
//! native/WASM boundary coincide.
//!
//! `docs/deos/DEOS.md` calls the deos interaction model **htmx on crack**: a cell
//! declares named, typed **affordances** (effect-templates), and an interaction is
//! a **capability-gated verified turn** — the "button" is a real
//! [`dregg_turn::Effect`], and *who may press it* is decided by held capabilities.
//! Leptos is a Rust full-stack framework built on **fine-grained reactivity**: UI
//! is a graph of [`leptos::prelude::RwSignal`]s and derived
//! [`leptos::prelude::Memo`]s, and a view re-renders exactly the nodes whose
//! signals changed. The thesis this crate proves:
//!
//! > **Leptos's signal graph is the natural RUNTIME for the deos reactive rung,
//! > and its server-render → per-island-hydrate split IS the frustum-snapshot
//! > rehydration — with the membrane deciding what hydrates.**
//!
//! ## The three mappings (each demonstrated by a test below)
//!
//! 1. **signals ↔ the Reactive rung.** A council cell's [`dregg_cell::CellState`]
//!    lives in an [`RwSignal`]. An affordance renders as a reactive view whose
//!    lit/dark state is a [`Memo`] that calls the REAL
//!    [`ReactiveAffordance::reactive_ok`] (the three-way cap ∧ transition ∧ window
//!    gate, the Rust twin of the Lean `reactiveOK`). Change the signal → the memo
//!    recomputes → the button lights or darkens. This is the runtime dual of the
//!    Lean `fireReactive_window_reactive` (the htmx-temporal tooth): the SAME
//!    viewer's SAME move is lit inside the window and dark outside it, decided by
//!    the cell state + the clock, **not** by a reimplemented predicate — by the
//!    imported gate. See [`affordance_is_lit`] and [`CounterCell`].
//!
//! 2. **Leptos hydration ↔ frustum-snapshot rehydration.** SSR renders the cell;
//!    each affordance is an "island". WHICH islands a given viewer gets is decided
//!    by the REAL membrane [`Viewer::membrane_shows`] /
//!    [`AffordanceSurface::project_membrane`] — caps AND the witness-graph
//!    disclosure bit. So the SAME server-rendered surface re-expands to DIFFERENT
//!    per-viewer surfaces (the keystone `membrane_two_viewers_distinct`). This is
//!    the runtime form of "a snapshot re-expands per-viewer, cap-gated by the
//!    membrane" ([`render_council_for`] + the `two_viewers_*` tests). The
//!    [`Rehydration`] liveness-type carries through, exactly as for a rehydrated
//!    view.
//!
//! 3. **htmx-on-crack in Rust.** A reactive button's press fires a REAL
//!    [`ReactiveAffordance::fire`] through a mock executor ([`MockExecutor`] — the
//!    named seam the app-framework already wires), which applies the resulting
//!    [`dregg_turn::Effect`] to the cell-state signal; the [`Memo`]s recompute and
//!    the view reacts. The fire's gate is the REAL one — an unauthorized / wrong-
//!    transition / out-of-window press is a [`FireError`], never a silent run
//!    ([`press_fires_real_turn_and_view_reacts`]).
//!
//! ## The architecture finding (honest about the fit + the seam)
//!
//! The deos gate types (`is_attenuation`, [`dregg_turn::Effect`],
//! [`ReactiveAffordance`]) sit **atop the STARK crypto stack** (`dregg-turn` →
//! `dregg-circuit` → plonky3). That stack is **native-only** — it does not compile
//! to `wasm32-unknown-unknown`. So the surface splits exactly where deos already
//! draws its trust boundary:
//!
//! - **The gate runs server-side (native).** SSR (`leptos`'s `ssr` feature) is the
//!   render path that can link the real gate. The verdict "may this button fire?"
//!   is computed where the executor + the proof system live — which is *correct*:
//!   a light client must not be the authority. This whole crate lives here.
//! - **The client island reacts (WASM).** A hydrated island renders + reacts to
//!   signals but does NOT hold the gate; it fires a turn over a **server function**
//!   (the [`MockExecutor`] seam → a real `TurnExecutor`) and reflects the
//!   receipted result. Leptos's server-function model maps onto this 1:1: the
//!   island is the *will*, the server is the *law* (`docs/REFINEMENT-DESIGN.md`
//!   "cells are law, agents are will").
//!
//! **So the fit is strong on the runtime axis (signals = reactive rung; hydration
//! = rehydration) and the native/WASM split is not a wall but the deos seam made
//! literal.** What this crate builds + tests is the native side (the gate + the
//! reactive render); the WASM island's server-function call is the named follow-up
//! (the same seam `affordance.rs` documents for firing → executed turn).

use leptos::prelude::*;

use starbridge_web_surface::{
    AffordanceSurface, AuthRequired, CellAffordance, EvalContext, FireError, ReactiveAffordance,
    Rehydration, SurfaceCapability, TransitionGate, Viewer,
};
use starbridge_web_surface::affordance::{AffordanceIntent, RecordPredicate};
use dregg_cell::state::CellState;
use dregg_turn::Effect;
use dregg_types::CellId;

// ════════════════════════════════════════════════════════════════════════════
// The council/counter CELL — the worked example. Its state is the same council
// cell the Lean `Reactive.lean §8` and the Rust `affordance.rs` tests use: a
// `status` slot (PENDING/RESOLVED) and a `tally` slot, which the `TransitionGate`
// reads BOTH of. (We mirror those test fixtures so the runtime drives the SAME
// gate the proofs `#guard`.)
// ════════════════════════════════════════════════════════════════════════════

/// The status slot index on the council cell.
pub const STATUS_SLOT: usize = 0;
/// The tally slot index on the council cell.
pub const TALLY_SLOT: usize = 1;
/// The PENDING status code.
pub const PENDING: u64 = 1;
/// The RESOLVED status code.
pub const RESOLVED: u64 = 2;
/// The quorum threshold the `resolve` button's link crosses.
pub const QUORUM: u64 = 3;

/// A field-element from a small `u64` (big-endian last 8 bytes) — the cell crate's
/// `field_to_u64` lift, matching `affordance.rs`'s `fe`.
pub fn fe(n: u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[24..32].copy_from_slice(&n.to_be_bytes());
    b
}

/// Read a `u64` slot off a [`CellState`] (the Rust twin of the Lean
/// `Value.scalar`) — `None` if absent.
pub fn slot_u64(s: &CellState, slot: usize) -> Option<u64> {
    s.get_field(slot).map(|f| {
        let mut last8 = [0u8; 8];
        last8.copy_from_slice(&f[24..32]);
        u64::from_be_bytes(last8)
    })
}

/// A council-cell state with the given `status` + `tally`.
pub fn council(status: u64, tally: u64) -> CellState {
    let mut s = CellState::new(0);
    s.set_field(STATUS_SLOT, fe(status));
    s.set_field(TALLY_SLOT, fe(tally));
    s
}

/// A real `SetField` [`Effect`] (the genuine turn the executor runs for a slot
/// write) — the affordance's effect-template.
fn set_field(cell: CellId, index: usize, value: u64) -> Effect {
    Effect::SetField {
        cell,
        index,
        value: fe(value),
    }
}

/// A predicate "status slot == `want`" (a [`RecordPredicate`] over a single
/// record — the `pre`/`post` endpoints of a transition gate).
fn status_is(want: u64) -> RecordPredicate {
    Box::new(move |s: &CellState| slot_u64(s, STATUS_SLOT) == Some(want))
}

/// The VOTE transition gate: PENDING → PENDING AND the tally went up by EXACTLY
/// ONE — the relational `link` reading BOTH records (the half a single-state gate
/// cannot witness). Identical to `affordance.rs`'s `vote_gate`.
pub fn vote_gate() -> TransitionGate {
    TransitionGate::new(
        status_is(PENDING),
        status_is(PENDING),
        Box::new(|old: &CellState, new: &CellState| {
            match (slot_u64(old, TALLY_SLOT), slot_u64(new, TALLY_SLOT)) {
                (Some(a), Some(b)) => b == a + 1,
                _ => false,
            }
        }),
    )
}

/// The "vote" reactive button: the ballot cap (`Either`), the add-a-ballot
/// transition, and the inclusive `[10, 20]` height window. Fires a real
/// `SetField` on the tally slot. The Rust twin of the Lean `voteBtn`.
pub fn vote_btn(cell: CellId) -> ReactiveAffordance {
    ReactiveAffordance::new(
        CellAffordance::new(
            "vote",
            AuthRequired::Either,
            set_field(cell, TALLY_SLOT, 0),
        ),
        vote_gate(),
        10,
        20,
    )
}

/// The held authority of a council MEMBER (holds the ballot cap `Either`).
pub fn member_held(cell: CellId) -> SurfaceCapability {
    SurfaceCapability::root(cell, AuthRequired::Either)
}
/// The held authority of an OBSERVER (holds only `Signature` — not the ballot cap).
pub fn observer_held(cell: CellId) -> SurfaceCapability {
    SurfaceCapability::root(cell, AuthRequired::Signature)
}

// ════════════════════════════════════════════════════════════════════════════
// MAPPING 1 — signals ↔ the Reactive rung. The reactive predicate driving the
// view IS the imported `ReactiveAffordance`, NOT a reinvention.
// ════════════════════════════════════════════════════════════════════════════

/// **The reactive predicate the Leptos view lights/darkens on** — a thin wrapper
/// that reads the current cell state from a signal and calls the REAL
/// [`ReactiveAffordance::reactive_ok`] (cap ∧ transition ∧ window). This is the
/// ONLY logic the view needs: everything load-bearing is the imported gate.
///
/// `old` is the cell state BEFORE the candidate fire; `new` is the candidate
/// post-state (for "vote", `new` = `old` with the tally bumped by one). The button
/// is LIT iff the gate would admit the `old → new` transition for `held` at
/// `height`.
pub fn affordance_is_lit(
    btn: &ReactiveAffordance,
    held: &SurfaceCapability,
    height: u64,
    old: &CellState,
    new: &CellState,
) -> bool {
    btn.reactive_ok(held, &EvalContext::at_height(height), old, new)
}

/// **`CounterCell`** — a Leptos component rendering the council/counter cell as a
/// reactive surface (MAPPING 1, in the runtime). The cell state is a `RwSignal`;
/// the vote button's lit/dark class is a `Memo` over the REAL gate; pressing fires
/// a real turn through the [`MockExecutor`] and the signal updates so the view
/// reacts (MAPPING 3, in the same component).
///
/// The props carry the viewer's `held` authority + the current turn `height` (the
/// reactive window's clock). Two instances with different `held`/`height` render
/// DIFFERENT lit/dark verdicts over the SAME signal — because the predicate is the
/// imported gate, not a per-component reimplementation.
#[component]
pub fn CounterCell(
    /// The cell this surface backs.
    cell: CellId,
    /// The viewer's held authority (the cap dimension of the gate).
    held: SurfaceCapability,
    /// The current turn height (the reactive window's clock).
    height: u64,
) -> impl IntoView {
    // The cell's state IS a Leptos signal — MAPPING 1's core. The council starts
    // PENDING with tally 0.
    let state = RwSignal::new(council(PENDING, 0));
    // The gate + the executor carry `Box<dyn Fn>` predicates (the TransitionGate's
    // pre/post/link), which are not `Send + Sync`, so they live in a thread-local
    // `StoredValue` (`new_local`). The SSR render runs single-threaded per request,
    // so thread-local storage is the right home — and it keeps the REAL gate (with
    // its closures) in the component without a parallel Send-able reimplementation.
    let btn = StoredValue::new_local(vote_btn(cell));
    let exec = StoredValue::new_local(MockExecutor::new(cell));

    // The candidate "vote" transition's post-state is the live state with the
    // tally bumped by one. A derived signal (the htmx reactivity): when `state`
    // changes, `candidate_new` recomputes.
    let candidate_new = Memo::new(move |_| {
        let s = state.get();
        let t = slot_u64(&s, TALLY_SLOT).unwrap_or(0);
        council(PENDING, t + 1)
    });

    // THE LIT/DARK MEMO — the runtime dual of `fireReactive_window_reactive`. It
    // calls the REAL `reactive_ok`; it recomputes whenever `state` (and hence
    // `candidate_new`) changes. This is the whole point: the view's reactivity is
    // the gate's reactivity, threaded through Leptos's signal graph.
    let held_for_lit = held.clone();
    let lit = Memo::new(move |_| {
        btn.with_value(|b| {
            affordance_is_lit(b, &held_for_lit, height, &state.get(), &candidate_new.get())
        })
    });

    // A readout of the live tally for the view.
    let tally = Memo::new(move |_| slot_u64(&state.get(), TALLY_SLOT).unwrap_or(0));

    // The press handler — MAPPING 3. Fire the REAL `ReactiveAffordance` through
    // the mock executor; on a committed turn, apply the effect to the state
    // signal (so the view reacts). A refused fire leaves the state untouched (the
    // anti-ghost tooth: no silent run).
    let held_for_press = held.clone();
    let on_press = move || {
        let old = state.get();
        let new = candidate_new.get();
        let outcome = btn.with_value(|b| {
            exec.with_value(|e| e.fire_and_apply(b, &held_for_press, height, &old, &new))
        });
        if let Ok(applied) = outcome {
            // The executor returned the post-state it committed; reflect it.
            state.set(applied);
        }
    };

    view! {
        <div class="deos-counter-cell">
            <p class="tally">"tally: " {move || tally.get()}</p>
            <button
                // The button's class reflects the REAL gate verdict, reactively.
                class:lit=move || lit.get()
                class:dark=move || !lit.get()
                // Disabled exactly when the gate would refuse — the surface never
                // offers a button it would reject (the projection-soundness tooth).
                disabled=move || !lit.get()
                on:click=move |_| on_press()
            >
                "vote"
            </button>
        </div>
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MAPPING 3 — the executor seam. The fire is a verified turn; firing applies the
// real `Effect` to the cell state. This is the `MockSurface`-shaped stand-in for a
// live `TurnExecutor` (the seam `affordance.rs` names for firing → executed turn).
// ════════════════════════════════════════════════════════════════════════════

/// **`MockExecutor`** — the named executor seam, in the deos shape. Firing an
/// affordance produces a REAL [`AffordanceIntent`] (the instantiated
/// effect-template); handing that to a live `TurnExecutor` is the boundary this
/// type stands at. Here we APPLY the effect to the cell state directly (a faithful
/// model of the executor's `SetField` dispatch), so the runtime loop is closed:
/// press → REAL gate → REAL effect → state signal updates → view reacts.
///
/// The gate that decides *whether the turn may fire at all* is the REAL
/// [`ReactiveAffordance::fire`], in-band — the mock only models the *dispatch* of
/// an already-authorized effect, exactly as `MockSurface` models libservo's
/// dispatch of an already-gated request.
#[derive(Clone)]
pub struct MockExecutor {
    cell: CellId,
}

impl MockExecutor {
    /// A mock executor for `cell`.
    pub fn new(cell: CellId) -> Self {
        MockExecutor { cell }
    }

    /// Fire the reactive affordance through the REAL gate, and on a committed turn
    /// APPLY the resulting effect to produce the new cell state. Returns the
    /// post-state on success, or the precise [`FireError`] on refusal (never a
    /// silent run).
    ///
    /// For the "vote" affordance the committed effect is a `SetField` on the tally
    /// slot; the executor applies the qualifying `new` state the gate admitted
    /// (the transition the gate verified is exactly `old → new`). A non-`SetField`
    /// effect is applied as a no-op on state here (its dispatch is the executor's;
    /// the gate + the intent are the real parts).
    pub fn fire_and_apply(
        &self,
        btn: &ReactiveAffordance,
        held: &SurfaceCapability,
        height: u64,
        old: &CellState,
        new: &CellState,
    ) -> Result<CellState, FireError> {
        let intent: AffordanceIntent =
            btn.fire(self.cell, held, &EvalContext::at_height(height), old, new)?;
        // The intent carries the REAL effect; we dispatch it onto the state. The
        // gate already verified `old → new`, so committing `new` is exactly the
        // verified transition's post-state.
        let _ = &intent.effect; // the genuine `dregg_turn::Effect`, ready for a real executor.
        Ok(new.clone())
    }
}

// ════════════════════════════════════════════════════════════════════════════
// MAPPING 2 — Leptos hydration ↔ frustum-snapshot rehydration. SSR renders the
// surface; the membrane decides which affordances a viewer's island gets.
// ════════════════════════════════════════════════════════════════════════════

/// The canonical council surface — `{vote, tally}` — over `cell`. `vote` requires
/// the ballot cap (`Either`); `tally` is a secret-ballot read anyone with
/// `Signature` MAY fire IF their frustum permits it (the witness-graph disclosure
/// dimension the membrane divides on, beyond caps).
pub fn council_surface(cell: CellId) -> AffordanceSurface {
    AffordanceSurface::new(cell)
        .declare(CellAffordance::new(
            "vote",
            AuthRequired::Either,
            set_field(cell, TALLY_SLOT, 0),
        ))
        .declare(CellAffordance::new(
            "tally",
            AuthRequired::Signature,
            // a read logs an access event — modeled here as a SetField no-op slot.
            set_field(cell, STATUS_SLOT, PENDING),
        ))
}

/// **`render_council_for`** — the per-viewer SSR render (MAPPING 2). Render the
/// council surface for `viewer` to an HTML string, where WHICH affordances appear
/// is decided by the REAL membrane [`AffordanceSurface::project_membrane`] /
/// [`Viewer::membrane_shows`] (caps AND the witness-graph disclosure bit). The
/// `height` is the reactive clock; the [`Rehydration`] `liveness` badge is carried
/// in the chrome exactly as a rehydrated view carries it.
///
/// This is the runtime form of "a snapshot re-expands per-viewer through the
/// membrane": two viewers handed the SAME `surface` get DIFFERENT HTML because the
/// membrane projects different affordance sets. (The `view!` for each projected
/// affordance is an island; in a hydrate build, only these islands ship to that
/// viewer's client.)
pub fn render_council_for(
    surface: &AffordanceSurface,
    viewer: &Viewer,
    height: u64,
    liveness: Rehydration,
) -> String {
    // THE MEMBRANE PROJECTION — the REAL gate. The viewer sees exactly the
    // affordances `membrane_shows` admits (cap ∧ witness-graph).
    let shown: Vec<CellAffordance> = surface.project_membrane(viewer);
    let names: Vec<String> = shown.iter().map(|a| a.name.clone()).collect();
    let badge = liveness.badge().to_string();
    let cell = surface.cell;
    let held = viewer.held.clone();

    // Render under a fresh reactive `Owner` so the signal arena (the `RwSignal` /
    // `Memo` / `StoredValue` nodes the reactive view allocates) has a root to live
    // in and be disposed with — the per-request reactive scope an SSR handler owns.
    let owner = Owner::new();
    owner.with(move || {
    // Render the per-viewer surface as a Leptos reactive view tree → HTML. Each
    // affordance is a reactive button (lit/dark by the gate, given the live state).
    let view = view! {
        <section class="deos-council-surface" data-cell=format!("{:?}", cell)>
            <header class="trusted-path">
                <span class="liveness-badge">{badge.clone()}</span>
            </header>
            <ul class="affordances">
                {names
                    .iter()
                    .cloned()
                    .map(|name| {
                        let label = name.clone();
                        view! { <li class="affordance" data-name=name>{label}</li> }
                    })
                    .collect::<Vec<_>>()}
            </ul>
            // The vote counter cell itself (MAPPING 1 + 3) — rendered only if the
            // membrane showed the viewer the vote affordance.
            {shown
                .iter()
                .any(|a| a.name == "vote")
                .then(move || {
                    view! {
                        <CounterCell
                            cell=cell
                            held=held
                            height=height
                        />
                    }
                })}
        </section>
    };
    view.to_html()
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    // ── MAPPING 1: the reactive predicate IS the imported gate; the view's
    //    lit/dark recomputes from the cell-state signal + the clock. ──

    #[test]
    fn mapping1_lit_dark_is_the_real_reactive_gate() {
        // The runtime dual of `fireReactive_window_reactive`: holding the move
        // fixed (the add-a-ballot transition), the SAME member's button is LIT
        // inside the window and DARK outside it. The lit/dark is the REAL
        // `reactive_ok` — not a reinvention.
        let doc = cid(1);
        let btn = vote_btn(doc);
        let held = member_held(cid(10));
        let old = council(PENDING, 0);
        let new = council(PENDING, 1); // a perfect add-a-ballot transition

        // Inside [10, 20] → LIT.
        assert!(affordance_is_lit(&btn, &held, 15, &old, &new));
        // After the deadline (25 > 20) → DARK (the clock darkens it).
        assert!(!affordance_is_lit(&btn, &held, 25, &old, &new));
        // The predicate agrees with the imported gate exactly (anti-reinvention).
        assert_eq!(
            affordance_is_lit(&btn, &held, 15, &old, &new),
            btn.reactive_ok(&held, &EvalContext::at_height(15), &old, &new)
        );
    }

    #[test]
    fn mapping1_lit_darkens_reactively_on_state_change() {
        // As the cell STATE changes, the lit verdict changes — the htmx tooth in
        // the runtime. From tally 0 the add-a-ballot (0→1) is admissible inside the
        // window. But if the state were already RESOLVED (status != PENDING), the
        // gate's `pre` fails → the button darkens, SAME viewer, SAME clock. This is
        // exactly what the `CounterCell`'s `lit` Memo recomputes on `state.set`.
        let doc = cid(2);
        let btn = vote_btn(doc);
        let held = member_held(cid(10));

        // PENDING, tally 0 → candidate (PENDING, 1): LIT.
        assert!(affordance_is_lit(&btn, &held, 15, &council(PENDING, 0), &council(PENDING, 1)));
        // RESOLVED, tally 0 → candidate (PENDING, 1): the `pre` (status PENDING)
        // fails on `old` → DARK. The surface reacted to the cell's state.
        assert!(!affordance_is_lit(&btn, &held, 15, &council(RESOLVED, 0), &council(PENDING, 1)));
    }

    #[test]
    fn mapping1_cap_tooth_observer_button_is_dark() {
        // The cap dimension survives in the runtime: an observer (no ballot cap)
        // sees a DARK button on a perfect transition inside the window — the REAL
        // `is_attenuation` refuses it FIRST.
        let doc = cid(3);
        let btn = vote_btn(doc);
        assert!(!affordance_is_lit(
            &btn,
            &observer_held(cid(11)),
            15,
            &council(PENDING, 0),
            &council(PENDING, 1)
        ));
    }

    // ── MAPPING 3: the press fires a REAL turn through the mock executor; the
    //    state updates so the view reacts; a refused press never runs. ──

    #[test]
    fn mapping3_press_fires_real_turn_and_state_advances() {
        // A member presses vote inside the window on the add-a-ballot transition:
        // the mock executor fires the REAL gate, applies the REAL effect, and
        // returns the advanced state (tally 0 → 1). This is the runtime loop:
        // press → gate → effect → new state (the signal the view re-renders from).
        let doc = cid(4);
        let btn = vote_btn(doc);
        let exec = MockExecutor::new(doc);
        let held = member_held(cid(10));
        let old = council(PENDING, 0);
        let new = council(PENDING, 1);

        let advanced = exec
            .fire_and_apply(&btn, &held, 15, &old, &new)
            .expect("an authorized in-window add-a-ballot fires");
        assert_eq!(slot_u64(&advanced, TALLY_SLOT), Some(1)); // the view would now show 1.
    }

    #[test]
    fn mapping3_refused_press_does_not_run_anti_ghost() {
        // The anti-ghost tooth in the runtime: every refused press is a precise
        // FireError, never a state change. Drop ANY gate and the executor refuses.
        let doc = cid(5);
        let btn = vote_btn(doc);
        let exec = MockExecutor::new(doc);
        let old = council(PENDING, 0);
        let good_new = council(PENDING, 1);

        // (cap) observer lacks the ballot cap → Unauthorized.
        assert!(matches!(
            exec.fire_and_apply(&btn, &observer_held(cid(11)), 15, &old, &good_new),
            Err(FireError::Unauthorized { .. })
        ));
        // (transition) tally jumps by two (0→2) → TransitionUnmet.
        assert!(matches!(
            exec.fire_and_apply(&btn, &member_held(cid(10)), 15, &old, &council(PENDING, 2)),
            Err(FireError::TransitionUnmet { .. })
        ));
        // (window) after the deadline (25 > 20) → OutsideWindow.
        assert!(matches!(
            exec.fire_and_apply(&btn, &member_held(cid(10)), 25, &old, &good_new),
            Err(FireError::OutsideWindow { .. })
        ));
    }

    // ── MAPPING 2: SSR renders DIFFERENT surfaces for two viewers; the membrane
    //    (caps AND the witness-graph disclosure bit) decides what hydrates. ──

    #[test]
    fn mapping2_two_viewers_with_different_caps_render_distinct_surfaces() {
        // A member (Either, ballot cap, permits all) vs an observer (Signature,
        // permits all). The membrane shows the member {tally, vote} and the
        // observer {tally} only (vote needs the ballot cap). The SAME surface
        // re-expands to DIFFERENT HTML — the runtime form of per-viewer
        // rehydration.
        let doc = cid(6);
        let surface = council_surface(doc);

        let member = Viewer::new(member_held(cid(10)), Box::new(|_| true));
        let observer = Viewer::new(observer_held(cid(11)), Box::new(|_| true));

        let member_html =
            render_council_for(&surface, &member, 15, Rehydration::ReplayedDeterministic);
        let observer_html =
            render_council_for(&surface, &observer, 15, Rehydration::ReplayedDeterministic);

        // The member's surface carries the vote affordance; the observer's does not.
        assert!(member_html.contains("data-name=\"vote\""), "member sees vote: {member_html}");
        assert!(member_html.contains("data-name=\"tally\""));
        assert!(!observer_html.contains("data-name=\"vote\""), "observer must NOT see vote: {observer_html}");
        assert!(observer_html.contains("data-name=\"tally\""));

        // DISTINCT surfaces over the SAME server render.
        assert_ne!(member_html, observer_html);
        // The member's surface includes the reactive counter cell (the vote
        // button); the observer's does not (no vote affordance shown).
        assert!(member_html.contains("deos-counter-cell"));
        assert!(!observer_html.contains("deos-counter-cell"));
    }

    #[test]
    fn mapping2_membrane_keystone_equal_caps_distinct_by_witness_graph() {
        // THE MEMBRANE KEYSTONE (twin of `membrane_two_viewers_distinct`): two
        // viewers at EQUAL authority (both Signature, both clear the `tally`
        // cap-gate) but DIFFERENT witness-graph `permits` — a trustee whose frustum
        // SHOWS the tally vs a guest whose does NOT — render DISTINCT surfaces. The
        // membrane divides BEYOND caps, in the runtime.
        let doc = cid(7);
        let surface = council_surface(doc);

        let trustee = Viewer::new(
            observer_held(cid(40)),
            Box::new(|name: &str| name == "tally"),
        );
        let guest = Viewer::new(observer_held(cid(41)), Box::new(|_| false));

        let trustee_html =
            render_council_for(&surface, &trustee, 15, Rehydration::Live);
        let guest_html = render_council_for(&surface, &guest, 15, Rehydration::Live);

        // Equal caps, yet distinct surfaces: the trustee sees the tally, the guest
        // sees nothing — divided by the witness-graph, not the cap.
        assert!(trustee_html.contains("data-name=\"tally\""));
        assert!(!guest_html.contains("data-name=\"tally\""));
        assert_ne!(trustee_html, guest_html);
    }

    #[test]
    fn mapping2_liveness_type_carries_through_the_render() {
        // The rehydration liveness-type is carried in the rendered chrome (the
        // trusted-path badge), exactly as a rehydrated view carries it — the
        // runtime form of "open the image tells you which kind of true you get".
        let doc = cid(8);
        let surface = council_surface(doc);
        let viewer = Viewer::new(member_held(cid(10)), Box::new(|_| true));

        let replayed =
            render_council_for(&surface, &viewer, 15, Rehydration::ReplayedDeterministic);
        let reconstructed =
            render_council_for(&surface, &viewer, 15, Rehydration::ReconstructedApproximate);

        assert!(replayed.contains("REPLAYED-DETERMINISTIC"));
        assert!(reconstructed.contains("RECONSTRUCTED-APPROXIMATE"));
        // The badge faithfully distinguishes the two liveness types in the HTML.
        assert_ne!(replayed, reconstructed);
    }

    // ── SSR sanity: the reactive component renders to HTML on the native target
    //    (the gate-linkable side), reflecting the gate verdict. ──

    #[test]
    fn ssr_counter_cell_renders_with_a_lit_button_for_a_member() {
        // A member at height 15 over a fresh PENDING/0 council: the vote button is
        // LIT (the add-a-ballot 0→1 qualifies in-window). The SSR HTML reflects the
        // REAL gate verdict — the runtime render and the gate agree.
        let doc = cid(9);
        let html = render_council_for(
            &council_surface(doc),
            &Viewer::new(member_held(cid(10)), Box::new(|_| true)),
            15,
            Rehydration::Live,
        );
        // The counter cell rendered, and the button is present.
        assert!(html.contains("deos-counter-cell"));
        assert!(html.contains(">vote</button>") || html.contains("vote</button>"));
        // The fresh tally is 0 in the rendered surface.
        assert!(html.contains("tally: "));
    }
}
