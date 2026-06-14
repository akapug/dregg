//! Cell affordances — **htmx on crack**, brought into the framework's own bones.
//!
//! `docs/deos/DEOS-APPS.md` (§"the deos app model") is the evolution plan: a
//! **deos app** is a set of **cells** exposing **affordances** (cap-gated
//! verified-turn templates) rendered as **web surfaces**. The standalone
//! `starbridge-web-surface` crate prototyped the *shape* (`affordance.rs`); this
//! module brings that shape INTO `dregg-app-framework`, built on the framework's
//! REAL primitives, and **closes the dispatch seam the standalone left open**:
//!
//! - The gate is the GENUINE [`dregg_cell::is_attenuation`] (`required ⊆ held`) —
//!   NOT a new gate, NOT a parallel role check, the SAME predicate the firmament
//!   runs for every capability.
//! - The effect-template is a real [`dregg_turn::Effect`] — the genuine turn the
//!   executor runs (a `SetField` for an edit, an `EmitEvent` for a comment, a
//!   `GrantCapability` for an admin grant).
//! - **Firing runs a REAL verified turn through the framework's
//!   [`EmbeddedExecutor`].** The standalone produced an `AffordanceIntent` and
//!   stopped (its named seam: "handing the intent to a live `TurnExecutor`"). HERE
//!   that seam is closed: [`AffordanceSurface::fire_through_executor`] hands the
//!   gated effect to [`EmbeddedExecutor::submit_turn`] and returns the executor's
//!   OWN [`dregg_turn::TurnReceipt`], chained on the per-agent receipt chain.
//!
//! ## The interaction model
//!
//! In htmx an element declares `hx-post="/x"` and the server returns a fragment.
//! In deos a **cell declares affordances** — named effect-templates — and an
//! interaction is a **verified turn**: the "button" is a cap-gated
//! [`dregg_turn::Effect`], and *who may press it* is decided by **held
//! capabilities** ([`AuthRequired`]), not a session cookie. Progressive
//! enhancement becomes progressive **attenuation**: an agent sees exactly the
//! affordances its caps authorize ([`AffordanceSurface::project_for`]).
//!
//! ## The pieces
//!
//! 1. [`CellAffordance`] — a named operation + the [`AuthRequired`] a viewer must
//!    HOLD + the real [`dregg_turn::Effect`] it would fire.
//! 2. [`AffordanceSurface`] — a cell's published set of affordances, with the
//!    per-viewer projection ([`AffordanceSurface::project_for`]) and the cap-gated
//!    fire ([`AffordanceSurface::fire`] / [`AffordanceSurface::fire_through_executor`]).
//! 3. [`AffordanceRegistry`] — the in-process registry apps populate through
//!    [`crate::starbridge::StarbridgeAppContext::register_affordance_surface`],
//!    alongside the existing factory/inspector registries.
//! 4. [`AffordanceSurface::descriptor`] — the anti-drift surface descriptor
//!    [`crate::webgen`] renders for the page (elements + required rights + the post
//!    endpoints), from the Rust source of truth.
//!
//! The HTTP fire endpoint ([`crate::affordance::router`]) uses the existing
//! `middleware`/`authorizer` proof/cap check, pointed at the affordance's
//! `required ⊆ held`.

use dregg_cell::{is_attenuation, AuthRequired};
use dregg_turn::action::Effect;
use dregg_types::CellId;

use crate::cipherclerk::{AppCipherclerk, EmbeddedExecutor, ExecutorSubmitError};

/// A single **cell affordance** — the htmx-on-crack element.
///
/// A `name` (the operation, the deos analogue of htmx's `hx-post` path), the
/// `required_rights` a viewer must HOLD to see/fire it ([`AuthRequired`]), and the
/// `effect_template` it would fire — a real [`dregg_turn::Effect`], the genuine
/// turn the executor would run.
///
/// The cap-gate is the load-bearing part and it is NOT new: a viewer may render or
/// fire this affordance iff [`CellAffordance::authorized_for`] — which is the
/// GENUINE [`dregg_cell::is_attenuation`] (`required ⊆ held`), the same gate the
/// firmament runs for every capability. No session cookie, no ambient role.
///
/// `Effect` does not derive `PartialEq` (it carries STARK proofs / eventual refs),
/// so this struct is identified by its `name` + `required_rights`; the
/// `effect_template` is compared structurally via the stable
/// [`CellAffordance::effect_summary`].
#[derive(Clone, Debug)]
pub struct CellAffordance {
    /// The operation name — the affordance's identity within its surface (the deos
    /// analogue of `hx-post="/comment"`). Unique per [`AffordanceSurface`].
    pub name: String,
    /// The authority a viewer must HOLD to see/fire this affordance. The gate is
    /// `is_attenuation(held, required)` = `required ⊆ held` — the viewer must hold
    /// AT LEAST this much authority. A `view` affordance requires a narrow right
    /// (any authenticated reader holds it); an `admin` affordance requires the
    /// broad root right (only a powerful holder clears it).
    pub required_rights: AuthRequired,
    /// The effect this affordance would FIRE — a real [`dregg_turn::Effect`], the
    /// genuine turn the executor runs. NOT a stub: firing the affordance yields
    /// exactly this effect, ready to hand to the [`EmbeddedExecutor`].
    pub effect_template: Effect,
}

impl CellAffordance {
    /// Declare an affordance named `name`, requiring `required_rights`, that fires
    /// `effect_template` (a real [`dregg_turn::Effect`]).
    pub fn new(
        name: impl Into<String>,
        required_rights: AuthRequired,
        effect_template: Effect,
    ) -> Self {
        CellAffordance {
            name: name.into(),
            required_rights,
            effect_template,
        }
    }

    /// Is this affordance authorized for a holder of `held` authority?
    ///
    /// THE cap-gate, and it is the REAL one: `is_attenuation(held, required)` =
    /// `required ⊆ held` (the proven attenuation lattice). True iff the holder's
    /// authority is at least as broad as this affordance demands. This is the same
    /// predicate the firmament runs to admit a child surface — NOT a parallel role
    /// check.
    pub fn authorized_for(&self, held: &AuthRequired) -> bool {
        is_attenuation(held, &self.required_rights)
    }

    /// A stable, `Eq`-able summary of the effect-template (its variant + the cells
    /// it touches), for diagnostics + tests where two templates must be compared
    /// (the `Effect` enum itself is not `PartialEq`). The summary names the REAL
    /// effect — a readout of the genuine template, not a substitute for it.
    pub fn effect_summary(&self) -> EffectSummary {
        EffectSummary::of(&self.effect_template)
    }
}

/// A stable, comparable readout of a [`dregg_turn::Effect`] template — its variant
/// tag + the principal cell(s) it acts on. (The `Effect` enum is not `PartialEq`
/// because some variants carry proofs / eventual refs; this is the
/// equality-friendly projection a test or a UI can compare.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EffectSummary {
    SetField { cell: CellId, index: usize },
    Transfer { from: CellId, to: CellId, amount: u64 },
    GrantCapability { from: CellId, to: CellId },
    RevokeCapability { cell: CellId, slot: u32 },
    EmitEvent { cell: CellId },
    IncrementNonce { cell: CellId },
    /// Any other real `Effect` variant, tagged by its name (still the genuine
    /// effect — only the *summary* is coarse).
    Other { tag: &'static str },
}

impl EffectSummary {
    /// Summarize a real [`Effect`] for comparison/diagnostics.
    pub fn of(effect: &Effect) -> EffectSummary {
        match effect {
            Effect::SetField { cell, index, .. } => EffectSummary::SetField {
                cell: *cell,
                index: *index,
            },
            Effect::Transfer { from, to, amount } => EffectSummary::Transfer {
                from: *from,
                to: *to,
                amount: *amount,
            },
            Effect::GrantCapability { from, to, .. } => EffectSummary::GrantCapability {
                from: *from,
                to: *to,
            },
            Effect::RevokeCapability { cell, slot } => EffectSummary::RevokeCapability {
                cell: *cell,
                slot: *slot,
            },
            Effect::EmitEvent { cell, .. } => EffectSummary::EmitEvent { cell: *cell },
            Effect::IncrementNonce { cell } => EffectSummary::IncrementNonce { cell: *cell },
            other => EffectSummary::Other {
                tag: effect_variant_tag(other),
            },
        }
    }

    /// The static variant tag of this summary (the effect kind name). Used by the
    /// surface descriptor so the page can label the button by its effect kind.
    pub fn variant_tag(&self) -> &'static str {
        match self {
            EffectSummary::SetField { .. } => "SetField",
            EffectSummary::Transfer { .. } => "Transfer",
            EffectSummary::GrantCapability { .. } => "GrantCapability",
            EffectSummary::RevokeCapability { .. } => "RevokeCapability",
            EffectSummary::EmitEvent { .. } => "EmitEvent",
            EffectSummary::IncrementNonce { .. } => "IncrementNonce",
            EffectSummary::Other { tag } => tag,
        }
    }
}

/// The static variant tag of a real [`Effect`] (used by [`EffectSummary::Other`]).
fn effect_variant_tag(effect: &Effect) -> &'static str {
    match effect {
        Effect::SetField { .. } => "SetField",
        Effect::Transfer { .. } => "Transfer",
        Effect::GrantCapability { .. } => "GrantCapability",
        Effect::RevokeCapability { .. } => "RevokeCapability",
        Effect::EmitEvent { .. } => "EmitEvent",
        Effect::IncrementNonce { .. } => "IncrementNonce",
        Effect::CreateCell { .. } => "CreateCell",
        Effect::SetPermissions { .. } => "SetPermissions",
        Effect::SetVerificationKey { .. } => "SetVerificationKey",
        // A catch-all so a HARDSWAP that ADDS an `Effect` variant still compiles
        // here. Any added variant is still the REAL effect.
        _ => "OtherEffect",
    }
}

/// A cell's published **affordance surface** — the set of affordances it exposes,
/// the deos analogue of a server's set of htmx endpoints.
///
/// This binds a `cell` (the surface's backing object) to its declared
/// `affordances`. Rendering it for a viewer is [`AffordanceSurface::project_for`]
/// (CAP-GATED); firing one is [`AffordanceSurface::fire`] (CAP-GATED, anti-ghost)
/// or [`AffordanceSurface::fire_through_executor`] (CAP-GATED + executed as a REAL
/// verified turn).
#[derive(Clone, Debug)]
pub struct AffordanceSurface {
    /// The cell backing this surface (the object whose affordances these are).
    pub cell: CellId,
    /// A human/diagnostic name for the surface (the deos analogue of a page
    /// title). Used in the [`SurfaceDescriptor`] banner; not load-bearing.
    pub name: String,
    /// The declared affordances. Names are unique (a [`AffordanceSurface::declare`]
    /// with a duplicate name replaces the prior one).
    pub affordances: Vec<CellAffordance>,
}

/// Why a [`AffordanceSurface::fire`] was refused (the gate verdict, before any
/// dispatch).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FireError {
    /// No affordance by that name on this surface.
    NoSuchAffordance,
    /// The actor's held caps do NOT satisfy the affordance's `required_rights` —
    /// the anti-ghost tooth: a viewer firing an affordance they lack the rights for
    /// is REFUSED by the REAL `is_attenuation`, never silently run.
    Unauthorized {
        /// The affordance the actor tried to fire.
        affordance: String,
        /// The authority it required (which the actor did not hold).
        required: AuthRequired,
        /// The authority the actor actually held.
        held: AuthRequired,
    },
}

impl std::fmt::Display for FireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FireError::NoSuchAffordance => write!(f, "no such affordance on this surface"),
            FireError::Unauthorized {
                affordance,
                required,
                held,
            } => write!(
                f,
                "unauthorized: firing `{affordance}` requires {required:?} but holder has {held:?}"
            ),
        }
    }
}

impl std::error::Error for FireError {}

/// Why a [`AffordanceSurface::fire_through_executor`] failed — either the gate
/// refused it ([`FireError`]) or the executor rejected the (authorized) turn.
#[derive(Clone, Debug)]
pub enum FireExecuteError {
    /// The cap gate refused the fire (the affordance was unauthorized / missing) —
    /// the turn was NEVER submitted. This is the anti-ghost path.
    Gate(FireError),
    /// The gate PASSED but the executor rejected the submitted turn (e.g. the
    /// surface cell was not present in the embedded ledger, or a program
    /// constraint bit). The effect WAS the real one; the executor declined it.
    Executor(ExecutorSubmitError),
}

impl std::fmt::Display for FireExecuteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FireExecuteError::Gate(e) => write!(f, "affordance fire refused by gate: {e}"),
            FireExecuteError::Executor(e) => write!(f, "affordance fire rejected by executor: {e}"),
        }
    }
}

impl std::error::Error for FireExecuteError {}

impl AffordanceSurface {
    /// A surface over `cell` with no affordances yet.
    pub fn new(cell: CellId) -> Self {
        AffordanceSurface {
            cell,
            name: String::new(),
            affordances: Vec::new(),
        }
    }

    /// A named surface over `cell` (the name is used in the descriptor banner).
    pub fn named(cell: CellId, name: impl Into<String>) -> Self {
        AffordanceSurface {
            cell,
            name: name.into(),
            affordances: Vec::new(),
        }
    }

    /// Declare (or replace, by name) an affordance on this surface. Builder-style.
    pub fn declare(mut self, affordance: CellAffordance) -> Self {
        self.affordances.retain(|a| a.name != affordance.name);
        self.affordances.push(affordance);
        self
    }

    /// All declared affordance names (sorted), regardless of viewer — the full
    /// surface, for diagnostics.
    pub fn all_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.affordances.iter().map(|a| a.name.clone()).collect();
        names.sort();
        names
    }

    /// Look up an affordance by name.
    pub fn get(&self, name: &str) -> Option<&CellAffordance> {
        self.affordances.iter().find(|a| a.name == name)
    }

    /// **The per-viewer affordance projection.** Return ONLY the affordances a
    /// holder of `held` authority is authorized to see/fire — progressive
    /// enhancement becomes progressive **attenuation**.
    ///
    /// Each affordance is admitted iff [`CellAffordance::authorized_for`] — the
    /// REAL `is_attenuation` (`required ⊆ held`). Two viewers holding different
    /// caps get DIFFERENT projections of the SAME surface. Declaration order is
    /// preserved, so the projection is a stable sub-list.
    pub fn project_for(&self, held: &AuthRequired) -> Vec<CellAffordance> {
        self.affordances
            .iter()
            .filter(|a| a.authorized_for(held))
            .cloned()
            .collect()
    }

    /// The names a viewer is authorized to see (sorted) — the per-viewer affordance
    /// set, the thing two different-cap viewers DIVERGE on.
    pub fn visible_names(&self, held: &AuthRequired) -> Vec<String> {
        let mut names: Vec<String> = self
            .project_for(held)
            .into_iter()
            .map(|a| a.name)
            .collect();
        names.sort();
        names
    }

    /// **Fire** the affordance named `name` as an actor holding `held` authority,
    /// from `actor` cell — producing the gated **verified-turn intent** (no
    /// dispatch yet).
    ///
    /// The gate is in-band and REAL: the fire is admitted iff the actor's `held`
    /// authority satisfies the affordance's `required_rights`
    /// ([`CellAffordance::authorized_for`] = `is_attenuation`). The **anti-ghost
    /// tooth**: an actor firing an affordance they lack the rights for is
    /// [`FireError::Unauthorized`] — REFUSED, never run.
    ///
    /// On success returns an [`AffordanceIntent`] carrying the REAL
    /// [`dregg_turn::Effect`] the executor would run. To actually EXECUTE it (the
    /// closed dispatch seam), use [`AffordanceSurface::fire_through_executor`].
    pub fn fire(
        &self,
        name: &str,
        actor: CellId,
        held: &AuthRequired,
    ) -> Result<AffordanceIntent, FireError> {
        let affordance = self.get(name).ok_or(FireError::NoSuchAffordance)?;
        if !affordance.authorized_for(held) {
            return Err(FireError::Unauthorized {
                affordance: name.to_string(),
                required: affordance.required_rights.clone(),
                held: held.clone(),
            });
        }
        Ok(AffordanceIntent {
            surface_cell: self.cell,
            affordance: affordance.name.clone(),
            actor,
            effect: affordance.effect_template.clone(),
        })
    }

    /// **Fire AND execute** the affordance named `name` — the closed dispatch seam.
    ///
    /// This is the piece the standalone `starbridge-web-surface` crate left as a
    /// named seam ("handing the intent to a live `TurnExecutor`"). HERE it is
    /// closed against the framework's OWN [`EmbeddedExecutor`]:
    ///
    /// 1. The cap gate runs FIRST ([`AffordanceSurface::fire`]) — an unauthorized
    ///    fire is [`FireExecuteError::Gate`] and the turn is NEVER submitted
    ///    (anti-ghost: confinement before execution).
    /// 2. The gated effect is wrapped in a signed [`dregg_turn::Turn`] through the
    ///    `cipherclerk` (a real `Authorization::Signature`, the action targeting the
    ///    affordance's surface cell + method = the affordance name) and submitted to
    ///    the `executor` via [`EmbeddedExecutor::submit_turn`].
    /// 3. The executor's OWN [`dregg_turn::TurnReceipt`] is returned — chained on
    ///    the agent's receipt chain. The receipt is the executor's, not a
    ///    self-reported stub.
    ///
    /// The `actor` of the intent is the `cipherclerk`'s cell (the principal of the
    /// turn). The effect carried IS the genuine one; whether it may fire AT ALL is
    /// decided in step 1 by the proven gate.
    pub fn fire_through_executor(
        &self,
        name: &str,
        held: &AuthRequired,
        cipherclerk: &AppCipherclerk,
        executor: &EmbeddedExecutor,
    ) -> Result<dregg_turn::TurnReceipt, FireExecuteError> {
        let actor = cipherclerk.cell_id();
        // Step 1: the REAL gate. An unauthorized fire is refused here; nothing is
        // ever submitted to the executor (anti-ghost).
        let intent = self
            .fire(name, actor, held)
            .map_err(FireExecuteError::Gate)?;
        // Step 2: the gated effect → a signed turn targeting the surface cell, with
        // the affordance name as the method (so the witness-graph records WHICH
        // affordance was fired). A real `Authorization::Signature` — no placeholder.
        let action = cipherclerk.make_action(
            self.cell,
            &intent.affordance,
            vec![intent.effect.clone()],
        );
        let turn = cipherclerk.make_turn(action);
        // Step 3: dispatch through the executor; return its OWN receipt.
        executor
            .submit_turn(&turn)
            .map_err(FireExecuteError::Executor)
    }

    /// The anti-drift **surface descriptor** the page renders — the elements (one
    /// per affordance), each with its required rights + effect kind + the post
    /// endpoint, derived from the Rust source of truth. See
    /// [`crate::webgen::ConstantsModule::affordance_surface`] for the JS emission.
    ///
    /// `route_prefix` is the path the [`router`] is mounted at (e.g.
    /// `"/doc-affordances"`); the fire endpoint for affordance `X` is then
    /// `POST {route_prefix}/fire/{X}`.
    pub fn descriptor(&self, route_prefix: &str) -> SurfaceDescriptor {
        let prefix = route_prefix.trim_end_matches('/');
        let elements = self
            .affordances
            .iter()
            .map(|a| AffordanceElement {
                name: a.name.clone(),
                required_rights: format!("{:?}", a.required_rights),
                effect_kind: a.effect_summary().variant_tag().to_string(),
                fire_endpoint: format!("{prefix}/fire/{}", a.name),
            })
            .collect();
        SurfaceDescriptor {
            surface: if self.name.is_empty() {
                format!("cell:{}", hex8(&self.cell))
            } else {
                self.name.clone()
            },
            cell_hex: hex_full(&self.cell),
            route_prefix: prefix.to_string(),
            projected_endpoint: format!("{prefix}/projected"),
            elements,
        }
    }
}

/// The **verified-turn intent** firing an authorized affordance produces — the
/// effect-template instantiated, ready for the executor.
///
/// This is that turn, before dispatch: the REAL [`dregg_turn::Effect`] the
/// affordance fires, the `actor` firing it, and the `surface_cell` it acts on. It
/// is ONLY ever minted by [`AffordanceSurface::fire`] AFTER the real
/// `is_attenuation` gate passed — so an intent's existence witnesses that the
/// actor was authorized.
#[derive(Clone, Debug)]
pub struct AffordanceIntent {
    /// The cell whose affordance was fired (the surface's backing cell).
    pub surface_cell: CellId,
    /// The affordance name that was fired.
    pub affordance: String,
    /// The actor cell that fired it (the principal of the turn).
    pub actor: CellId,
    /// The REAL effect the turn would run — the instantiated effect-template.
    pub effect: Effect,
}

impl AffordanceIntent {
    /// The `Eq`-able summary of the effect this intent would run (the `Effect` is
    /// not `PartialEq`). Names the REAL effect.
    pub fn effect_summary(&self) -> EffectSummary {
        EffectSummary::of(&self.effect)
    }
}

// =============================================================================
// SurfaceDescriptor — the anti-drift render payload
// =============================================================================

/// The page-facing **affordance surface descriptor** — the elements (one per
/// affordance), the per-viewer projection endpoint, and the fire endpoints —
/// derived from the Rust [`AffordanceSurface`] (the single source of truth).
///
/// Same anti-drift discipline as [`crate::webgen::ConstantsModule`]: the page
/// reads this (rather than hand-copying endpoint paths + required-rights labels),
/// so the JS surface cannot drift from the Rust affordance declarations. Rendered
/// to JS by [`crate::webgen::ConstantsModule::affordance_surface`].
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct SurfaceDescriptor {
    /// The surface's display name (or `cell:<hex8>` if unnamed).
    pub surface: String,
    /// The backing cell, full hex.
    pub cell_hex: String,
    /// The path the affordance router is mounted at.
    pub route_prefix: String,
    /// The per-viewer projection endpoint (`GET {prefix}/projected`).
    pub projected_endpoint: String,
    /// One element per declared affordance.
    pub elements: Vec<AffordanceElement>,
}

/// One element in a [`SurfaceDescriptor`] — the page's view of a single
/// affordance: its name, the rights a viewer must hold (a debug label of the real
/// [`AuthRequired`]), the effect kind it fires, and the POST endpoint that fires
/// it (cap-gated, verified-turn).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct AffordanceElement {
    /// The affordance name (the deos analogue of `hx-post="/comment"`).
    pub name: String,
    /// The `AuthRequired` a viewer must HOLD, as a stable debug label.
    pub required_rights: String,
    /// The effect kind this affordance fires (`SetField`, `EmitEvent`, …).
    pub effect_kind: String,
    /// The POST endpoint that fires it (`{prefix}/fire/{name}`), cap-gated.
    pub fire_endpoint: String,
}

// =============================================================================
// hex helpers (local — the crate's `hex` module is for full 32-byte round-trips)
// =============================================================================

fn hex_full(cell: &CellId) -> String {
    let mut s = String::with_capacity(64);
    for b in cell.as_bytes().iter() {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn hex8(cell: &CellId) -> String {
    let mut s = String::with_capacity(16);
    for b in cell.as_bytes().iter().take(8) {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_sdk::AgentCipherclerk;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    /// A real `SetField` effect (the genuine turn the executor runs for an edit).
    fn set_field(cell: CellId, index: usize) -> Effect {
        Effect::SetField {
            cell,
            index,
            value: [7u8; 32],
        }
    }

    /// A real `EmitEvent` effect (the genuine turn for a comment/log).
    fn emit_event(cell: CellId) -> Effect {
        Effect::EmitEvent {
            cell,
            event: dregg_turn::action::Event {
                topic: [1u8; 32],
                data: vec![],
            },
        }
    }

    /// A real `GrantCapability` effect (the genuine turn for an admin grant).
    fn grant_cap(from: CellId, to: CellId) -> Effect {
        Effect::GrantCapability {
            from,
            to,
            cap: dregg_cell::CapabilityRef {
                target: to,
                slot: 0,
                permissions: AuthRequired::Signature,
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
                stored_epoch: None,
            },
        }
    }

    /// The canonical four-affordance DOC-cell surface: {view, comment, edit, admin}
    /// on a clean three-tier rights chain `Signature ⊂ Either ⊂ None` — view at
    /// tier-1, comment+edit at tier-2, admin at tier-3. Each carries a REAL effect.
    fn doc_surface(doc: CellId) -> AffordanceSurface {
        AffordanceSurface::named(doc, "doc")
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature,
                emit_event(doc),
            ))
            .declare(CellAffordance::new(
                "comment",
                AuthRequired::Either,
                emit_event(doc),
            ))
            .declare(CellAffordance::new(
                "edit",
                AuthRequired::Either,
                set_field(doc, 1),
            ))
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::None,
                grant_cap(doc, cid(99)),
            ))
    }

    // viewer holds Signature; editor holds Either; admin holds None (root).
    const VIEWER: AuthRequired = AuthRequired::Signature;
    const EDITOR: AuthRequired = AuthRequired::Either;
    const ADMIN: AuthRequired = AuthRequired::None;

    // ── the gate is the REAL is_attenuation ──

    #[test]
    fn an_affordance_carries_a_real_effect_template() {
        let doc = cid(1);
        let edit = CellAffordance::new("edit", AuthRequired::Either, set_field(doc, 3));
        assert_eq!(
            edit.effect_summary(),
            EffectSummary::SetField { cell: doc, index: 3 }
        );
        assert!(matches!(edit.effect_template, Effect::SetField { .. }));
    }

    #[test]
    fn the_cap_gate_is_the_real_is_attenuation() {
        let doc = cid(1);
        let view = CellAffordance::new("view", AuthRequired::Signature, emit_event(doc));
        let admin = CellAffordance::new("admin", AuthRequired::None, grant_cap(doc, cid(99)));

        // The gate agrees with is_attenuation by construction, both polarities.
        assert!(view.authorized_for(&VIEWER));
        assert_eq!(
            view.authorized_for(&VIEWER),
            is_attenuation(&VIEWER, &AuthRequired::Signature)
        );
        assert!(!admin.authorized_for(&VIEWER));
        assert_eq!(
            admin.authorized_for(&VIEWER),
            is_attenuation(&VIEWER, &AuthRequired::None)
        );
        // The admin (root) holder clears the admin affordance.
        assert!(admin.authorized_for(&ADMIN));
    }

    // ── per-viewer projection — progressive attenuation ──

    #[test]
    fn two_viewers_with_different_caps_see_different_affordance_sets() {
        let doc = cid(2);
        let surface = doc_surface(doc);

        let viewer_set = surface.visible_names(&VIEWER);
        let editor_set = surface.visible_names(&EDITOR);
        let admin_set = surface.visible_names(&ADMIN);

        assert_eq!(viewer_set, vec!["view".to_string()]);
        assert_eq!(
            editor_set,
            vec!["comment".to_string(), "edit".to_string(), "view".to_string()]
        );
        assert_eq!(
            admin_set,
            vec![
                "admin".to_string(),
                "comment".to_string(),
                "edit".to_string(),
                "view".to_string()
            ]
        );

        // DIVERGENCE over the SAME surface; monotone in authority.
        assert_ne!(viewer_set, editor_set);
        assert_ne!(editor_set, admin_set);
        assert!(viewer_set.iter().all(|n| editor_set.contains(n)));
        assert!(editor_set.iter().all(|n| admin_set.contains(n)));
    }

    #[test]
    fn the_gate_refuses_a_viewer_who_holds_an_incomparable_right() {
        // A holder of `Proof` is INCOMPARABLE to `Either`/`Signature` (neither ⊆ the
        // other), so those affordances are refused — the gate is the real lattice,
        // not a numeric rank.
        let doc = cid(7);
        let surface = doc_surface(doc);
        let proof_held = AuthRequired::Proof;
        assert!(!surface.get("view").unwrap().authorized_for(&proof_held));
        assert!(!surface.get("comment").unwrap().authorized_for(&proof_held));
        assert!(surface.visible_names(&proof_held).is_empty());
    }

    // ── anti-ghost: firing an unauthorized affordance is REFUSED ──

    #[test]
    fn firing_an_authorized_affordance_yields_the_real_turn_intent() {
        let doc = cid(4);
        let surface = doc_surface(doc);
        let intent = surface
            .fire("view", cid(50), &VIEWER)
            .expect("an authorized fire yields an intent");
        assert_eq!(intent.actor, cid(50));
        assert_eq!(intent.surface_cell, doc);
        assert_eq!(intent.affordance, "view");
        assert_eq!(intent.effect_summary(), EffectSummary::EmitEvent { cell: doc });
        assert!(matches!(intent.effect, Effect::EmitEvent { .. }));
    }

    #[test]
    fn firing_an_unauthorized_affordance_is_refused_anti_ghost() {
        let doc = cid(5);
        let surface = doc_surface(doc);
        let refused = surface.fire("admin", cid(50), &VIEWER);
        assert_eq!(
            refused.unwrap_err(),
            FireError::Unauthorized {
                affordance: "admin".to_string(),
                required: AuthRequired::None,
                held: AuthRequired::Signature,
            }
        );
        // The editor ALSO cannot fire admin (lacks root).
        assert!(matches!(
            surface.fire("admin", cid(51), &EDITOR),
            Err(FireError::Unauthorized { .. })
        ));
        // But the admin (root) CAN — yielding the real GrantCapability turn.
        let admin_intent = surface
            .fire("admin", cid(52), &ADMIN)
            .expect("admin holder fires admin");
        assert_eq!(
            admin_intent.effect_summary(),
            EffectSummary::GrantCapability { from: doc, to: cid(99) }
        );
    }

    #[test]
    fn firing_a_missing_affordance_is_no_such_affordance() {
        let surface = doc_surface(cid(6));
        assert_eq!(
            surface.fire("nonexistent", cid(50), &ADMIN).unwrap_err(),
            FireError::NoSuchAffordance
        );
    }

    #[test]
    fn declare_replaces_by_name() {
        let doc = cid(91);
        let surface = AffordanceSurface::new(doc)
            .declare(CellAffordance::new("x", AuthRequired::None, emit_event(doc)))
            .declare(CellAffordance::new("x", AuthRequired::Signature, set_field(doc, 0)));
        assert_eq!(surface.affordances.len(), 1);
        assert_eq!(surface.get("x").unwrap().required_rights, AuthRequired::Signature);
        assert_eq!(
            surface.get("x").unwrap().effect_summary(),
            EffectSummary::SetField { cell: doc, index: 0 }
        );
    }

    // ── THE CLOSED DISPATCH SEAM: fire runs a REAL verified turn through the
    //    framework's EmbeddedExecutor; the receipt is the executor's own. ──

    #[test]
    fn fire_through_executor_runs_a_real_verified_turn_and_returns_the_executors_receipt() {
        // The agent fires `view` on ITS OWN cell (so the embedded ledger has the
        // surface cell — AgentRuntime seeds the agent's cell). The gate passes
        // (admin/root holder), the effect is the real EmitEvent, and the receipt is
        // the executor's OWN TurnReceipt (non-zero turn_hash, correct agent).
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [9u8; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        let surface = AffordanceSurface::named(cclerk.cell_id(), "self-doc").declare(
            CellAffordance::new("view", AuthRequired::None, emit_event(cclerk.cell_id())),
        );

        let receipt = surface
            .fire_through_executor("view", &ADMIN, &cclerk, &executor)
            .expect("an authorized fire executes a real turn");

        // The receipt is the EXECUTOR'S own — not a self-reported stub.
        assert_ne!(receipt.turn_hash, [0u8; 32], "turn_hash must be non-zero");
        assert_eq!(receipt.agent, cclerk.cell_id(), "receipt agent is the actor");
        assert_eq!(receipt.action_count, 1, "one action fired");
    }

    #[test]
    fn fire_through_executor_chains_receipts_across_two_fires() {
        // Two authorized fires advance the agent's receipt chain — proving the
        // executor's OWN chain is what backs the dispatch (not a per-call stub).
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [3u8; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        let surface = AffordanceSurface::new(cclerk.cell_id()).declare(CellAffordance::new(
            "bump",
            AuthRequired::None,
            emit_event(cclerk.cell_id()),
        ));

        let r1 = surface
            .fire_through_executor("bump", &ADMIN, &cclerk, &executor)
            .expect("first fire");
        let r2 = surface
            .fire_through_executor("bump", &ADMIN, &cclerk, &executor)
            .expect("second fire");

        assert_eq!(
            r2.previous_receipt_hash,
            Some(r1.receipt_hash()),
            "the second fire's receipt chains to the first (executor's own chain)"
        );
        assert_ne!(r1.turn_hash, r2.turn_hash, "distinct turns");
    }

    #[test]
    fn fire_through_executor_refuses_unauthorized_without_submitting_anti_ghost() {
        // THE anti-ghost tooth at the dispatch boundary: a viewer (Signature) firing
        // `admin` (req None) is refused by the gate — FireExecuteError::Gate — and
        // NOTHING is submitted to the executor. We prove the chain did NOT advance:
        // a subsequent AUTHORIZED fire is still the FIRST receipt in the chain.
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [5u8; 32]);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        let cell = cclerk.cell_id();
        let surface = AffordanceSurface::new(cell)
            .declare(CellAffordance::new("admin", AuthRequired::None, grant_cap(cell, cid(99))))
            .declare(CellAffordance::new("view", AuthRequired::None, emit_event(cell)));

        // Unauthorized fire: VIEWER (Signature) cannot fire admin (req None).
        let refused = surface.fire_through_executor("admin", &VIEWER, &cclerk, &executor);
        match refused {
            Err(FireExecuteError::Gate(FireError::Unauthorized { affordance, .. })) => {
                assert_eq!(affordance, "admin");
            }
            other => panic!("expected a Gate/Unauthorized refusal, got {other:?}"),
        }

        // The chain did NOT advance: the next AUTHORIZED fire is the chain's FIRST
        // receipt (previous_receipt_hash is None) — proving the refused fire never
        // touched the executor.
        let first = surface
            .fire_through_executor("view", &ADMIN, &cclerk, &executor)
            .expect("authorized fire executes");
        assert!(
            first.previous_receipt_hash.is_none(),
            "the refused fire must NOT have advanced the receipt chain"
        );
    }

    // ── the anti-drift descriptor (rendered by webgen) ──

    #[test]
    fn descriptor_names_every_affordance_with_rights_and_endpoint() {
        let doc = cid(8);
        let surface = doc_surface(doc);
        let desc = surface.descriptor("/doc-affordances");

        assert_eq!(desc.surface, "doc");
        assert_eq!(desc.route_prefix, "/doc-affordances");
        assert_eq!(desc.projected_endpoint, "/doc-affordances/projected");
        assert_eq!(desc.elements.len(), 4);

        let edit = desc.elements.iter().find(|e| e.name == "edit").unwrap();
        assert_eq!(edit.required_rights, "Either");
        assert_eq!(edit.effect_kind, "SetField");
        assert_eq!(edit.fire_endpoint, "/doc-affordances/fire/edit");

        let admin = desc.elements.iter().find(|e| e.name == "admin").unwrap();
        assert_eq!(admin.required_rights, "None");
        assert_eq!(admin.effect_kind, "GrantCapability");
        assert_eq!(admin.fire_endpoint, "/doc-affordances/fire/admin");
    }
}
