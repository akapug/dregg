//! # starbridge-web-surface — the embedded web surface + the `dregg://` web of cells
//!
//! Two designs, one substrate. Both build on the firmament's already-real
//! `Capability{ target: Surface(cell), rights }` handle and the real dregg
//! attenuation/attestation primitives — neither reinvents the cap model.
//!
//! ## 1. The embedded web surface ([`delegate`])
//!
//! `docs/EMBEDDED-WEB-SURFACE.md`: a web page is the canonical piece of
//! untrusted code that *wants ambient authority* — to fetch any origin, open any
//! window, read any permission. dregg's thesis is that there is **no ambient
//! authority**: every action is a held capability presented to a gate. libservo
//! surfaces every authority-bearing operation a `WebView` can perform as a
//! [`WebSurfaceDelegate`] callback (load_web_resource / allow_navigation /
//! request_open_auxiliary_webview / request_permission / authenticate), and **the
//! embedder's impl of that delegate IS the cap gate.** [`CapGatedDelegate`] is a
//! real such impl: each callback discharges the surface's held capability c-list,
//! so a fetch the cap does not permit is refused *at the callback*, before the
//! (mock) engine acts. An iframe / script-opened window is an **attenuation that
//! cannot amplify** — the no-amplification guarantee, applied to web content,
//! enforced by the REAL `dregg_cell::is_attenuation` (`granted ⊆ held`).
//!
//! ## 2. The `dregg://` web of cells ([`web_of_cells`])
//!
//! `docs/desktop-os-research/DISTRIBUTED-SERVO-FACETS.md` Facet 1: the open web's
//! link is a *location* (`https://host/path`) — you trust DNS to find the host,
//! TLS to authenticate the host, then trust whatever bytes the host returns. A
//! `dregg://<cell>` link is a *capability into a cell*: resolving it is a
//! **verified cross-cell read** that returns **attested content** — the bytes are
//! content-addressed AND carry a receipt + a quorum-signed
//! [`dregg_types::AttestedRoot`] the client checks, so you verify *the page is the
//! page the origin committed*, third-party-checkably, from any source. The
//! **trusted-path origin chrome is drawn from the LEDGER** (the cell's authority
//! lineage), never the fetched content — dregg's structural answer to
//! browser-chrome phishing.
//!
//! ## 3. Rehydratable surfaces ([`rehydrate`])
//!
//! `docs/desktop-os-research/REHYDRATABLE-SURFACES.md`: a dregg "screenshot" is the
//! present render-output of a certified compositor over a witness-graph; what it
//! actually embeds is a **sturdyref behind a membrane**; "opening" it is the
//! **membrane-negotiated, per-viewer reacquisition** of the witnessed state it was
//! always a certified projection of. This module ships the three load-bearing
//! pieces on the SAME real cap + attestation primitives:
//!
//! - the [`Rehydration`] liveness-type **DERIVED** from a context's
//!   witnessed-vs-ambient interaction log (a confinement readout, not a hand-set
//!   field): `ReplayedDeterministic` == "everything this context did went through
//!   the membrane";
//! - the [`Membrane`] enforcer — re-derives the per-viewer [`Projection`] = (held
//!   authority) ∧ (the graph's permitted projections) and **composes attenuation
//!   across reacquisition hops (A→B→C)** through the REAL `is_attenuation`, refusing
//!   any amplifying reshare;
//! - the [`Sturdyref`] + [`rehydrate`] — the persistable cap-handle and the
//!   membrane-negotiated reacquisition, with the fetch wired to the existing
//!   `dregg://` attested-fetch path (fetch = verified turn returning attested
//!   content).
//!
//! ## 4. Cell affordances — htmx on crack + the frustum-snapshot ([`affordance`])
//!
//! `docs/deos/DEOS.md`: the deos interaction model. A cell declares named, typed
//! **affordances** ([`CellAffordance`]) — effect-TEMPLATES, the analogue of htmx's
//! `hx-post="/x"` — and an interaction is a **capability-gated verified turn**: the
//! "button" is a real [`dregg_turn::Effect`], and *who may press it* is decided by
//! held caps through the SAME real `is_attenuation` gate. Rendering is the
//! per-viewer [`AffordanceSurface::project_for`] (progressive enhancement becomes
//! progressive **attenuation**); firing is the anti-ghost [`AffordanceSurface::fire`]
//! (an unauthorized fire is REFUSED in-band). The **frustum-snapshot**
//! ([`AffordanceSnapshot`]) is tiny — a [`Sturdyref`] + the culling boundary — and
//! [`rehydrate_affordances`] re-expands it PER-VIEWER through the EXISTING
//! [`Membrane`], carrying the derived [`Rehydration`] liveness-type: the
//! dregg-only novelty made real.
//!
//! ## 5. The fog-of-war webgame — fog IS the membrane ([`game`])
//!
//! `docs/deos/DEOS-APPS.md` §"the forcing function: a deos webgame": the deos
//! novelty *is a game mechanic made into a security property*. [`game`] is the
//! flagship exemplar — a hidden-information grid skirmish where **what a player can
//! SEE is exactly what its caps authorize it to rehydrate**, so a player *provably
//! cannot peek* at hidden enemy state. Fog of war stops being a client-side
//! honor-system and becomes a **confinement theorem**:
//!
//! - **Fog = the membrane's per-viewer projection** ([`Board::project_for`]). Vision
//!   rides the REAL cap lattice on two axes: a player's identity is a DISTINCT
//!   [`AuthRequired::Custom`]`{ vk_hash }` (two players' identities are
//!   *incomparable* — neither attenuates the other), and the vision frustum is the
//!   real fetch-allowlist of tiles its units illuminate. A tile gated to the enemy's
//!   identity is un-projectable by the genuine [`is_attenuation`] — the keystone
//!   [`game::Board::can_rehydrate_tile`] no-peek.
//! - **Moves = affordances** — each legal move is a [`CellAffordance`] firing a REAL
//!   [`Effect`]; an unauthorized move is a [`FireError`] (anti-cheat is free).
//! - **Agents-as-players** — [`AgentPlayer`] fires the SAME cap-gated affordances as
//!   a human; its action space IS its attenuated cap set.
//! - **Spectating** = a fog-respecting [`AffordanceSnapshot`] ([`Board::snapshot_for`])
//!   re-expanded through the SAME [`Membrane`].
//!
//! ## What is real vs. the seam
//!
//! - **Real (the cap discipline + attestation):** the `Capability{
//!   Surface(cell), rights }` handle, the five surface verbs against the real
//!   executor, `is_attenuation` (`granted ⊆ held`), the no-amplification gate,
//!   the `AttestedRoot` + receipt-stream Merkle verifier. All used directly. The
//!   fog-of-war game ([`game`]) drives its vision + moves through exactly these.
//! - **The LIBSERVO SEAM ([`delegate::MockSurface`]):** a real libservo `WebView`
//!   + a `WebViewDelegate` impl that forwards to [`CapGatedDelegate`] plugs in
//!   where `MockSurface` stands today. The seam is a single documented type and a
//!   single `// LIBSERVO SEAM` marker in [`delegate`]; the heavy libservo +
//!   Metal/wgpu toolchain is a frontier dep deliberately not linked here.
//! - **The full-turn seam ([`web_of_cells`]):** the fetch is modeled as a
//!   verified cell read against a real [`dregg_firmament::SurfaceBacking`] ledger
//!   with a receipt + attested root; wiring the serve as a full
//!   `Effect`-bearing executor turn (the `ServedResourceCell` template) is the
//!   named follow-up, reported in the BUILD STATUS note.

pub mod affordance;
pub mod delegate;
pub mod game;
pub mod rehydrate;
pub mod vision_predicate;
pub mod web_of_cells;

// Re-export the REAL dregg cap types so downstream code names the genuine model,
// not a parallel one. A web surface IS a firmament `Capability`; its rights are
// the real `AuthRequired` lattice; its identity is the real `CellId`.
pub use dregg_cell::{is_attenuation, AuthRequired};
pub use dregg_firmament::{Capability, SurfaceBacking, Target};
pub use dregg_types::{AttestedRoot, CellId};

pub use delegate::{
    CapGatedDelegate, MockSurface, NavigationDecision, PermissionDecision, PermissionKind,
    ResourceDecision, SurfaceCapability, WebSurfaceDelegate,
};
pub use web_of_cells::{
    AttestedResource, DreggUri, FetchError, OriginChrome, WebOfCells,
};
pub use rehydrate::{
    rehydrate, Interaction, InteractionLog, Membrane, Projection, Rehydration, RehydrateError,
    Sturdyref,
};
pub use affordance::{
    rehydrate_affordances, AffordanceIntent, AffordanceRehydrateError, AffordanceSnapshot,
    AffordanceSurface, CellAffordance, EffectSummary, FireError, SurfaceBoundary,
};
pub use game::{
    demo_skirmish, game_cell, side_rights, AgentPlayer, Board, Coord, IllegalMove, MoveOutcome,
    PlayerView, Side, TileView, Unit,
};
pub use vision_predicate::{
    register_vision_verifier, verify_vision_proof, FogVisionProducer, FogVisionVerifier,
    VisionKeypair, VisionProgram,
};
// Re-export the REAL turn `Effect` so downstream code (and the demo) names the
// genuine effect the executor runs as an affordance's template — not a parallel one.
pub use dregg_turn::Effect;

/// The genuine `dregg_turn` / `dregg_cell` payload types an affordance's effect-
/// template is built from — re-exported so an external consumer (the demo, an app)
/// can construct a REAL [`Effect`] without naming the (mid-HARDSWAP) upstream crates
/// directly. These are the genuine types, not parallel stubs: a `SetField` carries
/// a real `FieldElement` ([u8; 32]); an `EmitEvent` carries a real
/// [`dregg_turn::Event`]; a `GrantCapability` carries a real
/// [`dregg_cell::CapabilityRef`].
pub mod dregg_turn_reexport {
    pub use dregg_cell::CapabilityRef;
    pub use dregg_turn::Event;
}
