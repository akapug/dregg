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
//! ## What is real vs. the seam
//!
//! - **Real (the cap discipline + attestation):** the `Capability{
//!   Surface(cell), rights }` handle, the five surface verbs against the real
//!   executor, `is_attenuation` (`granted ⊆ held`), the no-amplification gate,
//!   the `AttestedRoot` + receipt-stream Merkle verifier. All used directly.
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

pub mod delegate;
pub mod web_of_cells;

// Re-export the REAL dregg cap types so downstream code names the genuine model,
// not a parallel one. A web surface IS a firmament `Capability`; its rights are
// the real `AuthRequired` lattice; its identity is the real `CellId`.
pub use dregg_cell::{is_attenuation, AuthRequired};
pub use dregg_firmament::{Capability, SurfaceBacking, Target};
pub use dregg_types::CellId;

pub use delegate::{
    CapGatedDelegate, MockSurface, NavigationDecision, PermissionDecision, PermissionKind,
    ResourceDecision, SurfaceCapability, WebSurfaceDelegate,
};
pub use web_of_cells::{
    AttestedResource, DreggUri, FetchError, OriginChrome, WebOfCells,
};
