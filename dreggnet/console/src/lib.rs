//! `dreggnet-console` — the signed-in **customer console**: the front door a real
//! user logs into to see and manage THEIR OWN stuff.
//!
//! The web-portals census (`docs/WEB-PORTALS-CENSUS.md`) named the biggest
//! product gap plainly: *"No unified console. There is no single authenticated
//! developer console that ties identity + machines + storage + hosting + billing
//! into one signed-in experience."* This crate is that surface.
//!
//! ```text
//!   webauth dga1_ forward-auth ──▶ X-Dregg-Subject (the cap holder = the OWNER)
//!                                          │
//!   sites · servers · agents · domains ·   ▼
//!   storage · $DREGG  (the resource    dreggnet-console
//!   surfaces, each recording its       (cap-SCOPE to the subject)
//!   owner = that subject) ──────────▶  one signed-in "my stuff" page
//!                                       + in-page verify-don't-trust
//! ```
//!
//! ## The shape (modelled on `dreggnet-ops`)
//!
//! Like the ops dashboard it is a pure-std HTTP server that **aggregates** the
//! live read surfaces — it does not re-implement any service. The one thing it
//! adds that ops does not is **cap-scoping**: ops shows the operator the whole
//! cloud; the console shows a customer ONLY their own cells. The authority is the
//! webauth `dga1_` forward-auth: the credential's stable subject
//! ([`dreggnet_webauth::subject_of`], `dregg:<16 hex>`) is the cap holder, and
//! every resource surface already records its `owner`/`lessee` as that subject.
//!
//! - [`model`] — the per-resource VIEW types + the [`model::Owned`] trait.
//! - [`scope`] — **the cap-scoping teeth**: filter the cloud-wide [`scope::Catalog`]
//!   to exactly the authenticated subject ([`model::ConsoleView::for_subject`]).
//! - [`source`] — where the catalog comes from ([`source::FixtureSource`] now;
//!   the live HTTP aggregation behind the webauth edge is the reviewed-go swap).
//! - [`verify`] — verify-anything: re-witness an agent run / deploy in-page (the
//!   real `dreggnet_exec::agent` chain + bound + QA re-witness).
//! - [`render`] — server-render the scoped view into one self-contained page.
//! - [`config`] — runtime config (bind, the cap gate, the login base).
//!
//! ## Honest scope
//! This is the **safe-autonomous** half: the console + the read aggregation
//! shape + the cap-scoping + the in-page verify + tests, green-standalone over
//! deterministic fixtures. The **reviewed-go** half is the live-edge deploy — a
//! `LiveSource` aggregating the real surfaces behind the production webauth
//! forward-auth (see [`source`]).

pub mod client;
pub mod config;
pub mod fixtures;
pub mod model;
pub mod render;
pub mod scope;
pub mod source;
pub mod verify;

pub use config::ConsoleConfig;
pub use model::ConsoleView;
pub use scope::Catalog;

/// The current time as RFC3339 (the view's `generated_at`), or a fallback.
pub fn now_rfc3339() -> String {
    time::OffsetDateTime::now_utc()
        .format(&time::format_description::well_known::Rfc3339)
        .unwrap_or_else(|_| "unknown".to_string())
}
