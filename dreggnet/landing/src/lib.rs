//! `dreggnet-landing` — the **public landing page**: the front door at the public
//! domain that tells a first-time visitor (and a hackathon judge) what DreggNet
//! Cloud IS, shows the LIVE status at a glance, and gives the three-step
//! quickstart.
//!
//! The cloud-provider readiness audit (`docs/CLOUD-PROVIDER-READINESS.md`) and
//! the web-portals census name the public faces the cloud needs. The
//! [`dreggnet-status`](../../status) page is "is the cloud up?"; the
//! [`dreggnet-console`](../../console) is the signed-in "my stuff"; this is the
//! **front door** that sits above both — the punchy, honest, judge-ready pitch +
//! the link into each.
//!
//! ## The shape (modelled on `dreggnet-ops` / `-status` / `-console`)
//! A pure-std HTTP server serving one self-contained page (no build step, no
//! external assets). The page is server-rendered HTML; a small
//! progressive-enhancement script fetches the public status page's `/status.json`
//! and paints the live banner. That fetch is the ONLY live coupling, and it is
//! honest: until it lands (or if it fails) the banner reads "checking…" — never
//! a false green.
//!
//! ## Honest scope
//! The page + render + tests are complete and green-standalone. The
//! **reviewed-go** half is the live-edge deploy: the Caddy route at the public
//! apex and the real public status URL ([`LandingConfig::status_url`]).

pub mod config;
pub mod render;

pub use config::LandingConfig;

/// Render the landing page for the given config (the one entry point the server
/// and the tests share).
pub fn landing_html(cfg: &LandingConfig) -> String {
    render::page_html(cfg)
}
