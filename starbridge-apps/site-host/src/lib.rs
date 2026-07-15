//! # starbridge-site-host — the WRITE control plane for verified microsite hosting.
//!
//! A hosted minisite is a cell: its content (path -> asset) carries a real
//! sorted-Poseidon2 [`content_root`](site::content_root) commitment — the same hash
//! family, heap-root function, and 8-felt faithful widening the kernel commits an
//! umem heap with — so a stranger re-witnesses the served bytes against the same
//! collision-resistant root the kernel understands. This crate is the missing WRITE
//! half: the cap-gated, lease-funded, receipted publish turn.
//!
//! ```text
//!   PUBLISH (this crate)                          SERVE (the read/metered plane)
//!   ─────────────────────────────────────        ─────────────────────────────
//!   POST /v1/sites/<name>/publish                 GET https://<name>.<apex>/
//!     1. cap-gate  site-host/<name>                 SiteRegistry::resolve
//!     2. fund      resident hosting lease           (agent-platform metered serve)
//!     3. publish   SiteRegistry::publish
//!        -> SiteCell + signed PublishReceipt
//! ```
//!
//! ## The three gates
//!
//! - **cap-gate** ([`publish`]) — the publish is authorized by a presented `dga1_`
//!   credential carrying the `site-host/<name>` capability, verified against the
//!   configured root ([`webauth_core`] / [`dregg_agent::cred`]). The verified
//!   subject becomes the published cell's owner; a cap for a different site, a
//!   foreign root, or none at all is refused (`401`/`403`).
//! - **funding-gate** ([`funding`]) — a publish is admitted only against a resident,
//!   non-lapsed [`hosted_lease::HostedLease`] covering the owner. No lease / a lapsed
//!   lease fails closed (`402`) — but the refusal carries an **x402-style topup hint**
//!   ([`funding::TopupHint`]) naming the lease, the rent asset, an amount, and the
//!   retry endpoint, so an agent client auto-funds and re-POSTs.
//! - **receipt** ([`registry`]) — a publish leaves a [`registry::PublishReceipt`];
//!   a [`signed`](registry::SiteRegistry::signed) registry seals it with an ed25519
//!   attestation over the binding fields, re-verifiable with no trust in the host
//!   ([`registry::verify_receipt`]).
//!
//! ## Composition
//!
//! - **launchpad** ([`launch`]) — a launch listing becomes a publishable landing
//!   page through the SAME control plane, its image + metadata content-addressed on
//!   IPFS ([`dregg_ipfs`]): a launch and its site share one turn.
//! - **the read plane** — the parameterized apex ([`registry::HostConfig`]) resolves
//!   `<name>.<apex>` to a published cell; the metered serving path is the resident
//!   `agent-platform` serve loop (not re-implemented here).
//!
//! ## The seam (honest)
//!
//! Real + tested here: the content model, the real Poseidon2 commitment, the
//! cap-gate, the lease-funding gate + x402 hint, the signed receipt, the IPFS-backed
//! launch page. The remaining seam — an on-chain `Effect::Write` committing the site
//! cell to a node and a light client witnessing that write in-circuit — is the
//! circuit epoch, deliberately not done here; the off-chain commitment is real today.

pub mod funding;
pub mod launch;
pub mod publish;
pub mod registry;
pub mod site;

pub use funding::{FundingDecision, LeaseBook, PublishFunding, TopupHint, TopupReason};
pub use launch::{LaunchAssets, LaunchImage, LaunchListing, LaunchMetadata, landing_page};
pub use publish::{HttpMethod, SitePublishHandler, WebResponse, bearer_credential};
pub use registry::{
    HostConfig, PUBLISH_CAP_PREFIX, PublishCap, PublishError, PublishReceipt, ReceiptAttestation,
    ServedAsset, SiteCell, SiteRegistry, verify_receipt,
};
pub use site::{Asset, SiteContent, content_root, is_valid_name};
