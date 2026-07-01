//! `hosting` — static minisite hosting on the verified rail: **a site is a dregg cell.**
//!
//! Where [`crate::router`] serves an agent's *dynamic* API (routes → the owned sandbox
//! handlers), this module serves *static* web content — a minisite (HTML/CSS/JS,
//! images, a whole `index.html` + assets) — backed by a dregg cell. The headline
//! shape DreggNet exposes on `dregg.works`:
//!
//! ```text
//!   PUBLISH (a cap-gated, receipted turn)        SERVE (read-only, public)
//!   ─────────────────────────────────────        ─────────────────────────
//!   PublishCap  site-host/<name>                  GET  https://<name>.dregg.works/
//!     └─ SiteRegistry::publish ─▶ SiteCell          └─ SiteRegistry::resolve
//!          { name, owner, content_root,                  │ host → <name>
//!            content: path → Asset }                     │ path → Asset
//!          + PublishReceipt (who published what)         ▼
//!                                                      WebResponse (bytes + content-type)
//! ```
//!
//! ## A site is a cell (the model)
//!
//! A hosted minisite is a [`SiteCell`]: a dregg cell whose committed state holds
//! the site's **route name** (the `<name>` subdomain label), its **owner** (the
//! publishing cell/agent — so *who published what* is provable), a **content
//! commitment** ([`SiteCell::content_root`]), and the **content** itself
//! ([`SiteContent`], a path → [`Asset`] map). Publishing is a *turn* that writes
//! the content cell, gated by the owner's [`PublishCap`] and leaving a
//! [`PublishReceipt`] — so hosting rides the same verified rail as everything else
//! on dregg: the publish is authorized (cap-attenuation) and receipted, not a bare
//! server write.
//!
//! ## Real vs the on-chain write (honest)
//!
//! - **Real here:** the cell model, the cap-gate (a `site-host/<name>` cap only
//!   authorizes publishing the site named `<name>` for its holder — attenuation),
//!   the deterministic content commitment ([`content_root`]), the receipt, the
//!   host→site resolver, and read-only static serving with correct content-types.
//!   `SiteRegistry` is an in-process registry of published cells — the data plane
//!   the gateway resolves against.
//! - **The on-chain write (the named seam):** committing the [`SiteCell`]
//!   to a dregg node — the publish turn as a real `Effect::Write` to the content
//!   cell, cap-gated by the `site-host/<name>` capability and witnessed as a dregg
//!   receipt — lands on the same surface `dreggnet-bridge`'s `dregg_verify` module
//!   names (`witness_receipt` / `query_shadow_attest_whole_log`). The
//!   [`content_root`] computed here is the cell's REAL sorted-Poseidon2 umem heap
//!   root (no stand-in); what remains the circuit swarm's VK-epoch is a LIGHT CLIENT
//!   witnessing that `Effect::Write` IN-CIRCUIT — the OFF-chain commitment is real
//!   and re-witnessable today; the in-circuit witness of the write is its shadow.
//!
//! ## Trustless serving (the docuverse tie-in)
//!
//! Because a site IS a cell with a committed [`content_root`], a visitor can be
//! served the **trustless** variant: the cell's content wrapped so the browser
//! re-witnesses that the bytes match the committed cell state (per-asset openings
//! against the heap root), exactly the projection
//! `deos-view::render_trustless_cell_document` performs for any dregg cell. That
//! renderer lives in the breadstuffs `deos-view` workspace (AGPL, separate); this
//! module carries the [`content_root`] commitment it needs and documents the seam
//! ([`SiteCell::content_root`]). The plain serving here is the public read path; the
//! trustless wrap is the verify-in-tab upgrade over the same cell.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use dreggnet_receipt::{BodyHasher, ReceiptAttestation, ReceiptBody, ReceiptChain};
use dreggnet_umem::{Record, UmemRegistry};
use serde::{Deserialize, Serialize};

use crate::http::{WebRequest, WebResponse};

/// The cap-token prefix a publish capability carries: `site-host/<name>`. A holder
/// of `site-host/blog` may publish (only) the site named `blog`. This mirrors a
/// dregg cap token whose caveats bind the authorized site name — the publish turn's
/// attenuation, the same shape `dreggnet-bridge`'s `exec-lease/<…>` lease cap uses.
pub const PUBLISH_CAP_PREFIX: &str = "site-host/";

/// One static asset within a site: the served bytes + the `Content-Type` to send.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Asset {
    /// The `Content-Type` header value for this asset.
    pub content_type: String,
    /// The asset bytes (HTML/CSS/JS/image/…).
    pub body: Vec<u8>,
}

impl Asset {
    /// An asset with an explicit content-type.
    pub fn new(content_type: impl Into<String>, body: impl Into<Vec<u8>>) -> Asset {
        Asset {
            content_type: content_type.into(),
            body: body.into(),
        }
    }

    /// An asset whose content-type is inferred from `path`'s extension
    /// ([`content_type_for`]).
    pub fn at(path: &str, body: impl Into<Vec<u8>>) -> Asset {
        Asset {
            content_type: content_type_for(path).to_string(),
            body: body.into(),
        }
    }
}

/// The content of a hosted minisite: request-path → [`Asset`].
///
/// Keys are absolute request paths (e.g. `/`, `/index.html`, `/style.css`,
/// `/img/logo.png`). [`SiteContent::resolve`] applies the standard static-host
/// path conventions (a directory request serves its `index.html`).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SiteContent {
    /// path → asset. A `BTreeMap` so the content (and thus its [`content_root`])
    /// is canonically ordered.
    pub assets: BTreeMap<String, Asset>,
}

impl SiteContent {
    /// Empty content.
    pub fn new() -> SiteContent {
        SiteContent {
            assets: BTreeMap::new(),
        }
    }

    /// Add an asset at `path`, content-type inferred from the extension.
    pub fn with(mut self, path: impl Into<String>, body: impl Into<Vec<u8>>) -> SiteContent {
        let path = path.into();
        let asset = Asset::at(&path, body);
        self.assets.insert(normalize_key(&path), asset);
        self
    }

    /// Add an asset at `path` with an explicit content-type.
    pub fn with_typed(
        mut self,
        path: impl Into<String>,
        content_type: impl Into<String>,
        body: impl Into<Vec<u8>>,
    ) -> SiteContent {
        let path = path.into();
        self.assets
            .insert(normalize_key(&path), Asset::new(content_type, body));
        self
    }

    /// Whether the site has no assets (an empty site can't be published).
    pub fn is_empty(&self) -> bool {
        self.assets.is_empty()
    }

    /// Number of assets.
    pub fn len(&self) -> usize {
        self.assets.len()
    }

    /// Resolve a request `path` to an asset, applying static-host conventions:
    /// `/` (or empty) → `/index.html`; a trailing-slash directory → its
    /// `index.html`; an extension-less path that misses → `<path>/index.html`.
    pub fn resolve(&self, path: &str) -> Option<&Asset> {
        let key = normalize_key(path);
        if let Some(a) = self.assets.get(&key) {
            return Some(a);
        }
        // A directory-style request without a trailing slash: try its index.
        if !key.ends_with('/') && !key.ends_with(".html") {
            let dir_index = format!("{key}/index.html");
            if let Some(a) = self.assets.get(&dir_index) {
                return Some(a);
            }
        }
        None
    }
}

/// A **site cell** — the dregg cell backing a hosted minisite.
///
/// The committed state of a hosting cell: the route name (the `<name>` subdomain
/// label), the owner (the publishing cell/agent), the content commitment, and the
/// content. On a real dregg node this is a cap-bounded cell whose umem heap holds
/// these fields; here it is the in-process value the [`SiteRegistry`] serves and
/// the publish turn writes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SiteCell {
    /// The route name — the subdomain label served at `<name>.dregg.works`.
    pub name: String,
    /// The owner cell/agent that published this site (the cap holder). Provable:
    /// the publish receipt binds `(name, owner, content_root)`.
    pub owner: String,
    /// A deterministic commitment to [`SiteCell::content`] ([`content_root`]).
    ///
    /// This is the cell's REAL sorted-Poseidon2 heap root — the same commitment a
    /// dregg light client / the kernel understands (see [`content_root`]), the wide
    /// 8-felt (~124-bit) faithful root pinned by `root_binds_get`, on every build.
    /// It is the anchor the **trustless** projection
    /// (`deos-view::render_trustless_cell_document`) opens each served asset against,
    /// so a visitor can re-witness in-tab that the bytes match the committed cell.
    pub content_root: String,
    /// The site content (path → asset, or a manifest of CAS pointers in a richer
    /// rung; here the bytes are carried inline).
    pub content: SiteContent,
}

impl SiteCell {
    /// Assemble a site cell from its parts, computing the [`content_root`].
    pub fn new(
        name: impl Into<String>,
        owner: impl Into<String>,
        content: SiteContent,
    ) -> SiteCell {
        let content_root = content_root(&content);
        SiteCell {
            name: name.into(),
            owner: owner.into(),
            content_root,
            content,
        }
    }

    /// Serve a request against this cell's content (read-only, public). A resolved
    /// asset is a `200` with its content-type; a miss is a `404`.
    pub fn serve(&self, req: &WebRequest) -> WebResponse {
        match self.content.resolve(&req.path) {
            Some(asset) => WebResponse {
                status: 200,
                content_type: asset.content_type.clone(),
                body: asset.body.clone(),
            },
            // HB-2: bound the reflected path — the miss body echoes the
            // attacker-controlled request path, so cap it to a fixed length to deny a
            // large-path amplification (a huge `GET /<…>` cannot inflate the 404 body).
            None => WebResponse::error(
                404,
                format!(
                    "no asset `{}` in site `{}`",
                    bounded_reflect(&req.path),
                    self.name
                ),
            ),
        }
    }
}

/// A published [`SiteCell`] is a durable record keyed by its site name — the unit
/// the [`SiteRegistry`]'s durable backend ([`UmemRegistry`]) lays into the registry
/// cell's umem heap, so a restart reconstructs the published sites FROM the committed
/// heap (the data-plane durability blocker, now on the real substrate).
impl Record for SiteCell {
    fn store_key(&self) -> String {
        self.name.clone()
    }
}

/// Cap an echoed, attacker-controlled string to a fixed length (with an ellipsis) so a
/// reflected error body cannot be inflated by a long request path (HB-2). 80 bytes is
/// ample to identify the miss without becoming an amplification vector.
fn bounded_reflect(s: &str) -> String {
    const MAX: usize = 80;
    if s.len() <= MAX {
        return s.to_string();
    }
    let mut cut = MAX;
    while cut > 0 && !s.is_char_boundary(cut) {
        cut -= 1;
    }
    format!("{}…", &s[..cut])
}

/// A capability authorizing a publish: a holder of a `site-host/<name>` cap may
/// publish the site named `<name>`. The capability is bound to BOTH the holder and
/// the site name — so it cannot be exercised to publish a different site, the
/// publish turn's cap-attenuation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublishCap {
    /// The cap holder (becomes the published cell's `owner`).
    pub holder: String,
    /// The cap token: `site-host/<name>`.
    pub cap: String,
}

impl PublishCap {
    /// A publish cap for `holder` over the site named `name` (`site-host/<name>`).
    pub fn for_site(holder: impl Into<String>, name: &str) -> PublishCap {
        PublishCap {
            holder: holder.into(),
            cap: format!("{PUBLISH_CAP_PREFIX}{name}"),
        }
    }

    /// The site name this cap authorizes, if it is a well-formed `site-host/<name>`
    /// token (a non-empty name).
    pub fn site(&self) -> Option<&str> {
        self.cap
            .strip_prefix(PUBLISH_CAP_PREFIX)
            .filter(|n| !n.is_empty())
    }

    /// Whether this cap authorizes publishing the site `name` (the cap token must
    /// name exactly `name`).
    pub fn authorizes(&self, name: &str) -> bool {
        self.site() == Some(name)
    }
}

/// The verifiable record a publish leaves: who published which site, at what
/// content commitment. The dregg analog is the publish turn's receipt — this is
/// the in-process projection (the on-chain `Effect::Write` witness is the named seam).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublishReceipt {
    /// The registry-monotonic sequence of this publish (publish order).
    pub seq: u64,
    /// The site name published.
    pub name: String,
    /// The owner (the cap holder) that published it.
    pub owner: String,
    /// The content commitment the published cell carries.
    pub content_root: String,
    /// How many assets the published site holds.
    pub asset_count: usize,
    /// The chained, signed attestation that lifts this publish into the receipt
    /// contract (prev-hash link + ed25519 signature). Present when the
    /// [`SiteRegistry`] was given a receipt chain ([`SiteRegistry::signed`]);
    /// `None` for the unsigned free/local default (a bare projection). A
    /// publish IS a turn, so this is the turn receipt; a `DeployReceipt` is a
    /// typed VIEW that carries this receipt's hash.
    #[serde(default)]
    pub attest: Option<ReceiptAttestation>,
}

impl ReceiptBody for PublishReceipt {
    fn body_hash(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(b"publish-receipt-v1");
        h.u64(self.seq)
            .field(self.name.as_bytes())
            .field(self.owner.as_bytes())
            .field(self.content_root.as_bytes())
            .u64(self.asset_count as u64);
        h.finalize()
    }
    fn seq(&self) -> u64 {
        self.seq
    }
    fn attestation(&self) -> Option<&ReceiptAttestation> {
        self.attest.as_ref()
    }
}

/// Why a publish was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PublishError {
    /// The presented cap does not authorize publishing `name` (wrong / ill-formed
    /// `site-host/<name>` token). The cap-attenuation refusal.
    CapRefused { cap: String, name: String },
    /// The site has no assets — there is nothing to serve.
    EmptyContent,
    /// The site name is not a usable subdomain label (empty, or contains a `.`/`/`
    /// that would break host resolution).
    InvalidName(String),
    /// The publish was cap-valid but the durable backend could not persist the site
    /// cell (a disk/fsync fault). The publish is refused rather than reported as
    /// durable when it is not — a published site that would vanish on restart is not
    /// a successful publish.
    Persist(String),
}

impl std::fmt::Display for PublishError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PublishError::CapRefused { cap, name } => {
                write!(f, "cap `{cap}` does not authorize publishing site `{name}`")
            }
            PublishError::EmptyContent => write!(f, "cannot publish a site with no assets"),
            PublishError::InvalidName(n) => write!(f, "`{n}` is not a valid site name"),
            PublishError::Persist(e) => write!(f, "could not persist the published site: {e}"),
        }
    }
}

impl std::error::Error for PublishError {}

/// The **per-site bandwidth byte-counter** — the new metering surface hosting
/// billing rides on (`docs/PERMISSIONLESS-CLOUD-PLAN.md` §3.5).
///
/// Bandwidth is the one genuinely-new hosting meter: every other resource (publish,
/// cert, build, uptime) reuses an existing meter shape, but *bytes served per site*
/// must be counted in the serving path itself. This counter is the data-plane half
/// of that meter — wired into [`SiteRegistry::serve_site`] (the serving loop the
/// gateway and the `dreggnet-host` binary both drive), it accumulates the response
/// body bytes delivered for each site, exposes the **unbilled** tail a control-plane
/// roll-up settles, and carries the **lapse** flag that stops serving a site whose
/// hosting budget is exhausted.
///
/// ## Don't double-count (the billing cursor)
///
/// Per site it tracks two monotonic counts: `served` (every delivered byte) and
/// `billed` (bytes already folded into a settled `$DREGG` charge). The control-plane
/// meter bills `unbilled = served − billed` each period and advances `billed` by
/// exactly what it settled ([`mark_billed`](BandwidthMeter::mark_billed)) — so a
/// re-run of the roll-up, or a second settler, never bills the same byte twice. Only
/// *successfully delivered* (`200`) content is counted, so a miss or a lapse-refusal
/// accrues no billable bandwidth.
///
/// ## Lapse = stop serving
///
/// When a roll-up cannot be paid (the owner's spend account is exhausted) the
/// control meter [`lapse`](BandwidthMeter::lapse)s the site; the serving path then
/// refuses it with `402` (the hosting analog of a compute lease lapsing → reap).
/// A top-up [`reinstate`](BandwidthMeter::reinstate)s it.
#[derive(Default)]
pub struct BandwidthMeter {
    /// site name → its byte accounting (served / billed / lapsed).
    sites: Mutex<BTreeMap<String, SiteBandwidth>>,
}

/// One site's bandwidth accounting within a [`BandwidthMeter`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct SiteBandwidth {
    /// Total bytes ever served for the site (monotonic).
    served: u64,
    /// Bytes already rolled into a settled bandwidth charge (the billing cursor).
    billed: u64,
    /// Whether the site's hosting budget is exhausted — serving is refused.
    lapsed: bool,
    /// The **funded byte budget** — the in-band serving ceiling (HB-1 fix). The owner
    /// funds coverage for this many served bytes; once `served` would exceed it the
    /// serving path refuses `402` IMMEDIATELY, so free egress is bounded by the funded
    /// budget rather than by how often the (post-paid) roll-up sweep runs. `None`
    /// leaves serving uncapped (the free/local default, or a site whose coverage the
    /// control plane has not set).
    budget: Option<u64>,
}

impl BandwidthMeter {
    /// A fresh meter with no recorded traffic.
    pub fn new() -> BandwidthMeter {
        BandwidthMeter::default()
    }

    /// Record `bytes` of delivered content for `site` (called by the serving path).
    pub fn record(&self, site: &str, bytes: u64) {
        let mut g = self.sites.lock().expect("bandwidth meter poisoned");
        g.entry(site.to_string()).or_default().served += bytes;
    }

    /// Total bytes ever served for `site` (`0` if it has served nothing).
    pub fn served(&self, site: &str) -> u64 {
        self.sites
            .lock()
            .expect("bandwidth meter poisoned")
            .get(site)
            .map(|s| s.served)
            .unwrap_or(0)
    }

    /// The **unbilled** bytes for `site`: `served − billed`, the tail a bandwidth
    /// roll-up charge settles. `0` when everything served is already billed.
    pub fn unbilled(&self, site: &str) -> u64 {
        self.sites
            .lock()
            .expect("bandwidth meter poisoned")
            .get(site)
            .map(|s| s.served.saturating_sub(s.billed))
            .unwrap_or(0)
    }

    /// Advance the billing cursor for `site` by `bytes` — called by the control
    /// meter **after** a bandwidth charge settles, so the same bytes are never
    /// billed twice. The cursor is clamped to `served` (never bills ahead).
    pub fn mark_billed(&self, site: &str, bytes: u64) {
        let mut g = self.sites.lock().expect("bandwidth meter poisoned");
        let s = g.entry(site.to_string()).or_default();
        s.billed = (s.billed + bytes).min(s.served);
    }

    /// Mark `site` lapsed — its hosting budget is exhausted; serving stops.
    pub fn lapse(&self, site: &str) {
        self.sites
            .lock()
            .expect("bandwidth meter poisoned")
            .entry(site.to_string())
            .or_default()
            .lapsed = true;
    }

    /// Clear `site`'s lapse (a budget top-up): serving resumes.
    pub fn reinstate(&self, site: &str) {
        if let Some(s) = self
            .sites
            .lock()
            .expect("bandwidth meter poisoned")
            .get_mut(site)
        {
            s.lapsed = false;
        }
    }

    /// Set `site`'s **funded byte budget** — the in-band serving ceiling (HB-1). The
    /// control plane sets this from the owner's funded hosting balance; the serving
    /// path then refuses `402` the moment a request would push `served` past it, so a
    /// bandwidth burst cannot deliver free egress between roll-up sweeps. An absolute
    /// set (the high-water authorization); pair with [`add_budget`](Self::add_budget)
    /// for top-ups.
    pub fn set_budget(&self, site: &str, budget_bytes: u64) {
        self.sites
            .lock()
            .expect("bandwidth meter poisoned")
            .entry(site.to_string())
            .or_default()
            .budget = Some(budget_bytes);
    }

    /// Top up `site`'s funded byte budget by `bytes` (a coverage top-up). A site with
    /// no budget set starts from `0` before the top-up (so an explicit top-up always
    /// makes the ceiling finite + enforced).
    pub fn add_budget(&self, site: &str, bytes: u64) {
        let mut g = self.sites.lock().expect("bandwidth meter poisoned");
        let s = g.entry(site.to_string()).or_default();
        s.budget = Some(s.budget.unwrap_or(0).saturating_add(bytes));
    }

    /// `site`'s funded byte budget, if a finite in-band ceiling is set (`None` ⇒
    /// uncapped serving).
    pub fn budget(&self, site: &str) -> Option<u64> {
        self.sites
            .lock()
            .expect("bandwidth meter poisoned")
            .get(site)
            .and_then(|s| s.budget)
    }

    /// Whether serving `extra` more bytes for `site` would exceed its funded byte
    /// budget (HB-1): `true` ⇒ the serving path must refuse `402` in-band. A site with
    /// no budget set (`None`) is uncapped, so this is always `false` for it.
    pub fn would_exceed_budget(&self, site: &str, extra: u64) -> bool {
        let g = self.sites.lock().expect("bandwidth meter poisoned");
        match g.get(site) {
            Some(s) => match s.budget {
                Some(b) => s.served.saturating_add(extra) > b,
                None => false,
            },
            None => false,
        }
    }

    /// Whether `site` is lapsed (serving is refused).
    pub fn is_lapsed(&self, site: &str) -> bool {
        self.sites
            .lock()
            .expect("bandwidth meter poisoned")
            .get(site)
            .map(|s| s.lapsed)
            .unwrap_or(false)
    }

    /// Every site with recorded traffic — the set a control-plane roll-up sweeps.
    pub fn sites(&self) -> Vec<String> {
        self.sites
            .lock()
            .expect("bandwidth meter poisoned")
            .keys()
            .cloned()
            .collect()
    }
}

/// The registry of published site cells — the hosting **data plane**.
///
/// Publishing inserts a cap-gated, receipted [`SiteCell`]; serving resolves an
/// inbound request's `Host` (`<name>.dregg.works`) to the named cell and serves its
/// content. This is what the gateway adopts (`gateway/src/hosting.rs`) and what the
/// portable `dreggnet-host` binary serves over real TCP.
///
/// With a [`BandwidthMeter`] attached ([`with_bandwidth`](SiteRegistry::with_bandwidth)),
/// the serving path counts the bytes it delivers per site and refuses a site whose
/// hosting budget has lapsed — the data-plane half of metered-`$DREGG` hosting.
#[derive(Default)]
pub struct SiteRegistry {
    sites: Mutex<BTreeMap<String, SiteCell>>,
    next_seq: AtomicU64,
    /// The per-site bandwidth byte-counter, when hosting is metered. `None` leaves
    /// serving unmetered (the free/local default).
    bandwidth: Option<Arc<BandwidthMeter>>,
    /// The receipt chain a publish is sealed into — prev-hash-chained + signed,
    /// so a client can verify a publish without trusting the host. `None` is the
    /// unsigned free/local default ([`PublishReceipt::attest`] is then `None`).
    receipt_chain: Option<ReceiptChain>,
    /// The latest signed publish receipt retained per site, so the serving/read
    /// side can hand a non-witness the receipt alongside the bytes (the
    /// [`crate::verify::SiteReceiptBundle`] the trustless read re-witnesses). Only
    /// populated when the registry is signed; the unsigned default leaves it empty.
    receipts: Mutex<BTreeMap<String, PublishReceipt>>,
    /// The durable backend — when set, the registry IS a **umem cell**: every
    /// published [`SiteCell`] is laid into the cell's `(collection,key) -> value`
    /// heap and committed to the real sorted-Poseidon2 boundary root
    /// ([`dreggnet_umem::UmemRegistry`]), so a gateway/host restart RECONSTRUCTS the
    /// published sites FROM the committed heap rather than losing them. This replaces
    /// the from-scratch JSON-lines log with the real substrate (the #2 re-dregg move,
    /// `docs/REGISTRIES-AS-UMEM.md`) — unlocking fork/time-travel/merge-readiness.
    /// `None` is the in-memory-only free/local default;
    /// [`with_durable_store`](SiteRegistry::with_durable_store) attaches it and
    /// reloads the prior sites.
    store: Option<UmemRegistry<SiteCell>>,
}

impl SiteRegistry {
    /// A fresh, empty registry (unmetered serving — the free/local default).
    pub fn new() -> SiteRegistry {
        SiteRegistry::default()
    }

    /// A fresh registry whose serving path counts bandwidth (and honors lapses)
    /// through `bandwidth` — the metered-`$DREGG` hosting data plane.
    pub fn with_bandwidth(bandwidth: Arc<BandwidthMeter>) -> SiteRegistry {
        SiteRegistry {
            bandwidth: Some(bandwidth),
            ..SiteRegistry::default()
        }
    }

    /// The bandwidth byte-counter this registry meters serving through, if any.
    pub fn bandwidth(&self) -> Option<&Arc<BandwidthMeter>> {
        self.bandwidth.as_ref()
    }

    /// Attach a [`BandwidthMeter`] to this registry (builder form) so a registry
    /// built with another constructor — e.g. [`signed`](SiteRegistry::signed), to
    /// seal re-witnessable publish receipts — also meters its serving path. Composes
    /// with [`signed`] / [`with_durable_store`](SiteRegistry::with_durable_store):
    /// `SiteRegistry::signed(seed).with_bandwidth_meter(bw)` is a signed AND metered
    /// data plane (what the gateway serves).
    pub fn with_bandwidth_meter(mut self, bandwidth: Arc<BandwidthMeter>) -> SiteRegistry {
        self.bandwidth = Some(bandwidth);
        self
    }

    /// Attach a **durable umem backend** at `path` and **reconstruct** the prior data
    /// plane: open the [`UmemRegistry`](dreggnet_umem::UmemRegistry) (the registry
    /// AS a umem cell), restore every persisted [`SiteCell`] FROM the committed heap
    /// back into the live registry, and commit every future
    /// [`publish`](SiteRegistry::publish) to the heap — so a gateway/host restart
    /// serves the sites a prior process published (the data-plane durability blocker)
    /// instead of losing them.
    ///
    /// Builder form: chains after [`new`](SiteRegistry::new) /
    /// [`with_bandwidth`](SiteRegistry::with_bandwidth) /
    /// [`signed`](SiteRegistry::signed). The restore **fails closed** if the committed
    /// heap does not bind its sealed boundary root (the `root_binds_get` discipline).
    pub fn with_durable_store(
        mut self,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<SiteRegistry> {
        let store = UmemRegistry::<SiteCell>::open(path).map_err(|e| e.into_io())?;
        // Reconstruct: every persisted site cell returns to the live map.
        let mut next = 0u64;
        {
            let mut sites = self.sites.lock().expect("sites poisoned");
            for cell in store.all() {
                sites.insert(cell.name.clone(), cell);
                next += 1;
            }
        }
        // Keep the publish sequence monotonic past what was reconstructed.
        self.next_seq.fetch_max(next, Ordering::Relaxed);
        self.store = Some(store);
        Ok(self)
    }

    /// A fresh registry whose published sites are **durable** at `path` — the
    /// data-plane-durable default a real gateway/host uses (shorthand for
    /// `SiteRegistry::new().with_durable_store(path)`).
    pub fn durable(path: impl AsRef<std::path::Path>) -> std::io::Result<SiteRegistry> {
        SiteRegistry::new().with_durable_store(path)
    }

    /// The durable backend path, if this registry persists its sites.
    pub fn durable_path(&self) -> Option<&std::path::Path> {
        self.store.as_ref().map(|s| s.path())
    }

    /// The registry's **committed umem boundary root** (hex), if it is durably backed:
    /// the real sorted-Poseidon2 `compute_heap_root` over the hosting cell's heap — the
    /// 32-byte commitment a dregg light client understands for the WHOLE published
    /// namespace (distinct from a single site's per-content `content_root`). `None` when
    /// the registry is in-memory-only.
    pub fn umem_root(&self) -> Option<String> {
        self.store.as_ref().map(|s| s.boundary_root())
    }

    /// **Fork the whole hosting namespace** (a umem superpower a `Mutex<BTreeMap>` can
    /// never give): copy the committed hosting cell at `new_path`, returning a divergent
    /// `SiteRegistry` that starts byte-identical (same boundary root) and diverges as
    /// either side publishes — a tenant forks their entire set of published sites at once
    /// (a preview/branch deploy of the namespace), then serves / stitches / discards it.
    /// `None` when the registry is in-memory-only (nothing committed to fork).
    pub fn fork_namespace(
        &self,
        new_path: impl AsRef<std::path::Path>,
    ) -> Option<std::io::Result<SiteRegistry>> {
        let store = self.store.as_ref()?;
        Some(match store.fork(new_path) {
            Ok(forked) => SiteRegistry::adopt_umem(forked),
            Err(e) => Err(e.into_io()),
        })
    }

    /// **Time-travel — checkpoint** the current namespace: the committed boundary root,
    /// retained so [`restore_namespace`](Self::restore_namespace) can return to it
    /// ("my sites as of now"). `None` when in-memory-only.
    pub fn checkpoint_namespace(&self) -> Option<String> {
        self.store.as_ref().map(|s| s.checkpoint())
    }

    /// **Time-travel — restore** the namespace to an earlier committed `root` (from
    /// [`checkpoint_namespace`](Self::checkpoint_namespace)): the published sites revert
    /// to that committed state, durably (the rollback survives a restart). Reloads the
    /// reconstructed in-memory view from the restored heap. A no-op `Ok(())` when
    /// in-memory-only.
    pub fn restore_namespace(&mut self, root: &str) -> std::io::Result<()> {
        if let Some(store) = &self.store {
            store.restore(root).map_err(|e| e.into_io())?;
            // Re-seed the in-memory serving map from the restored committed heap.
            let mut sites = self.sites.lock().expect("sites poisoned");
            sites.clear();
            for cell in store.all() {
                sites.insert(cell.name.clone(), cell);
            }
        }
        Ok(())
    }

    /// Build a `SiteRegistry` from an already-open [`UmemRegistry`] (the fork path),
    /// re-seeding the in-memory serving map from the committed heap.
    fn adopt_umem(store: UmemRegistry<SiteCell>) -> std::io::Result<SiteRegistry> {
        let mut reg = SiteRegistry::default();
        let mut next = 0u64;
        {
            let mut sites = reg.sites.lock().expect("sites poisoned");
            for cell in store.all() {
                sites.insert(cell.name.clone(), cell);
                next += 1;
            }
        }
        reg.next_seq.fetch_max(next, Ordering::Relaxed);
        reg.store = Some(store);
        Ok(reg)
    }

    /// A registry whose publishes are sealed into a prev-hash-chained,
    /// ed25519-signed receipt stream under the secret `seed` — so each
    /// [`PublishReceipt`] is re-witnessable (a client verifies a publish with
    /// [`dreggnet_receipt::verify_chain`] against [`Self::receipt_signer`], no
    /// trust in the host). A real host configures a persistent secret.
    pub fn signed(seed: [u8; 32]) -> SiteRegistry {
        SiteRegistry {
            receipt_chain: Some(ReceiptChain::from_seed(seed)),
            ..SiteRegistry::default()
        }
    }

    /// Attach a receipt chain to this registry (builder form).
    pub fn with_receipt_chain(mut self, chain: ReceiptChain) -> SiteRegistry {
        self.receipt_chain = Some(chain);
        self
    }

    /// The public key a non-witness verifies this registry's publish receipts
    /// under, if it is a signed registry.
    pub fn receipt_signer(&self) -> Option<[u8; 32]> {
        self.receipt_chain.as_ref().map(|c| c.signer_public())
    }

    /// Publish a minisite as a cap-gated, receipted turn.
    ///
    /// Gates on `cap` (must be a `site-host/<name>` cap whose name is `name`),
    /// validates the name as a subdomain label and the content as non-empty, writes
    /// the [`SiteCell`] (owner = the cap holder), and returns the [`PublishReceipt`].
    /// Republishing an existing name with the right cap replaces the cell (a new
    /// content commitment, a new receipt).
    pub fn publish(
        &self,
        cap: &PublishCap,
        name: &str,
        content: SiteContent,
    ) -> Result<PublishReceipt, PublishError> {
        if !is_valid_name(name) {
            return Err(PublishError::InvalidName(name.to_string()));
        }
        if !cap.authorizes(name) {
            return Err(PublishError::CapRefused {
                cap: cap.cap.clone(),
                name: name.to_string(),
            });
        }
        if content.is_empty() {
            return Err(PublishError::EmptyContent);
        }

        let cell = SiteCell::new(name, cap.holder.clone(), content);
        let seq = self.next_seq.fetch_add(1, Ordering::Relaxed);
        let mut receipt = PublishReceipt {
            seq,
            name: cell.name.clone(),
            owner: cell.owner.clone(),
            content_root: cell.content_root.clone(),
            asset_count: cell.content.len(),
            attest: None,
        };
        // A publish IS a turn: seal it into the registry's signed receipt chain
        // (the owned-state authority — this stream IS the turn-receipt chain for
        // hosting). `None` (free/local) leaves a bare projection.
        if let Some(chain) = &self.receipt_chain {
            receipt.attest = Some(chain.seal(receipt.body_hash(), receipt.seq(), None));
            // Retain the signed receipt so the read path can serve it beside the
            // bytes (the trustless re-witness bundle). Unsigned publishes are bare
            // projections — nothing re-witnessable to retain.
            self.receipts
                .lock()
                .expect("receipts poisoned")
                .insert(name.to_string(), receipt.clone());
        }
        // Durable-first: persist the published cell (append + fsync) BEFORE the
        // in-memory insert, so a publish is never reported successful unless it
        // survives a restart. A store fault refuses the publish (the data-plane
        // durability guarantee), it does not silently serve a will-vanish site.
        if let Some(store) = &self.store {
            store
                .append(&cell)
                .map_err(|e| PublishError::Persist(e.to_string()))?;
        }
        self.sites
            .lock()
            .expect("sites poisoned")
            .insert(name.to_string(), cell);
        Ok(receipt)
    }

    /// The latest signed publish receipt retained for `name`, if this is a signed
    /// registry that has published it. The read path hands this to a non-witness.
    pub fn receipt(&self, name: &str) -> Option<PublishReceipt> {
        self.receipts
            .lock()
            .expect("receipts poisoned")
            .get(name)
            .cloned()
    }

    /// Assemble the self-verifying [`crate::verify::SiteReceiptBundle`] for `name`:
    /// the owner signing key, the signed publish receipt, and the served content —
    /// everything a non-witness needs to re-verify the served bytes against the
    /// committed root with no trust in this host. `None` unless the registry is
    /// signed AND `name` has been published.
    pub fn site_bundle(&self, name: &str) -> Option<crate::verify::SiteReceiptBundle> {
        let signer = self.receipt_signer()?;
        let receipt = self.receipt(name)?;
        let cell = self.get(name)?;
        Some(crate::verify::SiteReceiptBundle {
            signer,
            receipt,
            content: cell.content,
        })
    }

    /// Look up a published site cell by name (a clone of the committed cell).
    pub fn get(&self, name: &str) -> Option<SiteCell> {
        self.sites
            .lock()
            .expect("sites poisoned")
            .get(name)
            .cloned()
    }

    /// The names of all published sites (publish-time set, sorted).
    pub fn names(&self) -> Vec<String> {
        self.sites
            .lock()
            .expect("sites poisoned")
            .keys()
            .cloned()
            .collect()
    }

    /// Resolve + serve one request, given the request's `Host` header.
    ///
    /// Extracts the `<name>` label from `<name>.dregg.works` (port + apex stripped),
    /// looks up the site cell, and serves `req`'s path against its content. An
    /// unresolvable host is a `404`; a request the host resolves to but whose path
    /// misses is the cell's own `404`.
    pub fn resolve(&self, host: &str, req: &WebRequest) -> WebResponse {
        let Some(name) = site_name_from_host(host) else {
            return WebResponse::error(404, format!("no site for host `{host}`"));
        };
        self.serve_site(&name, req)
    }

    /// Serve `req` against the named site cell, metered: a **lapsed** site (its
    /// hosting budget exhausted) is refused with `402` before any content is read,
    /// and the delivered body bytes of a `200` are recorded against the site's
    /// bandwidth counter (the single byte-counting hook, so neither the wildcard nor
    /// the custom-domain serving path double-counts).
    ///
    /// This is the serving-loop entry both `<name>.dregg.works` ([`resolve`]) and a
    /// verified custom domain (`gateway/src/hosting.rs`) funnel through.
    pub fn serve_site(&self, name: &str, req: &WebRequest) -> WebResponse {
        // A lapsed site (budget exhausted) is refused 402 before any content read.
        let lapsed = self
            .bandwidth
            .as_ref()
            .map(|bw| bw.is_lapsed(name))
            .unwrap_or(false);
        let mut resp = if lapsed {
            WebResponse {
                status: 402,
                content_type: "text/plain; charset=utf-8".to_string(),
                body: format!("site `{name}` hosting budget exhausted (lapsed)").into_bytes(),
            }
        } else {
            match self.get(name) {
                Some(cell) => cell.serve(req),
                None => WebResponse::error(404, format!("no site named `{name}`")),
            }
        };

        // HB-1: the IN-BAND budget gate. If delivering a `200` body would push the site
        // past its funded byte budget, refuse `402` instead — the over-budget body is
        // never delivered, so a burst's free egress is bounded by funded coverage, not
        // by how long until the next post-paid roll-up sweep lapses the site.
        if let Some(bw) = &self.bandwidth {
            if resp.status == 200 && bw.would_exceed_budget(name, resp.body.len() as u64) {
                resp = WebResponse {
                    status: 402,
                    content_type: "text/plain; charset=utf-8".to_string(),
                    body: format!("site `{name}` would exceed its funded bandwidth budget")
                        .into_bytes(),
                };
            }
        }

        // HB-2: meter EVERY delivered response body — a served `200` AND a `404` miss
        // body are real egress, so neither is free (closing the free-error-egress +
        // attacker-reflected-404 amplification leak). A `402` REFUSAL is the system's
        // "stop", not delivered content the owner chose to serve, so it is not billed
        // (billing a refusal would be perverse and is itself bounded — a 402 only fires
        // when serving has stopped). The single record point keeps the count
        // exactly-once per request across both serving paths.
        if let Some(bw) = &self.bandwidth {
            if resp.status != 402 {
                bw.record(name, resp.body.len() as u64);
            }
        }
        resp
    }
}

/// Extract the site `<name>` label from a request `Host`.
///
/// `<name>.dregg.works[:port]` → `Some(name)`. The bare apex `dregg.works` and
/// `www.dregg.works` resolve to `None` (no per-site landing here). For local
/// testing without DNS, a host that is *exactly* a bare label (no dot, e.g.
/// `blog` or `blog:8080`) resolves to that label, so `curl -H 'Host: blog'` hits
/// the `blog` site against a local gateway.
pub fn site_name_from_host(host: &str) -> Option<String> {
    // Strip a `:port` suffix.
    let host = host.split(':').next().unwrap_or(host).trim();
    if host.is_empty() {
        return None;
    }
    if let Some(label) = host.strip_suffix(".dregg.works") {
        // `<name>.dregg.works`; reject the `www` apex alias and empty/multi-label.
        if label.is_empty() || label == "www" || label.contains('.') {
            return None;
        }
        return Some(label.to_ascii_lowercase());
    }
    // Local-testing fallback: a bare single label (no dots) is taken as the name.
    if !host.contains('.') {
        return Some(host.to_ascii_lowercase());
    }
    None
}

/// Whether `name` is a usable subdomain label: non-empty, ≤63 chars, and only
/// `[a-z0-9-]` (not starting/ending with `-`). This keeps a site name a valid DNS
/// label and a clean `content_root` key.
pub fn is_valid_name(name: &str) -> bool {
    if name.is_empty() || name.len() > 63 {
        return false;
    }
    if name.starts_with('-') || name.ends_with('-') {
        return false;
    }
    name.bytes()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
}

/// Normalize a request/content path to a canonical content key:
/// `""`/`"/"` → `/index.html`; a trailing slash → `…/index.html`; otherwise the
/// path with a leading `/` ensured.
fn normalize_key(path: &str) -> String {
    let path = path.trim();
    if path.is_empty() || path == "/" {
        return "/index.html".to_string();
    }
    let with_slash = if path.starts_with('/') {
        path.to_string()
    } else {
        format!("/{path}")
    };
    if with_slash.ends_with('/') {
        format!("{with_slash}index.html")
    } else {
        with_slash
    }
}

/// A deterministic content commitment over a site's content.
///
/// The REAL sorted-Poseidon2 cell-heap commitment ([`poseidon2::content_root`]):
/// the same hash family (Poseidon2 over BabyBear), the same heap-root function
/// (`dregg_circuit::heap_root::compute_heap_root_entries`), and the same 8-felt
/// faithful widening (`wire_commit_8`, ~124-bit) the dregg kernel commits its umem
/// heap with — so a light client / a stranger re-witnesses the served bytes against
/// the SAME collision-resistant root the kernel understands (pinned by the proven
/// `Heap.root_binds_get`). There is no non-cryptographic fallback: the published
/// commitment is real Poseidon2 on every build.
///
/// ## The boundary (honest)
///
/// This makes the HOSTED content's commitment real Poseidon2 + locally-verifiable:
/// [`crate::verify::verify_site_bundle`] re-witnesses the served bytes against this
/// root with no trust in the host. The remaining seam — an on-chain `Effect::Write`
/// committing this heap to a dregg node, and a LIGHT CLIENT witnessing that write
/// IN-CIRCUIT (the S3 proof-attestation, so a pure verifier — not a re-executing
/// validator — sees the publish) — is the **circuit swarm's VK-epoch**, deliberately
/// NOT done here. The OFF-chain half is closed: the content commitment is the
/// kernel's real Poseidon2 and is re-witnessable; the in-circuit witness of the
/// write is its named shadow.
pub fn content_root(content: &SiteContent) -> String {
    poseidon2::content_root(content)
}

/// The REAL sorted-Poseidon2 site-content commitment.
///
/// A site IS a dregg cell; its content (path → asset) is committed the way the
/// kernel commits a cell's umem heap:
///
/// 1. each asset is hashed to a WIDE 8-felt (~124-bit) Poseidon2 digest binding the
///    length-delimited `(path, content_type, body)` (`hash_many_8`);
/// 2. those 8 felts are placed in the canonical SORTED Poseidon2 Merkle heap keyed
///    by `(collection = path, key = limb-index)` and the kernel's heap-root function
///    folds the root (`compute_heap_root_entries`);
/// 3. the published `content_root` is the kernel's 8-felt faithful widening
///    (`wire_commit_8`) over the per-asset wide limbs with the heap root as the final
///    `iroot` — a WIDE carrier chain with no 31-bit intermediate, so the commitment
///    matches the proof's ~130-bit FRI soundness (not the ~31-bit floor a single felt
///    would be, the `docs/FAITHFUL-STATE-COMMITMENT.md` discipline).
///
/// Real Poseidon2, locally re-witnessable. Byte-identity with the FULL deployed umem
/// cell root (cell id / lifecycle limbs / v9 rotation) and the in-circuit witness of
/// the `Effect::Write` are the circuit swarm's VK-epoch (see [`content_root`]).
pub mod poseidon2 {
    use super::SiteContent;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::heap_root::compute_heap_root_entries;
    use dregg_circuit::poseidon2::{hash_bytes, hash_many_8, wire_commit_8};

    /// Domain separation for the site-content commitment (distinct from the bucket
    /// commitment and any other heap use).
    const DOMAIN: &[u8] = b"dreggnet-site-content-root-v1";

    /// The published site content commitment — see the module docs.
    pub fn content_root(content: &SiteContent) -> String {
        let mut entries: Vec<((BabyBear, BabyBear), BabyBear)> = Vec::new();
        let mut limbs: Vec<BabyBear> = Vec::new();
        for (path, asset) in &content.assets {
            let d8 = asset_digest8(path, &asset.content_type, &asset.body);
            // The asset's namespace within the cell heap (the sort-key collection).
            let coll = hash_bytes(path.as_bytes());
            for (i, &limb) in d8.iter().enumerate() {
                entries.push(((coll, BabyBear::new(i as u32)), limb));
                limbs.push(limb);
            }
        }
        // (2) The kernel's sorted-Poseidon2 cell-heap root over the asset limbs.
        let heap_root = compute_heap_root_entries(&entries);
        // (3) The faithful 8-felt commitment: a WIDE-carrier fold over the per-asset
        // wide limbs (no 31-bit intermediate), bound to the heap root, the asset
        // count, and a domain tag. The 4-felt domain header also keeps the fold
        // total when content is empty (the publish path forbids that, belt-and-braces).
        let mut pre = vec![
            hash_bytes(DOMAIN),
            BabyBear::new(content.assets.len() as u32),
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        pre.extend_from_slice(&limbs);
        felts8_to_hex(&wire_commit_8(&pre, heap_root))
    }

    /// The per-asset WIDE (8-felt, ~124-bit) Poseidon2 digest over the
    /// length-delimited `(path, content_type, body)`.
    fn asset_digest8(path: &str, content_type: &str, body: &[u8]) -> [BabyBear; 8] {
        let mut input: Vec<BabyBear> = Vec::new();
        absorb_len_delimited(&mut input, path.as_bytes());
        absorb_len_delimited(&mut input, content_type.as_bytes());
        absorb_len_delimited(&mut input, body);
        hash_many_8(&input)
    }

    /// Push a length felt then the packed bytes, so field-domain concatenation is
    /// unambiguous (a server cannot shift bytes between fields without moving the
    /// digest). Bytes are packed with the **injective** [`pack_bytes`] so distinct
    /// byte strings always map to distinct felt sequences.
    fn absorb_len_delimited(out: &mut Vec<BabyBear>, bytes: &[u8]) {
        out.push(BabyBear::new(bytes.len() as u32));
        out.extend(pack_bytes(bytes));
    }

    /// **Injective** byte → field packing for the content commitment.
    ///
    /// Packs **3 little-endian bytes per element** (a u24 value `< 2^24 ≤ p`, so
    /// `BabyBear::new` performs no modular reduction). This is deliberately NOT the
    /// shared `dregg_circuit::field::from_bytes_packed`, which packs **4** bytes into
    /// a u32 and reduces `% p`: since `p ≈ 2^30.9 < 2^32`, ~53% of 4-byte chunks
    /// alias their `+p` partner (`v ≡ v + p`), so two distinct equal-length byte
    /// strings could produce the identical `content_root` and pass `verify_site_bundle`.
    ///
    /// With 3 bytes/felt there is no wraparound, so within a fixed length two byte
    /// strings differing at any position produce a different felt at that chunk;
    /// combined with the byte-length prefix in [`absorb_len_delimited`] the map is
    /// injective for same-length **and** different-length inputs.
    fn pack_bytes(bytes: &[u8]) -> Vec<BabyBear> {
        let mut out = Vec::with_capacity(bytes.len() / 3 + 1);
        for chunk in bytes.chunks(3) {
            let mut val: u32 = 0;
            for (j, &b) in chunk.iter().enumerate() {
                val |= (b as u32) << (j * 8);
            }
            // val < 2^24 < p, so `new` is the identity (no reduction, injective).
            out.push(BabyBear::new(val));
        }
        out
    }

    /// Lower-hex encode an 8-felt digest (8 × u32 → 64 hex chars; ~124-bit collision
    /// resistance, matching the proof's FRI soundness floor).
    fn felts8_to_hex(f: &[BabyBear; 8]) -> String {
        use std::fmt::Write as _;
        let mut s = String::with_capacity(64);
        for x in f {
            let _ = write!(s, "{:08x}", x.as_u32());
        }
        s
    }
}

/// Infer a `Content-Type` from a path's file extension. Unknown extensions get
/// `application/octet-stream` (a safe, downloadable default).
pub fn content_type_for(path: &str) -> &'static str {
    let ext = path.rsplit('.').next().unwrap_or("").to_ascii_lowercase();
    match ext.as_str() {
        "html" | "htm" => "text/html; charset=utf-8",
        "css" => "text/css; charset=utf-8",
        "js" | "mjs" => "text/javascript; charset=utf-8",
        "json" => "application/json",
        "wasm" => "application/wasm",
        "svg" => "image/svg+xml",
        "png" => "image/png",
        "jpg" | "jpeg" => "image/jpeg",
        "gif" => "image/gif",
        "webp" => "image/webp",
        "avif" => "image/avif",
        "ico" => "image/x-icon",
        "txt" | "text" => "text/plain; charset=utf-8",
        "xml" => "application/xml",
        "pdf" => "application/pdf",
        "woff2" => "font/woff2",
        "woff" => "font/woff",
        "ttf" => "font/ttf",
        "otf" => "font/otf",
        "map" => "application/json",
        "webmanifest" => "application/manifest+json",
        _ => "application/octet-stream",
    }
}

/// A small sample minisite — an `index.html` + `style.css` — for the demo binary
/// and the round-trip proof.
pub fn sample_site() -> SiteContent {
    SiteContent::new()
        .with(
            "/index.html",
            "<!doctype html><html><head><link rel=\"stylesheet\" href=\"/style.css\">\
             <title>hosted on dregg.works</title></head>\
             <body><h1>hello from a dregg cell</h1>\
             <p>this minisite is backed by a published site cell.</p></body></html>",
        )
        .with(
            "/style.css",
            "body{font-family:system-ui;margin:3rem;max-width:40rem}",
        )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pub_cap(holder: &str, name: &str) -> PublishCap {
        PublishCap::for_site(holder, name)
    }

    #[test]
    fn content_type_inference() {
        assert_eq!(content_type_for("/index.html"), "text/html; charset=utf-8");
        assert_eq!(content_type_for("/a/style.css"), "text/css; charset=utf-8");
        assert_eq!(
            content_type_for("/app.js"),
            "text/javascript; charset=utf-8"
        );
        assert_eq!(content_type_for("/logo.png"), "image/png");
        assert_eq!(content_type_for("/data.bin"), "application/octet-stream");
        assert_eq!(content_type_for("/noext"), "application/octet-stream");
    }

    #[test]
    fn host_resolution() {
        assert_eq!(
            site_name_from_host("blog.dregg.works").as_deref(),
            Some("blog")
        );
        assert_eq!(
            site_name_from_host("Blog.dregg.works:443").as_deref(),
            Some("blog")
        );
        assert_eq!(site_name_from_host("dregg.works"), None);
        assert_eq!(site_name_from_host("www.dregg.works"), None);
        assert_eq!(site_name_from_host("a.b.dregg.works"), None);
        // local-testing bare-label fallback
        assert_eq!(site_name_from_host("blog").as_deref(), Some("blog"));
        assert_eq!(site_name_from_host("blog:8080").as_deref(), Some("blog"));
    }

    #[test]
    fn name_validation() {
        assert!(is_valid_name("blog"));
        assert!(is_valid_name("my-site-2"));
        assert!(!is_valid_name(""));
        assert!(!is_valid_name("-x"));
        assert!(!is_valid_name("x-"));
        assert!(!is_valid_name("Has.Dot"));
        assert!(!is_valid_name("has space"));
    }

    #[test]
    fn content_root_is_deterministic_and_sensitive() {
        let a = SiteContent::new()
            .with("/index.html", "hi")
            .with("/x.css", "body{}");
        // Insertion order does not matter (BTreeMap canonical).
        let b = SiteContent::new()
            .with("/x.css", "body{}")
            .with("/index.html", "hi");
        assert_eq!(content_root(&a), content_root(&b));
        // A single changed byte moves the root.
        let c = SiteContent::new()
            .with("/index.html", "hI")
            .with("/x.css", "body{}");
        assert_ne!(content_root(&a), content_root(&c));
    }

    /// The site `content_root` is the REAL sorted-Poseidon2 cell-heap commitment —
    /// FNV is GONE from the content-commitment path. A published site commits to the
    /// real Poseidon2 root, and the wide (8-felt, ~124-bit) commitment is
    /// byte-sensitive across path / content-type / body.
    #[test]
    fn content_root_is_the_real_poseidon2_root_not_fnv() {
        let site = sample_site();
        let root = content_root(&site);

        // (a) the content-commitment path is the wide 64-hex (8-felt, ~124-bit)
        //     Poseidon2 commitment — collision-resistant, not a 16-hex non-CR stand-in.
        assert_eq!(
            root.len(),
            64,
            "the content_root is the wide 8-felt Poseidon2 commitment (64 hex)"
        );
        assert!(root.chars().all(|c| c.is_ascii_hexdigit()));

        // (b) the published root IS the real Poseidon2 root for a known input
        //     (recomputed from the kernel primitives in `poseidon2::content_root`),
        //     and is deterministic + input-order-independent.
        assert_eq!(root, poseidon2::content_root(&site));
        let reordered = SiteContent::new()
            .with(
                "/style.css",
                "body{font-family:system-ui;margin:3rem;max-width:40rem}",
            )
            .with(
                "/index.html",
                "<!doctype html><html><head><link rel=\"stylesheet\" href=\"/style.css\">\
                 <title>hosted on dregg.works</title></head>\
                 <body><h1>hello from a dregg cell</h1>\
                 <p>this minisite is backed by a published site cell.</p></body></html>",
            );
        assert_eq!(
            root,
            content_root(&reordered),
            "same content commits the same root"
        );

        // (c) a single flipped body byte, a moved path, and a changed content-type
        //     each move the wide root (the commitment binds all three).
        let flip_body = SiteContent::new()
            .with("/index.html", "<h1>hello from a dregg cell.</h1>")
            .with("/style.css", "body{}");
        let base2 = SiteContent::new()
            .with("/index.html", "<h1>hello from a dregg cell</h1>")
            .with("/style.css", "body{}");
        assert_ne!(
            content_root(&base2),
            content_root(&flip_body),
            "a flipped byte moves the root"
        );
        let moved_path = SiteContent::new()
            .with("/index2.html", "<h1>hello from a dregg cell</h1>")
            .with("/style.css", "body{}");
        assert_ne!(
            content_root(&base2),
            content_root(&moved_path),
            "a moved path moves the root"
        );
        let typed = SiteContent::new()
            .with_typed(
                "/index.html",
                "text/plain",
                "<h1>hello from a dregg cell</h1>",
            )
            .with("/style.css", "body{}");
        assert_ne!(
            content_root(&base2),
            content_root(&typed),
            "a changed content-type moves the root"
        );
    }

    #[test]
    fn publish_is_cap_gated() {
        let reg = SiteRegistry::new();
        // Right cap publishes.
        let r = reg
            .publish(&pub_cap("agent:ember", "blog"), "blog", sample_site())
            .expect("publish");
        assert_eq!(r.name, "blog");
        assert_eq!(r.owner, "agent:ember");
        assert_eq!(r.asset_count, 2);
        assert_eq!(r.seq, 0);

        // A cap for a different site cannot publish `blog`.
        let wrong = pub_cap("agent:ember", "shop");
        assert_eq!(
            reg.publish(&wrong, "blog", sample_site()),
            Err(PublishError::CapRefused {
                cap: "site-host/shop".into(),
                name: "blog".into()
            }),
        );

        // Empty content is refused.
        assert_eq!(
            reg.publish(&pub_cap("a", "empty"), "empty", SiteContent::new()),
            Err(PublishError::EmptyContent),
        );

        // Invalid name is refused.
        assert!(matches!(
            reg.publish(&pub_cap("a", "Bad.Name"), "Bad.Name", sample_site()),
            Err(PublishError::InvalidName(_)),
        ));
    }

    #[test]
    fn signed_publishes_form_a_verifiable_receipt_chain() {
        use dreggnet_receipt::{ChainError, verify_chain};

        // A signed registry seals each publish into a prev-hash-chained,
        // ed25519-signed stream — a publish IS a turn, this is its receipt.
        let reg = SiteRegistry::signed([5u8; 32]);
        let r0 = reg
            .publish(&pub_cap("agent:ember", "blog"), "blog", sample_site())
            .unwrap();
        let r1 = reg
            .publish(&pub_cap("agent:ember", "shop"), "shop", sample_site())
            .unwrap();
        let r2 = reg
            .publish(&pub_cap("agent:ember", "docs"), "docs", sample_site())
            .unwrap();

        // Each is signed; the chain links and verifies for a non-witness.
        assert!(r0.attest.is_some());
        let chain = vec![r0.clone(), r1.clone(), r2.clone()];
        assert_eq!(verify_chain(&chain), Ok(()));
        assert!(r0.attest.as_ref().unwrap().prev_receipt_hash.is_none());
        assert_eq!(
            r1.attest.as_ref().unwrap().prev_receipt_hash,
            r0.receipt_hash()
        );
        assert_eq!(
            reg.receipt_signer(),
            Some(r0.attest.as_ref().unwrap().signer)
        );

        // Tampering the recorded content_root invalidates the signature.
        let mut forged = r1.clone();
        forged.content_root = "deadbeef".into();
        assert_eq!(
            verify_chain(&[r0.clone(), forged, r2.clone()]),
            Err(ChainError::BadSignature { seq: 1 }),
        );

        // The free/local default leaves a bare (unsigned) projection.
        let free = SiteRegistry::new();
        let f = free
            .publish(&pub_cap("a", "x"), "x", sample_site())
            .unwrap();
        assert!(f.attest.is_none());
    }

    #[test]
    fn directory_request_serves_index() {
        let content = sample_site();
        // `/` serves index.html
        assert_eq!(
            content.resolve("/").map(|a| a.content_type.as_str()),
            Some("text/html; charset=utf-8"),
        );
        // exact asset
        assert_eq!(
            content
                .resolve("/style.css")
                .map(|a| a.content_type.as_str()),
            Some("text/css; charset=utf-8"),
        );
        // a miss
        assert!(content.resolve("/missing").is_none());
    }

    #[test]
    fn publish_then_resolve_round_trip() {
        let reg = SiteRegistry::new();
        reg.publish(&pub_cap("agent:ember", "blog"), "blog", sample_site())
            .expect("publish");

        // Serve the index over the host resolver.
        let resp = reg.resolve("blog.dregg.works", &WebRequest::get("/"));
        assert_eq!(resp.status, 200);
        assert_eq!(resp.content_type, "text/html; charset=utf-8");
        assert!(resp.body_str().contains("hello from a dregg cell"));

        // Serve the stylesheet with the right content-type.
        let css = reg.resolve("blog.dregg.works", &WebRequest::get("/style.css"));
        assert_eq!(css.status, 200);
        assert_eq!(css.content_type, "text/css; charset=utf-8");

        // Unknown site → 404.
        let miss = reg.resolve("nope.dregg.works", &WebRequest::get("/"));
        assert_eq!(miss.status, 404);

        // Unknown path on a known site → 404.
        let miss2 = reg.resolve("blog.dregg.works", &WebRequest::get("/nope"));
        assert_eq!(miss2.status, 404);
    }

    #[test]
    fn republish_replaces_with_new_root() {
        let reg = SiteRegistry::new();
        let cap = pub_cap("agent:ember", "blog");
        let r1 = reg.publish(&cap, "blog", sample_site()).unwrap();
        let r2 = reg
            .publish(
                &cap,
                "blog",
                SiteContent::new().with("/index.html", "<h1>v2</h1>"),
            )
            .unwrap();
        assert_ne!(r1.content_root, r2.content_root);
        assert_eq!(r2.seq, 1);
        let resp = reg.resolve("blog", &WebRequest::get("/"));
        assert!(resp.body_str().contains("v2"));
    }

    #[test]
    fn serving_accrues_bandwidth_per_site() {
        let bw = Arc::new(BandwidthMeter::new());
        let reg = SiteRegistry::with_bandwidth(Arc::clone(&bw));
        reg.publish(&pub_cap("agent:ember", "blog"), "blog", sample_site())
            .expect("publish");

        // Each successful serve records its delivered body bytes against the site.
        let r1 = reg.resolve("blog.dregg.works", &WebRequest::get("/"));
        assert_eq!(r1.status, 200);
        let r2 = reg.resolve("blog.dregg.works", &WebRequest::get("/style.css"));
        assert_eq!(r2.status, 200);
        let expected = r1.body.len() as u64 + r2.body.len() as u64;
        assert_eq!(bw.served("blog"), expected);
        assert_eq!(bw.unbilled("blog"), expected);

        // HB-2: a miss (404) IS billable egress now — its delivered body bytes accrue,
        // so error responses are no longer free.
        let miss = reg.resolve("blog.dregg.works", &WebRequest::get("/nope"));
        assert_eq!(miss.status, 404);
        let after_miss = expected + miss.body.len() as u64;
        assert_eq!(
            bw.served("blog"),
            after_miss,
            "a 404 body accrues bandwidth (HB-2)"
        );

        // The billing cursor advances only by what was settled (no double-count).
        bw.mark_billed("blog", after_miss);
        assert_eq!(bw.unbilled("blog"), 0);
        // A re-serve accrues fresh unbilled bytes.
        let r3 = reg.resolve("blog.dregg.works", &WebRequest::get("/"));
        assert_eq!(bw.unbilled("blog"), r3.body.len() as u64);
    }

    /// HB-2: error egress is metered and the reflected 404 path is bounded — a long
    /// `GET /<huge>` cannot be a free amplification vector. The 402 refusals (lapse /
    /// over-budget) are the system's "stop" and are NOT billed.
    #[test]
    fn error_egress_is_metered_and_the_404_reflection_is_bounded() {
        let bw = Arc::new(BandwidthMeter::new());
        let reg = SiteRegistry::with_bandwidth(Arc::clone(&bw));
        reg.publish(&pub_cap("agent:ember", "blog"), "blog", sample_site())
            .expect("publish");

        // A huge request path: the 404 body is BOUNDED (no large-path amplification),
        // and the bytes that ARE delivered are metered (not free).
        let huge = format!("/{}", "a".repeat(100_000));
        let miss = reg.resolve("blog.dregg.works", &WebRequest::get(&huge));
        assert_eq!(miss.status, 404);
        assert!(
            miss.body.len() < 1_000,
            "the reflected 404 body is bounded, not ~100KB"
        );
        assert_eq!(
            bw.served("blog"),
            miss.body.len() as u64,
            "the 404 egress is metered"
        );

        // A 402 refusal (lapsed) is the system's stop — not billed.
        bw.lapse("blog");
        let before = bw.served("blog");
        let refused = reg.resolve("blog.dregg.works", &WebRequest::get("/"));
        assert_eq!(refused.status, 402);
        assert_eq!(bw.served("blog"), before, "a 402 refusal is not billed");
    }

    #[test]
    fn a_lapsed_site_stops_serving() {
        let bw = Arc::new(BandwidthMeter::new());
        let reg = SiteRegistry::with_bandwidth(Arc::clone(&bw));
        reg.publish(&pub_cap("agent:ember", "blog"), "blog", sample_site())
            .expect("publish");

        // Live: serves normally.
        assert_eq!(
            reg.resolve("blog.dregg.works", &WebRequest::get("/"))
                .status,
            200
        );

        // Lapse (budget exhausted): serving is refused with 402, and no bytes accrue.
        let served_before = bw.served("blog");
        bw.lapse("blog");
        let lapsed = reg.resolve("blog.dregg.works", &WebRequest::get("/"));
        assert_eq!(lapsed.status, 402);
        assert!(lapsed.body_str().contains("lapsed"));
        assert_eq!(
            bw.served("blog"),
            served_before,
            "a lapsed serve accrues nothing"
        );

        // Reinstated (top-up): serving resumes.
        bw.reinstate("blog");
        assert_eq!(
            reg.resolve("blog.dregg.works", &WebRequest::get("/"))
                .status,
            200
        );
    }

    /// HB-1 / #10: the serving path enforces the funded byte budget IN-BAND — a
    /// bandwidth burst is bounded the moment it would exceed coverage, without waiting
    /// for a post-paid roll-up sweep to lapse the site. The over-budget body is never
    /// delivered (no free egress) and accrues no billable bandwidth.
    #[test]
    fn serving_refuses_in_band_once_the_funded_budget_is_exceeded() {
        let bw = Arc::new(BandwidthMeter::new());
        let reg = SiteRegistry::with_bandwidth(Arc::clone(&bw));
        reg.publish(&pub_cap("agent:ember", "blog"), "blog", sample_site())
            .expect("publish");

        // One index serve to size the body, then fund a budget that covers exactly ONE
        // more such serve (the high-water authorization the control plane sets).
        let probe = reg.resolve("blog.dregg.works", &WebRequest::get("/"));
        assert_eq!(probe.status, 200);
        let body = probe.body.len() as u64;
        let served_so_far = bw.served("blog");
        bw.set_budget("blog", served_so_far + body); // room for exactly one more

        // The next serve fits (served == budget): delivered + recorded.
        let ok = reg.resolve("blog.dregg.works", &WebRequest::get("/"));
        assert_eq!(ok.status, 200);
        assert_eq!(bw.served("blog"), served_so_far + body);

        // The bomb: the following serve would exceed the funded budget → 402 IN-BAND,
        // with NO lapse() call and NO roll-up sweep. The body is not delivered.
        let bomb = reg.resolve("blog.dregg.works", &WebRequest::get("/"));
        assert_eq!(
            bomb.status, 402,
            "in-band budget gate refuses before delivery"
        );
        assert!(
            !bw.is_lapsed("blog"),
            "the in-band gate did not need a lapse sweep"
        );
        assert_eq!(
            bw.served("blog"),
            served_so_far + body,
            "the refused (over-budget) response accrues no bandwidth"
        );

        // A coverage top-up lifts the ceiling and serving resumes in-band.
        bw.add_budget("blog", body);
        let resumed = reg.resolve("blog.dregg.works", &WebRequest::get("/"));
        assert_eq!(resumed.status, 200, "a top-up resumes serving in-band");
    }
}
