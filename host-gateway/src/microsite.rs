//! The static microsite data plane — published sites served by `Host`.
//!
//! A **microsite** is a named bundle of content-addressed assets owned by a subject.
//! The [`SiteRegistry`] resolves an inbound `Host` — the wildcard `<name>.<apex>`
//! (the deployment's configured hosting apex) — to a published site and serves its
//! assets. Every asset is committed by its [`Cid`] (a whole-blob blake3 address), and
//! a site's [`Microsite::content_root`] is the CID over its canonical
//! `path -> asset-CID` manifest — so a site's content is a single content-addressed
//! commitment a light client can re-witness.
//!
//! This is both the static serving plane the assembled gateway routes wildcard hosts
//! (and verified custom domains) to, AND the live source the cap-scoped `/api/sites`
//! read aggregates (owner-scoped).
//!
//! Publishing is owner-scoped: a site records the publishing `owner`, and a republish
//! by a different subject is refused (no takeover) — the same shape the custom-domain
//! binding enforces on-cell.

use std::collections::BTreeMap;
use std::sync::Mutex;

use dregg_ipfs::Cid;
use http_serve::WebResponse;

use crate::content::address;

/// One published asset: its declared content-type and its raw bytes. The asset's
/// content address is [`Asset::cid`] (a whole-blob blake3 CID).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Asset {
    /// The `Content-Type` served for this asset.
    pub content_type: String,
    /// The raw asset bytes.
    pub body: Vec<u8>,
}

impl Asset {
    /// A new asset with an explicit content-type.
    pub fn new(content_type: impl Into<String>, body: impl Into<Vec<u8>>) -> Asset {
        Asset {
            content_type: content_type.into(),
            body: body.into(),
        }
    }

    /// An asset whose content-type is inferred from `path`'s extension (the common
    /// static-file case).
    pub fn at(path: &str, body: impl Into<Vec<u8>>) -> Asset {
        Asset::new(content_type_for(path), body)
    }

    /// The content address of this asset's bytes (a CIDv1, blake3 multihash).
    pub fn cid(&self) -> Cid {
        address(&self.body)
    }
}

/// A published site: a named, owner-scoped bundle of content-addressed assets keyed by
/// request path (`/index.html`, `/style.css`, …).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Microsite {
    /// The site `<name>` (its `<name>.<apex>` host serves the bytes).
    pub name: String,
    /// The owner subject the `/api/sites` read scopes on (and the republish gate).
    pub owner: String,
    /// The site's assets keyed by request path.
    pub assets: BTreeMap<String, Asset>,
}

impl Microsite {
    /// A new, empty site owned by `owner`.
    pub fn new(name: impl Into<String>, owner: impl Into<String>) -> Microsite {
        Microsite {
            name: name.into(),
            owner: owner.into(),
            assets: BTreeMap::new(),
        }
    }

    /// Add an asset at `path` (content-type inferred from the extension). Builder form.
    pub fn with(mut self, path: impl Into<String>, body: impl Into<Vec<u8>>) -> Microsite {
        let path = path.into();
        let asset = Asset::at(&path, body);
        self.assets.insert(path, asset);
        self
    }

    /// Add an asset at `path` with an explicit content-type. Builder form.
    pub fn with_asset(mut self, path: impl Into<String>, asset: Asset) -> Microsite {
        self.assets.insert(path.into(), asset);
        self
    }

    /// Total served bytes across all assets.
    pub fn bytes(&self) -> u64 {
        self.assets.values().map(|a| a.body.len() as u64).sum()
    }

    /// The site's **content root** — the CID over its canonical `path\0cid\n` manifest.
    /// A single content-addressed commitment binding the whole site's content, so two
    /// sites with identical content share a root and any asset change moves the root.
    pub fn content_root(&self) -> Cid {
        let mut manifest = Vec::new();
        for (path, asset) in &self.assets {
            manifest.extend_from_slice(path.as_bytes());
            manifest.push(0);
            manifest.extend_from_slice(asset.cid().to_string_cid().as_bytes());
            manifest.push(b'\n');
        }
        address(&manifest)
    }

    /// Serve `path` against this site's assets. An empty path or `/` serves
    /// `/index.html`; an unknown path is a `404`.
    pub fn serve(&self, path: &str) -> WebResponse {
        let key = if path.is_empty() || path == "/" {
            "/index.html"
        } else {
            path
        };
        match self.assets.get(key) {
            Some(asset) => WebResponse {
                status: 200,
                content_type: asset.content_type.clone(),
                body: asset.body.clone(),
            },
            None => WebResponse::error(404, format!("no asset at `{key}`")),
        }
    }
}

/// Why a publish was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SiteError {
    /// `name` is not a valid single-label site name (empty, has a dot, or a bad char).
    InvalidName(String),
    /// A republish of an existing site by a subject that is not its owner (no takeover).
    OwnerMismatch { name: String },
}

impl std::fmt::Display for SiteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SiteError::InvalidName(n) => write!(f, "`{n}` is not a valid site name"),
            SiteError::OwnerMismatch { name } => {
                write!(f, "only the owner of site `{name}` may republish it")
            }
        }
    }
}

impl std::error::Error for SiteError {}

/// The registry of published microsites — the wildcard `<name>.<apex>` data plane and
/// the live source for the cap-scoped `/api/sites` read.
pub struct SiteRegistry {
    sites: Mutex<BTreeMap<String, Microsite>>,
    apex: String,
}

impl SiteRegistry {
    /// A fresh registry serving `<name>.<apex>` for the deployment's hosting `apex`
    /// (e.g. `dregg.net`, `dregg.fg-goose.online`). The apex is normalized (leading
    /// dot / trailing dot stripped, lowercased).
    pub fn new(apex: impl AsRef<str>) -> SiteRegistry {
        SiteRegistry {
            sites: Mutex::new(BTreeMap::new()),
            apex: normalize_apex(apex.as_ref()),
        }
    }

    /// The deployment's configured hosting apex.
    pub fn apex(&self) -> &str {
        &self.apex
    }

    /// Publish (or owner-republish) `site` — returns its content root. A republish by a
    /// different subject is refused ([`SiteError::OwnerMismatch`]); an invalid site name
    /// is [`SiteError::InvalidName`].
    pub fn publish(&self, site: Microsite) -> Result<Cid, SiteError> {
        let name = site.name.trim().to_ascii_lowercase();
        if !is_valid_label(&name) {
            return Err(SiteError::InvalidName(name));
        }
        let mut guard = self.sites.lock().expect("sites poisoned");
        if let Some(existing) = guard.get(&name) {
            if existing.owner != site.owner {
                return Err(SiteError::OwnerMismatch { name });
            }
        }
        let root = site.content_root();
        let mut site = site;
        site.name = name.clone();
        guard.insert(name, site);
        Ok(root)
    }

    /// A clone of the published site `<name>`, if any.
    pub fn get(&self, name: &str) -> Option<Microsite> {
        self.sites
            .lock()
            .expect("sites poisoned")
            .get(&name.trim().to_ascii_lowercase())
            .cloned()
    }

    /// All published site names, sorted.
    pub fn names(&self) -> Vec<String> {
        self.sites
            .lock()
            .expect("sites poisoned")
            .keys()
            .cloned()
            .collect()
    }

    /// All published sites, sorted by name (a snapshot).
    pub fn list(&self) -> Vec<Microsite> {
        self.sites
            .lock()
            .expect("sites poisoned")
            .values()
            .cloned()
            .collect()
    }

    /// Resolve an inbound wildcard `Host` (`<name>.<apex>`) to a **published** site
    /// name. Strips a `:port`, lowercases, and requires the label before `.<apex>` to
    /// be a single published label. `None` for a non-apex host or an unpublished name.
    pub fn site_for_host(&self, host: &str) -> Option<String> {
        let name = self.name_from_host(host)?;
        self.get(&name).map(|s| s.name)
    }

    /// The candidate site `<name>` a wildcard `Host` addresses — the label before
    /// `.<apex>` when it is a single label — WITHOUT requiring the site to exist (the
    /// on-demand-TLS `ask` uses this to check existence separately).
    pub fn name_from_host(&self, host: &str) -> Option<String> {
        let bare = host
            .split(':')
            .next()
            .unwrap_or(host)
            .trim()
            .to_ascii_lowercase();
        let suffix = format!(".{}", self.apex);
        let name = bare.strip_suffix(&suffix)?;
        // Exactly one label under the apex (`blog.<apex>`, not `a.b.<apex>`).
        if name.is_empty() || name.contains('.') {
            return None;
        }
        Some(name.to_string())
    }

    /// Whether `host` is a served wildcard host (a published `<name>.<apex>`).
    pub fn serves_host(&self, host: &str) -> bool {
        self.site_for_host(host).is_some()
    }

    /// Serve `path` for the wildcard `Host`, or `404` if the host is not a published
    /// site.
    pub fn resolve(&self, host: &str, path: &str) -> WebResponse {
        match self.site_for_host(host) {
            Some(name) => match self.get(&name) {
                Some(site) => site.serve(path),
                None => WebResponse::error(404, "site vanished"),
            },
            None => WebResponse::error(404, format!("no site for host `{host}`")),
        }
    }
}

/// Normalize a hosting apex: trim, strip a leading/trailing dot, lowercase.
pub fn normalize_apex(apex: &str) -> String {
    apex.trim()
        .trim_start_matches('.')
        .trim_end_matches('.')
        .to_ascii_lowercase()
}

/// Whether `label` is a valid single DNS label (a site `<name>`): 1..=63 chars,
/// `[a-z0-9-]`, not starting/ending with `-`, no dots.
pub fn is_valid_label(label: &str) -> bool {
    let l = label.trim();
    if l.is_empty() || l.len() > 63 || l.contains('.') {
        return false;
    }
    if l.starts_with('-') || l.ends_with('-') {
        return false;
    }
    l.chars()
        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
}

/// Infer a `Content-Type` from a path's extension (the common static-file types).
pub fn content_type_for(path: &str) -> String {
    let ext = path.rsplit('.').next().unwrap_or("").to_ascii_lowercase();
    let ct = match ext.as_str() {
        "html" | "htm" => "text/html; charset=utf-8",
        "css" => "text/css; charset=utf-8",
        "js" | "mjs" => "text/javascript; charset=utf-8",
        "json" => "application/json",
        "svg" => "image/svg+xml",
        "png" => "image/png",
        "jpg" | "jpeg" => "image/jpeg",
        "gif" => "image/gif",
        "webp" => "image/webp",
        "ico" => "image/x-icon",
        "txt" | "md" => "text/plain; charset=utf-8",
        "wasm" => "application/wasm",
        _ => "application/octet-stream",
    };
    ct.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: &str = "dregg:aaaa0000aaaa0000";
    const BOB: &str = "dregg:bbbb1111bbbb1111";

    fn registry() -> SiteRegistry {
        SiteRegistry::new("dregg.net")
    }

    #[test]
    fn publishes_and_serves_by_wildcard_host() {
        let reg = registry();
        let site = Microsite::new("blog", ALICE)
            .with("/index.html", "<h1>hello</h1>")
            .with("/style.css", "h1{color:teal}");
        let root = reg.publish(site).expect("publish");
        assert!(!root.digest.is_empty());

        // The wildcard host resolves and serves the index (empty path -> /index.html).
        let resp = reg.resolve("blog.dregg.net", "/");
        assert_eq!(resp.status, 200);
        assert!(resp.content_type.starts_with("text/html"));
        assert_eq!(resp.body, b"<h1>hello</h1>");

        // The css asset serves with the inferred content-type.
        let css = reg.resolve("blog.dregg.net:443", "/style.css");
        assert_eq!(css.status, 200);
        assert!(css.content_type.starts_with("text/css"));

        // An unknown path 404s; an unknown host 404s.
        assert_eq!(reg.resolve("blog.dregg.net", "/nope").status, 404);
        assert_eq!(reg.resolve("nope.dregg.net", "/").status, 404);
        // A two-label host under the apex is not a wildcard site.
        assert!(reg.name_from_host("a.b.dregg.net").is_none());
    }

    #[test]
    fn republish_by_a_stranger_is_refused() {
        let reg = registry();
        reg.publish(Microsite::new("shop", ALICE).with("/index.html", "alice"))
            .expect("alice publishes");
        // Bob cannot take over alice's site name.
        assert_eq!(
            reg.publish(Microsite::new("shop", BOB).with("/index.html", "bob")),
            Err(SiteError::OwnerMismatch {
                name: "shop".into()
            }),
        );
        // Alice can republish her own site (new content -> new root).
        let r1 = reg.get("shop").unwrap().content_root();
        let r2 = reg
            .publish(Microsite::new("shop", ALICE).with("/index.html", "alice v2"))
            .expect("alice republishes");
        assert_ne!(r1, r2, "changed content moves the content root");
    }

    #[test]
    fn invalid_names_are_refused() {
        let reg = registry();
        assert!(matches!(
            reg.publish(Microsite::new("bad.name", ALICE)),
            Err(SiteError::InvalidName(_))
        ));
        assert!(matches!(
            reg.publish(Microsite::new("-bad", ALICE)),
            Err(SiteError::InvalidName(_))
        ));
    }

    #[test]
    fn content_root_is_deterministic_and_content_addressed() {
        let a = Microsite::new("s", ALICE).with("/index.html", "same");
        let b = Microsite::new("s", BOB).with("/index.html", "same");
        // The content root binds CONTENT, not owner — identical assets share a root.
        assert_eq!(a.content_root(), b.content_root());
    }
}
