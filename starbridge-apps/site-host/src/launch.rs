//! Launchpad composition — a launch gets a landing page, content-addressed.
//!
//! This is the wire from microsite hosting toward the launchpad: a token/app launch
//! carries a [`LaunchListing`] (name, ticker, description, an optional image); this
//! module turns it into a publishable [`SiteContent`] landing page AND
//! content-addresses the launch's metadata + image on IPFS ([`dregg_ipfs`]).
//!
//! Why IPFS: a dregg content commitment IS an IPFS CID (both are blake3-addressed),
//! so pinning the image/metadata gives a decentralized, verify-don't-trust address
//! for a launch's media that any gateway can serve while the site's `content_root`
//! still commits the exact served bytes. The landing page is then published through
//! the same cap-gated, lease-funded, receipted turn as any other site — so a launch
//! and its landing page share one control plane.

use dregg_ipfs::IpfsError;
use dregg_ipfs::bridge::pin_blob;
use dregg_ipfs::client::IpfsClient;
use serde::{Deserialize, Serialize};

use crate::registry::HostConfig;
use crate::site::SiteContent;

/// A launch as the launchpad hands it over — the inputs a landing page is built
/// from. Brand-neutral: no product strings, just the listing shape.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaunchListing {
    /// The site subdomain label (also the site name the publish cap must authorize).
    pub name: String,
    /// The display title.
    pub title: String,
    /// The token/app ticker or short symbol (optional).
    pub ticker: Option<String>,
    /// A one-paragraph description.
    pub description: String,
    /// The launch image bytes + a media type (optional). Pinned to IPFS and served.
    pub image: Option<LaunchImage>,
    /// Outbound links (label -> url), rendered into the page.
    pub links: Vec<(String, String)>,
}

/// A launch image: the bytes and its media type (e.g. `image/png`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaunchImage {
    pub content_type: String,
    pub body: Vec<u8>,
}

/// The content-addressed artifacts a landing-page build pinned to IPFS.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaunchAssets {
    /// The CID of the pinned launch image, if the listing carried one.
    pub image_cid: Option<String>,
    /// The CID of the pinned launch metadata JSON.
    pub metadata_cid: String,
}

/// The launch metadata document that is content-addressed on IPFS (the token/app
/// metadata a wallet/indexer reads), committed by CID into the landing page.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LaunchMetadata {
    pub name: String,
    pub title: String,
    pub ticker: Option<String>,
    pub description: String,
    /// The IPFS CID of the image (an `ipfs://…` address), if any.
    pub image: Option<String>,
    pub links: Vec<(String, String)>,
}

/// Build a publishable landing page for `listing`, content-addressing its image and
/// metadata on IPFS via `ipfs`.
///
/// Pins (1) the image bytes (if any) and (2) a canonical [`LaunchMetadata`] JSON,
/// then assembles a self-contained `SiteContent`:
///   * `/index.html` — the landing page, referencing the image by its local path
///     (served bytes, committed in `content_root`) with the IPFS CID recorded in
///     `/metadata.json` for a decentralized fetch;
///   * the image asset at `/media/<image>` (when present);
///   * `/metadata.json` — the content-addressed launch metadata (same bytes as the
///     pinned CID).
///
/// Returns the content plus the [`LaunchAssets`] CIDs. `cfg` supplies the apex for
/// the canonical URL rendered on the page.
pub fn landing_page<C: IpfsClient>(
    listing: &LaunchListing,
    ipfs: &C,
    cfg: &HostConfig,
) -> Result<(SiteContent, LaunchAssets), IpfsError> {
    // (1) Pin the image, content-addressed.
    let (image_cid, image_path, image_ct) = match &listing.image {
        Some(img) => {
            let cid = pin_blob(ipfs, &img.body)?;
            let ext = ext_for(&img.content_type);
            let path = format!("/media/launch.{ext}");
            (
                Some(cid.to_string_cid()),
                Some((path, img.clone())),
                Some(img.content_type.clone()),
            )
        }
        None => (None, None, None),
    };
    let _ = image_ct;

    // (2) Build + pin the canonical metadata JSON (the CID an indexer/wallet reads).
    let metadata = LaunchMetadata {
        name: listing.name.clone(),
        title: listing.title.clone(),
        ticker: listing.ticker.clone(),
        description: listing.description.clone(),
        image: image_cid.as_ref().map(|c| format!("ipfs://{c}")),
        links: listing.links.clone(),
    };
    let metadata_json = serde_json::to_vec_pretty(&metadata).expect("LaunchMetadata serializes");
    let metadata_cid = pin_blob(ipfs, &metadata_json)?.to_string_cid();

    // (3) Assemble the landing page.
    let local_image = image_path.as_ref().map(|(p, _)| p.clone());
    let html = render_landing_html(listing, cfg, local_image.as_deref(), &metadata_cid);
    let mut content = SiteContent::new().with("/index.html", html);
    if let Some((path, img)) = &image_path {
        content = content.with_typed(path, img.content_type.clone(), img.body.clone());
    }
    content = content.with_typed("/metadata.json", "application/json", metadata_json);

    Ok((
        content,
        LaunchAssets {
            image_cid,
            metadata_cid,
        },
    ))
}

/// Render the landing page HTML. Minimal, self-contained (inline CSS), no external
/// requests — the served bytes are all committed in the site's `content_root`.
fn render_landing_html(
    listing: &LaunchListing,
    cfg: &HostConfig,
    local_image: Option<&str>,
    metadata_cid: &str,
) -> String {
    let title = escape(&listing.title);
    let ticker = listing
        .ticker
        .as_deref()
        .map(|t| format!(" <span class=\"ticker\">{}</span>", escape(t)))
        .unwrap_or_default();
    let desc = escape(&listing.description);
    let url = cfg.url_for(&listing.name);
    let img_tag = local_image
        .map(|p| {
            format!(
                "<img class=\"hero\" src=\"{}\" alt=\"{}\">",
                escape(p),
                title
            )
        })
        .unwrap_or_default();
    let links = if listing.links.is_empty() {
        String::new()
    } else {
        let items: String = listing
            .links
            .iter()
            .map(|(label, href)| {
                format!(
                    "<li><a href=\"{}\">{}</a></li>",
                    escape(href),
                    escape(label)
                )
            })
            .collect();
        format!("<ul class=\"links\">{items}</ul>")
    };

    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
<title>{title}</title>\
<style>body{{font-family:system-ui,sans-serif;margin:0;color:#111;background:#fafafa}}\
main{{max-width:44rem;margin:0 auto;padding:3rem 1.5rem}}\
.hero{{max-width:100%;border-radius:12px}}\
h1{{font-size:2rem;margin:1rem 0 .25rem}}\
.ticker{{font-size:1rem;color:#666;font-weight:600}}\
p{{line-height:1.6;color:#333}}\
.links{{list-style:none;padding:0;display:flex;gap:.75rem;flex-wrap:wrap}}\
.links a{{text-decoration:none;padding:.5rem .9rem;border:1px solid #ddd;border-radius:8px;color:#111}}\
footer{{margin-top:2rem;font-size:.8rem;color:#888}}\
code{{font-size:.8rem}}</style></head>\
<body><main>{img_tag}<h1>{title}{ticker}</h1><p>{desc}</p>{links}\
<footer>served at <code>{url}</code> · metadata <code>ipfs://{metadata_cid}</code></footer>\
</main></body></html>"
    )
}

/// Minimal HTML-escape for attribute/text contexts.
fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

/// A file extension for a media type (for the served image path).
fn ext_for(content_type: &str) -> &'static str {
    match content_type.split(';').next().unwrap_or("").trim() {
        "image/png" => "png",
        "image/jpeg" => "jpg",
        "image/gif" => "gif",
        "image/webp" => "webp",
        "image/avif" => "avif",
        "image/svg+xml" => "svg",
        _ => "bin",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::site::content_root;
    use dregg_ipfs::client::MockIpfs;

    fn listing() -> LaunchListing {
        LaunchListing {
            name: "moontoken".to_string(),
            title: "Moon Token".to_string(),
            ticker: Some("MOON".to_string()),
            description: "a launch on the verified rail".to_string(),
            image: Some(LaunchImage {
                content_type: "image/png".to_string(),
                body: b"\x89PNG\r\n\x1a\nFAKE".to_vec(),
            }),
            links: vec![("home".to_string(), "https://example.test".to_string())],
        }
    }

    #[test]
    fn a_launch_builds_a_content_addressed_landing_page() {
        let ipfs = MockIpfs::new();
        let cfg = HostConfig::with_apex("example.test");
        let (content, assets) = landing_page(&listing(), &ipfs, &cfg).unwrap();

        // The page, the media, and the metadata are all present + committed.
        assert!(content.resolve("/").is_some(), "index.html present");
        assert!(
            content.resolve("/media/launch.png").is_some(),
            "image served"
        );
        assert!(
            content.resolve("/metadata.json").is_some(),
            "metadata served"
        );
        assert_eq!(content_root(&content).len(), 64, "real content commitment");

        // The image + metadata were pinned, content-addressed.
        let image_cid = assets.image_cid.expect("image pinned");
        assert!(
            image_cid.starts_with("bafk") || !image_cid.is_empty(),
            "a CID"
        );
        assert!(!assets.metadata_cid.is_empty(), "metadata pinned");

        // The metadata JSON that was pinned re-fetches from the mock node.
        let served = content.resolve("/metadata.json").unwrap();
        let meta: LaunchMetadata = serde_json::from_slice(&served.body).unwrap();
        assert_eq!(meta.ticker.as_deref(), Some("MOON"));
        assert_eq!(meta.image, Some(format!("ipfs://{image_cid}")));

        // The rendered page escapes + references the content-addressed metadata.
        let html = String::from_utf8(content.resolve("/").unwrap().body.clone()).unwrap();
        assert!(html.contains("Moon Token"));
        assert!(html.contains("MOON"), "ticker rendered");
        assert!(
            html.contains(&assets.metadata_cid),
            "metadata CID referenced on the page"
        );
    }

    #[test]
    fn a_launch_without_an_image_still_pins_metadata() {
        let ipfs = MockIpfs::new();
        let cfg = HostConfig::local();
        let mut l = listing();
        l.image = None;
        let (content, assets) = landing_page(&l, &ipfs, &cfg).unwrap();
        assert!(assets.image_cid.is_none());
        assert!(!assets.metadata_cid.is_empty());
        assert!(content.resolve("/media/launch.png").is_none());
    }
}
