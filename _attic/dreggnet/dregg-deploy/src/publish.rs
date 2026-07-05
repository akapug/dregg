//! `publish` — step ④: a built `dist/` tree → a published [`SiteCell`].
//!
//! Walks the `dist/` tree into a [`SiteContent`] (content-types inferred per file), **injects
//! the source commitment** as a `/.well-known/dregg-deploy.json` manifest asset, and publishes
//! through [`SiteRegistry::publish`] (cap-gated, receipted). Because the manifest asset is part
//! of the content, the commit hash is folded into the cell's `content_root` commitment — so the
//! published cell itself carries, re-witnessably, *which commit it was built from*.

use std::path::Path;

use serde::{Deserialize, Serialize};

use dreggnet_webapp::hosting::{Asset, PublishCap, PublishReceipt, SiteContent, SiteRegistry};

/// Where the injected source-commitment manifest lands within the published site.
pub const DEPLOY_MANIFEST_PATH: &str = "/.well-known/dregg-deploy.json";

/// The source-commitment manifest committed into the published cell.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DeployManifestAsset {
    /// The repo the site was built from.
    pub repo: String,
    /// The full commit hash the build was pinned at (the source commitment).
    pub commit: String,
    /// The build plan that produced the published tree (`static`/`command`/`compute`).
    pub build_plan: String,
    /// The published subdomain label.
    pub site: String,
}

/// Walk `dist_dir` into a [`SiteContent`], inferring each file's content-type from its path.
/// Keys are absolute request paths rooted at the dist root (e.g. `dist/css/x.css` →
/// `/css/x.css`).
pub fn dist_to_content(dist_dir: &Path) -> anyhow::Result<SiteContent> {
    let mut content = SiteContent::new();
    walk(dist_dir, dist_dir, &mut content)?;
    if content.is_empty() {
        anyhow::bail!("dist `{}` has no files to publish", dist_dir.display());
    }
    Ok(content)
}

fn walk(root: &Path, dir: &Path, content: &mut SiteContent) -> anyhow::Result<()> {
    for entry in
        std::fs::read_dir(dir).map_err(|e| anyhow::anyhow!("read {}: {e}", dir.display()))?
    {
        let entry = entry?;
        let path = entry.path();
        // Refuse symlinks (D-2): never follow a symlink to read a host/other-tenant file's
        // bytes into the published content. The build's `copy_tree` already refuses them at
        // staging; this is the defense-in-depth tooth at the publish walk.
        let md = std::fs::symlink_metadata(&path)
            .map_err(|e| anyhow::anyhow!("stat {}: {e}", path.display()))?;
        if md.file_type().is_symlink() {
            anyhow::bail!(
                "refusing to publish symlink `{}` — symlinks are not followed into served content",
                path.display()
            );
        }
        if md.is_dir() {
            walk(root, &path, content)?;
        } else {
            let rel = path
                .strip_prefix(root)
                .map_err(|e| anyhow::anyhow!("strip prefix: {e}"))?;
            let key = format!("/{}", rel.to_string_lossy().replace('\\', "/"));
            let body = std::fs::read(&path)
                .map_err(|e| anyhow::anyhow!("read {}: {e}", path.display()))?;
            *content = std::mem::take(content).into_with_asset(&key, Asset::at(&key, body));
        }
    }
    Ok(())
}

/// Publish a built `dist_dir` as the site `name` for `owner`, injecting the source-commitment
/// manifest. Returns the [`PublishReceipt`] — whose `content_root` now commits to the manifest
/// (and thus the commit hash) too.
pub fn publish_dist(
    registry: &SiteRegistry,
    owner: &str,
    name: &str,
    dist_dir: &Path,
    manifest: &DeployManifestAsset,
) -> anyhow::Result<PublishReceipt> {
    let mut content = dist_to_content(dist_dir)?;
    let manifest_json = serde_json::to_vec_pretty(manifest)?;
    content = content.with_typed(DEPLOY_MANIFEST_PATH, "application/json", manifest_json);

    let cap = PublishCap::for_site(owner, name);
    registry
        .publish(&cap, name, content)
        .map_err(|e| anyhow::anyhow!("publish site `{name}`: {e}"))
}

/// A small extension so `walk` can fold assets into a `SiteContent` without re-borrowing.
trait SiteContentExt {
    fn into_with_asset(self, key: &str, asset: Asset) -> SiteContent;
}

impl SiteContentExt for SiteContent {
    fn into_with_asset(mut self, key: &str, asset: Asset) -> SiteContent {
        self.assets.insert(normalize_key(key), asset);
        self
    }
}

/// Normalize a request/content path the same way `dreggnet-webapp::hosting` does: `/` →
/// `/index.html`; a trailing slash → `…/index.html`; ensure a leading `/`.
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

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_webapp::WebRequest;
    use dreggnet_webapp::hosting::SiteRegistry;

    fn write(dir: &Path, rel: &str, body: &str) {
        let p = dir.join(rel);
        if let Some(parent) = p.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(p, body).unwrap();
    }

    #[test]
    fn dist_tree_becomes_content_with_types() {
        let dist = tempfile::tempdir().unwrap();
        write(dist.path(), "index.html", "<h1>hi</h1>");
        write(dist.path(), "css/app.css", "body{}");
        let content = dist_to_content(dist.path()).unwrap();
        assert_eq!(
            content.resolve("/").map(|a| a.content_type.as_str()),
            Some("text/html; charset=utf-8")
        );
        assert_eq!(
            content
                .resolve("/css/app.css")
                .map(|a| a.content_type.as_str()),
            Some("text/css; charset=utf-8")
        );
    }

    /// D-2: a symlink in the dist tree is refused at the publish walk (defense-in-depth),
    /// so a host/other-tenant file's bytes are never served.
    #[cfg(unix)]
    #[test]
    fn dist_symlink_is_refused_by_the_walk() {
        let dist = tempfile::tempdir().unwrap();
        write(dist.path(), "index.html", "<h1>hi</h1>");
        std::os::unix::fs::symlink("/etc/passwd", dist.path().join("creds")).unwrap();
        let err = dist_to_content(dist.path()).unwrap_err();
        assert!(
            err.to_string().contains("refusing to publish symlink"),
            "got {err}"
        );
    }

    #[test]
    fn publish_injects_the_commit_into_content_root() {
        let dist = tempfile::tempdir().unwrap();
        write(dist.path(), "index.html", "<h1>hi</h1>");
        let registry = SiteRegistry::new();
        let manifest = DeployManifestAsset {
            repo: "file:///fixture".into(),
            commit: "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef".into(),
            build_plan: "static".into(),
            site: "blog".into(),
        };
        let receipt =
            publish_dist(&registry, "agent:ember", "blog", dist.path(), &manifest).unwrap();
        assert_eq!(receipt.owner, "agent:ember");
        assert_eq!(receipt.name, "blog");
        // index.html + the injected manifest = 2 assets.
        assert_eq!(receipt.asset_count, 2);

        // The committed manifest is served, and carries the commit.
        let resp = registry.resolve("blog.example.com", &WebRequest::get(DEPLOY_MANIFEST_PATH));
        assert_eq!(resp.status, 200);
        let served: DeployManifestAsset = serde_json::from_slice(&resp.body).unwrap();
        assert_eq!(served.commit, manifest.commit);

        // A different commit moves the content_root (the commit is bound into the commitment).
        let registry2 = SiteRegistry::new();
        let mut m2 = manifest.clone();
        m2.commit = "0000000000000000000000000000000000000000".into();
        let r2 = publish_dist(&registry2, "agent:ember", "blog", dist.path(), &m2).unwrap();
        assert_ne!(
            receipt.content_root, r2.content_root,
            "commit binds the content_root"
        );
    }
}
