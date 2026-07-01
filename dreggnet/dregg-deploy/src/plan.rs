//! `plan` — framework detection → a [`BuildPlan`].
//!
//! Detection is a small, explicit heuristic over a cloned working tree, overridable by a
//! `dregg.toml` manifest in the repo (or a caller-supplied override). It answers the one
//! question the deploy workflow's Build step needs: *how is this repo turned into a tree of
//! servable bytes?* — with no build step (a static site), with a build command run in a
//! cap-bounded tier (a node/bundler build), with a polyana compute workload run through the
//! exec tier (the wasm/Caged build), or — detected but routed elsewhere — a long-running
//! server (the persistent-servers lane, §3.3).

use std::path::Path;

use serde::{Deserialize, Serialize};

/// The sandbox grade a build is authorized to run in — a serializable mirror of
/// [`dreggnet_exec::CapTier`] (so a [`BuildPlan`] round-trips through the durable workflow's
/// JSON). An arbitrary repo's build is untrusted code, so the default is the strongest
/// sandbox the deploy is willing to grant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum BuildTier {
    /// wasmi pure-interpreter, in-process (numeric args). The lightest cap-bounded compute.
    Sandboxed,
    /// wasmtime Cranelift JIT, in-process, fuel-metered.
    JitSandboxed,
    /// OS-sandboxed native process (seccomp+Landlock on Linux). The default for an
    /// arbitrary repo's build command.
    Caged,
    /// Firecracker microVM — a separate guest kernel.
    MicroVm,
}

impl Default for BuildTier {
    fn default() -> Self {
        BuildTier::Caged
    }
}

impl BuildTier {
    /// The exec tier this build grade maps to.
    pub fn to_cap_tier(self) -> dreggnet_exec::CapTier {
        match self {
            BuildTier::Sandboxed => dreggnet_exec::CapTier::Sandboxed,
            BuildTier::JitSandboxed => dreggnet_exec::CapTier::JitSandboxed,
            BuildTier::Caged => dreggnet_exec::CapTier::Caged,
            BuildTier::MicroVm => dreggnet_exec::CapTier::MicroVm,
        }
    }

    /// Parse a tier label (`sandboxed`/`jit`/`caged`/`microvm`), defaulting to [`Caged`].
    pub fn parse(s: &str) -> Self {
        match s.trim().to_ascii_lowercase().as_str() {
            "sandboxed" => BuildTier::Sandboxed,
            "jit" | "jit-sandboxed" | "jitsandboxed" => BuildTier::JitSandboxed,
            "microvm" | "micro-vm" => BuildTier::MicroVm,
            _ => BuildTier::Caged,
        }
    }
}

/// How a cloned repo is turned into a tree of servable bytes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum BuildPlan {
    /// No build step — publish a directory of the cloned tree directly (a static site).
    /// Detected by an `index.html` at the publish root.
    Static {
        /// The directory within the repo to publish (`.` = the repo root).
        publish_dir: String,
    },
    /// Run a build command in a cap-bounded tier, then publish a configured output dir.
    /// Detected by a `package.json` carrying a `build` script (or set via `dregg.toml`).
    Command {
        /// The shell command to run (e.g. `npm run build`).
        command: String,
        /// The directory the build writes its servable output into (e.g. `dist`).
        output_dir: String,
        /// The sandbox grade the build runs in.
        #[serde(default)]
        tier: BuildTier,
    },
    /// Run a polyana program through the exec compute tier — the literal "build in the
    /// wasm/Caged tier" path — and write its output as a generated artifact. The genuinely
    /// cap-bounded, exec-metered build ([`dreggnet_exec::run_workload`]).
    Compute {
        /// The polyana provider family (`wat`/`wasm`/`python`/`node`).
        lang: String,
        /// The program source.
        source: String,
        /// The sandbox grade.
        #[serde(default)]
        tier: BuildTier,
        /// The path the generated output is written to within the published site
        /// (e.g. `index.html`).
        artifact: String,
    },
    /// A long-running server target (a `Dockerfile` or a declared server entry). Detected
    /// here so the heuristic is complete; the launch belongs to the persistent-servers lane
    /// (§3.3), so the deploy workflow refuses it with that pointer rather than publishing.
    Server {
        /// The server entrypoint (e.g. `server.js`, or `Dockerfile`).
        entry: String,
        /// The port the server listens on.
        port: u16,
    },
}

impl BuildPlan {
    /// A short label for receipts/logs (`static`/`command`/`compute`/`server`).
    pub fn label(&self) -> &'static str {
        match self {
            BuildPlan::Static { .. } => "static",
            BuildPlan::Command { .. } => "command",
            BuildPlan::Compute { .. } => "compute",
            BuildPlan::Server { .. } => "server",
        }
    }
}

/// A `dregg.toml` deploy manifest — the in-repo override of detection.
///
/// All fields optional; a present `[build]` section pins the [`BuildPlan`], a present
/// `[site]` section supplies a default site name.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct DeployManifest {
    #[serde(default)]
    pub site: Option<SiteManifest>,
    #[serde(default)]
    pub build: Option<BuildManifest>,
}

/// The `[site]` table of a `dregg.toml`.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct SiteManifest {
    /// The default subdomain label to publish under.
    pub name: Option<String>,
}

/// The `[build]` table of a `dregg.toml` — pins the build plan.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct BuildManifest {
    /// `static` | `command` | `compute` | `server`.
    pub kind: Option<String>,
    // static
    pub publish_dir: Option<String>,
    // command
    pub command: Option<String>,
    pub output_dir: Option<String>,
    pub tier: Option<String>,
    // compute
    pub lang: Option<String>,
    pub source: Option<String>,
    pub source_file: Option<String>,
    pub artifact: Option<String>,
    // server
    pub entry: Option<String>,
    pub port: Option<u16>,
}

/// The manifest file a repo carries to override detection.
pub const MANIFEST_FILE: &str = "dregg.toml";

/// Detect (or read the override / manifest for) the [`BuildPlan`] of the cloned repo at
/// `workdir`.
///
/// Resolution order: an explicit `override_plan` wins; else a `dregg.toml`'s `[build]`
/// section; else the heuristic — `Dockerfile`/server entry → [`BuildPlan::Server`];
/// `package.json` with a `build` script → [`BuildPlan::Command`]; an `index.html` at the
/// root → [`BuildPlan::Static`]. An undetectable repo is an error (an honest refusal, not a
/// guess).
pub fn detect(workdir: &Path, override_plan: Option<&BuildPlan>) -> anyhow::Result<BuildPlan> {
    if let Some(p) = override_plan {
        return Ok(p.clone());
    }
    if let Some(p) = from_manifest(workdir)? {
        return Ok(p);
    }
    // A Dockerfile or a conventional server entry → the server target.
    if workdir.join("Dockerfile").is_file() {
        return Ok(BuildPlan::Server {
            entry: "Dockerfile".to_string(),
            port: 8080,
        });
    }
    // A node project with a `build` script → a build command.
    let pkg = workdir.join("package.json");
    if pkg.is_file() {
        let text = std::fs::read_to_string(&pkg).unwrap_or_default();
        let has_build = serde_json::from_str::<serde_json::Value>(&text)
            .ok()
            .and_then(|v| v.get("scripts").and_then(|s| s.get("build")).cloned())
            .is_some();
        if has_build {
            return Ok(BuildPlan::Command {
                command: "npm run build".to_string(),
                output_dir: "dist".to_string(),
                tier: BuildTier::default(),
            });
        }
        // A package.json without a build script but with an index.html → still static.
    }
    // A static site: an index.html at the root.
    if workdir.join("index.html").is_file() {
        return Ok(BuildPlan::Static {
            publish_dir: ".".to_string(),
        });
    }
    anyhow::bail!(
        "could not detect a project type in `{}` (no dregg.toml [build], no Dockerfile, \
         no package.json build script, no index.html). Add a dregg.toml to override.",
        workdir.display()
    )
}

/// Read + interpret a `dregg.toml` `[build]` section into a [`BuildPlan`], if present.
fn from_manifest(workdir: &Path) -> anyhow::Result<Option<BuildPlan>> {
    let path = workdir.join(MANIFEST_FILE);
    if !path.is_file() {
        return Ok(None);
    }
    let text = std::fs::read_to_string(&path)?;
    let manifest: DeployManifest =
        toml::from_str(&text).map_err(|e| anyhow::anyhow!("parse {MANIFEST_FILE}: {e}"))?;
    let Some(b) = manifest.build else {
        return Ok(None);
    };
    let kind = b.kind.as_deref().unwrap_or("static");
    let plan = match kind {
        "static" => BuildPlan::Static {
            publish_dir: b.publish_dir.unwrap_or_else(|| ".".to_string()),
        },
        "command" => BuildPlan::Command {
            command: b.command.ok_or_else(|| {
                anyhow::anyhow!("dregg.toml [build] kind=command needs `command`")
            })?,
            output_dir: b.output_dir.unwrap_or_else(|| "dist".to_string()),
            tier: b.tier.as_deref().map(BuildTier::parse).unwrap_or_default(),
        },
        "compute" => {
            let source = match (b.source, b.source_file) {
                (Some(s), _) => s,
                (None, Some(f)) => std::fs::read_to_string(workdir.join(&f))
                    .map_err(|e| anyhow::anyhow!("read source_file `{f}`: {e}"))?,
                (None, None) => {
                    anyhow::bail!("dregg.toml [build] kind=compute needs `source` or `source_file`")
                }
            };
            BuildPlan::Compute {
                lang: b.lang.unwrap_or_else(|| "wat".to_string()),
                source,
                tier: b.tier.as_deref().map(BuildTier::parse).unwrap_or_default(),
                artifact: b.artifact.unwrap_or_else(|| "index.html".to_string()),
            }
        }
        "server" => BuildPlan::Server {
            entry: b.entry.unwrap_or_else(|| "Dockerfile".to_string()),
            port: b.port.unwrap_or(8080),
        },
        other => anyhow::bail!("dregg.toml [build] unknown kind `{other}`"),
    };
    Ok(Some(plan))
}

/// Read a `dregg.toml`'s default site name, if any.
pub fn manifest_site_name(workdir: &Path) -> Option<String> {
    let text = std::fs::read_to_string(workdir.join(MANIFEST_FILE)).ok()?;
    let manifest: DeployManifest = toml::from_str(&text).ok()?;
    manifest.site.and_then(|s| s.name)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmp() -> tempfile::TempDir {
        tempfile::tempdir().unwrap()
    }

    #[test]
    fn detects_static_by_index_html() {
        let d = tmp();
        std::fs::write(d.path().join("index.html"), "<h1>hi</h1>").unwrap();
        assert_eq!(
            detect(d.path(), None).unwrap(),
            BuildPlan::Static {
                publish_dir: ".".to_string()
            }
        );
    }

    #[test]
    fn detects_node_command_by_build_script() {
        let d = tmp();
        std::fs::write(
            d.path().join("package.json"),
            r#"{"scripts":{"build":"vite build"}}"#,
        )
        .unwrap();
        match detect(d.path(), None).unwrap() {
            BuildPlan::Command {
                command,
                output_dir,
                tier,
            } => {
                assert_eq!(command, "npm run build");
                assert_eq!(output_dir, "dist");
                assert_eq!(tier, BuildTier::Caged);
            }
            other => panic!("expected command, got {other:?}"),
        }
    }

    #[test]
    fn detects_server_by_dockerfile() {
        let d = tmp();
        std::fs::write(d.path().join("Dockerfile"), "FROM scratch").unwrap();
        assert!(matches!(
            detect(d.path(), None).unwrap(),
            BuildPlan::Server { .. }
        ));
    }

    #[test]
    fn manifest_overrides_detection() {
        let d = tmp();
        // An index.html would heuristically be static, but the manifest pins compute.
        std::fs::write(d.path().join("index.html"), "<h1>hi</h1>").unwrap();
        std::fs::write(
            d.path().join(MANIFEST_FILE),
            "[site]\nname = \"blog\"\n[build]\nkind = \"compute\"\nlang = \"wat\"\n\
             source = \"(module)\"\ntier = \"sandboxed\"\nartifact = \"index.html\"\n",
        )
        .unwrap();
        match detect(d.path(), None).unwrap() {
            BuildPlan::Compute {
                lang,
                tier,
                artifact,
                ..
            } => {
                assert_eq!(lang, "wat");
                assert_eq!(tier, BuildTier::Sandboxed);
                assert_eq!(artifact, "index.html");
            }
            other => panic!("expected compute, got {other:?}"),
        }
        assert_eq!(manifest_site_name(d.path()).as_deref(), Some("blog"));
    }

    #[test]
    fn undetectable_repo_is_an_honest_error() {
        let d = tmp();
        std::fs::write(d.path().join("README.md"), "nothing servable").unwrap();
        assert!(detect(d.path(), None).is_err());
    }

    #[test]
    fn explicit_override_wins() {
        let d = tmp();
        let plan = BuildPlan::Static {
            publish_dir: "public".to_string(),
        };
        assert_eq!(detect(d.path(), Some(&plan)).unwrap(), plan);
    }
}
