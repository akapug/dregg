//! `build` — step ③: turn the cloned tree into a `dist/` of servable bytes, cap-bounded.
//!
//! The build is the one step that runs untrusted repo code, so it is **cap-bounded**:
//!
//! - [`BuildPlan::Compute`] runs a polyana program through [`dreggnet_exec::run_workload`] at
//!   a declared [`BuildTier`] — the genuinely sandboxed, exec-metered build (the literal
//!   "build in the wasm/Caged tier"). This is the path proven in-process end-to-end.
//! - [`BuildPlan::Command`] runs a build command (e.g. `npm run build`) as a wall-clock-
//!   bounded subprocess in the cloned workdir, at the declared tier. **Honest seam:** locally
//!   the command runs as a time-bounded subprocess so it can write its `dist/` tree; on a
//!   fleet node the same command + tier route through `dreggnet-exec`'s Caged/MicroVm tier —
//!   only the runner changes (the same in-process-vs-fleet split `dreggnet-durable` documents
//!   for its meter). Either way the build is *metered* against the deploy budget by the
//!   durable workflow's `MeterTick`, so a build that overruns its lease is reaped.
//! - [`BuildPlan::Static`] has no build step — it stages the published directory directly.
//!
//! Every path materializes its result into one canonical `dist_dir`, so the Publish step (and
//! a post-crash resume) reads a single, on-disk location.

use std::path::{Path, PathBuf};
use std::time::Duration;

use serde::{Deserialize, Serialize};

use crate::plan::BuildPlan;

/// The wall-clock bound on a build command, in seconds. Mirrors `dreggnet-exec`'s
/// `DREGGNET_EXEC_TIMEOUT_SECS` so the deploy build honors the same env knob.
const DEFAULT_BUILD_TIMEOUT_SECS: u64 = 300;

fn build_timeout() -> Duration {
    let secs = std::env::var("DREGGNET_EXEC_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .filter(|s| *s > 0)
        .unwrap_or(DEFAULT_BUILD_TIMEOUT_SECS);
    Duration::from_secs(secs)
}

/// The outcome of a build: which plan ran + how many files the `dist/` holds.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildOutcome {
    /// The build plan that ran (`static`/`command`/`compute`).
    pub plan_label: String,
    /// How many files landed in the published `dist/`.
    pub file_count: usize,
}

/// Run `plan` against the cloned `repo_dir`, materializing the servable output into
/// `dist_dir` (created fresh). Returns the [`BuildOutcome`].
///
/// A [`BuildPlan::Server`] is detected-but-not-handled here: it belongs to the persistent-
/// servers lane (§3.3), so this refuses it with that pointer rather than publishing a site.
pub fn run_build(
    plan: &BuildPlan,
    repo_dir: &Path,
    dist_dir: &Path,
) -> anyhow::Result<BuildOutcome> {
    // Fresh dist each build (idempotent: a replayed Build overwrites cleanly).
    if dist_dir.exists() {
        std::fs::remove_dir_all(dist_dir)
            .map_err(|e| anyhow::anyhow!("clear dist {}: {e}", dist_dir.display()))?;
    }
    std::fs::create_dir_all(dist_dir)
        .map_err(|e| anyhow::anyhow!("create dist {}: {e}", dist_dir.display()))?;

    match plan {
        BuildPlan::Static { publish_dir } => {
            // `publish_dir` is repo-controlled: confine it under the repo root (a `../..`
            // traversal or a symlink escaping the repo is refused — D-2).
            let src = safe_subpath(repo_dir, publish_dir)?;
            if !src.is_dir() {
                anyhow::bail!("static publish dir `{}` is not a directory", src.display());
            }
            copy_tree(&src, dist_dir)?;
        }
        BuildPlan::Command {
            command,
            output_dir,
            tier,
        } => {
            run_command_bounded(command, repo_dir, *tier)?;
            // The build's servable output. Try the configured dir, then common fallbacks.
            // Each candidate is confined under the repo root (D-2).
            let out = resolve_output_dir(repo_dir, output_dir)?;
            copy_tree(&out, dist_dir)?;
        }
        BuildPlan::Compute {
            lang,
            source,
            tier,
            artifact,
        } => {
            // The genuinely cap-bounded build: run the program through the exec tier.
            let output = dreggnet_exec::run_workload(lang, source, tier.to_cap_tier())
                .map_err(|e| anyhow::anyhow!("compute build (`{lang}` @ {tier:?}): {e}"))?;
            let body = output.values.join("\n");
            let dest = dist_dir.join(artifact.trim_start_matches('/'));
            if let Some(parent) = dest.parent() {
                std::fs::create_dir_all(parent).ok();
            }
            std::fs::write(&dest, body)
                .map_err(|e| anyhow::anyhow!("write compute artifact {}: {e}", dest.display()))?;
        }
        BuildPlan::Server { .. } => {
            anyhow::bail!(
                "this repo detected as a SERVER target; persistent servers are the §3.3 lane \
                 (`dregg deploy . --server`), not the site-publish deploy"
            );
        }
    }

    let file_count = count_files(dist_dir);
    if file_count == 0 {
        anyhow::bail!(
            "build produced no files in `{}` — nothing to publish",
            dist_dir.display()
        );
    }
    Ok(BuildOutcome {
        plan_label: plan.label().to_string(),
        file_count,
    })
}

/// Run a build command in the deny-default sandbox (D-1/D-3), bounded by the build timeout,
/// at the resource envelope `tier` selects. The build is untrusted repo code, so it runs
/// with a cleared environment (no host secrets), `HOME`/`TMPDIR` confined to the workdir, a
/// fresh process group (the whole tree — not just `sh` — is reaped on timeout/exit), and
/// resource rlimits (file-size, CPU; address-space + an empty network namespace on Linux).
/// The `tier` is honored here as that envelope; on a fleet node the same tier routes the
/// command through `dreggnet-exec`'s Caged (seccomp+Landlock) / MicroVm (Firecracker) tier,
/// the hard isolation boundary. It is no longer discarded.
fn run_command_bounded(
    command: &str,
    cwd: &Path,
    tier: crate::plan::BuildTier,
) -> anyhow::Result<()> {
    crate::sandbox::run_sandboxed_command(command, cwd, tier, build_timeout())
}

/// Resolve the build's output directory: the configured one, else a common fallback that
/// exists (`dist`/`build`/`out`/`public`). Every candidate is confined under the repo root —
/// a repo-controlled `output_dir = "../../etc"` (or a symlink escaping the repo) is refused
/// (D-2).
fn resolve_output_dir(repo_dir: &Path, configured: &str) -> anyhow::Result<PathBuf> {
    if let Ok(primary) = safe_subpath(repo_dir, configured) {
        if primary.is_dir() {
            return Ok(primary);
        }
    }
    for cand in ["dist", "build", "out", "public"] {
        if let Ok(p) = safe_subpath(repo_dir, cand) {
            if p.is_dir() {
                return Ok(p);
            }
        }
    }
    anyhow::bail!(
        "build output dir `{}` not found under the repo root (and no dist/build/out/public \
         fallback); a `..`-traversal or repo-escaping output dir is refused",
        repo_dir.join(configured).display()
    )
}

/// Resolve `rel` against `repo_dir` and refuse anything that escapes the repo root — a
/// repo-controlled `publish_dir`/`output_dir` is untrusted input (D-2). `canonicalize`
/// resolves `..` AND follows symlinks, so a `publish_dir` that is itself a symlink to
/// `/etc` lands outside the (canonicalized) repo root and is rejected. The path must exist.
fn safe_subpath(repo_dir: &Path, rel: &str) -> anyhow::Result<PathBuf> {
    let canon_root = repo_dir
        .canonicalize()
        .map_err(|e| anyhow::anyhow!("canonicalize repo dir {}: {e}", repo_dir.display()))?;
    let canon = repo_dir
        .join(rel)
        .canonicalize()
        .map_err(|e| anyhow::anyhow!("resolve `{rel}` under the repo root: {e}"))?;
    if !canon.starts_with(&canon_root) {
        anyhow::bail!(
            "path `{rel}` escapes the repo root ({} is not under {})",
            canon.display(),
            canon_root.display()
        );
    }
    Ok(canon)
}

/// Recursively copy `src` into `dst`, skipping `.git`. Both must exist (`dst` is the dist
/// root). **Refuses symlinks** (D-2): each entry is `symlink_metadata`'d, and a symlink is
/// an error rather than followed/copied — a repo symlink `dist/creds -> /etc` (or to another
/// tenant's tree) never has its target bytes copied into the servable site.
fn copy_tree(src: &Path, dst: &Path) -> anyhow::Result<()> {
    for entry in
        std::fs::read_dir(src).map_err(|e| anyhow::anyhow!("read {}: {e}", src.display()))?
    {
        let entry = entry?;
        let name = entry.file_name();
        if name == ".git" {
            continue;
        }
        let from = entry.path();
        let to = dst.join(&name);
        let md = std::fs::symlink_metadata(&from)
            .map_err(|e| anyhow::anyhow!("stat {}: {e}", from.display()))?;
        if md.file_type().is_symlink() {
            anyhow::bail!(
                "refusing to publish symlink `{}` — a build output symlink is not followed \
                 (it could read host/other-tenant files into the served site)",
                from.display()
            );
        }
        if md.is_dir() {
            std::fs::create_dir_all(&to)?;
            copy_tree(&from, &to)?;
        } else {
            if let Some(parent) = to.parent() {
                std::fs::create_dir_all(parent).ok();
            }
            std::fs::copy(&from, &to)
                .map_err(|e| anyhow::anyhow!("copy {} -> {}: {e}", from.display(), to.display()))?;
        }
    }
    Ok(())
}

/// Count the regular files under `root` (recursively).
fn count_files(root: &Path) -> usize {
    let mut n = 0;
    let Ok(rd) = std::fs::read_dir(root) else {
        return 0;
    };
    for entry in rd.flatten() {
        let p = entry.path();
        if p.is_dir() {
            n += count_files(&p);
        } else {
            n += 1;
        }
    }
    n
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plan::{BuildPlan, BuildTier};

    #[test]
    fn static_build_stages_the_tree() {
        let repo = tempfile::tempdir().unwrap();
        std::fs::write(repo.path().join("index.html"), "<h1>hi</h1>").unwrap();
        std::fs::create_dir_all(repo.path().join(".git")).unwrap();
        std::fs::write(repo.path().join(".git/HEAD"), "ref: x").unwrap();
        let dist = tempfile::tempdir().unwrap();
        let out = run_build(
            &BuildPlan::Static {
                publish_dir: ".".into(),
            },
            repo.path(),
            &dist.path().join("dist"),
        )
        .unwrap();
        assert_eq!(out.plan_label, "static");
        // .git is excluded; index.html is staged.
        assert!(dist.path().join("dist/index.html").is_file());
        assert!(!dist.path().join("dist/.git").exists());
    }

    #[test]
    fn compute_build_runs_through_the_exec_tier() {
        // A wat program that computes 42; its output becomes the published artifact.
        let repo = tempfile::tempdir().unwrap();
        let plan = BuildPlan::Compute {
            lang: "wat".into(),
            source: "(module (func (export \"run\") (result i32) (i32.const 42)))".into(),
            tier: BuildTier::Sandboxed,
            artifact: "index.html".into(),
        };
        let dist = tempfile::tempdir().unwrap();
        let out = run_build(&plan, repo.path(), &dist.path().join("dist")).unwrap();
        assert_eq!(out.plan_label, "compute");
        let body = std::fs::read_to_string(dist.path().join("dist/index.html")).unwrap();
        assert_eq!(
            body.trim(),
            "42",
            "the exec-tier build output is the artifact"
        );
    }

    #[test]
    fn command_build_runs_a_subprocess_and_publishes_output() {
        let repo = tempfile::tempdir().unwrap();
        // A build that writes a dist/ dir.
        let plan = BuildPlan::Command {
            command: "mkdir -p dist && printf '<h1>built</h1>' > dist/index.html".into(),
            output_dir: "dist".into(),
            tier: BuildTier::Caged,
        };
        let dist = tempfile::tempdir().unwrap();
        let out = run_build(&plan, repo.path(), &dist.path().join("dist")).unwrap();
        assert_eq!(out.plan_label, "command");
        let body = std::fs::read_to_string(dist.path().join("dist/index.html")).unwrap();
        assert_eq!(body, "<h1>built</h1>");
    }

    /// D-2 PoC (traversal): a repo-controlled `publish_dir` that escapes the repo root
    /// (`../../..`) is refused — nothing outside the repo is staged.
    #[test]
    fn static_publish_dir_traversal_is_refused() {
        let repo = tempfile::tempdir().unwrap();
        std::fs::write(repo.path().join("index.html"), "<h1>hi</h1>").unwrap();
        let dist = tempfile::tempdir().unwrap();
        let err = run_build(
            &BuildPlan::Static {
                publish_dir: "../../../../../../etc".into(),
            },
            repo.path(),
            &dist.path().join("dist"),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("escapes the repo root"),
            "traversal must be refused, got {err}"
        );
    }

    /// D-2 PoC (symlink exfil): a build output containing a symlink to a host path is
    /// refused — its target bytes are never copied into the published site.
    #[cfg(unix)]
    #[test]
    fn symlink_in_build_output_is_refused() {
        let repo = tempfile::tempdir().unwrap();
        std::fs::write(repo.path().join("index.html"), "<h1>hi</h1>").unwrap();
        // A repo symlink `creds -> /etc` (the classic host-file exfil).
        std::os::unix::fs::symlink("/etc", repo.path().join("creds")).unwrap();
        let dist = tempfile::tempdir().unwrap();
        let err = run_build(
            &BuildPlan::Static {
                publish_dir: ".".into(),
            },
            repo.path(),
            &dist.path().join("dist"),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("refusing to publish symlink"),
            "the symlink must be refused, got {err}"
        );
        // And its target was not served.
        assert!(!dist.path().join("dist/creds/passwd").exists());
    }

    /// D-2 PoC (symlinked publish_dir): a `publish_dir` that is itself a symlink pointing
    /// outside the repo is refused (canonicalize lands outside the repo root).
    #[cfg(unix)]
    #[test]
    fn symlinked_publish_dir_escaping_repo_is_refused() {
        let repo = tempfile::tempdir().unwrap();
        std::fs::write(repo.path().join("index.html"), "<h1>hi</h1>").unwrap();
        let outside = tempfile::tempdir().unwrap();
        std::fs::write(outside.path().join("secret.txt"), "secret").unwrap();
        std::os::unix::fs::symlink(outside.path(), repo.path().join("out")).unwrap();
        let dist = tempfile::tempdir().unwrap();
        let err = run_build(
            &BuildPlan::Static {
                publish_dir: "out".into(),
            },
            repo.path(),
            &dist.path().join("dist"),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("escapes the repo root"),
            "a publish_dir symlink escaping the repo must be refused, got {err}"
        );
    }

    #[test]
    fn server_target_is_refused_with_the_pointer() {
        let repo = tempfile::tempdir().unwrap();
        let err = run_build(
            &BuildPlan::Server {
                entry: "Dockerfile".into(),
                port: 8080,
            },
            repo.path(),
            &tempfile::tempdir().unwrap().path().join("dist"),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("§3.3"),
            "points at the persistent-servers lane"
        );
    }
}
