//! `dregg-deploy` — auto-deploy-from-git, the keystone DX (surpassing Liftoff's "you ship, we
//! host", made verifiable). See `docs/PERMISSIONLESS-CLOUD-PLAN.md` §3.1.
//!
//! ```text
//!   dregg deploy <git-url|.>
//!     │
//!     ▼ ① CLONE   — fetch the repo at a pinned commit          (the source commitment)
//!     ▼ ② DETECT  — framework heuristic → a BuildPlan          (static | node | compute)
//!     ▼ ③ BUILD   — run the build in a cap-bounded exec tier,  (metered against the deploy
//!     │              metered against the deploy budget          budget; over-budget → reaped)
//!     ▼ ④ PUBLISH — dist/ → a SiteCell + PublishReceipt        (commit folded into the root)
//!     ▼ ⑤ LIVE    — served at <name>.example.com
//! ```
//!
//! The deploy is modeled as a **crash-resumable, exactly-once, metered durable workflow**
//! ([`workflow`]): a deploy that crashes mid-build resumes from its last checkpoint (a
//! completed Clone/Build replayed, never re-run), and the build is metered the same way a
//! compute lease is. The **source commitment** — the cloned commit hash — lands in the
//! [`DeployReceipt`] and is committed into the published cell's `content_root` (a
//! `/.well-known/dregg-deploy.json` manifest asset), so *which commit a site was built from*
//! is re-witnessable (reproducibility Liftoff cannot offer).
//!
//! What is **safe-autonomous** (built + proven here): the whole clone→detect→build→publish→
//! serve round-trip through the local / in-process / on-disk path. What is **reviewed-go** (not
//! built): a public push-triggered webhook receiver (`docs/MORNING-REVIEW.md`).
//!
//! # The round-trip, in one call
//!
//! ```no_run
//! use std::sync::Arc;
//! use dregg_deploy::{DeployEngine, DeploySpec, deploy_on_disk_blocking};
//! use dreggnet_webapp::hosting::SiteRegistry;
//!
//! let registry = Arc::new(SiteRegistry::new());
//! let engine = Arc::new(DeployEngine::new("/var/lib/dregg/deploys", registry.clone()));
//! let spec = DeploySpec::new("https://example.com/repo.git", "blog", "agent:ember");
//! let receipt = deploy_on_disk_blocking(
//!     engine, &spec, "deploy-1", std::path::Path::new("/var/lib/dregg/deploy-1.db"),
//! ).expect("deploy");
//! println!("live at {} (commit {})", receipt.url, receipt.commit);
//! // The site is now served by `registry` at `<name>.example.com`.
//! ```

pub mod build;
pub mod clone;
pub mod plan;
pub mod publish;
pub mod sandbox;
pub mod workflow;

pub use build::BuildOutcome;
pub use clone::{CloneResult, clone_repo, head_commit};
pub use plan::{BuildPlan, BuildTier, DeployManifest, MANIFEST_FILE, detect, manifest_site_name};
pub use publish::{DEPLOY_MANIFEST_PATH, DeployManifestAsset, dist_to_content, publish_dist};
pub use workflow::{
    ACT_BUILD, ACT_CLONE, ACT_METER, ACT_PUBLISH, DeployEngine, DeployReceipt, DeploySpec,
    DeployStage, ORCH_DEPLOY, build_deploy_registries, deploy_in_memory, deploy_in_memory_blocking,
    deploy_on_disk, deploy_on_disk_blocking, meter,
};
