//! Stamps the build identity `/status` reports as `version` (#86 rider; product/bread-redeploy.md
//! asked for it after a redeploy could not tell which commit a live node ran).
//!
//! `DREGG_NODE_GIT_SHA` is `git rev-parse HEAD` of the tree being built, or `DREGG_BUILD_GIT_SHA`
//! when the build has no `.git` (a container context), or `unknown`. `DREGG_NODE_BUILD_UNIX` is
//! `SOURCE_DATE_EPOCH` when set, else the time this script ran. The script reruns when HEAD moves,
//! so the stamp is the time of the build that first saw that commit, not of every incremental build.

use std::path::Path;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn git(args: &[&str]) -> Option<String> {
    let out = Command::new("git").args(args).output().ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
    (!s.is_empty()).then_some(s)
}

/// Days-from-civil inverse (Howard Hinnant's `civil_from_days`), so the stamp needs no date crate.
fn rfc3339_utc(unix: u64) -> String {
    let days = (unix / 86_400) as i64;
    let secs = unix % 86_400;
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    format!(
        "{y:04}-{m:02}-{d:02}T{:02}:{:02}:{:02}Z",
        secs / 3_600,
        (secs / 60) % 60,
        secs % 60
    )
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=DREGG_BUILD_GIT_SHA");
    println!("cargo:rerun-if-env-changed=SOURCE_DATE_EPOCH");

    let sha = std::env::var("DREGG_BUILD_GIT_SHA")
        .ok()
        .filter(|s| !s.is_empty())
        .or_else(|| git(&["rev-parse", "HEAD"]))
        .unwrap_or_else(|| "unknown".to_string());

    // Rerun when HEAD moves: HEAD itself (branch switch, detached checkout) and the ref it names
    // (a commit on the current branch). Only paths that exist — a missing path reruns every build.
    let mut watch: Vec<String> = Vec::new();
    if let Some(dir) = git(&["rev-parse", "--absolute-git-dir"]) {
        watch.push(format!("{dir}/HEAD"));
    }
    if let (Some(common), Some(head_ref)) = (
        git(&["rev-parse", "--path-format=absolute", "--git-common-dir"]),
        git(&["symbolic-ref", "-q", "HEAD"]),
    ) {
        watch.push(format!("{common}/{head_ref}"));
        watch.push(format!("{common}/packed-refs"));
    }
    for path in watch.iter().filter(|p| Path::new(p).exists()) {
        println!("cargo:rerun-if-changed={path}");
    }

    let unix = std::env::var("SOURCE_DATE_EPOCH")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or_else(|| {
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0)
        });

    println!("cargo:rustc-env=DREGG_NODE_GIT_SHA={sha}");
    println!("cargo:rustc-env=DREGG_NODE_BUILD_UNIX={unix}");
    println!("cargo:rustc-env=DREGG_NODE_BUILD_TIME={}", rfc3339_utc(unix));
}
