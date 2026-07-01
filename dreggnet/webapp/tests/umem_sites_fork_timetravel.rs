//! The umem superpowers a `Mutex<BTreeMap>` + JSON-lines log can NEVER give, proven at
//! the `SiteRegistry` API (the #2 re-dregg move, `docs/REGISTRIES-AS-UMEM.md`):
//!
//! - **umem round-trip** — a publish commits to a real Poseidon2 boundary root; a restart
//!   reconstructs FROM the committed heap, exactly-once, owned correctly.
//! - **fork** — a tenant forks their WHOLE hosting namespace; the two copies diverge.
//! - **time-travel** — restore an earlier committed root ("my sites as of yesterday").
//!
//! These are the teeth that distinguish a registry-as-umem-cell from the prior
//! serde-struct-in-a-`Mutex`-map: a flat append-log can do none of them.

use dreggnet_webapp::hosting::{PublishCap, SiteRegistry, sample_site};
use dreggnet_webapp::http::WebRequest;

fn temp(tag: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    let n = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    p.push(format!("dreggnet-umem-sites-{tag}-{n}.snap"));
    p
}
fn cleanup(path: &std::path::Path) {
    std::fs::remove_file(path).ok();
    let mut h = path.as_os_str().to_os_string();
    h.push(".history");
    std::fs::remove_dir_all(std::path::PathBuf::from(h)).ok();
}

/// The umem round-trip on the registry: publish → the registry commits to a umem boundary
/// root → "restart" (drop + restore from the committed heap) → reconstructed, served,
/// owned correctly, and the boundary root is reproduced over the restored heap.
#[test]
fn umem_round_trip_commits_and_reconstructs() {
    let path = temp("round-trip");
    let root_after;
    {
        let reg = SiteRegistry::durable(&path).expect("open durable umem registry");
        reg.publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            sample_site(),
        )
        .expect("publish");
        // The registry commits to a REAL umem boundary root (64-hex Poseidon2), not a
        // JSON-lines content hash.
        root_after = reg.umem_root().expect("durable registry has a umem root");
        assert_eq!(root_after.len(), 64);
        assert!(root_after.chars().all(|c| c.is_ascii_hexdigit()));
    }
    // "Restart": a fresh registry over the same path restores FROM the committed heap.
    let restarted = SiteRegistry::durable(&path).expect("reopen");
    assert_eq!(restarted.names(), vec!["blog".to_string()]);
    let resp = restarted.resolve("blog.example.com", &WebRequest::get("/"));
    assert_eq!(resp.status, 200);
    assert!(resp.body_str().contains("hello from a dregg cell"));
    assert_eq!(restarted.get("blog").unwrap().owner, "agent:ember");
    // The committed boundary root is reproduced over the restored heap (the round-trip
    // is on the real umem boundary, not a re-hashed log).
    assert_eq!(restarted.umem_root().unwrap(), root_after);
    cleanup(&path);
}

/// Fork the whole hosting namespace: two divergent copies from one committed root. The
/// fork starts byte-identical (same boundary root), then each side publishes sites the
/// other never sees.
#[test]
fn fork_the_whole_namespace_diverges() {
    let base = temp("fork-base");
    let forked = temp("fork-copy");
    let reg = SiteRegistry::durable(&base).expect("open");
    let cap = |n: &str| PublishCap::for_site("agent:ember", n);
    reg.publish(&cap("alpha"), "alpha", sample_site()).unwrap();
    reg.publish(&cap("beta"), "beta", sample_site()).unwrap();
    let root0 = reg.umem_root().unwrap();

    // Fork: the tenant copies their ENTIRE namespace (both sites at once).
    let fork = reg
        .fork_namespace(&forked)
        .expect("durable registry forks")
        .expect("fork ok");
    assert_eq!(
        fork.umem_root().unwrap(),
        root0,
        "the fork starts at the parent's root"
    );
    let mut fnames = fork.names();
    fnames.sort();
    assert_eq!(fnames, vec!["alpha", "beta"]);

    // Diverge: the fork is a preview that adds `gamma`; the parent adds `delta`. Neither
    // sees the other's site — and the served data plane reflects the split.
    fork.publish(&cap("gamma"), "gamma", sample_site()).unwrap();
    reg.publish(&cap("delta"), "delta", sample_site()).unwrap();
    assert!(fork.get("gamma").is_some() && fork.get("delta").is_none());
    assert!(reg.get("delta").is_some() && reg.get("gamma").is_none());
    assert_eq!(
        fork.resolve("gamma.example.com", &WebRequest::get("/"))
            .status,
        200
    );
    assert_eq!(
        fork.resolve("delta.example.com", &WebRequest::get("/"))
            .status,
        404
    );
    assert_ne!(
        fork.umem_root().unwrap(),
        reg.umem_root().unwrap(),
        "the copies diverged"
    );
    cleanup(&base);
    cleanup(&forked);
}

/// Time-travel: restore an earlier committed root. A tenant rolls their whole namespace
/// back to "yesterday", and the rollback survives a restart.
#[test]
fn time_travel_restores_the_namespace() {
    let path = temp("time-travel");
    let cap = |n: &str| PublishCap::for_site("agent:ember", n);
    let root_v1;
    {
        let mut reg = SiteRegistry::durable(&path).expect("open");
        reg.publish(&cap("alpha"), "alpha", sample_site()).unwrap();
        root_v1 = reg.checkpoint_namespace().unwrap(); // "yesterday": only alpha
        reg.publish(&cap("beta"), "beta", sample_site()).unwrap();
        assert_eq!(reg.names().len(), 2);

        // Roll back to yesterday: beta is gone, alpha remains, and it still serves.
        reg.restore_namespace(&root_v1).expect("restore");
        assert_eq!(reg.names(), vec!["alpha".to_string()]);
        assert_eq!(reg.umem_root().unwrap(), root_v1);
        assert_eq!(
            reg.resolve("alpha.example.com", &WebRequest::get("/"))
                .status,
            200
        );
        assert_eq!(
            reg.resolve("beta.example.com", &WebRequest::get("/"))
                .status,
            404
        );
    }
    // The time-travel is durable: a restart serves the restored (earlier) namespace.
    let reopened = SiteRegistry::durable(&path).expect("reopen");
    assert_eq!(reopened.names(), vec!["alpha".to_string()]);
    assert_eq!(reopened.umem_root().unwrap(), root_v1);
    cleanup(&path);
}
