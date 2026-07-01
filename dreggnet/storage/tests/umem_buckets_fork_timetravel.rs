//! The umem superpowers a `Mutex<BTreeMap>` + JSON-lines log can NEVER give, proven at
//! the `BucketRegistry` API (the #2 re-dregg move, `docs/REGISTRIES-AS-UMEM.md`):
//!
//! - **umem round-trip** — a create/put commits to a real Poseidon2 boundary root; a
//!   restart reconstructs the buckets + their objects FROM the committed heap.
//! - **fork** — a tenant forks their WHOLE bucket namespace; the two copies diverge.
//! - **time-travel** — restore an earlier committed root ("my buckets as of yesterday").
//!
//! These are the teeth that distinguish a registry-as-umem-cell from the prior
//! serde-struct-in-a-`Mutex`-map: a flat append-log can do none of them.

use dreggnet_storage::{Account, BucketRegistry, StorageCap};

fn cap(holder: &str, bucket: &str) -> StorageCap {
    StorageCap::for_bucket(holder, bucket)
}
fn acct() -> Account {
    Account::funded("agent:ember", 1_000_000)
}
fn temp(tag: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    let n = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    p.push(format!("dreggnet-umem-buckets-{tag}-{n}.snap"));
    p
}
fn cleanup(path: &std::path::Path) {
    std::fs::remove_file(path).ok();
    let mut h = path.as_os_str().to_os_string();
    h.push(".history");
    std::fs::remove_dir_all(std::path::PathBuf::from(h)).ok();
}

/// The umem round-trip on the bucket registry: create + put → the registry commits to a
/// umem boundary root → "restart" (drop + restore from the committed heap) →
/// reconstructed, served, owned correctly, and the boundary root is reproduced.
#[test]
fn umem_round_trip_commits_and_reconstructs() {
    let path = temp("round-trip");
    let c = cap("agent:ember", "reports");
    let root_after;
    {
        let reg = BucketRegistry::durable(&path).expect("open durable umem registry");
        reg.create_bucket(&c, "reports").expect("create");
        reg.put(&c, &acct(), "reports", "q1.json", br#"{"rev":1}"#.to_vec())
            .expect("put");
        // The registry commits to a REAL umem boundary root (64-hex Poseidon2).
        root_after = reg.umem_root().expect("durable registry has a umem root");
        assert_eq!(root_after.len(), 64);
        assert!(root_after.chars().all(|ch| ch.is_ascii_hexdigit()));
    }
    // "Restart": a fresh registry over the same path restores FROM the committed heap.
    let restarted = BucketRegistry::durable(&path).expect("reopen");
    assert_eq!(restarted.bucket_names(), vec!["reports".to_string()]);
    assert_eq!(
        restarted.get_bucket("reports").unwrap().owner,
        "agent:ember"
    );
    let obj = restarted
        .get(&c, &acct(), "reports", "q1.json")
        .expect("object reconstructed");
    assert_eq!(obj.body, br#"{"rev":1}"#);
    assert_eq!(restarted.umem_root().unwrap(), root_after);
    cleanup(&path);
}

/// Fork the whole bucket namespace: two divergent copies from one committed root. The
/// fork starts byte-identical, then each side creates buckets the other never sees.
#[test]
fn fork_the_whole_namespace_diverges() {
    let base = temp("fork-base");
    let forked = temp("fork-copy");
    let reg = BucketRegistry::durable(&base).expect("open");
    reg.create_bucket(&cap("agent:ember", "alpha"), "alpha")
        .unwrap();
    reg.create_bucket(&cap("agent:ember", "beta"), "beta")
        .unwrap();
    let root0 = reg.umem_root().unwrap();

    // Fork: the tenant copies their ENTIRE namespace (both buckets at once).
    let fork = reg
        .fork_namespace(&forked)
        .expect("durable registry forks")
        .expect("fork ok");
    assert_eq!(
        fork.umem_root().unwrap(),
        root0,
        "the fork starts at the parent's root"
    );
    let mut fnames = fork.bucket_names();
    fnames.sort();
    assert_eq!(fnames, vec!["alpha", "beta"]);

    // Diverge: the fork adds `gamma`; the parent adds `delta`. Neither sees the other.
    fork.create_bucket(&cap("agent:ember", "gamma"), "gamma")
        .unwrap();
    reg.create_bucket(&cap("agent:ember", "delta"), "delta")
        .unwrap();
    assert!(fork.get_bucket("gamma").is_some() && fork.get_bucket("delta").is_none());
    assert!(reg.get_bucket("delta").is_some() && reg.get_bucket("gamma").is_none());
    assert_ne!(
        fork.umem_root().unwrap(),
        reg.umem_root().unwrap(),
        "the copies diverged"
    );
    cleanup(&base);
    cleanup(&forked);
}

/// Time-travel: restore an earlier committed root. A tenant rolls their whole bucket
/// namespace back to "yesterday", and the rollback survives a restart.
#[test]
fn time_travel_restores_the_namespace() {
    let path = temp("time-travel");
    let root_v1;
    {
        let reg = BucketRegistry::durable(&path).expect("open");
        reg.create_bucket(&cap("agent:ember", "alpha"), "alpha")
            .unwrap();
        root_v1 = reg.checkpoint_namespace().unwrap(); // "yesterday": only alpha
        reg.create_bucket(&cap("agent:ember", "beta"), "beta")
            .unwrap();
        assert_eq!(reg.bucket_names().len(), 2);

        // Roll back to yesterday: beta is gone, alpha remains.
        reg.restore_namespace(&root_v1).expect("restore");
        assert_eq!(reg.bucket_names(), vec!["alpha".to_string()]);
        assert_eq!(reg.umem_root().unwrap(), root_v1);
    }
    // The time-travel is durable: a restart serves the restored (earlier) namespace.
    let reopened = BucketRegistry::durable(&path).expect("reopen");
    assert_eq!(reopened.bucket_names(), vec!["alpha".to_string()]);
    assert_eq!(reopened.umem_root().unwrap(), root_v1);
    cleanup(&path);
}
