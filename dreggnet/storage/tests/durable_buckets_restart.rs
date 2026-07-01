//! Durable data plane — the **put → restart → reconstruct** proof for the bucket
//! registry (docs/CLOUD-PROVIDER-READINESS.md data-plane blocker).
//!
//! A storage bucket + its objects lived only in an in-memory `BTreeMap` and were
//! LOST ON RESTART. With the durable umem backend ([`dreggnet_umem`]) attached, every
//! bucket cell mutation (create/put/delete) is laid into the registry cell's
//! sorted-Poseidon2 heap and committed to its boundary root, so a fresh registry over
//! the same path RECONSTRUCTS the buckets AND their objects FROM the committed heap —
//! owned correctly, exactly-once, with the deletes reflected.

use dreggnet_storage::{Account, BucketRegistry, StorageCap};

fn cap(holder: &str, bucket: &str) -> StorageCap {
    StorageCap::for_bucket(holder, bucket)
}

fn temp_path(tag: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    p.push(format!("dreggnet-durable-buckets-{tag}-{nanos}.log"));
    p
}

/// Create a bucket, put objects, "restart", and confirm the bucket + its objects
/// are reconstructed — readable, owned by the creator, at the same committed root.
#[test]
fn bucket_and_objects_survive_a_restart() {
    let path = temp_path("survives");
    let cap = cap("agent:ember", "reports");
    let acct = Account::funded("agent:ember", 1_000_000);

    let root_after_writes;
    {
        let reg = BucketRegistry::durable(&path).expect("open durable registry");
        reg.create_bucket(&cap, "reports").expect("create");
        reg.put(
            &cap,
            &acct,
            "reports",
            "2026/q1.json",
            br#"{"rev":100}"#.to_vec(),
        )
        .expect("put q1");
        let r2 = reg
            .put(
                &cap,
                &acct,
                "reports",
                "2026/q2.json",
                br#"{"rev":200}"#.to_vec(),
            )
            .expect("put q2");
        root_after_writes = r2.content_root;
    }

    // "Restart": a brand-new registry over the same durable path reconstructs it.
    let restarted = BucketRegistry::durable(&path).expect("reopen");
    assert_eq!(restarted.bucket_names(), vec!["reports".to_string()]);
    let cell = restarted
        .get_bucket("reports")
        .expect("bucket reconstructed");
    assert_eq!(cell.owner, "agent:ember", "owned correctly after restart");
    assert_eq!(
        cell.content_root, root_after_writes,
        "the reconstructed bucket is at its last committed root"
    );

    // The objects are readable after the restart (cap-gated get).
    let q1 = restarted
        .get(&cap, &acct, "reports", "2026/q1.json")
        .expect("q1 reconstructed");
    assert_eq!(q1.body, br#"{"rev":100}"#);
    let q2 = restarted
        .get(&cap, &acct, "reports", "2026/q2.json")
        .expect("q2 reconstructed");
    assert_eq!(q2.body, br#"{"rev":200}"#);

    // The trustless read still re-witnesses against the reconstructed root.
    let opening = restarted
        .verified_get(&cap, &acct, "reports", "2026/q1.json")
        .expect("verified get");
    assert!(
        opening.verify(),
        "served bytes re-witness against the durable root"
    );

    std::fs::remove_file(&path).ok();
}

/// A delete is durable: after a restart the removed object is gone (the latest
/// committed bucket state wins — no resurrection), and there is no duplicate bucket.
#[test]
fn deletes_are_durable_across_a_restart() {
    let path = temp_path("delete");
    let cap = cap("agent:ember", "docs");
    let acct = Account::funded("agent:ember", 1_000_000);

    {
        let reg = BucketRegistry::durable(&path).expect("open");
        reg.create_bucket(&cap, "docs").expect("create");
        reg.put(&cap, &acct, "docs", "keep.txt", b"keep".to_vec())
            .expect("put keep");
        reg.put(&cap, &acct, "docs", "gone.txt", b"gone".to_vec())
            .expect("put gone");
        reg.delete(&cap, &acct, "docs", "gone.txt")
            .expect("delete gone");
    }

    let restarted = BucketRegistry::durable(&path).expect("reopen");
    assert_eq!(
        restarted.bucket_names().len(),
        1,
        "no duplicate bucket after reload"
    );
    // The kept object survives; the deleted one stays deleted.
    assert!(restarted.get(&cap, &acct, "docs", "keep.txt").is_ok());
    assert!(
        restarted.get(&cap, &acct, "docs", "gone.txt").is_err(),
        "a durable delete is not resurrected on restart"
    );

    std::fs::remove_file(&path).ok();
}
