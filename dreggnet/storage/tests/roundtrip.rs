//! End-to-end proofs for the object-store service, in-process (no node needed):
//! the put→get→list→delete round-trip, the cap-gate (a cap for bucket A cannot
//! write bucket B), the meter (an over-budget put is refused before any write),
//! and the trustless verified read (a served object re-witnesses against the
//! committed bucket root; a tampered byte is caught).

use dreggnet_storage::{
    Account, BucketRegistry, Object, Pricing, StorageCap, StorageError, verify_opening,
};

fn cap(holder: &str, bucket: &str) -> StorageCap {
    StorageCap::for_bucket(holder, bucket)
}

#[test]
fn put_get_list_delete_round_trip() {
    let reg = BucketRegistry::new();
    let cap = cap("agent:ember", "reports");
    // A generously funded account so the round-trip is never budget-limited.
    let acct = Account::funded("agent:ember", 10_000);

    // Create the bucket (cap-gated).
    let b = reg.create_bucket(&cap, "reports").expect("create");
    assert_eq!(b.owner, "agent:ember");

    // PUT two objects.
    let r1 = reg
        .put(
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
            br#"{"rev":250}"#.to_vec(),
        )
        .expect("put q2");
    assert_eq!(r1.bucket, "reports");
    assert_eq!(r1.key, "/2026/q1.json");
    assert!(r1.units_charged > 0, "a put is metered");
    // Each put moves the committed content root.
    assert_ne!(r1.content_root, r2.content_root);

    // GET an object back — bytes round-trip exactly.
    let got = reg
        .get(&cap, &acct, "reports", "2026/q1.json")
        .expect("get q1");
    assert_eq!(got.body, br#"{"rev":100}"#);
    assert_eq!(got.content_type, "application/json");

    // LIST the bucket, and list by prefix.
    let all = reg.list(&cap, &acct, "reports", "/").expect("list");
    assert_eq!(all, vec!["/2026/q1.json", "/2026/q2.json"]);
    let by_prefix = reg
        .list(&cap, &acct, "reports", "2026/q2")
        .expect("list prefix");
    assert_eq!(by_prefix, vec!["/2026/q2.json"]);

    // DELETE an object — the root moves, and a re-list reflects it.
    let d = reg
        .delete(&cap, &acct, "reports", "2026/q1.json")
        .expect("delete q1");
    assert_ne!(d.content_root, r2.content_root);
    let after = reg
        .list(&cap, &acct, "reports", "/")
        .expect("list after delete");
    assert_eq!(after, vec!["/2026/q2.json"]);
    // The deleted object is gone.
    assert!(matches!(
        reg.get(&cap, &acct, "reports", "2026/q1.json"),
        Err(StorageError::NoSuchObject { .. }),
    ));
    // Deleting an absent key is refused (a delete receipt always names a removal).
    assert!(matches!(
        reg.delete(&cap, &acct, "reports", "2026/q1.json"),
        Err(StorageError::NoSuchObject { .. }),
    ));
}

#[test]
fn cap_for_bucket_a_cannot_write_bucket_b() {
    let reg = BucketRegistry::new();
    let acct = Account::funded("agent:ember", 10_000);

    // Two buckets owned by the same holder, each with its own cap.
    let cap_a = cap("agent:ember", "alpha");
    let cap_b = cap("agent:ember", "beta");
    reg.create_bucket(&cap_a, "alpha").expect("create alpha");
    reg.create_bucket(&cap_b, "beta").expect("create beta");

    // The cap for `alpha` cannot put into `beta` — cap-attenuation refusal,
    // BEFORE any write and BEFORE any charge.
    let before = acct.spent();
    let refused = reg.put(&cap_a, &acct, "beta", "x.txt", b"nope".to_vec());
    assert!(matches!(
        refused,
        Err(StorageError::CapRefused { bucket, .. }) if bucket == "beta",
    ));
    assert_eq!(acct.spent(), before, "a cap-refused op charges nothing");

    // The same cap also cannot create `beta` (its token names `alpha`).
    assert!(matches!(
        reg.create_bucket(&cap_a, "beta"),
        Err(StorageError::CapRefused { .. }),
    ));

    // And a cap whose token matches the bucket name but whose holder is NOT the
    // owner is refused too (no cross-tenant access via a guessed name).
    let imposter = cap("agent:mallory", "alpha");
    assert!(matches!(
        reg.put(&imposter, &acct, "alpha", "x.txt", b"nope".to_vec()),
        Err(StorageError::CapRefused { .. }),
    ));

    // The legitimate cap works.
    reg.put(&cap_a, &acct, "alpha", "x.txt", b"ok".to_vec())
        .expect("alpha put");
}

#[test]
fn put_is_metered_and_over_budget_is_refused_before_writing() {
    // Price a put at op=10 + 1/KiB; fund an account that can afford exactly one
    // small put, then prove the second is refused without mutating state.
    let reg = BucketRegistry::with_pricing(Pricing::default());
    let cap = cap("agent:ember", "tiny");
    reg.create_bucket(&cap, "tiny").expect("create");

    // 11 units covers one 1-byte put (op 10 + 1 KiB * 1).
    let acct = Account::funded("agent:ember", 11);
    reg.put(&cap, &acct, "tiny", "a", b"x".to_vec())
        .expect("first put fits");
    assert_eq!(acct.remaining(), 0);

    // The second put is over budget: refused, and the bucket is unchanged.
    let refused = reg.put(&cap, &acct, "tiny", "b", b"y".to_vec());
    assert!(matches!(refused, Err(StorageError::OverBudget(_))));
    let bucket = reg.get_bucket("tiny").unwrap();
    assert_eq!(
        bucket.content.keys(),
        vec!["/a"],
        "no partial write on refusal"
    );
}

#[test]
fn verified_read_is_trustless_and_catches_tampering() {
    let reg = BucketRegistry::new();
    let cap = cap("agent:ember", "vault");
    let acct = Account::funded("agent:ember", 10_000);
    reg.create_bucket(&cap, "vault").expect("create");

    let put = reg
        .put_object(
            &cap,
            &acct,
            "vault",
            "secret.bin",
            Object::new("application/octet-stream", b"the-committed-bytes".to_vec()),
        )
        .expect("put");

    // The verified read returns an opening that re-witnesses against the SAME
    // root the put committed.
    let opening = reg
        .verified_get(&cap, &acct, "vault", "secret.bin")
        .expect("verified get");
    assert_eq!(opening.bucket_root, put.content_root);
    assert_eq!(opening.object.body, b"the-committed-bytes");
    assert!(verify_opening(&opening), "the honest opening verifies");

    // A man-in-the-middle flips a served byte: verification fails — the reader is
    // not fooled even though the registry served it.
    let mut tampered = opening.clone();
    tampered.object.body = b"the-corrupted-bytes".to_vec();
    assert!(!verify_opening(&tampered), "a flipped byte is caught");

    // Forging the root to match the tampered bytes also fails: the re-fold of the
    // listed leaves no longer reproduces the forged root.
    let mut forged = tampered.clone();
    forged.bucket_root = "0123456789abcdef".to_string();
    assert!(!verify_opening(&forged), "a forged root is caught");
}

/// The receipt-contract proof (storage side): a signed registry seals every op
/// — create / put / delete — into ONE prev-hash-chained, ed25519-signed receipt
/// stream that a non-witness verifies with no trust in the host, and a tampered
/// receipt is caught. This grounds the storage receipts on the kernel receipt
/// discipline (`docs/RECEIPT-CONTRACT.md`).
#[test]
fn signed_storage_ops_form_a_verifiable_receipt_chain() {
    use dreggnet_storage::receipt::{ChainError, ReceiptBody, verify_chain, verify_chain_from};

    let reg = BucketRegistry::signed([11u8; 32]);
    let cap = cap("agent:ember", "reports");
    let acct = Account::funded("agent:ember", 100_000);

    // The shared chain across kinds: create(seq 0) → put → put → delete, each
    // linking to the prior receipt's hash (proves one append-only stream).
    let b = reg.create_bucket(&cap, "reports").expect("create");
    let p1 = reg
        .put(&cap, &acct, "reports", "a.json", br#"{"x":1}"#.to_vec())
        .expect("put a");
    let p2 = reg
        .put(&cap, &acct, "reports", "b.json", br#"{"x":2}"#.to_vec())
        .expect("put b");
    let d = reg
        .delete(&cap, &acct, "reports", "a.json")
        .expect("delete a");

    assert!(b.attest.is_some() && p1.attest.is_some() && p2.attest.is_some() && d.attest.is_some());
    assert!(b.attest.as_ref().unwrap().prev_receipt_hash.is_none());
    assert_eq!(
        p1.attest.as_ref().unwrap().prev_receipt_hash,
        b.receipt_hash()
    );
    assert_eq!(
        p2.attest.as_ref().unwrap().prev_receipt_hash,
        p1.receipt_hash()
    );
    assert_eq!(
        d.attest.as_ref().unwrap().prev_receipt_hash,
        p2.receipt_hash()
    );
    assert_eq!(
        reg.receipt_signer(),
        Some(b.attest.as_ref().unwrap().signer)
    );

    // Full contract verification over a homogeneous run: the put sub-chain
    // verifies (signatures + links) starting from the create's hash.
    let puts = vec![p1.clone(), p2.clone()];
    assert_eq!(verify_chain_from(&puts, b.receipt_hash()), Ok(()));
    // From genesis, the put sub-chain's first link is non-None → caught.
    assert_eq!(verify_chain(&puts), Err(ChainError::BrokenLink { seq: 1 }));

    // Tamper a recorded field after sealing → the signature no longer verifies.
    let mut forged = puts.clone();
    forged[1].content_root = "deadbeef".into();
    assert_eq!(
        verify_chain_from(&forged, b.receipt_hash()),
        Err(ChainError::BadSignature { seq: 2 }),
    );

    // The unsigned local default leaves a bare projection (a log, not a receipt).
    let plain = BucketRegistry::new();
    let pc = StorageCap::for_bucket("a", "x");
    let pa = Account::funded("a", 1000);
    plain.create_bucket(&pc, "x").unwrap();
    let bare = plain.put(&pc, &pa, "x", "k", b"v".to_vec()).unwrap();
    assert!(bare.attest.is_none());
}
