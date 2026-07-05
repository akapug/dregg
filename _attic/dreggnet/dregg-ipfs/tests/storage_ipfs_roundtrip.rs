//! Storage → IPFS round-trip: the bridge fit, proven end to end over `MockIpfs`.
//!
//! This is the headline validation: a `dreggnet-storage` bucket `put` (the dregg
//! content-addressed object, with its signed `PutReceipt`) paired with an IPFS pin,
//! then a fetch-by-CID re-witnessed against BOTH the CID (content-addressing) and the
//! dregg receipt (the cell commits the CID). And the tamper tooth: a node that serves
//! the wrong bytes under the CID is refused.
//!
//! Two distinct content commitments live side by side, and the test keeps them
//! honest:
//!   - the bucket cell's **heap-leaf commitment** (FNV in-process / Poseidon2 on a
//!     dregg node) — binds the object into the cell `content_root` for the trustless
//!     `verify_opening` read; and
//!   - the object's **IPFS content address** (blake3 CIDv1) — the transport address,
//!     identical to a blake3 commitment over the raw blob.
//! The bridge commits the CID into the cell (here: as a sibling `*.cid` manifest
//! object, so the existing `content_root`/receipt machinery binds it with no change
//! to the storage crate).

use dregg_ipfs::{Cid, IpfsError, MockIpfs, blob_cid, fetch_verified, pin_blob};
use dreggnet_storage::{
    Account, BucketRegistry, StorageCap,
    receipt::{ReceiptBody, verify_chain_from},
};

fn cap(holder: &str, bucket: &str) -> StorageCap {
    StorageCap::for_bucket(holder, bucket)
}

#[test]
fn storage_put_pinned_to_ipfs_round_trips_and_is_receipted() {
    let node = MockIpfs::new();
    // A signed bucket registry: each put is a re-witnessable, owner-signed turn.
    let reg = BucketRegistry::signed([3u8; 32]);
    let owner_key = reg
        .receipt_signer()
        .expect("signed registry exposes its key");
    let account = Account::funded("agent:ember", 1_000_000);
    let c = cap("agent:ember", "media");
    let create = reg.create_bucket(&c, "media").expect("create");

    let key = "/img/logo.png";
    let bytes = b"\x89PNG\r\n the logo bytes ".to_vec();

    // (a) Pin the object bytes to IPFS — the CID is the dregg content commitment.
    let cid = pin_blob(&node, &bytes).expect("pin");
    assert_eq!(cid, blob_cid(&bytes), "the CID IS blake3(blob)");

    // (b) Store the object in the bucket cell (heap-leaf commitment + signed
    //     receipt), AND commit the CID in the cell as a sibling manifest object, so
    //     the cell's content_root + the PutReceipt bind which CID backs the object.
    let put = reg
        .put(&c, &account, "media", key, bytes.clone())
        .expect("put object");
    let cid_key = format!("{key}.cid");
    let cid_put = reg
        .put(
            &c,
            &account,
            "media",
            &cid_key,
            cid.to_string_cid().into_bytes(),
        )
        .expect("put cid manifest");

    // The puts are signed turns; the chain re-witnesses for a non-witness (the put
    // sub-chain links from the create receipt, the bucket's genesis turn).
    assert!(put.attest.is_some());
    assert_eq!(
        verify_chain_from(&[put.clone(), cid_put.clone()], create.receipt_hash()),
        Ok(())
    );
    assert_eq!(put.attestation().unwrap().signer, owner_key);

    // (c) A reader learns the CID from the committed cell (trustlessly: the manifest
    //     object opens against the bucket root), then fetches the bytes from ANY node
    //     and re-witnesses them against the CID — no trust in the node.
    let opening = reg
        .verified_get(&c, &account, "media", &cid_key)
        .expect("open cid manifest");
    assert!(
        opening.verify(),
        "the CID manifest is committed in the bucket root"
    );
    let committed_cid = Cid::parse(std::str::from_utf8(&opening.object.body).unwrap()).unwrap();
    assert_eq!(committed_cid, cid);

    let fetched = fetch_verified(&node, &committed_cid).expect("trustless fetch");
    assert_eq!(
        fetched, bytes,
        "the bytes served from the node ARE the published bytes"
    );
}

#[test]
fn a_node_serving_tampered_bytes_is_refused() {
    let node = MockIpfs::new();
    let reg = BucketRegistry::signed([4u8; 32]);
    let account = Account::funded("agent:ember", 1_000_000);
    let c = cap("agent:ember", "media");
    reg.create_bucket(&c, "media").unwrap();

    let bytes = b"the authorized report".to_vec();
    let cid = pin_blob(&node, &bytes).unwrap();
    reg.put(&c, &account, "media", "/report.txt", bytes)
        .unwrap();

    // The node turns malicious: it serves different bytes under the committed CID.
    node.tamper(&cid, b"a forged report");
    let err = fetch_verified(&node, &cid).unwrap_err();
    assert!(
        matches!(err, IpfsError::CidMismatch { .. }),
        "tamper must be refused, got {err:?}"
    );
}
