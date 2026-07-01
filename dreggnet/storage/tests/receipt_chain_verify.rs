//! The storage receipt chain re-witnessed by a non-witness: a signed
//! `BucketRegistry` seals every create/put into a prev-hash-chained, ed25519-signed
//! stream, and a client verifies that stream with `verify_chain` (the receipt
//! contract's non-witness check) — no trust in the host. This is the storage-side
//! live caller of `verify_chain`, alongside the trustless `verify_opening` read.

use dreggnet_storage::receipt::{ChainError, ReceiptBody, verify_chain, verify_chain_from};
use dreggnet_storage::{Account, BucketRegistry, PutReceipt, StorageCap, verify_opening};

fn setup() -> (BucketRegistry, StorageCap, Account) {
    let reg = BucketRegistry::signed([5u8; 32]);
    let cap = StorageCap::for_bucket("agent:ember", "reports");
    let acct = Account::funded("agent:ember", 1_000_000);
    (reg, cap, acct)
}

#[test]
fn a_signed_put_run_verifies_for_a_non_witness() {
    let (reg, cap, acct) = setup();
    let create = reg.create_bucket(&cap, "reports").unwrap();
    let put_a = reg
        .put(&cap, &acct, "reports", "a.txt", b"alpha".to_vec())
        .unwrap();
    let put_b = reg
        .put(&cap, &acct, "reports", "b.txt", b"bravo".to_vec())
        .unwrap();

    // The create is a genesis receipt; it verifies on its own.
    assert_eq!(verify_chain(std::slice::from_ref(&create)), Ok(()));

    // The puts form a homogeneous sub-chain whose first link is the create receipt.
    let puts = vec![put_a, put_b];
    assert_eq!(verify_chain_from(&puts, create.receipt_hash()), Ok(()));
}

#[test]
fn a_tampered_put_content_root_breaks_the_signature() {
    let (reg, cap, acct) = setup();
    let create = reg.create_bucket(&cap, "reports").unwrap();
    let put_a = reg
        .put(&cap, &acct, "reports", "a.txt", b"alpha".to_vec())
        .unwrap();
    let put_b = reg
        .put(&cap, &acct, "reports", "b.txt", b"bravo".to_vec())
        .unwrap();

    // A host forges the recorded content root of the first put — the signature over
    // it no longer verifies.
    let mut forged = put_a.clone();
    forged.content_root = "deadbeefdeadbeef".to_string();
    let chain = vec![forged, put_b.clone()];
    assert_eq!(
        verify_chain_from(&chain, create.receipt_hash()),
        Err(ChainError::BadSignature { seq: put_a.seq() })
    );
}

#[test]
fn splicing_out_a_put_breaks_the_link() {
    let (reg, cap, acct) = setup();
    let create = reg.create_bucket(&cap, "reports").unwrap();
    let _put_a = reg
        .put(&cap, &acct, "reports", "a.txt", b"alpha".to_vec())
        .unwrap();
    let put_b = reg
        .put(&cap, &acct, "reports", "b.txt", b"bravo".to_vec())
        .unwrap();

    // Removing put_a: put_b's prev link no longer matches the create head.
    let chain: Vec<PutReceipt> = vec![put_b.clone()];
    assert_eq!(
        verify_chain_from(&chain, create.receipt_hash()),
        Err(ChainError::BrokenLink { seq: put_b.seq() })
    );
}

#[test]
fn the_trustless_read_still_re_witnesses_the_object() {
    // The receipt chain (provenance) and the object opening (the bytes) compose:
    // verify_chain attests WHO wrote WHAT root; verify_opening attests the served
    // bytes ARE in that root.
    let (reg, cap, acct) = setup();
    reg.create_bucket(&cap, "reports").unwrap();
    reg.put(&cap, &acct, "reports", "a.txt", b"alpha".to_vec())
        .unwrap();
    let opening = reg.verified_get(&cap, &acct, "reports", "a.txt").unwrap();
    assert!(verify_opening(&opening));

    let mut tampered = opening.clone();
    tampered.object.body = b"ALPHA".to_vec();
    assert!(
        !verify_opening(&tampered),
        "a flipped object byte is caught"
    );
}
