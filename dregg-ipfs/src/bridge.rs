//! `bridge` — the **verify-don't-trust** read over a decentralized transport.
//!
//! This is the payoff the [`crate::cid`] alignment buys: a dregg content-addressed
//! object can be pinned on, and fetched from, *any* IPFS node, and a reader
//! re-witnesses it against the same content commitment with **no trust in the node**
//! it fetched from. Two independent checks compose:
//!
//! 1. **content-addressing** ([`fetch_verified`]): the fetched bytes must hash to the
//!    CID they were fetched under. A node that flips a byte moves the hash and is
//!    refused — this is intrinsic to IPFS and needs no dregg machinery.
//! 2. **the dregg receipt** (the caller's existing trustless read): the cell commits
//!    the CID (it is bound into the cell's `content_root` and the signed publish /
//!    put receipt), so the reader checks that the CID it fetched under is the one the
//!    owner committed — caught by the storage bucket-commitment trustless read
//!    (`storage::bucket_commitment::verify_opening`) over the committed cell.
//!
//! Together: *which* bytes (the CID, by content-addressing) AND *whose/authorized*
//! bytes (the receipt, by the owner-signed cell). IPFS gives a decentralized, any-node
//! transport; dregg adds the authorized, receipted, cap-gated commitment IPFS alone
//! does not have. (Contrast Fleek: git→IPFS, trust the pin/gateway — no operation
//! receipt, no cap-gate, no verifiable cell.)

use crate::cid::{CODEC_DAG_CBOR, CODEC_RAW, Cid};
use crate::client::{IpfsClient, IpfsError};
use crate::unixfs::DEFAULT_CHUNK_SIZE;

/// The largest content [`pin_blob`] will pin as a single raw block. Above this a stock
/// `ipfs add` chunks the content into a UnixFS DAG (returning a dag-pb root that is
/// *not* `raw(blake3(bytes))`), so `pin_blob` refuses it with
/// [`IpfsError::BlockTooLarge`] and directs the caller to [`crate::unixfs::pin_file`]
/// rather than letting it fail later as a confusing CID mismatch.
pub const MAX_SINGLE_BLOCK: usize = DEFAULT_CHUNK_SIZE;

/// The CID a raw blob will be pinned under — `raw(blake3(bytes))`, the dregg content
/// commitment. Computing it locally lets a caller commit the CID in the cell
/// *before* (or independently of) pinning.
pub fn blob_cid(bytes: &[u8]) -> Cid {
    Cid::raw_blake3(bytes)
}

/// Wrap a `dregg-merge` delta's 32-byte blake3 content id as a CID (default
/// `dag-cbor` codec — a delta is a structured IPLD node). The CID's digest IS the
/// delta id, so fetching a delta by this CID and recomputing its id re-witnesses it.
/// This is the cleanest alignment in the system: the merge runtime's content id and
/// its IPFS address are the same 32 bytes.
pub fn delta_cid(delta_id: [u8; 32]) -> Cid {
    Cid::from_blake3_digest(CODEC_DAG_CBOR, delta_id)
}

/// Pin `bytes` to `client` and return the CID, asserting the node agreed on the
/// content address (a node that returns a CID other than `raw(blake3(bytes))` is
/// refused — it computed the address differently / dishonestly).
pub fn pin_blob<C: IpfsClient>(client: &C, bytes: &[u8]) -> Result<Cid, IpfsError> {
    // Above one block a real daemon chunks into a DAG; refuse here with a clear,
    // typed error (pointing at unixfs::pin_file) instead of a downstream CID mismatch.
    if bytes.len() > MAX_SINGLE_BLOCK {
        return Err(IpfsError::BlockTooLarge {
            size: bytes.len(),
            max: MAX_SINGLE_BLOCK,
        });
    }
    let expected = blob_cid(bytes);
    let got = client.put_raw(bytes)?;
    if got != expected {
        return Err(IpfsError::CidMismatch {
            requested: expected.to_string_cid(),
            got: got.to_string_cid(),
        });
    }
    Ok(got)
}

/// **The trustless fetch.** Fetch the bytes addressed by `cid` from `client` and
/// re-witness them by content-addressing: recompute `blake3` and require it equals
/// the CID's embedded digest. A lying node that serves tampered bytes is refused with
/// [`IpfsError::CidMismatch`].
///
/// Only whole-blob **raw blake3** CIDs are flat-verifiable here (a chunked dag-pb
/// root cannot be checked by a flat re-hash — see [`crate::cid`]); a non-raw CID is
/// refused with [`IpfsError::NotVerifiableByFlatHash`] rather than silently trusted.
pub fn fetch_verified<C: IpfsClient>(client: &C, cid: &Cid) -> Result<Vec<u8>, IpfsError> {
    if cid.codec != CODEC_RAW || !cid.is_raw_blake3() {
        return Err(IpfsError::NotVerifiableByFlatHash(cid.to_string_cid()));
    }
    let bytes = client.get(cid)?;
    let recomputed = Cid::raw_blake3(&bytes);
    if &recomputed != cid {
        return Err(IpfsError::CidMismatch {
            requested: cid.to_string_cid(),
            got: recomputed.to_string_cid(),
        });
    }
    Ok(bytes)
}

// -- the receipt half: which bytes AND whose bytes ----------------------------

/// The **owner-receipt check** seam — the second, `dregg`-native half of the
/// guarantee. [`fetch_verified`] answers *which* bytes (content-addressing: the bytes
/// hash to the CID). This answers *whose/authorized* bytes: that the CID a reader is
/// about to fetch is the one the **owner committed** in the cell, so a node cannot
/// serve some *other* validly-content-addressed object in place of the committed one.
///
/// On a dregg node this is exactly the storage bucket-commitment trustless read
/// (`storage::bucket_commitment::verify_opening` over the owner-signed cell): the
/// caller implements this trait by opening the committed cell and confirming the CID is
/// the one bound at the requested key. Kept as an injected trait so `dregg-ipfs` stays
/// dependency-light (no edge into the heavy storage/circuit stack) while the receipt
/// check runs in **code**, composed with the content-address check by
/// [`fetch_authorized`].
pub trait ReceiptCheck {
    /// Confirm `cid` is the content the owner committed for this read. `Ok(())` to
    /// authorize; an error (as a message) to refuse an un-committed / substituted CID.
    fn authorize(&self, cid: &Cid) -> Result<(), String>;
}

/// A concrete [`ReceiptCheck`]: the exact set of CIDs an owner committed (e.g. the
/// content roots opened from a committed bucket cell). Refuses any CID not in the set —
/// the "whose bytes" gate, with no trust in the serving node's claim about what it holds.
#[derive(Clone, Debug, Default)]
pub struct CommittedCids {
    committed: std::collections::HashSet<String>,
}

impl CommittedCids {
    /// An empty committed set.
    pub fn new() -> CommittedCids {
        CommittedCids::default()
    }

    /// Record a CID the owner committed (its cell binds this content address).
    pub fn commit(&mut self, cid: &Cid) {
        self.committed.insert(cid.to_string_cid());
    }

    /// Whether `cid` is in the committed set.
    pub fn contains(&self, cid: &Cid) -> bool {
        self.committed.contains(&cid.to_string_cid())
    }
}

impl ReceiptCheck for CommittedCids {
    fn authorize(&self, cid: &Cid) -> Result<(), String> {
        if self.contains(cid) {
            Ok(())
        } else {
            Err(format!("CID {cid} is not owner-committed"))
        }
    }
}

/// **The authorized trustless read.** Both halves of the guarantee run in code: first
/// the owner-receipt check ([`ReceiptCheck::authorize`]) confirms the CID is the one
/// the owner committed (*whose* bytes), then [`fetch_verified`] fetches and re-witnesses
/// the bytes against that CID by content-addressing (*which* bytes). A node cannot
/// serve tampered bytes (fails content-addressing) *nor* substitute a different
/// validly-addressed object (fails the receipt check).
pub fn fetch_authorized<C: IpfsClient, R: ReceiptCheck>(
    client: &C,
    receipt: &R,
    cid: &Cid,
) -> Result<Vec<u8>, IpfsError> {
    receipt.authorize(cid).map_err(IpfsError::Unauthorized)?;
    fetch_verified(client, cid)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::client::MockIpfs;

    #[test]
    fn pin_then_fetch_verified_round_trips() {
        let node = MockIpfs::new();
        let bytes = b"<h1>hello from a dregg cell</h1>";
        let cid = pin_blob(&node, bytes).unwrap();
        // The CID is the dregg content commitment of the blob.
        assert_eq!(cid, blob_cid(bytes));
        // Fetched + re-witnessed against the CID with no trust in the node.
        assert_eq!(fetch_verified(&node, &cid).unwrap(), bytes);
    }

    #[test]
    fn a_tampered_fetch_is_refused() {
        let node = MockIpfs::new();
        let cid = pin_blob(&node, b"the authorized bytes").unwrap();
        // The node turns malicious and serves different bytes under the same CID.
        node.tamper(&cid, b"OWNED BY THE NODE");
        let err = fetch_verified(&node, &cid).unwrap_err();
        assert!(matches!(err, IpfsError::CidMismatch { .. }), "got {err:?}");
    }

    #[test]
    fn a_chunked_dag_root_is_not_flat_verifiable() {
        let node = MockIpfs::new();
        // A dag-pb CID over some digest is refused by the flat verifier (rather than
        // trusted) — it must be checked through the chunker, not a flat re-hash.
        let dag = Cid::from_blake3_digest(crate::cid::CODEC_DAG_PB, [7u8; 32]);
        let err = fetch_verified(&node, &dag).unwrap_err();
        assert!(
            matches!(err, IpfsError::NotVerifiableByFlatHash(_)),
            "got {err:?}"
        );
    }

    #[test]
    fn pin_blob_refuses_oversized_content() {
        let node = MockIpfs::new();
        let big = vec![0u8; MAX_SINGLE_BLOCK + 1];
        // A single-block pin above the block limit is refused with a clear typed error
        // pointing at the DAG path — NOT a confusing downstream CID mismatch.
        assert!(matches!(
            pin_blob(&node, &big),
            Err(IpfsError::BlockTooLarge { .. })
        ));
    }

    #[test]
    fn pin_blob_surfaces_a_cid_mismatch_from_a_dishonest_node() {
        use crate::cid::Cid;
        // A node that computes the CID differently (returns some *other* CID for the
        // bytes) is refused. This exercises the whole point of step 1 end-to-end — the
        // MockIpfs put_raw is honest, so we use a small lying client.
        struct LyingNode;
        impl IpfsClient for LyingNode {
            fn put_raw(&self, _bytes: &[u8]) -> Result<Cid, IpfsError> {
                Ok(Cid::raw_blake3(b"not the bytes you handed me"))
            }
            fn get(&self, _cid: &Cid) -> Result<Vec<u8>, IpfsError> {
                unreachable!()
            }
            fn pin(&self, _cid: &Cid) -> Result<(), IpfsError> {
                Ok(())
            }
        }
        let err = pin_blob(&LyingNode, b"the honest bytes").unwrap_err();
        assert!(matches!(err, IpfsError::CidMismatch { .. }), "got {err:?}");
    }

    #[test]
    fn fetch_authorized_runs_both_halves() {
        let node = MockIpfs::new();
        let cid = pin_blob(&node, b"authorized content").unwrap();

        // With the CID committed, both checks pass.
        let mut receipt = CommittedCids::new();
        receipt.commit(&cid);
        assert_eq!(
            fetch_authorized(&node, &receipt, &cid).unwrap(),
            b"authorized content"
        );

        // A validly content-addressed but NOT owner-committed object is refused by the
        // receipt half even though content-addressing alone would accept it.
        let other = pin_blob(&node, b"some other valid object").unwrap();
        assert!(matches!(
            fetch_authorized(&node, &receipt, &other),
            Err(IpfsError::Unauthorized(_))
        ));

        // And a committed CID whose bytes the node tampered still fails the content
        // half — both gates compose.
        node.tamper(&cid, b"tampered!");
        assert!(matches!(
            fetch_authorized(&node, &receipt, &cid),
            Err(IpfsError::CidMismatch { .. })
        ));
    }

    #[test]
    fn delta_cid_carries_the_exact_delta_id() {
        // A dregg-merge delta id (32-byte blake3) re-encodes to a CID with the SAME
        // digest — fetch-by-CID + recompute-id re-witnesses the delta.
        let id = *blake3::hash(b"a delta").as_bytes();
        let cid = delta_cid(id);
        assert_eq!(cid.blake3_digest().unwrap(), id);
        assert_eq!(cid.codec, CODEC_DAG_CBOR);
    }
}
