//! Content-addressed asset storage — a dregg content commitment **is** an IPFS CID.
//!
//! The gateway content-addresses everything it hosts: a microsite asset, a launch's
//! landing page, and a launch's token metadata / image are each committed by their
//! [`Cid`] (a CIDv1 carrying a blake3 multihash, [`dregg_ipfs`]). The same address is
//! the content's IPFS address, so the bytes can be pinned + served from any node or
//! gateway and re-witnessed against the CID — verify-don't-trust over a decentralized
//! transport.
//!
//! The [`ContentStore`] wraps the injected [`IpfsClient`] seam ([`dregg_ipfs`]'s
//! in-process [`MockIpfs`] for hermetic tests, a real `KuboClient` in prod). Pinning
//! is optional: [`ContentStore::address`] gives the CID with no I/O (the pure content
//! address a manifest commits), while [`ContentStore::put`] pins the bytes and returns
//! the same CID.

use dregg_ipfs::{Cid, IpfsClient, IpfsError, blob_cid, fetch_verified, pin_blob};

/// The pure content address of `bytes` — its CIDv1 (blake3 multihash), computed with
/// no I/O. The commitment a manifest / cell records; equal to what [`ContentStore::put`]
/// returns after pinning.
pub fn address(bytes: &[u8]) -> Cid {
    blob_cid(bytes)
}

/// A content-addressed store over an injected [`IpfsClient`]. Pins bytes and returns
/// their [`Cid`]; fetches by CID with content-address re-verification (a tampered
/// block is refused, never returned).
pub struct ContentStore<C: IpfsClient> {
    client: C,
}

impl<C: IpfsClient> ContentStore<C> {
    /// A store backed by `client` (e.g. `MockIpfs::new()` in-process, a `KuboClient`
    /// over a real daemon in prod).
    pub fn new(client: C) -> ContentStore<C> {
        ContentStore { client }
    }

    /// The pure content address of `bytes` (no pin) — see [`address`].
    pub fn address(bytes: &[u8]) -> Cid {
        address(bytes)
    }

    /// Pin `bytes` and return their content address (CIDv1, blake3 multihash).
    pub fn put(&self, bytes: &[u8]) -> Result<Cid, IpfsError> {
        pin_blob(&self.client, bytes)
    }

    /// Fetch the bytes for `cid`, re-verifying the returned block against the address
    /// (content-addressing: a store that hands back tampered bytes is refused).
    pub fn get(&self, cid: &Cid) -> Result<Vec<u8>, IpfsError> {
        fetch_verified(&self.client, cid)
    }

    /// The backing IPFS client (for a caller that pins additional blocks directly).
    pub fn client(&self) -> &C {
        &self.client
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_ipfs::MockIpfs;

    #[test]
    fn address_is_the_pinned_cid_and_round_trips() {
        let store = ContentStore::new(MockIpfs::new());
        let bytes = b"a landing page".to_vec();
        let pure = ContentStore::<MockIpfs>::address(&bytes);
        let pinned = store.put(&bytes).expect("pin");
        assert_eq!(pure, pinned, "the pure address equals the pinned CID");
        assert_eq!(store.get(&pinned).expect("fetch"), bytes);
    }

    #[test]
    fn distinct_content_distinct_address() {
        let a = address(b"one");
        let b = address(b"two");
        assert_ne!(a, b);
        // The same bytes always hash to the same address (deterministic commitment).
        assert_eq!(address(b"one"), a);
    }

    #[test]
    fn a_tampered_block_is_refused_not_returned() {
        let store = ContentStore::new(MockIpfs::new());
        let cid = store.put(b"honest bytes").expect("pin");
        store.client().tamper(&cid, b"evil bytes");
        assert!(
            store.get(&cid).is_err(),
            "content-addressing refuses a tampered block"
        );
    }
}
