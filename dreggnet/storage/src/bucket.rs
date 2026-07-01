//! `bucket` — the bucket cell, its content commitment, and the trustless read.
//!
//! **A bucket is a dregg cell.** Its committed state holds the bucket **name**,
//! its **owner** (the cap holder — so *who stored what* is provable), a
//! **content commitment** ([`BucketCell::content_root`]) over the
//! content-addressed objects, and the **content** itself. This is the object-store
//! analog of the hosting [`SiteCell`]: where a site commits a path→asset map and
//! is served read-only over a host, a bucket commits a key→object map and is
//! read/written through cap-gated, metered, receipted operations — with a
//! **trustless read** ([`ObjectOpening`]) over the same commitment.
//!
//! ## The content commitment + the trustless opening (the verified read)
//!
//! The bucket commits to its objects with a **leaf-fold root**:
//!
//! - each object commits to a **leaf** = `H(key, content_type, body)`
//!   ([`object_leaf`]);
//! - the [`BucketCell::content_root`] is the fold over the *sorted-by-key* leaves
//!   ([`content_root`]).
//!
//! A [`verified_get`](crate::BucketRegistry::verified_get) returns an
//! [`ObjectOpening`]: the requested object's bytes, the bucket's committed root,
//! and the full ordered list of `(key, leaf)` digests. The pure
//! [`verify_opening`] then re-witnesses, with **no trust in the server**, that the
//! served bytes are the committed object:
//!
//! 1. recompute the target leaf from the *served bytes* and check it equals the
//!    leaf the opening lists at that key (the bytes bind to the leaf), and
//! 2. re-fold the listed leaves and check the result equals the claimed
//!    `content_root` (the leaf is included in the committed root).
//!
//! Only the target object's bytes travel — the other entries are present as their
//! small leaf digests — so a reader verifies one object against the whole bucket
//! commitment without downloading the bucket, and a server that flips a byte (or
//! the root) is caught. On a dregg node the leaf/root are the cell's committed
//! Poseidon2 umem hashes and the opening is a Merkle path; the property
//! [`verify_opening`] checks — *served bytes bind to the committed root* — is
//! identical. This is the object-store counterpart of `deos-view`'s trustless
//! cell projection that the hosting module documents.
//!
//! ## Real vs the on-chain write (honest)
//!
//! - **Real here:** the cell model, the cap-gate (a `storage-bucket/<name>` cap
//!   only authorizes operating the bucket named `<name>`), the content-address +
//!   content-root commitments, the receipts, the metering, and the
//!   self-verifying [`ObjectOpening`] read.
//! - **The on-chain write (the named seam):** committing the bucket cell to
//!   a dregg node — each put/delete as a real cap-gated `Effect::Write` witnessed
//!   as a receipt — lands on the surface `dreggnet-bridge`'s `dregg_verify` module
//!   names, the deliberate flip-on step the hosting module also documents. The
//!   OFF-chain content commitment here is real Poseidon2 on every build.
//!
//! [`SiteCell`]: ../../dreggnet_webapp/hosting/struct.SiteCell.html

use serde::{Deserialize, Serialize};

use crate::object::{BucketContent, Object};

/// A **bucket cell** — the dregg cell backing an object-store bucket.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BucketCell {
    /// The bucket name (the cap-gated namespace label).
    pub name: String,
    /// The owner cell/agent that created the bucket (the cap holder). Provable:
    /// every receipt binds `(name, owner, content_root)`.
    pub owner: String,
    /// A deterministic commitment over [`BucketCell::content`] ([`content_root`]).
    /// In-process the leaf-fold root; on a dregg node the cell's committed umem
    /// heap root. The anchor [`ObjectOpening`]/[`verify_opening`] re-witness each
    /// served object against.
    pub content_root: String,
    /// The bucket content (object key → object).
    pub content: BucketContent,
}

impl BucketCell {
    /// A fresh, empty bucket owned by `owner`.
    pub fn empty(name: impl Into<String>, owner: impl Into<String>) -> BucketCell {
        let content = BucketContent::new();
        let content_root = content_root(&content);
        BucketCell {
            name: name.into(),
            owner: owner.into(),
            content_root,
            content,
        }
    }

    /// Assemble a bucket from existing content, computing the [`content_root`].
    pub fn with_content(
        name: impl Into<String>,
        owner: impl Into<String>,
        content: BucketContent,
    ) -> BucketCell {
        let content_root = content_root(&content);
        BucketCell {
            name: name.into(),
            owner: owner.into(),
            content_root,
            content,
        }
    }

    /// Recompute + store the content root after a mutation. Returns the new root.
    pub fn recommit(&mut self) -> String {
        self.content_root = content_root(&self.content);
        self.content_root.clone()
    }

    /// Build a self-verifying [`ObjectOpening`] for `key`, if the object is
    /// present. The opening carries the object bytes, the committed root, and the
    /// full ordered leaf list — everything [`verify_opening`] needs to re-witness
    /// the bytes against the root with no trust in the source.
    pub fn open(&self, key: &str) -> Option<ObjectOpening> {
        let object = self.content.get(key)?.clone();
        // The canonical key under which the object lives (normalized).
        let nkey = crate::object::normalize_key(key);
        let leaves: Vec<(String, String)> = self
            .content
            .objects
            .iter()
            .map(|(k, o)| (k.clone(), object_leaf(k, o)))
            .collect();
        Some(ObjectOpening {
            key: nkey,
            object,
            bucket_root: self.content_root.clone(),
            leaves,
        })
    }
}

/// The per-object **leaf** commitment: `H(key, content_type, body)`. Binds the
/// object's identity (its key) to its bytes. The bucket root is the fold over
/// these.
///
/// The object's REAL wide 8-felt (~124-bit) Poseidon2 leaf digest (64-hex), the
/// same collision-resistant hash family the kernel commits a cell value with, on
/// every build (no FNV stand-in).
pub fn object_leaf(key: &str, object: &Object) -> String {
    use crate::object::poseidon2::{digest8, felts8_to_hex};
    felts8_to_hex(&digest8(&[
        key.as_bytes(),
        object.content_type.as_bytes(),
        &object.body,
    ]))
}

/// The bucket **content commitment**: the fold over the sorted-by-key object
/// leaves. Deterministic and order-independent of insertion (the `BTreeMap`
/// canonicalizes), and a single changed byte in any object moves it.
///
/// The REAL sorted-Poseidon2 cell-heap root — the same commitment a dregg light
/// client / the kernel understands (see [`fold_leaves`]), on every build.
pub fn content_root(content: &BucketContent) -> String {
    fold_leaves(
        content
            .objects
            .iter()
            .map(|(k, o)| (k.clone(), object_leaf(k, o))),
    )
}

/// Fold an ordered `(key, leaf)` sequence into the bucket root — the REAL
/// sorted-Poseidon2 cell-heap root.
///
/// Each object's wide 8-felt leaf digest is placed in the canonical SORTED
/// Poseidon2 Merkle heap keyed by `(collection = key, limb-index)`; the kernel's
/// heap-root function (`compute_heap_root_entries`) folds the root, and the
/// published commitment is the kernel's 8-felt faithful widening (`wire_commit_8`)
/// over the per-object wide limbs with the heap root as the final `iroot` — a WIDE
/// carrier chain with no 31-bit intermediate (the `FAITHFUL-STATE-COMMITMENT.md`
/// discipline, ~124-bit matching the proof's ~130-bit FRI floor). The object key is
/// bound twice: into the leaf digest (its identity) and into the heap collection
/// (its position), so a server cannot reorder/relabel without moving the root.
///
/// The in-circuit witness of the on-chain `Effect::Write` that commits this heap to
/// a dregg node is the circuit swarm's VK-epoch (named, not done here); this OFF-chain
/// commitment is real Poseidon2 + locally re-witnessable.
fn fold_leaves(leaves: impl IntoIterator<Item = (String, String)>) -> String {
    use crate::object::poseidon2::{felts8_to_hex, parse_felts8};
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::heap_root::compute_heap_root_entries;
    use dregg_circuit::poseidon2::{hash_bytes, wire_commit_8};

    let mut entries: Vec<((BabyBear, BabyBear), BabyBear)> = Vec::new();
    let mut limbs: Vec<BabyBear> = Vec::new();
    let mut count: u32 = 0;
    for (key, leaf) in leaves {
        count += 1;
        // The object's namespace within the cell heap (the sort-key collection).
        let coll = hash_bytes(key.as_bytes());
        // `leaf` is the object's own 64-hex wide digest ([`object_leaf`]).
        let d8 = parse_felts8(&leaf).unwrap_or([BabyBear::ZERO; 8]);
        for (i, &limb) in d8.iter().enumerate() {
            entries.push(((coll, BabyBear::new(i as u32)), limb));
            limbs.push(limb);
        }
    }
    let heap_root = compute_heap_root_entries(&entries);
    // The 4-felt domain header binds the bucket domain + object count and keeps the
    // fold total when the bucket is empty (`pre_limbs.len() >= 4`).
    let mut pre = vec![
        hash_bytes(b"dreggnet-bucket-content-root-v1"),
        BabyBear::new(count),
        BabyBear::ZERO,
        BabyBear::ZERO,
    ];
    pre.extend_from_slice(&limbs);
    felts8_to_hex(&wire_commit_8(&pre, heap_root))
}

/// A self-verifying read of one object against a bucket's committed root.
///
/// Carries the served object bytes, the claimed `bucket_root`, and the full
/// ordered `(key, leaf)` digest list. [`verify_opening`] checks it with no trust
/// in the source. On a dregg node this is a Merkle path against the cell's
/// committed root; here it is the full leaf list (small digests + the one
/// object's bytes), which has the same *bytes-bind-to-root* property.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObjectOpening {
    /// The (normalized) object key this opening is for.
    pub key: String,
    /// The served object (the bytes being re-witnessed).
    pub object: Object,
    /// The bucket's committed content root the object is opened against.
    pub bucket_root: String,
    /// The full ordered list of `(key, leaf-digest)` — the target's neighbors as
    /// compact digests, the target's own listed leaf included.
    pub leaves: Vec<(String, String)>,
}

impl ObjectOpening {
    /// Re-witness this opening — a convenience wrapper over [`verify_opening`].
    pub fn verify(&self) -> bool {
        verify_opening(self)
    }
}

/// **The trustless read.** Re-witness, with no trust in the source, that the
/// served object bytes are the object committed at `key` in `bucket_root`.
///
/// Returns `true` iff both hold:
/// 1. the leaf recomputed from the *served bytes* (`object_leaf(key, object)`)
///    equals the leaf the opening lists at `key` — the bytes bind to the leaf; and
/// 2. re-folding the listed leaves reproduces the claimed `bucket_root` — the leaf
///    is included in the committed root.
///
/// A flipped object byte fails (1); a tampered root or a doctored leaf list fails
/// (2). This is the object-store counterpart of the hosting module's trustless
/// cell projection.
pub fn verify_opening(op: &ObjectOpening) -> bool {
    // (1) the served bytes must reproduce the leaf the opening claims at `key`.
    let recomputed = object_leaf(&op.key, &op.object);
    let Some((_, listed_leaf)) = op.leaves.iter().find(|(k, _)| k == &op.key) else {
        return false; // the key is not even in the opening's leaf list
    };
    if &recomputed != listed_leaf {
        return false;
    }
    // (2) the listed leaves must re-fold to the claimed root.
    let refolded = fold_leaves(op.leaves.iter().cloned());
    refolded == op.bucket_root
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bucket_with(objs: &[(&str, &str)]) -> BucketCell {
        let mut c = BucketContent::new();
        for (k, v) in objs {
            c.put(k, v.as_bytes().to_vec());
        }
        BucketCell::with_content("b", "agent:ember", c)
    }

    #[test]
    fn content_root_is_deterministic_and_sensitive() {
        let a = bucket_with(&[("a.txt", "hi"), ("b.json", "{}")]);
        // Insertion order does not matter (BTreeMap canonical).
        let mut c = BucketContent::new();
        c.put("b.json", b"{}".to_vec());
        c.put("a.txt", b"hi".to_vec());
        let b = BucketCell::with_content("b", "agent:ember", c);
        assert_eq!(a.content_root, b.content_root);
        // A single changed byte moves the root.
        let d = bucket_with(&[("a.txt", "hI"), ("b.json", "{}")]);
        assert_ne!(a.content_root, d.content_root);
    }

    #[test]
    fn trustless_read_round_trips() {
        let bucket = bucket_with(&[("a.txt", "hello"), ("b.json", "{\"k\":1}")]);
        let op = bucket.open("a.txt").expect("present");
        assert!(verify_opening(&op));
        assert_eq!(op.object.body, b"hello");
        // Opening a missing key yields nothing.
        assert!(bucket.open("missing").is_none());
    }

    #[test]
    fn tampered_bytes_fail_verification() {
        let bucket = bucket_with(&[("a.txt", "hello"), ("b.json", "{}")]);
        let mut op = bucket.open("a.txt").unwrap();
        // A server flips a byte of the served object — verification must fail
        // because the recomputed leaf no longer matches the listed leaf.
        op.object.body = b"hellO".to_vec();
        assert!(!verify_opening(&op));
    }

    /// The anti-aliasing tooth over the trustless read. A malicious host substitutes
    /// the served bytes for a SAME-LENGTH `+p` alias — the exact collision class the
    /// old 4-byte `% p` packing accepted as genuine. With the injective packing the
    /// substitution now moves the object leaf, so `verify_opening` REJECTS it and the
    /// bucket `content_root` moves. Before the fix this substitution verified as real.
    #[test]
    fn same_length_alias_substitution_is_rejected_by_verify_opening() {
        use dregg_circuit::field::BabyBear;

        // A `+p` alias pair over one 4-byte chunk (both length 4).
        let honest = vec![0x01u8, 0x00, 0x00, 0x00];
        let forged = vec![0x02u8, 0x00, 0x00, 0x78];
        // Witness that the OLD shared primitive aliased them (the pre-fix hole).
        assert_eq!(
            BabyBear::from_bytes_packed(&honest),
            BabyBear::from_bytes_packed(&forged),
            "the old 4-byte %p packing aliases this pair"
        );

        let mut c = BucketContent::new();
        c.put_object("blob.bin", Object::new("application/octet-stream", honest));
        c.put("b.json", b"{}".to_vec());
        let bucket = BucketCell::with_content("b", "agent:ember", c);

        // The honest served bytes verify.
        let op = bucket.open("blob.bin").expect("present");
        assert!(op.verify(), "the honest bytes re-witness against the root");

        // A same-length aliasing substitution is now REFUSED (it verified before).
        let mut tampered = op.clone();
        tampered.object.body = forged.clone();
        assert!(
            !verify_opening(&tampered),
            "the same-length +p alias substitution is caught by the injective leaf"
        );

        // And the content_root itself separates the two contents.
        let mut c2 = BucketContent::new();
        c2.put_object("blob.bin", Object::new("application/octet-stream", forged));
        c2.put("b.json", b"{}".to_vec());
        let forged_bucket = BucketCell::with_content("b", "agent:ember", c2);
        assert_ne!(
            bucket.content_root, forged_bucket.content_root,
            "the injective packing moves the content_root for the alias pair"
        );
    }

    #[test]
    fn tampered_root_fails_verification() {
        let bucket = bucket_with(&[("a.txt", "hello"), ("b.json", "{}")]);
        let mut op = bucket.open("a.txt").unwrap();
        op.bucket_root = "0000000000000000".to_string();
        assert!(!verify_opening(&op));
    }

    #[test]
    fn doctored_neighbor_leaf_fails_verification() {
        let bucket = bucket_with(&[("a.txt", "hello"), ("b.json", "{}")]);
        let mut op = bucket.open("a.txt").unwrap();
        // Tamper a *different* object's listed leaf — the re-fold no longer
        // reproduces the committed root, so the read is rejected.
        if let Some(slot) = op.leaves.iter_mut().find(|(k, _)| k != &op.key) {
            slot.1 = "ffffffffffffffff".to_string();
        }
        assert!(!verify_opening(&op));
    }

    /// The bucket `content_root` and the object leaf are the REAL Poseidon2
    /// cell-heap commitment — FNV is GONE from the content-commitment path. The wide
    /// (8-felt, ~124-bit) commitment is byte-sensitive, and the trustless
    /// `verify_opening` re-witnesses the served bytes against the real root (✓),
    /// rejecting a tampered byte (✗).
    #[test]
    fn content_root_is_the_real_poseidon2_root_not_fnv() {
        let bucket = bucket_with(&[("a.txt", "hello"), ("b.json", "{\"k\":1}")]);

        // (a) the verified root + leaf are the 64-hex (8-felt, ~124-bit)
        //     collision-resistant Poseidon2 commitment.
        assert_eq!(
            bucket.content_root.len(),
            64,
            "the bucket root is the wide Poseidon2 commitment (64 hex)"
        );
        assert!(bucket.content_root.chars().all(|c| c.is_ascii_hexdigit()));
        let leaf = object_leaf("/a.txt", bucket.content.get("a.txt").unwrap());
        assert_eq!(
            leaf.len(),
            64,
            "the verified object leaf is the wide Poseidon2 digest"
        );

        // (b) determinism + input-order independence (the BTreeMap canonicalizes).
        let mut c = BucketContent::new();
        c.put("b.json", b"{\"k\":1}".to_vec());
        c.put("a.txt", b"hello".to_vec());
        let reordered = BucketCell::with_content("b", "agent:ember", c);
        assert_eq!(bucket.content_root, reordered.content_root);

        // (c) sensitivity: a flipped object byte, a moved key, and a changed
        //     content-type each move the wide root.
        let flip = bucket_with(&[("a.txt", "hellO"), ("b.json", "{\"k\":1}")]);
        assert_ne!(
            bucket.content_root, flip.content_root,
            "a flipped byte moves the root"
        );
        let moved = bucket_with(&[("a2.txt", "hello"), ("b.json", "{\"k\":1}")]);
        assert_ne!(
            bucket.content_root, moved.content_root,
            "a moved key moves the root"
        );
        let mut ct = BucketContent::new();
        ct.put_object("a.txt", Object::new("text/plain", b"hello".to_vec()));
        ct.put("b.json", b"{\"k\":1}".to_vec());
        let typed = BucketCell::with_content("b", "agent:ember", ct);
        assert_ne!(
            bucket.content_root, typed.content_root,
            "a changed content-type moves the root"
        );

        // (d) the trustless read re-witnesses against the REAL root, and a tampered
        //     byte is refused.
        let op = bucket.open("a.txt").expect("present");
        assert!(
            op.verify(),
            "the served bytes re-witness against the Poseidon2 root"
        );
        let mut tampered = op.clone();
        tampered.object.body = b"hellO".to_vec();
        assert!(
            !tampered.verify(),
            "a flipped served byte is refused against the Poseidon2 root"
        );
    }
}
