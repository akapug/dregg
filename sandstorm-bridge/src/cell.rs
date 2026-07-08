//! The grain's private data = a dregg cell's **umem heap**.
//!
//! In Sandstorm a grain's `/var` is a read-write bind-mount, private to that grain,
//! that the app stores its database/state in. On dregg that `/var` *is* the cell's
//! umem heap: a keyed byte store that commits to a content-addressed **`data_root`**.
//! The difference Sandstorm cannot offer: the root is a commitment, so a checkpoint
//! is re-witnessable (a backup that proves what it contains), and the transitions —
//! not just a snapshot — are what get committed.
//!
//! This is the prototype's stand-in for `turn/src/umem.rs` + `durable/`: a real
//! content-addressed heap (a sha256 **Merkle tree** over the sorted entries) with the
//! same shape the grain lifecycle leans on (commit → `data_root`; restore from a
//! `data_root`).
//!
//! The heap commits to a Merkle root over its sorted, length-prefixed `(key, value)`
//! leaves, so a single entry's inclusion under the root is provable *without the rest
//! of the heap*: [`Umem::prove`] emits an [`InclusionProof`] for one key, and the
//! host-state-free [`verify_inclusion`] checks `{key, value, proof, root}` alone. This
//! is the tooth the trustless-serve weld leans on — a visitor re-hashes just the served
//! card and, with the proof, confirms it is the value at `key` under a root they trust,
//! independent of the (arbitrarily large, stateful) rest of `/var`.

use std::collections::BTreeMap;

use sha2::{Digest, Sha256};

use crate::spk::base32;

/// Domain-separation tags for the Merkle hash — a leaf and an internal node can never
/// collide (a leaf is `H(0x00 ‖ …)`, a node `H(0x01 ‖ …)`), so an internal node cannot
/// be reinterpreted as a leaf to forge an inclusion proof, and the empty heap has its
/// own tag (`0x02`) rather than aliasing any node.
const LEAF_TAG: u8 = 0x00;
const NODE_TAG: u8 = 0x01;
const EMPTY_TAG: u8 = 0x02;

/// The leaf commitment for one `(key, value)` entry: `H(0x00 ‖ klen ‖ key ‖ vlen ‖ value)`.
/// Length-prefixed so `(key, value)` is unambiguous, domain-tagged so it is never an
/// internal node.
fn leaf_hash(key: &str, value: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update([LEAF_TAG]);
    h.update((key.len() as u64).to_le_bytes());
    h.update(key.as_bytes());
    h.update((value.len() as u64).to_le_bytes());
    h.update(value);
    h.finalize().into()
}

/// An internal Merkle node: `H(0x01 ‖ left ‖ right)`.
fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update([NODE_TAG]);
    h.update(left);
    h.update(right);
    h.finalize().into()
}

/// Fold sorted leaves into a Merkle root. An odd node at a level is *promoted*
/// (carried up unchanged), so a one-leaf heap's root is that leaf's hash. The empty
/// heap commits to `H(0x02)`.
fn merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {
    if leaves.is_empty() {
        let mut h = Sha256::new();
        h.update([EMPTY_TAG]);
        return h.finalize().into();
    }
    let mut level = leaves.to_vec();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i < level.len() {
            if i + 1 < level.len() {
                next.push(node_hash(&level[i], &level[i + 1]));
                i += 2;
            } else {
                next.push(level[i]); // promote the odd node
                i += 1;
            }
        }
        level = next;
    }
    level[0]
}

/// Encode a 32-byte Merkle root as the `umem1…` [`DataRoot`] wire string.
fn root_string(root: &[u8; 32]) -> String {
    format!("umem1{}", base32(root))
}

/// One step of an [`InclusionProof`], bottom-up: the sibling to combine with the running
/// hash on the given side, or `Promote` when the node had no sibling at that level (it was
/// carried up unchanged).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofStep {
    /// Sibling on the left: `node = H(0x01 ‖ sibling ‖ node)`.
    Left([u8; 32]),
    /// Sibling on the right: `node = H(0x01 ‖ node ‖ sibling)`.
    Right([u8; 32]),
    /// Odd node at this level, carried up unchanged.
    Promote,
}

/// A Merkle inclusion proof that a single key's value is a leaf under a committed root —
/// the sibling path from that leaf to the root. Small (log-sized in the heap), and
/// verified with [`verify_inclusion`] against `{key, value, root}` alone; no heap needed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InclusionProof {
    pub steps: Vec<ProofStep>,
}

/// **Verify a single-leaf inclusion proof — host-state-free.** Given only the served
/// `{key, value}`, the `proof`, and a `root` the caller trusts (obtained independently —
/// e.g. an owner-attested root from the ledger, NOT from the serving host), recompute the
/// leaf and fold the proof to a root and check it matches. `true` iff `value` is exactly
/// the value at `key` under `root`. A light client runs this against just the card bytes.
pub fn verify_inclusion(root: &DataRoot, key: &str, value: &[u8], proof: &InclusionProof) -> bool {
    let mut acc = leaf_hash(key, value);
    for step in &proof.steps {
        acc = match step {
            ProofStep::Left(sib) => node_hash(sib, &acc),
            ProofStep::Right(sib) => node_hash(&acc, sib),
            ProofStep::Promote => acc,
        };
    }
    DataRoot(root_string(&acc)) == *root
}

/// A content commitment to a umem heap state (`data_root`). Deterministic in the
/// heap contents, order-free.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DataRoot(pub String);

/// The grain's read-write `/var`, realized as a dregg cell's umem heap.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Umem {
    entries: BTreeMap<String, Vec<u8>>,
}

impl Umem {
    pub fn new() -> Self {
        Umem::default()
    }

    pub fn get(&self, key: &str) -> Option<&[u8]> {
        self.entries.get(key).map(|v| v.as_slice())
    }

    pub fn put(&mut self, key: impl Into<String>, value: impl Into<Vec<u8>>) {
        self.entries.insert(key.into(), value.into());
    }

    pub fn remove(&mut self, key: &str) -> bool {
        self.entries.remove(key).is_some()
    }

    /// Drop every entry — used when a workload returns a fresh `/var` image.
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Iterate the heap entries (`key -> bytes`) in sorted key order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &[u8])> {
        self.entries.iter().map(|(k, v)| (k.as_str(), v.as_slice()))
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Total stored bytes — the storage meter's input (per-MB billing).
    pub fn stored_bytes(&self) -> usize {
        self.entries.values().map(|v| v.len()).sum()
    }

    /// Commit to the current heap state — the `data_root` a checkpoint records.
    /// Content-addressed as the sha256 **Merkle root** over the sorted, length-prefixed
    /// `(key, value)` leaves, so two heaps with the same contents commit to the same root
    /// regardless of insert order (the property that makes a checkpoint re-witnessable) —
    /// AND a single entry's inclusion is provable under this root via [`prove`](Self::prove)
    /// without disclosing the rest of the heap.
    pub fn commit(&self) -> DataRoot {
        let leaves: Vec<[u8; 32]> = self.entries.iter().map(|(k, v)| leaf_hash(k, v)).collect();
        DataRoot(root_string(&merkle_root(&leaves)))
    }

    /// **Prove one key's value is included under [`commit`](Self::commit)'s root** — the
    /// Merkle sibling path from that leaf to the root, so a visitor can verify the served
    /// value is the value at `key` under a trusted root with only `{key, value, proof,
    /// root}` (see [`verify_inclusion`]) — never the whole heap. `None` if `key` is absent.
    ///
    /// This is what makes the serve path witnessable for a *real, stateful* `/var`: a light
    /// client re-hashing just the served card, with this proof, reproduces the whole-heap
    /// root — it does not need (and never sees) the grain's other keys.
    pub fn prove(&self, key: &str) -> Option<InclusionProof> {
        let idx = self.entries.keys().position(|k| k == key)?;
        // Build the level stack over the sorted leaves (same order as `commit`).
        let leaves: Vec<[u8; 32]> = self.entries.iter().map(|(k, v)| leaf_hash(k, v)).collect();
        let mut levels: Vec<Vec<[u8; 32]>> = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let cur = levels.last().unwrap();
            let mut next = Vec::with_capacity(cur.len().div_ceil(2));
            let mut i = 0;
            while i < cur.len() {
                if i + 1 < cur.len() {
                    next.push(node_hash(&cur[i], &cur[i + 1]));
                    i += 2;
                } else {
                    next.push(cur[i]);
                    i += 1;
                }
            }
            levels.push(next);
        }
        // Walk up, recording the sibling (or a promotion) at each level.
        let mut steps = Vec::with_capacity(levels.len().saturating_sub(1));
        let mut index = idx;
        for level in &levels[..levels.len() - 1] {
            if index % 2 == 1 {
                steps.push(ProofStep::Left(level[index - 1]));
            } else if index + 1 < level.len() {
                steps.push(ProofStep::Right(level[index + 1]));
            } else {
                steps.push(ProofStep::Promote);
            }
            index /= 2;
        }
        Some(InclusionProof { steps })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn commit_is_order_free_and_content_addressed() {
        let mut a = Umem::new();
        a.put("notes/1", b"hello".to_vec());
        a.put("notes/2", b"world".to_vec());

        let mut b = Umem::new();
        // Insert in the opposite order.
        b.put("notes/2", b"world".to_vec());
        b.put("notes/1", b"hello".to_vec());

        assert_eq!(a.commit(), b.commit());

        // A different value → a different root.
        b.put("notes/2", b"WORLD".to_vec());
        assert_ne!(a.commit(), b.commit());
    }

    #[test]
    fn empty_commit_is_stable() {
        assert_eq!(Umem::new().commit(), Umem::new().commit());
        assert!(Umem::new().commit().0.starts_with("umem1"));
    }

    /// The inclusion proof works for a **non-degenerate** heap: put several keys, prove one,
    /// and verify it against the WHOLE-heap root with only `{key, value, proof, root}` — the
    /// rest of `/var` is neither needed nor disclosed.
    #[test]
    fn inclusion_proof_verifies_against_the_whole_heap_root() {
        let mut u = Umem::new();
        for i in 0..7 {
            u.put(format!("k{i}"), format!("value-{i}").into_bytes());
        }
        let root = u.commit();
        // Prove the middle key against the full root.
        let key = "k3";
        let value = u.get(key).unwrap().to_vec();
        let proof = u.prove(key).expect("key present → a proof");
        assert!(
            verify_inclusion(&root, key, &value, &proof),
            "the card verifies as the leaf at k3 under the whole-heap root"
        );
        // Also holds for the first and last keys (proof-path edge cases).
        for key in ["k0", "k6"] {
            let value = u.get(key).unwrap().to_vec();
            let proof = u.prove(key).unwrap();
            assert!(verify_inclusion(&root, key, &value, &proof));
        }
    }

    /// The proof binds the exact `(key, value)` under the exact root: a wrong value, a wrong
    /// key, or a stale root all fail. This is the tooth a tampering host cannot beat without
    /// finding a sha256 collision.
    #[test]
    fn inclusion_proof_rejects_wrong_value_key_or_root() {
        let mut u = Umem::new();
        u.put("a", b"one".to_vec());
        u.put("b", b"two".to_vec());
        u.put("c", b"three".to_vec());
        let root = u.commit();
        let proof = u.prove("b").unwrap();
        assert!(verify_inclusion(&root, "b", b"two", &proof));
        // Wrong value at the proven key.
        assert!(!verify_inclusion(&root, "b", b"TWO", &proof));
        // Right value+proof but claimed under the wrong key.
        assert!(!verify_inclusion(&root, "a", b"two", &proof));
        // Right leaf+proof but against a different (stale) root.
        let mut u2 = u.clone();
        u2.put("b", b"two!".to_vec());
        let stale = u2.commit();
        assert!(!verify_inclusion(&stale, "b", b"two", &proof));
        // An absent key has no proof.
        assert!(u.prove("zzz").is_none());
    }

    /// A single-entry heap: its root IS the leaf hash, the proof is empty, and it still
    /// verifies — the degenerate case is handled, not special-cased away.
    #[test]
    fn inclusion_proof_for_a_single_entry_heap() {
        let mut u = Umem::new();
        u.put("only", b"solo".to_vec());
        let root = u.commit();
        let proof = u.prove("only").unwrap();
        assert!(proof.steps.is_empty(), "a lone leaf needs no siblings");
        assert!(verify_inclusion(&root, "only", b"solo", &proof));
    }
}
