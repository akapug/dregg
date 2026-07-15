//! Content-addressed blob store (nameless writes).
//!
//! Write returns hash. No allocation, no indirection.
//! Each write has a computron cost (proportional to size).
//! Each stored blob has an OWNER (quota cell that paid for it).
//! Deletion refunds a portion of the computron cost.
//!
//! # Lean-spec status
//!
//! No Lean theorem specifies `ContentStore` yet.
//! `metatheory/Dregg2/Storage/BucketCommitment.lean::read_sound` proves the
//! trustless read for the COMMITTED bucket store
//! ([`crate::bucket_commitment`] — an opening verified against a published
//! Poseidon2 content root); this module is a local, unilateral BLAKE3 blob
//! store with no openings to verify, so that theorem does not apply here
//! and is not claimed. The store's executable contract — deterministic,
//! collision-sensitive content addressing; read-integrity (a read returns
//! the exact preimage of the requested hash); owner-gated splice/delete —
//! is pinned by the `prop_*` tests below, ready to bind when a Lean spec
//! for the local store lands.

use std::collections::HashMap;
use std::io;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::quota::SpaceBank;
use crate::{ComputronRefund, ContentHash, QuotaId, StorageError};

/// One owner's stake in a blob. Dedup is accounted **per owner**: each
/// deduplicating writer holds its own reference count and was charged its own
/// cost, so a second writer can neither be deleted out from under (only its
/// own references decrement its stake) nor destroy the blob for the others.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct OwnerRef {
    /// How many live references this owner holds (one per successful `write`).
    ref_count: u32,
    /// The computron cost charged for a single reference — the amount refunded
    /// to *this* owner when it drops a reference. (Cost is deterministic in
    /// size, so every reference this owner holds cost the same.)
    unit_cost: u64,
}

/// Metadata about a stored blob. The physical bytes exist once; ownership is a
/// map so N distinct quota cells can independently hold references.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct BlobMeta {
    /// Size in bytes (physical — charged once per owner-reference in quota).
    size: u64,
    /// Per-owner reference accounting. Never empty while the blob exists.
    owners: HashMap<QuotaId, OwnerRef>,
}

impl BlobMeta {
    /// Total live references across all owners.
    fn total_refs(&self) -> u32 {
        self.owners.values().map(|o| o.ref_count).sum()
    }
}

/// Content-addressed store. Nameless writes: data in, hash out.
#[derive(Debug)]
pub struct ContentStore {
    /// Blob data keyed by content hash.
    blobs: HashMap<ContentHash, Vec<u8>>,
    /// Metadata keyed by content hash.
    meta: HashMap<ContentHash, BlobMeta>,
    /// The space bank governing quota.
    pub bank: SpaceBank,
    /// Optional hard cap on total *physical* bytes stored (distinct from the
    /// per-owner quota byte caps). Bounds the in-memory/on-disk map itself so
    /// an operator's node cannot be OOM'd by unbounded distinct writes.
    max_total_bytes: Option<u64>,
    /// Running total of physical bytes stored (one count per distinct blob,
    /// not per owner-reference). Maintained incrementally.
    total_stored_bytes: u64,
}

/// Serializable snapshot of a [`ContentStore`] for crash-safe persistence.
#[derive(Serialize, Deserialize)]
struct StoreSnapshot {
    /// Snapshot format version (for forward migration).
    version: u32,
    blobs: Vec<(ContentHash, Vec<u8>)>,
    meta: Vec<(ContentHash, BlobMeta)>,
    bank: SpaceBank,
    max_total_bytes: Option<u64>,
    total_stored_bytes: u64,
}

const SNAPSHOT_VERSION: u32 = 1;

impl ContentStore {
    /// Create a new content store with the given space bank (no store cap).
    pub fn new(bank: SpaceBank) -> Self {
        Self {
            blobs: HashMap::new(),
            meta: HashMap::new(),
            bank,
            max_total_bytes: None,
            total_stored_bytes: 0,
        }
    }

    /// Create a store with a hard cap on total physical bytes.
    pub fn with_capacity(bank: SpaceBank, max_total_bytes: u64) -> Self {
        Self {
            blobs: HashMap::new(),
            meta: HashMap::new(),
            bank,
            max_total_bytes: Some(max_total_bytes),
            total_stored_bytes: 0,
        }
    }

    /// Set (or clear) the global physical-byte cap.
    pub fn set_capacity(&mut self, max_total_bytes: Option<u64>) {
        self.max_total_bytes = max_total_bytes;
    }

    /// Total physical bytes stored (one count per distinct blob).
    pub fn stored_bytes(&self) -> u64 {
        self.total_stored_bytes
    }

    /// Hash data using blake3.
    fn hash(data: &[u8]) -> ContentHash {
        let h = blake3::hash(data);
        ContentHash(*h.as_bytes())
    }

    /// Write data to the store. Returns the content hash.
    /// The payer's quota is charged for the write.
    ///
    /// Deduplication is **per owner**: a second writer of identical content is
    /// charged independently and gains its own reference; it does not inherit
    /// or disturb the first writer's stake. The physical bytes are stored once.
    pub fn write(&mut self, data: &[u8], payer: &QuotaId) -> Result<ContentHash, StorageError> {
        let hash = Self::hash(data);
        let size = data.len() as u64;
        let is_new_blob = !self.meta.contains_key(&hash);

        // Enforce the global physical-byte cap BEFORE charging — only new
        // distinct content consumes physical space; a dedup write does not.
        if is_new_blob {
            if let Some(max) = self.max_total_bytes {
                if self.total_stored_bytes.saturating_add(size) > max {
                    return Err(StorageError::StoreCapExceeded {
                        current: self.total_stored_bytes,
                        max,
                        attempted: size,
                    });
                }
            }
        }

        // Charge the payer (they claim storage under their own quota). Checked
        // arithmetic inside the bank rejects overflow before any mutation.
        let cost = self.bank.charge_write(payer, size)?;

        match self.meta.get_mut(&hash) {
            Some(meta) => {
                // Existing content: add/increment THIS owner's reference.
                let entry = meta.owners.entry(*payer).or_insert(OwnerRef {
                    ref_count: 0,
                    unit_cost: cost,
                });
                entry.ref_count = entry.ref_count.saturating_add(1);
                entry.unit_cost = cost;
            }
            None => {
                self.blobs.insert(hash, data.to_vec());
                let mut owners = HashMap::new();
                owners.insert(
                    *payer,
                    OwnerRef {
                        ref_count: 1,
                        unit_cost: cost,
                    },
                );
                self.meta.insert(hash, BlobMeta { size, owners });
                self.total_stored_bytes = self.total_stored_bytes.saturating_add(size);
            }
        }

        Ok(hash)
    }

    /// Read data by content hash.
    pub fn read(&self, hash: &ContentHash) -> Option<&[u8]> {
        self.blobs.get(hash).map(|v| v.as_slice())
    }

    /// Splice: replace a subrange of an existing blob, producing a new blob.
    /// This is delete(old) + write(new) atomically.
    pub fn splice(
        &mut self,
        old_hash: &ContentHash,
        offset: usize,
        new_data: &[u8],
        payer: &QuotaId,
    ) -> Result<ContentHash, StorageError> {
        // Read old data.
        let old_data = self
            .blobs
            .get(old_hash)
            .ok_or(StorageError::NotFound(*old_hash))?
            .clone();

        // Verify ownership: the caller must hold a reference to the old blob.
        let old_meta = self
            .meta
            .get(old_hash)
            .ok_or(StorageError::NotFound(*old_hash))?;
        if !old_meta.owners.contains_key(payer) {
            let some_owner = old_meta.owners.keys().next().copied().unwrap_or(*payer);
            return Err(StorageError::NotOwner {
                hash: *old_hash,
                owner: some_owner,
                caller: *payer,
            });
        }

        // Construct new data: old[..offset] + new_data + old[offset+new_data.len()..]
        let end = (offset + new_data.len()).min(old_data.len());
        let mut spliced = Vec::with_capacity(old_data.len());
        spliced.extend_from_slice(&old_data[..offset.min(old_data.len())]);
        spliced.extend_from_slice(new_data);
        if end < old_data.len() {
            spliced.extend_from_slice(&old_data[end..]);
        }

        // Delete old (with refund).
        self.delete(old_hash, payer)?;

        // Write new.
        self.write(&spliced, payer)
    }

    /// Drop one of `owner`'s references to a blob. Each owner can only drop its
    /// own references; a caller with no reference is refused with `NotOwner`.
    /// The physical blob is removed only when the LAST reference across ALL
    /// owners is dropped, so one owner's delete can never destroy another
    /// owner's data. Returns a computron refund to `owner`.
    pub fn delete(
        &mut self,
        hash: &ContentHash,
        owner: &QuotaId,
    ) -> Result<ComputronRefund, StorageError> {
        let meta = self
            .meta
            .get_mut(hash)
            .ok_or(StorageError::NotFound(*hash))?;

        let Some(owner_ref) = meta.owners.get_mut(owner) else {
            let some_owner = meta.owners.keys().next().copied().unwrap_or(*owner);
            return Err(StorageError::NotOwner {
                hash: *hash,
                owner: some_owner,
                caller: *owner,
            });
        };

        let size = meta.size;
        let unit_cost = owner_ref.unit_cost;

        owner_ref.ref_count -= 1;
        if owner_ref.ref_count == 0 {
            meta.owners.remove(owner);
        }

        // Remove the physical blob only when no owner holds any reference.
        if meta.owners.is_empty() {
            self.blobs.remove(hash);
            self.meta.remove(hash);
            self.total_stored_bytes = self.total_stored_bytes.saturating_sub(size);
        }

        // Refund THIS owner for the single reference it dropped.
        self.bank.process_refund(owner, unit_cost, size)
    }

    /// The number of live references `owner` holds to `hash` (0 if none).
    pub fn owner_ref_count(&self, hash: &ContentHash, owner: &QuotaId) -> u32 {
        self.meta
            .get(hash)
            .and_then(|m| m.owners.get(owner))
            .map(|o| o.ref_count)
            .unwrap_or(0)
    }

    /// Total live references to `hash` across all owners (0 if absent).
    pub fn total_ref_count(&self, hash: &ContentHash) -> u32 {
        self.meta.get(hash).map(|m| m.total_refs()).unwrap_or(0)
    }

    /// Check if a blob exists.
    pub fn contains(&self, hash: &ContentHash) -> bool {
        self.blobs.contains_key(hash)
    }

    /// Get the size of a blob.
    pub fn blob_size(&self, hash: &ContentHash) -> Option<u64> {
        self.meta.get(hash).map(|m| m.size)
    }

    /// Total bytes stored in this content store.
    pub fn total_bytes(&self) -> u64 {
        self.meta.values().map(|m| m.size).sum()
    }

    /// Number of blobs stored.
    pub fn blob_count(&self) -> usize {
        self.blobs.len()
    }

    /// Serialize the full store (blobs, per-owner metadata, quota bank, caps)
    /// into a versioned snapshot buffer.
    fn snapshot(&self) -> StoreSnapshot {
        StoreSnapshot {
            version: SNAPSHOT_VERSION,
            blobs: self.blobs.iter().map(|(h, d)| (*h, d.clone())).collect(),
            meta: self.meta.iter().map(|(h, m)| (*h, m.clone())).collect(),
            bank: self.bank.clone(),
            max_total_bytes: self.max_total_bytes,
            total_stored_bytes: self.total_stored_bytes,
        }
    }

    /// Persist the store to `path` **atomically** and durably: the snapshot is
    /// written to a sibling temp file, fsync'd, then `rename`d over the target
    /// (an atomic replace on POSIX), and finally the containing directory is
    /// fsync'd so the rename itself survives a crash. A crash at any point
    /// leaves either the old complete snapshot or the new complete snapshot —
    /// never a torn file. This turns the store from demo-grade (all state lost
    /// on restart) into one that survives process death.
    pub fn save_to(&self, path: impl AsRef<Path>) -> io::Result<()> {
        use std::fs::{self, File, OpenOptions};
        use std::io::Write;

        let path = path.as_ref();
        let bytes = postcard::to_stdvec(&self.snapshot())
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        let dir = path.parent().unwrap_or_else(|| Path::new("."));
        fs::create_dir_all(dir)?;
        let tmp = path.with_extension("tmp");

        {
            let mut f = OpenOptions::new()
                .create(true)
                .write(true)
                .truncate(true)
                .open(&tmp)?;
            f.write_all(&bytes)?;
            f.flush()?;
            f.sync_all()?;
        }

        fs::rename(&tmp, path)?;

        // fsync the directory so the rename is durable across a crash.
        if let Ok(dirf) = File::open(dir) {
            let _ = dirf.sync_all();
        }
        Ok(())
    }

    /// Reconstruct a store from a snapshot written by [`save_to`]. Returns an
    /// error (not a panic) on a missing, truncated, or otherwise corrupt file.
    pub fn load_from(path: impl AsRef<Path>) -> io::Result<Self> {
        let bytes = std::fs::read(path)?;
        let snap: StoreSnapshot = postcard::from_bytes(&bytes)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        if snap.version != SNAPSHOT_VERSION {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "unsupported snapshot version {} (expected {})",
                    snap.version, SNAPSHOT_VERSION
                ),
            ));
        }
        Ok(Self {
            blobs: snap.blobs.into_iter().collect(),
            meta: snap.meta.into_iter().collect(),
            bank: snap.bank,
            max_total_bytes: snap.max_total_bytes,
            total_stored_bytes: snap.total_stored_bytes,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A store with two funded quota cells (alice, bob).
    fn store_with_two_cells() -> (ContentStore, QuotaId, QuotaId) {
        let mut bank = SpaceBank::new(1, 1, 0.5);
        let alice = bank.allocate_quota([0xA1; 32], 1_000_000, None);
        let bob = bank.allocate_quota([0xB0; 32], 1_000_000, None);
        (ContentStore::new(bank), alice, bob)
    }

    /// Content addressing is deterministic (same bytes → same address,
    /// across writes, across store instances, and equal to the raw BLAKE3
    /// of the data) and collision-sensitive (negative pole: every
    /// single-byte mutation of the data yields a DIFFERENT address).
    #[test]
    fn prop_content_addressing_deterministic_and_collision_sensitive() {
        let (mut s1, a1, _) = store_with_two_cells();
        let (mut s2, a2, _) = store_with_two_cells();
        let base: Vec<u8> = (0u8..32).collect();
        let h1 = s1.write(&base, &a1).unwrap();
        let h2 = s2.write(&base, &a2).unwrap();
        assert_eq!(
            h1, h2,
            "same bytes must address identically across instances"
        );
        assert_eq!(
            h1.0,
            *blake3::hash(&base).as_bytes(),
            "the content address must be the raw BLAKE3 of the data"
        );
        assert_eq!(
            s1.write(&base, &a1).unwrap(),
            h1,
            "a re-write of the same bytes must dedup to the same address"
        );
        for i in 0..base.len() {
            let mut mutated = base.clone();
            mutated[i] ^= 1;
            let hm = s1.write(&mutated, &a1).unwrap();
            assert_ne!(hm, h1, "byte {i} mutation must change the content address");
        }
    }

    /// Read integrity: `read(h)` returns EXACTLY the written bytes, whose
    /// BLAKE3 is `h` (the local analog of a sound read). Negative pole: a
    /// forged address — any single-byte perturbation of a genuine hash —
    /// reads as absent; the store never serves other content for it.
    #[test]
    fn prop_read_returns_the_preimage_and_forged_addresses_are_absent() {
        let (mut s, alice, _) = store_with_two_cells();
        let blobs: Vec<Vec<u8>> = vec![
            b"alpha".to_vec(),
            b"beta-beta".to_vec(),
            (0u8..64).collect(),
        ];
        let mut hashes = Vec::new();
        for blob in &blobs {
            hashes.push(s.write(blob, &alice).unwrap());
        }
        for (blob, h) in blobs.iter().zip(&hashes) {
            let served = s.read(h).expect("stored blob must read back");
            assert_eq!(
                served,
                &blob[..],
                "read must return the exact written bytes"
            );
            assert_eq!(
                *blake3::hash(served).as_bytes(),
                h.0,
                "the served bytes must be the preimage of the requested address"
            );
        }
        for h in &hashes {
            for i in 0..32 {
                let mut forged = h.0;
                forged[i] ^= 1;
                let fh = ContentHash(forged);
                assert!(
                    s.read(&fh).is_none(),
                    "forged address (byte {i}) must read as absent"
                );
                assert!(!s.contains(&fh), "forged address (byte {i}) must not exist");
            }
        }
    }

    /// Splice preserves content addressing: the returned hash is the
    /// BLAKE3 of the spliced bytes, the new content reads back exactly,
    /// and the old address no longer resolves (ref_count was 1).
    /// Negative pole: a non-owner splice is refused with `NotOwner` and
    /// leaves the original blob intact.
    #[test]
    fn prop_splice_rehashes_result_and_is_owner_gated() {
        let (mut s, alice, bob) = store_with_two_cells();
        let old = b"hello cruel world".to_vec();
        let h_old = s.write(&old, &alice).unwrap();

        // Negative pole: bob may not splice alice's blob.
        let refused = s.splice(&h_old, 6, b"kind!", &bob);
        assert!(
            matches!(refused, Err(StorageError::NotOwner { .. })),
            "non-owner splice must be refused with NotOwner, got {refused:?}"
        );
        assert_eq!(
            s.read(&h_old).unwrap(),
            &old[..],
            "a refused splice must leave the blob intact"
        );

        // Positive pole: alice splices; result is re-addressed by content.
        let h_new = s.splice(&h_old, 6, b"kind!", &alice).unwrap();
        let expected = b"hello kind! world".to_vec();
        assert_eq!(
            h_new.0,
            *blake3::hash(&expected).as_bytes(),
            "the spliced blob's address must be the BLAKE3 of the spliced bytes"
        );
        assert_eq!(s.read(&h_new).unwrap(), &expected[..]);
        assert!(
            !s.contains(&h_old),
            "the old address (ref_count 1) must be gone after splice"
        );
    }

    /// Per-owner dedup accounting: a deduplicating second writer is charged
    /// independently and holds ITS OWN reference. Crucially, the first
    /// writer's delete cannot destroy the blob out from under the second
    /// (the physical bytes survive while any owner still holds a reference),
    /// and a caller who never wrote the content cannot delete it at all.
    #[test]
    fn prop_dedup_is_per_owner_and_cannot_delete_out_from_under() {
        let (mut s, alice, bob) = store_with_two_cells();
        // A third cell that never writes this content.
        let charlie = s.bank.allocate_quota([0xC1; 32], 1_000_000, None);
        let data = b"shared content".to_vec();

        let h = s.write(&data, &alice).unwrap();
        assert_eq!(
            s.write(&data, &bob).unwrap(),
            h,
            "dedup addresses identically"
        );
        assert_eq!(s.owner_ref_count(&h, &alice), 1);
        assert_eq!(s.owner_ref_count(&h, &bob), 1);
        assert_eq!(s.total_ref_count(&h), 2);

        // A non-owner (never wrote it) cannot delete.
        let refused = s.delete(&h, &charlie);
        assert!(
            matches!(refused, Err(StorageError::NotOwner { .. })),
            "a caller with no reference must be refused, got {refused:?}"
        );
        assert_eq!(s.read(&h).unwrap(), &data[..]);

        // Alice deletes her reference. THE BLOB MUST SURVIVE for bob — this is
        // the security property: alice cannot destroy bob's data.
        s.delete(&h, &alice).unwrap();
        assert!(
            s.contains(&h),
            "alice's delete must not destroy the blob out from under bob"
        );
        assert_eq!(s.owner_ref_count(&h, &alice), 0);
        assert_eq!(s.owner_ref_count(&h, &bob), 1);
        assert_eq!(
            s.read(&h).unwrap(),
            &data[..],
            "bob's content must still read back"
        );

        // Alice can no longer delete (she holds no reference).
        assert!(matches!(
            s.delete(&h, &alice),
            Err(StorageError::NotOwner { .. })
        ));

        // bob drops his last reference: only now is the physical blob removed.
        s.delete(&h, &bob).unwrap();
        assert!(!s.contains(&h), "the last owner's delete removes the blob");
        assert_eq!(s.total_ref_count(&h), 0);
    }

    /// Each owner is refunded independently for the reference IT drops — a
    /// dedup writer's refund goes to its own quota, never the first writer's.
    #[test]
    fn prop_dedup_refunds_are_per_owner() {
        let (mut s, alice, bob) = store_with_two_cells();
        let data = vec![0x7Eu8; 100]; // 100 bytes, cost_per_byte=1 => 100 each.
        let h = s.write(&data, &alice).unwrap();
        s.write(&data, &bob).unwrap();

        let bob_consumed_before = s.bank.get(&bob).unwrap().total_consumed;
        let alice_consumed_before = s.bank.get(&alice).unwrap().total_consumed;

        // bob deletes his reference; refund_rate 0.5 => 50 back to BOB only.
        let refund = s.delete(&h, &bob).unwrap();
        assert_eq!(refund.quota_id, bob);
        assert_eq!(refund.amount, 50);
        assert_eq!(
            s.bank.get(&bob).unwrap().total_consumed,
            bob_consumed_before - 50,
            "bob's refund must reduce bob's consumption"
        );
        assert_eq!(
            s.bank.get(&alice).unwrap().total_consumed,
            alice_consumed_before,
            "alice's balance must be untouched by bob's delete"
        );
    }

    /// The global physical-byte cap bounds the store: distinct writes are
    /// rejected once the cap would be exceeded, but a DEDUP write of already
    /// stored content still succeeds (it consumes no new physical space).
    #[test]
    fn prop_store_cap_bounds_physical_bytes() {
        let mut bank = SpaceBank::new(1, 1, 0.5);
        let alice = bank.allocate_quota([0xA1; 32], 1_000_000, None);
        let mut s = ContentStore::with_capacity(bank, 20);

        let a = s.write(&[1u8; 10], &alice).unwrap(); // 10 <= 20 ok
        let _b = s.write(&[2u8; 10], &alice).unwrap(); // 20 <= 20 ok
        assert_eq!(s.stored_bytes(), 20);

        // A third distinct 10-byte blob would push physical to 30 > 20.
        let over = s.write(&[3u8; 10], &alice);
        assert!(
            matches!(over, Err(StorageError::StoreCapExceeded { .. })),
            "over-cap distinct write must be rejected, got {over:?}"
        );

        // A dedup write of already-stored content is fine (no new bytes).
        assert_eq!(s.write(&[1u8; 10], &alice).unwrap(), a);
        assert_eq!(s.stored_bytes(), 20);
    }

    /// Persistence round-trip: a store saved to disk and reloaded reproduces
    /// every blob, the per-owner reference accounting, and the quota bank —
    /// the state that was previously lost on process restart.
    #[test]
    fn prop_persistence_round_trip() {
        let dir = std::env::temp_dir().join("dregg_content_persist_test");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join(format!("store-{}.bin", std::process::id()));
        let _ = std::fs::remove_file(&path);

        let (mut s, alice, bob) = store_with_two_cells();
        let d1 = b"persist me".to_vec();
        let d2 = b"and me too, differently".to_vec();
        let h1 = s.write(&d1, &alice).unwrap();
        let _ = s.write(&d1, &bob).unwrap(); // shared, per-owner refs
        let h2 = s.write(&d2, &bob).unwrap();
        let alice_consumed = s.bank.get(&alice).unwrap().total_consumed;

        s.save_to(&path).unwrap();
        let loaded = ContentStore::load_from(&path).unwrap();

        assert_eq!(loaded.read(&h1).unwrap(), &d1[..]);
        assert_eq!(loaded.read(&h2).unwrap(), &d2[..]);
        assert_eq!(loaded.owner_ref_count(&h1, &alice), 1);
        assert_eq!(loaded.owner_ref_count(&h1, &bob), 1);
        assert_eq!(loaded.total_ref_count(&h1), 2);
        assert_eq!(loaded.stored_bytes(), s.stored_bytes());
        assert_eq!(
            loaded.bank.get(&alice).unwrap().total_consumed,
            alice_consumed
        );

        let _ = std::fs::remove_file(&path);
    }

    /// A corrupt/truncated snapshot loads as an `Err`, never a panic.
    #[test]
    fn load_from_rejects_corrupt_snapshot() {
        let dir = std::env::temp_dir().join("dregg_content_persist_test");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join(format!("corrupt-{}.bin", std::process::id()));
        std::fs::write(&path, b"not a valid postcard snapshot at all").unwrap();
        assert!(ContentStore::load_from(&path).is_err());
        let _ = std::fs::remove_file(&path);
    }
}
