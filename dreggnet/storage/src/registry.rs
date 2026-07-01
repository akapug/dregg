//! `registry` — the bucket-store **data plane**: cap-gated, metered, receipted
//! operations over a set of bucket cells.
//!
//! [`BucketRegistry`] is the object-store counterpart of the hosting
//! [`SiteRegistry`]: it holds the published bucket cells and exposes the five
//! operations every operation gated by a [`StorageCap`], every mutation metered
//! against an [`Account`] and leaving a receipt:
//!
//! | op            | cap-gated | metered | receipt          | trustless |
//! |---------------|-----------|---------|------------------|-----------|
//! | `create_bucket` | ✓       | —       | [`BucketReceipt`]| —         |
//! | `put`         | ✓         | ✓       | [`PutReceipt`]   | —         |
//! | `get`         | ✓         | ✓       | —                | —         |
//! | `verified_get`| ✓         | ✓       | —                | ✓ ([`ObjectOpening`]) |
//! | `list`        | ✓         | ✓       | —                | —         |
//! | `delete`      | ✓         | ✓       | [`DeleteReceipt`]| —         |
//!
//! This typed surface is exactly what the gateway mounts (the deployment rung):
//! `gateway/src/hosting.rs` mounts the `SiteRegistry`; a sibling
//! `gateway/src/storage.rs` adapts inbound `PUT/GET/DELETE /<bucket>/<key>` onto
//! these methods (cap from the request's bearer token, account from the caller's
//! funded lease), and the SDK exposes one method per operation. The verified read
//! is served by returning the [`ObjectOpening`] (the bytes + the opening) so the
//! caller re-witnesses in place.
//!
//! [`SiteRegistry`]: ../../dreggnet_webapp/hosting/struct.SiteRegistry.html

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use dreggnet_receipt::{BodyHasher, ReceiptAttestation, ReceiptBody, ReceiptChain};
use dreggnet_umem::{Record, UmemRegistry};
use serde::{Deserialize, Serialize};

use crate::bucket::{BucketCell, ObjectOpening};
use crate::cap::{StorageCap, is_valid_bucket_name};
use crate::meter::{Account, OverBudget, Pricing};
use crate::object::{Object, is_valid_key, normalize_key};

/// A [`BucketCell`] is a durable record keyed by its bucket name — the unit the
/// [`BucketRegistry`]'s durable umem backend lays into the registry cell's heap after
/// every mutation, so a restart reconstructs the bucket AND all its objects FROM the
/// committed heap (the cell carries its content).
impl Record for BucketCell {
    fn store_key(&self) -> String {
        self.name.clone()
    }
}

/// The registry of bucket cells — the storage data plane.
pub struct BucketRegistry {
    buckets: Mutex<BTreeMap<String, BucketCell>>,
    pricing: Pricing,
    next_seq: AtomicU64,
    /// The receipt chain create/put/delete are sealed into — prev-hash-chained
    /// + ed25519-signed, so a client can verify an op without trusting the host.
    /// `None` is the unsigned local default (receipts carry no attestation).
    receipt_chain: Option<ReceiptChain>,
    /// The durable backend — when set, the registry IS a **umem cell**: every bucket
    /// cell mutation (create / put / delete) is laid into the cell's
    /// `(collection,key) -> value` heap and committed to the real sorted-Poseidon2
    /// boundary root ([`dreggnet_umem::UmemRegistry`]), so a gateway restart
    /// RECONSTRUCTS the buckets + their objects FROM the committed heap rather than
    /// losing them. This replaces the from-scratch JSON-lines log with the real
    /// substrate (the #2 re-dregg move, `docs/REGISTRIES-AS-UMEM.md`) — unlocking
    /// namespace fork / time-travel / merge-readiness. `None` is the in-memory-only
    /// default; [`with_durable_store`](BucketRegistry::with_durable_store) attaches it.
    store: Option<UmemRegistry<BucketCell>>,
}

impl Default for BucketRegistry {
    fn default() -> BucketRegistry {
        BucketRegistry::new()
    }
}

impl BucketRegistry {
    /// A fresh, empty registry at the default [`Pricing`].
    pub fn new() -> BucketRegistry {
        BucketRegistry::with_pricing(Pricing::default())
    }

    /// A fresh registry at a chosen price list.
    pub fn with_pricing(pricing: Pricing) -> BucketRegistry {
        BucketRegistry {
            buckets: Mutex::new(BTreeMap::new()),
            pricing,
            next_seq: AtomicU64::new(0),
            receipt_chain: None,
            store: None,
        }
    }

    /// Attach a **durable umem backend** at `path` and **reconstruct** the prior data
    /// plane: open the [`UmemRegistry`](dreggnet_umem::UmemRegistry) (the registry AS a
    /// umem cell), restore every persisted [`BucketCell`] (with its objects) FROM the
    /// committed heap back into the live registry, and commit every future
    /// create/put/delete to the heap — so a gateway restart serves the buckets a prior
    /// process held (the data-plane durability blocker) instead of losing them.
    ///
    /// Builder form: chains after [`new`](BucketRegistry::new) /
    /// [`with_pricing`](BucketRegistry::with_pricing) /
    /// [`signed`](BucketRegistry::signed). The restore **fails closed** if the committed
    /// heap does not bind its sealed boundary root (the `root_binds_get` discipline).
    pub fn with_durable_store(
        mut self,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<BucketRegistry> {
        let store = UmemRegistry::<BucketCell>::open(path).map_err(|e| e.into_io())?;
        {
            let mut buckets = self.buckets.lock().expect("buckets poisoned");
            for cell in store.all() {
                buckets.insert(cell.name.clone(), cell);
            }
        }
        self.store = Some(store);
        Ok(self)
    }

    /// The registry's **committed umem boundary root** (hex), if it is durably backed:
    /// the real sorted-Poseidon2 `compute_heap_root` over the bucket-store cell's heap —
    /// the 32-byte commitment a dregg light client understands for the WHOLE bucket
    /// namespace (distinct from a single bucket's per-content `content_root`). `None`
    /// when the registry is in-memory-only.
    pub fn umem_root(&self) -> Option<String> {
        self.store.as_ref().map(|s| s.boundary_root())
    }

    /// **Fork the whole bucket namespace** (a umem superpower a `Mutex<BTreeMap>` can
    /// never give): copy the committed bucket-store cell at `new_path`, returning a
    /// divergent `BucketRegistry` that starts byte-identical (same boundary root) and
    /// diverges as either side mutates — a tenant forks their entire set of buckets at
    /// once (a preview/branch of the namespace), then serves / stitches / discards it.
    /// `None` when the registry is in-memory-only (nothing committed to fork).
    pub fn fork_namespace(
        &self,
        new_path: impl AsRef<std::path::Path>,
    ) -> Option<std::io::Result<BucketRegistry>> {
        let store = self.store.as_ref()?;
        Some(match store.fork(new_path) {
            Ok(forked) => Ok(BucketRegistry::adopt_umem(forked, self.pricing)),
            Err(e) => Err(e.into_io()),
        })
    }

    /// **Time-travel — checkpoint** the current namespace: the committed boundary root,
    /// retained so [`restore_namespace`](Self::restore_namespace) can return to it ("my
    /// buckets as of now"). `None` when in-memory-only.
    pub fn checkpoint_namespace(&self) -> Option<String> {
        self.store.as_ref().map(|s| s.checkpoint())
    }

    /// **Time-travel — restore** the namespace to an earlier committed `root` (from
    /// [`checkpoint_namespace`](Self::checkpoint_namespace)): the buckets + their objects
    /// revert to that committed state, durably (the rollback survives a restart). Reloads
    /// the reconstructed in-memory view from the restored heap. A no-op `Ok(())` when
    /// in-memory-only.
    pub fn restore_namespace(&self, root: &str) -> std::io::Result<()> {
        if let Some(store) = &self.store {
            store.restore(root).map_err(|e| e.into_io())?;
            let mut buckets = self.buckets.lock().expect("buckets poisoned");
            buckets.clear();
            for cell in store.all() {
                buckets.insert(cell.name.clone(), cell);
            }
        }
        Ok(())
    }

    /// Build a `BucketRegistry` from an already-open [`UmemRegistry`] (the fork path),
    /// re-seeding the in-memory serving map from the committed heap.
    fn adopt_umem(store: UmemRegistry<BucketCell>, pricing: Pricing) -> BucketRegistry {
        let reg = BucketRegistry::with_pricing(pricing);
        {
            let mut buckets = reg.buckets.lock().expect("buckets poisoned");
            for cell in store.all() {
                buckets.insert(cell.name.clone(), cell);
            }
        }
        let mut reg = reg;
        reg.store = Some(store);
        reg
    }

    /// A fresh registry whose buckets are **durable** at `path` — the
    /// data-plane-durable default a real gateway uses (shorthand for
    /// `BucketRegistry::new().with_durable_store(path)`).
    pub fn durable(path: impl AsRef<std::path::Path>) -> std::io::Result<BucketRegistry> {
        BucketRegistry::new().with_durable_store(path)
    }

    /// The durable backend path, if this registry persists its buckets.
    pub fn durable_path(&self) -> Option<&std::path::Path> {
        self.store.as_ref().map(|s| s.path())
    }

    /// Persist a bucket cell through the durable backend (no-op when in-memory-only).
    /// A store fault surfaces as [`StorageError::Persist`] so a mutation is never
    /// reported successful unless it survives a restart.
    fn persist(&self, cell: &BucketCell) -> Result<(), StorageError> {
        if let Some(store) = &self.store {
            store
                .append(cell)
                .map_err(|e| StorageError::Persist(e.to_string()))?;
        }
        Ok(())
    }

    /// A registry whose ops are sealed into a prev-hash-chained, ed25519-signed
    /// receipt stream under the secret `seed` — each receipt is re-witnessable
    /// (verify with [`dreggnet_receipt::verify_chain`] against
    /// [`Self::receipt_signer`], no trust in the host). A real host configures a
    /// persistent secret.
    pub fn signed(seed: [u8; 32]) -> BucketRegistry {
        BucketRegistry {
            receipt_chain: Some(ReceiptChain::from_seed(seed)),
            ..BucketRegistry::with_pricing(Pricing::default())
        }
    }

    /// Attach a receipt chain (builder form).
    pub fn with_receipt_chain(mut self, chain: ReceiptChain) -> BucketRegistry {
        self.receipt_chain = Some(chain);
        self
    }

    /// The public key a non-witness verifies this registry's receipts under, if signed.
    pub fn receipt_signer(&self) -> Option<[u8; 32]> {
        self.receipt_chain.as_ref().map(|c| c.signer_public())
    }

    /// Seal a body into the registry's chain (no-op → `None` when unsigned).
    fn seal(&self, body_hash: [u8; 32], seq: u64) -> Option<ReceiptAttestation> {
        self.receipt_chain
            .as_ref()
            .map(|c| c.seal(body_hash, seq, None))
    }

    /// The price list this registry meters against.
    pub fn pricing(&self) -> Pricing {
        self.pricing
    }

    fn next_seq(&self) -> u64 {
        self.next_seq.fetch_add(1, Ordering::Relaxed)
    }

    // -- create ---------------------------------------------------------------

    /// Create a bucket as a cap-gated turn. Gates on `cap` (must be a
    /// `storage-bucket/<name>` cap whose name is `name`), validates the name, and
    /// writes an empty owned [`BucketCell`]. Creating an existing bucket with the
    /// right cap is idempotent (the existing cell is kept; its receipt re-issued).
    pub fn create_bucket(
        &self,
        cap: &StorageCap,
        name: &str,
    ) -> Result<BucketReceipt, StorageError> {
        if !is_valid_bucket_name(name) {
            return Err(StorageError::InvalidBucketName(name.to_string()));
        }
        if !cap.authorizes(name) {
            return Err(StorageError::CapRefused {
                cap: cap.cap.clone(),
                bucket: name.to_string(),
            });
        }
        let mut buckets = self.buckets.lock().expect("buckets poisoned");
        let cell = buckets
            .entry(name.to_string())
            .or_insert_with(|| BucketCell::empty(name, cap.holder.clone()));
        let mut receipt = BucketReceipt {
            seq: self.next_seq(),
            bucket: cell.name.clone(),
            owner: cell.owner.clone(),
            content_root: cell.content_root.clone(),
            attest: None,
        };
        // Durable-first: persist the bucket cell so a restart reconstructs it.
        self.persist(cell)?;
        receipt.attest = self.seal(receipt.body_hash(), receipt.seq);
        Ok(receipt)
    }

    // -- put ------------------------------------------------------------------

    /// Store an object as a cap-gated, metered, receipted turn.
    ///
    /// Gates on `cap` (must authorize `bucket` and be the bucket owner), meters
    /// `account` for [`Pricing::put_cost`] of the object bytes (refusing
    /// **before** any write if over budget), inserts the object (content-type
    /// inferred from the key extension), recomputes the bucket's content root, and
    /// returns the [`PutReceipt`].
    pub fn put(
        &self,
        cap: &StorageCap,
        account: &Account,
        bucket: &str,
        key: &str,
        body: impl Into<Vec<u8>>,
    ) -> Result<PutReceipt, StorageError> {
        self.put_object(cap, account, bucket, key, Object::at(key, body))
    }

    /// As [`put`](BucketRegistry::put), with an explicit object (content-type
    /// chosen by the caller rather than inferred from the key).
    pub fn put_object(
        &self,
        cap: &StorageCap,
        account: &Account,
        bucket: &str,
        key: &str,
        object: Object,
    ) -> Result<PutReceipt, StorageError> {
        if !is_valid_key(key) {
            return Err(StorageError::InvalidKey(key.to_string()));
        }
        // Meter BEFORE the write: an over-budget put never mutates state.
        let cost = self.pricing.put_cost(object.size());
        let mut buckets = self.buckets.lock().expect("buckets poisoned");
        let cell = self.authorized_mut(&mut buckets, cap, bucket)?;
        let remaining = account.charge(cost).map_err(StorageError::OverBudget)?;

        let nkey = normalize_key(key);
        let content_address = object.content_address();
        let size = object.size();
        cell.content.put_object(key, object);
        let content_root = cell.recommit();
        // Durable: persist the bucket's new committed state (cell + all objects).
        self.persist(cell)?;
        let mut receipt = PutReceipt {
            seq: self.next_seq(),
            bucket: bucket.to_string(),
            key: nkey,
            content_address,
            size,
            units_charged: cost,
            remaining,
            content_root,
            attest: None,
        };
        receipt.attest = self.seal(receipt.body_hash(), receipt.seq);
        Ok(receipt)
    }

    // -- get / verified_get ---------------------------------------------------

    /// Read an object as a cap-gated, metered operation (the plain read).
    pub fn get(
        &self,
        cap: &StorageCap,
        account: &Account,
        bucket: &str,
        key: &str,
    ) -> Result<Object, StorageError> {
        let buckets = self.buckets.lock().expect("buckets poisoned");
        let cell = self.authorized_ref(&buckets, cap, bucket)?;
        let object = cell
            .content
            .get(key)
            .cloned()
            .ok_or_else(|| StorageError::NoSuchObject {
                bucket: bucket.to_string(),
                key: normalize_key(key),
            })?;
        account
            .charge(self.pricing.get_op_units)
            .map_err(StorageError::OverBudget)?;
        Ok(object)
    }

    /// Read an object as a **trustless**, cap-gated, metered operation: returns an
    /// [`ObjectOpening`] the caller re-witnesses against the bucket's committed
    /// root with [`crate::verify_opening`] — no trust in this registry required.
    pub fn verified_get(
        &self,
        cap: &StorageCap,
        account: &Account,
        bucket: &str,
        key: &str,
    ) -> Result<ObjectOpening, StorageError> {
        let buckets = self.buckets.lock().expect("buckets poisoned");
        let cell = self.authorized_ref(&buckets, cap, bucket)?;
        let opening = cell.open(key).ok_or_else(|| StorageError::NoSuchObject {
            bucket: bucket.to_string(),
            key: normalize_key(key),
        })?;
        account
            .charge(self.pricing.get_op_units)
            .map_err(StorageError::OverBudget)?;
        Ok(opening)
    }

    // -- list -----------------------------------------------------------------

    /// List the object keys in a bucket (optionally filtered by a key `prefix`),
    /// as a cap-gated, metered operation. An empty/`"/"` prefix lists everything.
    pub fn list(
        &self,
        cap: &StorageCap,
        account: &Account,
        bucket: &str,
        prefix: &str,
    ) -> Result<Vec<String>, StorageError> {
        let buckets = self.buckets.lock().expect("buckets poisoned");
        let cell = self.authorized_ref(&buckets, cap, bucket)?;
        let keys = cell.content.keys_with_prefix(prefix);
        account
            .charge(self.pricing.list_op_units)
            .map_err(StorageError::OverBudget)?;
        Ok(keys)
    }

    // -- delete ---------------------------------------------------------------

    /// Delete an object as a cap-gated, metered, receipted turn. Deleting an
    /// absent key is a [`StorageError::NoSuchObject`] (so a delete receipt always
    /// names a real removal).
    pub fn delete(
        &self,
        cap: &StorageCap,
        account: &Account,
        bucket: &str,
        key: &str,
    ) -> Result<DeleteReceipt, StorageError> {
        let mut buckets = self.buckets.lock().expect("buckets poisoned");
        let cell = self.authorized_mut(&mut buckets, cap, bucket)?;
        if cell.content.get(key).is_none() {
            return Err(StorageError::NoSuchObject {
                bucket: bucket.to_string(),
                key: normalize_key(key),
            });
        }
        let remaining = account
            .charge(self.pricing.delete_op_units)
            .map_err(StorageError::OverBudget)?;
        cell.content.remove(key);
        let content_root = cell.recommit();
        // Durable: persist the bucket's new committed state after the removal.
        self.persist(cell)?;
        let mut receipt = DeleteReceipt {
            seq: self.next_seq(),
            bucket: bucket.to_string(),
            key: normalize_key(key),
            units_charged: self.pricing.delete_op_units,
            remaining,
            content_root,
            attest: None,
        };
        receipt.attest = self.seal(receipt.body_hash(), receipt.seq);
        Ok(receipt)
    }

    // -- read-only introspection ---------------------------------------------

    /// A clone of a bucket cell by name (the committed cell), if it exists. No cap
    /// needed — the cell carries its own owner + commitment; this is the
    /// inspection surface a light client reads.
    pub fn get_bucket(&self, name: &str) -> Option<BucketCell> {
        self.buckets
            .lock()
            .expect("buckets poisoned")
            .get(name)
            .cloned()
    }

    /// The names of all buckets, sorted.
    pub fn bucket_names(&self) -> Vec<String> {
        self.buckets
            .lock()
            .expect("buckets poisoned")
            .keys()
            .cloned()
            .collect()
    }

    // -- internal cap-gate helpers -------------------------------------------

    /// Resolve `bucket` to its cell, enforcing the cap-gate: the cap must
    /// authorize `bucket` AND its holder must be the bucket owner.
    fn authorized_ref<'a>(
        &self,
        buckets: &'a BTreeMap<String, BucketCell>,
        cap: &StorageCap,
        bucket: &str,
    ) -> Result<&'a BucketCell, StorageError> {
        if !cap.authorizes(bucket) {
            return Err(StorageError::CapRefused {
                cap: cap.cap.clone(),
                bucket: bucket.to_string(),
            });
        }
        let cell = buckets
            .get(bucket)
            .ok_or_else(|| StorageError::NoSuchBucket(bucket.to_string()))?;
        if cell.owner != cap.holder {
            return Err(StorageError::CapRefused {
                cap: cap.cap.clone(),
                bucket: bucket.to_string(),
            });
        }
        Ok(cell)
    }

    fn authorized_mut<'a>(
        &self,
        buckets: &'a mut BTreeMap<String, BucketCell>,
        cap: &StorageCap,
        bucket: &str,
    ) -> Result<&'a mut BucketCell, StorageError> {
        if !cap.authorizes(bucket) {
            return Err(StorageError::CapRefused {
                cap: cap.cap.clone(),
                bucket: bucket.to_string(),
            });
        }
        let cell = buckets
            .get_mut(bucket)
            .ok_or_else(|| StorageError::NoSuchBucket(bucket.to_string()))?;
        if cell.owner != cap.holder {
            return Err(StorageError::CapRefused {
                cap: cap.cap.clone(),
                bucket: bucket.to_string(),
            });
        }
        Ok(cell)
    }
}

/// The verifiable record a `create_bucket` leaves.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BucketReceipt {
    /// The registry-monotonic sequence of this operation.
    pub seq: u64,
    /// The bucket created.
    pub bucket: String,
    /// The owner (the cap holder).
    pub owner: String,
    /// The bucket's content commitment (empty-bucket root on first create).
    pub content_root: String,
    /// The chained, signed attestation lifting this op into the receipt
    /// contract; `None` for the unsigned local default. See [`ReceiptBody`].
    #[serde(default)]
    pub attest: Option<ReceiptAttestation>,
}

impl ReceiptBody for BucketReceipt {
    fn body_hash(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(b"bucket-receipt-v1");
        h.u64(self.seq)
            .field(self.bucket.as_bytes())
            .field(self.owner.as_bytes())
            .field(self.content_root.as_bytes());
        h.finalize()
    }
    fn seq(&self) -> u64 {
        self.seq
    }
    fn attestation(&self) -> Option<&ReceiptAttestation> {
        self.attest.as_ref()
    }
}

/// The verifiable record a `put` leaves — the object-store analog of hosting's
/// publish receipt: who stored what, at which content address, charged how much,
/// moving the bucket to which committed root.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PutReceipt {
    /// The registry-monotonic sequence of this operation.
    pub seq: u64,
    /// The bucket written.
    pub bucket: String,
    /// The (normalized) object key written.
    pub key: String,
    /// The stored object's content address.
    pub content_address: String,
    /// The stored object size, in bytes.
    pub size: usize,
    /// Meter units charged for this put.
    pub units_charged: i64,
    /// The account's remaining budget after the charge.
    pub remaining: i64,
    /// The bucket's content root after the write.
    pub content_root: String,
    /// The chained, signed attestation lifting this op into the receipt
    /// contract; `None` for the unsigned local default. See [`ReceiptBody`].
    #[serde(default)]
    pub attest: Option<ReceiptAttestation>,
}

impl ReceiptBody for PutReceipt {
    fn body_hash(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(b"put-receipt-v1");
        h.u64(self.seq)
            .field(self.bucket.as_bytes())
            .field(self.key.as_bytes())
            .field(self.content_address.as_bytes())
            .u64(self.size as u64)
            .u64(self.units_charged as u64)
            .u64(self.remaining as u64)
            .field(self.content_root.as_bytes());
        h.finalize()
    }
    fn seq(&self) -> u64 {
        self.seq
    }
    fn attestation(&self) -> Option<&ReceiptAttestation> {
        self.attest.as_ref()
    }
}

/// The verifiable record a `delete` leaves.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeleteReceipt {
    /// The registry-monotonic sequence of this operation.
    pub seq: u64,
    /// The bucket written.
    pub bucket: String,
    /// The (normalized) object key removed.
    pub key: String,
    /// Meter units charged for this delete.
    pub units_charged: i64,
    /// The account's remaining budget after the charge.
    pub remaining: i64,
    /// The bucket's content root after the removal.
    pub content_root: String,
    /// The chained, signed attestation lifting this op into the receipt
    /// contract; `None` for the unsigned local default. See [`ReceiptBody`].
    #[serde(default)]
    pub attest: Option<ReceiptAttestation>,
}

impl ReceiptBody for DeleteReceipt {
    fn body_hash(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(b"delete-receipt-v1");
        h.u64(self.seq)
            .field(self.bucket.as_bytes())
            .field(self.key.as_bytes())
            .u64(self.units_charged as u64)
            .u64(self.remaining as u64)
            .field(self.content_root.as_bytes());
        h.finalize()
    }
    fn seq(&self) -> u64 {
        self.seq
    }
    fn attestation(&self) -> Option<&ReceiptAttestation> {
        self.attest.as_ref()
    }
}

/// Why a storage operation was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StorageError {
    /// The presented cap does not authorize operating `bucket` (wrong/ill-formed
    /// token, or the holder is not the bucket owner). The cap-attenuation refusal.
    CapRefused { cap: String, bucket: String },
    /// The bucket name is not a usable namespace label.
    InvalidBucketName(String),
    /// The object key is not a usable key.
    InvalidKey(String),
    /// No bucket by that name exists.
    NoSuchBucket(String),
    /// No object by that key exists in the bucket.
    NoSuchObject { bucket: String, key: String },
    /// The account could not cover the operation's metered cost.
    OverBudget(OverBudget),
    /// The operation was valid but the durable backend could not persist the bucket
    /// cell (a disk/fsync fault). The mutation is refused rather than reported as
    /// durable when it is not — a stored object that would vanish on restart is not
    /// a successful put.
    Persist(String),
}

impl std::fmt::Display for StorageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StorageError::CapRefused { cap, bucket } => {
                write!(
                    f,
                    "cap `{cap}` does not authorize operating bucket `{bucket}`"
                )
            }
            StorageError::InvalidBucketName(n) => write!(f, "`{n}` is not a valid bucket name"),
            StorageError::InvalidKey(k) => write!(f, "`{k}` is not a valid object key"),
            StorageError::NoSuchBucket(b) => write!(f, "no bucket named `{b}`"),
            StorageError::NoSuchObject { bucket, key } => {
                write!(f, "no object `{key}` in bucket `{bucket}`")
            }
            StorageError::OverBudget(e) => write!(f, "payment required: {e}"),
            StorageError::Persist(e) => write!(f, "could not persist the bucket: {e}"),
        }
    }
}

impl std::error::Error for StorageError {}
