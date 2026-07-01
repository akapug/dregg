//! `dreggnet-storage` — durable object storage on the verified rail: **a bucket
//! is a dregg cell.**
//!
//! This is the object-store service in the DreggNet cloud catalog (see
//! `docs/SERVICES.md`). It is the direct generalization of the static-hosting
//! `hosting` module (`dreggnet-webapp::hosting`): where a hosted *site* is a cell
//! committing a path→asset map served read-only over a host, a *bucket* is a cell
//! committing a key→object map operated through cap-gated, metered, receipted
//! turns — with a **trustless read** over the same commitment.
//!
//! ```text
//!   PUT / DELETE  (cap-gated, metered, receipted)    GET  (trustless, re-witnessable)
//!   ─────────────────────────────────────────────    ────────────────────────────────
//!   StorageCap  storage-bucket/<name>                verified_get ─▶ ObjectOpening
//!     └─ BucketRegistry::put / ::delete                  └─ verify_opening (pure):
//!          │ charge Account (per op + per KiB)               recompute leaf from bytes,
//!          │ write the BucketCell                            re-fold → == bucket_root
//!          ▼
//!        BucketCell { name, owner, content_root, content: key → Object }
//!          + PutReceipt / DeleteReceipt  (who stored what, charged how much)
//! ```
//!
//! ## The four pillars (each grounded in a dregg primitive)
//!
//! - **Cell** — a [`BucketCell`] is the located state: an owner, a cap-gated
//!   namespace, and a committed [`content_root`] over content-addressed objects.
//! - **Cap-gated turn** — every operation is gated by a [`StorageCap`]
//!   (`storage-bucket/<name>`, bound to holder + bucket) and leaves a receipt
//!   ([`PutReceipt`] / [`DeleteReceipt`] / [`BucketReceipt`]).
//! - **Paid** — every mutation is metered against a funded [`Account`]
//!   ([`Pricing`]: per-op + per-KiB), refused before any write if over budget —
//!   the stand-in for a funded dregg `execution-lease` the bridge drives.
//! - **Verified** — the read is **trustless**: [`verified_get`] returns an
//!   [`ObjectOpening`] and [`verify_opening`] re-witnesses, with no trust in the
//!   server, that the served bytes are committed in the bucket root.
//!
//! ## Real vs the on-chain weld (honest)
//!
//! Real in this crate: the cell model, the cap-gate + attenuation, the
//! content-address + content-root commitments, the receipts, the metering, and the
//! self-verifying read. The deliberate flip-on step (shared with the hosting
//! module) is committing the bucket cell to a real dregg node so each put/delete
//! is a witnessed `Effect::Write` and the root is the cell's Poseidon2 umem heap
//! root — the surface `dreggnet-bridge`'s `dregg_verify` module names.
//!
//! ## Deployment rung (gateway / SDK)
//!
//! [`BucketRegistry`] is the typed data plane. The gateway mounts it beside the
//! hosting registry (`gateway/src/hosting.rs` → a sibling storage mount) adapting
//! `PUT/GET/DELETE /<bucket>/<key>` onto these methods; the SDK exposes one method
//! per operation. Neither is wired live here (the gateway/web-hosting lanes own
//! that surface) — this crate is the portable, fully-tested core they adopt.
//!
//! [`content_root`]: bucket::content_root
//! [`verified_get`]: BucketRegistry::verified_get

pub mod bucket;
pub mod cap;
pub mod meter;
pub mod object;
pub mod registry;

pub use bucket::{BucketCell, ObjectOpening, content_root, object_leaf, verify_opening};
pub use cap::{STORAGE_CAP_PREFIX, StorageCap, is_valid_bucket_name};
pub use meter::{Account, OverBudget, Pricing};
pub use object::{BucketContent, Object, content_type_for, digest, is_valid_key, normalize_key};
pub use registry::{BucketReceipt, BucketRegistry, DeleteReceipt, PutReceipt, StorageError};

/// The ONE product-wide receipt contract (re-exported): every bucket receipt is
/// prev-hash-chained + ed25519-signed + re-witnessable. See `docs/RECEIPT-CONTRACT.md`.
pub use dreggnet_receipt as receipt;
