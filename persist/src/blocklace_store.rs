//! Blocklace persistence: incremental block storage and metadata for crash recovery.
//!
//! Stores individual blocks by their ID and blocklace metadata (tips, equivocators,
//! ordering state) so the DAG can be reconstructed on restart without re-syncing
//! from peers.
//!
//! Design:
//! - Blocks are stored individually on each insert (incremental, not full snapshots).
//! - Metadata (tips, equivocators, finality state) is persisted periodically.
//! - On startup, all blocks are loaded and fed into `Blocklace::from_checkpoint()`.

use std::collections::HashMap;

const BLOCKLACE_CHECKPOINT_HEIGHTS: &str = "blocklace_checkpoint_heights";
const BLOCKLACE_CHECKPOINT_LATEST: &str = "blocklace_checkpoint_latest_height";

// Before atomic publication, the latest pointer could commit after both halves
// but before the height index. That last complete pair is recoverable on reads;
// an unindexed older pair (or one half) is never implicitly published.
fn checkpoint_height_is_published(
    index: Option<&[u8]>,
    latest: Option<&[u8]>,
    height: u64,
) -> Result<bool> {
    let heights: Vec<u64> = index
        .map(postcard::from_bytes)
        .transpose()?
        .unwrap_or_default();
    if heights.windows(2).any(|pair| pair[0] > pair[1]) {
        return Err(StoreError::Integrity(
            "checkpoint height index is out of order".into(),
        ));
    }
    let pointer = latest
        .map(|bytes| {
            <[u8; 8]>::try_from(bytes)
                .map(u64::from_le_bytes)
                .map_err(|_| StoreError::Integrity("invalid latest checkpoint height".into()))
        })
        .transpose()?;
    if pointer.is_none() && !heights.is_empty() {
        return Err(StoreError::Integrity(
            "checkpoint height index has no latest pointer".into(),
        ));
    }
    if let (Some(pointer), Some(tail)) = (pointer, heights.last().copied()) {
        if tail > pointer
            && (heights.iter().filter(|h| **h > pointer).count() != 1
                || !heights.contains(&pointer))
        {
            return Err(StoreError::Integrity(
                "checkpoint index tail disagrees with latest pointer".into(),
            ));
        }
    }
    Ok(heights.contains(&height) || pointer == Some(height) && heights.iter().all(|h| *h < height))
}

fn stale_checkpoint_pointer(index: Option<&[u8]>, latest: Option<&[u8]>) -> Result<Option<u64>> {
    let heights: Vec<u64> = index
        .map(postcard::from_bytes)
        .transpose()?
        .unwrap_or_default();
    let pointer = latest
        .and_then(|bytes| <[u8; 8]>::try_from(bytes).ok())
        .map(u64::from_le_bytes);
    Ok(pointer.filter(|p| heights.last().is_some_and(|tail| *tail > *p)))
}

fn legacy_latest_tombstone(
    index: Option<&[u8]>,
    latest: Option<&[u8]>,
    height: u64,
) -> Result<bool> {
    let heights: Vec<u64> = index
        .map(postcard::from_bytes)
        .transpose()?
        .unwrap_or_default();
    Ok(latest == Some(height.to_le_bytes().as_slice())
        && heights
            .windows(2)
            .any(|pair| pair[0] == height && pair[1] == height))
}

#[cfg(test)]
thread_local! {
    // One-shot fault in the real write transaction, after N mutations and before commit.
    static FAIL_CHECKPOINT_PUBLISH_AFTER: std::cell::Cell<Option<usize>> = const {
        std::cell::Cell::new(None)
    };
}

#[cfg(test)]
fn fail_checkpoint_publish_after(step: usize) -> bool {
    FAIL_CHECKPOINT_PUBLISH_AFTER.with(|fault| {
        if fault.get() == Some(step) {
            fault.set(None);
            true
        } else {
            false
        }
    })
}

use redb::{ReadableTable, ReadableTableMetadata};
use serde::{Deserialize, Serialize};

use dregg_blocklace::finality::{Block, BlockId, Blocklace, CheckpointData, CreatorTips};

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

/// Metadata for the blocklace state, persisted alongside blocks.
///
/// This captures the mutable state that is derived from block processing but
/// expensive to recompute (equivocators, tips, ordering). Stored as a single
/// postcard-serialized blob under `BLOCKLACE_META_KEY`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BlocklaceMeta {
    /// Creator -> tips: the chain head, or — for a detected equivocator — the
    /// pinned incomparable evidence PAIR (`CreatorTips::Pair`, the CM Alg. 1:5
    /// two-tips floor). ⚑ schema flag day 2026-08-08 (exclusion-by-past): the
    /// value type changed from a bare `BlockId`; an old blob refuses to decode
    /// and the `CANONICAL_STATE_SCHEMA_EPOCH` bump re-genesises the store.
    pub tips: HashMap<[u8; 32], CreatorTips>,
    /// Known equivocator public keys.
    pub equivocators: Vec<[u8; 32]>,
    /// Block IDs in their total order (tau output).
    pub ordered_block_ids: Vec<BlockId>,
    /// Block IDs that have been attested by quorum.
    pub attested_block_ids: Vec<BlockId>,
}

impl PersistentStore {
    /// Publish a fast-sync DAG/ledger pair, its height index, and the latest pointer
    /// in ONE redb transaction. These are derived bootstrap snapshots, not the signed
    /// blocks, commit records, attested roots, or historical proof authorities.
    /// Older pairs leave no tombstones; a height cannot be rebound to different bytes.
    pub fn publish_blocklace_checkpoint_pair(
        &self,
        height: u64,
        blocklace: &[u8],
        ledger: &[u8],
        keep_last: usize,
    ) -> Result<()> {
        if let Some(fault) = self.config_io_fault() {
            return Err(fault);
        }
        if keep_last == 0 || blocklace.is_empty() || ledger.is_empty() {
            return Err(StoreError::Integrity(
                "empty checkpoint pair or retention window".into(),
            ));
        }
        let checkpoint_key = format!("blocklace_checkpoint_{height}");
        let ledger_key = format!("blocklace_ledger_snapshot_{height}");
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::METADATA_BYTES)?;
            let index = table
                .get(BLOCKLACE_CHECKPOINT_HEIGHTS)?
                .map(|g| g.value().to_vec());
            let latest = table
                .get(BLOCKLACE_CHECKPOINT_LATEST)?
                .map(|g| g.value().to_vec());
            let mut heights: Vec<u64> = index
                .map(|bytes| postcard::from_bytes(&bytes))
                .transpose()?
                .unwrap_or_default();
            let latest_height = match latest {
                Some(bytes) if bytes.len() == 8 => {
                    Some(u64::from_le_bytes(bytes.try_into().unwrap()))
                }
                Some(_) => {
                    return Err(StoreError::Integrity(
                        "invalid latest checkpoint height".into(),
                    ));
                }
                None => None,
            };
            // The old writer appended a duplicate on every same-height callback,
            // pruned by setting both halves to empty, and ignored a failed latest
            // write before appending the new height to the index.
            if heights.windows(2).any(|pair| pair[0] > pair[1]) {
                return Err(StoreError::Integrity(
                    "checkpoint height index is out of order".into(),
                ));
            }
            let repeated_latest =
                latest_height.is_some_and(|h| heights.windows(2).any(|p| p[0] == h && p[1] == h));
            let indexed_above_pointer = heights
                .iter()
                .filter(|h| latest_height.is_some_and(|p| **h > p))
                .count();
            heights.dedup();
            let indexed_tail = heights.last().copied();
            let mut complete = Vec::with_capacity(heights.len());
            for h in heights {
                let checkpoint_key = format!("blocklace_checkpoint_{h}");
                let ledger_key = format!("blocklace_ledger_snapshot_{h}");
                let c = table.get(checkpoint_key.as_str())?.map(|g| g.value().len());
                let l = table.get(ledger_key.as_str())?.map(|g| g.value().len());
                match (c, l) {
                    (Some(c), Some(l)) if c > 0 && l > 0 => complete.push(h),
                    (Some(0), Some(0)) if Some(h) != latest_height || repeated_latest => {
                        // Only the old writer's TWO empty-value tombstones may be
                        // reclaimed. A duplicate latest can be republished after
                        // independent durable-root validation; a torn pair cannot.
                        table.remove(checkpoint_key.as_str())?;
                        table.remove(ledger_key.as_str())?;
                    }
                    _ => {
                        return Err(StoreError::Integrity(format!(
                            "checkpoint {h} has a torn or ambiguous pair"
                        )));
                    }
                }
            }
            let mut heights = complete;
            let pointer = latest_height.unwrap_or(0);
            if let Some(tail) = indexed_tail.filter(|tail| *tail > pointer) {
                // The original writer ignored the failed pointer write, but did
                // append exactly ONE complete new indexed pair. Any larger gap in
                // the index, or an absent previous pointer, is ambiguous.
                if heights.last().copied() != Some(tail)
                    || heights.iter().rev().nth(1).copied() != latest_height
                    || indexed_above_pointer != 1
                {
                    return Err(StoreError::Integrity(
                        "checkpoint index tail disagrees with latest pointer".into(),
                    ));
                }
            } else if heights.last().copied().unwrap_or(0) < pointer {
                // Legacy pointer-ahead publication is recoverable only with
                // both nonempty halves; a duplicated, tombstoned latest instead
                // remains unpublished until an authoritative producer repairs it.
                let c = table
                    .get(format!("blocklace_checkpoint_{pointer}").as_str())?
                    .map(|g| !g.value().is_empty())
                    .unwrap_or(false);
                let l = table
                    .get(format!("blocklace_ledger_snapshot_{pointer}").as_str())?
                    .map(|g| !g.value().is_empty())
                    .unwrap_or(false);
                if c && l {
                    heights.push(pointer);
                } else if !(repeated_latest && !c && !l && indexed_tail == latest_height) {
                    return Err(StoreError::Integrity(format!(
                        "latest checkpoint {pointer} is not a complete recoverable pair"
                    )));
                }
            }
            let recovered_latest = heights.last().copied().unwrap_or(0).max(pointer);
            if height < recovered_latest {
                return Err(StoreError::Integrity(format!(
                    "checkpoint height {height} predates {recovered_latest}"
                )));
            }
            if heights.contains(&height) {
                let stored_blocklace = table
                    .get(checkpoint_key.as_str())?
                    .map(|g| g.value().to_vec());
                let stored_ledger = table.get(ledger_key.as_str())?.map(|g| g.value().to_vec());
                if stored_blocklace.as_deref() != Some(blocklace)
                    || stored_ledger.as_deref() != Some(ledger)
                {
                    return Err(StoreError::Integrity(format!(
                        "checkpoint height {height} is already bound to a different pair"
                    )));
                }
            } else {
                // A legacy interrupted writer may have stored one or both
                // halves before it reached the index. Never overwrite existing
                // nonempty bytes at this height with a different snapshot.
                for (key, expected) in [
                    (checkpoint_key.as_str(), blocklace),
                    (ledger_key.as_str(), ledger),
                ] {
                    if let Some(existing) = table.get(key)?
                        && !existing.value().is_empty()
                        && existing.value() != expected
                    {
                        return Err(StoreError::Integrity(format!(
                            "unindexed checkpoint height {height} already has different bytes"
                        )));
                    }
                }
                heights.push(height);
                table.insert(checkpoint_key.as_str(), blocklace)?;
                #[cfg(test)]
                if fail_checkpoint_publish_after(1) {
                    return Err(StoreError::Database(
                        "checkpoint pair fault after DAG insert".into(),
                    ));
                }
                table.insert(ledger_key.as_str(), ledger)?;
                #[cfg(test)]
                if fail_checkpoint_publish_after(2) {
                    return Err(StoreError::Database(
                        "checkpoint pair fault after ledger insert".into(),
                    ));
                }
            }
            // Prune only superseded derived pairs, not the authoritative source
            // blocks or ledger checkpoints needed by historical snapshot consumers.
            while height > recovered_latest && heights.len() > keep_last {
                let old = heights.remove(0);
                table.remove(format!("blocklace_checkpoint_{old}").as_str())?;
                table.remove(format!("blocklace_ledger_snapshot_{old}").as_str())?;
            }
            let encoded = postcard::to_stdvec(&heights)?;
            table.insert(BLOCKLACE_CHECKPOINT_HEIGHTS, encoded.as_slice())?;
            #[cfg(test)]
            if fail_checkpoint_publish_after(3) {
                return Err(StoreError::Database(
                    "checkpoint pair fault after rollover/index".into(),
                ));
            }
            table.insert(BLOCKLACE_CHECKPOINT_LATEST, height.to_le_bytes().as_slice())?;
            #[cfg(test)]
            if fail_checkpoint_publish_after(4) {
                return Err(StoreError::Database(
                    "checkpoint pair fault after latest pointer".into(),
                ));
            }
        }
        txn.commit()?;
        Ok(())
    }

    /// Test a published height without copying the potentially enormous DAG and
    /// ledger snapshots into the executor's hot RAM on every finality callback.
    pub fn has_published_blocklace_checkpoint_pair(&self, height: u64) -> Result<bool> {
        if let Some(fault) = self.config_io_fault() {
            return Err(fault);
        }
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::METADATA_BYTES)?;
        let index = table.get(BLOCKLACE_CHECKPOINT_HEIGHTS)?;
        let latest = table.get(BLOCKLACE_CHECKPOINT_LATEST)?;
        if !checkpoint_height_is_published(
            index.as_ref().map(|g| g.value()),
            latest.as_ref().map(|g| g.value()),
            height,
        )? {
            return Ok(false);
        }
        if let Some(pointer) = stale_checkpoint_pointer(
            index.as_ref().map(|g| g.value()),
            latest.as_ref().map(|g| g.value()),
        )? {
            let c = table
                .get(format!("blocklace_checkpoint_{pointer}").as_str())?
                .map(|g| g.value().len());
            let l = table
                .get(format!("blocklace_ledger_snapshot_{pointer}").as_str())?
                .map(|g| g.value().len());
            if !matches!((c, l), (Some(c), Some(l)) if c > 0 && l > 0) {
                return Err(StoreError::Integrity(format!(
                    "checkpoint index tail has torn predecessor {pointer}"
                )));
            }
        }
        let c = table
            .get(format!("blocklace_checkpoint_{height}").as_str())?
            .map(|g| g.value().len());
        let l = table
            .get(format!("blocklace_ledger_snapshot_{height}").as_str())?
            .map(|g| g.value().len());
        if c == Some(0)
            && l == Some(0)
            && legacy_latest_tombstone(
                index.as_ref().map(|g| g.value()),
                latest.as_ref().map(|g| g.value()),
                height,
            )?
        {
            return Ok(false);
        }
        if !matches!((c, l), (Some(c), Some(l)) if c > 0 && l > 0) {
            return Err(StoreError::Integrity(format!(
                "published checkpoint {height} has no complete pair"
            )));
        }
        Ok(true)
    }

    /// Read only complete published pairs from one consistent transaction. A
    /// previous interrupted writer's orphaned half is never served by height.
    pub fn published_blocklace_checkpoint_pair(
        &self,
        height: u64,
    ) -> Result<Option<(Vec<u8>, Vec<u8>)>> {
        if let Some(fault) = self.config_io_fault() {
            return Err(fault);
        }
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::METADATA_BYTES)?;
        let index = table.get(BLOCKLACE_CHECKPOINT_HEIGHTS)?;
        let latest = table.get(BLOCKLACE_CHECKPOINT_LATEST)?;
        if !checkpoint_height_is_published(
            index.as_ref().map(|g| g.value()),
            latest.as_ref().map(|g| g.value()),
            height,
        )? {
            return Ok(None);
        }
        if let Some(pointer) = stale_checkpoint_pointer(
            index.as_ref().map(|g| g.value()),
            latest.as_ref().map(|g| g.value()),
        )? {
            let c = table
                .get(format!("blocklace_checkpoint_{pointer}").as_str())?
                .map(|g| g.value().len());
            let l = table
                .get(format!("blocklace_ledger_snapshot_{pointer}").as_str())?
                .map(|g| g.value().len());
            if !matches!((c, l), (Some(c), Some(l)) if c > 0 && l > 0) {
                return Err(StoreError::Integrity(format!(
                    "checkpoint index tail has torn predecessor {pointer}"
                )));
            }
        }
        let checkpoint = table
            .get(format!("blocklace_checkpoint_{height}").as_str())?
            .map(|g| g.value().to_vec());
        let ledger = table
            .get(format!("blocklace_ledger_snapshot_{height}").as_str())?
            .map(|g| g.value().to_vec());
        match (checkpoint, ledger) {
            (Some(c), Some(l)) if !c.is_empty() && !l.is_empty() => Ok(Some((c, l))),
            (Some(c), Some(l))
                if c.is_empty()
                    && l.is_empty()
                    && legacy_latest_tombstone(
                        index.as_ref().map(|g| g.value()),
                        latest.as_ref().map(|g| g.value()),
                        height,
                    )? =>
            {
                Ok(None)
            }
            _ => Err(StoreError::Integrity(format!(
                "published checkpoint {height} has no complete pair"
            ))),
        }
    }

    /// Hash both published halves while borrowing them from one read transaction.
    /// This is structural data only; the node's private finality receipt binds
    /// these bytes to H and its durable finalized ordinal.
    pub fn published_blocklace_checkpoint_pair_hashes(
        &self,
        height: u64,
    ) -> Result<Option<([u8; 32], [u8; 32])>> {
        if !self.has_published_blocklace_checkpoint_pair(height)? {
            return Ok(None);
        }
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::METADATA_BYTES)?;
        let dag = table
            .get(format!("blocklace_checkpoint_{height}").as_str())?
            .ok_or_else(|| StoreError::Integrity("checkpoint DAG disappeared".into()))?;
        let ledger = table
            .get(format!("blocklace_ledger_snapshot_{height}").as_str())?
            .ok_or_else(|| StoreError::Integrity("checkpoint ledger disappeared".into()))?;
        Ok(Some((
            *blake3::hash(dag.value()).as_bytes(),
            *blake3::hash(ledger.value()).as_bytes(),
        )))
    }

    /// Structural candidate only: the node must still require a private
    /// exact-height finalized producer receipt before advertising.
    pub fn latest_blocklace_checkpoint_candidate(&self) -> Result<Option<u64>> {
        if let Some(fault) = self.config_io_fault() {
            return Err(fault);
        }
        let (heights, pointer) = {
            let txn = self.db.begin_read()?;
            let table = txn.open_table(tables::METADATA_BYTES)?;
            let heights: Vec<u64> = table
                .get(BLOCKLACE_CHECKPOINT_HEIGHTS)?
                .map(|g| postcard::from_bytes(g.value()))
                .transpose()?
                .unwrap_or_default();
            let pointer = table
                .get(BLOCKLACE_CHECKPOINT_LATEST)?
                .map(|g| {
                    <[u8; 8]>::try_from(g.value())
                        .map(u64::from_le_bytes)
                        .map_err(|_| {
                            StoreError::Integrity("invalid latest checkpoint height".into())
                        })
                })
                .transpose()?;
            (heights, pointer)
        };
        let candidate = heights.last().copied().into_iter().chain(pointer).max();
        if let Some(height) = candidate {
            // Validates sorted index, pointer relation and complete candidate.
            if self.has_published_blocklace_checkpoint_pair(height)? {
                return Ok(Some(height));
            }
            // The old duplicate-at-latest tombstone erased only derived bytes.
            // Fall back to the previous complete indexed image, if any.
            for height in heights.into_iter().rev().filter(|h| Some(*h) != pointer) {
                if self.has_published_blocklace_checkpoint_pair(height)? {
                    return Ok(Some(height));
                }
            }
        }
        Ok(None)
    }

    // =========================================================================
    // Blocklace Block Storage
    // =========================================================================

    /// Persist a single block to the store.
    ///
    /// Called on every new block (local or received from peers). Uses the block's
    /// ID as the key and postcard-serialized bytes as the value.
    ///
    /// This is idempotent: re-inserting the same block is a no-op at the storage
    /// level (redb overwrites with identical data).
    pub fn persist_block(&self, block: &Block) -> Result<()> {
        if self
            .fail_persist_block
            .load(std::sync::atomic::Ordering::Relaxed)
        {
            return Err(StoreError::Database(
                "persist_block fault injected (test-only fail_persist_block seam)".to_string(),
            ));
        }
        let key = block.id().0;
        let value = block.to_bytes();
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::BLOCKLACE_BLOCKS)?;
            table.insert(&key, value.as_slice())?;
        }
        txn.commit()?;
        Ok(())
    }

    /// Test-only: arm/disarm the [`Self::persist_block`] fault seam (finding F2).
    /// Never called in production — a node durability test sets it to exercise the
    /// authored-block fail-closed rollback + no-broadcast path through the real
    /// producer, then clears it to let subsequent persists succeed.
    #[doc(hidden)]
    pub fn set_fail_persist_block(&self, fail: bool) {
        self.fail_persist_block
            .store(fail, std::sync::atomic::Ordering::Relaxed);
    }

    /// Persist multiple blocks in a single transaction (batch write).
    ///
    /// More efficient than individual `persist_block` calls when receiving
    /// a delta of multiple blocks from a peer.
    pub fn persist_blocks(&self, blocks: &[Block]) -> Result<()> {
        if blocks.is_empty() {
            return Ok(());
        }
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::BLOCKLACE_BLOCKS)?;
            for block in blocks {
                let key = block.id().0;
                let value = block.to_bytes();
                table.insert(&key, value.as_slice())?;
            }
        }
        txn.commit()?;
        Ok(())
    }

    /// Persist blocklace metadata (tips, equivocators, ordering state).
    ///
    /// Called periodically (e.g., after finality advances) rather than on every
    /// block insert, since metadata can be reconstructed from blocks if needed.
    pub fn persist_blocklace_meta(&self, meta: &BlocklaceMeta) -> Result<()> {
        let value =
            postcard::to_stdvec(meta).map_err(|e| StoreError::Serialization(e.to_string()))?;
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::BLOCKLACE_META)?;
            table.insert(tables::BLOCKLACE_META_KEY, value.as_slice())?;
        }
        txn.commit()?;
        Ok(())
    }

    /// Persist the executed_up_to index (how far the finality executor has processed).
    ///
    /// This prevents re-executing already-processed turns on restart.
    pub fn persist_executed_up_to(&self, index: u64) -> Result<()> {
        let value = index.to_le_bytes();
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::BLOCKLACE_META)?;
            table.insert(tables::BLOCKLACE_EXECUTED_UP_TO_KEY, value.as_slice())?;
        }
        txn.commit()?;
        Ok(())
    }

    /// Persist the executed finalized-block IDENTITY set (first-served order).
    ///
    /// This is the durable half of the node's identity execution cursor (the
    /// TauPrefixMonotone closure): on restart, execution resumes from this set
    /// (∪ the commit log's per-turn `block_id`s, which atomically cover the
    /// turn-carrying blocks), NEVER from an index into the tau order — the
    /// order can shift under honest catch-up growth. Written at the same batch
    /// cadence as [`Self::persist_blocklace_meta`]; if it lags a crash, the
    /// uncovered non-turn blocks re-process idempotently and turns are covered
    /// exactly by the commit log.
    pub fn persist_executed_block_ids(&self, ids: &[BlockId]) -> Result<()> {
        let value =
            postcard::to_stdvec(ids).map_err(|e| StoreError::Serialization(e.to_string()))?;
        let txn = self.db.begin_write()?;
        {
            let mut table = txn.open_table(tables::BLOCKLACE_META)?;
            table.insert(tables::BLOCKLACE_EXECUTED_IDS_KEY, value.as_slice())?;
        }
        txn.commit()?;
        Ok(())
    }

    /// Load the executed finalized-block identity set.
    ///
    /// Returns an empty vector if never persisted (fresh start or pre-upgrade
    /// DB — in the latter case the commit log still recovers every turn
    /// exactly, and non-turn blocks re-process idempotently once).
    pub fn load_executed_block_ids(&self) -> Result<Vec<BlockId>> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_META)?;
        match table.get(tables::BLOCKLACE_EXECUTED_IDS_KEY)? {
            Some(guard) => {
                let ids: Vec<BlockId> = postcard::from_bytes(guard.value())?;
                Ok(ids)
            }
            None => Ok(Vec::new()),
        }
    }

    /// Load the executed_up_to index from the store.
    ///
    /// Returns 0 if not previously persisted (fresh start).
    pub fn load_executed_up_to(&self) -> Result<u64> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_META)?;
        match table.get(tables::BLOCKLACE_EXECUTED_UP_TO_KEY)? {
            Some(guard) => {
                let bytes = guard.value();
                if bytes.len() == 8 {
                    Ok(u64::from_le_bytes(bytes.try_into().unwrap()))
                } else {
                    Ok(0)
                }
            }
            None => Ok(0),
        }
    }

    // =========================================================================
    // Blocklace Restoration
    // =========================================================================

    /// Load all persisted blocks from the store.
    ///
    /// Returns the raw block list (unordered). The caller is responsible for
    /// feeding them into `Blocklace::from_checkpoint()` with the appropriate
    /// metadata.
    pub fn load_all_blocks(&self) -> Result<Vec<Block>> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_BLOCKS)?;

        let mut blocks = Vec::new();
        for entry in table.iter()? {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let bytes = entry.1.value();
            let block = Block::from_bytes(bytes).ok_or_else(|| {
                StoreError::Serialization("failed to deserialize persisted block".to_string())
            })?;
            blocks.push(block);
        }
        Ok(blocks)
    }

    /// Load blocklace metadata from the store.
    ///
    /// Returns `None` if no metadata has been persisted yet (first run).
    pub fn load_blocklace_meta(&self) -> Result<Option<BlocklaceMeta>> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_META)?;
        match table.get(tables::BLOCKLACE_META_KEY)? {
            Some(guard) => {
                let meta: BlocklaceMeta = postcard::from_bytes(guard.value())?;
                Ok(Some(meta))
            }
            None => Ok(None),
        }
    }

    /// Restore a complete blocklace from persisted state.
    ///
    /// Loads all blocks and metadata, then reconstructs the blocklace using the
    /// AUTHENTICATING `Blocklace::from_checkpoint()`: every block's Ed25519
    /// signature is re-verified, causal closure is enforced (a dangling
    /// predecessor refuses the whole restore), equivocation is re-derived, and
    /// tips are re-derived from the authenticated blocks rather than copied
    /// from metadata. The persisted `equivocators` set is folded in only as a
    /// LOWER bound — an offline tamper of the metadata can never UN-flag a
    /// creator whose evidence pair is still in the blocks.
    ///
    /// ⚑ Until 2026-08-08 this used `from_checkpoint_trusted` on the grounds
    /// that "it came from our own local store". That justification contradicts
    /// the node's own recovery threat model: the NODE-1 signed-anchor exists
    /// precisely because an offline attacker with write access to this redb can
    /// rewrite it. The restart path must not trust what the running path
    /// verifies. What this still does NOT re-check (and why): the ML-DSA half
    /// of each block (the enrolled PQ roster is derived from committee state
    /// that is itself derived from this lace — checking it here would be
    /// circular; the ed25519 half plus the hybrid `creator` commitment carries
    /// the binding, and only a quantum adversary WITH store write access beats
    /// it), and the ordering/attested frontier (asserted; bounded by the
    /// NODE-1 root convergence and the commit-log identity cursor).
    ///
    /// Returns `None` if no blocks have been persisted (fresh start).
    pub fn load_blocklace(
        &self,
        signing_key: ed25519_dalek::SigningKey,
        quorum_threshold: usize,
    ) -> Result<Option<(Blocklace, usize)>> {
        let blocks = self.load_all_blocks()?;
        if blocks.is_empty() {
            return Ok(None);
        }

        let meta = self.load_blocklace_meta()?;
        let executed_up_to = self.load_executed_up_to()? as usize;

        // Build a CheckpointData from our persisted state.
        let checkpoint = CheckpointData {
            blocks: blocks.iter().map(|b| b.to_bytes()).collect(),
            tips: meta.as_ref().map(|m| m.tips.clone()).unwrap_or_default(),
            equivocators: meta
                .as_ref()
                .map(|m| m.equivocators.clone())
                .unwrap_or_default(),
            ordered_block_ids: meta
                .as_ref()
                .map(|m| m.ordered_block_ids.clone())
                .unwrap_or_default(),
            attested_block_ids: meta
                .as_ref()
                .map(|m| m.attested_block_ids.clone())
                .unwrap_or_default(),
        };

        // AUTHENTICATE on restore. Local-disk provenance is not an integrity
        // boundary (the NODE-1 anchor's own threat model: an offline attacker
        // can write this redb), so the restart path runs the same signature +
        // closure + equivocation checks the live receive path runs. A refusal
        // here is a STORE INTEGRITY EVENT and the node must not start on it.
        let blocklace = Blocklace::from_checkpoint(&checkpoint, signing_key, quorum_threshold)
            .map_err(StoreError::Integrity)?;

        Ok(Some((blocklace, executed_up_to)))
    }

    /// Get the number of blocks stored in the blocklace table.
    pub fn blocklace_block_count(&self) -> Result<u64> {
        let txn = self.db.begin_read()?;
        let table = txn.open_table(tables::BLOCKLACE_BLOCKS)?;
        Ok(table.len()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(seed: u8) -> ed25519_dalek::SigningKey {
        ed25519_dalek::SigningKey::from_bytes(&[seed; 32])
    }

    fn published_heights(store: &PersistentStore) -> Vec<u64> {
        postcard::from_bytes(
            &store
                .get_config(BLOCKLACE_CHECKPOINT_HEIGHTS)
                .unwrap()
                .unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn checkpoint_pair_rollover_reopen_and_historical_blocks_survive() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("checkpoint.redb");
        {
            let store = PersistentStore::open(&path).unwrap();
            persist_honest_lace(&store, &key(7));
            for h in 1..=7 {
                store
                    .publish_blocklace_checkpoint_pair(h, &[h as u8], &[h as u8 + 20], 5)
                    .unwrap();
            }
            assert_eq!(
                store.blocklace_block_count().unwrap(),
                3,
                "source blocks survive derived-pair rollover"
            );
            assert_eq!(published_heights(&store), vec![3, 4, 5, 6, 7]);
            assert!(
                store
                    .published_blocklace_checkpoint_pair(2)
                    .unwrap()
                    .is_none()
            );
            assert!(
                store
                    .get_config("blocklace_checkpoint_2")
                    .unwrap()
                    .is_none(),
                "evicted pair is removed, not tombstoned"
            );
        }
        let store = PersistentStore::open(&path).unwrap();
        assert_eq!(store.blocklace_block_count().unwrap(), 3);
        let (replayed, _) = store.load_blocklace(key(7), 1).unwrap().unwrap();
        assert_eq!(
            replayed.len(),
            3,
            "all historical signed blocks authenticate on restart"
        );
        assert_eq!(published_heights(&store), vec![3, 4, 5, 6, 7]);
        for h in 3..=7 {
            assert_eq!(
                store.published_blocklace_checkpoint_pair(h).unwrap(),
                Some((vec![h as u8], vec![h as u8 + 20]))
            );
        }
    }

    #[test]
    fn same_height_is_exact_and_does_not_evict_or_duplicate() {
        let store = PersistentStore::open_in_memory().unwrap();
        for h in 1..=5 {
            store
                .publish_blocklace_checkpoint_pair(h, &[h as u8], &[h as u8 + 20], 5)
                .unwrap();
        }
        for _ in 0..8 {
            store
                .publish_blocklace_checkpoint_pair(5, &[5], &[25], 5)
                .unwrap();
        }
        assert_eq!(published_heights(&store), vec![1, 2, 3, 4, 5]);
        // A repeated height does not retroactively shrink an older window.
        store
            .publish_blocklace_checkpoint_pair(5, &[5], &[25], 2)
            .unwrap();
        assert_eq!(published_heights(&store), vec![1, 2, 3, 4, 5]);
        assert!(
            matches!(
                store.publish_blocklace_checkpoint_pair(5, &[99], &[25], 5),
                Err(StoreError::Integrity(ref message)) if message.contains("already bound")
            ),
            "height is immutable even if only DAG differs"
        );
        assert_eq!(
            store.published_blocklace_checkpoint_pair(5).unwrap(),
            Some((vec![5], vec![25]))
        );
        store
            .publish_blocklace_checkpoint_pair(6, &[6], &[26], 5)
            .unwrap();
        assert_eq!(published_heights(&store), vec![2, 3, 4, 5, 6]);
        assert!(
            store
                .published_blocklace_checkpoint_pair(1)
                .unwrap()
                .is_none()
        );
        assert!(
            matches!(
                store.publish_blocklace_checkpoint_pair(4, &[4], &[24], 5),
                Err(StoreError::Integrity(ref message)) if message.contains("predates")
            ),
            "out-of-order publication cannot roll latest back"
        );
    }

    #[test]
    fn failed_checkpoint_pair_transaction_leaves_old_served_pair_untouched() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("failed-pair.redb");
        let mut store = PersistentStore::open(&path).unwrap();
        store
            .publish_blocklace_checkpoint_pair(1, b"dag", b"ledger", 1)
            .unwrap();
        for step in [1, 2, 3, 4] {
            FAIL_CHECKPOINT_PUBLISH_AFTER.with(|fault| fault.set(Some(step)));
            let err = store
                .publish_blocklace_checkpoint_pair(2, b"newdag", b"newledger", 1)
                .unwrap_err();
            assert!(format!("{err}").contains("checkpoint pair fault"));
            drop(store);
            store = PersistentStore::open(&path).unwrap();
            assert_eq!(published_heights(&store), vec![1]);
            assert_eq!(
                store.get_config(BLOCKLACE_CHECKPOINT_LATEST).unwrap(),
                Some(1u64.to_le_bytes().to_vec())
            );
            assert_eq!(
                store.published_blocklace_checkpoint_pair(1).unwrap(),
                Some((b"dag".to_vec(), b"ledger".to_vec()))
            );
            assert!(
                store
                    .get_config("blocklace_checkpoint_2")
                    .unwrap()
                    .is_none()
            );
            assert!(
                store
                    .get_config("blocklace_ledger_snapshot_2")
                    .unwrap()
                    .is_none()
            );
        }
        store.set_fail_config_io(true);
        assert!(matches!(
            store.publish_blocklace_checkpoint_pair(2, b"newdag", b"newledger", 1),
            Err(StoreError::Database(ref message)) if message.contains("config io fault injected")
        ));
        store.set_fail_config_io(false);
        assert_eq!(published_heights(&store), vec![1]);
        store
            .publish_blocklace_checkpoint_pair(2, b"newdag", b"newledger", 1)
            .unwrap();
        assert_eq!(published_heights(&store), vec![2]);
        assert_eq!(
            store.published_blocklace_checkpoint_pair(2).unwrap(),
            Some((b"newdag".to_vec(), b"newledger".to_vec()))
        );
    }

    #[test]
    fn legacy_duplicate_heights_repair_without_erasing_a_live_pair() {
        let store = PersistentStore::open_in_memory().unwrap();
        for h in 1..=3 {
            store
                .set_config(&format!("blocklace_checkpoint_{h}"), &[h as u8])
                .unwrap();
            store
                .set_config(&format!("blocklace_ledger_snapshot_{h}"), &[h as u8 + 20])
                .unwrap();
        }
        store
            .set_config(
                BLOCKLACE_CHECKPOINT_HEIGHTS,
                &postcard::to_stdvec(&vec![1u64, 2, 2, 3]).unwrap(),
            )
            .unwrap();
        store
            .set_config(BLOCKLACE_CHECKPOINT_LATEST, &3u64.to_le_bytes())
            .unwrap();
        store
            .publish_blocklace_checkpoint_pair(4, &[4], &[24], 3)
            .unwrap();
        assert_eq!(published_heights(&store), vec![2, 3, 4]);
        assert!(
            store
                .get_config("blocklace_checkpoint_1")
                .unwrap()
                .is_none()
        );
        assert_eq!(
            store.published_blocklace_checkpoint_pair(2).unwrap(),
            Some((vec![2], vec![22]))
        );
    }

    #[test]
    fn unindexed_orphan_cannot_be_rebound_to_different_bytes() {
        let store = PersistentStore::open_in_memory().unwrap();
        store
            .set_config("blocklace_checkpoint_1", b"original")
            .unwrap();
        assert!(matches!(
            store.publish_blocklace_checkpoint_pair(1, b"replacement", b"ledger", 5),
            Err(StoreError::Integrity(ref message)) if message.contains("unindexed checkpoint")
        ));
        assert_eq!(
            store.get_config("blocklace_checkpoint_1").unwrap(),
            Some(b"original".to_vec())
        );
        assert_eq!(
            store.get_config(BLOCKLACE_CHECKPOINT_HEIGHTS).unwrap(),
            None
        );
        store
            .publish_blocklace_checkpoint_pair(1, b"original", b"ledger", 5)
            .unwrap();
        assert_eq!(published_heights(&store), vec![1]);
    }

    #[test]
    fn legacy_tombstones_are_reclaimed_without_erasing_live_pairs() {
        let store = PersistentStore::open_in_memory().unwrap();
        for h in 1..=3 {
            store
                .set_config(
                    &format!("blocklace_checkpoint_{h}"),
                    if h == 1 { b"" } else { b"dag" },
                )
                .unwrap();
            store
                .set_config(
                    &format!("blocklace_ledger_snapshot_{h}"),
                    if h == 1 { b"" } else { b"ledger" },
                )
                .unwrap();
        }
        store
            .set_config(
                BLOCKLACE_CHECKPOINT_HEIGHTS,
                &postcard::to_stdvec(&vec![1u64, 1, 2, 3]).unwrap(),
            )
            .unwrap();
        store
            .set_config(BLOCKLACE_CHECKPOINT_LATEST, &3u64.to_le_bytes())
            .unwrap();
        store
            .publish_blocklace_checkpoint_pair(4, b"next", b"nextledger", 3)
            .unwrap();
        assert_eq!(published_heights(&store), vec![2, 3, 4]);
        assert_eq!(store.get_config("blocklace_checkpoint_1").unwrap(), None);
        assert_eq!(
            store.get_config("blocklace_ledger_snapshot_1").unwrap(),
            None
        );
        assert_eq!(
            store.published_blocklace_checkpoint_pair(2).unwrap(),
            Some((b"dag".to_vec(), b"ledger".to_vec()))
        );
    }

    #[test]
    fn legacy_pointer_ahead_of_index_recovers_only_complete_pair() {
        let store = PersistentStore::open_in_memory().unwrap();
        store.set_config("blocklace_checkpoint_2", b"dag").unwrap();
        store
            .set_config(BLOCKLACE_CHECKPOINT_LATEST, &2u64.to_le_bytes())
            .unwrap();
        assert!(matches!(
            store.publish_blocklace_checkpoint_pair(3, b"next", b"ledger", 5),
            Err(StoreError::Integrity(ref message)) if message.contains("not a complete recoverable pair")
        ));
        assert_eq!(
            store.get_config(BLOCKLACE_CHECKPOINT_HEIGHTS).unwrap(),
            None
        );
        store
            .set_config("blocklace_ledger_snapshot_2", b"oldledger")
            .unwrap();
        store
            .publish_blocklace_checkpoint_pair(3, b"next", b"ledger", 5)
            .unwrap();
        assert_eq!(published_heights(&store), vec![2, 3]);
        assert_eq!(
            store.published_blocklace_checkpoint_pair(2).unwrap(),
            Some((b"dag".to_vec(), b"oldledger".to_vec()))
        );
    }

    #[test]
    fn duplicate_latest_legacy_tombstone_recovers_without_erasing_older_pair() {
        let store = PersistentStore::open_in_memory().unwrap();
        store
            .set_config("blocklace_checkpoint_1", b"historical dag")
            .unwrap();
        store
            .set_config("blocklace_ledger_snapshot_1", b"historical ledger")
            .unwrap();
        store.set_config("blocklace_checkpoint_2", b"").unwrap();
        store
            .set_config("blocklace_ledger_snapshot_2", b"")
            .unwrap();
        store
            .set_config(
                BLOCKLACE_CHECKPOINT_HEIGHTS,
                &postcard::to_stdvec(&vec![1u64, 2, 2]).unwrap(),
            )
            .unwrap();
        store
            .set_config(BLOCKLACE_CHECKPOINT_LATEST, &2u64.to_le_bytes())
            .unwrap();
        assert!(!store.has_published_blocklace_checkpoint_pair(2).unwrap());
        assert_eq!(
            store.latest_blocklace_checkpoint_candidate().unwrap(),
            Some(1)
        );
        store
            .publish_blocklace_checkpoint_pair(2, b"restored dag", b"restored ledger", 5)
            .unwrap();
        assert_eq!(published_heights(&store), vec![1, 2]);
        assert_eq!(
            store.latest_blocklace_checkpoint_candidate().unwrap(),
            Some(2)
        );
        assert_eq!(
            store.published_blocklace_checkpoint_pair(1).unwrap(),
            Some((b"historical dag".to_vec(), b"historical ledger".to_vec()))
        );
        assert_eq!(
            store.published_blocklace_checkpoint_pair(2).unwrap(),
            Some((b"restored dag".to_vec(), b"restored ledger".to_vec()))
        );
        assert!(matches!(
            store.publish_blocklace_checkpoint_pair(2, b"other dag", b"restored ledger", 5),
            Err(StoreError::Integrity(_))
        ));
    }

    #[test]
    fn ambiguous_latest_tombstone_and_torn_pair_refuse_without_changes() {
        let store = PersistentStore::open_in_memory().unwrap();
        store.set_config("blocklace_checkpoint_1", b"").unwrap();
        store
            .set_config("blocklace_ledger_snapshot_1", b"")
            .unwrap();
        store
            .set_config(
                BLOCKLACE_CHECKPOINT_HEIGHTS,
                &postcard::to_stdvec(&vec![1u64]).unwrap(),
            )
            .unwrap();
        store
            .set_config(BLOCKLACE_CHECKPOINT_LATEST, &1u64.to_le_bytes())
            .unwrap();
        assert!(store.has_published_blocklace_checkpoint_pair(1).is_err());
        assert!(
            store
                .publish_blocklace_checkpoint_pair(1, b"dag", b"ledger", 5)
                .is_err()
        );
        assert_eq!(
            store.get_config("blocklace_checkpoint_1").unwrap(),
            Some(vec![])
        );
        store
            .set_config(
                BLOCKLACE_CHECKPOINT_HEIGHTS,
                &postcard::to_stdvec(&vec![1u64, 1]).unwrap(),
            )
            .unwrap();
        store.set_config("blocklace_checkpoint_1", b"half").unwrap();
        assert!(store.has_published_blocklace_checkpoint_pair(1).is_err());
        assert!(
            store
                .publish_blocklace_checkpoint_pair(1, b"dag", b"ledger", 5)
                .is_err()
        );
        assert_eq!(
            store.get_config("blocklace_checkpoint_1").unwrap(),
            Some(b"half".to_vec())
        );
    }

    #[test]
    fn legacy_failed_latest_write_recovers_only_single_complete_index_tail() {
        let store = PersistentStore::open_in_memory().unwrap();
        store.set_config("blocklace_checkpoint_1", b"dag1").unwrap();
        store
            .set_config("blocklace_ledger_snapshot_1", b"ledger1")
            .unwrap();
        store.set_config("blocklace_checkpoint_2", b"dag2").unwrap();
        store
            .set_config("blocklace_ledger_snapshot_2", b"ledger2")
            .unwrap();
        store
            .set_config(BLOCKLACE_CHECKPOINT_LATEST, &1u64.to_le_bytes())
            .unwrap();
        store
            .set_config(
                BLOCKLACE_CHECKPOINT_HEIGHTS,
                &postcard::to_stdvec(&vec![1u64, 2]).unwrap(),
            )
            .unwrap();
        assert_eq!(
            store.latest_blocklace_checkpoint_candidate().unwrap(),
            Some(2)
        );
        assert!(store.has_published_blocklace_checkpoint_pair(2).unwrap());
        store
            .publish_blocklace_checkpoint_pair(3, b"dag3", b"ledger3", 5)
            .unwrap();
        assert_eq!(published_heights(&store), vec![1, 2, 3]);
        assert_eq!(
            store.get_config(BLOCKLACE_CHECKPOINT_LATEST).unwrap(),
            Some(3u64.to_le_bytes().to_vec())
        );
        assert_eq!(
            store.published_blocklace_checkpoint_pair(2).unwrap(),
            Some((b"dag2".to_vec(), b"ledger2".to_vec()))
        );
    }

    #[test]
    fn incomplete_or_ambiguous_failed_latest_write_never_advances_pointer() {
        for extra_complete in [false, true] {
            let store = PersistentStore::open_in_memory().unwrap();
            store.set_config("blocklace_checkpoint_1", b"dag1").unwrap();
            store
                .set_config("blocklace_ledger_snapshot_1", b"ledger1")
                .unwrap();
            store.set_config("blocklace_checkpoint_2", b"dag2").unwrap();
            if extra_complete {
                store
                    .set_config("blocklace_ledger_snapshot_2", b"ledger2")
                    .unwrap();
                store.set_config("blocklace_checkpoint_3", b"dag3").unwrap();
                store
                    .set_config("blocklace_ledger_snapshot_3", b"ledger3")
                    .unwrap();
            }
            let index = if extra_complete {
                vec![1u64, 2, 3]
            } else {
                vec![1, 2]
            };
            store
                .set_config(
                    BLOCKLACE_CHECKPOINT_HEIGHTS,
                    &postcard::to_stdvec(&index).unwrap(),
                )
                .unwrap();
            store
                .set_config(BLOCKLACE_CHECKPOINT_LATEST, &1u64.to_le_bytes())
                .unwrap();
            assert!(store.latest_blocklace_checkpoint_candidate().is_err());
            assert!(
                store
                    .publish_blocklace_checkpoint_pair(4, b"new", b"newledger", 5)
                    .is_err()
            );
            assert_eq!(
                store.get_config(BLOCKLACE_CHECKPOINT_LATEST).unwrap(),
                Some(1u64.to_le_bytes().to_vec())
            );
            assert_eq!(
                store.get_config("blocklace_checkpoint_2").unwrap(),
                Some(b"dag2".to_vec())
            );
        }
    }

    #[test]
    fn duplicate_stale_tail_does_not_launder_two_index_writes_into_one() {
        let store = PersistentStore::open_in_memory().unwrap();
        for h in [1u64, 2] {
            store
                .set_config(&format!("blocklace_checkpoint_{h}"), &[h as u8])
                .unwrap();
            store
                .set_config(&format!("blocklace_ledger_snapshot_{h}"), &[h as u8 + 20])
                .unwrap();
        }
        store
            .set_config(BLOCKLACE_CHECKPOINT_LATEST, &1u64.to_le_bytes())
            .unwrap();
        store
            .set_config(
                BLOCKLACE_CHECKPOINT_HEIGHTS,
                &postcard::to_stdvec(&vec![1u64, 2, 2]).unwrap(),
            )
            .unwrap();
        assert!(store.has_published_blocklace_checkpoint_pair(2).is_err());
        assert!(
            store
                .publish_blocklace_checkpoint_pair(3, b"next", b"nextledger", 5)
                .is_err()
        );
        assert_eq!(
            store.get_config(BLOCKLACE_CHECKPOINT_LATEST).unwrap(),
            Some(1u64.to_le_bytes().to_vec())
        );
        assert_eq!(
            store.get_config("blocklace_checkpoint_2").unwrap(),
            Some(vec![2])
        );
    }

    #[test]
    fn archival_pair_retention_keeps_every_historical_bootstrap_height() {
        let store = PersistentStore::open_in_memory().unwrap();
        for height in 1..=8 {
            store
                .publish_blocklace_checkpoint_pair(
                    height,
                    &[height as u8],
                    &[height as u8 + 20],
                    usize::MAX,
                )
                .unwrap();
        }
        assert_eq!(published_heights(&store), (1..=8).collect::<Vec<_>>());
        assert_eq!(
            store.published_blocklace_checkpoint_pair(1).unwrap(),
            Some((vec![1], vec![21]))
        );
    }

    /// A small honest lace persisted the way the node persists it (blocks
    /// individually + meta blob).
    fn persist_honest_lace(store: &PersistentStore, sk: &ed25519_dalek::SigningKey) -> Blocklace {
        let mut lace = Blocklace::new(sk.clone(), 1);
        lace.add_block(dregg_blocklace::finality::Payload::Ack);
        lace.add_block(dregg_blocklace::finality::Payload::Ack);
        lace.add_block(dregg_blocklace::finality::Payload::Ack);
        let blocks: Vec<Block> = lace.iter().map(|(_, b)| b.clone()).collect();
        store.persist_blocks(&blocks).expect("persist blocks");
        let cp = lace.checkpoint();
        store
            .persist_blocklace_meta(&BlocklaceMeta {
                tips: cp.tips.clone(),
                equivocators: cp.equivocators.clone(),
                ordered_block_ids: cp.ordered_block_ids.clone(),
                attested_block_ids: cp.attested_block_ids.clone(),
            })
            .expect("persist meta");
        lace
    }

    /// HONEST POLE: a restart over an untampered store restores the same lace
    /// through the AUTHENTICATING loader (every block re-verified).
    #[test]
    fn honest_restart_restores_through_authentication() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        let sk = key(7);
        let lace = persist_honest_lace(&store, &sk);
        let (restored, _) = store
            .load_blocklace(sk, 1)
            .expect("load")
            .expect("blocks were persisted");
        assert_eq!(restored.len(), lace.len(), "every honest block restores");
        assert_eq!(restored.tips(), lace.tips(), "tips re-derive identically");
    }

    /// ⚑ CORRUPTED-CHECKPOINT POLE: a forged block in the store (valid shape,
    /// signature that does NOT verify — what an offline attacker with redb
    /// write access plants) REFUSES the whole restart. Until 2026-08-08 the
    /// restart path used `from_checkpoint_trusted` and this block sailed into
    /// the restored DAG unverified.
    #[test]
    fn forged_block_in_store_refuses_restart() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        let sk = key(7);
        persist_honest_lace(&store, &sk);

        // The mutation: an honestly-created block whose payload is altered
        // AFTER signing (the signature no longer covers the content).
        let mut forged = Block::new(
            &key(9),
            0,
            dregg_blocklace::finality::Payload::Ack,
            Vec::new(),
        );
        forged.payload = dregg_blocklace::finality::Payload::Checkpoint {
            root: [0xEE; 32],
            height: 99,
        };
        // ASSERT THE MUTATION IS PRESENT before reading the verdict: the
        // forged block genuinely fails authentication on its own.
        assert!(
            forged.verify_signature().is_err(),
            "the falsifier must be live: the tampered block's signature must not verify"
        );
        store
            .persist_block(&forged)
            .expect("attacker writes the row");

        // `expect_err` is unavailable here: the Ok payload is `(Blocklace, usize)`
        // and `Blocklace` is not `Debug`. Match, so the refusal is read explicitly.
        let err = match store.load_blocklace(key(7), 1) {
            Err(e) => e,
            Ok(_) => panic!("a store carrying a forged block must REFUSE the restart"),
        };
        assert!(
            format!("{err}").contains("signature"),
            "the refusal names the failed authentication: {err}"
        );
    }

    /// ⚑ EQUIVOCATOR-UNFLAG POLE (the `auto_evict` reversion class): the store
    /// holds a creator's incomparable pair (real, signed equivocation
    /// evidence) while the persisted metadata claims NO equivocators — the
    /// mutation an attacker (or a stale meta write) uses to launder a fork
    /// through a restart. The authenticating loader re-DERIVES equivocation
    /// from the blocks, so the flag comes back.
    #[test]
    fn cleared_equivocator_meta_cannot_unflag_on_restart() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        let sk = key(7);
        persist_honest_lace(&store, &sk);

        // A genuine equivocation: same creator, same seq, different payloads,
        // neither in the other's past.
        let eq = key(11);
        let a = Block::new(&eq, 0, dregg_blocklace::finality::Payload::Ack, Vec::new());
        let b = Block::new(
            &eq,
            0,
            dregg_blocklace::finality::Payload::Checkpoint {
                root: [0xAA; 32],
                height: 0,
            },
            Vec::new(),
        );
        assert!(
            a.verify_signature().is_ok() && b.verify_signature().is_ok(),
            "both halves of the pair are REAL signed blocks"
        );
        assert_eq!(a.creator, b.creator);
        store
            .persist_blocks(&[a.clone(), b.clone()])
            .expect("persist the pair");
        // ASSERT THE MUTATION: the persisted meta names NO equivocators.
        let meta = store
            .load_blocklace_meta()
            .expect("meta")
            .expect("meta present");
        assert!(
            meta.equivocators.is_empty(),
            "the falsifier must be live: the meta claims a clean creator set"
        );

        let (restored, _) = store
            .load_blocklace(key(7), 1)
            .expect("load")
            .expect("blocks present");
        assert!(
            restored.equivocators().contains(&a.creator),
            "restart re-derives the equivocation from the blocks — cleared metadata \
             cannot un-flag a creator whose evidence pair is persisted"
        );
    }

    /// The executed-block identity set round-trips (the durable resume state of
    /// the node's identity execution cursor — TauPrefixMonotone closure), and a
    /// never-persisted store reads back EMPTY (pre-upgrade/fresh DB: the commit
    /// log alone then covers every durably applied turn).
    #[test]
    fn executed_block_ids_round_trip_and_default_empty() {
        let store = PersistentStore::open_in_memory().expect("in-memory store");
        assert_eq!(
            store.load_executed_block_ids().expect("load"),
            Vec::<BlockId>::new(),
            "fresh/pre-upgrade store has no executed-id set"
        );

        let ids: Vec<BlockId> = (0u8..5).map(|i| BlockId([i; 32])).collect();
        store.persist_executed_block_ids(&ids).expect("persist");
        assert_eq!(store.load_executed_block_ids().expect("load"), ids);

        // Re-persisting (batch cadence) overwrites, preserving order.
        let grown: Vec<BlockId> = (0u8..7).map(|i| BlockId([i; 32])).collect();
        store.persist_executed_block_ids(&grown).expect("persist");
        assert_eq!(store.load_executed_block_ids().expect("load"), grown);
    }
}
