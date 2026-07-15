//! Space banks: quota cells that bound storage consumption.
//!
//! A quota cell bounds how much storage an entity can consume.
//! Inspired by Robigalia's Volume concept.
//! Quota = computrons allocated for storage. Each byte stored costs C computrons.
//! When quota is exhausted, writes fail. Quota can be topped up (Transfer effect).

use std::collections::HashMap;

use crate::{ComputronRefund, QuotaId, StorageError};

/// A single quota cell — bounds storage consumption for one entity.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct QuotaCell {
    pub id: QuotaId,
    /// Public key of the owner.
    pub owner: [u8; 32],
    /// Total computrons allocated to this quota.
    pub total_allocated: u64,
    /// Computrons consumed so far.
    pub total_consumed: u64,
    /// Total bytes currently stored under this quota.
    pub bytes_stored: u64,
    /// Hard cap on bytes (even if computrons available).
    pub max_bytes: Option<u64>,
}

impl QuotaCell {
    /// Remaining computrons available.
    pub fn available(&self) -> u64 {
        self.total_allocated.saturating_sub(self.total_consumed)
    }

    /// Whether a charge of `cost` computrons would succeed.
    pub fn can_charge(&self, cost: u64) -> bool {
        self.available() >= cost
    }

    /// Whether storing `additional_bytes` would exceed the byte cap.
    ///
    /// Uses saturating addition: an attacker-chosen `additional_bytes` that
    /// would overflow `u64` cannot wrap the running total below the cap and
    /// thereby slip past this check — it saturates to `u64::MAX`, which is
    /// `> max` for any finite cap, so the write is (correctly) rejected.
    pub fn would_exceed_byte_cap(&self, additional_bytes: u64) -> bool {
        if let Some(max) = self.max_bytes {
            self.bytes_stored.saturating_add(additional_bytes) > max
        } else {
            false
        }
    }

    /// Charge computrons. Returns error if insufficient.
    pub fn charge(&mut self, cost: u64) -> Result<(), StorageError> {
        if self.available() < cost {
            return Err(StorageError::QuotaExhausted {
                available: self.available(),
                required: cost,
            });
        }
        // `available() >= cost` and `available() = total_allocated -
        // total_consumed`, so `total_consumed + cost <= total_allocated`
        // cannot overflow `u64`; saturating is defensive only.
        self.total_consumed = self.total_consumed.saturating_add(cost);
        Ok(())
    }

    /// Refund computrons (from deletion). Cannot exceed total_consumed.
    pub fn refund(&mut self, amount: u64) {
        // Refund cannot make consumed go negative.
        self.total_consumed = self.total_consumed.saturating_sub(amount);
    }

    /// Record bytes stored. Saturating: the byte-cap check in
    /// [`SpaceBank::charge_write`] runs first, so in the normal path this
    /// never saturates; the saturation is a belt-and-suspenders guard so a
    /// mis-ordered call can never wrap `bytes_stored` to a small value.
    pub fn record_bytes_stored(&mut self, bytes: u64) {
        self.bytes_stored = self.bytes_stored.saturating_add(bytes);
    }

    /// Record bytes freed.
    pub fn record_bytes_freed(&mut self, bytes: u64) {
        self.bytes_stored = self.bytes_stored.saturating_sub(bytes);
    }

    /// Top up with additional computrons. Saturating: a top-up cannot wrap
    /// `total_allocated` past `u64::MAX` (which would silently shrink the
    /// available balance — an accounting corruption).
    pub fn top_up(&mut self, additional: u64) {
        self.total_allocated = self.total_allocated.saturating_add(additional);
    }
}

/// Space bank: manages multiple quota cells.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SpaceBank {
    pub quotas: HashMap<QuotaId, QuotaCell>,
    /// Computrons charged per byte for a write operation.
    pub cost_per_byte: u64,
    /// Computrons charged per relay message buffered.
    pub cost_per_relay_message: u64,
    /// Fraction of original cost refunded on deletion (0.0 to 1.0).
    pub refund_rate: f64,
    /// Next quota ID to assign.
    next_id: u64,
}

impl SpaceBank {
    /// Create a new space bank with the given cost parameters.
    pub fn new(cost_per_byte: u64, cost_per_relay_message: u64, refund_rate: f64) -> Self {
        Self {
            quotas: HashMap::new(),
            cost_per_byte,
            cost_per_relay_message,
            refund_rate: refund_rate.clamp(0.0, 1.0),
            next_id: 1,
        }
    }

    /// Allocate a new quota cell.
    pub fn allocate_quota(
        &mut self,
        owner: [u8; 32],
        initial_computrons: u64,
        max_bytes: Option<u64>,
    ) -> QuotaId {
        let id = QuotaId(self.next_id);
        self.next_id += 1;
        let cell = QuotaCell {
            id,
            owner,
            total_allocated: initial_computrons,
            total_consumed: 0,
            bytes_stored: 0,
            max_bytes,
        };
        self.quotas.insert(id, cell);
        id
    }

    /// Get a reference to a quota cell.
    pub fn get(&self, id: &QuotaId) -> Result<&QuotaCell, StorageError> {
        self.quotas.get(id).ok_or(StorageError::QuotaNotFound(*id))
    }

    /// Get a mutable reference to a quota cell.
    pub fn get_mut(&mut self, id: &QuotaId) -> Result<&mut QuotaCell, StorageError> {
        self.quotas
            .get_mut(id)
            .ok_or(StorageError::QuotaNotFound(*id))
    }

    /// Charge a write to a quota cell. Returns the cost charged.
    ///
    /// The cost `cost_per_byte * size_bytes` is computed with **checked**
    /// arithmetic: an attacker-chosen `size_bytes` can neither panic the node
    /// (overflow panic in debug = DoS) nor wrap to a near-zero charge (a
    /// wrapped cost is a billing bypass — a huge write charged ~nothing).
    /// Overflow is rejected with [`StorageError::CostOverflow`].
    pub fn charge_write(&mut self, payer: &QuotaId, size_bytes: u64) -> Result<u64, StorageError> {
        let cost = self
            .cost_per_byte
            .checked_mul(size_bytes)
            .ok_or(StorageError::CostOverflow { op: "charge_write" })?;
        let cell = self.get_mut(payer)?;

        // Check byte cap first.
        if cell.would_exceed_byte_cap(size_bytes) {
            return Err(StorageError::ByteCapExceeded {
                current: cell.bytes_stored,
                max: cell.max_bytes.unwrap_or(u64::MAX),
                attempted: size_bytes,
            });
        }

        cell.charge(cost)?;
        cell.record_bytes_stored(size_bytes);
        Ok(cost)
    }

    /// Process a deletion refund.
    pub fn process_refund(
        &mut self,
        owner: &QuotaId,
        original_cost: u64,
        size_bytes: u64,
    ) -> Result<ComputronRefund, StorageError> {
        let refund_amount = (original_cost as f64 * self.refund_rate) as u64;
        let cell = self.get_mut(owner)?;
        cell.refund(refund_amount);
        cell.record_bytes_freed(size_bytes);
        Ok(ComputronRefund {
            quota_id: *owner,
            amount: refund_amount,
        })
    }

    /// Charge a relay message to a quota cell.
    pub fn charge_relay(
        &mut self,
        payer: &QuotaId,
        size_bytes: u64,
        ttl_blocks: u64,
    ) -> Result<u64, StorageError> {
        // Cost = base message cost + (size * cost_per_byte * ttl), computed
        // with checked arithmetic. `size_bytes` and `ttl_blocks` are both
        // attacker-influenced; an unchecked product overflows and either
        // panics (DoS) or wraps to a near-zero charge (billing bypass).
        let cost = self
            .cost_per_relay_message
            .checked_add(
                size_bytes
                    .checked_mul(self.cost_per_byte)
                    .and_then(|v| v.checked_mul(ttl_blocks))
                    .ok_or(StorageError::CostOverflow { op: "charge_relay" })?,
            )
            .ok_or(StorageError::CostOverflow { op: "charge_relay" })?;
        let cell = self.get_mut(payer)?;
        cell.charge(cost)?;
        Ok(cost)
    }

    /// Top up a quota cell with additional computrons.
    pub fn top_up(&mut self, id: &QuotaId, additional: u64) -> Result<(), StorageError> {
        let cell = self.get_mut(id)?;
        cell.top_up(additional);
        Ok(())
    }

    /// Simulate an epoch passing: charge rental for all stored bytes.
    /// Returns list of quota IDs that are now depleted.
    pub fn tick_epoch(&mut self) -> Vec<QuotaId> {
        let cost_per_byte = self.cost_per_byte;
        let mut depleted = Vec::new();
        for (id, cell) in self.quotas.iter_mut() {
            // Saturating: an overflowed rental cost saturates to `u64::MAX`,
            // which always exceeds `available()`, so the cell is (correctly)
            // marked depleted rather than wrapping to a tiny rental.
            let rental_cost = cell.bytes_stored.saturating_mul(cost_per_byte);
            if cell.available() < rental_cost {
                depleted.push(*id);
            } else {
                cell.total_consumed = cell.total_consumed.saturating_add(rental_cost);
            }
        }
        depleted
    }
}

#[cfg(test)]
mod overflow_tests {
    use super::*;

    /// A write whose `cost_per_byte * size_bytes` overflows `u64` must be
    /// rejected with `CostOverflow` — never panic (DoS) and never wrap to a
    /// near-zero charge (billing bypass). Negative pole: the quota balance is
    /// left untouched by the rejected write.
    #[test]
    fn charge_write_rejects_overflow_without_wrapping() {
        let mut bank = SpaceBank::new(1_000_000, 0, 0.0);
        let id = bank.allocate_quota([7u8; 32], u64::MAX, None);
        // size chosen so cost_per_byte * size overflows u64.
        let huge = u64::MAX / 1_000 + 1;
        let r = bank.charge_write(&id, huge);
        assert!(
            matches!(r, Err(StorageError::CostOverflow { op: "charge_write" })),
            "overflowing write must be rejected, got {r:?}"
        );
        // The rejected write must not have consumed anything (no wrap-charge).
        assert_eq!(bank.get(&id).unwrap().total_consumed, 0);
        assert_eq!(bank.get(&id).unwrap().bytes_stored, 0);
    }

    /// A relay charge whose `size * cost_per_byte * ttl` overflows must be
    /// rejected, not wrapped. A wrapped product would let an attacker buffer
    /// a huge message for a near-zero charge.
    #[test]
    fn charge_relay_rejects_overflow_without_wrapping() {
        let mut bank = SpaceBank::new(1_000_000, 10, 0.0);
        let id = bank.allocate_quota([8u8; 32], u64::MAX, None);
        let r = bank.charge_relay(&id, u64::MAX, u64::MAX);
        assert!(
            matches!(r, Err(StorageError::CostOverflow { op: "charge_relay" })),
            "overflowing relay charge must be rejected, got {r:?}"
        );
        assert_eq!(bank.get(&id).unwrap().total_consumed, 0);
    }

    /// The byte-cap check cannot be bypassed by an overflowing
    /// `bytes_stored + additional`: saturation keeps the sum above any finite
    /// cap, so the oversized write is rejected.
    #[test]
    fn byte_cap_not_bypassed_by_overflow() {
        let mut cell = QuotaCell {
            id: QuotaId(1),
            owner: [0u8; 32],
            total_allocated: u64::MAX,
            total_consumed: 0,
            bytes_stored: 10,
            max_bytes: Some(1_000),
        };
        assert!(
            cell.would_exceed_byte_cap(u64::MAX),
            "an overflowing additional must not wrap below the cap"
        );
        // Sanity: a normal within-cap write is still allowed.
        assert!(!cell.would_exceed_byte_cap(100));
        cell.record_bytes_stored(u64::MAX);
        assert_eq!(
            cell.bytes_stored,
            u64::MAX,
            "record must saturate, not wrap"
        );
    }
}
