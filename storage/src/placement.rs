//! Per-grain, owner-anchored bonded-operator placement.
//!
//! Placement is the *discovery* half of a [`durability_deal`](crate::durability_deal):
//! before a grain's shards can be bound to operators, the owner must choose
//! *which* bonded operators hold them. This module makes that choice
//! **deterministically, weighted by bond, and without any global registry** —
//! the properties a DREGGIC placement needs:
//!
//! * **Per-grain, owner-anchored.** The candidate set is supplied by the caller
//!   (the grain's owner), never read from a global directory. There is no shared
//!   "operator table" here to become a consensus bottleneck; the owner curates
//!   the operators it is willing to deal with and this function ranks *those*.
//! * **Deterministic + reproducible.** Selection is a pure function of the
//!   candidate set and the grain id used as the seed. Given the same inputs, any
//!   party derives the same placement — no observer-dependent randomness, no
//!   wall-clock, no iteration-order surprises (ties break on the operator id).
//! * **Owner-verifiable.** Every placement carries the exact rendezvous key it
//!   was ranked by, and [`rendezvous_key`] lets anyone recompute it from the
//!   grain id, the operator id, and the bond — so a counterparty can *check* the
//!   owner's placement rather than trust it.
//! * **Weighted by bond.** Higher-bonded operators are favored (more skin in the
//!   game), but the per-grain hash still spreads placements across the eligible
//!   set so load does not collapse onto the single richest operator.
//!
//! ## The rendezvous construction
//!
//! Mirroring the ADR's `H(seed, grain, operator)` rendezvous idea (highest-random-
//! weight hashing), each eligible operator is scored by
//!
//! ```text
//! key(op) = bond(op) * H(grain_id, op_id)
//! ```
//!
//! where `H` is a domain-separated BLAKE3 hash of the grain id (the seed) and the
//! operator id, reduced to a `u64` — so the hash factor is a per-(grain,operator)
//! pseudo-random draw and the bond factor tilts the draw toward more accountable
//! operators. Operators are ranked by `key` descending and the top `count` are
//! taken. The product is done in `u128` so a full-range `bond * hash` never
//! overflows or saturates. Equal bonds reduce it to plain (unweighted)
//! rendezvous hashing; equal hashes reduce it to a bond ordering; ties on both
//! (astronomically unlikely) break deterministically on the operator id.
//!
//! ## Eligibility
//!
//! An operator is a candidate only if it clears the two bonded-operator
//! invariants read through the same lens as
//! `dregg_storage_templates::bonded_operator`: its bond must meet its floor
//! (`bond >= bond_min`) and it must be in good standing (`dispute_count == 0`).
//! Below-floor or disputed operators are excluded *before* ranking, never
//! silently placed.
//!
//! ## Composing with a durability deal
//!
//! [`select_operator_ids`] returns the chosen ids in rank order, ready to hand to
//! [`durability_deal::create`](crate::durability_deal::create) as its
//! `operators` argument (size the request with
//! [`durability_deal::shard_layout`](crate::durability_deal::shard_layout) so the
//! selected count equals the shard count `n`).

use std::collections::HashSet;

/// Domain separator for the placement rendezvous hash, so a placement digest can
/// never collide with any other BLAKE3 use in the crate.
const PLACEMENT_DOMAIN: &[u8] = b"dregg-storage:placement:rendezvous-v1";

// =============================================================================
// Candidate
// =============================================================================

/// A bonded operator the owner is willing to place a grain with, viewed through
/// the bond/standing lens.
///
/// The fields mirror the reads on
/// `dregg_storage_templates::bonded_operator::BondedOperator`
/// (`operator_pk_hash`, `bond_amount`, `bond_min`, `dispute_count`) so a caller
/// that holds an on-ledger operator cell can populate a candidate directly from
/// it. `operator_id` is the operator's public-key hash — the stable 32-byte
/// identity that both pins the operator and seeds its rendezvous hash.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OperatorCandidate {
    /// The operator's pinned identity (its public-key hash). Also the id that
    /// gets placed and, downstream, bound to a shard in a durability deal.
    pub operator_id: [u8; 32],
    /// The bond the operator has posted (its `BOND_AMOUNT_SLOT`).
    pub bond: u64,
    /// The floor the bond must clear (its `BOND_MIN_SLOT`).
    pub bond_min: u64,
    /// Resolved disputes recorded against the operator (its `DISPUTE_COUNT_SLOT`).
    /// Zero for an operator in good standing.
    pub dispute_count: u64,
}

impl OperatorCandidate {
    /// Construct a candidate from the bond/standing scalars.
    pub fn new(operator_id: [u8; 32], bond: u64, bond_min: u64, dispute_count: u64) -> Self {
        OperatorCandidate {
            operator_id,
            bond,
            bond_min,
            dispute_count,
        }
    }

    /// `true` while the bond still clears its floor.
    pub fn bond_meets_floor(&self) -> bool {
        self.bond >= self.bond_min
    }

    /// `true` while the operator has no recorded disputes.
    pub fn is_in_good_standing(&self) -> bool {
        self.dispute_count == 0
    }

    /// `true` iff the operator may be placed: it clears its bond floor *and* is
    /// in good standing. Below-floor or disputed operators are ineligible.
    pub fn is_eligible(&self) -> bool {
        self.bond_meets_floor() && self.is_in_good_standing()
    }
}

// =============================================================================
// Placement result
// =============================================================================

/// One operator selected to hold a grain, with the evidence needed to verify it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Placement {
    /// The selected operator's id (its public-key hash).
    pub operator_id: [u8; 32],
    /// Rank in the selection, `0` = strongest key. Also the natural shard-index
    /// order when handing these to a durability deal.
    pub rank: usize,
    /// The bond the ranking weighted by (carried so a verifier need not re-look
    /// it up).
    pub bond: u64,
    /// The rendezvous key this operator was ranked by. Recompute it with
    /// [`rendezvous_key`] to verify the placement independently.
    pub weight_key: u128,
}

/// Why a placement could not be produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlacementError {
    /// Fewer distinct eligible operators than the requested count. Placement
    /// never fabricates operators or places the same one twice, so it refuses
    /// rather than under-fill silently.
    InsufficientEligibleOperators {
        /// The number of operators the caller asked to place.
        requested: usize,
        /// The number of distinct, eligible operators actually available.
        eligible: usize,
    },
}

impl std::fmt::Display for PlacementError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlacementError::InsufficientEligibleOperators {
                requested,
                eligible,
            } => write!(
                f,
                "placement needs {requested} distinct eligible operators, only {eligible} available"
            ),
        }
    }
}

impl std::error::Error for PlacementError {}

// =============================================================================
// Rendezvous key
// =============================================================================

/// The domain-separated rendezvous hash `H(grain_id, operator_id)` reduced to a
/// `u64`. The grain id is length-prefixed so a variable-length seed cannot alias
/// into the fixed operator id.
fn rendezvous_hash_u64(grain_id: &[u8], operator_id: &[u8; 32]) -> u64 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(PLACEMENT_DOMAIN);
    hasher.update(&(grain_id.len() as u64).to_be_bytes());
    hasher.update(grain_id);
    hasher.update(operator_id);
    let digest = hasher.finalize();
    let bytes = digest.as_bytes();
    u64::from_be_bytes(bytes[..8].try_into().unwrap())
}

/// The bond-weighted rendezvous key an operator is ranked by for a grain:
/// `bond * H(grain_id, operator_id)`.
///
/// Exposed so an owner's placement is *verifiable*: given the grain id, the
/// operator id, and the operator's bond, anyone recomputes the exact key a
/// [`Placement`] claims. Monotonic in `bond` — raising an operator's bond never
/// lowers its key for a fixed grain.
pub fn rendezvous_key(grain_id: &[u8], operator_id: &[u8; 32], bond: u64) -> u128 {
    (bond as u128) * (rendezvous_hash_u64(grain_id, operator_id) as u128)
}

// =============================================================================
// Selection
// =============================================================================

/// Deterministically select `count` bonded operators to hold the grain seeded by
/// `grain_id`, weighted by bond via [`rendezvous_key`].
///
/// The candidate set is owner-supplied; there is no global registry. Ineligible
/// operators (below their bond floor, or out of good standing) are dropped, and
/// duplicate `operator_id`s are collapsed to the first occurrence so no operator
/// is placed twice. The remaining operators are ranked by rendezvous key
/// (descending, ties broken on the operator id) and the top `count` returned in
/// rank order.
///
/// Returns [`PlacementError::InsufficientEligibleOperators`] if fewer than
/// `count` distinct eligible operators exist — placement refuses rather than
/// under-fill. `count == 0` yields an empty selection.
pub fn select_operators(
    candidates: &[OperatorCandidate],
    grain_id: &[u8],
    count: usize,
) -> Result<Vec<Placement>, PlacementError> {
    // Eligible, distinct candidates — first occurrence of an id wins, so the
    // filter is a pure function of the input order (deterministic for a fixed
    // candidate set).
    let mut seen: HashSet<[u8; 32]> = HashSet::new();
    let mut ranked: Vec<Placement> = Vec::new();
    for c in candidates {
        if !c.is_eligible() {
            continue;
        }
        if !seen.insert(c.operator_id) {
            continue;
        }
        ranked.push(Placement {
            operator_id: c.operator_id,
            rank: 0, // assigned after the sort
            bond: c.bond,
            weight_key: rendezvous_key(grain_id, &c.operator_id, c.bond),
        });
    }

    if ranked.len() < count {
        return Err(PlacementError::InsufficientEligibleOperators {
            requested: count,
            eligible: ranked.len(),
        });
    }

    // Strongest key first; break exact-key ties on the operator id for a total,
    // input-order-independent order.
    ranked.sort_by(|a, b| {
        b.weight_key
            .cmp(&a.weight_key)
            .then_with(|| b.operator_id.cmp(&a.operator_id))
    });

    ranked.truncate(count);
    for (i, p) in ranked.iter_mut().enumerate() {
        p.rank = i;
    }
    Ok(ranked)
}

/// Convenience wrapper over [`select_operators`] returning just the selected
/// operator ids in rank order — the shape
/// [`durability_deal::create`](crate::durability_deal::create) wants for its
/// `operators` argument.
pub fn select_operator_ids(
    candidates: &[OperatorCandidate],
    grain_id: &[u8],
    count: usize,
) -> Result<Vec<[u8; 32]>, PlacementError> {
    Ok(select_operators(candidates, grain_id, count)?
        .into_iter()
        .map(|p| p.operator_id)
        .collect())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// A pool of `n` eligible operators, id `[i; 32]`, bond `base + i*step`,
    /// floor `base`, good standing.
    fn pool(n: u8, base: u64, step: u64) -> Vec<OperatorCandidate> {
        (0..n)
            .map(|i| OperatorCandidate::new([i; 32], base + i as u64 * step, base, 0))
            .collect()
    }

    #[test]
    fn selection_is_deterministic_for_a_fixed_seed() {
        let cands = pool(8, 100, 50);
        let grain = b"grain-alpha";
        let a = select_operators(&cands, grain, 3).unwrap();
        let b = select_operators(&cands, grain, 3).unwrap();
        assert_eq!(a, b, "same candidates + same grain must select identically");

        // Input order must not change the outcome (ranking is by key, ties by id).
        let mut shuffled = cands.clone();
        shuffled.reverse();
        let c = select_operators(&shuffled, grain, 3).unwrap();
        assert_eq!(
            a, c,
            "selection must be independent of candidate input order"
        );
    }

    #[test]
    fn different_grains_generally_place_differently() {
        // Same operators, different seeds -> the per-grain hash spreads load, so
        // the top pick is not always the same operator.
        let cands = pool(12, 100, 0); // equal bonds: pure rendezvous, hash decides
        let mut tops = std::collections::HashSet::new();
        for g in 0u64..64 {
            let sel = select_operators(&cands, &g.to_le_bytes(), 1).unwrap();
            tops.insert(sel[0].operator_id);
        }
        assert!(
            tops.len() > 1,
            "equal-bond placement must spread the top pick across grains, got {}",
            tops.len()
        );
    }

    #[test]
    fn exactly_count_selected_when_enough_eligible() {
        let cands = pool(8, 100, 10);
        let sel = select_operators(&cands, b"g", 5).unwrap();
        assert_eq!(sel.len(), 5, "must select exactly the requested count");
        // Ranks are 0..count and every selected id is distinct.
        let ids: std::collections::HashSet<_> = sel.iter().map(|p| p.operator_id).collect();
        assert_eq!(ids.len(), 5, "selected operators must be distinct");
        for (i, p) in sel.iter().enumerate() {
            assert_eq!(p.rank, i, "ranks must be a dense 0..count sequence");
        }
    }

    #[test]
    fn zero_count_selects_nothing() {
        let cands = pool(4, 100, 10);
        assert_eq!(select_operators(&cands, b"g", 0).unwrap(), vec![]);
    }

    #[test]
    fn keys_are_descending_across_ranks() {
        let cands = pool(10, 100, 25);
        let sel = select_operators(&cands, b"grain-order", 6).unwrap();
        for w in sel.windows(2) {
            assert!(
                w[0].weight_key >= w[1].weight_key,
                "rank {} key {} must be >= rank {} key {}",
                w[0].rank,
                w[0].weight_key,
                w[1].rank,
                w[1].weight_key
            );
        }
    }

    #[test]
    fn higher_bond_operators_are_favored() {
        // One heavily-bonded operator vs one barely-bonded one, both eligible.
        // Across many grains the heavy operator wins the single slot far more
        // often (bond tilts the per-grain hash draw).
        let heavy = OperatorCandidate::new([1; 32], 1_000_000, 100, 0);
        let light = OperatorCandidate::new([2; 32], 100, 100, 0);
        let cands = vec![heavy.clone(), light.clone()];

        let trials = 2_000u64;
        let mut heavy_wins = 0u64;
        for g in 0..trials {
            let sel = select_operators(&cands, &g.to_le_bytes(), 1).unwrap();
            if sel[0].operator_id == heavy.operator_id {
                heavy_wins += 1;
            }
        }
        assert!(
            heavy_wins > light_share_ceiling(trials),
            "heavy-bond operator won only {heavy_wins}/{trials}; expected a strong majority"
        );
    }

    /// The heavy operator should win far more than half; require > 80%.
    fn light_share_ceiling(trials: u64) -> u64 {
        (trials * 8) / 10
    }

    #[test]
    fn rendezvous_key_is_monotonic_in_bond() {
        let id = [7u8; 32];
        let grain = b"mono";
        let mut prev = rendezvous_key(grain, &id, 0);
        for bond in [1u64, 2, 10, 1000, u32::MAX as u64, u64::MAX / 2] {
            let k = rendezvous_key(grain, &id, bond);
            assert!(
                k >= prev,
                "raising bond to {bond} must not lower the key ({k} < {prev})"
            );
            prev = k;
        }
    }

    #[test]
    fn below_floor_operators_are_excluded() {
        let good_a = OperatorCandidate::new([1; 32], 500, 100, 0);
        let below = OperatorCandidate::new([2; 32], 50, 100, 0); // 50 < 100 floor
        let good_b = OperatorCandidate::new([3; 32], 300, 100, 0);
        assert!(!below.is_eligible());
        let cands = vec![good_a.clone(), below.clone(), good_b.clone()];

        // Request all *eligible* (2): the below-floor operator must never appear.
        let sel = select_operators(&cands, b"g", 2).unwrap();
        assert_eq!(sel.len(), 2);
        assert!(
            sel.iter().all(|p| p.operator_id != below.operator_id),
            "a below-floor operator must not be placed"
        );

        // Only 2 eligible: asking for 3 refuses rather than dip below the floor.
        assert_eq!(
            select_operators(&cands, b"g", 3).unwrap_err(),
            PlacementError::InsufficientEligibleOperators {
                requested: 3,
                eligible: 2,
            }
        );
    }

    #[test]
    fn disputed_operators_are_excluded() {
        let good = OperatorCandidate::new([1; 32], 500, 100, 0);
        let disputed = OperatorCandidate::new([2; 32], 5_000, 100, 1); // huge bond, but slashed
        assert!(!disputed.is_eligible());
        let cands = vec![good.clone(), disputed.clone()];

        // Even though the disputed operator vastly out-bonds the good one, it is
        // excluded — standing gates before bond weighting.
        let sel = select_operators(&cands, b"g", 1).unwrap();
        assert_eq!(sel.len(), 1);
        assert_eq!(sel[0].operator_id, good.operator_id);

        assert_eq!(
            select_operators(&cands, b"g", 2).unwrap_err(),
            PlacementError::InsufficientEligibleOperators {
                requested: 2,
                eligible: 1,
            }
        );
    }

    #[test]
    fn duplicate_ids_are_collapsed_not_placed_twice() {
        // The same operator listed twice must never hold two slots.
        let a = OperatorCandidate::new([1; 32], 500, 100, 0);
        let a_again = OperatorCandidate::new([1; 32], 900, 100, 0);
        let b = OperatorCandidate::new([2; 32], 400, 100, 0);
        let cands = vec![a.clone(), a_again, b.clone()];

        let sel = select_operators(&cands, b"g", 2).unwrap();
        assert_eq!(sel.len(), 2);
        let ids: std::collections::HashSet<_> = sel.iter().map(|p| p.operator_id).collect();
        assert_eq!(ids.len(), 2, "each operator placed at most once");

        // Only 2 distinct ids: a third slot is impossible.
        assert_eq!(
            select_operators(&cands, b"g", 3).unwrap_err(),
            PlacementError::InsufficientEligibleOperators {
                requested: 3,
                eligible: 2,
            }
        );
    }

    #[test]
    fn placements_are_owner_verifiable() {
        // A counterparty recomputes each placement's key from public inputs.
        let cands = pool(9, 200, 30);
        let grain = b"verify-me";
        let sel = select_operators(&cands, grain, 4).unwrap();
        for p in &sel {
            assert_eq!(
                p.weight_key,
                rendezvous_key(grain, &p.operator_id, p.bond),
                "placement key must be independently reproducible"
            );
        }
    }

    #[test]
    fn ids_wrapper_matches_full_selection() {
        let cands = pool(7, 100, 20);
        let grain = b"wrap";
        let full = select_operators(&cands, grain, 4).unwrap();
        let ids = select_operator_ids(&cands, grain, 4).unwrap();
        let expected: Vec<[u8; 32]> = full.iter().map(|p| p.operator_id).collect();
        assert_eq!(ids, expected);
    }

    #[test]
    fn selection_feeds_a_durability_deal() {
        // End-to-end: size the request to the shard count, select that many
        // operators, and bind them into a k-of-n deal.
        use crate::durability_deal::{self, shard_layout};

        let data = b"a grain whose shards get placed with bonded operators";
        let (k, n) = shard_layout(data.len(), 16, 2);
        assert!(n >= 2);

        // A pool with more eligible operators than shards.
        let cands = pool((n as u8) + 3, 100, 10);
        let grain_id = blake3::hash(data);
        let operators = select_operator_ids(&cands, grain_id.as_bytes(), n).unwrap();
        assert_eq!(operators.len(), n);

        let (deal, chunks) = durability_deal::create(data, 16, 2, &operators).unwrap();
        assert_eq!((deal.k, deal.n), (k, n));
        assert_eq!(chunks.len(), n);
        // Each shard is bound to one of the selected operators.
        for p in &deal.placements {
            assert!(operators.contains(&p.operator));
        }
        // And the deal still reconstructs from the data shards alone.
        let data_only: Vec<_> = chunks.into_iter().filter(|c| !c.is_parity).collect();
        assert_eq!(deal.reconstruct(&data_only).unwrap(), data);
    }
}
