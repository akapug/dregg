//! The **two-replica merge/write driver** over umem registries — the #3 re-dregg
//! move (`docs/REGISTRIES-AS-UMEM.md §4`, `THE-BIGGER-DREGGNET.md §4 #3`): the
//! I-confluent offchain-coordination path, finally with a registry-shaped cell to
//! live in.
//!
//! ## Why this was structurally blocked (and now is not)
//!
//! The architecture critique's deep finding: the offchain-coordination thesis was
//! blocked *because no resource was a umem cell* — the I-confluent write/merge path
//! had **nowhere to live**. [`UmemRegistry`](crate::UmemRegistry) fixed that: a
//! registry IS a umem cell whose heap leaf-set is a grow-only set. This module is
//! the merge runtime built **on that object**: it adapts a registry's live records
//! into a [`dregg_merge::GrowSet`] (a record = a content-addressed asserted delta,
//! `join = ∪`), runs the confluence gate [`dregg_merge::classify_merge`], and — on a
//! free merge — folds the other replica's records in and emits a re-witnessable
//! [`MergeReceipt`].
//!
//! ## The dichotomy the gate enforces
//!
//! - **Confluent writes merge FREE.** Two operators each `append` records to their
//!   own registry replica *offline, with no coordination* (new sites, new domain
//!   bindings — the grow-only `Assert` shape). Their record-sets merge by set union:
//!   commutative, associative, idempotent, **order-independent** — converging to one
//!   state with no consensus and no chain op. This is the offchain-coordination
//!   payoff (`VISION` Bet #2): the heap leaf-set is a CvRDT, so the merge is a
//!   *local* operation neither side has to be told is legal.
//! - **A conserved quantity does NOT free-merge.** When the two replicas diverge on
//!   the *same* logical key (a single-writer register written with two different
//!   values — the "billing balance leaf" / bounded-resource shape), reconciling it
//!   requires **retracting the loser**, a non-monotone op. The gate refuses the free
//!   merge ([`RegistryMergeError::Settle`]) and the write must go through a settling
//!   turn at the boundary — the one place revocation is non-monotone
//!   (`SettlementSoundness.lean`).
//!
//! ## The named in-circuit seam — `MergeRefinesConfluence`
//!
//! The merge here is **executor-grade**: a re-witnessing peer who holds the two input
//! GrowSet views can [`MergeReceipt::rewitness`] the merge — recompute the join and
//! check the commitment — with no chain op. That a *light client* (not a re-executing
//! peer) sees the merge preserved the invariant, i.e. that this driver's `join` IS the
//! `⊔` the Lean gate (`Dregg2.Confluence`) reasons about, witnessed **in-circuit**, is
//! the **`MergeRefinesConfluence` weld** — the swarm's VK-epoch, the same shape the
//! registry's committed-boundary witness already names. The off-chain half is closed
//! here; the in-circuit tooth is its named shadow. This module adds no Lean theorem.

use dregg_merge::{
    Delta, Escalation, GrowSet, MergeReceipt, MergeRuntime, MergeVerdict, classify_merge,
};

use crate::{Record, UmemError, UmemRegistry};

/// The human label the gate reports for a registry merge escalation.
const KIND_NAME: &str = "UmemRegistry";

/// The fixed delta author for registry records. A record's identity is its *content*
/// (the registry id + the record's canonical bytes), NOT which replica holds it — so
/// two replicas that independently `append` the byte-identical record produce the
/// **same** content-addressed delta, and the union deduplicates them (idempotence).
/// Which replica contributed a delta is tracked by the [`MergeReceipt`]'s provenance,
/// not by the delta id.
const REGISTRY_AUTHOR: &str = "umem-registry";

/// The canonical `Assert` delta for one registry record: an assertion on `cell`
/// carrying the record's canonical JSON bytes (the same bytes the umem heap lays in),
/// authored by the fixed registry tag.
fn record_delta<R: Record>(cell: &str, record: &R) -> Result<Delta, serde_json::Error> {
    let json = serde_json::to_vec(record)?;
    Ok(Delta::assert(cell, json, REGISTRY_AUTHOR))
}

/// The outcome of a successful **free** registry merge: the re-witnessable receipt and
/// the store_keys folded in from the other replica (the records this replica gained).
#[derive(Clone, Debug)]
pub struct RegistryMerge {
    /// The verifiable, re-witnessable receipt of the merge (the merged GrowSet
    /// commitment + per-delta provenance + the prev-hash chain). A third party who
    /// holds the two input [`GrowSet`] views can [`MergeReceipt::rewitness`] it — no
    /// chain op, no consensus.
    pub receipt: MergeReceipt,
    /// The store_keys this replica gained from the other (sorted). Empty on an
    /// idempotent re-merge (everything already present).
    pub added: Vec<String>,
}

/// Why a registry merge could not proceed offchain coordination-free.
#[derive(Debug)]
pub enum RegistryMergeError {
    /// The confluence gate **refused** the free merge: a conserved quantity / a
    /// non-monotone reconciliation participates, so the write must **settle at the
    /// boundary** (a conserving turn that re-checks the invariant against the
    /// certified prefix). `conflicts` names the divergent store_keys (a single-writer
    /// register written with two different values), empty if the gate refused for a
    /// structural reason.
    Settle {
        /// The gate's escalation reason (`NonMonotoneOp` for a divergent overwrite).
        escalation: Escalation,
        /// The store_keys the two replicas diverged on.
        conflicts: Vec<String>,
    },
    /// Folding the merged records into this replica's umem cell failed (a durable
    /// store fault); the merge did not complete.
    Umem(UmemError),
}

impl std::fmt::Display for RegistryMergeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegistryMergeError::Settle {
                escalation,
                conflicts,
            } => write!(
                f,
                "registry merge must settle at the boundary ({escalation}); \
                 divergent keys: {conflicts:?}"
            ),
            RegistryMergeError::Umem(e) => write!(f, "registry merge store fault: {e}"),
        }
    }
}

impl std::error::Error for RegistryMergeError {}

impl<R: Record> UmemRegistry<R> {
    /// A content-addressed [`GrowSet`] view of this replica's live records on logical
    /// cell `cell`: each live record becomes one `Assert` delta. This is the CvRDT
    /// face of the registry's heap leaf-set — the object the merge runtime joins.
    ///
    /// A third party can rebuild this view (from the registry's records) and use it to
    /// [`MergeReceipt::rewitness`] a merge.
    pub fn grow_set(&self, cell: &str) -> GrowSet {
        let mut gs = GrowSet::new(cell);
        for rec in self.all() {
            if let Ok(d) = record_delta(cell, &rec) {
                gs.apply(d);
            }
        }
        gs
    }

    /// The store_keys both replicas hold but with **different** record values — a
    /// single-writer-register conflict (last-write-wins needs a finalized order, so it
    /// is a conserved quantity that must settle, not free-merge).
    fn divergent_keys(&self, other: &UmemRegistry<R>) -> Vec<String> {
        let mut out = Vec::new();
        for key in self.keys() {
            if let (Some(a), Some(b)) = (self.get(&key), other.get(&key)) {
                let ja = serde_json::to_vec(&a).ok();
                let jb = serde_json::to_vec(&b).ok();
                if ja != jb {
                    out.push(key);
                }
            }
        }
        out
    }

    /// The gate's verdict on merging this replica with `other` on cell `cell`, WITHOUT
    /// performing it (a dry-run: would this merge be free, or must it settle?).
    pub fn would_merge(&self, other: &UmemRegistry<R>, cell: &str) -> MergeVerdict {
        let conflicts = self.divergent_keys(other);
        let gs_a = self.gated_grow_set(other, cell, &conflicts);
        let gs_b = other.grow_set(cell);
        classify_merge(&gs_a, &gs_b, KIND_NAME)
    }

    /// This replica's GrowSet view, with the conflict-forced retraction injected when
    /// the replicas diverge on a key — so the **gate** (not a hand-rolled branch)
    /// renders the settle verdict. Reconciling a divergent overwrite requires
    /// retracting the loser; that retraction is the non-monotone op
    /// (`negation_retracts`) the gate refuses a free merge over.
    fn gated_grow_set(
        &self,
        _other: &UmemRegistry<R>,
        cell: &str,
        conflicts: &[String],
    ) -> GrowSet {
        let mut gs = self.grow_set(cell);
        for key in conflicts {
            if let Some(rec) = self.get(key) {
                if let Ok(d) = record_delta(cell, &rec) {
                    // retract this replica's binding for the conflicted key — the
                    // op the reconciliation would require, which flips the merge
                    // FinalizedDependent and forces a settle.
                    gs.apply(Delta::retract(cell, d.id(), REGISTRY_AUTHOR));
                }
            }
        }
        gs
    }

    /// **Merge** another replica of this registry into this one — *offchain,
    /// coordination-free*.
    ///
    /// On [`Ok`] the confluence gate found the record-set merge I-confluent: the other
    /// replica's records are folded in by set union (commutative, idempotent,
    /// order-independent — converging with **no consensus, no chain op**), and a
    /// chained, re-witnessable [`MergeReceipt`] is returned. The two replicas, each
    /// merging the other, converge to the same record-set.
    ///
    /// On [`Err`]`(`[`RegistryMergeError::Settle`]`)` the gate refused: the replicas
    /// diverged on a key (a conserved single-writer register) or a non-monotone op
    /// participates, so the write must settle at the boundary (a turn). This replica
    /// is left **unchanged** on a settle.
    ///
    /// `cell` is the shared logical cell id (a fork and its parent, or two operators'
    /// replicas of the same registry, share one cell id). `runtime` carries the
    /// coordination chain head the receipt is chained onto.
    pub fn merge(
        &self,
        other: &UmemRegistry<R>,
        cell: &str,
        runtime: &mut MergeRuntime,
    ) -> Result<RegistryMerge, RegistryMergeError> {
        let gs_a = self.grow_set(cell);
        let gs_b = other.grow_set(cell);

        // Conserved-quantity / divergent-overwrite refusal — routed THROUGH the gate.
        let conflicts = self.divergent_keys(other);
        if !conflicts.is_empty() {
            let gated = self.gated_grow_set(other, cell, &conflicts);
            let escalation = match classify_merge(&gated, &gs_b, KIND_NAME) {
                MergeVerdict::Settle(e) => e,
                // a retraction must force a settle; defensively name the reason.
                MergeVerdict::Free => Escalation::NonMonotoneOp,
            };
            return Err(RegistryMergeError::Settle {
                escalation,
                conflicts,
            });
        }

        // No conflict — the gate finds the record-set merge I-confluent (free).
        let outcome = match runtime.merge(&gs_a, &gs_b) {
            Ok(o) => o,
            Err(escalation) => {
                return Err(RegistryMergeError::Settle {
                    escalation,
                    conflicts: Vec::new(),
                });
            }
        };

        // Fold the other replica's records this one lacks (the union grows). A shared
        // key with an identical value is already present — the union deduplicated it.
        let mut added = Vec::new();
        for rec in other.all() {
            let key = rec.store_key();
            if !self.contains(&key) {
                self.append(&rec).map_err(RegistryMergeError::Umem)?;
                added.push(key);
            }
        }
        added.sort();
        Ok(RegistryMerge {
            receipt: outcome.receipt,
            added,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_merge::{BoundedCounter, MergeState};
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
    struct Site {
        name: String,
        owner: String,
    }
    impl Record for Site {
        fn store_key(&self) -> String {
            self.name.clone()
        }
    }
    fn site(name: &str, owner: &str) -> Site {
        Site {
            name: name.to_string(),
            owner: owner.to_string(),
        }
    }
    fn temp(tag: &str) -> std::path::PathBuf {
        let mut p = std::env::temp_dir();
        let n = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        p.push(format!("dreggnet-umem-merge-unit-{tag}-{n}.snap"));
        p
    }

    /// The bounded-resource shape the gate refuses outright (`NonIConfluentKind`): the
    /// literal "billing balance leaf" — two locally-valid decrements merge to an
    /// overdraft, so a conserved quantity is never free-merged.
    #[test]
    fn conserved_balance_is_refused_by_the_gate() {
        let a = BoundedCounter::new("acct");
        let b = BoundedCounter::new("acct");
        match classify_merge(&a, &b, "BoundedCounter") {
            MergeVerdict::Settle(Escalation::NonIConfluentKind { .. }) => {}
            v => panic!("a conserved balance must settle, got {v:?}"),
        }
        // a grow-only registry record-set, by contrast, is I-confluent.
        assert!(GrowSet::is_iconfluent_kind());
    }

    /// A divergent overwrite (the same key with two values) is a conserved
    /// single-writer register and the gate refuses the free merge.
    #[test]
    fn divergent_key_settles() {
        let pa = temp("div-a");
        let pb = temp("div-b");
        let a = UmemRegistry::<Site>::open(&pa).unwrap();
        let b = UmemRegistry::<Site>::open(&pb).unwrap();
        a.append(&site("blog", "alice")).unwrap();
        b.append(&site("blog", "mallory")).unwrap(); // same key, different owner
        let mut rt = MergeRuntime::new("UmemRegistry", "a");
        match a.merge(&b, "registry", &mut rt) {
            Err(RegistryMergeError::Settle {
                escalation,
                conflicts,
            }) => {
                assert_eq!(escalation, Escalation::NonMonotoneOp);
                assert_eq!(conflicts, vec!["blog".to_string()]);
            }
            other => panic!("expected a settle, got {other:?}"),
        }
        // the refused merge left `a` unchanged.
        assert_eq!(a.get("blog"), Some(site("blog", "alice")));
        std::fs::remove_file(&pa).ok();
        std::fs::remove_file(&pb).ok();
    }
}
