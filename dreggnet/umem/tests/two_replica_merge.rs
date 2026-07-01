//! The **two-replica merge driver** end-to-end (the #3 re-dregg move,
//! `docs/REGISTRIES-AS-UMEM.md §4`): two replicas of a umem registry add records
//! offline, exchange leaf-deltas, and reconcile — confluent writes merge FREE
//! (no consensus, no settle), a conserved-quantity conflict is REFUSED-to-free-merge
//! (escalate to settle at the boundary), and every free merge leaves a re-witnessable
//! [`MergeReceipt`].
//!
//! The teeth:
//! 1. confluent merges are free + deterministic (commutative / idempotent / order-
//!    independent) — two replicas converge to one record-set with no chain op;
//! 2. a conserved-quantity conflict settles at the boundary;
//! 3. the merge receipt re-witnesses (recompute the join, check the commitment).

use dreggnet_umem::{MergeRuntime, MergeState, Record, RegistryMergeError, UmemRegistry};
use serde::{Deserialize, Serialize};

/// A domain binding — the `dregg-domains` registry record shape (`domain -> site`),
/// keyed by domain. Grow-only adds of new domains are I-confluent.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct DomainBinding {
    domain: String,
    site: String,
    owner: String,
}
impl Record for DomainBinding {
    fn store_key(&self) -> String {
        self.domain.clone()
    }
}
fn bind(domain: &str, site: &str, owner: &str) -> DomainBinding {
    DomainBinding {
        domain: domain.to_string(),
        site: site.to_string(),
        owner: owner.to_string(),
    }
}

fn temp(tag: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    let n = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    p.push(format!("dreggnet-umem-merge-{tag}-{n}.snap"));
    p
}
fn cleanup(path: &std::path::Path) {
    std::fs::remove_file(path).ok();
    let mut hist = path.as_os_str().to_os_string();
    hist.push(".history");
    std::fs::remove_dir_all(std::path::PathBuf::from(hist)).ok();
}

/// TOOTH 1 — two operators each add disjoint domains OFFLINE, then reconcile: the
/// merge is FREE (no settle), each replica gains the other's records, and after each
/// merges the other the two **converge** to the same record-set, with a verifiable
/// merge receipt and no chain op.
#[test]
fn confluent_merge_is_free_and_converges() {
    let pa = temp("conv-a");
    let pb = temp("conv-b");
    let a = UmemRegistry::<DomainBinding>::open(&pa).unwrap();
    let b = UmemRegistry::<DomainBinding>::open(&pb).unwrap();

    // Offline, no coordination: operator A registers two domains; operator B two more.
    a.append(&bind("alice.example", "alice-blog", "alice"))
        .unwrap();
    a.append(&bind("shop.example", "alice-shop", "alice"))
        .unwrap();
    b.append(&bind("bob.example", "bob-blog", "bob")).unwrap();
    b.append(&bind("forum.example", "bob-forum", "bob"))
        .unwrap();

    // Capture the input GrowSet views for re-witnessing the merge later.
    let cell = "domains";
    let gs_a = a.grow_set(cell);
    let gs_b = b.grow_set(cell);

    // A reconciles B into itself — a FREE local merge (the gate found it I-confluent).
    let mut rt_a = MergeRuntime::new("UmemRegistry", "operator-a");
    let out_a = a
        .merge(&b, cell, &mut rt_a)
        .expect("disjoint grow-only adds must merge free");
    assert_eq!(
        out_a.added,
        vec!["bob.example".to_string(), "forum.example".to_string()],
        "A gained exactly B's two domains"
    );
    assert_eq!(a.len(), 4, "A now holds the union");

    // TOOTH 3 — the receipt re-witnesses: a third party holding the two input views
    // recomputes the join and checks the merged commitment. No chain op, no consensus.
    out_a
        .receipt
        .rewitness(&gs_a, &gs_b)
        .expect("the merge receipt must re-witness over the input views");

    // B independently reconciles A into itself — also FREE.
    let mut rt_b = MergeRuntime::new("UmemRegistry", "operator-b");
    let out_b = b
        .merge(&a, cell, &mut rt_b)
        .expect("free the other way too");
    // (A already grew to the union, so B gains all four-minus-its-two.)
    assert_eq!(b.len(), 4, "B now holds the union too");

    // CONVERGENCE — the two replicas reached the SAME record-set, regardless of who
    // merged whom (commutative). Their content-addressed GrowSet commitments are equal.
    assert_eq!(
        a.grow_set(cell).commitment(),
        b.grow_set(cell).commitment(),
        "the two replicas converged to one confluent state"
    );
    // The merged commitment in A's receipt equals B's converged view (order-independent).
    assert_eq!(out_a.receipt.merged, a.grow_set(cell).commitment());
    let _ = out_b;

    cleanup(&pa);
    cleanup(&pb);
}

/// TOOTH 1 (determinism) — merge order does not matter: `join(A,B)` and `join(B,A)`
/// commit to the SAME merged state, and re-merging is idempotent (a no-op).
#[test]
fn merge_is_commutative_and_idempotent() {
    let pa = temp("ci-a");
    let pb = temp("ci-b");
    let a = UmemRegistry::<DomainBinding>::open(&pa).unwrap();
    let b = UmemRegistry::<DomainBinding>::open(&pb).unwrap();
    a.append(&bind("a.example", "s1", "alice")).unwrap();
    b.append(&bind("b.example", "s2", "bob")).unwrap();

    let cell = "domains";
    let gs_a = a.grow_set(cell);
    let gs_b = b.grow_set(cell);

    // Commutativity at the CvRDT level: both join orders commit identically.
    use dreggnet_umem::GrowSet;
    let ab = join_commit(&gs_a, &gs_b);
    let ba = join_commit(&gs_b, &gs_a);
    assert_eq!(
        ab, ba,
        "join is commutative — order-independent merged commitment"
    );

    // Idempotence end-to-end: A merges B, then merges B AGAIN — the second adds nothing.
    let mut rt = MergeRuntime::new("UmemRegistry", "op");
    let first = a.merge(&b, cell, &mut rt).unwrap();
    assert_eq!(first.added, vec!["b.example".to_string()]);
    let commit_after_first = a.grow_set(cell).commitment();
    let second = a.merge(&b, cell, &mut rt).unwrap();
    assert!(
        second.added.is_empty(),
        "re-merge gains nothing (idempotent)"
    );
    assert_eq!(
        a.grow_set(cell).commitment(),
        commit_after_first,
        "the state is unchanged by the idempotent re-merge"
    );

    cleanup(&pa);
    cleanup(&pb);

    fn join_commit(x: &GrowSet, y: &GrowSet) -> [u8; 32] {
        use dreggnet_umem::MergeState as _;
        x.join(y).commitment()
    }
}

/// TOOTH 2 — a conserved quantity does NOT free-merge. Two replicas write the SAME
/// logical key (a domain) with DIFFERENT bindings — a single-writer register conflict.
/// The gate refuses (escalate to settle at the boundary); the replica is left
/// unchanged and the caller must route the write through a settling turn.
#[test]
fn conserved_conflict_settles_at_the_boundary() {
    let pa = temp("settle-a");
    let pb = temp("settle-b");
    let a = UmemRegistry::<DomainBinding>::open(&pa).unwrap();
    let b = UmemRegistry::<DomainBinding>::open(&pb).unwrap();

    // Both claim the same domain offline, bound to different sites/owners.
    a.append(&bind("contested.example", "alice-site", "alice"))
        .unwrap();
    b.append(&bind("contested.example", "bob-site", "bob"))
        .unwrap();
    // ... plus a disjoint grow-only add each, to show ONLY the conflict forces settle.
    a.append(&bind("a-only.example", "as", "alice")).unwrap();
    b.append(&bind("b-only.example", "bs", "bob")).unwrap();

    let cell = "domains";
    let mut rt = MergeRuntime::new("UmemRegistry", "op");
    match a.merge(&b, cell, &mut rt) {
        Err(RegistryMergeError::Settle { conflicts, .. }) => {
            assert_eq!(
                conflicts,
                vec!["contested.example".to_string()],
                "exactly the divergent key forces the settle"
            );
        }
        other => panic!("a conserved-quantity conflict must settle, got {other:?}"),
    }

    // The refused merge left A unchanged — it did NOT silently absorb B's records.
    assert_eq!(a.len(), 2);
    assert_eq!(
        a.get("contested.example"),
        Some(bind("contested.example", "alice-site", "alice"))
    );
    assert!(
        !a.contains("b-only.example"),
        "no record crossed the boundary on a settle"
    );

    cleanup(&pa);
    cleanup(&pb);
}

/// TOOTH 3 (tamper) — a forged merged commitment fails re-witness. The receipt's
/// `merged` is the genuine join of exactly the two named inputs; flipping it is caught.
#[test]
fn tampered_receipt_fails_rewitness() {
    let pa = temp("tamper-a");
    let pb = temp("tamper-b");
    let a = UmemRegistry::<DomainBinding>::open(&pa).unwrap();
    let b = UmemRegistry::<DomainBinding>::open(&pb).unwrap();
    a.append(&bind("a.example", "s1", "alice")).unwrap();
    b.append(&bind("b.example", "s2", "bob")).unwrap();

    let cell = "domains";
    let gs_a = a.grow_set(cell);
    let gs_b = b.grow_set(cell);
    let mut rt = MergeRuntime::new("UmemRegistry", "op");
    let out = a.merge(&b, cell, &mut rt).unwrap();

    // A genuine receipt re-witnesses.
    out.receipt.rewitness(&gs_a, &gs_b).unwrap();
    // A forged merged commitment does not.
    let mut forged = out.receipt.clone();
    forged.merged[0] ^= 0xff;
    assert!(
        forged.rewitness(&gs_a, &gs_b).is_err(),
        "a tampered merged commitment must fail the re-witness"
    );

    cleanup(&pa);
    cleanup(&pb);
}
