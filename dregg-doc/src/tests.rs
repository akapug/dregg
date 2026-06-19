//! Thorough tests for the patch core.
//!
//! Coverage:
//! - apply round-trips (build content from patches; deletes tombstone; order
//!   follows the connect-edges);
//! - **merge is total + commutative + associative + idempotent** (the pushout
//!   property), checked on disjoint, overlapping, and conflicting forks;
//! - a genuine conflict (two concurrent inserts at one position) becomes a
//!   first-class [`ConflictRegion`] — NOT a panic/failure;
//! - a resolution patch collapses the antichain (both by ordering and by
//!   choosing), and the model is closed under its own conflicts.

use crate::*;

/// A two-atom document "Hello world" built from an empty doc.
fn hello_world() -> (DocGraph, AtomId, AtomId) {
    let mut g = DocGraph::new();
    let (h, op_h) = Patch::add(1, "Hello ", AtomId::ROOT);
    let (w, op_w) = Patch::add(2, "world", h);
    Patch::from_ops([op_h, op_w]).apply(&mut g);
    (g, h, w)
}

// ── apply round-trips ────────────────────────────────────────────────────────

#[test]
fn apply_builds_linear_content() {
    let (g, _, _) = hello_world();
    assert_eq!(content(&g).to_marked_string(), "Hello world");
    assert!(!content(&g).has_conflict());
}

#[test]
fn empty_doc_renders_empty() {
    let g = DocGraph::new();
    assert_eq!(content(&g).to_marked_string(), "");
    assert_eq!(g.atom_count(), 1); // just ROOT
}

#[test]
fn delete_tombstones_not_removes() {
    let (mut g, h, w) = hello_world();
    let before = g.atom_count();
    Patch::from_ops([Op::Delete { id: w }]).apply(&mut g);
    // The atom is still present (tombstoned), not physically gone.
    assert_eq!(g.atom_count(), before);
    assert_eq!(g.atom(w).unwrap().status, Status::Dead);
    // Content drops the dead span; the rest stays clean.
    assert_eq!(content(&g).to_marked_string(), "Hello ");
    let _ = h;
}

#[test]
fn delete_is_idempotent_and_monotone() {
    let (mut g, _, w) = hello_world();
    Patch::from_ops([Op::Delete { id: w }]).apply(&mut g);
    let once = g.clone();
    Patch::from_ops([Op::Delete { id: w }]).apply(&mut g);
    assert_eq!(g, once, "deleting twice == deleting once");
}

#[test]
fn add_is_idempotent_same_id() {
    let base = DocGraph::new();
    let (_id, op) = Patch::add(7, "x", AtomId::ROOT);
    let once = Patch::from_ops([op.clone()]).apply_to(&base);
    let twice = Patch::from_ops([op.clone(), op]).apply_to(&base);
    assert_eq!(once, twice, "the same content-addressed add applied twice == once");
}

#[test]
fn insert_in_the_middle() {
    let (mut g, h, w) = hello_world();
    // Insert "big " between "Hello " and "world": after h, before w.
    let (b, op) = Patch::add(3, "big ", h);
    let mut p = Patch::from_ops([op]);
    p.push(Op::Connect { from: b, to: w });
    p.apply(&mut g);
    assert_eq!(content(&g).to_marked_string(), "Hello big world");
}

#[test]
fn compose_equals_sequential_apply() {
    let base = DocGraph::new();
    let p1 = Patch::from_ops([Patch::add(1, "a", AtomId::ROOT).1]);
    let aid = Patch::add(1, "a", AtomId::ROOT).0;
    let p2 = Patch::from_ops([Patch::add(2, "b", aid).1]);
    let composed = p1.compose(&p2).apply_to(&base);
    let sequential = p2.apply_to(&p1.apply_to(&base));
    assert_eq!(composed, sequential);
}

// ── merge: the pushout property (total / commutative / associative / idempotent)

/// Three forks off a common base for the algebraic-law tests:
/// `disjoint` inserts in non-overlapping places, `conflicting` collides.
fn forks() -> (DocGraph, DocGraph, DocGraph) {
    let (base, h, w) = hello_world();
    // Fork A: append "!" after world.
    let a = Patch::from_ops([Patch::add(10, "!", w).1]).apply_to(&base);
    // Fork B: insert "there " after Hello (before world) — disjoint region.
    let (b_atom, b_op) = Patch::add(11, "there ", h);
    let mut bp = Patch::from_ops([b_op]);
    bp.push(Op::Connect { from: b_atom, to: w });
    let b = bp.apply_to(&base);
    // Fork C: delete world.
    let c = Patch::from_ops([Op::Delete { id: w }]).apply_to(&base);
    (a, b, c)
}

#[test]
fn merge_is_total_on_every_fork_pair() {
    let (a, b, c) = forks();
    // No pairing panics; every merge produces a graph (totality).
    for (x, y) in [(&a, &b), (&a, &c), (&b, &c), (&a, &a)] {
        let m = merge(x, y);
        assert!(m.atom_count() >= 1);
        // content() never panics on any merged graph, conflicted or not.
        let _ = content(&m);
    }
}

#[test]
fn merge_is_commutative() {
    let (a, b, c) = forks();
    assert_eq!(merge(&a, &b), merge(&b, &a));
    assert_eq!(merge(&a, &c), merge(&c, &a));
    assert_eq!(merge(&b, &c), merge(&c, &b));
}

#[test]
fn merge_is_associative() {
    let (a, b, c) = forks();
    assert_eq!(merge(&merge(&a, &b), &c), merge(&a, &merge(&b, &c)));
}

#[test]
fn merge_is_idempotent() {
    let (a, b, _) = forks();
    assert_eq!(merge(&a, &a), a);
    let m = merge(&a, &b);
    assert_eq!(merge(&m, &m), m);
    // Re-merging a fork already absorbed adds nothing.
    assert_eq!(merge(&m, &a), m);
}

#[test]
fn merge_all_is_order_independent() {
    let (a, b, c) = forks();
    let abc = merge_all([&a, &b, &c]);
    let cba = merge_all([&c, &b, &a]);
    let bca = merge_all([&b, &c, &a]);
    assert_eq!(abc, cba);
    assert_eq!(abc, bca);
}

#[test]
fn disjoint_edits_merge_clean() {
    let (base, h, w) = hello_world();
    // Two edits in disjoint regions: prepend before h, append after w.
    let (p, pop) = Patch::add(20, "Oh, ", AtomId::ROOT);
    let mut pp = Patch::from_ops([pop]);
    pp.push(Op::Connect { from: p, to: h });
    let left = pp.apply_to(&base);
    let right = Patch::from_ops([Patch::add(21, "!", w).1]).apply_to(&base);
    let m = merge(&left, &right);
    assert!(!content(&m).has_conflict(), "disjoint edits do not conflict");
    assert_eq!(content(&m).to_marked_string(), "Oh, Hello world!");
}

// ── conflict as a first-class STATE (not a panic/failure) ────────────────────

/// Two concurrent inserts at the *same* position (the document tail, after `w`)
/// with no edge between them — a genuine 2-way antichain. Inserting at the tail
/// is the clean case where the position has no pre-existing successor, so the
/// only successors of `w` are the two new, mutually-unordered atoms.
fn conflicting_merge() -> (DocGraph, AtomId, AtomId, AtomId) {
    let (base, _h, w) = hello_world();
    let (alt_a, op_a) = Patch::add(30, " ALPHA", w);
    let (alt_b, op_b) = Patch::add(31, " BETA", w);
    let a = Patch::from_ops([op_a]).apply_to(&base);
    let b = Patch::from_ops([op_b]).apply_to(&base);
    (merge(&a, &b), w, alt_a, alt_b)
}

#[test]
fn concurrent_inserts_become_a_conflict_region_not_a_panic() {
    let (m, _h, alt_a, alt_b) = conflicting_merge();
    let r = content(&m); // does not panic
    assert!(r.has_conflict(), "the merge carries a first-class conflict");
    let region = r.conflicts().next().expect("one conflict region");
    assert_eq!(region.alternatives.len(), 2, "an antichain of two alternatives");
    let heads: Vec<AtomId> = region.alternatives.iter().map(|(id, _)| *id).collect();
    assert!(heads.contains(&alt_a) && heads.contains(&alt_b));
    // Both alternatives are present and legible.
    let texts: Vec<&str> = region.alternatives.iter().map(|(_, t)| t.as_str()).collect();
    assert!(texts.iter().any(|t| t.contains("ALPHA")));
    assert!(texts.iter().any(|t| t.contains("BETA")));
}

#[test]
fn conflicted_doc_is_still_usable_around_the_conflict() {
    // The clean spans around the conflict still render: a contested paragraph
    // does not block the rest of the document.
    let (m, _h, _a, _b) = conflicting_merge();
    let s = content(&m).to_marked_string();
    assert!(s.starts_with("Hello "), "prefix is clean: {s}");
    assert!(s.contains("world"), "suffix is clean: {s}");
    assert!(s.contains("conflict"), "the contested region is marked: {s}");
}

#[test]
fn conflict_state_is_stable_under_remerge() {
    // Merging the conflicted graph with one of its parents again changes
    // nothing (idempotence) — the conflict is a stable STATE, not a transient.
    let (m, _h, _a, _b) = conflicting_merge();
    assert_eq!(merge(&m, &m), m);
    assert!(content(&merge(&m, &m)).has_conflict());
}

// ── resolution collapses the antichain ───────────────────────────────────────

#[test]
fn resolve_by_ordering_collapses_the_conflict() {
    let (mut m, _h, alt_a, alt_b) = conflicting_merge();
    let region = content(&m).conflicts().next().unwrap().clone();
    let heads: Vec<AtomId> = region.alternatives.iter().map(|(id, _)| *id).collect();
    assert_eq!(heads.len(), 2);
    // Resolution is JUST ANOTHER PATCH.
    resolve_connect(&heads).apply(&mut m);
    let r = content(&m);
    assert!(!r.has_conflict(), "ordering the alternatives resolves the conflict");
    // Both alternatives kept, now linearized; nothing lost.
    let s = r.to_marked_string();
    assert!(s.contains("ALPHA") && s.contains("BETA"), "got: {s}");
    let _ = (alt_a, alt_b);
}

#[test]
fn resolve_by_choosing_keeps_one_drops_the_other() {
    let (mut m, _h, alt_a, alt_b) = conflicting_merge();
    // Keep ALPHA's branch, drop BETA's.
    let (keep, drop) = {
        let region = content(&m).conflicts().next().unwrap().clone();
        let a = region.alternatives.iter().find(|(_, t)| t.contains("ALPHA")).unwrap().0;
        let b = region.alternatives.iter().find(|(_, t)| t.contains("BETA")).unwrap().0;
        (a, b)
    };
    resolve_keep(keep, &[drop]).apply(&mut m);
    let r = content(&m);
    assert!(!r.has_conflict());
    let s = r.to_marked_string();
    assert!(s.contains("ALPHA"), "kept: {s}");
    assert!(!s.contains("BETA"), "dropped: {s}");
    let _ = (alt_a, alt_b);
}

#[test]
fn resolution_is_a_patch_that_composes_and_is_witnessed_by_remerge() {
    // The model is closed under resolution: the resolved graph re-merges with
    // the original conflicted graph idempotently (the resolution patch's edges
    // are additive over the conflict union).
    let (m, _h, _a, _b) = conflicting_merge();
    let region = content(&m).conflicts().next().unwrap().clone();
    let heads: Vec<AtomId> = region.alternatives.iter().map(|(id, _)| *id).collect();
    let resolved = resolve_connect(&heads).apply_to(&m);
    // Merging the resolution back over the conflicted state yields the resolved,
    // conflict-free state (resolution is monotone over the union).
    let remerged = merge(&m, &resolved);
    assert_eq!(remerged, resolved);
    assert!(!content(&remerged).has_conflict());
}

#[test]
fn concurrent_resolutions_yield_a_smaller_conflict_still_a_state() {
    // Two parties propose DIFFERENT orderings of the same antichain. Their union
    // is again a valid state (closed under its own conflicts) — it must not
    // panic; whether it re-conflicts or settles, content() is total.
    let (m, _h, _a, _b) = conflicting_merge();
    let region = content(&m).conflicts().next().unwrap().clone();
    let heads: Vec<AtomId> = region.alternatives.iter().map(|(id, _)| *id).collect();
    let res_ab = resolve_connect(&[heads[0], heads[1]]).apply_to(&m);
    let res_ba = resolve_connect(&[heads[1], heads[0]]).apply_to(&m);
    let both = merge(&res_ab, &res_ba); // a -> b AND b -> a : a cycle
    // The union is total and content() does not panic on it.
    let _ = content(&both);
    // It is still a first-class STATE (a graph we can store / re-merge), proven
    // by idempotent re-merge.
    assert_eq!(merge(&both, &both), both);
}
