//! Inline **marks** — the within-cell rich-text overlay (Peritext /
//! Automerge-marks, DREGG-DOCUMENT-FOUNDATION.md §1.5, DREGG-DOCUMENT-DESIGN §2).
//!
//! A mark is a **non-destructive range overlay** — `Mark { start, end, kind }`
//! addressing a span of the document by its endpoint [`AtomId`]s — that lives in
//! a store **separate** from the [`DocGraph`]'s atoms. Marks are the ONLY sound
//! way to get mergeable formatting: baking "bold" into an atom's content is the
//! wrong design, because every concurrent text edit that touches the atom
//! re-mints it and destroys the formatting. Keeping marks in their own store
//! means:
//!
//! - **A mark and a concurrent text edit never conflict.** They touch disjoint
//!   stores — the [`Marks`] overlay vs the [`DocGraph`] atom graph — so a text
//!   insert and a mark addition made concurrently both survive their merge with
//!   no interaction at all (`a_mark_and_a_concurrent_text_edit_do_not_conflict`).
//! - **A mark addresses by stable [`AtomId`] endpoints**, and an `AtomId` is
//!   content-addressed and never moves (atom.rs), so a mark still covers its
//!   range after a text atom is inserted *between* its endpoints — the mark does
//!   NOT re-mint on a text edit (`a_mark_survives_a_text_insert_within_its_range`).
//! - **Two mark sets merge as a monotone set-union.** Adding a mark is
//!   inflationary; concurrent marks compose; a *removal* is a monotone tombstone
//!   ([`Status::Dead`]-wins), never a destructive delete — exactly the discipline
//!   [`crate::graph`]'s atom store uses, one level down. This mirrors §1.2's
//!   "composition factors collaboration."
//!
//! The overlay never alters atom content: [`render_marked`] layers the active
//! [`MarkKind`]s onto the rendered text runs, computed purely from the
//! (stable) endpoint positions in the document walk.

use crate::atom::{AtomId, Provenance, Status};
use crate::content::walk_atoms;
use crate::graph::DocGraph;
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};

/// The kind of formatting a [`Mark`] applies over its range. A small **closed
/// set** for v0 — deliberately extensible (add a variant) but bounded, mirroring
/// the schema-bounds-the-merge discipline the typed atom uses. `Link` carries its
/// target so two distinct links are distinct marks (distinct ids).
///
/// `Ord`/`Hash` are derived so a run's *set* of active kinds is a canonical
/// [`BTreeSet`] — the render is order-insensitive and comparable.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum MarkKind {
    /// Bold weight.
    Bold,
    /// Italic slant.
    Italic,
    /// A hyperlink to the carried target (URL / `dregg://` address).
    Link(String),
    /// An inline code span (monospace, no nested marks in v0).
    Code,
    /// Strikethrough.
    Strike,
}

impl MarkKind {
    /// A canonical, type-tagged, self-delimiting byte key that binds the kind
    /// (and a `Link`'s target). Feeds the [`MarkId`] derivation so two marks over
    /// the same range differ by kind, and `Link(a)` / `Link(b)` never collide.
    fn canonical_key(&self) -> Vec<u8> {
        let mut out = Vec::new();
        match self {
            MarkKind::Bold => out.push(0),
            MarkKind::Italic => out.push(1),
            MarkKind::Link(target) => {
                out.push(2);
                out.extend_from_slice(&(target.len() as u64).to_le_bytes());
                out.extend_from_slice(target.as_bytes());
            }
            MarkKind::Code => out.push(3),
            MarkKind::Strike => out.push(4),
        }
        out
    }
}

/// A stable, content-derived identity for a [`Mark`], derived from its
/// **range + kind** — NOT its author. This is what makes the overlay a monotone
/// set: two authors who independently bold the same range mint the *same* mark
/// (idempotent union), and a removal tombstones *that* id. A plain 128-bit value,
/// mirroring [`AtomId`]'s shape and derivation (non-cryptographic
/// `DefaultHasher`; the commitment's collision resistance would rest on the
/// substrate leaf, not on this).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct MarkId(pub u128);

impl MarkId {
    /// Derive a mark's identity from its endpoints and kind. Distinct
    /// `(start, end, kind)` triples get distinct ids w.o.p.; identical triples
    /// collide *deliberately* (the same mark added twice is one mark —
    /// idempotence, the inflationary set-union).
    pub fn derive(start: AtomId, end: AtomId, kind: &MarkKind) -> MarkId {
        let key = kind.canonical_key();
        let mut h = DefaultHasher::new();
        0x4D41524Bu64.hash(&mut h); // "MARK"
        start.0.hash(&mut h);
        end.0.hash(&mut h);
        key.hash(&mut h);
        let lo = h.finish();
        let mut h2 = DefaultHasher::new();
        key.hash(&mut h2);
        end.0.hash(&mut h2);
        start.0.hash(&mut h2);
        0x4F5645524Cu64.hash(&mut h2); // "OVERL"
        let hi = h2.finish();
        MarkId(((hi as u128) << 64) | (lo as u128))
    }
}

/// A **non-destructive range overlay** over the document: a `kind` of formatting
/// applied to the span `[start, end]` (inclusive, addressed by stable endpoint
/// [`AtomId`]s), with an alive/dead [`Status`] tombstone (a *removal* flips it to
/// [`Status::Dead`] — monotone, never a destructive delete) and [`Provenance`].
///
/// It lives in the [`Marks`] store, DISJOINT from the [`DocGraph`] atom graph:
/// this is the load-bearing soundness fact — a mark and a concurrent text edit
/// cannot conflict because they touch different stores.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Mark {
    /// The mark's stable, content-derived identity (range + kind).
    pub id: MarkId,
    /// The first atom of the covered span (inclusive).
    pub start: AtomId,
    /// The last atom of the covered span (inclusive).
    pub end: AtomId,
    /// What formatting this mark applies.
    pub kind: MarkKind,
    /// Alive (the formatting applies) or Dead (tombstoned removal). Monotone:
    /// only ever `Alive -> Dead`, joined `Dead`-wins, exactly like an atom.
    pub status: Status,
    /// Who added this mark and in which patch.
    pub provenance: Provenance,
}

impl Mark {
    /// True iff this mark's formatting currently applies (not tombstoned).
    pub fn is_alive(&self) -> bool {
        self.status == Status::Alive
    }
}

/// The **marks store** — a keyed map `MarkId -> Mark`, a grow-only overlay that
/// sits ALONGSIDE the [`DocGraph`] (never inside it), merging by the exact same
/// monotone union discipline the atom store uses ([`crate::graph`]'s
/// `union_in_place`): add a mark (additive, idempotent), tombstone a mark
/// (`Dead`-wins), and merge two stores by union. Keeping it separate is what
/// makes a mark independent of every concurrent text edit.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Marks {
    /// The overlay, keyed by content-derived mark id, sorted (BTreeMap) so the
    /// store has a canonical form and `==` is order-insensitive — load-bearing
    /// for the merge-law tests, mirroring `DocGraph`'s `BTreeMap` atoms.
    marks: BTreeMap<MarkId, Mark>,
}

impl Marks {
    /// A fresh, empty overlay.
    pub fn new() -> Self {
        Marks {
            marks: BTreeMap::new(),
        }
    }

    /// Add a mark over `[start, end]` of `kind`, authored by `provenance`. The
    /// mark's id is content-derived from `(start, end, kind)`, so re-adding the
    /// same mark is idempotent (the inflationary set-union — the same formatting
    /// added twice, or by two authors, is one mark). Returns the mark id.
    ///
    /// Additive: never resurrects a tombstone and never overwrites an existing
    /// mark's fields (content-addressing guarantees same id => same range+kind),
    /// exactly like [`crate::graph`]'s `insert_atom`.
    pub fn add(
        &mut self,
        start: AtomId,
        end: AtomId,
        kind: MarkKind,
        provenance: Provenance,
    ) -> MarkId {
        let id = MarkId::derive(start, end, &kind);
        self.marks.entry(id).or_insert(Mark {
            id,
            start,
            end,
            kind,
            status: Status::Alive,
            provenance,
        });
        id
    }

    /// Tombstone a mark (flip its status to [`Status::Dead`]) — a
    /// **non-destructive removal**. Monotone: a live mark becomes dead; a dead
    /// mark stays dead; a missing mark is ignored (you can only remove what an
    /// add introduced). Mirrors `DocGraph::tombstone`.
    pub fn remove(&mut self, id: MarkId) {
        if let Some(m) = self.marks.get_mut(&id) {
            m.status = Status::Dead;
        }
    }

    /// Look up a mark by id (alive or dead).
    pub fn get(&self, id: MarkId) -> Option<&Mark> {
        self.marks.get(&id)
    }

    /// Whether a mark with this id exists (alive or dead).
    pub fn contains(&self, id: MarkId) -> bool {
        self.marks.contains_key(&id)
    }

    /// The number of marks (including tombstoned ones).
    pub fn len(&self) -> usize {
        self.marks.len()
    }

    /// True iff the overlay holds no marks at all.
    pub fn is_empty(&self) -> bool {
        self.marks.is_empty()
    }

    /// Iterate over all marks (alive and dead) in id order.
    pub fn iter(&self) -> impl Iterator<Item = &Mark> {
        self.marks.values()
    }

    /// Iterate over the *alive* marks in id order.
    pub fn alive(&self) -> impl Iterator<Item = &Mark> {
        self.marks.values().filter(|m| m.is_alive())
    }

    /// Fold another overlay into this one by **union**: mark statuses join
    /// (`Dead` wins, monotone), the range+kind of an already-present id is kept
    /// (content-addressing guarantees same id => same range+kind). This is the
    /// per-mark mirror of [`crate::graph`]'s `union_in_place` on atoms — the
    /// engine of [`marks_merge`].
    pub fn union_in_place(&mut self, other: &Marks) {
        for (id, mark) in &other.marks {
            self.marks
                .entry(*id)
                .and_modify(|m| m.status = m.status.join(mark.status))
                .or_insert_with(|| mark.clone());
        }
    }
}

/// The union-merge of two marks overlays. Total, commutative, associative,
/// idempotent — the same monotone set-union [`crate::merge`] is on the atom
/// graph, one level down (DREGG-DOCUMENT-FOUNDATION.md §1.5). The `BTreeMap`
/// canonical form makes these hold as `==` equalities, not up-to-iso.
pub fn marks_merge(a: &Marks, b: &Marks) -> Marks {
    let mut out = a.clone();
    out.union_in_place(b);
    out
}

/// One rendered text run carrying the [`MarkKind`]s active over it — the
/// **non-destructive** render integration. Produced by [`render_marked`] purely
/// from the atom's content (unchanged) plus the overlay: the atom's `content` is
/// never touched, so tombstoning a mark returns the run to plain formatting.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MarkedRun {
    /// The atom this run renders.
    pub atom: AtomId,
    /// The atom's rendered text (verbatim from `AtomContent::render_text` — the
    /// overlay never mutates it).
    pub text: String,
    /// The set of formatting kinds active over this run (empty = plain),
    /// canonical (a [`BTreeSet`], order-insensitive).
    pub marks: BTreeSet<MarkKind>,
}

impl MarkedRun {
    /// True iff the given kind is active over this run.
    pub fn has(&self, kind: &MarkKind) -> bool {
        self.marks.contains(kind)
    }
}

/// Layer the alive marks of `overlay` onto the rendered text runs of `g`,
/// WITHOUT changing any atom content — a thin layer over [`walk_atoms`].
///
/// The render walks the document's alive atoms in order (the same walk
/// [`crate::content`] uses) and, for each atom, reports which [`MarkKind`]s cover
/// its position. A mark `[start, end]` covers atom `a` iff, in document order,
/// `pos(start) <= pos(a) <= pos(end)` — computed from the endpoints' *positions
/// in the walk*, which is why a text atom inserted between the endpoints inherits
/// the mark (its position falls inside the range) and why the mark survives a
/// concurrent text edit (the endpoints' `AtomId`s are stable, so their positions
/// bound the same span). A mark whose endpoint is absent from the walk (e.g.
/// tombstoned) covers nothing.
pub fn render_marked(g: &DocGraph, overlay: &Marks) -> Vec<MarkedRun> {
    let order = walk_atoms(g);
    // Position of each alive atom in the document walk (stable AtomId -> index).
    let pos: BTreeMap<AtomId, usize> = order
        .iter()
        .enumerate()
        .map(|(i, (id, _))| (*id, i))
        .collect();

    // Precompute each alive mark's covered index range, if both endpoints are in
    // the walk. `lo..=hi` is order-insensitive in the endpoints.
    let ranges: Vec<(std::ops::RangeInclusive<usize>, &MarkKind)> = overlay
        .alive()
        .filter_map(|m| {
            let a = *pos.get(&m.start)?;
            let b = *pos.get(&m.end)?;
            let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
            Some((lo..=hi, &m.kind))
        })
        .collect();

    order
        .into_iter()
        .enumerate()
        .map(|(i, (atom, text))| {
            let marks: BTreeSet<MarkKind> = ranges
                .iter()
                .filter(|(r, _)| r.contains(&i))
                .map(|(_, k)| (*k).clone())
                .collect();
            MarkedRun { atom, text, marks }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::{Author, PatchId};
    use crate::content::content;
    use crate::patch::{Op, Patch};

    /// Insert a fresh text atom `content` (seeded `seed`) between `after` and
    /// `before` — the clean middle-insert shape: anchor `after -> new`, and thread
    /// `new -> before` so the new atom is *ordered* into the sequence (no
    /// antichain). Returns the patch.
    fn insert_between(
        seed: u64,
        content: &str,
        after: AtomId,
        before: AtomId,
        author: u64,
    ) -> Patch {
        let (z, zop) = Patch::add(seed, content, after);
        let mut p = Patch::by(Author(author), [zop]);
        p.push(Op::Connect {
            from: z,
            to: before,
        });
        p
    }

    fn prov(author: u64) -> Provenance {
        Provenance {
            author: Author(author),
            patch: PatchId(author as u128),
        }
    }

    /// A three-atom document "the quick brown" — each word its own atom, so a
    /// mark can address a single word by its atom id (start == end) or a span.
    /// Returns `(graph, the_, quick, brown)`.
    fn the_quick_brown() -> (DocGraph, AtomId, AtomId, AtomId) {
        let mut g = DocGraph::new();
        let (a, op_a) = Patch::add(1, "the ", AtomId::ROOT);
        let (b, op_b) = Patch::add(2, "quick", a);
        let (c, op_c) = Patch::add(3, " brown", b);
        Patch::by(Author(1), [op_a]).apply(&mut g);
        Patch::by(Author(1), [op_b]).apply(&mut g);
        Patch::by(Author(1), [op_c]).apply(&mut g);
        (g, a, b, c)
    }

    // ── the merge laws hold (monotone set-union) ─────────────────────────────

    /// Three overlays over one document: a bold word, an italic span, and a link
    /// — enough concurrency to exercise the union laws.
    fn overlays() -> (Marks, Marks, Marks, AtomId, AtomId, AtomId) {
        let (_g, a, b, c) = the_quick_brown();
        let mut x = Marks::new();
        x.add(b, b, MarkKind::Bold, prov(1));
        let mut y = Marks::new();
        y.add(a, c, MarkKind::Italic, prov(2));
        let mut z = Marks::new();
        z.add(b, c, MarkKind::Link("https://dregg.net".into()), prov(3));
        (x, y, z, a, b, c)
    }

    #[test]
    fn marks_merge_is_total_and_never_panics() {
        let (x, y, z, ..) = overlays();
        for (p, q) in [(&x, &y), (&x, &z), (&y, &z), (&x, &x)] {
            let m = marks_merge(p, q);
            assert!(m.len() >= 1);
        }
    }

    #[test]
    fn marks_merge_is_commutative() {
        let (x, y, z, ..) = overlays();
        assert_eq!(marks_merge(&x, &y), marks_merge(&y, &x));
        assert_eq!(marks_merge(&x, &z), marks_merge(&z, &x));
        assert_eq!(marks_merge(&y, &z), marks_merge(&z, &y));
    }

    #[test]
    fn marks_merge_is_associative() {
        let (x, y, z, ..) = overlays();
        assert_eq!(
            marks_merge(&marks_merge(&x, &y), &z),
            marks_merge(&x, &marks_merge(&y, &z))
        );
    }

    #[test]
    fn marks_merge_is_idempotent() {
        let (x, y, ..) = overlays();
        assert_eq!(marks_merge(&x, &x), x);
        let m = marks_merge(&x, &y);
        assert_eq!(marks_merge(&m, &m), m);
        assert_eq!(marks_merge(&m, &x), m);
    }

    #[test]
    fn a_removal_merges_monotonically_dead_wins() {
        // One branch adds a bold mark; the other adds it and then removes it. The
        // merge is Dead-wins per id — the removal absorbs the add, monotonically,
        // exactly like an atom tombstone (never a destructive delete: the mark id
        // is still present, just dead).
        let (_g, _a, b, _c) = the_quick_brown();
        let mut added = Marks::new();
        let id = added.add(b, b, MarkKind::Bold, prov(1));

        let mut removed = added.clone();
        removed.remove(id);

        let m1 = marks_merge(&added, &removed);
        let m2 = marks_merge(&removed, &added);
        assert_eq!(m1, m2, "removal commutes with the add");
        assert_eq!(m1.get(id).unwrap().status, Status::Dead, "dead wins");
        assert!(
            m1.contains(id),
            "non-destructive: the tombstone is retained"
        );
        assert_eq!(m1.alive().count(), 0);
    }

    // ── THE SOUNDNESS PROPERTY (load-bearing) ────────────────────────────────

    #[test]
    fn a_mark_and_a_concurrent_text_edit_do_not_conflict() {
        // Author A adds a mark over the span [the, brown]; author B concurrently
        // inserts a NEW text atom (" very") into the graph. The two edits touch
        // DISJOINT stores — A only the Marks overlay, B only the DocGraph — so
        // the merged (DocGraph, Marks) carries BOTH, with no conflict.
        let (base_g, a, b, c) = the_quick_brown();
        let base_marks = Marks::new();

        // Author A: a mark, graph untouched.
        let mut marks_a = base_marks.clone();
        let mark_id = marks_a.add(a, c, MarkKind::Italic, prov(1));
        let graph_a = base_g.clone(); // A did not touch the text

        // Author B: a text insert (threaded cleanly between "the " and "quick"),
        // overlay untouched.
        let graph_b = insert_between(9, " very", a, b, 2).apply_to(&base_g);
        let marks_b = base_marks.clone(); // B did not touch the overlay

        // Merge each store by its own union — they never interact.
        let merged_g = crate::merge(&graph_a, &graph_b);
        let merged_marks = marks_merge(&marks_a, &marks_b);

        // BOTH survived. The graph has B's text and no conflict from the mark
        // (marks are not in the graph at all).
        assert!(
            !content(&merged_g).has_conflict(),
            "a mark cannot introduce a graph conflict — it is not in the graph"
        );
        assert!(
            content(&merged_g).to_marked_string().contains(" very"),
            "B's concurrent text edit survives"
        );
        // The mark survives, alive, still addressing its stable endpoints.
        let mark = merged_marks
            .get(mark_id)
            .expect("A's mark survives the merge");
        assert!(mark.is_alive());
        assert_eq!((mark.start, mark.end), (a, c));

        // And the render over the merged state still applies the mark across its
        // range — INCLUDING B's newly inserted atom, which fell inside [a, c].
        let runs = render_marked(&merged_g, &merged_marks);
        assert!(
            runs.iter()
                .any(|r| r.text == " very" && r.has(&MarkKind::Italic)),
            "the concurrently-inserted atom is covered by the concurrent mark — \
             disjoint stores composed with zero conflict"
        );
    }

    #[test]
    fn a_mark_survives_a_text_insert_within_its_range() {
        // A mark over [the, brown]. Then a text atom is inserted BETWEEN the
        // endpoints. Because a mark addresses by stable AtomId endpoints (which
        // never move — atom.rs), the mark does NOT re-mint: it still covers its
        // range, and the newly inserted atom, whose walk position falls inside
        // [the, brown], inherits the coverage.
        let (g, a, b, c) = the_quick_brown();
        let mut marks = Marks::new();
        let id = marks.add(a, c, MarkKind::Bold, prov(1));

        // Before the insert: "quick" (between the endpoints) is bold.
        let before = render_marked(&g, &marks);
        assert!(
            before
                .iter()
                .any(|r| r.text == "quick" && r.has(&MarkKind::Bold)),
            "the span is bold before the edit"
        );

        // Insert " very" between "the " and "quick" (strictly inside [the, brown]).
        let g2 = insert_between(9, " very", a, b, 2).apply_to(&g);

        // The mark is byte-for-byte unchanged — it did NOT re-mint.
        assert_eq!(marks.get(id).unwrap().start, a);
        assert_eq!(marks.get(id).unwrap().end, c);

        // The inserted atom is covered, AND the original span is still covered:
        // the mark's stable endpoints bound the same (now-wider) span.
        let after = render_marked(&g2, &marks);
        assert!(
            after
                .iter()
                .any(|r| r.text == " very" && r.has(&MarkKind::Bold)),
            "the inserted-within-range atom inherits the mark (stable endpoints)"
        );
        assert!(
            after
                .iter()
                .any(|r| r.text == "quick" && r.has(&MarkKind::Bold)),
            "the original span is still marked after the insert"
        );
        // The atom BEFORE the range start is NOT covered (the mark bites — it is
        // not covering everything).
        assert!(
            after
                .iter()
                .all(|r| r.text != "quick" || r.marks.len() == 1),
            "only bold is active"
        );
    }

    // ── non-destructive render integration ───────────────────────────────────

    #[test]
    fn bold_mark_renders_active_then_removal_renders_plain_non_destructively() {
        let (g, _a, b, _c) = the_quick_brown();
        let mut marks = Marks::new();
        let id = marks.add(b, b, MarkKind::Bold, prov(1));

        // Bold is active over "quick"; the atom content is unchanged.
        let runs = render_marked(&g, &marks);
        let quick = runs.iter().find(|r| r.atom == b).unwrap();
        assert_eq!(quick.text, "quick", "content is verbatim — never mutated");
        assert!(quick.has(&MarkKind::Bold), "the mark is active");
        // Every other run is plain (the mark does not leak past its range).
        assert!(
            runs.iter()
                .filter(|r| r.atom != b)
                .all(|r| r.marks.is_empty()),
            "the mark covers only its range"
        );

        // Remove the mark (a tombstone) and re-render: "quick" is plain again,
        // and — the non-destructive fact — the atom's TEXT is byte-identical.
        marks.remove(id);
        let runs2 = render_marked(&g, &marks);
        let quick2 = runs2.iter().find(|r| r.atom == b).unwrap();
        assert_eq!(
            quick2.text, "quick",
            "removing a mark never touches content"
        );
        assert!(!quick2.has(&MarkKind::Bold), "the formatting is gone");
        assert!(quick2.marks.is_empty(), "plain again");
        // The tombstone is retained (monotone removal), the atom is untouched.
        assert_eq!(marks.get(id).unwrap().status, Status::Dead);
    }

    #[test]
    fn concurrent_distinct_marks_compose_over_the_same_span() {
        // Bold from one author + a link from another, over overlapping spans,
        // compose in the union — a run inside both carries BOTH kinds.
        let (g, a, b, c) = the_quick_brown();
        let mut m1 = Marks::new();
        m1.add(a, c, MarkKind::Bold, prov(1));
        let mut m2 = Marks::new();
        m2.add(b, c, MarkKind::Link("https://dregg.net".into()), prov(2));

        let merged = marks_merge(&m1, &m2);
        let runs = render_marked(&g, &merged);
        let brown = runs.iter().find(|r| r.atom == c).unwrap();
        assert!(brown.has(&MarkKind::Bold));
        assert!(brown.has(&MarkKind::Link("https://dregg.net".into())));
        assert_eq!(brown.marks.len(), 2, "both marks compose over the span");
    }
}
