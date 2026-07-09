//! Atoms — the vertices of a [`crate::DocGraph`].
//!
//! An atom is a span of document content with a stable, content-derived
//! identity, an alive/dead status, and **provenance** (who authored it, in which
//! patch). Following Pijul (DOCUMENT-LANGUAGE.md §2.2), an atom is *never
//! physically removed*: a delete only flips its status to [`Status::Dead`] (a
//! tombstone). Because deletion is therefore additive (you add a tombstone, you
//! never subtract a vertex), deletes commute with everything — which is what
//! makes the union-merge total.
//!
//! The provenance is load-bearing for the conflict view (§3.5): each alternative
//! in a conflict carries *who wrote it*, so "who authored which alternative" is a
//! fact, not a guess. It is an [`Author`] + a [`PatchId`] — and under the
//! `cell-heap` ride these exact values are committed state: every structured
//! heap leaf's digest binds them (`substrate::leaf_for_atom` /
//! `leaf_for_field`), and the document's patch chain lives in the cell
//! (`doc_heap`'s `COLL_HISTORY`), so a reopened document replays the same
//! provenance the boundary root committed. The executor-driven ride
//! (`executor_drive`) additionally journals each committed edit as a real turn
//! receipt — a second witness of the same provenance (the receipt↔patch-id
//! cross-check is a named seam, not yet built).

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// A stable, content-derived identifier for an atom (a graph vertex).
///
/// A plain 128-bit value that the substrate projection binds VERBATIM: each
/// committed atom leaf's preimage carries this id (`substrate::leaf_for_atom`),
/// and the committed patch chain (`doc_heap`'s `COLL_HISTORY`) re-derives the
/// identical id on replay — so the id a light client's root binds and the id
/// the algebra computes are the same value, not a stand-in for a future one.
/// [`AtomId::ROOT`] is the reserved sentinel that anchors the start of the
/// document — every inserted atom is ordered *after* some existing atom, and
/// the first real atom is ordered after `ROOT`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct AtomId(pub u128);

impl AtomId {
    /// The sentinel start-of-document vertex. It is always alive and carries no
    /// content; it exists so that "insert at the beginning" is uniformly
    /// "insert after `ROOT`".
    pub const ROOT: AtomId = AtomId(0);

    /// Derive a content-addressed id from an author-chosen seed and the atom's
    /// content. Distinct (seed, content) pairs get distinct ids with
    /// overwhelming probability; identical pairs collide *deliberately* (the
    /// same edit authored twice is the same atom — idempotence).
    ///
    /// The derivation uses `DefaultHasher` — deliberately non-cryptographic.
    /// It supplies the *shape* the patch algebra relies on (deterministic,
    /// content-derived, idempotent); the *commitment's* collision resistance
    /// does not rest on it, because the substrate ride binds the derived id
    /// itself inside a BLAKE3 leaf preimage under the Poseidon2 heap root — a
    /// forged or substituted id cannot hide under the committed boundary.
    pub fn derive(seed: u64, content: &str) -> AtomId {
        let mut h = DefaultHasher::new();
        0xD0Cu64.hash(&mut h);
        seed.hash(&mut h);
        content.hash(&mut h);
        let lo = h.finish();
        let mut h2 = DefaultHasher::new();
        content.hash(&mut h2);
        seed.hash(&mut h2);
        0xA70Du64.hash(&mut h2);
        let hi = h2.finish();
        // Never collide with the ROOT sentinel.
        let v = ((hi as u128) << 64) | (lo as u128);
        AtomId(if v == 0 { 1 } else { v })
    }
}

/// Who authored an edit — an opaque label the conflict view attributes each
/// alternative to. The rides ground it twice: the committed heap binds every
/// `Author` value (inside each provenance-carrying leaf digest AND verbatim in
/// the committed patch chain, `doc_heap`'s `COLL_HISTORY`), and the
/// executor-driven ride (`executor_drive`) realizes the authoring identity as
/// an editor *cell* whose capability gates the edit.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Author(pub u64);

impl Author {
    /// The anonymous/system author (e.g. the genesis ROOT atom).
    pub const SYSTEM: Author = Author(0);
}

/// A patch's stable identity — content-addressed over its ops + author, so the
/// same edit has the same id (idempotence at the patch level). The committed
/// patch chain (`doc_heap`'s `COLL_HISTORY`) binds the ops + author this id
/// derives from, so replaying a reopened document re-derives the identical id
/// — blame's patch attribution survives close/reopen. The executor-driven
/// ride's turn receipt is a second, journaled witness of the same edit; the
/// receipt-id↔patch-id correspondence is a named seam, not yet cross-checked.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct PatchId(pub u128);

impl PatchId {
    /// The genesis "patch" that the ROOT sentinel belongs to.
    pub const GENESIS: PatchId = PatchId(0);
}

/// Provenance carried by every atom: who authored it and in which patch. The
/// document's commitment binds this (a light client cannot be shown an
/// alternative whose author is forged — the conflict-as-state soundness goal of
/// DOCUMENT-LANGUAGE.md §4.4 RESEARCH).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Provenance {
    /// The authoring identity.
    pub author: Author,
    /// The patch that introduced this atom.
    pub patch: PatchId,
}

impl Provenance {
    /// The genesis provenance for the ROOT sentinel.
    pub const GENESIS: Provenance = Provenance {
        author: Author::SYSTEM,
        patch: PatchId::GENESIS,
    };
}

/// The liveness status of an atom. Monotone: an atom may only travel
/// `Alive -> Dead`, never back. The join (used by [`crate::merge`]) is therefore
/// "dead wins" — if either branch tombstoned the atom, the merged atom is dead.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Status {
    /// The atom is live: it participates in the rendered content.
    Alive,
    /// The atom is tombstoned: it is retained in the graph (for provenance and
    /// commutation) but excluded from the rendered content.
    Dead,
}

impl Status {
    /// The monotone join of two statuses: `Dead` absorbs `Alive`.
    pub fn join(self, other: Status) -> Status {
        match (self, other) {
            (Status::Alive, Status::Alive) => Status::Alive,
            _ => Status::Dead,
        }
    }
}

/// A text run — the CRDT-sequenced leaf of the document (DREGG-DOCUMENT-DESIGN
/// §2). Today a plain `String`, byte-compatible with the pre-typed-atom content
/// so existing diffs/merges of prose behave identically. HOLE: a `Run` becomes a
/// byte-interval-addressed value once the interval-atom + status-lattice step
/// (design §2, build-order 5) lands, so split/join/move preserve atom identity.
pub type Run = String;

/// What an atom *is* — the typed content sum that replaces the old flat
/// `content: String` (DREGG-DOCUMENT-DESIGN §2, the one concentrated
/// re-foundation). Deliberately **DOM-shaped and schema-mappable**, NOT a closed
/// set of bespoke kinds: a document is a schema-constrained DOM subtree, so it
/// renders near-identically into shadow DOM (no foreign-IR translation that
/// throws away Range/selection/contenteditable/a11y/CSS), and merges are sound
/// *because* the schema bounds it (ProseMirror's insight).
///
/// The two live variants map 1:1 onto DOM:
/// - [`AtomContent::Text`] → a DOM **Text node**.
/// - [`AtomContent::Element`] → a DOM **Element** (`tag`, `attrs`, child nodes).
///   It subsumes what a closed sum would spell as separate kinds:
///   * **block**: `tag = "section" | "p" | "ul" | "li" | "table" | "td" | "blockquote"`;
///   * **code**: `tag = "code"`, `attrs = [("lang", …)]`, a `Text` child holding the source;
///   * **media**: `tag = "img" | "canvas"`, `attrs = [("src", <content-addr>), …]`.
///   A **schema** (the next step, ProseMirror/Notion-style) constrains which
///   `tag`s exist, which `attrs` each admits, and which child arrangements are
///   legal — that bound is what keeps a structural merge sound.
///
/// `children` are **atom ids** (references into the same [`crate::DocGraph`]), so
/// structure is a block+inline tree over the existing content-addressed vertices,
/// and reparenting/splitting is a structural edit — not a line-antichain accident.
///
/// HOLES left for later build-order steps (named, not silently absent):
/// - **`Embed(ChildRef)`** — a nested document / cell-pointer. Requires cross-cell
///   addressing (`docs/deos/DOC-CELL-COMPOSITION.md`, `composition.rs`'s two-arm
///   `ChildRef`), which is undesigned here; see the crate report. An embed would
///   need an atom id that names *(cell, atom)*, not just an atom within one graph.
/// - **`Transclude(AtomRange, provenance)`** — an authenticated live quote (design
///   §5); needs the `deos-web-cells` unification onto atom identity.
/// - **Marks** (bold/link/code-span) are NOT baked into content — they are a
///   separate mergeable range overlay (Peritext), design §2. Not a variant here.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AtomContent {
    /// A text run — a DOM Text node. Byte-compatible with the old `String`.
    Text(Run),
    /// A schema-constrained structural node — maps 1:1 to a DOM Element. Its
    /// children are atom ids in the same graph (a block+inline tree).
    Element {
        /// The DOM tag (`"section"`, `"p"`, `"code"`, `"img"`, …). A schema
        /// bounds the legal set.
        tag: String,
        /// DOM attributes, in author order (`lang`, `src`, …). Kept as a `Vec`
        /// (order-preserving) so the canonical encoding — hence the commitment —
        /// is deterministic without imposing a sort the DOM would not.
        attrs: Vec<(String, String)>,
        /// Child atom ids, in document order (the DOM child list).
        children: Vec<AtomId>,
    },
}

impl AtomContent {
    /// A plain text run (the common constructor; the byte-compatible leaf).
    pub fn text(s: impl Into<String>) -> AtomContent {
        AtomContent::Text(s.into())
    }

    /// The text run, if this is a `Text` atom (`None` for structural nodes).
    pub fn as_text(&self) -> Option<&str> {
        match self {
            AtomContent::Text(s) => Some(s),
            AtomContent::Element { .. } => None,
        }
    }

    /// The textual projection used by the linearized render / blame / diff. A
    /// `Text` run renders its bytes; a structural `Element` contributes no text of
    /// its own (its children are atoms, rendered in their own right by the walk).
    /// This is the DOM `textContent`-of-this-node-only stand-in, not the subtree.
    pub fn render_text(&self) -> String {
        match self {
            AtomContent::Text(s) => s.clone(),
            AtomContent::Element { .. } => String::new(),
        }
    }

    /// A canonical, **type-tagged**, self-delimiting byte encoding that binds the
    /// atom's KIND *and* content. Fed verbatim into the commitment preimage
    /// ([`crate::commit`]) and the substrate heap-leaf / history serializations,
    /// so the commitment binds an atom's type — a structural node and a text run
    /// with the same rendered bytes commit differently, and a forged/retagged
    /// atom cannot hide under an equal render (the anti-forge tooth, on a typed
    /// atom). Every variable-length run is length-prefixed (no concat ambiguity).
    pub fn canonical_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        fn run(out: &mut Vec<u8>, b: &[u8]) {
            out.extend_from_slice(&(b.len() as u64).to_le_bytes());
            out.extend_from_slice(b);
        }
        match self {
            AtomContent::Text(s) => {
                out.push(0);
                run(&mut out, s.as_bytes());
            }
            AtomContent::Element {
                tag,
                attrs,
                children,
            } => {
                out.push(1);
                run(&mut out, tag.as_bytes());
                out.extend_from_slice(&(attrs.len() as u64).to_le_bytes());
                for (k, v) in attrs {
                    run(&mut out, k.as_bytes());
                    run(&mut out, v.as_bytes());
                }
                out.extend_from_slice(&(children.len() as u64).to_le_bytes());
                for c in children {
                    out.extend_from_slice(&c.0.to_le_bytes());
                }
            }
        }
        out
    }

    /// The strict inverse of [`Self::canonical_bytes`] — decode a typed atom from
    /// its committed bytes. `None` on an unknown tag, truncation, invalid UTF-8,
    /// or trailing garbage (so a tampered heap byte is refused, not coerced).
    pub fn from_canonical_bytes(bytes: &[u8]) -> Option<AtomContent> {
        struct Dec<'a> {
            b: &'a [u8],
            at: usize,
        }
        impl<'a> Dec<'a> {
            fn take(&mut self, n: usize) -> Option<&'a [u8]> {
                let end = self.at.checked_add(n)?;
                if end > self.b.len() {
                    return None;
                }
                let s = &self.b[self.at..end];
                self.at = end;
                Some(s)
            }
            fn u64(&mut self) -> Option<u64> {
                Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
            }
            fn u128(&mut self) -> Option<u128> {
                Some(u128::from_le_bytes(self.take(16)?.try_into().ok()?))
            }
            fn run(&mut self) -> Option<&'a [u8]> {
                let n = self.u64()? as usize;
                self.take(n)
            }
            fn string(&mut self) -> Option<String> {
                String::from_utf8(self.run()?.to_vec()).ok()
            }
        }
        let mut d = Dec { b: bytes, at: 0 };
        let tag = *d.take(1)?.first()?;
        let content = match tag {
            0 => AtomContent::Text(d.string()?),
            1 => {
                let t = d.string()?;
                let n_attrs = d.u64()? as usize;
                let mut attrs = Vec::with_capacity(n_attrs);
                for _ in 0..n_attrs {
                    let k = d.string()?;
                    let v = d.string()?;
                    attrs.push((k, v));
                }
                let n_children = d.u64()? as usize;
                let mut children = Vec::with_capacity(n_children);
                for _ in 0..n_children {
                    children.push(AtomId(d.u128()?));
                }
                AtomContent::Element {
                    tag: t,
                    attrs,
                    children,
                }
            }
            _ => return None,
        };
        if d.at != bytes.len() {
            return None; // trailing garbage
        }
        Some(content)
    }
}

/// A vertex of the document graph: typed content with identity, status, and
/// provenance.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Atom {
    /// The atom's stable identity.
    pub id: AtomId,
    /// The atom's typed content ([`AtomContent`]): a text run or a
    /// schema-constrained structural node — replacing the old flat `String`
    /// (DREGG-DOCUMENT-DESIGN §2). The atom granularity for the `Text` leaf stays
    /// an empirical choice (DOCUMENT-LANGUAGE.md §4.4).
    pub content: AtomContent,
    /// Alive or tombstoned.
    pub status: Status,
    /// Who authored this atom and in which patch.
    pub provenance: Provenance,
}

impl Atom {
    /// True iff this atom currently participates in the rendered content.
    pub fn is_alive(&self) -> bool {
        self.status == Status::Alive
    }
}
