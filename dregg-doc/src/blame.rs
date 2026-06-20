//! Blame / annotate — per-atom authorship that **survives moves and merges**.
//!
//! `git blame` attributes each *line* by walking the textual diff backwards: it
//! asks "which commit last touched this line of text?". Because its unit is a
//! line position in a file, blame gets *reassigned* the moment surrounding text
//! shifts — insert a paragraph above and the line numbers move; reflow, reorder,
//! or merge and authorship smears onto whoever happened to rewrite the region.
//! The authorship is an artifact of the *diff*, not of the *content*.
//!
//! Here blame is **correct by construction**. The unit is the [`Atom`], whose
//! [`AtomId`] is content-addressed and *stable*: it is the same id wherever the
//! atom lives in the order, however many patches insert around it, however the
//! branches merge. So [`blame`] reads authorship straight off each live atom's
//! [`Provenance`] — who authored it, in which patch — and that attribution does
//! not move when the text around it does. A middle insert by a third author
//! leaves the surrounding atoms' blame *exactly* where it was: the famous
//! git-blame failure mode simply cannot occur, because nothing about an atom's
//! identity depends on its neighbours.
//!
//! [`Atom`]: crate::Atom

use crate::atom::{AtomId, Author, PatchId};
use crate::content::walk_atoms;
use crate::graph::DocGraph;
use std::collections::BTreeMap;

/// One line of blame output: a live atom, its rendered content, and the
/// authorship read off its provenance (who, in which patch).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BlameLine {
    /// The content-addressed atom this content belongs to (stable across moves
    /// and merges — the reason the attribution is correct).
    pub atom: AtomId,
    /// The atom's rendered content span.
    pub content: String,
    /// Who authored this atom.
    pub author: Author,
    /// The patch that introduced this atom.
    pub patch: PatchId,
}

/// Annotate every live atom in document order with its real authorship.
///
/// Walks the live atoms in the same order [`crate::content`] renders them (via
/// [`walk_atoms`]) and, for each, reads the authorship directly from the atom's
/// [`crate::Provenance`]. Because the [`AtomId`] is content-addressed and stable,
/// the attribution rides *with the content*: inserting, deleting, reordering, or
/// merging around an atom never reassigns who authored it.
pub fn blame(g: &DocGraph) -> Vec<BlameLine> {
    walk_atoms(g)
        .into_iter()
        .filter_map(|(id, content)| {
            let atom = g.atom(id)?;
            Some(BlameLine {
                atom: id,
                content,
                author: atom.provenance.author,
                patch: atom.provenance.patch,
            })
        })
        .collect()
}

/// A contribution tally: how many live atoms each author authored.
///
/// Counts *every* live atom (including each alternative of an unresolved
/// conflict), not just the linear prefix — so a co-author's contribution inside
/// a conflict region is still credited. The ROOT sentinel (authored by
/// [`Author::SYSTEM`]) is excluded; it carries no content.
pub fn blame_summary(g: &DocGraph) -> BTreeMap<Author, usize> {
    let mut tally: BTreeMap<Author, usize> = BTreeMap::new();
    for atom in g.atoms() {
        if atom.id == AtomId::ROOT || !atom.is_alive() {
            continue;
        }
        *tally.entry(atom.provenance.author).or_default() += 1;
    }
    tally
}
