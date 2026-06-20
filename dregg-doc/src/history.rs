//! Document history — content as the fold of the patch-history.
//!
//! A document is *not* a final graph; it is the **sequence of patches** that
//! produced it (DOCUMENT-LANGUAGE.md §0, §4.1: "the document's content is the
//! result of applying its patch-history"). [`History`] is that sequence, with
//! [`History::replay`] / [`History::replay_to`] folding the patches from genesis
//! into a [`DocGraph`] — the substrate's `History::replay_to(tip)`, in miniature.
//!
//! Because every patch is content-addressed ([`PatchId`]) and applying patches
//! is order-independent up to causality, the *fold* and the *merge* of the
//! per-patch graphs coincide (the colimit seen two ways). A branch is a history
//! that shares a prefix and then diverges; publishing it is a [`crate::merge`]
//! of the two folds (the stitch = pushout, BRANCH-AND-STITCH-PROTOCOL.md §3).

use crate::atom::PatchId;
use crate::graph::DocGraph;
use crate::patch::Patch;

/// A document's patch-history: the ordered list of patches from genesis. The
/// content at any point is the fold of a prefix.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct History {
    patches: Vec<Patch>,
}

impl History {
    /// An empty history (genesis only).
    pub fn new() -> Self {
        History {
            patches: Vec::new(),
        }
    }

    /// Record a patch as the new tip. Returns its [`PatchId`] (the tip cursor).
    pub fn commit(&mut self, patch: Patch) -> PatchId {
        let id = patch.id();
        self.patches.push(patch);
        id
    }

    /// The patches, oldest first.
    pub fn patches(&self) -> &[Patch] {
        &self.patches
    }

    /// How many patches are in the history.
    pub fn len(&self) -> usize {
        self.patches.len()
    }

    /// Whether the history is empty (genesis only).
    pub fn is_empty(&self) -> bool {
        self.patches.is_empty()
    }

    /// The tip patch id, or `None` at genesis.
    pub fn tip(&self) -> Option<PatchId> {
        self.patches.last().map(Patch::id)
    }

    /// Fold the *whole* history from genesis into a graph (the current content).
    pub fn replay(&self) -> DocGraph {
        let mut g = DocGraph::new();
        for p in &self.patches {
            p.apply(&mut g);
        }
        g
    }

    /// Fold the history up to and including the patch with id `cursor` (a
    /// time-travel read; the patch-history scrubber, §5). If `cursor` is not in
    /// the history, replays the whole thing.
    pub fn replay_to(&self, cursor: PatchId) -> DocGraph {
        let mut g = DocGraph::new();
        for p in &self.patches {
            p.apply(&mut g);
            if p.id() == cursor {
                break;
            }
        }
        g
    }

    /// Fork a draft branch off the current tip: a new history that shares this
    /// one's patches as its prefix (BRANCH-AND-STITCH-PROTOCOL.md §1). Edits on
    /// the branch are confined to the branch until published.
    pub fn branch(&self) -> History {
        self.clone()
    }

    /// Publish (stitch) another history into this one: the merge of the two
    /// folds, the pushout into the shared document (§3.1). Returns the merged
    /// graph; the shared history gains the branch's *new* patches (those past
    /// the shared prefix) so the published content is reproducible.
    pub fn stitch(&mut self, branch: &History) -> DocGraph {
        let shared = self
            .patches
            .iter()
            .zip(&branch.patches)
            .take_while(|(a, b)| a == b)
            .count();
        for p in &branch.patches[shared..] {
            self.patches.push(p.clone());
        }
        self.replay()
    }
}
