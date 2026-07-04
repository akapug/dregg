//! THE FRUSTUM — the cap-bounded, per-viewer crawl ("cap-gated Pharo").
//!
//! Reflection is NOT omniscient. `.as(viewer)` computes what a principal MAY observe:
//!
//!   - **which cells** it can crawl — the reachability closure of its own c-list (the
//!     ocap topology; a viewer reaches only cells it holds a capability path to, plus
//!     itself);
//!   - **which fields** it reads — bounded by `FieldVisibility` (a `Committed` slot
//!     surfaces its commitment, never the value — enforced in [`reflect_cell`]);
//!   - **which affordances** it may fire — projected by `is_attenuation`
//!     ([`crate::affordances`]).
//!
//! A frustum can never observe past the viewer's authority: an unreachable cell is
//! simply absent. This is the structural core of the membrane's non-amplification —
//! observing through your own caps, darkening what you can't reach.

use std::collections::BTreeSet;

use dregg_cell::Ledger;
use dregg_types::CellId;

use crate::graph::OcapGraph;
use crate::substance::{Inspectable, reflect_cell};

/// A viewer's cap-bounded view of the image: the set of cells it may crawl + the
/// reflective projection of each, computed off the live ledger through the viewer's
/// own authority. Build with [`Frustum::project`].
pub struct Frustum<'l> {
    ledger: &'l Ledger,
    graph: OcapGraph,
    viewer: CellId,
    visible: BTreeSet<CellId>,
}

impl<'l> Frustum<'l> {
    /// **Project the image through `viewer`'s authority.** The visible set is the
    /// viewer itself plus the transitive reachability closure of its c-list (the cells
    /// it holds a capability path to). Cells outside the closure are NOT observable —
    /// the frustum simply does not contain them (darkened, never forged).
    pub fn project(ledger: &'l Ledger, viewer: CellId) -> Self {
        let graph = OcapGraph::build(ledger);
        let mut visible: BTreeSet<CellId> = graph.reachable_from(&viewer);
        // A cell trivially observes itself (if it is on the ledger).
        if ledger.get(&viewer).is_some() {
            visible.insert(viewer);
        }
        // Intersect with what is actually on the ledger (reachability is over edges,
        // which could name a target absent from this ledger snapshot).
        visible.retain(|c| ledger.get(c).is_some());
        Frustum {
            ledger,
            graph,
            viewer,
            visible,
        }
    }

    /// The viewer this frustum is projected for.
    pub fn viewer(&self) -> CellId {
        self.viewer
    }

    /// The ocap graph (the full topology — the frustum's `visible` set is the bounded
    /// view; the graph is the substrate it was computed from).
    pub fn graph(&self) -> &OcapGraph {
        &self.graph
    }

    /// **Can the viewer observe `cell`?** True iff `cell` is in the reachability
    /// closure of the viewer's authority (or is the viewer itself).
    pub fn can_observe(&self, cell: &CellId) -> bool {
        self.visible.contains(cell)
    }

    /// The cells the viewer MAY crawl, id-sorted (the bounded `for (const c of
    /// deos.world.cells())` a frustum exposes).
    pub fn visible_cells(&self) -> Vec<CellId> {
        let mut v: Vec<CellId> = self.visible.iter().copied().collect();
        v.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
        v
    }

    /// How many cells the viewer may crawl (its observable subgraph size).
    pub fn visible_count(&self) -> usize {
        self.visible.len()
    }

    /// **Reflect a cell THROUGH the frustum** — the attested per-viewer read. Returns
    /// `None` if the cell is outside the viewer's authority (unobservable: not a
    /// forgery, an absence). On success the `Inspectable` already redacts `Committed`
    /// fields (the reflector reads them publicly).
    pub fn reflect(&self, cell: &CellId) -> Option<Inspectable> {
        if !self.can_observe(cell) {
            return None;
        }
        self.ledger.get(cell).map(|c| reflect_cell(cell, c))
    }
}
