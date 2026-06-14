//! **Fog-of-war as a confinement theorem** — the deos forcing-function webgame,
//! made into steel. A hidden-information grid skirmish where *what a player can
//! SEE is exactly what their capabilities authorize them to rehydrate*, so a
//! player **provably cannot peek** at hidden enemy state: the membrane refuses to
//! project it, and the refusal is cap-gated by the GENUINE [`is_attenuation`] /
//! [`Membrane`] / affordance discipline this crate already ships — never a
//! client-side honor-system visibility flag.
//!
//! `docs/deos/DEOS-APPS.md` §"the forcing function: a deos webgame" — the deos
//! novelty *is a game mechanic made into a security property*:
//!
//! - **Fog of war = the membrane's per-viewer projection.** In a normal game,
//!   "what you can see" is a rendering trick the client could cheat. Here, what a
//!   player can see is *what its caps authorize it to rehydrate* — the membrane
//!   will not project the enemy's hidden tiles to you. Fog of war stops being
//!   honor-system and becomes a **confinement property** ([`Board::project_for`] /
//!   the `no_peek` keystone).
//! - **Moves = affordances** ([`CellAffordance`] — cap-gated verified-turn
//!   templates carrying a REAL [`dregg_turn::Effect`]) → an illegal move is a
//!   **refused turn** ([`AffordanceSurface::fire`] → [`crate::affordance::FireError`]);
//!   anti-cheat is free.
//! - **Multiplayer = the web-of-cells** — each player is a cell, the board is a
//!   shared cell, every tile is a cell published into a real [`WebOfCells`].
//! - **Agents-as-players** — an AI player ([`AgentPlayer`]) fires the SAME
//!   cap-gated affordances as a human; its action space IS its attenuated cap set.
//! - **Spectating = a rehydratable frustum-snapshot** ([`Board::snapshot_for`])
//!   that RESPECTS the spectator's fog (they rehydrate only what their
//!   spectator-cap authorizes) and carries the [`Rehydration`] liveness-type.
//!
//! ## Why this is a *cap-confinement* property, not a visibility flag
//!
//! Vision rides the REAL cap lattice on **three independent axes**, all refusing a
//! cross-player peek through the SAME machinery the rest of the crate proves:
//!
//! 1. **Player identity = the window rights** ([`AuthRequired::Custom`]`{ vk_hash
//!    }`). Each player's vision authority carries a DISTINCT `Custom { vk_hash }` —
//!    and the `vk_hash` is the GENUINE [`crate::vision_predicate::VisionProgram::vk_hash`]
//!    (`canonical_predicate_vk` of the side's real vision program), not a fabricated
//!    tag. By the genuine lattice, two different `Custom` values are **incomparable**
//!    (`cell/src/permissions.rs::is_narrower_or_equal`: different vk_hashes are
//!    neither narrower nor equal) — so player A's vision authority is NOT an
//!    attenuation of a tile gated to player B, and [`is_attenuation`] refuses the
//!    projection. This is the structural refusal.
//! 2. **The vision frustum = the fetch allowlist.** A player's board-vision cap is
//!    [`SurfaceCapability::scoped`] to exactly the set of tile-origins its units
//!    currently illuminate (own tiles + tiles in range). The membrane intersects
//!    this with the board lineage ([`Membrane::project`]) and a per-tile rehydrate
//!    asks the REAL [`SurfaceCapability::may_fetch`]; a tile outside the frustum is
//!    not in the set, so the projection yields NOTHING — confinement before
//!    relation, the exact tooth `rehydrate.rs` runs.
//! 3. **The PROOF obligation — the `vk_hash` is EARNED** ([`VisionDeck::prove_can_view`],
//!    [`crate::vision_predicate`]). Axes 1-2 refuse a peek *structurally*, but on
//!    their own the `Custom { vk_hash }` is an inert identity tag — nobody has to
//!    *prove* anything to hold it. This axis closes that: the `vk_hash` names a real
//!    registered [`crate::vision_predicate::FogVisionVerifier`], and to project a
//!    side's tiles you must PRODUCE a proof the real
//!    [`crate::vision_predicate::WitnessedPredicateRegistry`] verifies — a genuine
//!    Ed25519 knowledge-of-secret over the canonical turn-bound message (the SAME
//!    registry the `dregg-turn` executor dispatches `Authorization::Custom`
//!    through). It is **fail-closed and EUF-CMA**: a player holding only its own
//!    side's secret literally cannot *construct* a verifying proof for the enemy's
//!    vision ([`VisionGateError::NoSecretForSide`]), and a forged proof is rejected
//!    by the real verifier. "Provably cannot peek" is now a real proof obligation,
//!    not lattice incomparability alone.
//!
//! A tile a player cannot see is therefore unreachable on ALL THREE axes: gated to
//! another player's incomparable `Custom` identity, absent from the viewer's frustum
//! allowlist, AND unprovable (no secret → no verifying proof). The KEYSTONE tests
//! `no_peek_a_player_cannot_rehydrate_an_enemy_tile` (axes 1-2) and
//! `no_peek_for_real_only_the_secret_holder_can_prove_vision` (axis 3)
//! drive a full-board enemy tile (carrying a hidden unit) through
//! [`Board::project_for`] / [`Board::prove_vision`] for the wrong player and assert
//! the result is empty / unprovable — provable no-peek. (See the `tests` module:
//! `no_peek_a_player_cannot_rehydrate_an_enemy_tile` and
//! `no_peek_for_real_only_the_secret_holder_can_prove_vision`.)
//!
//! ## What is real vs. the seam
//!
//! - **Real (the whole game logic):** the board, the tiles, the units, the moves,
//!   and the fog are all driven by the genuine cap primitives — moves are real
//!   [`CellAffordance`]s firing real [`dregg_turn::Effect`]s through the real
//!   `is_attenuation` gate; vision is the real lattice on the real
//!   [`SurfaceCapability`] axes; a snapshot is a real [`AffordanceSnapshot`]
//!   re-expanded through the real [`Membrane`] / [`rehydrate`].
//! - **The seam (inherited, named, not papered):** firing a move yields an
//!   [`AffordanceIntent`] carrying the REAL effect the executor would run; handing
//!   it to a live [`dregg_turn::TurnExecutor`] is the SAME boundary `affordance.rs`
//!   names (`## What is real vs. the seam`). The game advances its own board state
//!   from the intent (the move's effect is applied to the model), exactly as a
//!   `MockSurface` advances from a gated request; the gate that decides whether a
//!   move may fire AT ALL is the real `is_attenuation`, in-band.

use std::collections::{BTreeMap, BTreeSet};

use dregg_cell::is_attenuation;
use dregg_cell::AuthRequired;
use dregg_turn::Effect;
use dregg_types::CellId;

use crate::affordance::{AffordanceIntent, AffordanceSnapshot, AffordanceSurface, CellAffordance};
use crate::delegate::SurfaceCapability;
use crate::rehydrate::{InteractionLog, Membrane, Rehydration, Sturdyref};
use crate::web_of_cells::{DreggUri, WebOfCells};

/// Which side a player is on. A two-player skirmish; the side is the player's
/// identity for fog purposes (each side's vision is incomparable to the other's).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Side {
    /// The first player (Blue).
    Blue,
    /// The second player (Red).
    Red,
}

impl Side {
    /// The opposing side.
    pub fn opponent(self) -> Side {
        match self {
            Side::Blue => Side::Red,
            Side::Red => Side::Blue,
        }
    }

    /// A short label for narration.
    pub fn label(self) -> &'static str {
        match self {
            Side::Blue => "Blue",
            Side::Red => "Red",
        }
    }

    /// A stable byte tag for deriving this side's distinct cell / vk_hash.
    fn tag(self) -> u8 {
        match self {
            Side::Blue => 0xB1,
            Side::Red => 0xED,
        }
    }
}

/// A grid coordinate (row, column).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Coord {
    /// The row (0-based, top to bottom).
    pub row: u8,
    /// The column (0-based, left to right).
    pub col: u8,
}

impl Coord {
    /// A coordinate at `(row, col)`.
    pub fn new(row: u8, col: u8) -> Self {
        Coord { row, col }
    }

    /// The Chebyshev (king-move) distance to `other` — the vision/movement metric
    /// (a unit illuminates / can step to all tiles within a Chebyshev radius).
    pub fn chebyshev(self, other: Coord) -> u8 {
        let dr = (self.row as i16 - other.row as i16).unsigned_abs() as u8;
        let dc = (self.col as i16 - other.col as i16).unsigned_abs() as u8;
        dr.max(dc)
    }

    /// The `dregg://tile-<r>-<c>` origin string this tile is addressed by in the
    /// vision frustum (the fetch-allowlist member). The vision allowlist is a set
    /// of these — a player sees a tile iff this string is in its frustum.
    pub fn origin(self) -> String {
        format!("dregg://tile-{}-{}", self.row, self.col)
    }
}

/// A unit on the board — owned by a [`Side`], standing on a [`Coord`], with a
/// vision radius (how far it illuminates the fog) and a movement radius.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unit {
    /// The unit's stable id (its content-addressed cell — units are cells too).
    pub id: CellId,
    /// Which side owns it.
    pub side: Side,
    /// Where it stands.
    pub at: Coord,
    /// How far it sees (the Chebyshev radius it lifts the fog within).
    pub vision: u8,
    /// How far it can move in one turn (the Chebyshev radius a `move` affordance
    /// may step it to).
    pub movement: u8,
    /// A short call-sign for narration.
    pub name: String,
}

/// The result of trying to apply a move — kept as a typed value so the game's
/// state transition is explicit (the move's REAL effect, mirrored onto the model).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MoveOutcome {
    /// The move was applied: the unit relocated from `from` to `to`.
    Moved { unit: CellId, from: Coord, to: Coord },
    /// The move resolved as a capture: the mover took an enemy unit at `to`.
    Captured { mover: CellId, taken: CellId, at: Coord },
}

/// Why a move was rejected by the game rules (BEFORE the cap gate — these are the
/// game's own legality rules; an *unauthorized* move is refused separately by the
/// affordance gate as a [`crate::affordance::FireError`], which is the anti-cheat tooth).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IllegalMove {
    /// No unit of the moving side stands at the claimed origin.
    NoUnitThere,
    /// The destination is off the board.
    OffBoard,
    /// The destination is farther than the unit's movement radius.
    OutOfRange { allowed: u8, requested: u8 },
    /// The destination is occupied by a FRIENDLY unit (cannot stack).
    BlockedByFriendly,
    /// It is not this side's turn.
    NotYourTurn { whose: Side },
}

/// The board — a grid of tiles, the units on it, and whose turn it is. The shared
/// cell of the web-of-cells skirmish (`docs/deos/DEOS-APPS.md`: "the board a shared
/// cell"). The board owns the ground truth; each player only ever PROJECTS it
/// through their own vision cap.
#[derive(Clone, Debug)]
pub struct Board {
    /// Grid extent (rows).
    pub rows: u8,
    /// Grid extent (columns).
    pub cols: u8,
    /// The board's own backing cell (the shared cell).
    pub cell: CellId,
    /// Every unit on the board (the ground truth — never handed to a player whole).
    pub units: Vec<Unit>,
    /// Whose turn it is.
    pub turn: Side,
    /// The turn counter (advances each completed move).
    pub ply: u32,
}

/// A player's **vision** of the board — the slice their caps authorize, with the
/// fog applied. This is what a [`Board::project_for`] returns: the tiles the
/// player may see (each carrying its visible occupant, if any) + the count of
/// tiles hidden in fog. A tile the player cannot see is simply ABSENT — the
/// projection never even constructs it, because the membrane refused the rehydrate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlayerView {
    /// Which player this view is for.
    pub side: Side,
    /// The visible tiles, by coordinate. A coordinate ABSENT from this map is in
    /// fog for this player (provably un-projectable, not merely unrendered).
    pub visible: BTreeMap<Coord, TileView>,
    /// How many tiles are hidden in fog for this player (the board area minus the
    /// visible count) — a scalar confinement readout.
    pub fogged: usize,
    /// The liveness-type the projection rehydrated as (LIVE / REPLAYED / RECON),
    /// carried from the source context's witness-log exactly as a `rehydrate` does.
    pub liveness: Rehydration,
}

impl PlayerView {
    /// Can this player see the tile at `coord`? True iff it is in [`Self::visible`]
    /// — i.e. iff the membrane projected it (the player held the vision cap for it).
    pub fn can_see(&self, coord: Coord) -> bool {
        self.visible.contains_key(&coord)
    }

    /// The unit (if any) the player sees at `coord`. `None` if the tile is empty OR
    /// in fog — the player cannot distinguish "empty" from "fogged" beyond
    /// [`Self::can_see`] (which is the point: hidden enemy state is not leaked).
    pub fn unit_at(&self, coord: Coord) -> Option<&Unit> {
        self.visible.get(&coord).and_then(|t| t.occupant.as_ref())
    }

    /// The set of enemy units this player can currently see (the only enemy state
    /// fog ever reveals — units that wandered into a friendly unit's vision).
    pub fn visible_enemies(&self) -> Vec<&Unit> {
        self.visible
            .values()
            .filter_map(|t| t.occupant.as_ref())
            .filter(|u| u.side == self.side.opponent())
            .collect()
    }

    /// The set of coordinates visible to this player (sorted).
    pub fn visible_coords(&self) -> Vec<Coord> {
        self.visible.keys().copied().collect()
    }
}

/// A single tile as a player sees it — the coordinate + whatever occupant is on it.
/// Only ever constructed for tiles the player's cap authorized (so its mere
/// existence in a [`PlayerView`] witnesses the player was allowed to see it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TileView {
    /// Where the tile is.
    pub coord: Coord,
    /// The unit standing on it as the player sees it (`None` = the player sees an
    /// empty tile). A tile the player CANNOT see is absent from the `PlayerView`
    /// entirely, so this is never "a hidden enemy rendered as empty".
    pub occupant: Option<Unit>,
}

impl Board {
    /// A fresh board of `rows`×`cols` with the given units, Blue to move first. The
    /// board's backing cell is derived deterministically.
    pub fn new(rows: u8, cols: u8, board_cell: CellId, units: Vec<Unit>) -> Self {
        Board {
            rows,
            cols,
            cell: board_cell,
            units,
            turn: Side::Blue,
            ply: 0,
        }
    }

    /// Is `coord` on the board?
    pub fn in_bounds(&self, coord: Coord) -> bool {
        coord.row < self.rows && coord.col < self.cols
    }

    /// The unit standing at `coord` in ground truth (the board's own view — NOT a
    /// player projection; only the engine calls this).
    pub fn unit_at(&self, coord: Coord) -> Option<&Unit> {
        self.units.iter().find(|u| u.at == coord)
    }

    /// All units of `side` (ground truth).
    pub fn units_of(&self, side: Side) -> Vec<&Unit> {
        self.units.iter().filter(|u| u.side == side).collect()
    }

    /// **The vision frustum for `side`**: the set of tile-origin strings the side's
    /// units currently illuminate — every tile within any friendly unit's vision
    /// radius (Chebyshev). This is the fetch-allowlist a player's board-vision cap
    /// is scoped to: a player sees a tile IFF it is in this set. Derived from the
    /// live unit positions every time (vision moves with the units).
    pub fn frustum_for(&self, side: Side) -> BTreeSet<String> {
        let mut frustum = BTreeSet::new();
        for unit in self.units_of(side) {
            for row in 0..self.rows {
                for col in 0..self.cols {
                    let c = Coord::new(row, col);
                    if unit.at.chebyshev(c) <= unit.vision {
                        frustum.insert(c.origin());
                    }
                }
            }
        }
        frustum
    }

    /// **The board-vision capability a player of `side` holds.** This is the REAL
    /// [`SurfaceCapability`] the fog rides on, on BOTH axes:
    ///
    /// - **window rights** = [`AuthRequired::Custom`]`{ vk_hash }` derived from the
    ///   side (the player's distinct, incomparable identity — A's cap is not an
    ///   attenuation of anything gated to B);
    /// - **fetch allowlist** = the side's current [`Self::frustum_for`] (the tiles
    ///   its units illuminate) — the vision frustum.
    ///
    /// The cap is bound to the board cell. A player projects the board THROUGH this
    /// cap; the membrane's `is_attenuation` + `may_fetch` then decide every tile.
    pub fn vision_cap_for(&self, side: Side) -> SurfaceCapability {
        SurfaceCapability::scoped(
            self.cell,
            side_rights(side),
            self.frustum_for(side),
            [],
        )
    }

    /// The board's **vision lineage** — the publisher's authority the board surface
    /// is a certified projection of, for a given viewer `side`. It carries the
    /// side's own `Custom { vk_hash }` window rights (so a viewer of that side
    /// projects a non-empty meet) and the side's frustum as the lineage reach. The
    /// membrane meets a viewer's held vision cap against THIS, so a viewer can never
    /// see beyond what the board would project for their side. (The board is the
    /// authority root; the lineage is its per-side facet.)
    pub fn vision_lineage_for(&self, side: Side) -> SurfaceCapability {
        // The lineage permits the side's full frustum under the side's identity; a
        // viewer's held cap (also the side's identity, possibly a narrower frustum)
        // meets to ≤ this. Using the SAME side identity keeps the meet non-empty for
        // the right player and empty (incomparable) for the wrong one.
        self.vision_cap_for(side)
    }

    /// **Project the board for `side`** — apply the fog. Returns the [`PlayerView`]:
    /// exactly the tiles `side`'s vision cap authorizes, each with its visible
    /// occupant. This is THE fog-of-war operation, and it is a cap-confinement, not
    /// a flag: each candidate tile is admitted IFF the side's vision cap (via the
    /// REAL [`is_attenuation`] on the window-rights axis AND the REAL
    /// [`SurfaceCapability::may_fetch`] on the frustum axis) authorizes it. A tile
    /// the side cannot see is never constructed — the membrane refused it.
    ///
    /// The `liveness` is the rehydration liveness-type the projection carries
    /// (LIVE / REPLAYED / RECON), DERIVED from the witness-log of the source
    /// context exactly as a `rehydrate` does.
    pub fn project_for(&self, side: Side, liveness: Rehydration) -> PlayerView {
        let vision = self.vision_cap_for(side);
        let mut visible = BTreeMap::new();

        for row in 0..self.rows {
            for col in 0..self.cols {
                let coord = Coord::new(row, col);
                // THE GATE — both axes, both REAL:
                //  (a) the player's identity must authorize the tile's vision
                //      requirement (window rights, the REAL is_attenuation). The
                //      tile's requirement is the side's own identity (a friendly
                //      tile) — a viewer of the WRONG side is incomparable, refused.
                //  (b) the tile-origin must be in the player's vision frustum (the
                //      REAL may_fetch over the fetch-allowlist).
                let tile_requirement = side_rights(side); // the tile is gated to THIS side's view
                let identity_ok = is_attenuation(&vision.window.rights, &tile_requirement);
                let frustum_ok = vision.may_fetch(&coord.origin());
                if identity_ok && frustum_ok {
                    visible.insert(
                        coord,
                        TileView {
                            coord,
                            occupant: self.unit_at(coord).cloned(),
                        },
                    );
                }
            }
        }

        let area = self.rows as usize * self.cols as usize;
        let fogged = area.saturating_sub(visible.len());
        PlayerView {
            side,
            visible,
            fogged,
            liveness,
        }
    }

    /// **Can `viewer` rehydrate the tile at `coord`?** — the per-tile no-peek check,
    /// run through the REAL [`Membrane`]. `viewer_side` is the membrane the request
    /// comes through; `tile_owner_side` is the side the tile's vision is gated to.
    /// Returns `true` only if the membrane would project that tile to the viewer:
    /// the viewer's vision cap must (a) be an `is_attenuation` of the tile's
    /// owner-side identity AND (b) carry the tile's origin in its frustum. A viewer
    /// asking for a tile gated to the OTHER side is refused on the identity axis
    /// (incomparable `Custom`), regardless of frustum — provable no-peek.
    ///
    /// This routes through the genuine [`Membrane::project`]: it meets the viewer's
    /// held vision cap against the tile-owner's lineage; an incomparable meet is
    /// [`crate::rehydrate::RehydrateError::Amplification`] (no projection), which we
    /// surface as `false`.
    pub fn can_rehydrate_tile(
        &self,
        viewer_side: Side,
        tile_owner_side: Side,
        coord: Coord,
    ) -> bool {
        let viewer_cap = self.vision_cap_for(viewer_side);
        let membrane = Membrane::new(viewer_cap);
        // The lineage is the tile-owner side's vision facet (gated to that side's
        // identity, permitting that side's frustum).
        let lineage = self.vision_lineage_for(tile_owner_side);
        match membrane.project(&lineage) {
            // The meet exists: the viewer's identity is comparable to the tile
            // owner's (same side). It still must carry the tile in its frustum.
            Ok(projected) => projected.may_fetch(&coord.origin()),
            // Incomparable identities (different sides) → no projection at all. The
            // cross-player peek is refused at the cap lattice — the keystone.
            Err(_) => false,
        }
    }

    /// **The affordance surface of moves for `side`** — the cap-gated, verified-turn
    /// move templates. Each legal move a unit could make is a [`CellAffordance`]
    /// named `move:<unit>:<r>-<c>`, requiring the side's identity ([`side_rights`]),
    /// firing a REAL [`Effect::SetField`] that records the unit's new position into
    /// the board cell's state (the genuine turn the executor would run). An ENEMY
    /// cannot fire these (their identity is incomparable to the required rights) —
    /// anti-cheat is the affordance gate, not a separate check.
    ///
    /// Only legal moves are declared (in-range, on-board, not blocked by a friendly)
    /// — but legality is the GAME rule; the cap gate is the *authority* rule. Both
    /// must pass: a move must be (1) declared (legal) AND (2) fired with the owning
    /// side's authority (authorized).
    pub fn move_surface_for(&self, side: Side) -> AffordanceSurface {
        let mut surface = AffordanceSurface::new(self.cell);
        for (i, unit) in self.units.iter().enumerate() {
            if unit.side != side {
                continue;
            }
            for row in 0..self.rows {
                for col in 0..self.cols {
                    let dest = Coord::new(row, col);
                    if !self.is_legal_move(unit, dest) {
                        continue;
                    }
                    // The move records the unit's new position into the board cell
                    // state at the unit's slot (a REAL SetField turn). Slot = the
                    // unit's index; value = the packed destination coordinate.
                    let effect = Effect::SetField {
                        cell: self.cell,
                        index: i,
                        value: pack_coord(dest),
                    };
                    surface = surface.declare(CellAffordance::new(
                        move_name(&unit.name, dest),
                        side_rights(side),
                        effect,
                    ));
                }
            }
        }
        surface
    }

    /// Is moving `unit` to `dest` legal under the GAME rules (not the cap gate)?
    /// On-board, within movement range, and not landing on a friendly. Landing on
    /// an enemy is a legal capture.
    pub fn is_legal_move(&self, unit: &Unit, dest: Coord) -> bool {
        self.check_move(unit, dest).is_ok()
    }

    /// The detailed legality check (so the executor can report WHY a move is
    /// illegal). Returns `Ok(())` if legal, else the [`IllegalMove`] reason.
    pub fn check_move(&self, unit: &Unit, dest: Coord) -> Result<(), IllegalMove> {
        if self.turn != unit.side {
            return Err(IllegalMove::NotYourTurn { whose: self.turn });
        }
        if !self.in_bounds(dest) {
            return Err(IllegalMove::OffBoard);
        }
        if dest == unit.at {
            // A no-op "move" to the same tile is out of range (distance 0 is not a
            // move). Treat as out of range to keep moves real relocations.
            return Err(IllegalMove::OutOfRange {
                allowed: unit.movement,
                requested: 0,
            });
        }
        let dist = unit.at.chebyshev(dest);
        if dist > unit.movement {
            return Err(IllegalMove::OutOfRange {
                allowed: unit.movement,
                requested: dist,
            });
        }
        if let Some(occ) = self.unit_at(dest) {
            if occ.side == unit.side {
                return Err(IllegalMove::BlockedByFriendly);
            }
            // An enemy occupant → a legal capture.
        }
        Ok(())
    }

    /// **Apply a fired move intent to the board** — the state transition. The intent
    /// was already authorized by the affordance gate (it only exists because
    /// [`AffordanceSurface::fire`] passed the REAL `is_attenuation`); here the game
    /// mirrors the move's REAL effect onto its own model (relocate the unit, resolve
    /// a capture), advances the ply, and passes the turn. Returns the
    /// [`MoveOutcome`], or an [`IllegalMove`] if the move violated a GAME rule
    /// (defense in depth: the surface only declares legal moves, but we re-check so
    /// a hand-built intent cannot smuggle an illegal one past the rules).
    ///
    /// `mover_side` is the side that fired (the intent's authority). The unit to
    /// move is identified by the intent's effect slot (the unit index) — the SAME
    /// slot the move affordance wrote.
    pub fn apply_move(
        &mut self,
        intent: &AffordanceIntent,
        mover_side: Side,
    ) -> Result<MoveOutcome, IllegalMove> {
        // Decode the move from the REAL effect the intent carries (the SetField the
        // affordance fired): the slot is the unit index, the value is the packed
        // destination.
        let (unit_index, dest) = match &intent.effect {
            Effect::SetField { index, value, .. } => (*index, unpack_coord(value)),
            // The move surface only ever fires SetField; any other effect is not a
            // move (treated as no unit there).
            _ => return Err(IllegalMove::NoUnitThere),
        };
        let unit = self
            .units
            .get(unit_index)
            .cloned()
            .ok_or(IllegalMove::NoUnitThere)?;
        // The firer must own the unit it is moving (authority ⟂ ownership). The
        // affordance gate already bound the side; this re-binds it to the unit.
        if unit.side != mover_side {
            return Err(IllegalMove::NoUnitThere);
        }
        // Re-check the move under the game rules (defense in depth).
        self.check_move(&unit, dest)?;

        let from = unit.at;
        // Resolve a capture: if an enemy stands on the destination, remove it.
        let captured = self.unit_at(dest).map(|u| u.id);
        if let Some(taken_id) = captured {
            self.units.retain(|u| u.id != taken_id);
            // Recompute the mover's index after the removal (the vector shifted).
            let mover_pos = self
                .units
                .iter()
                .position(|u| u.id == unit.id)
                .ok_or(IllegalMove::NoUnitThere)?;
            self.units[mover_pos].at = dest;
            self.ply += 1;
            self.turn = self.turn.opponent();
            return Ok(MoveOutcome::Captured {
                mover: unit.id,
                taken: taken_id,
                at: dest,
            });
        }

        // A plain relocation.
        let mover_pos = self
            .units
            .iter()
            .position(|u| u.id == unit.id)
            .ok_or(IllegalMove::NoUnitThere)?;
        self.units[mover_pos].at = dest;
        self.ply += 1;
        self.turn = self.turn.opponent();
        Ok(MoveOutcome::Moved {
            unit: unit.id,
            from,
            to: dest,
        })
    }

    /// **Take a fog-respecting frustum-snapshot for a spectator of `side`.** The
    /// snapshot is a real [`AffordanceSnapshot`] over the board surface, embedding a
    /// [`Sturdyref`] whose lineage is the spectator's vision facet — so when the
    /// spectator rehydrates it, they re-expand ONLY the moves/tiles their
    /// spectator-cap authorizes (the same fog), and the [`Rehydration`] liveness-type
    /// tells them live-vs-replay. `web` is the published web-of-cells the board
    /// surface lives in; `board_uri` is the board cell's `dregg://` ref.
    ///
    /// A spectator is just a viewer with a (possibly attenuated) vision cap; the
    /// snapshot respects their fog for free because rehydration runs the SAME
    /// membrane projection [`Self::project_for`] does. A spectator gated to Blue's
    /// view rehydrating the snapshot CANNOT re-expand Red's hidden tiles — the
    /// no-peek property carries into spectating.
    pub fn snapshot_for(
        &self,
        side: Side,
        board_uri: DreggUri,
        witness_log: InteractionLog,
        sources_reachable: bool,
    ) -> AffordanceSnapshot {
        let surface = self.move_surface_for(side);
        let lineage = self.vision_lineage_for(side);
        let sturdyref = Sturdyref::new(board_uri, lineage, witness_log, sources_reachable);
        AffordanceSnapshot::take(&surface, sturdyref)
    }

    /// **The PROOF-BACKED no-peek gate** — the third, load-bearing axis. The lattice
    /// (`is_attenuation` on incomparable `Custom` identities) and the frustum
    /// (`may_fetch`) refuse a cross-player peek *structurally*; this axis makes the
    /// `Custom { vk_hash }` **earned**: to project a tile gated to `tile_owner`'s
    /// vision, `viewer` must PRODUCE a vision proof the registry VERIFIES for that
    /// side's `vk_hash` — a genuine knowledge-of-secret obligation
    /// ([`crate::vision_predicate`]), fail-closed.
    ///
    /// `deck` carries the per-side vision programs + the registry + whichever
    /// secrets the caller holds. `viewer` can pass IFF `deck` lets it produce a
    /// proof for `tile_owner`'s program that the registry accepts — i.e. IFF the
    /// caller holds `tile_owner`'s vision secret (so a player holds only its OWN
    /// side's secret, and the enemy's tiles are unprovable to it). `signing_message`
    /// is the canonical turn-bound message the proof commits to (the executor builds
    /// this for `Authorization::Custom`; the game supplies a representative one via
    /// [`Self::vision_signing_message`]).
    ///
    /// Returns `Ok(())` on a verifying proof, or the [`crate::vision_predicate`]
    /// rejection (no secret → cannot produce → refused). This is the genuine version
    /// of "provably cannot peek": not lattice incomparability alone, a real proof.
    pub fn prove_vision(
        &self,
        deck: &VisionDeck,
        viewer: Side,
        tile_owner: Side,
        signing_message: &[u8],
    ) -> Result<(), VisionGateError> {
        deck.prove_can_view(viewer, tile_owner, signing_message)
    }

    /// The canonical turn-bound signing message a vision proof commits to, for
    /// `viewer` projecting `tile`'s region at the current ply. Binds the board cell,
    /// the viewer side, the tile, and the ply — so a proof authorizes THIS look at
    /// THIS turn (the replay binding the executor's `compute_custom_signing_message`
    /// provides for real). A representative stand-in for the executor-built message.
    pub fn vision_signing_message(&self, viewer: Side, tile: Coord) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"dregg-fogwar-vision-look-v1");
        msg.extend_from_slice(&self.cell.0);
        msg.push(viewer.tag());
        msg.push(tile.row);
        msg.push(tile.col);
        msg.extend_from_slice(&self.ply.to_le_bytes());
        msg
    }
}

/// **The vision deck** — the game's PROOF-BACKED vision authority context. It binds
/// each [`Side`] to its real [`crate::vision_predicate::VisionProgram`] (hence its
/// genuine `vk_hash`), registers each side's verifier in a real
/// [`crate::vision_predicate::WitnessedPredicateRegistry`], and holds whichever
/// side **secrets** the local player possesses (a producer per held side).
///
/// This is what makes a side's `Custom { vk_hash }` **earned**, not inert: a player
/// can pass [`Self::prove_can_view`] / fire a move for a side IFF the deck can
/// produce a vision proof the registry verifies for that side — i.e. IFF it holds
/// that side's secret. A player constructed with only its OWN side's keypair
/// therefore cannot prove the enemy's vision (no-peek, as a real proof obligation),
/// while a validator/auditor holding only the public programs can still VERIFY any
/// proof presented (the asymmetry the whole design rides on).
#[derive(Clone)]
pub struct VisionDeck {
    /// Each side's public vision program (its bound public key + the derived
    /// `vk_hash`). Public — anyone can verify against these.
    programs: std::collections::BTreeMap<Side, crate::vision_predicate::VisionProgram>,
    /// The real witnessed-predicate registry, with each side's verifier registered
    /// under its `vk_hash`. The SAME registry the executor dispatches
    /// `Authorization::Custom` through.
    registry: crate::vision_predicate::WitnessedPredicateRegistry,
    /// The side SECRETS the local player holds, as producers (keyed by side). A
    /// player holds only its own side here; an all-seeing referee could hold both.
    producers: std::collections::BTreeMap<Side, crate::vision_predicate::FogVisionProducer>,
}

/// Why a proof-backed vision gate ([`VisionDeck::prove_can_view`]) refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VisionGateError {
    /// The local player does not hold the secret for the side whose tile it tried to
    /// view — it cannot PRODUCE a vision proof for that side. THE no-peek refusal:
    /// the enemy's vision is unprovable to you.
    NoSecretForSide { side: Side },
    /// A proof was produced but the registry's verifier REJECTED it (forged / wrong
    /// key / wrong message). Fail-closed at the real Ed25519 check.
    ProofRejected { reason: String },
    /// The producer could not synthesize a proof (binding mismatch).
    ProducerFailed { reason: String },
}

impl VisionDeck {
    /// Build a vision deck for a set of sides, deriving each side's keypair
    /// deterministically from `secret_seed(side)` and registering its verifier. The
    /// returned deck holds the secrets for exactly `held_sides` (the local player's
    /// own side(s)); it can VERIFY any side's proof but can only PRODUCE for the held
    /// ones. `all_sides` is every side whose program/verifier must be registered
    /// (so the gate can verify the enemy's program too).
    pub fn new(all_sides: &[Side], held_sides: &[Side]) -> Self {
        let mut programs = std::collections::BTreeMap::new();
        let mut registry = crate::vision_predicate::WitnessedPredicateRegistry::empty();
        for &side in all_sides {
            let keypair = Self::keypair_for(side);
            let program = keypair.program();
            crate::vision_predicate::register_vision_verifier(&mut registry, &program);
            programs.insert(side, program);
        }
        let mut producers = std::collections::BTreeMap::new();
        for &side in held_sides {
            producers.insert(
                side,
                crate::vision_predicate::FogVisionProducer::new(Self::keypair_for(side)),
            );
        }
        VisionDeck {
            programs,
            registry,
            producers,
        }
    }

    /// A deck for a single local player on `side` in a two-sided skirmish (it holds
    /// only `side`'s secret; both sides' verifiers are registered).
    pub fn for_player(side: Side) -> Self {
        Self::new(&[Side::Blue, Side::Red], &[side])
    }

    /// A referee deck holding BOTH sides' secrets (an all-seeing spectator / the
    /// engine) — can prove any side's vision. Use for tests/demos that need to drive
    /// both players' proofs.
    pub fn referee() -> Self {
        Self::new(&[Side::Blue, Side::Red], &[Side::Blue, Side::Red])
    }

    /// The deterministic vision keypair for `side` (its secret material). In
    /// production each player mints its own secret; here it is derived from a
    /// per-side seed so the demo/tests are reproducible.
    pub fn keypair_for(side: Side) -> crate::vision_predicate::VisionKeypair {
        let mut seed = [0u8; 32];
        seed[0] = side.tag();
        seed[1] = side.tag().rotate_left(3);
        seed[31] = side.tag().wrapping_mul(7);
        crate::vision_predicate::VisionKeypair::from_seed(seed)
    }

    /// The genuine `vk_hash` for `side` (= `canonical_predicate_vk` of its vision
    /// program). THIS is the real value [`side_rights`] should carry — a hash of a
    /// real predicate program, re-derivable by any validator.
    pub fn vk_hash_for(side: Side) -> [u8; 32] {
        Self::keypair_for(side).program().vk_hash()
    }

    /// The real witnessed-predicate registry (with every side's verifier). Hand this
    /// to an executor and a `Custom { vk_hash }` authorization for any side dispatches
    /// to its genuine vision verifier.
    pub fn registry(&self) -> &crate::vision_predicate::WitnessedPredicateRegistry {
        &self.registry
    }

    /// `side`'s public vision program (if registered).
    pub fn program(&self, side: Side) -> Option<&crate::vision_predicate::VisionProgram> {
        self.programs.get(&side)
    }

    /// **The proof-backed gate.** Can `viewer` (the local player) view a tile gated
    /// to `tile_owner`'s vision? `Ok(())` IFF the deck holds `tile_owner`'s secret
    /// AND the proof it produces VERIFIES through the registry. A player holding only
    /// its own side's secret gets `NoSecretForSide` for the enemy — the genuine
    /// no-peek (it cannot even construct a verifying proof for the enemy's vision).
    ///
    /// The flow is the real producer⊣verifier round-trip against the real registry:
    /// produce a proof for `tile_owner`'s program over `signing_message`, then verify
    /// it through `registry.verify` (the SAME path the executor runs).
    pub fn prove_can_view(
        &self,
        viewer: Side,
        tile_owner: Side,
        signing_message: &[u8],
    ) -> Result<(), VisionGateError> {
        // A player proves its OWN side's vision. Viewing a tile gated to `tile_owner`
        // requires holding `tile_owner`'s secret. The local player holds only its own
        // side(s) — so for the enemy's tile it has no producer → cannot prove → NO
        // PEEK. (`viewer` is recorded for the message binding; the secret it must
        // hold is `tile_owner`'s.)
        let _ = viewer;
        let producer = self
            .producers
            .get(&tile_owner)
            .ok_or(VisionGateError::NoSecretForSide { side: tile_owner })?;
        let program = self
            .programs
            .get(&tile_owner)
            .ok_or(VisionGateError::NoSecretForSide { side: tile_owner })?;

        // Produce the genuine proof (Ed25519 over the signing message) for the
        // tile-owner's vision program — only possible because we hold the secret.
        let input = crate::vision_predicate::PredicateInput::SigningMessage(signing_message);
        let proof = {
            use crate::vision_predicate::WitnessProducer;
            producer
                .produce(&program.commitment(), &input, &[])
                .map_err(|e| VisionGateError::ProducerFailed {
                    reason: e.to_string(),
                })?
        };

        // Verify it through the REAL registry (the executor's dispatch path).
        let wp = program.witnessed_predicate(0);
        crate::vision_predicate::verify_vision_proof(&self.registry, &wp, signing_message, &proof)
            .map_err(|e| VisionGateError::ProofRejected {
                reason: e.to_string(),
            })
    }

    /// Verify a vision proof someone ELSE produced (the validator path) — no secret
    /// needed, only the public registry. Returns `Ok(())` iff the proof verifies for
    /// `tile_owner`'s registered program over `signing_message`. This is how a
    /// referee / light client checks a player's claimed look without holding any
    /// secret (the asymmetry: verify-with-public, produce-with-secret).
    pub fn verify_presented_proof(
        &self,
        tile_owner: Side,
        signing_message: &[u8],
        proof_bytes: &[u8],
    ) -> Result<(), VisionGateError> {
        let program = self
            .programs
            .get(&tile_owner)
            .ok_or(VisionGateError::NoSecretForSide { side: tile_owner })?;
        let wp = program.witnessed_predicate(0);
        crate::vision_predicate::verify_vision_proof(
            &self.registry,
            &wp,
            signing_message,
            proof_bytes,
        )
        .map_err(|e| VisionGateError::ProofRejected {
            reason: e.to_string(),
        })
    }
}

/// **An AI agent player** — a first-class user that fires the SAME cap-gated move
/// affordances as a human (`docs/deos/DEOS-APPS.md`: "AI opponents/allies are
/// first-class users firing the same affordances, attenuated by the same caps").
/// The agent holds a side identity ([`Self::vision_cap`] over the board) and a
/// simple policy; its action space IS its attenuated affordance set — it can only
/// ever fire moves its caps authorize, so it is confined to legal+authorized play
/// by construction (it cannot cheat any more than a human can).
#[derive(Clone, Debug)]
pub struct AgentPlayer {
    /// The side this agent plays.
    pub side: Side,
    /// The agent's cell identity (it is a cell, like any player).
    pub cell: CellId,
}

impl AgentPlayer {
    /// An agent playing `side` from cell `cell`.
    pub fn new(side: Side, cell: CellId) -> Self {
        AgentPlayer { side, cell }
    }

    /// The agent's held vision/authority cap — the SAME [`Board::vision_cap_for`] a
    /// human of this side holds. The agent is no more privileged than a human; it
    /// projects the board through this and acts only within it.
    pub fn vision_cap(&self, board: &Board) -> SurfaceCapability {
        board.vision_cap_for(self.side)
    }

    /// **Choose and fire a move** through the cap-gated affordance surface — the
    /// agentic turn. The policy: among the moves the agent's caps authorize (it
    /// projects the move surface for its own side, so it only ever SEES its own
    /// legal moves), prefer the move that captures a visible enemy; else step the
    /// first unit toward the nearest visible enemy; else the first available legal
    /// move. Returns the fired [`AffordanceIntent`] (carrying the REAL effect) — or
    /// `None` if the agent has no legal move (it passes).
    ///
    /// Crucially the agent FIRES through [`AffordanceSurface::fire`] with its own
    /// side authority, so the move it returns was admitted by the REAL
    /// `is_attenuation` gate — the agent's "AI" cannot route around the cap
    /// discipline. An agent that tried to fire an enemy unit's move would be
    /// [`FireError::Unauthorized`], identical to a human cheating.
    pub fn choose_move(&self, board: &Board) -> Option<AffordanceIntent> {
        if board.turn != self.side {
            return None; // not the agent's turn
        }
        let surface = board.move_surface_for(self.side);
        let held = self.vision_cap(board);
        // The agent's authorized action space: the moves it may fire (project_for is
        // the SAME gate the fog uses). Each `name` is move:<unit>:<r>-<c>.
        let candidates = surface.project_for(&held);
        if candidates.is_empty() {
            return None;
        }

        // What enemies can the agent SEE (fog applies to the agent too)?
        let view = board.project_for(self.side, Rehydration::Live);
        let visible_enemies: Vec<Coord> = view.visible_enemies().iter().map(|u| u.at).collect();

        // (1) Prefer a capture: a candidate whose destination is a visible enemy.
        if !visible_enemies.is_empty() {
            // Find a candidate move landing on a visible enemy tile.
            for cand in &candidates {
                if let Some(dest) = dest_of_move(&cand.name) {
                    if visible_enemies.contains(&dest) {
                        // Fire it (through the REAL gate, with the agent's authority).
                        return surface.fire(&cand.name, self.cell, &held).ok();
                    }
                }
            }
            // (2) Else step toward the nearest visible enemy: pick the candidate
            //     minimizing Chebyshev distance to any visible enemy.
            let best = candidates
                .iter()
                .filter_map(|c| dest_of_move(&c.name).map(|d| (c, d)))
                .min_by_key(|(_, d)| {
                    visible_enemies
                        .iter()
                        .map(|e| d.chebyshev(*e))
                        .min()
                        .unwrap_or(u8::MAX)
                });
            if let Some((cand, _)) = best {
                return surface.fire(&cand.name, self.cell, &held).ok();
            }
        }

        // (3) Else just take the first authorized legal move.
        let first = &candidates[0];
        surface.fire(&first.name, self.cell, &held).ok()
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// helpers — deriving the per-side identity, packing coords into a field element,
// and the move-name encoding. All over the REAL types (no parallel model).
// ──────────────────────────────────────────────────────────────────────────────

/// The window-rights identity of a [`Side`]: [`AuthRequired::Custom`]`{ vk_hash }`
/// where the `vk_hash` is the side's **GENUINE** vision-predicate hash —
/// [`VisionDeck::vk_hash_for`] = `canonical_predicate_vk` of the side's real vision
/// program (its bound Ed25519 public key), re-derivable by any validator. This is
/// the load-bearing fix over the earlier inert tag: the same `vk_hash` now (a) makes
/// the two sides INCOMPARABLE on the lattice (`cell/src/permissions.rs`: different
/// `Custom` vk_hashes neither attenuate) — the structural fog refusal — AND (b)
/// names a real registered verifier ([`crate::vision_predicate`]), so passing the
/// gate requires PRODUCING a proof the registry verifies ([`VisionDeck::prove_can_view`]).
///
/// Two axes, one genuine `vk_hash`: the lattice refuses the enemy's tile
/// *structurally*, and the proof obligation makes a side's authority *earned*
/// (only the secret-holder can prove it). Fog-of-war is no longer "your identity
/// does not attenuate the enemy's tile gate" alone — it is "you cannot even PROVE
/// the enemy's vision."
pub fn side_rights(side: Side) -> AuthRequired {
    AuthRequired::Custom {
        vk_hash: VisionDeck::vk_hash_for(side),
    }
}

/// Pack a [`Coord`] into a field element ([u8; 32]) — the value a move's REAL
/// `SetField` writes into the board cell state (the unit's new position). Stored in
/// the first two bytes (row, col) with a domain tag, so [`unpack_coord`] inverts it.
fn pack_coord(coord: Coord) -> [u8; 32] {
    let mut v = [0u8; 32];
    v[0] = coord.row;
    v[1] = coord.col;
    v[2] = 0xC0; // a domain tag marking this as a packed coordinate
    v
}

/// Invert [`pack_coord`] — read the destination back out of a move's field value.
fn unpack_coord(value: &[u8; 32]) -> Coord {
    Coord::new(value[0], value[1])
}

/// The canonical name of a move affordance: `move:<unit>:<r>-<c>`.
fn move_name(unit_name: &str, dest: Coord) -> String {
    format!("move:{}:{}-{}", unit_name, dest.row, dest.col)
}

/// Parse the destination coordinate out of a `move:<unit>:<r>-<c>` affordance name.
fn dest_of_move(name: &str) -> Option<Coord> {
    let rc = name.rsplit(':').next()?; // "<r>-<c>"
    let mut parts = rc.split('-');
    let r: u8 = parts.next()?.parse().ok()?;
    let c: u8 = parts.next()?.parse().ok()?;
    Some(Coord::new(r, c))
}

/// Derive a deterministic [`CellId`] for a named game object (a unit, a player, the
/// board) from a tag + seed — so units/players/board are addressable cells.
pub fn game_cell(tag: u8, seed: u8) -> CellId {
    let mut k = [0u8; 32];
    k[0] = tag;
    k[1] = seed;
    CellId::derive_raw(&k, &[0u8; 32])
}

/// Build the canonical demo skirmish: a 5×5 board with two Blue units and two Red
/// units placed at opposite corners, vision radius 1, movement radius 2. Returns
/// `(board, board_uri, web)` with the board surface published into a real
/// [`WebOfCells`] (so snapshots have a live ref to rehydrate). The corners are far
/// enough apart that NEITHER side can initially see the other (the opening fog).
pub fn demo_skirmish() -> (Board, DreggUri, WebOfCells) {
    let board_cell = game_cell(0xB0, 0);
    let units = vec![
        Unit {
            id: game_cell(0xB1, 1),
            side: Side::Blue,
            at: Coord::new(0, 0),
            vision: 1,
            movement: 2,
            name: "B-scout".to_string(),
        },
        Unit {
            id: game_cell(0xB1, 2),
            side: Side::Blue,
            at: Coord::new(1, 0),
            vision: 1,
            movement: 2,
            name: "B-guard".to_string(),
        },
        Unit {
            id: game_cell(0xED, 1),
            side: Side::Red,
            at: Coord::new(4, 4),
            vision: 1,
            movement: 2,
            name: "R-scout".to_string(),
        },
        Unit {
            id: game_cell(0xED, 2),
            side: Side::Red,
            at: Coord::new(3, 4),
            vision: 1,
            movement: 2,
            name: "R-guard".to_string(),
        },
    ];
    let board = Board::new(5, 5, board_cell, units);

    // Publish the board surface into a real web-of-cells so a snapshot's sturdyref
    // has a live ref to rehydrate through (the board cell is the dregg:// origin).
    let mut web = WebOfCells::new(3);
    let board_uri = web.publish(0xB0, b"<h1>fog-of-war skirmish board</h1>", "dregg://board");
    // The board's logical cell and the published cell are both real CellIds; for the
    // snapshot/rehydrate path we use the PUBLISHED uri (it is the one the web-of-cells
    // can fetch). The board's own `cell` is used for the affordance/vision surfaces.
    (board, board_uri, web)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affordance::FireError;
    use crate::rehydrate::InteractionLog;

    fn small_board() -> Board {
        // A 5×5 board: Blue at the top-left corner, Red at the bottom-right. Vision
        // radius 1 → at the start neither can see the other (they are 4 apart).
        let (board, _uri, _web) = demo_skirmish();
        board
    }

    // ── The KEYSTONE: provable no-peek. A player cannot rehydrate an enemy tile. ──

    #[test]
    fn no_peek_a_player_cannot_rehydrate_an_enemy_tile() {
        // THE fog-of-war confinement theorem: a tile carrying a hidden enemy unit,
        // gated to the ENEMY's vision identity, is NOT projectable by the other
        // player — the membrane refuses it on the incomparable-Custom identity axis,
        // regardless of anything else. This is the security property nothing else
        // can offer: not a client-side visibility flag, a cap-confinement.
        let board = small_board();

        // Red's scout sits at (4,4) — a tile gated to RED's vision. Blue tries to
        // rehydrate it through Blue's membrane.
        let enemy_tile = Coord::new(4, 4);
        assert!(
            board.unit_at(enemy_tile).is_some(),
            "ground truth: an enemy unit IS on that tile"
        );

        // Blue CANNOT rehydrate the enemy-gated tile — the cross-player peek is
        // refused at the cap lattice (Blue's Custom identity ⟂ Red's).
        assert!(
            !board.can_rehydrate_tile(Side::Blue, Side::Red, enemy_tile),
            "no-peek: Blue must NOT be able to rehydrate a tile gated to Red"
        );
        // And symmetrically Red cannot peek Blue's home tile.
        let blue_home = Coord::new(0, 0);
        assert!(
            !board.can_rehydrate_tile(Side::Red, Side::Blue, blue_home),
            "no-peek: Red must NOT be able to rehydrate a tile gated to Blue"
        );

        // The refusal is the REAL is_attenuation: Blue's identity is not an
        // attenuation of Red's tile gate (incomparable Custom vk_hashes).
        assert!(
            !is_attenuation(&side_rights(Side::Blue), &side_rights(Side::Red)),
            "the no-peek root cause: Blue's Custom identity ⟂ Red's (neither attenuates)"
        );

        // The projection itself: the enemy tile is ABSENT from Blue's view (the
        // membrane never constructed it — confinement before relation).
        let blue_view = board.project_for(Side::Blue, Rehydration::Live);
        assert!(
            !blue_view.can_see(enemy_tile),
            "the enemy tile is not in Blue's projected view at all"
        );
        assert!(
            blue_view.unit_at(enemy_tile).is_none(),
            "Blue sees NOTHING at the enemy tile — not even 'occupied'"
        );
        // Blue sees no enemies at the opening (full fog between the corners).
        assert!(
            blue_view.visible_enemies().is_empty(),
            "at the opening, the enemy is fully fogged"
        );
    }

    #[test]
    fn a_player_can_rehydrate_its_own_tiles() {
        // The other polarity: a player CAN rehydrate the tiles within its own
        // frustum (its identity attenuates its own tile gate AND the tile is in its
        // frustum). Fog hides the enemy, not yourself.
        let board = small_board();
        let blue_home = Coord::new(0, 0);
        assert!(
            board.can_rehydrate_tile(Side::Blue, Side::Blue, blue_home),
            "a player CAN rehydrate its own occupied tile"
        );
        let blue_view = board.project_for(Side::Blue, Rehydration::Live);
        assert!(blue_view.can_see(blue_home), "Blue sees its own home tile");
        assert!(
            blue_view.unit_at(blue_home).is_some(),
            "Blue sees its own unit on its home tile"
        );
        // Blue sees a non-empty but STRICTLY-FOGGED board (it cannot see the whole
        // 5×5 — most tiles are dark).
        assert!(blue_view.fogged > 0, "most of the board is fog for Blue");
        assert!(
            blue_view.visible.len() < (board.rows as usize * board.cols as usize),
            "Blue's view is a strict sub-board, not the whole grid"
        );
    }

    // ── Per-viewer vision DIVERGENCE: the two players see different boards. ──

    #[test]
    fn two_players_see_genuinely_different_boards() {
        // The deos property: Blue and Red project the SAME board to DIFFERENT
        // views — each sees only its own frustum. Their visible-tile sets are
        // disjoint at the opening (the corners don't overlap in vision).
        let board = small_board();
        let blue = board.project_for(Side::Blue, Rehydration::Live);
        let red = board.project_for(Side::Red, Rehydration::Live);

        let blue_coords: BTreeSet<Coord> = blue.visible_coords().into_iter().collect();
        let red_coords: BTreeSet<Coord> = red.visible_coords().into_iter().collect();

        // Genuinely different views.
        assert_ne!(blue_coords, red_coords, "the two players see different tiles");
        // At the opening the frustums are disjoint (no shared visibility).
        assert!(
            blue_coords.is_disjoint(&red_coords),
            "the opening frustums do not overlap"
        );
        // Blue can see its own units; Red can see its own units; neither sees the
        // other's.
        assert!(blue.visible_enemies().is_empty());
        assert!(red.visible_enemies().is_empty());
        assert_eq!(blue.unit_at(Coord::new(0, 0)).map(|u| u.side), Some(Side::Blue));
        assert_eq!(red.unit_at(Coord::new(4, 4)).map(|u| u.side), Some(Side::Red));
    }

    #[test]
    fn vision_moves_with_the_units_and_can_reveal_an_enemy() {
        // Fog is dynamic: when a unit moves toward the enemy, its frustum shifts and
        // can bring an enemy into view. We march Blue's scout down the board and
        // confirm that once it is within vision range of a Red unit, Red appears in
        // Blue's view (and was NOT visible before).
        let mut board = small_board();

        // Initially Blue cannot see Red.
        assert!(board
            .project_for(Side::Blue, Rehydration::Live)
            .visible_enemies()
            .is_empty());

        // Manually advance Blue's scout toward Red over several plies (alternating
        // turns; Red passes by re-stating position via a no-move we skip — we just
        // hand-relocate for the vision test, the move-gate is tested separately).
        // Move B-scout (index 0) from (0,0) stepwise toward (4,4).
        let path = [Coord::new(2, 2), Coord::new(4, 4)];
        // Step 1: to (2,2) — movement radius 2 allows (0,0)->(2,2).
        board.units[0].at = path[0];
        // After moving to (2,2) with vision 1, Blue sees (3,3)? Chebyshev((2,2),(3,3))
        // = 1 ≤ 1, but Red is at (4,4)/(3,4): Chebyshev((2,2),(3,4)) = 2 > 1 — still
        // fogged. March one more.
        let after_first: Vec<Coord> = board
            .project_for(Side::Blue, Rehydration::Live)
            .visible_enemies()
            .iter()
            .map(|u| u.at)
            .collect();
        // Step 2: to (3,3) — now Chebyshev((3,3),(3,4)) = 1 ≤ vision 1 → R-guard at
        // (3,4) is revealed; Chebyshev((3,3),(4,4)) = 1 → R-scout at (4,4) revealed.
        board.units[0].at = Coord::new(3, 3);
        let blue_view = board.project_for(Side::Blue, Rehydration::Live);
        let seen: Vec<Side> = blue_view
            .visible_enemies()
            .iter()
            .map(|u| u.side)
            .collect();
        assert!(
            !seen.is_empty(),
            "after marching into range, Blue MUST see at least one Red unit (saw {:?}; after_first={:?})",
            seen,
            after_first
        );
        assert!(
            blue_view.visible_enemies().iter().all(|u| u.side == Side::Red),
            "the revealed units are the enemy"
        );
        // And the enemy tile is now rehydratable by Blue VIA its own frustum (the
        // tile entered Blue's vision — note it is now seen under BLUE's projection,
        // because Blue's own units illuminate it).
        assert!(
            blue_view.can_see(Coord::new(3, 4)) || blue_view.can_see(Coord::new(4, 4)),
            "the revealed enemy tile is in Blue's projection"
        );
    }

    // ── Moves = affordances: an illegal/unauthorized move is a REFUSED turn. ──

    #[test]
    fn a_legal_move_is_an_affordance_carrying_a_real_turn() {
        // A move IS a cap-gated affordance firing a REAL effect. Blue's scout at
        // (0,0) moving to (2,2) (Chebyshev 2 ≤ movement 2) is a declared affordance;
        // firing it with Blue's authority yields an intent carrying a real SetField.
        let board = small_board();
        let surface = board.move_surface_for(Side::Blue);
        let blue = board.vision_cap_for(Side::Blue);

        let move_to = move_name("B-scout", Coord::new(2, 2));
        assert!(
            surface.get(&move_to).is_some(),
            "the legal move B-scout->(2,2) is declared as an affordance"
        );
        let intent = surface
            .fire(&move_to, game_cell(0xB1, 1), &blue)
            .expect("Blue fires its own move (authorized)");
        // The intent carries a REAL SetField turn (the move the executor would run).
        assert!(
            matches!(intent.effect, Effect::SetField { .. }),
            "the move fires a real SetField turn"
        );
    }

    #[test]
    fn an_illegal_move_is_not_even_declared() {
        // Anti-cheat, the GAME-rule half: an out-of-range move (scout at (0,0) to
        // (4,4), Chebyshev 4 > movement 2) is NOT a declared affordance — it cannot
        // be fired at all.
        let board = small_board();
        let surface = board.move_surface_for(Side::Blue);
        let too_far = move_name("B-scout", Coord::new(4, 4));
        assert!(
            surface.get(&too_far).is_none(),
            "an out-of-range move is never declared"
        );
        // Firing the (undeclared) move is NoSuchAffordance.
        let blue = board.vision_cap_for(Side::Blue);
        assert_eq!(
            surface.fire(&too_far, game_cell(0xB1, 1), &blue).unwrap_err(),
            FireError::NoSuchAffordance
        );
    }

    #[test]
    fn an_unauthorized_move_is_a_refused_turn_anti_cheat() {
        // Anti-cheat, the CAP half (the free anti-cheat): RED tries to fire one of
        // BLUE's move affordances — a legal move, but Red lacks the authority. The
        // REAL is_attenuation refuses it: Red's Custom identity ⟂ the Blue-required
        // rights. An illegal (unauthorized) move is a REFUSED turn, not a silent
        // cheat.
        let board = small_board();
        let blue_surface = board.move_surface_for(Side::Blue);
        let a_blue_move = move_name("B-scout", Coord::new(2, 2));
        assert!(blue_surface.get(&a_blue_move).is_some(), "it is a real Blue move");

        // Red presents ITS authority to fire Blue's move → REFUSED.
        let red_cap = board.vision_cap_for(Side::Red);
        let refused = blue_surface.fire(&a_blue_move, game_cell(0xED, 1), &red_cap);
        assert!(
            matches!(refused, Err(FireError::Unauthorized { .. })),
            "Red firing Blue's move is refused by the cap gate (anti-cheat is free)"
        );

        // Even a player holding NO Custom identity (a plain Signature spectator)
        // cannot fire a move — Signature ⟂ Custom.
        let spectator = SurfaceCapability::root(game_cell(0x5C, 0), AuthRequired::Signature);
        assert!(
            matches!(
                blue_surface.fire(&a_blue_move, game_cell(0x5C, 0), &spectator),
                Err(FireError::Unauthorized { .. })
            ),
            "a non-owning spectator cannot fire a move either"
        );
    }

    #[test]
    fn applying_a_move_relocates_the_unit_and_passes_the_turn() {
        // The state transition: a fired move, applied, relocates the unit on the
        // model (mirroring its REAL effect) and passes the turn to the opponent.
        let mut board = small_board();
        let surface = board.move_surface_for(Side::Blue);
        let blue = board.vision_cap_for(Side::Blue);
        let mv = move_name("B-scout", Coord::new(2, 2));
        let intent = surface.fire(&mv, game_cell(0xB1, 1), &blue).expect("authorized");

        assert_eq!(board.turn, Side::Blue);
        let outcome = board.apply_move(&intent, Side::Blue).expect("legal move applies");
        assert_eq!(
            outcome,
            MoveOutcome::Moved {
                unit: game_cell(0xB1, 1),
                from: Coord::new(0, 0),
                to: Coord::new(2, 2),
            }
        );
        // The unit relocated.
        assert_eq!(board.units[0].at, Coord::new(2, 2));
        // The turn passed to Red, and the ply advanced.
        assert_eq!(board.turn, Side::Red);
        assert_eq!(board.ply, 1);
    }

    #[test]
    fn a_move_can_capture_a_revealed_enemy() {
        // A move onto an enemy-occupied tile is a legal capture: the enemy is
        // removed, the mover takes the tile. We set up an adjacency and capture.
        let board_cell = game_cell(0xB0, 9);
        let units = vec![
            Unit {
                id: game_cell(0xB1, 1),
                side: Side::Blue,
                at: Coord::new(2, 2),
                vision: 1,
                movement: 2,
                name: "B-scout".to_string(),
            },
            Unit {
                id: game_cell(0xED, 1),
                side: Side::Red,
                at: Coord::new(2, 3), // adjacent to Blue's scout
                vision: 1,
                movement: 2,
                name: "R-scout".to_string(),
            },
        ];
        let mut board = Board::new(5, 5, board_cell, units);
        let surface = board.move_surface_for(Side::Blue);
        let blue = board.vision_cap_for(Side::Blue);
        // Blue captures by moving onto (2,3).
        let cap = move_name("B-scout", Coord::new(2, 3));
        let intent = surface.fire(&cap, game_cell(0xB1, 1), &blue).expect("authorized");
        let outcome = board.apply_move(&intent, Side::Blue).expect("capture is legal");
        assert_eq!(
            outcome,
            MoveOutcome::Captured {
                mover: game_cell(0xB1, 1),
                taken: game_cell(0xED, 1),
                at: Coord::new(2, 3),
            }
        );
        // The enemy is gone; Blue stands on the captured tile.
        assert_eq!(board.units.len(), 1);
        assert_eq!(board.units[0].at, Coord::new(2, 3));
        assert_eq!(board.units[0].side, Side::Blue);
    }

    // ── Agents-as-players: an AI fires the SAME cap-gated affordances. ──

    #[test]
    fn an_agent_player_fires_a_legal_authorized_move() {
        // The agentic part: an AI agent for Blue chooses and FIRES a move through
        // the SAME cap-gated affordance surface — the returned intent was admitted
        // by the REAL is_attenuation (the agent cannot route around the gate).
        let board = small_board();
        let agent = AgentPlayer::new(Side::Blue, game_cell(0xA1, 0));

        let intent = agent
            .choose_move(&board)
            .expect("the agent has a legal authorized move at the opening");
        // The agent's move carries a REAL effect.
        assert!(matches!(intent.effect, Effect::SetField { .. }));
        // The intent's actor is the agent's cell (it fired as itself).
        assert_eq!(intent.actor, game_cell(0xA1, 0));
        // The move it fired is one a Blue unit could legally make — applying it
        // succeeds under the game rules (it is legal AND was authorized).
        let mut b2 = board.clone();
        let outcome = b2.apply_move(&intent, Side::Blue);
        assert!(outcome.is_ok(), "the agent's fired move is legal: {outcome:?}");
    }

    #[test]
    fn an_agent_cannot_move_on_the_opponents_turn() {
        // The agent respects the turn order (it is no more privileged than a human):
        // on Red's turn, a Blue agent has no move.
        let mut board = small_board();
        board.turn = Side::Red;
        let blue_agent = AgentPlayer::new(Side::Blue, game_cell(0xA1, 0));
        assert!(
            blue_agent.choose_move(&board).is_none(),
            "the Blue agent passes when it is Red's turn"
        );
    }

    #[test]
    fn an_agent_prefers_a_capture_when_an_enemy_is_in_reach() {
        // The agent's policy: when an enemy is visible AND in capture range, it
        // takes the capture. Set up a Blue agent adjacent to a visible Red unit.
        let board_cell = game_cell(0xB0, 7);
        let units = vec![
            Unit {
                id: game_cell(0xB1, 1),
                side: Side::Blue,
                at: Coord::new(2, 2),
                vision: 2, // sees the adjacent enemy
                movement: 1,
                name: "B-scout".to_string(),
            },
            Unit {
                id: game_cell(0xED, 1),
                side: Side::Red,
                at: Coord::new(2, 3),
                vision: 1,
                movement: 1,
                name: "R-scout".to_string(),
            },
        ];
        let board = Board::new(5, 5, board_cell, units);
        let agent = AgentPlayer::new(Side::Blue, game_cell(0xA1, 0));
        // The agent sees the enemy (vision 2 ≥ distance 1) and can reach it
        // (movement 1 ≥ distance 1) → it should fire the capturing move.
        let intent = agent.choose_move(&board).expect("the agent has a move");
        let mut b2 = board.clone();
        let outcome = b2.apply_move(&intent, Side::Blue).expect("the move applies");
        assert!(
            matches!(outcome, MoveOutcome::Captured { .. }),
            "the agent took the available capture: {outcome:?}"
        );
    }

    // ── Spectating: a fog-respecting frustum-snapshot. ──

    #[test]
    fn a_spectator_snapshot_respects_the_spectators_fog() {
        // Spectating = a rehydratable frustum-snapshot that RESPECTS the spectator's
        // fog. A snapshot taken for the Blue spectator, rehydrated through a Blue
        // membrane, re-expands ONLY Blue's authorized moves — and a Blue spectator
        // CANNOT re-expand Red's hidden state (the no-peek property carries into
        // spectating). We verify the snapshot is a real frustum frame whose lineage
        // is the spectator's vision facet.
        let (board, board_uri, _web) = demo_skirmish();

        // The Blue spectator's snapshot.
        let snap = board.snapshot_for(
            Side::Blue,
            board_uri.clone(),
            InteractionLog::new(),
            /* sources_reachable */ true,
        );
        // The snapshot's lineage is BLUE's identity (a spectator gated to Blue's
        // view). Its window rights are Blue's Custom identity.
        assert_eq!(snap.sturdyref.lineage.window.rights, side_rights(Side::Blue));
        // The boundary names exactly Blue's legal moves (the frustum extent of the
        // spectator's view) — and contains NO Red moves (anti-peek in the snapshot).
        assert!(
            snap.boundary.affordance_names.iter().all(|n| !n.contains("R-")),
            "the Blue spectator's snapshot names no Red moves"
        );
        assert!(
            snap.boundary.affordance_names.iter().any(|n| n.contains("B-")),
            "the Blue spectator's snapshot names Blue's moves"
        );
        // The snapshot is tiny (a sturdyref + the boundary), not the board state.
        assert!(snap.boundary_extent() > 0);
    }

    #[test]
    fn the_demo_skirmish_publishes_a_real_board() {
        // The demo wiring: the board surface is published into a real web-of-cells
        // with a fetchable dregg:// ref (so snapshots have a live ref to rehydrate).
        let (board, board_uri, web) = demo_skirmish();
        assert_eq!(board.rows, 5);
        assert_eq!(board.cols, 5);
        assert_eq!(board.units.len(), 4);
        // The board cell is fetchable in the web-of-cells.
        let (resource, _chrome) = web.fetch(&board_uri).expect("the board cell is published");
        assert!(resource.verify().is_ok(), "the board cell's attestation verifies");
    }

    // ── Anti-toy: the fog is the REAL lattice, not a flag. ──

    #[test]
    fn the_fog_is_the_real_is_attenuation_not_a_flag() {
        // Anti-toy keystone: prove the fog decision IS the genuine cap lattice. The
        // per-side identities are real AuthRequired::Custom values, and the no-peek
        // is exactly is_attenuation returning false for cross-player identities —
        // the SAME predicate the cap crown proves, not a bespoke `bool visible`.
        let blue = side_rights(Side::Blue);
        let red = side_rights(Side::Red);
        // They are genuine Custom rights.
        assert!(matches!(blue, AuthRequired::Custom { .. }));
        assert!(matches!(red, AuthRequired::Custom { .. }));
        // A side's identity attenuates ITSELF (you see your own tiles).
        assert!(is_attenuation(&blue, &blue));
        assert!(is_attenuation(&red, &red));
        // Cross-player: NEITHER attenuates the other (the no-peek root) — and this
        // is symmetric.
        assert!(!is_attenuation(&blue, &red));
        assert!(!is_attenuation(&red, &blue));
        // The board's vision cap carries exactly this identity on the window-rights
        // axis (the real firmament cap).
        let board = small_board();
        assert_eq!(board.vision_cap_for(Side::Blue).window.rights, blue);
        assert_eq!(board.vision_cap_for(Side::Red).window.rights, red);

        // AND the vk_hash is now the GENUINE one — canonical_predicate_vk of the
        // side's real vision program — NOT a fabricated tag. This is the load-bearing
        // fix: the same hash the proof obligation registers under.
        use dregg_cell::predicate::canonical_predicate_vk;
        let blue_prog = VisionDeck::keypair_for(Side::Blue).program();
        assert_eq!(
            blue,
            AuthRequired::Custom { vk_hash: canonical_predicate_vk(&blue_prog.canonical_bytes()) },
            "side_rights carries the REAL canonical_predicate_vk, re-derivable by a validator"
        );
    }

    // ── The PROOF-BACKED no-peek: the vk_hash is EARNED, not inert. ──

    #[test]
    fn no_peek_for_real_only_the_secret_holder_can_prove_vision() {
        // THE upgraded keystone: fog-of-war's no-peek is now a real PROOF obligation,
        // not lattice incomparability alone. A Blue player (holding only Blue's
        // vision secret) CAN prove its own vision but CANNOT prove Red's — it cannot
        // even construct a verifying proof for the enemy's vision program.
        let board = small_board();
        let blue_deck = VisionDeck::for_player(Side::Blue); // holds ONLY Blue's secret
        let msg = board.vision_signing_message(Side::Blue, Coord::new(0, 0));

        // Blue proves Blue's own vision → Ok (it holds the secret, the registry
        // verifies the genuine Ed25519 proof).
        assert!(
            board.prove_vision(&blue_deck, Side::Blue, Side::Blue, &msg).is_ok(),
            "Blue can PROVE its own vision (holds the secret)"
        );

        // Blue tries to prove RED's vision (to peek a Red-gated tile) → REFUSED. It
        // holds no Red secret, so it cannot produce a proof at all — NoSecretForSide.
        let enemy_msg = board.vision_signing_message(Side::Blue, Coord::new(4, 4));
        assert_eq!(
            board.prove_vision(&blue_deck, Side::Blue, Side::Red, &enemy_msg),
            Err(VisionGateError::NoSecretForSide { side: Side::Red }),
            "no-peek FOR REAL: Blue cannot PROVE Red's vision (it lacks Red's secret)"
        );
        // Symmetric: a Red player cannot prove Blue's vision.
        let red_deck = VisionDeck::for_player(Side::Red);
        assert_eq!(
            board.prove_vision(&red_deck, Side::Red, Side::Blue, &msg),
            Err(VisionGateError::NoSecretForSide { side: Side::Blue })
        );
    }

    #[test]
    fn a_forged_vision_proof_is_rejected_by_the_real_registry() {
        // Even if an adversary FABRICATES a proof for the enemy's vk_hash (by signing
        // with its OWN side's secret), the real registry's Ed25519 verifier REJECTS
        // it — the signature does not verify against the enemy's committed public
        // key. The verify path (validator/referee) catches the forgery with NO secret
        // needed (verify-with-public, the asymmetry).
        use crate::vision_predicate::{FogVisionProducer, PredicateInput, WitnessProducer};
        let board = small_board();
        let referee = VisionDeck::referee(); // can verify any side's proofs
        let msg = board.vision_signing_message(Side::Blue, Coord::new(4, 4));

        // Blue produces a GENUINE proof for ITS OWN program (it holds Blue's secret).
        let blue_program = VisionDeck::keypair_for(Side::Blue).program();
        let blue_producer = FogVisionProducer::new(VisionDeck::keypair_for(Side::Blue));
        let blue_proof = blue_producer
            .produce(
                &blue_program.commitment(),
                &PredicateInput::SigningMessage(&msg),
                &[],
            )
            .expect("Blue produces its own proof");

        // Presenting Blue's signature against RED's program → REJECTED (wrong key).
        // The forge — "claim I can see Red's tiles" — fails closed at the real check.
        assert!(
            matches!(
                referee.verify_presented_proof(Side::Red, &msg, &blue_proof),
                Err(VisionGateError::ProofRejected { .. })
            ),
            "a proof signed with Blue's key is rejected for RED's vision program (forge fails closed)"
        );
        // But the SAME proof verifies for BLUE's program (the honest path) — a
        // referee/light-client confirms Blue's claimed look with only public data.
        assert!(
            referee.verify_presented_proof(Side::Blue, &msg, &blue_proof).is_ok(),
            "a genuine Blue proof verifies for Blue's vision program"
        );
    }

    #[test]
    fn the_deck_registers_the_same_vk_hash_side_rights_carries() {
        // Coherence: the registry the deck builds registers each side's verifier
        // under EXACTLY the vk_hash side_rights(side) carries — so the lattice axis
        // and the proof axis name the SAME genuine hash (not two parallel ids).
        let deck = VisionDeck::referee();
        for side in [Side::Blue, Side::Red] {
            let vk = match side_rights(side) {
                AuthRequired::Custom { vk_hash } => vk_hash,
                _ => unreachable!(),
            };
            assert_eq!(vk, VisionDeck::vk_hash_for(side));
            // The registry has a verifier registered under that hash.
            assert!(
                deck.registry()
                    .get(dregg_cell::predicate::WitnessedPredicateKind::Custom { vk_hash: vk })
                    .is_some(),
                "the deck's registry has {side:?}'s vision verifier under side_rights's vk_hash"
            );
        }
    }

    #[test]
    fn a_referee_holding_both_secrets_can_prove_either_side() {
        // The asymmetry made concrete: a referee (the engine / an all-seeing
        // spectator) holds BOTH secrets and can prove EITHER side's vision — while a
        // per-player deck cannot. Proof-of-vision is gated by SECRET POSSESSION, the
        // genuine ocap stance.
        let board = small_board();
        let referee = VisionDeck::referee();
        let bmsg = board.vision_signing_message(Side::Blue, Coord::new(0, 0));
        let rmsg = board.vision_signing_message(Side::Red, Coord::new(4, 4));
        assert!(board.prove_vision(&referee, Side::Blue, Side::Blue, &bmsg).is_ok());
        assert!(board.prove_vision(&referee, Side::Red, Side::Red, &rmsg).is_ok());
        // And the referee can also prove the cross — because it holds both secrets
        // (it is the engine, not a player). A PLAYER deck cannot (tested above).
        assert!(board.prove_vision(&referee, Side::Blue, Side::Red, &rmsg).is_ok());
    }

    #[test]
    fn the_vision_frustum_is_the_real_fetch_allowlist() {
        // The second axis is also real: the frustum is the genuine fetch-allowlist
        // of a real SurfaceCapability, and may_fetch is the real membrane check.
        let board = small_board();
        let blue_cap = board.vision_cap_for(Side::Blue);
        // Blue's home tile origin is in the frustum (its unit illuminates it).
        assert!(blue_cap.may_fetch(&Coord::new(0, 0).origin()));
        // A far corner Blue cannot see is NOT in the frustum.
        assert!(!blue_cap.may_fetch(&Coord::new(4, 4).origin()));
        // The frustum is a finite allowlist (not the wildcard) — fog is concrete
        // confinement, not "see everything".
        assert!(blue_cap.fetch_allow.is_some(), "the vision frustum is a concrete allowlist");
    }
}
