//! **The overworld offering** — a player traverses a REGION of universes, the map opening as they
//! honestly clear each dungeon.
//!
//! Where [`crate::dungeon::DungeonOffering`] hosts ONE universe (the Keep) and
//! [`crate::character::AdventurerOffering`] binds a persistent character across runs, this offering
//! is the layer ABOVE both: a [`RegionMap`] of universes joined by travel edges, played on a real
//! dregg [`RegionCell`]. It re-homes `attested-dm`'s PROVEN overworld design (a region of dungeons,
//! travel gated on VERIFIED COMPLETION) off the toy blake3 ledger onto the real spween-dregg
//! executor.
//!
//! ## The teeth are REAL executor teeth (not app bookkeeping)
//!
//! - **Travel is gated on verified completion.** [`OverworldOffering::travel`] fires a real
//!   region-cell turn the executor REFUSES unless the destination's prerequisite is cleared (a
//!   `FieldGte` on a WriteOnce cleared flag — see [`dungeon_on_dregg::overworld`]). The map opens
//!   as you clear it.
//! - **Completion → unlock is a real committed turn.** [`OverworldOffering::play_and_clear`] drives
//!   a location's universe START → WIN on the real substrate, re-verifies the whole playthrough by
//!   replay, and ONLY THEN fires the sanctioned `clear` turn that sets the cleared flag — the
//!   session-level binding of a real, replay-verified WIN to a real committed unlock (the same
//!   `Won + verify + replay` gate attested-dm's `record_completion` used, and the same shape
//!   [`crate::character`] uses to bind a real dungeon outcome to a real character-cell XP turn).
//! - **A forged clear is refused.** A cleared flag written outside the sanctioned method is a real
//!   default-deny executor refusal ([`RegionCell::forge_cleared`]); an UNFINISHED run credits
//!   nothing (the completion gate refuses to clear it).
//!
//! ## Honest scope
//!
//! - "Verified completion" is bound to the unlock at the SESSION level (drive to WIN + replay-verify
//!   → fire the real clear turn). The purist alternative — the region cell gating `clear` on the
//!   dungeon cell's finalized WIN root via a cross-cell `ObservedFieldEquals` (the `multicell`
//!   pattern) — needs region + dungeon cells co-hosted on one executor ledger, a named follow-up.
//! - Region progress is the live [`RegionCell`] in-process; the durable per-identity store is a
//!   follow-up (as the character store is). A fuller overworld adds branching/converging regions,
//!   world events, and a shared/persistent overworld across players — named, not built here.

use dregg_app_framework::TurnReceipt;
use dungeon_on_dregg::overworld::{
    RegionCell, RegionMap, WinRun, deepening_ways, play_to_win, reverify_win,
};

use crate::{DreggIdentity, OfferingError, Outcome, SessionConfig, VerifyReport};

/// **A player's live traversal of a region.** Owns the real region cell (the map + its committed
/// cleared flags), the player's identity, the log of region turns (travel + clear receipts, for
/// re-verify), and the cleared dungeons' recorded playthroughs (each re-verified by replay).
pub struct OverworldSession {
    who: DreggIdentity,
    region: RegionCell,
    /// The deploy seed of the region cell — [`OverworldOffering::verify`] re-deploys an identical
    /// region cell from it and replays the recorded ops.
    seed: u8,
    /// The region cell's committed ops, in order (travel + clear) — re-verified by replay on a
    /// fresh identically-seeded region cell.
    ops: Vec<RegionOp>,
    /// Each cleared location's recorded WIN run (id + seed + playthrough) — replay re-verified.
    cleared_runs: Vec<WinRun>,
}

/// One committed region turn, recorded for replay re-verification.
#[derive(Clone, Debug)]
enum RegionOp {
    /// A sanctioned clear of a location (unlocking the roads gated on it).
    Clear(String),
    /// A gated travel to a destination.
    Travel(String),
}

impl OverworldSession {
    /// The player traversing this region.
    pub fn who(&self) -> &DreggIdentity {
        &self.who
    }
    /// The live region cell (for the driven forged-flag leg + introspection).
    pub fn region(&self) -> &RegionCell {
        &self.region
    }
    /// The region topology.
    pub fn map(&self) -> &RegionMap {
        self.region.map()
    }
    /// The location the traveller currently stands in.
    pub fn current_location(&self) -> String {
        self.region.current_location()
    }
    /// Whether location `loc` is cleared.
    pub fn is_cleared(&self, loc: &str) -> bool {
        self.region.is_cleared(loc)
    }
    /// How many dungeons are cleared.
    pub fn cleared_count(&self) -> usize {
        self.region.cleared_count()
    }
    /// The destinations reachable RIGHT NOW — a `to` for which an edge departs the current location
    /// and whose gate is satisfied by the cleared flags (the map's currently-open roads).
    pub fn available_destinations(&self) -> Vec<String> {
        let map = self.region.map();
        let here = self.current_location();
        map.edges_from(&here)
            .into_iter()
            .filter(|e| match &e.gate {
                None => true,
                Some(prereq) => self.region.is_cleared(prereq),
            })
            .map(|e| e.to.clone())
            .collect()
    }
}

/// **Why a completion was NOT credited** — the completion gate is fail-closed.
#[derive(Debug, Clone)]
pub enum ClearError {
    /// The location is not a place in this region.
    UnknownLocation(String),
    /// The run did not reach a WIN — an unfinished dungeon credits nothing.
    NotWon(String),
    /// The run's playthrough failed re-verification by replay — a forged/reordered record.
    ReplayFailed(String),
    /// The region cell refused the sanctioned clear turn (carries the executor reason).
    ClearRefused(String),
    /// The run is a win for a DIFFERENT universe than the location plays — a win for the wrong
    /// dungeon cannot credit this one.
    WrongUniverse {
        /// The location claimed.
        location: String,
        /// The universe the location actually plays.
        expected: String,
        /// The universe the run is actually for.
        got: String,
    },
}

impl std::fmt::Display for ClearError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClearError::UnknownLocation(l) => {
                write!(f, "REFUSED: `{l}` is not a place in this region")
            }
            ClearError::NotWon(l) => write!(f, "REFUSED: the run of `{l}` is not won"),
            ClearError::ReplayFailed(l) => write!(f, "REFUSED (re-execution): `{l}` failed replay"),
            ClearError::ClearRefused(why) => write!(f, "REFUSED (executor): {why}"),
            ClearError::WrongUniverse {
                location,
                expected,
                got,
            } => write!(
                f,
                "REFUSED: this run is of `{got}`, not `{expected}` (the universe location `{location}` plays)"
            ),
        }
    }
}

impl std::error::Error for ClearError {}

/// **The overworld offering** — a stateless factory over a [`RegionMap`]. Each [`open`](Self::open)
/// deploys a fresh [`OverworldSession`] (a real region cell) for a player. Additive: the underlying
/// [`crate::dungeon::DungeonOffering`] / [`crate::character::AdventurerOffering`] are untouched; this
/// consumes the crate's universes through the `dungeon_on_dregg::overworld` registry.
pub struct OverworldOffering {
    map: RegionMap,
}

impl OverworldOffering {
    /// An offering over the concrete [`deepening_ways`] region (four universes, hub-and-branch).
    pub fn new() -> Self {
        OverworldOffering {
            map: deepening_ways(),
        }
    }

    /// An offering over an explicit region map.
    pub fn over(map: RegionMap) -> Self {
        OverworldOffering { map }
    }

    /// The region topology this offering serves.
    pub fn map(&self) -> &RegionMap {
        &self.map
    }

    /// **Open a traversal for `who`** — deploy a fresh region cell at the config seed, at the
    /// region's start location with nothing cleared.
    pub fn open(
        &self,
        who: DreggIdentity,
        cfg: SessionConfig,
    ) -> Result<OverworldSession, OfferingError> {
        if !self.map.is_well_formed() {
            return Err(OfferingError::Deploy(format!(
                "malformed region: {:?}",
                self.map.validate()
            )));
        }
        let seed = ((cfg.seed.unwrap_or(1) % 251) + 1) as u8;
        let region = RegionCell::deploy(&self.map, seed);
        Ok(OverworldSession {
            who,
            region,
            seed,
            ops: Vec::new(),
            cleared_runs: Vec::new(),
        })
    }

    /// **Travel to `dest` — the gated travel turn.** Fires a real region-cell turn: a legal move
    /// (the destination's prerequisite is cleared) commits ([`Outcome::Landed`]); a locked road is a
    /// real executor [`Outcome::Refused`] that commits nothing (anti-ghost). A committed travel is
    /// recorded onto the traversal's chain.
    pub fn travel(&self, session: &mut OverworldSession, dest: &str) -> Outcome {
        match session.region.travel(dest) {
            Ok(receipt) => {
                session.ops.push(RegionOp::Travel(dest.to_string()));
                Outcome::Landed {
                    receipt,
                    ended: false,
                }
            }
            Err(why) => Outcome::Refused(why),
        }
    }

    /// **Play the location's universe to a WIN and, iff it genuinely won + re-verifies, CLEAR it.**
    /// Drives the universe START → WIN on the real substrate, re-verifies the whole playthrough by
    /// replay, and only then fires the sanctioned `clear` turn on the region cell (a real committed
    /// unlock). Returns the clear turn's receipt on success, or the precise [`ClearError`]. An
    /// unfinished / forged run credits NOTHING (the completion gate is fail-closed).
    pub fn play_and_clear(
        &self,
        session: &mut OverworldSession,
        loc: &str,
    ) -> Result<TurnReceipt, ClearError> {
        let uni = self
            .map
            .location(loc)
            .ok_or_else(|| ClearError::UnknownLocation(loc.to_string()))?
            .universe_id
            .clone();
        // A deterministic per-(player, location) dungeon seed, so a re-verify re-deploys the
        // identical world-cell (the identity gives the cell identity; the run gives the state).
        let seed = dungeon_seed(&session.who, loc);
        let run =
            play_to_win(&uni, seed).ok_or_else(|| ClearError::UnknownLocation(loc.to_string()))?;
        self.credit(session, loc, run)
    }

    /// **Credit a location from an already-driven run** — the completion GATE, factored so the
    /// non-vacuous "an unfinished run credits nothing" leg can present a partial run. Fires the
    /// sanctioned `clear` turn IFF the run is a genuine WIN AND re-verifies by replay.
    pub fn credit(
        &self,
        session: &mut OverworldSession,
        loc: &str,
        run: WinRun,
    ) -> Result<TurnReceipt, ClearError> {
        let expected = self
            .map
            .location(loc)
            .ok_or_else(|| ClearError::UnknownLocation(loc.to_string()))?
            .universe_id
            .clone();
        // IDENTITY: the run must be for THIS location's universe — a win for the wrong dungeon
        // cannot credit this one (the fingerprint check attested-dm's `record_completion` used).
        if run.id != expected {
            return Err(ClearError::WrongUniverse {
                location: loc.to_string(),
                expected,
                got: run.id.clone(),
            });
        }
        if !run.won {
            return Err(ClearError::NotWon(loc.to_string()));
        }
        if !reverify_win(&run.id, run.seed, &run.playthrough) {
            return Err(ClearError::ReplayFailed(loc.to_string()));
        }
        // The verified WIN is bound to the unlock: fire the real committed clear turn.
        let receipt = session
            .region
            .clear(loc)
            .map_err(ClearError::ClearRefused)?;
        session.ops.push(RegionOp::Clear(loc.to_string()));
        session.cleared_runs.push(run);
        Ok(receipt)
    }

    /// **Re-verify the whole traversal by REPLAY.** Re-deploys a fresh, identically-seeded region
    /// cell and re-drives the recorded op sequence: every committed travel/clear must re-commit in
    /// order (a forged log — e.g. a travel before its prerequisite clear — is REFUSED on the fresh
    /// executor), and the replayed region reproduces exactly the live cleared set + position. Then
    /// every cleared dungeon's playthrough re-verifies by replay against a fresh world-cell. A
    /// forged region op or a forged dungeon record fails.
    pub fn verify(&self, session: &OverworldSession) -> VerifyReport {
        let region_turns = session.ops.len();
        let replay = RegionCell::deploy(&self.map, session.seed);
        for (n, op) in session.ops.iter().enumerate() {
            let r = match op {
                RegionOp::Clear(loc) => replay.clear(loc),
                RegionOp::Travel(dest) => replay.travel(dest),
            };
            if let Err(why) = r {
                return VerifyReport::broken(
                    region_turns,
                    format!("region op {n} ({op:?}) refused on replay: {why}"),
                );
            }
        }
        // The replayed region reproduces the live traversal's committed state.
        for loc in &self.map.locations {
            if replay.is_cleared(&loc.id) != session.region.is_cleared(&loc.id) {
                return VerifyReport::broken(
                    region_turns,
                    format!("replayed cleared flag for `{}` diverged", loc.id),
                );
            }
        }
        if replay.current_location() != session.region.current_location() {
            return VerifyReport::broken(region_turns, "replayed position diverged");
        }
        // Every cleared dungeon's own playthrough re-verifies by replay (the per-dungeon teeth).
        let mut dungeon_turns = 0usize;
        for run in &session.cleared_runs {
            dungeon_turns += run.playthrough.receipts().len();
            if !reverify_win(&run.id, run.seed, &run.playthrough) {
                return VerifyReport::broken(
                    dungeon_turns,
                    format!("dungeon `{}` failed replay", run.id),
                );
            }
        }
        VerifyReport::ok(region_turns + dungeon_turns)
    }
}

impl Default for OverworldOffering {
    fn default() -> Self {
        OverworldOffering::new()
    }
}

/// Re-export the partial-run helper so a frontend/test can present an unfinished run to the
/// fail-closed completion gate (the non-vacuous "credits nothing" leg).
pub use dungeon_on_dregg::overworld::play_partial as play_partial_run;

/// A deterministic per-(player, location) dungeon deploy seed in `1..=251`.
fn dungeon_seed(who: &DreggIdentity, loc: &str) -> u8 {
    let mut h = blake3::Hasher::new();
    h.update(who.as_str().as_bytes());
    h.update(b"/");
    h.update(loc.as_bytes());
    (h.finalize().as_bytes()[0] % 251) + 1
}

#[cfg(test)]
mod tests {
    use super::*;

    fn player() -> DreggIdentity {
        DreggIdentity("player-overworld-key".to_string())
    }

    /// THE FULL DRIVEN TRAVERSAL: travel to a locked dungeon is REFUSED until its prerequisite is
    /// verified-cleared; clearing a dungeon (a real, replay-verified WIN) unlocks the next on a real
    /// turn; a forged cleared flag is refused; an unfinished run credits nothing; the whole
    /// traversal re-verifies.
    #[test]
    fn the_map_opens_as_you_honestly_clear_it() {
        let off = OverworldOffering::new();
        let mut s = off
            .open(player(), SessionConfig::with_seed(11))
            .expect("open the region");
        assert_eq!(s.current_location(), "keep", "start at the hub");
        assert_eq!(s.cleared_count(), 0);

        // LOCKED: travel to the vault before clearing the keep is a real executor refusal.
        let locked = off.travel(&mut s, "vault");
        assert!(
            !locked.landed(),
            "travel to a locked dungeon is refused, got {locked:?}"
        );
        assert_eq!(s.current_location(), "keep", "anti-ghost: did not move");

        // FORGED FLAG: writing the keep's cleared flag under a non-sanctioned method is refused.
        let forged = s.region().forge_cleared("keep");
        assert!(
            forged.is_err(),
            "a forged cleared flag is refused, got {forged:?}"
        );
        assert!(!s.is_cleared("keep"), "anti-ghost: keep still not cleared");

        // UNFINISHED RUN CREDITS NOTHING: a partial (not-won) keep run is refused by the gate.
        let partial =
            play_partial_run("keep", dungeon_seed(s.who(), "keep"), 2).expect("partial run");
        assert!(!partial.won);
        let refused = off.credit(&mut s, "keep", partial);
        assert!(
            matches!(refused, Err(ClearError::NotWon(_))),
            "an unfinished run credits nothing, got {refused:?}"
        );
        assert!(!s.is_cleared("keep"), "anti-ghost: still not cleared");

        // CLEAR (a genuine, replay-verified WIN) → unlock on a real committed turn.
        off.play_and_clear(&mut s, "keep")
            .expect("a genuine win clears the keep");
        assert!(s.is_cleared("keep"));

        // NON-VACUOUS: the SAME travel that was refused now commits.
        let now = off.travel(&mut s, "vault");
        assert!(
            now.landed(),
            "clearing the keep opens the road to the vault, got {now:?}"
        );
        assert_eq!(s.current_location(), "vault");

        // The deeper road stays sealed until the vault is cleared.
        let deep_locked = off.travel(&mut s, "crypt");
        assert!(
            !deep_locked.landed(),
            "the crypt stays sealed until the vault is cleared"
        );

        // Clear the vault → the deep road to the crypt opens; travel and clear it.
        off.play_and_clear(&mut s, "vault")
            .expect("clear the vault");
        assert!(
            off.travel(&mut s, "crypt").landed(),
            "the vault opens the way to the crypt"
        );
        assert_eq!(s.current_location(), "crypt");
        off.play_and_clear(&mut s, "crypt")
            .expect("clear the crypt");

        // Walk home along the open return roads (crypt ▸ vault ▸ keep), then take the keep's other
        // branch to the bazaar (opened when the keep cleared) and clear it — a full travelled sweep.
        assert!(
            off.travel(&mut s, "vault").landed(),
            "open return road crypt → vault"
        );
        assert!(
            off.travel(&mut s, "keep").landed(),
            "open return road vault → keep"
        );
        assert!(
            off.travel(&mut s, "bazaar").landed(),
            "the keep opened the bazaar branch"
        );
        assert_eq!(s.current_location(), "bazaar");
        off.play_and_clear(&mut s, "bazaar")
            .expect("clear the bazaar branch");
        assert_eq!(
            s.cleared_count(),
            4,
            "all four dungeons cleared by travelled, verified wins"
        );

        // THE WHOLE TRAVERSAL RE-VERIFIES.
        let report = off.verify(&s);
        assert!(
            report.verified,
            "the whole traversal re-verifies: {}",
            report.detail
        );
        assert!(report.turns > 0);
    }

    /// A win for the WRONG universe cannot clear a location: [`OverworldOffering::credit`] binds a
    /// location to its OWN universe id, so a GENUINE, replay-verified keep WIN offered to credit the
    /// vault is REFUSED with `WrongUniverse` — you cannot clear the vault by winning the keep. The
    /// non-vacuous identity tooth (the same keep run DOES credit the keep).
    #[test]
    fn a_win_for_the_wrong_universe_cannot_clear_a_location() {
        let off = OverworldOffering::new();
        let mut s = off
            .open(player(), SessionConfig::with_seed(5))
            .expect("open");

        let keep_run = play_to_win("keep", dungeon_seed(s.who(), "keep")).expect("keep run");
        assert!(keep_run.won);

        // Offered to credit the VAULT: refused — the run is of `keep`, the vault plays `vault`.
        let refused = off.credit(&mut s, "vault", keep_run.clone());
        assert!(
            matches!(&refused, Err(ClearError::WrongUniverse { expected, got, .. }) if expected == "vault" && got == "keep"),
            "a keep win cannot credit the vault, got {refused:?}"
        );
        assert!(
            !s.is_cleared("vault"),
            "anti-ghost: the vault is not cleared"
        );

        // The very same keep run DOES legitimately credit the keep (non-vacuous).
        off.credit(&mut s, "keep", keep_run)
            .expect("the keep run credits the keep");
        assert!(s.is_cleared("keep"));
    }
}
