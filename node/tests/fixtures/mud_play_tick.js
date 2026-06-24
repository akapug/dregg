// mud_play_tick.js — the GAMEMASTER's reactive TICK for the playable MUD client.
//
// A pure deos-js program the host runs AFTER the player has acted (moved + gained XP via
// signed turns). The GM — holding broad caps over its world — OBSERVES the live ledger and
// reacts. This is the living-world's "the world responds" half:
//
//   LEVEL-UP      — read the character's XP off the real ledger; if it crossed the
//                   threshold (100), raise the level + reset XP (real SetField turns). A
//                   player cannot do this — it is the GM's setField superpower.
//   NPC REACTION  — the watchman REACTS to the player's arrival in the HALL: the GM raises
//                   the watchman's mood (alert).
//
// The host substitutes the real character + watchman hexes for "__CHAR__" / "__NPC__".

var XP_THRESHOLD = 100;

// ── observe ── read the character's live XP + room off the ledger.
var xp = deos.server.getField("__CHAR__", 1);
var room = deos.server.getField("__CHAR__", 2);

var leveled = 0;
var reacted = 0;

// ── LEVEL-UP ── XP crossed the threshold ⇒ raise level, reset XP (real turns).
if (xp >= XP_THRESHOLD) {
    var setLevel = deos.server.setField("__CHAR__", 0, 2);   // LEVEL := 2
    var resetXp = deos.server.setField("__CHAR__", 1, 0);    // XP    := 0
    leveled = (setLevel === 1 && resetXp === 1) ? 1 : 0;
}

// ── NPC REACTION ── the player reached the HALL (room 2) ⇒ the watchman goes alert.
if (room === 2) {
    var mood = deos.server.setField("__NPC__", 0, 1);        // MOOD := 1 (alert)
    reacted = (mood === 1) ? 1 : 0;
}

// Witness: 1 iff both GM reactions fired (or were not yet warranted).
(leveled === 1 && reacted === 1) ? 1 : 0;
