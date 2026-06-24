// mud_play_gm.js — the GAMEMASTER for the PLAYABLE MUD CLIENT (`dregg-node mud-client`).
//
// A pure deos-js program the headless dregg node HOSTS — the rich living world is DATA +
// verified turns on the node's ledger (no Rust gameplay logic, no gpui). The GM is a
// PRIVILEGED server holding broad caps over its whole world; the player is cap-constrained
// and drives the world ONLY through signed turns over the affordances the GM offers.
//
// This is a SUPERSET of the e2e `mud_gm.js`: same rooms/character/NPC/move/gain-xp, PLUS it
// stands up TWO dungeon instances so the client can demonstrate the full membrane-fork story:
//
//   PERSONAL DUNGEON  (mud-play-dungeon-aria) — forked AND the player is GRANTED a cap over
//                      it, so the player's `descend` (a signed cross-cell write into the
//                      instance) is AUTHORIZED: the player can actually enter their dungeon.
//   SEALED DUNGEON    (mud-play-dungeon-sealed) — forked but the player is NOT admitted. Its
//                      surface is discoverable, but a `descend` fired by this player is
//                      REFUSED by the executor's reach gate (fork isolation: you cannot forge
//                      progress inside a party session you were never admitted to).
//
// The host substitutes the player's agent-cell hex for "__PLAYER__". All seeds are
// deterministic so the Rust client/harness can re-derive the same cell ids.

// ── ROOMS — the GM spawns the map (real CreateCell turns) ──────────────────────────
var entrance = deos.server.spawnCell("mud-play-room-entrance", "open");
var hall = deos.server.spawnCell("mud-play-room-hall", "open");

// ── CHARACTER — spawn + stamp stats (level/xp/room) via the setField superpower ─────
var character = deos.server.spawnCell("mud-play-char-aria", "open");
deos.server.setField(character, 0, 1);   // slot 0 = LEVEL  := 1
deos.server.setField(character, 1, 0);   // slot 1 = XP     := 0
deos.server.setField(character, 2, 1);   // slot 2 = ROOM   := 1 (ENTRANCE)

// ── NPC — a watchman; mood field starts calm ────────────────────────────────────────
var watchman = deos.server.spawnCell("mud-play-npc-watchman", "open");
deos.server.setField(watchman, 0, 0);    // slot 0 = MOOD := 0 (calm)

// ── GRANT — the player holds a cap over its character (so its move/gain-xp authorize) ─
deos.server.grant("__PLAYER__", character, "none");

// ── AFFORDANCES — the cap-gated gameplay verbs players fire via /turns/submit ────────
// MOVE: enter the HALL (room := 2).
deos.server.defineAffordance({
    name: "move",
    required: "signature",
    effects: [
        { type: "setField", cell: character, index: 2, value: 2 }
    ]
});

// GAIN-XP: a kill grants XP (xp := 120, crossing the level-up threshold of 100).
deos.server.defineAffordance({
    name: "gain-xp",
    required: "signature",
    effects: [
        { type: "setField", cell: character, index: 1, value: 120 }
    ]
});

// ── PERSONAL DUNGEON — the GM FORKS a private instance AND ADMITS the player ─────────
// The player is granted a cap over the instance, so its `descend` write authorizes: this
// is a dungeon the player can actually enter (the membrane-fork they hold a key to).
var dungeon = deos.server.fork("mud-play-dungeon-aria");
deos.server.grant("__PLAYER__", dungeon, "none");
deos.server.defineAffordance({
    name: "descend",
    required: "signature",
    instance: dungeon,
    effects: [
        { type: "setField", cell: dungeon, index: 0, value: 1 }   // slot 0 = DESCENDED := 1
    ]
});

// ── SEALED DUNGEON — forked but NOT admitting this player (the refusal demo) ──────────
// Its `descend` affordance is discoverable, but firing it as this player is refused by the
// executor's reach gate (no cap over the instance) — fork isolation.
var sealed = deos.server.fork("mud-play-dungeon-sealed");
deos.server.defineAffordance({
    name: "descend",
    required: "signature",
    instance: sealed,
    effects: [
        { type: "setField", cell: sealed, index: 0, value: 1 }
    ]
});

// Witness object the host returns (1 iff the whole world stood up).
(entrance && entrance.length === 64 &&
 hall && hall.length === 64 &&
 character && character.length === 64 &&
 watchman && watchman.length === 64 &&
 dungeon && dungeon.length === 64 &&
 sealed && sealed.length === 64) ? 1 : 0;
