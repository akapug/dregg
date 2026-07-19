# Bot Depth Wins — 2026-07-17

Two of the three "top moves" from `docs/BOT-EXCELLENCE-BACKLOG-2026-07-17.md` are now
wired in `discord-bot/` as new modules:

- **#15 — the real per-identity persistent RPG world** (`commands::rpg_world`, folding in #24).
- **#8 — the crown**: fold a finished match to ONE proof, stranger-verifies in O(1)
  (`commands::crown`).

This is the state as it now stands in the tree — what each does, how it is wired, how a
user experiences it, and the honest residuals. Companion to the backlog above and
`docs/LIVE-SURFACE-TRUST.md`.

---

## #15 — Real per-identity persistent world (`commands/rpg_world.rs`)

### What it now is

Before this module the eight RPG `/play` keys —
`trade | craft | inventory | guild | cheevos | companion | tavern | party` — each opened a
**throwaway** `SharedWorld::demo("Adventurer")` / `CheevoShowcase::demo()`: canned stock,
forgotten on restart, and — the deepest cut — **no composition** (trade, craft, inventory each
stood on their own private ledger, so a forged blade was not in your inventory and not listable).

`rpg_world.rs` mounts, **for each player's derived dregg identity**, one persistent
`OfferingHost` built by the SAME `dreggnet_surfaces::register_surfaces` one-call registration the
web catalog uses — which mounts trade + craft + inventory onto **ONE `SharedWorld`** (one
`AssetWorld`, one item registry). So on Discord, as on the web: forge an item on the craft
surface and it IS in your inventory and IS listable on your trade stall, as the same note-cell
(the `dreggnet-saga` composition). `RPG_KEYS` (8 keys) is the owned set; the other four `/play`
keys (the games + names/compute) keep their per-channel generic-adapter stores.

### Persistence — replay, never a state blob

Each player's host writes through `SqliteRpgResumeStore` (`discord-bot/src/rpg_store.rs`, a real
`SessionResumeStore` impl over the bot's sqlite `Database`): every session open (its seed) and
every LANDED advance persists as reproducible public input. On the player's first touch after a
restart the host is rebuilt by **replaying those logs through the real executor**
(`OfferingHost::resume`) — a tampered log is refused on re-drive and fails closed, never reopened
to a forged state. Because craft/inventory/trade share ONE world, `order_logs_for_replay` replays
**craft first** (the only surface that mints into the shared ledger), then the movers.

### Real earned cheevos (#24, folded in)

The `cheevos` key no longer shows `CheevoShowcase::demo()`. At host build the player's OWN
persisted `/descent` board completions (the no-cheat `descent_completions` store) are replayed and
fed to `CheevoLedger::earn` — the full gate: re-execute the run against the regenerated
day-world, then hold the achievement predicate over the run's REAL committed trajectory. A player
who has cleared nothing sees an honest empty showcase; nothing is inherited from a demo fixture.

### How a user experiences it

- `/play craft` opens **your** forge in any channel; a button press on any rendered surface acts
  in the **presser's** own world (the embed re-renders as theirs). `/play inventory` anywhere is
  the same singleton world (session slot `"primary"`, per identity, not per channel).
- Forge an item, then open `/play inventory` — it is there. Open `/play trade` — it is listable.
  The same note-cell across all three. This survives a bot restart (replayed from sqlite).
- `/play cheevos` reflects only what you have actually earned via `/descent`.
- Each surface renders byte-consistent with the rest of the offering family (same
  `TITLE`/`COLOR`/`TAGLINE` pulled from the generic adapter's `DiscordOffering` impls).

### Honest residuals (#15)

- **Cross-session interleave.** The exact cross-session interleaving is not recorded, so an exotic
  interleave (two sessions touching one note in opposite order) could re-drive to a refusal — the
  session then honestly fails to reopen (its log is kept; nothing forged goes live). Named in the
  module header.
- **Single-player world.** The canned trade counterparty ("buyer" + its purse) is part of the
  seeded single-player world; **cross-player trading is a named next step, not faked** here.

---

## #8 — The crown (`commands/crown.rs`)

### What it now is

THE CROWN, wired — the one flow no other Discord bot can do. A finished, WON `/play tug` or
`/play automatafl` match (every turn of it a real committed executor turn) **folds, in the
background, into ONE succinct `WholeChainProof`**, and that proof — never the moves — is submitted
to the proof-carrying `dreggnet_game_board::GameBoard`:

```
  PLAY (Discord, fast)      PROVE (background, minutes)      SUBMIT (a proof, not moves)
  /play tug|automatafl  ─▶  dreggnet_prove_service        ─▶ dreggnet_game_board::GameBoard
  a win lands           👑  ::enqueue → deployed             ::submit — verified O(1),
  "Fold this match"         recursive STARK fold             ranked, has_moves() == false
```

- **The fold is real and slow** — `MatchProveService` runs the deployed recursion
  (`prove_turn_chain_recursive`) on a bounded worker pool, OFF the interaction path. The player
  gets an honest "proving in the background (minutes)" status they poll; nothing spins, nothing
  pretends.
- **The board stores NO moves** — an accepted entry is the proof envelope + attested publics. For
  a tug match the fold's leaves are Poseidon2 membership proofs whose public inputs are
  `[blinded_leaf, hand_root]`; the winner's card ids are in nobody's hands but their own.
- **Any stranger re-verifies in O(1)** — the proof envelope is attached to the ranked post as a
  file, and a **Re-verify** button lets ANY user watch the bot re-run the whole-history light
  client against the pinned anchor: one check, zero replay, zero trust in the winner or the bot.

### The wire

| custom-id                | meaning                                                    |
|--------------------------|------------------------------------------------------------|
| `crown:fold:<key>`       | fold this channel's finished `<key>` match (enqueue)       |
| `crown:status:<token>`   | poll the background fold; on Ready, submit + post the crown |
| `crown:reverify:<token>` | ANY user: re-run the O(1) light client on the ranked entry  |

The win-moment offer is posted by `commands::offering`'s ended-match hook: on a landed
`ended: true` turn of a `foldable_key` (`tug`/`automatafl`), both the component path
(`offering.rs:1222`) and the modal path (`offering.rs:1363`) call `crown::offer_fold`. There is
also a slash surface — `/crown fold | status | board` (`crown::register` / `crown::handle`).

### How a user experiences it

1. Win a `/play tug` or `/play automatafl` match. A **"Fold this match to one proof"** button
   appears at the win moment (no extra command needed).
2. Press it (or `/crown fold`) → honest "proving in the background (minutes)" embed with a poll
   button. The interaction never blocks on the prover.
3. Poll → on `Ready`, the fold submits to the board and posts the crown: *ranked, the board holds
   a proof and NO moves — your hand was never revealed; anyone can re-verify in O(1)*, with the
   proof envelope attached as a file.
4. **Any other user** presses **Re-verify** on that post and watches the bot re-check the proof
   against the pinned anchor, publicly. One flow demonstrates every pillar.

### Honest residuals / named scope (#8)

- **Succinct, not hiding.** The deployed STARK is succinct, not ZK: "moves never posted" is a
  **data-availability privacy property** (the board never sees them, nobody publishes them), NOT
  a crypto-ZK claim about the transcript. Every crown embed footer says so.
- **Tug win-leaf scope.** The deployed win leaf proves the *influence* path (`charm >= 11`, the
  range gadget). A tug round won on the guild-count threshold with `charm < 11` is real on the
  executor but the fold's win leaf cannot honestly attest it — the crown **refuses that fold
  honestly** rather than forge or wedge the witness builder.
- **Automatafl fold scope.** The automatafl fold is the game crate's own named scope: the
  committed D1 automaton-step chain (stepping from the final committed position). The player-move
  D2/D3 stages fold identically but are not the chain driven here — `dreggnet_game_board`'s named
  residual, repeated in the post.
- **In-process board.** The `GameBoard` and pending-fold records live in this process (in-memory,
  like the other offering sessions); a restart forgets pending folds. **The proof FILE survives on
  Discord** and stays verifiable by anyone holding the anchor.

---

## Build state (from the Repair phase)

Phase 1 (these two lanes) was deliberately **no-build** — the two modules share the `discord-bot`
target lock, so building in parallel gridlocks; edits were kept type-consistent by careful reading,
and the Repair phase owns the single workspace build (its `tail -30` output was still in flight at
the time this summary was written — the green is the Repair phase's to confirm).

What is structurally in place, verified by reading:

- **Modules declared:** `commands::rpg_world` and `commands::crown` are both in
  `discord-bot/src/commands/mod.rs`.
- **Supporting substrate present:** `SqliteRpgResumeStore` (`src/rpg_store.rs`) implements
  `SessionResumeStore`; the dep crates all exist and are declared in `discord-bot/Cargo.toml`:
  `dreggnet-surfaces`, `dreggnet-game-board`, `dreggnet-prove-service`, `dreggnet-cheevo`,
  `dreggnet-offerings` (root workspace members, consumed, never modified by these lanes).
- **Button routes live:** `main.rs` already routes `crown:` component presses to
  `crown::handle_component`; `offering.rs` and `portfolio.rs` delegate the eight RPG keys to
  `rpg_world` and hook the crown offer on match end.

### The one central registration handoff (Repair phase / `main.rs`)

Per the no-touch rule on `main.rs`'s command registry + `REGISTERED_COMMAND_NAMES` sync test,
these lanes did **not** register the `/crown` slash command. `crown::register()` and
`crown::handle()` exist and are ready; the Repair phase must centrally:

1. add `crown::register()` to the command list built in `main.rs`,
2. dispatch `"crown" => crown::handle(...)` in the by-name command match,
3. add `"crown"` to `REGISTERED_COMMAND_NAMES` so the sync test passes.

The **button-driven crown** (win-moment "Fold this match" offer + status poll + stranger
Re-verify) needs none of that — it is fully wired through the already-routed `crown:` component
prefix. The slash `/crown` is the additive convenience surface awaiting central registration.

`rpg_world` adds **no new command** — it intercepts the existing eight `/play` keys, so it needs
no registry change.
