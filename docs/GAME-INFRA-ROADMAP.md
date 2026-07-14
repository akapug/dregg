# The Descent / dregg game-engine — infra roadmap (2026-07, 3-ideator + NFT synthesis)

What to build for the game, grounded in the real engine. Every item rides a primitive that already ships on the executor;
the "verifiable edge" is the thing a normal engine can't sell. Companion to GAME-STRATEGY / GAME-FUN-AND-INFRA-PLAN /
CONTENT-AND-ASSET-SPEC.

## THE CROWN — the only-dregg-can-do thing (lead with this)
Records + items are PROOFS, not server rows. The sharpest unlock: **PRIVATE-STRATEGY play** — the proof-leaderboard (ugc
`submit_proof`) verifies a fold proof in O(1) and stores NO moves, so you prove "I soloed today's hardcore, no hits" WITHOUT
revealing HOW (route/build stay secret forever). A normal engine has only trust-the-client (cheatable) or demand-the-replay
(leaks strategy); dregg has a strictly-better third. Composes with: **items whose provenance IS their identity** (a loot
AssetId encodes the drop; rarity a provable ~3% tail), **no dupes by construction** (double-spend = a type error, the #1 MMO
economy-killer gone), **un-fakeable cheevos** (an achievement = an anchored fold-proof predicate — depth>=N, no-death-streak
— mintable soulbound). Build first (crypto mostly exists): cheevos-as-fold-proofs, the private-strategy tournament (move the
bracket to the proof path), cross-game portable holdings (the AssetId is already game-independent).

## SOCIAL / MULTIPLAYER (ranked; the biggest play-together unlocks are closest to built)
1. **PARTIES (small->med, #1):** the crowd IS the party, each seat a job. mud.rs (seated player-cells, each cap = its role
   mandate — you can't take another's turn) + collective.rs::open_with (a signed roster + quorum at forks) + combat.rs
   FOCUS_BUDGET (a shared party resource). Escape the TPP mush via DISTINCT caps per seat. Edge: nobody plays your seat /
   forges your vote / fakes the loot split.
2. **SHARED HUB / presence (small, ALREADY BUILT):** node/shared_world.rs boot_shared_world = a hosted board + presence
   seats + live receipt-stream sync + over-reach refusal. Re-home as a tavern between runs (LFG, market stalls). Un-fakeable
   presence — the connective tissue that makes every other social system discoverable.
3. **PLAYER TRADING (med, named seam):** dreggnet-asset transfer + escrow-market atomic swap = scam-proof P2P trade + real
   provenance. Keep tradable to cosmetics/provenance/mats, NEVER power.
4. **RAIDS (big, the frontier):** a PROVEN world-first kill — combat.rs reverify_draw (un-forgeable dice) + multicell.rs
   ObservedFieldEquals (phases gate on prior-phase completion) + collective coordination. Needs the multi-cell concurrent-
   battle frontier combat.rs names. Stage after parties+hub.
5. **GUILDS (med-big, now unblocked by durable stores):** aggregate of un-forgeable clears + an escrow treasury.
6. **SPECTATOR (med, machinery built):** fog-respecting, anti-stream-snipe (a full-board mid-game grant is REFUSED); the
   SpectatorGrant/MembraneNegotiation stack is remarkably complete.

## WORLD / QUESTS / CONTENT (quests + UGC + factions are ONE tent)
1. **QUESTS (biggest world unlock, greenfield-but-every-tooth-exists):** the dialogue idiom generalized — a quest-giver + a
   multi-step gated objective + an un-fakeable completion receipt. dialogue.rs (WriteOnce step flags + BoundedBy ordering +
   FieldGte turn-in) + overworld.rs (travel gated on a replay-verified WIN) + multicell.rs (cross-cell "content opens because
   objective done"). A quest = a gated scene; completion = a Completion re-executed to a WinCondition. FAILURE MODE: quest
   state must be a gated committed cell, never host bookkeeping (the LARP the rebuild kills).
2. **UGC / AUTHORING (the flywheel):** a stranger authors a quest/world as a spween .scene (text, no Rust) -> the no-cheat
   board. Safe MODS = a new TransitionCase under an attenuated cap. The one missing surface: E4 `/gallery publish-scene` ->
   authored_signed (small, high leverage). Authorship ed25519-attested + remix lineage.
3. **FACTIONS / REPUTATION (pure whitespace):** disposition IS per-NPC reputation; generalize to a faction cell (per-faction
   Monotonic rep slots); faction-vs-faction = a FieldLteOther cross-slot cap. Ship rep only WITH the content it gates.
4. **PERSISTENT WORLD / PLACES:** the overworld IS the map of places; add a TOWN HUB Loc (dialogue NPCs — quest-givers,
   faction reps, merchants) + durable place state (the resume-store move-log) + a living world. Durable persistence non-
   negotiable.
5. **WORLD EVENTS / SEASONS (most-built; needs content wiring):** a beacon-seeded limited-time Universe (everyone plays the
   same, verifiable by re-derivation) + collective boss invasions (the crowd can't vote past the teeth). The Season
   abstraction carries the hall-of-fame/prestige across boundaries.
6. **AI-DRIVEN CONTENT:** the crown applied to content — AI PROPOSES a typed Command / an authored scene, the world + the
   no-cheat board DISPOSE (an ill-formed/cheating scene fails the publish gate; an AI grant of an unearned reward refused).

## PROGRESSION / ECONOMY (all through the dregg-schema keystone)
1. **CRAFTING:** a provably-fair forge that CONSUMES inputs (the economy's first sink); the outcome a verified draw; a
   legendary craft a provable flex; a forged craft mints nothing.
2. **GEAR:** assets gated CROSS-CELL by real ownership (multicell: "this ability unlocks because you own+equip the flaming
   sword" is a kernel predicate); durability as a Monotonic sink.
3. **DEEPER PROGRESSION:** the talent tree meta.rs already names (echoes-gated) + wire the built-but-idle spells.rs -> a Mage
   run != a Warrior run. Talents bought with death-earned ECHOES, never $DREGG.
4. **THE ECONOMY:** escrow swaps + sinks(craft/durability/respec/entry) + faucets(loot/echoes/quests). No-P2W BY
   CONSTRUCTION: $DREGG = the illiquid service-pile (buys cosmetics/AI-DM/seats), power from earned play, rank re-executed
   against the shared seed (can't be bought).
5. **COMPANIONS:** an owned asset FUSED with a progression cell (a provable bond, can't be faked-leveled or duped; hardcore
   permadeath makes it real).
THE KEYSTONE UNDERNEATH: build crafting/gear/talents/companions THROUGH dregg-schema (declare components, don't hand-roll a
16-slot layout each time) — one reusable game-state layer, the keystone's payoff.

## NFT (project the proven achievements onto a durable external chain + take a fee on the motion)
The provable achievement is ALREADY built dregg-native (dregg-season hall-of-fame/prestige/champions, loot.rs fair-drop
assets, the no-cheat board, meta.rs). So the NFT work is 3 new legs, not a new system: (1) the Solana EXPORT leg (the inverse
of the built import rail — a 1-of-1 SPL NFT carrying the dregg proof in its metadata; reuses HD custody signing; the
instruction-builder + RPC-submit are the gap; Metaplex/cNFT is a bigger later dep); (2) the FEE/ROYALTY rail (NO settlement
path has a cut today — a marketplace/OTC cut at settle -> the treasury, which already receives); (3) RE-IMPORT is nearly free
(ProvenForeignHolding + bridge_mint_against_lock fits a 1-of-1 SPL as-is -> mint the dreggnet-asset). Bots: /claim-a-cheevo,
an artist /store, /mint over the /gallery + deposit-address + signing pattern. Angle: EARNED, PROVABLE NFTs (a cheevo backed
by a verifiable run), not JPEGs. NOT dregg-native (dodges devnet churn); importable when stable.

## THE PORTFOLIO (the platform proof)
automatafl (a verified BOARDGAME — Lean-proven mechanics + a STARK) + multiway-tug (a verified CARD GAME — cards as assets +
a hidden hand) are the keystone's 2nd/3rd customers: if they build on dregg-schema + game-turn-slice, "dregg is a verifiable
game ENGINE" stops being a claim. Turn-based = native to a proof-carrying-turn engine. (Plans: separate docs.)

## SEQUENCING
The recurring failure mode across ALL of it: any world/game state that is host bookkeeping instead of a gated committed cell
is the LARP. Everything must be a real StateConstraint the executor re-checks + a stranger can replay. Recommended order:
lead with the CROWN (private-strategy proof-play + cheevos + un-dupable items — most crypto exists), then PARTIES + HUB (the
biggest play-together, closest to built), then QUESTS + the publish-scene flywheel, then progression (talents+spells) +
trading, with crafting/gear/companions/factions/raids/guilds/events as the deepening, all through the schema keystone.
