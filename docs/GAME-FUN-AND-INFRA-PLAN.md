# dregg game engine — fun + infra plan (2026-07-12, 3-thinker synthesis)

From a game designer (is it fun?), a platform architect (reusable engine?), and a prior-art scholar (autonomous worlds /
ZK games / what makes games fun). They converge. (Companion to docs/GAME-ENGINE-ROADMAP.md + docs/GAME-ROLEPLAY-STACK-MAP.md.)

## The diagnosis
World-class verifiable-turn engine + N-surface platform, but two gaps:
- **Not FUN yet:** "the substrate is a marvel and the core loop is a click-through." Three fun-killers, none fixable by
  more provability: **you cannot lose · your choices rarely fork · your character never changes how you play.** The
  verifiable-fairness tech is a solution in search of stakes.
- **Not a game-engine PLATFORM yet:** every non-narrative game hand-rolls a 16-slot layout + a CellProgram; no general
  game-state schema, no real-time reactive read path (indexer), no session-key play UX.

## dregg's unfair advantages (all three flagged; the AW engines would kill for these)
Verification is the SUBSTRATE not a bolt-on · a real attenuable capability/authority model (not just token ownership) ·
**attested AI narration bound to verified state = THE cure for AI Dungeon's fatal flaw** (the DM can't forget your HP or
teleport you) · provably-fair randomness native.

## TRACK A — FUN (ranked; every fix rides a tooth the engine already proves)
1. **Real loss / stakes** (biggest unlock, small). HP-zero is REFUSED not fatal (dice_combat.rs:543) -> downside risk = 0,
   which drains every other system. Route a lethal blow to a terminal DEFEAT passage (a WriteOnce `downed` flag + ->END)
   instead of gating it out; + opt-in hardcore (death WriteOnce-final) -> the no-cheat leaderboard finally means PROVING
   YOU SURVIVED.
2. **Forking dilemmas + a meaningful choice every turn** (medium). Risk-it rolls (skills.rs d20-vs-DC) + opportunity cost
   (WriteOnce: the treasure OR the key). Makes the crowd ARGUE.
3. **Flagship = a ROGUELITE on the daily procgen dungeon** (medium — reuses a finished crate). Turn-based + permadeath +
   meta-progression is NATIVE to "a turn = an attenuable proof-carrying token"; the receipt IS the run; bind a real drand
   beacon (procgen:56) -> today's dungeon is unpredictable-until-revealed -> surprise + fairness + replay + a leaderboard
   race. Precedent: Loot Survivor (genre works on-chain), Hades/STS/FTL (the fun). Real-time RTS fights the substrate.
4. **Attested-DM roguelike (the unfair advantage).** Rebuild AI Dungeon WITH the rules layer it never had: verified state
   adjudicates HP/inventory/dice, the attested LLM narrates within it. dregg's edge is decisive; the incumbent's failure
   (memory cliff + no adjudication) is documented.
5. Deeper retention: build identity (wire the persistent character's class/level into the ballot — spells.rs built+unused,
   so a Mage run != a Warrior run); loot that matters (a chest = a provably-fair draw -> a WriteOnce heap item; a
   legendary is a PROVABLE flex); the crowd IS the party (mud.rs seats, each a job); drop the finished dialogue.rs into
   the play surface; a Monotonic countdown; leaderboard streaks.

## TRACK B — INFRA (ranked; keystone first)
1. **THE KEYSTONE — a general game-state / ECS-style component schema + a VERIFIED allocator.** Author declares typed
   components -> a slot layout + a generated CellProgram + a typed API, each component -> a tooth (resource->Monotonic,
   identity->WriteOnce, stat->FieldGte+Lte, timer->temporal, inventory->HeapField, invariant->FieldLteOther). ALL THREE
   converged: the architect's #1 + the scholar's "adopt ECS (MUD/Dojo/Cardinal did)" + the "verified layout optimizer"
   forward vision. TRANSLATION VALIDATION (untrusted allocator, checked refinement). Every game type reuses it.
2. **A reactive-read INDEXER (the biggest infra gap for a PLAYABLE client).** Torii/MUD pattern — auto-index every state
   change, real-time sync, reactive queries + local tx simulation, so a client renders a living world at low latency.
3. **Session keys + passkeys + paymaster UX (Cartridge).** Cap-gated turns ARE attenuated capabilities — session keys are
   the same idea (pre-scoped authority for a play session); a natural weld to the macaroon model. Playable-vs-not.
4. **Durable persistence** (CharacterStore/Registry/session-store in-memory; seams are the trait boundaries -> pg-dregg/redb).
5. **A game-author SDK / paved path** (the Offering/Host/Frontend spine is generic; missing = a scaffold + docs/guide so a
   STRANGER ships a dregg game — the pug bar; capability confinement is the SAFE moddability pure-EVM can't offer).
6. Later: a verifiable-asset/item/economy layer (TCG/loot/betting); matchmaking + no-cheat tournaments (brackets advance
   only on verify_completion); game-tick/settlement-tick separation (World Engine/Keystone/Paima); parallel sessions.

## Failure modes (documented by the field)
Tokenomics-first (P2E collapse — fun BEFORE economy); interoperability theater; tech-demo-not-a-game (verifiability is not
a mechanic); crypto-native-only accessibility (why Cartridge exists); AI-DM without rules / with a memory cliff (AI Dungeon
— bind narration to verified state + design moderation up front); crowd-play without an aggregator (TPP Democracy mode —
but a deviant minority can be productive, don't over-sanitize); commit-reveal mid-game (use zk); real-time genres.

## Recommendation (sequence)
1. NOW for fun: **real loss + forking dilemmas** (A1-2) — cheapest, most "is it fun" conversion.
2. The flagship: **a daily-procgen ROGUELITE with an attested DM** (A3-4) — native strengths + the AI-Dungeon opportunity.
3. The keystone infra: **the game-state schema + verified allocator** (B1) — unlocks every future game.
4. The playability infra: **the reactive-read indexer + session-key UX** (B2-3) — demo vs a game people play.
