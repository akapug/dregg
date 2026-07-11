# Verifiable Interactive Fiction

A handful of small games over one idea: **a story you can trust.**

> the AI narrates · the world resolves · the crowd decides · the chain remembers

An AI may narrate anything, but it can only *do* what the rules allow — **prose is not power**.
A crowd can co-author a branch, and no one can quietly rewrite what was witnessed. Every turn is a
signed, replayable entry in a hash chain a stranger can check.

---

## The games

### AI dungeon crawlers — the AI narrates, the world resolves
Five dungeons over one attested engine (`attested-dm`). The model proposes a *typed* action; the
**world** resolves it deterministically. You cannot narrate yourself through a locked door.

| game | mechanic | play |
|---|---|---|
| **The Sunken Vault** | the crawl — light, key, sword, amulet, escape | `/vault` · `cargo run -p attested-dm --example play` |
| **Bramble Keep** | world-bounded NPCs + multi-turn HP combat | `/vault` picker · `--example play2` |
| **The Starfall Spire** | bounded spellcasting (learn from grimoires, cast in-context) | `/vault` picker · `--example play3` |
| **The Deepdark Mine** | light as a depleting resource (race the dark) | `/vault` picker · `--example play4` |
| **The Venomous Deep** | consumables + timed status (poison ford, shield-elixir, antidote) | `--example play5` |

Further engine capabilities (Rust-authored; see the examples): a **turn-based combat encounter**
(initiative + abilities + targeting, `--example combat`), and a **verifiable-random loot chest**
whose drop is a fair, replay-checkable draw (`--example loot_chest`).

The world-bounded parts are load-bearing: the Hedge-Witch trades the sickle *only* for the nightshade;
an unlearned spell does nothing; the lamp burns down and the dark is impassable without it; a healing
potion heals exactly what its rule says. A jailbroken narrator saying otherwise changes nothing — the
rules decide, not the prose.

### The Overworld — `/region`
The five dungeons are **locations in one navigable region** with completion-gated travel: a forward
road opens only once its prerequisite dungeon is *genuinely cleared*. Completion is
**verification-gated** — a location credits only on a `Won` chain that passes both `verify()` and
`verify_replay()`, so progress can't be forged (a wrong-game, unfinished, or tampered session is
refused). The map renders your progress; each node opens its game.

### The Collective Dungeon — `/party`
A crowd votes the party's next move with buttons; the world still resolves the winner. Vote to force a
locked exit and watch it refuse — collective choice does not bypass the gates. The vote runs on the
real `collective-choice` engine: each ballot is a `WriteOnce` cap-bounded turn, the tally is
`Monotonic`, and a round certifies only once the polis `AffineLe` **quorum gate** (M = 3 of the
5-seat roster) admits the decision-turn — a quorum-met close emits a **verifiable quorum certificate**
(with a light-client recomputation), not a bare count.
*Honest scope: quorum-certified over **demo identities** (each seat's key is `blake3(name)`); a
production deployment adds real **custody keys** per seat.*

### The Attested Dungeon — `/dungeon`
Jailbreak the dungeon-master for real. It will crown you King of Eternity; the ledger says you hold no
crown. The model proposes; the capabilities dispose.

### Collective fiction — `/` (The Commons) and The Drowned Library
A crowd co-authors a branching story. Votes are custody-signed and **quorum-certified** by the real
`CollectiveChoiceEngine`; the founding record cannot be quietly rewritten.

---

## Authoring — no Rust, no recompile

- **Stories** (`.scene`) — the `/author` page compiles a story you type *in the browser tab* and plays it
  verifiably (`StoryWorld::new(source)`). A broken scene shows a line-pinned error and mounts nothing.
- **Dungeons** (`.dungeon`) — a readable text DSL (`attested_dm::parse_dungeon`) covering rooms, gated
  exits, items, use-rules, NPCs, dialogue, combat, spells, light, and consumables/status. `validate()`
  catches dangling exits, an objective unreachable from the start, an unplaced win/gate item, an
  NPC/combat/spell in an unknown room, and a spell with no learn source. The `/forge` page: write a
  world, watch errors surface live as you type, hit **Play** — a model narrates it while the chain
  remembers it. A dungeon that exists *only as text* plays to a win through the same engine
  (`cargo run -p attested-dm --example play_authored`). **Full guide:**
  [`docs/AUTHORING-DUNGEONS.md`](../docs/AUTHORING-DUNGEONS.md).

Sample worlds live in `attested-dm/dungeons/` (`lantern_fen`, `clockwork_orchard`, `ember_observatory`,
plus a deliberately-`broken` one for the validator).

---

## The narrator — hosted, metered

Rooms and actions are narrated by a hosted model (**Claude Haiku 4.5 via AWS Bedrock**) behind a **hard,
self-enforced USD ledger** (`dregg-narrator`, default $20):

- a pre-flight **reservation refuses before any network call** if it would exceed the cap;
- a **corrupt ledger fails closed** (never silently resets to $0); a missing one starts at $0;
- an **unpriced model is refused** — you cannot cap a cost you do not know;
- `kind()` never names a model that did not actually produce the text.

It falls back to a local model (`ollama`) or a deterministic scripted narrator, always labeled honestly.
Prices are pinned from the AWS Pricing API where verifiable, else as a documented conservative upper bound.

---

## What is proven (the teeth)

Verification is a **ladder of independent, checkable guarantees** — reported as levels, never one
green check. Full detail in [`docs/TRUST-LEVELS.md`](../docs/TRUST-LEVELS.md).

- **Input** — the player is confined to a template slot (`slot_confinement`); a `{{`-bearing field is
  refused *before* the model is called, so it cannot rewrite the DM's rules.
- **Output** — the model proposes through one closed typed channel; capabilities + the world's rules
  dispose. Prose is not power at the level of grants, game moves, dialogue, spells, light, and combat.
- **Integrity (`verify`)** — a real prev-linked hash chain; truncate / reorder / splice are caught.
- **Rule-correctness (`verify_replay`)** — re-runs the resolver over every bound action from genesis
  and checks each effect; a forged "valid chain, wrong effect" playthrough is *caught* by replay.
- **Fair randomness (`dregg-dice`)** — loot/combat rolls are non-grindable, reject-free-unbiased draws
  bound into the receipt and reproduced by replay. The strongest source is a **post-quantum LB-VRF**
  (`pqvrf`) whose uniqueness reduces to Module-SIS (*proved* in the Lean), with a Hybrid
  VRF+beacon+timeout that leaves withholding no reroll.
- **Resumable, self-verifying saves** — `save()`/`load()`; a load re-verifies both tiers and refuses a
  tampered save.

## Honest scope

- The attestation's *authentic* leg is an in-tree fixture — it does **not** prove a real model produced
  the bytes. Its *well-formed* leg (a JSON-parse certificate) is genuine.
- The `/party` vote is **quorum-certified** on the real `collective-choice` engine (the same substrate The Commons uses) — over demo identities; the remaining production step is real custody keys per seat.

---

## Run it

```sh
# The collective stories play out of the box:
node demo/serve.mjs                 # → http://127.0.0.1:8787/hub

# The AI dungeon games also need the game service (a real GameSession over the engine).
# It narrates via Bedrock Haiku (AWS creds present) → ollama → scripted, whichever is available.
cargo run -p dungeon-service        # terminal 1 — binds 127.0.0.1:7878
DM_PORT=7878 node demo/serve.mjs    # terminal 2 — proxies /game + /party + /game/author

# open http://127.0.0.1:8787/hub  → every game
```
> Passkey voting on The Commons needs `localhost` (not `127.0.0.1`) — WebAuthn rejects a bare IP.

**Driven proofs** (each writes a screenshot + transcript to `demo/run/`):
`run-vault.mjs` · `run-games.mjs` · `run-party.mjs` · `run-forge.mjs` · `run-author.mjs` · `run-dungeon.mjs` · `run.mjs`

## Tests

- `attested-dm` — 120 lib + 19 DSL + 6 savegame tests; `play`..`play5` / `play_authored` / `combat` /
  `loot_chest` / `verify_replay` / `overworld` all win + verify.
- `dregg-dice` — 34 tests (unbiased chi-square draw, grinding-detection, LB-VRF forged-proof-rejected,
  Hybrid timeout-no-reroll, wrong-epoch/wrong-beacon rejected).
- `pqvrf` — 11 tests (LB-VRF correctness + the uniqueness→Module-SIS extraction, forged-proof rejected, few-time).
- `dregg-narrator` — 11 ledger tests (refuse-before-network, concurrency, corrupt-fail-closed, unpriced-refused, kind-honesty) + a live Bedrock smoke behind `DREGG_NARRATOR_LIVE=1`.

*(`OPEN-ME.md` keeps the detailed walkthroughs and the recorded driven-run transcripts.)*
