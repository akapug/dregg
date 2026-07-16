# The Descent — Content & Asset Authoring Spec (for spwashi)

A content author's guide + task spec, grounded in the real code (every claim cites file:line).
Three tracks spwashi can pick from. Of the four Rust **enablements** that pave the tracks, E1–E3 are built
(Track A details them); E4 (`/gallery publish-scene`) is the one still open, and Track B names it.

## The guiding principle (what makes this different)
Two properties the whole system already enforces, which content must ride:
1. **Provable rarity.** An asset's traits are drawn by a *provably-fair weighted draw* off a committed (drand-beacon) seed —
   so "I have the legendary" is a *proof anyone re-derives*, not a claim. Rarity = the weight of the trait-combo; the draw is
   verifiable (`procgen-dregg` transcript + `verify_generation`, `procgen-dregg/src/lib.rs:280`).
2. **Deterministic render.** traits → sprite must be a *pure deterministic function* (same traits → same image, so a stranger
   re-renders the identical asset). This matches the house norm — everything is byte-identical replay (`bindings_descent.rs`
   "a stranger re-executes byte-identically"). Free/nondeterministic art would break the "anyone reproduces it" property.

## Content is per-SEASON
The game runs as seasons (one VK-epoch's run, punctuated by upgrades — see `dregg-season/`). This matters for content:
appending to a procgen table **re-buckets every seed's draw** (`pick` is a `draw_bounded(index, table.len())`,
`procgen-dregg/src/lib.rs:902`),
which breaks re-generation of *already-published* universes. So **content expansion is a content-epoch bump = a season
boundary**, not a silent edit. A season ships a content SET (`SeasonManifest.content_tag` is the handle). Frame it as the
content cadence, not churn: each season, a fresh set.

---

## TRACK A — Generative visual assets (deterministic SVG sprites)  ⟵ the paved path is BUILT
The visual layer ships end to end — a deterministic sprite pipeline runs from committed asset identity to in-tab
vector art. What exists at HEAD:

**The pipeline (live):** `AssetId bytes → derive_key → Seed → dregg-dice DrawStream → trait vector → layered SVG`
(`dreggnet-sprite/src/lib.rs`). Pure and deterministic — no floats, no unordered iteration — so the same asset yields a
byte-identical SVG on every platform, and a stranger re-renders + verifies the identical art. Two parametric kinds ship
(`render_gear`, `render_card`), each a composed stack of layered `<g>` groups where every trait axis measurably changes
the geometry.

### The enablements (E1–E3): shipped
- **E1 — the committed trait field.** `trait_root` is a first-class `WriteOnce` 32-byte identity component on the note
  schema (`dreggnet-asset/src/lib.rs:162`), folded into `note_digest` and carried across the lineage.
  `AssetWorld::mint` populates it with a deterministic derivation of the id; `mint_with_traits` /
  `mint_soulbound_with_traits` commit an explicit root (a stat-block digest); `AssetWorld::trait_root_of` (`:765`)
  reads it back.
- **E2 — the first-class weighted draw.** `DrawStream::weighted(index, &weights) -> usize` is a provably-fair CDF
  selection over a committed weight table, one draw per index (`dice/src/draw.rs:158`). The sprite rarity axis rides it
  over the committed `RARITY_WEIGHTS` const (`dreggnet-sprite/src/lib.rs:68`) — "I drew the legendary" is a claim anyone
  re-derives. A 1/1000 tier is just a small weight; no repeated-table-slot workaround.
- **E3 — the surfaces.** wasm exports `spriteSvg` / `traitsJson` (`wasm/src/bindings_sprite.rs:130,139`); the extension
  registers the closed-shadow, port-fed `<dregg-sprite>` element (`extension/src/elements/dregg-sprite.ts`) driven by the
  background `SpriteEngine` (`extension/src/port.ts:2452`); dreggnet-web serves the art endpoint
  `GET /sprite/{kind}/{ref}` (`image/svg+xml`) + a gallery (`dreggnet-web/src/sprite.rs`).

### Named seams in Track A (labeled, not closed)
- The shipped renderers derive the trait vector from the `AssetId` bytes (domain-tagged); drawing from an
  explicitly-committed `trait_root` stat block inside the renderer is the named follow-up
  (`dreggnet-sprite/src/lib.rs` header names it).
- `dreggnet-gear`'s statblock rarity is a declared field, not yet produced by the E2 weighted draw
  (`dreggnet-gear/src/statblock.rs:24` names the seam).

### spwashi's work (Track A) — on the built path:
- **The weight tables**: the rarity distribution per trait axis (blade-shape weights, glow-rarity, palette weights, …) —
  committed consts beside `RARITY_WEIGHTS`, tuned by spwashi; committed so rarity stays provable.
- **New sprite kinds / trait axes**: extend `dreggnet-sprite`'s parametric renderers (each a pure `traits → SVG` in the
  gear/card mold) — or author JS renderers over `traitsJson`, which the `<dregg-sprite>` element + typed port already
  deliver to page JS. Either way a renderer must stay a **pure deterministic** `render(traits) -> SVGString` (vector,
  animatable via `@keyframes`/SMIL) so byte-identical re-render holds.
- Optional: a preview harness (feed random trait vectors, see the sprite range) — pure JS, no chain needed.

---

## TRACK B — Scene / content authoring (spween `.scene` + UGC)  ⟵ text, no Rust
The Descent's live daily + the no-cheat board both consume **spween `.scene`** (not the older attested-dm `.dungeon`).
`daily_scene` emits spween text (`dreggnet-offerings/src/daily_descent.rs:220`); `compile_scene` lowers gates → real
executor teeth (`spween-dregg/src/compiler.rs:374`); the leaderboard re-executes the *same* teeth, so **the no-cheat
property is preserved automatically** — no augmentation on the daily path.

### The exact authorable syntax (spween, `~/dev/spween/src/parser.rs`):
```
---
id: my-scene
title: The Salt Vault
tags: [descent]
---
=== entrance
The vault door hangs open.
* [Force it] { strength >= 5 }
  ~ noise += 1
  -> hall
* [Pick the lock] { gold >= "$price" }      # var-op-var: a REAL cross-slot tooth (compiler.rs:553)
  ~ gold -= 10
  -> hall
=== hall
...
* [Take the crown] { hands < 1 }
  ~ hands = 1
  -> END
```
- **Conditions** `{ … }`: `var op value` (`>= <= > < == !=`), membership `category.key` (e.g. `inventory.sword`), `!`, `&&`/
  `,` (AND), `||` (OR).
- **Effects** `~`: `var = v` / `var += n` / `var -= n` / `call("name", args)`.
- **Lowers to REAL executor teeth:** numeric/bool `var op literal`, membership, `Or`->`AnyOf`, `Not`, and **var-op-var**
  (`{ gold >= "$price" }`, the `$`-sigil, `compiler.rs:553`). **Handler-only (not enforced):** a gate on a var the same
  choice `Set`s, string/float compares, `!=`, deep boolean nesting. Budget: 16 slots (`STATE_SLOTS`, `compiler.rs:134`).
- **Stakes pattern** (copy Bloodgate, `dungeon-on-dregg/src/bloodgate.rs`): a warden that hits back + an HP-floor gate +
  a `[Fall…]{hp<=20}` passage that sets `downed=1 -> END` = real permadeath.

### Publishing (UGC):
- `Universe::authored_signed(name, author, source, win, parent, author_public_key, signature)` (`ugc-dregg/src/lib.rs:409`)
  content-addresses + ed25519-attests a hand-written spween world; remix lineage via the declared `parent`
  (`Universe::parent`, `:464`). The no-cheat board re-executes to the declared `WinCondition` (`verify_completion`, `:819`).
- **Enablement E4 (named gap — still open):** `/gallery publish` mints only *procgen* universes from a `seed:` string
  (`discord-bot/src/commands/gallery.rs:1094`); the `authored`-scene machinery exists + reconstructs on boot (the store's
  `authored_desc` sits `#[allow(dead_code)]`) but **no command accepts a raw `.scene`** — `dreggnet-quest` names this
  flywheel as a seam over its real core. Wiring `/gallery publish-scene <spween source>` -> `Universe::authored_signed` is
  the one surface that lets spwashi (and every player) publish hand-written universes to the board **without Rust**.
  Small; high flywheel leverage.

### spwashi's work (Track B): author `.scene` files (text) — new rooms, encounters, branching, prose, gated logic, stakes,
win conditions. Publish via E4. All executor-refereed automatically.

---

## TRACK C — Procgen content expansion (Rust tables, per-season)
`procgen-dregg/src/lib.rs`: `const THEMES: [Theme; 6]` (`:394`) is the biome table; `struct Theme` (`:348`) is one biome's
schema (adjectives/nouns/descriptions, a weapon, a `monsters: &[Monster]` slice, one `boss`, treasures, a potion, a hazard
trio, a lore NPC, a shrine spell). **Add a biome** = append a `Theme` + bump `[Theme; 6]->[Theme; 7]`. **Add a monster** =
push onto that biome's `monsters` slice. Fairness: appending re-buckets draws → **do it at a season boundary** (a content
epoch bump), never silently on a live season.

### Highest-leverage expansions (most daily variety per effort):
1. **Enrich the daily template** (`daily_scene`, `dreggnet-offerings/src/daily_descent.rs:220` — TEXT, no kernel change):
   the daily is structurally thin (one warden + a key + linear corridors + one hoard) while procgen already models
   monsters/loot/NPCs/shrines/hazards it doesn't use. Inject encounter *types* into the corridor loop — a mid-descent
   monster with an HP-floor trade, a loot/consumable choice, a skill-check door, an NPC lore gate. **Biggest single win.**
2. **Unify the daily's 4 flavor themes** (`daily_descent.rs:116`, a *separate* hardcoded table) **with procgen's 6 biomes**
   (`:394`) — one table, 4→6+ variety, every future biome flows to both.
3. **Grow `Monster` rosters + descriptions/nouns/adjectives** per biome (versioned table appends) — cheap naming variety.
4. Wire E4 (authored-scene publish) — turns the whole UGC flywheel on for text authors.

Items 1/2/4 are text/plumbing; item 3 is a versioned Rust table edit.

---

## Division of labor (the paved-path handoff)
**The enablements E1–E3 are built** (the trait field, the weighted draw, the `traitsJson` getter + `<dregg-sprite>`
element — see Track A). **Still ours to build:** E4 `/gallery publish-scene`, then the daily-template enrichment
(Track C #1) + the theme unification (#2) as the reference content.

**spwashi builds** on the paved path: the committed weight tables + new sprite kinds/renderers (Track A), `.scene`
universes (Track B), and — as versioned per-season content — procgen biome/monster appends (Track C).

**The pipeline, end to end (the Track-A half runs today):** `weight tables + a committed seed → E2 weighted draw → E1
trait_root on a minted dreggnet-asset (owned, provenance-bound) → E3 traitsJson / spriteSvg → a deterministic SVG
sprite`, and separately `spwashi's .scene → parse → compile_scene (teeth) → deploy → the no-cheat board re-executes`
(gated on E4 for non-Rust publishing). Provable rarity + deterministic render + no-cheat verification, all preserved by
construction.
