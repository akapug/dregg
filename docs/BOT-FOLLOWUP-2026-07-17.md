# Bot FOLLOWUP Wave — 2026-07-17 (tidy · excellence · repair)

What the follow-up wave landed **on top of** the ultracode run whose final state is
`docs/BOT-E2E-GAPMAP.md`. Where this document and the gap-map disagree on a deep-gap
status, THIS document is later and wins (the gap-map's flow table remains accurate; its
"Deep gaps" section is updated below). Backlog `#N` numbers refer to
`docs/BOT-EXCELLENCE-BACKLOG-2026-07-17.md`; the cutover design is
`docs/BOT-SHARED-BACKEND-DESIGN.md`. Everything here is verified by reading the code at
HEAD and by the repair phase's real gate output (quoted verbatim in §5), not by lane
self-reports.

## The one-sentence shape

The wave closed the gap-map's **deep gap 5 entirely** (crown `/crown`, descent
`Re-verify #N`, the persistent per-identity RPG world, `/council` on the verified
weighted engine), **built the Telegram runtime shell** (deep gap 1's Telegram half is now
code-complete and ops-gated on one BotFather token, WeChat unchanged), and moved the
**Discord catalog cutover** (deep gap 4) from "bespoke, drifting" to "one mounting table,
parity-pinned to the live registrar" — with Phase C (routing through the registrar
itself) the named remaining step.

## 1. Deep-gap status updates (supersedes gap-map §"Deep gaps")

### Deep gap 1 — Telegram/WeChat runtime: **Telegram BUILT + TESTED, NOT DEPLOYED; WeChat unchanged**

`dreggnet-telegram` is no longer library-only. At HEAD it has:

- a real `[[bin]]` (`src/bin/dreggnet-telegram-bot.rs`) and the runtime module
  (`src/runtime.rs`): `BotApi` (getUpdates long-poll, answerCallbackQuery,
  getMe startup token check), pure `parse_updates` decoding, `route_callback`/`route_text`
  into the ONE `TelegramHost` router, and `run_update_loop`;
- the live byte seam: `src/reqwest_transport.rs` — a blocking reqwest+rustls `HttpPost`
  impl (no tokio, mirroring the discord-bot's reqwest posture); everything above the seam
  stays net-free and driven;
- a **durable session store**: `durable_telegram_host` over
  `dreggnet_offerings::FileResumeStore` — every open + landed advance persists as a
  move-log, boot RESUMES by replay, a tampered log refuses to reopen (fail-closed), and a
  stale button pressed after a restart auto-rebinds its chat and still lands; the
  consumed getUpdates offset persists too (no double-routing across restarts);
- a user-facing command surface: `/offerings`, `/open <key>`, `/verify` (real replay
  re-verification), `/act <turn> <arg>`, `/help`;
- the deploy unit + runbook: `deploy/telegram/dregg-telegram-bot.service`,
  `deploy/telegram/RUNBOOK-TELEGRAM.md`.

Gate: `cargo check -p dreggnet-telegram --all-targets` GREEN; `cargo test -p
dreggnet-telegram` **23 passed, 0 failed** (driven 4, dungeon 7, full_parity 3,
multi_offering 6, runtime_shell 3). The ONE thing no test can supply is the real
`api.telegram.org` edge — see §4.

**WeChat stays library-only** (no bin target, no runtime module) — the WeChat half of
deep gap 1 is still open and is its own lane.

### Deep gap 4 — Discord catalog cutover: **PARTIAL (census unified + parity-pinned; Phase-C routing remains)**

`discord-bot` now depends on `dreggnet-catalog`, and `commands/offering.rs` replaced the
old shape (two hand-maintained ~15-arm matches plus a folklore count) with **ONE mounting
table** — the `for_each_generic_offering!` macro (offering.rs:1445, 20 offering types
including the new gear ×2 and overworld) from which both routers (`route_component` /
`route_modal`) and the key census expand. The offering **set** is pinned by a
both-polarity parity test (`the_mounted_offerings_are_exactly_the_shared_catalog`,
offering.rs:1635): everything `dreggnet_catalog::full_catalog_host` serves is reachable
on Discord, and every mounted key is either a catalog offering or a declared Discord
extra — registering a new catalog offering fails the test until Discord serves it.

**What remains (honestly):** Discord still *serves* through its per-type
`DiscordOffering` impls and per-type stores; it does not yet route by key string through
`full_catalog_host` itself. That is Phase C of the shared-backend design (the
`generic_offering_keys` census is explicitly runtime-unused until then —
offering.rs:1473-1474). Cutover = drift-proofed and parity-gated, not yet
registrar-served.

### Deep gap 5 — the remaining Discord Tier-1s: **CLOSED, all four**

- **#8 THE CROWN — `/crown`, wired** (`commands/crown.rs`; registered main.rs:370,
  routed :530, `crown:` component prefix :567). A finished `/play tug|automatafl` match
  folds in the background (`dreggnet_prove_service::MatchProveService` running the
  deployed `prove_turn_chain_recursive` on a bounded worker pool — honest
  "proving in the background (minutes)" poll, nothing spins), and the proof — never the
  moves — is submitted to `dreggnet_game_board::GameBoard`: verified O(1),
  `has_moves() == false`, proof envelope attached as a file, and a **Re-verify** button
  any stranger can press. Honest scope is in the module docs and repeated in the post:
  the deployed STARK is succinct not hiding ("moves never posted" is data-availability
  privacy, not a crypto-ZK transcript claim); the automatafl fold drives the committed D1
  chain (the game crate's own named residual); the board is in-process, like the other
  session state.
- **#9 Descent re-verify, user-facing** (`descent.rs`): per-row **Re-verify #N** buttons
  (`descent:rv:<completion_id hex>`, deliberately no owner gate — ANY presser) re-execute
  that entry's recorded moves through the no-cheat gate in front of the presser; `/descent`
  also carries a "re-verify your current run's committed chain by replay" action; the
  board loads + re-verifies from the durable store on first touch after a restart. 12
  descent tests in the green suite.
- **#15/#24 The persistent per-identity RPG world** (`commands/rpg_world.rs`): the eight
  `/play trade|craft|inventory|guild|cheevos|companion|tavern|party` keys no longer open
  throwaway `SharedWorld::demo` worlds — each player's derived identity gets one
  persistent `OfferingHost` built by `dreggnet_surfaces::register_surfaces` (the same
  one-call registration web uses), so trade + craft + inventory share ONE `SharedWorld`:
  a forged Greatblade IS in your inventory IS listable, as the same note-cell.
  Persistence is replay, never a state blob (`SqliteRpgResumeStore`; craft-first replay
  ordering because craft is the only surface that mints; tampered logs fail closed). The
  module names its residual: exact cross-session interleaving is not recorded, so an
  exotic opposite-order interleave over one note can re-drive to a refusal.
- **#22 `/council` reaches the verified weighted engine**
  (`commands/council_weighted.rs`; `pub mod` in commands/mod.rs:91): `/council open
  weighted:true` builds the offering via `CouncilOffering::new_weighted`, PROPOSE opens
  through `collective_choice::open_poll_weighted_gated`, every APPROVE/REJECT lands
  through `collective_choice::cast_weighted` — one nullifier carries the member's whole
  weight, quorum is a weight threshold with the distinct-approver floor, zero-weight
  casts refused fail-closed. **Weight provenance is stated on the surface**
  (`WEIGHT_SOURCE_NOTE`): weight = 1 + run-credits at open — bot-recorded standing from
  the paid-credit ledger, NOT a consensus-proven on-chain holding; the
  proof-of-holdings path (`dregg_governance::holding_weight`) is the named upgrade. 10
  council tests in the green suite.

Beyond deep gap 5, the excellence wave also landed from the backlog: **#17** `/export`
(a VERIFIED Descent board completion → 1-of-1 SPL NFT via `dregg_pay::NftMinter`; the
mint is refused without a real proof commitment; RPC refusals reported in their own
words), **#20** gear (`LoadoutOffering`/`TalentTreeOffering` in the mounting table),
**#23** overworld (13th `/play` key), **#26** the fg-goose sweep (cards, explorer_link,
devnet all route through `DREGG_EXPLORER_BASE` with anti-fg-goose test asserts), part of
**#27** (`/credits` + `/buy-credits`; `/treasury` for the two-balance fuel/pile), and
`/link-prove` (#4's completion, already in the gap-map). The registered-command list and
the router are pinned equal by a unit test in main.rs.

### Deep gaps 2, 3, 6 — **unchanged, still their own lanes**

- **2 Cross-platform identity:** TG/WX derivations still take no `federation_id`;
  separate bot secrets; `/link-prove` remains the ceremony shape to generalize. (The TG
  runbook's `TELEGRAM_BOT_SECRET` pin protects identity stability across token rotation —
  it does not link platforms.)
- **3 Platform-agnostic economic layer:** TG turns still run UNMETERED — the runtime
  shell routes turns and verification but charges nothing; faucet/credits/pay remain
  welded into `discord-bot`.
- **6 TG/WX council electorate enrollment:** still constructor-time (the TG shell seats
  the electorate from `TELEGRAM_COUNCIL_UIDS` at boot; runtime enrollment still needs to
  reach the live `CouncilOffering`).

## 2. Tidy phase — what it consolidated

One flagged nicety, reconciled in the repair phase: `discord-bot/src/cards.rs` carried a
private twin of the shared `src/explorer_link.rs` helpers. Consolidated —
`explorer_link::short_ref_with_base` exposed `pub(crate)`, cards.rs imports the shared
module, the twin deleted (~25 lines). **One deliberate behavior delta**, adopting the
shared module's law: with NO `DREGG_EXPLORER_BASE` set, activity-card cell/tx ids render
as the FULL copyable id instead of a truncated `abcdef01...` dead end. Tests pin the new
rule; the full suite re-ran green after the edit.

## 3. Repair phase — what it verified and reconciled

Every lane's wiring was verified **by reading main.rs**, not by trusting lane reports:
`dreggnet-catalog` dep present in `discord-bot/Cargo.toml`; `pub mod council_weighted;`
present; `/council` (main.rs:359 register, :520 route) and `/crown` (:370, :530, plus the
`crown:` component prefix :567) both in `REGISTERED_COMMAND_NAMES` + the router, with the
sync unit test passing. **Central registrations needed: none** — every lane had landed
its own. No conflicts between the catalog-cutover `offering.rs` and any other lane's
edits (no other lane touched offering.rs). Nothing left unlanded.

## 4. DEPLOY-READY vs token/ops-gated

**DEPLOY-READY now — the discord-bot redeploy.** The crate is committed and green at
HEAD (gates in §5): rebuild + restart the bot on the AWS edge and the whole wave ships —
`/crown`, `/export`, `/council weighted`, descent `Re-verify #N`, the persistent RPG
world, `/credits`/`/buy-credits`/`/treasury`, `/link-prove`, honest pay-poll errors, the
defer-before-narration fix. Slash-command re-registration happens on boot (the
names==router sync test guards it). Ops notes for the redeploy, none blocking:

- set `DREGG_EXPLORER_BASE` if explorer links are wanted — without it, ids render as
  full copyable text (the new law), never a dead fg-goose URL;
- `/export` uses `DREGG_PAY_RPC` (devnet default) and the operator seed's HD custody;
  an unfunded authority or down RPC is reported in its own words, not smoothed;
- gallery IPFS pinning is only real with the deploy's IPFS endpoint (CID derivation is
  network-free either way);
- the crown board and offering sessions are in-process — restart-lossy, as documented.
- the ONE thing only the deployed run can confirm remains the 3-second ACK discipline
  under real gateway latency — the gap-map's checklist is the script for that run.

**Token/ops-gated — the Telegram bot.** Code-complete, driven green, NOT deployable by
any agent: the real run needs ember to (1) mint the BotFather token, (2) write the env
file (`TELEGRAM_BOT_TOKEN`, recommended `TELEGRAM_BOT_SECRET` pin, optional
`TELEGRAM_COUNCIL_UIDS`), (3) `cargo build --release -p dreggnet-telegram`, (4) install
`deploy/telegram/dregg-telegram-bot.service` as a user unit. Full steps + failure modes:
`deploy/telegram/RUNBOOK-TELEGRAM.md`. Outbound 443 only — no listening socket, nothing
public to expose. Nothing else is missing.

## 5. Real build state (repair phase gate output, verbatim)

- `cargo check --all-targets` — GREEN, **zero warnings from dregg-discord-bot** (all 66
  warning lines belong to upstream path-dep crates other lanes are churning:
  dregg-circuit ×18, dregg-sdk ×5, starbridge-v2 ×4, dungeon-on-dregg ×2,
  dregg-lean-ffi ×2, +9 singles — none in the bot crate).
- `cargo test` (discord-bot) — **309 passed; 0 failed** (includes the catalog-parity
  tests, the 10 council tests, 12 descent tests, and the main.rs
  `REGISTERED_COMMAND_NAMES == router` sync test).
- `cargo check -p dreggnet-telegram --all-targets` — GREEN (only warning = a
  pre-existing `dreggnet-web` dead field, not this crate).
- `cargo test -p dreggnet-telegram` — **23 passed; 0 failed**.

Files edited in the repair phase itself: `discord-bot/src/explorer_link.rs`,
`discord-bot/src/cards.rs` (the §2 consolidation). Upstream-crate warnings in the shared
build are other lanes' churn, untouched.
