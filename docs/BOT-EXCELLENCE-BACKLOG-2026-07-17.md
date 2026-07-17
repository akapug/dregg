# Bot Excellence Backlog — 2026-07-17

Mined from three parallel adversarial reviews of the Discord bot (`discord-bot/`) —
UX/discoverability, integration-breadth, and dreggic-ness — cross-checked against code.
Ranked by value. Companion to `docs/LIVE-SURFACE-TRUST.md` and the game-affordances closure
ledger (`docs/GAME-AFFORDANCES-MAP.md` §8). This is an ASSESSMENT + backlog, not applied changes;
the top moves are ready to become lanes (the bot runs on the AWS edge, separate from the hbox
games redeploy, so these are their own workstream).

## The one-paragraph diagnosis

**The first five minutes are engineered and excellent; minute six onward was written by developers
for developers.** `/start`'s tour (identity → faucet → first paid turn, node-outage retry, step
chaining) is the best flow in the bot and genuinely dreggic — its first-turn embed literally says
*"You just did a real, paid, verifiable thing… Verify it yourself"* (`transfer.rs:322`). Then it
unravels along three axes: **(1) UX** — the game paths never `defer`, so a slow narrator shows
"This interaction failed" on a permadeath turn that already committed; payment-poll errors render
as "you have 0 credits"; several headline commands are permanent dead-ends. **(2) Ethos** — every
proof the bot surfaces is a dead end and every "verification" is the bot verifying itself; the
user reads *about* verify-don't-trust but is never handed the artifact or the button; **the crown
(fold-a-match-to-one-proof, stranger-verifies, moves never revealed) is entirely unwired.** **(3)
Breadth** — the generic offering adapter is capable and is NOT the bottleneck, but the RPG surfaces
open throwaway demo worlds instead of your real state, and the proof-crown features (NFT export,
match-fold, seasons, IPFS) are absent. Surface count is 49 commands (not ~57).

---

## TIER 1 — flows that lose a user's work, money, or trust (fix first)

1. **Game presses never `defer`; a committed permadeath turn can show "This interaction failed."**
   No `defer` anywhere in descent/fiction/portfolio/offering. `/descent` press commits on-chain
   (`descent.rs:1101`), THEN awaits narration (20s timeout, `:1156`) before the first ACK
   (`:1177`) — Discord's 3s window blows, the user sees failure on a move that permanently landed,
   and there's no "re-show my room" path (reopening abandons the run, `descent.rs:1013`).
   **Move:** defer immediately, edit after narration; add a re-render affordance. THE most
   dangerous bug in the bot.
2. **Payment-poll failure renders as "you have 0 credits."** `commands/pay.rs:83,125` map
   `poll_and_credit Err(_) => 0`; `src/pay.rs` swallows deeper. A user who just sent real $DREGG
   during an RPC error sees "0 run-credits" — indistinguishable from "my money vanished." (Now
   worse-mattering post-`e91222144`: a real SolanaWatcher's RPC outage is real.) **Move:**
   distinguish "couldn't check right now, funds safe, retry" from a genuine zero.
3. **`/key set` takes the API key as a visible slash option** (`key.rs:55`, secret sits in the
   composer in clear) — while `/start` collects the same key in a modal (`start.rs:447`). **Move:**
   `/key set` opens the same modal.
4. **`/link-cipherclerk` is a permanent dead-end** — hands a blake3 challenge, "not active until
   ownership is proven" (`federation.rs:250`), but no command submits the proof, and the pending
   state then walls the user out of all `/cap-*` (`captp.rs:580` — a literal not-built-yet
   confession in user copy). **Move:** build the prove step or unregister.
5. **Governance voting is impossible for anyone but the proposer.** The Vote modal demands the
   64-hex "Prior proposal root" (`dashboard.rs:685`) shown only in the proposer's own *ephemeral*
   embed (`:1006`); no proposals-list surface exists. Collective governance presents as a
   single-player loop. **Move:** a proposals list + vote-buttons on a public proposal card.
6. **Subscription panel promises DMs no code delivers** — "You will receive DMs when new messages
   arrive" (`dashboard.rs:1282`) but subscribe rows are only counted (`db.rs:1787`), no dispatcher
   reads them, and publish sends only a `message_hash` (body goes nowhere). **Move:** implement the
   dispatcher or label experimental.
7. **Keyless Hermes chat burns a turn and answers with a hash.** No LLM key → chat falls to the
   tool loop, commits a receipt, posts "✅ chat — cap-gated turn committed · receipt a1b2…"
   (`hermes_channel.rs:170`) — no answer, no `/key` pointer — right after the tour said "just
   type." **Move:** short-circuit keyless chat with a plain pointer to `/key`.

## TIER 2 — the ethos failures: make verify-don't-trust a VISIBLE feature

*The disease: every proof surfaced is a dead end; every "verification" is the bot verifying
itself. The user is told to trust where they could be handed the button.*

8. **THE CROWN IS UNWIRED.** `dreggnet-game-board` (play → fold to ONE `WholeChainProof` →
   proof-carrying board, `has_moves()==false`, O(1) stranger verify) has **zero references in
   `discord-bot/`**. `/play tug|automatafl` drive real matches and a win just scrolls away.
   `GameBoard`, `ProvingService::{enqueue,status,submit_when_ready}` all exist
   (`dreggnet-game-board/src/lib.rs:491`). **THE single highest-leverage move (all three reviews
   converge):** on a hidden-hand tug win, a **"Fold this match to one proof"** button →
   `ProvingService::enqueue` → honest "proving in background (minutes)" poll → on `Ready`, submit
   to the board and post *"Ranked. The board holds a proof and NO moves — your hand was never
   revealed; anyone can re-verify in O(1),"* proof envelope attached as a file that any OTHER user
   can press **Re-verify** on and watch the bot re-check publicly. One flow demonstrates every
   pillar; nothing else on Discord can do it.
9. **The no-cheat board claims replay-verification nobody can press.** `descent.rs:1427` prose says
   runs re-execute to the WIN; `Registry::reverify_entry` exists but runs only in a test
   (`:1736`); the day-universe content-address + committed seed (the exact public inputs a stranger
   needs, `:551`) are never shown. **Move:** a `Re-verify #N` button per row → live re-execute,
   "reached the WIN, verified in front of you just now"; print the universe id + seed hex so
   verification is possible outside the bot too.
10. **The flagship games are the LEAST verifiable surfaces.** `/council /market /grain /doc
    /dungeon` each register `verify`; `/play` (12 offerings incl. both games) registers only the
    offering choice (`portfolio.rs:351`) — no verify, though `offering::handle_verify::<SeatedTug>`
    is one line away. **Move:** `/play <offering> verify`, or a standing "⛓ re-verify chain" button
    on every offering surface.
11. **`/proof turn` fetches a STARK and doesn't verify it** — shows size + hex head + "Attached: ✅"
    (`explorer.rs:949`), a trust-me presentation of the one artifact whose purpose is that anyone
    can check it. **Move:** verify the bytes against the VK right there — "✓ verifies under VK
    de3f… checked just now, not trusted" + the offline re-check incantation.
12. **The surfaced `turn_hash` is a dead end** — 8 bytes shown, but sessions are process-local so
    `/explorer turn <hash>` can't find it, no link, no explanation. **Move:** make it pressable
    ("recompute this hash from the move history in front of me") + say why it matters (it chains;
    mutate any past move and it changes).
13. **`/history`/`/leaderboard` are pure trust-me sqlite** — history renders from the bot's private
    DB with no tx hash/link/receipt, though the transfer path records `tx_hash` into that same DB
    (`transfer.rs:180`). **Move:** each row carries its hash as a link + a "re-check against the
    chain" press.
14. **The macaroon keychain is a museum demo** — tokens re-materialize per command, an attenuated
    child evaporates on return, `authorize` verifies against nothing (`cipherclerk.rs:337`).
    **Move:** persist tokens + give attenuation one real consumer (the LLM proxy honors an
    attenuated `http` token's caveats) so a user watches the caveat that bit.

## TIER 3 — integration breadth: the bot as a window onto dregg

*The adapter is capable; the gaps are (a) registration, (b) real state vs demo worlds, (c) the
proof-crown layer outside the Offering trait.*

15. **Real player state under the 8 RPG surfaces** (the biggest depth failure). `/play
    trade|craft|inventory|guild|cheevos|companion|tavern|party` each open a throwaway
    `SharedWorld::demo("Adventurer")` / `CheevoShowcase::demo()` — canned, forgotten on restart, no
    composition (`portfolio.rs:22,399`). `dreggnet_surfaces::register_surfaces` already mounts ONE
    shared world across trade/craft/inventory; `dreggnet-adventure` is the whole loop as a library.
    **Move:** a per-identity persistent `OfferingHost` (sqlite-backed like characters) so a crafted
    item IS in your inventory IS tradeable — the saga composition, real. Turns 8 shallow surfaces
    into the actual game.
16. **`/descent tournament`** — `descent_tournament` is a module of a crate the bot already deps;
    welds the daily + the no-cheat gate into a weekly bracket. Near-pure registration + announce
    cron; big social payoff.
17. **NFT export** — `/export` on a verified win/champion: `dregg_pay::nft_mint` (already a dep)
    builds the 1-of-1 SPL mint carrying the proof memo. "Earned-ness travels," zero new crates.
18. **Match-fold status for `/play tug|automatafl`** — the enqueue/poll wiring of #8 (this is the
    breadth face of the crown).
19. **IPFS in `/gallery publish`** — `ugc_dregg::ipfs::{publish_universe,bundle_universe_car}`
    landed tonight (`05b8dadcb`); a `pin:true` option + the CID in `/gallery show` makes published
    universes durable across gateways. One dep + one option.
20. **Gear / Quest / Faction** — gear is cheapest (`LoadoutOffering`/`TalentTreeOffering` already
    `impl Offering` — two `DiscordOffering` blocks + `PLAY_KEYS`); quest/faction need a thin
    offering shim in their crate first. All flagship "teeth not bookkeeping" stories invisible on
    Discord.
21. **Seasons** — `dregg_season::{advance_season,champions}` + prestige over the existing board; a
    `/descent season` read + boundary cron makes the leaderboard a living arc.
22. **Governance breadth** — `/council` never reaches `cast_weighted`/`open_poll_weighted`
    (shipped `bc512214f`); none of dregg-governance's community-poll/story faces have a command. A
    `/poll` on the same engine is the "game is a little DAO" thread made visible.
23. **Overworld** — a 13th `/play` key; the region-map above dungeon+character, already an offering.
24. **Real earned cheevos** (folds into #15) — `CheevoLedger::earn` over the invoker's own
    persisted completions instead of `CheevoShowcase::demo()` (Ada's museum).
25. **Signed attribution unexposed** — every offering turn uses asserted `identity_of`; the
    `dreggnet_offerings::signed` module (landed `6fa643d05`) is unwired in the bot. The trust level
    is invisible. (Custodial cclerks make this lower-stakes than web, but the footer could say it.)

## TIER 4 — coherence, vocabulary, dead links

26. **Sweep the dead `fg-goose` domain** — stamped on every branded footer (`embeds.rs:17,24`) +
    hardcoded links at `activity_feed.rs:133`, `devnet.rs:955`, `cipherclerk.rs:292`,
    `explorer.rs:1178` (`cards.rs:47` fixed exactly this class via `DREGG_EXPLORER_BASE` tonight;
    5 sites unswept). Compounds with truncated hashes (`explorer.rs:1175`, 12 chars) whose only
    full-hash escape is the dead link — the advertised verify-a-receipt workflow can't complete.
    Joins the repo-wide fg-goose lane. **Move:** route all through `DREGG_EXPLORER_BASE`; full
    hashes in copyable code blocks.
27. **One object, four names; one word, two balances.** wallet=identity=cipherclerk=cclerk; the
    `/start` **Balance** button shows DEC, the `/balance` command shows $DREGG credits — same word,
    different money; three currencies (DEC/$DREGG/computrons) with no explainer. **Move:** one
    public noun, one setup path, rename `/balance`→`/credits`.
28. **The games are invisible from the front door** — `/help`'s power-user field lists `/cap-*`,
    `/proof`, federation but never `/descent /dungeon /play /gallery /market` (`start.rs:222`). The
    actual draw is unlisted; the plumbing is listed. **Move:** lead `/help` with the games.
29. **Stale-session hint is wrong for all 12 `/play` offerings** — "Start one with `/tug open`"
    (`offering.rs:1274`) but the real invocation is `/play offering:tug`; every stale button after
    a restart emits an un-typeable instruction. **Move:** per-offering open-hint + note sessions
    don't survive restart.
30. **Two incompatible handoff systems distinguished only by the word "real"** (`/cap-delegate`
    dash-tokens vs `/handoff` colon-tokens; `/cap-accept` silently mis-parses the colon form,
    `captp.rs:141`). **Move:** one system, cross-detect, name the next step.
31. **Silent interaction drops** — `Driven::NotOurs => {}` (`offering.rs:1093`), un-ACKed
    collective non-`Fire` presses (`:1062`), `/card` never defers. **Move:** every path ACKs.
32. **Any user can wipe a live game with no confirmation** (`open_in` "replaces any session",
    `offering.rs:239`; `/descent play` overwrites; `/market open` mid-auction nukes it). **Move:**
    refuse-with-confirm when a live session exists.
33. **`{:?}` debug dumps + jargon in user copy** — `{:?}` of a permissions struct on a *success*
    screen (`handoff.rs:308`); "Export a sturdy ref", "Enliven a shared dregg URI", "swiss table";
    executor internals as game copy (`FieldGte(hp,1)` in `/descent today`, `WriteOnce`/`Monotonic`
    in `/dungeon list`). `bounty.rs`/`polis.rs` already have the `user_message` pattern the rest
    never adopted. **Move:** adopt `user_message` everywhere; translate teeth to plain effects.
34. **Misc:** hardcore death dodgeable by waiting out a restart (progress saved only on the terminal
    move, `descent.rs:476`); no pagination anywhere; `/send` success is ephemeral-only (invisible
    social feature); dashboard "Request Proof"/"Resolve Name" buttons always fail; `/dungeon` rounds
    only advance on a manual `/dungeon close` the ballot never mentions.

## The top moves (if you do five things)

1. **Defer-everywhere in the game paths** (#1) — stops losing committed permadeath turns to
   "interaction failed." Safety first.
2. **Ship the crown: "Fold my match" + public stranger-verify** (#8) — the one thing no other
   Discord bot can do; makes dregg's magic visible in one flow.
3. **Real per-identity persistent world under the RPG surfaces** (#15) — turns 8 demo-world
   surfaces into the actual composing saga.
4. **Sweep dead links + one vocabulary + games in `/help`** (#26/#27/#28) — un-terminates the exact
   workflows the bot tells users to try.
5. **Payment errors that don't read as "money vanished"** (#2) — trust-critical now that the real
   watcher landed.

## The baseline that's already good (spread this register)

`/start`'s tour + node-outage retry; the adapter's honest `outcome_note` ("Refused — nothing
committed, no receipt"); `transfer.rs`'s "Verify it yourself" first-turn embed (the most dreggic
moment — make it not happen only once); `/descent`'s beacon-honesty footer + the tooth shown on
refusal; boot preflight failing fast on FEDERATION_ID mismatch with the exact fix; gallery's
re-verified persistence. These are the standard; bring minute-six-onward up to them.
