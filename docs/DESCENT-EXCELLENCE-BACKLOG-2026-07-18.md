# The Descent — Excellence Backlog (2026-07-18)

A read-only UX / loop / onboarding / presentation / **feel** audit of dregg's flagship
game, *The Descent*. Scope is deliberately the **surface a stranger meets** — the daily
loop, first-run, the no-cheat board as a social artifact, the embeds/copy/pacing, and the
reach (Discord vs web/Telegram). **Out of scope** (belongs to the Lean terminal authoring
the dungeon): the game rules, the AIR/circuit/constraint layer, `daily_scene`'s move math,
`dungeon-on-dregg`, `spween-dregg`, and any "does the prover accept X" question. Where a
finding brushes the rules substrate it is tagged **[for the Lean terminal]** and dropped.

The verdict up front: the *substrate* is excellent and the *presentation is honest*, but
the **flagship is Discord-only in practice**, its designed viral loop (the shareable
verified run) is built-but-unlinked, and its daily retention hook is a bare opt-in text
line. A stranger who hits the product website's "Play The Descent" button lands on a
**scoreboard, not a game**. The gap between "the engine is real" and "a stranger can meet
it and want to come back" is the whole backlog.

---

## What is genuinely great (keep, and lean on)

- **The no-cheat board is a real, legible, differentiated magic trick.** `/descent board`
  mints **Re-verify #N** buttons (`descent:rv:<completion_id hex>`) and
  `handle_reverify` *re-executes a ranked run live, in front of the channel* against a
  fresh seed, timing it ("checked just now … {elapsed_ms} ms"), and prints the exact
  public inputs a stranger needs to repeat it outside the bot. Nothing else in the genre
  does this. It is the single best asset here.
- **Permadeath is real and the copy sells it.** The death embed —
  `"💀 PERISHED — the descent is lost / A blow you could not answer felled you. Your
  hardcore character has PERISHED, un-undoably — the death carries to every future day."`
  — lands the stakes honestly, and the substrate backs it (`character.perish()`,
  `WriteOnce`-final).
- **Honesty in the footer is a brand pillar, not a wart.** `footer_text` reports the
  narrator kind, the **live-vs-pinned beacon status**, and the tagline
  (`"beacon-seeded · permadeath · the chain remembers · no-cheat board"`). The
  `BeaconStatus::PinnedFallback` label literally tells the player "daily world repeats
  until the reveal cron reaches drand." This is the right register.
- **The recovery affordances are thoughtful.** `/descent room` re-shows a lost room, a
  re-`/descent play` never abandons a live run, and every press is ACK'd inside the 3s
  window before the ~20s narrator runs so a slow narration never surfaces as "This
  interaction failed."
- **The web provenance surface is beautiful and sound** (`dreggnet-web/src/descent.rs`):
  the run-card stamps a **PASS/FAIL** certificate by *re-executing on render*, and the
  leaderboard excludes forgeries by re-verification, never by a stored flag.

The problem is almost never the depth of what's built. It's that the best parts are
**buried, unlinked, or unreachable off Discord**.

---

## HIGH — make the flagship excellent

### H1. The product's "Play" button lands on a leaderboard, not a game (dead-end for every non-Discord stranger)

**What's wrong.** *The Descent is playable only in Discord.* Every web and Telegram
call-to-action promises play and delivers a scoreboard:

- `dreggnet-web/src/lib.rs:2140` — `<a class="play" href="/descent">Play today's descent →</a>`
- `dreggnet-web/src/lib.rs:2715` — `<a class="btn btn-primary" href="/descent">Play The Descent →</a>`
- `dreggnet-web/src/telegram_miniapp.rs:702` — `<a class="btn btn-primary" href="/descent">Play today's descent</a>`

…but the `/descent` route is `get_leaderboard`:

```rust
// dreggnet-web/src/descent.rs
.route("/descent", get(get_leaderboard))
.route("/descent/", get(get_leaderboard))
.route("/descent/leaderboard", get(get_leaderboard))
```

Telegram punts entirely — `dreggnet-telegram/src/host.rs:281` tells the user *"The
Descent is NOT in this catalog … Play it at {base}/descent"* (again, the leaderboard).

A **playable** surface actually exists — `<dregg-descent>` (`extension/src/elements/`)
over the wasm `DescentWorld` (`wasm/src/bindings_descent.rs`) plays the whole run in-tab,
private and verifiable — but it is wired **only inside the browser extension** (a
`chrome.runtime` message port to a background `DescentEngine`). No served HTML page mounts
it; the only host is `extension/tests/dregg-descent/fixture.html`. So a stranger with a
URL cannot play in a browser; play requires either Discord or installing the extension.

**Why it matters for a flagship.** This is the first impression on the *product website*.
"Play" that yields a table of hex-named strangers is a broken promise at the exact moment
you are trying to convert a curious stranger. It also silently narrows the flagship's
reach to "people already in the Discord."

**Concrete fix.** Two honest paths, do the cheap one now:
1. *Now (S–M):* relabel the web/Telegram CTAs to what they are — "See today's no-cheat
   board" — and add a **real** primary CTA that routes to play: a Discord install/deep
   link, or a `/descent/play` page.
2. *The real win (L):* mount the already-built `<dregg-descent>` + `DescentWorld` on a
   served `GET /descent/play` page (ship the wasm bundle to the page, not only the
   extension). ~80% of the client exists; what's missing is a page that hosts it without
   the extension. This makes the flagship reachable from a plain URL — the strategy's
   "playable by normal humans."

**Effort.** S–M to stop lying; L to serve web play.

---

### H2. The designed viral loop — the shareable verified run — is built but never linked from the win

**What's wrong.** The strategy's growth artifact is *"I survived today's Descent — and I
can prove it,"* and it is **built**: `dreggnet-web`'s `GET /descent/run/{id}` renders a
run-card that re-executes the run and stamps PASS. `daily_descent.rs` and
`descent.rs` both say the bot's result embed is supposed to carry that link — the web
module even exposes `run_share_path(run_id)` "the shareable link shape the bot's result
embed points at."

But the Discord win never emits it. `result_embed` (descent.rs:1633) prints the verdict,
the board rank, and *"run `/descent verify`"* — and **no share URL**. The winning player is
handed the trophy and no way to show it to anyone outside the channel.

**Why it matters.** This is *the* flagship's viral mechanic per the strategy ("the
shareable verified run," Phase 3.2), and it's a two-line hole between two finished halves.
A win that can't be shared as a proof is a win nobody hears about.

**Concrete fix.** On a landed terminal run (won *and* honestly-lost — both re-verify),
ingest its reproducible input to the web board (`POST /descent/submit`, or a direct
`DescentState::ingest`), get the `sub-…` run id, and add a field to `result_embed`:
"**Share this verified run →** `https://<host>/descent/run/{id}`". The link opens a page
that re-proves the run to a stranger. Consider the same on the death embed ("a lost run
still verifies — here's the proof of how far you got").

**Effort.** M (mostly the bot→web ingest wire; the web side is done).

---

### H3. The daily reveal — the entire retention engine — is a bare, opt-in text line

**What's wrong.** For a daily game, the reveal *is* the product ("at midnight the
leaderboard freezes and a new dungeon is revealed" — GAME-STRATEGY). The reveal cron is
wired (`reveal_cron::start`), fetches + verifies live drand, and rolls the day. But its
announcement is:

```rust
// reveal_cron.rs — announce()
let body = format!(
    "**{}** — today's Descent is open. A beacon-seeded, permadeath run everyone plays; a WON \
     run ranks on the no-cheat board. Descend with `/descent play`.",
    reveal.title
);
```

…posted as **plain content**, and only if the operator set `DESCENT_ANNOUNCE_CHANNEL_ID`.
No embed, no theme art, no "yesterday's champion," no scouting line, no Play affordance, no
pin. The cron's own doc admits it: *"A live posting surface (a rich embed, a pinned
spectator message) is the frontend lane above this core."* That lane is empty.

**Why it matters.** A daily game with a forgettable reveal has no daily. This is the
single highest-frequency, highest-leverage surface The Descent owns, and it's a sentence.

**Concrete fix.** A rich, pinned reveal embed: the day's theme + a one-line "scouting
report" (warden strength → "stout: bring the field-dressing"; depth), **yesterday's
winner and their turns**, a run/survivor tally, and a button to `/descent play` (and to
the board). Promote the announce channel from an env var to first-class config. Repost/pin
daily. This is also where H2's share links and H7's board naturally surface.

**Effort.** M.

---

### H4. The leaderboard shows hex-fragment identities, not names — the social hook is illegible

**What's wrong.** The board's "player" is a raw slice of the derived identity:

```rust
// descent.rs
fn short_player(p: &str) -> String { p.chars().take(12).collect() }
```

So `/descent board` and the rank line read as a column of 12-char hex prefixes, not
"**Ada** beat **Bran** in 9 turns." The no-cheat board's whole point is social bragging,
and it's rendered in a font only a hash could love.

**Why it matters.** A leaderboard nobody recognizes themselves or their friends on
generates zero social pull. The identity hash is the right *provenance* key and the wrong
*display* key.

**Concrete fix.** The bot already holds discord-id → identity. Resolve board rows and the
"ranked #N" line to Discord display names (fall back to the short hash only for identities
the bot can't resolve — e.g. web-submitted runs). Keep the hash available as the
provenance/verify handle. Do the same on the web leaderboard where a display name is known.

**Effort.** S–M.

---

### H5. First-run has no stakes moment and no class choice — the flagship opens mid-fight, unclassed

**What's wrong.** `/descent play` drops the player **straight into the gate room** with
prose + a vitals HUD + five move buttons. The framing that makes this game *matter* —
permadeath, a *permanent* character, a no-cheat board — lives entirely in `/descent today`,
which a new player has no reason to run first. And class is a **slash sub-option**:

```rust
CreateCommandOption::new(CommandOptionType::String, "class",
    "Pick your class if unclassed (warrior / mage / rogue) — frozen once chosen")
```

A newcomer who types `/descent play` and presses buttons never sees the stakes copy and
plays **unclassed** (class shows "unset"), silently forgoing a `WriteOnce` choice that
"makes a Mage run != a Warrior run" (the Phase-0 deliverable). Ten-second comprehension is
partial: the buttons are self-explanatory, but *why the run matters* is not on screen.

**Why it matters.** The first 10 seconds decide whether a stranger cares. Right now the
weight of the game (permanence, provable survival) is invisible at the exact moment it
should be the hook, and the one identity choice is easy to skip.

**Concrete fix.** Detect a first-ever run (character has no class and 0 turns) and show a
**one-screen intro before the gate**: two lines of stakes ("one life, one dungeon a day, a
death is forever, a win is provable") + **class-pick buttons** (Warrior/Mage/Rogue) that
open the run on press. Returning players skip straight to the gate. This also fixes the
silent-unclassed problem without adding a command to memorize.

**Effort.** M.

---

### H6. The "daily" may not be daily — the pinned fallback is one identical world, forever

**What's wrong.** When the live drand fetch hasn't populated the cache,
`resolve_todays_beacon` serves a **single pinned round** (`DRAND_QUICKNET_ROUND =
1_000_000`), and *every* fallback day draws the **same** `daily_scene(seed)` — the same
dungeon. The footer is honest about it ("daily world repeats"), but honesty about a broken
daily loop is not a working daily loop. Given the devnet reality (the bot has run hand-run,
non-durable), the fallback is a live risk, not a theoretical one.

**Why it matters.** A daily roguelite whose world doesn't change daily has no reason to
return tomorrow. This is the retention engine failing closed to "Groundhog Day."

**Concrete fix.** Two layers:
1. *Code (S):* make the offline fallback **date-derived**, not a single pinned round —
   fold the UTC day number into the fallback seed so the world at least varies by calendar
   day even with no drand. Keep the footer honest ("offline: date-seeded, not
   beacon-verified fresh") so nobody claims un-grindability it doesn't have.
2. *Ops:* ensure the reveal cron actually runs on the durable deployment with drand
   reachable (the real fresh-daily path). Tracked as deployment, not code.

**Effort.** S (date-seeded fallback) + ops.

---

### H7. The best thing here — the live re-verify board — is buried behind a command nobody types

**What's wrong.** The Re-verify-live-in-channel button (see "what's great") is only
reachable via `/descent board`. A new player finishes a run and is never shown the board,
never sees the trick that makes this game unlike any other daily.

**Why it matters.** You have a genuinely novel, screenshot-worthy moment (a stranger's win
re-executed live, timed, in public) and it's opt-in behind a subcommand. Differentiation
you don't put in front of people isn't differentiation.

**Concrete fix.** Add a **"See the no-cheat board"** button to the win/loss `result_embed`
and to the H3 reveal embed. When a run newly ranks, consider auto-posting the updated board
(or a "you're now #N" line with the board link). Make the re-verify trick something a
player stumbles into, not something they have to know to summon.

**Effort.** S.

---

## NICE-TO-HAVE

### N1. Pacing: paid narration can be ~20s per room, and prose is doubled
`narrate_room_gated` runs real Bedrock (the code notes "the narrator alone can take
~20s") on every room; across the ~8–12 rooms of a run that is minutes of waiting for a
paid player, while the free scripted tier is instant. And `room_embed` renders the
narration *plus* the scripted prose in italics beneath it when they differ — often
verbose. **Fix:** a snappier default (pre-narrate the opening while the player reads the
intro; or a "fast" toggle); drop the doubled italic under-line once narration is present.
**Effort:** M.

### N2. No solo cold-start loop (beat-your-own-ghost / personal best)
The strategy explicitly requires "the leaderboard must be fun SOLO day one (beat your own
ghost / the global best)." The empty board says "Be the first" (good), but there is no
personal best, no "you placed #k of m," no ghost to beat. On a cold day-one board, a solo
player has nothing to chase. **Fix:** surface "your best today: N turns" and "#k of m
survivors" on the result embed; track a personal best to beat. **Effort:** S.

### N3. `/descent today` doesn't scout the actual day
`handle_today` prints generic rules copy but never surfaces the day's **drawn**
parameters — warden HP, depth — even though the web leaderboard shows exactly these as day
facts (`Warden HP`, `Depth`). A daily game's "what's today?" should tease today's
*specific* danger. **Fix:** add a per-day scouting line ("The Tide-Warden stands at 60 HP —
stout; 3 corridors deep"). **Effort:** S.

### N4. Telegram has no native play (blocked on H1)
Telegram punts to `/descent` on the web, which is the leaderboard. Once web play exists
(H1), wire a Telegram web-app "Play" button to the real play page. **Effort:** L (depends
on H1).

### N5. Harvest the in-tab client that already exists
`<dregg-descent>` + `DescentWorld` are a complete, private, verifiable in-tab player —
today reachable only via the extension. This is the bulk of H1's "real win." Flag it as an
asset to mount, not a thing to rebuild. **Effort:** context for H1.

### N6. The win moment is a text verdict, not a run summary
`result_embed` gives a verdict + rank but no shareable "run card" feel (the line you took,
damage taken, depth, class). A richer win summary (mirroring the web run-card) makes the
screenshot better and feeds H2's share. **Effort:** S.

### N7. Locked moves don't say why (proactively)
`move_rows` renders an ineligible move as `🔒 <label>` (secondary style); the player only
learns *why* on a refusal ("Refused — the world disposed"). A one-line hint ("needs HP ≥
16" / "the warden must fall first") on the locked button's context would teach the system
without a failed press. Mild — the executor-is-referee honesty is otherwise good.
**Effort:** S.

### N8. Loop question to verify (not asserted) — re-attempts and dead-character re-open
Worth confirming for feel/integrity: after a **won** day, can a player re-`/descent play`
the same day and grind for a better board time? And after a **hardcore death**, what does a
same-day re-open present (the character loads dead)? These are loop-feel questions with a
board-integrity edge; if any answer touches the win-condition or eligibility rules,
**[for the Lean terminal]**. Flagged for a read, not a claim.

---

## The single highest-leverage improvement (3 lines)

**Stop the flagship's front door from lying, and close the viral loop.** The product
website's "Play The Descent" button lands on a scoreboard (H1) and a won run — the whole
"I can prove I survived" pitch — is never handed a shareable link (H2), even though both
the web run-card and `run_share_path` are already built. Wire the Discord win to emit its
`/descent/run/{id}` share link *and* relabel/route the web CTA to something that actually
plays: two small welds that turn a buried, Discord-only demo into a flagship a stranger can
meet, believe, and pass on.
