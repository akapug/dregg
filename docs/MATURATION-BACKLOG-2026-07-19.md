# Maturation Backlog — 2026-07-19 (4 adversarial reviews of the convergence work)

Reviews: /da Activities, crowd-stream, identity-link, Descent+small-pieces. Verdict per subsystem:
- **/da Activities**: SOUND (no trust-root holes). Sharpenings only.
- **Identity**: crypto solid, RESOLUTION barely wired ("one you everywhere" unfulfilled).
- **Crowd-stream**: LEAST mature — verified-turn spine is test-only, ingest forgeable.
- **Descent/free-text/audit**: the funnel is severed + a whole free-text class silently broken.

## Already FIXED (churn-independent)
- link_registry atomic-append (silent-record-loss bug) + tie-break — committed c152c3fd8.

## THE FIX WAVE (prioritized clusters)

### 1. IDENTITY RESOLUTION WIRING — make "one you everywhere" TRUE
- CRIT: resolution called from only 2 Discord-process display sites; web/Telegram descent
  leaderboard doesn't resolve AT ALL. Thread resolve_root through the REAL leaderboards
  (web descent RecordedRun.player, Discord descent board).
- CRIT: the crown board only RELABELS, never MERGES — group entries by resolved root + rank per human.
- HIGH: resolve_root_account (account-id join key) is DEAD — adopt it at EVERY resolution site
  (so shallow TSV + future cell agree; makes link_kel/linked_platforms stop being dead code).
- MED: two divergent link protocols — Discord /link-prove signs the bare challenge (custodial/
  platform/root NOT bound); unify onto verify_link_claim's canonical message.
- MED: hosted Discord users can't link in-chat (only ExternalPending) — add a hosted-user ceremony.

### 2. DESCENT FUNNEL — close acquire->play->share end-to-end
- CRIT: /descent/play is unreachable — NO front door links to it. Point the Play CTAs at it.
- CRIT: H2 share link structurally DEAD — bot plays drand/date seed, web demo plays hardcoded
  [3;32], bot omits `day` => ranked:false => share never emits. Fix: ONE shared (day_key, seed)
  helper used by both processes; web demo opens today's REAL seed; bot sends `day`.
- HIGH: Telegram miniapp "Play" button lands on the board — repoint to /descent/play.
- HIGH: /descent/play inert on real deploy (no wasm artifacts committed, no build step; wasm/pkg
  gitignored) — add a just/make target (esbuild + wasm-pack --target web + copy) + CI/commit.
- LOW: /descent/play opens a fixed demo day, decoupled from the board's world (same seed helper).

### 3. FREE-TEXT CLASS — a Telegram-only silent-failure class
- HIGH x3: hermes, names, compute NEVER migrated to taking_text + input.text — typed input
  silently dropped or mis-read (compute settle outright impossible). ~one-liners each.
- HIGH: the doc editor is secretly APPEND-ONLY — pending_text_action uses the FIRST of 4 text
  affordances; set-title/insert/resolve unreachable. Add a selectable text affordance.
- MED: typed text into a resumed doc after restart dropped (no resume_chat on the free-text path).
- MED: greedy group-chat capture (every member's message becomes offering input) — gate on
  active-participant / explicit arm / reply-scope.

### 4. CROWD-STREAM CRITs — turn scaffolding into a real demo (honesty)
- CRIT: the deployed overlay NEVER lands a certified turn (demo_state has no world; close_tick
  uncalled). Wire OverlayState over a live World::open cell + drive close_tick on a timer.
- CRIT: ingest is unauthenticated + forgeable (POST /overlay/ingest trusts caller's amount_micros).
  Make the SERVER the authenticated YouTube fetcher (API key, nextPageToken, pollingIntervalMillis).
- HIGH: 64 replicated signed seats per voter (O(64N) crypto under a mutex) — one weighted ballot.
- HIGH: platform-minted custody — real per-viewer custody via DreggIdentity/Companion enrollment.
- MED: pure-weight quorum (a single $3 Super Chat wins) — add a distinct-voter floor / concave weight.

### 5. /da ACTIVITIES — 3 sharpenings (sound underneath)
- MED: rate-limit / concurrency-cap /da/token (the one unauth'd endpoint making an outbound call).
- LOW: the /descent card in /da navigates OUT of the ticket context to unverified cookie identity —
  route the flagship through a ticket-gated /da twin or drop it from the "Verified" shelf.
- LOW: shorten/annotate the 24h bearer ticket default. Vendor the SDK bundle (ember; + a live smoke run).

### 6. AUDIT — cross-service correlate is dead on arrival
- CRIT(deploy): DREGG_AUDIT_DIR set in ZERO deploy artifacts -> all three services diverge ->
  auditq correlate can't join. Add Environment=DREGG_AUDIT_DIR=... to all three units + .env.example.
- MED: unified dir + concurrent O_APPEND tears lines (same class as the link bug) — PER-PROCESS
  filenames (audit-DATE.<platform>.jsonl) keeps one correlate-able dir without contention.
- MED: default durability loses data (fsync opt-in; queue lost on SIGKILL) — default fsync on +
  sync() on shutdown + web bin arms audit; add byte-size rotation.

### 7. ROLES-CAPS — orphaned (never compiled)
- HIGH: no `mod roles_caps;` => never compiled, tests vacuous, grant_cap_role fires nowhere.
  Wire the mod + fold /roles under /identity (Reach::Under) + call grant at the no-cheat-win +
  /credential verify seams.

## Confirmed DONE (not gaps)
H6 date-seeded fallback real; durable no-cheat board real; wants_text is a proper offering-agnostic
bool; doc APPEND works; /da trust root sound + hardened /da/link; initData signature regression pinned;
derivation parity holds; web single-use real; custodial never client-supplied; SSE backpressure clean;
crowd-stream honesty labeling correct (no over-claim on the viewer surface).
