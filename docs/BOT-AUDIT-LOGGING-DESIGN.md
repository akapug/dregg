# Bot Audit Logging — the INTERACTION ENVELOPE around every turn

**Status: DESIGN (no code yet).** Covers `discord-bot`, `dreggnet-telegram`, `dreggnet-web`
(including the `/tg` Mini App surface).

## 1. Goal — what the receipt chain does NOT record

The receipt/turn chain already records every on-chain MOVE: a landed
`TurnReceipt { turn_hash, pre_state_hash, post_state_hash, previous_receipt_hash, agent, … }`
(`turn/src/turn.rs:856`), chained per session, replayable from the move-log
(`dreggnet_offerings::FileResumeStore`, `dreggnet-offerings/src/resume.rs:345`). That is the
*dregg side* — the committed history.

What is NOT recorded anywhere durable is the **interaction envelope** around each move:

- who pressed/typed/POSTed what, on which surface, attributed how strongly;
- what the frontend DECIDED (routed to the executor, refused before the substrate,
  gated by auth/policy, errored);
- what came back (the `turn_hash` when a turn landed; the executor's refusal reason;
  the transport/HTTP error) — and the join between the envelope and the receipt.

Refusals and errors are *exactly* the events that never reach the receipt chain (the
anti-ghost tooth: `Outcome::Refused` commits nothing, `dreggnet-offerings/src/lib.rs:206`) —
so today a "why did my bid not land" bug has no trail at all. The audit log is that trail:
**append-only, structured, secret-free, correlated to the receipt chain by `turn_hash`.**

Two logs, two jobs, one join:

| log | contains | replay gives you |
|---|---|---|
| move-log / receipt chain (exists) | committed turns only | the identical committed state (fail-closed) |
| audit log (this design) | ALL inputs + decisions + outcomes | the full interaction, incl. what did NOT land |

## 2. Survey — the emit points (where interactions enter and decisions are made)

### 2.1 discord-bot

Single gateway funnel: `Handler::interaction_create`, `discord-bot/src/main.rs:333`.

| surface | emit point | decision made there |
|---|---|---|
| slash command (13 arms) | `main.rs:337-362` (`dregg`, `descent`, `play`, `adventure`, `cipherclerk`, `gallery`, `govern`, `verify`, `identity`, `hermes`, `federation`, `leaderboard`, `help`; unknown → warn at `:361`) | routed to a handler / unknown |
| component press | `main.rs:364-414` by custom-id prefix: `menu:`, `start:`, `deosturn:`, `deos:`, `fiction:`, `descent:`, `offering:`, `crown:`, `verifychain:`, `txcheck:`, dashboard fallback | routed / stale-surface refusal inside handler |
| modal submit | `main.rs:415-427`: `start:`, `offering:submit:…`, dashboard | routed; typed value collected |
| channel message | `main.rs:430-436` → `event_bridge.on_message` + `hermes_channel::on_message` (the metered confined-Hermes turn) | drives a paid, cap-gated turn |
| desktop drive | `deos_drive` — `POST /api/op` on the bot's HTTP surface | builds + signs + submits the same real turn |
| chain reactor | `bot_reactor::start` (`main.rs:281`) — watches the command cell, reacts with a custodial turn | turn fired from on-chain command |
| HTTP read surface | `http_server` (axum; `/api/cells`, SSE) | read-only; low-tier |

Where turns land / refuse (the outcome half):

- generic offering adapter: `commands/offering.rs:872` (`Outcome::Landed { receipt, ended }`),
  `:887` (`Refused`), `:985`/`:1010` (`advance`), `:567` (`advance_collective`);
- descent: `commands/descent.rs:458` `advance_core` → `Landed`/`Refused` (`:469-474`),
  button route `descent:move:` at `:1216`;
- everything routed through `commands/ack.rs` deferred-ACK helpers (commit inside Discord's
  3 s window — the audit emit must ride the same non-blocking discipline).

Actor derivation: `cipherclerk::UserCipherclerk::derive(&bot_secret, discord_uid, federation_id)`
→ cell id + Ed25519 pubkey. **The audit actor is the derived pubkey/cell id + the platform uid —
never the secret.**

### 2.2 dreggnet-telegram

Single funnel: `run_update_loop`, `dreggnet-telegram/src/runtime.rs:518`, three event kinds
from `parse_updates` (`runtime.rs:207`):

| surface | emit point | decision made there |
|---|---|---|
| button callback | `runtime.rs:540` → `route_callback` (`:295`) → `TelegramHost::press` (`host.rs:404`) | `HostPress::{Opened, Advanced{Outcome}, Verified, NotOffered, NoSession}` — `NotOffered` is the frontend-level refusal BEFORE the substrate; includes the restart-resume retry path (`resume_chat`, `host.rs:489`) |
| text command | `runtime.rs:554` → `route_text` (`:322`): `/start /help /offerings /menu /play /open /verify /act`; ordinary chatter ignored | routed / usage-refused / synthetic press (`/verify`, `/act` mint `encode_callback` presses) |
| Mini App `web_app_data` | `runtime.rs:566` → `route_web_app_data` (`:399`) | decodable payload → synthetic press through the SAME router; otherwise acknowledged-and-dropped (client-authored, untrusted) |
| boot resume | `durable_telegram_host` (`runtime.rs:478`): per-log resumed / REFUSED (fail-closed, file kept) | resume decisions currently only on stderr |

Actor: `TelegramCipherclerk::derive(&bot_secret, uid)` → identity; the update itself
attributes the uid (a client string can never name an identity).

### 2.3 dreggnet-web

Catalog router: `dreggnet-web/src/lib.rs:1332` (plus the legacy dungeon router at `:372`).

| surface | emit point | decision made there |
|---|---|---|
| `GET /offerings/{key}/session/{id}` | `lib.rs:1357` | `ensure_open_as` with `Attribution::Asserted` (forgeable cookie — advisory); policy refusal → honest 4xx (`:1387`) |
| `POST …/act` | `lib.rs:1430` `post_offering_act` | `CatalogAct::{Advanced(Outcome), NotOffered, Missing}` |
| `POST …/act-signed` | `act_signed.rs:205` (`decode` at `:173`) | wire decode (400s) → signature/counter verify (403: `BadSignature`, `StaleCounter`) → `advance_signed` → `Outcome` — **Signed provenance, user-held key** |
| `GET …/verify` | `lib.rs:1341` | replay re-verification (`VerifyReport`) |
| `GET /tg` shell + `GET /tg/offerings` | `telegram_miniapp.rs:576,583` | shell serves unauthenticated; listing requires initData |
| `GET/POST /tg/offerings/…` | `telegram_miniapp.rs:622,707` | `verified_user` (`:543`) → `validate_init_data_at` (`:300`): `InitDataError` taxonomy 401/400/403 (`Missing`, `BadHmac`, `Stale`, `FromFuture`, `MissingUser`, …); then custodial sign-at-counter → `advance_signed`; a verifier refusal on this path is a SERVER BUG (logged loudly, `:808`) |

Actor grades on the web are heterogeneous and the audit record must say which:
cookie (`web_identity`, asserted/forgeable) vs initData-verified (Telegram-attested)
vs act-signed (user-held Ed25519 key).

## 3. The `AuditEvent` shape

One record per interaction, emitted at the frontend call site that both routed the input
AND saw the outcome (every frontend blocks on `host.run(...)` in one function scope, so
**no cross-thread correlation plumbing is needed** — ingress and outcome are the same stack
frame).

```rust
/// One audited interaction. Serialized as a single JSON line. Schema-versioned.
#[derive(Serialize, Deserialize)]
pub struct AuditEvent {
    /// Schema version (start at 1).
    pub v: u16,
    /// Unix millis, assigned at emit.
    pub ts_ms: u64,
    /// Unique per interaction: 8-byte random + 6-byte timestamp, hex (sortable-ish, cheap).
    pub correlation_id: String,
    /// "discord" | "telegram" | "web" | "tg-miniapp".
    pub platform: String,
    pub actor: Actor,
    pub surface: Surface,
    pub input: Input,
    pub decision: Decision,
    pub outcome: AuditOutcome,
    /// The offering session, when one is in play (joins to the move-log file).
    pub session_id: Option<String>,
    /// The offering key ("dungeon", "market", …), when known.
    pub offering: Option<String>,
}

pub struct Actor {
    /// Platform-native id: Discord uid / Telegram uid / web cookie label. NOT a secret.
    pub platform_id: String,
    /// The derived dregg identity (hex pubkey / cell id), when derivable at the site.
    pub dregg_identity: Option<String>,
    /// HOW STRONGLY attributed — the codebase's own vocabulary:
    /// "asserted" (forgeable cookie) | "custodial" (bot-derived from platform uid)
    /// | "initdata-verified" (HMAC-checked Telegram attestation) | "signed" (user-held key).
    pub grade: String,
}

pub enum Surface {           // serialized as lowercase strings
    Command,                 // slash command / TG text command
    Component,               // Discord button/select press
    Modal,                   // Discord modal submit
    Callback,                // TG inline-button callback
    WebAppData,              // TG Mini App sendData round-trip
    Http,                    // web catalog GET/POST (incl. act-signed)
    InitData,                // /tg Mini App authenticated routes
    Message,                 // channel message driving a turn (hermes_channel)
    ChainCommand,            // bot_reactor: turn fired from an on-chain command
    Resume,                  // boot-time session resume decision
}

pub struct Input {
    /// The command name / custom_id prefix / route, e.g. "descent", "offering:fire",
    /// "POST /tg/offerings/{key}/session/{id}/act".
    pub kind: String,
    /// The typed substance, SECRET-REDACTED: {turn, arg, text?} for an act;
    /// the subcommand + options for a slash command; the callback_data for a press.
    /// Free text is carried verbatim (user content IS the audit trail) EXCEPT on
    /// redact-listed inputs (§8).
    pub detail: serde_json::Value,
}

pub struct Decision {
    /// "routed" | "refused" | "gated" | "error".
    pub kind: String,
    /// The machine reason: "not_offered", "no_session", "stale_surface",
    /// "initdata:bad_hmac", "initdata:stale", "policy", "usage", "unknown_command",
    /// "sig:stale_counter", "resume:tampered", … Empty for "routed".
    pub reason: String,
}

pub enum AuditOutcome {
    /// A turn landed: THE JOIN to the receipt chain.
    Landed {
        turn_hash: String,               // hex(TurnReceipt.turn_hash), 64 chars
        ended: bool,
    },
    /// The executor refused (anti-ghost: nothing committed) — carries its own reason.
    Refused { why: String },
    /// A verify ran: the report verdict.
    Verified { verified: bool, turns: u64 },
    /// The interaction never reached the substrate (decision.kind != "routed"),
    /// or a read-only surface answered.
    None,
    /// Transport/HTTP/internal error, stringified (no secrets in the Display impls —
    /// verified for the types above; keep it that way).
    Error { what: String },
}
```

Decision-taxonomy mapping (so the three frontends emit the SAME words):

| frontend result | decision | outcome |
|---|---|---|
| `Outcome::Landed { receipt, ended }` | routed | `Landed { turn_hash: hex(receipt.turn_hash), ended }` |
| `Outcome::Refused(why)` | routed (the substrate was reached) | `Refused { why }` |
| `HostPress::NotOffered` / `CatalogAct::NotOffered` | refused / "not_offered" | None |
| `HostPress::NoSession` (post-resume-retry) | refused / "no_session" | None |
| `InitDataError::*` (401/400/403) | gated / "initdata:&lt;variant&gt;" | None |
| `HostError::Policy`/`ResumeFailed` | gated / "policy" · "resume_failed" | None |
| `SignedError::BadSignature`/`StaleCounter` | gated / "sig:&lt;variant&gt;" | None |
| usage errors (`/act` parse, unknown slash cmd) | refused / "usage" · "unknown_command" | None |
| transport/API failure after routing | routed | `Error { what }` |
| boot resume per-log | routed / or refused "resume:tampered" | None |

## 4. The shared facility: a NEW light crate `dregg-audit`

**Decision: a new crate, not a module in `dreggnet-offerings`.** The offerings crate pulls
`deos-view`, `dregg-app-framework`, the executor — heavy, and `discord-bot`'s non-offering
surfaces (deos_drive, hermes_channel, pay) also need to emit. `dregg-audit` depends on
**`serde`, `serde_json` only** (time via `std::time`, randomness via a tiny xorshift over
`SystemTime` + a counter — no `rand`, no `tokio`, no async runtime). Every frontend already
has serde_json in its tree.

```rust
// dregg-audit/src/lib.rs — the whole public API
pub struct AuditLog { /* SyncSender<String> to the writer thread + drop counter */ }

impl AuditLog {
    /// Open (or create) `dir`, spawn the writer thread. Never fails the caller:
    /// an unopenable dir returns a DISABLED log that counts drops (one loud warning),
    /// mirroring durable_telegram_host's degrade posture.
    pub fn open(dir: impl Into<PathBuf>, platform: &'static str) -> AuditLog;
    /// A disabled log (env opt-out) — every emit is a no-op.
    pub fn disabled() -> AuditLog;
    /// Resolve from env: DREGG_AUDIT_DIR ("off" → disabled; unset → `default_dir`).
    pub fn from_env(default_dir: Option<PathBuf>, platform: &'static str) -> AuditLog;

    /// NON-BLOCKING emit: serialize on the caller, try_send to the writer.
    /// A full queue DROPS the event and bumps a counter (never block a turn on a log
    /// write); the drop counter is itself logged on the next successful write.
    pub fn emit(&self, ev: AuditEvent);

    /// Fresh correlation id (also usable by callers that pre-announce it in a reply).
    pub fn correlation_id() -> String;
}
```

Writer thread mechanics:

- bounded `sync_channel` (capacity 4096 events); caller side is `try_send` — **the hot path
  never blocks and never allocates beyond the one serialize**;
- one open `File` in `O_APPEND`; each event is ONE `write(2)` of one `\n`-terminated line
  (atomic for typical line sizes; a crash can truncate at most the tail line — the reader
  skips a torn last line);
- **no fsync by default**; `DREGG_AUDIT_FSYNC=1` opts into per-write flush for deployments
  that want crash-durability over throughput;
- **rotation**: files are `audit-YYYY-MM-DD.jsonl` (UTC); the writer rolls on date change
  and, if `DREGG_AUDIT_RETAIN_DAYS=N` is set, prunes files older than N days on roll.
  Append-only otherwise: nothing rewrites an existing line, ever.

This is deliberately the same durable-store idiom the session stores use
(`FileResumeStore`: a directory of append-only logs; degrade-with-warning; fail-closed
reads) — one posture across the deploys.

## 5. Storage: JSONL canonical, sqlite as a tool-side index

**Canonical store: the JSONL directory.** Replayable (each line is a complete input
record), greppable, `tail -f`-able, rotation-aware, zero new deps in the frontends,
identical across all three deploys.

**Queryable store: sqlite, built BY THE TOOL, not by the bots.** The discord bot already
has sqlite (`db.rs`), the others don't; putting a live sqlite writer into each frontend
buys nothing the tool cannot do offline and adds a second hot-path store to keep honest.
Instead `auditq` (§7) imports/incrementally indexes the JSONL into a local
`audit-index.sqlite` (table `audit_events` with columns mirroring §3 plus generated
columns on `actor_platform_id`, `decision_kind`, `turn_hash`, `ts_ms`; indexes on each).
The JSONL remains the source of truth; the index is disposable and rebuildable.

Default locations (env `DREGG_AUDIT_DIR` overrides everywhere; `DREGG_AUDIT_DIR=off`
disables):

| deploy | default |
|---|---|
| discord-bot | `<dir of DATABASE_URL file>/audit/` |
| dreggnet-telegram-bot | `<TELEGRAM_SESSION_DIR>/../audit/` (sibling of the session store) |
| dreggnet-web-server | `<DREGGNET_WEB_SESSION_DIR>/../audit/` (sibling), else disabled with one warning |

## 6. Receipt correlation — the dregg-side join

The audit event carries `outcome.Landed.turn_hash = hex(TurnReceipt.turn_hash)`
(`turn/src/turn.rs:857`). Joins, in both directions:

- **envelope → receipt**: given an audit line with a `turn_hash`, the committed turn is on
  the session's receipt chain — re-verifiable by the offering's own verifier
  (`/verify`, `verifychain:` press, `GET …/verify`) and findable in the move-log store
  (`<session-dir>/<key>/<sid>.log`) via the recorded `session_id` + `offering`;
- **receipt → envelope**: given a `turn_hash` from the chain/explorer,
  `auditq join <turn_hash>` returns the interaction that produced it — who, on what
  surface, with what input, at what attribution grade;
- the chain of custody is checkable end-to-end: `previous_receipt_hash` links receipts,
  the audit line links the receipt to the human act, and `session_id` links both to the
  replayable move-log. A receipt with NO audit envelope (after audit was enabled) is
  itself a finding: a turn landed outside the audited frontends (deos_drive? reactor? a
  direct node client) — which is why those paths emit too (`Surface::ChainCommand`, Http).

## 7. Replay and find-bugs — the `auditq` tool

One small bin (`dregg-audit/src/bin/auditq.rs`; serde_json + rusqlite, tool-side only).

**Find a bug:**

```
auditq index <audit-dir>                          # (re)build audit-index.sqlite
auditq grep --actor 123456789 --since 2026-07-16  # everything a user did
auditq grep --decision refused --reason not_offered --offering market
auditq grep --outcome error                       # every transport/internal error
auditq join 9f3ab2…e1                             # turn_hash → the envelope (or reverse)
auditq session <sid>                              # the whole interaction envelope of one
                                                  # session, interleaved landed/refused, in order
tail -f audit-2026-07-17.jsonl | jq 'select(.decision.kind!="routed")'   # live, no tool
```

**Replay a session** (re-drive the recorded inputs):

```
auditq replay --session <sid> [--offering <key>] [--until <correlation_id>]
```

Replay reads the session's audit lines in `ts_ms` order and re-issues each `input`
(`{turn, arg, text?}`, actor identity from the record) against a FRESH host
(`dreggnet_catalog::full_catalog_host`) with a session seeded from the same `sid` — the
sessions are deterministically seeded from the session id (host docs, `host.rs:44`), so
the replay is real: every formerly-landed turn must land with the SAME `turn_hash`
(divergence = nondeterminism or a code change — printed as a diff), and every
formerly-refused input must refuse again with the same reason. This is strictly stronger
than the move-log replay (which carries only committed turns): the audit replay re-drives
**refusals and errors too**, which is exactly where bugs live. `--until` stops one event
before the bug for a state-at-the-moment repro.

Platform notes: Telegram/web inputs replay fully (they are `{turn, arg}` acts). Discord
inputs replay at the adapter level (the same `(key, turn, arg, actor)` the component
handlers build) — Discord's own gateway cannot be re-driven, and does not need to be:
every decision below the parse is shared.

## 8. Secret hygiene — HARD RULES (enforced, not hoped)

NEVER in an audit record: `DISCORD_TOKEN` / `TELEGRAM_BOT_TOKEN`, `BOT_SECRET` /
`TELEGRAM_BOT_SECRET` / any 32-byte master secret, derived Ed25519 SEEDS, user LLM
provider keys (`key_vault`), `DREGG_PAY_*` credentials, the initData HMAC `secret_key`,
and **the raw initData string** (it embeds `hash`; the code already never logs it —
`telegram_miniapp.rs:542` — the audit record carries the verified `uid` + `auth_date`
only, same rule).

FINE to log (they ARE the trail): platform uids, derived PUBLIC identities
(pubkey/cell-id hex), turn hashes, session ids, offering keys, `{turn, arg}`, user free
text, act-signed `actor_pubkey_hex` + `counter` + even the signature (public material).

Enforcement, layered:

1. **redact-listed inputs**: the emit sites for `/key` (provider-key port-in,
   `commands/key.rs` surface) and any modal collecting credentials record
   `detail: {"redacted": "provider-key"}` — the redaction happens AT the emit point, by
   the module that knows what it collected;
2. **type discipline**: `AuditEvent` fields are `String`/`Value` built from already-public
   material; no constructor takes a `[u8; 32]` secret type;
3. **a standing test in `dregg-audit`**: serialize representative events from each
   frontend fixture and assert the output matches `^[^]]*$` against a denylist of the
   env-var VALUES injected into the fixture (token, secret hex, initData blob) — the
   canary that a future emit site started leaking.

## 9. Per-frontend wiring plan (surgical; new modules preferred)

**discord-bot** — new module `discord-bot/src/audit.rs`: holds the `AuditLog` on
`BotState`, plus one helper `audit_interaction(...)`. Emit sites:

1. `interaction_create` (`main.rs:333`): wrap each of the three arms — build the event
   before dispatch (correlation id, actor, surface, input), let the handler fill
   decision+outcome via a small `&AuditCtx` passed down, emit after. Handlers that
   already return/format an `Outcome` (offering adapter `commands/offering.rs:872`,
   descent `commands/descent.rs:469`, menus) record `Landed`/`Refused` there;
2. `hermes_channel::on_message` (metered turn), `deos_drive` `POST /api/op`,
   `bot_reactor` reaction — one emit each;
3. presence updates and the read-only HTTP surface are NOT audited by default (volume,
   no decision) — `DREGG_AUDIT_READS=1` opts reads in.

**dreggnet-telegram** — new module `dreggnet-telegram/src/audit.rs`. The single best seam
is `run_update_loop` (`runtime.rs:518`): every event kind flows through it, and
`route_callback`/`route_text`/`route_web_app_data` already return the decision as a
value. Change: have `route_*` return (or expose alongside) the structured
`HostPress`/decision rather than only the human string — a small enum-carrying wrapper —
so the loop emits `AuditEvent` with the machine taxonomy and still formats the same human
ack. Boot: `durable_telegram_host` (`runtime.rs:478`) emits one `Surface::Resume` event
per resumed/refused log (today stderr-only).

**dreggnet-web** — new module `dreggnet-web/src/audit.rs`: `AuditLog` on `CatalogState` +
`TgMiniAppState`. Emit sites: `get_offering_session` / `post_offering_act`
(`lib.rs:1357,1430`), `post_offering_act_signed` (`act_signed.rs:205` — grade "signed"),
`get_offering_verify`, and the four `/tg` handlers (`telegram_miniapp.rs:583-707` — grade
"initdata-verified"; every `InitDataError` refusal is a `gated` event). The legacy
`/session/{id}` router gets the same treatment or is left un-audited with a note
(it is the pre-catalog surface).

All three: the emit is fire-and-forget (`try_send`) — a turn NEVER waits on the log.

## 10. Component list

| # | component | where | what |
|---|---|---|---|
| 1 | `dregg-audit` crate | `dregg-audit/` (new; workspace member) | `AuditEvent` + taxonomy, `AuditLog` (bounded-queue writer thread, JSONL, rotation, drop-counting, env resolve), redaction helpers, secret-canary test |
| 2 | `auditq` bin | `dregg-audit/src/bin/auditq.rs` | index → sqlite, grep (actor/time/decision/reason/offering), `join <turn_hash>`, `session <sid>`, `replay --session` with landed-hash diffing |
| 3 | discord emit points | `discord-bot/src/audit.rs` + touches in `main.rs:333`, `commands/offering.rs`, `commands/descent.rs`, `hermes_channel.rs`, `deos_drive.rs`, `bot_reactor.rs` | envelope for all 13 commands, 11 component prefixes, 3 modal routes, message-driven turns, `/api/op`, chain reactions |
| 4 | telegram emit points | `dreggnet-telegram/src/audit.rs` + `runtime.rs` loop (+ `route_*` returning structured decisions) | envelope for callbacks, text commands, web_app_data, boot resumes |
| 5 | web emit points | `dreggnet-web/src/audit.rs` + catalog/act-signed/miniapp handlers | envelope for HTTP acts (3 attribution grades), initData gates, verifies, policy refusals |
| 6 | storage | per-deploy `audit/` dir (env `DREGG_AUDIT_DIR`), files `audit-YYYY-MM-DD.jsonl`, `DREGG_AUDIT_RETAIN_DAYS`, `DREGG_AUDIT_FSYNC` | canonical append-only store, sibling of the session stores |
| 7 | docs | `deploy/telegram/RUNBOOK-TELEGRAM.md` + bot READMEs | the env knobs + the two query/replay workflows |

Rollout order: 1 → 2 (tool works on synthetic fixtures) → 4 (telegram: smallest funnel,
one loop) → 5 (web) → 3 (discord: widest surface) → 7. Each frontend lands independently;
the shape is shared from day one so `auditq` reads all three interleaved
(`auditq grep --actor …` across platforms is the cross-surface debugging win).

## 11. Overhead

Hot path per interaction: one struct build + one `serde_json::to_string` (~1-3 µs at
these sizes) + one `try_send`. Writer thread: one `write(2)` per event, no fsync. At bot
scale (Discord's 3 s interaction window; Telegram long-poll; human-driven HTTP) this is
noise — three orders of magnitude below the executor turn itself. The bounded queue +
drop counter guarantees the worst case is a LOST AUDIT LINE (counted, reported), never a
slow or failed turn.
