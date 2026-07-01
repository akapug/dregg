# FAKEOUTS Audit — the distribution layer (hosted session · SSH attach · portal cockpit · panes · webauth · extension · MCP)

_Read-only audit, 2026-06-30, grounded to file:line at HEAD (`dev`) across
`~/dev/DreggNet` + `~/dev/breadstuffs`. No code was changed. A "fakeout" here is a
**laundered fake** — a fixture/planned/canned thing presented as live/real, a
vacuous auth/verify/cap-scope, or a decorative security mechanism — as distinct
from an **honestly-labeled seam** (a disclosed reviewed-go / demo / fixture, which
is NOT a fakeout). Fakeout-leaning items are flagged; honest seams are listed
separately per surface._

## TL;DR verdict

- **No CRITICAL fakeout on the auth/verify/cap-scope core.** webauth `/auth` really
  verifies the `dga1_` sig-chain + cap-meet + expiry + revocation, fail-closed
  (no vacuous admit, no prod `dev_subject`, no fail-open). The MCP's two verifies
  (`dregg_verify`, `dregg_agent_verify`) and the portal cockpit's in-browser
  verify + tamper-demo are **real re-witnesses** (genuine ed25519 over blake3,
  prev-hash chained; tamper genuinely bites). The extension really signs (wasm
  ed25519), submits, and logs in. The panes default to **live** with a real
  honest-unknown and real owner==subject cap-scoping. This is a system that
  practices "a named seam is not a hole," not a wall of laundered vacuity.
- **The worst fake is a decorative security mechanism:** `--os-isolation`
  re-grants a raw shell on the operator-key-holding host while the per-tenant jail
  it names (`JailSpec`/`bwrap`) is fully built + unit-tested but **never invoked on
  any real path** (F1). The runner-up is an **unbounded-spend hole**: the session
  budget resets to full on every SSH re-attach, behind a "hard bound" claim (F2).
  **BOTH FIXED (2026-06-30) — see the RESOLVED notes on F1/F2 below.**
- Everything else is an honestly-labeled seam or a low-severity honesty nuance
  (missing "demo/sample data" banners, an over-broad break-glass that is
  default-off, a static revocation set). None of them present a vacuous
  auth/verify or a fixture-as-the-live-default-in-prod.

---

## Ranked findings (highest first)

### F1 — `--os-isolation` re-grants a raw shell on the key-holding host; the jail is never wired · **HIGH** · **FAKEOUT (borderline)**
- **Where:** `DreggNet/agent-host/src/lib.rs:143-164` (`authorized_keys_line_with`) ·
  `breadstuffs/dregg-agent/src/bin/dregg-agent.rs:999-1006` (`cmd_session`) ·
  the entire `DreggNet/agent-host/src/isolation.rs` (`JailSpec`/`bwrap_argv`/`launch`).
- **Pretends:** `with_os_isolation(true)` / `--os-isolation` means "the host runs
  each session under a per-tenant OS jail whose filesystem lacks the operator keys,
  so a raw `shell` is safe again" (`lib.rs:140-142`).
- **Does:** setting the flag only (a) appends the literal string `--os-isolation`
  to the forced command (`lib.rs:150-152`) and (b) flips `Confinement::Hosted →
  Local` (`dregg-agent.rs:1002-1006`), which makes `shell` parse and `real_shell`
  run (`dregg-agent.rs:1072`). The emitted `authorized_keys` line runs `dregg-agent
  attach … --os-isolation` **directly** — it is *not* wrapped in `bwrap`.
  **Verified:** `JailSpec::launch` / `bwrap_argv` have **zero call sites** outside
  `isolation.rs`'s own definition + unit tests (grep across `agent-host cli gateway
  attach`). So an operator who enables isolation gets an **unconfined raw shell** on
  the box holding `~/.stripekey`/`~/.nousportalkey`, with no namespace jail in
  force. The fully-built + tested `JailSpec` creates a false impression that the
  jail is enforced.
- **Why fakeout (borderline):** a security mechanism presented as enforced that is
  not wired. Mitigating: default is fail-closed OFF (`lib.rs:514` asserts no jail by
  default), it requires an operator to opt in AND stand up a real sshd, and the doc
  calls it an operator "assertion." Aggravating: the flag *alone* re-enables the
  dangerous capability while the jail runs nowhere.
- **Fix:** make `attach` re-exec inside `JailSpec::launch()` when `--os-isolation`
  is passed and **fail-closed (refuse `shell`) if `launch` returns `Unsupported`**,
  so the flag can never grant a shell unless the jail is actually active.
- **RESOLVED (2026-06-30) — dropped the decorative flag (the blessed fallback).**
  `dregg-agent` now **hard-errors** on `--os-isolation` (`dregg-agent.rs` `cmd_session`
  — refuses to start rather than flip to the local posture / re-grant a shell). The
  `agent-host` registry lost `with_os_isolation`/`os_isolation`: `confinement()` is
  always `Hosted`, the `authorized_keys` line never emits `--os-isolation`, and a
  `shell` cap is refused at enrol under every configuration. `hostctl` hard-errors on
  the flag too. `isolation.rs` is kept as an honestly-labelled, tested-but-**NOT-YET-
  WIRED** building block (its module doc now says so up top), not an enforced
  mechanism — so no flag claims isolation without enforcing it. Proofs: `agent-host`
  `no_forced_command_ever_carries_the_os_isolation_flag` + `a_shell_cap_is_refused_at_enrol`;
  `dregg-agent` integration `os_isolation_flag_is_refused_and_never_grants_a_shell`
  (refused, no session, no shell) + `a_local_session_still_grants_a_shell` (the own-box
  path unaffected) + the existing `a_hosted_session_cannot_read_the_operator_keys`.

### F2 — Session budget resets to full on every re-attach (no cross-session persistence) · **HIGH** · **FAKEOUT (unlabeled gap)**
- **Where:** `breadstuffs/dregg-agent/src/session.rs:258-260` (`open` → `AgentCloud::new`) ·
  `agent.rs:1191-1194` (fresh `ReplenishingMeter::new()`) ·
  `dregg-agent/src/bin/dregg-agent.rs:1050` (`cmd_session` calls `Session::open` per process).
- **Pretends:** docstrings call the budget "the hard bound on the whole session …
  everything it could have done"; the account carries a persistent `budget_cents`
  ceiling.
- **Does:** every attach process builds a brand-new `AgentCloud` with a fresh
  **in-memory** meter (`Mutex<HashMap>`, no serde, no disk); `consumed` lives only
  for the process lifetime. A tenant who exhausts the ceiling can detach and
  reconnect (a new attach process) and receive the **full budget again**. The
  registry persists the ceiling but never the consumed total, so the dollar bound
  (including Stripe `pay:`) is **per-process, not per-account**.
- **Why fakeout:** a real unbounded-spend hole behind an honest-looking "hard
  bound" claim; the reset-on-reconnect is silent and undisclosed. (In-session
  draw-down itself is genuine and tested — see honest seams.)
- **Fix:** persist per-account `consumed` to the durable store keyed by account id
  and reload it into the meter at `Session::open`, so the ceiling spans reconnects.
- **RESOLVED (2026-06-30) — the drawdown now persists across re-attach.** New
  `dregg-agent::session_store::ConsumedStore`: a durable per-account consumed-budget
  store (one JSON file per account, atomic + monotonic writes, keyed by a domain-hash
  of the account id under `$DREGG_AGENT_STATE_DIR` / `~/.dregg-agent/state`). The
  `attach` binary loads the account's persisted consumed at open and calls the new
  `Session::restore_consumed`, which pre-charges the meter (a reserved carryover key)
  so the ceiling is drawn down exactly as at detach — over-budget is refused **across**
  the reconnect — and seeds a genesis carryover receipt so `verify` still holds on a
  bare re-attach. The drawdown is persisted after every goal. Value is clamped to the
  ceiling (a corrupt store can never widen the bound). Proofs: `session.rs`
  `the_budget_persists_across_reattach_and_over_budget_is_refused` +
  `a_restored_session_verifies_with_no_new_actions` + `restore_clamps_to_the_ceiling`;
  `session_store` round-trip/monotonic tests; `dregg-agent` integration
  `the_budget_persists_across_attach_processes_and_over_budget_is_refused` (three real
  attach processes over one shared store).

### F3 — Portal cockpit renders canned tool verdicts carrying a `WitnessedRun` "proof" the verify never re-witnesses · **MED** · **FAKEOUT (nuance)**
- **Where:** `DreggNet/attach/src/driver.rs:148-179` (`DemoToolkit`) ·
  `attach/src/live.rs:136` (`verify_live`) · `attach/src/render.rs:373`.
- **Pretends:** admitted tool calls return real QA verdicts —
  `"tests: 34 passed, 0 failed"`, `"deploy verified: 12/12 checks green"` — plus a
  `WitnessedRun` (`output_digest: [9u8;32]`, `code_root: "demo-session-code-root"`)
  and a comment that the witness is carried "so the in-browser re-witness has a real
  proof to check." The cockpit renders it as `observe · tests: 34 passed` with a
  green ✓ pill.
- **Does:** the strings + digests are hardcoded constants; no tests run. Critically
  `verify_live` only calls `verify_agent_run` (chain signatures + budget bound) and
  **never** calls `verify_witnessed_qa`, so the attached `WitnessedRun` is sealed
  but never re-executed. The signature proves only "the host recorded '34 passed'
  and didn't edit it," not that tests ran. The green ✓ slightly overstates what it
  attests.
- **Why fakeout (nuance):** the receipt chain + tamper detection are genuinely real
  (see honest seams); the overreach is the canned verdict + the "real proof to
  check" comment for a proof the verify path ignores.
- **Fix:** either re-witness the `WitnessedRun` in the verify path, or drop the
  "real proof to check" comment and label the tool_summary as a canned demo verdict.

### F4 — Status banner can read "All systems operational" while a Core surface went unprobed · **MED** · **HONESTLY-LABELED-SEAM (banner gap)**
- **Where:** `DreggNet/status/src/config.rs:44` (`economy_url: None` default) ·
  `status/src/aggregate.rs:365-425` (`roll_up`, banner at `:422-425`) ·
  `status/src/live.rs:95-96`.
- **Pretends:** the overall banner may say "All systems operational."
- **Does:** with the default config `economy_url` is unset → the **Core**
  economy-conservation (Σδ=0) row is `NotConfigured` and **excluded** from the
  rollup (`counts()` filter, `aggregate.rs:366`). So the page can say "All systems
  operational" having never probed the conservation invariant (same for node-only
  defaults where `bridge_url`/`control_url` are unset). Honest at the row level
  ("not deployed here"), but the banner doesn't reflect an unprobed Core surface.
- **Fix:** if any `Tier::Core` row is `NotConfigured`, cap the banner at Degraded /
  emit a "conservation not probed" caveat rather than "All systems operational."

### F5 — webauth break-glass admits every surface, prod-expected-on · **MED** · **HONESTLY-LABELED-SEAM (highest live risk)**
- **Where:** `DreggNet/webauth/src/lib.rs:116-123` (guidance `lib.rs:29`) ·
  header read `server.rs:252-258` · default `config.rs:76,118`.
- **Pretends:** an operator lock-out escape hatch.
- **Does:** a single static shared-secret header (`X-Dregg-Break-Glass`) that, as
  **step 1 before all checks**, admits every surface — bypassing cap, expiry, AND
  revocation, with `cap: None`, subject `dregg:break-glass`. `lib.rs:29` tells
  operators to **keep it set in production** until the cap flow is exercised.
- **Why not a fakeout:** default-off in code (`config.rs:76` `break_glass: None`,
  only enabled by a non-empty `DREGG_WEBAUTH_BREAK_GLASS`), constant-time compared,
  full-entropy operator secret, honestly labeled in-code. But it is the single most
  dangerous live element — a weak/leaked value = full unrevocable access. (Already
  flagged in `docs/DEPLOY-READINESS.md`: must be cleared before calling webauth
  "cap-auth as default".)
- **Fix:** bind break-glass to a specific cap + short TTL, log every use loudly,
  make its removal a deploy gate.

### F6 — webauth revocation is a static, empty-by-default, no-live-reload deny-set · **MED** · **HONESTLY-LABELED-SEAM**
- **Where:** `DreggNet/webauth/src/config.rs:99-107,132-141`.
- **Pretends (config doc `:37-45`):** the cloud-side `Effect::RevokeCapability`.
- **Does:** a `BTreeSet` loaded **once** at process start from
  `DREGG_WEBAUTH_REVOKED`/`_REVOKED_FILE`; `is_revoked` returns `false` when empty.
  Killing a leaked token requires editing env/file + restarting; a default
  deployment enforces **no revocation at all**. Genuinely checked (tests pass), just
  not live.
- **Fix:** hot-reload the file (mtime watch) or query a live deny-set; document that
  no `DREGG_WEBAUTH_REVOKED` = no revocation.

### F7 — `STATUS_DEMO=1` serves a constant all-green bundle · **MED** · **HONESTLY-LABELED-SEAM (opt-in fake-green)**
- **Where:** `DreggNet/status/src/config.rs:72-78` ·
  `status/src/bin/dreggnet-status.rs:37-41` · `status/src/fixtures.rs:62-95`.
- **Pretends:** a live public status page.
- **Does:** `STATUS_DEMO=1` swaps in `FixtureSource::healthy()` — a constant
  Operational/n=5/conservation-OK bundle served regardless of real health. A genuine
  fake-green **if** a public deploy sets the flag. Opt-in only, default `live=true`
  (`config.rs:46`), stderr logs `source: fixture (STATUS_DEMO)`.
- **Fix:** watermark the demo page ("DEMO DATA") or refuse `STATUS_DEMO` when bound
  to a public interface.

### F8 — Per-account "concurrent sessions" quota actually bounds enrolled keys, not live sessions · **MED** · mild mislabel (mechanism real)
- **Where:** `DreggNet/agent-host/src/lib.rs:294-305` (doc `:57-59`).
- **Pretends:** `DEFAULT_SESSIONS_PER_ACCOUNT` caps "concurrent sessions per
  enrolled subject — the exhaustion-vector backstop."
- **Does:** `enroll` counts existing `records` (enrolled *keys*). One enrolled key
  can open unlimited concurrent SSH connections, each spawning an attach process;
  nothing counts/caps live sessions. Partially disclosed ("a real deploy also bounds
  total SSH connections at the sshd").
- **Fix:** reword to "max enrolled keys per account" and enforce a real
  concurrent-session cap at session-spawn / sshd.

### F9 — Console default source is `FixtureSource` with no on-page "sample data" banner · **LOW/MED** · **HONESTLY-LABELED-SEAM**
- **Where:** `DreggNet/console/src/bin/dreggnet-console.rs:43-48` ·
  `console/src/render.rs:21-29` · `console/src/config.rs:132` vs `:68-78`.
- **Pretends:** header "My sites / My servers / My agents … cap-scoped to your
  cells."
- **Does:** default source is `FixtureSource` (`is_live()` false with no env), so a
  viewer scoped to `DEMO_SUBJECT` sees fabricated demo resources under "My stuff"
  with no on-page banner — the only tell is the `signed in as dregg:demo0001…`
  line. Strong mitigations: the UI never says "live," it's documented
  (`lib.rs:39-44`, `source.rs:6-13`), stderr logs `source: fixture`, and a **real**
  signed-in subject sees *empties* (fixtures owned only by the two demo subjects),
  never another's data. Footgun: `CONSOLE_LIVE=1` alone stays on fixtures because
  `is_live()` also needs a surface URL (`config.rs:132`).
- **Fix:** render a "sample data — not wired to live surfaces" banner when the
  source is the fixture; warn when `CONSOLE_LIVE=1` but no surface URL is set.

### F10 — Extension `dregg:isConnected` returns `true` unconditionally · **LOW** · borderline honest
- **Where:** `breadstuffs/extension/src/background.ts:3214-3215` · `page.ts:239`.
- **Pretends:** node reachability.
- **Does:** resolves `true` whenever the background merely responds ("provider
  present," not node-live) — mirrors `window.ethereum.isConnected()` semantics, so
  defensible, but the name can mislead a dApp.
- **Fix:** rename to `isAvailable()` or actually probe `/api/node/status`.

### F11 — Stale/misleading comments (reverse-fakeouts, under-claim) · **LOW** · doc/code drift
- `breadstuffs/extension/src/page.ts:198` — comment "requires the wasm
  `sign_turn_v3` export (stub until it lands)"; the impl is fully real
  (`background.ts:2899` → wasm `lib.rs:1917`). Delete the "stub until it lands"
  clause.
- `DreggNet/webauth/src/config.rs:15-16` — doc claims a `dregg_break_glass` cookie
  channel the code never reads (`server.rs:252-258` reads only the header). Safe
  direction (fewer channels); delete the cookie clause.
- `DreggNet/webauth/src/server.rs:516-529` — `login_submit` sets a session cookie
  without chain verification when the root key is missing/unparseable; **not
  exploitable** (`/auth` then fails closed, `lib.rs:133-139`), honestly commented.
  Fix for defense-in-depth: refuse to set a cookie when no verifiable root is
  configured.

---

## Honest seams affirmed as REAL (not fakeouts)

### Hosted session / SSH attach (`breadstuffs/dregg-agent`, `DreggNet/agent-host`)
- **SSH forced command is real confinement.** Uses real OpenSSH
  `command="…",restrict,pty` (`lib.rs:160-163`). Because it is a *forced* command, a
  connecting user **cannot** inject `--account`/`--caps` — their input arrives only
  as `SSH_ORIGINAL_COMMAND`, read as a natural-language goal
  (`dregg-agent.rs:1092-1108`), never re-parsed as flags.
- **Cap-gate is real + fail-closed** — signed-credential `verify` against the fixed
  bundle before any draw (`agent.rs:1405-1422`); hosted `shell` refusal at parse is
  real (`session.rs:140-150`); exfil-teeth test proves no shell admits.
- **In-session budget is a genuine non-vacuous forge-detector** — honest accept and
  every forge reject run through `BudgetState::check_draw`; over-budget refused
  in-band before the priced tool runs; draw exactly-once per `(agent, seq)`
  (`budget.rs`, `meter.rs`, `agent.rs:1424-1466`). (The per-account persistence gap
  is F2.)
- **Two sessions are cryptographically isolated within a process** (distinct
  roots/meters; a bundle does not verify under another root) — real, tested.
- **Standing up a real sshd** is honestly labeled as the reviewed-go deploy seam
  (`lib.rs:29-37`); `isolation.rs::bwrap_argv` is a correct, deterministic, tested
  argv builder, fail-closed off-Linux — its only defect is that nothing invokes it
  (F1). Recorded/replay brain paths are labeled "RECORDED," not passed off as live.

### Portal cockpit (`DreggNet/attach`)
- **In-browser verify is a REAL re-witness** — `verify_live → verify_agent_run →
  verify_chain` does actual `VerifyingKey::verify(&receipt_hash, &sig)` + prev-hash
  link checks (`dregg-agent/src/receipt.rs:307-353`). `tamper_demo`
  (`verify.rs:109-130`) flips a real signed field (`tool_ok`, in the signed body)
  and re-runs the SAME verify, which genuinely fails `BadSignature`. Tests
  `a_tampered_receipt_is_caught` / `a_dropped_receipt_is_caught` exercise real
  detection.
- **Cap-scoping (owner == subject) is REAL** — `owner` stamped from the verified
  `X-Dregg-Subject` at create (`store.rs:142-160`, never a body field);
  `get_for_subject` (`store.rs:238-244`) filters `owner()==subject` before any
  read/stream/fork/verify; a non-owned id 404s (`bin:190`). Dev-subject fallback is
  disclosed as dev-only, disabled once `require_cap` is set.
- **The whole braid is genuine** — cap-gate + budget meter + signed receipt chain +
  real re-witness. Honest seams: the scripted `PlannedBrain` (surfaced to the user
  in the meta model string `"dregg-demo-planner (scripted; live Hermes/Kimi brain is
  the reviewed-go swap)"`, `driver.rs:100`), the recorded-transcript SSE replay
  (`stream.rs:6-9`), and the `exfiltrate` refusal (genuinely cap-gate-enforced). The
  canned tool verdicts are F3.

### Panes (`console`, `status`, `landing`)
- **Status defaults to LIVE** (`config.rs:46`) and **honest-unknown is REAL, not
  fake-green** — `Unreachable → Unknown` never Operational; total blindness →
  Unknown, partial → Degraded (`aggregate.rs:409-420`); economy un-observed →
  Unknown; bridge conservation un-observed → Degraded (never green); rust↔lean
  divergence → Down (`aggregate.rs:290-300`). (Banner-over-Core-unprobed nuance is F4.)
- **Console cap-scoping is REAL and non-vacuous** — `scope()` filters
  `owner()==subject` (`scope.rs:26-32`); owner-less records dropped fail-closed;
  "unknown subject sees nothing" + two-owner disjointness tested. Prod
  (`require_cap` set) ignores `dev_subject`.
- **Console verify re-witnesses a GENUINE chain** — the fixture report is built by
  the real `dreggnet_exec::agent` braid; forge/`CodeRootMismatch` teeth bite
  (`verify.rs:180-208`). **Landing** live banner is honest ("checking…" → "Live
  status unavailable" on failure, never false green); no fixtures.
- These three panes are **not yet in `deploy/staging/docker-compose.yml`** —
  consistent with the reviewed-go framing, not silently shipped as prod-live.

### webauth (`DreggNet/webauth`) — the auth core is SOUND
- `/auth` `decide` (`lib.rs:113`) runs, in order and fail-closed: revocation →
  `verify_chain` (full ed25519 chain-from-root + tail-key match, `cred.rs:473-494`)
  → `is_expired` → `verify` (chain re-check + caveat meet incl. the cap). The cap is
  bound from the **surface's** required cap (`grant.rs:68-70`), not the credential,
  so it cannot be self-satisfied. Every error/None branch returns `deny` — **no
  fail-open**. Subject is **never client-supplied** (derived only from the verified
  credential, inbound `X-Dregg-Subject` ignored + Caddy-stripped — **no `dev_subject`
  leak**). No-amplify attenuation holds end-to-end (tested). The residual risks are
  operational (F5 break-glass, F6 revocation), both default-off / honestly labeled.

### cipherclerk extension (`breadstuffs/extension`)
- **Sign / submit / login are REAL.** `signTurnV3` (`background.ts:2899`) → wasm
  `sign_turn_v3` (`wasm/src/lib.rs:1917-1979`) real `ed25519_dalek`; submit is a
  real `fetch` to `/api/turns/submit-signed`. `capLogin` (`background.ts:1544-1597`)
  is a real challenge→sign→session (real `POST /auth/challenge`, real Ed25519 of the
  challenge bytes, real `POST /auth/login`; missing token surfaced as an error, no
  canned session). At-rest encryption is real PBKDF2-600k + AES-256-GCM; mnemonic
  derivation real. **The one genuinely-unsafe primitive is fail-closed:**
  `dregg:composeProofs` (`background.ts:3804-3816`) returns an explicit error
  ("STARK membership hash is not collision-resistant (forgeable)") rather than
  shipping a forgeable proof — the textbook honest seam. Auth-receipt seed uses
  blake3 (CR), deliberately not the forgeable demo STARK.

### MCP (`DreggNet/cli/src/mcp.rs`) — 9 verbs, all REAL
| Verb | Real / Canned |
|---|---|
| `dregg_verify` (`mcp.rs:722`) | **REAL re-witness** — `verify_site_bundle` checks signer, `verify_chain`, **recomputes** `content_root`; `tamper:true` really flips a byte and `bail!`s if a tampered bundle passes |
| `dregg_agent_verify` (`mcp.rs:916`) | **REAL re-witness** — `verify_agent_run`: `verify_chain` + `consumed<=budget` + final-total agreement; real error on the false branch |
| `dregg_deploy` (`mcp.rs:462`) | REAL (`deploy_on_disk` local / `CloudClient` HTTP live) |
| `dregg_run` (`mcp.rs:576`) | REAL — executes caller's WAT via `fulfill_workload` (wasmi durable step); never reaches the 42/84 demo constant |
| `dregg_login` (`mcp.rs:387`) | REAL (`mint_caps` / `RootKey::generate` / `subject_of`) |
| `dregg_machines` (`mcp.rs:948`) | REAL HTTP to gateway |
| `dregg_status` (`mcp.rs:270`) | REAL (reads persisted Store) |
| `dregg_cell_read` (`mcp.rs:334`) | REAL (reads persisted Store) |
| `dregg_agent_deploy` (`mcp.rs:814`) | **REAL enforcement, SCRIPTED brain** — honest seam, disclosed in docstring + tool description |

The module header's claim "no second object model and no mock — the MCP is a face,
not a reimplementation" (`mcp.rs:6-11`) **holds**: every verb reuses the same
library symbols the CLI imports. The only "mock" is the agent's scripted plan,
which the verb docs disclose.

---

## The worst fake (one line)

`--os-isolation` (F1): a fully-built, unit-tested per-tenant jail (`JailSpec`/
`bwrap`) that is **never invoked on any real path**, while the flag that names it
re-enables an **unconfined raw shell on the operator-key-holding host** — a security
mechanism presented as enforced that runs nowhere. Runner-up: the session budget
that silently **resets to full on every SSH re-attach** (F2), an unbounded-spend
hole behind a "hard bound" claim. **Both were FIXED on 2026-06-30 (F1: the flag
hard-errors, no jail claimed; F2: consumed persists across re-attach) — see the
RESOLVED notes above.**
