# CLI / SDK Interface Review — interfacing with DreggNet Cloud

*Dated 2026-06-30. A read-only assessment of the **client** experience — the CLI/SDK
a user drives, not host-your-own. Grounded to file:line at HEAD; every flow below
was run against the prebuilt `target/debug/dregg-cloud`.*

## TL;DR

The `dregg-cloud` CLI is genuinely good as a *self-contained local notebook*: the
verb set is coherent, the help text is unusually honest, the verify-don't-trust
commands work and are legible, and the secret-redaction / 0600 hygiene is real.
The earlier stranger-usability pass (binary-name `dregg-cloud`, honest "published
locally not served" deploy output, login redaction) **holds** — I re-ran it.

The two things a hackathon judge will actually hit and stumble on:

1. **Duroxide `Database locked` / activity-failure WARN logs leak to stderr** in
   the middle of `deploy` and `run`, making a *successful* run look broken.
2. **`run` hides the real failure.** A workload whose WASM lacks the `run` export
   prints a misleading `(no output — the lease lapsed and the machine was reaped)`
   — the true cause (`export 'run' not found`) is buried in a WARN line. A
   stranger who writes `(export "main")` instead of `(export "run")` dead-ends
   with the wrong diagnosis.

And the strategic gap for "interface with the *live* cloud": **there is no live
cloud to interface with from this CLI.** Every verb routes through the in-process
`LocalProvider`; there is no `--endpoint`/`--node` flag, and the CLI never calls
the gateway's machines API. This is honestly disclosed in the output and docs, but
it means the headline "interface with the cloud" is, today, "interface with an
in-process simulation of the cloud."

**First-run verdict:** a stranger following `docs/DEVELOPERS.md` §3.5 *exactly*
reaches first value in ~5 min (login → deploy → verify is a real, satisfying
loop). A stranger who improvises even slightly (wrong WAT export, or expecting a
live URL) hits friction with poor diagnostics. The log noise alone reads as "this
is broken" on first contact.

---

## 1. `dregg-cloud` CLI (`cli/src/main.rs`, binary `dregg-cloud`)

Crate `dreggnet-cli`, `[[bin]] name = "dregg-cloud"` (`cli/Cargo.toml:12`). Verified
the binary name matches every printed next-step hint via `prog()`
(`cli/src/main.rs:78`) — good, no name collision.

### Verb-by-verb

**`login`** (`cmd_login`, `main.rs:837`) — **Good.** Re-ran `login --new`: prints
subject, caps, root, a redacted `dga1_7PeA1Ra…` credential, a BEARER-SECRET
warning naming the 0600 state file. Redaction (`redact_credential`, `main.rs:828`)
and the 0600 chmod (`Store::save`, `main.rs:666`) both hold.
- **Rough:** the post-login hint says *"reveal it with `dregg-cloud login --new
  --show-credential`"* (`main.rs:918`). But re-running `login --new` mints a
  **brand-new account**, it does not reveal the existing one. Misleading hint.
- **Rough:** `--credential` without `--root` silently produces an account that can
  `deploy` but not `domains` (`account_authority`, `main.rs:939`). The error when
  you later try `domains` is good, but nothing at login time warns you you've
  created a half-capable account.

**`deploy`** (`cmd_deploy`, `main.rs:2224`) — **Good core, two rough edges.** Re-ran
on a local git repo: clone→build→publish→signed-receipt→recorded-bundle all
work; output is honest ("published locally (not yet served on the public edge)",
`main.rs:2273`); the source-commitment manifest + `verify it` next-step are
genuinely nice differentiators.
- **Rough (judge-hits-it):** duroxide emits `WARN … Database locked …` lines to
  stderr mid-deploy (observed every run). The deploy *succeeds*, but it reads as
  an error. See quick-win #1.
- **Rough (honesty bug):** the `login` docstring claims *"Subsequent `deploy` /
  `domains` default their owner to it"* (`main.rs:166`), but `deploy --owner`
  defaults to the literal `"operator"` (`main.rs:150`) and `cmd_deploy` never
  consults `store.identity`. After `login --new` (subject `dregg:cc94…`), the
  deployed site's owner is still `operator`. `domains` *does* honor the identity;
  `deploy` does not. The claim and the behavior disagree. See quick-win #4.
- `--serve` works (binds `127.0.0.1:<port>`, prints copy-pasteable `curl` lines
  with the `Host:` header and the no-DNS path-prefix fallback — `main.rs:2345`).

**`run` / `run --source`** (`cmd_run`, `main.rs:2048`) — **The weakest verb's UX.**
The plumbing is real (the declared WAT threads into a durable metered workflow,
the owned wasmi sandbox steps run, the meter charges). But:
- **Rough (judge-hits-it):** with a WAT exporting `main` instead of `run`, the run
  produces `state reaped` + `(no output — the lease lapsed and the machine was
  reaped)` (`main.rs:2129`). That message blames the **lease/budget**. The actual
  error — `wasmi-provider: export 'run' not found or not a function` — appears
  only in a duroxide WARN line, not in the CLI's own output. The diagnosis the CLI
  gives is wrong. See quick-win #2.
- **Rough:** the `--source` help (`main.rs:127`) says "the declared program; WAT
  text" but never states the required export name (`run`) or the supported
  signature. The contract lives only in `docs/DEVELOPERS.md:307`.
- Same duroxide WARN noise as deploy.

**`verify`** (`cmd_verify`, `main.rs:1227`) — **Excellent. The crown jewel.** Re-ran:
`✓ verified: served bytes match the committed root, receipt chain intact`, with
site / owner / content-root / assets / signer / commit, and a source-commitment
cross-check against the recorded deploy. Honest refusal when a deploy predates
signed publishing (`main.rs:1235`). The `--url` path fetches the bundle from a
running server over the wire (`fetch_site_bundle`, `main.rs:1255`) — a genuine
non-witness read. This is the literal "you verify, you don't trust" command and it
delivers. Only nit: no `--tamper` self-demo here (the `dregg-agent` CLI has one;
`dregg-cloud verify` does not — a missed teaching opportunity, see #6).

**`agent deploy` / `agent verify`** (`main.rs:1536` / `main.rs:1833`) — **Very good.**
Re-ran `agent deploy --budget 10`: clear report — admitted / cap-refused /
budget-bound counts, receipt-chain tip + signer, consumed/headroom with a `% of
ceiling`. `agent verify <id>` re-witnesses cleanly. The mock path is self-contained
(no key needed); `--brain kimi/openai` is a real BYO-LLM path behind the
`kimi-live` feature with a good rebuild-hint bail (`main.rs:1788`). The `--subagent`
attenuation demo is a strong "no-amplify" story. This is the most demo-ready verb.

**`domains add/list/verify`** (`main.rs:961` / `1028` / `1068`) — **Good + correctly
strict.** `add` emits the exact DNS record + the copy-paste `verify` next-step.
`verify` resolves through **live system DNS** and explicitly refuses to trust the
`--txt`/`--cname` you pass (`main.rs:1086`, advisory-only) — the right security
posture. Binding is cap-gated under the account root. Requires a `login --new` (or
`--credential … --root`) first, with a clear error if missing.

**`model cron/stream/escrow/run`** (`main.rs:1886`+) — **Good, slightly over-rich
for a first-run.** Real receipted runs over the shared meter; the escrow path runs
a genuine agent and settles on the verified verdict. Honest output. But this verb
is the densest and least likely to be a judge's first stop; it competes for
attention with the simpler keystones.

**`ls` / `status`** (`main.rs:1128` / `2191`) — **Good + honest.** `ls` header is
explicit: *"local notebook — these records are not yet on the public network"*
(`main.rs:1136`), and per-row labels say `(mock record)` / `(local — published,
not served)`. No live state is dressed up as cloud state. `status` is a clean
table.

**`logs`** (`cmd_logs`, `main.rs:1346`) — **Good.** Real captured stdout/stderr from
the durable log store, cap-scoped to the caller (a different subject is `Forbidden`
— `main.rs:1382`); `--follow` / `--search` / `--tail`. Falls back to step metadata
when no capture exists, clearly labeled. Deploys honestly show "runtime-log capture
is a named seam."

**`destroy`** (`main.rs:1474`) — **Fine.** Prefix-matches id / domain, cascades
lease→workloads, prints what it removed, errors if nothing matched.

### Cross-cutting CLI observations

- **Honesty of output: genuinely above average.** "mock record", "local notebook",
  "not yet served on the public edge", "named seam" — the CLI consistently refuses
  to overclaim. This is a real asset; do not let the quick-wins erode it.
- **`--help` is excellent** — every subcommand carries a real one-paragraph
  explanation. A judge running `dregg-cloud --help` learns the model.
- **The duroxide log noise is the single biggest first-impression liability.** It
  appears on the two most common verbs and looks like failure.
- **No global `--json` output mode.** For an agent/judge scripting against the CLI,
  every verb is human-prose-only (except `model` which dumps JSON). A `--json`
  would make the CLI agent-drivable. (Lower priority than the noise/diagnostics.)

---

## 2. `dregg-agent` CLI (`~/dev/breadstuffs/dregg-agent/src/bin/dregg-agent.rs`)

A separate binary in the **breadstuffs** (open substrate) repo — the substrate-only,
no-cloud agent runtime. `run --goal/--budget/--caps … ` + `verify <run.json>
[--tamper]`.

- **Ergonomics: strong.** `--goal` is free natural language; `--caps` is a tidy
  comma list with a per-resource grammar (`shell`, `fs`, `git:HOST`, `http:HOST`,
  `spend`, `cell:/path`) documented both in `usage()` (`bin:50`) and the demo
  README. Sensible live defaults (`DEFAULT_GOAL` / `DEFAULT_CAPS`, `bin:209`/`215`)
  so a bare `run` does something real.
- **Output: very legible.** Banner with GOAL / MODEL / BUDGET / WORKDIR / CAPS /
  FUNDING; a `reason → act → observe` transcript with ✓/✗ per step + tool
  summaries; a one-line tally (admitted · cap-refused · budget-refused · consumed
  · headroom); then "wrote the receipt to run.json / audit it yourself".
- **The verify / tamper story is the best teeth in either repo.** `verify` prints
  a PROVE banner + ✓ chain / ✓ bound / ✓ scale; `verify --tamper` flips a spend
  receipt's cost and the audit catches it (`BadSignature`), with `--tamper`
  correctly exiting 0 because a caught tamper is the *intended* outcome
  (`bin:161`). This is exactly the "the proof does not lie" demo a judge wants.
- **Honest funding leg** (`bin:293`): real Stripe test PaymentIntent only with an
  `sk_test_` key, else a clearly-labeled real budget-ledger draw — never a fake
  "✓ paid".
- **Rough:** `run` needs the `live-brain` feature *and* an NVIDIA key
  (`~/.nvidiakey`), and without the feature it bails with a rebuild hint (`bin:177`)
  — good, but it means the headline `run` verb is not exercisable from a clean
  `cargo run` without setup. `verify` is std-only and always works, so the
  `--replay`-then-`verify` path is the dependency-free demo. Worth signposting that
  more loudly for judges without a key.
- **Naming friction:** two different live-LLM feature flags across the two repos —
  `dregg-agent` uses `live-brain`, `dregg-cloud` uses `kimi-live`. Minor, but a
  judge moving between them will trip.

---

## 3. SDKs — `@dregg/sdk` (npm) + `dregg` (pip)

Both **exist and are real**, but they are **substrate SDKs, not DreggNet-cloud
SDKs**, and they live in **breadstuffs**, not this repo.

- `~/dev/breadstuffs/sdk-ts` → `@dregg/sdk` v0.3.0 (`package.json`): a proper
  multi-entry TS package (`.`, `./raw`, `./pg`, `./wasm`, `./browser`), typed,
  tree-shakeable. API is the substrate vocabulary: "authorization-first turns,
  receipts, the organ nouns (trustline, channels, mailbox), attested-query
  light-client reads, profiles, events, the cell-program constraint language."
- `~/dev/breadstuffs/sdk-py` → `dregg` (pyproject, maturin): light kernel-free
  client by default, optional heavy `dregg[kernel]` (embedded Lean) and `dregg[pg]`
  extras. Same substrate surface: "Identity → turn → sign → submit → Receipt …".
- **The mismatch that matters for this review:** the quickstart in
  `docs/USING-DREGGNET.md` and `docs/GETTING-STARTED.md` advertises a
  `ServiceRuntime` with `pay_native` / `lease` / `lease.run` as *the* SDK cloud
  interface. That `ServiceRuntime.lease(...).run(work)` shape is the **substrate
  Rust `dregg-sdk` example** (`sdk/examples/agent_business_loop.rs`), not a verb on
  the `dregg-cloud` control plane. So "the SDK to interface with the cloud" is
  really "the substrate SDK to author turns locally"; the live-network leg is
  "the same call pointed at a node" — which, as in §4, is not yet a wired endpoint.
- There is **no DreggNet-cloud client SDK** (no TS/Python package that wraps the
  gateway machines API / lease-open / deploy over the wire). The CLI is the only
  cloud-facing client, and it too is in-process.

Verdict: the SDKs are well-built for what they are (substrate turn authoring), and
the docs' code snippets are plausible, but a judge who reads "interface with the
cloud" and `pip install dregg` will get an offline turn-authoring library, not a
remote cloud client. The docs are mostly honest about this ("runs the real verified
executor in-process … paying a peer or running against the live network is the same
call pointed at a node") but the framing oversells the cloud connection.

---

## 4. The connect-to-a-live-cloud story

**This is the central strategic gap.** There is no client path to a live DreggNet.

- The CLI has **no `--endpoint` / `--node` / `--gateway` flag anywhere**
  (`grep` of `cli/src/main.rs` finds only the LLM `--llm-base`, the deploy
  `--serve` localhost bind, and `verify --url` to a *local* running server).
- Every verb routes through the in-process `Scheduler` over `LocalProvider`
  (`main.rs:16`, `cmd_run` at `main.rs:2084`). The header comment is explicit:
  "no live edge — that is reviewed-go" (`main.rs:14`).
- The **gateway has a real fly-compatible machines API** (`gateway/src/*.rs`,
  ~5K LOC, binds TCP, serves the route table + lease gate), but **the CLI never
  calls it.** The control-plane→gateway wire that would let a client open a lease
  on a remote node is not connected to any client.
- The only "live" endpoints a user can point at are read-only and external to the
  CLI: `portal.dregg.studio` (a wasm light client, browser) and the Discord bot
  (token-gated). Neither is the CLI/SDK "interface with the cloud."

So the honest current shape: **the CLI is a faithful local simulation of the cloud
control plane.** The plumbing it drives is real (durable workflows, signed
receipts, the meter), but it provisions an in-process machine, not a remote one.
For "interface with the *live* cloud," the missing piece is a client transport: a
`--endpoint <gateway-url>` that makes `lease open` / `run` / `deploy` POST to the
gateway machines API instead of `LocalProvider`.

---

## Ranked quick-wins (most-improves "interfacing with the cloud" first)

Each is tagged **[today]** (cheap enough to land in a sitting) or **[bigger]**.

1. **Silence the duroxide WARN noise on `deploy`/`run`. [today]** Install a quiet
   `tracing_subscriber` in `main()` (default the duroxide/duroxide-provider targets
   to `error`, honor `RUST_LOG` for opt-in). The CLI currently installs no
   subscriber, so duroxide's default leaks `Database locked` / activity-failure
   lines into the middle of successful runs. This is the #1 first-impression
   liability and a judge hits it on the most common verb. ~10 lines.

2. **Surface the real workload failure in `run`. [today]** When a workload is
   reaped/lapsed, print the actual durable error (e.g. `export 'run' not found`)
   instead of the generic `(no output — the lease lapsed and the machine was
   reaped)` (`main.rs:2129`), which misdiagnoses a program-contract error as a
   budget problem. Thread the workflow's failure reason into the output. Pair with:
   state the required export name (`run`) + signature in the `--source` help
   (`main.rs:127`). The single biggest "stranger improvised and dead-ended" fix.

3. **Add `--endpoint <gateway-url>` to the cloud verbs (lease/run/deploy/status/ls).
   [bigger]** The one change that turns "interface with a local simulation" into
   "interface with the live cloud." `LocalProvider` becomes the default; an
   `--endpoint` selects a remote provider that POSTs to the gateway machines API
   (which already exists). Even a thin `lease open`/`status` over the wire would
   make the headline claim true. This is the highest-*value* item; it is not a
   today item, but it should be the next real build.

4. **Make `deploy` honor the logged-in identity, or fix the docstring. [today]**
   Either have `cmd_deploy` default `owner` to `store.identity.subject` (matching
   `domains` and the `login` docstring at `main.rs:166`), or correct the docstring
   to say only `domains` defaults to the account. Today they contradict and a
   deployed site is owned by `operator` even when logged in. ~5 lines.

5. **Fix the post-login reveal hint. [today]** `main.rs:918` tells the user to
   reveal the credential with `login --new --show-credential`, which mints a *new*
   account. Either drop the hint or add a `login --show` / `whoami --show-credential`
   that reveals the *current* account's credential. ~5 lines (or a tiny new verb).

6. **Add a `verify --tamper` self-demo to `dregg-cloud`. [today]** `dregg-agent`
   has the killer "flip one line → caught" demo; `dregg-cloud verify` does not.
   A `--tamper` that flips a served byte / receipt field and shows the `✗ MISMATCH`
   path would make the cloud CLI's verify command as persuasive as the agent's.
   The verify machinery already distinguishes the mismatch case (`main.rs:1294`).

7. **Reconcile the SDK story with reality, or build a cloud client. [bigger]** The
   docs sell `pip install dregg` / `npm i @dregg/sdk` as the way to "interface with
   the cloud," but those are substrate turn-authoring SDKs with no remote DreggNet
   transport. Short term [today]: tighten the docs to say the SDKs author turns
   locally and the cloud face is the CLI. Long term [bigger]: a real cloud client
   SDK over the same `--endpoint` gateway transport as #3.

8. **Unify the live-LLM feature flag name. [today]** `dregg-agent` uses
   `live-brain`; `dregg-cloud` uses `kimi-live`. Pick one (or alias) so a judge
   moving between the two binaries isn't tripped. Cosmetic but cheap.

9. **Add a global `--json` output mode. [bigger-ish]** Makes the CLI
   agent/script-drivable (a judge wiring it into their own agent). Most verbs are
   human-prose-only today; `model` already emits JSON, so the precedent exists.

### Cheap-enough-for-today set

Items **1, 2, 4, 5, 6, 8** are all small, localized edits with no architectural
risk. Doing **1 + 2** alone would remove the two worst first-run stumbles a
hackathon judge hits; adding **4 + 5 + 6** closes the honesty/consistency gaps and
gives the cloud CLI its own tamper-demo. Item **3** (the `--endpoint`) is the real
"interface with the live cloud" unlock and should be the next build, not a today
patch.
