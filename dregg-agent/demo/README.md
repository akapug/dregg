# dregg-agent — a real, flexible, live operator agent you can audit

Hand a **live model** an *arbitrary* natural-language goal, a **budget**, and a
**cap bundle**. It runs a genuine **reason → act → observe** loop: the model
decides the next tool call, and every call is **cap-gated · metered · receipted**
and executed **for real** — a real shell, real fs, real http, real `git clone`,
or the **real Stripe Skills for Hermes** (provision its own SaaS, pay for the
services it uses). The whole run is one cryptographic receipt chain you can
re-verify yourself, offline, trusting no host.

There is **no script**. Hand it a different `--goal` and it genuinely adapts —
that is the proof it is not a puppet.

Built on [`dregg-agent`](../) — the open-source (AGPL), substrate-only,
cap-bounded / budget-bounded / receipted agent runtime. No cloud, no control plane.

## Run it (one command)

```sh
bash demo/business.sh
```

It builds once, then runs **two beats**: (1) the live agent on a real open goal
(clone a tiny repo, inspect it, hit the GitHub API, provision a SaaS, pay for the
work — all real), and (2) the **Stripe Skills** beat (provision a DB + pay a
vendor, with the ungranted-vendor and over-budget teeth shown). Each beat
narrates every real step, writes a receipt chain, **re-witnesses it**, and shows
a **tampered line caught**. A model key in `~/.nvidiakey` (or `NVIDIA_API_KEY`)
drives beat 1 live; without one, a bundled transcript replays (tools still run
for real). The Stripe legs run against the recorded transport offline and the
**live CLIs** the moment a test key + the Stripe CLIs are present.

Hand it your own goal:

```sh
bash demo/business.sh "clone https://github.com/octocat/Hello-World, read its \
   files, and report what the repo is" --caps shell,fs,git:github.com --budget 800
```

## What the judge sees

1. **A live model reasons and acts.** The open goal makes a real NVIDIA
   Nemotron agent `git clone` a repo, `list_dir` + `fs_read` it, `http_get` the
   GitHub API, `stripe_provision` its own database, and `stripe_pay` a vendor —
   each decided live from the previous observation. Native OpenAI `tool_calls`
   drive it (confirmed against the live endpoint).
2. **The real Stripe Skills for Hermes.** `stripe_provision` wraps the Stripe
   **Projects** CLI (`stripe projects add neon/postgres` — the agent provisions
   its own SaaS); `stripe_pay` wraps the Stripe **Link** CLI (`@stripe/link-cli`
   — the agent pays for a service it uses). Each is cap-gated **per provider /
   vendor** (`provision:neon` / `pay:openai`), the amount drawn from the budget
   cell, and receipted.
3. **Every tool is on a leash.** Each call is cap-gated **per-tool AND
   per-resource**: `shell` is granted but confined to the workdir; `fs` only
   under the workdir root (a `/etc/passwd` read is refused **before it runs**, no
   receipt); `http` only to granted hosts; an ungranted vendor/provider is
   **cap-refused**; the pay amount is drawn from the budget cell, so an
   over-budget pay is refused **in-band before any money moves**.
4. **It is all receipted.** Every admitted action is sealed into a prev-hash
   chained, ed25519-signed receipt (with a witnessed `(command · inputs ·
   result)` binding), so a forged "it succeeded / I paid $5 not $500" breaks the
   signature.
5. **SCALE — no amplify.** It forks a sub-agent with a *narrower* cap bundle it
   provably cannot exceed (an out-of-bundle http / pay is refused on both axes).
6. **PROVE.** `dregg-agent verify run.json` re-witnesses the whole run offline —
   chain intact + signed, consumed ≤ ceiling, sub-agent chain too. Then
   `--tamper` flips one receipted line and the proof **rejects it**
   (`BadSignature`).

## The operator toolkit (every tool rides the same cap · meter · receipt rail)

| tool | what it does | cap (per-resource) |
|------|--------------|--------------------|
| `shell` | real bash: persistent cwd, pipes/`&&`, real stdout/stderr/exit, timeout | `shell` (workdir-confined) |
| `fs_read`/`fs_write`/`list_dir`/`mkdir` | real fs, scoped to the workdir root | `fs-read:<path>` / `fs-write:<path>` (prefix grant) |
| `http_get` | real outbound GET | `http:<host>` (per-host egress) |
| `git_clone` | real shallow clone into the workdir | `http:<host>` |
| `stripe_provision` | the Stripe **Projects** skill: `stripe projects add <provider>/<service>` (provision a SaaS) | `provision:<provider>` + the budget draw |
| `stripe_pay` | the Stripe **Link** skill: `@stripe/link-cli` pay (pay a vendor) | `pay:<vendor>` + the variable budget draw |
| `cell_read`/`cell_write` | real committed state | `cell-read:`/`cell-write:<path>` |

The cap bundle is a **signed** `dga1_` credential; resource scopes ride
`AttrPrefix`, so a sub-agent can only ever **narrow** them (`attenuate_subset`).

## Caps (`--caps`, comma-separated)

`shell`, `fs`, `git:HOST`, `http:HOST`, `provision:PROVIDER` (Stripe Projects
skill), `pay:VENDOR` (Stripe Link skill), `spend` (pay any vendor), `run_tests`,
`cell:/path` — each is a per-tool / per-resource grant. Default:
`shell,fs,git:github.com,http:api.github.com,provision:neon,pay:openai`.

## The money leg (honest)

The budget draw is **always real** (a metered ledger cell — the spend bound is a
theorem about the cell, not a watchdog). The two **Stripe Skills** are the real
CLIs:

- `stripe_provision` → `stripe projects add <provider>/<service>` (Stripe Projects
  CLI) — the agent provisions real SaaS and syncs the credentials.
- `stripe_pay` → `@stripe/link-cli` pay (Stripe Link wallet for agents) — the
  agent pays a vendor via one-time virtual cards / shared payment tokens.

The live legs run **only when the CLIs + a test key are present**: put a key in
`~/.stripekey` (or `STRIPE_API_KEY`) and install the Stripe CLIs, and the tools
shell the real commands in test mode. The key is read at runtime, passed to the
child via the **environment** (never argv), and **redacted** from every summary /
receipt / log. Without the CLIs+key, a faithful **recorded transport** runs,
labeled honestly (*"(Stripe Skill live leg needs the CLI + a test key)"*) — never
a fake "✓ paid". The amount is bound into the receipt twice (the budget `cost` +
the witnessed binding), so a forged "I paid $5 not $500" breaks the signature.

## Capture a good run for the film

```sh
dregg-agent run --record demo/resp.json --out demo/run.json    # live; saves the brain
dregg-agent run --replay demo/resp.json                        # re-runs it, tools FOR REAL
```

Replaying a captured **real** run is legit (the model's decisions are re-fed; the
tools execute for real against the same workdir). The default is always live.

## Verify it yourself

```sh
dregg-agent verify demo/run.json          # re-witness offline (green)
dregg-agent verify --tamper demo/run.json # one line flipped → caught (BadSignature)
```

Nothing here is mocked: the model really reasons, the tools really run, the
budget refusal is real, and the receipts really re-witness. The only recorded
artifact is the optional `--replay` capture — and it re-executes the real tools.
