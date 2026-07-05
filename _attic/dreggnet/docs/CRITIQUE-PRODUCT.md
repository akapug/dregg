# CRITIQUE — Product / Usability (the stranger test)

An adversarial, honest read of DreggNet's *user-facing* surfaces — the `dreggnet`
CLI, the deploy / domains / hosting flows, the onboarding docs, and the
"verify-don't-trust" hook — asking one question: **could a real developer (not
ember, not us) actually use this today?** Scope is the product surfaces; the
circuit / metatheory are out of scope by design.

Grounded in the code at HEAD (`cli/src/main.rs`, `dregg-deploy/`,
`dregg-domains/`, `docs/*`). Each finding cites the flow + the file:line and ends
with a fix direction. Ranked worst-first.

> **Verdict up front.** A stranger **cannot** complete the marquee flows
> end-to-end from the CLI today. The two paths that *do* work for a stranger are
> the Docker one-command demo (`docs/RUN-LOCALLY.md`) and the SDK economy loop
> (which lives in the *other* repo, `breadstuffs/`). The headline CLI verbs —
> `deploy` a site to a live URL, `domains add/verify`, `run` your own workload —
> each break in a specific, demonstrable way below. None of these are deep
> architectural problems; they are last-mile DX gaps and naming/honesty defects.
> The honesty *register* of the codebase is genuinely excellent; the honesty has
> just not reached the **runtime output and the binary name** yet.

---

## The frictions, ranked

### 1. CRITICAL — the binary is `dreggnet`, but every doc, every help string, and every printed next-step says `dregg`

The CLI binary is named `dreggnet` (`cli/Cargo.toml` `[[bin]] name = "dreggnet"`),
and the operator runbook uses it correctly (`docs/RUN-LOCALLY.md:71`
`dregg-cloud lease open …`). But the developer half — the doc-comment header
(`cli/src/main.rs:6-9`), `docs/PERMISSIONLESS-CLOUD-PLAN.md:221-225`, and, worst
of all, the program's **own printed instructions** — all say `dregg`:

- `cli/src/main.rs:530` prints `then    dregg-cloud domains verify {} --txt {}`
- `cli/src/main.rs:533` prints `then    dregg-cloud domains verify {} --cname {}`
- `cli/src/main.rs:483` errors with `run \`dregg-cloud login --new\` first`
- `cli/src/main.rs:552` prints `(\`dregg-cloud domains add <domain> --site <name>\`)`

So the very first thing a user does — copy the next-step line the tool just
printed — fails: there is no `dregg` binary in this repo. And `dregg` **is** a
real binary in the sibling `breadstuffs/` repo (the substrate CLI), so a developer
who has both checked out runs the *wrong program* and gets a confusing error,
not a missing-command error. This breaks command #1 of every CLI journey.

**Fix.** Pick one name and make it consistent everywhere — the printed prompts,
the help header, and the docs must match `argv[0]`. Either (a) sweep all
`dregg <verb>` → `dreggnet <verb>` in `cli/src/main.rs` doc/prints + the deploy
docs, or (b) deliberately ship the CLI *as* `dregg-cloud`/`dregg cloud` and brand
it that way, but never as bare `dregg` (collides with the substrate). Lowest
effort, highest payoff: derive the prompt strings from `clap`'s `crate_name!` /
the actual bin name so they can't drift again.

---

### 2. CRITICAL — `dregg-cloud deploy` prints a live `https://<name>.example.com` URL that nothing serves

This is the keystone DX ("you ship, we host", made verifiable) and the single
most compelling promise in the product. The CLI runs the real
clone→detect→build→publish pipeline and prints:

```
deployed: https://blog.example.com
```

(`cli/src/main.rs:927`, `cmd_deploy`). But the publish target is an **in-process
`SiteRegistry` created fresh inside the command and dropped when the process
exits** (`cli/src/main.rs:914` `let registry = Arc::new(SiteRegistry::new());`).
Nothing in the CLI path connects that registry to a running gateway, and the
serving wire is explicitly deferred: `docs/WEB-HOSTING.md:181-189` ("Deferred —
the live `example.com` deploy … Mounting `SiteHostHandler` in the gateway serving
binary"), and DNS `*.example.com` + Caddy wildcard TLS are "design; deferred to
the deploy lane." `dregg-deploy/src/lib.rs:12` labels step ⑤ "LIVE — served at
`<name>.example.com`," and the lib doc-comment even asserts "The site is now
served by `registry`" (`lib.rs:41`) — but `registry` here is the throwaway the CLI
drops.

Net effect: the user runs the headline command, is told their site is *deployed*
at a real-looking HTTPS URL, and the URL does not resolve / 404s. That is the
worst kind of demo failure — it looks finished and isn't usable end-to-end.

**Fix (in order of value).**
1. Make the CLI deploy write into a registry the local gateway actually serves
   (or have `dregg-cloud deploy` optionally `--serve` to bring up `dreggnet-host`
   over the published content so `curl -H 'Host: blog.example.com' localhost:8080`
   works on the spot). That turns the promise into a real local round-trip.
2. Until the live edge is wired, the output must stop printing a bare live URL as
   if it resolves. Say what is true: `published locally (commit <h>); serving on
   the public edge is the gateway-mount step — see docs/WEB-HOSTING.md`. Print the
   verify manifest path (`/.well-known/dregg-deploy.json`) the deploy genuinely
   produced, which *is* a real, shippable differentiator.

---

### 3. HIGH — `dregg-cloud run --source X` validates and records X, then runs a hardcoded demo program instead

The `run` verb advertises `--source <PATH>` as "Path to the workload source (the
declared program; WAT text)" (`cli/src/main.rs:96-98`). It reads the file, checks
it is non-empty (`cli/src/main.rs:801-805`), records its path — and then **never
passes it to execution**. `cmd_run` calls `scheduler.place(lease)`
(`cli/src/main.rs:813`) with no source argument; the executed workflow is the
fixed canned demo (`add(40,2)=42`, `*2=84`), as the file's own honesty note admits
(`cli/src/main.rs:39-41`: "the durable workflow's `WorkloadSpec` is fixed there
today"). So a developer hand-writes a WAT program, runs it, and sees output from a
program they did not write. The honesty note is in a source comment the user never
reads; the `--help` text says the opposite.

**Fix.** Either thread `--source` into the bridge `WorkloadSpec` (the real fix —
"run *my* program"), or, until then, change the flag help + the run output to say
the executed program is a fixed demo and `--source` is recorded only. A flag that
silently does nothing is worse than an absent flag.

---

### 4. HIGH — the developer CLI is invisible in the onboarding, and the onboarding points into a different repo

The two "start here" docs — `docs/USING-DREGGNET.md` ("I just joined, now what")
and `docs/DEVELOPERS.md` ("the single entry point") — **never mention** the
`login` / `deploy` / `domains` / `ls` / `logs` / `destroy` verbs at all (grep:
zero hits). They route every reader to the Discord bot, the SDKs, and the gateway
machines API. So the CLI flows that this critique is about — the ones with real
e2e tests (`cli/tests/deploy_e2e.rs`, `cli/tests/cli_verbs_e2e.rs`) — are
undiscoverable. A developer would never learn `dregg-cloud deploy` exists.

Compounding it: the entry docs lean heavily on docs that live in the **sibling
`breadstuffs/` repo** — `breadstuffs/docs/GETTING-STARTED.md`,
`breadstuffs/QUICKSTART.md`, `breadstuffs/docs/ONBOARDING.md`,
`breadstuffs/docs/guide/*`, `breadstuffs/sdk-ts/README.md`. There is no
`GETTING-STARTED.md` or `QUICKSTART.md` in DreggNet itself. A stranger who clones
*only* DreggNet (the natural assumption for "use DreggNet") hits a wall of dead
relative links and a `breadstuffs/` prefix they don't have.

**Fix.** (a) Add a CLI quickstart block to `DEVELOPERS.md §2/§3`: `login → deploy
→ ls → logs` as a copy-paste path, with the real binary name. (b) State, once and
prominently at the top of both entry docs, that the SDK/substrate docs require the
`breadstuffs/` checkout and how to get it — or vendor a minimal self-contained
quickstart so DreggNet-alone is usable.

---

### 5. HIGH — `login` is split-brained: the realistic (wallet) path dead-ends at domains, and the demo path prints a bearer secret to the terminal with no warning

`dregg-cloud login` has two modes (`cli/src/main.rs:425-472`):

- `--credential dga1_…` (bind a wallet-held credential — the *realistic* path)
  records an **empty** `root_pubkey` (`cli/src/main.rs:443`), because the root key
  isn't recoverable from the wire. That is honest, but it means
  `account_authority` later refuses domain binding with "this account is a
  wallet-bound credential with no local root key … bind domains from a minted
  local account (`dregg-cloud login --new`)" (`cli/src/main.rs:484-488`). So the user
  who logs in the way the docs frame as primary (a wallet credential) **cannot use
  `domains` at all** and is told to throw it away for a `--new` local account.
- `--new` mints a fresh root + credential and **prints the `dga1_…` credential to
  stdout** (`cli/src/main.rs:468`) and persists it plaintext in `state.json`. A
  `dga1_` credential is a bearer secret. There is no "keep this secret" warning,
  no file-permission note, nothing flagging that it just dumped a key into the
  scrollback.

**Fix.** (a) Let a wallet-bound login optionally carry the verifying root (e.g.
`--root <hex>`) so the realistic path can also bind domains; or document the split
loudly so it isn't a silent dead-end. (b) Mark the minted credential as secret in
the output, write `state.json` `0600`, and consider not echoing the raw
credential by default (offer `login --new --show-credential`).

---

### 6. MEDIUM — `domains add → verify` cannot be completed by anyone without a real domain, DNS access, and propagation patience, and there is no worked example

The `verify` path correctly resolves through `LiveDns::from_system()` against the
binding's own `_dregg-verify.<domain>` TXT / `<domain>` CNAME, and pointedly does
*not* trust the `--txt`/`--cname` the user passes (`cli/src/main.rs:575-617`).
This is exactly right as security — it is the DOM-1 fix
(`docs/RED-TEAM-FINDINGS-2.md:32`), and credit is due. But as *DX* it means the
only way to see the add→verify loop succeed is: own a domain, publish a TXT
record, wait for propagation, then run verify. There is no sandbox, no example
domain in the docs, no `--dry-run` for a demo. A stranger evaluating the feature
hits `verify failed` with no path to a green result. The flow *looks* complete
(`add` prints a tidy challenge + next command) but is uncompletable in a tutorial
setting.

**Fix.** Ship a fully worked example in a domains doc (a real domain, the exact
TXT, the exact verify command, the success output) so a reader can see what
"works" looks like. Optionally a clearly-labeled local/dev resolver path for
demos (never the production verify) so the loop can be exercised offline. The
security must stay; the *teachability* is the gap.

---

### 7. MEDIUM — concepts land on the user with no inline explanation: cap-grades, meter units, DEC, leases, cipherclerk, `dga1_`

The CLI surface assumes the whole dregg vocabulary. `lease open` demands
`--cap-tier sandboxed|caged|microvm` with no hint of what differs or what each
costs; `--budget`/`--per-period` are "meter units" of an unspecified thing;
`deploy --budget` says "clone+build+publish each charge 1/step" (good!) but the
unit is never tied to DEC/$DREGG the docs talk about. "cipherclerk," "cell,"
"turn," "computrons," and "`dga1_`" all appear without point-of-use definition;
the explainers live in `breadstuffs/`. A normal developer at `--cap-tier` does not
know which to choose or what it implies for isolation or price.

**Fix.** A one-paragraph glossary at the top of `DEVELOPERS.md`, a `dreggnet
--help` example block, and richer `clap` `long_help` on `--cap-tier` (what each
grade isolates) and the budget flags (what a "unit" is and how it relates to DEC).
Sensible defaults so the happy path needs no grade choice.

---

### 8. MEDIUM — the CLI presents a local JSON notebook as if it were a cloud account; the "this isn't on the network yet" honesty never reaches runtime output

`ls` / `status` / `logs` all read `.dreggnet/state.json` (`cli/src/main.rs:62`,
`Store::load`). Leases are explicitly *mock* records (`cli/src/main.rs:36-37`,
"`lease open` registers a plain funded lease record rather than reading a real
funded lease from a dregg node"); deploys are local; domains are a re-adopted
local set. The output reads like a real control plane — `account`, `sites`,
`leases`, `domains`, `workloads` — with no marker that this is a local notebook
not network state. The scrupulous "real vs mock" honesty is in code comments and
deep docs, not in what the user sees when they type `dregg-cloud ls`.

**Fix.** Surface the state in the output the user actually reads: tag mock leases
and not-yet-served sites at runtime ("(local record — not yet on the network)"),
and have `ls` print the state-dir path so it's clear this is local. Honesty in a
doc-comment doesn't protect the user; honesty in the table does.

---

## What is genuinely good (credit where due)

- **The honesty register is the best thing here.** Nearly every doc carries an
  explicit "what's real vs deferred" section (`USING-DREGGNET.md §5`,
  `DEVELOPERS.md §6`, `RUN-LOCALLY.md` "live vs deferred", `WEB-HOSTING.md`
  code-proven-vs-deploy). This is rare and valuable; the *only* gap is that this
  honesty hasn't propagated to the binary name and the runtime output (findings
  1–3, 8). Close those and the candor becomes a genuine trust asset.
- **The fly.io-compatible machines API is a smart adoption hook.** "If you speak
  the fly machines API, you speak DreggNet's compute control plane"
  (`DEVELOPERS.md §2b`, `gateway/`) is legible, concrete, and lowers the barrier
  for a real audience. The real bridge-gate-before-record behavior (an
  unfunded/ill-formed lease yields 4xx + no machine) is exactly the right shape.
- **The security posture is real, not theater.** `RED-TEAM-FINDINGS-2.md` is a
  serious adversarial pass with concrete, mostly-fixed criticals (sandboxed
  builds, symlink/traversal refusal, live-DNS domain verify, HMAC-sealed
  SturdyRefs). The DOM-1 verify fix (never trust client-seeded DNS) and the D-1/D-2
  deploy-sandbox fixes are the right calls. A stranger's untrusted repo will not
  trivially RCE the host.
- **The verifiable-receipt hook is compelling and well-articulated.** "Don't
  trust the server; verify it in your own browser" (`USING-DREGGNET.md §2`) and
  the deploy **source-commitment manifest** — the build commit folded into the
  cell's `content_root` so *which commit a site was built from* is re-witnessable
  (`dregg-deploy/src/publish.rs:1-31`) — are real differentiators over fly /
  Liftoff. This is the product's strongest idea.
- **Several error messages are exemplary.** `deploy --budget < 3` explains *why*
  (`cli/src/main.rs:900`); a missing lease points to `lease open`
  (`cli/src/main.rs:798`); `domains add` prints the exact next command and the
  exact DNS record. This is the standard the rest of the CLI should meet.
- **The Docker one-command demo works** (`docs/RUN-LOCALLY.md`,
  `docker compose run --rm dreggnet dreggnet-demo`) and is a real, runnable
  first-five-minutes for an evaluator.

---

## The compelling hook — is "verify, don't trust" legible to a user?

In the **docs**, yes — `USING-DREGGNET.md §2` and the portal framing make it
clear and it is the right wedge. At the **CLI**, no: `deploy` produces a genuine
verifiable manifest but never tells the user it exists or how to verify it, and
`run`'s receipt-like output is a canned demo (finding 3). The single
highest-leverage move to make the hook land for a CLI user: after `deploy`, print
the manifest path and a one-line "verify your deploy" command, and after a real
`run`, print the receipt + a verify link. Right now the most compelling property
of the system is invisible at the surface a developer touches first.

---

## The highest-leverage fixes (do these first)

1. **Fix the binary-name collision (finding 1).** One line of impact per print
   site; unblocks command #1 of every journey. Derive prompts from the real bin
   name so it can't regress.
2. **Make `deploy` honest *or* live (finding 2).** Either serve the published
   content locally on `--serve`, or stop printing a dead live URL. This is the
   keystone DX; it must either work or say it doesn't.
3. **Make `run --source` do what it says, or say what it does (finding 3).**
4. **Put the CLI into the onboarding and make DreggNet-alone usable (finding 4).**
5. **Surface the real-vs-local state in runtime output (finding 8)** — propagate
   the codebase's excellent honesty from comments into what `ls`/`deploy`/`run`
   print.

None of these touch the circuit, the metatheory, or the security model. They are
last-mile DX: naming, honest output, discoverability, and one real local serving
round-trip. Close them and a stranger can actually use the headline flows.

---

*Dated 2026-06-30. Grounded against HEAD; verify a specific file:line before
relying on it.*
