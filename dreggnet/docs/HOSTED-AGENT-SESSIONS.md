# Hosted Agent Sessions + SSH Attach

> **The distribution model.** Instead of a user installing the runtime, **we host
> a cap-bounded, budget-bounded, receipted Hermes agent on DreggNet, and they
> attach over SSH** (the portal is a sibling lane). The pitch, in one line:
> *"ssh into your hosted verifiable Hermes agent, give it a goal, watch it run on
> our cloud, verify everything."*

This is a new product layer on top of the open-source agent runtime
(`breadstuffs/dregg-agent`). It does **not** invent a new agent mechanism — it
takes the existing confined run loop and makes it a *persistent, attachable,
multi-user-isolated session* you rent rather than install.

---

## 1. What a hosted agent session IS

A **hosted agent session** is a `dregg-agent` (a Hermes/Nemotron brain) running as
a long-lived cell/session on DreggNet, scoped to:

- a **user's `dga1_` cap-account** (their identity + the root the session's
  authority is minted under),
- a **budget** (a USD-cents spend ceiling the whole session draws down from), and
- a **cap bundle** (which tools / vendors / hosts the session may use:
  `fs,http:api.github.com,pay:openai,…` — the lexically-confined tools; `shell` is
  hosted-disabled until per-tenant OS isolation is present, see
  `docs/HOSTED-ISOLATION.md`).

The user **attaches** (SSH now, portal next) and **drives** it: they type a goal,
the brain runs a real reason → act → observe loop *server-side*, and:

1. every action is **cap-gated** (a tool outside the bundle is refused in-band),
2. every action is **budget-drawn** (an over-ceiling action is refused before any
   effect — no money moves), and
3. every admitted action is **receipted** (a prev-hash-chained ed25519 record).

At any point the user can `verify` the whole session: a host-untrusted re-witness
of the entire receipt chain + the spend bound. **They run nothing locally** — the
brain, the tools, and the proof all live on the cloud; the user supplies goals and
walks away with a proof of everything the agent did and a hard bound on everything
it *could* have done.

```
   user (ssh / portal)
        │  goal: "clone X, run its tests, pay the CI vendor 50c"
        ▼
   ┌──────────────────────────────────────────────────────────────┐
   │  hosted session  (account dga1_alice · budget 500¢ · caps …)  │
   │   brain (Hermes) ──▶ tool call ──▶ [cap-gate · meter · receipt]│
   │        ▲                                   │                   │
   │        └────────── observe (verdict) ◀─────┘                   │
   │   persistent: budget draws down · receipt chain accumulates    │
   └──────────────────────────────────────────────────────────────┘
        │  transcript + receipts + running budget   ▲  verify (host-untrusted)
        ▼                                           │
   user sees it run, live                      user re-witnesses everything
```

---

## 2. The session lifecycle

The session core is `dregg_agent::session::Session` (the substrate type; std-only,
no HTTP/SSH). One per attached user.

| phase | what happens | where |
|-------|--------------|-------|
| **create** | `Session::open(account, spec)` mints a fresh **root + meter** for this session and deploys the agent (the cap bundle as a `dga1_` credential + the budget cell). | `dregg-agent` session core |
| **attach** | the user connects (SSH forced-command / portal) and is dropped into the session REPL. | this crate + `dregg-agent attach` |
| **drive** | per typed goal: `Session::run_goal(goal, brain, toolkit)` runs the loop, **threading the persistent state** — the budget keeps drawing down, the receipt chain keeps linking, the cell heap carries forward. Returns the delta (this goal's steps + the running budget). | `dregg-agent` session core |
| **detach** | the user disconnects; the session artifact (the cumulative receipt chain) persists and can still be verified. | — |
| **verify** | `Session::verify()` re-witnesses the **whole** session as one chain (signed + unbroken + tamper-evident; consumed ≤ ceiling; tip agrees with the total). | `dregg-agent` session core |

The key invariant vs the one-shot `run`: **persistence**. A one-shot run takes one
goal and emits one chain. A session takes many goals over a conversation and
emits **one accumulating chain** — goal 2's first receipt links to goal 1's last,
the budget is one ceiling for the whole session (no per-goal reset a runaway could
exploit), and the seq stays monotonic so the meter draws are exactly-once across
the whole session.

---

## 3. Multi-user isolation (the firmament framing)

Each session owns its **own** `AgentCloud` — its own root authority and its own
meter cell. So isolation is not a policy the host enforces; it is the **shape of
the construction**:

- user A's `dga1_` bundle is minted under **root A** and *cannot verify* under
  root B — a cap leaked from one session is inert in another;
- the two budget cells are **separate** — A exhausting her ceiling does not touch
  B's headroom;
- the two receipt chains have **different signers** — neither can be spliced into
  the other.

This is the **firmament** idea — *one cap across distance*. The SSH attach is the
cap crossing the wire: the user drives a confined cell that runs server-side. The
session *is* a cell you attach to; n=1 collapses the distributed bound to the
strong-local one (the single-machine principle).

The `dregg-agent` test `session::tests::two_sessions_are_isolated_by_construction`
proves the cryptographic isolation; the e2e test
`two_accounts_are_isolated_by_their_own_budget_and_identity` proves it through the
binary (each account bounded by its own budget + its own `agent:session:<acct>`
identity).

---

## 4. The SSH attach mechanism

The goal: `ssh <account>@agents.example.com` drops the connecting user into THEIR
hosted session — a **restricted shell** where they can only drive the agent, not
touch the host. The Hermes/Nemotron brain + the tools run server-side; the user
needs no local install.

### 4.1 The forced-command pattern

We do **not** give the user a host shell. We use the OpenSSH **forced-command**
(`authorized_keys` `command=`) so the SSH session *is* the agent REPL:

```
command="dregg-agent attach --account dga1_alice --budget 500 --caps fs,http:api.github.com",restrict,pty ssh-ed25519 AAAA… alice@laptop
```

> **HOSTED CONFINEMENT (the red-team CRITICAL fix).** The hosted forced command
> grants the **lexically-confined** tools only — NO raw `shell`. A hosted box also
> holds the operator's keys, and a raw `bash -c` can read them (`cat
> /home/op/.stripekey`) or exfiltrate them (`curl … -d @/abs/path`) past the
> in-process env-scrub. `agent-host` refuses a `shell` cap at enrol unless the host
> declares per-tenant OS isolation; `dregg-agent attach` refuses it at parse. To
> restore `shell` safely, deploy the per-tenant jail and pass `--os-isolation`
> (then the forced command carries the flag) — see `docs/HOSTED-ISOLATION.md`.

- `command="…"` — whatever the client asks to run is **ignored**; the connection
  always runs `dregg-agent attach` scoped to this account + budget + caps.
- `restrict` — disables agent/port/X11 forwarding and the other extras
  (fail-closed lock-down).
- `pty` — re-enables a terminal so the REPL is usable interactively.
- `dregg-agent attach` reads `SSH_ORIGINAL_COMMAND`, so `ssh acct@host "a goal"`
  runs that **one** goal non-interactively and exits (scripting), while a bare
  `ssh acct@host` drops into the interactive REPL.

The REPL: type a goal → it runs (transcript + receipts + running budget printed) →
type the next goal. `:status` `:caps` `:verify` `:history` `:help` `:quit` inspect
the session. `:verify` re-witnesses the whole session on demand.

### 4.2 The identity glue (this crate: `dreggnet-agent-host`)

`AgentHostRegistry` maps an **SSH public key** → an `AccountRecord`
(`account`, `budget_cents`, `caps`, `brain`) and emits the `authorized_keys`
content a real sshd consumes. The caps string is validated against the **real**
`dregg-agent` grant vocabulary at enrol time (a bad bundle is rejected here, not
at the next login). One forced-command line per enrolled key → every key lands in
its own confined session.

```sh
# enrol a user, then generate the authorized_keys the edge serves:
dreggnet-agent-hostctl --registry reg.json enroll \
    --account dga1_alice --budget 500 \
    --caps shell,fs,http:api.github.com \
    --key "ssh-ed25519 AAAA… alice@laptop"
dreggnet-agent-hostctl --registry reg.json authorized-keys > ~agent/.ssh/authorized_keys
```

### 4.3 Honest about the auth

We map an SSH key → a `dga1_` cap-account + a budget. The SSH key is the user's
**identity at the edge**; the `dga1_` account is the **authority** the session runs
under. A production deploy can resolve the mapping dynamically via OpenSSH's
`AuthorizedKeysCommand` (call into the registry per login) instead of a static
file — same forced-command output.

---

## 5. The portal — the sibling lane

The same `Session` core backs the **portal** attach (a browser drives the session
over HTTP/WS instead of SSH). The portal is a separate lane (not built here); it
reuses `Session::run_goal` / `Session::verify` byte-for-byte — only the transport
differs. The in-browser STARK-verification hero (the `example.com` portal) is the
"verify everything" half made visceral.

---

## 6. Real vs reviewed-go (honest)

**Real (built + tested, green):**

- the persistent session core (`dregg_agent::session::Session`): budget draws down
  across goals, the receipt chain accumulates, `verify` re-witnesses the whole
  session, two sessions isolated by construction;
- the interactive REPL (`dregg-agent session`) and the SSH forced-command target
  (`dregg-agent attach`, incl. the `SSH_ORIGINAL_COMMAND` one-shot path),
  std-only on the recorded brain, live with the keys;
- the identity/edge glue (`dreggnet-agent-host`): key→account→budget→caps mapping,
  caps validation, durable registry, `authorized_keys` forced-command generation,
  enrol/revoke/list/authorized-keys CLI;
- the e2e proof: a user "ssh"es in (simulated SSH → REPL drop over piped stdin) →
  types a goal → it runs bounded + proven → an out-of-bundle tool is refused → a
  second account is isolated → `verify` re-witnesses the session.

**Reviewed-go (the public hosting step):**

- the **live edge SSH endpoint** — a real `sshd` (or a custom SSH server) on
  `agents.example.com` whose `AuthorizedKeysFile` / `AuthorizedKeysCommand` is fed
  by `dreggnet-agent-host`, with the `dregg-agent` binary installed as the
  forced-command target. The forced-command, the per-user confinement, and the
  isolation are proven here; standing up the public box is the deploy.
- the **live brain keys** — the recorded transport proves the loop deterministically
  in CI; the live Hermes/Nemotron run goes live the moment the provider key is
  present on the host. **No key is ever committed.**

---

## 7. The demo

```sh
# (recorded brain — deterministic, no key needed)
# 1. drive a hosted session interactively: type goals, watch them run, verify.
printf 'clone and inspect a repo\nnow summarize it\n:verify\n:quit\n' \
  | dregg-agent session --account dga1_demo --budget 10 --caps shell \
      --replay resp.json --out session.json

# 2. the SSH attach, simulated: the forced-command drop-in, one goal via SSH_ORIGINAL_COMMAND
SSH_ORIGINAL_COMMAND="do a single thing" \
  dregg-agent attach --account dga1_alice --budget 5 --caps shell --replay resp.json

# 3. re-witness the whole session offline, trusting no host
dregg-agent verify session.json

# 4. enrol users + generate the authorized_keys the live edge serves
dreggnet-agent-hostctl --registry reg.json enroll \
    --account dga1_alice --budget 500 --caps shell,fs,http:api.github.com \
    --key "ssh-ed25519 AAAA… alice@laptop"
dreggnet-agent-hostctl --registry reg.json authorized-keys
```

With the keys present, drop `--replay` and the same commands run a **live** Hermes
agent on the cloud. That is the product: **ssh into your hosted verifiable Hermes
agent, give it a goal, watch it run, verify everything.**
