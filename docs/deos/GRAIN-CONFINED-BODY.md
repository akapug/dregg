# The confined-body grain: an OS-jailed agent behind the grain seam

A grain is a hosted agent whose mind is a committed, forkable cell funded by its
own lease (`grain-fork`, `agent-platform`). Its mind is driven by an
[`AgentBrain`](../../dregg-agent/src/agent.rs) — the seam that yields the next
`AgentAction`, observes the braid's verdict, and repeats. Today every brain runs
*in-process*: `PlannedBrain` (scripted), the BYO-key LLM brain, the model-over-
portal brain. The cap system gates the tools an action calls *through* the
toolkit, and the lease meters + receipts every admitted turn.

In-process is right for a brain that only ever proposes actions through the seam.
It is **not** enough for an untrusted *body* — a coding-agent subprocess, a BYO
agent binary — which can ignore the cap system entirely and make raw syscalls
(read the operator's keys, open a socket, exec a shell). For that case the grain
needs **ambient OS confinement**: the body runs in a jail that denies everything
but one channel, and its every tool-call arrives back through the grain's
cap-gated seam.

## What is

**`ConfinedBrain`** (crate `grain-jail`) is an `AgentBrain` whose decisions come
from a jailed subprocess instead of in-process code. It bridges two shapes that
already bottom out at the same place:

- The jailed body proposes tool-calls over a minimal line protocol.
- `ConfinedBrain::next_action` reads the next proposal and translates it into an
  `AgentAction` for the grain's drive loop.
- The drive loop cap-gates + meters + receipts the action (unchanged), then hands
  the verdict to `ConfinedBrain::observe`.
- `observe` serializes that `ActionObservation` back to the jailed body, which
  reacts and proposes its next call.

```text
  jailed body (subprocess, OS-sandboxed)        grain drive loop (unchanged)
    │  propose {tool, args}      ─────────▶  next_action ─▶ AgentAction
    │                                          cap-gate · meter · receipt (R2 turn)
    │  ◀───────── observe {admitted, refusal, summary}  ◀── ActionObservation
    └─ react, propose next
```

Because `ConfinedBrain` *is* an `AgentBrain`, the grain's lease, vat lifecycle,
prepaid meter, checkpoint/fork/rewind of the mind-cell, and the R0→R2 attestation
ladder all apply to a confined body **with no change to the drive path**. The
body is jailed; its authority is exactly the grain's caps; its whole session is a
re-witnessable chain of committed turns.

## The jail

The confinement is the firmament process-PD substrate
(`dregg-firmament`, features `process-pd` / `process-pd-sandbox`), the same
primitive the confined-agent bridge uses: `fork()` → close every fd but one
endpoint → self-apply the host OS sandbox (Linux seccomp + landlock; macOS
Seatbelt) before the body runs. `process-pd` is `libc`-only and cheap;
`process-pd-sandbox` adds the default-deny confinement. The body's sole channel
is the one endpoint fd, over which the line protocol runs. The confinement teeth
(`IPC_WORKS · OPEN_DENIED · NET_DENIED · ONLY_ENDPOINT_FD`) are the same ones the
firmament probe asserts.

`grain-jail` depends only on `dregg-agent` (the brain seam) and `dregg-firmament`
(the jail) — never the heavy verified-executor sdk — so it links into the main
workspace cleanly. The `agent-host` bwrap `JailSpec` is a second, Linux-only jail
backend behind the same body-spawn trait.

## The line protocol

A minimal newline-delimited JSON protocol over the endpoint — deliberately
smaller than ACP, and mappable onto it later:

- body → host: `{"propose": {"tool": "<service>", "amount_cents"?: N, ...}}` or
  `{"done": {...}}`.
- host → body: `{"verdict": {"admitted": bool, "refusal"?: "...",
  "tool_ok"?: bool, "summary"?: "..."}}`.

`tool` maps to the grain's cap vocabulary (`invoke:<service>`, the `Spend` rail
for priced calls, `cell-read`/`cell-write`, …); an unmappable proposal is refused
in-band, exactly as an over-budget action is.

## What runs today

- **The seam + protocol** — `ConfinedBrain` + the line protocol; `map_proposal`
  translates a proposal into the grain's `AgentAction` vocabulary and refuses the
  malformed in-band. (`grain-jail/src/{lib,protocol}.rs`.)
- **The real jail** — `spawn_confined_body` (`real-jail` feature,
  `grain-jail/src/jail.rs`) forks the body into a firmament process-PD confined
  to Endpoint-only (macOS Seatbelt / Linux seccomp+Landlock) and drives it over
  the surface socketpair. A jailed body cannot open a host file; the tooth is
  asserted in `jail::tests`.
- **A real grain, end-to-end** — `grain-jail/tests/grain_end_to_end.rs`:
  `agent-platform` rents a grain, drives it with a `ConfinedBrain` (in-process
  AND, under `real-jail`, a genuinely OS-jailed body), meters + mints each turn,
  and the renter verifies (R2) that every turn is a committed kernel turn; a
  proposal for an ungranted cell is cap-refused; a forged manifest is refused.
- **The granted egress door** — `spawn_confined_body_with_egress` (`real-jail`)
  opens EXACTLY one outbound `host:port` for the jailed body (firmament
  `spawn_pd_confined_with_surface_and_egress`, folding `Confinement::with_net_out`
  into the endpoint-only jail); every other remote stays denied. The deny is
  asserted non-vacuously (`jail::tests`): two live loopback listeners, one
  granted, and the jailed body reaches the granted one AND is denied the
  ungranted one (EPERM, not connection-refused, since both are listening).
- **The model-driven mechanic, end-to-end** — `grain_end_to_end.rs`
  (`a_jailed_body_driven_by_a_model_over_its_egress_door_runs_the_grain_r2`): a
  jailed body reads instructions from a "model" over its ONE granted door, relays
  them as proposals to a real grain (cap-gated + metered + minted + R2), and
  reaches nothing but the model. This is the full "rent a coding agent" loop —
  the only mock is the model itself.
- **Hostile-body robustness** — a jailed body cannot wedge (crash → clean;
  hang → read-timeout + SIGKILL-reap), fool (garbage → fail-closed), exceed (caps
  refused), or OOM (per-message length cap) the host.
- **A forkable confined session** — `grain_fork::confined::ConfinedSession`
  bundles a confined session's full state (committed mind + prepaid budget +
  caps + egress confinement + receipt chain); `fork_two` takes one checkpoint
  and yields two sovereign sessions, with all four conservation/attenuation
  teeth tested (egress doors a subset of the parent's, caps attenuated,
  budgets summing to no more than the parent's, isolated per-fork receipt
  chains rooted at the shared fork point). Spec:
  `docs/deos/FORKABLE-CONFINED-SESSION.md`.
- **A runnable demo** — `cargo run -p grain-jail --example rent_a_confined_agent`
  (add `--features real-jail` to OS-jail the body).

## Frontier

- **A REAL LLM body.** The mock model above is the last mock. A real body is a
  confined in-jail harness that POSTs to an OpenAI-compat provider over the
  granted door (`dregg_agent::brain::{OpenAICompatBrain, LiveOpenAICompatCaller}`,
  the `live-brain` reqwest path). The real work is running an HTTP client INSIDE
  the jail without a post-fork tokio runtime (the fork is `exec`-less) — a
  blocking `reqwest`/raw-TLS client on the granted socket, or a host-side proxy
  the jail reaches over loopback (the `localhost:PORT` grant is exactly this
  pattern). The live Nous portal is broken in-env, so a mock/recorded provider
  stays the CI path.
- **Productization.** `agent-platform` gaining a first-class jailed-grain drive
  (rent → jailed body → drive) so the confined agent is a rentable product, not
  only a test path. (`agent-platform` is edited by another lane — coordinate.)
- **Drive a forked session through `agent-platform::Tenant`.** The unifying
  type exists (`ConfinedSession`, above); the remaining seam is the adapter
  that lets a `Tenant`'s brain-driven rent/session state ride a
  `ConfinedSession` — the forkable/rewindable confined coding session
  end-to-end, drive loop included.
- **R3.** The whole-session STARK fold (`grain_verify::WHOLE_HISTORY_GAP`) stays
  the grain's verifiability frontier; R2 is today's ceiling.

## Boundaries (what this is not)

- Not a change to the kernel, effect vocabulary, commitment, or the
  grain-turn / grain-verify soundness surface — it is a new brain over the
  existing seam.
- Cross-platform sandbox coverage follows firmament: the Linux
  seccomp+landlock path is validated on a Linux builder; macOS Seatbelt locally.
  The plain `process-pd` (fork + fd-close, no OS sandbox) runs anywhere Unix and
  is the fallback body-spawn.
- R2 is the verifiability ceiling; the whole-history STARK fold (R3) stays the
  named grain gap.
