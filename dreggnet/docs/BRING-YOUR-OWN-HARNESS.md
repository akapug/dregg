# Bring-Your-Own-Harness — the Verifiable Agent Cloud for subscription users

## The strategic insight

Most people's *best* LLM access is **harness-tied**, not a portable API key.
Their subscription lives inside a coding-agent CLI — `kimi` / kimi-code, Claude
Code, Codex, Cursor, aider — or behind an "alternative access route" (an OAuth
subscription token, a harness-proxied endpoint). The raw, portable
`sk-…` API key is the *minority* case.

DreggNet's agent brain ([`AgentBrain`](../exec/src/agent.rs)) until now ate
either a fixed plan ([`PlannedBrain`]) or a **BYO raw API key**
([`KimiBrain`](../exec/src/kimi.rs) — `~/.kimikey`, the OpenAI-compatible POST).
If the only door is an API key, **we exclude most subscription users.**

The elegant fit — and it is *peak dregg*: **run the user's already-installed,
already-authed harness AS the confined brain.** The harness brings the smarts +
the subscription auth; **dregg brings the bound + the proof.** We confine a
powerful agent we don't control, meter it, and prove what it did. The harness is
*untrusted*; the cap-gate + budget + receipt is what makes running someone's
arbitrary harness safe.

```text
  the user's harness (kimi / claude / codex / aider) — brings smarts + subscription auth
        │  emits tool-calls (proposals)
        ▼
  ┌─────────────── the dregg braid (the only authority) ───────────────┐
  │  cap-gate  ·  budget draw  ·  receipt seal   (the harness can't escape) │
  └────────────────────────────────────────────────────────────────────┘
        │  verdict (allow+receipt / refuse+reason) — fed back
        ▼
  the harness adapts within confinement → next tool-call …
```

The harness **proposes**; the dregg braid **disposes**. No tool-call the harness
emits — in-bundle, out-of-bundle, a runaway loop, a forged result — can exceed
the budget or the cap bundle. The whole run re-witnesses with
[`verify_agent_run`] without trusting the host *or the harness*.

## The access-route landscape (how each plugs into `AgentBrain`)

### (A) The harness-as-subprocess brain — THE UNIVERSAL ROUTE

Run the installed agent CLI (`kimi`, `claude`, `codex`, `aider`, …) as a
**subprocess**. The harness reasons and emits **tool-calls**; dregg
**intercepts** each one and routes it through the cap-gate + budget + receipt
rail. The harness's *own* subscription auth is what reaches the model provider —
**dregg never sees the LLM credential at all.** Dregg confines, meters, proves.

* **Plugs into `AgentBrain`:** a `HarnessBrain` is an `AgentBrain`.
  `next_action()` reads the harness's next emitted tool-call and maps it to an
  [`AgentAction`] (`invoke` / `cell_read` / `cell_write`); `observe()` feeds the
  gate's verdict back to the harness so it adapts. The existing `AgentCloud::run`
  loop is **unchanged** — same braid as the mock and the Kimi brains.
* **The auth story — the cleanest of the three:** the harness holds its own
  subscription credential *inside the subprocess* and uses it to call its
  provider directly. **The credential never crosses the dregg boundary.** The
  only things that cross are tool-call JSON (proposals, outbound) and verdict
  JSON (responses, inbound). There is no key for dregg to hold, redact, or leak —
  cf. the BYO-key route (B), where dregg *does* hold the key and must confine it.
* **ToS / legitimacy:** **clean.** The harness IS the provider's official client,
  invoked exactly as the provider intends (the user runs their own `claude` /
  `codex` / `kimi`). Dregg does not impersonate a client, forge headers, or
  proxy a subscription token — it wraps the official tool's *tool-call surface*.
  This is precisely why route (A) sidesteps the ToS nuance that dogs route (C).
* **The confinement (the load-bearing part):** the harness is **untrusted**
  arbitrary code. Its safety comes entirely from the dregg braid around it:
  - an out-of-bundle tool the harness emits is **refused before it runs**
    (cap-gate), leaving no receipt;
  - a runaway harness (emit the same tool forever) is **budget-bounded in-band**;
  - every admitted action is **receipted** — a forged result breaks the
    signature on re-witness;
  - a `step_cap` bounds the *number* of harness turns (the budget bounds spend;
    this bounds turns) so a degenerate harness can't spin forever.

#### The interception — what's the cleanest universal shim?

The harness must surface its intended tool-calls to dregg. Four mechanisms, in
order of cleanliness:

1. **An ndjson tool-call line protocol over stdio (what this prototype models).**
   The harness (or a thin adapter) emits one JSON object per line on stdout —
   `{"tool":"invoke","service":"run_tests"}` — and reads the verdict back as one
   JSON line on stdin — `{"admitted":true,"receipted":true}` /
   `{"admitted":false,"refusal":"outside the cap bundle: invoke:exfiltrate"}`.
   This is the **lowest-common-denominator** shim: any harness that can shell out
   to a command, or be wrapped by one, can speak it. It is exactly the shape the
   confined-Hermes ACP client already uses (a `request_permission` round-trip),
   reduced to its essence.
2. **An MCP server dregg exposes; the harness's tools ARE dregg tools.** Most
   modern harnesses (Claude Code, Codex, Cursor, kimi-code) speak the **Model
   Context Protocol**. Dregg runs an MCP server whose `tools/call` handler is the
   cap-gate + budget + receipt rail. The harness, configured to use *only*
   dregg's MCP server, can reach nothing else — every tool it calls is a
   receipted dregg turn. This is the cleanest *production* route for MCP-native
   harnesses; the ndjson protocol (1) is its transport-agnostic generalization.
3. **ACP `session/request_permission` (the confined-Hermes route).** A harness
   that speaks the Agent Client Protocol (Hermes/Zed) asks the *client* for
   permission on each tool-call. Dregg is the ACP client: it answers each
   permission request by running the tool-call through the gateway and returns
   ALLOW+receipt / REJECT+reason. Already built for Hermes in `deos-hermes`.
4. **A tool-shim binary the harness calls.** Configure the harness so its tools
   are thin shims that re-emit to dregg over (1). Works for harnesses with no
   MCP/ACP surface but a configurable tool/command set (aider's `/run`, custom
   tool configs).

All four reduce to the same seam: **the harness names a tool-call; dregg decides
allow+receipt / refuse+reason; the harness adapts.** The prototype models (1)
because it is the universal substrate the others specialize.

### (B) OpenAI-compatible local endpoint — the `--llm-base` brain

Many harnesses and tools expose (or can be wrapped to expose) a local
OpenAI-compatible `/v1/chat/completions` endpoint (LM Studio, ollama, llama.cpp,
vLLM, a harness's own proxy). That is the **same shape `KimiBrain` already
drives** — point the brain's endpoint at the local base URL instead of Moonshot.
The sibling `--llm-base` lane builds this out.

* **Plugs into `AgentBrain`:** it *is* `KimiBrain` (the OpenAI-compatible
  brain) with a different `endpoint` (and often an empty/throwaway key).
* **Auth:** whatever the local endpoint wants (often none); if the endpoint
  fronts a subscription, the key confinement of route (B') applies.
* **ToS:** clean for genuinely local models; if the "local endpoint" is a
  re-exported subscription, see (C).
* **Overlap:** this route and route (A) overlap when a harness exposes BOTH an
  OpenAI endpoint *and* a tool-call surface — prefer (A)'s tool-call
  interception when you want dregg to confine the *tools*, not just meter tokens.

### (C) OAuth / subscription tokens — honest about the ToS

Claude Max, ChatGPT Plus, and similar expose the subscription through an **OAuth
flow** the official client performs. It is *technically* possible to extract the
resulting bearer token and replay it against the provider's endpoint from a
non-official client.

**We do not build that bridge, and here is the honest reason:** several
providers' Terms of Service restrict subscription access to their *official*
clients and prohibit programmatic/non-official use of the consumer subscription.
A token-replay bridge would put dregg — and the user — in violation. We flag it
rather than ship it.

**Route (A) is the principled answer to the same need.** It reaches the exact
same subscription, but *through the official client* (the user's own harness),
used exactly as the provider intends. The subscription auth never leaves the
official tool; dregg only wraps the tool-call surface. So the user gets their
harness-tied subscription **and** the dregg bound + proof, with **no ToS
violation** — because we never act as the client, the harness does.

If a provider offers an *official* programmatic credential for a subscription
(some do), that is a clean BYO-key (route B) and needs no OAuth bridge.

## Route comparison

| route | who holds the LLM auth | what crosses the dregg boundary | ToS posture |
|-------|------------------------|---------------------------------|-------------|
| (A) harness subprocess | the harness (in its subprocess) | tool-call JSON ↔ verdict JSON | clean — official client |
| (B) OpenAI-compat / BYO key | dregg (redacted, confined) | the request body (key in header only) | clean for local / official keys |
| (C) OAuth sub token | — (we don't build it) | — | **restricted — not built** |

In all three the **confinement is identical**: cap-gate + budget + receipt. The
routes differ only in *where the model auth lives* and *what crosses the
boundary*. Route (A) is the universal one because it asks nothing of the
provider's auth model — the user already authed their harness.

## The prototype (route A)

[`exec/src/harness.rs`](../exec/src/harness.rs) ships `HarnessBrain` — an
`AgentBrain` that drives a harness subprocess over the ndjson tool-call protocol.

* `HarnessTransport` is the subprocess seam (mirrors `KimiCaller`):
  - `MockHarness` — replays scripted tool-call JSON lines (the **fake "harness"
    subprocess** for the green tests) and **records every verdict delivered back**
    (so a test asserts the harness saw the refusal — the confinement feedback).
    A `repeating` variant models a runaway harness.
  - `SubprocessHarness` — spawns a configured `Command`, reads ndjson tool-calls
    from its stdout, writes verdict lines to its stdin. Std-only; this is where a
    real `kimi` / `claude` / `codex` adapter wires in.
* `HarnessBrain::next_action` reads the harness's next tool-call and maps it to
  an `AgentAction`; `finish`, EOF, or an unparseable line ends the turn
  fail-closed. A `step_cap` bounds the harness turns.
* `HarnessBrain::observe` delivers the gate's verdict back to the harness.

**Proven by the tests (all std-only, green):**
- a mock harness drives a real cap-bounded, receipted agent run that
  re-witnesses;
- an **out-of-bundle** tool the harness emits is **refused** (and the harness is
  told, in-band, via the recorded verdict) — confinement holds over an untrusted
  harness;
- a **runaway** harness is **budget-bounded**;
- a harness-internal secret (modeled in the mock) **never leaks** into the
  receipts / report — nothing but tool-calls crosses the boundary;
- a forged verdict in a harness run breaks the receipt signature.

**The killer property:** even a *fully arbitrary* harness — code dregg did not
write and cannot inspect — is contained, metered, and proven. That is the answer
to "let people use their harness-tied subscriptions."

## Next step (reviewed-go): the real-harness wiring

The prototype proves the **shim + the confinement** over a *mock* harness. The
remaining work is the per-harness subprocess adapter, each a `SubprocessHarness`
configuration + a tiny translation of the harness's native tool surface into the
ndjson protocol (or a direct MCP/ACP binding per the table above):

* **kimi / kimi-code** — spawn `kimi` in a non-interactive/agent mode; bridge its
  tool-call emission (MCP or its tool config) to the ndjson protocol.
* **Claude Code** — MCP-native (route A.2): dregg runs an MCP server; configure
  Claude Code to use *only* it. Each `tools/call` is a receipted dregg turn.
* **Codex** — MCP/tool-config, same shape as Claude Code.
* **aider** — tool-shim (route A.4) over its `/run` + config surface.
* **Hermes** — already wired via ACP in `deos-hermes` (route A.3).

Each adapter is a confinement-preserving plug into the *same* `HarnessBrain`
seam; none touches the cap-gate / budget / receipt rail, which is what holds the
guarantee. The model-provider auth stays inside the harness throughout.
