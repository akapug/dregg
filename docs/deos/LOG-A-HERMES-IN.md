# Log a Hermes in — watch a live brain drive the cockpit

A live Claude (over the `hermes-acp` ACP subprocess) is given a short task, **decides
the JavaScript itself**, and that JS runs `run_js` against the cockpit's **live
`World`**: a real crawl of the live cells plus real receipted verified turns landing
on the live ledger — each fire bounded by the agent's `held` authority (the cap
tooth; an over-reach is refused in-band). The cockpit inspector reflects the
committed turns.

This is the dregg confinement story made concrete: the brain is **empowered** (it
writes arbitrary JS), **accountable** (every `run_js` is a metered, receipted gateway
turn), and **bounded** (every affordance fire is cap-gated; the World's own executor
is the second gate).

## What you need

- The release binary (built once):
  ```
  cd starbridge-v2
  cargo build --release --features native-full,agent-js --bin starbridge-v2
  ```
  Binary: `starbridge-v2/target/release/starbridge-v2`.

- The live-brain bake binary (pulls the `hermes-acp` ACP loop + the run_js→live-World
  wiring; a heavier build — its own `live-brain` feature):
  ```
  cd starbridge-v2
  cargo build --release --features native-full,live-brain --bin starbridge-v2
  ```

- `hermes-acp` on PATH (or set `HERMES_ACP_BIN`). Confirm it is usable:
  ```
  hermes-acp --check          # must print "Hermes ACP check OK"
  ```
  It needs its venv's `agent-client-protocol` package. (`brew`/`uvx hermes-agent[acp]`.)

## Run it — the live brain on the live cockpit

```
cd starbridge-v2
HERMES_INFERENCE_PROVIDER=copilot \
HERMES_ACP_MODEL=copilot:claude-sonnet-4.5 \
HERMES_MAX_ITERATIONS=3 \
  target/release/starbridge-v2 --render-live-brain /tmp/live-brain
```

- `HERMES_INFERENCE_PROVIDER=copilot` + `HERMES_ACP_MODEL=copilot:claude-sonnet-4.5`
  drive a real Claude (Sonnet) on the box's **GitHub Copilot** subscription (no
  Anthropic credits required).
- `HERMES_MAX_ITERATIONS=3` **hard-caps** the agent loop to bound Copilot spend.

### What you'll see (a real run, observed)

1. **`/tmp/live-brain.before.png`** — the cockpit inspector over the live World
   before the brain runs (the agent cell's counter at its starting value, 0).
2. The brain handshakes (`initialize` → `session/new` → `session/set_model` →
   `session/prompt`), is given the task ("inspect the ledger, then bump your counter
   by 5"), and **decides the JS itself**. A real observed answer (Sonnet 4.5 on
   Copilot, 1 API call):
   ```
   ── the brain's chosen JS (run_js on the LIVE World) ──
   var cellCount = deos.world.cells().length;
   var app = deos.applet({ affordances: ["bump", "escalate"] });
   app.fire("bump", 5);
   ──
      run_js tool-call admitted = true; result = Some(5); fires committed = 1
      (real verified turns); receipts = [0d03f6ee9b81]
   ```
3. **`/tmp/live-brain.after.png`** — the inspector over the **same** World after; the
   committed turn is on the glass (provenance/blocklog feed shows the new receipt).
   The closing line reports the real ledger movement:
   `LIVE LEDGER: height 5→6, receipts 5→6, agent slot-0 0→5`.

Approx spend: ~1 Copilot API call (in≈15k tokens, ~97% cached; out≈50 tokens) —
negligible, well under the 3-iteration cap.

If the env can't reach a provider (no `hermes-acp`, or no Copilot auth), the bake
**skips gracefully** (exit 0): it still bakes the BEFORE shot and prints exactly which
step is missing. The `run_js`→live-World wiring is real either way — only the live
brain depends on the subprocess + provider.

### How the brain's JS reaches our run_js (the seam, honestly)

Hermes's own tool registry (`terminal`, `write_file`, …) does **not** include a
`run_js` tool, and an MCP-registered tool's arguments do **not** round-trip through
the ACP permission seam (only Hermes's dangerous-command approvals carry a payload we
can read — a bare command string). So the brain cannot today *call* a `run_js` tool
whose args we intercept. What IS real:

- the brain **decides** the deos-js program (its actual model output), and
- we run that **exact** script through `RunJsTool::run_attached_on` on the live World
  — a real cap-gated, receipted verified turn on the live ledger.

The brain emits its chosen JS as its answer (a fenced ```js block); `--render-live-brain`
extracts and runs it. This is faithful (real model, real chosen JS, real receipts), but
the model is reasoning in Hermes's OWN unconfined process, not inside dregg's sandbox.

**The remaining step for a DEEP integration** (so the model's tools — including shells —
are physically redirected through our container/cap sandbox): expose `run_js` (and a
confined `terminal`) as a real **stdio MCP server** Hermes registers via `session/new`'s
`mcpServers`, bridged over a socket back to the cockpit's live `World`. Then the brain
*calls* `run_js` as a first-class tool, Hermes routes the call to our MCP server, and the
server executes on the live ledger — every tool the model reaches for lands inside dregg
confinement. See "Depth of integration" below.

## Depth of integration — what's confined today vs. the target

There are two confinement faces (see `deos-hermes/src/{bridge,confined}.rs`):

- **Authority face** (`HermesGateway`): every tool-call deos *sees over ACP* becomes a
  cap-gated, metered, receipted dregg turn. Today this fires on Hermes's
  dangerous-command **permission** requests (the `rm -rf` seam) — proven live
  (`live-refuse`: a rate-0 `terminal` grant refuses the model's command in-band).
- **Ambient face** (`confined.rs`): an agent body runs in an OS-sandboxed PD
  (Seatbelt/seccomp+landlock), reachable only over a firmament Endpoint — file/network/
  exec denied. But the **real `hermes-acp` subprocess cannot be that body** (the sandbox
  denies `execve`, which is the point), so the confined path runs a Rust stand-in peer,
  not the live brain.

So **right now the live brain and the OS-sandbox are disjoint**: you get the real brain
(running Hermes's own tools in Hermes's own process — shells execute there, NOT in our
sandbox), OR the sandbox (with a stand-in, not the real model). The deep target — the
real model whose every tool (shell included) is redirected through our cap/container
sandbox — is the **MCP-server bridge** above: deos advertises the ONLY tools Hermes may
use (a confined `run_js`, a confined `terminal` that execs inside a dregg PD), so the
model has no path to an unconfined shell. That is the next slice, named here, not built.

## The Anthropic-key path (one env swap)

When ember's Anthropic credits are restored, swap the provider — nothing else changes:

```
HERMES_INFERENCE_PROVIDER=anthropic \
HERMES_ACP_MODEL=anthropic:claude-sonnet-4-5 \
HERMES_MAX_ITERATIONS=3 \
ANTHROPIC_API_KEY=...   # ember's key; never commit it \
  target/release/starbridge-v2 --render-live-brain /tmp/live-brain
```

## The scripted live-cockpit drive (no brain, always green)

To see the `run_js`→live-cockpit machinery without a provider — a SCRIPTED `run_js`
on the live World (crawl 4 real cells, fire a real turn 5→6, an over-reach refused):

```
cd starbridge-v2
cargo build --release --features native-full,agent-js --bin starbridge-v2
target/release/starbridge-v2 --render-agent-attach /tmp/agent-attach
```

Produces `/tmp/agent-attach.png` (the inspector showing the cell the JS modified) and
prints the crawl/fire/refuse witness. Add `--fork` to drive a `world.fork()` (the safe
sandbox; the live image untouched).

## How it's wired (the seam)

- `starbridge-v2/src/agent_attach.rs` — `WorldSinkAdapter::live(...)` / `fork_of(...)`:
  a `deos_js::WorldSink` over the cockpit's `Rc<RefCell<World>>`. A fire goes through
  `World::commit_turn` (the real verified executor) and lands on the live ledger +
  provenance feed.
- `deos-hermes/src/run_js.rs` — `RunJsTool::run_attached_on(...)`: runs a JS script on
  a provided live `WorldSink` under the agent's `held` (the accountability turn + the
  cap-gated fires). This is what the bake calls with the brain's chosen script.
- `deos-hermes/src/live_js.rs` — `LiveJsHands` + `AcpClient::with_run_js_hook(...)`
  (`deos-hermes/src/acp_client.rs`): the forward-looking seam for when Hermes CAN call
  a `run_js` tool (the MCP-server bridge). A `run_js` permission request would be
  dispatched here, the model's `rawInput.script` executed on the live World, and the
  receipts recorded (`AcpClient::js_runs()`). Wired + ready; the bake uses the
  direct path above because Hermes does not yet expose `run_js` (see the seam note).
- `starbridge-v2/src/main.rs` — `--render-live-brain`: builds the live cockpit World,
  bakes before/after, drives the real `hermes-acp` brain, and runs its chosen JS.
