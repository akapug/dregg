# Teaching / Usability / Stranger-Usable Frontier

*A read-only scout of the register the soundness/liquid/house/deos waves haven't touched: can a
stranger USE dregg without ember in the loop? Source-verified at HEAD (2026-06-24). Every claim cites
`file:line` and a state (ALIVE / PARTIAL / MISSING). Paths are repo-root-relative (`…/breadstuffs/`)
unless prefixed `metatheory/`.*

The Refinement-Epoch mandate this serves: usability, teaching, the "lamesauce" predicate-caveat
LANGUAGE uplift, not-a-toy apps, the **Pug Handoff** bar — *works without ember in the loop*.

---

## Headline: the top 3 stranger-usability moves

The substrate is in far better onboarding shape than the "lamesauce" framing implies. A stranger can
run a real verified turn **in under two minutes, in-process, with zero network** — and that path WORKS
TODAY (verified below). The remaining gap is not *getting started*; it's *understanding a refusal* and
*authoring a policy by hand*. Ranked by delight-per-unit-work:

1. **Export the executor's refusal reason to the wire (the single biggest comprehension win).**
   The verified executor *knows* exactly why it rejected a turn (8 named, theorem-backed admission
   gates), but the FFI boundary returns a bare `Bool`/status — the reason is trapped behind the proof.
   A stranger whose turn is refused at admission gets silence, or a generic node error, with no "nonce
   replay: expected 5, got 3." The Rust `TurnError` layer is already exemplary (80+ contextful
   variants); the gap is *the verified gate → wire* hop. **Size: build (Lean `AdmissionReason` enum +
   FFI decode), ~1–2 days.** This is the thing most likely to turn "it just says no" into "oh, I see."

2. **Add a fluent builder + named constructors to the Rust `Pred`/caveat surface.** The caveat
   *algebra* is proven and minimal; the *low-level authoring surface* is raw enum-variant construction
   (`Pred::AllOf(vec![Pred::AnyOf(vec![Pred::AttrEq{...}])])`, `.into()` everywhere). The
   product-level `Grant::to(...).tools([...]).until(T)` builder is already lovely — the uplift is to
   bring that ergonomics down to `Pred` (`Pred::eq("tool","read").and(Pred::within(100,200))`). Zero
   semantic change, pure ergonomics. **Size: wire, ~200–300 LOC + tests/doc.**

3. **Promote `first-room` to the flagship "what is dregg FOR?" demo (README + run line).** It is the
   single most compelling app: an agent HOLDS a mandate, earns conserving escrow pay, and *five
   distinct cheats are each provably refused in-band with the receipt saying why*. It runs end-to-end
   against the real embedded executor and its 4 tests are green — but it has **no README** and no
   "run this" line, so a stranger never finds it. **Size: write (~100-line README + a `cargo test`/run
   pointer in QUICKSTART), hours.**

**The single thing most likely to make a stranger GET dregg — or give up:** refusal legibility (move
#1). dregg's entire thesis is *"every cheat is refused, with a witnessed reason."* When a stranger's
first failed turn returns an opaque `false` instead of that reason, the thesis silently fails to land
at the exact moment it should be most convincing. Conversely, `first-room` (move #3) *already renders
the refusal-why in-room* — it is the thesis made visible. Wiring the reason to the wire generalizes
that one demo's payoff to every turn a stranger ever submits.

---

## Verification correction (the discipline caught an inflation)

A first-pass scout reported the **`dregg-cli` and `dregg-node` fail to build** on a `[u8; 64]` serde
trait-bound error in `turn/src/encrypted.rs:142`, calling it the "single highest-value move."
**This is FALSE at HEAD.** Verified directly:

- `turn/src/encrypted.rs:144` — the `signature: [u8; 64]` field already carries
  `#[serde(with = "crate::action::serde_sig64")]`; there is no serde gap.
- `cargo check -p dregg-cli` → **Finished in 16.93s** (warnings only, no errors).
- `cargo run -p dregg-sdk --example hello_receipt_chain` → **runs to completion**, prints the agent
  cell id, the human-readable "What am I about to authorize?" block, the `TurnReceipt` JSON, and the
  receipt chain. No node, no network.

The scout had hit a cold/stale build state and read a struct without seeing the existing serde adapter.
Trust the build, not the first map. (The node build is *heavy* — Lean compile + FFI link, several
minutes — which is real friction, but it is build *latency*, not build *breakage*.)

---

## Area 1 — The stranger-onboarding path — **ALIVE** (stronger than expected)

**State: ALIVE.** A stranger has multiple working doors and a copy-paste quickstart.

- `README.md:40-135` — four "first five minutes" doors, each with copy-paste commands: (A) run a
  node + faucet a cell via `curl`, (B) `dregg demo` CLI lifecycle, (C) in-browser wasm playground,
  (D) the desktop cockpit. Honest framing ("there is no public server"). **ALIVE.**
- `QUICKSTART.md:1-302` — "dregg in 15 minutes," entirely local; every command's expected output is
  pasted. Node → signed turn → guided demo → governance ceremony → browser → receipt stream. **ALIVE.**
- `sdk/examples/hello_receipt_chain.rs` (79 lines) — **the best stranger entry point, VERIFIED
  RUNNING.** `cargo run -p dregg-sdk --example hello_receipt_chain` produces a real signed turn +
  receipt + receipt chain, fully in-process (embedded executor), **zero network**. Wired into
  `sdk/Cargo.toml` as an `[[example]]`. **ALIVE.**
- `sdk/examples/{polis_ceremony,polis_sealed_vote,agent_demo}.rs` — additional in-process examples
  (a 2-of-3 council lifecycle, etc.). **ALIVE.**
- `cli/src/main.rs` — the `dregg` CLI builds (verified), ~17 subcommands with help text (`id`, `cell`,
  `turn`, `name`, `polis`, `voting`, `bounty`, `demo`, …). `demo --passphrase` is the easiest guided
  lifecycle. **ALIVE** (needs a running node for the network commands).
- `README-LLMs.md` (314 lines) — a machine-facing onboarding door for agents specifically. **ALIVE.**

**Where a stranger actually gets stuck** (honest walls, in order):

1. **Build latency, not breakage.** The first `cargo build -p dregg-node` is a multi-minute Lean
   compile + FFI link with sparse feedback; a stranger may think it has hung. The SDK example builds
   far faster and needs no node — but the README's *door A* leads with the node. Mitigation is a doc
   note, not code.
2. **The node door requires two shells** (`… run … &` is non-obvious).
3. **Dead-server references.** The README/QUICKSTART correctly say "no public server," but stray
   mentions of a devnet (decommissioned 2026-06-22) elsewhere can send a stranger chasing a dark box.

**Highest-value move:** *reorder the front door* — lead README/QUICKSTART with
`cargo run -p dregg-sdk --example hello_receipt_chain` (fast, in-process, no node, no `&`, no curl)
as door #0, then escalate to the node. The verified-running example is the lowest-friction "real
verified turn" a stranger can hit. **Size: write, ~30 min** (re-sequence + one note about the node
build being slow-but-not-stuck).

---

## Area 2 — The predicate-caveat LANGUAGE — **PARTIAL** (proven; raw to author by hand)

**State: PARTIAL.** The algebra is proven and *more complete* than the "lamesauce" memory implies;
the gap is authoring ergonomics at the low level, plus a fork into three parallel algebras.

What is **ALIVE**:

- The Lean atom set is **large and the "missing" atoms already exist**
  (`metatheory/Dregg2/Exec/Program.lean`): `memberOf:81`, `prefixOf:88`, `inRangeTwoSided:92`,
  `deltaBounded:96`, `clearanceGe:298`, `affineLe:303`, `affineEq:306`, `reachable:313`,
  `affineDeltaLe:328` — each with admit-characterization + non-vacuity `#guard` teeth. (Source:
  `metatheory/docs/RESEARCH-predicate-language.md`, which corrects the stale "atoms to add" framing —
  D0–D4, D7 are DONE.) **ALIVE.**
- A uniform Boolean `Pred` algebra (`metatheory/Dregg2/Exec/PredAlgebra.lean:127`) with De Morgan,
  the lifts, typed identity leaves, and an executor adapter (`PredCaveat`/`predStateStepGuarded:556`).
  **ALIVE.**
- The Rust credential core mirrors it faithfully (`dregg-auth/src/credential/pred.rs:46-164`,
  `caveat.rs:24-128`), decidable + three-valued + fail-closed under `Not`. **ALIVE.**
- **The product-level builder is genuinely pleasant** (`dregg-auth/src/policy.rs:156-220`):
  `Grant::to("ci-bot").tools([...]).until(T)` → compiled to caveats. Solves ~70% of real cases without
  touching raw predicates. **ALIVE** — and the model the low level should imitate.

What is **PARTIAL / MISSING**:

- **Low-level `Pred` authoring is raw AST.** To say "tool ∈ {read, pr-create} AND clock ∈ [100,200]"
  a hand-author writes nested `Pred::AllOf(vec![Pred::AnyOf(vec![Pred::AttrEq{key:"tool".into(),
  value:"read".into()}, …]), Pred::Within{not_before:100, not_after:200}])` — verbose, no IDE
  completion, `.into()` noise (`dregg-auth/tests/credential_cycle.rs:14-98`). **PARTIAL.**
- **No fluent builder on `Pred`**, no convenience constructors (`Pred::before/after/eq/within`), no
  `.and/.or/.not` chain. **MISSING.**
- **No textual DSL / parser** for caveats (`"tool == read AND time < 200"`). **MISSING.**
- **`Caveat.local` is still an opaque `Ctx → Bool`** in Lean (`metatheory/Dregg2/Authority/
  Caveat.lean:38-40`) — a caveat cannot be inspected, serialized, refined, or circuit-emitted as a
  term; structural caveat *refinement* (one caveat provably narrows another by content) is therefore
  inexpressible. (D6, the one genuinely-open language item per RESEARCH-predicate-language.md.)
- **Three parallel record-predicate algebras** (`Pred` over `StateConstraint`, `RelPred` over
  `RelCaveat`, `Spec.Guard`) — an author picks a surface and gets a different atom set + evaluator.
  Convergence is the standing ergonomics tax.

**Highest-value move (authoring delight, no risk):** add a fluent builder + named constructors to the
Rust `Pred` (`dregg-auth/src/credential/pred.rs`): `Pred::eq/prefix/before/after/within` +
`.and/.or/.not`, mirroring the `Grant` builder's feel. Zero semantic change. **Size: wire, ~200–300
LOC + tests.** (The deeper Lean `Caveat.pred` reification (D6) and three-algebra convergence are
*medium, front-loaded small* per the research doc, and unlock content-level refinement — a real new
theorem — but are a follow-on, not the stranger-delight move.)

---

## Area 3 — Error / refusal legibility — **PARTIAL** (the comprehension keystone)

**State: PARTIAL — exemplary in Rust, opaque at the verified gate, vague at the caveat layer.** This
is the highest-leverage area for *understanding*, because dregg's whole pitch is "refused, with a
reason."

- **Lean executor — PARTIAL (reason trapped behind the proof).** Admission is 8 sequential checks
  returning a bare `Bool` (`metatheory/Dregg2/Exec/Admission.lean:21-46`: EmptyForest, AgentLive,
  Expiry, NonceMatch, FeeCoverage, NotFrozen, ChainHead, Budget). Each gate has a *named, fail-closed
  theorem* (`admissible_rejects_empty`, `admissible_rejects_replay`, …) — so the proof knows *exactly*
  why — but the value is just `false`. The richer `TurnStatus` enum
  (`metatheory/Dregg2/Exec/TurnAdmission.lean:60-70`: `rejected | prologueCommittedBodyFailed |
  bodyCommitted`) *is* exported (`runGatedForestTurnStatus`), distinguishing admission-reject from
  body-fail — but **no admission *reason* rides with it.** **PARTIAL.**
- **Rust node/SDK — ALIVE (exemplary).** `turn/src/error.rs` defines `TurnError` with 80+ contextful
  variants, each `impl Display` (e.g. `NonceReplay{expected,got}` → "nonce replay: expected 5, got 3";
  `PermissionDenied{cell,action,required}`; `InsufficientBalance{cell,required,available}`;
  `FacetViolation{…}`; `LeanShadowVeto`). The node's `SubmitTurnResponse` carries the `Display` string
  in its `error` field. **ALIVE — this is how it should work.**
- **Caveat-failure path — PARTIAL (vague).** Rust token caveats collapse to a generic
  `TokenError::Denied(String)` (`token/src/error.rs:14`); when a `ValidityWindow{not_before:100,
  not_after:200}` rejects a call at clock 250, there is no *structured* "clock 250 not within
  [100,200]" — the specificity exists in principle but is flattened. (Note: the `explain()` the caveat
  scout praised lives on the Lean/`dregg-auth` `Pred` variants, *not* on the Rust `token` caveat
  verifier — a missed wire.) **PARTIAL.**
- **Dry-run / preflight — MISSING.** There is a `preflight/src/main.rs` binary, but it is a 27-test
  *subsystem* smoke suite, not a per-turn "would THIS turn be refused, and why?" endpoint. A stranger's
  only way to learn why a turn fails is to submit it. **MISSING.**
- A bright spot pointing the way: `sdk/examples/hello_receipt_chain.rs` already prints a human-readable
  **"What am I about to authorize?"** block before signing (verified in output) — the *legibility for
  the success/authorize path already exists at the SDK layer*; the gap is the *refusal* path.

**Worst opaque failure a stranger hits:** an admission-rejected turn returns `rejected`/`false` with
no reason — the verified executor knows (nonce? expired? frozen? budget?) but doesn't say. Second-worst:
a denied caveat returns a generic `Denied(...)` without the bound it violated.

**Highest-value move (the headline):** add a Lean `AdmissionReason` inductive, project it from each of
the 8 `admissible` gates (each already has its theorem), thread it through the FFI/`TurnStatus` export,
and surface it in `SubmitTurnResponse.error`. Then a refused turn says *"rejected: nonce replay
(expected 5, got 3)"* instead of silence. **Size: build, ~200 Lean LOC + ~100 Rust LOC, ~1–2 days.**
Secondary: route per-caveat reasons (which caveat, which bound) into `TokenError` instead of
`Denied(String)`. **Size: wire, hours.**

---

## Area 4 — Not-a-toy apps — **ALIVE** (rich; under-surfaced)

**State: ALIVE.** `starbridge-apps/` holds ~20 real apps with working code + green tests — **zero
pure-stubs** found; the gap is *which one a stranger is pointed at*, not whether they exist.

Most compelling, by thesis-fit (each verified to have real `src/` + passing tests, not just READMEs):

- **`first-room/` — THE flagship candidate. ALIVE.** (`starbridge-apps/first-room/`, ~909 LOC, 4
  tests green: `the_honest_cycle_earns_and_is_paid`, `the_first_room_holds_end_to_end`,
  `the_room_renders_the_inhabitant_and_the_refusals`, `every_cheat_is_provably_refused`.) A *weld* of
  three proven apps: a colonist HOLDS a mandate (job DAG + clearance + spend budget), earns conserving
  escrow pay on completion, and **five cheats — skip a step, overspend, reach outside the compartment,
  use ungranted verbs, release without approval — are each provably refused in-band, with the receipt
  saying why** (`src/scenario.rs:58-94`). It *renders the refusal-why in-room*: the thesis made
  visible. Runs against the real `EmbeddedExecutor`. **Its one gap: no README, no "run me" pointer.**
- **`nameservice/` — ALIVE** (~1,979 LOC, ~45 tests, has a web surface): federation name registry,
  WriteOnce + Monotonic slot caveats, forms.
- **`sealed-auction/` — ALIVE** (~1,205 LOC, ~13 tests): commit-reveal sealed bids, Blake3, atomic
  settlement, *proven in Lean*.
- **`escrow-market/` / `compute-exchange/` — ALIVE**: value-conserving settlement
  (released + refunded == escrowed), over-budget-bid refusal, on the verified executor.
- **`bounty-board/`, `subscription/`, `privacy-voting/`, `gallery/`, `governed-namespace/`,
  `polis/`, `tussle/`, the mandate family — all ALIVE** (real src + green tests).
- **`identity/` — PARTIAL** (~1,564 LOC; the richest theorem story: selective disclosure +
  verifiable credentials + revocation + schema layering). Core lib tests pass; an earlier scout
  reported 5 integration tests failing on `IssuerNotInFederation`, but `tests/deos_seam.rs:460-477`
  claims that seam CLOSED via `register_deos` (which mounts AND seeds the issuer) — **so the failing
  path may be a stale/duplicate test harness, not a missing wire.** *Verify which test file is the
  live one before acting.*
- **`deos-matrix/` membrane chat — ALIVE**: real `matrix-rust-sdk 0.18`, E2E encryption, and the
  `MembraneEnvelope` keystone (a message carries a rehydratable cap-bounded world-fork). Runnable
  (`cargo run --features gui --bin deos-chat` / `--headless`).

**Highest-value move:** make `first-room` discoverable — a ~100-line README (mandate → escrow economy
→ the five cheats and which tooth refuses each) + a one-line `cargo test -p starbridge-first-room`
pointer in QUICKSTART/README as "what is dregg FOR?". **Size: write, hours.** Secondary: confirm the
`identity` integration-test state (read `deos_seam.rs` vs the failing file) — likely a stale-harness
cleanup, not new work.

---

## Area 5 — Teaching the model — **ALIVE** (good; could use one "GET it in 5 min" front page)

**State: ALIVE.** There is a genuine teaching layer; the gap is a single short *first-contact*
explainer that lands the through-line before the layer cake.

- `metatheory/docs/guides/` — four newcomer orientations: `authority.md`, `circuit.md`,
  `distributed.md`, `executor.md`. `authority.md:18-22` states the through-line cleanly: *"A capability
  is constructive knowledge: to hold one is to be able to exhibit a witness that verifies… authority is
  generative and attenuating… the token gates the executor's admission inline on the critical path."*
  **ALIVE.**
- `metatheory/README.md` — what dregg2 *is*: the five guarantees (Authority/Conservation/Integrity/
  Freshness/Unfoolability), the eight verbs, "the Lean kernel IS the executor." Excellent for a
  verification-literate reader. **ALIVE.**
- `metatheory/docs/NAVIGATION.md` — the where-is-X index (92 Rust crates, ~790 Lean modules), with a
  stale-link banner that honestly points at the harvested `rebuild/` stratum. **ALIVE.**
- `docs/ASSURANCE.md`, `.docs-history-noclaude/DREGG3.md`, `README-LLMs.md`, the `docs/deos/` corpus — deep teaching
  material. **ALIVE.**

**The gap:** the guides are excellent but pitched at the *verification-literate*; the README leads with
five guarantees and a layer cake. There is no single **"dregg in one screen for a working programmer
who has never heard of macaroons or ZK"** — the one-paragraph "a turn = exercising an attenuable
proof-carrying token over owned state, leaving a verifiable receipt; here is that exact sentence as 20
lines of runnable code (the hello example), and here is what each word means." The pieces all exist
(the through-line sentence in `authority.md`, the runnable example, the receipt) — they are just not
welded into one first-contact page.

**Highest-value move:** write `docs/guides/start-here.md` (or a README "in one screen" section) that
(a) states the one-sentence model, (b) shows the `hello_receipt_chain` output annotated word-by-word
against that sentence ("this is the *owned state*; this is the *attenuable token*; this is the
*verifiable receipt*"), (c) links the four guides + `first-room` as "now go deeper." **Size: write,
hours.** This is the cheapest single artifact that turns "I read five guarantees and a layer cake" into
"oh — *that's* the idea, and I just ran it."

---

## Summary table

| Area | State | Highest-value move | Size |
|---|---|---|---|
| 1. Stranger onboarding | **ALIVE** | Lead with the in-process `hello_receipt_chain` (door #0); note node build is slow-not-stuck | write, ~30m |
| 2. Caveat language (author) | **PARTIAL** | Fluent builder + named ctors on Rust `Pred` (mirror `Grant`) | wire, ~250 LOC |
| 3. Refusal legibility | **PARTIAL** | Lean `AdmissionReason` → FFI → `SubmitTurnResponse.error` | build, ~1–2 d |
| 4. Not-a-toy apps | **ALIVE** | `first-room` README + "run me" pointer as the flagship | write, hours |
| 5. Teaching the model | **ALIVE** | `start-here.md`: one-sentence model + annotated hello output | write, hours |

**The through-line:** the substrate is *more usable than the "lamesauce" framing assumes* — a stranger
can run a real verified turn in-process today, and ~20 real apps + four guides exist. The frontier is
not *building* usability; it is *surfacing* what already works (move the fast example forward, give
`first-room` and a one-screen explainer a front door) and closing the one true comprehension hole:
**when a turn is refused, say why** — the moment dregg's thesis either lands or silently fails.
