# WHAT IS DREGG — an honest, grounded review

*Written 2026-06-06 by a skeptic, grounded in the actual code/artifacts at the time
of writing. Quotes are `file:line` or live commands. No laundering — the goal is for
the maintainer to know what they actually have, how it performs, and where the gaps are.*

---

## 0. The one-line answer

**dregg is a capability-secure distributed runtime with a deep, separately-built Lean
metatheory — not (yet) a verified-execution node.** A solo node is live and running
real leaderless DAG consensus. A Rust executor really executes ~56 effects per turn. A
large Lean development really proves conservation, capability-attenuation, and
nullifier/no-double-spend for a *model* of that executor. A real STARK prover (plonky3)
really proves a generic AIR on demand. **But these three pieces are not yet welded into
one pipeline**: the node runs the *Rust* executor (the Lean is a shadow comparator), and
the finalized-turn path does **not** generate a STARK that binds the post-state. So today
"verified" means *the metatheory of a model is largely proven*, not *the bytes the live
node committed were proven*.

---

## 1. What is dregg, in one honest paragraph?

dregg ("Dragon's Egg") is a **capability-secure, object-capability distributed runtime**
in the vat/E-rights lineage: cells (objects) own balances and capabilities, and state
advances in *turns* (effect bundles) that are authorized by an
object-capability/credential model (a 10-variant `Authorization` with
attenuation/revocation). The transport layer is a **blocklace** — a leaderless DAG with
total ordering via a `tau` function, taken from the Cordial Miners paper
(`node/src/blocklace_sync.rs:1` "Federation sync via the blocklace (Cordial Miners)
consensus layer"; `use dregg_blocklace::ordering::tau`). It is **not** a classical-BFT
propose/vote/commit chain (that was superseded), and it is **not** a smart-contract VM
in the EVM sense. Its distinguishing ambition is a **third, verification layer**: a Lean
4 metatheory (`metatheory/` ≈ 236k LOC of Lean) that aims to prove the executor sound and
to extract verifiable circuits, plus a plonky3 STARK layer for ZK/privacy (notes,
nullifiers). So the honest category is: **an object-capability distributed runtime with
DAG consensus, a privacy/ZK toolkit, and an unusually ambitious — but not-yet-integrated
— formal-verification program.** What it is *for*: agent-to-agent value/credential
exchange where each party can verify the others' turns rather than trust them.

---

## 2. What has actually been BUILT and WORKS

### Running devnet — REAL (solo)
`curl https://devnet.dregg.fg-goose.online/status` returns:
```json
{"healthy":true,"peer_count":0,"latest_height":0,"dag_height":1107,
 "block_count":1773,"consensus_live":true,"revocation_count":0,
 "note_count":0,"federation_mode":"solo", ...}
```
A node is live, has produced 1773 blocks / dag_height 1107, reports `consensus_live:true`.
The web surfaces (`/`, `/apps.html`, `/explorer/`) all return HTTP 200. **Real and
running** — but `peer_count:0`, `federation_mode:"solo"`, `latest_height:0`,
`note_count:0`. So: a single node, alone, ticking heartbeats; the *distributed* and
*privacy* claims are not exercised by this deployment. Consensus liveness in a one-node
DAG is the trivial case (memory: the strong single-machine bounds collapse here).

### Rust executor — REAL, and it IS the runtime
The node executes turns through the **Rust** `dregg_turn::TurnExecutor`
(`node/src/executor_setup.rs:6,70`), invoked at
`node/src/blocklace_sync.rs:55` `executor.execute(&signed_turn.turn, &mut s.ledger)` inside
`execute_finalized_turn`. The ledger is HashMap/BTreeMap-backed
(`cell/src/ledger.rs:1`), so the *running* state representation is efficient. This is the
real, working execution engine. ~606k LOC of Rust across the top-level crates.

### Verified Lean executor — REAL as a model, NOT wired in
`execFullForestG` / `dregg_exec_full_forest_auth` is the single credential-gated entry
(`metatheory/Dregg2/Exec/GatedForestCfg.lean:84`). `HandlerExecutor.lean` maps **56**
`FullActionA` variants to closed effects
(`HandlerExecutor.lean:18` "the TOTAL map `FullActionA → ClosedEffect` mapping each of the
56"). It carries real `#guard` adversarial tests (forged-cred and false-caveat forests
are rejected: `GatedForestCfg.lean:272,275` both `== false`). **But** this executor runs
only as an *optional shadow* (`turn/src/lean_shadow.rs:1` "compares Rust commit decisions
against the verified Lean kernel **without affecting** `TurnResult`", gated on
`DREGG_LEAN_SHADOW=1`), and `grep` finds **no** import of `lean_shadow`/`dregg_lean_ffi`
in `node/src`. So the verified executor is a differential oracle in `turn/`, **not** the
node's runtime.

### Circuit / ZK layer — REAL prover, partial coverage
plonky3 is a real dependency and `p3_uni_stark::{prove,verify}` is really used
(`circuit/src/plonky3_prover.rs:45`). Proving is invoked from API/MCP endpoints
(`node/src/api.rs:1805`, `node/src/mcp.rs:262,479,3576` all call
`dregg_circuit::stark::try_prove`/`prove`). There is a real generic "Lean-emitted
descriptor" interpreter AIR (`circuit/src/lean_descriptor_air.rs`, 1685 LOC) and a landed
**LogUp efficiency win** for its range checks (`circuit/src/lean_lookup_air.rs:1` "the
FIRST concrete efficiency win for the verified extraction circuit"; replaces 30 aux cols +
31 constraints per 30-bit wire with a shared byte range-table). Kimchi/Mina and an sp1
guest are also wired as optional backends. **Caveat:** the *consensus path does not prove
turns* — `execute_finalized_turn` notes "full STARK root binding is a [best-effort]"
(`node/src/blocklace_sync.rs:106`). So STARKs are an on-demand capability, not a
per-finalized-turn guarantee.

### Apps — toy/template scale
Two app surfaces: Lean `metatheory/Dregg2/Apps/` (nameservice, identity, subscription,
governed-namespace, privacy-voting, etc. — each with a `*Gated.lean` variant on the gated
executor) and Rust `starbridge-apps/` (nameservice/identity/subscription/… each a single
`lib.rs`). These are **demonstrations on the model**, not production apps with users.
`note_count:0` on the live node confirms the privacy apps aren't exercised in production.

### SDK / node plumbing — REAL
There's a real `sdk/`, `cli/`, gossip, websocket, MCP, persistence, multi-group routing,
genesis, blocklace sync/checkpoint. The node is a genuinely substantial piece of systems
software, not a demo script.

**Scorecard:** devnet node = REAL (solo/trivial regime). Rust executor = REAL (is the
runtime). Lean executor = REAL-as-model, shadow-only. STARK prover = REAL but on-demand,
not in the commit path. Privacy = built, unexercised. Apps = templates.

---

## 3. The verification story — honestly

### What is genuinely PROVEN (about the *model*)
- **Conservation** across a turn: `execHandlerTurn_conserves`
  (`HandlerExecutor.lean:299`) is proved by *lifting* the generic `turn_conserves`, not a
  56-arm matrix — a clean, non-vacuous keystone, `#assert_axioms`-pinned.
- **Handler refines the kernel** per effect: a long list of
  `handler_refines_execFullA_*` theorems (transfer/mint/burn/escrow/obligation/bridge/…,
  `HandlerExecutor.lean:383+`) tie each handler arm to the kernel spec.
- **Capability attenuation / authorization gating**: forged credentials and false caveats
  are rejected (the `#guard … == false` tests above), and the gate is the single
  unavoidable entry.
- **Nullifier / no-double-spend** lives in the Lean privacy kernel
  (`PrivacyKernel.lean`, `Privacy.lean`, `Exec/CellNullifier.lean`) and in the Rust AIR
  (`note_spending_air.rs`).
- **Data refinement to a HashMap kernel**: `ConcreteKernel.lean` (commit `c3d8dc1e`) is a
  real l4v-style abstraction relation (`toAbstract`) with the transfer/writeField squares
  proved, "NO `sorry`/`admit`/`axiom`/`native_decide`" (`ConcreteKernel.lean:23`).
- Discipline is taken seriously: **311** files carry `#print axioms`/`assert_axioms`
  footprint guards, and the named crypto carriers are each annotated "rests only on the
  standard axioms — no `sorryAx`, no crypto axiom" (e.g. `Crypto/Bridge.lean:407`).

### What is ASSUMED
- **Poseidon2 collision-resistance** and the named crypto carriers (commitment/digest
  injectivity portals) are grounded *on* Poseidon2 CR (`fe5a6a36` "ground injectivity
  portals on Poseidon2 CR"), i.e. assumed as a hardness axiom, not derived. This is normal
  and correct — but it's an assumption.

### What is OPEN (the load-bearing honesty)
- **No execute→prove wiring.** The biggest gap. The node commits turns with the Rust
  executor and only a "best-effort" STARK root binding (`blocklace_sync.rs:106`). Nothing
  proves the *committed post-state* on the live chain.
- **The Lean development is NOT sorry-free.** `grep` counts **693** `sorry` occurrences
  across **344** Lean files (`grep -rn 'sorry' metatheory --include='*.lean'`). Heaviest in
  `Circuit/` (101), `Exec/` (116/54), `Apps/` (30). Many are framed as
  scaffold-placeholders being progressively closed (`Circuit/DigestPortal.lean:66` "These
  were `def … : Prop := sorry` placeholders. They are now PROVED"), but the raw count means
  **this is a verification-in-progress, not a verified system**. The proven keystones are
  real; the surrounding surface is not all discharged.
- **Consensus is not fully proven**: `Dregg2/Exec/Consensus.lean` has 10 `sorry`s; the
  Stingray/Fairness proofs are partial. The Cordial-Miners ordering that the live node
  actually runs is the dregg1 Rust implementation, not a Lean-verified one.
- **circuit ⟺ protocol soundness** (the stated "crown jewel": "the circuit's algebraic
  statement suffices to enforce protocol dynamics") is **not** closed — the
  `lean_descriptor_air` generic interpreter exists and a cross-binding beachhead was
  prototyped, but the full executor⟺spec *and* circuit⟺spec triangle per effect (the
  3-corner soundness with a state commitment + anti-ghost tooth) is the open program, not a
  done result.

**What "verified" buys today:** confidence that the *abstract execution laws* (value
conservation, attenuation monotonicity, refinement to an efficient kernel) hold for a
faithful *model* of the executor, with checkable axiom footprints. It does **not** yet buy
"the running node's committed state is proven correct or proven-in-zero-knowledge."

---

## 4. Efficiency — honestly

- **Running node:** the Rust ledger is HashMap/BTreeMap-backed (`cell/src/ledger.rs:1`),
  so live per-effect state access is O(1)-ish. The runtime path is reasonable.
- **Lean executor (the verified model):** the kernel state is *function-based* —
  `RecordKernelState.cell : CellId → Value` plus ~15 more `CellId → …` fields
  (`Exec/RecordKernel.lean:442,446,475,…`). Updates are if-then-else function extension =
  **O(n)/op in proof-evaluation terms** and not how you'd run production. The recently
  landed `ConcreteKernel.lean` (`c3d8dc1e`) is the l4v **data-refinement** answer: a
  `Std.HashMap`/`Std.HashSet`-backed concrete kernel with a proved abstraction relation, so
  the efficient representation inherits the abstract proofs. This is the right pattern, but
  it currently covers the **hot path** (transfer/writeField + nullifier/commitment sets),
  not all 56 effects — refinement coverage is partial.
- **Circuit:** the verified-extraction AIR (`lean_descriptor_air`) is a *generic
  interpreter*, which is inherently more expensive than a hand-rolled per-effect AIR. The
  **LogUp range-bus** (`lean_lookup_air.rs`) is a concrete, measured win (byte-limb shared
  range table vs per-bit decomposition). One win landed; broad circuit efficiency work
  remains.
- **The shadow tax:** when `DREGG_LEAN_SHADOW=1`, every eligible turn is marshalled across
  FFI and re-executed in Lean for differential comparison — useful for trust-building, pure
  overhead for throughput, and off by default.

**Posture:** the *running* system is efficient enough for a devnet; the *verified* system
is being dragged from proof-friendly (slow) representations toward efficient ones via
refinement, with the hot path done and the long tail open. The circuit path is the least
efficient and least complete leg.

---

## 5. Limitations / what dregg is NOT (yet)

1. **Not a verifiable-execution node.** No prover is wired to the commit path; STARKs are
   on-demand API/MCP calls, not per-finalized-turn (`blocklace_sync.rs:106` best-effort).
2. **Consensus/finalization is not connected to the verified executor.** The node runs the
   Rust executor against the Rust blocklace ordering; the Lean executor is a shadow, and
   the Lean consensus is `sorry`-bearing.
3. **dregg1's Rust is still the runtime.** "THE SWAP" — making the gated Lean executor *be*
   the executor via FFI — has not happened; the Lean side remains an oracle/shadow.
4. **Privacy is partially welded and unexercised.** Notes/nullifiers exist in both Rust
   AIR and Lean kernel, but the live node reports `note_count:0`; the MASP-grade privacy is
   a goal, with a recommendation to pull in a vetted component rather than ship bespoke.
5. **Distribution is unproven in practice.** `peer_count:0`, `federation_mode:"solo"`. The
   interesting BFT/equivocation/cross-group properties aren't being exercised by a
   multi-node deployment.
6. **The Lean metatheory is verification-in-progress.** 693 `sorry`s; the centerpiece
   circuit⟺protocol soundness triangle is open. The proven keystones (conservation,
   refinement, attenuation) are genuine but partial coverage.
7. **Docs drift.** There are many `.md` files (`docs/rebuild/` alone is dense), and per the
   maintainer's own notes several are stale/aspirational — trust the code, not the markdown.

---

## 6. Honest maturity verdict

**A well-architected research seed with one foot in production-plumbing.** It is past
"prototype script" — there's a live node, real consensus ordering, a real executor, a real
STARK prover, and a serious (236k-LOC) Lean development with genuine proved keystones and
disciplined axiom hygiene. But it is well short of "a real verified node": the three layers
(execute / order+finalize / prove) each work in isolation and are not yet welded, and the
verification surface is far from sorry-free.

### The 3–5 things that most define the gap to "a real verified node"

1. **Wire a prover into the commit path.** Make `execute_finalized_turn` emit a STARK that
   binds the committed post-state (state commitment + authenticated root update), replacing
   the "best-effort" binding at `blocklace_sync.rs:106`. Without this there is no
   *verifiable* execution, only verified *theory*.
2. **Close the circuit⟺protocol soundness triangle per effect** (the crown jewel): an
   independent full-state spec, with BOTH executor⟺spec and circuit⟺spec proved, pinned by
   an injective state commitment + anti-ghost tooth (tampering any cell ⇒ UNSAT). The
   `lean_descriptor_air` interpreter is the substrate; the soundness theorem is the missing
   capstone.
3. **THE SWAP:** make the gated Lean executor (`execFullForestG`) *be* the runtime (FFI in,
   not shadow), so the thing that runs is the thing that's proved — eliminating the
   Rust/Lean divergence risk that the shadow only *detects*.
4. **Finish the refinement + drive down `sorry`s where it matters.** Extend
   `ConcreteKernel` refinement past the hot path; discharge the load-bearing consensus and
   circuit `sorry`s (not the cosmetic ones). Report a *verified target* (a named theorem set
   that is sorry-free and axiom-pinned), not a whole-tree green.
5. **Exercise distribution and privacy for real:** a multi-node deployment (peer_count > 1)
   that actually runs the DAG ordering under equivocation, and a privacy app that moves
   notes (note_count > 0), so the BFT and MASP claims are tested rather than asserted.

---

*Evidence index (commands run, read-only):*
`curl …/status` (live), `git log --oneline | wc -l` → 960 commits,
`find … *.lean | wc -l` → 236k Lean LOC, `find … *.rs` → 606k Rust LOC,
`grep -rn sorry metatheory` → 693 in 344 files,
`grep assert_axioms` → 311 guarded files,
plus the cited `file:line` reads of `blocklace_sync.rs`, `executor_setup.rs`,
`lean_shadow.rs`, `plonky3_prover.rs`, `lean_lookup_air.rs`, `RecordKernel.lean`,
`ConcreteKernel.lean`, `HandlerExecutor.lean`, `GatedForestCfg.lean`.
