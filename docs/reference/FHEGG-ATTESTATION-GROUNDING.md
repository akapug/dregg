# fhEgg Attestation Grounding — what actually attests the clearing, and why the receipt stack does not

*Read-only grounding (2026-07-17) to resolve one conflation and ground the Market-#4 optimality
repair in what the code/Lean/docs ACTUALLY say. Cited to `file:line` at HEAD. No mechanism is
invented here; where the honest answer is "model-level Lean only, no runtime cert," it says so.*

---

## 0. The conflation, resolved in one line

**Claim (made, then caught):** the dregg proof-carrying / turn-RECEIPT infrastructure (turn-attestation
over the ledger) attests that the fhEgg confidential-clearing algorithm's steps were run.

**Verdict: FALSE — the two stacks are separate.** The turn receipt attests *settlement* (balance
movements over ledger state), never *how the clearing was computed*. The clearing computation's honesty
rests on a DIFFERENT object — the **Cert-F** primal-dual certificate and its own AIR/STARK — which shares
only the STARK *backend* with the receipt stack and meets it only at settlement. ember is correct.

---

## 1. What actually attests the fhEgg clearing computation

There are **three distinct layers at three resolutions**. Only one of them is a runtime attestation of a
given execution, and it covers the convex route — not the uniform-price fold, and not yet at optimality.

### 1a. Model-level Lean proofs — about the algorithm as SPECIFIED, not about any execution

These prove the *rule* is correct/optimal/conserving over an idealized `OrderBook`/`Fill` model. They are
NOT runtime certificates: nothing binds a particular execution's output to them.

- `metatheory/Market/FhEggClearing.lean` — the uniform-price fold→argmax crossing:
  - `clearedVolume_optimal` (`:360`) — the argmax bucket MAXIMIZES executed volume `∀ q < K`; genuine,
    non-vacuous (tooth `workBook_old_crossing_suboptimal` `:487`).
  - `clearedBatch_conserves` (`:386`), `clearedBatch_optimal` (`:436`) — the two-leg cleared batch
    conserves per asset and is uniform-price optimal (no-arbitrage / value-neutral / IR) — the WEAK sense,
    at ANY `V ≥ 0`, discharged through `Optimality.uniform_price_optimal`.
- `metatheory/Market/FhEggAllocation.lean` — per-order rationing: `ration_sum` (`:292`, exact
  conservation), `ration_fair` (`:364`, ±1 pro-rata), `allocation_conserves_at_Vstar` (`:476`). Model-level.
- `metatheory/Market/FhEggRustDenotation.lean` — the Lean argmax equals a Lean **re-authoring** of the
  Rust loop under the honest premise `AggregatesFitU32` (`:96`). `FhEggCrossingDenotation` (`:124`),
  `MpcCrossingDenotation` (`:607`). Binding to the ACTUAL deployed Rust is trust-by-human-reading up to
  the named, un-discharged `FhEggTfheSourceRefinementResidual` (`:508`). Model-level correspondence, not
  a runtime attestation.
- `metatheory/Market/CertF.lean` — `certifies_epsilon_optimal` (`:133`): a Cert-F triple ⇒ `f` is
  ε-optimal, independent of how it was found. This is the model theorem that MAKES a runtime cert possible.

### 1b. The runtime certificate — Cert-F — exists for the CONVEX route only

`Cert-F` is a real runtime object `(f, π, s)` the untrusted solver emits and a **verified checker**
validates. Its linear check — `Af=0, 0≤f≤c, s≥0, Aᵀπ+s≥w, cᵀs−wᵀf ≤ ε` — proves the output is ε-optimal
on the actual public program `(A,w,c,ε)` regardless of the solver's path (verify-not-find). So for the
**volume-max circulation** route there IS a certificate that the cleared flow is honest-optimal:

- `fhegg-solver/src/cert.rs` (`CertF`) + `fhegg-solver/src/air.rs` (the `n+4m+1` constraint rows), driven
  by `fhegg-solver/src/bin/fhegg_clear.rs` — the CLI emits `(f,π,s)`, runs `check_strict`, emits the AIR,
  and evaluates it (honest ACCEPTED `:241-243`, tampered/non-conserving REJECTED `:246-250`).

**Crucial scope limit — the uniform-price fold has NO such certificate.** `FhEggClearing.lean` §7's emit
bridge (`clearingCircuit_sound` `:580`) emits ONLY the balance decomposition + conservation gates, and its
own scope note (`:553-559`) says it is explicitly **NOT** a circuit for the volume-argmax *selection* —
"emitting the argmax … is a separate AIR obligation, not modeled here." So for the uniform-price `(p*,V*)`
clearing (the "fhEgg confidential clearing" the conflation is about), optimality is **model-level Lean
only**; the only runtime-emittable gate is conservation.

### 1c. The runtime STARK — real backend, but the deployed descriptor attests conservation, not optimality

`circuit-prove/src/cert_f_air.rs` lowers the Cert-F AIR to an `EffectVmDescriptor2` and proves it in the
**production STARK** (`prove_vm_descriptor2`, BabyBear + FRI, `prove_cert_f` `:334`), witness `(f,π,s)` in
the trace, only `wᵀf` public (`public_inputs` `:248`). This IS, in principle, a runtime attestation that a
valid Cert-F certificate exists for `(A,w,c,ε)` with cleared volume `wᵀf`. But four deployed caveats gut
the optimality half:

1. **Registered for ONE toy program only.** `is_registered_ring3_program` (`:299`) hardcodes the unit
   3-cycle (`n=3, edges [(0,1),(1,2),(2,0)], w=c=[1,1,1], ε=0`) and refuses everything else (`:311-317`).
2. **The descriptor does NOT force the ε-gap.** Per `docs/reference/MARKET-METATHEORY-REVIEW.md` Finding on
   `CertFDescriptor`, `certFDescriptor_emit_sound` (`CertFDescriptor.lean:547`) is OVER-NAMED: the
   gap-linking gate `g == ε−(cᵀs−wᵀf)` is extracted NOWHERE; the descriptor delivers ~2.5 of 5 certificate
   families (conservation `≡0`, `0≤f`, `0≤s`, and bare `0≤u,0≤d,0≤g` — the nonneg of slack columns WITHOUT
   the gates linking them to the gap). So the deployed AIR forces **conservation + box**, NOT the
   ε-optimality clause — the whole point of a certificate.
3. **ε=0 registration vs achieved-gap mismatch.** The solver bridge `from_solution_json` sets `ε := achieved
   gap` (generally `>0`, `:491`), but registration requires `ε=0` — so even a ring-3-shaped real solve is
   refused unless exactly tight (`FHEGG-SDK-READINESS.md §3`).
4. **Non-hiding PCS.** The deployed path rides plain `TwoAdicFriPcs` (`descriptor_ir2::ir2_config`);
   witness-hiding is `cert_f_air.rs:58-64`'s own "named, not discharged." `fhegg_clear` evaluates the AIR
   natively but does NOT run the STARK ("NAMED, not run in this demo", `fhegg_clear.rs:312`).

**Honest picture (1):** the fhEgg clearing's *optimality* is attested at MODEL LEVEL only. A real runtime
certificate object (Cert-F) exists for the convex route and its AIR is Lean-proven sound in the abstract,
but the DEPLOYED STARK descriptor currently attests only conservation + box for one toy program, on a
non-hiding PCS; the uniform-price fold has no optimality cert at all (conservation gate only).

---

## 2. The receipt/turn stack vs the fhEgg stack — separation confirmed

They are **separate stacks that share the STARK backend and meet only at settlement.**

- **Turn-receipt stack** — "a turn is the exercise of an attenuable proof-carrying token over owned state,
  leaving a receipt." Attests state transitions / balance movements on the ledger (the `EffectVmDescriptor2`
  effect-VM STARK, whose soundness floor is the Poseidon2-CR / FRI tower). It knows nothing about
  demand/supply curves, the argmax, PDHG iterations, or Cert-F.
- **fhEgg clearing stack** — fold → crossing (or PDHG) → `(p*,V*)` / `f` → Cert-F cert → Cert-F AIR. This is
  the clearing computation and its (convex-route) optimality certificate.

**Where they meet — three points, none of which make the receipt attest the clearing math:**

1. **Settlement (the real meeting point).** `metatheory/Market/FhEggLedgerBinding.lean` lowers the fhEgg
   output `(p*,V*)` to a bilateral `MatchNode` cycle (`fhEggMatchNodes` `:49`) that settles through the SAME
   verified executor the turn-receipt attests — `fhEgg_output_executes_exact_drex_clearing` (`:181`) proves
   `settleRing pre (settlementsOf nodes) = some post`. So the clearing RESULT lands as ledger turns
   (receipts). But the receipt attests "these transfers happened and conserve," NOT "these transfers are the
   honest ε-optimal clearing of the sealed book." Binding the deployed output to this constructor is the
   named, un-discharged `FhEggLedgerSourceBinding` (`:197`).
2. **Shared STARK backend.** `cert_f_air.rs` uses the same `dregg_circuit::descriptor_ir2` /
   `prove_vm_descriptor2` / BabyBear+FRI prover as the effect-VM turn descriptors — same backend, DIFFERENT
   AIR/descriptor. One soundness substrate, two independent proof objects.
3. **Order LINKAGE (product frontier).** `FHEGG-PRODUCT-ORDER-FRONTIER.md §R2.2` compiles integer/disjunctive
   ORDER semantics (OCO, bracket, if-then) onto the turn-kernel's nullifier/receipt sequencing — the receipt
   sequences ORDERS, still not the clearing computation.

**Honest picture (2):** genuinely independent stacks. The receipt/turn STARK (circuit-soundness) does NOT
touch the fhEgg clearing computation; it attests settlement of the RESULT. The clearing's own attestation
is the separate Cert-F object. The conflation — that the receipt infra attests the clearing steps — is wrong.

---

## 3. The honest Market-#4 optimality claim + the real path to strengthen it

Ranked from strongest-honest to weakest, with what is proven vs. runtime-attested:

- **Conservation / value-neutrality / individual-rationality (weak uniform-price optimality)** — the
  STRONGEST honest claim. PROVEN model-level (`clearedBatch_optimal` via `uniform_price_optimal`, at any
  `V≥0`) AND the one property runtime-enforceable end-to-end: the conservation gate is emitted in both the
  uniform-price bridge (`clearingCircuit_sound`) and the Cert-F AIR, and the deployed Cert-F STARK descriptor
  DOES force the conservation rows. Say this without qualification.
- **Volume-maximization (the argmax IS the volume peak) / Cert-F ε-optimality** — PROVEN MODEL-LEVEL,
  NOT runtime-attested. `clearedVolume_optimal` (∀ q<K) and `certifies_epsilon_optimal` are real,
  non-vacuous theorems, but (a) the uniform-price emit bridge omits the argmax selection by its own scope
  note, and (b) the deployed Cert-F descriptor does not extract the ε-gap gate (Review: ~2.5 of 5 families).
  So optimality is a property of the SPECIFIED algorithm, not a checked property of a given execution. The
  MPC "joined theorem" further reveals the SUBOPTIMAL balance-threshold and calls the WEAK sense "optimal" —
  OVER-NAMED (Review Finding #1).
- **A PDHG / per-optimizer-step certificate** — does NOT exist, and BY DESIGN must not. Verify-not-find puts
  the `T` solver iterations OUT of the trusted base (`CertF.lean` scope note `:36-41`); the Cert-F certificate
  is the intended substitute for a step-trace. Do not claim or seek one.

**The strongest HONEST Market-#4 sentence:** *"The cleared batch conserves value (no mint/burn) and is
uniform-price value-neutral / individually-rational — proven at model level AND runtime-enforced by the
conservation AIR gate. Its volume-maximization / ε-optimality is proven at model level (`clearedVolume_optimal`,
`certifies_epsilon_optimal`) but is NOT yet runtime-attested: the uniform-price bridge omits the argmax
selection and the deployed Cert-F descriptor does not force the ε-gap."*

**The real path to strengthen (no invented mechanism — each already named in the tree):**

1. **Extract the CertFDescriptor gap-gate.** Prove `g == ε−(cᵀs−wᵀf)` at descriptor level and compose the
   box-upper/dual-feas sub-lemmas into `certFDescriptor_emit_sound`, so the AIR forces the ε-optimality
   clause it currently only names (Review improvement #8). Then the Cert-F STARK attests optimality, not just
   conservation.
2. **Generalize Cert-F beyond ring-3.** Prove `certFDescriptor_emit_sound` generically over `p : CertFProg`,
   emit + byte-pin descriptors for real market program shapes, and fix the ε=0-vs-achieved-gap registration
   mismatch so a real (`ε>0`) solve can register (`FHEGG-SDK-READINESS.md §4.2`).
3. **Attest the uniform-price argmax, or route it through Cert-F.** Emit the argmax-selection AIR (a witness
   that no other bucket executes strictly more — the "separate AIR obligation, not modeled" of
   `FhEggClearing.lean §7`), OR clear uniform-price through the Cert-F convex descriptor (it is the
   linear-utility floor of the circulation LP, `FHEGG-KERNEL.md §2`).
4. **Mechanize the Rust↔Lean denotation.** Discharge `FhEggTfheSourceRefinementResidual` /
   `FhEggLedgerSourceBinding` with extracted-Rust differential tests, so "the deployed Rust computes the Lean
   argmax and routes it to the exact node list" stops being trust-by-reading (Review Finding #3).
5. **Route Cert-F through `HidingFriPcs`** so the witness `(f,π,s)` is actually hidden (currently plain PCS).

---

## 4. What was gotten wrong (flagged plainly)

- **The conflation itself:** that the receipt/turn-attestation infrastructure attests the fhEgg clearing
  computation. It does not — it attests settlement of the result; the clearing's attestor is the separate
  Cert-F object. Separate stacks, sharing only the STARK backend and meeting at settlement.
- **Implicit over-read to avoid:** "the fhEgg clearing is STARK-attested optimal." The DEPLOYED Cert-F STARK
  attests conservation + box for one toy program on a non-hiding PCS; it does not currently force optimality,
  and the uniform-price fold has no optimality cert at all. Optimality is model-level Lean today.
