# fhEgg Attestation Grounding — what actually attests the clearing, and why the receipt stack does not

*Grounding updated 2026-07-19. It resolves the receipt/clearing conflation and records the
current Cert-F, hiding-proof, output-MPC, and settlement boundaries. Verify named artifacts at
HEAD; exact line numbers from the earlier review have intentionally been removed where the code moved.*

---

## 0. The conflation, resolved in one line

**Claim (made, then caught):** the dregg proof-carrying / turn-RECEIPT infrastructure (turn-attestation
over the ledger) attests that the fhEgg confidential-clearing algorithm's steps were run.

**Verdict: FALSE — the two proof stacks are separate.** The turn receipt attests *settlement* (balance
movements over ledger state), never *how the clearing was computed*. A canonical fhEgg runtime envelope now
binds roster, inputs/ciphertexts, BFV identity, rule, transcript, output, and replay context into one claim
digest, but binding is not computation integrity: its binding-only grade is categorically rejected by full
verification. A production-shaped Ed25519 threshold-roster `ComputationIntegrityVerifier` now authenticates
which exact quorum endorsed that claim, and an opt-in market module co-endorses the complete certified
settlement. That is authenticated attribution, not a proof that ciphertexts open to the certified order book
or that a malicious-secure MPC produced it; the live default offering does not yet consume the weld.

---

## 1. What actually attests the fhEgg clearing computation

There are **three distinct layers at three resolutions**. Registered convex programs have a runtime
optimality proof. The no-viewer uniform-price path computes only `(p*,V*)` but still lacks an attestation
binding that output to the committed/encrypted source orders.

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

### 1c. The runtime STARK — registered convex optimality is real and has a hiding path

`circuit-prove/src/cert_f_air.rs` lowers the full Cert-F relation to an
`EffectVmDescriptor2`. The descriptor now enforces conservation, box bounds, slack sign,
dual feasibility, and the ε-gap link, with explicit field-to-integer admission ranges. Lean proves
the generic emit theorem plus unconditional integer admissions for two byte-pinned programs:

1. unit ring3 (`ε=0`), width 465 / 482 constraints;
2. market4 (`ε=2000`), width 581 / 602 constraints.

Unregistered programs fail closed. `prove_cert_f` remains the plain non-hiding compatibility
entry point. `prove_cert_f_zk` / `verify_cert_f_zk` run the identical registered AIR through
`DreggZkStarkConfig` and `HidingFriPcs`; the focused ring3 tooth mints/verifies the proof, asserts
the ZK random commitment/openings exist, and refuses a changed public objective.

**Honest picture (1):** registered convex Cert-F optimality is runtime-attested, including a real
hiding PCS construction. This does **not** yet attest the no-viewer uniform-price MPC execution:
the Cert-F public program exposes `(A,w,c,ε)`, and no proof currently binds the MPC's `(p*,V*)`
to the committed/encrypted source orders. A complete batch-STARK simulator theorem and full FRI
decode/soundness floor also remain separate from the working construction.

---

## 2. The receipt/turn stack vs the fhEgg stack — separation confirmed

They are **separate proof stacks.** A runtime claim envelope and authenticated quorum now name and endorse
both sides precisely, but the installed verifier does not prove that the named ciphertexts open to the named
orders or that those orders produced the clearing and settlement.

- **Turn-receipt stack** — "a turn is the exercise of an attenuable proof-carrying token over owned state,
  leaving a receipt." Attests state transitions / balance movements on the ledger (the `EffectVmDescriptor2`
  effect-VM STARK, whose soundness floor is the Poseidon2-CR / FRI tower). It knows nothing about
  demand/supply curves, the argmax, PDHG iterations, or Cert-F.
- **fhEgg clearing stack** — fold → crossing (or PDHG) → `(p*,V*)` / `f` → Cert-F cert → Cert-F AIR. This is
  the clearing computation and its (convex-route) optimality certificate.

**Where they meet — four points, none of which make the receipt attest the clearing math:**

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
4. **Canonical runtime claim envelope + authenticated co-endorsement.** `fhegg-fhe/src/attestation.rs`
   domain-separates the exact protocol/session, ordered roster and input digests, BFV identity, rule shape,
   strict transcript, `(p*,V*)`, output bits, and replay context. `verify_full` additionally requires an
   external computation-integrity verifier over that exact digest; `OutputOnlySelfAssertion` can never pass.
   `AuthenticatedQuorumVerifier` enforces an exact ordered Ed25519 key roster, a threshold, canonical signer
   order, strict signatures, and exact roster equality. The opt-in `dreggnet-market::authenticated_receipt`
   module commits the full `CertifiedClearing` once inside that claim and checks the output crossing and replay
   gate from scratch. Its executable negative tooth is load-bearing: old quorum evidence fails after changing
   a ciphertext digest, but a quorum may sign a new arbitrary ciphertext/settlement pair and it passes. Thus
   this layer proves exact co-endorsement and attribution—not the missing ciphertext-opening/source relation.
   The provided replay guard remains process-local; durable deployment needs transactional persistence.

**Honest picture (2):** genuinely independent proof stacks with an explicit envelope and authenticated
co-endorsement between their statements. The receipt/turn STARK does NOT touch the fhEgg clearing
computation; it attests settlement of the result. Cert-F attests registered convex optimality. Threshold
signatures attest who endorsed the combined claim. The no-viewer uniform-price execution still needs a
proof/MAC relation from exact encrypted inputs through computation to the committed order book; an honest
verifier-in-every-accepted-quorum policy is currently an assumption, not a cryptographic source theorem.

---

## 3. The honest Market-#4 optimality claim + the real path to strengthen it

Ranked from strongest-honest to weakest, with what is proven vs. runtime-attested:

- **Conservation / value-neutrality / individual-rationality** — proven model-level and enforced by the
  settlement/turn path. This says the recorded transfers are coherent; it does not identify the order
  source from which a clearing output was computed.
- **Cert-F ε-optimality for registered convex programs** — proven in Lean and runtime-attested by the full
  descriptor, with integer admission and optional hiding PCS. This is a checked property of the registered
  public program and private certificate witness.
- **Uniform-price volume-maximization from committed no-viewer orders** — the rule and Rust/Lean denotation
  are proved/model-tested, and the party MPC computes reveal-minimal `(p*,V*)`; the missing statement is the
  runtime binding from those exact committed/encrypted inputs through the distributed computation to the
  settlement receipt.
- **A PDHG / per-optimizer-step certificate** — does NOT exist, and BY DESIGN must not. Verify-not-find puts
  the `T` solver iterations OUT of the trusted base (`CertF.lean` scope note `:36-41`); the Cert-F certificate
  is the intended substitute for a step-trace. Do not claim or seek one.

**The strongest HONEST Market-#4 sentence:** *"Registered convex clearings have full integer-sound Cert-F
optimality proofs and a real hiding batch-STARK path; the no-viewer uniform-price engine computes only
`(p*,V*)`, and a strict threshold roster can authenticate the exact combined input/output/settlement claim,
but the ciphertext-opening and malicious-computation relation joining those fields is still missing."*

**The real path to strengthen (no invented mechanism — each already named in the tree):**

1. **Bind the uniform-price output to committed orders.** The attestation must name the exact roster,
   order commitments/ciphertexts, clearing rule/version, `(p*,V*)`, and settlement receipt; output-only
   attestation is insufficient.
2. **Choose the Tier-0 integrity construction.** Authenticated malicious-secure MPC with transcript/MAC
   verification, distributed ZK from shares, or verifiable FHE can close this without creating a plaintext
   prover. A conventional single-prover ZK witness would itself violate no-viewer.
3. **Handle private coefficients honestly.** Cert-F hides `(f,π,s)` but treats `(A,w,c,ε)` as public
   descriptor algebra. Dynamic bid weights therefore require a different fixed AIR/input-commitment
   relation rather than per-book public descriptor specialization.
4. **Mechanize the Rust↔Lean denotation and settlement join.** Discharge `FhEggTfheSourceRefinementResidual` /
   `FhEggLedgerSourceBinding` with extracted-Rust differential tests, so "the deployed Rust computes the Lean
   argmax and routes it to the exact node list" stops being trust-by-reading (Review Finding #3).
5. **Discharge the remaining proof floors.** Prove the complete hiding batch-STARK simulator statement and
   the full FRI decode/soundness theorem rather than treating the working PCS configuration as those theorems.

---

## 4. What was gotten wrong (flagged plainly)

- **The conflation itself:** that the receipt/turn-attestation infrastructure attests the fhEgg clearing
  computation. It does not — it attests settlement of the result; the clearing's attestor is the separate
  Cert-F object. Separate stacks, sharing only the STARK backend and meeting at settlement.
- **Implicit over-read to avoid:** "the no-viewer fhEgg clearing is source-bound and STARK-attested optimal."
  Registered convex Cert-F programs now have real optimality and hiding proofs; the distributed uniform-price
  path still lacks the exact committed-input → `(p*,V*)` → settlement attestation join.
