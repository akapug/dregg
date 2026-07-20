# fhEgg — the maturity roadmap: are we building the vision, or the easy waters?

*Written 2026-07-18; corrected from code and executable artifacts at HEAD 2026-07-19. This is a
maturity ledger, not a calendar or cost estimate. Companion to `FHEGG-KERNEL.md` (what-is),
`FHEGG-SDK-READINESS.md` (is-it-shippable), `DREGGFI-VISION.md` (the ambition), and
`FHEGG-MATHEMATICAL-BRIEF.md` §5-7 (the frontier).*

---

## 0. The honest self-assessment: where the effort has actually gone

The vision (from the genesis 2026-07-13 → the codex rounds) is a **private convex-derivatives factory**:
one homomorphic-fold kernel, three privacy tiers, a typed product DSL (`fhIR`), the convex engine at `T>1`,
real no-viewer — *"you shouldn't have to choose between a market that's private and one you can prove is
fair."*

What we have actually BUILT, graded by **distance-to-vision**, not by effort:

| built | grade | is it the vision, or the tractable foundation? |
|---|---|---|
| addition fold (CPU, Lean-verified; GPU, parity-proven) | WORKING | **foundation.** The additive encrypted primitive. |
| resident GPU fold arena | WORKING / BOUNDED | Upload-once, device-resident recursive folding, adapter-derived chunking, explicit CPU fallback, and bit parity are implemented. The *whole clearing program* is not GPU-resident yet. |
| uniform-price clearing + Cert-F + private N4K4 relation | WORKING / RESEARCH | Plaintext settlement is usable; fixed-shape private orders are hidden by `HidingFriPcs` and exact output constraints. The committed-order source weld is not yet a lattice/FHE same-opening proof. |
| typed `fhIR` compiler | WORKING / PARTLY LEAN-AUTHORITATIVE | The visibility/curvature/phase axes, named reject list, resource/leakage manifests, and runnability checks compile real programs. One canonical rebalance plan is emitted from Lean and strictly interpreted by Rust; the broader Rust grammar is not yet wholly refined to Lean. QP compilation emits an explicit exact SDD/PSD certificate, strict bounded `FHSDD001` transports it, and the runner rechecks its complete integer structure plus bit-exact binding to backend `P` before solving. `FHQPB001` now exports the SDD/PSD admission witness and exact-arithmetic fixed-point KKT residual witness as one bounded canonical artifact, rechecking both and requiring byte-exact agreement on `P`. Lean composes same-matrix SDD with exact-zero KKT into global optimality; the deployed positive-tolerance checker does not by itself inhabit that stronger premise. The source-f64-to-exact rounding refinement is not yet a theorem. |
| convex engine at `T>1` | WORKING / BOUNDED CLASS | Exact scaled-domain affine iterations, a Lean-shaped noise ceiling, fail-closed window checks, and `T=6` private rebalance are executable. A prox that may bind is refused; private comparison/projection is not silently approximated. |
| no-single-viewer custody | RESEARCH / REAL PROTOCOL SHAPE | Collective BFV, masked decrypt-to-shares, party MPC, authenticated `t<n` quorum openings, bivariate VSS linked to the actual BFV public-key contribution, and VSS-anchored ZK proofs of the exact decrypt-share equation/quotients/smudge range exist. Six degree-4096 proofs take 1086.009s release; setup-key shortness, malicious MPC, private authenticated deployment channels, durable replay, and interactive proof performance remain. |
| hidden-reserve Dark AMM | RESEARCH / EXECUTABLE / HOSTED | Reserve state and `dx`/`dy` are ciphertexts; one ct×ct multiplication verifies an exact constant-product transition. The collective-key path generates relin without assembling the secret, threshold-opens only a masked invariant, releases one equality bit, verifies a strict quorum receipt, and atomically commits/refuses without reconstructing the product. Lean proves the receipt state machine (7 clean keystones), authors the two-root semantics (9), and closes the 104-column descriptor's full `Satisfied2->Accepts` bridge (19); the hiding-only prover is green. An owner-only offline producer now carries the private root opening forward, proves the transition, and deterministically encrypts the same amounts. A Tier-1 issuer quorum re-encrypts those exact openings, reconstructs the statement, verifies the proof, and signs one canonical same-opening claim. The v3 authority claim signs the complete canonical BFV parameter digest (including error variance) plus both public BFV wrap-safety bounds and refuses either bound below the witnessed amount; the hiding relation proves ten-bit amounts and no-overdraw. Strict hosted v3 reconstructs every object, rejects all v1/v2 bypasses, and commits receipt replay with the encrypted/root transition; web, Telegram, Discord, startup, and deployment configuration expose only that policy when authority is configured. Separately, `FHDAP002` restarts the complete collective public evaluation state into a host with no secret key, private candidate nonces bind the exact encrypted pre-state, and independently configured `FHDAR001` quorum evidence can commit the ciphertext transition without the in-process decision capability. v2 hashes the canonical full fhe.rs parameter encoding—including error variance—and rejects retired v1. `Market.DarkAmmPublicHost` proves the corresponding state law with ten clean keystones, including independent state-staleness and receipt-replay sequential barriers; `Market.DarkAmmPublicHostLifecycle` adds fourteen clean two-phase staging/commit/abandon/restart laws while leaving cryptographic carriers explicit. A new dreggnet collective service verifies collective Tier-1 same-opening at stage without consuming replay; FHDAR commit atomically installs public ciphertext material/root/sequence plus both exact replay images; pending state is strict-restartable and abandon/restage is live. Its focused gate uses real 3-party DKG/relin and HidingFri but simulates the reveal-only decision transcript; the upstream no-assembled-secret test remains the real masked-computation gate. Relin has signed, session/PK/roster/phase-bound public manifests and a strict restartable coordinator transcript, but fhe.rs exposes no canonical R1/R2 share codec: live parties must resend their opaque typed shares and the manifest ID does not yet commit to that algebraic value. The Tier-1 issuers see the witness and seeds, and the existing player-facing web/Telegram/Discord v3 offering still uses explicit `n=1`; it has not yet been replaced by the standalone collective service. A lattice-ZK/no-viewer replacement for both same-opening and bound soundness, trusted initial-carrier/key-domain evidence, distributed witness production, malicious MPC input binding, floor swaps, malicious-share correctness, rollback-resistant carrier/replay persistence, dropout/party-restart relin, `t<n` relin, and shared-interface collective deployment remain. |

**The corrected verdict:** fhEgg is no longer only a foundation or a one-iteration sketch. It is an
executable research system with a typed factory language, a bounded `T>1` encrypted solver, real
collective-custody paths, hiding proofs, and two end-to-end private market shapes (a six-step portfolio
rebalance and an exact constant-product transition). It is **not production-private**. The center of
gravity now belongs at the composition seams: prove that all private representations share the same
opening, bind the decision circuit's private shares to that opening, make custody/MPC malicious-secure and restart-safe, and
carry those properties through the player-facing settlement path.

---

## 1. The residency insight — performance excellence is an ARCHITECTURE, not a shader tweak

**The mistake we measured:** the GPU fold "loses ~5-7×" because the benchmark uploads N ciphertexts,
does ONE streaming pass of adds (arithmetic intensity ≈ 0), and downloads. The transfer dominates *because
the data should never have been round-tripping*. We optimized a shader when the problem was the memory
model.

**The right architecture — GPU-RESIDENT end-to-end.** Encrypted orders should be uploaded ONCE at ingress
and stay on the device while the whole clearing runs:

```
ingress: encrypt orders ──upload once──▶  [ GPU-resident ciphertext arena ]
                                             │  fold        (add, resident — now FREE, no transfer)
                                             │  histogram   (measured 11.4× at N=1M)
                                             │  crossing / argmax
                                             │  convex iterations  x ← prox(x − τAx)   (T of them)
                                             │  ct×ct multiply  (NTT — the GPU-saturating kernel, Merkle-class 23×)
                                             ▼
egress: threshold-decrypt (p*, V*) ◀──download once (a few scalars)
```

The transfer then amortizes over a long homomorphic computation instead of over one add. Every
op that already wins on-device (histogram 11×, Merkle-class hashing 23×, DFT 4-6×) wins, and the fold
becomes *free* (already resident). **This is the performance north star: a resident ciphertext arena + a
scheduler that keeps data on-device across the whole pipeline, host↔device only at ingress/egress** — the
same shape real FHE accelerators (Zama CUDA, FPGA) use. `GpuResidentPipelineResidual` — the single
highest-leverage performance build.

**What is already closed:** `fhegg-fhe/src/gpu_arena.rs` implements the retained arena for the additive
fold, including bounded streaming uploads, device-to-device recursive reduction, one final readback,
capacity accounting, and parity/refusal tests. **What is not closed:** histogram/crossing, convex
iterations, ct×ct/NTT, and threshold egress do not yet share one resident scheduler. Do not collapse
"resident fold" into "resident fhEgg pipeline" in either direction.

---

## 2. The five vision-critical builds (the "fullest fhEgg" — NOT the easy waters)

These are the five load-bearing builds, now recorded as a burn-down rather than a list that falsely calls
implemented work absent:

1. **REAL no-viewer — RESEARCH PATH BUILT; MALICIOUS/DEPLOYED PATH OPEN.** `threshold.rs`,
   `threshold/quorum.rs`, `boundary.rs`, and `mpc_party.rs` now compose collective BFV custody, Lean-pinned
   smudging bounds, exact masked opening, arithmetic-to-boolean sharing, and output-only MPC. The `t<n`
   path authenticates a roster and canonical share transcript; its bivariate VSS public images bind the
   hidden dealer constants to the exact BFV `p0 = -a*s+e` contribution. Its `FHQPv001` certificate now
   proves the exact negacyclic/RNS decrypt-share equation, both quotient families, and the inclusive
   `[-2^80,2^80]` smudge range against VSS-anchored Pedersen commitments. Remaining: zero-knowledge
   ternary/CBD setup-key shortness, a distributed persistent commitment ceremony, malicious MPC
   input/share validity, real private channels and preprocessing, crash/recovery, and wiring the new
   canonical replay snapshot into rollback-resistant transactional storage.
   Six degree-4096 proofs took 1086.009s release, so compression/batching/parallel proving is an immediate
   product blocker. Independent custodians now have a canonical parallel scheduling API, but the heavy
   composition has not yet been re-measured through it and each certificate remains large.
   `NoViewerKeyCustodyResidual` is narrower than it was, not closed.

2. **The convex engine at `T>1` — CLOSED FOR THE AFFINE / INACTIVE-PROX CLASS.**
   `convex_engine::convex_solve` executes exact scaled-domain iterations and refuses past its composed
   noise ceiling. `e2e_private_derivative.rs` compiles a Tier-0 fhIR rebalance, encrypts under a collective
   key, runs six iterations, threshold-opens the result, and matches the integer reference bit-for-bit.
   The residual is no longer `T>1`; it is expressive depth. The first genuinely **active** box product is
   now built in `fhegg-fhe/src/fhir/private_box.rs`: an n-of-n party-shared canonical integer is range-gated
   and compared privately against both public faces, then retained as shares in the interior or replaced by
   a party-zero sharing of the selected endpoint. No operand, difference, residue, or projected value opens;
   a focused equality-bit boundary checks the output. `Market/PrivateBoxProjection.lean` authors the exact
   clamp and proves that the runtime share selection reconstructs that clamp, plus range/idempotence laws.
   Projected shares can be consumed by a second box step without an output-share accessor; the next session
   must name a digest of the exact prior session, disclosed branch, and reveal-only transcripts.
   This first product deliberately reveals **which face** was selected and requires the canonical
   power-of-two comparison domain `t = 2^value_bits`; it is not yet the branch-oblivious prox inside the
   deployed prime-modulus BFV iteration loop. Remaining: hide the face bits (or prove them acceptable product
   leakage), bridge/re-share the prime BFV modulus without a truncation seam, chain the shared projection back
   into subsequent encrypted iterations, add SOC projections, and harden preprocessing/input validity against
   malicious parties. `ActivePrivateProxResidual` is materially narrowed, not closed.

3. **`fhIR` — WORKING COMPILER; FORMAL CUTOVER PARTIAL.** `fhegg-fhe/src/fhir/mod.rs` implements the three
   type axes, syntax, named refusals, six-part admissibility check, tier inference, and direct engine spec.
   `Market/FhIRClearingPlan.lean` supplies a canonical Lean-authored rebalance family consumed strictly by
   Rust. The remaining language work is to move the general denotation/compiler into Lean (or prove a
   faithful twin), add reusable product-authoring libraries and certificate backends, and replace the
   intentionally refused PSD/exp/private-operator cases with explicit approved implementations.
   `FhIRGeneralRefinementResidual`.

4. **The GPU-resident pipeline — FOLD CLOSED, WHOLE PROGRAM OPEN.** The arena and bounded resident fold are
   working. The next performance build is a typed resident plan that keeps the outputs of fold,
   histogram/comparison, affine iterations, ct×ct multiplication, and proof-friendly commitment kernels
   on one device allocation until the threshold boundary. `GpuResidentWholeProgramResidual`.

5. **A REAL product cleared privately, end-to-end — TWO HONEST BEACHHEADS BUILT.** The portfolio rebalance
   is fhIR→collective BFV→`T=6` solve→threshold result. The Dark AMM has encrypted reserves and encrypted
   amounts and verifies an exact transition with one secret×secret product. Neither alone closes the full
   product claim: the rebalance uses the earlier n-of-n research custody rather than the authenticated
   `t<n` service; the AMM's masked equality-only rejection is built but still needs malicious share/source
   validity, amount range proofs, and threshold
   dropout-tolerant relin/opening custody (the honest n-of-n relin algebra and authenticated/recoverable
   public control transcript are built, but the upstream opaque-share codec and malicious-share seam remain);
   the fixed N4K4 hiding proof still needs a proof-authoritative ledger/source
   relation rather than trusting FHE and proof witnesses to share an opening. `EndToEndPrivateProductWeldResidual`.

### 2.1 The next central closures

1. Make the hiding proof relation authoritative for the sealed order ledger, and treat fhEgg as an
   untrusted finder unless/until a dedicated BFV same-opening proof binds ciphertexts to those commitments.
2. The masked party-MPC equality-to-`k` decision is now built and candidate-bound. Bind every party's
   arithmetic input to the actual masked ciphertext opening (and authenticate the MPC transport) so a
   malicious party cannot substitute shares while the bad-swap path continues to reveal only refusal.
3. ~~Bind the fixed receipt's range/no-overdraw facts and the BFV wrap bounds to the exact encrypted AMM
   amounts.~~ **DONE AT TIER 1:** the HidingFri relation proves ten-bit amounts and no-overdraw, the issuer
   re-encrypts those same values, and the signed v3 authority claim pins the full parameters plus both caps and refuses an
   underdeclared bound. Remaining: make that composition lattice-ZK/no-single-viewer. Separately, the
   authenticated decrypt-share certificate proves `h = lambda*canonical(c1*s_i) + smudge` with exact RNS
   quotients and the required smudge range; optimize/batch it to interactive latency and prove DKG
   ternary/CBD key shortness.
4. ~~Put the first opaque operations through durable hosted game sessions and receipts—not a separate
   demonstration endpoint.~~ **BUILT FOR THE CURRENT FAMILIES:** strict Dark AMM v3 and the private raid,
   preference, shuffle, and quest operations use the common hosted journal and web/Telegram/Discord
   adapters. Dark AMM v3 now lands real independently session-bound uploads after production-path Telegram
   initData verification and Discord activity-ticket mint/verification, with cross-surface credential and
   replay refusal. Remaining: recursive receipt aggregation, production custody services, and an
   active asset-settlement leg for the AMM game operation.
5. Extend fhIR's Lean-authoritative product library and resident execution plan so another derivative is
   expressed, admitted, and executed rather than hand-wired. The active private box projection and exact
   SDD-to-PSD admission theorem are now real library stones; the general compiler refinement, branch-hidden
   projection, and one whole-program GPU resident schedule remain.
6. ~~Emit `Market.DarkAmmPrivateReceipt` as a fixed descriptor and HidingFri prover~~ **DONE:** public
   `(session,rule,k,oldRoot8,newRoot8)`, private bounded reserves/amounts/blinds, exact nonzero,
   no-overdraw, derived-state, old/new constant-product gates, full Lean `Satisfied2->Accepts`, and a
   hiding-only prover are green. ~~Bind the proof to the exact hosted BFV request and ledger transition.~~
   **DONE AT TIER 1:** the exact re-encryption authority and strict v3 host weld are built. **Remaining:**
   replace issuer-visible witness checking with lattice-ZK/no-single-viewer same-opening while retaining
   the now-bound amount range/no-overdraw and wrap-safety guarantees without disclosing them to any one
   operator.

---

## 3. The discipline this doc exists to enforce

Green isolated stones are useful only when their trust boundaries compose. Before starting a fhEgg unit,
ask: **which public fact becomes unforgeable, which secret stops reaching a viewer, which refused input
fails before mutation, or which player-visible operation becomes real?** This keeps proof engineering,
cryptographic protocol work, solver work, and game integration on the same path.

The one-line vision: **fhEgg is a factory for markets that are private and provably fair; it is mature when
a product can be authored, admitted, found, proved, settled, and recursively verified without any party
learning more than the declared output.**
