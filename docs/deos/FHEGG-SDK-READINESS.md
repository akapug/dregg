# fhEgg SDK-Readiness — the honest state, for the next dev spike

*Written 2026-07-16 from a 3-lane code-level analysis (not the docs), corrected at HEAD 2026-07-19 —
"is fhegg actually ready for SDK-level integration?" The plaintext answer is **experimental yes**;
the production-private answer is **not yet**. This file is the actionable why + the roadmap.
Companion: `FHEGG-KERNEL.md` (the model-scope kernel doc — accurate post-de-staling but has two named
doc-residuals, see §5). Everything below is cited to `file:line` at HEAD so the spike can jump straight in.
Grading vocabulary: **PROVEN** (Lean, model-scope) · **WORKING** (real Rust, tested, real perf) ·
**RESEARCH** (compiles, honest prototype — toy params / internal keys / decrypt-at-seam) ·
**NAMED-RESIDUAL** (a build not done) · **ABSENT** (claimed, not in code).*

---

## 0. TL;DR verdict

**fhEgg has a working experimental plaintext Rust SDK surface, but is NOT production-private SDK-ready.**
`sdk/src/fhegg.rs` exposes versioned `clear_book` settlement through `fhegg-solver`, and the SDK's default
features include it. Python/TypeScript bindings and the private FHE/MPC service surface remain absent.

- The all-TFHE **FHE clearing** (`fhe_clear`) remains **minutes-slow and single-key**. A separate
  collective-BFV → masked threshold boundary → party-MPC path now implements the no-single-viewer
  composition locally, but it is not yet an authenticated/malicious-secure SDK service.
- The **plaintext clearing** has versioned, ID-bearing wire types, deterministic per-order allocation,
  settlement verification, an honest CLI, and the experimental Rust SDK adapter. It is callable today,
  but deliberately makes no privacy claim.
- The **verify-not-find loop** (solver → Cert-F certificate → native check) is **real, tested, honest** and
  tested. Its Lean-pinned STARK path works for two fixed registered programs (ring3 and
  market4), not arbitrary live books. A fixed `N<=4,K=4` Dark Bazaar family now moves order
  side/limit/quantity out of public coefficients and into a `HidingFriPcs` witness, commits them with
  a faithful 8-felt root, and publishes only `(session,rule,root8,p*,V*)`; see
  `DARK-BAZAAR-PRIVATE-N4K4.md`. It is operator/prover-visible, not yet no-single-viewer, and its final
  Lean `Satisfied2 → Accepts` integer-decode lift is a named residual.
- The canonical FHE/MPC claim now has a strict Ed25519 threshold-roster verifier and an opt-in market
  co-endorsement weld. It authenticates an exact combined ciphertext/output/settlement claim; it does not
  prove that the ciphertexts open to that settlement's orders or upgrade the local MPC to malicious security.
- fhIR now has one concrete Lean-authoritative family: a proved two-coordinate rebalance plan emits canonical
  bytes that Rust strictly validates and dispatches to the real exact-integer engine. Other fhIR product
  families remain under the broader legacy Rust compiler and are not covered by that cutover.

**Current SDK target:** keep `sdk::fhegg::clear_book` explicitly EXPERIMENTAL / plaintext / demo-scale and
self-checking, then grow it toward the Cert-F CLI shape. Do not relabel the local collective-BFV/MPC path as
a production-private API until authenticated malicious execution, resilient custody, and source-bound
attestation close.

---

## 1. Capability readiness table

| capability | state | SDK verdict | the blocker |
|---|---|---|---|
| `reference_clear` (plaintext uniform-price) | WORKING (rule) | PROTOTYPE | ~~no per-order allocation/fill; no serde/IDs/versioning; price is an abstract bucket index, no tick map~~ ALL THREE CLOSED 2026-07-17 on the SOLVER side: `fhegg-solver::clearing::{allocate,ration}` (verified, Lean-bound) + `fhegg-solver::wire` (versioned/ID-bearing serde types, tick↔bucket map, `Settlement::verify`). `fhegg-fhe`'s own types stay serde-less BY DESIGN (§4.4: don't surface the FHE path) |
| `fhe_clear` (TFHE homomorphic) | RESEARCH (honest) | NOT READY | minutes-slow; single-key (caller decrypts all); no keygen/serialization API; no-viewer decrypt ABSENT |
| collective BFV carry-free fold | RESEARCH pipeline | NOT READY | party-owned n-of-n key custody + retained GPU fold + masked boundary are composed; fhe.rs remains a research dependency and the path is not an authenticated service |
| `mpc_party` output-boundary crossing | RESEARCH PoC | NOT READY | party-thread direct-peer arithmetic ingress and exact A2B/crossing are built; trusted-dealer triples, unauthenticated in-memory channels, n-of-n liveness, semi-honest only |
| solver (PDHG on the circulation LP) | WORKING | usable (plaintext) | CPU path is real; GPU PDHG has measured large-shape wins, but whole private-solver residency and at-scale product throughput are not established |
| Cert-F certificate (emit + native check) | WORKING | usable (plaintext) | prescriptive ε bridge is built; exact integer admission/range bounds remain program-specific |
| Cert-F **verified** (Lean-pinned STARK) | RESEARCH | NOT READY (closer) | full generic emit-soundness + integer admissions for ring3/market4 + real hiding proof path; residual: registration is per-program-constants, so live arbitrary private books need a fixed-shape committed-input relation, not public per-book weights |
| Dark Bazaar private N4K4 | RESEARCH (real hiding proof) | NOT READY (beachhead) | fixed `N<=4,K=4,qty<16`; 8-felt committed private orders + exact output AIR + hiding prover are built; final Lean descriptor→`Accepts` decode/no-wrap theorem, no-viewer producer, ingestion and ledger/allocation weld remain |
| canonical clearing attestation | RESEARCH | NOT READY | strict Ed25519 threshold roster + full claim/settlement co-endorsement and replay teeth are built; ciphertext-opening/source relation, honest-verifier enforcement, and durable replay are not |
| Lean-authored fhIR ClearingPlan | WORKING for one family | PROTOTYPE | exact rebalance-v1 plan/no-wrap/noise proof + canonical artifact + strict Rust interpreter are built; general product compiler/refinement is not |
| sibling certs (CertQp/Eq/Route/Package/Grad) | MIXED | NOT READY | CertQp now has an exact fixed-point KKT checker and fhIR product acceptance uses it (the rounded problem, PSD pinned separately); Eq/Route/Package/Grad remain f64-native, and none yet has Cert-F's general descriptor/STARK chain |
| `fhegg-rtl` | RESEARCH scaffolding | N/A | FPGA netlist-DSL→Verilog spine + a proven full-adder; gates nothing in the software path — ignore for SDK |

---

## 2. What's real, with citations (so the spike trusts the good parts)

- **The uniform-price rule is correct and the f04b-era crossing correction is cut everywhere:**
  `p* = argmax_p min(D[p],S[p])`, lowest-p tie-break via strict-`>` update
  (`fhegg-fhe/src/lib.rs:126-141`); u32 accumulation so legal u16 qtys can't wrap (`lib.rs:109-124`, tested
  `:349-379`); the out-of-domain-ask clamp bug is fixed (`lib.rs:93-102`, tested `:384-404`); the
  counter-witness that breaks the old "largest crossing" heuristic is a test (`lib.rs:337-347`). Solver
  side: `fhegg-solver/src/clearing.rs:143-151`. Lean: `argmaxUpto`/`crossing` vs the distinct
  `balanceCrossing` (`FhEggClearing.lean:205-284`).
- **`fhe_clear` is genuinely homomorphic**, not a shell: aggregation via tfhe-rs `FheUint32::sum`
  (deferred-carry parallel tree-sum, `lib.rs:219-239`); oblivious argmax crossing of K min-selects + K-1
  gt/selects entirely on ciphertexts (`lib.rs:248-267`); decrypts only p*/V* (`lib.rs:272-281`). Real
  tfhe 1.6, default ≥128-bit params.
- **The solver is a real Chambolle–Pock PDHG** on `max wᵀf s.t. Af=0, 0≤f≤c`
  (`fhegg-solver/src/pdhg.rs:137-163`) with a guaranteed-convergent topology-only preconditioner
  (`:126-134`) and an exactness pass `restore_feasibility` routing the conservation residual along a
  max-slack spanning forest so `Af=0` to ~1e-13 (`:335-413`, tested `:503-587`). No `todo!()`/
  `unimplemented!()` in `fhegg-solver/src`. (Honest negative-data note in code: the rayon path is ~30×
  SLOWER than serial, kept deliberately — `pdhg.rs:194-197`.)
- **The certificate emits + checks three ways with negative-polarity tamper tests:** dual feasibility by
  construction `s=(w−Aᵀπ)₊` (`cert.rs:84-106`); f64 tolerance check (`cert.rs:112-150`, loose default
  `1e-3·max(c)` at `:153-156`, `check_strict` 1e-9); the `n+4m+1` linear rows in O(m+nnz A)
  (`air.rs:96-206`, agree-with-checker `:311-321`); exact integer check matching `Market.Certified`
  (`cert_f_air.rs:182-199`); release-hard "minted proof of a bad cert must fail verify" (`cert_f_air.rs:694-715`).
- **The Lean keystone is real + kernel-clean:** `certifies_epsilon_optimal`, `weak_duality`, `gap_nonneg`
  (`metatheory/Market/CertF.lean:113-146`), no `sorry`, axiom-hygiene pinned (`#assert_all_clean`
  `CertF.lean:322`). The range-gadget soundness the old doc deferred is now proved
  (`rangeGadget_forces_range`, `CertFDescriptor.lean §5`). Scope caveat: proven over an ordered ring with
  EXACT arithmetic; the f64 `check()` the plaintext path uses is OUTSIDE that statement (reached only via
  the fixed-point i64 bridge), and there is no executable Lean verifier in the production loop.

---

## 3. The end-to-end gap map (where the composition breaks)

**Plaintext verify-not-find** — REAL all the way, this is the exposable chain:
`order → aggregate` (uniform-price fold+crossing, O(N+K), tested) → `aggregate → solve` (PDHG + restore) →
`solve → certify` (CertF + JSON) → `certify → native verify` (`bin/e2e.rs` runs both polarities;
`bin/fhegg_clear.rs` is a working JSON-in/JSON-out CLI). **This is what an SDK could wrap today.**

**Verified (Lean-pinned STARK) verify** — REAL FOR TWO FIXED REGISTRIES. `prove_cert_f` routes through
`try_cert_f_descriptor`, whose fail-closed registry contains the unit ring3 and the 3-asset/4-order
market4 program (including its prescriptive `ε=2000` budget). The AIR is authored by the total Lean
function `certFDescriptorOf`; `certFDescriptor_emit_sound` is generic over `p : CertFProg`. Integer
interpretation is now closed separately and honestly: the descriptors enforce `π<2²⁸` on both programs
and market4 additionally enforces `f<2²¹`, `s<2¹⁹`; Lean proves the unconditional uniform admissions
`ring3Prog_integerAdmission` and `market4Prog_integerAdmission`, then the direct deployed
`Market.Certified` corollaries. The deliberate descriptor compatibility break changed ring3 from
381/389 to **465 columns / 482 constraints** and market4 from 497/507 to **581 / 602**; both committed
JSON artifacts and exact Lean byte goldens were re-keyed. Old Cert-F proofs/VKs do not verify against
these descriptor bytes. Unregistered public programs remain refused until they choose sufficient
range policies, are emitted, byte-pinned, and entered in the registry.

**Private (witness-hidden) clearing** — REAL FOR THE SAME TWO FIXED REGISTRIES.
`prove_cert_f_zk` / `verify_cert_f_zk` pass the identical Lean-emitted IR-v2 AIR to
`DreggZkStarkConfig` (`HidingFriPcs` with fresh OS-seeded salts, random trace rows, and random FRI
codewords). The focused ring3 test mints and verifies the batch proof, asserts its random commitment
and per-instance random openings are present, and refuses a changed public volume. The old
`prove_cert_f` entry point remains as an explicitly **non-hiding** compatibility path; callers making a
privacy claim must not use it. The construction is built, while the formal simulator theorem for the
complete batch-STARK transcript remains a separate floor. Also, `(A,w,c,ε)` is public descriptor
algebra: if bid values live in `w`, this hides the certificate witness, not those bids.

**No-viewer FHE clearing** — a process-shaped composition now exists:
party-owned n-of-n collective BFV keygen → retained carry-free GPU fold → encrypted party masks →
smudged threshold opening of only `y = m + Σr_i mod t` → each party's private mod-t row → direct-peer
boolean sharing and exact A2B/mod-t reduction → balanced volume-argmax MPC → only `(p*,V*)`.
`threshold_masked_boundary_channels` drives the real masked-boundary rows through `mpc_party.rs`; the
coordinator has no peer-input endpoint and the triple dealer receives public shape only. This closes the
old cleartext decrypt-and-reshare seam and removes any BFV→TFHE scheme switch from the selected architecture.
It is still a **local semi-honest PoC**, not the product property: channels are unauthenticated/in-memory,
triples come from a trusted dealer, all `n` parties must be live, the current BFV custody is n-of-n, and no
malicious-input/share proof or isolated-process deployment exists.

---

## 4. Roadmap — minimum work to SDK-PROTOTYPE (the spike's todo)

Prioritized. The nearest real target is the plaintext verify-not-find engine, NOT the FHE path.

1. **Allocation + wire types (unblocks the plaintext SDK).** ~~Add a per-order fill/allocation rule~~
   **DONE (2026-07-17, both halves).** First half: the per-order allocation EXISTS and is VERIFIED —
   `fhegg-solver/src/clearing.rs::{allocate, ration}` (short side fills fully; long side pro-rata by
   qty with a deterministic largest-remainder pass) with the invariant re-checker
   `Allocation::validate` (shape, per-order cap, IR at `p*`, side sums, conservation at `V*` —
   surfaced as `allocationValid` in `fhegg_uniform`'s JSON), and
   `metatheory/Market/FhEggAllocation.lean` proves the rule model-side: conservation-at-`V*` both
   sides (`allocation_conserves_at_Vstar`), per-order cap (`ration_getD_le`), ±1 pro-rata fairness
   (`ration_fair` / `FairFills`, with `favoritism_refused`/`starvation_refused` teeth), active
   sides = the curves (`activeBidQtys_sum_eq_demand`), all `#assert_all_clean`-pinned; Rust↔Lean held
   together by golden-vector KATs both sides (`lean_workbook_golden_vector` ↔ the `#guard`s).
   ~~REMAINING: serde-stable, versioned, ID-bearing types and a tick↔bucket-index mapping.~~
   **DONE (2026-07-17, second half):** `fhegg-solver/src/wire.rs` — versioned (`version: 1`,
   wrong version + unknown fields REFUSED), ID-bearing `WireOrder`/`WireBook`/`Settlement` with
   `TickGrid` (bucket `j` ↔ integer price `base + j·tick` at `10^priceExponent`; off-grid prices
   REFUSED, never rounded — the rounding would fabricate willingness, same class as the clamp bug),
   fills keyed by order ID + exhaustive, `Settlement::verify` re-derives everything from the book
   (wire-level verify-not-find), qty totals checked-summed (fold cannot wrap), `k` capped. 16 tests
   incl. a golden JSON snapshot pinning the v1 field layout, the Lean workBook golden vector lifted
   onto real prices, and a 300-book seeded property test (conservation + IR at the REAL price +
   determinism, checked from scratch); 3 mutations (ration tie-break, silent price round-down,
   field rename) each verified red-then-restored. Rationing convention is NAMED in the module doc:
   pro-rata-overall on the long side (the Lean-proven rule), not price-priority; changing it means a
   new version. `fhegg-fhe`'s research types deliberately get NO wire surface (§4.4 rule).
   Also note: the fold's out-of-domain-ask clamp bug (an ask with `limit ≥ K` fabricated
   supply in bucket `K-1` → false NON-CONSERVING clearings; the exact bug fhegg-fhe fixed) is now
   ALSO fixed in `fhegg-solver::fold_curves`, regression-tested against the Lean
   `outOfDomainAskBook` witness.
2. **Generalize Cert-F beyond ring-3.** **DONE (2026-07-17), one named residual.**
   (a) `certFDescriptor_emit_sound` is now GENERIC over `p : CertFProg` (not a named family — the
   full quantifier), and STRENGTHENED: the old bundle exposed `g ≥ 0` but never extracted the gap
   GATE, so it never actually touched ε; the generic bundle now carries the gate pins
   `g ≡ ε − (cᵀs − wᵀf)`, `u ≡ c − f`, `d ≡ Aᵀπ + s − w`, `obj ≡ wᵀf`
   (`certFDescriptor_gap_gate_sound`/`_obj_gate_sound`, all `#assert_all_clean`-pinned; field-level
   mod-p congruences under the canonicity hypothesis, as before). The field theorem needs no
   per-program re-proof. Integer registration additionally chooses enforced flow/slack/potential
   ranges and proves the complete weighted residuals cannot wrap; ring3 and market4 now have those
   unconditional admission theorems, while unknown programs fail closed.
   (b) The ε trap is fixed: `from_solution_json_with_epsilon` (cert_f_air.rs) is the PRESCRIPTIVE
   bridge (ε := the registered budget, refuses gap > budget); the registry (`CERT_F_REGISTRY`)
   matches programs including their pinned ε budget; `cert_f_prove` takes `CERT_F_EPSILON`.
   (c) A REAL market shape is registered past the toy: `market4Prog` (`CertFDescriptor.lean` §4b) —
   the 3-asset/4-order DrEX batch under `fhegg_clear`'s nodes=assets/edge-per-order mapping, scale
   100, ε budget 2000 — emitted (`EmitCertFMarket4.lean`), byte-pinned (`CERT_F_MARKET4_GOLDEN` +
   `dregg-cert-f-market4-ir2.json`, drift-gated in `emit_descriptors.py`), and proven END-TO-END
   from a genuine PDHG solve (`stark_proves_real_market4_pdhg_solve`), including a genuinely
   nonzero-gap certificate under budget (mutation-tested: the old descriptive-ε semantics is
   refused, a wrong registered artifact fails the width check, over-budget gap is STARK-refused).
   **RESIDUAL:** registration is still per-program-constants — every distinct batch `(A,w,c,ε)` is
   a new emission+pin, so arbitrary live batches need either a runtime Lean emitter or a verified
   Rust twin of `certFDescriptorOf` (the generic theorem makes that twin meaningful); and the f64→
   integer bridge's entrywise rounding can in principle break exact integer conservation on a
   degenerate solve (the bridge then refuses honestly; a conserving integer-rounding pass is
   unbuilt). Also: `cert_f_descriptor_matches_lean` is now tautological (both sides parse the same
   committed file) since Rust no longer hand-builds the descriptor — a retire-or-repoint candidate.
3. **Re-measure the current FHE circuit.** The `MEASURED-ENVELOPE.md` table is on the SUPERSEDED FheUint16 /
   sum-of-sign-bits circuit; current code is FheUint32 (2× radix) + the heavier argmax crossing (~3× ops/bucket),
   so it is plausibly 2–3× slower than documented. Re-run the current circuit end-to-end before any perf claim.
4. **Harden the selected BFV → output-boundary-MPC trust story (bigger).** The architecture decision and
   process-shaped composition now exist: injected party-owned collective keys, strict ciphertext/share
   framing, masked threshold opening, direct-peer arithmetic ingress, exact A2B/mod-t reduction, and the
   party-thread balanced crossing. Remaining product work is authenticated isolated-process transport,
   roster/replay binding, malicious-share/input validity, dealer-free or auditable triple preprocessing,
   crash/recovery behavior, and a real `t<n` threshold construction. A BFV→TFHE scheme switch is not part
   of this selected path.

**Do NOT** surface `fhe_clear`/the collective-BFV path/`mpc_party` as a production-private SDK until the
remaining items in (4) close. The first is still minutes-slow and single-key; the second is a fast,
party-shaped but local semi-honest research composition.

---

## 5. Doc-residuals in FHEGG-KERNEL.md (partially fixed 2026-07-16)

- **FIXED, then BUILT:** the privacy overstatement was first corrected because `prove_cert_f` used the
  plain `TwoAdicFriPcs`. Cert-F now has a distinct real `prove_cert_f_zk` path through `HidingFriPcs`;
  the plain compatibility entry point remains non-hiding. The complete transcript-simulator theorem is
  still named rather than silently inferred from "not a public input."
- **NAMED-RESIDUAL `FheggEnvelopeDocResidual`:** the §3.1/§6 "measured" FHE envelope cites LITERATURE
  numbers (ePrint 2025/1170, etc.) while the repo's OWN measurements (`fhegg-fhe/MEASURED-ENVELOPE.md`,
  `HBOX-24CORE-ENVELOPE.md`, `ADDITIVE-FOLD-ENVELOPE.md`, `docs/deos/OUTPUT-BOUNDARY-MPC.md`) sit UNCITED,
  and the FheUint16 table is stale (see §4.3). Also the doc drifts CONSERVATIVE — it UNDERSTATES proven
  work: `FhEggRustDenotation.lean` (closes 5 named residuals — would upgrade the crossing claim from "cut
  to" to "proven-denoting"), `FhEggLedgerBinding.lean` + `LedgerRealization.lean` (ledger-realization
  half-discharged since `65d969c52`), `CertFDescriptor.lean`+`CertFGolden.lean`, `AggregateBinding.lean`
  (MSIS PQ binding). Trueing these up is a doc-refresh task for the spike, not urgent.

---

## 6. Provenance

Analysis: workflow `wf_ee966db1-40a` (3 fable lanes, read-only, ~273k tok) — harvest full returns with
`cv workflow ec6d3a9c-be51-4a0a-8cda-a9a6722d3d10 wf_ee966db1-40a --results`. Verdict + doc fix recorded in
`GOAL-STARK-KILL.md` under "fhegg SDK-READINESS VERDICT". This file is the spike's starting point; update it
as the readiness table changes.

---

## 7. ⚠ THE DEPENDENCY QUESTION UNDER §4.4 (raised by ember 2026-07-17, verified from code+registry)

**"is fhe.rs any good? seems old/bad? shouldn't we be using tfhe or our own lean-first?"** — the instinct is
right, and the answer reframes §4.4 from "wire the scheme-switch" to "decide what we build BFV on."

**What it is / its state:** `fhe.rs` (crate `fhe`, + `fhe-math`/`fhe-traits`/`fhe-util`, all `0.1.1`) is a
pure-Rust **BFV** implementation by Tancrède Lepoint — serious, not a toy. Registry check: 10 versions,
`0.1.0-beta.1` … `0.1.0` → **`0.1.1` IS the latest**. So we are NOT pinned to a stale version; the CRATE
stalled at 0.1.1 and never reached 1.0. Research-grade. (Our mirror lags — treat "latest" as a floor.)

**Why tfhe CANNOT replace it (the load-bearing reason):** different schemes, deliberately both used.
`tfhe-rs` (Zama 1.6) = **TFHE**, bit-level, the right tool for the oblivious CROSSING (compares/selects).
`fhe.rs` = **BFV**, SIMD-packed batched addition = the FOLD. Measured
(`ADDITIVE-FOLD-ENVELOPE.md:55-60`): BFV fold **sub-10 ms at N=512** vs **616 s** for the TFHE fold — **~10⁵×**.
tfhe-rs does not do BFV; swapping would vaporize the fold. **That gap is exactly WHY the BFV→TFHE
scheme-switch is a named residual** — it is not incidental, it is the architecture.

**THE REAL PROBLEM (why ember's suspicion lands):** the threshold primitive the entire no-viewer story would
rest on — `mbfv` collective keygen/decryption (Mouchet et al. ePrint 2020/304) — lives INSIDE fhe.rs, and its
**smudging noise is a literal upstream `TODO`** (`mbfv/secret_key_switch.rs:76`: *"TODO this should be
exponential in ciphertext noise!"*). Smudging is what stops decryption shares from leaking the secret key.
Also n-of-n only (no t-of-n). **So shipping production no-viewer on fhe.rs today = inheriting a
known-incomplete SECURITY parameter from an unmaintained 0.1.1 crate.** That is building on sand — the class
this repo deletes. `FheggBfvDependencyResidual`.

**The option set, honestly:**
| option | verdict |
|---|---|
| stay on `fhe.rs` | research-grade, stalled at 0.1.1; threshold path has an upstream security TODO |
| OpenFHE/SEAL via FFI | mature — but **unverified C++ in the TCB**, against the whole ethos (cf. the EverCrypt lesson: never let a "use a real lib" default put unverified C in a verified TCB) |
| `lattigo` (Go) | non-starter for this stack |
| **Lean-first BFV (ours)** | ethos-coherent (we already EMIT circuits from Lean; the repo is a Lean-verified-kernel-first stack) — but NTT/RNS/noise-analysis/param-selection is a BIG build, and **wrong FHE params fail SILENTLY** (no test goes red — the worst failure shape for this repo's discipline) |

**The honest framing:** fhegg's no-viewer path is **gated on a dependency decision nobody has made**, not on
the scheme-switch code. Do NOT ship a privacy claim on fhe.rs's mbfv while its smudging TODO stands. Lean-first
BFV is the coherent END STATE; the open question is whether that is a funded build or a named residual we
simply refuse to ship on top of. **Named, not claimed.**
