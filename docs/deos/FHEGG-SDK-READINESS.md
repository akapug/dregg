# fhEgg SDK-Readiness — the honest state, for the next dev spike

*Written 2026-07-16 from a 3-lane code-level analysis (not the docs) — "is fhegg actually ready for
SDK-level integration?" The answer is **not yet**, and this file is the actionable why + the roadmap.
Companion: `FHEGG-KERNEL.md` (the model-scope kernel doc — accurate post-de-staling but has two named
doc-residuals, see §5). Everything below is cited to `file:line` at HEAD so the spike can jump straight in.
Grading vocabulary: **PROVEN** (Lean, model-scope) · **WORKING** (real Rust, tested, real perf) ·
**RESEARCH** (compiles, honest prototype — toy params / internal keys / decrypt-at-seam) ·
**NAMED-RESIDUAL** (a build not done) · **ABSENT** (claimed, not in code).*

---

## 0. TL;DR verdict

**fhegg is NOT SDK-ready.** It is high-quality research with real crypto on every path and unusually candid
envelope docs — but there is **zero SDK surface** for it today (nothing in `sdk/`, `sdk-py/`, `sdk-ts/`
touches fhegg), and no capability is a callable third-party API:

- The **FHE clearing** (`fhe_clear`) is real homomorphic clearing but **minutes-slow, single-key, no key
  mgmt / serialization**, and the "no-viewer" privacy property is prose + a modeled seam, not code.
- The **plaintext clearing** (`reference_clear`) is a **correct price rule** but has **no per-order
  allocation** and no wire-stable types — you cannot settle a market from its output.
- The **verify-not-find loop** (solver → Cert-F certificate → native check) is **real, tested, honest** and
  is the **single nearest SDK target** — but only as an *experimental plaintext* engine; its "Lean-verified
  / STARK" trust story works end-to-end for exactly **one hardcoded toy program** (a unit 3-cycle).

**Nearest real SDK target:** the `fhegg_clear` plaintext CLI shape (JSON orders in → cleared flows +
Cert-F certificate + native check out), labeled EXPERIMENTAL / plaintext / demo-scale / untrusted-solver-
self-checkable. Even that needs the three items in §4 first.

---

## 1. Capability readiness table

| capability | state | SDK verdict | the blocker |
|---|---|---|---|
| `reference_clear` (plaintext uniform-price) | WORKING (rule) | PROTOTYPE | no per-order allocation/fill; no serde/IDs/versioning; price is an abstract bucket index, no tick map |
| `fhe_clear` (TFHE homomorphic) | RESEARCH (honest) | NOT READY | minutes-slow; single-key (caller decrypts all); no keygen/serialization API; no-viewer decrypt ABSENT |
| `additive::bfv_fold` (BFV carry-free fold) | RESEARCH harness | NOT READY | decrypts internally with a **hard-coded-seed** key; measurement harness, not a pipeline component |
| `mpc` output-boundary crossing | RESEARCH PoC | NOT READY | single-process simulation; trusted-dealer triples; decrypt-and-reshare at the seam; semi-honest only |
| solver (PDHG on the circulation LP) | WORKING | usable (plaintext) | demo-scale perf (n=256/m=4096/T=4000); no verified large-scale numbers; GPU path unexercised |
| Cert-F certificate (emit + native check) | WORKING | usable (plaintext) | ε is descriptive not prescriptive on the bridge; `VALUE_BITS=28` caps amounts < 2^28 |
| Cert-F **verified** (Lean-pinned STARK) | RESEARCH | NOT READY | works for **ring-3 only**; per-program Lean-proof/emit/byte-pin/registry is a named-residual pipeline |
| the 5 sibling certs (CertEq/Route/Qp/Package/Grad) | WORKING (f64) | NOT READY | Rust f64 check only; none have the descriptor/STARK chain Cert-F has |
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

**Verified (Lean-pinned STARK) verify** — REAL FOR RING-3 ONLY. `prove_cert_f` (`cert_f_air.rs:334`) routes
through `try_cert_f_descriptor` (`:310`), which hardcodes `is_registered_ring3_program`
(`:299-305`: `n_nodes==3, edges==[(0,1),(1,2),(2,0)], w==c==[1,1,1], ε==0`) and refuses everything else
("must first be added to `CertFDescriptor.lean`, proved, emitted, byte-pinned, registered"). The committed
descriptor `circuit/descriptors/dregg-cert-f-ir2.json` (389 constraints, traceWidth 381) is the ring-3
instance only. The Lean emit-soundness theorem `certFDescriptor_emit_sound` (`CertFDescriptor.lean:559`) is
stated for `ring3Prog`, not generically over `p : CertFProg`. **Extra trap:** registration requires ε=0,
but the solver bridge `from_solution_json` sets `ε := achieved gap` (generally >0) (`cert_f_air.rs:491`) —
so even a ring-3-shaped real solve is refused unless it lands exactly tight.

**Private (witness-hidden) clearing** — the deployed Cert-F rides the **plain non-hiding PCS**
(`descriptor_ir2::ir2_config` → `TwoAdicFriPcs`; `HidingFriPcs` = 0 hits in that path). Witness-hiding is
`cert_f_air.rs:58-63`'s own "named, not discharged." (The shielded *note-spend* DOES use `HidingFriPcs` via
`prove_dsl_zk` — `shielded/mod.rs:24-25` — but that's a different circuit.) The ZK-leakage claim rests on a
sibling-lane theorem the code marks "named, not discharged" (`cert_f_air.rs:62-64`).

**No-viewer FHE clearing** — no code path exists where encrypted orders go fold → crossing → (p*,V*) with
nobody able to see the curves: the all-TFHE path is single-key (caller decrypts anything, `lib.rs:172-176`
names the threshold-committee decrypt, absent); the BFV+MPC path decrypts at the seam
(`mpc_bench.rs:85-94` literally decrypts + re-shares cleartext); the BFV+TFHE path lacks the scheme-switch
(NAMED-RESIDUAL, `ADDITIVE-FOLD-ENVELOPE.md:86-96`). Each stage is real in isolation; the composition — the
actual product property — is prose plus a modeled seam.

---

## 4. Roadmap — minimum work to SDK-PROTOTYPE (the spike's todo)

Prioritized. The nearest real target is the plaintext verify-not-find engine, NOT the FHE path.

1. **Allocation + wire types (unblocks the plaintext SDK).** Add a per-order fill/allocation rule
   (pro-rata rationing of the marginal bucket) on top of `reference_clear`/`clearing.rs`; add serde-stable,
   versioned, ID-bearing `Order`/`ClearOutcome`/certificate types (today: zero serde in `fhegg-fhe`,
   JSON only on the solver's Cert path). A tick↔bucket-index mapping.
2. **Generalize Cert-F beyond ring-3.** Make `certFDescriptorOf` (already a total fn, `CertFDescriptor.lean:173`)
   the emitted path: prove `certFDescriptor_emit_sound` generically over `p : CertFProg` (not just
   `ring3Prog`), emit + byte-pin descriptors for the real market program shapes, and fix the ε=0-vs-achieved-gap
   mismatch on the bridge so a real (ε>0) solve can register. Until then "verified clearing" is exposable
   only for the toy instance.
3. **Re-measure the current FHE circuit.** The `MEASURED-ENVELOPE.md` table is on the SUPERSEDED FheUint16 /
   sum-of-sign-bits circuit; current code is FheUint32 (2× radix) + the heavier argmax crossing (~3× ops/bucket),
   so it is plausibly 2–3× slower than documented. Re-run the current circuit end-to-end before any perf claim.
4. **Decide the FHE trust story (bigger).** Either wire the BFV→TFHE scheme-switch (no clean Rust impl
   exists today) or commit to the pure-MPC fold with a REAL multi-party runtime (network layer, party
   abstraction, real triples — today it's a single-process semi-honest sim). And a real key API: injected
   keys (not hard-coded seeds), serialized ciphertexts, the threshold-committee decrypt implemented.

**Do NOT** surface `fhe_clear`/`bfv_fold`/`mpc` in an SDK until (4) — they'd ship a minutes-slow, single-key
research prototype as a "private clearing" product.

---

## 5. Doc-residuals in FHEGG-KERNEL.md (partially fixed 2026-07-16)

- **FIXED (`91c3c63bd`):** the privacy OVERSTATEMENT — the doc claimed Cert-F's `(f,π,s)` "live under the
  hiding PCS." The deployed path uses the plain `TwoAdicFriPcs`; witness-hiding is a named unbuilt step.
  Also fixed a conflation attributing the shielded note-spend's hiding to `cert_f_air.rs`.
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
