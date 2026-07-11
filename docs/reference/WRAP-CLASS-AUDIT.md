# Wrap-class soundness audit of the deployed dregg circuit

Systematic sweep for the **mod-p reconstruction wrap class**: a deployed AIR gate reconstructs or
sums a value whose honest range can reach `≥ p = 2013265921` (BabyBear ≈ 2³¹), but the gate only
forces it `≡ 0 [ZMOD p]`. When the adversary controls the decomposition (bits / limbs / carries /
amount) and no range invariant pins the ℤ value, a p-shifted witness satisfies the mod-p gate while
violating the true-ℤ relation ⟹ forgery.

`p = 2013265921`, `2³⁰ = 1073741824`, `2³¹ = 2147483648`, `p − 2³⁰ = 939524097`, `2p = 4026531842 < 2³²`.

**Discriminant (applied to every candidate below):** does the gate's reconstructed/summed value have
an honest range that reaches `p`, AND does the adversary control the decomposition, AND is there NO
range-check pinning the ℤ value? All three ⟹ SUSPECT. Any one absent ⟹ SAFE (state which).

---

## Verdict summary

| # | Gate | File:line | Class | Verdict |
|---|---|---|---|---|
| 1 | Vault 16-bit product carry | `vault_weld.rs:76` / `VaultSatDescriptor.lean:76` | carry reach `−p` | **A — FIXED (16→15)** |
| 2 | Cap-open 32-bit maskRecon | `trace_rotated.rs:2882` / `DeployedCapOpen.lean:335` | 32-bit, `2p<2³²` | **A — fix pending** |
| 3 | Cross-cell conservation Σδ | `cross_cell_conservation_air.rs:182` / `CrossCellConservation.lean:161` | single-felt prefix sum, `mag<2³⁰`, N≥2 | **A — CONFIRMED (latent, not wired live)** |
| **4** | **Per-cell balance debit / move** | **`trace_rotated.rs:694` / `EffectVmEmitTransfer.lean:224`** | **`post=pre+amt·(1−2dir)`, only AFTER range-checked, amount UNranged** | **⚠⚠ A — NEW, HIGH (deployed core value primitive)** |
| — | dregg-transfer-v1 two-party Σ (unranged `amt` wire 4) | `lean_descriptor_air.rs:2079` | conservation, amt unranged | A-shaped but **test-only, NOT deployed** |
| S1 | Balance-limb decomp (W9) | `columns.rs:225` | `[0,2³⁰)` unique | SAFE-BY-RANGECHECK |
| S2 | Committed-threshold diff | `committed_threshold.rs:49` | 30-bit, bit29=0 ⟹ diff<2²⁹<p/2 | SAFE-BY-RANGECHECK |
| S3 | Presentation expiry diff | `presentation.rs:391` | diff>p/2 ⟹ expired; range wire | SAFE-BY-RANGECHECK |
| S4 | Non-revocation ordering diffs | `non_revocation_witness.rs:83` | `HALF_P_MINUS_1−diff` range-checked 30-bit | SAFE-BY-RANGECHECK |
| S5 | Cap-reshape `gMaskRecon` | `EffectVmEmitCapReshape.lean:496` | 8-bit, `<256` | SAFE-BY-WIDTH |
| S6 | 8-limb hash / 2-limb amount BINDING | `bridge_action_air.rs`, `effect_action_air.rs` | limbs pinned to PI, NO Σ·2ᵏ value gate | SAFE — binding only |
| S7 | Poseidon2 / Merkle / schnorr limb groups | `poseidon2_air.rs`, `merkle_air.rs`, `schnorr_curve.rs` | hash/equality-pinned, carry-chained | SAFE-BY-STRUCTURE |
| R1 | Bilateral-agg cross-side existence Σ | `bilateral_aggregation_air.rs:446` | prefix sum, `balance[last]=0`, over hash fingerprints | SUSPECT-RESIDUAL (not adversary-chosen magnitudes) |

**Count: 5 SAFE-classified families (S1–S7) · 3 confirmed verdict-A (vault fixed, cap-open pending,
cross-cell) · 1 NEW verdict-A (per-cell debit) · 1 test-only A-shape · 1 SUSPECT-RESIDUAL.**

---

## §3 — Cross-cell conservation (target #3): VERDICT A, CONFIRMED

`build_cross_cell_conservation_trace` (`cross_cell_conservation_air.rs:178-190`) computes the running
balance **in the field, single-felt**: `balance += sign * mag` (line 182), and the descriptor pins
`balance[last] = 0` (`lastBalanceZero`, `CrossCellConservation.lean:171`). Each `mag < 2³⁰`
(inherited from the per-cell `NET_DELTA_MAG` range-check; `BAL_BITS = 30`, Lean line 108). The
`balance` column is a **single BabyBear felt summed mod p — NOT multi-limb**, and there is **no
range-check on the running balance** (`d.ranges.is_empty()`, test line 270).

So the AIR forces only `Σδ ≡ 0 [ZMOD p]`. Since `N·2³⁰ ≥ p` at **N = 2** already
(`2·2³⁰ = 2³¹ > p`), the ℤ-sum can equal a nonzero multiple of p. Concrete forgery: two credit rows,
`mag₁ = 1006632961`, `mag₂ = 1006632960` (both `< 2³⁰`), `Σ = p ≡ 0`. The boundary `balance[last]=0`
accepts a turn that **minted ≈ 2·10⁹ units** with no debit and no declared supply row.

The Lean **names this honestly** (`CrossCellConservation.lean` §5.2, lines 320-326): "⚠ WRAP-RESIDUAL
(named, NOT laundered) … mod-p does not pin the ℤ value of the SUM … additionally needs the turn-size
envelope N·2³⁰ < p … or a multi-limb balance. Until that bound is wired, the theorems below state
exactly the cell-level facts the AIR forces." `ccc_last_balance_zero` is scoped to the **cell-level**
residue and carries the caveat — not laundered.

**Note the §5.2 arithmetic is itself wrong:** it writes "N·2³⁰ < p (≈ N < 2³¹ rows)". With `|δ| < 2³⁰`,
`N·2³⁰ < p` forces `N ≤ 1` (p/2³⁰ ≈ 1.875), **not** N < 2³¹. A row-count bound is therefore **not a
viable fix** (a turn touches many cells). The sound fix is a **multi-limb (per-limb + carry) balance
accumulator**, mirroring the note-spend/bridge 2×32-bit approach.

**Mitigating:** ADDITIVE, **not wired** into `turn/src/executor/proof_verify.rs` (headers say so). The
off-AIR pre-flight `BlockConservation::check` uses a Rust `i64` sum (`block_conservation.rs:237`) — no
wrap — but the **light-client path `verify_with_proofs` (line 308) trusts only the AIR proof**, so it
is the surface exposed to the wrap once wired. Severity: HIGH, fix before flip. Verdict **A**.

---

## §4 — NEW: per-cell balance debit / move underflow-wrap. VERDICT A (deployed, HIGH)

This is the **root value-conservation gap** and is **deeper than #3**: it lives in the deployed
rotated per-cell proof — the core primitive every transfer/burn rides.

**The deployed gate** (`trace_rotated.rs:694`, Lean `gBalLo`):
`after.bal_lo = before.bal_lo + amount·(1 − 2·dir) − feeCol`  (dir=1 debit ⟹ `after = before − amount`).
Rust `air.rs:541` form: `transferLo = new − old − amount + 2·dir·amount` (`Spike/EffectVmConstraints.lean:259`).

**The only range teeth** are on the AFTER-state balance limbs:
`ranges := [⟨saCol BALANCE_LO, 30⟩, ⟨saCol BALANCE_HI, 30⟩]` (`EffectVmEmitTransfer.lean:224`;
`#guard ranges.length == 2`). **The `amount` wire is NOT range-checked in-circuit at all** (not in
the ranges list; W9 decomposes only the balance limbs, `columns.rs:302-313`). The trace-gen
`assert!(amt ≤ running_balance)` (`trace.rs:446`) is a **Rust panic, not an AIR constraint** — a
malicious prover crafts the trace directly.

**Why the AFTER-range does NOT force availability.** The design claims (`columns.rs:229`,
`helpers.rs:254`, `EffectVmEmit.lean:401`): "a wrapped underflowed debit `old−amount ≡ p−k` lands
≥ 2³⁰ and has no 30-bit decomposition, so the range-check rejects it." **This is false whenever
`amount − old ∈ (p−2³⁰, 2³⁰) = (939524097, 1073741824)`:** then `post = p − (amount−old)` lands **back
in `[0, 2³⁰)`** and has a valid 30-bit decomposition.

**Concrete forgery witness** (defeats gate + range simultaneously): `old = 1`, `amount = 1006632961`,
`dir = 1`, `post = 1006632961`.
- gate: `post − old + amount = 1006632961 − 1 + 1006632961 = 2013265921 = p ≡ 0 [ZMOD p]` ✓
- range: `post = 1006632961 < 2³⁰` ✓ (valid 30-bit decomposition)
- truth: `amount = 1006632961 ≫ old = 1` — an **over-debit / underflow**. The cell "debits"
  ≈10⁹ while holding 1, and its committed post-balance becomes 1006632961 — **≈10⁹ minted**.

The Spike theorem `underflow_now_impossible` (`EffectVmConstraints.lean:282`) proves rejection only
for the **single** witness `new = p−1` (which is `≥ 2³⁰`); it does **not** generalize, and this
witness (`post < 2³⁰`) evades it.

**The Lean availability theorem launders the gap.** `transferVm_enforces_availability`
(`EffectVmEmitTransferSound.lean:581`) does prove `dir=1 → amount ≤ pre`, but **only under the
hypothesis** `hcanonMove : 0 ≤ pre + amount·(1−2·dir) < p` (lines 586-589). For a debit,
`hcanonMove.1` **is** `0 ≤ pre − amount` — i.e. availability itself. It is declared "the
interpreter-edge's job" (line 578), **enforced by no deployed gate**. My witness fails `hcanonMove`
(`pre − amount < 0`) yet satisfies `satisfiedVm` — so the circuit accepts what the theorem excludes
by assumption. Same structure as CapOpen's carried `reconExact` (MASK doc): a real insecurity priced
into a hypothesis the wire does not pay for.

**Relation to #3:** even a *perfectly fixed* multi-limb cross-cell conservation would **not** catch
this, because the per-cell proof publishes `NET_DELTA = −amount` derived from the *same* wrapped
arithmetic (off by exactly `p` from the true `+post−pre` change). #4 is the primitive; #3 is a second
independent wrap in the aggregation.

**Fix (mirrors vault 16→15):** either (a) range-check `amount` and both balance operands to **≤ 29
bits** so `post − pre + amount ∈ (−2²⁹, 2³⁰) ⊂ (−p, p)` (0 the only multiple of p) — cheapest,
liveness-preserving if 29-bit balances suffice; or (b) add an explicit **borrow-bit availability
gate** (`pre = post + amount` with a boolean borrow and a `pre ≥ amount` comparison via the
`HALF_P_MINUS_1 − diff` range-wire method the comparison gates S2–S4 already use correctly). Then
`transferVm_enforces_availability`'s `hcanonMove` becomes DERIVED, not assumed.

**Burn** rides the same shape: `RotatedKernelRefinementMintBurn.lean:219 burn_availability_forced`
and `EffectVmEmitBurnRunnable` debit `bal_lo` identically; expect the same `hcanonMove`-style
assumption. Treat #4 as covering the whole debit family (Transfer debit, Burn, fee-debit `feeCol`).

---

## SAFE classifications (with the concrete bound)

- **S1 — Balance-limb decomposition (W9-RANGECHECK, `columns.rs:225-237`).** Each AFTER limb is
  decomposed into 30 booleans and recomposed; recomposed value `< 2³⁰ < p` ⟹ the decomposition is
  UNIQUE, no wrap. This is the SAFE half of #4 — it correctly pins the *stored* limb; the #4 gap is
  that it does **not** pin the *move*.
- **S2 — Committed-threshold (`committed_threshold.rs:49-57`).** `COMMITTED_DIFF_BITS = 30`, and the
  gate checks **bit 29 = 0** ⟹ `diff < 2²⁹ = 536870912 < p/2`, proving `value ≥ threshold`
  non-negatively. The header records the prior `31`-bit value as UNSOUND and fixed to 30 — this is the
  **wrap class already closed correctly**. SAFE-BY-RANGECHECK.
- **S3 — Presentation expiry (`presentation.rs:387-392`, 681-683).** `diff = not_after − verifier_h`;
  `diff > p/2 (1006632960)` ⟹ expired. The comparison keys on the half-p split; the accepted branch
  has `diff < p/2 < p`, unique. SAFE-BY-RANGECHECK.
- **S4 — Non-revocation ordering (`non_revocation_witness.rs:52-58, 83`).** Strict-ordering gaps
  `diff = x−L−1`, `R−x−1` with range wires `HALF_P_MINUS_1 − diff` range-checked to 30 bits ⟹
  `diff < (p−1)/2`, pinning `L < x < R` over ℤ. SAFE-BY-RANGECHECK. (`CommittedThresholdRefine.lean:223`
  confirms: "Without it the congruence `diff ≡ value − threshold` admits the classic underflow
  forgery" — i.e. this IS the class, deliberately closed by the range wire.)
- **S5 — Cap-reshape `gMaskRecon` (`EffectVmEmitCapReshape.lean:496`, `MASK_BITS = 8`).** 8-bit sum
  `< 256 < p` ⟹ unique mod-p decomposition. SAFE-BY-WIDTH (cf. MASK doc §5).
- **S6 — Hash/amount BINDING AIRs (`bridge_action_air.rs`, `effect_action_air.rs`).** 32-byte fields
  = 8 limbs and u64 amounts = 2×32-bit limbs are each **boundary-pinned to a PI slot** (`build_descriptor`,
  `effect_action_air.rs:307-314` emits only `PiBinding` + continuity). There is **no `Σ limbᵢ·2ᵏ`
  gate reconstructing a value ≥ p bound mod p** — the limbs are carried side-by-side, never summed
  into a wide congruence. SAFE — not a value reconstruction. (The doc-commented `AlgebraicConstraint::Burn`
  2×32-bit borrow-subtraction, `effect_action_air.rs:78-93`, is **NOT emitted** by the deployed
  descriptor path — see blind-spot list.)
- **S7 — Poseidon2 / Merkle / schnorr limb groups.** Poseidon2 chip absorbs (`poseidon2_air.rs`) and
  Merkle child recomposition (`plonky3_prover.rs:298-327`) are **equality/hash-pinned** — the
  adversary cannot choose a decomposition that both hashes correctly and wraps. Schnorr scalar
  arithmetic (`schnorr_curve.rs:311-378`) is 8×32-bit multiprecision with **explicit carry-out bits
  and `cond_sub_n`** (host-side, carry-chained), not a single mod-p sum. SAFE-BY-STRUCTURE.

---

## SUSPECT-RESIDUAL (flagged, not fully resolved)

- **R1 — Bilateral-aggregation cross-side existence (`bilateral_aggregation_air.rs:446-447`).** Same
  shape as #3: a `windowGate` **balance prefix sum with `balance[last] = 0`**. Difference: the summed
  contributions are **edge fingerprints** (Poseidon2 outputs, ~31-bit, hash-derived), not
  adversary-chosen small magnitudes. A wrap-to-`k·p` forgery would require choosing fingerprints
  summing to a nonzero multiple of p — a collision/structure problem, not a free choice — so this is
  **probably SAFE-BY-STRUCTURE**, but it shares the single-felt-prefix-sum shape and deserves the same
  §5.2-style ℤ-sum note. **What's needed:** confirm the fingerprints are Poseidon2-pinned (not free
  witness columns) and add the wrap caveat to its Lean twin, or a row-count/limb bound if they are free.

---

## Blind spot the migration cannot catch (deployed gates with no faithful Lean twin)

The ℤ→mod-p migration only breaks proofs that **exist**; a deployed reconstruction gate with no
`Dregg2/**` twin is invisible to it. Findings:

- **Coverage is good for value/authority gates:** vault, cap-open, cross-cell, and the
  transfer/burn debit all have faithful Lean twins (that is *why* the migration surfaced #1–#4).
- **`effect_action_air::AlgebraicConstraint::Burn` (borrow-subtraction, `effect_action_air.rs:78-93`)
  is documented in Rust but NOT emitted into the deployed descriptor** (`build_descriptor` emits only
  `PiBinding` + continuity; the borrow gate has no counterpart in the `EffectVmDescriptor2` output).
  The live Burn is `burnBalanceUMem` (`effect_vm_descriptors.rs:860`) / `EffectVmEmitBurnRunnable`.
  This is a **doc↔deployment mismatch**, not a wrap gap (the borrow gate is enforced by neither the
  descriptor nor a twin) — but it means the commented 2×32-bit subtraction analysis is moot for the
  live path; #4 (Burn via `bal_lo`) is the real one.
- **Native-crypto AIRs** (`schnorr_air.rs`, `xmss.rs`, `garbled_air.rs`, `merkle_air.rs`,
  `poseidon2_air.rs`) are structural (signature/hash/comparison), not `Σ·2ᵏ ≥ p` value
  reconstructions, so they are outside this class — but their Lean coverage was **not exhaustively
  verified here**; residual: confirm none introduces a value/authority sum reachable to p.

---

## Prioritized NEW/updated gaps

1. **⚠⚠ #4 per-cell balance debit underflow-wrap — NEW, VERDICT A, HIGH, DEPLOYED.** The core value
   primitive; amount not range-checked; AFTER-range does not force availability; Lean availability
   theorem assumes the gap away (`hcanonMove`). Fix: 29-bit operand range OR explicit borrow/availability
   gate. Covers Transfer debit, Burn, fee-debit.
2. **#3 cross-cell conservation — CONFIRMED VERDICT A (latent).** Multi-limb balance (or the fix is
   moot until wired). The §5.2 row-count-bound suggestion is arithmetically wrong (forces N=1); use a
   multi-limb accumulator.
3. **#2 cap-open maskRecon — VERDICT A, fix pending** (per-16-bit-limb decomposition; MASK doc §4).
4. **R1 bilateral-aggregation prefix sum — resolve** the fingerprint-freedom question and annotate.
5. **dregg-transfer-v1 (test-only)** — not deployed, but its `amt` (wire 4) is unranged; if ever
   promoted, it carries the #4 wrap. Keep test-only or range-check wire 4.
