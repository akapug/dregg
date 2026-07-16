import Dregg2.Circuit.FriVerifier

/-!
# `FriLedger` — the COMPUTABLE, PARAMETRIC FRI soundness ledger, and its `@[export]`

**Why this module exists.** `circuit/tests/fri_params_soundness_budget.rs` used to RE-DERIVE, in
hand-written Rust, the soundness arithmetic this metatheory already models in detail: the capacity
column `numQueries · logBlowup + powBits`, the Johnson column `numQueries · logBlowup / 2 + powBits`,
and — only in prose — the per-fold proximity-gap posture that `FriCorrelatedAgreementSharp` §8 and
`FriArityTransfer` actually PROVE. A hand-written twin drifts from the model it claims to report, and
a re-computation is not a check: it agrees with itself by construction.

This module makes the ledger a LEAN OBJECT that Rust CALLS. `friLedger` is an ordinary total,
computable `Nat`-arithmetic function of a `FriParams`; `@[export dregg_fri_ledger]` compiles it to a
C-ABI entry (`dregg-lean-ffi/src/lean_init.c`'s `dregg_fri_ledger_str` bridge, the same mechanism
`dregg_grain_r3_verify` / `dregg_holding_grant_weight` use). Rust hands it the DEPLOYED knobs and
reports what comes back.

## What is exported, and what is not

**The soundness bound is a `Prop`; a `Prop` cannot be exported.** What is exported is the COMPUTABLE
LEDGER — the numbers. `Dregg2/Circuit/FriLedgerSound.lean` is what JUSTIFIES them: it proves, of THIS
function (not of a restatement of it), that `friLedger`'s `goodCount` is exactly the bound
`FriArityTransfer.good_card_le_of_phase_injective` proves, and that its `perFoldBits` is a
genuine per-fold error exponent at that count (`ledger_perFold_soundness`). The Rust gate reports the
`@[export]`ed numbers; the Lean theorems say why those numbers are true.

## PARAMETRIC, not collapsed

`friLedger` takes the config. Every shipped config (the IR-v2 leaf wrap at arity 8, the v1 production
prover, the gnark ETH-wrap at arity 2) is an INSTANCE of one function, justified by one theorem —
never one headline number quoted for all of them. The arity-8 and arity-2 postures differ by
`log₂ 7 ≈ 2.807` bits and the ledger says so per config.

## The model this ledger reads (and therefore what its numbers mean)

Read `FriCorrelatedAgreementSharp.lean` §8 and `FriArityTransfer.lean` before touching anything here.

* `arity m = 2 ^ maxLogArity` — the deployed p3 fold is a degree-`(m−1)` Lagrange moment curve
  (`fri/src/two_adic_pcs.rs`), NOT an affine line. `FriArityTransfer` is where that is established.
* `foldedDomain |κ| = 2 ^ logBlowup` — the modeled rate-`2^(−logBlowup)` setup folds `m · 2^logBlowup`
  points down to `2^logBlowup` (at `m = 2`, `logBlowup = 6`: `friSetupWrapRate`'s
  `Fin (2^7) → Fin (2^6)`; at `m = 8`: the `|L| = 512 → |κ| = 64` setup built as
  `FriArityFiberDischarge.friSetupK8Wrap`). So
  `|κ|` and the code dimension are BOTH consequences of `logBlowup` — which is why a `logBlowup` move
  silently restates every per-fold theorem about a different object.
* `goodCount = (m − 1) · C(|κ|, 2)` — the arity-generic good-challenge count
  (`good_card_le_of_phase_injective`). At `m = 2` it is §8's `C(64,2) = 2016` EXACTLY
  (`arity2_recovers_capacity_count`); at the deployed `m = 8` it is `7 · 2016 = 14112`.
* `perFoldBits` = the greatest `b` with `goodCount · 2^b < |F|`, `|F| = babyBearP ^ extDeg` — the
  proven per-fold proximity-gap error exponent, `|Good|/|F| < 2^(−perFoldBits)`.
  ⚑ **AT THE NEAR-CAPACITY RADIUS ONLY — see the `perFoldBits` field doc.**
* `johnsonBits` / `capacityBits` — the two query-ledger columns. `capacityBits` rests on the
  up-to-capacity correlated-agreement conjecture, which is **REFUTED** (see the citation block
  below). It is retained as the historical arithmetic and a knob-drift baseline, NOT as a security
  number. `johnsonBits` (list-decoding to `√rate`) is proven for any code — but see `commitBits`:
  as an FRI soundness reading it is the `m → ∞` IDEALISATION and drops a term.
* `commitBits` (`friCommitLedger`) — **the commit-phase error `ε_C` the `johnsonBits` column drops.**

## ⚑ THE CITATIONS, CORRECTED (2026-07-15) — verified against the primary sources

The tree carried *"Kambiré, eprint 2025/2046"* as one work. **It is two papers by different
authors.** Verified from the sources, not from a summary:

* **eprint 2025/2046 is Crites–Stewart**, not Kambiré: Elizabeth Crites & Alistair Stewart
  (Web3 Foundation), *On Reed–Solomon Proximity Gaps Conjectures*, rec. 2025-11-05, rev. 2025-12-19
  (authors/title read from the eprint landing page's own `citation_*` metadata). They prove FALSE
  the BCIKS up-to-capacity correlated-agreement conjecture and WHIR's mutual-correlated-agreement
  conjecture, and separately prove that correlated agreement with small enough error implies RS
  list-decoding. (⚠ We could not fetch the BODY — `eprint.iacr.org` serves 403 to every PDF from
  here — so the METHOD is characterised from the abstract plus BCHKS25's concurrent-work section,
  which reads *"[CS25] also independently discovered the reduction"*, marking the reduction as
  ADDITIONAL to the disproof.)
* **Kambiré is arXiv 2604.09724**: Antonio Kambiré, *Proximity Gaps Conjecture Fails Near Capacity
  over Prime Fields*, 9 Apr 2026 — a counterexample over prime fields. ⚑ **It does not instantiate
  at BabyBear.** His Thm 1 quantifies the prime AFTER the block length (*"there exist infinitely
  many block lengths n … there exists a prime p < n^A with p ≡ 1 (mod n)"*, via a quantitative
  Linnik theorem), so `p` must GROW with `n`; dregg runs a FIXED 31-bit prime. And his radius is
  `δ = (1 − ρ) − Ω(1/log n)` — vanishingly close to CAPACITY, far above the Johnson radius we run at.
* Also refuting, none reaching us: **Diamond–Gruen** eprint 2025/2010 (rate → 0 only) and **BCHKS**
  ECCC TR25-169 Thm 1.6 (constant rate — `ρ = 1/64` exactly at `τ = 4` — but characteristic 2 and a
  random `F₂`-subspace domain).

⚑ **The posture does NOT rest on that escape, and must not be read as doing so.** A conjecture
refuted in general cannot be a security basis for anyone, whatever the field-cardinality technicality
— which is exactly why `capacityBits` is carried only as a drift canary and every claim stands on
`johnsonBits`. Do not "defend" capacity with "no counterexample reaches BabyBear"; it is true and it
is not a defence.

⚑ **`perFoldBits` is the PER-FOLD error, not the whole soundness.** It is one factor of the FRI
soundness product; the query ledger is the other. The ledger reports the columns separately and never
multiplies them into a single headline — `FriLedgerSound.query_ledger_does_not_determine_perFold` is
a theorem, and the ε_C work below **quantitatively vindicates** the law: the two columns move under
different parameters (`perFoldBits` is trace-INVARIANT; `commitBits` falls ~2 bits per trace
doubling), so no single product could track both.

⚑ **THE `M = 1` FIBER BOUND IS DISCHARGED AT EVERY SHIPPED CONFIG** (2026-07-15). Every per-fold
number is derived from `good_card_le_of_phase_injective`, which takes the fiber bound as the
HYPOTHESIS `hΦ` — correctly, since it is arity-generic and mentions no setup. `hΦ` was discharged
only at `m = 2, logBlowup = 6` (§8's `far_fiber_card` + `wrap_fiber_le_one`) and open at `m = 8` and
at `logBlowup = 3`. `Dregg2.Circuit.FriArityFiberDischarge` now builds the arity-`2^k` rate-`2^(−b)`
setups parametrically and PROVES `hΦ` from farness at all six configs
(`phase_injective_of_far`; at the deployed arity 8, `arity8_phase_injective`, for `dOut ≥ 496`), with
a concrete far word at every `(k, b)` to keep it non-vacuous. So the numbers below carry no `hΦ` at
any config the tree ships. (Found on the way: the `Prop` that formerly NAMED the arity-8 obligation
was FALSE — it omitted the farness link — and had no consumers.)

`#assert_axioms` is blind to hypotheses — kernel-clean does not mean hypothesis-free. The `hΦ`
discharge is a theorem, not an axiom-check result.

## Why this module's imports are thin

`@[export]` puts this module in `dregg-lean-ffi/build.rs`'s splice set, so its import closure becomes
archive members that every downstream binary links. The definitions below therefore use CORE `Nat`
operations only — `Nat.log2` (core) rather than Mathlib's `Nat.log`, and `chooseTwo` rather than
`Nat.choose`. `FriLedgerSound.lean` carries the Mathlib-heavy proofs and is NOT spliced; it PINS each
core operation to its Mathlib counterpart (`chooseTwo_eq_choose_two`, `perFoldBits_eq_log`,
`ledgerP_eq_babyBearP`), so the thin definitions are not a second model — they are the same one.
-/

namespace Dregg2.Circuit.FriLedger

open Dregg2.Circuit.FriVerifier (FriParams)

/-- **BabyBear's modulus** `p = 2³¹ − 2²⁷ + 1`, as a literal.

This module is import-thin on purpose (see the header), so it cannot reach
`BabyBearFriField.babyBearP`. `FriLedgerSound.ledgerP_eq_babyBearP` pins the two by `rfl` — the
literal is checked against the field the theorems are stated over, not asserted by a comment. -/
def ledgerP : Nat := 2013265921

/-- `C(n, 2)` by core `Nat` arithmetic. `FriLedgerSound.chooseTwo_eq_choose_two` proves
`chooseTwo n = Nat.choose n 2`, so the count below IS the count the arity theorem bounds. -/
def chooseTwo (n : Nat) : Nat := n * (n - 1) / 2

/-- **THE LEDGER** — the honest per-config numbers.

Each field is a distinct quantity with a distinct justification; they are deliberately NOT collapsed
into one figure. See the module header for what each means and `FriLedgerSound.lean` for the theorem
behind each. -/
structure Ledger where
  /-- The fold arity `m = 2 ^ maxLogArity`. The deployed wrap folds at `8`. -/
  arity : Nat
  /-- The folded domain size `|κ| = 2 ^ logBlowup` — the number of fibres the fold lands on. -/
  foldedDomain : Nat
  /-- `(m − 1) · C(|κ|, 2)` — the good-challenge count `good_card_le_of_phase_injective` proves. -/
  goodCount : Nat
  /-- The greatest `b` with `goodCount · 2^b < babyBearP ^ extDeg`: the PROVEN per-fold
  proximity-gap error exponent at this config (`|Good|/|F| < 2^(−b)`).

  ⚑ **AT THE NEAR-CAPACITY RADIUS, NOT AT THE RADIUS FRI OPERATES AT** (2026-07-15). `goodCount`
  is `good_card_le_of_phase_injective`'s count, whose `M = 1` fiber hypothesis `hΦ` is discharged
  (`FriArityFiberDischarge.arity8_phase_injective`) only for words `dOut ≥ |L| − 2·arity`-far —
  `496` of `512` = **96.9%** at the deployed wrap. FRI's proven argument runs at the **Johnson
  radius** `1 − √ρ` = **87.5%** (`dOut = 448`). `M = 1` is **FALSE** in the band `[448, 496)`:
  `FriJohnsonRadiusGap.deployed_M1_false_at_johnson` exhibits a `448`-far word with a non-injective
  phase map, and `deployed_discharge_threshold_tight` shows `496` cannot be weakened by even one.

  So this column is a TRUE, NON-VACUOUS claim about `96.9%`-far words that does **not** cover the
  operating regime. At the Johnson radius the fiber bound is `M ≤ 7`, and the honest count is
  `FriJohnsonRadiusGap.arity8_johnson_good_card_le`'s `3528` ⟹ **~111 bits** — which is HIGHER only
  because it is a WEAKER claim (it bounds the `dIn = 56` challenge family, not the far larger
  `dIn = 62` one). Different objects; neither dominates. This ledger reports the near-capacity
  reading; the Johnson reading is proved in `FriJohnsonRadiusGap`, not exported here, because its
  `M`/`s` instantiation is only integral at even `logBlowup` (`√ρ·|κ|` is irrational at `lb = 3`)
  and inventing a rounding would be inventing a number. -/
  perFoldBits : Nat
  /-- `numQueries · logBlowup / 2 + powBits` — the Johnson (list-decoding-to-`√rate`) query ledger.
  Integer floor: the reported figure rounds down, never up.

  ⚑ **THIS IS THE `m → ∞` IDEALISATION AND IT DROPS `ε_C`** (2026-07-15). `logBlowup/2` is
  `−log₂ α` in the limit of BCIKS20's `α = √ρ·(1 + 1/2m)`; the paper's actual bound is
  `ε_FRI = ε_C + α^s` (Thm 8.3). The dropped `ε_C` is `friCommitLedger`'s `commitBits`, and at the
  deployed wrap it BINDS: ethSTARK eq. (20) composes them as
  `λ ≥ min{−log₂ ε_C, ζ − s·log₂ α} − 1`, giving **~70**, not this column's `73`. Read this column
  as the query ledger it is, never as "the proven soundness". -/
  johnsonBits : Nat
  /-- `numQueries · logBlowup + powBits` — the capacity query ledger. The conjecture beneath it is
  REFUTED (Crites–Stewart eprint 2025/2046; Kambiré arXiv 2604.09724; see the header). Retained as
  the historical arithmetic and a knob-drift baseline ONLY. -/
  capacityBits : Nat
  deriving Repr, DecidableEq, Inhabited

/-- **THE LEDGER FUNCTION** — one computable function of the config, instantiated at every shipped
config. This is the object `@[export dregg_fri_ledger]` compiles and `FriLedgerSound.lean` proves
about; there is no second copy of this arithmetic anywhere (that was the point of the exercise).

Degenerate inputs are total, not special-cased: at `maxLogArity = 0` the arity is `1`, `goodCount` is
`0`, and `perFoldBits` reads `Nat.log2 (… / 0) = 0` — a `0`-bit posture, which is the honest reading
of "this model says nothing here", not a claim. -/
def friLedger (cfg : FriParams) : Ledger :=
  let m := 2 ^ cfg.maxLogArity
  let kappa := 2 ^ cfg.logBlowup
  let good := (m - 1) * chooseTwo kappa
  let fieldSize := ledgerP ^ cfg.extDeg
  { arity := m
    foldedDomain := kappa
    goodCount := good
    -- The greatest `b` with `good · 2^b < fieldSize`. `good · 2^b < N ↔ 2^b ≤ (N−1)/good`
    -- (`Nat.le_div_iff_mul_le`), and the greatest such `b` is `log₂` of that quotient.
    -- `FriLedgerSound.ledger_perFoldBits_sound` proves this reading of `Nat.log2` is correct.
    perFoldBits := Nat.log2 ((fieldSize - 1) / good)
    johnsonBits := cfg.numQueries * cfg.logBlowup / 2 + cfg.powBits
    capacityBits := cfg.numQueries * cfg.logBlowup + cfg.powBits }

/-! ## ⚑ THE COMMIT-PHASE COLUMN `ε_C` — the term `johnsonBits` drops.

**Read verbatim from BCIKS20 (eprint 2020/654, JACM 10.1145/3614423), Lemma 8.2 / Theorem 8.3
(printed pp. 40–41) — checked against the paper, not against a summary:**

```
ε_FRI = ε_C + α^s ,   α = √ρ·(1 + 1/2m) ,   m ≥ 3
ε_C   = (m+½)⁷·|D⁽⁰⁾|² / (2ρ^{3/2}|F|)  +  (2m+1)(|D⁽⁰⁾|+1)/√ρ · (Σᵢ l⁽ⁱ⁾)/|F|
```

`johnsonBits`' `numQueries·logBlowup/2` is `−s·log₂ α` as `m → ∞`. **So the existing column is the
bottom row of Thm 8.3 at `m → ∞` and omits `ε_C` entirely.** ethSTARK (eprint 2021/582) eq. (20)
composes them: `λ ≥ min{−log₂ ε_C, ζ − s·log₂ α} − 1`.

⚑ **Why this is a REAL column and not a footnote.** `ε_C ∝ |D⁽⁰⁾|²/|F|` — it depends on the TRACE
HEIGHT, which is not an FRI knob at all. So:

* the proven posture is **NOT trace-invariant**: at the deployed wrap `commitBits` reads `71` at
  `|D⁽⁰⁾| = 2^12` and `55` at `2^20` — ~2 bits per trace doubling;
* `ε_C` contains **no `numQueries` and no `powBits`**, so buying queries or the QUERY proof-of-work
  cannot pass it. This is the CEILING: at ext-degree `4` the best any `(q, pow)` can reach is `min`
  over `m ≥ 3` of the two columns, and `commitBits` at `m = 3` caps it (`78` at `|D⁽⁰⁾| = 2^12`).
  The lever that moves the ceiling is `extDeg`, worth exactly `log₂ p ≈ 30.91` bits per degree,
  because `ε_C ∝ 1/|F| = 1/p^extDeg`.

  ⚠ **THE CEILING IS A FACT ABOUT WHAT SHIPS, NOT A THEOREM ABOUT THE PROTOCOL.** plonky3 has a
  SECOND proof-of-work knob that this ledger does not model and `FriParams` does not carry:
  `commit_proof_of_work_bits` (`fri/src/config.rs:18`, distinct from the `query_proof_of_work_bits`
  at `:20`), ground **per fold round, before `β` is drawn** (`fri/src/prover.rs:224`) — i.e. against
  exactly the commit-phase the `ε_C` term bounds. It is omitted from plonky3's own
  `conjectured_soundness_bits` too (`:42-44`). **Every dregg config sets it to `0`**, so the ceiling
  holds for every config we ship — but it is unpriced, and `query_and_pow_cannot_pass_epsC` is
  scoped exactly to what it says: `numQueries` and `powBits`. A named residual, not a swept one.

**Parametric, never a fixture's height.** `logD0` is an INPUT, and that is the point: `ε_C` depends
on the STATEMENT being proved, so a ledger that took only `FriParams` could not express it. The
deployed heights ARE measured — `circuit-prove/tests/fri_trace_height_measure.rs` reads them off real
verified proofs' `BatchProof::degree_bits` — and `FriLedgerSound.ledger_commitBits_at_measured_heights`
reports the column at each config's own: the recursion wrap's `|D⁽⁰⁾| = 2^19` (`WRAP_LOG_CEIL = 2^16`,
FORCED on every fold) gives **`61`**, where the cost grid's 1-effect fixture (`2^12`) gives `71`.
**`61` is the deployed posture.**

## ⚑ WHICH THEOREM THIS COLUMN RESTS ON, AND WHY NOT THE NEWER ONE

**This column is BCIKS20's `ε_C`, and that choice is deliberate.**

**BCSS25** (= BCHKS25 — ECCC TR25-169 and eprint 2025/2055 are the SAME paper, verified: same title,
same authors Ben-Sasson/Carmon/Haböck/Kopparty/Saraf, Nov 2025) improves the Johnson-radius proximity
gap from `O(n²)` to `O(n)` exceptional `z`'s. That attacks exactly the `|D⁽⁰⁾|²` that makes `ε_C`
bind, and it is worth **+17 to +31 bits** at our heights. Its Thm 1.5 carries **no restriction on the
evaluation domain** — a 2-smooth multiplicative coset is a legal `D` — and the "the constants are
brutal at `ρ = 1/64`" worry is **false**: BCIKS20 and BCSS25 carry the SAME `ρ^{-3/2}`, so it cancels
in the ratio and the gain is rate-independent. So the ingredient genuinely fits.

**It is still not our number, for a reason that has nothing to do with the rate:**

* **BCSS25 states no FRI soundness theorem at all.** There is no `ε_FRI` in it. It explicitly DEFERS:
  its error bound *"replaces the O(n²)-bound from [BCI⁺20], used in any round-by-round analysis of FRI
  in the list-decoding regime ([BCI⁺20], see also [HLP24] or [Sta25])"* (§4.2, printed p. 27–28). It
  asserts the consequence; it does not perform the composition.
* **The theorems FRI actually consumes are sketches resting on unreadable sources.** BCIKS20's Lemma
  8.2 applies its Thm 7.2 (weighted correlated agreement over CURVES) once per round. BCSS25's
  curve/weighted versions live in §4, and Thm 4.3's entire proof is *"obtained by plugging in the
  improved bounds in the proof of [Sta25, Theorem 22]"* — and **[Sta25] is a PERSONAL COMMUNICATION**
  (S-two whitepaper), as is **[Hab25]**, which Thm 4.6 rests on. Neither is public.
* **plonky3 does not do it for FRI either.** `p3-whir/src/parameters/soundness.rs:99-123` does
  transcribe BCSS25 verbatim — but it composes it WHIR-style (per-round OOD, sumcheck folding), not
  through FRI's round structure, and its Johnson branch's stated assumption is *mutual* correlated
  agreement (Thm 4.6, the [Hab25] sketch), which Thm 1.5 does not discharge. `p3-fri` still cites
  BCIKS20 (`fri/src/prover.rs:25-26`). And `p3-whir` is **not a dependency of this repo**.

Composing BCSS25's gap into BCIKS20's round structure would be an assembly that is OURS, resting on
a citation we cannot read. **That is the named-carrier pattern this tree refuses**, so the column
reports the bound of the paper that actually proves an `ε_FRI`, and the number is the smaller one.

⚑ **The upgrade is a real theorem to prove, not a citation to copy.** The interface matches exactly
(BCSS25's Cor 4.4 is a drop-in for the object BCIKS20's Thm 7.2 supplies), and routing through
BCSS25's Thm 4.2 — curves, unweighted, derived from the fully-proved §3 — would avoid the [Sta25]
dependency IF the round analysis can be made to accept unweighted curve agreement. Until that is
proved it is not a security number. When it is, it belongs BESIDE this column, not instead of it.

⚑ **The columns stay SEPARATE.** `commitBits` is NOT multiplied or `min`-ed into `johnsonBits` here.
The `min` of eq. (20) is a reading a CALLER may take; the ledger reports the terms. -/

/-- The BCIKS20 commit-phase ledger. Parametric in the trace-derived `|D⁽⁰⁾|` and the proximity
parameter `m` — NEITHER of which is an FRI knob, which is exactly why they are separate inputs. -/
structure CommitLedger where
  /-- `|D⁽⁰⁾| = 2 ^ logD0` — the FRI domain size, i.e. trace height × blowup. NOT an FRI knob. -/
  domainD0 : Nat
  /-- The number of folding rounds `|D⁽⁰⁾| → 2^logBlowup`, `⌈(logD0 − logBlowup)/maxLogArity⌉`. -/
  foldRounds : Nat
  /-- `Σᵢ l⁽ⁱ⁾ = foldRounds · arity` — the localization sum of BCIKS20's second `ε_C` term. -/
  sumArities : Nat
  /-- The numerator of the UPPER bound `ε_C ≤ epsCNum / (2^8 · |F|)`. Every rounding in it rounds
  `ε_C` UP (⟹ `commitBits` DOWN), never the reverse. -/
  epsCNum : Nat
  /-- **`commitBits`** — the greatest `b` with `ε_C ≤ 2^(−b)`, i.e. with
  `epsCNum · 2^b < 2^8 · |F|`. A LOWER bound on `−log₂ ε_C`, because `epsCNum` over-estimates. -/
  commitBits : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `⌈a / b⌉` on `Nat` (and `0` at `b = 0`, total). Used for the round count and the half-integer
`ρ` exponents: rounding those UP over-estimates `ε_C`, which is the conservative direction. -/
def ceilDiv (a b : Nat) : Nat := if b = 0 then 0 else (a + b - 1) / b

/-- **THE COMMIT-PHASE LEDGER.** With `ρ = 2^(−logBlowup)`:
`1/(2ρ^{3/2}) = 2^(3·lb/2 − 1)` and `1/√ρ = 2^(lb/2)`, and `(m+½)⁷ = (2m+1)⁷/2⁷`, so

  `term₁ = (2m+1)⁷·|D⁰|²·2^(3lb/2) / (2^8·|F|)` ,  `term₂ = (2m+1)(|D⁰|+1)·Σl·2^(lb/2) / |F|`
  `ε_C = term₁ + term₂ ≤ (A₁ + 2^8·A₂) / (2^8·|F|) =: epsCNum / (2^8·|F|)`.

The `2^8` common denominator keeps everything in `Nat` with **no division in the numerator** — a
`Nat` division would truncate DOWN, shrinking `ε_C` and INFLATING the bits, which is the one
direction a soundness ledger must never round. The only lossy step is `⌈·⌉` on the half-integer
exponents `3lb/2` and `lb/2` (odd `logBlowup` only — the deployed `lb = 6` is exact), and it rounds
`ε_C` UP. -/
def friCommitLedger (cfg : FriParams) (logD0 bciksM : Nat) : CommitLedger :=
  let m := 2 ^ cfg.maxLogArity
  let d0 := 2 ^ logD0
  let rounds := ceilDiv (logD0 - cfg.logBlowup) cfg.maxLogArity
  let sumL := rounds * m
  let twoMp1 := 2 * bciksM + 1
  -- ⌈3·lb/2⌉ and ⌈lb/2⌉ — rounded UP, so `ε_C` is over-estimated.
  let e3 := ceilDiv (3 * cfg.logBlowup) 2
  let e1 := ceilDiv cfg.logBlowup 2
  let a1 := twoMp1 ^ 7 * (d0 * d0) * 2 ^ e3
  let a2 := twoMp1 * (d0 + 1) * sumL * 2 ^ e1
  let num := a1 + 2 ^ 8 * a2
  let den := 2 ^ 8 * ledgerP ^ cfg.extDeg
  { domainD0 := d0
    foldRounds := rounds
    sumArities := sumL
    epsCNum := num
    commitBits := Nat.log2 ((den - 1) / num) }

/-! ## The `@[export]` FFI entry (Rust → Lean), running the computable ledger.

Mirrors the repo's established string-wire export mechanism (`Dregg2.Grain.R3Verify.r3VerifyFFI`,
`Dregg2.Bridge.ProofOfHoldings.grantWeightFFI`): a `String → String` `@[export]` plus a plain-C
bridge in `dregg-lean-ffi/src/lean_init.c`. Rust is the thin marshaller; the NUMBERS are Lean's. -/

/-- Sanity bounds on the wire so a malformed/hostile knob set cannot make `ledgerP ^ extDeg` or
`2 ^ logBlowup` blow up the caller. These are WIRE guards, not soundness claims: every shipped config
sits far inside them (`extDeg = 4`, `logBlowup ∈ {3, 6}`, `maxLogArity ∈ {1, 3}`). Outside the window
the export refuses (empty output) rather than compute for an unbounded time. -/
def knobsInWindow (cfg : FriParams) : Bool :=
  cfg.extDeg ≤ 16 && cfg.logBlowup ≤ 24 && cfg.maxLogArity ≤ 8 &&
    cfg.numQueries ≤ 4096 && cfg.powBits ≤ 256 && cfg.logFinalPolyLen ≤ 24

/-- The window for the `ε_C` inputs. `3 ≤ bciksM` is **not** a wire guard — it is BCIKS20 Thm 8.3's
own hypothesis (`m ≥ 3`). Outside it the formula is not the paper's, so the export REFUSES rather
than returning a number no theorem backs. `maxLogArity ≥ 1` keeps the round count meaningful. -/
def epsCInWindow (cfg : FriParams) (logD0 bciksM : Nat) : Bool :=
  3 ≤ bciksM && bciksM ≤ 64 && logD0 ≤ 40 && cfg.logBlowup ≤ logD0 && 1 ≤ cfg.maxLogArity

/-- **The C-ABI entry.** Wire grammar:

  * in:  `"logBlowup numQueries powBits maxLogArity logFinalPolyLen extDeg logD0 bciksM"` (eight
    decimal `Nat`s — the five deployed knobs, the extension degree that fixes `|F|`, and the two
    `ε_C` inputs that are NOT FRI knobs: the FRI domain size `|D⁽⁰⁾| = 2^logD0` (trace height ×
    blowup) and BCIKS20's proximity parameter `m ≥ 3`).
  * out: `"arity foldedDomain goodCount perFoldBits johnsonBits capacityBits commitBits"` (seven
    decimal `Nat`s — the `Ledger` fields in declaration order, then `CommitLedger.commitBits`).
  * `""` (empty) — fail-closed for a malformed wire, a knob set outside `knobsInWindow`, or `ε_C`
    inputs outside `epsCInWindow` (notably `m < 3`, which is BCIKS20's own hypothesis).

`logD0` and `bciksM` are on the wire rather than in `FriParams` because they are **not FRI knobs**:
`|D⁽⁰⁾|` is a property of the STATEMENT being proved (the trace height), and `m` is a parameter of
the ANALYSIS. Folding them into `FriParams` would have implied the deployed config determines
`ε_C`, and the whole point of this column is that it does not.

`logFinalPolyLen` is READ and echoed into no ledger column, because it enters no soundness formula in
this tree. That is deliberate and is the honest answer: the export does not invent a number for it.
It stays on the wire so the Rust pin passes the WHOLE deployed knob set through one boundary. -/
@[export dregg_fri_ledger]
def friLedgerFFI (input : String) : String :=
  match (input.splitOn " ").filterMap String.toNat? with
  | [lb, nq, pw, mla, lfpl, ed, logD0, bciksM] =>
      let cfg : FriParams :=
        { logBlowup := lb, numQueries := nq, powBits := pw, maxLogArity := mla,
          logFinalPolyLen := lfpl, extDeg := ed }
      if knobsInWindow cfg && epsCInWindow cfg logD0 bciksM then
        let l := friLedger cfg
        let cl := friCommitLedger cfg logD0 bciksM
        s!"{l.arity} {l.foldedDomain} {l.goodCount} {l.perFoldBits} {l.johnsonBits} \
{l.capacityBits} {cl.commitBits}"
      else ""
  | _ => ""

end Dregg2.Circuit.FriLedger
