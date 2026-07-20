import Dregg2.Circuit.FriLedgerSound

/-!
# `FriDeployedHeightPairing` — WHICH `(config, |D⁽⁰⁾|)` pair is the deployed one, and what it reads

`FriLedger.friCommitLedger` is parametric in **two** inputs that are not FRI knobs: the config and
the trace-derived domain size `logD0`. That parametricity exists, in its own docstring's words, so
that "pairing a config with another config's height" cannot happen. **It happened anyway**, and this
file localizes it, corrects it, and refutes the two numbers the tree currently carries.

## ⚑ SCOPE — read this before quoting any number below

Every theorem here is an **arithmetic** statement about `friCommitLedger`'s own formula at a given
`(cfg, logD0, m)`. **None of them is a soundness claim against an adversary.** There is no prover
strategy, no interaction, no random-oracle query bound, and no `ε` quantified over efficient or
`Q`-bounded provers anywhere in this file or in the ledger it reads. `commitBits` is
`⌊−log₂⌋` of a transcribed **upper bound on BCIKS20's `ε_C`** — an information-theoretic
round-by-round term from a **cited, unmechanized** paper (eprint 2020/654 Lemma 8.2 / Thm 8.3),
whose body this tree has never been able to fetch. The FRI extraction guarantee the apex actually
consumes (`FriLdtExtractV3`) is **assumed**, carried as a hypothesis, and **not discharged by any of
these bits**. So the honest reading of every number below is: *this is what our own calculator says
at the parameters we actually ship* — a **knob-ledger reading**, never "the system has N bits".

What this file therefore CAN and DOES establish is a real defect: the calculator was **evaluated at
the wrong point**, and the two numbers in circulation are the readings of configurations the
deployed prover does not run.

## The deployed pairing, from the Rust

The accumulator's running aggregation — the step that runs on **every** fold — binds, in ONE
`prove` call (`circuit-prove/src/accumulator.rs`, `Accumulator::accumulate`):

* `let config = ir2_leaf_wrap_config();` — `circuit-prove/src/ivc_turn_chain.rs:1028`, built by
  `create_recursion_config_for_inner_fri(IR2_INNER_LOG_BLOWUP = 6, …)`. That constructor calls
  `create_recursion_config_with_fri`, whose `log_blowup` lands in the `FriParameters` handed to
  `MyPcs::new` — **the PCS that MINTS the proof**, not merely an in-circuit verifier parameter.
  So the running fold's tables are committed at **`log_blowup = 6`**.
* `let fold_params = if self.wrap_enabled { wrap_params() } …` — `accumulator.rs:242`, which sets
  `min_trace_height = 1 << WRAP_LOG_CEIL` with `WRAP_LOG_CEIL = 16` (`accumulator.rs:236`), a FLOOR
  applied to every running-proof table. `wrap_enabled` is `true` in `Accumulator::genesis`.

Hence `|D⁽⁰⁾| = trace_height × blowup = 2^16 · 2^6 = 2^22`, and the config is the **arity-2**,
`logBlowup = 6` knob set — `FriLedgerSound.ir2LeafWrapRotatedConfig` (arity 2 because
`INNER_FRI_MAX_LOG_ARITY = 1`, `plonky3_recursion_impl.rs:116`).

`create_recursion_config` (`logBlowup = 3`) is **not on that path**.

## The two errors, which agreed with each other

The tree's standing pair is `(recursionConfig, logD0 = 19)`. Both halves are wrong, and they are
wrong **consistently**, which is why the pair looked coherent and survived review:

1. **config** — `FriLedgerSound.ledger_commitBits_at_measured_heights` row 4 uses `recursionConfig`
   (`logBlowup = 3`), a config the wrap path never constructs.
2. **height** — `circuit-prove/tests/fri_trace_height_measure.rs:133` computes
   `DEPLOYED_WORST_LOG_D0 = WRAP_LOG_CEIL + RECURSION_FRI_LOG_BLOWUP = 16 + 3 = 19`, adding the
   trace-height floor of the `lb = 6` path to the blowup of the `lb = 3` config. ⚑ It is also
   **not a measurement**, despite the surrounding prose calling it MEASURED: it is a sum of two
   compile-time constants.

Fix only (1) — keep `logD0 = 19` — and the reading is `57`. That is exactly what
`docs/reference/PROVEN-120-CONFIG.md` §3 does: it derives `2^16 · 2^6 = 2^22` **in its own
sentence**, then reports the number for `2^19`. Its correction is **half-applied**.

Fix both and the reading is **51**. -/

namespace Dregg2.Circuit.FriDeployedHeightPairing

open Dregg2.Circuit.FriLedger
open Dregg2.Circuit.FriLedgerSound
open Dregg2.Circuit.FriVerifier (FriParams ir2LeafWrapConfig)

/-! ## §1. The Rust constants, mirrored, so the pairing is an OBJECT and not a literal

The whole defect was a literal (`19`) typed into a theorem with no link to the constants that
produce it. These defs restore the link: the height is *derived* from the blowup of the config it is
paired with, so a future arity/blowup move cannot silently leave the height behind. -/

/-- `accumulator.rs:236` — the `min_trace_height` floor the wrap applies to EVERY running-proof
table on every fold. -/
def wrapLogCeil : Nat := 16

/-- `ivc_turn_chain.rs:955` `IR2_INNER_LOG_BLOWUP` — the blowup of the PCS that mints the running
fold, i.e. of `ir2_leaf_wrap_config()`. -/
def ir2InnerLogBlowup : Nat := 6

/-- `plonky3_recursion_impl.rs:94` `RECURSION_FRI_LOG_BLOWUP` — the blowup of
`create_recursion_config`, which the wrap path does NOT call. -/
def recursionFriLogBlowup : Nat := 3

/-- **THE DEPLOYED DOMAIN.** `WRAP_LOG_CEIL + IR2_INNER_LOG_BLOWUP`, i.e. the floored trace height
times the blowup the running fold is actually committed at. -/
def deployedWrapLogD0 : Nat := wrapLogCeil + ir2InnerLogBlowup

/-- What `fri_trace_height_measure.rs:133` computes: the same floor, but with the OTHER config's
blowup. -/
def treeAssertedLogD0 : Nat := wrapLogCeil + recursionFriLogBlowup

/-- BCIKS20 Thm 8.3's proximity parameter, as the ledger's callers instantiate it. A CHOICE about
how sharply the paper is read, not a property of anything shipped. -/
def bciksM : Nat := 7

theorem deployedWrapLogD0_eq : deployedWrapLogD0 = 22 := rfl

theorem treeAssertedLogD0_eq : treeAssertedLogD0 = 19 := rfl

/-- ⚑ **The height and the config must move together — the arithmetic of the mis-pairing.**
The two heights differ by exactly the blowup gap `6 − 3`, so pairing the `lb = 6` config with `19`
is off by 3 doublings of the domain. `ε_C ∝ |D⁽⁰⁾|²`, so 3 doublings cost ~6 bits — which is
precisely the `57 → 51` gap `deployed_wrap_is_not_the_proven120_number` exhibits. -/
theorem the_height_gap_is_the_blowup_gap :
    deployedWrapLogD0 - treeAssertedLogD0 = ir2InnerLogBlowup - recursionFriLogBlowup ∧
      deployedWrapLogD0 - treeAssertedLogD0 = 3 := by
  constructor <;> rfl

/-! ## §2. The bracket lemma

`FriLedgerSound`'s own `commitBits_eq_of_bracket` is `private`, so it is re-derived here rather than
re-implemented differently. `Nat.log2` is well-founded-recursive and does not reduce in the kernel,
so `decide` cannot see these; and `native_decide` would drag `Lean.ofReduceBool` plus the whole
compiler into the trust base of a soundness column, which is exactly the wrong place for it. -/

private theorem commitBits_bracket (cfg : FriParams) (logD0 m b : ℕ)
    (h₁ : 2 ^ b ≤ (2 ^ 8 * ledgerP ^ cfg.extDeg - 1) / (friCommitLedger cfg logD0 m).epsCNum)
    (h₂ : (2 ^ 8 * ledgerP ^ cfg.extDeg - 1) / (friCommitLedger cfg logD0 m).epsCNum
        < 2 ^ (b + 1)) :
    (friCommitLedger cfg logD0 m).commitBits = b := by
  show Nat.log2 _ = b
  rw [log2_eq_log_two]
  exact Nat.log_eq_of_pow_le_of_lt_pow h₁ h₂

/-! ## §3. THE CORRECTED DEPLOYED READING -/

/-- **⚑ THE DEPLOYED COMMIT COLUMN READS `51`.**

At the pair the Rust actually runs — `ir2_leaf_wrap_config()` (arity 2, `logBlowup = 6`) at
`|D⁽⁰⁾| = 2^(16+6) = 2^22` — BCIKS20's `ε_C` ledger reads **51 bits**.

⚑ Scope, again, because this is the number people will quote: this says the calculator outputs 51
at the deployed knobs. It does **not** say a `Q`-bounded prover forges with probability `≤ 2⁻⁵¹`;
no theorem in this tree says that about anything, because there is no adversary object. -/
theorem deployed_wrap_commitBits :
    (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 bciksM).commitBits = 51 := by
  refine commitBits_bracket _ _ _ 51 ?_ ?_ <;>
    norm_num [friCommitLedger, ceilDiv, ledgerP, ir2LeafWrapRotatedConfig, deployedWrapLogD0,
      wrapLogCeil, ir2InnerLogBlowup, bciksM]

/-! ## §4. THE REFUTATIONS — both circulating numbers are readings of something else -/

/-- **⚑ REFUTED: the deployed reading is not `61`.** `61` is the tree's standing figure
(`FriLedgerSound.ledger_commitBits_at_measured_heights` row 4,
`recursion_is_weakest_on_the_commit_column_too`, and `fri_params_soundness_budget.rs`'s
"`log_d0 = 19 (MEASURED deployed WORST) … 61 bits ← the real deployed posture`"). It is a **true
reading of `recursionConfig` at `2^19`** — a config/height pair the wrap path never realizes. -/
theorem deployed_wrap_is_not_61 :
    (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 bciksM).commitBits ≠ 61 := by
  rw [deployed_wrap_commitBits]; decide

/-- **⚑ REFUTED: the deployed reading is not `57` either** — the figure
`docs/reference/PROVEN-120-CONFIG.md` §3 substitutes for `61`. `57` fixes the CONFIG (to the
`logBlowup = 6` engine) but keeps the height `19` that was computed from the OTHER config's blowup,
so it is the reading of the right config at the wrong domain. See
`the_proven120_correction_is_half_applied`. -/
theorem deployed_wrap_is_not_the_proven120_number :
    (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 bciksM).commitBits ≠ 57 := by
  rw [deployed_wrap_commitBits]; decide

/-- **BOTH-TRUTH TOOTH for `61`.** The tree's number is not nonsense — it is exactly right about
`recursionConfig` at `2^19`. Localizing the error as a MIS-PAIRING (rather than as bad arithmetic)
is the whole content of this file, so it is stated as a theorem and not as prose. -/
theorem the_61_is_the_recursion_config_reading :
    (friCommitLedger recursionConfig treeAssertedLogD0 bciksM).commitBits = 61 := by
  refine commitBits_bracket _ _ _ 61 ?_ ?_ <;>
    norm_num [friCommitLedger, ceilDiv, ledgerP, recursionConfig, treeAssertedLogD0,
      wrapLogCeil, recursionFriLogBlowup, bciksM]

/-- **⚑ THE `PROVEN-120-CONFIG.md` §3 CORRECTION IS HALF-APPLIED — the witness.**

That section derives the deployed domain **correctly and explicitly** (*"`WRAP_LOG_CEIL` floors
tables that are minted at `lb = 6` ⟹ `2^16 · 2^6 = 2^22`"*), then concludes *"the deployed posture
is 57"*. `57` is the `logBlowup = 6` engine's reading at `2^19` — the height it had just finished
refuting. At the `2^22` it derived, the same engine reads `51`.

This theorem exhibits both readings of the SAME config, so the gap cannot be attributed to a
different knob set: only `logD0` moves. -/
theorem the_proven120_correction_is_half_applied :
    (friCommitLedger ir2LeafWrapRotatedConfig treeAssertedLogD0 bciksM).commitBits = 57 ∧
      (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 bciksM).commitBits = 51 ∧
      treeAssertedLogD0 ≠ deployedWrapLogD0 := by
  refine ⟨?_, deployed_wrap_commitBits, by decide⟩
  refine commitBits_bracket _ _ _ 57 ?_ ?_ <;>
    norm_num [friCommitLedger, ceilDiv, ledgerP, ir2LeafWrapRotatedConfig, treeAssertedLogD0,
      wrapLogCeil, recursionFriLogBlowup, bciksM]

/-- **⚑ THE FIXTURE FLATTERED THE COLUMN BY 20 BITS, NOT 10.** `COMMIT_FLOOR_BITS = 71` in
`fri_params_soundness_budget.rs` gates the `2^12` cost-grid fixture. The deployed reading is `51`.
The gate's own docstring states the gap as "~10 bits" (`71 → 61`); the true gap is **20**. -/
theorem the_fixture_gap_is_twenty_bits :
    (friCommitLedger ir2LeafWrapRotatedConfig 12 bciksM).commitBits = 71 ∧
      (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 bciksM).commitBits = 51 ∧
      71 - 51 = 20 := by
  refine ⟨?_, deployed_wrap_commitBits, by decide⟩
  refine commitBits_bracket _ _ _ 71 ?_ ?_ <;>
    norm_num [friCommitLedger, ceilDiv, ledgerP, ir2LeafWrapRotatedConfig, bciksM]

/-! ## §5. THE PENDING ARITY FLIP DOES NOT MOVE THIS COLUMN

`INNER_FRI_MAX_LOG_ARITY = 1` is documented in-tree as a PROBE, and `E2` reports GO on flipping it
`1 → 3` (arity 2 → 8). That flip DOES move `perFoldBits` (`112 → 109`,
`FriLedgerSound.arity8_costs_seven_times_arity2_at_logBlowup6`). It is worth knowing, before the
flip lands, whether it also moves the commit column — because if it did, the corrected deployed
number would have a shelf life of one commit. -/

/-- **⚑ THE COMMIT COLUMN IS ARITY-BLIND AT THE DEPLOYED PAIRING.** Same `logBlowup = 6`, same
`|D⁽⁰⁾| = 2^22`, arity 2 vs arity 8: both read `51`.

The arity enters `ε_C` only through `Σᵢ l⁽ⁱ⁾ = foldRounds · arity`, which sits in the SECOND term;
term₁ (`(2m+1)⁷·|D⁰|²·2^{3lb/2}`) dominates at these parameters, so the arity change is invisible
after the `⌊log₂⌋`. ⚑ Consequence: **the `51` survives the E2 arity flip.** It is a fact about the
blowup and the height, not about the fold arity — unlike `perFoldBits`, which is the reverse. -/
theorem arity_flip_does_not_move_the_commit_column :
    (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 bciksM).commitBits =
        (friCommitLedger ir2LeafWrapConfig deployedWrapLogD0 bciksM).commitBits ∧
      (friCommitLedger ir2LeafWrapConfig deployedWrapLogD0 bciksM).commitBits = 51 := by
  have h8 : (friCommitLedger ir2LeafWrapConfig deployedWrapLogD0 bciksM).commitBits = 51 := by
    refine commitBits_bracket _ _ _ 51 ?_ ?_ <;>
      norm_num [friCommitLedger, ceilDiv, ledgerP, ir2LeafWrapConfig, deployedWrapLogD0,
        wrapLogCeil, ir2InnerLogBlowup, bciksM]
  exact ⟨by rw [deployed_wrap_commitBits, h8], h8⟩

/-- **⚑ AND THE TWO COLUMNS SPLIT ON THE FLIP — the two-column law, at the deployed pairing.**
The arity flip moves `perFoldBits` by 3 bits and `commitBits` by 0. Neither column is a function of
the other, so there is no single "the arity flip costs N bits" figure. -/
theorem the_flip_moves_perFold_only :
    (friLedger ir2LeafWrapRotatedConfig).perFoldBits = 112 ∧
      (friLedger ir2LeafWrapConfig).perFoldBits = 109 ∧
      (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 bciksM).commitBits =
        (friCommitLedger ir2LeafWrapConfig deployedWrapLogD0 bciksM).commitBits :=
  ⟨rotatedLeafWrap_ledger_perFoldBits, wrap_ledger_perFoldBits,
    arity_flip_does_not_move_the_commit_column.1⟩

/-! ## §6. WHAT THE COMPOSITE READS, AND WHY IT IS STILL NOT A SECURITY LEVEL -/

/-- **⚑ THE COMMIT COLUMN BINDS AT THE DEPLOYED PAIRING, BY 22 BITS.**

ethSTARK (eprint 2021/582) eq. (20) composes the two columns as
`λ ≥ min{−log₂ ε_C, ζ − s·log₂ α} − 1`. At the deployed pair that `min` is `min{51, 73} = 51`, so
the composite reads **50** — and the Johnson column (`73`) is 22 bits of slack that no one can
spend. Buying queries cannot help: `ε_C` contains no `numQueries` and no `powBits`
(`FriLedgerSound.query_and_pow_cannot_pass_epsC`). Only `extDeg` moves it.

⚑ This `50` is a COMPOSITION OF TWO LEDGER READINGS, performed here in `Nat`. It is not a proof
that the protocol has 50 bits of anything against anybody. -/
theorem the_commit_column_binds_at_the_deployed_pairing :
    (friLedger ir2LeafWrapRotatedConfig).johnsonBits = 73 ∧
      (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 bciksM).commitBits = 51 ∧
      min 51 73 - 1 = 50 := by
  refine ⟨by norm_num [friLedger, ir2LeafWrapRotatedConfig], deployed_wrap_commitBits, by decide⟩

/-- **⚑ NON-VACUITY / MUTATION CANARY.** A ledger correction is worthless if the bracket lemma would
have accepted any number. These four readings are pairwise distinct and each is pinned by its own
two-sided bracket, so a single wrong digit in `friCommitLedger` reds at least one of them. -/
theorem the_four_readings_are_distinct :
    (friCommitLedger ir2LeafWrapRotatedConfig 12 bciksM).commitBits = 71 ∧
      (friCommitLedger ir2LeafWrapRotatedConfig treeAssertedLogD0 bciksM).commitBits = 57 ∧
      (friCommitLedger recursionConfig treeAssertedLogD0 bciksM).commitBits = 61 ∧
      (friCommitLedger ir2LeafWrapRotatedConfig deployedWrapLogD0 bciksM).commitBits = 51 := by
  exact ⟨the_fixture_gap_is_twenty_bits.1, the_proven120_correction_is_half_applied.1,
    the_61_is_the_recursion_config_reading, deployed_wrap_commitBits⟩

/-! ## §7. Axiom hygiene

`#assert_axioms` checks the AXIOM closure. It is **blind to hypotheses**, and it is blind to
`sorry`-free-ness of the *modeling* — these theorems are kernel-clean statements about a formula
that was transcribed from a paper we could not fetch. Kernel-clean here means "the arithmetic is
right", never "the security claim is discharged". -/

#assert_axioms deployed_wrap_commitBits
#assert_axioms deployed_wrap_is_not_61
#assert_axioms deployed_wrap_is_not_the_proven120_number
#assert_axioms the_proven120_correction_is_half_applied
#assert_axioms the_61_is_the_recursion_config_reading
#assert_axioms arity_flip_does_not_move_the_commit_column
#assert_axioms the_commit_column_binds_at_the_deployed_pairing
#assert_axioms the_four_readings_are_distinct

end Dregg2.Circuit.FriDeployedHeightPairing
