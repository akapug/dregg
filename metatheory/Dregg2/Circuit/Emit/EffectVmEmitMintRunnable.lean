/-
# Dregg2.Circuit.Emit.EffectVmEmitMintRunnable — MINT lifted to FULL-STATE on the RUNNABLE descriptor.

`EffectVmEmitMint` proved the per-cell soundness `mintDescriptor_full_sound` (a satisfying mint row
forces `CellMintSpec` + publishes `NEW_COMMIT`) on the 186-wide `mintVmDescriptor`. But that descriptor's
published `state_commit` absorbs only the 13 state-block columns — NOT the `system_roots` sub-block, so it
is still the dominant Class-C projection (`EffectVmFullStateRunnable` header): a satisfying RUNNABLE proof
pins a projection, not the WHOLE 17-field post-state.

This module amplifies mint to full-state via the VALIDATED RECIPE
(`EffectVmFullStateRunnable.lean` §6, exactly as `transferRunnableSpec` is the worked reference):

  * **the wide descriptor** `mintVmDescriptorWide` — `mintVmDescriptor` with `traceWidth :=
    EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites` (the `system_roots`-absorbing sites). The
    per-row/transition/boundary gate list is BYTE-IDENTICAL (`mintWide_constraints_eq`); only the width
    grows by 2 and site 3's spare `.zero` 4th slot becomes the `sysRootsDigestCol` carrier.
  * **`mintGates_give_cellSpec`** — the GATE-ONLY per-cell soundness (no hash-site hypothesis): the per-row
    gates of `mintVmDescriptor`, on a row decoded by `RowEncodes`, force `CellMintSpec`. This is
    `mintDescriptor_full_sound`'s per-cell body with the hash-site/boundary layer DROPPED — it factors
    through `mintVm_faithful` + `intent_to_cellSpec`, NEITHER of which reads the sites.
  * **`mintRunnableSpec`** — the `RunnableFullStateSpec CellState` instance. Mint touches NO side-table, so
    its `system_roots` sub-block is FROZEN: `fullClause = CellMintSpec ∧ postRoots = preRoots`.
  * **`mint_runnable_full_sound`** — instantiating the GENERIC `runnable_full_sound`: a row satisfying
    `mintVmDescriptorWide` (the RUNNABLE wide descriptor), under the decode, pins the FULL 17-field post —
    the per-cell `CellMintSpec` AND the frozen 8 side-table roots. The crypto/anti-ghost on all 17 fields
    falls out of the generic `wide_rejects_state_tamper_or_collides`/`wide_rejects_root_tamper_or_collides`
    (instantiated at `mintRunnableSpec` in §4) — tamper ANY column or root ⇒ a produced hash collision.

## HONEST PRECONDITION-GAP NOTE (recorded for the audit wave, per the task brief)

The wide descriptor binds the FULL post-state, but — exactly as the per-cell `EffectVmEmitMint` already
states in its BOUNDARY — the mint `(cell, asset)` index + the `mintAdmit` AUTHORITY / non-negativity
/ destination-liveness GUARD have NO row column: they are executor-side preconditions of `recCMintAsset`
that are NOT in-circuit conjuncts of `mintVmDescriptor`. This module does not widen the gate set (that is
the named, deferred systematic audit wave); it lifts the EXISTING gates to full-state. The named residual
(the global supply total, a turn-level cross-cell accumulator) is unchanged and unaffected by this lift.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. The §4 anti-ghost teeth carry
NO crypto hypothesis: they conclude a DISJUNCTION handing back a specific `WideColl`/`RootsColl` collision
in the tamper branch, so they hold of the deployed sponge rather than of an injective idealisation of it.
Imports are read-only; this module owns only its own declarations.
-/
import Dregg2.Circuit.Emit.EffectVmEmitMint
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitMintRunnable

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitMint
  (mintVmDescriptor mintRowGates mintRowGates_flag_indep mintVm_faithful intent_to_cellSpec
   CellMintSpec RowEncodes MintRowIntent IsMintRow mintVmAirName
   goodMintRow goodMintRow_realizes_intent)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols wideHashSites RunnableFullStateSpec runnable_full_sound
   WideColl RootsColl wide_rejects_state_tamper_or_collides wide_rejects_root_tamper_or_collides)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — The WIDE mint descriptor (`system_roots`-absorbing). -/

/-- **`mintVmDescriptorWide`** — `mintVmDescriptor` WIDENED: the SAME per-row credit/freeze gates +
transitions + boundary PI pins, but `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites :=
wideHashSites` (the `system_roots`-absorbing sites). Strictly additive over `mintVmDescriptor`: the
constraint list is byte-identical; only the width grows by 2 and site 3's spare `.zero` 4th slot becomes
the `sysRootsDigestCol` carrier (so the published `state_commit` now absorbs the — frozen — side-table
digest). `usesWideSites := rfl`. -/
def mintVmDescriptorWide : EffectVmDescriptor :=
  { mintVmDescriptor with
    name := mintVmAirName ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide mint descriptor's constraints ARE mint's (the width/site swap leaves the
per-row/transition/boundary gate list untouched). -/
theorem mintWide_constraints_eq :
    mintVmDescriptorWide.constraints = mintVmDescriptor.constraints := rfl

/-! ## §2 — The GATE-ONLY per-cell soundness (the THIN per-effect content of `decodeFull`). -/

/-- **`mintGates_give_cellSpec` — gate-only per-cell soundness (no hash-site hypothesis).** The per-row
gates of `mintVmDescriptor` (a constraint-list segment), on a mint row decoded by `RowEncodes`, force
`CellMintSpec`. This is the body of `mintDescriptor_full_sound` with the hash-site/boundary layer DROPPED —
the per-cell credit/freeze factors through `mintVm_faithful` (`mintRowGates ⟺ MintRowIntent`) +
`intent_to_cellSpec`, NEITHER of which reads the sites. So the runnable per-cell soundness depends ONLY on
the gates (the sites bind the COMMITMENT — §1/§4 of the generic module — not the per-cell spec). -/
theorem mintGates_give_cellSpec (env : VmRowEnv) (hrow : IsMintRow env)
    (pre post : CellState) (amt : ℤ)
    (henc : RowEncodes env pre amt post)
    (hgates : ∀ c ∈ mintVmDescriptor.constraints, c.holdsVm env true false) :
    CellMintSpec pre amt post := by
  -- the per-row gates are a sub-list of the descriptor's constraints; restrict + flatten flags.
  have hrowgates : ∀ c ∈ mintRowGates, c.holdsVm env true false := by
    intro c hc
    apply hgates
    unfold mintVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hrowgates' := mintRowGates_flag_indep env true hrowgates
  exact intent_to_cellSpec env pre post amt henc ((mintVm_faithful env hrow).mp hrowgates')

/-! ## §3 — THE RUNNABLE FULL-STATE INSTANCE. -/

/-- **`MintFullClause`** — the full declarative post-state for mint over `(pre, post, postRoots)`: the
per-cell `CellMintSpec` (balance credited by `amt`, the whole frame — `bal_hi`/nonce/8 fields/`cap_root`/
`reserved` — frozen) AND the `system_roots` sub-block FROZEN (mint touches no side-table). `amt` is the
fixed credit; `preRoots` is the frozen reference sub-block. Non-vacuous: §`goodMint_realizes` inhabits it. -/
def MintFullClause (amt : ℤ) (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellMintSpec pre amt post ∧ postRoots = preRoots

/-- **`mintRunnableSpec` — the FULL-state RUNNABLE instance for mint.** `decodeAfter` is `RowEncodes` PLUS
the frozen-roots witness; `decodeFull` projects the wide descriptor's per-row gates (= mint's) to the
GATE-ONLY `mintGates_give_cellSpec`, then carries the frozen-roots fact. THIN — the only per-effect content
is the (proved here, hash-site-free) `mintGates_give_cellSpec` + the frozen-roots decode. NON-VACUOUS:
`fullClause` is the genuine per-cell credit + the frozen sub-block, NOT `True`. -/
def mintRunnableSpec (amt : ℤ) (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := mintVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsMintRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodes env pre amt post ∧ postRoots = preRoots
  fullClause    := MintFullClause amt preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨mintGates_give_cellSpec env hrow pre post amt henc (mintWide_constraints_eq ▸ hgates), hroots⟩

/-- **`mint_runnable_full_sound` — THE DELIVERABLE (full-state on the RUNNABLE descriptor).** A row
satisfying `mintVmDescriptorWide` — the WIDE descriptor the prover RUNS (`satisfiedVm`, first/last active) —
under the structured decode, pins the FULL 17-field declarative post-state: the per-cell `CellMintSpec`
(balance credit + the whole frame frozen) AND the 8 side-table roots FROZEN (`postRoots = preRoots`). The
crypto is discharged ONCE in the generic `runnable_full_sound`; mint supplies only the THIN `decodeFull`.
Strictly stronger than `mintDescriptor_full_sound` (which binds only the 13-column projection): the wide
`state_commit` absorbs the `system_roots` digest, so a tamper of ANY of the 17 fields' content is UNSAT
(§4). -/
theorem mint_runnable_full_sound (amt : ℤ) (preRoots : SysRoots) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsMintRow env)
    (henc : RowEncodes env pre amt post)
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash mintVmDescriptorWide env true false) :
    CellMintSpec pre amt post ∧ postRoots = preRoots :=
  runnable_full_sound (mintRunnableSpec amt preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

#assert_axioms mint_runnable_full_sound

/-! ## §4 — ANTI-GHOST on all 17 fields (instantiating the generic teeth at `mintRunnableSpec`).

The whole-state tooth: two rows satisfying `mintVmDescriptorWide` that publish the SAME `NEW_COMMIT` (with
`systemRootsDigest` carriers) can DISAGREE on an absorbed state-block column
(`mint_rejects_state_tamper_or_collides`) or on a side-table root (`mint_rejects_root_tamper_or_collides`)
only by exhibiting a hash collision. So the RUNNABLE mint commitment binds the per-cell block AND the
side-table state — the magnesium breadth, not a projection — up to a collision the theorem produces. -/

/-- **`mint_rejects_state_tamper_or_collides` — per-cell-block anti-ghost, as EXTRACTION.** Two wide mint
rows publishing the same `NEW_COMMIT` whose absorbed state-block columns DIFFER exhibit a concrete
collision of `hash`: a `WideColl` on the wide absorbed lists, or a `RootsColl` on the two root lists.

The previous form concluded `False` from `Poseidon2SpongeCR hash`. The deployed BabyBear sponge REFUTES
that hypothesis (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so the previous form was vacuous at
deployed parameters. This disjunction is formally weaker and holds of the deployed sponge. -/
theorem mint_rejects_state_tamper_or_collides (amt : ℤ) (preRoots : SysRoots)
    (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash mintVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash mintVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : baseAbsorbedCols e₁ ≠ baseAbsorbedCols e₂) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  wide_rejects_state_tamper_or_collides (mintRunnableSpec amt preRoots) hash e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`mint_rejects_root_tamper_or_collides` — side-table anti-ghost on mint, as EXTRACTION.** Two wide
mint rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) whose side-table sub-blocks
DIFFER at some index `i` exhibit a concrete collision of `hash` — a `WideColl` on the wide absorbed lists
or a `RootsColl` on the two root lists. The side-table state is bound BY the runnable mint commitment up
to a produced collision.

The previous form concluded `False` from `Poseidon2SpongeCR hash`, which the deployed BabyBear sponge
refutes; it was therefore vacuous at deployed parameters. This form is weaker and holds of that sponge. -/
theorem mint_rejects_root_tamper_or_collides (amt : ℤ) (preRoots : SysRoots)
    (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash mintVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash mintVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  wide_rejects_root_tamper_or_collides (mintRunnableSpec amt preRoots) hash e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

#assert_axioms mint_rejects_state_tamper_or_collides
#assert_axioms mint_rejects_root_tamper_or_collides

/-! ## §5 — NON-VACUITY: the full clause is inhabited by a real mint, and refutable.

`goodMintRow` (from `EffectVmEmitMint`) realizes the mint intent (`100 → 130 = 100 + 30`). We decode it to a
concrete `(pre, post)` `CellState` pair and confirm the full clause's `CellMintSpec` is satisfied
(witness TRUE), and refute a forged post-state (witness FALSE) — pinning non-vacuity from BOTH sides. -/

/-- The pre-state `goodMintRow` encodes: bal_lo 100, nonce 5, everything else 0. -/
def goodMintPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- The post-state `goodMintRow` encodes: bal_lo 130, nonce 6 (the runtime TICK 5 → 6), frame frozen. -/
def goodMintPost : CellState :=
  { balLo := 130, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- A frozen reference sub-block (the empty `system_roots`, since mint touches no side-table). -/
def goodMintPreRoots : SysRoots := emptySystemRoots

/-- **`goodMint_realizes` — NON-VACUITY (witness TRUE).** The mint `fullClause` is INHABITED by a real
mint: `goodMintPost` is the genuine credit image of `goodMintPre` (`100 → 130`, the nonce TICKED
`5 → 6` matching the runtime, the frame frozen) and the roots are frozen. So the framework's
`fullClause` is NOT `True` for mint — it is a meaningful 17-field predicate a real mint satisfies. -/
theorem goodMint_realizes :
    (mintRunnableSpec 30 goodMintPreRoots).fullClause goodMintPre goodMintPost goodMintPreRoots :=
  ⟨⟨by norm_num [goodMintPre, goodMintPost], rfl, by norm_num [goodMintPre, goodMintPost],
    fun _ => rfl, rfl, rfl⟩, rfl⟩

/-- **`mintFullClause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose
`bal_lo` is NOT the credit (`goodMintPre.balLo = 100`, demanding `130`, but a forged `999`) FAILS
`MintFullClause` — so the clause is not vacuously true. -/
theorem mintFullClause_not_trivial :
    ¬ MintFullClause 30 goodMintPreRoots goodMintPre
        { goodMintPost with balLo := 999 } goodMintPreRoots := by
  rintro ⟨⟨hbal, _⟩, _⟩
  simp only [goodMintPre] at hbal
  norm_num at hbal

#assert_axioms goodMint_realizes
#assert_axioms mintFullClause_not_trivial

/-! ## §6 — axiom-hygiene tripwires + structural pins. -/

#guard mintVmDescriptorWide.traceWidth == 190
#guard mintVmDescriptorWide.hashSites.length == 4
#guard mintVmDescriptorWide.constraints.length == mintVmDescriptor.constraints.length

#assert_axioms mintWide_constraints_eq
#assert_axioms mintGates_give_cellSpec

end Dregg2.Circuit.Emit.EffectVmEmitMintRunnable
