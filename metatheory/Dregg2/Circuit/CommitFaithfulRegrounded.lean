/-
# Dregg2.Circuit.CommitFaithfulRegrounded — the FAITHFUL, REGROUNDED state-commitment leaf.

Two faithfulness-audit findings against the state-commitment keystones:

  (1) FAITHFULNESS. `StateCommit.recStateCommit_binds_kernel` (and its fin twin, and the
      `StateCommitReduce` OrBreak twins) are parametric over `CH : CellId → Value → ℤ`. The only
      grounding that reaches them, `FinBindsKernel.CH_fin sponge = sponge (refEncodeLeaf c v)`, is a
      toy 2-element sponge over a whole-`Value` `Nat` encoding — it does NOT denote the deployed Rust
      per-cell commitment `CellState::compute_commitment` (`circuit/src/effect_vm/cell_state.rs`).

  (2) VACUITY. `cellLeafInjective CH` is discharged (in `FinBindsKernel`) from `Poseidon2SpongeCR`
      (sponge injectivity), which `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at
      real BabyBear params. A bounded-range hash cannot be injective.

The FAITHFUL leaf already exists, differential-pinned: `CommitDifferential.effectVmCommit h4 …` is the
SAME `hash_4_to_1` tree as the Rust `compute_commitment` (pinned by
`circuit/tests/effect_vm_commit_lean_differential.rs`). But it was an UNBRIDGED island — it never
co-occurred with `CH_fin`/`cellDigest`/`recStateCommit` in any theorem.

This module BRIDGES it and REGROUNDS the leaf binding, additively (no keystone file edited):

  * §1 — `CH_faithful h4 c v` instantiates the abstract `CH` from `effectVmCommit`, decoding
    `(c, v)` into the deployed limb order `[balLo, balHi, nonce, fields[0..8], capRoot, recordDigest]`.
    A `#guard` witnesses that `CH_faithful` DENOTES `effectVmCommit` on concrete named-field limbs
    (the decode pulls the right cell fields into the right limb positions).

  * §2 — the REGROUNDED binding. NOT `cellLeafInjective CH_faithful` (vacuous — needs `h4` injective,
    which is false). Instead: a leaf collision at `CH_faithful` REDUCES to EITHER a concrete 4-to-1
    `h4` collision (`Compress4Collision`, the honest computational floor) OR a `LimbDecodeCollision`
    (two distinct `Value`s decoding to identical deployed limbs — the NAMED faithfulness gap, §2b).
    `effectVmCommit_collision_of_ne` traces the `h4` tree constructively: equal commitment + differing
    limbs ⇒ some `h4` node is a genuine collision. No injectivity hypothesis anywhere.

  * §3 — the REGROUNDED KEYSTONE. Instantiating `StateCommitReduce.recStateCommit_binds_kernel_orBreak`
    (the OrBreak twin, already carrying NO injectivity premise) at `CH := CH_faithful h4` and
    propagating the `CellCollision` disjunct through §2's reduction: equal full-state roots over the
    FAITHFUL leaf force `k = k'` OR a concrete collision of one of the frame primitives OR a concrete
    `h4` collision OR the named limb-decode gap. The leaf now DENOTES the Rust and rests on a REDUCTION
    (bind-or-collision), not a false premise.

  * §4 — the honest floor + non-vacuity. The `Compress4Collision h4` disjunct is the ROM-negligible
    event (`OodRomBound.RomUniform` idealization — a found collision of a fixed hash is a
    bounded-advantage event, NOT an impossibility; there is NO honest `¬ Compress4Collision` witness at
    real params, exactly as there is no honest injectivity). `_of_no_faithfulBreak` recovers full
    soundness on the adversary-fails event; `plus4_collision`/`cellColl_fire` FIRE the collision branch
    on the lossy `+`-fold (the fake hash the whole campaign exists to catch).

No `sorry`/`admit`/`native_decide`/`axiom`. `import Dregg2.Tactics`; `#assert_axioms` on every theorem.
-/
import Dregg2.Tactics
import Dregg2.Circuit.CommitDifferential
import Dregg2.Circuit.StateCommitReduce
import Dregg2.Circuit.OodRomBound
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectTransfer

namespace Dregg2.Circuit.CommitFaithfulRegrounded

open Dregg2.Exec (CellId Value Turn RecordKernelState balOf)
open Dregg2.Exec.EffectTransfer (nonceOf)
open Dregg2.Circuit.CommitDifferential (effectVmCommit)
open Dregg2.Circuit.StateCommit (recStateCommit RestHashIffFrame AccountsWF)
open Dregg2.Circuit.CollisionReduce (CellCollision SpongeCollision CompressCollision)
open Dregg2.Circuit.StateCommitReduce (StateBreakP recStateCommit_binds_kernel_orBreak)

set_option autoImplicit false

/-! ## §1 — the deployed limb decode + `CH_faithful` (the FAITHFUL leaf as an abstract `CH`).

The Rust `CellState::compute_commitment(balance, nonce, fields, cap_root, record_digest)` absorbs the
ordered limb list `[balLo, balHi, nonce, fields[0..8], capRoot, recordDigest]`, where
`(balLo, balHi) = split_u64(balance)` is the **30-bit** split (`circuit/src/effect_vm/helpers.rs`:
`lo = val & 0x3FFF_FFFF`, `hi = val >> 30`). We decode a cell `Value` into those limbs by NAMED field
lookup — the dregg2 `Value` is name-keyed (`Exec/Value.lean`), so the correspondence is field-by-field.
The cell id `c` is NOT a limb of `compute_commitment` (the cell's *position* is bound by the Merkle
path / `frameDigest` ordering, not the leaf), so `CH_faithful` ignores `c` — faithful to the Rust. -/

/-- The 30-bit split modulus `2^30` (`split_u64`'s `0x3FFF_FFFF + 1`). -/
def splitMod : ℤ := 1073741824

/-- `balLoLimb v` — the low 30 bits of the cell's `balance` scalar field (Rust `lo`). -/
def balLoLimb (v : Value) : ℤ := balOf v % splitMod
/-- `balHiLimb v` — the high bits of the cell's `balance` scalar field (Rust `hi = val >> 30`). -/
def balHiLimb (v : Value) : ℤ := balOf v / splitMod
/-- `nonceLimb v` — the cell's `nonce` scalar field (Rust `BabyBear::new(nonce)`). -/
def nonceLimb (v : Value) : ℤ := nonceOf v

/-- The eight welded user-field limb names (`fields[0..8]`). -/
def fieldName : Fin 8 → Dregg2.Exec.FieldName
  | 0 => "f0" | 1 => "f1" | 2 => "f2" | 3 => "f3"
  | 4 => "f4" | 5 => "f5" | 6 => "f6" | 7 => "f7"

/-- `fieldLimbs v i` — the i-th welded user field (`fields[i]`), read by name (`0` if absent). -/
def fieldLimbs (v : Value) : Fin 8 → ℤ := fun i => (v.scalar (fieldName i)).getD 0
/-- `capRootLimb v` — the cell's capability c-list root (`cap_root`). -/
def capRootLimb (v : Value) : ℤ := (v.scalar "capRoot").getD 0
/-- `recordDigestLimb v` — the single authority-residue felt (`record_digest`), folding all
authority-bearing state no named limb carries (the Lean shadow of `compute_authority_digest_felt`). -/
def recordDigestLimb (v : Value) : ℤ := (v.scalar "recordDigest").getD 0

/-- **`CH_faithful h4 c v`** — the abstract cell-leaf `CH` INSTANTIATED at the deployed commitment:
`effectVmCommit h4` over the decoded limbs, in the Rust limb order. This is the SAME `hash_4_to_1`
tree as `CellState::compute_commitment` (`CommitDifferential.effectVmCommit`, differential-pinned),
now presented as a `CellId → Value → ℤ` leaf the state-commitment keystones consume. -/
def CH_faithful (h4 : ℤ → ℤ → ℤ → ℤ → ℤ) (c : CellId) (v : Value) : ℤ :=
  effectVmCommit h4 (balLoLimb v) (balHiLimb v) (nonceLimb v) (fieldLimbs v)
    (capRootLimb v) (recordDigestLimb v)

/-! ### Non-vacuity: `CH_faithful` DENOTES `effectVmCommit` on concrete named-field limbs.

A concrete cell `Value` with balance/nonce/f0..f7/capRoot/recordDigest fields commits to exactly
`effectVmCommit` over the LITERAL expected limbs — the decode pulls the right cell fields into the
right limb positions (`balance 5 → balLo 5, balHi 0`; `nonce 7`; `fields[i] = 10+i`; `capRoot 100`;
`recordDigest 42`), witnessing that `CH_faithful` is the deployed shape, not a re-abstraction. -/

private def h4C : ℤ → ℤ → ℤ → ℤ → ℤ :=
  fun a b c d => a * 1000000000 + b * 1000000 + c * 1000 + d

private def cellC : Value :=
  .record [("balance", .int 5), ("nonce", .int 7),
    ("f0", .int 10), ("f1", .int 11), ("f2", .int 12), ("f3", .int 13),
    ("f4", .int 14), ("f5", .int 15), ("f6", .int 16), ("f7", .int 17),
    ("capRoot", .int 100), ("recordDigest", .int 42)]

-- DENOTATION: `CH_faithful` on `cellC` equals `effectVmCommit` over the deployed limbs the cell's
-- named fields decode to (balance-30-bit-split lo=5/hi=0, nonce=7, fields[i]=10+i, cap=100, rd=42).
#guard decide (CH_faithful h4C 0 cellC = effectVmCommit h4C 5 0 7 (fun i => 10 + (i : ℤ)) 100 42)

/-! ## §2 — the honest computational floor: a 4-to-1 `h4` collision + the tree-tracing reduction. -/

/-- **`Compress4Collision h4`** — a concrete collision of the 4-to-1 compress `h4`: distinct input
tuples with equal output. The honest floor of `hash_4_to_1` (its 4-ary analog of `CompressCollision`).
NOT the vacuous `compress4Injective` (whose negation this is) — a REALIZABLE break event. -/
def Compress4Collision (h4 : ℤ → ℤ → ℤ → ℤ → ℤ) : Prop :=
  ∃ a b c d a' b' c' d' : ℤ, ¬ (a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∧ h4 a b c d = h4 a' b' c' d'

/-- **`effectVmCommit_collision_of_ne`** — the tree-tracing reduction. If two `effectVmCommit`s over
DIFFERING limb tuples are EQUAL, then some node of the `h4` tree is a concrete `Compress4Collision`.
Constructive (no injectivity): descend root → `inter1`/`inter2`/`inter3`; at each node either its four
inputs agree (recurse) or they differ while the node outputs agree (a collision). If EVERY node's
inputs agree, all thirteen limbs agree — contradicting the differing-limbs hypothesis. This is the
contrapositive of `CommitDifferential.effectVmCommit_binds_all`, but WITHOUT assuming `h4` injective:
the disjunction hands back the witnessing collision instead of deriving `False` from a false premise. -/
theorem effectVmCommit_collision_of_ne (h4 : ℤ → ℤ → ℤ → ℤ → ℤ)
    (bl bh n : ℤ) (f : Fin 8 → ℤ) (cr rd : ℤ)
    (bl' bh' n' : ℤ) (f' : Fin 8 → ℤ) (cr' rd' : ℤ)
    (hne : ¬ (bl = bl' ∧ bh = bh' ∧ n = n'
      ∧ f 0 = f' 0 ∧ f 1 = f' 1 ∧ f 2 = f' 2 ∧ f 3 = f' 3
      ∧ f 4 = f' 4 ∧ f 5 = f' 5 ∧ f 6 = f' 6 ∧ f 7 = f' 7
      ∧ cr = cr' ∧ rd = rd'))
    (heq : effectVmCommit h4 bl bh n f cr rd = effectVmCommit h4 bl' bh' n' f' cr' rd') :
    Compress4Collision h4 := by
  simp only [effectVmCommit] at heq
  by_cases hr : (h4 bl bh n (f 0) = h4 bl' bh' n' (f' 0)
      ∧ h4 (f 1) (f 2) (f 3) (f 4) = h4 (f' 1) (f' 2) (f' 3) (f' 4)
      ∧ h4 (f 5) (f 6) (f 7) cr = h4 (f' 5) (f' 6) (f' 7) cr'
      ∧ rd = rd')
  · -- root inputs agree; descend into inter1 / inter2 / inter3.
    obtain ⟨he1, he2, he3, herd⟩ := hr
    by_cases ha : (bl = bl' ∧ bh = bh' ∧ n = n' ∧ f 0 = f' 0)
    · by_cases hb : (f 1 = f' 1 ∧ f 2 = f' 2 ∧ f 3 = f' 3 ∧ f 4 = f' 4)
      · by_cases hc : (f 5 = f' 5 ∧ f 6 = f' 6 ∧ f 7 = f' 7 ∧ cr = cr')
        · -- every node's inputs agree ⇒ all thirteen limbs agree ⇒ contradiction.
          exfalso; apply hne
          obtain ⟨e0, e1, e2, e3⟩ := ha
          obtain ⟨e4, e5, e6, e7⟩ := hb
          obtain ⟨e8, e9, e10, e11⟩ := hc
          exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, herd⟩
        · exact ⟨_, _, _, _, _, _, _, _, hc, he3⟩   -- inter3 node collision
      · exact ⟨_, _, _, _, _, _, _, _, hb, he2⟩     -- inter2 node collision
    · exact ⟨_, _, _, _, _, _, _, _, ha, he1⟩       -- inter1 node collision
  · exact ⟨_, _, _, _, _, _, _, _, hr, heq⟩         -- root node collision

#assert_axioms effectVmCommit_collision_of_ne

/-! ## §2b — the NAMED faithfulness gap: `LimbDecodeCollision`.

The decode `Value → limbs` is lossy: two distinct `Value`s can carry identical deployed limbs iff they
differ ONLY in structure the thirteen limbs do not name (an unnamed extra field; an authority residue
the `recordDigest` field does not fold). In the DEPLOYED circuit `record_digest =
compute_authority_digest_felt` folds precisely that residue, so distinct residues give distinct
`recordDigest` limbs and this gap is EMPTY on well-formed cells. In this ABSTRACT model `recordDigestLimb`
reads a single scalar field and does NOT enforce the fold, so the gap is inhabited (§4 `decode_gap_fires`).
NAMING it as its own disjunct is the honest resolution: the leaf binding reduces to (h4 collision) ∨
(this decode gap), and closing the gap on real cells is the residue-fold obligation, discharged
circuit-side by `compute_authority_digest_felt` (audit P0-2, the differential-pinned `record_digest`). -/

/-- **`SameLimbs v w`** — `v` and `w` decode to identical deployed limbs (limb order fixed to the
Rust absorption order: `balLo, balHi, nonce, fields[0..8], capRoot, recordDigest`). -/
def SameLimbs (v w : Value) : Prop :=
  balLoLimb v = balLoLimb w ∧ balHiLimb v = balHiLimb w ∧ nonceLimb v = nonceLimb w
    ∧ fieldLimbs v 0 = fieldLimbs w 0 ∧ fieldLimbs v 1 = fieldLimbs w 1
    ∧ fieldLimbs v 2 = fieldLimbs w 2 ∧ fieldLimbs v 3 = fieldLimbs w 3
    ∧ fieldLimbs v 4 = fieldLimbs w 4 ∧ fieldLimbs v 5 = fieldLimbs w 5
    ∧ fieldLimbs v 6 = fieldLimbs w 6 ∧ fieldLimbs v 7 = fieldLimbs w 7
    ∧ capRootLimb v = capRootLimb w ∧ recordDigestLimb v = recordDigestLimb w

/-- **`LimbDecodeCollision v w`** — the NAMED faithfulness gap: two DISTINCT `Value`s decoding to the
SAME deployed limbs. Empty on well-formed cells (the `record_digest` fold), inhabited in the abstract
model — the precisely-named residual, not a hidden re-abstraction. -/
def LimbDecodeCollision (v w : Value) : Prop := v ≠ w ∧ SameLimbs v w

/-- **`cellCollision_faithful_reduces`** — a leaf collision at the FAITHFUL leaf reduces to EITHER a
concrete `h4` tree collision (the honest floor) OR a `LimbDecodeCollision` (the named gap). This is the
REGROUNDED replacement for `cellLeafInjective (CH_faithful h4)` (which would need `h4` injective =
false): the binding is a REDUCTION, not an assumed injectivity. -/
theorem cellCollision_faithful_reduces (h4 : ℤ → ℤ → ℤ → ℤ → ℤ) :
    CellCollision (CH_faithful h4) → (∃ v w, LimbDecodeCollision v w) ∨ Compress4Collision h4 := by
  rintro ⟨c, v, w, hne, heq⟩
  simp only [CH_faithful] at heq
  by_cases hs : SameLimbs v w
  · exact Or.inl ⟨v, w, hne, hs⟩
  · exact Or.inr (effectVmCommit_collision_of_ne h4
      (balLoLimb v) (balHiLimb v) (nonceLimb v) (fieldLimbs v) (capRootLimb v) (recordDigestLimb v)
      (balLoLimb w) (balHiLimb w) (nonceLimb w) (fieldLimbs w) (capRootLimb w) (recordDigestLimb w)
      hs heq)

#assert_axioms cellCollision_faithful_reduces

/-! ## §3 — THE REGROUNDED KEYSTONE (equal FAITHFUL roots ⇒ equal kernel OR a concrete collision).

The honest replacement for `StateCommit.recStateCommit_binds_kernel` / `FinBindsKernel.
recStateCommit_binds_kernel_fin` (both of which consume the vacuous `cellLeafInjective`). We instantiate
`StateCommitReduce.recStateCommit_binds_kernel_orBreak` — the OrBreak twin that carries NO injectivity
premise — at `CH := CH_faithful h4`, then propagate the `CellCollision` disjunct through §2's reduction.
The frame primitives `cmb`/`compress`/`compressN`/`RH` stay abstract (their regrounding is the existing
`StateCommitReduce` chain); THIS module regrounds the LEAF. -/

/-- **`FaithfulBreak h4 cmb compress compressN`** — the apex break with the leaf disjunct regrounded:
a concrete collision of the frame sponge / root combiner / node hash, OR the named limb-decode gap, OR
a concrete `h4` tree collision. Every disjunct is a REALIZABLE break event — none is a false premise. -/
def FaithfulBreak (h4 : ℤ → ℤ → ℤ → ℤ → ℤ) (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) : Prop :=
  SpongeCollision compressN ∨ CompressCollision cmb ∨ CompressCollision compress
    ∨ (∃ v w, LimbDecodeCollision v w) ∨ Compress4Collision h4

/-- **`recStateCommit_binds_kernel_faithful` — THE REGROUNDED KEYSTONE.** Equal full-state roots (same
turn, both `AccountsWF`) over the FAITHFUL leaf `CH_faithful h4` force the WHOLE `RecordKernelState`
equal — OR a concrete `FaithfulBreak`. The leaf DENOTES the Rust `compute_commitment` (§1) and the
binding rests on a REDUCTION (§2), never on `h4` injectivity. `RestHashIffFrame RH` (a modeling premise,
not a collision event) is the sole non-hash hypothesis, exactly as in `StateCommitReduce`. -/
theorem recStateCommit_binds_kernel_faithful (h4 : ℤ → ℤ → ℤ → ℤ → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (RH : RecordKernelState → ℤ)
    (hRest : RestHashIffFrame RH)
    (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : recStateCommit (CH_faithful h4) RH cmb compress compressN k t
      = recStateCommit (CH_faithful h4) RH cmb compress compressN k' t) :
    k = k' ∨ FaithfulBreak h4 cmb compress compressN := by
  have h := recStateCommit_binds_kernel_orBreak (CH_faithful h4) cmb compress compressN RH hRest
    k k' t hwf hwf' hroot
  rcases h with hk | hbrk
  · exact Or.inl hk
  · -- StateBreakP = SpongeCollision ∨ CompressCollision cmb ∨ CompressCollision compress ∨ CellCollision.
    rcases hbrk with hs | hc1 | hc2 | hcell
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr (Or.inl hc1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hc2)))
    · rcases cellCollision_faithful_reduces h4 hcell with hgap | hcol
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hgap))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcol))))

#assert_axioms recStateCommit_binds_kernel_faithful

/-! ## §4 — the honest floor, recovery, and FIRE (both poles).

`Compress4Collision h4` is the ROM-negligible event: finding a collision of a FIXED 4-to-1 hash is a
bounded-advantage event under the random-oracle idealization (`OodRomBound.RomUniform` — a fresh squeeze
lands uniformly, so a target collision has probability `≤ deg/|F|`), NOT an impossibility. There is NO
honest `¬ Compress4Collision h4` at real params — any bounded-range `h4` HAS collisions (`h4C` itself
does), exactly as no bounded-range hash is injective. So `_of_no_faithfulBreak` below is CONDITIONAL on
the adversary-fails event `¬ FaithfulBreak`, never asserting it — mirroring
`StateCommitReduce.recStateCommit_binds_kernel_of_no_break`. -/

/-- **Recovery (resolve):** on the adversary-fails event `¬ FaithfulBreak` the regrounded keystone
recovers the injective-style conclusion `k = k'` verbatim — so it strictly SUBSUMES the (vacuous)
`cellLeafInjective`-carrying original, discharging its false premise for a live (ROM-bounded) one. -/
theorem recStateCommit_binds_kernel_faithful_of_no_break (h4 : ℤ → ℤ → ℤ → ℤ → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ) (RH : RecordKernelState → ℤ)
    (hNo : ¬ FaithfulBreak h4 cmb compress compressN)
    (hRest : RestHashIffFrame RH)
    (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hroot : recStateCommit (CH_faithful h4) RH cmb compress compressN k t
      = recStateCommit (CH_faithful h4) RH cmb compress compressN k' t) :
    k = k' := by
  rcases recStateCommit_binds_kernel_faithful h4 cmb compress compressN RH hRest k k' t hwf hwf' hroot
    with hk | hbrk
  · exact hk
  · exact absurd hbrk hNo

#assert_axioms recStateCommit_binds_kernel_faithful_of_no_break

/-! ### FIRE — the collision branch is live on the lossy `+`-fold (the fake hash the campaign catches). -/

/-- The lossy 4-to-1 `+`-fold — the `hash_4_to_1` stand-in the differential exists to reject. -/
def plus4 : ℤ → ℤ → ℤ → ℤ → ℤ := fun a b c d => a + b + c + d

/-- **FIRE (floor):** the `+`-fold HAS a concrete `Compress4Collision` (`100+5+0+0 = 99+6+0+0`) — the
event the keystone hands back instead of silently binding. The injective-form original cannot even be
stated here (its `compress4Injective plus4` premise is false). -/
theorem plus4_collision : Compress4Collision plus4 :=
  ⟨100, 5, 0, 0, 99, 6, 0, 0, by decide, by decide⟩

#assert_axioms plus4_collision

private def vFire : Value := .record [("balance", .int 5)]
private def wFire : Value := .record [("balance", .int 4), ("f0", .int 1)]

/-- `vFire ≠ wFire` — distinct cells (balance 5 vs 4). -/
theorem vFire_ne_wFire : vFire ≠ wFire :=
  fun h => absurd (congrArg balOf h) (by decide)

/-- **FIRE (leaf collision):** under the lossy `plus4` leaf, two DISTINCT cells with the SAME limb sum
(`vFire`: balance 5 → limb-sum 5; `wFire`: balance 4 + f0 1 → limb-sum 5) collide at `CH_faithful`. So
`CellCollision (CH_faithful plus4)` is inhabited — the leaf binding is genuinely at risk on a fake hash,
and §2's reduction is FORCED to hand back a break. -/
theorem cellColl_fire : CellCollision (CH_faithful plus4) :=
  ⟨0, vFire, wFire, vFire_ne_wFire, by decide⟩

/-- **FIRE (reduction fires to the floor):** the leaf collision above reduces to a concrete
`Compress4Collision plus4` — the differing-limbs branch, not the decode gap (`vFire`/`wFire` differ in
`balLo`), so the machinery catches the fake `+`-hash. -/
theorem cellColl_fire_reduces :
    (∃ v w, LimbDecodeCollision v w) ∨ Compress4Collision plus4 :=
  cellCollision_faithful_reduces plus4 cellColl_fire

#assert_axioms vFire_ne_wFire
#assert_axioms cellColl_fire
#assert_axioms cellColl_fire_reduces

/-- **FIRE (decode gap):** the NAMED faithfulness gap is inhabited in the abstract model — two distinct
`Value`s with identical deployed limbs (`vFire` carries an unnamed extra field beyond the thirteen the
limbs name). Witnessing the gap is what makes NAMING it (rather than hiding it under a false injectivity)
the honest move; closing it on real cells is the circuit-side `record_digest` residue-fold obligation. -/
private def gapA : Value := .record [("balance", .int 5)]
private def gapB : Value := .record [("balance", .int 5), ("unnamedResidue", .int 99)]

theorem decode_gap_fires : LimbDecodeCollision gapA gapB := by
  refine ⟨?_, ?_⟩
  · exact fun h => absurd (congrArg (fun v => (Value.field v "unnamedResidue").isSome) h) (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

#assert_axioms decode_gap_fires

/-! ## §5 — the ROM anchor (the honest floor, named).

The residual after this module is `Compress4Collision h4` — the event "the adversary exhibits a
`hash_4_to_1` collision". Its negligibility is the `OodRomBound.RomUniform` idealization (a fresh
Poseidon2 squeeze lands uniformly ⇒ any fixed target is hit with probability `≤ deg/|F|`, the honest
computational floor, satisfiable and refutable, never an axiom). We re-export the named floor Prop so a
downstream probabilistic bound can quantify the collision disjunct; there is deliberately NO
`¬ Compress4Collision` theorem (that would be the false injectivity, re-introduced). -/

/-- The named ROM floor, re-exported for downstream probabilistic bounds on the collision disjunct. -/
abbrev RomFloor := @Dregg2.Circuit.OodRomBound.RomUniform

end Dregg2.Circuit.CommitFaithfulRegrounded
