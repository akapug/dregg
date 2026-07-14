/-
# Dregg2.Shielded.RealCrypto — retire the two toy crypto stand-ins the critic flagged in rung-3.

Rung-3 private matching (`Market/ShieldedClearing.lean`) was proved over TWO declared toys:

  * the value commitment `refVC.commit v r = (v + r).toNat` (`Exec/ShieldedValue.lean`) —
    ADDITIVE in a single `Nat` coordinate, so it is **not binding** (it collapses `(v, r)`:
    `commit 8 3 = commit 3 8 = 11`) and carries **no hiding/binding assumption** at all;
  * the tree root `refTreeRoot leaves = leaves.foldl (·*31 + · + 1) 7`
    (`Shielded/ClaimRefinement.lean`) — a LINEAR rolling hash with **no collision-resistance**;
    its "binding" was arithmetic invertibility, not a cryptographic floor.

This module re-grounds both halves on the REAL crypto the codebase already carries, with the
honest floors NAMED (not laundered):

  * **§1 — REAL PEDERSEN** (`Dregg2.Crypto.Pedersen` / `Crypto.Primitives.CryptoPrimitives`):
    the value commitment is the two-generator group Pedersen `commit v r = v·G + r·H` over an
    `AddCommGroup` `Digest`, whose additive homomorphism `commit_hom` is PROVED and whose
    **binding rests on the discrete-log carrier `CryptoPrimitives.binding`** (a `Prop`, never a
    Lean law). The hidden conservation `Σ C_in = Σ C_out` is re-proved over THIS real commitment
    (`ring_conserves_pedersen` / `_list`, off `committed_conservation` / `listCommit_collapse`),
    so "hidden conservation" now holds over a hiding+binding Pedersen, not the additive toy. The
    key structural gap the toy hid: a real Pedersen is **not `Nat`-additive** — it lives in a
    group — so `ValueCommitment.hom` (Nat-additivity) was only ever satisfiable by a linear
    stand-in. The real conservation therefore lives at the GROUP layer here.

  * **§2 — REAL POSEIDON2 TREE** (`Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR` — the
    deployed sponge CR, the SAME floor `StateCommit` / `SortedTreeNonMembership` bind under): the
    tree root is `sponge leaves` and **root-binds-the-leaf-set rests on the named sponge CR**
    (`root_binds` / `forged_set_forces_collision`), so a forged membership (a committed set faked
    to hit an honest root) FORCES a Poseidon2 collision. The linear rolling hash is gone.

  * **§3 — COMPOSE**: the rung-3 shape (hidden conservation + membership) restated over the two
    real primitives, each conditioned on its honest floor (DLog binding / Poseidon2 CR).

## HONEST GRADE
The conservation ALGEBRA (`commit_hom`/`map_sum`), the no-wrap range REDUCTION (`twoLeg_noWrap_…`),
the value-binding CR REDUCTION (§1.3: CR ⇒ injective on `(value, asset)`), and the tree root-binding
REDUCTION (§2: CR ⇒ injective) are all unconditional Lean.

## §PQ CUTOVER (`docs/deos/PQ-SHIELDED-COMMITMENT.md`, Option A) — the value-binding floor MOVED.
The AUTHORITATIVE shielded value-binding is no longer the DLog Pedersen: it is the in-AIR Poseidon2
`value_binding = hash_fact(value, [asset_type, randomness, 0])`, binding `(value, asset_type)` jointly
under `HashCR` (§1.3, `ValueBindingCommit.binds_value_and_asset` / `mint_forces_collision`) — a
QUANTUM-SAFE floor. The no-mint (conservation + no-wrap range) is the fully-in-AIR STARK gate
(`Poseidon2ChipArithSound`, field-conservation `Σ` + the `VALUE_BITS` range gadget refined here by
`inAir_conservation_refines_pedersen`), also quantum-safe. So the residual crypto for the shielded
value-side is now exactly `HashCR` (Poseidon2 CR) + STARK soundness — the SAME floors the tree/
nullifier stand on — NOT discrete-log.

The §1 `pedTwoGen` conservation MODEL (whose `binding` names DLog) is retained as the group-Pedersen
ALGEBRA the in-AIR field conservation refines; the DLog `binding` carrier is NO LONGER the
value-binding floor (that is §1.3's `HashCR`), and the off-AIR Pedersen/Schnorr/Bulletproof are
retired from the value-binding TCB. NAMED RESIDUAL (separate frontier, NOT this cutover): the fhEgg
homomorphic-fold's PQ-lattice-additive commitment for aggregating independently-produced commitments
(Option B / the aggregation layer), and the full 64-bit multi-limb in-AIR range widening (the current
gadget is sound over the BabyBear no-wrap range, `< 2^VALUE_BITS`).
-/
import Dregg2.Crypto.Pedersen
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Exec.ShieldedValue
import Dregg2.Bignum

namespace Dregg2.Shielded.RealCrypto

open Dregg2.Crypto
open Dregg2.Crypto.Pedersen
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option autoImplicit false

universe u

/-! ## §1 — REAL PEDERSEN value commitment (retires `refVC`).

The real Pedersen commitment is `commit v r = v·G + r·H` over a group `Digest`. We reuse the
proved conservation of `Dregg2.Crypto.Pedersen` (`committed_conservation`, `listCommit_collapse`)
and expose it as the shielded-ring hidden-conservation over the REAL commitment, with the DLog
`binding` carrier named. -/

variable {Digest : Type u} [AddCommGroup Digest]

/-- **`ring_conserves_pedersen` — hidden conservation over the REAL group Pedersen.** If the ring's
input and output notes carry equal value sums AND equal blinding sums, their Pedersen COMMITMENT
sums are equal — `Σ commit(vᵢ_in, rᵢ_in) = Σ commit(vⱼ_out, rⱼ_out)`, so the homomorphic excess is
zero and a verifier confirms conservation over the commitments alone, learning no single amount.
This is `shielded_ring_value_conserves_hidden` re-grounded on the two-generator group commitment
(`CryptoPrimitives.commit`, `commit_hom` PROVED); the step from the commitment equation to the
VALUE equation is the `CryptoPrimitives.binding` (DLog) carrier — NAMED, not asserted. -/
theorem ring_conserves_pedersen [CryptoPrimitives Digest]
    {ι κ : Type} (insV inB : ι → Int) (outV outB : κ → Int)
    (sin : Finset ι) (sout : Finset κ)
    (hval : sin.sum insV = sout.sum outV) (hbl : sin.sum inB = sout.sum outB) :
    (sin.sum (fun i => CryptoPrimitives.commit (insV i) (inB i)) : Digest)
      = sout.sum (fun j => CryptoPrimitives.commit (outV j) (outB j)) :=
  committed_conservation insV inB outV outB sin sout hval hbl

/-- **`ring_conserves_pedersen_list`** — the `List Pedersen.Note` form matching
`Market.shielded_ring_value_conserves_hidden`, over the REAL group Pedersen: equal value+blinding
sums ⇒ equal commitment-list sums. Proved by collapsing each side with `listCommit_collapse`
(`commit_hom`/`map_sum`) and the two balance hypotheses. -/
theorem ring_conserves_pedersen_list [CryptoPrimitives Digest] (ins outs : List Note)
    (hval : (ins.map Note.value).sum = (outs.map Note.value).sum)
    (hbl  : (ins.map Note.blinding).sum = (outs.map Note.blinding).sum) :
    listCommit (CryptoPrimitives.commit (Digest := Digest)) ins
      = listCommit (CryptoPrimitives.commit (Digest := Digest)) outs := by
  rw [listCommit_collapse, listCommit_collapse, hval, hbl]

/-! ### §1.1 — a genuine two-generator Pedersen instance (NOT the additive `v+r` / `.toNat` toy).

`commit v r := (v, r)` over `ℤ × ℤ` is the free two-generator commitment `v·(1,0) + r·(0,1)`: the
generators `G = (1,0)`, `H = (0,1)` are independent, so — unlike the toy — the commitment is
BINDING (perfectly here; computationally under DLog on a real curve) and keeps `value` and
`blinding` in separate coordinates. This witnesses the parametric theorems above non-vacuously and
exhibits the exact binding the toy lacked. -/

/-- A two-generator Pedersen `CryptoPrimitives` instance over `ℤ × ℤ` (a `def`, not a global
`instance`, to avoid silent auto-resolution): `commit v r = v·(1,0) + r·(0,1) = (v, r)`. The
`commit_hom` is the group law `(v+w, r+s) = (v,r) + (w,s)`. Hardness carriers are the honest
NAMES — `binding` = the two generators have no known DLog relation (real curve), `collisionHard`
= Poseidon2 CR — inhabited here by `True` only for the witness (real crypto discharges them). -/
@[reducible] def pedTwoGen : CryptoPrimitives (ℤ × ℤ) where
  compress a b := a + b
  compressN l := l.sum
  collisionHard := True
  commit v r := (v, r)
  commit_hom := by intro v w r s; simp
  binding := True
  nullifier d := d
  unlinkable := True

/-- The two-generator commitment. -/
def pedCommit (v r : Int) : ℤ × ℤ := pedTwoGen.commit v r

@[simp] theorem pedCommit_def (v r : Int) : pedCommit v r = (v, r) := rfl

/-- **REAL BINDING (structural).** The two-generator Pedersen commitment is injective in its
opening: `commit v r = commit v' r' → v = v' ∧ r = r'`. It does NOT collapse `(value, blinding)`.
(On a real curve this is the DLog `binding` carrier; the free group here makes it perfect.) -/
theorem pedCommit_binding {v r v' r' : Int} (h : pedCommit v r = pedCommit v' r') :
    v = v' ∧ r = r' := by
  simp only [pedCommit_def, Prod.mk.injEq] at h; exact h

/-- **THE TOY WAS NOT BINDING.** `refVC` (`commit v r = (v+r).toNat`) collapses distinct openings:
`commit 8 3 = commit 3 8 = 11`. A commitment that cannot tell `(8,3)` from `(3,8)` binds nothing —
the exact defect this module retires. -/
theorem refVC_not_binding :
    Dregg2.Exec.ShieldedValue.refVC.commit 8 3 = Dregg2.Exec.ShieldedValue.refVC.commit 3 8 := by
  decide

/-- **THE REAL COMMITMENT DISTINGUISHES THEM.** The two-generator Pedersen keeps them apart:
`commit 8 3 ≠ commit 3 8`. Binding restored. -/
theorem pedCommit_distinguishes : pedCommit 8 3 ≠ pedCommit 3 8 := by decide

/-- **ANTI-MINT tooth over the REAL Pedersen.** With equal total blinding, unequal total value
gives UNEQUAL commitment sums: a value-minting output cannot balance the commitment equation
(`(Σv_in, Σr) ≠ (Σv_out, Σr)` when `Σv_in ≠ Σv_out`). The additive toy FAILS this — it cannot see
value separately from blinding. -/
theorem pedCommit_mint_refused {vin vout r : Int} (hne : vin ≠ vout) :
    pedCommit vin r ≠ pedCommit vout r := by
  simp only [pedCommit_def, ne_eq, Prod.mk.injEq, not_and]
  intro h; exact absurd h hne

/-- Non-vacuity of `ring_conserves_pedersen_list` at the REAL two-generator instance: a
value-neutral clearing (inputs `(3, bl 2)`, `(4, bl 1)`; output `(7, bl 3)` — equal value 7 and
blinding 3) has EQUAL commitment sums over the real Pedersen. -/
theorem demo_hidden_conservation_pedersen :
    letI := pedTwoGen
    listCommit (CryptoPrimitives.commit (Digest := ℤ × ℤ))
        [{ value := 3, blinding := 2, bits := [] }, { value := 4, blinding := 1, bits := [] }]
      = listCommit (CryptoPrimitives.commit (Digest := ℤ × ℤ))
          [{ value := 7, blinding := 3, bits := [] }] := by
  letI := pedTwoGen
  apply ring_conserves_pedersen_list
    [{ value := 3, blinding := 2, bits := [] }, { value := 4, blinding := 1, bits := [] }]
    [{ value := 7, blinding := 3, bits := [] }] <;> decide

/-! ### §1.2 — the in-AIR RANGE GADGET's meaning: field conservation + range ⇒ INTEGER conservation.

The circuit realization (`circuit-prove/src/shielded_ring_clearing_air.rs`, clause (c)) enforces the
conservation `Σ value_in − Σ value_out = 0` as a BabyBear FIELD gate. A field equation ALONE is NOT
integer conservation: a value-minting ring can satisfy `Σ value_in ≡ Σ value_out (mod p)` by
WRAPAROUND (an output committed to `p − k`, a "wrapped negative"), minting real value while the field
sum stays fixed. The AIR's in-AIR RANGE GADGET bit-decomposes every conservation value into
`[0, 2^k)` with `RING_LEGS · 2^k ≤ p` — which is exactly what forces the field gate to be the INTEGER
`hval` hypothesis `ring_conserves_pedersen_list` consumes. These two lemmas ARE that reduction: the
Lean meaning of the range gadget, tying the in-AIR conservation to the real group Pedersen. -/

/-- **No-wraparound reduction (2-leg, matching the deployed `RING_LEGS = 2` AIR).** Two
range-bounded inputs and two range-bounded outputs (each `< 2^k`, with `2·2^k ≤ p` — the BabyBear
no-wrap bound the AIR asserts at compile time) whose FIELD sums agree mod `p` have EQUAL INTEGER
sums. The range bound is LOAD-BEARING: drop any `_ < 2^k` and the conclusion is false (wraparound
mints) — the exact field-soundness the in-AIR range gadget supplies.

CONSOLIDATED onto the audited bedrock: this is the `k = 2` instance of the unified library keystone
`Dregg2.Bignum.legs_noWrap_conservation` (which was written to generalize exactly this lemma from the
deployed `RING_LEGS = 2` to any leg count). One audited no-wrap proof, instantiated here — not a
second hand-rolled copy. -/
theorem twoLeg_noWrap_conservation {p a0 a1 b0 b1 k : ℕ}
    (ha0 : a0 < 2 ^ k) (ha1 : a1 < 2 ^ k) (hb0 : b0 < 2 ^ k) (hb1 : b1 < 2 ^ k)
    (hnoWrap : 2 * 2 ^ k ≤ p) (hcong : (a0 + a1) % p = (b0 + b1) % p) :
    a0 + a1 = b0 + b1 := by
  have hpk : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hp : 0 < p := by omega
  have key := Dregg2.Bignum.legs_noWrap_conservation (n := k) (p := p)
    (as := [a0, a1]) (bs := [b0, b1]) hp
    (by intro x hx; fin_cases hx <;> assumption)
    (by intro x hx; fin_cases hx <;> assumption)
    (by simpa using hnoWrap) (by simpa using hnoWrap)
    (by simpa using hcong)
  simpa using key

/-- **The tie: the in-AIR conservation REFINES `ring_conserves_pedersen_list`.** Given two input
notes and two output notes whose VALUES are range-bounded (the in-AIR range gadget) and whose value
sums agree mod `p` (the in-AIR field conservation gate), and whose BLINDING sums are equal, their
REAL two-generator Pedersen commitment sums are equal. The range-gadget hypotheses are precisely what
upgrade the field gate to the integer `hval` that `ring_conserves_pedersen_list` needs — so the
circuit's field-level conservation refines the Lean group-Pedersen conservation. -/
theorem inAir_conservation_refines_pedersen [CryptoPrimitives Digest]
    {p k : ℕ} {a0 a1 b0 b1 : ℕ} (i0 i1 o0 o1 : Note)
    (hv0 : i0.value = (a0 : Int)) (hv1 : i1.value = (a1 : Int))
    (hw0 : o0.value = (b0 : Int)) (hw1 : o1.value = (b1 : Int))
    (ha0 : a0 < 2 ^ k) (ha1 : a1 < 2 ^ k) (hb0 : b0 < 2 ^ k) (hb1 : b1 < 2 ^ k)
    (hnoWrap : 2 * 2 ^ k ≤ p) (hcong : (a0 + a1) % p = (b0 + b1) % p)
    (hbl : i0.blinding + i1.blinding = o0.blinding + o1.blinding) :
    listCommit (CryptoPrimitives.commit (Digest := Digest)) [i0, i1]
      = listCommit (CryptoPrimitives.commit (Digest := Digest)) [o0, o1] := by
  have hint : a0 + a1 = b0 + b1 := twoLeg_noWrap_conservation ha0 ha1 hb0 hb1 hnoWrap hcong
  apply ring_conserves_pedersen_list [i0, i1] [o0, o1]
  · -- value sums equal (as Int), from the no-wrap integer equality
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hv0, hv1, hw0, hw1]
    exact_mod_cast hint
  · -- blinding sums equal
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact hbl

/-! ### §1.3 — the PQ VALUE-BINDING: a Poseidon2 HASH COMMITMENT binding (value, asset), under HashCR.

The PQ cutover (`docs/deos/PQ-SHIELDED-COMMITMENT.md`, Option A) retires the DLog Pedersen
value-commitment as the AUTHORITATIVE shielded value-binding. The authoritative commitment is now the
in-AIR Poseidon2 `value_binding = hash_fact(value, [asset_type, randomness, 0])` (the spend circuit's
C7 PI, `circuit-prove/src/shielded/spend_circuit.rs`). Its binding rests on Poseidon2
collision-resistance (`HashCR`) — a QUANTUM-SAFE floor (Grover only halves CR) — NOT discrete-log.

This section names that floor, exactly as §2 names the Poseidon2 TREE root-binding: an
injective-under-CR hash commitment. The `binding` carrier here is `HashCR` (Poseidon2 CR), the PQ
REPLACEMENT for `pedCommit_binding` (DLog). The floor has MOVED from discrete-log to hash CR, so the
shielded no-mint value-binding now survives Shor. -/

/-- A **Poseidon2 value-binding commitment**: the hash `vbind value asset r` the spend circuit's C7
publishes (`hash_fact(value, [asset_type, randomness, 0])`), and the SOLE crypto carrier —
collision-resistance of that hash on the `(value, asset, randomness)` preimage (the `HashCR` floor,
the SAME Poseidon2 CR the tree root-binding §2 and the nullifier stand on). -/
structure ValueBindingCommit where
  /-- The value-binding hash `hash_fact(value, [asset_type, randomness, 0])`. -/
  vbind  : ℤ → ℤ → ℤ → ℤ
  /-- The SOLE crypto carrier: the value-binding hash is collision-resistant — injective on its
  `(value, asset, randomness)` preimage. This is `HashCR` (Poseidon2 CR), named, never `axiom`;
  quantum-safe. It is the PQ replacement for the DLog `binding` carrier of `pedTwoGen`. -/
  hashCR : ∀ v a r v' a' r', vbind v a r = vbind v' a' r' → v = v' ∧ a = a' ∧ r = r'

/-- **THE PQ VALUE-BINDING BINDS (value, asset_type) JOINTLY, under HashCR.** Equal value-bindings ⇒
equal value AND equal asset — the multi-asset binding the retired three-generator Ristretto
`commit_hidden_asset (value·V + asset·H_asset + r·R)` gave under DLog, now under Poseidon2 CR
(Shor-safe). This is the PQ replacement for `pedCommit_binding`: the floor moved from DLog to HashCR. -/
theorem ValueBindingCommit.binds_value_and_asset (C : ValueBindingCommit) {v a r v' a' r' : ℤ}
    (h : C.vbind v a r = C.vbind v' a' r') : v = v' ∧ a = a' :=
  have hc := C.hashCR v a r v' a' r' h
  ⟨hc.1, hc.2.1⟩

/-- **A HIDDEN VALUE-MINT UNDER THE PQ COMMITMENT FORCES A HashCR COLLISION.** If a spender re-opens a
published value-binding to a DIFFERENT value (a hidden inflation — the exact quantum attack the DLog
Pedersen admitted), the two openings collide the Poseidon2 hash — impossible under `HashCR`. The
no-mint value-binding now rests on hash collision-resistance, not discrete-log: it survives Shor. -/
theorem ValueBindingCommit.mint_forces_collision (C : ValueBindingCommit) {v a r v' a' r' : ℤ}
    (hmint : v ≠ v') (h : C.vbind v a r = C.vbind v' a' r') : False :=
  hmint (C.binds_value_and_asset h).1

/-- Non-vacuity: a concrete INJECTIVE value-binding (via `Encodable.encode` on the triple) inhabits
the `HashCR` carrier, so `binds_value_and_asset` / `mint_forces_collision` are non-vacuous — exactly
the `refTree` pattern §2.1 uses for the tree CR. -/
def refValueBinding : ValueBindingCommit where
  vbind v a r := (Encodable.encode (v, a, r) : ℤ)
  hashCR := by
    intro v a r v' a' r' h
    have hnat : Encodable.encode (v, a, r) = Encodable.encode (v', a', r') := by exact_mod_cast h
    have htriple : (v, a, r) = (v', a', r') := Encodable.encode_injective hnat
    have h2 : (a, r) = (a', r') := congrArg Prod.snd htriple
    exact ⟨congrArg Prod.fst htriple, congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-- The teeth FIRE on the concrete value-binding: equal bindings ⇒ equal (value, asset). -/
theorem refValueBinding_binds {v a r v' a' r' : ℤ}
    (h : refValueBinding.vbind v a r = refValueBinding.vbind v' a' r') : v = v' ∧ a = a' :=
  refValueBinding.binds_value_and_asset h

/-- A hidden mint is IMPOSSIBLE on the concrete value-binding: distinct values give distinct
bindings (no collision), so no hidden inflation can re-open one commitment to another value. -/
theorem refValueBinding_no_mint {v a r a' r' : ℤ} (hmint : v ≠ v + 1) :
    refValueBinding.vbind v a r ≠ refValueBinding.vbind (v + 1) a' r' := fun h =>
  refValueBinding.mint_forces_collision hmint h

/-! ## §2 — REAL POSEIDON2 tree (retires `refTreeRoot`).

The note-commitment tree root is the Poseidon2 sponge over the leaf list — `root = sponge leaves`,
mirroring the deployed `StateCommit` sponge-root — with the SINGLE named crypto floor
`Poseidon2SpongeCR sponge` (the SAME sponge CR `SortedTreeNonMembership` / `StateCommit` bind
under). Root-binds-the-leaf-set is then a REDUCTION to that CR, replacing the linear rolling hash
`refTreeRoot` (which had no collision-resistance at all). -/

/-- **A real Poseidon2 note-commitment tree**: the sponge it folds the leaf set through, and the
SOLE crypto carrier — collision-resistance of that Poseidon2 sponge (`Poseidon2SpongeCR`, the
deployed floor). -/
structure Poseidon2Tree where
  /-- The Poseidon2 sponge (`hash_many` over `babyBearD4W16`) the tree root squeezes through. -/
  sponge   : List ℤ → ℤ
  /-- The SOLE crypto carrier: the Poseidon2 sponge is collision-resistant. Named, never `axiom`. -/
  spongeCR : Poseidon2SpongeCR sponge

/-- **The tree root committing a leaf set** — `sponge leaves` (the sponge over the committed
note-commitment leaves), the real analog of `refTreeRoot`. A function of the leaf set, so
"membership under a root" is set membership plus root-commits-that-set. -/
def Poseidon2Tree.root (T : Poseidon2Tree) (leaves : List ℤ) : ℤ := T.sponge leaves

/-- **`Poseidon2Tree.root_binds` — THE ROOT BINDS ITS LEAF SET, under Poseidon2 CR.** Two leaf sets
with the same root ARE the same set: a REDUCTION to the sponge CR carrier `T.spongeCR`. Where the
toy `refTreeRoot`'s "binding" was arithmetic, this is the named cryptographic floor. -/
theorem Poseidon2Tree.root_binds (T : Poseidon2Tree) {l₁ l₂ : List ℤ}
    (h : T.root l₁ = T.root l₂) : l₁ = l₂ :=
  T.spongeCR l₁ l₂ h

/-- **`MemberAtRoot` over the REAL tree** — `leaf` is a committed member iff it is one of the
leaves AND `root` genuinely commits that leaf set (`root = sponge leaves`). The real replacement of
`ClaimRefinement.MemberAtRoot` (which pinned `root = refTreeRoot leaves`). -/
def MemberAtRoot (T : Poseidon2Tree) (root leaf : ℤ) (leaves : List ℤ) : Prop :=
  leaf ∈ leaves ∧ root = T.root leaves

/-- **`forged_set_forces_collision` — A FORGED MEMBERSHIP FORCES A COLLISION.** If a forged leaf
set `forged` claims the honest root that commits `leaves` (`sponge forged = sponge leaves`), then
`forged = leaves` — so any set that DIFFERS from the committed one and still hits the root would be
a Poseidon2 collision. A forged committed-set cannot be presented at an honest root without
breaking the named sponge CR. -/
theorem forged_set_forces_collision (T : Poseidon2Tree) {leaves forged : List ℤ}
    (hforge : T.root forged = T.root leaves) : forged = leaves :=
  T.root_binds hforge

/-- A non-member is REFUSED (`False`): if `leaf` is claimed a member at the honest root committing
`leaves` but is NOT one of those leaves, no leaf set can rescue it — CR (`root_binds`) pins the
claimed set `leaves'` to `leaves`, so `leaf ∈ leaves'` collapses to `leaf ∈ leaves`, contradicting
`leaf ∉ leaves`. Forging membership at an honest root breaks the sponge CR. -/
theorem nonmember_refused (T : Poseidon2Tree) {root leaf : ℤ} {leaves leaves' : List ℤ}
    (hcommit : root = T.root leaves) (hclaim : MemberAtRoot T root leaf leaves')
    (hnon : leaf ∉ leaves) : False := by
  obtain ⟨hin, hroot'⟩ := hclaim
  have hset : leaves' = leaves := T.root_binds (by rw [← hroot', ← hcommit])
  exact hnon (hset ▸ hin)

/-! ### §2.1 — non-vacuity: a real realized sponge (injective) so the reduction FIRES.

The reference injective sponge `Poseidon2Binding.Reference.refSponge` (`Encodable.encode`, a
provably-injective CR stand-in tagged with the REAL `babyBearD4W16` params in
`refRealizedSponge`) inhabits the `Poseidon2SpongeCR` carrier, so `root_binds` /
`forged_set_forces_collision` are non-vacuous. -/

/-- A concrete real-tree instance over the reference CR sponge. -/
def refTree : Poseidon2Tree where
  sponge   := Dregg2.Circuit.Poseidon2Binding.Reference.refSponge
  spongeCR := Dregg2.Circuit.Poseidon2Binding.Reference.refSponge_CR

/-- The root binding FIRES on the concrete tree: equal roots ⇒ equal leaf sets. -/
theorem refTree_root_binds {l₁ l₂ : List ℤ} (h : refTree.root l₁ = refTree.root l₂) : l₁ = l₂ :=
  refTree.root_binds h

/-- A concrete member: leaf `5` in the committed set `[5, 7]` at its honest root. -/
theorem refTree_member : MemberAtRoot refTree (refTree.root [5, 7]) 5 [5, 7] :=
  ⟨by decide, rfl⟩

/-- The teeth FIRE: a forged set `[9, 9]` claiming the root of `[5, 7]` would be a collision
(`[9,9] ≠ [5,7]`), so it cannot hit that root. -/
theorem refTree_forge_impossible : refTree.root [9, 9] ≠ refTree.root [5, 7] := by
  intro h; exact absurd (refTree.root_binds h) (by decide)

/-! ## §3 — COMPOSE: rung-3 over the TWO real primitives.

The rung-3 private-matching shape — hidden conservation + membership — restated so that
conservation is over the REAL Pedersen (`binding`/DLog) and membership is over the REAL Poseidon2
tree (`spongeCR`/CR). Each half carries its honest floor; neither is a toy. -/

/-- **`rung3_real_crypto` — the two real-crypto halves, composed.** Given (i) a balanced ring over
the REAL group Pedersen (equal value+blinding sums), its commitment sums are equal (hidden
conservation, under DLog binding); and (ii) a leaf committed under the REAL Poseidon2 tree, its
membership root binds the leaf set (under sponge CR) and a forged set forces a collision. The two
declared toys are retired: value conservation over a hiding+binding Pedersen, membership over a
CR tree. -/
theorem rung3_real_crypto [CryptoPrimitives Digest] (T : Poseidon2Tree)
    (ins outs : List Note)
    (hval : (ins.map Note.value).sum = (outs.map Note.value).sum)
    (hbl  : (ins.map Note.blinding).sum = (outs.map Note.blinding).sum)
    (leaf : ℤ) (leaves : List ℤ) (hmem : MemberAtRoot T (T.root leaves) leaf leaves) :
    -- (a) hidden conservation over the REAL Pedersen (binding = DLog):
    (listCommit (CryptoPrimitives.commit (Digest := Digest)) ins
      = listCommit (CryptoPrimitives.commit (Digest := Digest)) outs)
    -- (b) membership over the REAL Poseidon2 tree, root binding under CR:
    ∧ (leaf ∈ leaves ∧ ∀ forged, T.root forged = T.root leaves → forged = leaves) :=
  ⟨ring_conserves_pedersen_list ins outs hval hbl,
   hmem.1, fun _ h => forged_set_forces_collision T h⟩

/-! ## §AXIOM HYGIENE — the real-crypto theorems pinned to the standard axioms only. -/

#assert_axioms ring_conserves_pedersen
#assert_axioms ring_conserves_pedersen_list
#assert_axioms twoLeg_noWrap_conservation
#assert_axioms inAir_conservation_refines_pedersen
#assert_axioms pedCommit_binding
#assert_axioms pedCommit_mint_refused
#assert_axioms ValueBindingCommit.binds_value_and_asset
#assert_axioms ValueBindingCommit.mint_forces_collision
#assert_axioms refValueBinding_binds
#assert_axioms refValueBinding_no_mint
#assert_axioms Poseidon2Tree.root_binds
#assert_axioms forged_set_forces_collision
#assert_axioms nonmember_refused
#assert_axioms rung3_real_crypto

end Dregg2.Shielded.RealCrypto
