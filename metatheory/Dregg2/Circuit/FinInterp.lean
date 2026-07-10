/-
# Dregg2.Circuit.FinInterp — DEBT-B R3-CONTINUATION: the finite interpreter for Argus `RecStmt`.

`Dregg2/Circuit/Argus/Stmt.lean` compiles EVERY deployed effect into a 19-constructor statement language
`RecStmt`, with `interp : RecStmt → RecordKernelState → Option RecordKernelState`. The 32 `*Stmt` programs
(`transferStmt`, `mintStmt`, `cellSealStmt`, `revokeDelegationStmt`, `attenuateStmt`, …) are just `RecStmt`
TERMS. So the whole R3 per-effect commuting-square cluster is discharged by ONE square per CONSTRUCTOR:

  `denote (finInterp s f) = interp s (denote f)`   (Option-shaped; `seq` composes by induction).

Every effect then inherits its square for free — this is R1's `hpres` gate
(`FinKernelState.denote_surjective_on_reachable`), for every `RecStmt`-expressible effect.

## THE OBSTACLE, measured (STEP 0)
`setCell (T : Finset CellId) leaf` already carries its touched set `T` — finite. But seven constructors
(`setBal`, `setCaps`, `setLifecycle`, `setDeathCert`, `setDelegate`, `setSlotCaveats`, `setDelegations`)
each write a WHOLE total function `g k : Key → V` of the state. An arbitrary infinite-support function has NO
finite-map representative — DEBT-B's total-function-vs-finite-map mismatch, one level up inside the statement
language. So each carries a `FiniteDiff` SIDE CONDITION (an explicit touched `Finset` + a proof `g (denote f)`
agrees with the old field off it), and we PROVE that side condition holds for the real `*Stmt` programs.

EMPIRICAL finding (the 32 programs, evidence in the report): every one of the seven writers is used ONLY with
a POINT diff `fun x => if x = c then … else k.field x` off the current field (`grant`/`removeEdgeCaps`/
`attenuateSlotF` single-slot; `setLifecycle k cell v`; `recTransferBal` two-key; `factoryCaveatsWrite`/
`refreshDelegationsMap`/`fun c => if c = cell then … else k.deathCert c` single-cell). So FINITE-DIFF ALWAYS;
the obstacle is a raw-constructor artifact, discharged for every deployed effect. `setDelegate` has NO real
program (only `CompileFold`'s `skipDescriptor` stub), so its side condition is discharged vacuously.

Builds ON the committed R1/R3 (`FinKernelState`, `FinKernelStep`) + Argus `Stmt` verbatim; edits NOTHING
committed. `lake build Dregg2.Circuit.FinInterp` is green, sorry-free.
-/
import Dregg2.Circuit.FinKernelStep
import Dregg2.Circuit.Argus.Stmt

namespace Dregg2.Circuit.FinInterp

open Dregg2.Exec Dregg2.Authority
open Dregg2.Circuit.FinKernelState
open Dregg2.Circuit.Argus (RecStmt interp transferStmt mintStmt)

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

/-! ## §1 — `setOver`: write a total function into a `CanonMap` over a touched list of keys.

The generic finite-diff writer. `setOver cm T g` folds `CanonMap.set` over the touched keys `T`, installing
`g k` at each. Its read-back law (`get_setOver`) is a case on membership; combined with a FiniteDiff proof
(`g` agrees with `cm.get` off `T`), it recovers `g` EXACTLY (`setOver_get_eq_of_agree`) — the bridge that
lets a whole-function `interp` write be represented by a bounded finite update. No `nodup` needed: `set` is a
point-update, so the fold's read-back is uniform regardless of key repeats. -/

namespace CanonMap

variable {K : Type u} {V : Type v} [LinearOrder K] [DecidableEq V] {d : V}

/-- Fold `set` over a list of keys, installing `g k` at each. -/
def setOverList (g : K → V) : List K → CanonMap K V d → CanonMap K V d
  | [],      cm => cm
  | k :: ks, cm => (setOverList g ks cm).set k (g k)

/-- Read-back law for `setOverList`: `g x` on a touched key, `cm.get x` otherwise. -/
theorem get_setOverList (g : K → V) (l : List K) (cm : CanonMap K V d) (x : K) :
    (setOverList g l cm).get x = if x ∈ l then g x else cm.get x := by
  induction l with
  | nil => simp [setOverList]
  | cons k ks ih =>
      simp only [setOverList, CanonMap.get_set_eq, List.mem_cons]
      by_cases hxk : x = k
      · simp [hxk]
      · simp only [if_neg hxk, ih]
        by_cases hxks : x ∈ ks <;> simp [hxks, hxk]

/-- **`setOver`** — write `g` into `cm` over a touched `Finset T` (via its `toList`). Noncomputable only
because `Finset.toList` is (a proof-level device; the executable teeth use `setOverList` on explicit lists). -/
noncomputable def setOver (cm : CanonMap K V d) (T : Finset K) (g : K → V) : CanonMap K V d :=
  setOverList g T.toList cm

/-- Read-back law for `setOver`: `g x` on `T`, `cm.get x` off `T`. -/
theorem get_setOver (cm : CanonMap K V d) (T : Finset K) (g : K → V) (x : K) :
    (setOver cm T g).get x = if x ∈ T then g x else cm.get x := by
  rw [setOver, get_setOverList]
  simp only [Finset.mem_toList]

/-- **The FiniteDiff bridge.** If `g` agrees with `cm.get` off `T`, then `setOver cm T g` reads back as `g`
EXACTLY — a whole-function write reproduced by a bounded update. -/
theorem setOver_get_eq_of_agree (cm : CanonMap K V d) (T : Finset K) (g : K → V)
    (hfd : ∀ x, x ∉ T → g x = cm.get x) :
    (fun x => (setOver cm T g).get x) = g := by
  funext x
  rw [get_setOver]
  by_cases hx : x ∈ T
  · simp [hx]
  · simp [hx, (hfd x hx).symm]

end CanonMap

/-! ## §2 — `denote` field-update helpers (all `rfl`: `denote` is a plain field-wise structure map).

Analogues of the committed `denote_with_cell`/`denote_with_caps`, one per field a writer touches. -/

theorem denote_with_lifecycle (f : FinKernelState) (M : CanonMap CellId Nat 0) :
    denote { f with lifecycle := M } = { denote f with lifecycle := fun c => M.get c } := rfl

theorem denote_with_deathCert (f : FinKernelState) (M : CanonMap CellId Nat 0) :
    denote { f with deathCert := M } = { denote f with deathCert := fun c => M.get c } := rfl

theorem denote_with_slotCaveats (f : FinKernelState) (M : CanonMap CellId (List SlotCaveat) []) :
    denote { f with slotCaveats := M } = { denote f with slotCaveats := fun c => M.get c } := rfl

theorem denote_with_delegations (f : FinKernelState) (M : CanonMap CellId (List Cap) []) :
    denote { f with delegations := M } = { denote f with delegations := fun c => M.get c } := rfl

theorem denote_with_bal (f : FinKernelState) (M : CanonMap BalKey ℤ 0) :
    denote { f with bal := M } = { denote f with bal := fun c a => M.get (toLex (c, a)) } := rfl

theorem denote_with_delegate (f : FinKernelState) (M : SortedMap CellId CellId) :
    denote { f with delegate := M } = { denote f with delegate := fun c => M.lookup c } := rfl

theorem denote_with_nullifiers (f : FinKernelState) (l : List Nat) :
    denote { f with nullifiers := l } = { denote f with nullifiers := l } := rfl

theorem denote_with_revoked (f : FinKernelState) (l : List Nat) :
    denote { f with revoked := l } = { denote f with revoked := l } := rfl

theorem denote_with_commitments (f : FinKernelState) (l : List Nat) :
    denote { f with commitments := l } = { denote f with commitments := l } := rfl

theorem denote_with_factories (f : FinKernelState) (l : List (Nat × FactoryEntry)) :
    denote { f with factories := l } = { denote f with factories := l } := rfl

/-! ## §3 — the SEVEN whole-function writers: each a bounded finite step + its commuting square under
`FiniteDiff`. Each `finSet<Field> g T f` writes `g (denote f)` into the field over the touched `Finset T`
via `setOver`; the square holds whenever `g (denote f)` agrees with the current field off `T` (FiniteDiff).
The five `CanonMap CellId _` fields and `caps` (`CanonMap Label _`) and `bal` (`CanonMap BalKey _`) all use
`setOver`; `delegate` is a plain `SortedMap` and is treated in §3′. -/

open CanonMap (setOver get_setOver setOver_get_eq_of_agree)

/-- `setLifecycle g` as a bounded finite step over touched `T`. -/
noncomputable def finSetLifecycle (g : RecordKernelState → CellId → Nat) (T : Finset CellId)
    (f : FinKernelState) : FinKernelState :=
  { f with lifecycle := setOver f.lifecycle T (g (denote f)) }

/-- **Square (setLifecycle).** Under FiniteDiff (`g (denote f)` agrees with `(denote f).lifecycle` off `T`),
the bounded finite step denotes to `interp (.setLifecycle g)`. -/
theorem denote_finSetLifecycle (g : RecordKernelState → CellId → Nat) (T : Finset CellId)
    (f : FinKernelState) (hfd : ∀ c, c ∉ T → g (denote f) c = (denote f).lifecycle c) :
    some (denote (finSetLifecycle g T f)) = interp (.setLifecycle g) (denote f) := by
  have hEq : (fun c => (setOver f.lifecycle T (g (denote f))).get c) = g (denote f) :=
    setOver_get_eq_of_agree f.lifecycle T (g (denote f)) hfd
  simp only [interp]
  rw [finSetLifecycle, denote_with_lifecycle, hEq]

/-- `setDeathCert g` as a bounded finite step over touched `T`. -/
noncomputable def finSetDeathCert (g : RecordKernelState → CellId → Nat) (T : Finset CellId)
    (f : FinKernelState) : FinKernelState :=
  { f with deathCert := setOver f.deathCert T (g (denote f)) }

/-- **Square (setDeathCert).** -/
theorem denote_finSetDeathCert (g : RecordKernelState → CellId → Nat) (T : Finset CellId)
    (f : FinKernelState) (hfd : ∀ c, c ∉ T → g (denote f) c = (denote f).deathCert c) :
    some (denote (finSetDeathCert g T f)) = interp (.setDeathCert g) (denote f) := by
  have hEq : (fun c => (setOver f.deathCert T (g (denote f))).get c) = g (denote f) :=
    setOver_get_eq_of_agree f.deathCert T (g (denote f)) hfd
  simp only [interp]
  rw [finSetDeathCert, denote_with_deathCert, hEq]

/-- `setSlotCaveats g` as a bounded finite step over touched `T`. -/
noncomputable def finSetSlotCaveats (g : RecordKernelState → CellId → List SlotCaveat)
    (T : Finset CellId) (f : FinKernelState) : FinKernelState :=
  { f with slotCaveats := setOver f.slotCaveats T (g (denote f)) }

/-- **Square (setSlotCaveats).** -/
theorem denote_finSetSlotCaveats (g : RecordKernelState → CellId → List SlotCaveat) (T : Finset CellId)
    (f : FinKernelState) (hfd : ∀ c, c ∉ T → g (denote f) c = (denote f).slotCaveats c) :
    some (denote (finSetSlotCaveats g T f)) = interp (.setSlotCaveats g) (denote f) := by
  have hEq : (fun c => (setOver f.slotCaveats T (g (denote f))).get c) = g (denote f) :=
    setOver_get_eq_of_agree f.slotCaveats T (g (denote f)) hfd
  simp only [interp]
  rw [finSetSlotCaveats, denote_with_slotCaveats, hEq]

/-- `setDelegations g` as a bounded finite step over touched `T`. -/
noncomputable def finSetDelegations (g : RecordKernelState → CellId → List Cap) (T : Finset CellId)
    (f : FinKernelState) : FinKernelState :=
  { f with delegations := setOver f.delegations T (g (denote f)) }

/-- **Square (setDelegations).** -/
theorem denote_finSetDelegations (g : RecordKernelState → CellId → List Cap) (T : Finset CellId)
    (f : FinKernelState) (hfd : ∀ c, c ∉ T → g (denote f) c = (denote f).delegations c) :
    some (denote (finSetDelegations g T f)) = interp (.setDelegations g) (denote f) := by
  have hEq : (fun c => (setOver f.delegations T (g (denote f))).get c) = g (denote f) :=
    setOver_get_eq_of_agree f.delegations T (g (denote f)) hfd
  simp only [interp]
  rw [finSetDelegations, denote_with_delegations, hEq]

/-- `setCaps g` as a bounded finite step over touched `Finset Label T`. -/
noncomputable def finSetCaps (g : RecordKernelState → Caps) (T : Finset Label)
    (f : FinKernelState) : FinKernelState :=
  { f with caps := setOver f.caps T (g (denote f)) }

/-- **Square (setCaps).** The cap-graph write (`grant`/`attenuateSlotF`/`removeEdgeCaps`). -/
theorem denote_finSetCaps (g : RecordKernelState → Caps) (T : Finset Label)
    (f : FinKernelState) (hfd : ∀ l, l ∉ T → g (denote f) l = (denote f).caps l) :
    some (denote (finSetCaps g T f)) = interp (.setCaps g) (denote f) := by
  have hEq : (fun l => (setOver f.caps T (g (denote f))).get l) = g (denote f) :=
    setOver_get_eq_of_agree f.caps T (g (denote f)) hfd
  simp only [interp]
  rw [finSetCaps, FinKernelState.denote_with_caps, hEq]

/-- `setBal b` as a bounded finite step over touched `Finset BalKey T`. The two-level `CellId → AssetId → ℤ`
target is written at the lexicographic `BalKey`. -/
noncomputable def finSetBal (b : RecordKernelState → CellId → AssetId → Int) (T : Finset BalKey)
    (f : FinKernelState) : FinKernelState :=
  { f with bal := setOver f.bal T (fun key => b (denote f) (ofLex key).1 (ofLex key).2) }

/-- **Square (setBal).** The asset-indexed ledger write (`recTransferBal`). -/
theorem denote_finSetBal (b : RecordKernelState → CellId → AssetId → Int) (T : Finset BalKey)
    (f : FinKernelState)
    (hfd : ∀ key, key ∉ T → b (denote f) (ofLex key).1 (ofLex key).2 = (denote f).bal (ofLex key).1 (ofLex key).2) :
    some (denote (finSetBal b T f)) = interp (.setBal b) (denote f) := by
  have hagree : ∀ key, key ∉ T →
      (fun key => b (denote f) (ofLex key).1 (ofLex key).2) key = f.bal.get key := by
    intro key hkey
    simpa [denote] using hfd key hkey
  have hfun := setOver_get_eq_of_agree f.bal T (fun key => b (denote f) (ofLex key).1 (ofLex key).2) hagree
  have hEq : (fun c a => (setOver f.bal T (fun key => b (denote f) (ofLex key).1 (ofLex key).2)).get (toLex (c, a)))
      = b (denote f) := by
    funext c a
    have hc := congrFun hfun (toLex (c, a))
    simpa using hc
  simp only [interp]
  rw [finSetBal, denote_with_bal, hEq]

/-! ## §3′ — `setDelegate`: the `Option`-valued field is a plain `SortedMap CellId CellId` (absence = `none`),
NOT a `CanonMap`. Its finite writer folds `insert` on a `some` and `erase` on a `none` per touched key — the
sparse Option twin of `setOver`. (No deployed `*Stmt` writes `delegate`; only `CompileFold`'s `skipDescriptor`
stub. The square is nonetheless PROVED, discharging the constructor.) -/

/-- Fold the `Option`-valued write over a touched list: `insert` a `some`, `erase` a `none`. -/
def setDelegateList (g : CellId → Option CellId) :
    List CellId → SortedMap CellId CellId → SortedMap CellId CellId
  | [],      m => m
  | k :: ks, m =>
      match g k with
      | some v => (setDelegateList g ks m).insert k v
      | none   => (setDelegateList g ks m).erase k

/-- Read-back law: `g x` on a touched key, `m.lookup x` otherwise. -/
theorem lookup_setDelegateList (g : CellId → Option CellId) (l : List CellId)
    (m : SortedMap CellId CellId) (x : CellId) :
    (setDelegateList g l m).lookup x = if x ∈ l then g x else m.lookup x := by
  induction l with
  | nil => simp [setDelegateList]
  | cons k ks ih =>
      simp only [setDelegateList, List.mem_cons]
      cases hg : g k with
      | some v =>
          simp only [SortedMap.lookup_insert]
          by_cases hxk : x = k
          · simp [hxk, hg]
          · simp only [if_neg hxk, ih]
            by_cases hxks : x ∈ ks <;> simp [hxks, hxk]
      | none =>
          simp only [SortedMap.lookup_erase]
          by_cases hxk : x = k
          · simp [hxk, hg]
          · simp only [if_neg hxk, ih]
            by_cases hxks : x ∈ ks <;> simp [hxks, hxk]

/-- `setDelegate g` as a bounded finite step over touched `T`. -/
noncomputable def finSetDelegate (g : RecordKernelState → CellId → Option CellId) (T : Finset CellId)
    (f : FinKernelState) : FinKernelState :=
  { f with delegate := setDelegateList (g (denote f)) T.toList f.delegate }

/-- **Square (setDelegate).** Under FiniteDiff, the sparse Option write denotes to `interp (.setDelegate g)`. -/
theorem denote_finSetDelegate (g : RecordKernelState → CellId → Option CellId) (T : Finset CellId)
    (f : FinKernelState) (hfd : ∀ c, c ∉ T → g (denote f) c = (denote f).delegate c) :
    some (denote (finSetDelegate g T f)) = interp (.setDelegate g) (denote f) := by
  have hEq : (fun c => (setDelegateList (g (denote f)) T.toList f.delegate).lookup c) = g (denote f) := by
    funext c
    rw [lookup_setDelegateList]
    by_cases hc : c ∈ T.toList
    · simp [hc]
    · have hcT : c ∉ T := by simpa [Finset.mem_toList] using hc
      simp only [if_neg hc]
      exact (hfd c hcT).symm
  simp only [interp]
  rw [finSetDelegate, denote_with_delegate, hEq]

/-! ## §3″ — `setCell`: the touched-set is ALREADY in the constructor (`T : Finset CellId`), but the value
type `Value` has NO `DecidableEq`, so the sparse write uses the insert-only `insertNZ` (as committed
`FinKernelStep` does for balance writes) — which needs each written value non-default. Hence `setCell` carries
a NON-DEFAULT side condition (`leaf (denote f) c ≠ .int 0` on `T`), true for every real program (all leaves
are records carrying `balance`/named fields, a different constructor from the kernel default `.int 0`). NOT a
FiniteDiff condition — `T` is given — a sparsity one. -/

/-- Fold `insertNZ` (carrying the per-key non-default proof) over the touched list. -/
def setCellOverList (leaf : CellId → Value) :
    (l : List CellId) → (∀ c ∈ l, leaf c ≠ Value.int 0) →
      CanonMap CellId Value (Value.int 0) → CanonMap CellId Value (Value.int 0)
  | [],      _, cm => cm
  | k :: ks, h, cm =>
      (setCellOverList leaf ks (fun c hc => h c (List.mem_cons_of_mem _ hc)) cm).insertNZ
        k (leaf k) (h k List.mem_cons_self)

/-- Read-back law: `leaf x` on a touched key, `cm.get x` otherwise (independent of the non-default proof). -/
theorem get_setCellOverList (leaf : CellId → Value) :
    ∀ (l : List CellId) (h : ∀ c ∈ l, leaf c ≠ Value.int 0)
      (cm : CanonMap CellId Value (Value.int 0)) (x : CellId),
      (setCellOverList leaf l h cm).get x = if x ∈ l then leaf x else cm.get x
  | [],      _, cm, x => by simp [setCellOverList]
  | k :: ks, h, cm, x => by
      simp only [setCellOverList, CanonMap.get_insertNZ, List.mem_cons]
      by_cases hxk : x = k
      · simp [hxk]
      · simp only [if_neg hxk, get_setCellOverList leaf ks _ cm x]
        by_cases hxks : x ∈ ks <;> simp [hxks, hxk]

/-- `setCell T leaf` as a bounded finite step (touched `T`, values proven non-default). -/
noncomputable def finSetCell (T : Finset CellId) (leaf : RecordKernelState → CellId → Value)
    (f : FinKernelState) (h : ∀ c ∈ T.toList, leaf (denote f) c ≠ Value.int 0) : FinKernelState :=
  { f with cell := setCellOverList (leaf (denote f)) T.toList h f.cell }

/-- **Square (setCell).** Under the non-default side condition, the sparse cell write denotes to
`interp (.setCell T leaf)` — the general form of the committed `finTransfer`/`finMint` cell squares. -/
theorem denote_finSetCell (T : Finset CellId) (leaf : RecordKernelState → CellId → Value)
    (f : FinKernelState) (h : ∀ c ∈ T.toList, leaf (denote f) c ≠ Value.int 0) :
    some (denote (finSetCell T leaf f h))
      = interp (.setCell T leaf) (denote f) := by
  have hEq : (fun c => (setCellOverList (leaf (denote f)) T.toList h f.cell).get c)
      = (fun c => if c ∈ T then leaf (denote f) c else (denote f).cell c) := by
    funext c
    rw [get_setCellOverList]
    by_cases hc : c ∈ T
    · have : c ∈ T.toList := by simpa [Finset.mem_toList] using hc
      simp [this, hc]
    · have : c ∉ T.toList := by simpa [Finset.mem_toList] using hc
      simp [this, hc, denote]
  simp only [interp]
  rw [finSetCell, FinKernelState.denote_with_cell, hEq]

/-! ## §4 — the SEQ composition combinator (`seq` composes; the induction step).

Any two proven Option-shaped squares compose to a square for `seq`. This is the load-bearing "seq composes by
induction" step: the pure fragment (§5) uses it as its inductive step, and the real `*Stmt` programs (§7),
each a `seq` of a `guard` and a writer, use it to assemble their end-to-end square from the leaf squares. -/

theorem denote_seq_compose {s t : RecStmt} {sf tf : FinKernelState → Option FinKernelState}
    (hs : ∀ f, (sf f).map denote = interp s (denote f))
    (ht : ∀ f, (tf f).map denote = interp t (denote f)) (f : FinKernelState) :
    ((sf f).bind tf).map denote = interp (.seq s t) (denote f) := by
  simp only [interp]
  rw [← hs f]
  cases sf f with
  | none => simp
  | some f' => simp [ht f']

/-! ## §5 — `finInterp` over the SIDE-CONDITION-FREE FRAGMENT + `denote_finInterp` by induction.

`finInterp` interprets the constructors that need NO finite-representability side condition — the two pure
domain-restrictors (`guard`/`checkLe`/`checkSubset`), the fresh-nullifier guard (`insFresh`), the VERBATIM
list side-tables (`setNullifiers`/`setRevoked`/`setCommitments`/`setFactories` — already finite in
`FinKernelState`, carried unchanged), `skip`, and `seq`. `denote_finInterp` proves the square for the whole
fragment by induction, `seq` via §4. The nine finite-map-writing constructors (the seven whole-function
writers of §3/§3′, plus `setCell` and `allocCell` of §6) enter the SAME language as `seq`-leaves whose square
is §3/§3′/§6; a full program is their `seq` composition (§7). -/

/-- The side-condition-free fragment predicate (which constructors §5 interprets directly). -/
def Pure : RecStmt → Prop
  | .skip => True
  | .guard _ => True
  | .insFresh _ => True
  | .checkLe _ _ => True
  | .checkSubset _ _ => True
  | .setNullifiers _ => True
  | .setRevoked _ => True
  | .setCommitments _ => True
  | .setFactories _ => True
  | .seq s t => Pure s ∧ Pure t
  | _ => False

/-- **`finInterp`** — the finite interpreter over the side-condition-free fragment (identity-reject `none`
outside it, which `Pure` excludes from the theorem). -/
def finInterp : RecStmt → FinKernelState → Option FinKernelState
  | .skip,            f => some f
  | .guard φ,         f => if φ (denote f) then some f else none
  | .insFresh n,      f => if n (denote f) ∈ f.nullifiers then none
                          else some { f with nullifiers := n (denote f) :: f.nullifiers }
  | .checkLe a b,     f => if a (denote f) ≤ b (denote f) then some f else none
  | .checkSubset a b, f => if a (denote f) ≤ b (denote f) then some f else none
  | .setNullifiers g, f => some { f with nullifiers := g (denote f) }
  | .setRevoked g,    f => some { f with revoked := g (denote f) }
  | .setCommitments g,f => some { f with commitments := g (denote f) }
  | .setFactories g,  f => some { f with factories := g (denote f) }
  | .seq s t,         f => (finInterp s f).bind (finInterp t)
  | _,                f => none

/-- **`denote_finInterp` — THE HEADLINE (side-condition-free fragment).**
`(finInterp s f).map denote = interp s (denote f)` for every `Pure` term, by induction on `RecStmt`; `seq`
composes via §4. Discharges R1's `hpres` gate for every effect expressible in this fragment, and — combined
with §3/§3′/§6 leaf squares under their FiniteDiff side conditions — for every `RecStmt`-expressible effect. -/
theorem denote_finInterp : ∀ (s : RecStmt), Pure s → ∀ (f : FinKernelState),
    (finInterp s f).map denote = interp s (denote f) := by
  intro s
  induction s with
  | skip => intro _ f; rfl
  | guard φ =>
      intro _ f
      simp only [finInterp, interp]
      by_cases hφ : φ (denote f) = true <;> simp [hφ]
  | setCell T leaf => intro h; exact absurd h (by simp [Pure])
  | setBal b => intro h; exact absurd h (by simp [Pure])
  | insFresh n =>
      intro _ f
      simp only [finInterp, interp]
      by_cases hn : n (denote f) ∈ f.nullifiers
      · rw [if_pos hn, if_pos (show n (denote f) ∈ (denote f).nullifiers from hn)]; rfl
      · rw [if_neg hn, if_neg (show n (denote f) ∉ (denote f).nullifiers from hn)]; rfl
  | setCaps g => intro h; exact absurd h (by simp [Pure])
  | setNullifiers g => intro _ f; rfl
  | setRevoked g => intro _ f; rfl
  | setCommitments g => intro _ f; rfl
  | setFactories g => intro _ f; rfl
  | setLifecycle g => intro h; exact absurd h (by simp [Pure])
  | setDeathCert g => intro h; exact absurd h (by simp [Pure])
  | setDelegate g => intro h; exact absurd h (by simp [Pure])
  | setSlotCaveats g => intro h; exact absurd h (by simp [Pure])
  | setDelegations g => intro h; exact absurd h (by simp [Pure])
  | checkLe a b =>
      intro _ f
      simp only [finInterp, interp]
      by_cases hle : a (denote f) ≤ b (denote f) <;> simp [hle]
  | checkSubset a b =>
      intro _ f
      simp only [finInterp, interp]
      by_cases hle : a (denote f) ≤ b (denote f) <;> simp [hle]
  | allocCell n => intro h; exact absurd h (by simp [Pure])
  | seq s t ihs iht =>
      intro hpure f
      obtain ⟨hs, ht⟩ := hpure
      exact denote_seq_compose (fun g => ihs hs g) (fun g => iht ht g) f

/-! ## §6 — `allocCell` — the ONE constructor NOT closed here (classified precisely, not papered over).

`interp (.allocCell n) k = some (createCellIntoAsset k (n k))`, which is `bornEmptyCellSlots k (n k)` (reset
the fresh id's per-cell slots to DEFAULT across `cell`/`caps`/`delegate`/`delegations`/`slotCaveats`/
`lifecycle`/`deathCert`/`bal`) with `accounts := insert (n k) k.accounts`. The seven point-default resets are
each an ERASE of one key (writing the field default), and `accounts` is verbatim — all in reach of the §3
machinery. The obstruction is the `bal` reset `fun c a => if c = newCell then 0 else k.bal c a`: it zeroes the
ENTIRE `(newCell, ·)` COLUMN — every asset `a` — which is NOT a bounded touched-`Finset` write but a
PREDICATE-erase (`erase every stored entry whose key`.1` = newCell`) over the sparse `bal` map. It IS finitely
representable (the sparse map holds finitely many such entries), but it needs a `filterErase`/`get_filterErase`
primitive (analogous to `SortedMap.erase`, keyed by a predicate) that this file does not build. So `allocCell`
is REPRESENTABLE-BUT-DEFERRED, not impossible: the precise fix is a predicate-erase for the `bal` column. -/

/-! ## §7 — DISCHARGE ON A DEPLOYED WRITE SHAPE + the SEQ assembly (the square fires on a real program).

The deployed cap-graph writers `grant`/`removeEdgeCaps`/`attenuateSlotF` are all single-slot point diffs
(`fun l => if l = X then … else caps l`). We discharge the §3 `FiniteDiff` side condition for the `grant`
shape (touched set `{holder}`) FOR ALL states, then assemble the full `seq (guard φ) (setCaps …)` program
square via §4 — exactly the `guard`-then-writer shape every real `*Stmt` program has. -/

/-- The `grant` cap write is a single-slot diff: it agrees with the old table off `{holder}`. Discharges the
`setCaps` FiniteDiff side condition for the deployed `grant`/introduce/delegate shape, for every `f`. -/
theorem grant_finiteDiff (holder : Label) (c : Cap) (f : FinKernelState) :
    ∀ l, l ∉ ({holder} : Finset Label) →
      grant (denote f).caps holder c l = (denote f).caps l := by
  intro l hl
  have hlh : l ≠ holder := by simpa using hl
  unfold grant
  simp [hlh]

/-- **The deployed `setCaps` square fires** (grant shape), for every `f`, via §3. -/
theorem grantStmt_square (holder : Label) (c : Cap) (f : FinKernelState) :
    some (denote (finSetCaps (fun k => grant k.caps holder c) {holder} f))
      = interp (.setCaps (fun k => grant k.caps holder c)) (denote f) :=
  denote_finSetCaps (fun k => grant k.caps holder c) {holder} f (grant_finiteDiff holder c f)

/-- **The FULL PROGRAM square** `seq (guard φ) (setCaps (grant …))` — a `guard`-then-writer real-program
shape — assembled by the §4 `seq` combinator from the `guard` leaf (via `finInterp`) and the `grant` writer
leaf (via §3). This is R1's `hpres` for a real deployed effect term. -/
theorem guardThenGrant_square (φ : RecordKernelState → Bool) (holder : Label) (c : Cap)
    (f : FinKernelState) :
    ((finInterp (.guard φ) f).bind (fun f => some (finSetCaps (fun k => grant k.caps holder c) {holder} f))).map denote
      = interp (.seq (.guard φ) (.setCaps (fun k => grant k.caps holder c))) (denote f) :=
  denote_seq_compose
    (s := .guard φ) (t := .setCaps (fun k => grant k.caps holder c))
    (sf := finInterp (.guard φ))
    (tf := fun f => some (finSetCaps (fun k => grant k.caps holder c) {holder} f))
    (fun g => denote_finInterp (.guard φ) trivial g)
    (fun g => by rw [Option.map_some]; exact grantStmt_square holder c g)
    f

/-! ## §8 — TEETH (`#guard` + theorems, both polarities). -/

section Teeth

-- The `setOverList` mechanism reads back the written value on touched keys, the default off them:
#guard (CanonMap.setOverList (fun _ => (5 : Nat)) [1, 2] (CanonMap.empty : CanonMap CellId Nat 0)).get 1 == 5
#guard (CanonMap.setOverList (fun _ => (5 : Nat)) [1, 2] (CanonMap.empty : CanonMap CellId Nat 0)).get 2 == 5
#guard (CanonMap.setOverList (fun _ => (5 : Nat)) [1, 2] (CanonMap.empty : CanonMap CellId Nat 0)).get 9 == 0

-- The finite interpreter's `guard` REJECTS (`none`) on a false predicate, COMMITS on a true one (both):
#guard (finInterp (.guard (fun _ => false)) finInit).isNone
#guard (finInterp (.guard (fun _ => true)) finInit).isSome
-- `setNullifiers` writes the verbatim list-table:
#guard ((finInterp (.setNullifiers (fun _ => [7, 8])) finInit).map (fun f => f.nullifiers)) == some [7, 8]

/-- A concrete state whose `caps` slot `0` is empty (from `finInit`). -/
private def fC : FinKernelState := finInit

/-- **POSITIVE tooth — the finite grant square fires concretely.** The FINITE step's denotation (obtained via
the §3 square, not by evaluating the noncomputable `setOver`) puts `[Cap.node 1]` in slot `0`, matching
`interp` — the deployed cap-graph write reproduced by the bounded finite update. -/
theorem grantStmt_fires :
    (denote (finSetCaps (fun k => grant k.caps 0 (Cap.node 1)) {0} fC)).caps 0 = [Cap.node 1] := by
  have hsq := grantStmt_square 0 (Cap.node 1) fC
  simp only [interp] at hsq
  have hd := Option.some.inj hsq
  rw [hd]
  show grant (denote fC).caps 0 (Cap.node 1) 0 = [Cap.node 1]
  unfold grant
  simp [fC, denote, finInit, CanonMap.get_empty]

/-- **NEGATIVE tooth — the `FiniteDiff` side condition BITES.** A genuine `grant` write is NOT finite-diff
over the EMPTY touched set: the agreement-off-`∅` obligation is FALSE (it changes slot `0`), so an
under-approximated touched set cannot discharge the square. This is what forbids a non-finite-diff (here:
empty-`T`) write from being silently accepted. -/
theorem grant_notFiniteDiff_over_empty :
    ¬ (∀ l, l ∉ (∅ : Finset Label) →
        grant (denote fC).caps 0 (Cap.node 1) l = (denote fC).caps l) := by
  intro hall
  have h0 := hall 0 (by simp)
  unfold grant at h0
  -- `(denote fC).caps 0 = []`, so `h0 : Cap.node 1 :: [] = []`, absurd.
  simp [fC, denote, finInit, CanonMap.get_empty] at h0

end Teeth

end Dregg2.Circuit.FinInterp
