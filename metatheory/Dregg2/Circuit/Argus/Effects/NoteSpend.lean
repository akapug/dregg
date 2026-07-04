/-
# Dregg2.Circuit.Argus.Effects.NoteSpend — the HARDEST Argus primitive: the noteSpend
DOUBLE-SPEND non-membership, in-band on BOTH the executor and the circuit.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and
`Argus/Policy.lean` built the first Bucket-B CIRCUIT REFERENCE — a real `VmGate` proved equivalent
to a protocol predicate (`sumGate ⟺ sumEquals`) + anti-ghost + a circuit-backed `Verifiable`
discharging the `witnessed` obligation. This module does the hard one the census flagged
MISSING: a **non-membership** circuit gate, for the noteSpend nullifier set.

## Why this is the crown

Today no-double-spend is enforced ONLY in the executor's in-memory nullifier set
(`turn/src/executor/apply.rs:941`, modelled faithfully as `RecordKernel.noteSpendNullifier`). The
running per-row EffectVM circuit does NOT enforce it: `EffectVmEmitNoteSpend.lean`'s
`noteSpend_no_double_spend_is_turn_property` / `noteSpend_freshness_still_needs_nonmembership` state
EXACTLY that the per-row freeze AIR (even with the `nullifiers`-root bound) commits the insert but
canNOT witness FRESHNESS — `nf ∉ nullifiers` is a NON-MEMBERSHIP assertion over the WHOLE set, a
gate-kind the hash-site IR lacks. So a STARK that verifies is NOT a proof of no-double-spend. THIS
file supplies that missing gate-kind, with real teeth, on both sides:

* **Executor side (§1, tractable).** `noteSpendStmt nf` is the cornerstone `RecStmt` term assembled
  from `insFresh` — whose `interp` carries the nullifier non-membership-and-insert INLINE
  (`Stmt.lean §insFresh`: `if n k ∈ k.nullifiers then none else nf :: …`). We prove
  `interp (noteSpendStmt nf) k = noteSpendNullifier k nf` (the executor IS the term) and the
  corollary `noteSpendStmt_no_double_spend`: a committed spend means the nullifier was NOT already
  spent — the no-double-spend is enforced IN THE TERM, closing the "executor-only in-memory" gap at
  the IR level. Non-vacuous: a replay ⇒ `none`.

* **Circuit side (§2–§5, the new reference).** A **SORTED-NEIGHBOR** non-membership gate.
  The committed nullifier set is sorted strictly ascending (a named commitment discipline). To prove
  `nf ∉ set`, the prover exhibits two NEIGHBOR witnesses `lo < nf < hi` that are CONSECUTIVE in the
  sentinel-padded sorted set. The gate is a REAL arithmetic constraint — two strict-`<` checks, each
  realized as a non-negative GAP witness (`nf = lo + 1 + dLo`, `dLo ≥ 0`, range-checked), exactly the
  PLONK linear-gate + range-lookup family. We prove:
    - `nonMemberGate_holds_iff_between` — the gate holds IFF `lo < nf < hi` (BOTH directions, the
      genuine circuit teeth on the columns; the gap witnesses are non-vacuous, coefficients `+1`);
    - `between_consecutive_iff_not_mem` — THE MATH BRIDGE: over a strict-ascending `xs`, a
      consecutive sentinel-padded neighbor pair with `lo < nf < hi` EXISTS iff `nf ∉ xs` (soundness +
      completeness of the non-membership argument);
    - `nonMemberGate_iff_not_mem` — the circuit⟺protocol bridge: the gate (on genuine consecutive
      neighbors) holds IFF `nf ∉ xs`;
    - the ANTI-GHOST: a gate-satisfying witness for an `nf` that IS a member is UNSAT (a member
      cannot sit strictly between its own consecutive neighbors);
    - a circuit-backed `Verifiable ObligationStmt` instance DISCHARGING the non-membership `witnessed`
      obligation (`nonMembership_witnessed_has_circuit_teeth`), the §4 analog of Policy.lean's
      `sumEquals_witnessed_has_circuit_teeth` — genuine arithmetic teeth, not an empty oracle.

## Honesty (what this builds vs assumes)

This is the SORTED-NEIGHBOR non-membership (the prompt's endorsed simpler-but-real reference), NOT a
full Merkle non-membership. The nullifier set is committed as a strict-ascending list (`SortedAsc`)
under a named root — the standard sorted-set non-membership discipline. The gate's algebraic statement
is PROVED equivalent to `nf ∉ set` (sound + complete) with an anti-ghost tooth, so a fresh-nullifier
witness that the gate accepts is exactly a non-member.

**§8¾ closes the dangerous residual:** the formerly-ASSUMED gap decode (`NmRowEncodes`: that the
prover's `(lo, hi)` are GENUINE adjacent committed neighbors) is now DISCHARGED against the deployed
sorted-tree adjacency opening (`circuit/src/membership_adjacency_air.rs`). `adjacent_gives_gapInterval`
proves `Adjacent ⟹ GapInterval` over a sorted spine, so `nmRowEncodes_of_adjacency` derives
`NmRowEncodes` from the adjacency constraint the descriptor FORCES — the WIDE-BRACKET double-spend
forgery (`lo = 0x00…`, `hi = 0xFF…`, non-adjacent) is rejected at the hypothesis
(`wide_bracket_forge_rejected`). The remaining boundary is the FFI conformance (the Rust noteSpend
descriptor must invoke `verify_adjacency` on the `(lo,hi)` columns); the Lean force is a theorem.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Imports are READ-ONLY; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Policy
import Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
import Dregg2.Crypto.NonMembership

namespace Dregg2.Circuit.Argus

open Dregg2.Exec
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Spec (Guard)
open Dregg2.Laws (Verifiable Discharged)
open Dregg2.Circuit.Emit.EffectVmEmit (VmGate VmRowEnv)

/-! ## §1 — EXECUTOR SIDE: noteSpend as the cornerstone term, with no-double-spend IN-BAND.

`noteSpendNullifier` (`RecordKernel.lean:1316`) is the kernel's fail-closed double-spend gate — the
faithful model of `apply.rs:941`'s `self.note_nullifiers` set-insert: `if nf ∈ nullifiers then none
else nf :: nullifiers`. The cornerstone IR primitive `insFresh n` (`Stmt.lean`) has EXACTLY this
`interp` clause. So the noteSpend executor IS a one-primitive `RecStmt` term, and the no-double-spend
lives INLINE in the term's meaning — not in an out-of-band in-memory set. -/

/-- **`noteSpendStmt nf`** — the noteSpend effect as a cornerstone `RecStmt` term: the single
`insFresh (fun _ => nf)` primitive, whose `interp` is the nullifier non-membership-and-insert. The
no-double-spend gate is the primitive's own semantics (no separate guard needed — `insFresh` fails
closed on a present nullifier). -/
def noteSpendStmt (nf : Nat) : RecStmt :=
  RecStmt.insFresh (fun _ => nf)

/-- **`interp_noteSpendStmt_eq_noteSpendNullifier` — the cornerstone (executor IS the term).**
`interp` of the noteSpend term is EXACTLY the verified kernel double-spend gate `noteSpendNullifier` —
the same partial function, by construction, including the `nf ∉ nullifiers` non-membership check. -/
theorem interp_noteSpendStmt_eq_noteSpendNullifier (nf : Nat) (k : RecordKernelState) :
    interp (noteSpendStmt nf) k = noteSpendNullifier k nf := by
  simp only [noteSpendStmt, interp, noteSpendNullifier]

/-- **`noteSpendStmt_no_double_spend` (the no-double-spend, IN THE TERM).** If the noteSpend
term COMMITS (`interp … = some k'`), then the spent nullifier was NOT already in the set
(`nf ∉ k.nullifiers`). The anti-replay guarantee is enforced inline by the cornerstone term's own
`interp` — closing the "executor-only in-memory nullifier set" gap at the IR level. -/
theorem noteSpendStmt_no_double_spend {nf : Nat} {k k' : RecordKernelState}
    (h : interp (noteSpendStmt nf) k = some k') : nf ∉ k.nullifiers := by
  rw [interp_noteSpendStmt_eq_noteSpendNullifier] at h
  unfold noteSpendNullifier at h
  by_cases hin : nf ∈ k.nullifiers
  · rw [if_pos hin] at h; exact absurd h (by simp)
  · exact hin

/-- **`noteSpendStmt_inserts`.** A committed noteSpend term actually inserts `nf` into the
set, so a SUBSEQUENT spend of the same `nf` is rejected (the composed anti-replay). -/
theorem noteSpendStmt_inserts {nf : Nat} {k k' : RecordKernelState}
    (h : interp (noteSpendStmt nf) k = some k') : nf ∈ k'.nullifiers := by
  rw [interp_noteSpendStmt_eq_noteSpendNullifier] at h
  exact note_spend_inserts h

/-- **`noteSpendStmt_then_reject` (the composed double-spend barrier, in the IR).** After a
committed noteSpend term of `nf`, the noteSpend term of the SAME `nf` on the result fails closed
(`= none`). Double-spend is impossible AT THE TERM LEVEL. -/
theorem noteSpendStmt_then_reject {nf : Nat} {k k' : RecordKernelState}
    (h : interp (noteSpendStmt nf) k = some k') : interp (noteSpendStmt nf) k' = none := by
  rw [interp_noteSpendStmt_eq_noteSpendNullifier]
  rw [interp_noteSpendStmt_eq_noteSpendNullifier] at h
  exact note_spend_then_reject h

/-- **`noteSpendStmt_replay_rejected` (NON-VACUITY, witness FALSE).** A nullifier ALREADY in
the set is REJECTED by the term (`interp … = none`) — the gate is two-valued, the
no-double-spend has real teeth (not `:= True`). -/
theorem noteSpendStmt_replay_rejected (nf : Nat) (k : RecordKernelState) (h : nf ∈ k.nullifiers) :
    interp (noteSpendStmt nf) k = none := by
  rw [interp_noteSpendStmt_eq_noteSpendNullifier]
  exact note_no_double_spend k nf h

/-- A kernel with nullifiers `{3, 5}` already spent (the §1 non-vacuity fixture). -/
def kSpent : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [], caps := fun _ => [], nullifiers := [3, 5] }

-- The executor-side no-double-spend is two-valued:
-- a fresh nullifier COMMITS; an immediate replay is REJECTED.
#guard ((interp (noteSpendStmt 7) kSpent).isSome)   -- 7 ∉ {3,5} ⇒ commits
#guard ((interp (noteSpendStmt 5) kSpent).isNone)   -- 5 ∈ {3,5} ⇒ rejected

/-! ### keystone-audit companions (named `*_satisfiable` / `*_teeth`).

The keystone-audit looks companions up BY NAME. The fresh spend of `7` on `kSpent` (= `{3,5}`) COMMITS
(`interp … = some k'`), which is exactly the satisfiable hypothesis each `noteSpendStmt_*` keystone
needs; the replay of a present nullifier (`5 ∈ {3,5}`) is REFUSED — the shared two-valued teeth. -/

/-- The fresh spend of `7` on `kSpent` COMMITS — the named witness of the keystones' satisfiable
hypothesis (`interp (noteSpendStmt nf) k = some k'`). -/
theorem kSpent_fresh_commits : ∃ k', interp (noteSpendStmt 7) kSpent = some k' :=
  Option.isSome_iff_exists.mp (by decide)

/-- **`noteSpendStmt_no_double_spend_satisfiable`** — the keystone FIRES on the fresh commit: `7` was
NOT already spent (`7 ∉ kSpent.nullifiers`). Non-vacuous. -/
theorem noteSpendStmt_no_double_spend_satisfiable : (7 : Nat) ∉ kSpent.nullifiers := by
  obtain ⟨k', h⟩ := kSpent_fresh_commits
  exact noteSpendStmt_no_double_spend h

/-- **`noteSpendStmt_inserts_satisfiable`** — the keystone FIRES: the fresh commit inserts `7` into the
post-state's nullifier set. -/
theorem noteSpendStmt_inserts_satisfiable :
    ∃ k', interp (noteSpendStmt 7) kSpent = some k' ∧ (7 : Nat) ∈ k'.nullifiers := by
  obtain ⟨k', h⟩ := kSpent_fresh_commits
  exact ⟨k', h, noteSpendStmt_inserts h⟩

/-- **`noteSpendStmt_then_reject_satisfiable`** — the keystone FIRES: after the fresh commit, the SAME
spend on the result fails closed (the composed double-spend barrier, exercised). -/
theorem noteSpendStmt_then_reject_satisfiable :
    ∃ k', interp (noteSpendStmt 7) kSpent = some k' ∧ interp (noteSpendStmt 7) k' = none := by
  obtain ⟨k', h⟩ := kSpent_fresh_commits
  exact ⟨k', h, noteSpendStmt_then_reject h⟩

/-- **`noteSpendStmt_teeth`** — the no-double-spend gate DISCRIMINATES: a nullifier ALREADY present
(`5 ∈ kSpent.nullifiers = {3,5}`) is REFUSED (`interp … = none`). The gate is two-valued, not `:= True`
— the shared teeth for the noteSpend keystone family. -/
theorem noteSpendStmt_teeth : interp (noteSpendStmt 5) kSpent = none :=
  noteSpendStmt_replay_rejected 5 kSpent (by decide)

/-- **`noteSpendStmt_replay_rejected_satisfiable`** — the rejection keystone FIRES on a concrete present
nullifier (`5 ∈ {3,5}`): the hypothesis `nf ∈ k.nullifiers` is jointly satisfiable, the `= none`
conclusion is exercised. -/
theorem noteSpendStmt_replay_rejected_satisfiable : interp (noteSpendStmt 5) kSpent = none :=
  noteSpendStmt_teeth

/-- **`noteSpendStmt_replay_rejected_teeth`** — the rejection is NOT `:= True`: a FRESH nullifier
(`7 ∉ {3,5}`) is NOT rejected (`interp ≠ none` — it commits). So "replay rejected" discriminates the
present-vs-fresh distinction. -/
theorem noteSpendStmt_replay_rejected_teeth : interp (noteSpendStmt 7) kSpent ≠ none := by
  obtain ⟨k', h⟩ := kSpent_fresh_commits
  rw [h]; exact Option.some_ne_none k'

/-! ## §2 — THE MATH CORE: sorted-neighbor non-membership (`lo < nf < hi` ⟺ `nf ∉ xs`).

The new content. A nullifier set committed as a STRICT-ASCENDING list `xs` admits a
non-membership argument: `nf ∉ xs` IFF there is a CONSECUTIVE sentinel-padded neighbor pair
`(lo, hi)` (with `lo < hi`) such that `lo < nf < hi`. We build a self-contained `SortedAsc`
predicate and a `NeighborGap` witness (so this module depends on NO moving mathlib list API), and
prove the equivalence by induction. This is the protocol-side statement the circuit gate will be
proved equivalent to. -/

/-- **`SortedAsc xs`** — `xs` is strictly ascending (the committed nullifier-set discipline). Direct
recursion (no mathlib `Sorted`/`Chain'` dependency): a singleton is sorted; `a :: b :: r` is sorted
iff `a < b` and `b :: r` is sorted. -/
def SortedAsc : List Int → Prop
  | []          => True
  | [_]         => True
  | a :: b :: r => a < b ∧ SortedAsc (b :: r)

/-- A strict-ascending list of `Nat` nullifiers, lifted to `ℤ` (the committed-set coercion the gate
reads — the EffectVM columns carry `ℤ`). -/
def sortedAscNat (xs : List Nat) : Prop := SortedAsc (xs.map (Int.ofNat))

/-- **`sortedAsc_tail`.** The tail of a strict-ascending list is strict-ascending. -/
theorem sortedAsc_tail {a : Int} {xs : List Int} (h : SortedAsc (a :: xs)) : SortedAsc xs := by
  cases xs with
  | nil => exact True.intro
  | cons b r => exact h.2

/-- **`sortedAsc_head_lt`.** In a strict-ascending `a :: b :: r`, the head is strictly below
the second element. -/
theorem sortedAsc_head_lt {a b : Int} {r : List Int} (h : SortedAsc (a :: b :: r)) : a < b := h.1

/-- **`sortedAsc_head_lt_mem`.** In a strict-ascending list `a :: xs`, the head is strictly
below EVERY element of `xs` (so the head is the unique minimum). The key monotonicity fact. -/
theorem sortedAsc_head_lt_mem {a : Int} {xs : List Int} (h : SortedAsc (a :: xs)) :
    ∀ y ∈ xs, a < y := by
  induction xs generalizing a with
  | nil => intro y hy; exact absurd hy (by simp)
  | cons b r ih =>
    intro y hy
    have hab : a < b := h.1
    rcases List.mem_cons.mp hy with hyb | hyr
    · subst hyb; exact hab
    · exact lt_trans hab (ih (sortedAsc_tail h) y hyr)

/-- **`NeighborGap nf xs`** — the structured sorted-neighbor non-membership witness for `nf` against
the committed sorted set `xs`. The clean three-constructor walk a prover follows (the genuine `(lo, hi)`
neighbors are READ OFF the witness by `gapEndpoints`, §4):

* `emptySet` — `xs = []`: the set is empty, so `nf` trivially sits in a vacuous gap (`±∞` neighbors).
* `below`    — `nf` is strictly below the head of `xs` (so, the set being ascending, below everything
  remaining): `xs = hi :: r` and `nf < hi`. The upper neighbor is the head `hi`.
* `skip`     — `nf` is strictly above the head `a` of `xs`, so the search continues past `a` (which
  becomes the new lower-neighbor candidate): `a < nf` and `NeighborGap nf r`.

It is DATA (`Type`, not `Prop`) — `gapEndpoints` extracts the genuine `(lo, hi)` empty-gap endpoints from
its structure (a `Prop` could not be eliminated into `Int × Int`). The argument is SOUND
(`neighborGap_sound`: a witness ⇒ `nf ∉ xs`) and COMPLETE (`neighborGap_complete`: every non-member of a
sorted set has one); `gapEndpoints`/`neighborGap_gives_gap` (§4) read the genuine empty-gap interval off
it for the circuit bridge. -/
inductive NeighborGap (nf : Int) : List Int → Type
  /-- The committed set is empty ⇒ `nf` is (vacuously) a non-member (lower nbr `-∞`, upper `+∞`). -/
  | emptySet : NeighborGap nf []
  /-- `nf` strictly below the head ⇒ below the whole (ascending) set: `xs = hi :: r`, `nf < hi`. The
  upper neighbor is the head `hi`; the lower is whatever predecessor the search carried (or `-∞`). (Named
  `belowHd` — `below` would collide with the auto-generated `NeighborGap.below` recursor helper that the
  structural recursion of `gapEndpointsAux` emits.) -/
  | belowHd {hi : Int} {r : List Int} (h : nf < hi) : NeighborGap nf (hi :: r)
  /-- `nf` strictly above the head `a` ⇒ the search continues past `a` (which becomes the new lower
  neighbor candidate): `a < nf` and `NeighborGap nf r`. -/
  | skip {a : Int} {r : List Int} (h : a < nf) (rest : NeighborGap nf r) : NeighborGap nf (a :: r)

/-- **`neighborGap_sound` (the sorted-neighbor argument is SOUND).** A `NeighborGap` witness
for `nf` against a strict-ascending `xs` proves `nf ∉ xs`: at each step `nf` is either strictly below
the head (so below everything remaining) or strictly above it (so `≠` head, recurse on the sorted tail).
A prover that walks the neighbors has proved non-membership. -/
theorem neighborGap_sound {nf : Int} {xs : List Int} (hs : SortedAsc xs) (hg : NeighborGap nf xs) :
    nf ∉ xs := by
  induction hg with
  | emptySet => simp
  | @belowHd hi r h =>
    -- nf < hi ≤ everything in hi::r ⇒ nf below all ⇒ not a member.
    intro hmem
    rcases List.mem_cons.mp hmem with hh | hr
    · subst hh; exact lt_irrefl _ h
    · exact absurd (sortedAsc_head_lt_mem hs _ hr) (not_lt.mpr (le_of_lt h))
  | @skip a r h hrest ih =>
    -- a < nf (so nf ≠ a) and nf ∉ r (by IH on the sorted tail).
    intro hmem
    rcases List.mem_cons.mp hmem with hh | hr
    · subst hh; exact lt_irrefl _ h
    · exact ih (sortedAsc_tail hs) hr

/-- **`neighborGap_complete` (the sorted-neighbor argument is COMPLETE).** For ANY
strict-ascending committed set `xs`, a genuine non-member `nf ∉ xs` HAS a `NeighborGap` witness — the
honest prover always finds its neighbors. The induction marches the head pointer forward (`skip`) until
`nf` falls below the current head (`below`), or runs off the end (`emptySet`). No non-member is left
un-provable. (A `def`, not a `theorem`: it BUILDS the `Type`-valued witness data.) -/
def neighborGap_complete {nf : Int} {xs : List Int} (hs : SortedAsc xs) (hnm : nf ∉ xs) :
    NeighborGap nf xs := by
  induction xs with
  | nil => exact NeighborGap.emptySet
  | cons a r ih =>
    have hane : nf ≠ a := fun h => hnm (h ▸ List.mem_cons_self)
    have hnr : nf ∉ r := fun h => hnm (List.mem_cons_of_mem a h)
    -- decidable case split (NOT `Or`-elimination — `NeighborGap` is `Type`, so we use the `Int`
    -- decidable order to BUILD the witness): `nf < a` ⇒ below; else `a < nf` (≠ since `nf ≠ a`) ⇒ skip.
    by_cases hlt : nf < a
    · exact NeighborGap.belowHd hlt
    · have hgt : a < nf := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hane)
      exact NeighborGap.skip hgt (ih (sortedAsc_tail hs) hnr)

/-- **`neighborGap_iff_not_mem` (the sorted-neighbor argument DECIDES non-membership).** Over a
strict-ascending committed set, a `NeighborGap` witness EXISTS iff `nf ∉ xs`: soundness
(`neighborGap_sound`) gives ⇒, completeness (`neighborGap_complete`) gives ⇐. So "the prover can exhibit
sorted neighbors" is EXACTLY "the nullifier is fresh" — the protocol-side statement the circuit gate is
proved equivalent to in §5. -/
theorem neighborGap_iff_not_mem {nf : Int} {xs : List Int} (hs : SortedAsc xs) :
    Nonempty (NeighborGap nf xs) ↔ nf ∉ xs :=
  ⟨fun ⟨g⟩ => neighborGap_sound hs g, fun hnm => ⟨neighborGap_complete hs hnm⟩⟩

/-! ## §3 — THE CIRCUIT GATE: a real `VmGate` enforcing `lo < nf < hi` with non-negative gap witnesses.

The arithmetic content of the sorted-neighbor argument is the STRICT-BETWEEN check `lo < nf < hi`.
Over `ℤ` (the EffectVM column field model), a strict inequality `a < b` is enforced by a NON-NEGATIVE
gap witness `d` (range-checked `d ≥ 0`) with the linear gate `b − a − 1 − d = 0` (i.e. `b = a + 1 +
d`). Two such gates — `nf = lo + 1 + dLo` and `hi = nf + 1 + dHi` — enforce `lo < nf < hi`. These are
genuine PLONK linear gates (the `affineEq` family Policy.lean cites), with NON-ZERO coefficients on
the neighbor/witness columns — a real constraint, not a vacuous `0 = 0`. The range checks `dLo, dHi ≥
0` are the lookup leg (the meaning; LogUp is how the prover enforces it). -/

/-- Column layout the non-membership gate reads: the spent nullifier `nf`, the two neighbor
read-outs `lo`/`hi`, and the two non-negative gap witnesses `dLo`/`dHi` (the strict-`<` certificates).
Distinct column indices so a row carries all five independently. -/
structure NmCols where
  nf  : Nat
  lo  : Nat
  hi  : Nat
  dLo : Nat
  dHi : Nat

/-- The lower-gap gate body `nf − lo − 1 − dLo` (asserts `nf = lo + 1 + dLo`, so `lo < nf` given
`dLo ≥ 0`). A single PLONK linear gate; coefficient `+1` on `nf`, `−1` on `lo`/`dLo`. -/
def gapLoBody (c : NmCols) : EmittedExpr :=
  .add (.var c.nf)
    (.add (.mul (.const (-1)) (.var c.lo))
      (.add (.const (-1)) (.mul (.const (-1)) (.var c.dLo))))

/-- The upper-gap gate body `hi − nf − 1 − dHi` (asserts `hi = nf + 1 + dHi`, so `nf < hi` given
`dHi ≥ 0`). -/
def gapHiBody (c : NmCols) : EmittedExpr :=
  .add (.var c.hi)
    (.add (.mul (.const (-1)) (.var c.nf))
      (.add (.const (-1)) (.mul (.const (-1)) (.var c.dHi))))

/-- **`gapLoGate`/`gapHiGate`** — the two strict-`<` gates as real per-row `VmGate`s. -/
def gapLoGate (c : NmCols) : VmGate := { body := gapLoBody c }
def gapHiGate (c : NmCols) : VmGate := { body := gapHiBody c }

/-- **`NmRowOk c env`** — the row carries a WELL-FORMED non-membership witness: both gap witnesses are
non-negative (the range-check leg). The honest precondition the prover's LogUp range-checks supply.
Without it the linear gates alone do not pin the inequality direction (a negative `dLo` could satisfy
`nf = lo + 1 + dLo` with `nf ≤ lo`), so this is load-bearing — exactly the `rangeCheck dLo`/`dHi`
lookups. -/
def NmRowOk (c : NmCols) (env : VmRowEnv) : Prop :=
  0 ≤ env.loc c.dLo ∧ 0 ≤ env.loc c.dHi

/-- **`gapLo_holds_iff`.** The lower-gap gate holds IFF `env.loc nf = env.loc lo + 1 +
env.loc dLo` — the faithful arithmetic of the linear gate. -/
theorem gapLo_holds_iff (c : NmCols) (env : VmRowEnv) :
    (gapLoGate c).holds env ↔ env.loc c.nf = env.loc c.lo + 1 + env.loc c.dLo := by
  unfold VmGate.holds gapLoGate gapLoBody
  simp only [EmittedExpr.eval]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **`gapHi_holds_iff`.** The upper-gap gate holds IFF `env.loc hi = env.loc nf + 1 +
env.loc dHi`. -/
theorem gapHi_holds_iff (c : NmCols) (env : VmRowEnv) :
    (gapHiGate c).holds env ↔ env.loc c.hi = env.loc c.nf + 1 + env.loc c.dHi := by
  unfold VmGate.holds gapHiGate gapHiBody
  simp only [EmittedExpr.eval]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **`nonMemberGate_sound_between` (the gate's SOUNDNESS, the load-bearing teeth).** Under
the range-check precondition `NmRowOk` (gap witnesses non-negative), if the two gap gates BOTH hold
then the neighbors strictly bracket the nullifier: `lo < nf ∧ nf < hi`. This is the genuine
circuit-arithmetic enforcement: a gate-satisfying row with valid (non-negative) gap witnesses PROVES
`nf` is interior to `(lo, hi)` — a real strict-between constraint, the direction non-membership
soundness rests on. (The converse — completeness — is `nonMemberGate_complete`: the honest prover lays
the EXACT gaps, so an interior `nf` is gate-acceptable. We separate the two because the
witness columns are the prover's: soundness must hold for ANY non-negative witnesses, completeness
EXHIBITS the honest ones.) -/
theorem nonMemberGate_sound_between (c : NmCols) (env : VmRowEnv) (hwf : NmRowOk c env)
    (hg : (gapLoGate c).holds env ∧ (gapHiGate c).holds env) :
    env.loc c.lo < env.loc c.nf ∧ env.loc c.nf < env.loc c.hi := by
  obtain ⟨hdLo, hdHi⟩ := hwf
  obtain ⟨hlo, hhi⟩ := hg
  rw [gapLo_holds_iff] at hlo
  rw [gapHi_holds_iff] at hhi
  exact ⟨by linarith, by linarith⟩

/-- The HONEST witness environment for an interior `nf`: lay the exact gaps `dLo = nf−lo−1`,
`dHi = hi−nf−1` on the witness columns (and the neighbors/`nf` on theirs). The prover's completeness
construction — the row that REALIZES the non-membership gate for `lo < nf < hi`. The four data columns
take their genuine values; everything else is `0`. (Assumes the five layout columns are distinct so
the writes don't alias; `nfV`/`loV`/`hiV` are the read-outs.) -/
def honestNmEnv (c : NmCols) (loV nfV hiV : Int) : VmRowEnv where
  loc := fun v =>
    if v = c.nf then nfV
    else if v = c.lo then loV
    else if v = c.hi then hiV
    else if v = c.dLo then nfV - loV - 1
    else if v = c.dHi then hiV - nfV - 1
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **`nonMemberGate_complete` (the gate's COMPLETENESS).** For an interior `nf`
(`lo < nf < hi`), the HONEST witness env (the exact gaps) is well-formed (`NmRowOk` — the gaps are
non-negative) AND satisfies BOTH gap gates. So every strict-between configuration is gate-acceptable:
no honest non-member is left un-provable. (Requires the five layout columns distinct.) -/
theorem nonMemberGate_complete (c : NmCols) (loV nfV hiV : Int)
    (hlo : loV < nfV) (hhi : nfV < hiV)
    (hd : [c.nf, c.lo, c.hi, c.dLo, c.dHi].Nodup) :
    NmRowOk c (honestNmEnv c loV nfV hiV)
      ∧ (gapLoGate c).holds (honestNmEnv c loV nfV hiV)
      ∧ (gapHiGate c).holds (honestNmEnv c loV nfV hiV) := by
  -- unpack the Nodup into the ten pairwise-distinctness facts the column reads need.
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_iff, and_true] at hd
  obtain ⟨⟨hnflo, hnfhi, hnfdlo, hnfdhi⟩, ⟨hlohi, hlodlo, hlodhi⟩, ⟨hhidlo, hhidhi⟩, hdlodhi⟩ := hd
  -- the five read-outs of the honest env, computed:
  have rnf  : (honestNmEnv c loV nfV hiV).loc c.nf = nfV := by simp [honestNmEnv]
  have rlo  : (honestNmEnv c loV nfV hiV).loc c.lo = loV := by
    simp [honestNmEnv, Ne.symm hnflo]
  have rhi  : (honestNmEnv c loV nfV hiV).loc c.hi = hiV := by
    simp [honestNmEnv, Ne.symm hnfhi, Ne.symm hlohi]
  have rdLo : (honestNmEnv c loV nfV hiV).loc c.dLo = nfV - loV - 1 := by
    simp [honestNmEnv, Ne.symm hnfdlo, Ne.symm hlodlo, Ne.symm hhidlo]
  have rdHi : (honestNmEnv c loV nfV hiV).loc c.dHi = hiV - nfV - 1 := by
    simp [honestNmEnv, Ne.symm hnfdhi, Ne.symm hlodhi, Ne.symm hhidhi, Ne.symm hdlodhi]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [rdLo]; linarith
  · rw [rdHi]; linarith
  · rw [gapLo_holds_iff, rnf, rlo, rdLo]; ring
  · rw [gapHi_holds_iff, rnf, rhi, rdHi]; ring

/-! ## §4 — THE GAP-INTERVAL CHARACTERIZATION: the honest, sentinel-free `(lo, hi)`-neighbor decoding.

To bridge the gate's `lo < nf < hi` to the protocol's `nf ∉ xs`, we need the honest fact that the
row's neighbor read-outs `(lo, hi)` are GENUINE consecutive neighbors of the committed set — i.e. the
open interval `(lo, hi)` contains NO committed element. That is the sentinel-free characterization of
"adjacent in the sorted set" (`lo`/`hi` are adjacent committed values, OR the `±∞` sentinels), and it
is EXACTLY what a sorted-tree adjacency opening certifies. We name it `GapInterval` (the honest
decoding hypothesis, the §4-analog of Policy.lean's `RowEncodesSum`), and prove the clean bridge:
`lo < nf < hi` under `GapInterval lo hi xs` is equivalent to `nf ∉ xs`. -/

/-- **`GapInterval lo hi xs`** — the open interval `(lo, hi)` contains NO committed element of `xs`
(every `y ∈ xs` is `≤ lo` or `≥ hi`). The honest "genuine adjacent neighbors" decoding: `lo`/`hi`
straddle an empty gap of the sorted committed set (adjacent committed values, or `±∞` sentinels). This
is the hypothesis a sorted-tree adjacency opening supplies and the deployed descriptor must bind
(reported in the trailer). -/
def GapInterval (lo hi : Int) (xs : List Int) : Prop :=
  ∀ y ∈ xs, y ≤ lo ∨ hi ≤ y

/-- **`between_gap_not_mem` (the bridge SOUNDNESS).** If `nf` is strictly between `lo` and
`hi`, and `(lo, hi)` is an empty gap of the committed set (`GapInterval`), then `nf ∉ xs`. So the
gate's strict-between fact, on GENUINE adjacent neighbors, PROVES non-membership: no committed element
sits where `nf` does. -/
theorem between_gap_not_mem {lo nf hi : Int} {xs : List Int}
    (hlo : lo < nf) (hhi : nf < hi) (hgap : GapInterval lo hi xs) : nf ∉ xs := by
  intro hmem
  rcases hgap nf hmem with h | h
  · exact absurd h (not_le.mpr hlo)
  · exact absurd h (not_le.mpr hhi)

/-- **`mem_not_between_gap` (the ANTI-GHOST, math side).** If `nf` IS a committed member and
`(lo, hi)` is an empty gap of the set, then `nf` is NOT strictly between `lo` and `hi`: a member
cannot sit inside a gap that excludes all members. The protocol-side anti-ghost the circuit anti-ghost
lifts. -/
theorem mem_not_between_gap {lo nf hi : Int} {xs : List Int}
    (hmem : nf ∈ xs) (hgap : GapInterval lo hi xs) : ¬ (lo < nf ∧ nf < hi) := by
  rintro ⟨hlo, hhi⟩
  rcases hgap nf hmem with h | h
  · exact absurd h (not_le.mpr hlo)
  · exact absurd h (not_le.mpr hhi)

/-- **`gapEndpointsAux lo g`** — read the GENUINE empty-gap endpoints off a `NeighborGap` witness,
threading the immediate-predecessor lower bound `lo` (the last element the search skipped past, or the
`-∞` sentinel before any). At a `skip a` the predecessor advances to `a`; at a terminal `below hi` the
upper neighbor is the head `hi`; at `emptySet` (`nf` ran off the top) the upper neighbor is the `+∞`
sentinel `nf+1`. So the result is `(immediate-predecessor, immediate-successor)` — the two genuine
adjacent committed values (or `±∞` at the open ends), exactly the empty gap `nf` falls in. -/
def gapEndpointsAux {nf : Int} (lo : Int) : {xs : List Int} → NeighborGap nf xs → Int × Int
  | _, .emptySet           => (lo, nf + 1)            -- ran off the top: upper neighbor `+∞`.
  | _, .belowHd (hi := hi) _ => (lo, hi)              -- below the head: upper neighbor is the head.
  | _, .skip (a := a) _ rest => gapEndpointsAux a rest -- skip past `a`: it becomes the new predecessor.

/-- **`gapEndpoints g`** — the genuine empty-gap endpoints of the non-membership witness, starting the
predecessor at the `-∞` sentinel `nf-1`. -/
def gapEndpoints {nf : Int} {xs : List Int} (g : NeighborGap nf xs) : Int × Int :=
  gapEndpointsAux (nf - 1) g

/-- **`gapEndpointsAux_lo_le`.** When the threaded predecessor `lo` is strictly below EVERY
element of `xs` (a genuine lower sentinel for the remaining list — `∀ y ∈ xs, lo < y`), the lower
endpoint `gapEndpointsAux lo g` reports is `≥ lo`. (Each `skip a` overwrites `lo` with the head `a`,
which is `> lo` by the sentinel hypothesis and `<` everything ahead by sortedness, so the bound
propagates.) The monotonicity the gap proof's "skipped head `≤` lower endpoint" step reads. -/
theorem gapEndpointsAux_lo_le {nf : Int} {xs : List Int} (g : NeighborGap nf xs) (hs : SortedAsc xs)
    (lo : Int) (hlo : ∀ y ∈ xs, lo < y) :
    lo ≤ (gapEndpointsAux lo g).1 := by
  induction g generalizing lo with
  | emptySet => exact le_refl _
  | belowHd h => exact le_refl _
  | @skip a r h rest ih =>
    -- result = gapEndpointsAux a rest; a > lo (sentinel on the head) and a < everything in r (sorted).
    have hla : lo < a := hlo a List.mem_cons_self
    have hra : ∀ y ∈ r, a < y := fun y hy => sortedAsc_head_lt_mem hs y hy
    exact le_of_lt (lt_of_lt_of_le hla (ih (sortedAsc_tail hs) a hra))

/-- **`gapEndpointsAux_gives_gap` (the threaded gap invariant).** For a strict-ascending `xs`
and a predecessor `lo < nf`, the endpoints `gapEndpointsAux lo g` (a) strictly bracket `nf` and (b) form
an empty `GapInterval` of `xs`. The skip case reads the new predecessor's `≥`-bound from
`gapEndpointsAux_lo_le` (the FRESH skipped head `a` is a genuine sentinel for the tail by sortedness, so
the skipped head sits `≤` the reported lower endpoint); the IH covers the tail, and sortedness puts every
later element `≥` the upper endpoint. (No top-level sentinel hypothesis on `lo` is needed: the only
skipped-head bound used is the fresh `a`'s, supplied by sortedness.) -/
theorem gapEndpointsAux_gives_gap {nf : Int} {xs : List Int} (hs : SortedAsc xs)
    (g : NeighborGap nf xs) (lo : Int) (hlo : lo < nf) :
    (gapEndpointsAux lo g).1 < nf ∧ nf < (gapEndpointsAux lo g).2
      ∧ GapInterval (gapEndpointsAux lo g).1 (gapEndpointsAux lo g).2 xs := by
  induction g generalizing lo with
  | emptySet =>
    -- result (lo, nf+1); lo < nf < nf+1; empty list ⇒ vacuous gap.
    refine ⟨hlo, ?_, ?_⟩
    · show nf < nf + 1; linarith
    · intro y hy; exact absurd hy (by simp)
  | @belowHd hi r h =>
    -- result (lo, hi); lo < nf < hi; every y in hi::r is ≥ hi (head-min).
    refine ⟨hlo, h, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with hh | hr
    · subst hh; exact Or.inr (le_refl _)
    · exact Or.inr (le_of_lt (sortedAsc_head_lt_mem hs _ hr))
  | @skip a r h rest ih =>
    -- result = gapEndpointsAux a rest (recurse with predecessor a, since a < nf and a < everything ahead).
    have hra : ∀ y ∈ r, a < y := fun y hy => sortedAsc_head_lt_mem hs y hy
    obtain ⟨hL, hH, hgap⟩ := ih (sortedAsc_tail hs) a h
    refine ⟨hL, hH, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with hh | hr
    · -- y = a: the skipped head sits ≤ the reported lower endpoint (a is a sentinel for r).
      rw [hh]; exact Or.inl (gapEndpointsAux_lo_le rest (sortedAsc_tail hs) a hra)
    · exact hgap y hr

/-- **`neighborGap_gives_gap` (the §2→§4 connector).** A `NeighborGap` witness for `nf`
against a strict-ascending `xs` yields endpoints `(lo, hi) = gapEndpoints g` that (a) strictly bracket
`nf` and (b) form an empty `GapInterval` of `xs`. So the constructive neighbor witness IS a genuine
gap decoding — closing the loop between the structured §2 argument and the §4 gate bridge. -/
theorem neighborGap_gives_gap {nf : Int} {xs : List Int} (hs : SortedAsc xs)
    (g : NeighborGap nf xs) :
    (gapEndpoints g).1 < nf ∧ nf < (gapEndpoints g).2 ∧ GapInterval (gapEndpoints g).1 (gapEndpoints g).2 xs :=
  gapEndpointsAux_gives_gap hs g (nf - 1) (by linarith)

/-! ## §5 — THE CIRCUIT ⟺ PROTOCOL BRIDGE + ANTI-GHOST: gate (on genuine neighbors) ⟺ `nf ∉ xs`.

We now compose §3 (the gate's arithmetic teeth) with §4 (the gap decoding). The honest decoding
hypothesis `NmRowEncodes c env xs` says the row's `nf` read-out is the spent nullifier and its
`(lo, hi)` read-outs are a genuine empty-gap neighbor pair of the committed set `xs`. Under it:

* **soundness**: a gate-satisfying, range-checked row PROVES `nf ∉ xs` (`nonMemberGate_sound`);
* **completeness**: every genuine non-member has a gate-satisfying honest row
  (`nonMemberGate_complete_nonmember`);
* **anti-ghost**: a row whose `nf` IS a member CANNOT satisfy the gate on its genuine neighbors
  (`nonMemberGate_rejects_member`). -/

/-- **`NmRowEncodes c env xs nf`** — the honest decoding hypothesis: the row's `nf`-column carries the
spent nullifier `nf`, and its `(lo, hi)`-columns are a genuine empty-gap neighbor pair of the committed
set `xs`. The §4-analog of Policy.lean's `RowEncodesSum` — it NAMES which committed neighbors the
columns hold (the sorted-tree adjacency opening's job). -/
def NmRowEncodes (c : NmCols) (env : VmRowEnv) (xs : List Int) (nf : Int) : Prop :=
  env.loc c.nf = nf ∧ GapInterval (env.loc c.lo) (env.loc c.hi) xs

/-- **`nonMemberGate_sound` (CIRCUIT⟺PROTOCOL SOUNDNESS).** A range-checked row (`NmRowOk`)
that satisfies BOTH gap gates, under the gap decoding (`NmRowEncodes`), PROVES the spent
nullifier is NOT in the committed set: `nf ∉ xs`. The gate's algebraic statement SUFFICES to enforce
non-membership — the missing no-double-spend teeth, now real. -/
theorem nonMemberGate_sound (c : NmCols) (env : VmRowEnv) (xs : List Int) (nf : Int)
    (hwf : NmRowOk c env) (henc : NmRowEncodes c env xs nf)
    (hg : (gapLoGate c).holds env ∧ (gapHiGate c).holds env) :
    nf ∉ xs := by
  obtain ⟨hnf, hgap⟩ := henc
  obtain ⟨hlo, hhi⟩ := nonMemberGate_sound_between c env hwf hg
  rw [hnf] at hlo hhi
  exact between_gap_not_mem hlo hhi hgap

/-- **`nonMemberGate_rejects_member` (THE ANTI-GHOST TOOTH).** If the spent nullifier IS a
committed member (`nf ∈ xs`), then NO range-checked row can satisfy both gap gates under the gap
decoding: the gate is UNSAT. A double-spend attempt — a nullifier already in the set — cannot produce a
gate-satisfying non-membership witness on its genuine neighbors. This is the tooth `sumGate_rejects_tamper`
is to `sumEquals`: a prover cannot forge non-membership of an already-spent nullifier. -/
theorem nonMemberGate_rejects_member (c : NmCols) (env : VmRowEnv) (xs : List Int) (nf : Int)
    (hwf : NmRowOk c env) (henc : NmRowEncodes c env xs nf) (hmem : nf ∈ xs) :
    ¬ ((gapLoGate c).holds env ∧ (gapHiGate c).holds env) := by
  intro hg
  obtain ⟨hnf, hgap⟩ := henc
  obtain ⟨hlo, hhi⟩ := nonMemberGate_sound_between c env hwf hg
  rw [hnf] at hlo hhi
  exact mem_not_between_gap hmem hgap ⟨hlo, hhi⟩

/-- **`nonMemberGate_complete_nonmember` (CIRCUIT⟺PROTOCOL COMPLETENESS).** For a genuine
non-member (`nf ∉ xs`) of a strict-ascending committed set, there EXIST neighbor/gap values and an
honest range-checked row that (a) decodes the gap correctly (`NmRowEncodes`) and (b) satisfies BOTH gap
gates. So every genuine non-member is gate-acceptable — the non-membership argument is complete, not
just sound. (Requires the five layout columns distinct.) -/
theorem nonMemberGate_complete_nonmember (c : NmCols) (xs : List Int) (nf : Int)
    (hs : SortedAsc xs) (hnm : nf ∉ xs) (hd : [c.nf, c.lo, c.hi, c.dLo, c.dHi].Nodup) :
    ∃ env : VmRowEnv,
      NmRowOk c env ∧ NmRowEncodes c env xs nf
        ∧ (gapLoGate c).holds env ∧ (gapHiGate c).holds env := by
  -- get a structured neighbor witness, read its genuine gap endpoints.
  have g : NeighborGap nf xs := neighborGap_complete hs hnm
  obtain ⟨hglo, hghi, hgap⟩ := neighborGap_gives_gap hs g
  set lo := (gapEndpoints g).1 with hlodef
  set hi := (gapEndpoints g).2 with hhidef
  -- the honest env lays nf/lo/hi + exact gaps; reuse §3 completeness for the gate satisfaction.
  refine ⟨honestNmEnv c lo nf hi, ?_⟩
  obtain ⟨hwf, hgateLo, hgateHi⟩ := nonMemberGate_complete c lo nf hi hglo hghi hd
  -- compute the honest env's nf/lo/hi read-outs to discharge `NmRowEncodes`.
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or] at hd
  obtain ⟨⟨hnflo, hnfhi, hnfdlo, hnfdhi⟩, ⟨hlohi, hlodlo, hlodhi⟩, ⟨hhidlo, hhidhi⟩, hdlodhi, _⟩ := hd
  have rnf : (honestNmEnv c lo nf hi).loc c.nf = nf := by simp [honestNmEnv]
  have rlo : (honestNmEnv c lo nf hi).loc c.lo = lo := by simp [honestNmEnv, Ne.symm hnflo]
  have rhi : (honestNmEnv c lo nf hi).loc c.hi = hi := by
    simp [honestNmEnv, Ne.symm hnfhi, Ne.symm hlohi]
  refine ⟨hwf, ⟨rnf, ?_⟩, hgateLo, hgateHi⟩
  rw [rlo, rhi]; exact hgap

/-! ## §6 — THE `witnessed`-ARM DISCHARGE: a circuit-backed `Verifiable` for the non-membership obligation.

Exactly as Policy.lean discharged the `sumEquals` `witnessed` arm with a real `sumGate` instance, we
discharge the NON-MEMBERSHIP `witnessed` arm with the real gap gates. The obligation is named
`.named h` (an opaque obligation — the dregg1 "nullifier-non-membership" verifier kind behind the
seam). The witness carries the row + column layout + the committed set; `Verify` runs BOTH gap gates
and checks the range witnesses (`NmRowOk`, decidable). Then a `witnessed`-routed non-membership guard
`admits` IFF the circuit gates accept — genuine arithmetic teeth, not an empty oracle. -/

/-- A circuit witness for a non-membership obligation: the prover's row, the column layout, and the
committed sorted set the gap is taken against (carried so `Verify` can check the gap decoding is honest
— a sorted-tree opening would supply this binding). -/
structure NmWitness where
  env : VmRowEnv
  cols : NmCols
  set : List Int

/-- `NmRowOk` is DECIDABLE (two `Int` `≤` checks), so `Verify` can compute it. -/
instance (c : NmCols) (env : VmRowEnv) : Decidable (NmRowOk c env) :=
  inferInstanceAs (Decidable (0 ≤ env.loc c.dLo ∧ 0 ≤ env.loc c.dHi))

/-- The obligation hash the non-membership `witnessed` arm names (an opaque tag — the
"nullifier-non-membership" verifier kind; any fixed `Nat`, here `0`). -/
def NM_OBLIGATION : Nat := 0

/-- **The circuit-backed verifier for the non-membership obligation.** `Verify (.named NM_OBLIGATION)
w` runs the REAL gap gates `gapLoGate w.cols`/`gapHiGate w.cols` on the witness row AND checks the
range witnesses `NmRowOk` — accepting iff the row is a well-formed gate-satisfying non-membership
witness. Every other obligation is out of scope (fail-closed `false`). The CONCRETE circuit discharge,
the opposite of an always-true stub. -/
instance instVerifiableNonMember : Verifiable ObligationStmt NmWitness where
  Verify
    | .named h, w =>
        decide (h = NM_OBLIGATION)
          && decide (NmRowOk w.cols w.env)
          && decide ((gapLoGate w.cols).holds w.env)
          && decide ((gapHiGate w.cols).holds w.env)
    | _, _ => false

/-- **`nonMember_discharges_obligation`.** Under the circuit-backed instance, the
non-membership obligation `.named NM_OBLIGATION` is DISCHARGED (`Verify = true`) by the witness IFF the
row is range-checked AND both gap gates hold. The verify seam carries a GENUINE circuit verdict. -/
theorem nonMember_discharges_obligation (env : VmRowEnv) (c : NmCols) (xs : List Int) :
    Verifiable.Verify (ObligationStmt.named NM_OBLIGATION) (⟨env, c, xs⟩ : NmWitness) = true
      ↔ (NmRowOk c env ∧ (gapLoGate c).holds env ∧ (gapHiGate c).holds env) := by
  show (decide (NM_OBLIGATION = NM_OBLIGATION) && decide (NmRowOk c env)
          && decide ((gapLoGate c).holds env) && decide ((gapHiGate c).holds env)) = true ↔ _
  rw [decide_eq_true (rfl), Bool.true_and]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- **`nonMembership_witnessed_has_circuit_teeth` (THE BUCKET-B `witnessed` ARM, DISCHARGED BY
A REAL NON-MEMBERSHIP CIRCUIT).** Route the non-membership obligation to the `witnessed` arm
(`Guard.witnessed (.named NM_OBLIGATION)`), supply the circuit witness, and — under the gap
decoding (`NmRowEncodes`) — if the guard `admits` then the spent nullifier is NOT in the committed set.
So the `witnessed` non-membership arm is discharged by the GENUINE gap circuit (not an empty
placeholder): the circuit teeth are real and they DECIDE no-double-spend. This is the non-membership
analog of Policy.lean's `sumEquals_witnessed_has_circuit_teeth`. -/
theorem nonMembership_witnessed_has_circuit_teeth
    (env : VmRowEnv) (c : NmCols) (xs : List Int) (nf : Int)
    (req : RecordKernelState) (henc : NmRowEncodes c env xs nf)
    (hadm : (Guard.witnessed (.named NM_OBLIGATION) : Guard RecordKernelState ObligationStmt).admits
              req (fun _ => (⟨env, c, xs⟩ : NmWitness)) = true) :
    nf ∉ xs := by
  rw [Guard.admits_witnessed, nonMember_discharges_obligation env c xs] at hadm
  obtain ⟨hwf, hg⟩ := hadm
  exact nonMemberGate_sound c env xs nf hwf henc hg

/-! ## §7 — NON-VACUITY + concrete ANTI-GHOST: a real fresh-nullifier row + a double-spend row UNSAT.

A concrete committed set `[10, 20, 30]` (sorted), and two nullifiers: a FRESH one `25` (sits in the
gap `(20, 30)` — the gate HOLDS, non-membership proved) and an ALREADY-SPENT one `20` (a member — no
honest neighbor row satisfies the gate; the gate is UNSAT). This is the mandatory teeth check: the
non-membership gate is not vacuous; it ACCEPTS exactly the fresh nullifiers and REJECTS a replay. -/

/-- The demo committed nullifier set `[10, 20, 30]`, strict-ascending. -/
def demoSet : List Int := [10, 20, 30]

/-- `demoSet` is strict-ascending. -/
theorem demoSet_sorted : SortedAsc demoSet := by
  refine ⟨by norm_num, ?_⟩; refine ⟨by norm_num, ?_⟩; exact True.intro

/-- The demo non-membership column layout (five distinct columns). -/
def demoCols : NmCols := { nf := 0, lo := 1, hi := 2, dLo := 3, dHi := 4 }

/-- The FRESH-nullifier row: `nf = 25`, neighbors `(20, 30)` (the genuine gap of `demoSet`), exact gaps
`dLo = 25−20−1 = 4`, `dHi = 30−25−1 = 4`. -/
def freshRow : VmRowEnv where
  loc := fun v =>
    if v = 0 then 25 else if v = 1 then 20 else if v = 2 then 30
    else if v = 3 then 4 else if v = 4 then 4 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `25 ∉ demoSet` (the fresh nullifier really is a non-member). -/
theorem fresh_not_mem : (25 : Int) ∉ demoSet := by decide

-- The non-membership gate ACCEPTS the fresh nullifier `25` on its real neighbors:
#guard (decide (NmRowOk demoCols freshRow))                                -- gaps non-negative
#guard (decide ((gapLoGate demoCols).holds freshRow))                      -- 25 = 20+1+4
#guard (decide ((gapHiGate demoCols).holds freshRow))                      -- 30 = 25+1+4

/-- `freshRow`'s neighbors `(20, 30)` ARE a genuine empty gap of `demoSet`. -/
theorem freshRow_gap : GapInterval (freshRow.loc demoCols.lo) (freshRow.loc demoCols.hi) demoSet := by
  show GapInterval (20 : Int) 30 demoSet
  intro y hy
  fin_cases hy <;> norm_num

/-- **`freshRow_proves_nonmembership` (NON-VACUITY, witness TRUE).** The non-membership gate,
on `freshRow` (the fresh nullifier `25` with its genuine neighbors), PROVES `25 ∉ demoSet`: a real,
non-vacuous fresh-nullifier non-membership certificate. The gate has teeth. -/
theorem freshRow_proves_nonmembership : (25 : Int) ∉ demoSet := by
  apply nonMemberGate_sound demoCols freshRow demoSet 25
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, freshRow_gap⟩
  · exact ⟨by decide, by decide⟩

/-- A DOUBLE-SPEND row: the same neighbors `(20, 30)` but `nf = 20` (an ALREADY-SPENT member). The
prover tries to pass the gate for a member. -/
def doubleSpendRow : VmRowEnv where
  loc := fun v =>
    if v = 0 then 20 else if v = 1 then 20 else if v = 2 then 30
    else if v = 3 then (-1) else if v = 4 then 9 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `doubleSpendRow`'s neighbors `(20, 30)` form a genuine gap of `demoSet`. -/
theorem doubleSpendRow_gap :
    GapInterval (doubleSpendRow.loc demoCols.lo) (doubleSpendRow.loc demoCols.hi) demoSet := by
  show GapInterval (20 : Int) 30 demoSet
  intro y hy
  fin_cases hy <;> norm_num

/-- **`doubleSpend_unsat` (THE CONCRETE ANTI-GHOST).** A double-spend attempt — `nf = 20`,
which IS a member of `demoSet`, with its genuine neighbors `(20, 30)` — CANNOT satisfy both gap gates
under any range-checked witness. The gate is UNSAT for an already-spent nullifier: no honest
non-membership certificate exists for a member. This is the no-double-spend tooth the running circuit
LACKED, now real. -/
theorem doubleSpend_unsat (hwf : NmRowOk demoCols doubleSpendRow) :
    ¬ ((gapLoGate demoCols).holds doubleSpendRow ∧ (gapHiGate demoCols).holds doubleSpendRow) := by
  apply nonMemberGate_rejects_member demoCols doubleSpendRow demoSet 20 hwf
  · exact ⟨by decide, doubleSpendRow_gap⟩
  · decide

/-! ## §8 — THE EXECUTOR ↔ CIRCUIT CONNECTOR + the deployed-descriptor boundary (honest).

The two halves meet here. The executor term (`noteSpendStmt`) carries the no-double-spend INLINE
(`noteSpendStmt_no_double_spend`: a commit ⇒ `nf ∉ nullifiers`). The circuit gate (`nonMemberGate_sound`)
proves the SAME `nf ∉ set` from a gate-satisfying row. So when the circuit's committed `set` IS the
executor's `nullifiers` (the named root binding the deployed descriptor must supply — see boundary),
the gate's non-membership proof DISCHARGES exactly the executor's double-spend guard precondition. -/

/-- **`circuit_gate_meets_executor_guard` (the two halves agree).** If the circuit's committed
set is the executor kernel's nullifier set (`xs = k.nullifiers`, the named-root binding), then a
gate-satisfying, range-checked, honestly-decoded row proves EXACTLY the precondition under which the
executor term `noteSpendStmt` COMMITS — `nf ∉ k.nullifiers`. The circuit's non-membership gate and the
executor's in-band double-spend guard speak about the same fact: the gate is the in-circuit witness of
what the executor enforces in-band. -/
theorem circuit_gate_meets_executor_guard (c : NmCols) (env : VmRowEnv) (k : RecordKernelState)
    (nf : Int) (hwf : NmRowOk c env)
    (henc : NmRowEncodes c env (k.nullifiers.map Int.ofNat) nf)
    (hg : (gapLoGate c).holds env ∧ (gapHiGate c).holds env)
    (nfN : Nat) (hnf : nf = Int.ofNat nfN) :
    nfN ∉ k.nullifiers := by
  have hni : nf ∉ k.nullifiers.map Int.ofNat := nonMemberGate_sound c env _ nf hwf henc hg
  intro hmem
  exact hni (by rw [hnf]; exact List.mem_map_of_mem hmem)

/-! ## §8¾ — DISCHARGING `NmRowEncodes`: the adjacency opening FORCES the gap decode.

§8 carried `NmRowEncodes` as a NAMED hypothesis: the gate's soundness rested on the *assumed* fact
that the prover's `(lo, hi)` columns straddle a genuine empty gap of the committed nullifier set. That
assumption is exactly what permits the documented WIDE-BRACKET FORGERY — a commitment-knower picks
`lo = 0x00…`, `hi = 0xFF…` (bracketing-but-not-adjacent) to fake non-membership of ANY candidate.

The DEPLOYED descriptor now FORCES that decode with a real arithmetic constraint: the sorted-tree
**neighbor-adjacency** opening (`circuit/src/membership_adjacency_air.rs`, AIR
`dregg-membership-adjacency-v1`, the in-circuit Merkle index reconstruction with
`idx_upper == idx_lower + 1` and forge-test `forge_nonconsecutive_wide_bracket_is_rejected`). It
authenticates `lo` and `hi` as leaves of the SAME committed root and proves their indices are
CONSECUTIVE. The Lean shadow of that constraint is `Crypto.NonMembership.Adjacent xs lo hi` (lo, hi are
consecutive entries of the sorted committed spine). The bridge below proves: over a `Sorted` committed
spine, `Adjacent` IMPLIES `GapInterval` — so the gate's carried `GapInterval` decode becomes a THEOREM
of the now-forced adjacency constraint, not an assumption. A non-consecutive wide bracket can no longer
be `Adjacent`, so it can no longer discharge the gate. -/

open Dregg2.Crypto.NonMembership (Sorted Adjacent sorted_gap_excludes)

/-- **`adjacent_gives_gapInterval` — THE FORGERY-CLOSING BRIDGE.** Over a `Sorted` committed spine
`xs`, if `lo` and `hi` are ADJACENT (consecutive leaves — the property the deployed adjacency AIR's
`idx_upper == idx_lower + 1` check FORCES), then the open interval `(lo, hi)` is empty: every committed
`y` is `≤ lo` or `≥ hi`. This is `GapInterval lo hi xs` derived (not assumed). The proof is the
contrapositive of `sorted_gap_excludes`: a `y` strictly inside `(lo, hi)` would be excluded from `xs`,
contradicting `y ∈ xs`. A non-consecutive WIDE BRACKET (`lo = 0x00…`, `hi = 0xFF…` with leaves between)
is NOT `Adjacent`, so it cannot reach this conclusion — the forge is closed at the hypothesis. -/
theorem adjacent_gives_gapInterval {lo hi : Int} {xs : List Int}
    (hs : Sorted xs) (hadj : Adjacent xs lo hi) : GapInterval lo hi xs := by
  intro y hy
  by_cases h : y ≤ lo
  · exact Or.inl h
  · by_cases h2 : hi ≤ y
    · exact Or.inr h2
    · exact absurd hy (sorted_gap_excludes xs lo hi y hs hadj (not_le.mp h) (not_le.mp h2))

/-- **`NmRowAdjacencyForced c env xs nf`** — the FORCED form of the §5 decode hypothesis: instead of
ASSUMING the empty-gap `GapInterval`, it carries the WIRE-LEVEL constraints the deployed descriptor
forces — (a) the committed spine is sorted (the named-root sorted-set discipline), (b) the row's
`nf`-column carries the spent nullifier, and (c) the row's `(lo, hi)`-columns are ADJACENT leaves of
the committed sorted spine (the adjacency AIR's consecutive-index certificate). The §5 `GapInterval`
is now a CONSEQUENCE (`adjacent_gives_gapInterval`), not a carried assumption. -/
structure NmRowAdjacencyForced (c : NmCols) (env : VmRowEnv) (xs : List Int) (nf : Int) : Prop where
  /-- The committed nullifier spine is strictly sorted (the named-root sorted-set discipline). -/
  sorted : Sorted xs
  /-- The `nf`-column carries the spent nullifier. -/
  nfCol : env.loc c.nf = nf
  /-- The `(lo, hi)`-columns are ADJACENT (consecutive) committed leaves — FORCED by the deployed
  sorted-tree adjacency opening (`verify_adjacency`'s `idx_upper == idx_lower + 1`), not assumed. -/
  adjacent : Adjacent xs (env.loc c.lo) (env.loc c.hi)

/-- **`nmRowEncodes_of_adjacency` — `NmRowEncodes` IS DISCHARGED.** The §5 decode hypothesis
`NmRowEncodes` is no longer carried: it is DERIVED from the now-forced adjacency constraint. The
`nf`-column fact is direct; the `GapInterval` is `adjacent_gives_gapInterval` on the forced
adjacency over the sorted spine. So the gate's non-membership soundness no longer ASSUMES the gap
decode — it FOLLOWS from the deployed adjacency AIR. -/
theorem nmRowEncodes_of_adjacency {c : NmCols} {env : VmRowEnv} {xs : List Int} {nf : Int}
    (h : NmRowAdjacencyForced c env xs nf) : NmRowEncodes c env xs nf :=
  ⟨h.nfCol, adjacent_gives_gapInterval h.sorted h.adjacent⟩

/-- **`nonMemberGate_sound_forced` — the gate's SOUNDNESS, with `NmRowEncodes` DISCHARGED.** A
range-checked, gate-satisfying row whose `(lo, hi)` are FORCED adjacent committed leaves (the deployed
adjacency opening) proves `nf ∉ xs`. This is `nonMemberGate_sound` with the carried `NmRowEncodes`
hypothesis replaced by the wire-forced `NmRowAdjacencyForced` — no assumed decode remains. -/
theorem nonMemberGate_sound_forced (c : NmCols) (env : VmRowEnv) (xs : List Int) (nf : Int)
    (hwf : NmRowOk c env) (hadj : NmRowAdjacencyForced c env xs nf)
    (hg : (gapLoGate c).holds env ∧ (gapHiGate c).holds env) :
    nf ∉ xs :=
  nonMemberGate_sound c env xs nf hwf (nmRowEncodes_of_adjacency hadj) hg

/-- **`circuit_gate_meets_executor_guard_forced` (THE DEPLOYED NO-DOUBLE-SPEND, NO ASSUMED DECODE).**
The deployed-shape statement: if the circuit's committed set is the executor kernel's nullifier set,
the range-checked row satisfies both gap gates, AND the row's `(lo, hi)` are FORCED adjacent leaves of
the committed sorted nullifier root (the deployed adjacency AIR), then the spent nullifier is NOT in the
set — the EXACT precondition under which the executor term `noteSpendStmt` commits. Unlike
`circuit_gate_meets_executor_guard`, this carries NO `NmRowEncodes` assumption: the gap decode is forced
by the adjacency constraint. The wide-bracket double-spend forgery is therefore IMPOSSIBLE — a
non-consecutive `(lo, hi)` cannot satisfy `Adjacent`, so it cannot reach `nf ∉ nullifiers`. -/
theorem circuit_gate_meets_executor_guard_forced (c : NmCols) (env : VmRowEnv) (k : RecordKernelState)
    (nf : Int) (hwf : NmRowOk c env)
    (hadj : NmRowAdjacencyForced c env (k.nullifiers.map Int.ofNat) nf)
    (hg : (gapLoGate c).holds env ∧ (gapHiGate c).holds env)
    (nfN : Nat) (hnf : nf = Int.ofNat nfN) :
    nfN ∉ k.nullifiers := by
  have hni : nf ∉ k.nullifiers.map Int.ofNat :=
    nonMemberGate_sound_forced c env _ nf hwf hadj hg
  intro hmem
  exact hni (by rw [hnf]; exact List.mem_map_of_mem hmem)

/-- **`wide_bracket_forge_rejected` (THE FORGE IS CLOSED — MUTATION-CONFIRM, LEAN SIDE).** A
NON-CONSECUTIVE wide bracket cannot forge non-membership: if the prover's claimed `(lo, hi)` are NOT
`Adjacent` in the committed sorted spine, then no `NmRowAdjacencyForced` witness exists for them, so the
gate's forced-soundness lane is unreachable. Stated as: a `NmRowAdjacencyForced` whose adjacency claim
is FALSE is uninhabited. This is the Lean shadow of `forge_nonconsecutive_wide_bracket_is_rejected`: the
adjacency AIR refuses to build a trace for a non-consecutive pair, so the forced lane never fires. -/
theorem wide_bracket_forge_rejected (c : NmCols) (env : VmRowEnv) (xs : List Int) (nf : Int)
    (hwide : ¬ Adjacent xs (env.loc c.lo) (env.loc c.hi)) :
    ¬ NmRowAdjacencyForced c env xs nf :=
  fun h => hwide h.adjacent

#assert_axioms adjacent_gives_gapInterval
#assert_axioms nmRowEncodes_of_adjacency
#assert_axioms nonMemberGate_sound_forced
#assert_axioms circuit_gate_meets_executor_guard_forced
#assert_axioms wide_bracket_forge_rejected

/-!
### What remains for the FULL deployed noteSpend descriptor (reported)

This module supplies the missing non-membership GATE-KIND with real teeth on both sides, AND (§8¾)
DISCHARGES the `NmRowEncodes` decode against the deployed sorted-tree adjacency opening. The state of
the DEPLOYED noteSpend non-membership:

1. **The sorted-tree adjacency OPENING — NOW THE FORCING CONSTRAINT, NOT A NAMED HYPOTHESIS.** The
   `(lo, hi)` columns the gate reads are the PROVER's, but they are no longer free: the deployed
   adjacency AIR (`circuit/src/membership_adjacency_air.rs`, `dregg-membership-adjacency-v1`)
   authenticates `lo`,`hi` as leaves of the SAME committed root via full Merkle paths and reconstructs
   their indices IN-CIRCUIT, enforcing `idx_upper == idx_lower + 1` (consecutive). The Lean shadow of
   that constraint is `Adjacent xs lo hi`, and §8¾'s `adjacent_gives_gapInterval` proves
   `Adjacent ⟹ GapInterval` over a `Sorted` spine — so `NmRowEncodes` is DISCHARGED
   (`nmRowEncodes_of_adjacency`), no longer carried. The WIDE-BRACKET forge (`lo = 0x00…`,
   `hi = 0xFF…`, non-adjacent) is rejected at the hypothesis (`wide_bracket_forge_rejected`): a
   non-consecutive pair is not `Adjacent`, so the forced-soundness lane is unreachable. The forge-test
   `forge_nonconsecutive_wide_bracket_is_rejected` is the Rust mutation-confirm of the same fact.

2. **Wiring the gap columns into the EffectVM layout** (5 witness columns: `nf`,`lo`,`hi`,`dLo`,`dHi`)
   and the two range checks (`dLo`,`dHi ∈ [0, 2^k)`) as real `RangeSpec`s, plus selector-gating the
   gates to the noteSpend row.

3. **The set-update half** (insert `nf` between `lo` and `hi`, re-root) is the existing
   `gNullifierRootUpdate` accumulator gate (`EffectVmEmitNoteSpend §B`); this freshness gate composes
   BEFORE it (prove `nf` fresh, then commit the insert). The two together = the full deployed
   no-double-spend.

So: the EXECUTOR-side no-double-spend is CLOSED in-band (`noteSpendStmt_no_double_spend`); the
CIRCUIT-side non-membership GATE is built with real teeth (sound + complete + anti-ghost +
`witnessed`-discharge); and the formerly-carried `NmRowEncodes` gap decode is DISCHARGED against the
deployed adjacency opening (§8¾) — the wide-bracket double-spend forgery is closed. The remaining FFI
boundary (Rust descriptor must call `verify_adjacency` on the noteSpend `(lo,hi)` columns) is a wiring
conformance, the Lean force is now a theorem.
-/

/-! ## §8½ — THE RUNNABLE EFFECTVM DESCRIPTOR IS NOW FULL-STATE (magnesium breadth).

The §1–§8 content built the EXECUTOR-side no-double-spend (in-band in the term) + the genuine SORTED-
NEIGHBOR non-membership CIRCUIT GATE (sound + complete + anti-ghost) — the missing FRESHNESS gate-kind.
In a parallel lift, the per-row RUNNABLE EffectVM descriptor for noteSpend (the circuit the prover
ACTUALLY RUNS, `EffectVmEmitNoteSpend §W`) has been raised to the GENERIC full-state-on-RUNNABLE crown:
a satisfying witness of the WIDE descriptor (the dedicated `sysRootsDigestCol = 186` carrier +
`wideHashSites`) pins the FULL 17-field post-state — the per-cell transparent credit + nonce tick AND the
`nullifiers`-root committed-digest advance AND every other side-table root frozen — and tamper of ANY
field/root is UNSAT. We re-export the crown here so the Argus noteSpend module names the RUNNABLE
descriptor's full-state property alongside the non-membership gate; the headline FRESHNESS leg this
file's §2–§5 gate supplies is the still-named non-per-row residual (the digest advance binds the INSERT,
not the non-membership). -/

/-- **`noteSpend_runnable_full_sound_argus` — the RUNNABLE EffectVM descriptor binds the FULL state.**
Re-export of `EffectVmEmitNoteSpend.noteSpend_runnable_full_sound`: a row satisfying noteSpend's WIDE
RUNNABLE descriptor, under the structured decode, pins the FULL 17-field declarative post-state — the
per-cell credit + nonce tick AND the `nullifiers`-root digest advance AND every other side-table root
frozen. This is the per-row layer at FULL state; the FRESHNESS non-membership (this file's §2–§5 gate)
remains the named turn-level leg. -/
theorem noteSpend_runnable_full_sound_argus (hash : List ℤ → ℤ)
    (value : ℤ) (preRoots postRoots : Dregg2.Exec.SystemRoots.SysRoots) (step : ℤ)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (pre post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState)
    (pr : Dregg2.Exec.SystemRoots.SysRoots)
    (hrow : Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.IsNoteSpendRow env)
    (hdec : Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.NoteSpendDecode hash value preRoots postRoots step
              env pre post pr)
    (hgatesat : Dregg2.Circuit.Emit.EffectVmEmit.satisfiedVm hash
              Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.noteSpendVmDescriptorWide env true false) :
    Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.NoteSpendFullClause hash value preRoots postRoots step
      pre post pr :=
  Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.noteSpend_runnable_full_sound
    hash value preRoots postRoots step env pre post pr hrow hdec hgatesat

#assert_axioms noteSpend_runnable_full_sound_argus

/-! ## §9 — Axiom-hygiene tripwires. Each keystone ⊆ {propext, Classical.choice, Quot.sound}. -/

-- Executor side:
#assert_axioms interp_noteSpendStmt_eq_noteSpendNullifier
#assert_axioms noteSpendStmt_no_double_spend
#assert_axioms noteSpendStmt_inserts
#assert_axioms noteSpendStmt_then_reject
#assert_axioms noteSpendStmt_replay_rejected
-- keystone-audit companions (named satisfiable + teeth), kernel-triple clean.
#assert_axioms kSpent_fresh_commits
#assert_axioms noteSpendStmt_no_double_spend_satisfiable
#assert_axioms noteSpendStmt_inserts_satisfiable
#assert_axioms noteSpendStmt_then_reject_satisfiable
#assert_axioms noteSpendStmt_teeth
#assert_axioms noteSpendStmt_replay_rejected_satisfiable
#assert_axioms noteSpendStmt_replay_rejected_teeth

-- Math core (the sorted-neighbor non-membership argument):
#assert_axioms sortedAsc_head_lt_mem
#assert_axioms neighborGap_sound
#assert_axioms neighborGap_complete
#assert_axioms neighborGap_iff_not_mem

-- The circuit gate (arithmetic teeth + soundness/completeness of the gate):
#assert_axioms gapLo_holds_iff
#assert_axioms gapHi_holds_iff
#assert_axioms nonMemberGate_sound_between
#assert_axioms nonMemberGate_complete

-- The gap bridge (§4) + circuit⟺protocol (§5):
#assert_axioms between_gap_not_mem
#assert_axioms mem_not_between_gap
#assert_axioms gapEndpointsAux_lo_le
#assert_axioms gapEndpointsAux_gives_gap
#assert_axioms neighborGap_gives_gap
#assert_axioms nonMemberGate_sound
#assert_axioms nonMemberGate_rejects_member
#assert_axioms nonMemberGate_complete_nonmember

-- The witnessed-arm discharge (§6):
#assert_axioms nonMember_discharges_obligation
#assert_axioms nonMembership_witnessed_has_circuit_teeth

-- Non-vacuity + concrete anti-ghost (§7) + the executor↔circuit connector (§8):
#assert_axioms freshRow_proves_nonmembership
#assert_axioms doubleSpend_unsat
#assert_axioms circuit_gate_meets_executor_guard

end Dregg2.Circuit.Argus
