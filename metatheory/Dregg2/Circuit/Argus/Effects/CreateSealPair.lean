/-
# Dregg2.Circuit.Argus.Effects.CreateSealPair — the CREATE-SEAL-PAIR capability effect welded into the
Argus IR, in its OWN disjoint module (the per-effect-farm vehicle, off the Argus cornerstone).

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn (single-cell moves) and on createEscrow (a two-component side-table move).
`Effects/Delegate.lean` welded the first CAP-GRAPH effect (a single `setCaps` write of a `grant …` map);
`Effects/BalanceA.lean` welded against a FULL-STATE Surface2 `*_full_sound` (the WHOLE 17-field
post-state). This module welds CREATE-SEAL-PAIR (`apply_create_seal_pair`, `apply.rs:2675`) — a second
CAP-GRAPH effect, and like balanceA it carries a genuine Surface2 full-state descriptor, so we PREFER the
stronger BalanceA surface (conclude the WHOLE `CreateSealPairSpec`), not the per-cell EffectVM projection.

## ⚑ COMPLETENESS-FIX (2026-06-09): the R3 `pidFresh` gate is now an IN-CIRCUIT conjunct.

⚑ A prior version of this module refined the IR term against the WEAKER chained executor
`createSealPairChainA` (gating ONLY on `stateAuthB`), and CARRIED — as a "witnessed divergence" — the fact
that the IR term still committed on a STALE (already-bound) pid. That was a SEVERE COMPLETENESS GAP, not a
seam: the AUTHORITATIVE executor a host runs is `execHandlerTurn` (the FFI **cutover executor**,
`Exec/FFI.lean:18`), whose create-seal-pair step is the R3-CLOSING handler `createSealPairStep`
(`Exec/Handlers/Seal.lean:100`), which gates on `stateAuthB ∧ pidFresh`. The crown-jewel functional
refinement (`Spec/FunctionalRefinement.lean`'s `createSealPair_triangle` + `createSealPair_antighost`)
validates THAT step, with `pidFresh` as the R3 no-pid-reuse discipline. A light client that verified ONLY
the weaker descriptor would ACCEPT a pid-reuse create — the documented R3 attack: because `findSealedBox`
returns the FIRST match (`RecordKernel.lean:460`), re-using a pid that already binds a box lets a STALE
unsealer-cap holder open the NEW pair's box (and `unsealerCap pid = endpoint pid [reply]` is the SAME cap
across createSealPair calls, so old/new holders are indistinguishable to `holdsSealCapFor pid`).

`pidFresh k pid = (findSealedBox k.sealedBoxes pid).isNone` is a NON-MEMBERSHIP / id-freshness check over
committed `sealedBoxes` — it is NOT a named crypto primitive, so per the circuit acceptance criterion it
MUST be an in-circuit conjunct. We CLOSE the gap by strengthening the RUNNABLE descriptor's gate to the
genuine R3 gate: the Argus IR term's `RecStmt.guard` (which `compile` emits as a circuit constraint — the
one-term-two-readings lever, `Argus/Stmt.lean`'s "`insFresh` carries no-double-spend *inline*") now carries
`stateAuthB ∧ pidFresh`. The cornerstone refines `createSealPairStep` (the cutover executor's step); the
anti-gate tooth (§6) proves the strengthened term REJECTS — `interp … = none` — a reused-pid witness. So
the descriptor a light client checks now enforces the SAME admissibility set the running executor does.

## The executor primitive, unfolded (read off the CODE) — the R3-CLOSING `createSealPairStep`

The handler step `createSealPairStep` (`Exec/Handlers/Seal.lean:100`), the one `execHandlerTurn` runs and
`createSealPair_triangle` validates, is:

    createSealPairStep k a
      = if stateAuthB k.caps a.actor a.sealerHolder = true ∧ pidFresh k a.pid = true then
          some { k with caps := grant (grant k.caps a.sealerHolder (sealerCap a.pid))
                                       a.unsealerHolder (unsealerCap a.pid) }
        else none

So a committed create-seal-pair:

  * **GUARD** `stateAuthB k.caps actor sealerHolder = true ∧ pidFresh k pid = true` — `actor` holds
    authority over `sealerHolder` (the writer of the pair) AND `pid` is FRESH (no box already bound under
    it — the R3 conjunct that serializes pid usage so the first-match `findSealedBox` is unambiguous).
  * **TOUCHED `caps`** ← `createSealPairCaps … pid sealerHolder unsealerHolder` (= the double `grant`):
    `sealerHolder` gains the sealer cap `sealerCap pid`, `unsealerHolder` gains the unsealer cap
    `unsealerCap pid` — TWO real c-list grants, a genuine sealer/unsealer KEYPAIR
    (`createSealPairCaps_correct`: the two caps are GENUINELY DISTINCT — `[grant]` vs `[reply]` rights).
  * **FRAME** every other `RecordKernelState` component literally unchanged (`caps` is the one touched
    field; in particular `sealedBoxes` is FRAMED — a fresh pair holds no box yet). So the IR body is
    `seq (guard (stateAuthB ∧ pidFresh)) (setCaps …)` — the §A cap-graph write primitive (the `Delegate`
    shape) under the R3 gate.

`createSealPairCaps caps pid sealerHolder unsealerHolder
:= grant (grant caps sealerHolder (sealerCap pid)) unsealerHolder (unsealerCap pid)` is the validated
post-`caps` map (`createSealPairCaps_correct`), which we reuse VERBATIM as the `setCaps` leaf.

## The circuit side — the audited Surface2 FULL-STATE descriptor (the BalanceA surface)

The full-state digest circuit is `Inst.CreateSealPairA.createSealPairE` (the v2 `EffectSpec2` whose touched
component is the WHOLE `caps` slot-function, a `funcComponent` full-function digest) + its soundness
`createSealPairA_full_sound : satisfiedE2 … (createSealPairE D hD) … ⟹ CreateSealPairSpec` — a FULL
17-field declarative post-state agreement, keyed on the chained executor via the independent
`createSealPair_iff_spec`. This Surface2 circuit pins the WHOLE post-state `CreateSealPairSpec` (the double
cap grant + the log + every other kernel field frozen — full `caps`-function equality, so a tamper of ANY
holder's slot is REJECTED). It is the `caps`-DIGEST half of the descriptor (NOT a module this file owns, so
its guard column is left at `stateAuthB`); the R3 `pidFresh` admissibility lives in the RUNNABLE Argus
term's gate, where a light client's `compile` reads it as a constraint.

## What the weld pins

`createSealPair_compile_sound`: a satisfying witness of the Surface2 circuit `createSealPairE` (under the
realizable portals `RestIffNoCaps`/`logHashInjective`/`Function.Injective D`) and a COMMITTING run of the
strengthened (R3-gated) IR term AGREE on the WHOLE chained post-state
`st' = { kernel := k', log := receipt :: st.log }` — all 17 kernel fields + the receipt log. The
`caps`-component digest portal (`Function.Injective D`) enters ONLY inside the reused
`createSealPairA_full_sound`, not in the welded conclusion's statement. Because the IR gate now carries
`pidFresh`, a committing IR run is exactly a committing R3-handler run (`createSealPairStep`), so the weld
speaks about the AUTHORITATIVE executor.

## Honesty

`#assert_axioms` on the cornerstone + the weld + the R3 anti-gate tooth ⊆ {propext, Classical.choice,
Quot.sound}; Poseidon2 CR / whole-`caps`-function digest enters ONLY inside the reused
`createSealPairA_full_sound` (its `Function.Injective D` hypothesis), never in the welded conclusion's
statement. No `sorry`, no `:= True`, no `native_decide`, no `rfl`-posing-as-bridge. Non-vacuity teeth: the
IR term genuinely INSTALLS the keypair (observable double cap-graph write), the two granted caps are
GENUINELY DISTINCT, it genuinely REJECTS an unauthorized writer (fail-closed), it genuinely REJECTS a
REUSED pid (the R3 anti-gate tooth, §6), and the welded descriptor is the genuine Surface2 full-state one
(full `caps`-function equality), not the inert placeholder. Imports are read-only; this file owns only
itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.createSealPairA
import Dregg2.Exec.Handlers.Seal          -- the R3-CLOSING `createSealPairStep` + `pidFresh` (cutover step)
import Dregg2.Spec.FunctionalRefinement   -- the R3 triangle `createSealPair_triangle`/`_antighost`

namespace Dregg2.Circuit.Argus.Effects.CreateSealPair

open Dregg2.Exec
open Dregg2.Authority (Caps Cap Auth Label)
-- The CHAINED create-seal-pair executor `createSealPairChainA`, the seal-cap helpers, AND the unified
-- action executor `execFullA` all live in `Dregg2.Exec.TurnExecutorFull`; opened broadly (as BalanceA
-- does) so the §0 bridge / §3 chained lift / IR leaf can name them unqualified. (`grant` is in
-- `Dregg2.Exec`, already opened above.)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Circuit.Argus (RecStmt interp)
-- Broad opens mirroring `Inst/createSealPairA.lean` so the standalone-descriptor names resolve unqualified
-- (`logHashInjective` lives in `StateCommit`; `Surface2`/`satisfiedE2`/`encodeE2` in `EffectCommit2`).
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.Spec.SealPairCreation
  (CreateSealPairSpec CreateSealPairGuard createSealPairCaps createSealPairReceipt
   createSealPairCaps_correct createSealPair_iff_spec)
-- `CreateSealPairArgs` resolves to the Inst (Surface2-circuit) args record — the type `createSealPairE`
-- is keyed on; the §4 weld builds `⟨pid, actor, sealerHolder, unsealerHolder⟩ : CreateSealPairArgs` there.
open Dregg2.Circuit.Inst.CreateSealPairA
  (CreateSealPairArgs RestIffNoCaps createSealPairE createSealPairA_full_sound)
-- The R3-CLOSING handler step `createSealPairStep` (the cutover executor's create-seal-pair arm) + the
-- pid-freshness gate `pidFresh`. `createSealPairStep` consumes `Handlers.Seal.CreateSealPairArgs`
-- (structurally identical, distinct type); referenced fully-qualified at its use sites in §0/§2.
open Dregg2.Exec.Handlers.Seal (createSealPairStep pidFresh)
-- The crown-jewel R3 triangle: `createSealPairStep k a = some k' ↔ (stateAuthB ∧ pidFresh) ∧ k' = spec`,
-- and the anti-ghost tooth (a reused pid / wrong-holder candidate cannot come out of the step).
open Dregg2.Spec.FunctionalRefinement (createSealPairGate createSealPairSpec createSealPair_triangle)

set_option autoImplicit false

/-! ## §0 — THE KERNEL TARGET: the R3-CLOSING `createSealPairStep`, and its bridge to the chained executor.

The Argus `interp` produces `Option RecordKernelState` (the bare kernel). The AUTHORITATIVE create-seal-pair
step — the one `execHandlerTurn` (the FFI cutover executor) runs and `createSealPair_triangle` validates —
is the R3-closing handler `createSealPairStep` (`Exec/Handlers/Seal.lean:100`), which gates on
`stateAuthB ∧ pidFresh` and rewrites `caps` to the double grant. We refine the IR term DIRECTLY to THAT
step (so the `pidFresh` precondition becomes an in-circuit conjunct of the runnable descriptor's gate). The
Surface2 full-state digest circuit (§4) is keyed on the chained executor `createSealPairChainA`, so we ALSO
prove (not assert) the bridge `createSealPairStep_to_chainA`: a committed R3 step lifts to a committed
chained run with the SAME kernel — sound because `pidFresh` only RESTRICTS the chained executor's admission
(both share the `stateAuthB`-conjunct and the SAME post-`caps`). -/

/-- The handler-args record `createSealPairStep` consumes (= `Handlers.Seal.CreateSealPairArgs`). A local
abbreviation built from the four scalars, so §0/§2 read uniformly. -/
def csArgs (pid : Nat) (actor sealerHolder unsealerHolder : CellId) :
    Dregg2.Exec.Handlers.Seal.CreateSealPairArgs :=
  { pid := pid, actor := actor, sealerHolder := sealerHolder, unsealerHolder := unsealerHolder }

/-- **`createSealPairStep_to_chainA` — the bridge (PROVED, not asserted).** A committed R3 step
`createSealPairStep k (csArgs …) = some k'` (which required `stateAuthB ∧ pidFresh`) lifts to a committed
chained run `createSealPairChainA s … = some ⟨k', receipt :: s.log⟩` over any chained state whose kernel is
`k` — the chained executor's `stateAuthB`-only gate is implied by the R3 gate, and the post-`caps` /
receipt are identical. So the R3 target this module refines the IR term to lifts faithfully to the chained
executor the Surface2 descriptor speaks about (the receipt-log stamp made explicit). -/
theorem createSealPairStep_to_chainA (s : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) (k' : RecordKernelState)
    (h : createSealPairStep s.kernel (csArgs pid actor sealerHolder unsealerHolder) = some k') :
    createSealPairChainA s pid actor sealerHolder unsealerHolder
      = some { kernel := k', log := createSealPairReceipt actor sealerHolder :: s.log } := by
  -- the R3 triangle decodes the committed step: the gate (stateAuthB ∧ pidFresh) holds and `k'` is the spec.
  obtain ⟨hgate, hk'⟩ := (createSealPair_triangle s.kernel k'
    (csArgs pid actor sealerHolder unsealerHolder)).mp h
  -- the chained executor's `if` opens on the stateAuthB conjunct (the FIRST half of the R3 gate).
  unfold createSealPairChainA
  have hauth : stateAuthB s.kernel.caps actor sealerHolder = true := by
    have := hgate.1; simpa [csArgs] using this
  rw [if_pos hauth]
  -- the post-state: `k'` is `createSealPairSpec`, whose `caps` is the double grant the chained arm installs;
  -- the receipt is `createSealPairReceipt actor sealerHolder` by definition.
  simp only [Option.some.injEq]
  have : k' = { s.kernel with
                  caps := grant (grant s.kernel.caps sealerHolder (sealerCap pid))
                                unsealerHolder (unsealerCap pid) } := by
    rw [hk']; simp [createSealPairSpec, csArgs]
  rw [this]; rfl

#assert_axioms createSealPairStep_to_chainA

/-! ## §1 — THE IR TERM: gate on (authority ∧ pid-FRESHNESS), then the single cap-graph write.

`createSealPairStmt = seq (guard (stateAuthB ∧ pidFresh)) (setCaps createSealPairCaps)` — the R3
admissibility premise as an Argus `guard` domain-restrictor, then the SINGLE cap-graph write installing the
validated double-grant map `createSealPairCaps k.caps pid sealerHolder unsealerHolder`. Unlike createEscrow
(two component writes), and exactly like `Delegate`, create-seal-pair touches ONE component (`caps`) — the
§A `setCaps` primitive, with NO new constructor. The `setCaps` leaf re-reads `k.caps` (a pure function of
`k`), so on commit it installs the double grant on the CURRENT cap graph — exactly `createSealPairStep`'s.

⚑ The `guard` carries BOTH conjuncts of the R3 gate — `stateAuthB` (authority over the writer) AND
`pidFresh k pid = (findSealedBox k.sealedBoxes pid).isNone` (no box already bound under `pid`). The
`pidFresh` conjunct is the IN-CIRCUIT closure of the R3 no-pid-reuse discipline: `compile` emits this
`guard` as a circuit constraint (the one-term-two-readings lever), so a light client's proof is UNSAT on a
reused-pid witness (§6). This is the fix for the completeness gap a prior version carried as a "divergence". -/

/-- **The create-seal-pair R3 admissibility gate as a `Bool`** — exactly `createSealPairStep`'s `if`
condition: `actor` holds authority over `sealerHolder` (`stateAuthB`, the writer of the pair) AND `pid` is
FRESH (`pidFresh` — no box already bound under it). Both conjuncts are committed-state reads (no crypto
primitive), so both MUST be — and now ARE — in the runnable descriptor's gate. -/
def createSealPairGuardB (pid : Nat) (actor sealerHolder : CellId) (k : RecordKernelState) : Bool :=
  stateAuthB k.caps actor sealerHolder && pidFresh k pid

/-- **The create-seal-pair effect as an Argus IR term: R3 gate, then the cap-graph write.** A single
`setCaps` move installing the validated double-grant map `createSealPairCaps k.caps pid sealerHolder
unsealerHolder` (= `grant (grant k.caps sealerHolder (sealerCap pid)) unsealerHolder (unsealerCap pid)`),
under the `stateAuthB ∧ pidFresh` gate. Mirrors the `Delegate` shape (gate, then ONE cap-graph write) — the
double grant is a single `caps` overwrite, now serialized by pid freshness. -/
def createSealPairStmt (pid : Nat) (actor sealerHolder unsealerHolder : CellId) : RecStmt :=
  RecStmt.seq (RecStmt.guard (createSealPairGuardB pid actor sealerHolder))
    (RecStmt.setCaps (fun k => createSealPairCaps k.caps pid sealerHolder unsealerHolder))

/-! ## §2 — THE CORNERSTONE: `interp` of the create-seal-pair term IS the R3 step `createSealPairStep`. -/

/-- The R3 `Bool` gate decodes to `createSealPairStep`'s admissibility (the SAME two conjuncts: authority
over the writer ∧ pid freshness). The seal-pair analog of `transferGuard_iff`. -/
theorem createSealPairGuardB_iff (pid : Nat) (actor sealerHolder : CellId) (k : RecordKernelState) :
    createSealPairGuardB pid actor sealerHolder k = true ↔
      (stateAuthB k.caps actor sealerHolder = true ∧ pidFresh k pid = true) := by
  simp only [createSealPairGuardB, Bool.and_eq_true]

/-- **The cornerstone (cap graph, R3-gated).** `interp` of the create-seal-pair term IS the AUTHORITATIVE
R3-closing handler step `createSealPairStep` — the same partial function, by construction, exactly as the
transfer/mint/burn/escrow/delegate cornerstones, now over the CAP-GRAPH double-grant effect (a single `caps`
write gated by `stateAuthB ∧ pidFresh`). The `setCaps` leaf's `createSealPairCaps k.caps …` is
DEFINITIONALLY the double `grant`, the exact map `createSealPairStep` installs; the IR `guard`'s `pidFresh`
conjunct is `createSealPairStep`'s freshness gate, so the two REJECT the same inputs. The executor IS the
meaning of the term — and that executor is now the R3-closing one a host runs (`execHandlerTurn`). -/
theorem interp_createSealPairStmt_eq_createSealPairStep (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) (k : RecordKernelState) :
    interp (createSealPairStmt pid actor sealerHolder unsealerHolder) k
      = createSealPairStep k (csArgs pid actor sealerHolder unsealerHolder) := by
  simp only [createSealPairStmt, interp]
  unfold createSealPairStep csArgs createSealPairCaps
  by_cases hg : createSealPairGuardB pid actor sealerHolder k = true
  · -- ADMIT: the guard fires (`some k`); the `bind` β-reduces and the `setCaps` write installs the double
    -- grant. The RHS `if` opens on the decoded `stateAuthB ∧ pidFresh`.
    rw [if_pos hg]
    simp only [Option.bind_some]
    rw [if_pos ((createSealPairGuardB_iff pid actor sealerHolder k).mp hg)]
  · -- REJECT: the guard fails (`none`); the `bind` short-circuits ⇒ `none`. The RHS `if` closes on the
    -- (negated) decoded conjunction.
    rw [if_neg hg]
    simp only [Option.bind_none]
    rw [if_neg (fun hp => hg ((createSealPairGuardB_iff pid actor sealerHolder k).mpr hp))]

#assert_axioms interp_createSealPairStmt_eq_createSealPairStep

/-! ## §3 — Lifting the cornerstone to the CHAINED executor `execFullA`.

The Surface2 digest descriptor (§4) is keyed on the CHAINED executor `execFullA`/`createSealPairChainA` over
`RecChainedState` (kernel + receipt log). The §2 cornerstone is over the R3 step `createSealPairStep`. Since
`createSealPairStep` only RESTRICTS the chained executor's admission (it ADDS the `pidFresh` conjunct), a
committed R3 step lifts to a committed chained run with the SAME kernel (the §0 bridge
`createSealPairStep_to_chainA`) — the receipt-log stamp made explicit. `execFullA (.createSealPairA …)` is
DIRECTLY `createSealPairChainA`, so the lift is clean. -/

/-- **`interp_createSealPairStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.** When
the §2 cornerstone commits on the kernel (`interp (createSealPairStmt …) st.kernel = some k'`, i.e. the R3
step `createSealPairStep` committed), the unified action executor `execFullA st (.createSealPairA …)`
commits to the chained state `⟨k', createSealPairReceipt actor sealerHolder :: st.log⟩`. So the Argus term's
kernel meaning (now the R3-gated one) lifts to the chained executor the Surface2 descriptor speaks about. -/
theorem interp_createSealPairStmt_chained
    (st : RecChainedState) (pid : Nat) (actor sealerHolder unsealerHolder : CellId)
    (k' : RecordKernelState)
    (hexec : interp (createSealPairStmt pid actor sealerHolder unsealerHolder) st.kernel = some k') :
    execFullA st (.createSealPairA pid actor sealerHolder unsealerHolder)
      = some { kernel := k', log := createSealPairReceipt actor sealerHolder :: st.log } := by
  -- the §2 cornerstone turns the IR term into the R3 step `createSealPairStep`.
  rw [interp_createSealPairStmt_eq_createSealPairStep] at hexec
  -- `execFullA st (.createSealPairA …)` is DIRECTLY `createSealPairChainA st …`; the §0 bridge lifts the
  -- committed R3 step to the committed chained run with the same kernel + the receipt stamp.
  show createSealPairChainA st pid actor sealerHolder unsealerHolder
    = some { kernel := k', log := createSealPairReceipt actor sealerHolder :: st.log }
  exact createSealPairStep_to_chainA st pid actor sealerHolder unsealerHolder k' hexec

#assert_axioms interp_createSealPairStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of create-seal-pair's OWN Surface2 circuit agrees with the
FULL post-state the IR term's executor interpretation produces.

This welds against create-seal-pair's GENUINE Surface2 descriptor `createSealPairE D hD` (whose soundness is
`createSealPairA_full_sound`, concluding the WHOLE `CreateSealPairSpec`) — the BalanceA full-state surface,
NOT the per-cell EffectVM projection. The executor side is routed through §3 (`interp` ⟹ `execFullA`) and
the independent `createSealPair_iff_spec` (executor ⟺ `CreateSealPairSpec`); the circuit side is the audited
`createSealPairA_full_sound` (circuit ⟹ `CreateSealPairSpec`). Both name the SAME `CreateSealPairSpec`, so
they PROVABLY agree on the WHOLE 17-field state + the receipt log — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a create-seal-pair term: create-seal-pair's OWN audited Surface2 v2
circuit step — the full-state arithmetization `satisfiedE2 S (createSealPairE D hD) (encodeE2 …)` satisfied
on the encoded `(st, args, st')` triple. Its soundness `createSealPairA_full_sound` pins the complete
`CreateSealPairSpec`. The create-seal-pair analog of balanceA's `balanceACircuit`, in the descriptor universe
where create-seal-pair carries its OWN genuine FULL-STATE circuit (the whole-`caps`-function digest). -/
def createSealPairCircuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (st : RecChainedState) (args : CreateSealPairArgs) (st' : RecChainedState) : Prop :=
  satisfiedE2 S (createSealPairE D hD) (encodeE2 S (createSealPairE D hD) st args st')

/-- **`createSealPairSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH satisfy
`CreateSealPairSpec st pid actor sealerHolder unsealerHolder ·` are equal. Rather than re-derive this
field-by-field, we route through the PROVEN executor⟺spec corner `createSealPair_iff_spec`: each
`CreateSealPairSpec` reconstructs the SAME committed value `execFullA st (.createSealPairA …) = some ·`, and
`some` is injective. This is exactly the sense in which `CreateSealPairSpec` is functional — it determines
the post-state — so the circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem createSealPairSpec_unique {st st₁ st₂ : RecChainedState} {pid : Nat}
    {actor sealerHolder unsealerHolder : CellId}
    (h₁ : CreateSealPairSpec st pid actor sealerHolder unsealerHolder st₁)
    (h₂ : CreateSealPairSpec st pid actor sealerHolder unsealerHolder st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.createSealPairA pid actor sealerHolder unsealerHolder) = some st₁ :=
    (createSealPair_iff_spec st pid actor sealerHolder unsealerHolder st₁).mpr h₁
  have e₂ : execFullA st (.createSealPairA pid actor sealerHolder unsealerHolder) = some st₂ :=
    (createSealPair_iff_spec st pid actor sealerHolder unsealerHolder st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`createSealPair_compile_sound` — the welded soundness (create-seal-pair slice), against its OWN
Surface2 descriptor.**

Suppose, for the Argus create-seal-pair term `createSealPairStmt pid actor sealerHolder unsealerHolder`:
  * the Surface2 circuit `createSealPairCircuit S D hD st ⟨pid, actor, sealerHolder, unsealerHolder⟩ st'`
    (= `createSealPairE`'s full-state v2 arithmetization satisfied on the encoded triple) holds, under the
    realizable whole-`caps`-function digest portals (`hRest : RestIffNoCaps S.RH`,
    `hLog : logHashInjective S.LH`, `hD : Function.Injective D`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel:
    `interp (createSealPairStmt …) st.kernel = some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := createSealPairReceipt actor sealerHolder :: st.log }`. I.e.
create-seal-pair's OWN circuit and the IR term AGREE on the WHOLE 17-field RecordKernelState (`caps` set to
the double grant `createSealPairCaps`, every other field frozen — including `sealedBoxes`, untouched) AND the
receipt log — the full `CreateSealPairSpec`, not a per-cell projection. So the circuit the prover runs for
create-seal-pair pins the complete state the IR term's executor produces. (NO nonce-tick divergence at this
Surface2 universe-A layer — `CreateSealPairSpec` has no per-cell nonce; the post-state is pinned exactly.
The IR `hexec` premise is now the R3-gated commit — so the agreed post-state is the AUTHORITATIVE executor's,
and the `pidFresh` precondition is enforced in-circuit by the term's `guard`, witnessed by the §6 anti-gate
tooth.) -/
theorem createSealPair_compile_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (pid : Nat) (actor sealerHolder unsealerHolder : CellId)
    (k' : RecordKernelState)
    (hcirc : createSealPairCircuit S D hD st ⟨pid, actor, sealerHolder, unsealerHolder⟩ st')
    (hexec : interp (createSealPairStmt pid actor sealerHolder unsealerHolder) st.kernel = some k') :
    st' = { kernel := k', log := createSealPairReceipt actor sealerHolder :: st.log } := by
  -- circuit side: create-seal-pair's OWN audited soundness forces the FULL `CreateSealPairSpec` on the triple.
  have hspec : CreateSealPairSpec st pid actor sealerHolder unsealerHolder st' :=
    createSealPairA_full_sound S D hD hRest hLog st ⟨pid, actor, sealerHolder, unsealerHolder⟩ st' hcirc
  -- executor side: the §3 chained lift gives `execFullA st (.createSealPairA …) = some ⟨k', receipt :: log⟩`,
  -- and the independent executor⟺spec corner turns THAT into `CreateSealPairSpec st … ⟨k', receipt :: log⟩`.
  have hspec' : CreateSealPairSpec st pid actor sealerHolder unsealerHolder
      { kernel := k', log := createSealPairReceipt actor sealerHolder :: st.log } :=
    (createSealPair_iff_spec st pid actor sealerHolder unsealerHolder _).mp
      (interp_createSealPairStmt_chained st pid actor sealerHolder unsealerHolder k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + the log).
  exact createSealPairSpec_unique hspec hspec'

#assert_axioms createSealPair_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely INSTALLS the keypair (observable double cap-graph write), the
two granted caps are GENUINELY DISTINCT, it genuinely REJECTS an unauthorized writer (fail-closed), and the
welded descriptor is the genuine Surface2 full-state one (full `caps`-function equality), not a placeholder.

The cornerstone/weld would be hollow if create-seal-pair never committed, if the grant were a no-op, or if
the gate admitted everything. A concrete kernel `kSP0` (cell `0` Live, HOLDING a `node 1` cap so it has
authority over `sealerHolder := 0`) exercises a real keypair install; the rejection lemma shows the
authority gate fails closed. -/

/-- A concrete kernel for the witnesses: cells 0,1,2 are live accounts; cell `0` HOLDS a `node 0` cap (so
`stateAuthB caps 0 0` holds — `0` has authority over itself as `sealerHolder`). The unsealer holder (cell
`2`) holds nothing, so the keypair install is OBSERVABLE on its slot. -/
def kSP0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 0] else [] }

/-- **NON-VACUITY (the unsealer keypair leg is OBSERVABLE — the cap INSTALLS).** Running the create-seal-pair
term on `kSP0` (writer `0` authorized over `sealerHolder 0`, unsealer holder `2` holds nothing) commits, and
the unsealer holder cell `2`'s cap-slot GAINS the unsealer cap `unsealerCap 7` (`[]` → `[unsealerCap 7]`):
the `setCaps` double-grant write is a real, observable cap-graph mutation, not a no-op. -/
theorem createSealPairStmt_installs_unsealer :
    (interp (createSealPairStmt 7 0 0 2) kSP0).map (fun k => k.caps 2)
      = some [unsealerCap 7] := by
  rw [interp_createSealPairStmt_eq_createSealPairStep]
  decide

/-- **NON-VACUITY (the unsealer holder was empty before).** Cell `2` held NO caps before the create — so the
unsealer install above is a genuine state change, not a pre-existing cap. -/
theorem createSealPairStmt_unsealer_empty_before : kSP0.caps 2 = [] := by decide

/-- **NON-VACUITY (the sealer leg is OBSERVABLE too — and the keypair is GENUINELY DISTINCT).** The committed
create installs a sealer cap conferring the seal authority for `pid` into `sealerHolder` and an unsealer cap
conferring the unseal authority for `pid` into `unsealerHolder`, and the two are GENUINELY DISTINCT (`[grant]`
vs `[reply]` rights — a real keypair, not one cap twice). Read off `createSealPairCaps_correct` against the
committed step the cornerstone refines to. A flag-flip could NEVER witness this. -/
theorem createSealPairStmt_grants_distinct_keypair (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) (k k' : RecordKernelState)
    (hne : sealerHolder ≠ unsealerHolder)
    (h : interp (createSealPairStmt pid actor sealerHolder unsealerHolder) k = some k') :
    sealerCap pid ∈ k'.caps sealerHolder
    ∧ unsealerCap pid ∈ k'.caps unsealerHolder
    ∧ holdsSealCapFor pid (sealerCap pid) = true
    ∧ holdsSealCapFor pid (unsealerCap pid) = true
    ∧ sealerCap pid ≠ unsealerCap pid := by
  rw [interp_createSealPairStmt_eq_createSealPairStep] at h
  -- the committed R3 step installs `k'.caps = createSealPairCaps k.caps pid sealerHolder unsealerHolder`.
  have hcaps : k'.caps = createSealPairCaps k.caps pid sealerHolder unsealerHolder := by
    unfold createSealPairStep csArgs createSealPairCaps at h
    by_cases hg : stateAuthB k.caps actor sealerHolder = true ∧ pidFresh k pid = true
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
      simp [createSealPairCaps]
    · rw [if_neg hg] at h; exact absurd h (by simp)
  obtain ⟨hms, hmu, hhs, hhu, hdne, _⟩ :=
    createSealPairCaps_correct k.caps pid sealerHolder unsealerHolder hne
  exact ⟨by rw [hcaps]; exact hms, by rw [hcaps]; exact hmu, hhs, hhu, hdne⟩

/-- **NON-VACUITY (fail-closed: unauthorized writer).** A create-seal-pair whose `actor` holds NO authority
over `sealerHolder` does NOT commit: from the empty cell `1` (which holds no `node`/`control` cap over `2`)
writing the pair to `sealerHolder 2` returns `none` — the `stateAuthB` conjunct fails closed; no keypair is
conjured. -/
theorem createSealPairStmt_rejects_unauthorized :
    interp (createSealPairStmt 7 1 2 0) kSP0 = none := by
  rw [interp_createSealPairStmt_eq_createSealPairStep]
  decide

#assert_axioms createSealPairStmt_installs_unsealer
#assert_axioms createSealPairStmt_unsealer_empty_before
#assert_axioms createSealPairStmt_grants_distinct_keypair
#assert_axioms createSealPairStmt_rejects_unauthorized

/-! ## §6 — THE R3 ANTI-GATE TOOTH: the strengthened (in-circuit) `pidFresh` conjunct REJECTS a reused pid.

A PRIOR version of this module gated the IR term ONLY on `stateAuthB` and CARRIED — as a "witnessed
divergence" — the fact that the term still COMMITTED on a STALE (already-bound) pid the R3 handler would
reject. That was the completeness gap (§header): a light client checking that weaker descriptor would have
ACCEPTED a pid-reuse create, enabling the documented R3 attack (because `findSealedBox` returns the FIRST
match, a stale unsealer-cap holder opens the NEW pair's box). The fix put `pidFresh` into the runnable
term's `guard`, where `compile` emits it as a circuit constraint. These teeth PROVE the gap is CLOSED: the
strengthened term REJECTS — `interp … = none`, UNSAT — exactly the reused-pid input, while a FRESH pid on
the SAME state still commits (so the freshness conjunct genuinely DISCRIMINATES, it is not everything-reject).

The cornerstone (§2) already establishes the descriptor refines the AUTHORITATIVE `createSealPairStep` (the
`execHandlerTurn` cutover step, validated by `createSealPair_triangle`) — so this is not merely "matches a
stricter side-lemma"; it is the same admissibility set the running executor enforces. -/

/-- A kernel whose `sealedBoxes` ALREADY binds pid `7` (a box keyed under it), with cell `0` authorized over
itself (holds `node 0`) AND pid `9` FRESH. The R3 attack input: a create reusing pid `7` here would (under
the old weaker gate) let a stale unsealer open the new pair's box. The strengthened term REJECTS it. -/
def kSPstale : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 0] else []
    sealedBoxes := [{ pairId := 7, sealer := 0, payload := Cap.node 0 }] }

/-- **`pidFresh` discriminates on `kSPstale`.** pid `7` is STALE (a box binds it) ⇒ `pidFresh = false`;
pid `9` is FRESH ⇒ `pidFresh = true`. So the conjunct the gate adds is a genuine, non-trivial state read. -/
theorem kSPstale_pid7_stale : pidFresh kSPstale 7 = false := by decide
theorem kSPstale_pid9_fresh : pidFresh kSPstale 9 = true := by decide

/-- **`createSealPairStmt_rejects_reused_pid` — THE R3 ANTI-GATE TOOTH (PROVED).** On `kSPstale` (pid `7`
ALREADY binds a sealed box), the strengthened IR term's executor REJECTS the reused pid: `interp … = none`,
NO state produced. This is the in-circuit closure of the R3 no-pid-reuse discipline — `compile` emits the
term's `guard` as a constraint, so a light client's proof is UNSAT on this exact pid-reuse witness. The
authority conjunct holds here (cell `0` is authorized over itself), so it is the `pidFresh` conjunct ALONE
that bites — exactly the gap a prior version left open. -/
theorem createSealPairStmt_rejects_reused_pid :
    interp (createSealPairStmt 7 0 0 1) kSPstale = none := by
  rw [interp_createSealPairStmt_eq_createSealPairStep]
  decide

/-- **`createSealPairStmt_admits_fresh_pid` — the freshness gate is NOT everything-reject.** On the SAME
stale-box state `kSPstale`, a create under the FRESH pid `9` (cell `0` authorized over itself) COMMITS —
the `pidFresh` conjunct discriminates, it does not blanket-reject. (Non-vacuity of the R3 gate: it rejects
EXACTLY the reused pids, not all creates.) -/
theorem createSealPairStmt_admits_fresh_pid :
    (interp (createSealPairStmt 9 0 0 1) kSPstale).isSome = true := by
  rw [interp_createSealPairStmt_eq_createSealPairStep]
  decide

/-- **`createSealPairStmt_refines_R3_executor` — the descriptor IS the authoritative step.** The IR term's
`interp` is DEFINITIONALLY (by the §2 cornerstone) the R3-closing `createSealPairStep` — the create-seal-pair
arm of the `execHandlerTurn` cutover executor, validated by `createSealPair_triangle`. So the in-circuit
gate of the runnable descriptor enforces the SAME admissibility (`stateAuthB ∧ pidFresh`) as the running
executor: the completeness criterion holds (every executor precondition is an in-circuit conjunct). -/
theorem createSealPairStmt_refines_R3_executor (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) (k : RecordKernelState) :
    interp (createSealPairStmt pid actor sealerHolder unsealerHolder) k
      = createSealPairStep k (csArgs pid actor sealerHolder unsealerHolder) :=
  interp_createSealPairStmt_eq_createSealPairStep pid actor sealerHolder unsealerHolder k

#assert_axioms kSPstale_pid7_stale
#assert_axioms kSPstale_pid9_fresh
#assert_axioms createSealPairStmt_rejects_reused_pid
#assert_axioms createSealPairStmt_admits_fresh_pid
#assert_axioms createSealPairStmt_refines_R3_executor

end Dregg2.Circuit.Argus.Effects.CreateSealPair
