/-
# Dregg2.Circuit.Argus.Policy — the Argus POLICY-ENFORCEMENT layer: a cell's INSTALLED program
gates the effect, AND Bucket-B's `witnessed` arm gets a REAL circuit gate.

The per-effect Argus welds (`Argus/Stmt.lean §M`, `Argus/Compile.lean`) enforce each effect's
STATE TRANSITION (transfer/mint/burn's commit IS the verified executor / the audited
descriptor). What they do NOT yet enforce is the *target cell's INSTALLED policy*: dregg's rich
installed-policy machinery is UNDER-ENFORCED —

  1. the `StateConstraint` catalog (`Exec/Program.lean`, ~19 variants —
     `sumEquals`/`memberOf`/`immutable`/`inRangeTwoSided`/`boundDelta`/…) is `evalConstraint`-checked
     on the LIVE leg, but `turn/src/executor/mod.rs:~305-337` **silently IGNORES** it in the running
     circuit ("Bucket B" — declared, enforced nowhere on the circuit path);
  2. the SGM/CWM mandate predicates "live offline, the executor never calls";
  3. macaroon caveats.

The unifying mechanism ALREADY EXISTS in `Argus/Guard.lean`: `guardG` (lifts a `Spec.Guard` into the
cornerstone's `RecStmt.guard`), the **domain-restriction keystone** `interp_guardSeq_*` (a guard only
RESTRICTS, never mutates — so every executor keystone of the gated effect lifts through it for free),
`constraintToGuard` (routes a `StateConstraint` onto the unified `Guard`), and `programToGuard` /
`programGuardStmt` (a whole `List StateConstraint` → one `Guard.all`-conjoined gate term). This file
makes the installed policy **ENFORCED AS THE OPERATION**, and gives the first Bucket-B `witnessed` arm
a **genuine circuit gate** (the reference).

## What this file proves

* **`policyGuarded prog s`** (§1) — gate the effect term `s` by the target cell's installed program
  `prog : List StateConstraint`: prepend `programGuardStmt` so `s` commits ONLY IF the installed
  StateConstraints admit the `(old,new)` transition. It REUSES `Guard.lean`'s `programGuardStmt` (hence
  `programToGuard` / the domain-restriction keystone) — it does NOT reinvent the gate.

* **The ENFORCEMENT keystone** (§2) — `interp (policyGuarded prog s) k = some k'` IFF the installed
  program ADMITS *and* `interp s k = some k'`, and the committed state is EXACTLY `interp s`'s (the
  policy only RESTRICTS, never mutates — so every effect keystone lifts). This is the proof that the
  installed assertions/caveats are now ENFORCED INLINE (the SGM/CWM-never-called gap closed). MEANINGFUL
  + non-vacuous: §3 exhibits a `memberOf` allowlist and an `immutable` anchor that a real installed
  constraint REJECTS one transition and ADMITS another, and shows the gated effect is rejected/admitted
  accordingly.

* **THE BUCKET-B CIRCUIT REFERENCE** (§4) — `sumEquals fields value` (a post-state field sum equals a
  constant) is, today, evaluated in Lean (`evalConstraint`) but carries **NO circuit teeth**. We build
  a real CIRCUIT GATE for it: an `EmittedExpr` arithmetic constraint over the layout columns
  (`Σ new[fᵢ]-columns − value`, a single PLONK linear gate) whose `VmGate.holds` denotation is the
  prover's `assert_zero`. We prove `sumGate_holds ⟺ sumEquals` (real teeth, BOTH directions) + an
  ANTI-GHOST (a sum ≠ value ⇒ the gate is UNSAT), and DISCHARGE the `witnessed` obligation
  `constraintToGuard`-style routing names with a concrete circuit-backed `Verifiable` instance — so the
  Bucket-B `witnessed` arm has GENUINE circuit teeth, not an empty oracle placeholder.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). Imports are READ-ONLY; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Guard
import Dregg2.Circuit.Emit.EffectVmEmit

namespace Dregg2.Circuit.Argus

open Dregg2.Exec
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Spec (Guard)
open Dregg2.Laws (Verifiable Discharged)
open Dregg2.Circuit.Emit.EffectVmEmit (VmGate VmRowEnv)

/-- `VmGate.holds` is DECIDABLE: it unfolds to the `Int` equation `g.body.eval env.loc = 0`. This lets
the circuit-backed verify seam (§4.3) compute the gate verdict and the `#guard`/anti-ghost `decide` it —
the gate is a real, checkable arithmetic constraint, not an opaque `Prop`. -/
instance instDecidableHolds (g : VmGate) (env : VmRowEnv) : Decidable (g.holds env) :=
  inferInstanceAs (Decidable (g.body.eval env.loc = 0))

/-! ## §1 — `policyGuarded`: the INSTALLED policy enforced AS THE OPERATION.

The executor side of closing the gap. A cell carries an installed program `prog : List StateConstraint`
(its `RecordProgram.predicate`). `policyGuarded prog s` gates the effect term `s` by that program: it
prepends the Bucket-B program guard `programGuardStmt` (`Guard.lean §4.2`), so running `s` first checks
that EVERY installed constraint admits the `(old, new)` slot transition (local constraints EVALUATE via
`evalConstraint`; circuit-discharged constraints route to the verify seam), and only then runs `s`.

This is NOT a new gate: it is exactly `Guard.lean`'s `programGuardStmt view prog w s`, which is
`RecStmt.seq (guardG (programToGuard view prog) w) s` — the `programToGuard` meet of each constraint's
`constraintToGuard`, lifted into the cornerstone `RecStmt.guard` and sequenced before `s`. The
`view : RecordKernelState → Value × Value` is the slot `(old, new)` view the live `setFieldA` leg
computes; the witness supply `w` discharges the circuit-routed arms. -/

/-- **`policyGuarded view prog w s`** — gate the effect term `s` by the target cell's INSTALLED program
`prog`. Definitionally `Guard.lean`'s `programGuardStmt`: prepend the routed program guard, so `s`
commits ONLY IF every installed `StateConstraint` admits the transition (the SGM/CWM/macaroon checks the
running circuit historically dropped, now enforced inline). REUSES `programToGuard` / the
domain-restriction keystone — no reinvention. -/
def policyGuarded [Verifiable ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (prog : List StateConstraint)
    (w : ObligationStmt → Witness) (s : RecStmt) : RecStmt :=
  programGuardStmt view prog w s

/-- **`policyGuarded_eq_seq` (the shape).** `policyGuarded` is exactly a guarded `seq`: the
routed program guard `guardG (programToGuard view prog) w` sequenced before the effect `s`. This is
the structural fact every keystone below reads off — and it is `programGuardStmt`'s definition, so the
§4.2 Guard.lean theorems apply verbatim. -/
theorem policyGuarded_eq_seq [Verifiable ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (prog : List StateConstraint)
    (w : ObligationStmt → Witness) (s : RecStmt) :
    policyGuarded view prog w s
      = RecStmt.seq (guardG (programToGuard view prog) w) s := rfl

/-! ## §2 — THE ENFORCEMENT KEYSTONE: `interp (policyGuarded prog s)` commits IFF the program admits
AND `interp s` commits, with the committed state EXACTLY `interp s`'s.

This is the proof that the installed policy is ENFORCED INLINE. The policy is a pure domain restrictor
(`Guard.lean`'s keystone): it adds an admission side-condition and mutates NOTHING, so

  * a violated installed constraint REJECTS the WHOLE effect (`policyGuarded_reject`, FAIL-CLOSED) —
    the teeth that close the SGM/CWM-never-called / Bucket-B-silently-ignored gap;
  * a committed gated effect produces EXACTLY the underlying effect's post-state
    (`policyGuarded_commit_eq_underlying`) — so EVERY executor keystone of `s` (conservation, authority,
    frame, the per-effect Argus weld) lifts through the WHOLE installed program for free;
  * a committed gated effect means EVERY installed constraint admitted (`policyGuarded_admits_all`).

Together they are the IFF (`policyGuarded_commit_iff`). -/

/-- **`policyGuarded_commit_iff` (THE ENFORCEMENT KEYSTONE).** The installed-policy-gated
effect commits to `k'` IFF the routed installed program ADMITS the transition AND the underlying effect
`interp s` commits to that very same `k'`. The policy only restricts the domain — the committed state
is `interp s`'s, never anything the policy cooked up. This IS "the installed assertions are enforced
inline": no effect commits unless the cell's installed program admits it. -/
theorem policyGuarded_commit_iff [Verifiable ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (prog : List StateConstraint)
    (w : ObligationStmt → Witness) (s : RecStmt) (k k' : RecordKernelState) :
    interp (policyGuarded view prog w s) k = some k'
      ↔ ((programToGuard view prog).admits k w = true ∧ interp s k = some k') := by
  rw [policyGuarded_eq_seq]
  exact interp_guardSeq_iff (programToGuard view prog) w s k k'

/-- **`policyGuarded_commit_eq_underlying` (the policy NEVER MUTATES).** A committed
policy-gated effect produces EXACTLY the post-state the underlying effect `interp s` produces on the
same input. The installed program is a pure domain restrictor — it can only ever PREVENT the effect,
never alter its result. This is what lifts every executor / Argus-weld keystone of `s` through the
WHOLE installed program with no per-policy reproof. -/
theorem policyGuarded_commit_eq_underlying [Verifiable ObligationStmt Witness]
    {view : RecordKernelState → Value × Value} {prog : List StateConstraint}
    {w : ObligationStmt → Witness} {s : RecStmt} {k k' : RecordKernelState}
    (h : interp (policyGuarded view prog w s) k = some k') :
    interp s k = some k' :=
  programGuardStmt_commit_eq_underlying h

/-- **`policyGuarded_admits_all`.** A committed policy-gated effect means EVERY installed
constraint ADMITTED the transition (the meet semantics of the routed program guard): each local
constraint evaluated true, each circuit-routed obligation was discharged. The witness that the WHOLE
installed program was enforced, not just consulted. -/
theorem policyGuarded_admits_all [Verifiable ObligationStmt Witness]
    {view : RecordKernelState → Value × Value} {prog : List StateConstraint}
    {w : ObligationStmt → Witness} {s : RecStmt} {k k' : RecordKernelState}
    (h : interp (policyGuarded view prog w s) k = some k') :
    ∀ c ∈ prog, (constraintToGuard view c).admits k w = true :=
  programGuardStmt_admits_all h

/-- **`policyGuarded_reject` (FAIL-CLOSED, the teeth).** If the installed program REJECTS the
transition (`(programToGuard view prog).admits k w = false`), the policy-gated effect does NOT commit —
regardless of what the underlying effect `interp s` would do. This is the executor-level enforcement:
a violated installed assertion/caveat rejects the WHOLE effect, BY THE EXECUTOR. The closing of the
"declared, enforced nowhere" gap, as a theorem. -/
theorem policyGuarded_reject [Verifiable ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (prog : List StateConstraint)
    (w : ObligationStmt → Witness) (s : RecStmt) (k : RecordKernelState)
    (h : (programToGuard view prog).admits k w = false) :
    interp (policyGuarded view prog w s) k = none := by
  rw [policyGuarded_eq_seq]
  exact interp_guardSeq_reject (programToGuard view prog) w s k h

/-- **`programToGuard_singleton_admits`.** A single-constraint installed program's
`programToGuard` admits IFF that one constraint's `constraintToGuard` admits (the `Guard.all` of a
singleton is its sole conjunct). The reduction the §3 non-vacuity reads off, so the routed installed
program's verdict is exactly the constraint's. -/
theorem programToGuard_singleton_admits [Verifiable ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (c : StateConstraint)
    (k : RecordKernelState) (w : ObligationStmt → Witness) :
    (programToGuard view [c]).admits k w = (constraintToGuard view c).admits k w := by
  simp only [programToGuard, List.map_cons, List.map_nil, Guard.admits_all_eq,
    Guard.admitsAll_cons, Guard.admitsAll_nil, Bool.and_true]

/-! ### §2.1 — the keystone PAYS OFF: a verified transfer, gated by an installed program, still
conserves and is still authorized — inherited THROUGH the enforcement keystone, not re-proved.

`interp s := interp (transferStmt turn)` (= `recKExec`, the cornerstone). Wrap it in ANY installed
program; conservation AND authority STILL hold of the gated commit, read off the keystone. This is the
"every effect keystone lifts through the installed policy for free" claim made real. -/

/-- **`policyGuarded_transfer_conserves`.** A policy-gated transfer that commits PRESERVES the
total balance — `recKExec_conserves` lifted through the enforcement keystone. The installed program
added an admission side-condition and changed NOTHING about the committed state. -/
theorem policyGuarded_transfer_conserves [Verifiable ObligationStmt Witness]
    {view : RecordKernelState → Value × Value} {prog : List StateConstraint}
    {w : ObligationStmt → Witness} {turn : Turn} {k k' : RecordKernelState}
    (h : interp (policyGuarded view prog w (transferStmt turn)) k = some k') :
    recTotal k' = recTotal k := by
  have hs : interp (transferStmt turn) k = some k' := policyGuarded_commit_eq_underlying h
  rw [interp_transferStmt_eq_recKExec] at hs
  exact recKExec_conserves k k' turn hs

/-- **`policyGuarded_transfer_authorized`.** A policy-gated transfer that commits was
AUTHORIZED — `recKExec_authorized` lifted through the same keystone. Two independent executor keystones
(conservation, authority) lifting through ONE installed program with no per-policy reproof. -/
theorem policyGuarded_transfer_authorized [Verifiable ObligationStmt Witness]
    {view : RecordKernelState → Value × Value} {prog : List StateConstraint}
    {w : ObligationStmt → Witness} {turn : Turn} {k k' : RecordKernelState}
    (h : interp (policyGuarded view prog w (transferStmt turn)) k = some k') :
    authorizedB k.caps turn = true := by
  have hs : interp (transferStmt turn) k = some k' := policyGuarded_commit_eq_underlying h
  rw [interp_transferStmt_eq_recKExec] at hs
  exact recKExec_authorized k k' turn hs

/-! ## §3 — NON-VACUITY: the installed policy GENUINELY gates the operation.

We exhibit two REAL installed constraints from the catalog — a `memberOf` allowlist and an `immutable`
anchor — each of which a real cell would install, and show the policy-gated effect is REJECTED on a
violating transition and ADMITTED on a valid one. This is what makes the enforcement MEANINGFUL: the
policy is two-valued and the gate fires.

The `view` reads cell `0`'s record as the `(old, new)` slot view (`old` from the pre-state cell, `new`
from the proposed post-state cell). For these constraints we use the absolute / immutable views below.
The effect we gate is the verified `transferStmt` on a self-authorized move (so the underlying effect
commits — the gate is the ONLY thing that can reject). -/

/-- The trivial obligation-seam verify instance (the §3 examples route only LOCAL constraints, which
ignore the witness; the circuit-discharged arm is exercised by §4's real gate). Always accepts —
MINIMAL, only to carry the `Verifiable ObligationStmt Unit` class constraint; the genuine discharge is
§4's `sumGate`-backed instance, never this stub. -/
instance : Verifiable ObligationStmt Unit where
  Verify := fun _ _ => true

/-- A slot view reading cell `0`'s record as both `old` and `new` (the absolute-constraint view —
`memberOf`/`sumEquals` are absolute on `new`; `old` is the SAME record, so `immutable` sees `old=new`
i.e. "unchanged", admitting). Concrete, computable. -/
def cell0AbsView (k : RecordKernelState) : Value × Value := (k.cell 0, k.cell 0)

/-- A two-account kernel: `0 → 1`, account `0` holds 100, cell `0` carries `role = 2` (in the allowlist
{1,2,3}). The transfer `0 → 1` commits; `role` is in-allowlist. -/
def kRoleLive : RecordKernelState :=
  { accounts := {0, 1},
    cell := fun c => if c = 0 then .record [("role", .int 2), ("balance", .int 100)]
                     else .record [("balance", .int 0)],
    caps := fun _ => [] }

/-- The SAME kernel but cell `0` carries `role = 9` (NOT in {1,2,3}) — a violator of the installed
`memberOf` allowlist. -/
def kRoleBadLive : RecordKernelState :=
  { accounts := {0, 1},
    cell := fun c => if c = 0 then .record [("role", .int 9), ("balance", .int 100)]
                     else .record [("balance", .int 0)],
    caps := fun _ => [] }

/-- A self-authorized transfer of 30 from `0` to `1`. -/
def tRole : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

/-- The installed program: cell `0` admits only `role ∈ {1,2,3}` (a `memberOf` mandate). A single
real constraint from the catalog. -/
def rolePolicyProg : List StateConstraint := [.simple (.memberOf "role" [1, 2, 3])]

-- The installed `memberOf` policy gates the transfer:
-- ADMIT — role 2 ∈ allowlist ⇒ the program admits ⇒ the gated transfer commits.
#guard ((programToGuard cell0AbsView rolePolicyProg).admits kRoleLive (fun _ => ()))            -- true
#guard ((interp (policyGuarded cell0AbsView rolePolicyProg (fun _ => ()) (transferStmt tRole)) kRoleLive).isSome)  -- commits
-- REJECT — role 9 ∉ allowlist ⇒ the program rejects ⇒ the gated transfer fails closed,
-- EVEN THOUGH the bare transfer would commit (the gate is the only thing rejecting).
#guard ((programToGuard cell0AbsView rolePolicyProg).admits kRoleBadLive (fun _ => ())) == false -- false
#guard ((interp (policyGuarded cell0AbsView rolePolicyProg (fun _ => ()) (transferStmt tRole)) kRoleBadLive).isNone)  -- gated out
#guard ((interp (transferStmt tRole) kRoleBadLive).isSome)                                      -- bare transfer WOULD commit

/-- **`policyGuarded_memberOf_nonvacuous`.** The installed `memberOf` program ADMITS the
satisfier `kRoleLive` (role ∈ allowlist) and REJECTS the violator `kRoleBadLive` (role ∉ allowlist) —
two-valued, evaluating `evalConstraint`. The installed policy has real teeth (not `:= True`),
so the enforcement keystone is MEANINGFUL. -/
theorem policyGuarded_memberOf_nonvacuous :
    (programToGuard cell0AbsView rolePolicyProg).admits kRoleLive (fun _ => ()) = true ∧
      (programToGuard cell0AbsView rolePolicyProg).admits kRoleBadLive (fun _ => ()) = false := by
  refine ⟨?_, ?_⟩
  · rw [rolePolicyProg, programToGuard_singleton_admits,
        constraintToGuard_firstParty_eval cell0AbsView _ (by decide)]; decide
  · rw [rolePolicyProg, programToGuard_singleton_admits,
        constraintToGuard_firstParty_eval cell0AbsView _ (by decide)]; decide

/-- **`policyGuarded_memberOf_gates_transfer` (the gate ∘ effect, end-to-end).** On the
violator `kRoleBadLive`, the installed-`memberOf`-gated transfer FAILS CLOSED (`= none`) even though
the underlying transfer would commit — the installed policy rejected the WHOLE effect. On the satisfier
`kRoleLive`, the gated transfer commits to EXACTLY the bare transfer's state. This exhibits the
enforcement keystone LIVE: the installed assertion gates the operation. -/
theorem policyGuarded_memberOf_gates_transfer :
    interp (policyGuarded cell0AbsView rolePolicyProg (fun _ => ()) (transferStmt tRole)) kRoleBadLive
        = none
    ∧ interp (policyGuarded cell0AbsView rolePolicyProg (fun _ => ()) (transferStmt tRole)) kRoleLive
        = interp (transferStmt tRole) kRoleLive := by
  refine ⟨?_, ?_⟩
  · -- REJECT: the installed program rejects ⇒ the whole effect fails closed.
    apply policyGuarded_reject
    exact (policyGuarded_memberOf_nonvacuous).2
  · -- ADMIT: the program admits ⇒ the gated effect commits to EXACTLY the bare transfer's state.
    rw [policyGuarded_eq_seq, interp_guardSeq, if_pos (policyGuarded_memberOf_nonvacuous).1]

/-! ### §3.1 — a SECOND real installed constraint: `immutable` (a read-only anchor).

`immutable f` admits a transition iff `new[f] = old[f]` (after init). A cell that installs
`immutable "owner"` forbids any effect that would CHANGE `owner`. We show the policy rejects an
owner-changing transition and admits an owner-preserving one — a second, structurally-different
catalog atom gating the operation (so the non-vacuity is not memberOf-special). -/

/-- A `view` that exhibits an owner CHANGE: `old[owner] = 5`, `new[owner] = 7` (a violation of an
installed `immutable "owner"` anchor). Concrete, computable — the `(old, new)` an owner-rewriting
effect would present. -/
def ownerChangeView (_k : RecordKernelState) : Value × Value :=
  (.record [("owner", .int 5)], .record [("owner", .int 7)])

/-- A `view` that PRESERVES the owner: `old[owner] = 5`, `new[owner] = 5` (admitted by `immutable`). -/
def ownerKeepView (_k : RecordKernelState) : Value × Value :=
  (.record [("owner", .int 5)], .record [("owner", .int 5)])

/-- The installed program: cell forbids changing `owner` (an `immutable` anchor). -/
def ownerPolicyProg : List StateConstraint := [.simple (.immutable "owner")]

-- The installed `immutable` policy gates: REJECTS the owner change, ADMITS the keep.
#guard ((programToGuard ownerChangeView ownerPolicyProg).admits kRoleLive (fun _ => ())) == false -- false (5 ≠ 7)
#guard ((programToGuard ownerKeepView   ownerPolicyProg).admits kRoleLive (fun _ => ()))           -- true  (5 = 5)

/-- **`policyGuarded_immutable_nonvacuous`.** The installed `immutable "owner"` program
REJECTS the owner-CHANGING transition (`old=5 ≠ new=7`) and ADMITS the owner-PRESERVING one
(`old=5 = new=5`) — a second real catalog atom two-valued, gating the operation. The
enforcement is meaningful across structurally-distinct installed constraints, not just `memberOf`. -/
theorem policyGuarded_immutable_nonvacuous :
    (programToGuard ownerChangeView ownerPolicyProg).admits kRoleLive (fun _ => ()) = false ∧
      (programToGuard ownerKeepView ownerPolicyProg).admits kRoleLive (fun _ => ()) = true := by
  refine ⟨?_, ?_⟩
  · rw [ownerPolicyProg, programToGuard_singleton_admits,
        constraintToGuard_firstParty_eval ownerChangeView _ (by decide)]; decide
  · rw [ownerPolicyProg, programToGuard_singleton_admits,
        constraintToGuard_firstParty_eval ownerKeepView _ (by decide)]; decide

/-- **`policyGuarded_immutable_rejects_change`.** Gating ANY effect by the installed
`immutable "owner"` program under the owner-CHANGING view fails the whole effect closed (`= none`):
the read-only anchor is enforced by the executor. (We gate `transferStmt tRole`; the rejection is the
installed policy's, independent of the effect body.) -/
theorem policyGuarded_immutable_rejects_change :
    interp (policyGuarded ownerChangeView ownerPolicyProg (fun _ => ()) (transferStmt tRole)) kRoleLive
      = none :=
  policyGuarded_reject ownerChangeView ownerPolicyProg (fun _ => ()) (transferStmt tRole) kRoleLive
    (policyGuarded_immutable_nonvacuous).1

/-! ## §4 — THE BUCKET-B CIRCUIT REFERENCE: a REAL circuit gate for `sumEquals`.

`sumEquals fields value` ("Σ new[fields] = value", `Exec/Program.lean`) is a genuine Bucket-B
constraint: `evalConstraint` evaluates it on the LIVE leg, but the running CIRCUIT historically
dropped it (the `turn/src/executor/mod.rs` "Bucket B" silently-ignored set), so it had NO circuit
teeth. We give it teeth: a REAL `VmGate` — an `EmittedExpr` polynomial over the layout columns the
prover asserts is ZERO (`tb.assert_zero`) — that ENFORCES the sum in-circuit, and we prove
`gate holds ⟺ sumEquals` (BOTH directions, real teeth) + an ANTI-GHOST (a wrong sum is UNSAT).
This validates that Bucket B's `witnessed` arm can be discharged by a genuine circuit gate (§4.3), not
the empty oracle placeholder.

`sumEquals` is the cleanest Bucket-B reference: it is a single PLONK LINEAR gate (`Σ kᵢ·new[fᵢ] = c`
with all `kᵢ = 1`, exactly the `affineEq`/`affineLe` "Maps to a PLONK linear gate" family), so the
circuit teeth are a faithful arithmetic constraint — no hashing, no opaque AIR. (The
cross-cell `boundDelta` needs a two-row peer-state composition — a strictly harder circuit; `sumEquals`
is the right FIRST reference, and the gate generalizes to it by adding the peer columns.) -/

/-! ### §4.1 — the gate body and its pure CIRCUIT-arithmetic meaning.

`sumGateBody cols value` is the polynomial `(Σ_{c ∈ cols} var c) − value` — a sum of the layout column
variables minus the target constant. `sumGate` wraps it as a `VmGate`, whose `holds` denotation is the
prover's `assert_zero`: `body.eval loc = 0`. The pure-arithmetic characterization
(`sumGate_holds_iff_colsum`) says the gate holds IFF the column readouts sum to `value` — the genuine
circuit teeth ON THE COLUMNS, before any record bridge. The columns carry NON-ZERO coefficients (each
`var c` has coefficient `+1`), so this is a real linear constraint, not a vacuous `0 = 0`. -/

/-- The running sum polynomial `Σ_{c ∈ cols} var c`, built left-to-right (the prover's column-add
accumulator). `colSumExpr [] = const 0`; `colSumExpr (c :: cs) = var c + colSumExpr cs`. -/
def colSumExpr : List Nat → EmittedExpr
  | []      => .const 0
  | c :: cs => .add (.var c) (colSumExpr cs)

/-- **`colSumExpr_eval`.** The sum polynomial evaluates to the actual `ℤ`-sum of the column
readouts: `(colSumExpr cols).eval a = (cols.map a).sum`. The faithful arithmetic of the linear gate. -/
theorem colSumExpr_eval (cols : List Nat) (a : Dregg2.Circuit.Assignment) :
    (colSumExpr cols).eval a = (cols.map a).sum := by
  induction cols with
  | nil => simp [colSumExpr, EmittedExpr.eval]
  | cons c cs ih => simp [colSumExpr, EmittedExpr.eval, ih, List.map_cons, List.sum_cons]

/-- **`sumGateBody cols value`** — the `sumEquals` circuit-gate polynomial `(Σ_{c ∈ cols} var c) −
value`. The prover asserts this is ZERO (`tb.assert_zero`) — a single PLONK linear gate enforcing
`Σ columns = value`. -/
def sumGateBody (cols : List Nat) (value : Int) : EmittedExpr :=
  .add (colSumExpr cols) (.const (-value))

/-- **`sumGate cols value`** — the `sumEquals` constraint as a real per-row `VmGate` (the circuit teeth
the running circuit historically dropped for Bucket-B `sumEquals`). -/
def sumGate (cols : List Nat) (value : Int) : VmGate := { body := sumGateBody cols value }

/-- **`sumGate_holds_iff_colsum` (the gate's pure circuit meaning, BOTH directions).** The
`sumEquals` gate HOLDS on a row IFF the layout columns sum to `value`: `body.eval loc = 0 ↔
(cols.map loc).sum = value`. This is the genuine circuit-arithmetic teeth on the columns — a real
linear constraint (each column has coefficient `+1`), satisfied EXACTLY when the column sum hits the
target, UNSAT otherwise. -/
theorem sumGate_holds_iff_colsum (cols : List Nat) (value : Int) (env : VmRowEnv) :
    (sumGate cols value).holds env ↔ (cols.map env.loc).sum = value := by
  unfold VmGate.holds sumGate sumGateBody
  simp only [EmittedExpr.eval, colSumExpr_eval]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ### §4.2 — the BRIDGE to the `sumEquals` PREDICATE (the circuit gate ⟺ the protocol constraint).

The gate above enforces a sum over COLUMNS; the protocol constraint `sumEquals fields value` is a sum
over the post-state record's named FIELDS. A LAYOUT `lay : List (FieldName × Nat)` binds each field to
its prover column. A row ENCODES the post-state record `new` under the layout when, for every
`(f, col)` binding, the column carries the field's scalar: `env.loc col = (new.scalar f).getD …`. Under
that encoding the column sum IS the field sum, so `sumGate holds ⟺ sumEquals`. This is the
`circuit ⟺ protocol` soundness+completeness for `sumEquals`: the algebraic gate statement suffices to
enforce the constraint, and every constraint-satisfying post-state is gate-acceptable. -/

/-- The fields of a layout (the `sumEquals` field list the circuit binds). -/
def layFields (lay : List (FieldName × Nat)) : List FieldName := lay.map (·.1)

/-- The columns of a layout (the prover columns the gate sums over). -/
def layCols (lay : List (FieldName × Nat)) : List Nat := lay.map (·.2)

/-- **`sumScalars_cons`.** `sumScalars`'s right-fold step, as a clean cons-lemma: the field
sum of `f :: fs` prepends `f`'s scalar onto the rest sum (fail-closed if either is absent). The shape
the layout-induction below reads off. -/
theorem sumScalars_cons (v : Value) (f : FieldName) (fs : List FieldName) :
    sumScalars v (f :: fs)
      = (match sumScalars v fs, v.scalar f with
         | some s, some x => some (s + x)
         | _, _ => none) := rfl

/-- **`RowEncodesSum env lay new`** — the row ENCODES the post-state record `new` under the layout:
every laid-out field's scalar reads (`new.scalar f = some xᶠ`) AND its prover column carries that
scalar (`env.loc col = xᶠ`). This is the honest decoding hypothesis the §3-style `RowEncodes` of the
audited descriptors carries — it NAMES which columns hold which post-state field, the precondition for
a circuit⟺protocol bridge (the prover is responsible for laying the field scalars on the columns; the
gate then enforces the sum). Structural over the layout list. -/
def RowEncodesSum (env : VmRowEnv) : List (FieldName × Nat) → Value → Prop
  | [],            _   => True
  | (f, col) :: r, new =>
      (∃ x : Int, new.scalar f = some x ∧ env.loc col = x) ∧ RowEncodesSum env r new

/-- **`rowEncodesSum_colsum_eq_fieldsum` (the encoding aligns the sums).** Under
`RowEncodesSum`, the gate's column sum EQUALS the protocol's field sum: `(layCols lay).map (env.loc)`
sums to the same `ℤ` as `sumScalars new (layFields lay)` produces (and the field sum reads —
no field is absent, because the encoding witnessed each `new.scalar f = some xᶠ`). The bridge's
arithmetic core. -/
theorem rowEncodesSum_colsum_eq_fieldsum (env : VmRowEnv) (lay : List (FieldName × Nat)) (new : Value)
    (h : RowEncodesSum env lay new) :
    sumScalars new (layFields lay) = some ((layCols lay).map env.loc).sum := by
  induction lay with
  | nil => simp [sumScalars, layFields, layCols]
  | cons fc r ih =>
    obtain ⟨⟨x, hx, hcol⟩, hr⟩ := h
    obtain ⟨f, col⟩ := fc
    -- `layFields (f::r) = f :: layFields r`; use the clean cons-lemma for the field sum, then `ih`.
    show sumScalars new (f :: layFields r) = some ((col :: layCols r).map env.loc).sum
    rw [sumScalars_cons, ih hr]
    -- the rest sum reads as `some (rest-colsum)`; the head field is `x = env.loc col`.
    simp only [hx, List.map_cons, List.sum_cons, hcol]
    ring_nf

/-- **`sumGate_iff_sumEquals` (THE CIRCUIT ⟺ PROTOCOL BRIDGE for `sumEquals`).** Under the
honest row encoding, the `sumEquals` CIRCUIT GATE holds IFF the `sumEquals` PROTOCOL constraint holds of
the encoded post-state: `(sumGate (layCols lay) value).holds env ↔ evalConstraint (.sumEquals
(layFields lay) value) old new = true`. So the gate's algebraic statement SUFFICES to enforce
`sumEquals` (soundness) and every `sumEquals`-satisfying post-state is gate-acceptable (completeness) —
the `witnessed` obligation now has a REAL circuit discharging it, not an empty placeholder. -/
theorem sumGate_iff_sumEquals (env : VmRowEnv) (lay : List (FieldName × Nat)) (value : Int)
    (old new : Value) (henc : RowEncodesSum env lay new) :
    (sumGate (layCols lay) value).holds env
      ↔ evalConstraint (.sumEquals (layFields lay) value) old new = true := by
  rw [sumGate_holds_iff_colsum]
  -- the protocol side: `evalConstraint .sumEquals = (sumScalars new fields == some value)`.
  show ((layCols lay).map env.loc).sum = value
    ↔ (sumScalars new (layFields lay) == some value) = true
  rw [rowEncodesSum_colsum_eq_fieldsum env lay new henc]
  simp only [beq_iff_eq, Option.some.injEq]

/-! ### §4.3 — the gate DISCHARGES the `witnessed` obligation (genuine circuit teeth at the seam).

`Guard.lean`'s `constraintToGuard` routes a circuit-discharged constraint to `Guard.witnessed
(.constraint c)`, whose `admits` is `Verifiable.Verify (.constraint c) (w …)` — an ABSTRACT oracle, an
empty placeholder until a real circuit instance is supplied. We supply one for `sumEquals`: a
`Verifiable ObligationStmt SumWitness` instance whose `Verify` of `.constraint (.sumEquals fields
value)` runs the REAL `sumGate` on the witness's row+layout. Then a `witnessed`-routed `sumEquals`
guard `admits` IFF the circuit gate holds IFF (under the encoding) the `sumEquals` predicate holds — so
Bucket-B's witnessed arm has GENUINE circuit teeth (`sumEquals_witnessed_has_circuit_teeth`). -/

/-- A circuit witness for a `sumEquals` obligation: the prover's row + the field→column layout the gate
reads. (The real `Verifiable` evidence behind the seam for `sumEquals`, the §4 analog of the eight
dregg1 verifier kinds — here a genuine arithmetic gate, not an opaque oracle.) -/
structure SumWitness where
  env : VmRowEnv
  lay : List (FieldName × Nat)

/-- **The circuit-backed verifier for `sumEquals` obligations.** `Verify (.constraint (.sumEquals
fields value)) w` runs the REAL `sumGate (layCols w.lay) value` on the witness row `w.env` and accepts
iff it holds AND the witness layout's fields ARE the obligation's `fields` (so the gate is for the right
constraint). Every other obligation shape is out of this instance's scope (accepts `false` — fail-closed
for non-`sumEquals`). This is a CONCRETE circuit discharge, the opposite of the §3 always-true stub. -/
instance instVerifiableSumGate : Verifiable ObligationStmt SumWitness where
  Verify
    | .constraint (.sumEquals fields value), w =>
        decide (layFields w.lay = fields) && decide ((sumGate (layCols w.lay) value).holds w.env)
    | _, _ => false

/-- **`sumGate_discharges_obligation`.** Under the circuit-backed instance, the `sumEquals`
obligation `.constraint (.sumEquals (layFields lay) value)` is DISCHARGED (`Verify = true`) by the
witness `⟨env, lay⟩` IFF the real `sumGate` holds on the row. The verify seam carries a GENUINE circuit
verdict — not the abstract oracle. -/
theorem sumGate_discharges_obligation (env : VmRowEnv) (lay : List (FieldName × Nat)) (value : Int) :
    Verifiable.Verify (ObligationStmt.constraint (.sumEquals (layFields lay) value))
        (⟨env, lay⟩ : SumWitness) = true
      ↔ (sumGate (layCols lay) value).holds env := by
  show (decide (layFields lay = layFields lay)
          && decide ((sumGate (layCols lay) value).holds env)) = true ↔ _
  rw [decide_eq_true (rfl), Bool.true_and, decide_eq_true_iff]

/-- **`sumEquals_witnessed_has_circuit_teeth` (THE BUCKET-B `witnessed` ARM, DISCHARGED BY A
REAL CIRCUIT).** Route a `sumEquals` constraint to the `witnessed` arm (`Guard.witnessed (.constraint
(.sumEquals (layFields lay) value))`), supply the circuit witness `⟨env, lay⟩`, and — under the honest
row encoding — the guard `admits` IFF the `sumEquals` PROTOCOL constraint holds of the encoded
post-state. So the Bucket-B `witnessed` arm `constraintToGuard` names is discharged by the GENUINE
`sumGate` circuit (not the empty `Verifiable` placeholder): the circuit teeth are real, and they decide
the same transitions as the predicate. -/
theorem sumEquals_witnessed_has_circuit_teeth
    (env : VmRowEnv) (lay : List (FieldName × Nat)) (value : Int) (old new : Value)
    (req : RecordKernelState) (henc : RowEncodesSum env lay new) :
    (Guard.witnessed (.constraint (.sumEquals (layFields lay) value))
        : Guard RecordKernelState ObligationStmt).admits req (fun _ => (⟨env, lay⟩ : SumWitness)) = true
      ↔ evalConstraint (.sumEquals (layFields lay) value) old new = true := by
  -- the guard's verdict IS `Verify` of the obligation; that IS `sumGate holds` (the real circuit) …
  rw [Guard.admits_witnessed, sumGate_discharges_obligation env lay value]
  -- … and the circuit gate holds IFF the `sumEquals` predicate holds (the §4.2 bridge).
  exact sumGate_iff_sumEquals env lay value old new henc

/-! ### §4.4 — NON-VACUITY + ANTI-GHOST: the circuit gate SATISFIES the satisfier and is
UNSAT on a tampered sum.

A concrete layout `[("a", 100), ("b", 101)]`, target `value = 7`, and two rows: one whose columns carry
`3, 4` (sum 7 — the gate HOLDS, the predicate holds) and one carrying `3, 5` (sum 8 ≠ 7 — the gate is
UNSAT, the predicate fails). This is the mandatory teeth check: the gate is not a vacuous `0 = 0`; it
SATISFIES exactly the right column sums and REJECTS a tampered one. -/

/-- The demo layout: field `a`→column 100, field `b`→column 101 (two distinct non-selector columns). -/
def demoLay : List (FieldName × Nat) := [("a", 100), ("b", 101)]

/-- A row whose columns 100,101 carry `3,4` (sum 7) — the SATISFIER. Cols outside the layout are `0`. -/
def envSat : VmRowEnv :=
  { loc := fun c => if c = 100 then 3 else if c = 101 then 4 else 0,
    nxt := fun _ => 0, pub := fun _ => 0 }

/-- A row whose columns 100,101 carry `3,5` (sum 8 ≠ 7) — the TAMPERED row (anti-ghost witness). -/
def envBad : VmRowEnv :=
  { loc := fun c => if c = 100 then 3 else if c = 101 then 5 else 0,
    nxt := fun _ => 0, pub := fun _ => 0 }

-- The circuit gate SATISFIES the right sum and is UNSAT on the tampered one:
#guard (decide ((sumGate (layCols demoLay) 7).holds envSat))            -- true  (3+4=7)
#guard (decide ((sumGate (layCols demoLay) 7).holds envBad)) == false   -- false (3+5=8≠7)

/-- **`sumGate_satisfies_satisfier`.** The `sumEquals` gate (layout `demoLay`, target 7) HOLDS
on `envSat` (columns sum to `3+4 = 7`). The gate is satisfiable — non-vacuous, real teeth. -/
theorem sumGate_satisfies_satisfier : (sumGate (layCols demoLay) 7).holds envSat := by
  rw [sumGate_holds_iff_colsum]; decide

/-- **`sumGate_rejects_tamper` (THE ANTI-GHOST TOOTH).** The `sumEquals` gate is UNSAT on
`envBad` (columns sum to `3+5 = 8 ≠ 7`): `¬ (sumGate …).holds envBad`. A row whose post-state field
sum is tampered FAILS the circuit gate — the genuine circuit teeth `sumEquals` lacked. A vacuous gate
could not reject this. -/
theorem sumGate_rejects_tamper : ¬ (sumGate (layCols demoLay) 7).holds envBad := by
  rw [sumGate_holds_iff_colsum]; decide

/-- **`sumGate_demo_iff_predicate` (the bridge, witnessed concretely).** On the satisfier row
`envSat` with a record `new = {a:3, b:4}` it encodes, the gate holds IFF the `sumEquals` predicate holds
(both true); the circuit⟺protocol bridge at a concrete encoded row, non-vacuous (the predicate
reads `some 7`). -/
theorem sumGate_demo_iff_predicate :
    (sumGate (layCols demoLay) 7).holds envSat
      ↔ evalConstraint (.sumEquals (layFields demoLay) 7) (.record [])
            (.record [("a", .int 3), ("b", .int 4)]) = true := by
  apply sumGate_iff_sumEquals envSat demoLay 7 (.record []) (.record [("a", .int 3), ("b", .int 4)])
  -- the encoding: column 100 = 3 = new.scalar "a", column 101 = 4 = new.scalar "b".
  refine ⟨⟨3, ?_, ?_⟩, ⟨4, ?_, ?_⟩, trivial⟩ <;> decide

/-! ## §5 — Axiom-hygiene tripwires.

Pin every keystone: the enforcement keystone (commit-iff + never-mutates + admits-all + fail-closed),
the two executor-property lifts, the non-vacuity (memberOf + immutable gating the operation), and the
WHOLE Bucket-B circuit reference (the gate's circuit meaning, the circuit⟺protocol bridge, the witnessed
discharge, the satisfier + anti-ghost). Each ⊆ {propext, Classical.choice, Quot.sound}. -/

#assert_axioms policyGuarded_eq_seq
#assert_axioms policyGuarded_commit_iff
#assert_axioms policyGuarded_commit_eq_underlying
#assert_axioms policyGuarded_admits_all
#assert_axioms policyGuarded_reject
#assert_axioms policyGuarded_transfer_conserves
#assert_axioms policyGuarded_transfer_authorized
#assert_axioms policyGuarded_memberOf_nonvacuous
#assert_axioms policyGuarded_memberOf_gates_transfer
#assert_axioms policyGuarded_immutable_nonvacuous
#assert_axioms policyGuarded_immutable_rejects_change
#assert_axioms colSumExpr_eval
#assert_axioms sumGate_holds_iff_colsum
#assert_axioms rowEncodesSum_colsum_eq_fieldsum
#assert_axioms sumGate_iff_sumEquals
#assert_axioms sumGate_discharges_obligation
#assert_axioms sumEquals_witnessed_has_circuit_teeth
#assert_axioms sumGate_satisfies_satisfier
#assert_axioms sumGate_rejects_tamper
#assert_axioms sumGate_demo_iff_predicate

end Dregg2.Circuit.Argus
