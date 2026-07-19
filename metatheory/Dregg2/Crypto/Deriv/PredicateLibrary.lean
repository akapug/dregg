/-
# Dregg2.Crypto.Deriv.PredicateLibrary — a USABLE policy-authoring surface over `Pred`, with
# WORKED EXAMPLES wired to the decidable language-equivalence / emptiness decision.

The machinery underneath is real but abstract: `Pred` (`Exec/PredAlgebra.lean`) is the Boolean
predicate algebra; `PredRE` (`Core.lean`) lifts a `Pred` to a single-frame regex leaf (`.sym φ`);
and the two decisions

* `predRE_emptiness_decidable_fix`  (`SymbolicFixpoint.lean`) — "is this policy SATISFIABLE?"
* `predRE_equivalence_decidable_fix` (`EquivalenceFixpoint.lean`) — "are these two policies THE SAME?"

kernel-run on the RIGID symbolic fragment. This module is the ergonomic front: named combinators a
builder actually writes (`roleIs`, `statusIn`, `ownerMatch`, `noSelfTransfer`, `requireAll`/
`requireAny`, and `∧ₚ`/`∨ₚ`/`¬ₚ` sugar), a handful of policies a real user would author, and — for
each — a `#guard`/theorem CONNECTING the policy to the decision: its guard decides satisfiable or
unsatisfiable, and TWO spellings of a policy decide equivalent (the killer app).

## The fragment lattice, said out loud (so the reach of each example is legible)

A `Pred` leaf `φ` lands the guard `.sym φ` in one of three tiers, each a *computable* membership check.
The 07-19 `predBEq` widenings made rigidity (`rigidRE`) hold broadly (`symEq`/`digEq`/`symMemberOf`/
`digFieldEq` under `and`/`or`/`not`), so the discriminating axis is now PIN-REPRESENTABILITY
(`IsSymbolic` — does a computable minterm cover exist):

* **RIGID ∧ SYMBOLIC** (`rigidRE (.sym φ) = true` and `IsSymbolic (.sym φ)`): leaves over
  `tt`/`ff`/`symEq`/`digEq`/`symMemberOf` under `and`/`or`/`not`. The `≅`-fixpoint runs here — both
  SATISFIABILITY and EQUIVALENCE decide by `decide`, fast (a handful of `≅`-classes). Every
  KILLER-APP example below lives here (`roleIs`/`refIs`-based); `statusIn` is here too.
* **SYMBOLIC, bounded route**: any `IsSymbolic` guard (same leaf set) — the general BOUNDED
  satisfiability decision (`nonemptyWithinG` + `nonemptyWithinG_iff_bounded`) runs on the STABLE
  `IsSymbolic` property alone, which is how `enumGate` (`statusIn`) is connected below.
* **CROSS-FIELD, not pin-representable**: `digFieldEq`/`fieldEqField` (`ownerMatch`/`noSelfTransfer`)
  are cross-field equalities over an infinite value domain, so `predAtoms?` returns `none` — no
  minterm cover, so the guard is not `IsSymbolic` and the REGEX-level decision does not apply (a
  deeper wall than `predBEq`-rigidity, which the widening already crossed for `digFieldEq`). But
  `Pred.eval` is total, computable, decidable, so the policy still admits/rejects concrete
  transitions (the executor teeth, `predStateStepGuarded`) — these examples get `#guard` admit/reject
  pairs, and the standing wall is `#guard`-witnessed by `IsSymbolic (.sym transferAuth) = false`.

No `sorry`; every decision `#guard`/theorem is a kernel computation.
-/
import Dregg2.Crypto.Deriv.EquivalenceFixpoint

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open PredRE (derives null der RigidFull rigidRE)

namespace PredicateLibrary

/-! ## §1 The combinators — the surface a builder writes. -/

/-! ### Boolean sugar (negation/conjunction/disjunction at EVERY level — the `Pred` algebra's whole
point vs the forked 2-level grammars). Thin wrappers over the constructors, plus scoped notation. -/

/-- Conjunction of two policies. -/
def pAnd (a b : Pred) : Pred := .and a b
/-- Disjunction of two policies. -/
def pOr  (a b : Pred) : Pred := .or a b
/-- Negation of a policy (at any level). -/
def pNot (a : Pred) : Pred := .not a

@[inherit_doc] scoped infixr:35 " ∧ₚ " => pAnd
@[inherit_doc] scoped infixr:30 " ∨ₚ " => pOr
@[inherit_doc] scoped prefix:75  "¬ₚ"   => pNot

/-- **`requireAll ps`** — every policy in `ps` must hold (n-ary conjunction; vacuously admits `[]`). -/
def requireAll (ps : List Pred) : Pred := .allOf ps
/-- **`requireAny ps`** — at least one policy in `ps` must hold (n-ary disjunction; `[]` rejects,
fail-closed). -/
def requireAny (ps : List Pred) : Pred := .anyOf ps

/-! ### Named field conventions (a builder names the columns of their record once). -/

/-- **`roleIs r`** — the actor's `role` symbol is exactly `r` (typed identity equality on field
`"role"`). RIGID: `.sym (roleIs r)` runs through the fast fixpoint decision. -/
def roleIs (r : Nat) : Pred := .symEq "role" r

/-- **`statusIn ss`** — the record's `status` symbol is one of the enum cases `ss` (typed enum
membership on field `"status"`). Pin-representable (`IsSymbolic`), so the bounded satisfiability
decision runs; post-widening it is `rigidRE` too, so the fast fixpoint route is also available. -/
def statusIn (ss : List Nat) : Pred := .symMemberOf "status" ss

/-- **`refIs d`** — field `"ref"`'s digest / cell-reference is exactly `d`. RIGID (`digEq`). -/
def refIs (d : Nat) : Pred := .digEq "ref" d

/-- **`ownerMatch`** — the `sender` digest equals the `owner` digest: "only the owner may act". The
owner-match tooth; a CROSS-FIELD equality (`digFieldEq`), so not pin-representable — decided at the
`Pred.eval` (executor) level, not the regex level. -/
def ownerMatch : Pred := .digFieldEq "sender" "owner"

/-- **`noSelfTransfer`** — the `from` and `to` digests differ: "you cannot transfer to yourself".
The negation of a cross-field `digFieldEq` tooth; `Pred.eval`-decided (executor level). -/
def noSelfTransfer : Pred := ¬ₚ (.digFieldEq "from" "to")

/-! ### §1 non-vacuity — the combinators genuinely discriminate (both polarities, no `:= true`). -/

-- `roleIs` reads the `role` SYMBOL by proper type (a scalar / digest of the same word fails closed).
#guard ((roleIs 5).eval (.record []) (.record [("role", .sym 5)]))            -- true
#guard ((roleIs 5).eval (.record []) (.record [("role", .sym 6)])) == false   -- false
#guard ((roleIs 5).eval (.record []) (.record [("role", .int 5)])) == false   -- false (typed)

-- `statusIn` is enum-by-symbol; a scalar of the same word is not a member.
#guard ((statusIn [1, 2]).eval (.record []) (.record [("status", .sym 2)]))            -- true
#guard ((statusIn [1, 2]).eval (.record []) (.record [("status", .sym 3)])) == false   -- false
#guard ((statusIn [1, 2]).eval (.record []) (.record [("status", .int 1)])) == false   -- false (typed)

-- `ownerMatch` / `noSelfTransfer` admit and reject on a transfer record.
#guard (ownerMatch.eval (.record []) (.record [("sender", .dig 7), ("owner", .dig 7)]))            -- true
#guard (ownerMatch.eval (.record []) (.record [("sender", .dig 9), ("owner", .dig 7)])) == false   -- false
#guard (noSelfTransfer.eval (.record []) (.record [("from", .dig 7), ("to", .dig 9)]))             -- true
#guard (noSelfTransfer.eval (.record []) (.record [("from", .dig 7), ("to", .dig 7)])) == false    -- false

/-! ## §2 Combinator LAWS — the sugar means exactly the Boolean operation, and the n-ary forms agree
with the binary spelling. These are the ALGEBRAIC facts a builder relies on when refactoring a
policy (they hold for ANY sub-policies, rigid or not — pure `Pred.eval` reasoning). -/

/-- `∧ₚ` is `&&` on the evaluations. -/
theorem pAnd_eval (a b : Pred) (o n : Value) :
    (a ∧ₚ b).eval o n = (a.eval o n && b.eval o n) := rfl

/-- `∨ₚ` is `||`. -/
theorem pOr_eval (a b : Pred) (o n : Value) :
    (a ∨ₚ b).eval o n = (a.eval o n || b.eval o n) := rfl

/-- `¬ₚ` is Boolean complement. -/
theorem pNot_eval (a : Pred) (o n : Value) :
    (¬ₚ a).eval o n = !(a.eval o n) := rfl

/-- **`requireAll [a, b] ≡ a ∧ₚ b`** — the n-ary conjunction of a pair is the binary conjunction, at
EVERY transition. The "are these two policies the same?" question answered at the `Pred` level for a
pair of ARBITRARY sub-policies (this holds even where the regex decision does not reach). -/
theorem requireAll_pair_eq_and (a b : Pred) (o n : Value) :
    (requireAll [a, b]).eval o n = (a ∧ₚ b).eval o n := by
  simp only [requireAll, pAnd, Pred.allOf_cons, Pred.allOf_nil_admits, Pred.eval_and, Bool.and_true]

/-- **`requireAny [a, b] ≡ a ∨ₚ b`** — the n-ary disjunction of a pair is the binary disjunction. -/
theorem requireAny_pair_eq_or (a b : Pred) (o n : Value) :
    (requireAny [a, b]).eval o n = (a ∨ₚ b).eval o n := by
  simp only [requireAny, pOr, Pred.anyOf_cons, Pred.anyOf_nil_rejects, Pred.eval_or, Bool.or_false]

/-- **Disjunction commutes.** `admin ∨ active` and `active ∨ admin` are the SAME policy — the
refactor a builder makes without thinking, here a theorem over any sub-policies. -/
theorem pOr_comm (a b : Pred) (o n : Value) :
    (a ∨ₚ b).eval o n = (b ∨ₚ a).eval o n := by
  rw [pOr_eval, pOr_eval, Bool.or_comm]

/-- **Conjunction is idempotent.** `p ∧ p` is `p`. -/
theorem pAnd_idem (a : Pred) (o n : Value) :
    (a ∧ₚ a).eval o n = a.eval o n := by
  rw [pAnd_eval, Bool.and_self]

/-- **De Morgan.** `¬(a ∧ b)` and `¬a ∨ ¬b` are the SAME policy at every transition (the deny-policy
refactor). At the `Pred` level for ANY sub-policies; the RIGID instance below decides it as a
LANGUAGE equivalence too. -/
theorem deMorgan_eval (a b : Pred) (o n : Value) :
    (¬ₚ (a ∧ₚ b)).eval o n = ((¬ₚ a) ∨ₚ (¬ₚ b)).eval o n := by
  rw [pNot_eval, pAnd_eval, pOr_eval, pNot_eval, pNot_eval, Bool.not_and]

/-! ## §3 WORKED EXAMPLES on the RIGID fragment — each wired to the DECISION by `decide`.

Convention: `role` is an interned symbol — `admin = 0`, `active = 1` (frozen = 2). These policies
use only `roleIs`/`refIs` under `∧ₚ`/`∨ₚ`/`¬ₚ`, so every guard `.sym φ` is RIGID and the fixpoint
decisions kernel-run. -/

/-- Access-control policy: **admin OR active** (`role = 0 ∨ role = 1`). -/
def accessPolicy : Pred := roleIs 0 ∨ₚ roleIs 1

/-- A CONTRADICTORY policy: **admin AND active** (`role = 0 ∧ role = 1`) — one `role` symbol cannot
be two values, so no frame satisfies it. The satisfiability decision must return UNSAT. -/
def contradictoryPolicy : Pred := roleIs 0 ∧ₚ roleIs 1

/-- A redundant conjunction: **active AND active** — the same as `active`, by idempotence. -/
def redundantActive : Pred := roleIs 1 ∧ₚ roleIs 1

/-! ### The guards (`.sym φ`) and their RIGID-fragment bundles (`IsSymbolic` + `RigidFull`, both
computed by `rfl`). A `RigidSymbolicRE` feeds BOTH decisions: `.val`/`.property` = SymbolicRE +
RigidFull for emptiness, the whole bundle for equivalence.

The DECISION theorems below each force one kernel run of the `≅`-fixpoint (`by rfl` on the `decide`);
they are the deliverable, so we do NOT also `#guard` the same `decide` (that would double the
kernel work). The cheap structural `#guard rigidRE …` witnesses fragment membership. -/

def accessRE  : PredRE := .sym accessPolicy
def accessR   : RigidSymbolicRE :=
  ⟨⟨accessRE, by rw [IsSymbolic]; rfl⟩, show rigidRE accessRE = true from rfl⟩

def contradictoryRE : PredRE := .sym contradictoryPolicy
def contradictoryR  : RigidSymbolicRE :=
  ⟨⟨contradictoryRE, by rw [IsSymbolic]; rfl⟩, show rigidRE contradictoryRE = true from rfl⟩

def redundantRE : PredRE := .sym redundantActive
def redundantR  : RigidSymbolicRE :=
  ⟨⟨redundantRE, by rw [IsSymbolic]; rfl⟩, show rigidRE redundantRE = true from rfl⟩

def activeRE : PredRE := .sym (roleIs 1)
def activeR  : RigidSymbolicRE :=
  ⟨⟨activeRE, by rw [IsSymbolic]; rfl⟩, show rigidRE activeRE = true from rfl⟩

-- Two DIFFERENT single-role policies, to exhibit a NON-equivalence verdict.
def role7RE : PredRE := .sym (roleIs 7)
def role7R  : RigidSymbolicRE :=
  ⟨⟨role7RE, by rw [IsSymbolic]; rfl⟩, show rigidRE role7RE = true from rfl⟩
def role8RE : PredRE := .sym (roleIs 8)
def role8R  : RigidSymbolicRE :=
  ⟨⟨role8RE, by rw [IsSymbolic]; rfl⟩, show rigidRE role8RE = true from rfl⟩

-- All the worked guards are in the RIGID fragment (kernel-checked, cheap structural test):
#guard rigidRE accessRE && rigidRE contradictoryRE && rigidRE redundantRE
        && rigidRE activeRE && rigidRE role7RE && rigidRE role8RE

/-! ### "Is this policy SATISFIABLE?" — the emptiness decision, fired by `decide`. -/

/-- **`accessPolicy_satisfiable`** — concluded FROM the running fixpoint: some transition satisfies
the admin-or-active access policy (a frame with `role = 0` is accepted). The `decide` returns
NONEMPTY at ALL word lengths, in a handful of `≅`-classes, where the bound-based route is
astronomical. -/
theorem accessPolicy_satisfiable : ∃ w, derives w accessRE = true :=
  @of_decide_eq_true _ (predRE_emptiness_decidable_fix 32 accessR.val accessR.property) (by rfl)

/-- **`contradictoryPolicy_unsatisfiable`** — the `admin ∧ active` policy admits NO transition of ANY
length: an authoring bug (mutually exclusive role pins) caught by the decision, not by testing. A
COMPLETE emptiness verdict over the infinite `Value` alphabet. -/
theorem contradictoryPolicy_unsatisfiable : ¬ ∃ w, derives w contradictoryRE = true :=
  @of_decide_eq_false _ (predRE_emptiness_decidable_fix 32 contradictoryR.val contradictoryR.property)
    (by rfl)

/-! ### THE KILLER APP — "are these two access policies THE SAME?" — the equivalence decision.

Two representative verdicts, both polarities. De Morgan and disjunction-commutativity are also real
policy equivalences a builder relies on; they are decided here at the cheaper `Pred.eval` level
(`deMorgan_eval`, `pOr_comm`) — the LANGUAGE-equivalence route runs on them too (both guards are
rigid), just at more kernel cost than we spend by default. -/

/-- **`redundant_equiv_active`** — the redundant conjunction and the plain policy accept EXACTLY the
same transitions, every length: the refactor `p ∧ p ⇝ p` is decided sound by the running fixpoint. -/
theorem redundant_equiv_active : ∀ w, derives w redundantRE = derives w activeRE :=
  @of_decide_eq_true _ (predRE_equivalence_decidable_fix 32 redundantR activeR) (by rfl)

/-- **`role7_not_equiv_role8`** — two distinct role policies are decided NOT the same (they disagree
on the frame `[{role ↦ sym 7}]`): the decision that catches "these two policies I thought were equal
actually differ". -/
theorem role7_not_equiv_role8 : ¬ ∀ w, derives w role7RE = derives w role8RE :=
  @of_decide_eq_false _ (predRE_equivalence_decidable_fix 32 role7R role8R) (by rfl)

/-! ## §4 The enum tier — `statusIn` (enum-by-symbol), decided SATISFIABLE through the pin-cover
route. `symMemberOf` is pin-representable (`IsSymbolic`), so the general BOUNDED decision applies;
the 07-19 `predBEq` widening additionally made it `rigidRE`, so the fast fixpoint route is available
too. We connect it via the pin-cover route, which holds on the STABLE `IsSymbolic` property alone. -/

/-- Enum-state gate: `status ∈ {active, frozen}` (`statusIn [1, 2]`). -/
def enumGate : Pred := statusIn [1, 2]
def enumGateRE : PredRE := .sym enumGate

-- `enumGate` IS pin-representable (`IsSymbolic`), so its minterm cover is computable and the general
-- bounded satisfiability decision applies (a `symMemberOf` leaf enumerates one pin per enum case):
#guard (atomsOfLeaves? (leavesOf enumGateRE)).isSome

/-- **`enumGate_satisfiable`** — concluded THROUGH the general BOUNDED decision (pin cover +
`nonemptyWithinG_iff_bounded`): an accepting transition of length ≤ 1 genuinely exists for the
enum-state gate (a frame with `status = active`). -/
theorem enumGate_satisfiable : ∃ w, w.length ≤ 1 ∧ derives w enumGateRE = true :=
  (nonemptyWithinG_iff_bounded (coverOfSymbolic (R := enumGateRE) rfl)
    (symbolicOver_leavesOf _) (n := 1)).mp rfl

/-! ## §5 The cross-field tier — a real transfer-authorization policy over `digFieldEq`. `digFieldEq`
is a CROSS-FIELD equality over an infinite value domain, so it is NOT pin-representable (`predAtoms?`
returns `none`) — the minterm cover cannot enumerate it, so `.sym transferAuth` is not `IsSymbolic`
and the REGEX-level decision does not apply (this is a deeper wall than the `predBEq`-rigidity one,
which the 07-19 widening already crossed for `digFieldEq`). But `Pred.eval` is total and DECIDABLE,
so the policy admits/rejects concrete transitions — the executor teeth (`predStateStepGuarded`). -/

/-- **Transfer-authorization policy**: the sender must own the cell AND it must not be a self-transfer
(`ownerMatch ∧ₚ noSelfTransfer`). Authored in the clean Boolean algebra over the typed atoms. -/
def transferAuth : Pred := ownerMatch ∧ₚ noSelfTransfer

def goodTransfer : Value :=   -- sender = owner, from ≠ to: authorized
  .record [("sender", .dig 7), ("owner", .dig 7), ("from", .dig 7), ("to", .dig 9)]
def selfTransfer : Value :=   -- sender = owner but from = to: REFUSED (self-transfer)
  .record [("sender", .dig 7), ("owner", .dig 7), ("from", .dig 7), ("to", .dig 7)]
def nonOwnerTransfer : Value := -- from ≠ to but sender ≠ owner: REFUSED (not the owner)
  .record [("sender", .dig 9), ("owner", .dig 7), ("from", .dig 7), ("to", .dig 9)]

#guard (transferAuth.eval (.record []) goodTransfer)              -- true
#guard (transferAuth.eval (.record []) selfTransfer) == false     -- false
#guard (transferAuth.eval (.record []) nonOwnerTransfer) == false -- false

-- Fragment boundary, witnessed: the transfer policy's `digFieldEq` atoms are NOT pin-representable,
-- so `.sym transferAuth` is not `IsSymbolic` and the REGEX-level decision (which needs a minterm
-- cover) does not apply — the standing wall for cross-field equality over an infinite domain:
#guard (atomsOfLeaves? (leavesOf (.sym transferAuth))).isSome == false

/-- **`transferAuth_discriminates`** — the transfer policy is a genuine multi-tooth discriminator
(both polarities): authorizes the owner-driven non-self transfer, refuses a self-transfer and a
non-owner transfer. Decided by `Pred.eval` (the executor leg), independent of the regex fragment. -/
theorem transferAuth_discriminates :
    transferAuth.eval (.record []) goodTransfer = true ∧
    transferAuth.eval (.record []) selfTransfer = false ∧
    transferAuth.eval (.record []) nonOwnerTransfer = false :=
  ⟨by decide, by decide, by decide⟩

/-- **`transferAuth_eq_requireAll`** — the same transfer policy authored as `requireAll [ownerMatch,
noSelfTransfer]` agrees with the `∧ₚ` spelling at every transition (a `Pred`-level equivalence that
holds even though the regex decision cannot reach these atoms yet). The "two spellings are the same
policy" answer, on the EVAL-only tier. -/
theorem transferAuth_eq_requireAll (o n : Value) :
    (requireAll [ownerMatch, noSelfTransfer]).eval o n = transferAuth.eval o n :=
  requireAll_pair_eq_and ownerMatch noSelfTransfer o n

/-! ## Axiom hygiene — every LAW and DECISION-concluded theorem is kernel-clean. -/

#assert_all_clean [
  pAnd_eval,
  pOr_eval,
  pNot_eval,
  requireAll_pair_eq_and,
  requireAny_pair_eq_or,
  pOr_comm,
  pAnd_idem,
  deMorgan_eval,
  accessPolicy_satisfiable,
  contradictoryPolicy_unsatisfiable,
  redundant_equiv_active,
  role7_not_equiv_role8,
  enumGate_satisfiable,
  transferAuth_discriminates,
  transferAuth_eq_requireAll
]

end PredicateLibrary

end Dregg2.Crypto.Deriv
