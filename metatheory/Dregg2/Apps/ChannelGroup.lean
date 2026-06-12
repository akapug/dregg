/-
# Dregg2.Apps.ChannelGroup — the channel-group cell program (ORGANS §4, the group-key epoch lift).

The Lean twin of `cell/src/blueprint.rs`'s channel section (`channel_state_constraints`,
commit `72d43dc64`) — the program installed on a group cell for its whole life, transcribed
faithfully onto the `Exec.Program` predicate language (name-keyed over the 8 `CH_*_SLOT`s).

The deployed teeth, in keystone order (`blueprint.rs:817`):

1. **term pins** — admin + tag pinned once out of `UNINIT` (`pin_term`, `blueprint.rs:247`);
2. **lifecycle** — `AllowedTransitions` UNINIT→OPEN→CLOSED, CLOSED terminal/inert;
3. **the epoch never rewinds** — `Monotonic{epoch}`;
4. **THE EPOCH UNIFICATION TRIPLE** (`blueprint.rs:879`):
   membership-root change ⇒ `StrictMonotonic{epoch}`; key-commitment change ⇒ epoch step;
   epoch step ⇒ `Not(Immutable{key_commit})`. Together: remove-without-rekey, silent rekey,
   and stale-key epoch steps are each UNSAT — remove + rekey are ONE turn or nothing.
5. **governance** — membership/epoch/key/lifecycle writes admit only the admin sender
   (`AnyOf[Immutable{slot}, SenderIs{admin}]` — the polis per-slot actor binding, whose
   Lean proof `actorBound_*` lives at `Exec/Program.lean:816`; we CONSUME it here).

Commitments (`member_root` = the sorted BLAKE3 member-leaf set, `key_commit` =
`BLAKE3(epoch ‖ key)`) are modeled as opaque scalars: the cell only ever sees commitments
(`blueprint.rs`: the key schedule is swappable off-cell), and the hash-binding content (a
replayed old-key commitment at a new epoch is *detectable*) is the §8 crypto portal — here we
prove the ORDERING/REWRITE laws the program enforces on the commitments themselves. The Lean
record substrate is strictly fail-closed on an absent field where Rust's 8 slots are
always-present; every modeled state carries all 8 fields, so the two readings agree.

## The capability-darkness half (HONEST — a named interface premise, not a proof)

The group's key epoch and the capability freshness epoch are THE SAME counter
(`sdk/src/channels.rs` module docs) — but the `delegation_epoch` side of that tie lives in
the EXECUTOR (`RevokeDelegation{epoch_anchor}` bumps it; R7's epoch-at-retrieval
`CapabilityStale` refusal, `turn/src/executor/apply.rs`, stales every group-held cap with
`stored_epoch < delegation_epoch`), OUTSIDE the cell program: a cell program cannot read
`delegation_epoch` yet. The tie is carried by the canonical turn builders' fail-closed checks
(`Channel::epoch_step`, `sdk/src/channels.rs`; `node/src/channels_service.rs`) — so here it is
the NAMED premise `DelegationEpochTie` (the SAME residue the Rust docs name loudly), and
`remove_darkens_both` is the composition theorem UNDER that premise. The closure lane is the
program-readable `delegation_epoch` executor atom (the executor lane owns those files — out of
scope here). Likewise the in-program M-of-N council gate needs a count-equal/order-statistic
atom (`SimpleConstraint.countEqual`-shaped, slotting into `adminGated`'s `anyOf` in place of
`senderIs admin`) the constraint language does not yet have — named loudly, not attempted.

Keystones (all `#assert_axioms`-pinned, non-vacuity both polarities via `#guard`):
  * `membership_change_steps_epoch` — an admitted root change strictly increases the epoch;
  * `epoch_step_rewrites_key`       — an admitted epoch step rewrites the key commitment;
  * `remove_without_rekey_unsat`    — THE keystone: root changed ∧ key unchanged ⇒ REFUSED
                                      (and the full remove+rekey turn ADMITS — `#guard`);
  * `epoch_never_rewinds`           — epoch monotone forever along any admitted schedule;
  * `admin_gates`                   — a non-admin sender cannot move any control-plane slot;
  * `remove_darkens_both`           — under `DelegationEpochTie`: an admitted remove turn ⇒
                                      forward-key darkness (fresh commitment ≠ old) AND
                                      capability staleness (every cap stamped ≤ the pre-epoch
                                      is R7-stale at the new delegation epoch).
-/
import Dregg2.Exec.Program

namespace Dregg2.Apps.ChannelGroup

open Dregg2.Exec

/-! ## The 8 slots (`cell/src/blueprint.rs` `CH_*_SLOT`, name-keyed). -/

/-- `CH_STATE_SLOT = 0` — lifecycle state. -/
def stateF      : FieldName := "state"
/-- `CH_MEMBER_ROOT_SLOT = 1` — the openable membership commitment (opaque scalar here). -/
def memberRootF : FieldName := "member_root"
/-- `CH_EPOCH_SLOT = 2` — THE epoch counter: group-key epoch AND capability freshness epoch. -/
def epochF      : FieldName := "epoch"
/-- `CH_KEY_COMMIT_SLOT = 3` — the epoch key commitment `BLAKE3(epoch ‖ key)` (opaque scalar). -/
def keyCommitF  : FieldName := "key_commit"
/-- `CH_ADMIN_SLOT = 4` — the governance identity (term-pinned once OPEN). -/
def adminF      : FieldName := "admin"
/-- `CH_APP_SLOT_A = 5` — application slot (unconstrained; reserved for the M-of-N successor). -/
def appAF       : FieldName := "app_a"
/-- `CH_APP_SLOT_B = 6` — application slot (unconstrained). -/
def appBF       : FieldName := "app_b"
/-- `CH_TAG_SLOT = 7` — the group tag (term-pinned). -/
def tagF        : FieldName := "tag"

/-- `STATE_UNINIT = 0`. -/
def stateUninit : Int := 0
/-- `STATE_OPEN = 1`. -/
def stateOpen   : Int := 1
/-- `CH_STATE_CLOSED = 2` (terminal/inert). -/
def stateClosed : Int := 2

/-! ## The program (`channel_state_constraints`, `blueprint.rs:838`). -/

/-- `pin_term(slot, lit)` (`blueprint.rs:247`): pin `slot` to `lit` whenever the cell has left
`UNINIT` — `AnyOf[state == UNINIT, slot == lit]` (both read the POST-state, as in Rust). -/
def pinTerm (f : FieldName) (lit : Int) : StateConstraint :=
  .anyOf [.fieldEquals stateF stateUninit, .fieldEquals f lit]

/-- `admin_gated(slot)` (`blueprint.rs:847`): the polis per-slot actor binding
`AnyOf[Immutable{slot}, SenderIs{admin}]` — slot `f` flips only in a turn SENT by the admin.
The Lean semantics of this exact shape is already PROVED (`actorBound_owner_flips` /
`actorBound_flip_requires_sender` / `actorBound_untouched_open`, `Exec/Program.lean:816`);
the keystones below consume those theorems rather than reproving them. (The M-of-N council
successor would replace the `senderIs admin` disjunct with a count-equal atom over approval
slots — an `Exec.Program` atom the language does not yet have; named, out of scope.) -/
def adminGated (admin : Int) (f : FieldName) : StateConstraint :=
  .anyOf [.immutable f, .senderIs admin]

/-- `epoch_steps_when_changed(slot)` (`blueprint.rs:853`): a change to `slot` demands a STRICT
epoch step — `AnyOf[Immutable{slot}, StrictMonotonic{epoch}]`. -/
def epochStepsWhenChanged (f : FieldName) : StateConstraint :=
  .anyOf [.immutable f, .strictMono epochF]

/-- The triple's third leg (`blueprint.rs:887`): an epoch step demands a REWRITTEN key
commitment — `AnyOf[Immutable{epoch}, Not(Immutable{key_commit})]` (a removal that bumps the
epoch but keeps the old key is UNSAT). -/
def freshKeyOnEpochStep : StateConstraint :=
  .anyOf [.immutable epochF, .not (.immutable keyCommitF)]

/-- The full channel-group constraint set, in the Rust keystone order. (Rust's constructor
additionally FAILS CLOSED on a zero admin — no governor — and a zero tag — indistinguishable
from an unborn cell; the theorems below are parametric in both, so that creation-time gate is
upstream of everything proved here.) -/
def channelConstraints (admin tag : Int) : List StateConstraint :=
  [ pinTerm adminF admin                                                       -- 1. term pins
  , pinTerm tagF tag
  , .allowedTransitions stateF [(0, 0), (0, 1), (1, 1), (1, 2)]                -- 2. lifecycle
  , .simple (.monotonic epochF)                                                -- 3. no rewind
  , epochStepsWhenChanged memberRootF                                          -- 4. THE TRIPLE
  , epochStepsWhenChanged keyCommitF
  , freshKeyOnEpochStep
  , adminGated admin memberRootF                                               -- 5. governance
  , adminGated admin epochF
  , adminGated admin keyCommitF
  , adminGated admin stateF
  ]

/-- **The channel-group program** (`channel_cell_program`, `blueprint.rs:906`): the
`CellProgram::Predicate` installed on the group cell for its whole life. -/
def channelProgram (admin tag : Int) : RecordProgram :=
  .predicate (channelConstraints admin tag)

/-! ## Extraction plumbing — an admitted turn satisfies every constraint. -/

/-- Every constraint of the list binds on an admitted turn (`admitsCtx` on `.predicate` IS the
conjunction, definitionally). -/
private theorem admitted_mem {admin tag : Int} {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : (channelProgram admin tag).admitsCtx ctx m o n = true)
    {c : StateConstraint} (hc : c ∈ channelConstraints admin tag) :
    evalConstraintCtx ctx c o n = true := by
  have hall : (channelConstraints admin tag).all
      (fun c => evalConstraintCtx ctx c o n) = true := h
  exact List.all_eq_true.mp hall c hc

/-- A two-variant `anyOf` whose first disjunct fails forces the second. -/
private theorem anyOf_pair_right {ctx : TurnCtx} {x y : SimpleConstraint} {o n : Value}
    (h : evalConstraintCtx ctx (.anyOf [x, y]) o n = true)
    (hx : evalSimpleCtx ctx x o n = false) :
    evalSimpleCtx ctx y o n = true := by
  have h' : (evalSimpleCtx ctx x o n || (evalSimpleCtx ctx y o n || false)) = true := h
  rw [hx] at h'
  simpa using h'

/-- A strict epoch step refutes `immutable epoch` (the changed-slot reading of `a < b`). -/
private theorem strict_step_changes_epoch {o n : Value} {a b : Int}
    (ha : o.scalar epochF = some a) (hb : n.scalar epochF = some b) (hab : a < b) :
    evalSimple (.immutable epochF) o n = false := by
  simp only [evalSimple, ha, hb, beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
  omega

/-- `immutable f = false` with the old value present yields the honest disequality. -/
private theorem immutable_false_ne {f : FieldName} {o n : Value} {x : Int}
    (hx : o.scalar f = some x) (h : evalSimple (.immutable f) o n = false) :
    n.scalar f ≠ some x := by
  simp only [evalSimple, hx] at h
  intro hn
  simp [hn] at h

/-- An admitted `monotonic f` yields both scalars and the inequality (the local one-direction
shadow of `evalSimple_monotonic_iff`, `Proof/WPCatalog.lean:144` — kept local so this app
imports only `Exec.Program`). -/
private theorem monotonic_le {f : FieldName} {o n : Value}
    (h : evalSimple (.monotonic f) o n = true) :
    ∃ a b, o.scalar f = some a ∧ n.scalar f = some b ∧ a ≤ b := by
  cases ha : o.scalar f with
  | none => simp [evalSimple, ha] at h
  | some a =>
    cases hb : n.scalar f with
    | none => simp [evalSimple, ha, hb] at h
    | some b =>
      simp only [evalSimple, ha, hb] at h
      exact ⟨a, b, rfl, rfl, of_decide_eq_true h⟩

/-- Constraint 3 (`Monotonic{epoch}`) read off an admitted turn: the epoch scalars exist on
both sides and never decrease. -/
private theorem admitted_epoch_le {admin tag : Int} {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : (channelProgram admin tag).admitsCtx ctx m o n = true) :
    ∃ x y, o.scalar epochF = some x ∧ n.scalar epochF = some y ∧ x ≤ y := by
  have hcon : evalConstraintCtx ctx (.simple (.monotonic epochF)) o n = true :=
    admitted_mem h (by
      unfold channelConstraints
      exact .tail _ (.tail _ (.tail _ (.head _))))
  have hsim : evalSimple (.monotonic epochF) o n = true := hcon
  exact monotonic_le hsim

/-! ## KEYSTONE 1 — membership change ⇒ the epoch strictly steps. -/

/-- **`membership_change_steps_epoch`** — any admitted turn that CHANGES the membership root
(the `immutable member_root` disjunct rejects) strictly increases the epoch: both epoch
scalars are present and `pre < post`. The triple's first leg, through the new
`evalSimple_strictMono_iff` admit-characterization. -/
theorem membership_change_steps_epoch {admin tag : Int} {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : (channelProgram admin tag).admitsCtx ctx m o n = true)
    (hroot : evalSimple (.immutable memberRootF) o n = false) :
    ∃ a b, o.scalar epochF = some a ∧ n.scalar epochF = some b ∧ a < b := by
  have hany : evalConstraintCtx ctx (epochStepsWhenChanged memberRootF) o n = true :=
    admitted_mem h (by
      unfold channelConstraints
      exact .tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have himm : evalSimpleCtx ctx (.immutable memberRootF) o n = false := hroot
  have hstrict : evalSimpleCtx ctx (.strictMono epochF) o n = true :=
    anyOf_pair_right hany himm
  exact (evalSimple_strictMono_iff epochF o n).mp hstrict

/-- The same leg for the key slot: a key-commitment change strictly steps the epoch (no
SILENT REKEY within an epoch — the triple's second leg). -/
theorem key_change_steps_epoch {admin tag : Int} {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : (channelProgram admin tag).admitsCtx ctx m o n = true)
    (hkey : evalSimple (.immutable keyCommitF) o n = false) :
    ∃ a b, o.scalar epochF = some a ∧ n.scalar epochF = some b ∧ a < b := by
  have hany : evalConstraintCtx ctx (epochStepsWhenChanged keyCommitF) o n = true :=
    admitted_mem h (by
      unfold channelConstraints
      exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have himm : evalSimpleCtx ctx (.immutable keyCommitF) o n = false := hkey
  have hstrict : evalSimpleCtx ctx (.strictMono epochF) o n = true :=
    anyOf_pair_right hany himm
  exact (evalSimple_strictMono_iff epochF o n).mp hstrict

/-! ## KEYSTONE 2 — an epoch step rewrites the key commitment. -/

/-- **`epoch_step_rewrites_key`** — any admitted turn that moves the epoch slot rewrites the
key commitment (the triple's third leg: `immutable epoch` rejected forces
`not (immutable key_commit)` to have fired). -/
theorem epoch_step_rewrites_key {admin tag : Int} {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : (channelProgram admin tag).admitsCtx ctx m o n = true)
    (hepoch : evalSimple (.immutable epochF) o n = false) :
    evalSimple (.immutable keyCommitF) o n = false := by
  have hany : evalConstraintCtx ctx freshKeyOnEpochStep o n = true :=
    admitted_mem h (by
      unfold channelConstraints
      exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  have himm : evalSimpleCtx ctx (.immutable epochF) o n = false := hepoch
  have hnot : evalSimpleCtx ctx (.not (.immutable keyCommitF)) o n = true :=
    anyOf_pair_right hany himm
  have hbang : (!(evalSimpleCtx ctx (.immutable keyCommitF) o n)) = true := hnot
  cases hk : evalSimpleCtx ctx (.immutable keyCommitF) o n with
  | false => exact hk
  | true  => rw [hk] at hbang; cases hbang

/-! ## KEYSTONE 3 — remove-without-rekey is UNSAT (THE keystone). -/

/-- **`remove_without_rekey_unsat`** — the partial turn is REFUSED: a turn changing the
membership root while keeping the key commitment is inadmissible at EVERY context, method,
and term pair. (Chain: root change ⇒ strict epoch step ⇒ epoch slot moved ⇒ key must be
rewritten — contradicting the kept key.) The positive polarity — the FULL remove+rekey turn
ADMITS — is the `#guard` battery below (`remove + rekey are ONE turn or nothing`). -/
theorem remove_without_rekey_unsat {admin tag : Int} {ctx : TurnCtx} {m : Nat} {o n : Value}
    (hroot : evalSimple (.immutable memberRootF) o n = false)
    (hkey : evalSimple (.immutable keyCommitF) o n = true) :
    (channelProgram admin tag).admitsCtx ctx m o n = false := by
  cases hadm : (channelProgram admin tag).admitsCtx ctx m o n with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨a, b, ha, hb, hab⟩ := membership_change_steps_epoch hadm hroot
    have hep : evalSimple (.immutable epochF) o n = false :=
      strict_step_changes_epoch ha hb hab
    have hkfalse := epoch_step_rewrites_key hadm hep
    rw [hkey] at hkfalse
    cases hkfalse

/-! ## KEYSTONE 4 — the epoch never rewinds, forever. -/

/-- An admitted schedule: a chain of turns, each admitted by the channel program (any context,
any method, per step). -/
inductive AdmittedChain (admin tag : Int) : Value → Value → Prop where
  /-- The empty schedule. -/
  | refl (s : Value) : AdmittedChain admin tag s s
  /-- Extend an admitted schedule by one admitted turn. -/
  | step {s₀ s₁ s₂ : Value} (ctx : TurnCtx) (m : Nat)
      (hc : AdmittedChain admin tag s₀ s₁)
      (h : (channelProgram admin tag).admitsCtx ctx m s₁ s₂ = true) :
      AdmittedChain admin tag s₀ s₂

/-- **`epoch_never_rewinds`** — along ANY admitted schedule the epoch is monotone: the final
epoch dominates the initial one (constraint 3, `Monotonic{epoch}`, folded over the chain). -/
theorem epoch_never_rewinds {admin tag : Int} {s₀ s₁ : Value}
    (hchain : AdmittedChain admin tag s₀ s₁) :
    ∀ a b, s₀.scalar epochF = some a → s₁.scalar epochF = some b → a ≤ b := by
  induction hchain with
  | refl =>
      intro a b ha hb
      rw [ha] at hb
      cases hb
      omega
  | step ctx m hc h ih =>
      intro a b ha hb
      obtain ⟨x, y, hx, hy, hxy⟩ := admitted_epoch_le h
      have hax : a ≤ x := ih a x ha hx
      rw [hy] at hb
      cases hb
      omega

/-! ## KEYSTONE 5 — the admin gates the control plane. -/

/-- One gated slot: an admitted turn whose sender is NOT the admin leaves the slot untouched.
Consumes the PROVED polis binding `actorBound_flip_requires_sender` (`Exec/Program.lean:821`)
— a stolen capability cannot move a gated slot. -/
private theorem gated_slot_fixed {admin : Int} {ctx : TurnCtx} {o n : Value} {f : FieldName}
    (hany : evalConstraintCtx ctx (adminGated admin f) o n = true)
    (hs : ctx.sender ≠ some admin) :
    evalSimple (.immutable f) o n = true := by
  cases hcase : evalSimple (.immutable f) o n with
  | true => rfl
  | false =>
    exfalso
    have hfalse : evalConstraintCtx ctx (adminGated admin f) o n = false :=
      actorBound_flip_requires_sender admin f ctx o n hcase hs
    rw [hfalse] at hany
    cases hany

/-- **`admin_gates`** — a non-admin sender cannot change ANY control-plane slot: membership
root, epoch, key commitment, and lifecycle state are all untouched by an admitted turn whose
sender is not the admin. (The app slots 5/6 stay open to anyone — posting is off-cell.) -/
theorem admin_gates {admin tag : Int} {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : (channelProgram admin tag).admitsCtx ctx m o n = true)
    (hs : ctx.sender ≠ some admin) :
    evalSimple (.immutable memberRootF) o n = true ∧
    evalSimple (.immutable epochF) o n = true ∧
    evalSimple (.immutable keyCommitF) o n = true ∧
    evalSimple (.immutable stateF) o n = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact gated_slot_fixed (admitted_mem h (by
      unfold channelConstraints
      exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))) hs
  · exact gated_slot_fixed (admitted_mem h (by
      unfold channelConstraints
      exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
        (.head _)))))))))) hs
  · exact gated_slot_fixed (admitted_mem h (by
      unfold channelConstraints
      exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
        (.head _))))))))))) hs
  · exact gated_slot_fixed (admitted_mem h (by
      unfold channelConstraints
      exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
        (.tail _ (.head _)))))))))))) hs

/-! ## KEYSTONE 6 — the capability-darkness composition (under the NAMED premise). -/

/-- **`DelegationEpochTie` — THE NAMED INTERFACE PREMISE** (the capability half, stated
honestly). The group's epoch SLOT equals the executor's `delegation_epoch` counter for the
group cell. This tie lives OUTSIDE the cell program: it is carried by the canonical
epoch-stepping turn builders' fail-closed checks (`Channel::epoch_step`,
`sdk/src/channels.rs`, asserts `epoch slot ≡ delegation_epoch` before EVERY step;
`node/src/channels_service.rs` likewise) because every such turn carries the
`RevokeDelegation{epoch_anchor}` effect — the one kernel verb that bumps `delegation_epoch` —
in the SAME atomic turn as the slot write. A cell program cannot read `delegation_epoch` yet;
the closure lane is the program-readable executor atom (executor lane — out of scope here).
Until then this premise is exactly the residue the Rust docs name loudly: a divergence is
detectable by any member (`epoch slot ≠ delegation_epoch` is loud), never silently assumed. -/
structure DelegationEpochTie (s : Value) (delegationEpoch : Int) : Prop where
  /-- The post-state epoch slot IS the executor's delegation epoch for the group cell. -/
  tie : s.scalar epochF = some delegationEpoch

/-- R7's epoch-at-retrieval staleness check (`turn/src/executor/apply.rs`, the
`CapabilityStale` refusal): a cap stamped `stored_epoch = some e` is STALE iff
`e < delegation_epoch`; a DIRECT grant (`stored_epoch = none` — the admin's own driving cap)
is R7-exempt, so the governor does not lose the group on every rekey. -/
def r7Stale (storedEpoch : Option Int) (delegationEpoch : Int) : Bool :=
  match storedEpoch with
  | none   => false
  | some e => decide (e < delegationEpoch)

/-- **`remove_darkens_both`** — the composition: UNDER `DelegationEpochTie` at the post-state,
an admitted turn that changes the membership root (the remove) yields BOTH halves of the
group-key lift in one epoch step:

1. **forward-key darkness** — the key commitment is REWRITTEN: the post commitment differs
   from the pre commitment (the removed member's keys open only ≤-pre-epoch ciphertext; the
   fresh key's *content* freshness — `BLAKE3(epoch ‖ key)` binding — is the §8 crypto portal,
   here the program-level rewrite is what is enforced);
2. **capability staleness** — every group-held capability stamped at or before the pre-epoch
   is `r7Stale` at the new delegation epoch (which the premise ties to the post epoch slot):
   `e ≤ pre < post = delegation_epoch` ⇒ `CapabilityStale`.

The removed member loses the next epoch's key AND their freshest cap in the SAME turn. -/
theorem remove_darkens_both {admin tag : Int} {ctx : TurnCtx} {m : Nat} {o n : Value}
    {d k₀ : Int}
    (h : (channelProgram admin tag).admitsCtx ctx m o n = true)
    (hroot : evalSimple (.immutable memberRootF) o n = false)
    (hk₀ : o.scalar keyCommitF = some k₀)
    (htie : DelegationEpochTie n d) :
    (n.scalar keyCommitF ≠ some k₀) ∧
    (∀ e a, o.scalar epochF = some a → e ≤ a → r7Stale (some e) d = true) := by
  obtain ⟨a, b, ha, hb, hab⟩ := membership_change_steps_epoch h hroot
  have hep : evalSimple (.immutable epochF) o n = false :=
    strict_step_changes_epoch ha hb hab
  have hkey : evalSimple (.immutable keyCommitF) o n = false :=
    epoch_step_rewrites_key h hep
  refine ⟨immutable_false_ne hk₀ hkey, ?_⟩
  intro e a' ha' he
  -- the premise ties the new delegation epoch to the post epoch slot: d = b.
  have hd : d = b := by
    have := htie.tie
    rw [hb] at this
    cases this
    rfl
  -- and the pre-epoch is determined: a' = a.
  have ha'' : a' = a := by
    rw [ha] at ha'
    cases ha'
    rfl
  subst hd ha''
  simp only [r7Stale, decide_eq_true_eq]
  omega

/-! ## Axiom hygiene — every keystone pinned. -/

#assert_axioms membership_change_steps_epoch
#assert_axioms key_change_steps_epoch
#assert_axioms epoch_step_rewrites_key
#assert_axioms remove_without_rekey_unsat
#assert_axioms epoch_never_rewinds
#assert_axioms admin_gates
#assert_axioms remove_darkens_both

/-! ## It runs — non-vacuity BOTH polarities on the canonical test channel.

The Lean shadow of `blueprint.rs`'s `channel_birth_and_open` / `channel_remove_and_rekey_are_
one_turn` tests: admin `17`, tag `99`, commitments as opaque scalars (`300`/`200` = the 3- and
2-member roots, `1100`/`2200` = the epoch-1 and epoch-2 key commitments). -/

private def adm : Int := 17
private def tg  : Int := 99
private def prog : RecordProgram := channelProgram adm tg
private def adminCtx    : TurnCtx := { sender := some adm }
private def strangerCtx : TurnCtx := { sender := some 5 }

/-- The unborn cell: all 8 slots zero. -/
private def stUninit : Value := .record
  [(stateF, .int 0), (memberRootF, .int 0), (epochF, .int 0), (keyCommitF, .int 0),
   (adminF, .int 0), (appAF, .int 0), (appBF, .int 0), (tagF, .int 99)]

/-- Post-birth: OPEN, 3 members at epoch 1, epoch-1 key committed, terms pinned. -/
private def stOpen : Value := .record
  [(stateF, .int 1), (memberRootF, .int 300), (epochF, .int 1), (keyCommitF, .int 1100),
   (adminF, .int 17), (appAF, .int 0), (appBF, .int 0), (tagF, .int 99)]

/-- The FULL remove turn: 2-member root + epoch 2 + FRESH epoch-2 key, in ONE turn. -/
private def stRemoved : Value := .record
  [(stateF, .int 1), (memberRootF, .int 200), (epochF, .int 2), (keyCommitF, .int 2200),
   (adminF, .int 17), (appAF, .int 0), (appBF, .int 0), (tagF, .int 99)]

/-- The PARTIAL remove: root changes, epoch steps, key KEPT (the keystone's foil). -/
private def stRemovedStaleKey : Value := .record
  [(stateF, .int 1), (memberRootF, .int 200), (epochF, .int 2), (keyCommitF, .int 1100),
   (adminF, .int 17), (appAF, .int 0), (appBF, .int 0), (tagF, .int 99)]

/-- Remove WITHOUT an epoch step (root changes, epoch kept). -/
private def stRemovedNoStep : Value := .record
  [(stateF, .int 1), (memberRootF, .int 200), (epochF, .int 1), (keyCommitF, .int 1100),
   (adminF, .int 17), (appAF, .int 0), (appBF, .int 0), (tagF, .int 99)]

/-- A SILENT rekey: key changes within the epoch (no step). -/
private def stSilentRekey : Value := .record
  [(stateF, .int 1), (memberRootF, .int 300), (epochF, .int 1), (keyCommitF, .int 9900),
   (adminF, .int 17), (appAF, .int 0), (appBF, .int 0), (tagF, .int 99)]

/-- An epoch REWIND from `stRemoved` (2 → 1, fresh key, root restored). -/
private def stRewound : Value := .record
  [(stateF, .int 1), (memberRootF, .int 300), (epochF, .int 1), (keyCommitF, .int 3300),
   (adminF, .int 17), (appAF, .int 0), (appBF, .int 0), (tagF, .int 99)]

/-- An app-plane write: slot 5 moves, every control-plane slot untouched. -/
private def stAppWrite : Value := .record
  [(stateF, .int 1), (memberRootF, .int 300), (epochF, .int 1), (keyCommitF, .int 1100),
   (adminF, .int 17), (appAF, .int 7), (appBF, .int 0), (tagF, .int 99)]

/-- CLOSED (terminal). -/
private def stClosed : Value := .record
  [(stateF, .int 2), (memberRootF, .int 300), (epochF, .int 1), (keyCommitF, .int 1100),
   (adminF, .int 17), (appAF, .int 0), (appBF, .int 0), (tagF, .int 99)]

-- Birth (UNINIT → OPEN, terms pinned, first epoch + key + roster in one turn): ADMITTED.
#guard prog.admitsCtx adminCtx 0 stUninit stOpen
-- THE keystone, positive polarity: the FULL remove+rekey turn (root + epoch + fresh key) ADMITS.
#guard prog.admitsCtx adminCtx 0 stOpen stRemoved
-- THE keystone, negative polarity: remove with a STALE key (epoch steps, key kept) — REFUSED.
#guard prog.admitsCtx adminCtx 0 stOpen stRemovedStaleKey == false
-- Remove WITHOUT an epoch step — REFUSED (triple leg 1).
#guard prog.admitsCtx adminCtx 0 stOpen stRemovedNoStep == false
-- SILENT rekey within an epoch — REFUSED (triple leg 2).
#guard prog.admitsCtx adminCtx 0 stOpen stSilentRekey == false
-- Epoch REWIND — REFUSED (Monotonic{epoch}), even with a fresh key and an admin sender.
#guard prog.admitsCtx adminCtx 0 stRemoved stRewound == false
-- A NON-ADMIN sender attempting the full (otherwise-legal) remove turn — REFUSED (governance).
#guard prog.admitsCtx strangerCtx 0 stOpen stRemoved == false
-- ... and with NO sender in context — REFUSED (fail-closed).
#guard prog.admitsCtx {} 0 stOpen stRemoved == false
-- The app plane stays OPEN: a stranger's app-slot write touching no gated slot ADMITS.
#guard prog.admitsCtx strangerCtx 0 stOpen stAppWrite
-- Lifecycle: OPEN → CLOSED by the admin ADMITS; CLOSED is terminal (no row out) — REFUSED.
#guard prog.admitsCtx adminCtx 0 stOpen stClosed
#guard prog.admitsCtx adminCtx 0 stClosed stOpen == false
-- Term pins: an admin-slot rewrite once OPEN is REFUSED (pin), even by the admin.
#guard prog.admitsCtx adminCtx 0 stOpen
  (.record [(stateF, .int 1), (memberRootF, .int 300), (epochF, .int 1),
            (keyCommitF, .int 1100), (adminF, .int 55), (appAF, .int 0), (appBF, .int 0),
            (tagF, .int 99)]) == false

-- R7 staleness, both polarities: a cap stamped at epoch 1 is STALE at delegation epoch 2;
-- a cap stamped AT the new epoch is live; a DIRECT grant (none) is exempt.
#guard r7Stale (some 1) 2
#guard r7Stale (some 2) 2 == false
#guard r7Stale none 2 == false

-- The premise is INHABITED at the post-remove state (epoch slot 2 = delegation epoch 2):
example : DelegationEpochTie stRemoved 2 := ⟨by decide⟩
-- ... and REFUTABLE when the counters diverge (the loud detectable divergence).
example : ¬ DelegationEpochTie stRemoved 3 := fun ⟨h⟩ => absurd h (by decide)

end Dregg2.Apps.ChannelGroup
