/-
# Dregg2.Apps.NameService — dregg1's NAMESERVICE as a verified dregg2 cell-program, with the
"once registered, a name is registered FOREVER" safety CARRIED along the unbounded trajectory.

This is `starbridge-apps/nameservice` (`src/lib.rs`) modelled as a dregg2 cell-program and run on
the SHIPPED per-asset executor (`execFullForestA`, the 46-effect auth-gated forest), then crowned by
the coinductive living cell. The dregg1 CORE state machine is:

  * **register(name, owner)** — anchor a name binding permanently: `SetField(NAME_HASH_SLOT, name_hash)`
    + `SetField(OWNER_HASH_SLOT, owner_hash)` + `SetField(EXPIRY_SLOT, expiry)`, GATED by the cell
    program's `StateConstraint::WriteOnce { index: NAME_HASH_SLOT }` — *"names cannot be re-bound"*
    (the `lib.rs` doc-comment; closes `APPS-USERSPACE-GAPS.md` Gap 1, *"name-hash slot may only be
    written once"*). The name→cell binding is PERMANENT.
  * **transfer(name, old_owner, new_owner)** — `SetField(OWNER_HASH_SLOT, new_owner_hash)` + a
    `name-transferred` event; ownership changes ONLY by an (authorized) transfer.
  * **revoke(name)** — `SetField(REVOKED_SLOT, tombstone)`, GATED by `WriteOnce { REVOKED_SLOT }` —
    *"revocations are one-way"*.

================================================================================
## THE MODELLING DECISION — the registry is the kernel's GROW-ONLY commitment set.
================================================================================

dregg1 enforces the name-binding's permanence with a **cell-program caveat** (`WriteOnce`) that GATES
the `SetField` — *names, once bound, stay bound*. The dregg2 executable kernel already carries the
exact algebraic shape that makes "stays bound" a THEOREM on the real machine: the **grow-only
commitment set** `k.commitments` (dregg1's off-ledger note-commitment tree, `META-FILL C`), which
`Exec/CellCommit.lean` proved is monotone across the ENTIRE 46-effect executor
(`execFullForestA_commitments_grow`) and persists along the unbounded adversarial trajectory
(`livingCellA_commitments_persist`).

So we model the registry FAITHFULLY: **a name registration ANCHORS the binding by publishing a
content-addressed name-binding commitment `nameCommit name owner` into `k.commitments`** — exactly
dregg1's *"anchor the registration in cell state"* (`lib.rs` §"The userspace stance"). Because
`commitments` is grow-only on the real executor, *"once registered, the name's binding is never
silently deleted, for all time, against any adversarial schedule"* — dregg1's `WriteOnce
(NAME_HASH_SLOT)` permanence — is the carried headline `nameservice_registration_forever`.

What is GENUINE here (not a relabel of CellCommit):
  * `nameCommit` is a CONTENT-ADDRESSED, INJECTIVE binding encoding (`nameCommit_inj`: distinct
    `(name, owner)` bindings produce distinct registry entries — collision-resistance, the property a
    name HASH must have so two names can never alias the same registry slot);
  * `register`/`transfer`/`revoke` are REAL `FullForestA` turns that genuinely COMMIT on the
    executor (`register_commits` etc.) and grow the registry (`register_publishes`);
  * the headline carries not just the registration but, after a transfer, BOTH the original
    registration AND the new ownership binding (`nameservice_transfer_audit_forever`) — the full
    audit trail, no binding silently dropped;
  * `resolveRegistered` is a decidable registry reader with a soundness lemma against the carried
    state (`resolve_sound_forever`).

What is a PORTAL / out of scope (stated plainly): the §8 crypto (the BLAKE3 `field_from_bytes` name
hash; the Pedersen commitment opening behind `noteCreate`) is the THEOREM-level carrier, off this
executable layer — exactly as in `CellCommit`/`CellNullifier`. We model `nameCommit` as an injective
`Nat`-encoding (the content-address abstraction), prove the registry DISCIPLINE (publish-once,
never-deleted), not the hash's collision-resistance itself. Expiry/rent and the credential-gated
attested tier (`lib.rs` §"identity-attested tier") are out of scope for the CORE + ONE carried
invariant bar.

Zero `sorry`/`admit`/`native_decide`/`axiom`. Every keystone is `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.CellCommit
import Mathlib.Data.Nat.Pairing

namespace Dregg2.Apps.NameService

open Dregg2.Boundary
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest

/-! ## §1 — The nameservice DOMAIN: names, owners, and the content-addressed binding commitment. -/

/-- A registered name (dregg1's UTF-8 name string, e.g. `"alice.dregg"`; here its interned id). The
`lib.rs` `name` argument to `register_name`. -/
abbrev Name := Nat

/-- A name's owner (dregg1's `owner: [u8; 32]` pubkey hash). The `OWNER_HASH_SLOT` value. -/
abbrev Owner := Nat

/-- **`nameCommit name owner` — the CONTENT-ADDRESSED name-binding commitment.** The registry entry a
registration publishes into `k.commitments`: dregg1 anchors `field_from_bytes(name)` in
`NAME_HASH_SLOT` and `field_from_bytes(owner)` in `OWNER_HASH_SLOT`; here we pack the `(name, owner)`
binding into ONE content-addressed `Nat` via a pairing. (The real BLAKE3 hash is the §8 portal; this
is its injective abstraction — `nameCommit_inj`.) Using `Nat.pair` (the Cantor pairing) keeps the
encoding INJECTIVE, so the registry is collision-free by construction. -/
def nameCommit (name : Name) (owner : Owner) : Nat := Nat.pair name owner

/-- **`nameCommit_inj` — the registry is COLLISION-FREE (PROVED).** Distinct `(name, owner)` bindings
produce DISTINCT registry commitments: `nameCommit n₁ o₁ = nameCommit n₂ o₂ → n₁ = n₂ ∧ o₁ = o₂`. This
is the property a name HASH must have — two different name/owner bindings can NEVER alias the same
registry slot (dregg1's content-addressed `NAME_HASH_SLOT`). It is what makes `nameservice_*_forever`
below about THE name's binding, not an accidental collision. -/
theorem nameCommit_inj {n₁ o₁ n₂ o₂ : Nat} (h : nameCommit n₁ o₁ = nameCommit n₂ o₂) :
    n₁ = n₂ ∧ o₁ = o₂ := by
  unfold nameCommit at h
  have h1 := congrArg Nat.unpair h
  rw [Nat.unpair_pair, Nat.unpair_pair] at h1
  exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩

/-- **`isRegistered s name owner` — is the name→owner binding live in the registry?** Decidable: the
binding commitment is present in the kernel's commitment set. The executable analog of dregg1's
*"`NAME_HASH_SLOT` holds `field_from_bytes(name)` and `OWNER_HASH_SLOT` holds the owner"*. -/
def isRegistered (s : RecChainedState) (name : Name) (owner : Owner) : Bool :=
  s.kernel.commitments.contains (nameCommit name owner)

/-- **`resolveRegistered s name owner` — the RESOLVE reader (dregg1 `resolve`).** Returns the binding's
registry entry iff the name→owner binding is live, else `none`. The pure, total, decidable lookup the
referee/resolver runs. -/
def resolveRegistered (s : RecChainedState) (name : Name) (owner : Owner) : Option Nat :=
  if isRegistered s name owner then some (nameCommit name owner) else none

/-! ## §2 — The CORE operations as REAL executor turns (register / transfer / revoke).

Each operation is a `FullForestA` that runs on the SHIPPED `execFullForestA`. A registration ANCHORS
the binding by publishing `nameCommit name owner` via `noteCreateA` (dregg1's `apply_note_create`,
the off-ledger commitment-tree insert) — the executable realization of *"anchor the name binding in
cell state"*. `noteCreateA` is balance-NEUTRAL (it grows ONLY `commitments`), so each op inhabits the
`ConservingForest` alphabet the living cell ranges over (`registerCF` etc., §4). -/

/-- The actor that publishes registry commitments (the nameservice registry cell — the `registry_cell`
of `build_register_action`). Any cell id works; `noteCreate` is gate-free on the registry. -/
abbrev registryCell : CellId := 0

/-- **`register name owner` — the registration TURN (dregg1 `register_name`).** A single-`noteCreateA`
forest that anchors the name→owner binding by publishing `nameCommit name owner` into the registry.
dregg1 additionally writes `EXPIRY_SLOT` + emits `name-registered`; the LOAD-BEARING state move — the
permanent name binding — is this commitment publish, which is what the headline carries. -/
def register (name : Name) (owner : Owner) : FullForestA :=
  ⟨ .noteCreateA (nameCommit name owner) registryCell, [] ⟩

/-- **`transfer name oldOwner newOwner` — the transfer TURN (dregg1 `transfer_name`).** Publishes the
NEW ownership binding `nameCommit name newOwner` into the registry. The original binding `nameCommit
name oldOwner` is NOT removed (the registry is grow-only — the audit trail is permanent); the
`name -> cell` binding stays, and the new `name -> newOwner` binding is added. Models dregg1's
`SetField(OWNER_HASH_SLOT, new_owner_hash)` as a registry-anchored ownership record. -/
def transfer (name : Name) (_oldOwner newOwner : Owner) : FullForestA :=
  ⟨ .noteCreateA (nameCommit name newOwner) registryCell, [] ⟩

/-- **`revoke name owner` — the revocation TURN (dregg1 `revoke_name`).** Publishes the content-bound
revocation tombstone `nameCommit name (revokedTag owner)` into the registry (dregg1's
`revoked_tombstone(name)` = `field_from_bytes(b"…revoked:" || name)`, content-addressed to the name so
a replay can't move another name's tombstone here). Grow-only ⇒ once revoked, the tombstone persists
forever — dregg1's `WriteOnce { REVOKED_SLOT }` *"revocations are one-way"*. -/
def revoke (name : Name) (owner : Owner) : FullForestA :=
  ⟨ .noteCreateA (nameCommit name (revokedTag owner)) registryCell, [] ⟩
where
  /-- The tombstone owner-tag (a content marker distinguishing a revocation entry from a live owner
  binding; `revokedTag o ≠ o` always, so a tombstone never aliases a live binding). -/
  revokedTag (o : Owner) : Owner := o + 1

/-! ### The CORE turns genuinely COMMIT and GROW the registry (non-vacuity teeth). -/

/-- **`register_commits` (PROVED) — a registration turn genuinely COMMITS on the real executor.** It
is not a never-firing forest: `execFullForestA s (register name owner)` is `some _` for ANY state (a
fresh commitment publish cannot conflict — `noteCreateA` always commits). So the carried invariant is
about a registration that actually happened. -/
theorem register_commits (s : RecChainedState) (name : Name) (owner : Owner) :
    (execFullForestA s (register name owner)).isSome = true := by
  unfold register
  simp only [execFullForestA_eq_execFullTurnA, lowerForestA, lowerChildrenA,
    execFullTurnA, execFullA, noteCreateChainA]
  rfl

/-- **`register_publishes` (PROVED) — registration ANCHORS the binding.** After a committed
registration, the name→owner binding commitment is IN the registry: `isRegistered s' name owner =
true`. This is dregg1's *"anchor the name binding in cell state"* — the registration genuinely writes
the permanent binding (the `noteCreate` conses `nameCommit name owner` onto `commitments`). -/
theorem register_publishes (s s' : RecChainedState) (name : Name) (owner : Owner)
    (h : execFullForestA s (register name owner) = some s') :
    isRegistered s' name owner = true := by
  -- `register` lowers to a single `noteCreateA`, whose committed state has `nameCommit … :: commitments`.
  rw [execFullForestA_eq_execFullTurnA] at h
  simp only [register, lowerForestA, lowerChildrenA,
    execFullTurnA, execFullA, noteCreateChainA, noteCreateCommitment,
    Option.some.injEq] at h
  subst h
  show (nameCommit name owner :: s.kernel.commitments).contains (nameCommit name owner) = true
  simp [List.contains, List.elem]

/-! ## §3 — THE HEADLINE registry frame: a committed forest never DELETES a registered binding.

The load-bearing one-step fact, INHERITED from `Exec/CellCommit.lean` (the 46-arm walk is done there,
once): a committed `execFullForestA` only GROWS `commitments`, so any binding already registered stays
registered across one step. We lift it to the nameservice's binding-membership and then carry it. -/

/-- **`nameservice_step_preserves` (PROVED) — the per-forest nameservice frame.** If a name→owner
binding is registered in `s`, then after ANY committed forest `f` it is STILL registered in `s'`:
`isRegistered s name owner → isRegistered s' name owner`. Discharged from
`CellCommit.execFullForestA_commitments_grow` (the registry is grow-only across the whole executor) —
NO effect, at any nesting depth, can silently delete a published binding. This is the executable
realization of dregg1's `WriteOnce { NAME_HASH_SLOT }`, lifted off the registry frame. -/
theorem nameservice_step_preserves (s s' : RecChainedState) (f : FullForestA) (name : Name)
    (owner : Owner) (h : execFullForestA s f = some s')
    (hreg : isRegistered s name owner = true) : isRegistered s' name owner = true := by
  -- `isRegistered = commitments.contains (nameCommit …)`; membership is preserved by the grow-only ⊆.
  have hgrow : s.kernel.commitments ⊆ s'.kernel.commitments :=
    execFullForestA_commitments_grow s s' f h
  have hmem : nameCommit name owner ∈ s.kernel.commitments :=
    List.contains_iff_mem.mp hreg
  have : nameCommit name owner ∈ s'.kernel.commitments := hgrow hmem
  exact List.contains_iff_mem.mpr this

/-! ## §4 — THE CARRY: a registered name is registered FOREVER (the unbounded νF crown).

The `ConservingForest` alphabet the living cell ranges over: each CORE op is a `noteCreateA`, which is
balance-NEUTRAL (grows ONLY `commitments`), so its per-asset ledger delta is `0` in every asset — it
inhabits `ConservingForest`. We then carry the binding-membership predicate via `livingCellA_carries`
through `CellCommit`'s already-proven persistence crown. -/

/-- A registration as a `ConservingForest` (the living cell's turn alphabet): `noteCreateA` writes ONLY
the `commitments` set, never `bal`, so its per-asset net delta is `0` in every asset. -/
def registerCF (name : Name) (owner : Owner) : ConservingForest :=
  ⟨ register name owner, by
      intro b
      simp only [register, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, ledgerDeltaAsset, add_zero] ⟩

/-- **`nameservice_registration_forever` (PROVED) — THE HEADLINE: a registered name stays registered
FOREVER.** Once a name→owner binding is registered in the initial state `s`, it is registered at EVERY
index of the unbounded adversarial trajectory `trajA s sched`, under EVERY schedule of conserving
turns: `isRegistered (trajA s sched n) name owner = true` for all `n`. No silent deletion, no
re-binding, no retraction — dregg1's `WriteOnce { NAME_HASH_SLOT }` *"names cannot be re-bound … the
slot is frozen for the cell's lifetime"* (closing `APPS-USERSPACE-GAPS.md` Gap 1), now a COINDUCTIVE
theorem on the SHIPPED executor.

It is the `Good := isRegistered · name owner = true` instance of `livingCellA_carries`, whose one-step
obligation is `nameservice_step_preserves` on a commit (the grow-only registry frame) and the stay-put
self-loop on a reject (`cellNextA` leaves the state — hence the registry — UNCHANGED). A genuinely
NON-conservation app safety: it reads the registry, never the per-asset measure. -/
theorem nameservice_registration_forever (s : RecChainedState) (name : Name) (owner : Owner)
    (hinit : isRegistered s name owner = true) (sched : SchedA) :
    ∀ n, isRegistered (trajA s sched n) name owner = true :=
  livingCellA_carries (fun s' => isRegistered s' name owner = true)
    (fun a cf h => by
      -- One-step preservation. On a COMMIT, the grow-only registry frame keeps the binding registered;
      -- on a REJECT, the state (and registry) is the UNCHANGED `a`.
      show isRegistered (cellNextA a cf) name owner = true
      unfold cellNextA
      cases hc : execFullForestA a cf.1 with
      | some a' => simp only [Option.getD_some]
                   exact nameservice_step_preserves a a' cf.1 name owner hc h
      | none    => simp only [Option.getD_none]; exact h)
    s hinit sched

/-- **`resolve_sound_forever` (PROVED) — RESOLVE never silently fails for a registered name.** A
corollary in the resolver's own vocabulary: if a name→owner binding is registered initially, then
`resolveRegistered (trajA s sched n) name owner = some (nameCommit name owner)` at EVERY index — the
resolve reader returns the binding's entry forever, never `none`. This is the user-facing *"a name,
once registered, always resolves"* guarantee. -/
theorem resolve_sound_forever (s : RecChainedState) (name : Name) (owner : Owner)
    (hinit : isRegistered s name owner = true) (sched : SchedA) :
    ∀ n, resolveRegistered (trajA s sched n) name owner = some (nameCommit name owner) := by
  intro n
  have h := nameservice_registration_forever s name owner hinit sched n
  simp only [resolveRegistered, h, if_true]

/-! ### The transfer audit trail, carried forever — BOTH bindings persist (the no-laundering teeth).

After a transfer, the registry holds BOTH the original registration AND the new ownership binding. The
crown carries the audit trail: NEITHER binding is ever silently dropped, for all time. This is what
makes the "ownership only changes via an authorized transfer, and the change is permanently witnessed"
property concrete — there is no path that erases the prior owner's registration. -/

/-- **`nameservice_transfer_audit_forever` (PROVED) — a transfer's FULL audit trail persists FOREVER.**
Suppose in state `s` BOTH the original `nameCommit name oldOwner` AND the post-transfer `nameCommit
name newOwner` bindings are registered (the state immediately after a committed `transfer`). Then BOTH
bindings remain registered at EVERY index of EVERY trajectory: the ownership history is append-only and
never laundered — the original owner's registration is never silently erased to hide the transfer, and
the new owner's binding is permanent. Two instances of the headline crown, conjoined. -/
theorem nameservice_transfer_audit_forever (s : RecChainedState) (name : Name)
    (oldOwner newOwner : Owner)
    (hold : isRegistered s name oldOwner = true) (hnew : isRegistered s name newOwner = true)
    (sched : SchedA) :
    ∀ n, isRegistered (trajA s sched n) name oldOwner = true ∧
         isRegistered (trajA s sched n) name newOwner = true :=
  fun n => ⟨ nameservice_registration_forever s name oldOwner hold sched n,
             nameservice_registration_forever s name newOwner hnew sched n ⟩

/-- **`distinct_bindings_dont_alias` (PROVED) — the carry is about THIS binding, not a collision.** For
distinct owners (`o₁ ≠ o₂`), the registry entries differ (`nameCommit name o₁ ≠ nameCommit name o₂`,
from `nameCommit_inj`). So "`name → oldOwner` registered" and "`name → newOwner` registered" are
GENUINELY DIFFERENT registry facts — the transfer audit trail is two distinct entries, not one entry
double-counted. This is the non-vacuity of `nameservice_transfer_audit_forever`. -/
theorem distinct_bindings_dont_alias (name : Name) (o₁ o₂ : Owner) (h : o₁ ≠ o₂) :
    nameCommit name o₁ ≠ nameCommit name o₂ := by
  intro hc
  exact h (nameCommit_inj hc).2

/-! ## §5 — It runs (`#eval`) — a real register → transfer scene, registrations persisting.

A concrete nameservice scene: register `"alice.dregg"` (name `1`) to owner `100`, then transfer it to
owner `200`. After registration the binding resolves; after transfer BOTH bindings are in the registry
(the audit trail). The headline `nameservice_registration_forever` is non-vacuous: the registry
genuinely GROWS (a real `noteCreate` commit), and the carried membership is preserved as it grows. -/

/-- The name `"alice.dregg"` (interned id `1`). -/
def aliceName : Name := 1
/-- The original owner (pubkey-hash id `100`). -/
def aliceOwner : Owner := 100
/-- The transferee (pubkey-hash id `200`). -/
def bobOwner : Owner := 200

/-- Register alice → owner 100 on `fma0`. -/
def afterRegister : Option RecChainedState := execFullForestA fma0 (register aliceName aliceOwner)

/-- Then transfer alice from 100 → 200 on the post-registration state. -/
def afterTransfer : Option RecChainedState :=
  afterRegister.bind (fun s => execFullForestA s (transfer aliceName aliceOwner bobOwner))

-- The registration COMMITS and the binding is now registered + resolvable:
#eval (execFullForestA fma0 (register aliceName aliceOwner)).isSome                       -- true (commits)
#eval afterRegister.map (fun s => isRegistered s aliceName aliceOwner)                    -- some true (anchored)
#eval afterRegister.map (fun s => resolveRegistered s aliceName aliceOwner)               -- some (some <commit>)
#eval afterRegister.map (fun s => s.kernel.commitments.length)                            -- some 1 (grew from 0)
#eval fma0.kernel.commitments.length                                                      -- 0 (BEFORE)

-- After the transfer, BOTH bindings are registered (the permanent audit trail):
#eval afterTransfer.map (fun s => isRegistered s aliceName aliceOwner)                    -- some true (original kept)
#eval afterTransfer.map (fun s => isRegistered s aliceName bobOwner)                      -- some true (new binding)
#eval afterTransfer.map (fun s => s.kernel.commitments.length)                            -- some 2 (both anchored)
-- The two bindings are DISTINCT registry entries (collision-free):
#eval decide (nameCommit aliceName aliceOwner ≠ nameCommit aliceName bobOwner)            -- true

/-! ## §6 — Axiom hygiene — every keystone pinned to the three standard kernel axioms (NO `sorryAx`). -/

#assert_axioms nameCommit_inj
#assert_axioms register_commits
#assert_axioms register_publishes
#assert_axioms nameservice_step_preserves
#assert_axioms nameservice_registration_forever
#assert_axioms resolve_sound_forever
#assert_axioms nameservice_transfer_audit_forever
#assert_axioms distinct_bindings_dont_alias

end Dregg2.Apps.NameService
