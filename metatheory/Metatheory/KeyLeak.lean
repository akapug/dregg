/-
# Metatheory.KeyLeak — the adversary / key-leak harness, as a theorem.

ember's question: *"what happens if someone leaks a private key?"* A dregg key
authorizes capabilities (the macaroon root-key HMAC chain in
`token/src/macaroon_backend.rs`; the pubkey→cell binding `CellId::derive_raw` in
`types/src/lib.rs`). So a leaked key = a **compromised principal** whose held caps an
attacker can now exercise. This file MODELS that adversary and proves its **blast
radius is already bounded by the deployed machinery** — and that **revocation kills it**.

The keystone insight: `Metatheory.Polis.polis_safety` ALREADY quantifies over an
arbitrary, opaque controller (`∀ ctrl`, never inspected — "verify the cage, not the
animal"). A leaked-key attacker IS exactly such a controller: it holds the
compromised principal's caps and drives the system with them. So the blast-radius
bound does NOT need new safety machinery — it is `polis_safety` instantiated with
the attacker as the controller, where the floor is the leaked principal's authority
floor (`held ⊆ bound`, mirroring `cell/src/capability.rs::is_attenuation` /
`granted ⊆ held`).

What this file establishes (all kernel-checked):

  * §1 — THE BLAST RADIUS is the **attenuation-closure** of the leaked principal's
    held caps: every cap the attacker can produce is `is_attenuation`-narrower than
    something the principal already held. The attacker NEVER amplifies
    (`leak_blast_no_amplify`). This is the cap-graph transitive closure, bounded.
  * §2 — THE CONTAINMENT is `polis_safety` re-read as a key-leak theorem: under the
    capability envelope (admit a proposed cap-state iff it stays within the leaked
    principal's authority floor, else shield), NO opaque attacker — holding the
    leaked key — can drive the principal outside its floor
    (`key_leak_contained`). Confinement (`firmament`) and conservation (`Σδ=0`) are
    additional floors that AND into the same shared floor; the proof is uniform.
  * §3 — REVOCATION kills it: the attacker's exercises stop being honored once the
    revocation propagates. We reuse the SHAPE of
    `Dregg2.Distributed.Revocation.eventual_bounded_revocation` (topology-bounded;
    n=1 ⇒ immediate) on the leaked credential (`revoke_kills_leak`,
    `revoke_kills_leak_immediate`).

The honest verdict (developed in `docs/deos/ADVERSARY-KEY-LEAK.md`): the
blast-radius bound and the containment FALL OUT of the deployed proofs. What is
genuinely NEW is only the *naming* — assembling them as one "key-compromise"
theorem — plus the settlement seam (a revoke must bind before settlement; the
Distributed-Houyhnhnm Settlement-Soundness frontier).

Pure Lean 4 core (imports `Metatheory.Polis`); kernel-clean.
-/
import Metatheory.Polis

namespace Metatheory.KeyLeak

open Metatheory.Polis

/-! ## §0. The faithful cap model — mirrors `cell/src/capability.rs`.

A capability is a target cell plus the rights conferred on it. `is_attenuation`
mirrors `cell/src/capability.rs::is_attenuation` (`granted.is_narrower_or_equal(held)`
in `cell/src/permissions.rs`): a granted cap must be narrower-or-equal to the held
one — NEVER an amplification. This is the one load-bearing predicate of the leak. -/

/-- A faithful rights enum (mirrors `Dregg2.Authority.Auth` / `AuthRequired`). Ordered
`read < write < admin`: a numeric tier so "narrower" is decidable. -/
inductive Right | read | write | admin
deriving DecidableEq, Repr

/-- Rights as a tier (`read=0 < write=1 < admin=2`). Narrowing = lowering the tier. -/
def Right.tier : Right → Nat
  | .read => 0
  | .write => 1
  | .admin => 2

/-- A capability: a target cell (a `Nat` id, standing for `CellId`) and the rights it
confers. -/
structure Cap where
  target : Nat
  right  : Right
deriving DecidableEq, Repr

/-- **`isAttenuation held granted`** — mirrors `cell/src/capability.rs::is_attenuation`:
`granted` is admissible from `held` iff it targets the SAME cell and confers
narrower-or-equal rights. NEVER widens the target set, NEVER amplifies rights. -/
def isAttenuation (held granted : Cap) : Prop :=
  granted.target = held.target ∧ granted.right.tier ≤ held.right.tier

instance : DecidableRel isAttenuation := fun h g =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- Attenuation is reflexive (you may re-present what you hold) … -/
theorem isAttenuation.refl (c : Cap) : isAttenuation c c := ⟨Eq.refl _, Nat.le_refl _⟩

/-- … and transitive (a delegate's delegate is still bounded by the root) — this is
the cap-graph transitive closure being a closure. -/
theorem isAttenuation.trans {a b c : Cap}
    (h1 : isAttenuation a b) (h2 : isAttenuation b c) : isAttenuation a c :=
  ⟨h2.1.trans h1.1, Nat.le_trans h2.2 h1.2⟩

/-! ## §1. THE BLAST RADIUS — the attenuation-closure of the leaked principal's caps.

When a key leaks, the attacker gains exactly the caps the principal HELD, and every
cap the attacker can derive (delegate, re-present, narrow) is `isAttenuation`-bounded
by some held cap. The blast radius is this set — and it never escapes the held set's
authority. -/

/-- The leaked principal's held cap-set (its c-list). -/
abbrev CList := List Cap

/-- **`reaches held c`** — `c` is in the BLAST RADIUS of a leaked key holding `held`:
the attacker can produce `c` iff it is an attenuation of SOME held cap. This is the
attenuation-closure (the transitive cap graph; closure-under-`isAttenuation.trans`). -/
def reaches (held : CList) (c : Cap) : Prop := ∃ h ∈ held, isAttenuation h c

instance (held : CList) : DecidablePred (reaches held) := fun c =>
  inferInstanceAs (Decidable (∃ _ ∈ held, _))

/-- The attacker reaches everything the principal actually held (the floor of the
blast radius — what's directly compromised). -/
theorem reaches_held (held : CList) (c : Cap) (hc : c ∈ held) : reaches held c :=
  ⟨c, hc, isAttenuation.refl c⟩

/-- **`leak_blast_no_amplify` — THE BLAST-RADIUS BOUND.** Every cap in the blast
radius confers rights no greater than some held cap, on a cell the principal already
held a cap to. The attacker NEVER amplifies authority and NEVER reaches a new target:
the radius is bounded to the *attenuation-downward-closure* of the c-list. This is
`is_attenuation` (the deployed gate) read as a security theorem. -/
theorem leak_blast_no_amplify (held : CList) (c : Cap) (h : reaches held c) :
    ∃ src ∈ held, c.target = src.target ∧ c.right.tier ≤ src.right.tier := by
  obtain ⟨src, hmem, htgt, hrt⟩ := h
  exact ⟨src, hmem, htgt, hrt⟩

/-- **The closure is closed.** A delegate of something in the blast radius is still in
the blast radius (the attacker delegating onward gains nothing): the transitive cap
graph adds no new authority. -/
theorem reaches_closed (held : CList) {c d : Cap}
    (hc : reaches held c) (hd : isAttenuation c d) : reaches held d := by
  obtain ⟨src, hmem, hsrc⟩ := hc
  exact ⟨src, hmem, isAttenuation.trans hsrc hd⟩

/-- **TOOTH (the radius genuinely bounds).** An `admin` cap on a cell the principal
held only `read` to is NOT in the blast radius — the attacker holding the leaked key
cannot amplify `read` to `admin`. (Mirrors the `is_attenuation` rejection of
amplification.) -/
theorem leak_blast_no_admin_from_read :
    ¬ reaches [⟨7, Right.read⟩] ⟨7, Right.admin⟩ := by
  rintro ⟨src, hmem, _htgt, hrt⟩
  simp only [List.mem_singleton] at hmem
  subst hmem
  simp [Right.tier] at hrt

/-- **TOOTH (no new targets).** A cap on cell `9` is not reachable from a c-list that
only holds caps to cell `7`: the attacker cannot reach cells the principal never had a
cap to. The blast radius is confined to the principal's own target set. -/
theorem leak_blast_no_new_target :
    ¬ reaches [⟨7, Right.admin⟩] ⟨9, Right.read⟩ := by
  rintro ⟨src, hmem, htgt, _⟩
  simp only [List.mem_singleton] at hmem
  subst hmem
  simp at htgt

/-! ## §2. THE CONTAINMENT — `polis_safety`, re-read as a key-leak theorem.

The deployed `polis_safety` quantifies over an opaque controller. The leaked-key
attacker IS that controller. We instantiate the polis cap-state model: the state is
the principal's currently-held c-list; the floor is the authority bound (`held ⊆
bound`, the `dreggFloor` authority leg); the attacker proposes a next c-list and the
envelope admits it iff it stays in the floor, else shields (no-op).

The point: NO new safety argument is needed. The containment is `polis_safety` with
`ctrl := attacker`. Confinement (firmament: the attacker's reachable cells are
bounded to the confined sub-world) and conservation (`Σδ=0`: the attacker cannot mint
value) AND into the same shared floor and the proof is uniform. -/

/-- The leak state: the c-list the (possibly compromised) principal currently holds. -/
abbrev LeakState := CList

/-- **The authority floor** — `held ⊆ bound`: every held cap is an attenuation of a
cap in the principal's exported `bound` (its policy ceiling). This is the polis
`authOK`, faithful to `granted ⊆ held` / `checkSubset`. The leaked-key attacker, no
matter how it drives the c-list, must stay inside this floor or be shielded. -/
def authFloor (bound : CList) : Floor LeakState :=
  fun held => ∀ c ∈ held, reaches bound c

instance (bound : CList) (s : LeakState) : Decidable (authFloor bound s) :=
  inferInstanceAs (Decidable (∀ _ ∈ s, _))

/-- The runtime: the controller PROPOSES the next held c-list. -/
def leakStep (_ : LeakState) (proposed : LeakState) : LeakState := proposed
/-- The shield: refuse the proposal — keep the current c-list (no amplification). -/
def leakShield (s : LeakState) : LeakState := s
/-- Admissible iff the proposed c-list stays inside the authority floor. -/
def leakPol (bound : CList) : Policy LeakState LeakState := fun _ proposed => authFloor bound proposed

theorem leak_sound (bound : CList) : SoundPolicy leakStep (authFloor bound) (leakPol bound) := by
  intro _ a _ ha; exact ha

theorem leak_shieldSafe (bound : CList) :
    ∀ s, authFloor bound s → authFloor bound (leakStep s (leakShield s)) := by
  intro _ hs; exact hs

/-- **`key_leak_contained` — THE CONTAINMENT.** For EVERY opaque attacker holding the
leaked key, and every number of turns, the enveloped system keeps the leaked
principal's authority floor: the attacker can NEVER hold a cap outside the bound. This
is `Metatheory.Polis.polis_safety` with the attacker as the universally-quantified
controller — the blast radius is bounded for free by the deployed proof. -/
theorem key_leak_contained (bound : CList)
    (init : LeakState) (hinit : authFloor bound init) :
    ∀ (attacker : LeakState → LeakState) (n : Nat),
      authFloor bound (traj leakStep (envAct (leakPol bound) leakShield attacker) init n) :=
  polis_safety (leak_sound bound) (leak_shieldSafe bound) hinit

/-- **The attacker is INERT against the floor** (the cap-leak corollary of
`polis_envelope_ctrl_blind`): two different attackers — a naive one and a maximally
adversarial one — are bounded identically. No "how clever is the attacker" question
is load-bearing; possession of the key buys the held caps and NOTHING more. -/
theorem key_leak_attacker_blind (bound : CList)
    (init : LeakState) (hinit : authFloor bound init) (a₁ a₂ : LeakState → LeakState) :
    (∀ n, authFloor bound (traj leakStep (envAct (leakPol bound) leakShield a₁) init n))
      ∧ (∀ n, authFloor bound (traj leakStep (envAct (leakPol bound) leakShield a₂) init n)) :=
  ⟨key_leak_contained bound init hinit a₁, key_leak_contained bound init hinit a₂⟩

/-- **TOOTH (the floor bites the attacker).** An amplification attempt — proposing an
`admin` cap on a cell the bound only allows `read` — is OUTSIDE the floor, so the
envelope SHIELDS it: the attacker's amplified c-list is refused. -/
example : ¬ authFloor [⟨7, Right.read⟩] [⟨7, Right.admin⟩] := by
  intro h
  have := h ⟨7, Right.admin⟩ (List.mem_singleton.mpr rfl)
  exact leak_blast_no_admin_from_read this

/-- **CONFINEMENT as another floor (firmament).** The attacker confined to a
sub-world can only reach cells in that confined target set. We model the firmament
confinement floor as "every held cap targets a confined cell" and show it composes
with the authority floor by intersection — `polis_safety` then bounds BOTH at once
(the `SharedFloor` of authority ∧ confinement ∧ conservation). -/
def confinedFloor (confinedCells : List Nat) : Floor LeakState :=
  fun held => ∀ c ∈ held, c.target ∈ confinedCells

instance (cs : List Nat) (s : LeakState) : Decidable (confinedFloor cs s) :=
  inferInstanceAs (Decidable (∀ _ ∈ s, _))

/-- The combined floor: authority ∧ firmament-confinement (conservation would AND in
identically). The leaked-key attacker is bounded by ALL of them simultaneously — the
uniform `SharedFloor` argument, no per-floor re-proof. -/
def combinedFloor (bound : CList) (confinedCells : List Nat) : Floor LeakState :=
  fun s => authFloor bound s ∧ confinedFloor confinedCells s

instance (bound : CList) (cs : List Nat) (s : LeakState) : Decidable (combinedFloor bound cs s) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem combined_sound (bound : CList) (cs : List Nat) :
    SoundPolicy leakStep (combinedFloor bound cs) (fun _ a => combinedFloor bound cs a) := by
  intro _ a _ ha; exact ha

theorem combined_shieldSafe (bound : CList) (cs : List Nat) :
    ∀ s, combinedFloor bound cs s → combinedFloor bound cs (leakStep s (leakShield s)) := by
  intro _ hs; exact hs

/-- **`key_leak_contained_confined`** — the attacker is bounded by authority AND
firmament confinement at once. A leaked key in a sandboxed PD reaches only its
confined sub-world AND only its attenuated rights. `polis_safety` over the combined
(intersection) floor, for every opaque attacker. -/
theorem key_leak_contained_confined (bound : CList) (cs : List Nat)
    (init : LeakState) (hinit : combinedFloor bound cs init) :
    ∀ (attacker : LeakState → LeakState) (n : Nat),
      combinedFloor bound cs
        (traj leakStep (envAct (fun _ a => combinedFloor bound cs a) leakShield attacker) init n) :=
  polis_safety (combined_sound bound cs) (combined_shieldSafe bound cs) hinit

/-! ## §3. REVOCATION kills the leak — the topology-bounded story.

The leaked key's exercises stop being honored once the leaked credential is revoked
and the revocation propagates. This is the SHAPE of
`Dregg2.Distributed.Revocation.eventual_bounded_revocation` (n=1 ⇒ immediate). We
restate it self-containedly on the leak credential so this harness reads end-to-end;
the full keys-as-caps / `CryptoKernel`-oracle version lives in `Revocation.lean`. -/

/-- A leaked credential id (content-addressed; the macaroon root-key's derived id). -/
abbrev CredId := Nat

/-- A revocation event: the leaked cred, the origin node that revoked it, and the
logical time. Mirrors `Revocation.RevEvent`. -/
structure RevEvent where
  cred : CredId
  origin : Nat
  issuedAt : Nat
deriving DecidableEq, Repr

/-- Worst-case propagation delay (the gossip/consensus bound). `delay m m = 0` is the
single-machine seam. -/
structure Topo where
  delay : Nat → Nat → Nat
  selfDelay : ∀ m, delay m m = 0

/-- Node `n` HONORS the leaked cred at time `t` iff NO logged revocation of it has
propagated to `n` by `t`. (Fail-closed: a propagated revocation forces `false`.) -/
def honors (T : Topo) (log : List RevEvent) (cred : CredId) (n t : Nat) : Bool :=
  log.all (fun e => !(decide (e.cred = cred ∧ e.issuedAt + T.delay e.origin n ≤ t)))

/-- **`revoke_kills_leak` — DISTRIBUTED ⇒ EVENTUAL-BOUNDED.** If the leaked cred was
revoked at origin `m` at time `τ`, then for every node `n` and every `t` at/after the
explicit bound `τ + delay m n`, node `n` does NOT honor the leaked cred: the
attacker's exercises stop being accepted. The bound is the propagation delay; the leak
is contained in *time* as well as in *authority*. -/
theorem revoke_kills_leak (T : Topo) (log : List RevEvent) (cred : CredId) (m τ : Nat)
    (hrev : (⟨cred, m, τ⟩ : RevEvent) ∈ log) (n t : Nat) (hbound : τ + T.delay m n ≤ t) :
    honors T log cred n t = false := by
  unfold honors
  -- the revocation event in the log fails the `all` predicate, so `all = false`.
  apply List.all_eq_false.mpr
  refine ⟨⟨cred, m, τ⟩, hrev, ?_⟩
  have hdec : decide (cred = cred ∧ τ + T.delay m n ≤ t) = true :=
    decide_eq_true (⟨rfl, hbound⟩)
  rw [hdec]; decide

/-- **`revoke_kills_leak_immediate` — SINGLE-MACHINE (n=1) ⇒ IMMEDIATE.** Under
instantaneous propagation (`delay ≡ 0`, the n=1 collapse), the leaked cred is NOT
honored at any `t ≥ τ`: the synchronous revoke kills the leak the instant it lands.
The dregg single-machine principle, on the key-leak. -/
theorem revoke_kills_leak_immediate (T : Topo) (hinst : ∀ m n, T.delay m n = 0)
    (log : List RevEvent) (cred : CredId) (m τ : Nat)
    (hrev : (⟨cred, m, τ⟩ : RevEvent) ∈ log) (n t : Nat) (ht : τ ≤ t) :
    honors T log cred n t = false := by
  apply revoke_kills_leak T log cred m τ hrev n t
  rw [hinst m n, Nat.add_zero]; exact ht

/-! ### The leak, run end-to-end (`#guard`): exercise → contained → revoked. -/

/-- A two-node topology with a `5`-tick cross delay (the stale window). -/
def demoTopo : Topo where
  delay := fun m n => if m = n then 0 else 5
  selfDelay := fun _ => by simp

/-- The leaked cred `42`, revoked at node `0` at time `0`. -/
def demoLog : List RevEvent := [⟨42, 0, 0⟩]

-- Before propagation, node 1 still honors (the distributed stale window — the
-- attacker has a bounded window, NOT unbounded reach):
#guard honors demoTopo demoLog 42 1 4 == true
-- At the bound t=5, node 1 stops honoring (the revoke has propagated):
#guard honors demoTopo demoLog 42 1 5 == false
-- The origin node 0 stops honoring IMMEDIATELY (self-delay 0 — n=1 immediacy):
#guard honors demoTopo demoLog 42 0 0 == false

-- The blast radius bites: read-cap cannot amplify to admin, cannot reach a new cell.
#guard decide (reaches [⟨7, Right.read⟩] ⟨7, Right.read⟩) == true
#guard decide (reaches [⟨7, Right.read⟩] ⟨7, Right.admin⟩) == false
#guard decide (reaches [⟨7, Right.admin⟩] ⟨9, Right.read⟩) == false

/-! ## Axiom hygiene — the keystones inherit `polis_safety`'s kernel-cleanliness. -/

#print axioms leak_blast_no_amplify
#print axioms reaches_closed
#print axioms key_leak_contained
#print axioms key_leak_contained_confined
#print axioms revoke_kills_leak
#print axioms revoke_kills_leak_immediate

/-!
The key-leak stack, in the logic:

  1. BLAST RADIUS = attenuation-closure of held caps — never amplifies, never reaches
     a new target (`leak_blast_no_amplify`, `reaches_closed`). [from `is_attenuation`]
  2. CONTAINMENT = `polis_safety` with the attacker as the opaque controller; the floor
     is the authority bound, AND-composable with firmament confinement and conservation
     (`key_leak_contained`, `key_leak_contained_confined`). [from `polis_safety`]
  3. REVOCATION = topology-bounded; n=1 ⇒ immediate (`revoke_kills_leak`,
     `revoke_kills_leak_immediate`). [from `Revocation.eventual_bounded_revocation`]

The verdict: 1+2+3 are INSTANCES of deployed proofs. The genuinely-new work is the
settlement seam (a revoke must bind into the commitment before settlement) — the
Distributed-Houyhnhnm Settlement-Soundness frontier. See
`docs/deos/ADVERSARY-KEY-LEAK.md`.
-/

end Metatheory.KeyLeak
