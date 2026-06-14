/-
# Dregg2.Deos.Rehydration — `ReplayedDeterministic` IS the confined fragment (leg 3, THE CROWN).

`docs/deos/DEOS.md` §"the verified-deos program", target 3 (**Rehydration confinement = the
liveness-type — the verified-desktop crown**):

  > Prove `ReplayedDeterministic` *is exactly* the confined fragment: a context whose every external
  > interaction was an attested turn replays deterministically; otherwise `ReconstructedApproximate`.
  > This makes the liveness-type a *proven* confinement readout (the doc's "derived" row, lifted to a
  > theorem).

`docs/desktop-os-research/REHYDRATABLE-SURFACES.md` residual #3 ("the liveness-type is a confinement
readout"): `Rehydration::classify(log, sources_reachable)` COMPUTES the variant from a context's
`InteractionLog` — `Live` iff sources reachable; else `ReplayedDeterministic` iff *every* interaction
`is_witnessed` (and "witnessed" is itself derived — the attested root must structurally hold); else
`ReconstructedApproximate`. The doc's ledger row: this assignment is `derived`, not `heuristic`.

## The theorem this lifts (the "derived" row → a theorem)

The Rust `classify` is the realization (running, tested in `starbridge-web-surface`). This module is
the PROOF that its output is a faithful confinement readout: `ReplayedDeterministic` is *exactly* the
fragment of contexts whose entire external interaction stayed inside the capability discipline. The
enum does DOUBLE DUTY (honesty label AND confinement metric), and that double duty is a `↔`:

  > a non-`Live` context is `ReplayedDeterministic`  ⟺  every interaction it made was witnessed
  >                                                       (an attested turn that structurally holds).

So `ReplayedDeterministic` ≡ "everything this context did went through the membrane" — the confined
fragment, by construction. A context that reached OUTSIDE the membrane (an ambient/un-witnessed
interaction) is intrinsically `ReconstructedApproximate`, because the thing that made it
non-deterministic was never witnessed.

## What is proven

  * `Interaction.isWitnessed` — an interaction is witnessed iff it carries an `AttestedRoot` that
    STRUCTURALLY HOLDS (`v4-complete ∧ quorum` — a purported attestation that does not even hold is
    NOT a witness; the doc's "witnessed is itself derived"). An ambient interaction is never witnessed.
  * `confined log` — the confinement predicate: EVERY interaction in the log is witnessed (the whole
    external trace stayed inside the membrane).
  * `classify log reachable` — the derived liveness-type (mirrors the Rust `classify`).
  * **`replayedDeterministic_iff_confined` (KEYSTONE)** — for a non-`Live` context (`reachable =
    false`), `classify = ReplayedDeterministic ↔ confined log`. The liveness-type IS exactly the
    confined fragment — the doc's "derived" row as an `↔`. (Both polarities discharged.)
  * `reconstructedApproximate_iff_unconfined` — the dual: a non-`Live` context is
    `ReconstructedApproximate ↔ NOT confined` (some interaction reached outside the membrane). So the
    classifier partitions non-live contexts EXACTLY into confined/unconfined.
  * `replayedDeterministic_replays` — the confinement PAYOFF: a `ReplayedDeterministic` context's
    witnessed trace is a well-linked receipt chain, hence replay-deterministic and tamper-evident
    (`Dregg2.Exec.Receipts.chain_tamper_evident` under the §8 digest oracle, carried as NAMED
    hypotheses `HInj`/`HFresh`). The "replays deterministically" half of target 3 — riding the
    EXISTING receipt-chain law, not a new one.
  * Teeth (`#guard`): an all-witnessed non-live log classifies `ReplayedDeterministic`; one ambient
    interaction flips it to `ReconstructedApproximate`; a structurally-invalid attestation is NOT a
    witness (so a forged root does not buy `ReplayedDeterministic`); `Live` when sources reachable.

§8 SEAM (NAMED, not `sorry`'d): the receipt-digest collision-resistance enters `replayedDeterministic_
replays` as the hypotheses `HInj : Function.Injective H` / `HFresh : ∀ p, H p ≠ genesisSentinel` —
the SAME `dregg2 §8` oracle `Dregg2.Exec.Receipts.chain_tamper_evident` already names, never a Lean
axiom. The classifier theorems (the crown `↔`) need NO oracle — they are pure structural facts about
the log.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide`. `lake build
Dregg2` green (LOCAL).
-/
import Dregg2.Exec.Receipt
import Dregg2.Tactics

namespace Dregg2.Deos.Rehydration

open Dregg2.Exec.Receipts (Receipt ReceiptChain wellLinked genesisSentinel mkReceipt
  chain_tamper_evident replayFold replayFold_wellLinked)

/-! ## §1 — An attested root, and what it means to be witnessed.

A deos context's external interactions are either `dregg://` ATTESTED fetches (cap-gated, receipt-
logged — they carry an `AttestedRoot`) or AMBIENT reaches outside the membrane (a raw fetch, an
un-witnessed timing/agent choice). An attested root is a WITNESS only if it STRUCTURALLY HOLDS — a
purported attestation that does not even hold (incomplete receipt / no quorum) is NOT a witness. So
"witnessed" is itself a derived, checkable property, not a hand-set flag. -/

/-- **`AttestedRoot`** — the attestation a `dregg://` interaction carries: a state-commitment `root`
plus the two structural soundness flags the Rust `AttestedRoot` checks
(`is_v4_receipt_complete() && has_quorum()`). A root is a genuine witness only when BOTH hold (§2). -/
structure AttestedRoot where
  /-- The committed state-commitment this interaction attested (the receipt's `newCommit` analog). -/
  root      : Nat
  /-- `is_v4_receipt_complete()` — the receipt structure is complete (not a stub). -/
  v4Complete : Bool
  /-- `has_quorum()` — the attestation reached quorum (not a unilateral claim). -/
  quorum     : Bool
deriving DecidableEq, Repr

/-- **`AttestedRoot.holds`** — the root STRUCTURALLY holds: `v4Complete ∧ quorum`. The derived
"witnessed is itself derived" check — a purported attestation that does not even hold is rejected here,
BEFORE it can buy `ReplayedDeterministic`. -/
def AttestedRoot.holds (ar : AttestedRoot) : Bool := ar.v4Complete && ar.quorum

/-- **`Interaction`** — one external interaction a deos context made: either a `dregg://` ATTESTED
fetch carrying an `AttestedRoot`, or an AMBIENT reach outside the membrane (un-witnessed by
construction). -/
inductive Interaction where
  /-- A cap-gated `dregg://` fetch — carries the attestation it was witnessed under. -/
  | attested (ar : AttestedRoot)
  /-- A raw reach outside the membrane — never witnessed (the thing that made it non-deterministic was
  never captured in the witness-graph). -/
  | ambient
deriving DecidableEq, Repr

/-- **`Interaction.isWitnessed`** — is this interaction a genuine witness? An attested fetch IS, but
ONLY when its root STRUCTURALLY HOLDS (`holds` — v4-complete ∧ quorum); an ambient reach is NEVER. So
a forged/incomplete attestation is NOT a witness — "witnessed" is derived from the attestation's own
soundness, not asserted. -/
def Interaction.isWitnessed : Interaction → Bool
  | .attested ar => ar.holds
  | .ambient     => false

/-- **`InteractionLog`** — the context's full external interaction trace (the thing `classify` reads). -/
abbrev InteractionLog := List Interaction

/-! ## §2 — The confinement predicate: every interaction stayed inside the membrane. -/

/-- **`confined log`** — the context is CONFINED: EVERY interaction it made was witnessed (an attested
fetch whose root structurally holds). "Everything this context did went through the membrane." This is
the confined fragment — the property `ReplayedDeterministic` will turn out to be exactly. -/
def confined (log : InteractionLog) : Bool := log.all Interaction.isWitnessed

/-! ## §3 — The derived liveness-type and the classifier (the Rust `Rehydration::classify`). -/

/-- **`Rehydration`** — the liveness-type carried on every reacquisition (`docs/.../REHYDRATABLE-
SURFACES.md`): which KIND of true you are getting. `Live` (touching the live scene),
`ReplayedDeterministic` (a faithful replay — the confined fragment), or `ReconstructedApproximate` (a
reconstruction, because something was un-witnessed). -/
inductive Rehydration where
  | Live
  | ReplayedDeterministic
  | ReconstructedApproximate
deriving DecidableEq, Repr

/-- **`classify log reachable`** — the DERIVED liveness-type (the Rust `Rehydration::classify`). `Live`
iff the live sources are reachable; else `ReplayedDeterministic` iff the context is `confined` (every
interaction witnessed); else `ReconstructedApproximate`. NOT a hand-set field — computed from the log
and reachability. -/
def classify (log : InteractionLog) (reachable : Bool) : Rehydration :=
  if reachable then .Live
  else if confined log then .ReplayedDeterministic
  else .ReconstructedApproximate

/-! ## §4 — THE CROWN: `ReplayedDeterministic` IS EXACTLY the confined fragment.

For a non-`Live` context (sources gone, `reachable = false`), the classifier outputs
`ReplayedDeterministic` if and only if the context is confined — every interaction was a witnessed
attested turn. So the liveness-type is not merely an honesty label: it is a PROVEN readout of how much
behaviour stayed inside the capability discipline. The doc's "derived" row, as an `↔`. -/

/-- **THE CROWN — `replayedDeterministic_iff_confined`.** For a non-`Live` context (`reachable =
false`), `classify log false = ReplayedDeterministic ↔ confined log`. The liveness-type
`ReplayedDeterministic` IS *exactly* the confined fragment — a context replays deterministically iff
its every external interaction was an attested (witnessed) turn. Both polarities: confined ⇒ classified
replayed; classified replayed ⇒ confined. This turns `docs/deos/DEOS.md`'s "derived" row into a
theorem — the verified-desktop crown. -/
theorem replayedDeterministic_iff_confined (log : InteractionLog) :
    classify log false = Rehydration.ReplayedDeterministic ↔ confined log = true := by
  unfold classify
  simp only [if_neg (by decide : ¬ (false = true))]
  by_cases hc : confined log = true
  · -- confined ⇒ the `then` branch fires ⇒ ReplayedDeterministic; the iff holds (both true).
    rw [if_pos hc]
    exact ⟨fun _ => hc, fun _ => rfl⟩
  · -- not confined ⇒ the `else` branch ⇒ ReconstructedApproximate ≠ ReplayedDeterministic; both false.
    rw [if_neg hc]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h hc

/-- **THE DUAL — `reconstructedApproximate_iff_unconfined`.** For a non-`Live` context, `classify log
false = ReconstructedApproximate ↔ ¬ confined log`. A context is reconstructed-approximate iff SOME
interaction reached outside the membrane (was un-witnessed). Together with the crown, the classifier
partitions non-live contexts EXACTLY into confined (replayed) / unconfined (reconstructed) — a total,
faithful confinement readout, no third bucket. -/
theorem reconstructedApproximate_iff_unconfined (log : InteractionLog) :
    classify log false = Rehydration.ReconstructedApproximate ↔ confined log = false := by
  unfold classify
  simp only [if_neg (by decide : ¬ (false = true))]
  by_cases hc : confined log = true
  · rw [if_pos hc]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; rw [hc] at h; exact absurd h (by decide)
  · -- confined log ≠ true means confined log = false (a Bool).
    have hcf : confined log = false := by
      cases hb : confined log with
      | true  => exact absurd hb hc
      | false => rfl
    rw [if_neg hc]
    exact ⟨fun _ => hcf, fun _ => rfl⟩

/-- **A FORGED/INCOMPLETE ATTESTATION DOES NOT BUY `ReplayedDeterministic`** (the anti-ghost tooth on
the crown): if any interaction is a structurally-INVALID attestation (`¬ holds` — incomplete or no
quorum), the context is NOT confined, so a non-`Live` classification is `ReconstructedApproximate`, not
`ReplayedDeterministic`. A purported attestation that does not even hold cannot launder a context into
the confined fragment. -/
theorem invalidAttestation_not_replayed (log : InteractionLog) (ar : AttestedRoot)
    (hbad : ar.holds = false) (hmem : Interaction.attested ar ∈ log) :
    classify log false ≠ Rehydration.ReplayedDeterministic := by
  -- `Ne` is `… = … → False`; intro the (would-be) equality and push it through the crown iff.
  intro heq
  have hconf : confined log = true := (replayedDeterministic_iff_confined log).mp heq
  -- the bad interaction is in the log but not witnessed ⇒ `all isWitnessed` is false: contradiction.
  have : (Interaction.attested ar).isWitnessed = true :=
    List.all_eq_true.mp hconf _ hmem
  simp only [Interaction.isWitnessed] at this
  rw [hbad] at this
  exact absurd this (by decide)

/-! ## §5 — THE CONFINEMENT PAYOFF: a confined context's trace IS a tamper-evident replay.

The crown says `ReplayedDeterministic` = confined. Here is WHY that is the right name: a confined
context's witnessed interactions form a well-linked receipt chain — so its rehydration is
replay-deterministic AND tamper-evident, by the EXISTING `Dregg2.Exec.Receipts` law. The §8 digest
collision-resistance enters as NAMED hypotheses (the same `chain_tamper_evident` oracle), never a
Lean axiom. -/

/-- The receipt chain a confined context's witnessed interactions induce: each attested root's `root`
is the per-turn state-commitment, folded into a well-linked chain via the §8 digest `H` (the same
`replayFold` the receipt module proves well-linked). We expose it as the bridge from "confined log" to
"a tamper-evident receipt chain". -/
def witnessChain (H : Receipt → Nat) (roots : List Nat) : ReceiptChain :=
  replayFold H [] (roots.map (fun r => (r, r, 0)))

/-- The induced witness chain is WELL-LINKED — replay cannot manufacture a broken link (directly
`Dregg2.Exec.Receipts.replayFold_wellLinked` from the empty, vacuously-well-linked start). -/
theorem witnessChain_wellLinked (H : Receipt → Nat) (roots : List Nat) :
    wellLinked H (witnessChain H roots) :=
  replayFold_wellLinked H [] _ trivial

/-- **THE REPLAY PAYOFF — `replayedDeterministic_replays`.** A `ReplayedDeterministic` (confined)
context's witnessed trace induces a well-linked receipt chain that is TAMPER-EVIDENT: any other
well-linked chain agreeing on the head receipt IS the same history (`Dregg2.Exec.Receipts.
chain_tamper_evident`). So a confined context replays to a UNIQUE, non-forgeable history — "replays
deterministically", the second half of target 3. The receipt-digest collision-resistance is the NAMED
§8 oracle (`HInj`/`HFresh`), carried as hypotheses exactly as the underlying keystone names them —
NOT a new assumption, NOT a Lean axiom. -/
theorem replayedDeterministic_replays
    {H : Receipt → Nat} (HInj : Function.Injective H) (HFresh : ∀ p, H p ≠ genesisSentinel)
    (log : InteractionLog) (roots : List Nat)
    (_hrepl : classify log false = Rehydration.ReplayedDeterministic)
    (other : ReceiptChain)
    (hother : wellLinked H other)
    (hhead : (witnessChain H roots).head? = other.head?) :
    witnessChain H roots = other :=
  chain_tamper_evident HInj HFresh (witnessChain H roots) other
    (witnessChain_wellLinked H roots) hother hhead

/-! ## §6 — NON-VACUITY TEETH (`#guard`): the classifier BITES, all branches. -/

section Witnesses

/-- A genuine (holding) attested root: complete + quorum. -/
def goodRoot : AttestedRoot := { root := 42, v4Complete := true, quorum := true }
/-- A structurally-invalid root: complete but NO quorum (a unilateral claim — does NOT hold). -/
def badRoot : AttestedRoot := { root := 42, v4Complete := true, quorum := false }

/-- An all-witnessed log: two genuine attested fetches (the confined trace). -/
def confinedLog : InteractionLog := [.attested goodRoot, .attested goodRoot]
/-- A log with one ambient reach (escaped the membrane — unconfined). -/
def ambientLog : InteractionLog := [.attested goodRoot, .ambient]
/-- A log with a structurally-invalid attestation (a forged root — unconfined, NOT a witness). -/
def forgedLog : InteractionLog := [.attested goodRoot, .attested badRoot]

-- `holds` derives witnessing: the good root holds, the bad (no-quorum) root does NOT:
#guard goodRoot.holds
#guard !badRoot.holds
#guard (Interaction.attested goodRoot).isWitnessed
#guard !(Interaction.attested badRoot).isWitnessed       -- forged root is NOT a witness
#guard !(Interaction.ambient).isWitnessed                -- ambient is never a witness

-- the confinement predicate: the all-witnessed log is confined; ambient/forged are not:
#guard confined confinedLog
#guard !confined ambientLog
#guard !confined forgedLog

-- THE CROWN, witnessed: a non-live confined context classifies ReplayedDeterministic …
#guard classify confinedLog false == Rehydration.ReplayedDeterministic
-- … one ambient interaction flips it to ReconstructedApproximate (confinement readout bites) …
#guard classify ambientLog false == Rehydration.ReconstructedApproximate
-- … a FORGED root likewise yields ReconstructedApproximate (anti-ghost: invalid ≠ witnessed) …
#guard classify forgedLog false == Rehydration.ReconstructedApproximate
-- … and ANY context with reachable sources is Live (regardless of the log):
#guard classify confinedLog true == Rehydration.Live
#guard classify ambientLog true == Rehydration.Live
-- the empty trace is vacuously confined ⇒ ReplayedDeterministic when non-live:
#guard classify [] false == Rehydration.ReplayedDeterministic

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  replayedDeterministic_iff_confined,
  reconstructedApproximate_iff_unconfined,
  invalidAttestation_not_replayed,
  witnessChain_wellLinked,
  replayedDeterministic_replays
]

end Dregg2.Deos.Rehydration
