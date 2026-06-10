/-
# Dregg2.Circuit.Spec.sealpaircreation — INDEPENDENT full-state spec + executor⟺spec for the
  dregg2 seal-pair-creation effect family (`createSealPairA`).

This leaf module is the `Transfer.lean` reference pattern (`TransferSpec` + `recKExec_iff_spec` +
`recTransfer_correct`) carried to the ONE seal-pair-creation arm of `execFullA`:

  * `createSealPairA pid actor sealerHolder unsealerHolder`
      ⟶ `createSealPairChainA s pid actor sealerHolder unsealerHolder`
      — the Wave-3 DE-SHADOWED `apply_create_seal_pair` (`apply.rs:2675`). GATED on `actor` holding
        authority over `sealerHolder` (`stateAuthB s.kernel.caps actor sealerHolder`, the writer of
        the pair). On commit it performs TWO REAL c-list grants — the sealer cap `sealerCap pid`
        (`Cap.endpoint pid [Auth.grant]`) to `sealerHolder`, AND the unsealer cap `unsealerCap pid`
        (`Cap.endpoint pid [Auth.reply]`) to `unsealerHolder` (`grant_with_breadstuff`,
        `apply.rs:2705`/`:2725`) — and prepends a receipt to the log. Fail-closed (no authority over
        `sealerHolder` ⇒ `none`). bal-NEUTRAL (edits `caps`, never `bal`).

We state an INDEPENDENT declarative full-state spec — the admissibility guard ∧ the EXACT post-state
on the touched components (`kernel.caps` (the double grant) + `log`) ∧ EVERY OTHER `RecChainedState`
field LITERALLY unchanged (the FRAME). `RecChainedState` has TWO fields: `kernel : RecordKernelState`
and `log : List Turn`. The kernel has SEVENTEEN fields — `accounts cell caps escrows nullifiers
revoked commitments bal queues swiss slotCaveats factories lifecycle deathCert delegate delegations
sealedBoxes` — so the FRAME enumerates the SIXTEEN non-`caps` kernel fields plus the kernel↔kernel
`caps` rewrite, plus the `log` head-cons. NO frame clause names the executor
(`execFullA`/`createSealPairChainA`); the post-`caps` clause uses only the PURE cap helpers
(`grant`/`sealerCap`/`unsealerCap`), so the spec is genuinely independent of the executor it validates.

The `→` direction of `createSealPair_iff_spec` VALIDATES the arm against the independent spec: all 17
kernel fields + the log are checked, so had the arm silently mutated `bal`/`nullifiers`/`revoked`/…
a frame clause would make the proof FAIL. (None do — see `frameGaps` in the run report.)

⚑ FRAME NOTE (a surfaced executor-shape fact, NOT a bug): the task brief listed
`kernel.sealedBoxes (pid entry created)` as a rewrite of this arm. The EXECUTOR
(`createSealPairChainA`, `TurnExecutorFull.lean:1828`) does NOT touch `sealedBoxes` — it ONLY grants
the two caps. (`sealedBoxes` is inserted by `seal` / read by `unseal`, NOT by pair-creation: a freshly
created pair has no boxes yet.) The spec correctly FRAMES `sealedBoxes` as UNCHANGED, and the `↔`
proof goes through, CONFIRMING the executor does not silently mutate it. This is recorded in
`frameGaps` as a brief↔executor discrepancy (the brief over-described the rewrite set), not a missing
frame clause.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.SealPairCreation

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth Label)

/-! ## §1 — the admissibility guard + the cap-update validation lemma.

`execFullA s (.createSealPairA pid actor sealerHolder unsealerHolder)
  = createSealPairChainA s pid actor sealerHolder unsealerHolder`, which is

    if stateAuthB s.kernel.caps actor sealerHolder = true then
      some { kernel := { s.kernel with
                          caps := grant (grant s.kernel.caps sealerHolder (sealerCap pid))
                                        unsealerHolder (unsealerCap pid) },
             log    := { actor := actor, src := sealerHolder, dst := sealerHolder, amt := 0 }
                       :: s.log }
    else none

so the arm commits IFF `actor` holds authority over `sealerHolder`, rewriting ONLY `k.caps` (to the
double grant) and prepending the receipt. -/

/-- **The admissibility guard `createSealPairA` checks**, as a `Prop`: `actor` holds authority over
`sealerHolder` (the writer of the pair — `apply_create_seal_pair`'s `stateAuthB` over the sealer
slot). Stated INDEPENDENTLY (over the pre-state's `caps`), NOT by referencing the executor. -/
def CreateSealPairGuard (s : RecChainedState) (actor sealerHolder : CellId) : Prop :=
  EffectsState.stateAuthB s.kernel.caps actor sealerHolder = true

/-- The exact log receipt a committed `createSealPairA` prepends (the writer of the pair acting on
`sealerHolder`; bal `0` — generative, bal-neutral). Stated as the literal `Turn`, NOT via the
executor, so the spec's `log` clause stays executor-independent. -/
def createSealPairReceipt (actor sealerHolder : CellId) : Turn :=
  { actor := actor, src := sealerHolder, dst := sealerHolder, amt := 0 }

/-- The pure double-grant the arm applies to `caps`: grant the sealer cap to `sealerHolder`, then the
unsealer cap to `unsealerHolder`. Named so the spec's `caps` clause is a single pure expression. -/
def createSealPairCaps (caps : Caps) (pid : Nat) (sealerHolder unsealerHolder : CellId) : Caps :=
  grant (grant caps sealerHolder (sealerCap pid)) unsealerHolder (unsealerCap pid)

/-- **`createSealPairCaps_correct`** — the cap-update helper validated DECLARATIVELY (the
`recTransfer_correct` analog), for the DISTINCT-holder case (`sealerHolder ≠ unsealerHolder`, the
dregg1 keypair shape). The pure double grant:
  (a) puts `sealerCap pid` in `sealerHolder`'s slot — a HELD cap conferring the seal authority for
      `pid` (`holdsSealCapFor pid (sealerCap pid) = true`);
  (b) puts `unsealerCap pid` in `unsealerHolder`'s slot — a HELD cap conferring the unseal authority
      for `pid` (`holdsSealCapFor pid (unsealerCap pid) = true`);
  (c) leaves the two granted caps GENUINELY DISTINCT (`sealerCap pid ≠ unsealerCap pid`: their
      conferred rights are `[grant]` vs `[reply]` — a real keypair, not one cap twice);
  (d) leaves EVERY OTHER holder's slot (≠ `sealerHolder`, ≠ `unsealerHolder`) LITERALLY untouched.
So the spec's `… = createSealPairCaps …` clause genuinely encodes two-real-distinct-grants ∧
slot-frame, rather than blindly trusting the helper. -/
theorem createSealPairCaps_correct (caps : Caps) (pid : Nat) (sealerHolder unsealerHolder : CellId)
    (hne : sealerHolder ≠ unsealerHolder) :
    (sealerCap pid ∈ createSealPairCaps caps pid sealerHolder unsealerHolder sealerHolder)
    ∧ (unsealerCap pid ∈ createSealPairCaps caps pid sealerHolder unsealerHolder unsealerHolder)
    ∧ holdsSealCapFor pid (sealerCap pid) = true
    ∧ holdsSealCapFor pid (unsealerCap pid) = true
    ∧ sealerCap pid ≠ unsealerCap pid
    ∧ (∀ h, h ≠ sealerHolder → h ≠ unsealerHolder →
        createSealPairCaps caps pid sealerHolder unsealerHolder h = caps h) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `sealerHolder`'s slot: the outer grant misses it (`sealerHolder ≠ unsealerHolder`), the inner
    -- grant prepends `sealerCap pid`.
    unfold createSealPairCaps grant
    rw [if_neg hne, if_pos rfl]
    exact List.mem_cons_self
  · -- `unsealerHolder`'s slot: the outer grant prepends `unsealerCap pid`.
    unfold createSealPairCaps grant
    rw [if_pos rfl]
    exact List.mem_cons_self
  · -- the sealer cap really confers the seal authority for `pid`.
    unfold holdsSealCapFor sealerCap; simp
  · -- the unsealer cap really confers the unseal authority for `pid`.
    unfold holdsSealCapFor unsealerCap; simp
  · -- the two granted caps are genuinely distinct (different rights lists ⇒ different endpoints).
    unfold sealerCap unsealerCap; simp
  · -- a holder that is neither recipient is unchanged by both grants.
    intro h hhs hhu
    unfold createSealPairCaps grant
    rw [if_neg hhu, if_neg hhs]

/-- **The full-state declarative spec of a committed `createSealPairA`** — the INDEPENDENT reference
semantics. The guard holds; the post-state's `kernel.caps` is the pure double grant (see
`createSealPairCaps_correct`); the log gains exactly the receipt; and every one of the SIXTEEN
non-`caps` kernel fields is unchanged. No frame clause mentions the executor. NOTE the FRAME includes
`sealedBoxes = sealedBoxes` — pair-creation creates NO box (only `seal` does), so a freshly created
pair leaves the box store untouched; the `↔` below confirms the executor agrees. -/
def CreateSealPairSpec (s : RecChainedState) (pid : Nat) (actor sealerHolder unsealerHolder : CellId)
    (s' : RecChainedState) : Prop :=
  CreateSealPairGuard s actor sealerHolder
  ∧ s'.kernel.caps = createSealPairCaps s.kernel.caps pid sealerHolder unsealerHolder
  ∧ s'.log = createSealPairReceipt actor sealerHolder :: s.log
  -- THE FRAME: the sixteen non-`caps` kernel fields, all LITERALLY unchanged.
  ∧ s'.kernel.accounts = s.kernel.accounts
  ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.queues = s.kernel.queues
  ∧ s'.kernel.swiss = s.kernel.swiss
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt

/-- **`createSealPair_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The full executor
`execFullA` commits a `createSealPairA pid actor sealerHolder unsealerHolder` into `s'` IFF `s'` is
EXACTLY the spec'd full post-state. The `→` direction VALIDATES the arm against the independent spec —
all 17 kernel fields + the log are checked, so had the arm silently mutated `bal`/`nullifiers`/
`sealedBoxes`/… the corresponding frame clause would make this proof FAIL; the `←` reconstructs the
committed state from the spec. This is the executor corner of the spec⟺executor⟺circuit triangle. -/
theorem createSealPair_iff_spec (s : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) (s' : RecChainedState) :
    execFullA s (.createSealPairA pid actor sealerHolder unsealerHolder) = some s'
      ↔ CreateSealPairSpec s pid actor sealerHolder unsealerHolder s' := by
  unfold CreateSealPairSpec CreateSealPairGuard createSealPairCaps createSealPairReceipt
  simp only [execFullA, createSealPairChainA]
  by_cases hg : EffectsState.stateAuthB s.kernel.caps actor sealerHolder = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hcaps, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
      -- reconstruct `s'` from its (kernel field-by-field) + log spec.
      obtain ⟨k', log'⟩ := s'
      obtain ⟨acc, cell, caps, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb, dge, dgea⟩ := k'
      simp only at hcaps hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      subst hcaps hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §2 — corollaries read off the spec (the headline cap-movement + bal-neutrality facts).

The point of seal-pair-creation is that it installs a REAL sealer/unsealer keypair (two distinct held
caps) and moves no value. These corollaries extract that from the executor⟺spec equivalence (so they
hold of the REAL committed step). -/

/-- **`createSealPair_spec_grants_keypair`** — from a committed `createSealPairA` over DISTINCT
holders, `sealerHolder` HOLDS the sealer cap and `unsealerHolder` HOLDS the unsealer cap in the
post-state, the two caps confer the seal/unseal authority for `pid`, and they are GENUINELY DISTINCT.
Read off the spec's `caps` clause (which the committed step pins via `createSealPair_iff_spec`) +
`createSealPairCaps_correct`. A flag-flip could NEVER witness this. -/
theorem createSealPair_spec_grants_keypair (s : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) (s' : RecChainedState)
    (hne : sealerHolder ≠ unsealerHolder)
    (h : execFullA s (.createSealPairA pid actor sealerHolder unsealerHolder) = some s') :
    sealerCap pid ∈ s'.kernel.caps sealerHolder
    ∧ unsealerCap pid ∈ s'.kernel.caps unsealerHolder
    ∧ holdsSealCapFor pid (sealerCap pid) = true
    ∧ holdsSealCapFor pid (unsealerCap pid) = true
    ∧ sealerCap pid ≠ unsealerCap pid := by
  have hspec := (createSealPair_iff_spec s pid actor sealerHolder unsealerHolder s').mp h
  have hcaps : s'.kernel.caps
      = createSealPairCaps s.kernel.caps pid sealerHolder unsealerHolder := hspec.2.1
  obtain ⟨hms, hmu, hhs, hhu, hdne, _⟩ :=
    createSealPairCaps_correct s.kernel.caps pid sealerHolder unsealerHolder hne
  exact ⟨by rw [hcaps]; exact hms, by rw [hcaps]; exact hmu, hhs, hhu, hdne⟩

/-- **`createSealPair_spec_frames_others`** — from a committed `createSealPairA` over DISTINCT
holders, every OTHER holder's cap slot (≠ both recipients) is LITERALLY unchanged: the grant is
LOCAL, no third party's authority is touched. Read off the spec's `caps` clause +
`createSealPairCaps_correct`. -/
theorem createSealPair_spec_frames_others (s : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder h0 : CellId) (s' : RecChainedState)
    (hne : sealerHolder ≠ unsealerHolder)
    (hh : execFullA s (.createSealPairA pid actor sealerHolder unsealerHolder) = some s')
    (h0s : h0 ≠ sealerHolder) (h0u : h0 ≠ unsealerHolder) :
    s'.kernel.caps h0 = s.kernel.caps h0 := by
  have hspec := (createSealPair_iff_spec s pid actor sealerHolder unsealerHolder s').mp hh
  have hcaps : s'.kernel.caps
      = createSealPairCaps s.kernel.caps pid sealerHolder unsealerHolder := hspec.2.1
  obtain ⟨_, _, _, _, _, hframe⟩ :=
    createSealPairCaps_correct s.kernel.caps pid sealerHolder unsealerHolder hne
  rw [hcaps]; exact hframe h0 h0s h0u

/-- **`createSealPair_spec_balance_neutral`** — from a committed `createSealPairA`, the per-asset
ledger `bal` and the live-account set are UNCHANGED (the family is `caps`-only ⇒ conservation-trivial,
bal-NEUTRAL). Read directly off the spec's frame clauses — INCLUDING `sealedBoxes` (untouched: a fresh
pair has no box). -/
theorem createSealPair_spec_balance_neutral (s : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) (s' : RecChainedState)
    (h : execFullA s (.createSealPairA pid actor sealerHolder unsealerHolder) = some s') :
    s'.kernel.bal = s.kernel.bal
    ∧ s'.kernel.accounts = s.kernel.accounts
    ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes
    ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
    ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt := by
  have hspec := (createSealPair_iff_spec s pid actor sealerHolder unsealerHolder s').mp h
  exact ⟨hspec.2.2.2.2.2.2.2.2.1, hspec.2.2.2.1,
         hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## §3 — non-vacuity: the gate is REAL (an unauthorized pair-create is REJECTED).

A `createSealPairA` whose `actor` holds NO authority over `sealerHolder` (`CreateSealPairGuard` fails)
makes `execFullA` return `none` — the unauthorized pair-create cannot commit. This is the soundness
content (matching `Transfer.lean`'s `rejects_unauthorized`): the spec is worthless if it accepted bad
inputs. -/

/-- **`createSealPair_rejects_unauthorized` — PROVED.** A `createSealPairA` over a pre-state where the
`actor` holds NO authority over `sealerHolder` (`¬ CreateSealPairGuard`) is REJECTED by the executor
(`= none`): no `s'` is produced. An unauthorized pair-create cannot commit. -/
theorem createSealPair_rejects_unauthorized (s : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId)
    (hbad : ¬ CreateSealPairGuard s actor sealerHolder) :
    execFullA s (.createSealPairA pid actor sealerHolder unsealerHolder) = none := by
  unfold CreateSealPairGuard at hbad
  simp only [execFullA, createSealPairChainA]
  rw [if_neg hbad]

/-- **`createSealPair_no_spec_when_unauthorized` — corollary.** When the guard fails, NO post-state
satisfies the spec via the executor (the `↔` collapses to `none = some s'`, impossible). -/
theorem createSealPair_no_spec_when_unauthorized (s : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId) (s' : RecChainedState)
    (hbad : ¬ CreateSealPairGuard s actor sealerHolder) :
    ¬ execFullA s (.createSealPairA pid actor sealerHolder unsealerHolder) = some s' := by
  rw [createSealPair_rejects_unauthorized s pid actor sealerHolder unsealerHolder hbad]; simp

/-! ## §4 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms createSealPairCaps_correct
#assert_axioms createSealPair_iff_spec
#assert_axioms createSealPair_spec_grants_keypair
#assert_axioms createSealPair_spec_frames_others
#assert_axioms createSealPair_spec_balance_neutral
#assert_axioms createSealPair_rejects_unauthorized
#assert_axioms createSealPair_no_spec_when_unauthorized

end Dregg2.Circuit.Spec.SealPairCreation
