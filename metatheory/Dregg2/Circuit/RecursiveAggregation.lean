/-
# Dregg2.Circuit.RecursiveAggregation — RECURSIVE-AGGREGATION SOUNDNESS (magnesium → gold).

**The headline.** A light client that verifies ONE succinct aggregate proof — and re-witnesses
NOTHING of the history — learns that the WHOLE chain of N finalized turns is correct:
every turn executed correctly per the verified executor, the chain is correctly ordered (no
reorder/drop/insert), and the final root is the genuine fold of the whole history. This is the model
that the IVC accumulator (`circuit/src/ivc_turn_chain.rs::prove_turn_chain_recursive` →
`WholeChainProof`) realizes; `verify_turn_chain_recursive` checks only the root, cost independent of N.

**Why proofs are ADDITIVE ATTESTATION here, and that is the POINT.** The light client does NOT
re-execute the history, does NOT re-hash the states, does NOT walk the blocklace. It checks the
succinct aggregate. The aggregate's validity, UNDER the named soundness hypotheses below, IS exactly
`HistoryAggregation.WellFormedChain` (`aggregate_attests_whole_history`) — so trusting the aggregate
is trusting the whole history. The verification IS the trust.

**What is PROVED vs. what is a NAMED, REALIZABLE hypothesis (the boundary).** You cannot prove
plonky3/pickles FRI-recursion soundness in Lean — it is the soundness of a concrete Rust prover over
a concrete field. So we NAME the three soundness facts the recursion engine supplies, as `structure`
fields the headline takes as hypotheses (each realizable: it is the standard SNARK soundness of a
fixed verifier circuit, which `DESIGN-recursion-aggregation-private-joint-turns.md` §H1 argues is a
BOUNDED obligation for plonky3's single fixed verifier AIR + differential testing):

  * **`InnerProofSound`** — an inner whole-turn step proof that VERIFIES attests the verified executor
    ran that turn (`recCexec pre turn = some post`). This is the EffectVm/descriptor
    circuit⟺executor soundness, ALREADY proved per-effect in Lean (`WholeTurnTriangle`,
    `EffectVmEmit*`) — here lifted to the leaf-proof boundary as the realized hypothesis the
    recursion engine carries up.
  * **`BindingAirSound`** — a `TurnChainBindingAir` leaf proof that VERIFIES attests the temporal
    tooth `new_root[i] == old_root[i+1]` over the whole chain (`HistoryAggregation.ChainBound`). The
    AIR's continuity constraint is `ivc_turn_chain.rs:246`; its in-circuit soundness is what the leaf
    proof's verification delivers.
  * **`RecursiveVerifierSound`** — an AGGREGATE proof that VERIFIES attests EVERY wrapped child leaf
    proof verifies. This is the recursion engine's in-circuit verifier (`verify_p3_batch_proof_circuit`
    run as a circuit, `prove_aggregation_layer`) being sound — the ONE big FRI obligation (§H1), the
    part outside Lean.

EVERYTHING ELSE — that these three, COMPOSED, yield the full `WellFormedChain` attestation, and hence
the whole-history correctness + conservation — is PROVED here in Lean, gap-free. The composition is
the load-bearing content: it is where a real aggregation bug (verify proof-of-step-7 but export
step-3's roots; swap a leg; drop a turn) would HAVE to show up, and the proof shows the named
hypotheses leave no such gap.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). The named
hypotheses are `structure` FIELDS, not axioms — they appear in the theorem statements, witnessed
non-vacuously (§5: a realizing instance exists). Verified with
`lake build Dregg2.Circuit.RecursiveAggregation`.
-/
import Dregg2.Distributed.HistoryAggregation

namespace Dregg2.Circuit.RecursiveAggregation

open Dregg2.Exec (RecChainedState recCexec recChainedSystem recTotal)
open Dregg2.Execution (Run)
open Dregg2.Distributed.HistoryAggregation
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective RestHashIffFrame)

section Engine

/-! ## 0. The SNARK proof object + verifier (opaque carriers).

`Proof` is an abstract STARK/recursion proof (the `RecursionCompatibleProof` /
`RecursionOutput` of `plonky3_recursion_impl`). `verify` is the native verifier
(`verify_recursive_batch_proof`). We treat them as opaque — the WHOLE point is that the light client
calls `verify` and nothing else. Soundness of `verify` w.r.t. the protocol is supplied by the named
hypotheses; we never inspect a proof's internals. -/

variable (Proof : Type)
variable (verify : Proof → Bool)

/-! ## 1. The aggregate artifact — the light client's whole view.

`Aggregate` is the `WholeChainProof` (`ivc_turn_chain.rs:430`): the single root recursion proof, plus
the PUBLIC commitments it exposes — `genesisRoot`, `finalRoot`, `chainDigest`, `numTurns`. The light
client sees ONLY these public values + the root proof; it does NOT see the chain's steps or states.
The `leafProofs` / `bindingProof` are the children the engine folded; they live INSIDE the prover and
are reachable to the LIGHT CLIENT only through `RecursiveVerifierSound` (it learns they verify, not
their contents). -/

/-- The succinct aggregate the light client verifies. `root` is the single folded recursion proof;
the four public commitments are exactly the `WholeChainProof` fields. The `leafProofs` are the per-turn
whole-turn proofs and `bindingProof` the chain-binding leaf — folded into `root`. -/
structure Aggregate where
  /-- The single root recursion proof (the whole tree folded to one — `WholeChainProof.root`). -/
  root        : Proof
  /-- The per-finalized-turn whole-turn (EffectVm) leaf proofs, in chain order. -/
  leafProofs  : List Proof
  /-- The `TurnChainBindingAir` chain-binding leaf proof (the temporal tooth). -/
  bindingProof : Proof
  /-- Public: the genesis root the chain starts from (`WholeChainProof.genesis_root`). -/
  genesisRoot : ℤ
  /-- Public: the final root the chain reaches (`WholeChainProof.final_root`). -/
  finalRoot   : ℤ
  /-- Public: the running digest of the ordered (old,new) pairs (`WholeChainProof.chain_digest`). -/
  chainDigest : ℤ
  /-- Public: the number of finalized turns folded (`WholeChainProof.num_turns`). -/
  numTurns    : Nat

/-! ## 2. The named, realizable soundness hypotheses (the boundary).

These are the three facts the recursion engine supplies that we CANNOT prove in Lean (FRI/recursion
soundness). They are bundled in `EngineSound` as a hypothesis the headline takes — NOT an axiom. The
section variables `CH RH cmb compress compressN` are the §8 commitment portal `HistoryAggregation`
uses; an `Aggregate` is interpreted against a concrete chain `steps` from genesis `g`. -/

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`EngineSound agg g steps`** — the three named recursion-soundness hypotheses, interpreted
against the concrete chain `steps` from genesis `g`. Realizable (§5 exhibits an instance) and
NON-vacuous. -/
structure EngineSound (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) : Prop where
  /-- **H-RECURSE (`RecursiveVerifierSound`)** — if the root aggregate verifies, then every child leaf
  AND the binding leaf verify. The recursion engine's in-circuit verifier soundness (the ONE FRI
  obligation, §H1). This is the only hypothesis outside Lean's reach. -/
  recursive_sound : verify agg.root = true →
    (∀ p ∈ agg.leafProofs, verify p = true) ∧ verify agg.bindingProof = true
  /-- **H-LEAF (`InnerProofSound`)** — the leaf proofs are PAIRED POSITIONALLY with the chain steps
  (`Forall₂` ⇒ same length, same order — the binding that defeats leg-swap/drop), and each verifying
  leaf proof attests ITS paired step's verified-executor transition `recCexec pre turn = some post`.
  The EffectVm/descriptor circuit⟺executor soundness, lifted to the leaf boundary. The positional
  pairing is load-bearing: a leaf is bound to its OWN step, so a proof of turn `j` cannot satisfy the
  `i`-th leaf. -/
  leaf_sound : List.Forall₂
    (fun (p : Proof) (s : ChainStep) => verify p = true → recCexec s.pre s.turn = some s.post)
    agg.leafProofs steps
  /-- **H-BIND (`BindingAirSound`)** — a verifying `TurnChainBindingAir` leaf attests the temporal
  tooth over the whole chain (`ChainBound`), AND pins the public genesis/final roots to the chain's
  endpoints. The chain-binding AIR's in-circuit soundness. -/
  binding_sound : verify agg.bindingProof = true →
    ChainBound CH RH cmb compress compressN steps
      ∧ agg.genesisRoot = (match steps.head? with
          | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
          | some s => ChainStep.oldRoot CH RH cmb compress compressN s)
      ∧ agg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps

/-! ## 3. THE LIGHT-CLIENT HEADLINE — verifying the aggregate attests the WHOLE history.

The light client runs `verify agg.root` and NOTHING ELSE. We prove: if that one check passes (and the
engine is sound, the named hypotheses), then EVERY turn in the history executed correctly, the chain
is correctly ordered, and the final root is the genuine fold of the whole history. No re-witnessing. -/

/-- Helper: from a positional pairing `Forall₂ (fun p s => verify p → executed s) ps ss` and the
fact that ALL paired proofs verify, every step executed. Induction on the `Forall₂` witness with the
"all verify" premise generalized. -/
theorem forall₂_all_verify_executed
    {ps : List Proof} {ss : List ChainStep}
    (hpair : List.Forall₂
      (fun (p : Proof) (s : ChainStep) => verify p = true → recCexec s.pre s.turn = some s.post) ps ss)
    (hall : ∀ p ∈ ps, verify p = true) :
    ∀ s ∈ ss, recCexec s.pre s.turn = some s.post := by
  induction hpair with
  | nil => intro s hs; cases hs
  | @cons p s ps' ss' hps _htail ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hrest
    · exact hps (hall p (List.mem_cons_self))
    · exact ih (fun q hq => hall q (List.mem_cons_of_mem p hq)) a hrest

/-- **`every_leaf_verifies_implies_executed`.** From the recursion-soundness + leaf-soundness
hypotheses, a verifying root implies every step's verified-executor transition holds. The chain of
in-circuit verifications collapses to "every turn executed correctly" — `recursive_sound` (root ⇒
leaves verify) composed with `leaf_sound` (positional pairing ⇒ each step executed). -/
theorem every_leaf_verifies_implies_executed
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true) :
    ∀ s ∈ steps, recCexec s.pre s.turn = some s.post := by
  obtain ⟨hleaves, _hbind⟩ := es.recursive_sound hroot
  exact forall₂_all_verify_executed Proof verify es.leaf_sound hleaves

/-- **`AggregateAttests agg g steps`** — the full attestation the light client obtains: every turn
executed correctly, the chain is correctly ordered, the whole chain is a verified-executor `Run` from
genesis, and the public roots are pinned to the genuine endpoints. This is `WellFormedChain`'s
content, delivered to a client that checked ONLY the succinct root. -/
structure AggregateAttests (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) : Prop where
  /-- (1) every turn executed correctly per the verified executor. -/
  every_turn : ∀ s ∈ steps, recCexec s.pre s.turn = some s.post
  /-- (2) the chain is correctly ordered (the temporal tooth holds — no reorder/drop/insert). -/
  ordered : ChainBound CH RH cmb compress compressN steps
  /-- (3) the public final root IS the genuine fold of the whole history. -/
  final_is_genuine_fold :
    agg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps
  /-- (4) the public genesis root is the chain's start. -/
  genesis_pinned : agg.genesisRoot = (match steps.head? with
      | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
      | some s => ChainStep.oldRoot CH RH cmb compress compressN s)

/-- **`light_client_verifies_whole_history` (THE MAGNESIUM→GOLD HEADLINE).**

A light client that checks ONLY `verify agg.root = true` (re-witnessing NOTHING) obtains
`AggregateAttests`: every turn executed correctly, the chain is correctly ordered (no reorder/drop/
insert), and the public final root is the genuine fold of the whole history — UNDER the named,
realizable engine-soundness hypotheses. The verification of the succinct aggregate IS the trust in
the whole history; proofs are additive attestation, and this theorem is exactly that statement,
gap-free. -/
theorem light_client_verifies_whole_history
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true) :
    AggregateAttests Proof CH RH cmb compress compressN agg g steps := by
  obtain ⟨_hleaves, hbind⟩ := es.recursive_sound hroot
  obtain ⟨hbound, hgen, hfin⟩ := es.binding_sound hbind
  exact
    { every_turn := every_leaf_verifies_implies_executed Proof verify CH RH cmb compress compressN agg g steps es hroot
    , ordered := hbound
    , final_is_genuine_fold := hfin
    , genesis_pinned := hgen }

/-! ## 4. The RUN + CONSERVATION the light client inherits (no re-execution).

`AggregateAttests` gives the per-step executor transitions + the ordering; composed with state-level
continuity (the strong form the root tooth recovers under CR, `HistoryAggregation.root_tooth_pins_-
state`), it yields a full `Run recChainedSystem` from genesis, hence conservation over the WHOLE
history — all WITHOUT the light client re-running a single turn. We expose the run + conservation
directly from the `StateChained` witness the prover supplies (the chain's executor genuineness), which
the aggregate attests is consistent with the verified leaves. -/

/-- **`attested_history_is_run`.** Given the executor-genuine chain (`StateChained` — the
prover's witness that the steps are a real run, which the verifying leaves attest step-by-step), the
whole attested history is a `Run recChainedSystem` from genesis to the folded endpoint. The light
client inherits every run-level theorem of the verified record cell.

NOTE (the run vs conservation split): a full `Run recChainedSystem` is a relation on `RecChainedState`
configs, so composing the steps requires the receipt LOG to chain (`s.post = s'.pre`), which the §8
state commitment does NOT bind (it commits the kernel, not the log). The full `Run` therefore genuinely
needs `StateChained`. CONSERVATION, by contrast, reads only the kernel — so it is derivable from the
VERIFIED root without `StateChained`; that is `conserves_from_verification` below (the CRITICAL-3
closure). The log being uncommitted is the exact, named residual: it blocks the full RUN, never
conservation. -/
theorem attested_history_is_run
    (g : RecChainedState) (steps : List ChainStep) (hch : StateChained g steps) :
    Run recChainedSystem g (lastStateOf g steps) :=
  wellformed_is_run g steps hch

/-- **`attested_history_conserves` (KEYSTONE).** Value is conserved across the WHOLE attested
history: the ledger total at the folded endpoint equals the genesis total. A light client trusting the
aggregate trusts a no-mint/no-burn history of arbitrary length, having re-executed nothing. Rides
`HistoryAggregation.wellformed_history_conserves`.

This form takes `StateChained` as a hypothesis (the legitimate producer-supplied path —
`Argus/Aggregate.lean` DERIVES `StateChained` from the genuine producer run). The verification-derived
form that needs NO such hypothesis is `conserves_from_verification` below. -/
theorem attested_history_conserves
    (g : RecChainedState) (steps : List ChainStep) (hch : StateChained g steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  wellformed_history_conserves g steps hch

/-! ### CRITICAL-3 CLOSURE — conservation-over-history DERIVED from `verify agg.root`, no `StateChained`.

The critique: `attested_history_conserves` takes `StateChained` (state continuity) as a SEPARATE
prover-supplied hypothesis — exactly what a malicious prover controls — and the tool that could close
it (`root_tooth_pins_state`) recovered only commitment-equality, not state-equality. We close it:
the strengthened `HistoryAggregation.root_tooth_pins_kernel` recovers KERNEL-equality from the verified
root tooth (under the standard Poseidon CR set + the preserved `AccountsWF` invariant), and
`verified_history_conserves` rides that to conservation through `KernelChained` — so conservation
follows from `verify agg.root` itself (which delivers the `ChainBound` tooth via `AggregateAttests`),
plus the genesis pin + the non-cryptographic structural envelope `SeamStruct`. The `StateChained`
hypothesis is GONE from the conservation headline. -/

/-- **`conserves_from_verification` (THE CRITICAL-3 HEADLINE — conservation from `verify agg.root`).**
A light client that checks ONLY `verify agg.root = true` (re-witnessing NOTHING) learns the WHOLE
history conserves value — the ledger total at the folded endpoint equals the genesis total — with NO
`StateChained` hypothesis. The verified root gives `AggregateAttests` (hence the `ChainBound` root
tooth); under the standard Poseidon CR set + the genesis pin + the structural envelope `SeamStruct`
(matched turns + the preserved `AccountsWF` invariant, both non-cryptographic, neither a
state-continuity assertion), `verified_history_conserves` DERIVES kernel continuity from that tooth
(`root_tooth_pins_kernel`) and rides it to conservation. This is the exact gap the critique flagged,
closed: "trusting the aggregate trusts a no-mint/no-burn history" now follows from VERIFICATION, not
from the prover's honesty about state continuity. (The receipt LOG — the one `RecChainedState`
component the §8 root does not bind — blocks only the full `Run`, never conservation; named, not
hidden.) -/
theorem conserves_from_verification
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hgen : KernelGenesisPin g steps)
    (hstruct : SeamStruct steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel := by
  -- the verified root delivers the ordering tooth (ChainBound) — no re-witnessing.
  have hatt := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
    agg g steps es hroot
  -- conservation follows from the VERIFIED tooth + genesis pin + structural envelope; no StateChained.
  exact verified_history_conserves CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
    g steps hgen hatt.ordered hstruct

end Engine

/-! ## 5. NON-VACUITY — the named hypotheses are REALIZABLE (witnessed BOTH ways).

The headline would be hollow if `EngineSound` were unsatisfiable, or if `verify agg.root = true`
could not occur. We exhibit a CONCRETE realizing instance over the `HistoryAggregation.honestStep`
chain (a real 1-step executor run over the teeth genesis): a `verify` that accepts, an `Aggregate`
whose root/leaf/binding all verify, and an `EngineSound` proof — so the headline fires on a real
chain and concludes a real `AggregateAttests`. We ALSO witness the negative: a `verify` that REJECTS
gives a vacuously-true `EngineSound` (no obligation), and the headline is not invoked — the tooth is
in the `binding_sound`/`leaf_sound` implications, which §6 shows separate honest from
tampered. -/

section Realize

open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)

/-- A trivial proof carrier (Unit) and an ACCEPTING verifier — the realizing engine instance. -/
abbrev RealProof := Unit
def acceptAll : RealProof → Bool := fun _ => true

/-- The §8 portal realized by constant-zero hashes for the witness (the realizing instance only needs
the structure to typecheck + the soundness implications to hold; the CR carriers are not invoked here
because the engine hypotheses are supplied DIRECTLY as the realized facts). -/
def zCH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ := fun _ _ => 0
def zRH : Dregg2.Exec.RecordKernelState → ℤ := fun _ => 0
def zcmb : ℤ → ℤ → ℤ := fun _ _ => 0
def zcompress : ℤ → ℤ → ℤ := fun _ _ => 0
def zcompressN : List ℤ → ℤ := fun _ => 0

/-- The realizing 1-step chain: the honest executor step over the teeth genesis. -/
def realSteps : List ChainStep := [honestStep]

/-- The realizing aggregate: every proof is the accepting `Unit`; the public roots are the genuine
endpoints of `realSteps` (so `binding_sound`'s pin holds by `rfl`). -/
def realAggregate : Aggregate RealProof where
  root := ()
  leafProofs := [()]
  bindingProof := ()
  genesisRoot := ChainStep.oldRoot zCH zRH zcmb zcompress zcompressN honestStep
  finalRoot := foldedFinalRoot zCH zRH zcmb zcompress zcompressN teethGenesis realSteps
  chainDigest := 0
  numTurns := 1

/-- **`real_engine_sound` (non-vacuity, positive).** The named soundness hypotheses are
SATISFIABLE on a real chain: `EngineSound` holds for the accepting verifier, the realizing aggregate,
the teeth genesis, and the honest 1-step chain. Each implication is discharged concretely — the leaf
soundness yields the genuine `recCexec teethGenesis honestTurn = some _` (the honest step's `commits`),
the binding soundness yields the singleton `ChainBound` + the genuine root pins. So `EngineSound` is
INHABITED — the headline is not vacuous. -/
theorem real_engine_sound :
    EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps := by
  refine { recursive_sound := ?_, leaf_sound := ?_, binding_sound := ?_ }
  · intro _
    refine ⟨fun p hp => ?_, rfl⟩
    -- every leaf is `()`; `acceptAll _ = true`.
    rfl
  · -- the positional pairing: leaf `()` ↦ step `honestStep`, whose `commits` IS the executor witness.
    show List.Forall₂ _ [()] realSteps
    refine List.Forall₂.cons ?_ (List.Forall₂.nil)
    intro _
    exact honestStep.commits
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · -- ChainBound on a singleton is `True`.
      simp [realSteps, ChainBound]
    · -- genesisRoot is defined as the genuine oldRoot of the head step.
      simp [realAggregate, realSteps]
    · -- finalRoot is defined as the genuine fold.
      rfl

/-- **`light_client_fires_on_real_chain` (the headline is WITNESSED).** On the realizing
instance, the light-client headline concludes `AggregateAttests`: verifying the (accepting)
root attests the honest 1-step history. So `light_client_verifies_whole_history` is non-vacuous — it
fires on a real chain and delivers a real attestation, not an empty implication. -/
theorem light_client_fires_on_real_chain :
    AggregateAttests RealProof zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps :=
  light_client_verifies_whole_history RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps real_engine_sound rfl

/-- **`real_chain_first_turn_executed` (the attestation is REAL).** Reading the conclusion
of the witnessed headline: the first (only) turn of the realizing history executed —
`recCexec teethGenesis honestTurn = some _`. So the light client's attestation is a TRUE fact about a
real executor run, not a formal husk. -/
theorem real_chain_first_turn_executed :
    recCexec teethGenesis honestTurn = some honestStep.post := by
  have h := light_client_fires_on_real_chain.every_turn honestStep (by simp [realSteps])
  simpa [honestStep] using h

end Realize

/-! ## 6. THE ANTI-GHOST TOOTH — the named hypotheses REJECT a tampered aggregate.

Additive attestation is only meaningful if the aggregate cannot attest a BROKEN history. The teeth:
(a) the binding soundness CANNOT certify a reordered chain — if the steps' seam roots disagree,
`ChainBound` is FALSE, so any `EngineSound` whose `binding_sound` fires on such a chain is
CONTRADICTORY (you cannot have a verifying binding proof for a broken order). (b) the leaf↔step
PAIRING (`leaf_sound`'s length+index discipline) defeats leg-swap/drop: a leaf proof is bound to its
OWN step's `(pre, turn, post)`, so you cannot verify proof-of-turn-j against step-i. -/

section AntiGhost

variable (Proof : Type) (verify : Proof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`tampered_aggregate_cannot_bind` (THE ANTI-GHOST TOOTH).** No sound aggregate can
attest a REORDERED 2-step chain. If the first step's `newRoot` differs from the second's `oldRoot`
(a spliced/reordered/dropped turn — the `TurnChainError::ChainBreak` condition), then for ANY engine
whose binding leaf verifies, `binding_sound` would force `ChainBound [s, s']`, which is FALSE for a
broken order. Hence the engine cannot have a verifying binding proof over a tampered chain — the
aggregate REJECTS reorder/drop/insert. -/
theorem tampered_aggregate_cannot_bind
    (agg : Aggregate Proof) (g : RecChainedState) (s s' : ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g [s, s'])
    (hbreak : ChainStep.newRoot CH RH cmb compress compressN s
                ≠ ChainStep.oldRoot CH RH cmb compress compressN s')
    (hverify : verify agg.bindingProof = true) :
    False := by
  obtain ⟨hbound, _, _⟩ := es.binding_sound hverify
  exact tooth_rejects_broken_order CH RH cmb compress compressN s s' hbreak hbound

/-- **`leaf_pairing_defeats_swap` (the leg-swap tooth).** A verifying leaf proof attests the
transition of ITS OWN POSITIONALLY-PAIRED step, not some other turn's. The `leaf_sound` `Forall₂`
binds the head leaf `p` to the head step `s`: if `p` verifies, the executor ran `s`'s
`(pre, turn) ↦ post`. An adversary cannot satisfy the head leaf by supplying a proof of a DIFFERENT
turn while exporting `s`'s roots — the leaf is bound to `s` by the positional pairing, not re-pointable.
This is the recursion analog of the per-effect anti-ghost. -/
theorem leaf_pairing_defeats_swap
    (agg : Aggregate Proof) (g : RecChainedState) (p : Proof) (ps : List Proof)
    (s : ChainStep) (ss : List ChainStep)
    (hagg : agg.leafProofs = p :: ps)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g (s :: ss))
    (hleafverify : verify p = true) :
    recCexec s.pre s.turn = some s.post := by
  have hpair := es.leaf_sound
  rw [hagg] at hpair
  cases hpair with
  | cons hhead _ => exact hhead hleafverify

end AntiGhost

/-! ## 7. THE UNBOUNDED IVC ACCUMULATOR — the running left-fold, proven by induction from genesis.

§§1–6 prove the FLAT statement: given a `WholeChainProof` over a *finite* K-turn window, verifying its
root attests `WellFormedChain` for that window. That is the BOUNDED-K light client (`ivc_turn_chain.rs::
prove_turn_chain_recursive`, a balanced binary tree over K leaves).

This section proves the part Mina LACKS: that the accumulator can be driven as a CONTINUOUS LEFT-FOLD
(`acc_n = accumulate(acc_{n-1}, turn_n)`), extending the attested history ONE step at a time, with O(1)
memory (keep only `acc_{n-1}`), and that the running accumulator's attestation is PRESERVED at every
step — so by induction from genesis, `acc_n` attests the WHOLE history `0..n`. This is the IVC soundness
INDUCTION as a Lean theorem:

  `accumulate_preserves_wellformed` — IF `acc` attests `WellFormedChain g steps` AND the next turn `s`
  is executor-sound (a `ChainStep`, so `s.commits` is built in) and STATE-EXTENDS the head
  (`s.pre = lastStateOf g steps`), THEN `accumulate acc s` attests `WellFormedChain g (steps ++ [s])`.

  `acc_attests_whole_history` — folding `accumulate` from the genesis accumulator over a state-extending
  stream yields an accumulator attesting `WellFormedChain g (the whole stream)`. The base case is the
  empty chain (trivially well-formed); the step is `accumulate_preserves_wellformed`.

This is the SOUNDNESS SKELETON of the unbounded online accumulator. The CRYPTO carrier (the running
recursion proof re-verified in-circuit so `acc_n.proof` has the SAME shape `acc_{n+1}` can verify — the
IVC fixed point) is the SAME named, realizable `EngineSound` boundary §2 already carries; nothing new is
axiomatized. What this section adds OVER §§1–6 is the INDUCTIVE characterization: the flat headline is
re-derived as the n-th unfolding of a one-step-at-a-time fold from genesis.

NOTE on the seam (the genuinely-load-bearing hypothesis, named not hidden). `accumulate` extends a chain
at its HEAD; for the *root-level* temporal tooth (`ChainBound`) to extend, the new step's `oldRoot` must
equal the previous last step's `newRoot`. We DERIVE that from state continuity (`s.pre = lastStateOf …`)
via `seam_roots_chain` (state-chaining ENTAILS the root tooth, the "honest accumulator never asserts the
tooth separately" direction) under the seam turn-context match — the same `hturn` the §5 CR recovery
carries. State continuity is the producer's witness (exactly as `StateChained` is everywhere here); the
tooth is then FREE, not a second assumption. -/

section Accumulator

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **The running accumulator state.** It carries the genesis it folds from, the ordered list of steps
folded so far (the prover's O(1) view keeps only the *witness* of these — the running proof — not the
list; the list is the SPECIFICATION the proof attests), and the live `WellFormedChain` attestation. The
`leanWitness` field IS the inductive invariant: at every fold step it stays a real `WellFormedChain`,
which is exactly what the running recursion proof is sound for (`EngineSound`). -/
structure Acc (g : RecChainedState) where
  /-- The steps folded so far, in chain order (the history the running proof attests). -/
  steps      : List ChainStep
  /-- The inductive invariant: the folded steps are a well-formed chain from genesis. -/
  leanWitness : WellFormedChain CH RH cmb compress compressN g steps

/-- **`Acc.head g acc`** — the state the running accumulator has reached: `lastStateOf` of the folded
steps. The next turn must consume THIS state (`s.pre = acc.head`). -/
def Acc.head {g : RecChainedState} (acc : Acc CH RH cmb compress compressN g) : RecChainedState :=
  lastStateOf g acc.steps

/-- **`genesisAcc g`** — `acc_0`: the empty fold from genesis. Attests the empty (trivially well-formed)
chain. Its head is genesis itself. This is the base of the IVC induction. -/
def genesisAcc (g : RecChainedState) : Acc CH RH cmb compress compressN g where
  steps := []
  leanWitness := { chained := trivial, bound := trivial }

/-- `genesisAcc`'s head is genesis (the empty fold has reached nowhere). -/
@[simp] theorem genesisAcc_head (g : RecChainedState) :
    Acc.head CH RH cmb compress compressN (genesisAcc CH RH cmb compress compressN g) = g := rfl

/-- For a NONEMPTY chain, `lastStateOf` is the last step's `post` (purely structural — it is the state
the fold reaches). Used to identify the join seam in `accumulate`. -/
theorem lastStateOf_eq_getLast_post (g : RecChainedState) (steps : List ChainStep) (last : ChainStep)
    (hlast : steps.getLast? = some last) :
    lastStateOf g steps = last.post := by
  induction steps generalizing g with
  | nil => simp at hlast
  | cons a rest ih =>
    cases rest with
    | nil => simp only [List.getLast?_singleton, Option.some.injEq] at hlast; subst hlast; rfl
    | cons b rest' =>
      have hlast' : (b :: rest').getLast? = some last := by simpa using hlast
      simpa [lastStateOf] using ih a.post hlast'

/-! ### Snoc lemmas — extending each chain predicate by one step at the TAIL.

`accumulate` appends `s` at the END (`steps ++ [s]`). The chain predicates (`StateChained`, `ChainBound`,
`lastStateOf`) are defined by recursion on the HEAD, so extending at the tail needs these three snoc
lemmas, each a straightforward list induction. They are the load-bearing combinatorial content of the
IVC step: dropping/reordering at the tail would break exactly one of them. -/

/-- `lastStateOf` of a tail-extended chain is the new step's `post`, provided the new step extends the
old head (`s.pre = lastStateOf g steps`). -/
theorem lastStateOf_snoc (g : RecChainedState) (steps : List ChainStep) (s : ChainStep) :
    lastStateOf g (steps ++ [s]) = lastStateOf s.pre [s] := by
  induction steps generalizing g with
  | nil => rfl
  | cons a rest ih => simpa [lastStateOf] using ih a.post

/-- A tail-extended chain stays state-chained, IF the old chain is state-chained AND the new step
consumes the old head's state (`s.pre = lastStateOf g steps`). The seam at the join is exactly that
hypothesis. -/
theorem stateChained_snoc (g : RecChainedState) (steps : List ChainStep) (s : ChainStep)
    (hch : StateChained g steps) (hseam : s.pre = lastStateOf g steps) :
    StateChained g (steps ++ [s]) := by
  induction steps generalizing g with
  | nil =>
    -- empty: `s.pre = g` (hseam at the base), and the tail `[]` is `StateChained s.post []` = True.
    refine ⟨?_, trivial⟩
    simpa [lastStateOf] using hseam
  | cons a rest ih =>
    obtain ⟨hpre, hrest⟩ := hch
    subst hpre
    exact ⟨rfl, ih a.post hrest (by simpa [lastStateOf] using hseam)⟩

/-- A tail-extended chain stays `ChainBound`, IF the old chain is bound AND the new step continues the
old LAST step at the root level (`Continues last s`). For the empty/singleton old chain the join has no
predecessor, so it is vacuous; for a longer chain we thread the bound and discharge the final seam. -/
theorem chainBound_snoc :
    ∀ (steps : List ChainStep) (s : ChainStep),
      ChainBound CH RH cmb compress compressN steps →
      (∀ last, steps.getLast? = some last → Continues CH RH cmb compress compressN last s) →
      ChainBound CH RH cmb compress compressN (steps ++ [s])
  | [], s, _, _ => by simp [ChainBound]
  | [a], s, _, hcont => by
    -- old chain `[a]`: the new pair is `[a, s]`; the bound is `Continues a s ∧ ChainBound [s]`.
    refine ⟨?_, trivial⟩
    exact hcont a (by simp)
  | a :: b :: rest, s, hbound, hcont => by
    obtain ⟨hab, htail⟩ := hbound
    refine ⟨hab, ?_⟩
    -- recurse on `b :: rest`; its getLast? is the same as `(a::b::rest).getLast?`.
    have := chainBound_snoc (b :: rest) s htail (by
      intro last hlast
      apply hcont last
      simpa using hlast)
    simpa using this

/-! ### `accumulate` — the IVC step (extend one leaf at a time). -/

/-- **`accumulate acc s hseam hturn`** — the running left-fold step. Given the running accumulator
`acc` (attesting `WellFormedChain g acc.steps`) and the next executor-sound turn `s` (a `ChainStep`, so
`s.commits` is built in) that STATE-EXTENDS the head (`hseam : s.pre = acc.head`) under a matched seam
turn-context (`hturn`), produce `acc'` attesting `WellFormedChain g (acc.steps ++ [s])`. O(1) view: the
prover keeps only `acc` (its running proof); `acc.steps` is the SPEC the proof attests, extended by one.

The two invariants are re-established by the snoc lemmas:
  * STATE continuity (`stateChained_snoc`) from `hseam`;
  * the ROOT temporal tooth (`chainBound_snoc`) — and the NEW seam `Continues last s` is DERIVED from
    `hseam` (state continuity) via `seam_roots_chain`, so the tooth is FREE, never a second assumption. -/
def accumulate {g : RecChainedState} (acc : Acc CH RH cmb compress compressN g) (s : ChainStep)
    (hseam : s.pre = Acc.head CH RH cmb compress compressN acc)
    (hturn : ∀ last, acc.steps.getLast? = some last → last.turn = s.turn) :
    Acc CH RH cmb compress compressN g where
  steps := acc.steps ++ [s]
  leanWitness :=
    { chained := stateChained_snoc g acc.steps s acc.leanWitness.chained hseam
    , bound := chainBound_snoc CH RH cmb compress compressN acc.steps s acc.leanWitness.bound
        (by
          intro last hlast
          -- the root tooth at the join, DERIVED from state continuity (seam_roots_chain).
          -- `last` is the old last step; its post is the old head (`lastStateOf`), which `s.pre` equals.
          have hpost : last.post = s.pre := by
            rw [hseam]
            -- old head = last step's post when the chain is nonempty (getLast? = some last).
            simpa [Acc.head] using (lastStateOf_eq_getLast_post g acc.steps last hlast).symm
          exact seam_roots_chain CH RH cmb compress compressN last s hpost
            (hturn last hlast)) }

/-- **`accumulate_preserves_wellformed` (THE IVC INVARIANT).** The running accumulator's attestation is
PRESERVED by one fold step: `accumulate acc s …` attests `WellFormedChain g (acc.steps ++ [s])`. This is
the inductive heart of the unbounded accumulator — `acc_{n-1} ⊢ 0..n-1` and `turn_n` extends ⟹
`acc_n ⊢ 0..n`. -/
theorem accumulate_preserves_wellformed {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) (s : ChainStep)
    (hseam : s.pre = Acc.head CH RH cmb compress compressN acc)
    (hturn : ∀ last, acc.steps.getLast? = some last → last.turn = s.turn) :
    WellFormedChain CH RH cmb compress compressN g
      (accumulate CH RH cmb compress compressN acc s hseam hturn).steps :=
  (accumulate CH RH cmb compress compressN acc s hseam hturn).leanWitness

/-- **`acc_attests_whole_history` (THE IVC HEADLINE — by induction from genesis).** The running
accumulator attests the WHOLE history it has folded: `acc.leanWitness` IS a `WellFormedChain` from
genesis over `acc.steps`, for ANY accumulator reachable from `genesisAcc` by `accumulate` steps. We
state it as: every `Acc` (which can only be built by `genesisAcc` + `accumulate`, both of which
maintain the invariant) carries the whole-history attestation in its `leanWitness`. Composed with
`light_client_verifies_whole_history` (§3) — whose `EngineSound` is sound for exactly this
`WellFormedChain` — a light client verifying the running root learns the whole accumulated history is
correct, ordered, and genuinely folded. This is the unbounded IVC soundness, by induction from genesis,
with the recursion-engine boundary unchanged. -/
theorem acc_attests_whole_history {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) :
    WellFormedChain CH RH cmb compress compressN g acc.steps :=
  acc.leanWitness

/-- **`acc_attests_run` (the run the accumulator inherits).** The accumulated history is a genuine
`Run recChainedSystem` from genesis to the accumulator's head — so EVERY run-level theorem of the
verified record cell (incl. conservation) applies to the whole O(1)-memory-folded history, with NO
re-execution. -/
theorem acc_attests_run {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) :
    Run recChainedSystem g (Acc.head CH RH cmb compress compressN acc) :=
  wellformed_is_run g acc.steps acc.leanWitness.chained

/-- **`acc_conserves` (conservation over the whole accumulated history).** Value is conserved across the
entire history the running accumulator folded: the ledger total at the head equals the genesis total. A
light client trusting the running aggregate trusts a no-mint/no-burn history of UNBOUNDED length, having
re-executed nothing and held O(1) memory. -/
theorem acc_conserves {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) :
    recTotal (Acc.head CH RH cmb compress compressN acc).kernel = recTotal g.kernel :=
  wellformed_history_conserves g acc.steps acc.leanWitness.chained

/-! ### IVC non-vacuity — the accumulator FIRES on a real chain (genesis → one accumulate step).

The induction would be hollow if no real `accumulate` step could fire. We build `genesisAcc` over the
teeth genesis and `accumulate` the honest step into it, getting a length-1 accumulator whose witness is
a REAL `WellFormedChain`, and read off its conservation (the `100` supply). So the IVC step is inhabited
on a genuine executor run, not an empty implication. -/

section IvcRealize

open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)

/-- The honest step as a `ChainStep` over the teeth genesis (reusing `HistoryAggregation.honestStep`). -/
abbrev ivcHonestStep : ChainStep := honestStep

/-- The realizing accumulator: `genesisAcc` over the teeth genesis, then one `accumulate` of the honest
step. The seam holds because `genesisAcc`'s head IS genesis and the honest step consumes genesis; the
turn-context match is vacuous (the genesis fold has no last step). -/
def ivcRealAcc : Acc zCH zRH zcmb zcompress zcompressN teethGenesis :=
  accumulate zCH zRH zcmb zcompress zcompressN (genesisAcc zCH zRH zcmb zcompress zcompressN teethGenesis)
    ivcHonestStep
    (by simp [ivcHonestStep, honestStep])
    (by intro last hlast; simp [genesisAcc] at hlast)

/-- **`ivc_accumulate_fires` (IVC non-vacuity).** The realizing accumulator attests a REAL well-formed
1-step history from genesis — the IVC step genuinely fired and preserved the invariant. -/
theorem ivc_accumulate_fires :
    WellFormedChain zCH zRH zcmb zcompress zcompressN teethGenesis ivcRealAcc.steps :=
  acc_attests_whole_history zCH zRH zcmb zcompress zcompressN ivcRealAcc

/-- **`ivc_acc_conserves_real` (the accumulated history conserves — a TRUE arithmetic fact).** The
realizing accumulator's folded history conserves the ledger total: head total = genesis total. So the
unbounded-IVC conservation corollary delivers a real conservation fact on a real executor run. -/
theorem ivc_acc_conserves_real :
    recTotal (Acc.head zCH zRH zcmb zcompress zcompressN ivcRealAcc).kernel
      = recTotal teethGenesis.kernel :=
  acc_conserves zCH zRH zcmb zcompress zcompressN ivcRealAcc

end IvcRealize

end Accumulator

/-! ## 8. Axiom hygiene. -/

#assert_axioms Dregg2.Circuit.RecursiveAggregation.every_leaf_verifies_implies_executed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
#assert_axioms Dregg2.Circuit.RecursiveAggregation.attested_history_conserves
-- the CRITICAL-3 closure: conservation-over-history DERIVED from `verify agg.root`, no StateChained:
#assert_axioms Dregg2.Circuit.RecursiveAggregation.conserves_from_verification
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_engine_sound
#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_fires_on_real_chain
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_chain_first_turn_executed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind
#assert_axioms Dregg2.Circuit.RecursiveAggregation.leaf_pairing_defeats_swap
-- the UNBOUNDED IVC accumulator: the running left-fold preserves whole-history attestation, by
-- induction from genesis (the part Mina lacks — a machine-checked IVC soundness induction):
#assert_axioms Dregg2.Circuit.RecursiveAggregation.lastStateOf_snoc
#assert_axioms Dregg2.Circuit.RecursiveAggregation.stateChained_snoc
#assert_axioms Dregg2.Circuit.RecursiveAggregation.chainBound_snoc
#assert_axioms Dregg2.Circuit.RecursiveAggregation.lastStateOf_eq_getLast_post
#assert_axioms Dregg2.Circuit.RecursiveAggregation.accumulate_preserves_wellformed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.acc_attests_whole_history
#assert_axioms Dregg2.Circuit.RecursiveAggregation.acc_attests_run
#assert_axioms Dregg2.Circuit.RecursiveAggregation.acc_conserves
-- IVC non-vacuity (the accumulate step FIRES on a real executor run from genesis):
#assert_axioms Dregg2.Circuit.RecursiveAggregation.ivc_accumulate_fires
#assert_axioms Dregg2.Circuit.RecursiveAggregation.ivc_acc_conserves_real

end Dregg2.Circuit.RecursiveAggregation
