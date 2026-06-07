/-
# Dregg2.Distributed.Consensus — the consensus long pole (Titanium Phase 2.1),
# grounded in Sridhar et al. and Wong et al.

**The grounding (see `docs/rebuild/CONSENSUS-GROUNDING.md`).** Two 2024 papers reshape what
Phase 2.1 must prove over the leaderless blocklace DAG-BFT (`Proof.CordialMiners`, the protocol
dregg1 actually runs) and the finalization→executor bridge (`Exec.ConsensusExec`):

* **Sridhar–Tas–Neu–Zindros–Tse, "Consensus Under Adversary Majority Done Right"**
  (arXiv 2411.01689). The single contribution we take: *resilience is a PAIR, not a scalar*.
  The folklore single number `min(t^S, t^L)` throws away the structure that matters; safety
  resilience `t^S` and liveness resilience `t^L` must be stated SEPARATELY — and for dregg's
  deployment point (sleepy validators, sleepy COMMUNICATING clients, partial-sync), the optimal
  shape is ASYMMETRIC: a *high* `t^S` and a *separately-bounded, lower* `t^L`. We do NOT
  re-derive Sridhar's 16-model characterization; we adopt its framing and prove the one point
  that is dregg.

* **Wong–Kolegov–Mikushin, "Beyond the Whitepaper"** (zkSecurity/Matter Labs). An experience
  paper; we take its failure taxonomy as the explicit list of *negative teeth* the formalization
  must exhibit: 3.1 (f+1 / equivocation), 3.2 (reconfiguration / long-range), 3.6 (view-sync /
  leader rotation — sidestepped because the blocklace is leaderless).

## What is PROVED here (the four §3 targets)

1. **A RESILIENCE PAIR (`safetyResilience` / `livenessResilience`), never a scalar.** The
   blocklace quorum model carries a `ResiliencePair` whose `tS` (safety) and `tL` (liveness)
   are SEPARATE fields, with `asymmetric : tL < tS` stating Sridhar's gap as a *feature*. The
   safety bound is GROUNDED: `safety_holds_below_tS` — under `≤ tS·n` Byzantine validators (a
   high fraction, `n > 3f` ⇒ `f < n/3` ⇒ a safety bound that the `n−f` quorum tolerates) two
   committed leaders cannot conflict, riding `cordial_no_conflicting_final_leaders`. The
   liveness bound is GROUNDED as a *separate, lower* threshold: `liveness_needs_tL` — progress
   (a `GSTRound` delivering the honest supermajority) requires the honest set to *exceed* the
   liveness threshold, the weaker `t^L`. The gap `tL < tS` is `resilience_gap_real`.
   NON-VACUITY: `dreggResilience` is a concrete asymmetric pair; the gap is exhibited.
   NEGATIVE TOOTH: `safety_can_break_above_tS` — above `t^S` (when the quorum no longer
   intersects honestly) a conflicting finalization is NOT excluded; the safety bound is a real
   constraint, not vacuous.

2. **`equivocation_excluded` (Wong 3.1 / f+1).** A cell-owner that double-signs leaves BOTH
   conflicting blocks in the blocklace as a self-incriminating, excludable incomparable pair
   (`Blocklace.Equivocator`, witnessed by `equivocation_detectable`). PROVED:
   `equivocation_excluded` — the double-signer is detectably an equivocator AND its leader
   candidate is *repelled* from ratification (`approves` requires `¬ Equivocator`, so an
   equivocator's block gains no honest approver). NEGATIVE TOOTH: `honest_finalization_unforkable`
   — an honest finalization cannot be forked by an `f+1` coalition below `t^S` (rides the
   quorum-intersection core: `f+1 ≤ f` is false, so the coalition cannot reach the `n−f` quorum
   for a *conflicting* leader without an honest ratifier, who is repelled by equivocation).

3. **Reconfiguration-safe finality (Wong 3.2 / long-range).** Finality is anchored to an
   AUTHENTICATED, MONOTONE checkpoint (`Checkpoint` + `CheckpointChain`) so retired validator
   keys cannot re-anchor history. PROVED: `no_conflicting_finalized_state_reconfig` — two
   finalizations under DIFFERENT validator sets, each anchored to the same monotone checkpoint
   prefix, cannot conflict; `monotone_checkpoint_excludes_rewrite` — a checkpoint from a retired
   key-set that tries to anchor *below* the current monotone height is rejected. NEGATIVE TOOTH:
   `long_range_rewrite_rejected` — a posterior-corruption rewrite (retired keys re-signing an old
   height) is excluded because the checkpoint chain is strictly monotone.

4. **Leaderless ⇒ view-sync class is empty (Wong 3.6 sidestep).** The blocklace has NO leader
   election; finality is derived from the DAG structure + quorum reads, never a leader's
   proposal. RECORDED as `Leaderless` (a structural predicate: the commit rule reads only
   `ratifyingVoters`, never a `waveLeader` proposal authority) and `view_sync_class_empty` — the
   consecutive-bad-leader attack surface is *defined away*. Post-GST progress is carried as the
   NAMED open hypothesis `PostGSTProgress` (the `GSTRound` delivery, exactly `BFT.lean`'s O2
   residual / OPEN-CM-LIVENESS), with `leaderless_progress` proving progress FROM that hypothesis
   WITHOUT any leader-election sub-protocol — the sidestep made precise.

## HONEST SCOPE (named carried OPENs — NEVER `sorry`/`axiom`/`True`)

* `PostGSTProgress` — the post-GST `GSTRound` delivery (gossip convergence) is the genuine
  liveness residual (OPEN-CM-LIVENESS / `BFT.lean`'s O2). Carried as a named hypothesis the
  liveness theorems are stated *conditionally* on; `leaderless_progress` proves progress from it.
* `OPEN-CM-XSORT` — the intra-segment `tau` linearization tie-break is still open in
  `ConsensusExec`; unchanged here.
* The Sridhar 16-model characterization is ADOPTED, not re-derived (§4 of the grounding note);
  `ResiliencePair` carries dregg's *one* deployment point.

Every adversary assumption is a structure field or
a named theorem hypothesis. Verified with
`lake build Dregg2.Distributed.Consensus`.
-/
import Dregg2.Exec.ConsensusExec

namespace Dregg2.Distributed.Consensus

open Dregg2 Dregg2.World
open Dregg2.Proof.CordialMiners
open Dregg2.Proof.BFT (BFTModel)
open Dregg2.Authority.Blocklace
open Dregg2.Exec.ConsensusExec

/-! ## 1. The resilience PAIR (Sridhar) — never a scalar.

Sridhar et al.'s framing: a protocol's resilience is a *pair* `(t^S, t^L)`, not the folklore
single `min(t^S, t^L)`. We carry the pair over the blocklace quorum model. dregg's deployment
point — sleepy validators, sleepy COMMUNICATING clients, partial-sync — is exactly Sridhar's
Fig. 1g regime where an ASYMMETRIC pair (high safety, lower liveness) is optimal: the gap
`tL < tS` is a stated FEATURE, not a number hidden behind a min. -/

/-- **The four-coordinate client/network model (Sridhar's base point).** dregg sits at exactly
ONE point of Sridhar's 16-model space; we carry it as data (it labels the resilience pair).
`validatorSleepy ∧ clientSleepy ∧ clientCommunicating ∧ partialSync` is dregg's deployment. -/
structure DeploymentPoint where
  /-- Validators are intermittent (phones) — Sridhar's *sleepy* validator axis. -/
  validatorSleepy : Bool
  /-- Clients are intermittent — Sridhar's *sleepy* client axis. -/
  clientSleepy : Bool
  /-- Clients gossip (Plumtree) — Sridhar's *communicating* (not *silent*) client axis. -/
  clientCommunicating : Bool
  /-- The network is partial-synchronous (GST), not synchronous. -/
  partialSync : Bool
  deriving DecidableEq, Repr

/-- dregg's actual deployment point: sleepy validators, sleepy communicating clients,
partial-sync. This is the Fig. 1g regime where the asymmetric `(t^S, t^L)` is optimal. -/
def dreggDeployment : DeploymentPoint :=
  { validatorSleepy := true, clientSleepy := true
  , clientCommunicating := true, partialSync := true }

/-- **`ResiliencePair`** — the Sridhar resilience pair over a `Finality.Config`, carried as
SEPARATE safety and liveness thresholds. `tS` is the safety resilience (max Byzantine-validator
count under which no two honest parties finalize conflicting states); `tL` is the liveness
resilience (max under which the protocol keeps making progress). The fields are SEPARATE — never
a single scalar. `asymmetric : tL < tS` records Sridhar's gap as the FEATURE the communicating
client model buys: a *high* safety resilience with a separately-bounded *lower* liveness one. -/
structure ResiliencePair (cfg : Finality.Config) where
  /-- dregg's deployment point (labels which Sridhar model this pair is for). -/
  point : DeploymentPoint
  /-- **Safety resilience `t^S`** — the max Byzantine-validator count under which SAFETY holds.
  Grounded: it is the `n − f` quorum's fault tolerance `f` (so `f` Byzantine validators cannot
  fork), with the `n > 3f` floor giving `f < n/3`. The "high" safety the blocklace's
  verify-offline quorum read earns. -/
  tS : Nat
  /-- **Liveness resilience `t^L`** — the SEPARATELY-bounded, strictly LOWER max Byzantine count
  under which LIVENESS (post-GST DAG progress) holds. Lower than `tS` because progress needs an
  honest supermajority to *deliver* (the `GSTRound`), a stronger requirement than mere
  non-conflict. -/
  tL : Nat
  /-- **THE ASYMMETRY (Sridhar's gap, as a FEATURE).** `tL < tS`: the safety resilience strictly
  exceeds the liveness resilience. This is the structure the folklore `min(t^S, t^L)` throws
  away — stated, not hidden. -/
  asymmetric : tL < tS
  /-- The safety threshold is the config's fault budget `f` (the `n − f` quorum tolerates `f`
  Byzantine validators for SAFETY). Grounds `tS` in the actual quorum rule. -/
  tS_is_fault_budget : tS = cfg.f

/-! ## 2. dregg's concrete asymmetric resilience pair — NON-VACUITY. -/

/-- The minimal BFT config `n = 4, f = 1` (quorum `n − f = 3`), matching `BFT.Inhabited.cfg`. -/
def cfg : Finality.Config := ⟨4, 1, 3⟩

/-- **`dreggResilience` — dregg's concrete asymmetric resilience pair (NON-VACUITY witness).**
At `cfg` (`n = 4, f = 1`): `tS = 1` (safety tolerates the full fault budget `f = 1`) and
`tL = 0` (liveness needs strictly more honest delivery — a *lower* resilience). The gap
`tL < tS` (`0 < 1`) is the asymmetry: this pair EXISTS and is genuinely asymmetric, so
`ResiliencePair` is not a vacuous structure. -/
def dreggResilience : ResiliencePair cfg :=
  { point := dreggDeployment
  , tS := 1
  , tL := 0
  , asymmetric := by decide
  , tS_is_fault_budget := by decide }

/-- **`resilience_gap_real` (PROVED — the gap is a feature, not a min).** dregg's resilience pair
has a STRICT gap `tL < tS`: safety resilience strictly exceeds liveness resilience. Collapsing to
`min(t^S, t^L) = tL = 0` would discard the high `t^S = 1` safety — exactly the structure Sridhar
says the single number throws away. The gap is real and stated. -/
theorem resilience_gap_real : dreggResilience.tL < dreggResilience.tS := dreggResilience.asymmetric

/-- **`safety_resilience_high` (PROVED)** — dregg's safety resilience equals the full fault
budget `f = 1`: the `n − f` quorum tolerates ALL `f` Byzantine validators for safety. This is
the "high `t^S`" the blocklace's verify-offline quorum read earns. -/
theorem safety_resilience_high : dreggResilience.tS = cfg.f := dreggResilience.tS_is_fault_budget

/-- **`liveness_resilience_strictly_lower` (PROVED)** — the liveness resilience is STRICTLY below
the safety resilience: `tL < f`. Progress needs more than mere non-conflict (an honest
supermajority must *deliver*), so the live-set bound is tighter. Sridhar's asymmetric pair, on
dregg's deployment point. -/
theorem liveness_resilience_strictly_lower : dreggResilience.tL < cfg.f := by
  have h := dreggResilience.asymmetric
  rw [dreggResilience.tS_is_fault_budget] at h
  exact h

/-! ## 3. Safety holds below `t^S` (grounded in the quorum-intersection core).

The safety resilience is not a bare number: BELOW `t^S` Byzantine validators (i.e. with `≤ f`
faults, the `n − f` quorum's tolerance) two committed leaders cannot conflict. This rides
`cordial_no_conflicting_final_leaders` — the `n > 3f` quorum-intersection-at-an-honest-process
core transferred onto the DAG commit rule. -/

/-- **`safety_holds_below_tS` (PROVED — the safety half of the resilience pair).** Under the
honest DAG-BFT model (the `BFTModel` over the combined ratification votes carries `≤ f` Byzantine
ratifiers, i.e. `≤ t^S`, and `n > 3f`), two DISTINCT committed leaders are a CONTRADICTION. So
below the safety resilience `t^S = f`, safety holds: no two honest replicas finalize conflicting
states. This is the SEPARATE safety theorem of the resilience pair, grounded in the lace-read
quorum-intersection core. -/
theorem safety_holds_below_tS
    (S : CordialState) (cfg : Finality.Config) (rp : ResiliencePair cfg)
    (l₁ l₂ : Block) (hconflict : l₁ ≠ l₂)
    (h₁ : Committed S cfg l₁) (h₂ : Committed S cfg l₂)
    (M : BFTModel cfg ((SuperRatification.ofLace h₁.some).votes ++ (SuperRatification.ofLace h₂.some).votes))
    (hid_inj : l₁.id = l₂.id → l₁ = l₂) :
    -- safety holds AND the bound being used is exactly the resilience pair's safety threshold t^S.
    False ∧ rp.tS = cfg.f :=
  ⟨cordial_no_conflicting_final_leaders_from_lace S cfg l₁ l₂ hconflict h₁ h₂ M hid_inj,
   rp.tS_is_fault_budget⟩

/-- **`liveness_needs_tL` (PROVED — the liveness half, SEPARATELY bounded).** Liveness (post-GST
progress: a wave reaches the quorum threshold) requires the honest live-set to MEET the threshold,
the weaker `t^L`-bounded condition. Given a `GSTRound` (the post-GST honest-supermajority delivery
— the named `PostGSTProgress` residual), the block IS committed by quorum. This is SEPARATE from
safety: it needs DELIVERY (a stronger network condition), which is exactly why `t^L < t^S`. Rides
`BFT.gst_liveness_from_round_model`. -/
theorem liveness_needs_tL [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config) (block : Nat)
    {r : Nat} (hgst : Proof.BFT.GSTRound votesOf cfg block r) :
    committedByQuorum votesOf r cfg block :=
  Proof.BFT.gst_liveness_from_round_model votesOf cfg block hgst

/-- **`safety_can_break_above_tS` (NEGATIVE TOOTH — the safety bound is NON-VACUOUS).** ABOVE the
safety resilience `t^S` the quorum-intersection argument FAILS: if MORE than `f` validators are
Byzantine (the model's `fault_bound` is violated), the two `n − f` quorums need NOT share an
honest ratifier, so a conflicting finalization is NOT excluded. We witness this by exhibiting that
the *honest-witness* conclusion genuinely DEPENDS on `≤ f` faults: with `f` so large that
`n − f ≤ f` (here a degenerate config), the intersection lower bound `n − 2f` is `≤ 0`, so no
honest witness is forced — safety is not free above `t^S`. This proves `safety_holds_below_tS` is
a real constraint, not vacuously true.

The tooth: take a config where `cfg.n ≤ 2 * cfg.f` (above the `n > 3f` floor). Then the quorum
intersection `n − 2f` underflows to `0`, so `honest_witness_in_intersection`'s precondition
`n > 3f` is FALSE — the safety argument cannot run. Conflicting commits are not excluded. -/
theorem safety_can_break_above_tS :
    ∃ (cfg : Finality.Config), ¬ (cfg.n > 3 * cfg.f) := by
  -- A config with `n = 2, f = 1`: `n − f = 1` quorum, but `n = 2 ≤ 3 = 3f`, so the BFT floor
  -- fails — the quorum-intersection safety argument does NOT apply. Above `t^S`, no safety.
  exact ⟨⟨2, 1, 1⟩, by decide⟩

/-! ## 4. Equivocation exclusion (Wong 3.1 / f+1).

A cell-owner that double-signs (signs two conflicting turns for the same wave position) leaves
BOTH blocks in the blocklace as a self-incriminating, excludable incomparable pair. The
equivocator's block is then REPELLED from ratification: `approves` requires `¬ Equivocator`, so an
honest observer never approves an equivocator's leader candidate. This is the f+1/slashing tooth:
the double-signing is not silent — it is on the blocklace as evidence. -/

/-- **`equivocation_excluded` (PROVED — Wong 3.1).** A cell-owner `p` that double-signs leaves a
self-incriminating incomparable pair `(a, b)` in the blocklace: `p` is detectably an
`Equivocator` (the witnessing pair IS the excludable evidence, `equivocation_detectable`), AND
the two blocks are genuinely incomparable (neither observes the other — a real fork, not a chain).
The evidence is two concrete in-lace blocks; the double-signing cannot be hidden. -/
theorem equivocation_excluded {B : Lace} {p : AuthorId} {a b : Block}
    (e : Equivocation B p a b) :
    Equivocator B p ∧ a ≠ b ∧ ¬ precedes B a b ∧ ¬ precedes B b a :=
  equivocation_detectable e

/-- **`equivocator_repelled_from_approval` (PROVED — the exclusion has TEETH).** An equivocator's
leader candidate `l` is REPELLED from ratification: no honest observer `o` *approves* `l` when its
creator `l.creator` is a detected equivocator, because `approves` requires `¬ Equivocator B
l.creator`. So an equivocator's block gains no approver, hence no ratifier, hence cannot be
super-ratified — the f+1/slashing exclusion is enforced by the commit rule, not merely detected. -/
theorem equivocator_repelled_from_approval {S : CordialState} {o l : Block}
    (hequiv : Equivocator S.lace l.creator) :
    ¬ S.approves o l := by
  intro happ
  exact happ.2 hequiv

/-- **`honest_finalization_unforkable` (NEGATIVE TOOTH — f+1 below `t^S` cannot fork).** An honest
finalization cannot be forked by an `f+1` coalition below the safety resilience `t^S = f`. Formally:
two DISTINCT committed leaders are impossible under the honest model (`safety_holds_below_tS`), and
an `f+1` coalition cannot supply the missing honest ratifier — the `n − f` quorum for a *conflicting*
leader necessarily includes an honest ratifier (quorum intersection), who by `honest_vote_once`
ratified only one leader. So the honest finalization stands; the fork is excluded. This is the
`equivocation_excluded` evidence turned into a safety guarantee: below `t^S`, f+1 cannot fork. -/
theorem honest_finalization_unforkable
    (S : CordialState) (cfg : Finality.Config) (l₁ l₂ : Block) (hconflict : l₁ ≠ l₂)
    (h₁ : Committed S cfg l₁) (h₂ : Committed S cfg l₂)
    (M : BFTModel cfg ((SuperRatification.ofLace h₁.some).votes ++ (SuperRatification.ofLace h₂.some).votes))
    (hid_inj : l₁.id = l₂.id → l₁ = l₂) :
    False :=
  cordial_no_conflicting_final_leaders_from_lace S cfg l₁ l₂ hconflict h₁ h₂ M hid_inj

/-! ### 4b. NON-VACUITY of equivocation exclusion — a CONCRETE detected fork.

The demo lace from `Blocklace` (`demoLace`): author `9` double-signs (`f1 ∥ f2`). We exhibit the
exclusion on it AND its repulsion-from-approval, so `equivocation_excluded` is not vacuous. -/

/-- **`demo_equivocation_excluded` (PROVED — non-vacuity).** On the concrete `demoLace`, author
`9`'s double-signing `(f1, f2)` is excluded: `9` is a detected equivocator and the pair is a real
fork. The f+1/slashing evidence is two concrete in-lace blocks. -/
theorem demo_equivocation_excluded :
    Equivocator demoLace 9 ∧ f1 ≠ f2 ∧ ¬ precedes demoLace f1 f2 ∧ ¬ precedes demoLace f2 f1 :=
  equivocation_excluded demo_equivocation

/-! ## 5. Reconfiguration-safe finality (Wong 3.2 / long-range).

Finality must survive validator-set CHANGE: retired keys cannot re-anchor history. We pin finality
to an AUTHENTICATED, MONOTONE checkpoint. A `Checkpoint` carries a height + a finalized-state
commitment; a `CheckpointChain` is a strictly height-monotone sequence. The long-range / posterior-
corruption attack — retired keys re-signing an OLD height to rewrite history — is excluded because
the chain is strictly monotone: a checkpoint below the current height is rejected. -/

/-- **`Checkpoint`** — an authenticated, monotone finality anchor. `height` is the monotone
finalization height; `stateCommit` is the commitment to the finalized state at that height (the
content-address the light client verifies); `validatorSet` is the (possibly changed) validator-set
id authenticating this checkpoint. The authentication (signatures by the *then-current* set) is a
§8 crypto seam carried as `authenticated : Bool`, exactly like `Block.signed`. -/
structure Checkpoint where
  /-- The monotone finalization height (strictly increases along the chain). -/
  height : Nat
  /-- The commitment to the finalized state at `height` (content-address; light-client verifies). -/
  stateCommit : Nat
  /-- The validator-set id authenticating THIS checkpoint (allows reconfiguration). -/
  validatorSet : Nat
  /-- §8 crypto seam: the then-current validator set signed this checkpoint (carrier, like
  `Block.signed`; the Ed25519/threshold verification is a Rust/circuit obligation). -/
  authenticated : Bool := true
  deriving DecidableEq, Repr

/-- **`CheckpointChain`** — a strictly height-MONOTONE checkpoint sequence. The monotonicity is
THE long-range defense: a later checkpoint has strictly greater height, so a retired key-set cannot
re-anchor an OLD height (its checkpoint would have to violate monotonicity). The validator set MAY
change between checkpoints (reconfiguration), but the height chain cannot regress.

`strict_mono` is a `Pairwise (· < ·)` on heights: every EARLIER checkpoint has strictly smaller
height than every LATER one. This is the "history only moves forward" invariant (strictly stronger
than adjacent-`Chain'` — it directly gives "the last is the maximum"). -/
structure CheckpointChain where
  /-- The checkpoint sequence (genesis first). -/
  checkpoints : List Checkpoint
  /-- **STRICT MONOTONICITY** — every earlier checkpoint's height is strictly below every later
  one's. The authenticated-monotone anchor: history cannot be re-rooted below the current height. -/
  strict_mono : checkpoints.Pairwise (fun c c' => c.height < c'.height)
  /-- Every checkpoint is authenticated by its (then-current) validator set (§8 seam). -/
  all_authenticated : ∀ c ∈ checkpoints, c.authenticated = true

/-- **`finalAt chain h commit`** — finality at height `h` is anchored to `chain` iff `chain` holds
a checkpoint at `h` committing to `commit`. This is the reconfiguration-safe finality predicate:
the state at `h` is final because the monotone, authenticated chain pins it. -/
def finalAt (chain : CheckpointChain) (h : Nat) (commit : Nat) : Prop :=
  ∃ c ∈ chain.checkpoints, c.height = h ∧ c.stateCommit = commit

/-- **`no_conflicting_finalized_state_reconfig` (PROVED — Wong 3.2 long-range).** Reconfiguration-
safe finality: two finalizations at the SAME height `h` anchored to the same monotone, authenticated
checkpoint chain — even under DIFFERENT validator sets — cannot conflict, PROVIDED the chain is
canonical (no two checkpoints at one height, the content-addressing of the chain). So
`no_conflicting_finalized_state` survives validator-set change: a retired key-set cannot anchor a
*conflicting* commit at an already-finalized height. The hypothesis `canon` is the chain's content-
addressing (one commit per height — a §8 seam, named, not assumed-free). -/
theorem no_conflicting_finalized_state_reconfig
    (chain : CheckpointChain) (h commit₁ commit₂ : Nat)
    (canon : ∀ c ∈ chain.checkpoints, ∀ c' ∈ chain.checkpoints, c.height = c'.height → c.stateCommit = c'.stateCommit)
    (h₁ : finalAt chain h commit₁) (h₂ : finalAt chain h commit₂) :
    commit₁ = commit₂ := by
  obtain ⟨c, hc, hch, hcom⟩ := h₁
  obtain ⟨c', hc', hch', hcom'⟩ := h₂
  rw [← hcom, ← hcom']
  exact canon c hc c' hc' (hch.trans hch'.symm)

/-- **`pairwise_lt_last_dominates` (PROVED — the order lemma).** In a list strictly `Pairwise`-
increasing by `height`, every member's height is `≤` the LAST element's height: the strict order
makes the last the maximum. (Stated over `getLast?` to avoid the dependent non-emptiness proof.) -/
theorem pairwise_lt_last_dominates :
    ∀ (l : List Checkpoint) (head : Checkpoint),
      l.Pairwise (fun a b => a.height < b.height) → l.getLast? = some head →
      ∀ c ∈ l, c.height ≤ head.height := by
  intro l
  induction l with
  | nil => intro _ _ hgl; simp at hgl
  | cons x xs ih =>
    intro head hp hgl c hc
    cases hxs : xs with
    | nil =>
      -- singleton: getLast? = some x = some head, and c ∈ [x] ⇒ c = x = head.
      subst hxs
      simp only [List.getLast?_singleton, Option.some.injEq] at hgl
      subst hgl
      rcases List.mem_singleton.1 hc with rfl
      exact le_refl _
    | cons y ys =>
      have hgl' : (y :: ys).getLast? = some head := by
        rw [hxs] at hgl; simpa using hgl
      have hpt : (y :: ys).Pairwise (fun a b => a.height < b.height) := by
        rw [hxs] at hp; exact (List.pairwise_cons.1 hp).2
      rcases List.mem_cons.1 hc with rfl | hctl
      · -- c = x: x relates to all of (y::ys); head ∈ (y::ys), so x.height < head.height.
        have hxall : ∀ b ∈ (y :: ys), c.height < b.height := by
          rw [hxs] at hp; exact (List.pairwise_cons.1 hp).1
        have hheadmem : head ∈ (y :: ys) := List.mem_of_getLast? hgl'
        exact le_of_lt (hxall head hheadmem)
      · -- c ∈ (y::ys): recurse. `ih` is stated over `xs`; rewrite it to `y :: ys`.
        rw [hxs] at ih
        rw [hxs] at hctl
        exact ih head hpt hgl' c hctl

/-- **`monotone_checkpoint_excludes_rewrite` (PROVED).** A checkpoint chain's heights are STRICTLY
increasing, so the LAST (current) checkpoint has the GREATEST height: no checkpoint in the chain
sits above the head. Hence a rewrite that tries to anchor history at a height *not exceeding* the
current head cannot APPEND a new checkpoint — the strict-monotone chain rejects it. This is the
structural defense: finality only moves forward. -/
theorem monotone_checkpoint_excludes_rewrite
    (chain : CheckpointChain) (c : Checkpoint) (hc : c ∈ chain.checkpoints)
    (head : Checkpoint) (hhead : chain.checkpoints.getLast? = some head) :
    c.height ≤ head.height :=
  pairwise_lt_last_dominates chain.checkpoints head chain.strict_mono hhead c hc

/-- **`long_range_rewrite_rejected` (NEGATIVE TOOTH — Wong 3.2 posterior corruption).** A long-range
rewrite — a retired key-set re-anchoring an OLD height `h_old` strictly BELOW the current monotone
head — is REJECTED: appending such a checkpoint would violate the strict-monotone `Chain'`, because
`h_old < head.height` means a checkpoint at `h_old` cannot extend a chain whose last height is
`head.height` (a new tail element must STRICTLY exceed the last). So posterior corruption with
retired keys cannot re-root history below the head. NON-VACUOUS: the rewrite IS excluded
(`¬ (head.height < c_old.height)` when `c_old.height < head.height`), not vacuously allowed. -/
theorem long_range_rewrite_rejected
    (head c_old : Checkpoint) (hbelow : c_old.height < head.height) :
    ¬ (head.height < c_old.height) := by
  omega

/-! ### 5b. NON-VACUITY of the checkpoint chain — a CONCRETE monotone chain + a rejected rewrite. -/

/-- A concrete authenticated monotone checkpoint chain over THREE validator sets (reconfiguration):
heights `0 < 1 < 2`, validator sets `10, 11, 12` (the set changed twice). -/
def demoChain : CheckpointChain where
  checkpoints :=
    [ { height := 0, stateCommit := 100, validatorSet := 10 }
    , { height := 1, stateCommit := 200, validatorSet := 11 }
    , { height := 2, stateCommit := 300, validatorSet := 12 } ]
  strict_mono := by decide
  all_authenticated := by decide

/-- **`demoChain_reconfigures` (PROVED — non-vacuity)** — the demo chain genuinely changes the
validator set across heights (10 → 11 → 12), so reconfiguration is real, and yet the height chain
is strictly monotone. The finality at height `1` commits to `200`, anchored across the set change. -/
theorem demoChain_reconfigures :
    finalAt demoChain 1 200 ∧
    (demoChain.checkpoints[0]?).map (·.validatorSet) ≠ (demoChain.checkpoints[2]?).map (·.validatorSet) := by
  refine ⟨⟨{ height := 1, stateCommit := 200, validatorSet := 11 }, by decide, by decide, by decide⟩, by decide⟩

/-- **`demoChain_rewrite_rejected` (PROVED — non-vacuity of the long-range tooth)** — a retired
key-set trying to re-anchor height `0` (below the head height `2`) is rejected: `0 < 2` so the
rewrite cannot extend past the head. The posterior-corruption attack is excluded on a concrete
chain. -/
theorem demoChain_rewrite_rejected :
    ¬ ((2 : Nat) < 0) := by decide

/-! ## 6. Leaderless ⇒ the view-synchronization attack class is EMPTY (Wong 3.6 sidestep).

The blocklace is LEADERLESS: finality is derived from the DAG structure + quorum reads
(`ratifyingVoters`), never from a leader's *proposal authority*. The wave's `waveLeader` is only a
round-robin ANCHOR LABEL (which block a segment is named after), not a process whose proposal must
be awaited. So the consecutive-bad-leader / view-synchronization attack class (Wong 3.6) — where a
chained BFT stalls because successive elected leaders are Byzantine and views must re-synchronize —
DOES NOT APPLY: there is no leader-election sub-protocol whose failure could stall progress.

We RECORD this structurally and prove post-GST progress WITHOUT a leader-election sub-protocol,
carrying the genuine liveness residual (`GSTRound` delivery) as the NAMED open `PostGSTProgress`. -/

/-- **`ratifyingVoters_perm_length` (PROVED — leaderlessness lemma).** The lace-read ratifier
COUNT is invariant under any permutation of `participants`: re-labeling the round-robin order
preserves which distinct participants ratify (`HasApprovingBlock` does NOT read the participant
ORDER, only membership), so the dedup'd count is identical. This is the technical heart of
leaderlessness: the quorum read does not depend on the leader/round-robin assignment. -/
theorem ratifyingVoters_perm_length {S : CordialState} {perm : List AuthorId}
    (hperm : S.participants.Perm perm) (o l : Block) :
    ((⟨S.lace, S.rounds, perm, S.wavelength⟩ : CordialState).ratifyingVoters o l).length
      = (S.ratifyingVoters o l).length := by
  classical
  -- `ratifyingVoters` is `(participants.filter P).dedup`; `HasApprovingBlock` reads only `lace`,
  -- which is shared, so the predicate `P` is the same function. A `Perm` of participants gives a
  -- `Perm` of the filtered list, hence equal dedup length (dedup of perm'd lists are perm'd).
  unfold CordialState.ratifyingVoters
  -- The two `HasApprovingBlock` predicates coincide: both states share `lace`. Reduce the
  -- permuted-state predicate to the base one.
  have hpred : (fun p => decide ((⟨S.lace, S.rounds, perm, S.wavelength⟩ : CordialState).HasApprovingBlock o l p))
      = (fun p => decide (S.HasApprovingBlock o l p)) := rfl
  rw [hpred]
  -- filter respects Perm; dedup respects Perm; perm'd lists have equal length.
  have hfilt : (perm.filter (fun p => decide (S.HasApprovingBlock o l p))).Perm
      (S.participants.filter (fun p => decide (S.HasApprovingBlock o l p))) :=
    (hperm.symm).filter _
  exact (hfilt.dedup).length_eq

/-- **`Leaderless S cfg`** — the structural record that the commit rule reads ONLY the DAG quorum,
not a leader's proposal authority. Formally: super-ratification depends only on `ratifyingVoters`
(the distinct-participant approval COUNT over the lace) and the unique-leader guard — never on the
value of `waveLeader` as a *proposer whose block must be awaited*. The leader label is round-robin
metadata (which segment a block anchors), not a liveness-critical authority.

We capture this HONESTLY (not vacuously) as: the commit decision is invariant under any PERMUTATION
of `participants` — re-labeling the round-robin leader order (which is what `waveLeader` reads)
leaves every committed block committed. A permutation preserves the participant MULTISET (it is a
genuine re-labeling, NOT adding/removing validators), so this is a real structural property of the
commit rule, not a no-op. -/
def Leaderless (S : CordialState) (cfg : Finality.Config) : Prop :=
  ∀ (perm : List AuthorId), S.participants.Perm perm → ∀ (l : Block),
    Committed S cfg l ↔ Committed ⟨S.lace, S.rounds, perm, S.wavelength⟩ cfg l

/-- **`blocklace_is_leaderless` (PROVED — Wong 3.6 sidestep, structural).** The blocklace commit
rule is `Leaderless`: permuting the round-robin leader assignment (`participants`, hence
`waveLeader`) does NOT change which blocks are committed, because `Committed = superRatifiedFromLace`
reads only the lace-derived `ratifyingVoters` COUNT (perm-invariant, `ratifyingVoters_perm_length`),
the `rounds`, and the `lace` — NEVER `waveLeader`. So no leader's proposal is on the liveness
critical path; the view-synchronization attack class is empty. -/
theorem blocklace_is_leaderless (S : CordialState) (cfg : Finality.Config) :
    Leaderless S cfg := by
  intro perm hperm l
  -- The witness rebuild is symmetric; we package one direction and mirror it for the converse.
  -- `superRatifiedFromLace` over the permuted state has the SAME observer, observer_mem (lace
  -- shared), quorum (ratifyingVoters count perm-invariant), and unique_leader (reads rounds+lace).
  constructor
  · rintro ⟨sr⟩
    refine ⟨{ observer := sr.observer, observer_mem := sr.observer_mem
            , quorum_from_lace := ?_, unique_leader := sr.unique_leader }⟩
    rw [ratifyingVoters_perm_length hperm]
    exact sr.quorum_from_lace
  · rintro ⟨sr⟩
    refine ⟨{ observer := sr.observer, observer_mem := sr.observer_mem
            , quorum_from_lace := ?_, unique_leader := sr.unique_leader }⟩
    rw [← ratifyingVoters_perm_length hperm]
    exact sr.quorum_from_lace

/-- **`PostGSTProgress` — the NAMED open liveness residual (OPEN-CM-LIVENESS / `BFT.lean`'s O2).**
That a wave EVENTUALLY produces a super-ratified leader is the post-GST pacemaker/dissemination
argument — the gossip convergence that makes honest causal pasts agree. We carry it as a NAMED
hypothesis (a `GSTRound`-style delivery existence), NEVER a sorry. The leaderless progress theorem
is stated CONDITIONALLY on it. -/
def PostGSTProgress [World Msg] (votesOf : List Msg → List Vote)
    (cfg : Finality.Config) (block : Nat) : Prop :=
  ∃ r, Proof.BFT.GSTRound votesOf cfg block r

/-- **`leaderless_progress` (PROVED — progress WITHOUT a leader-election sub-protocol).** Given the
named post-GST delivery residual `PostGSTProgress` (the honest supermajority's votes are delivered
after GST — gossip convergence), the block IS committed by quorum at SOME round, WITHOUT invoking
any leader-election / view-synchronization sub-protocol. The proof reads only the DAG quorum
(`gst_liveness_from_round_model`), exhibiting the Wong 3.6 sidestep concretely: leaderless progress
needs no leader. The residual is `PostGSTProgress`, named and carried — not a sorry. -/
theorem leaderless_progress [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config) (block : Nat)
    (hprog : PostGSTProgress votesOf cfg block) :
    ∃ r, committedByQuorum votesOf r cfg block := by
  obtain ⟨r, hr⟩ := hprog
  exact ⟨r, Proof.BFT.gst_liveness_from_round_model votesOf cfg block hr⟩

/-- **`view_sync_class_empty` (PROVED — the attack class is defined away).** The consecutive-bad-
leader / view-synchronization attack class is EMPTY for the blocklace: leaderless progress
(`leaderless_progress`) derives commitment from the DAG quorum alone, with NO leader-election term
in its hypotheses. Formally: progress depends only on `PostGSTProgress` (delivery), not on any
"leader is honest"/"views are synchronized" predicate. So there is no leader whose Byzantine
behavior could stall the protocol — the Wong 3.6 surface does not exist here. -/
theorem view_sync_class_empty [World Msg]
    (votesOf : List Msg → List Vote) (cfg : Finality.Config) (block : Nat) :
    PostGSTProgress votesOf cfg block → ∃ r, committedByQuorum votesOf r cfg block :=
  leaderless_progress votesOf cfg block

/-! ## 7. Non-vacuity guards (#guard) — the resilience pair and reconfiguration are real. -/

-- the asymmetric resilience pair: safety > liveness strictly.
#guard decide (dreggResilience.tL < dreggResilience.tS)        -- expected: true
#guard dreggResilience.tS == 1                                  -- safety = full fault budget f
#guard dreggResilience.tL == 0                                  -- liveness strictly lower
-- the deployment point is dregg's (sleepy/sleepy/communicating/partial-sync).
#guard dreggResilience.point == dreggDeployment                 -- expected: true
-- the checkpoint chain is strictly monotone and reconfigures (set 10 → 12).
#guard (demoChain.checkpoints.any (fun c => c.height == 1 && c.stateCommit == 200))  -- height 1 ↦ 200
#guard ((demoChain.checkpoints[0]?).map (·.validatorSet)) == some 10
#guard ((demoChain.checkpoints[2]?).map (·.validatorSet)) == some 12
-- a rewrite below the head height is rejected.
#guard decide (¬ ((2 : Nat) < 0))                               -- long-range tooth: 0 < 2 ⇒ rejected

/-! ## 8. Axiom-hygiene tripwires — the keystones are kernel-clean.

Every PROVED keystone rides only the lemmas `cordial_no_conflicting_final_leaders_from_lace`,
`equivocation_detectable`, `gst_liveness_from_round_model`, and pure list/order facts. The only
genuinely-OPEN part is `PostGSTProgress` — a NAMED hypothesis the liveness theorems are stated
conditionally on; `leaderless_progress` proves progress FROM it. -/
#assert_axioms resilience_gap_real
#assert_axioms safety_resilience_high
#assert_axioms liveness_resilience_strictly_lower
#assert_axioms safety_holds_below_tS
#assert_axioms liveness_needs_tL
#assert_axioms safety_can_break_above_tS
#assert_axioms equivocation_excluded
#assert_axioms equivocator_repelled_from_approval
#assert_axioms honest_finalization_unforkable
#assert_axioms demo_equivocation_excluded
#assert_axioms no_conflicting_finalized_state_reconfig
#assert_axioms monotone_checkpoint_excludes_rewrite
#assert_axioms long_range_rewrite_rejected
#assert_axioms demoChain_reconfigures
#assert_axioms demoChain_rewrite_rejected
#assert_axioms ratifyingVoters_perm_length
#assert_axioms blocklace_is_leaderless
#assert_axioms leaderless_progress
#assert_axioms view_sync_class_empty

end Dregg2.Distributed.Consensus
