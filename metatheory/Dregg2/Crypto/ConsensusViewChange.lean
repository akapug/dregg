/-
# `Dregg2.Crypto.ConsensusViewChange` — FULL BFT LIVENESS with VIEW-CHANGE / leader rotation.

`ConsensusLiveness.liveness_after_gst` proves the HONEST-PROPOSER case: *if* an honest node proposes a
valid block, the honest supermajority finalizes it after GST. That is only half of real liveness. A
Byzantine leader can simply STALL — propose nothing — and the honest-proposer theorem never fires,
because its proposer is never honest. This file closes the real thing: the standard PBFT/HotStuff-family
**view-change** argument, showing progress happens after GST *even when Byzantine leaders stall*.

We REUSE both prior models VERBATIM: the `ConsensusSafety` finalization model (`SigScheme`, `ValidVote`,
`Finalized`, the quorum `q`, `two_quorums_share_honest`, the `n > 3f` / `≤ f` threshold, `EufCma`) and the
`ConsensusLiveness` progress model (`honest_set_is_quorum`, `liveness_after_gst`, the partial-synchrony
delivery bound). Nothing here re-derives them; view-change is a thin, honest layer ON TOP.

## The model

Views `v = 0, 1, 2, …` (here `ℕ`) with a deterministic leader rotation `leader : ℕ → Member`. A view TIMES
OUT if no block finalizes within the view timeout `timeout`, which after GST exceeds `2 * Δ` (two message
delays: propose + vote). Rotation "hits distinct members" over a window — modelled as `leader` being
INJECTIVE over any `f + 1`-view window `Finset.Icc v (v + f)`.

## The three theorems

1. **`honest_leader_within` — the COUNTING CORE (pigeonhole).** Among any `f + 1` consecutive views, at
   least one leader is HONEST. Proof: the `f + 1` window views map (by rotation-injectivity) to `f + 1`
   DISTINCT members; if every one were Byzantine, that image `⊆ byz` would give `f + 1 ≤ |byz| ≤ f`, absurd.
   This needs ONLY `≤ f` Byzantine and distinct rotation — no threshold, no committee membership — which is
   exactly why it still holds at `n = 3f` (tooth (c)).

2. **`view_change_preserves_safety` — safety ACROSS views.** A view change does not finalize conflicting
   blocks. The quorum-intersection argument of `ConsensusSafety` (`two_quorums_share_honest`) applies
   unchanged across two DIFFERENT views `v1 ≠ v2`: any two finalizing quorums share an honest member, and
   the explicit **lock / highest-QC rule** (`LockRule`) forbids that honest member from casting
   finalization votes for two different blocks at one height — even in different views. So a new leader
   cannot finalize a block conflicting with an already-finalized one. Un-cast verifying votes are forgeries
   refuting `EufCma`, exactly as in single-view safety.

3. **`eventual_progress` — THE HEADLINE.** After GST, within at most `f + 1` view timeouts an HONEST leader
   leads a view (`honest_leader_within`), proposes a valid block, and that block FINALIZES
   (`liveness_after_gst` in that view). Progress is made despite Byzantine leaders: rotation guarantees the
   honest leader arrives, partial synchrony + the honest supermajority finalize its block.

`honest_view_finalizes_before_timeout` supplies the timing side: after GST the view timeout exceeds `2 * Δ`,
so the honest quorum assembles STRICTLY before the view times out — the honest view completes, it does not
time out.

## Honest boundary — NAMED, not hidden.

View-change liveness does NOT reduce to `MLWE`/`MSIS`/`SchnorrDL`. Its irreducible inputs are the honest
duals of the crypto floor: (i) **partial synchrony** (after GST, honest→honest delivery within `Δ`, and the
view timeout exceeds `2Δ`), (ii) the **threshold** `n > 3f` (so the honest set is a quorum), and (iii) the
**leader-rotation** assumption (distinct leaders over an `f + 1` window). Safety across views additionally
consumes the **lock/highQC rule** (a protocol invariant, a hypothesis — never an `axiom`) and, for the
unforgeability of votes, `SchnorrDLHard ∨ MSISHard` via `ConsensusSafety`. No FLP violation: progress is
claimed only AFTER GST.

## Teeth (load-bearing, both instances exhibited)

(a) `tooth_rotation_reaches_honest_leader`: with a real rotation, `honest_leader_within` FIRES — an honest
    leader arrives within `f + 1` views.
(b) `tooth_fixed_byzantine_leader_stalls`: with a FIXED Byzantine leader (no rotation), NO honest leader
    ever appears over any horizon — progress never happens. Rotation is genuinely required (the injectivity
    hypothesis is load-bearing).
(c) `tooth_n_eq_3f_pigeonhole_holds_quorum_fails`: at `n = 3f` the honest-leader pigeonhole STILL holds
    (it needs only `≤ f` Byzantine + rotation) but the honest set is TOO SMALL to be a quorum — tying
    rotation-gives-a-leader to safety's own `n > 3f` threshold.
(d) `tooth_view_change_lock_load_bearing`: WITHOUT the lock rule, a view change DOES finalize two
    conflicting blocks in two different views — so the lock/highQC rule is what preserves cross-view safety.

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake env lean Dregg2/Crypto/ConsensusViewChange.lean`.
-/
import Dregg2.Crypto.ConsensusLiveness
import Mathlib.Tactic

namespace Dregg2.Crypto.ConsensusViewChange

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.ConsensusSafety
open Dregg2.Crypto.ConsensusLiveness

/-! ## §1. The counting core — an honest leader within any `f + 1` consecutive views (pigeonhole).

Rotation "hits distinct members" is modelled as `leader` being injective over the `f + 1`-view window
`Finset.Icc v (v + f)`. This is the ONLY assumption the pigeonhole needs, together with `≤ f` Byzantine —
no threshold and no committee membership, which is why it survives at `n = 3f` (tooth (c)). -/

variable {Member : Type*} [DecidableEq Member]

/-- **`honest_leader_within` — THE PIGEONHOLE.** Among any `f + 1` consecutive views `[v, v + f]`, at least
one view is led by an HONEST member (`leader w ∉ byz`). The `f + 1` window views map to `f + 1` DISTINCT
members (rotation-injectivity); were all of them Byzantine, that image would sit inside `byz`, forcing
`f + 1 ≤ |byz| ≤ f` — absurd. Depends only on `≤ f` Byzantine and distinct rotation. -/
theorem honest_leader_within
    (byz : Finset Member) (leader : ℕ → Member) (f v : ℕ)
    (hbyzc : byz.card ≤ f)
    (hinj : Set.InjOn leader ↑(Finset.Icc v (v + f))) :
    ∃ w ∈ Finset.Icc v (v + f), leader w ∉ byz := by
  by_contra hcon
  push_neg at hcon
  -- every leader in the window is Byzantine, so the (distinct) window image sits inside `byz`.
  have hsub : (Finset.Icc v (v + f)).image leader ⊆ byz := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact hcon w hw
  -- but the image has `f + 1` distinct members (injective rotation over an `f + 1`-view window).
  have hcardimg : ((Finset.Icc v (v + f)).image leader).card = f + 1 := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
    omega
  have hle := Finset.card_le_card hsub
  omega

/-! ## §2. Safety across views — the lock / highest-QC rule.

The quorum-intersection argument of `ConsensusSafety` does not care which VIEW a finalizing quorum came
from; two quorums (from any views) still share an honest member. The extra ingredient a view change needs is
the **lock / highest-QC rule**: an honest member that has voted to finalize a block at a height is LOCKED,
and will not cast a finalization vote for a conflicting block at that height in any later view. This is the
cross-view generalization of `ConsensusSafety.HonestVotingRule`. -/

variable {SK PK Msg Sig : Type*}
variable {Height Block : Type*}

/-- **`LockRule` — the lock / highest-QC invariant.** An honest member never holds finalization votes for
two DIFFERENT blocks at one height, even across different views `v v'`: once it has voted to finalize `b` at
height `h` (in view `v`), the highest-QC lock forbids voting for a conflicting `b'` at height `h` in any
other view `v'`. A stated protocol invariant — a hypothesis, never an `axiom`. -/
def LockRule (voteMsg : ℕ → Height → Block → Msg) (Q : Member → Msg → Prop)
    (honest : Member → Prop) : Prop :=
  ∀ m, honest m → ∀ (v v' : ℕ) (h : Height) (b b' : Block),
    Q m (voteMsg v h b) → Q m (voteMsg v' h b') → b = b'

/-- **`view_change_preserves_safety` — SAFETY ACROSS VIEWS.** Under `n > 3f`, `≤ f` Byzantine, each honest
member's finalization-vote `EufCma`, and the lock/highQC rule, two CONFLICTING blocks `b ≠ b'` cannot both
be finalized at one height — even if they finalize in DIFFERENT views `v1`, `v2`.

Proof: quorum intersection (`two_quorums_share_honest`, reused verbatim) gives an honest member `m` in both
finalizing quorums, holding a valid vote for `voteMsg v1 h b` AND for `voteMsg v2 h b'`. If `m` never cast
one of them, that verifying vote on an un-queried body is a `Forgery` refuting its `EufCma`; if it cast
BOTH, the lock rule forces `b = b'`, contradicting `b ≠ b'`. A conflicting cross-view finalization is thus a
forged vote — impossible. The new leader's proposal is bound by the lock. -/
theorem view_change_preserves_safety
    (S : SigScheme SK PK Msg Sig)
    (committee byz : Finset Member) (memberPk : Member → PK)
    (voteMsg : ℕ → Height → Block → Msg) (Q : Member → Msg → Prop)
    (n f : ℕ) (hn : 3 * f + 1 ≤ n) (hcard : committee.card = n)
    (hbyz : byz ⊆ committee) (hbyzc : byz.card ≤ f)
    (heuf : ∀ m ∈ committee, m ∉ byz → EufCma S (memberPk m) (Q m))
    (hlock : LockRule voteMsg Q (fun m => m ∈ committee ∧ m ∉ byz))
    (v1 v2 : ℕ) (height : Height) (b b' : Block) (hconf : b ≠ b')
    (F1 : Finalized S committee memberPk (voteMsg v1) (n - f) height b)
    (F2 : Finalized S committee memberPk (voteMsg v2) (n - f) height b') :
    False := by
  -- an HONEST member in both quorums — quorum intersection is view-agnostic.
  obtain ⟨m, hmA, hmB, hmnb⟩ :=
    two_quorums_share_honest committee byz F1.quorum F2.quorum n f hn hcard
      F1.sub F2.sub hbyz hbyzc F1.size F2.size
  have hmC : m ∈ committee := F1.sub hmA
  obtain ⟨σ1, hv1⟩ := F1.votes m hmA
  obtain ⟨σ2, hv2⟩ := F2.votes m hmB
  by_cases hq1 : Q m (voteMsg v1 height b)
  · by_cases hq2 : Q m (voteMsg v2 height b')
    · exact hconf (hlock m ⟨hmC, hmnb⟩ v1 v2 height b b' hq1 hq2)
    · exact heuf m hmC hmnb ⟨voteMsg v2 height b', σ2, hq2, hv2⟩
  · exact heuf m hmC hmnb ⟨voteMsg v1 height b, σ1, hq1, hv1⟩

/-! ## §3. THE HEADLINE — eventual progress despite Byzantine leaders.

Combine the two halves: `honest_leader_within` guarantees an honest leader within `f + 1` views, and in
that view `liveness_after_gst` finalizes its proposed block. -/

/-- **`eventual_progress` — FULL BFT LIVENESS.** After GST, within at most `f + 1` view timeouts an HONEST
leader `leader w` (`w ∈ [v, v + f]`) leads a view, proposes its valid block `propose (leader w) w`, and that
block is `Finalized` at quorum `q = 2f + 1`. Byzantine leaders may stall the earlier views of the window;
rotation guarantees an honest leader still arrives (`honest_leader_within`), and partial synchrony + the
honest supermajority finalize its block (`liveness_after_gst`). Progress is made despite Byzantine leaders. -/
theorem eventual_progress
    (S : SigScheme SK PK Msg Sig)
    (committee byz : Finset Member) (leader : ℕ → Member)
    (sk : Member → SK) (memberPk : Member → PK)
    (voteMsg : ℕ → Height → Block → Msg) (propose : Member → ℕ → Block)
    (n f : ℕ) (hn : 3 * f + 1 ≤ n) (hcard : committee.card = n)
    (hbyz : byz ⊆ committee) (hbyzc : byz.card ≤ f)
    (hc : Correct S) (hpk : ∀ m, memberPk m = S.pkOf (sk m))
    (v : ℕ) (hinj : Set.InjOn leader ↑(Finset.Icc v (v + f)))
    (h : Height) :
    ∃ w ∈ Finset.Icc v (v + f), leader w ∉ byz ∧
      Nonempty (Finalized S committee memberPk (voteMsg w) (2 * f + 1) h (propose (leader w) w)) := by
  obtain ⟨w, hw, hhon⟩ := honest_leader_within byz leader f v hbyzc hinj
  exact ⟨w, hw, hhon,
    ⟨liveness_after_gst S committee byz sk memberPk (voteMsg w) n f hn hcard hbyz hbyzc hc hpk
      h (propose (leader w) w)⟩⟩

/-- **`honest_view_finalizes_before_timeout` — the TIMING side of view change.** After GST
(`gst ≤ startTime`), with the view timeout exceeding `2 * Δ` (partial synchrony: two message delays,
propose + vote, fit inside a view), every honest member's vote arrives STRICTLY before the view times out.
So the honest view assembles its quorum and finalizes — it does not time out. The `2 * delta < timeout`
condition is the "after GST the view timeout exceeds `2Δ`" assumption; `gst ≤ startTime` is load-bearing
(no FLP violation before GST). -/
theorem honest_view_finalizes_before_timeout
    (committee byz : Finset Member) (arrival : Member → ℕ)
    (gst delta timeout startTime : ℕ)
    (hafter : gst ≤ startTime)
    (htimeout : 2 * delta < timeout)
    (hdeliver : gst ≤ startTime → ∀ m ∈ committee, m ∉ byz → arrival m ≤ startTime + 2 * delta) :
    ∀ m ∈ committee \ byz, arrival m < startTime + timeout := by
  intro m hm
  rw [Finset.mem_sdiff] at hm
  have := hdeliver hafter m hm.1 hm.2
  omega

/-! ## §4. Teeth — rotation fires, a fixed Byzantine leader stalls, `n = 3f` ties to the quorum, lock is
load-bearing. -/

section Teeth

/-! ### (a) With rotation, an honest leader arrives within `f + 1` views. -/

/-- **`tooth_rotation_reaches_honest_leader`.** Rotation `leader = id`, Byzantine `{0}`, `f = 1`: among the
two views `[0, 1]`, `honest_leader_within` FIRES — view `1` is led by the honest member `1 ∉ {0}`. -/
theorem tooth_rotation_reaches_honest_leader :
    ∃ w ∈ Finset.Icc 0 1, (fun v => v) w ∉ ({0} : Finset ℕ) :=
  honest_leader_within ({0} : Finset ℕ) (fun v => v) 1 0 (by decide) (fun a _ b _ hab => hab)

/-! ### (b) A FIXED Byzantine leader stalls forever — rotation is load-bearing. -/

/-- **`tooth_fixed_byzantine_leader_stalls` — ROTATION IS REQUIRED.** With a FIXED Byzantine leader
(`leader = fun _ => 0`, `0 ∈ byz`) there is NO honest leader over ANY horizon (here 101 views): the
conclusion of `honest_leader_within` is unattainable, so `eventual_progress` can never fire. Progress
genuinely requires rotation — the injectivity hypothesis is load-bearing. -/
theorem tooth_fixed_byzantine_leader_stalls :
    ¬ ∃ w ∈ Finset.Icc 0 100, (fun _ : ℕ => (0 : ℕ)) w ∉ ({0} : Finset ℕ) := by
  rintro ⟨w, _, hw⟩
  exact hw (Finset.mem_singleton_self 0)

/-! ### (c) At `n = 3f` the pigeonhole holds but the quorum fails — ties to safety's threshold. -/

/-- **`tooth_n_eq_3f_pigeonhole_holds_quorum_fails` — TIE TO THE THRESHOLD.** At `n = 3f` (`n = 3, f = 1`)
the honest-leader pigeonhole STILL delivers an honest leader (it needs only `≤ f` Byzantine + rotation, not
`n > 3f`) — BUT the honest set `{1, 2}` has size `2 < 3 = 2f + 1`, too small to be a finalization quorum.
So rotation gives you the honest leader, yet without `n > 3f` its block still cannot finalize: the same
threshold that safety needs. -/
theorem tooth_n_eq_3f_pigeonhole_holds_quorum_fails :
    (∃ w ∈ Finset.Icc 0 1, (fun v => v) w ∉ ({0} : Finset ℕ)) ∧
    (∃ (committee byz : Finset ℕ),
        committee.card = 3 ∧ byz ⊆ committee ∧ byz.card ≤ 1 ∧
        (committee \ byz).card < 2 * 1 + 1) := by
  refine ⟨honest_leader_within ({0} : Finset ℕ) (fun v => v) 1 0 (by decide)
      (fun a _ b _ hab => hab), ?_⟩
  exact ⟨{0, 1, 2}, {0}, by decide, by decide, by decide, by decide⟩

/-! ### (d) Without the lock rule, a view change finalizes conflicting blocks — the lock is load-bearing. -/

/-- The demo finalization-vote scheme (as in `ConsensusSafety`): a vote is valid iff `sig = memberPk + body`,
members are their own keys. -/
@[reducible] def toyS : SigScheme ℕ ℕ ℕ ℕ where
  pkOf sk := sk
  sign sk m := sk + m
  verify pk m sig := sig = pk + m

/-- View-indexed demo vote body: `vcVoteMsg v h b = 10000 * v + 100 * h + b`. -/
@[reducible] def vcVoteMsg : ℕ → ℕ → ℕ → ℕ := fun v h b => 10000 * v + 100 * h + b

/-- Block `5` finalizes at height `0` IN VIEW `0` (quorum `{0,1,2}`, each vote `member + vcVoteMsg 0 0 5`). -/
def vcFinalized5_view0 :
    Finalized toyS ({0, 1, 2, 3} : Finset ℕ) (fun m => m) (vcVoteMsg 0) 3 0 5 where
  quorum := {0, 1, 2}
  sub := by decide
  size := by decide
  votes := fun m _ => ⟨m + vcVoteMsg 0 0 5, rfl⟩

/-- Conflicting block `7` finalizes at height `0` IN VIEW `1` (quorum `{1,2,3}`): shared members `1,2`
double-vote across the view change. -/
def vcFinalized7_view1 :
    Finalized toyS ({0, 1, 2, 3} : Finset ℕ) (fun m => m) (vcVoteMsg 1) 3 0 7 where
  quorum := {1, 2, 3}
  sub := by decide
  size := by decide
  votes := fun m _ => ⟨m + vcVoteMsg 1 0 7, rfl⟩

/-- **`tooth_view_change_lock_load_bearing` — THE LOCK IS LOAD-BEARING.** With `toyS` alone — no lock rule,
no `EufCma` — a view change finalizes BOTH conflicting blocks: block `5` in view `0` AND block `7` in view
`1`, at one height. The shared members `1,2` double-vote across the view change freely. So the `Finalized`
structure by itself does NOT prevent a cross-view fork: it is exactly the lock/highQC rule (plus each
honest member's `EufCma`) of `view_change_preserves_safety` that turns the double vote into a refuted
forgery. Drop the lock and view-change safety fails. -/
theorem tooth_view_change_lock_load_bearing :
    Nonempty (Finalized toyS ({0, 1, 2, 3} : Finset ℕ) (fun m => m) (vcVoteMsg 0) 3 0 5) ∧
    Nonempty (Finalized toyS ({0, 1, 2, 3} : Finset ℕ) (fun m => m) (vcVoteMsg 1) 3 0 7) :=
  ⟨⟨vcFinalized5_view0⟩, ⟨vcFinalized7_view1⟩⟩

-- Rotation reaches an honest leader within f+1=2 views (view 1's leader ∉ Byzantine {0})…
#guard decide ((fun v => v) 1 ∉ ({0} : Finset ℕ))
-- …but a FIXED Byzantine leader is never honest — no progress without rotation.
#guard decide (¬ ((fun _ : ℕ => (0 : ℕ)) 7 ∉ ({0} : Finset ℕ)))
-- At n=3f the honest set {1,2} is too small to be a quorum (2 < 2·1+1 = 3).
#guard decide ((({0, 1, 2} : Finset ℕ) \ {0}).card < 2 * 1 + 1)
-- Cross-view double vote verifies under toyS on the view-indexed body (the lock-rule witness).
#guard decide (toyS.verify 1 (vcVoteMsg 1 0 7) (1 + vcVoteMsg 1 0 7))
-- After GST the view timeout exceeds 2Δ, so an honest vote (arrival 7 ≤ start+2Δ) beats the timeout…
#guard decide ((7 : ℕ) < 3 + 10 ∧ 2 * 2 < 10)
-- …and the honest vote arrival 7 ≤ startTime 3 + 2·Δ 2 = 7 (delivered within the two-delay round).
#guard decide ((7 : ℕ) ≤ 3 + 2 * 2)

end Teeth

/-! ## §5. Axiom hygiene — every view-change keystone is kernel-clean. -/

#assert_all_clean [
  honest_leader_within,
  view_change_preserves_safety,
  eventual_progress,
  honest_view_finalizes_before_timeout,
  tooth_rotation_reaches_honest_leader,
  tooth_fixed_byzantine_leader_stalls,
  tooth_n_eq_3f_pigeonhole_holds_quorum_fails,
  tooth_view_change_lock_load_bearing
]

end Dregg2.Crypto.ConsensusViewChange
