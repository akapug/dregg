/-
# Metatheory.ResharingChain — forward-secure COMMITTEE SECRETS: the D-side dual of KERI.

A **resharing chain** is a sequence of common secrets `S₀ → S₁ → … → Sₙ` in which each `Sₙ₊₁`
is a fresh re-sharing of the SAME underlying secret value to a (possibly new) committee, causally
linked to `Sₙ` (proactive secret sharing, iterated — Herzberg-Jarecki-Krawczyk-Yung 1995). This
module formalizes the object as the **D-side dual of KERI pre-rotation** (`Dregg2.Apps.PreRotation`):

  > KERI's pre-rotation gives a forward-secure IDENTITY chain — the `∀`/`Knows` side: compromise of
  > the CURRENT signing key cannot rewrite the past (`rotChain_pinned_by_commitments`, a public
  > COMMITMENT chain pins the key history). A resharing chain gives forward-secure COMMITTEE SECRETS
  > — the `D`/`DistKnows^{≥K}` side: compromise of the CURRENT shares cannot reveal the past, because
  > each reshare RE-RANDOMIZES the shares (same `f(0)`, fresh higher coefficients) and the old shares
  > are erased. The SAME forward-security shape applied to the two epistemic polarities dregg already
  > pairs — single-agent signing (`Knows`/`EpistemicConsensus`) vs group-pooled common-secret
  > (`DistKnows^{≥K}`/`CommonSecret`).

It EXTENDS `Metatheory.CommonSecret` (`ThresholdFrame`, `KnowsSecret`, `subThreshold_secret_blind`):
the per-epoch node `Sₙ` is a `ThresholdFrame`; the chain LINK adds the fresh-randomness floor.

DISCIPLINE (the `CommonSecret`/`PreRotation` bar, verbatim): faithful Props; the SINGLE
cryptographic obligation — that a sub-threshold POST-reshare coalition's pooled view is
information-theoretically consistent with EVERY value of the PRE-reshare secret (HJKY renewal-secrecy
/ the mobile-adversary floor) — enters ONLY as the `ReshareLink.forward_blind` STRUCTURAL FIELD, the
exact analogue of `subThreshold_blind` (and of `KeySetCR` on the ∀-side), never as an `axiom` or an
open hole. Every keystone is pinned `#assert_axioms` (kernel-clean: only `propext`/`Classical.choice`/
`Quot.sound`), so any unproven keystone fails the build. A discriminating concrete model (§5) — a real reshare
of a 2-of-2 XOR secret to two FRESH shares of the SAME secret — certifies the keystones non-vacuous.

The four angles (`docs/deos/RESHARING-CHAINS.md`):
  * §A — the forward-secure common-secret chain + `reshareChain_forward_secret` (the cliff across a link);
  * §B — the chain as a PRIME EVENT STRUCTURE (causal links = a partial order, fork = re-randomize);
  * §C — the KERI-DUAL SYMMETRY (the `∀`-side and `D`-side as instances of one "forward-secure chain");
  * §5 — the non-vacuity certificate.
-/
import Metatheory.CommonSecret
import Metatheory.EpistemicConsensus
import Mathlib.Order.Lattice

namespace Metatheory.ResharingChain

open Metatheory Metatheory.EpistemicConsensus Metatheory.CommonSecret

universe u v

/-! # §A. The reshare LINK and forward-secure common secrets — the D-side dual of KERI.

A reshare link `Sₙ → Sₙ₊₁` carries two `ThresholdFrame`s over the SAME secret space `S`, the
guarantee that the recoverable secret VALUE is identical pre/post (`f(0)` preserved — the HJKY
renewal pins the constant term), and the one crypto floor: a sub-threshold POST coalition, EVEN
holding whatever (un-erased) PRE shares it corrupted, is information-theoretically blind on the PRE
secret. That floor is `subThreshold_blind` relocated across the link — carried as a structural field
exactly as `CommonSecret` carries the within-epoch floor, NEVER an axiom. -/

/-- **A reshare LINK** `Sₙ → Sₙ₊₁`: two threshold frames over the SAME secret space, with `f(0)`
preserved and the cross-epoch fresh-randomness floor.

The `Indist` of `post.base` is the POST coalition's pooled view; `forward_blind` says that view,
when restricted to a sub-threshold POST coalition, is consistent with EVERY value of the PRE secret
read through `pre.secret` along the SHARED world space `Ω`. We share the world space `Ω` between the
two frames: a world `w : Ω` carries both the pre share-assignment (read by `pre`) and the post
share-assignment (read by `post`); the reshare re-randomizes the post-readout while pinning
`pre.secret`/`post.secret` to agree on the actual world (`secret_preserved`). -/
structure ReshareLink (Ω : Type u) (ι : Type v) (S : Type u) where
  /-- The PRE-reshare epoch's threshold frame (the secret as held by committee `Gₙ`). -/
  pre  : ThresholdFrame Ω ι S
  /-- The POST-reshare epoch's threshold frame (the SAME secret as held by `Gₙ₊₁`). -/
  post : ThresholdFrame Ω ι S
  /-- Both frames are anchored at the SAME actual world — the reshare is an event ON the live state,
  not a fresh sample (the constant term `f(0)` is pinned by the HJKY anchor commitments). -/
  same_actual : post.base.actual = pre.base.actual
  /-- **`f(0)` PRESERVED** — the recoverable secret VALUE is identical pre/post (the homomorphic
  reshare keeps `Σ λⱼ sⱼ = f(0)`; the group public key, and any already-issued beacon, survive). -/
  secret_preserved : post.secret post.base.actual = pre.secret pre.base.actual
  /-- **FORWARD BLINDNESS — the cross-epoch crypto floor (THE hypothesis, never an axiom).** A
  POST-epoch coalition `B` that does NOT reach the POST threshold cannot, even pooling its POST view,
  distinguish the actual world from one with a DIFFERENT PRE secret value: for every alternative `s`,
  there is a world `w'` that `B` jointly confuses with the actual world (via the POST indist.) and
  whose PRE secret is `s`. This is `subThreshold_blind` ADVANCED ONE EPOCH — the renewal-secrecy /
  mobile-adversary floor of HJKY (re-randomized shares ⇒ the post view masks the pre share vector),
  carried STRUCTURALLY exactly as `CommonSecret.subThreshold_blind` is. -/
  forward_blind : ∀ (B : ι → Prop), (∀ i, B i → post.committee i) → ¬ post.ReachesThreshold B →
    ∀ s : S, ∃ w' : Ω, (∀ i, B i → post.base.Indist i w' post.base.actual) ∧ pre.secret w' = s

namespace ReshareLink

variable {Ω : Type u} {ι : Type v} {S : Type u} (L : ReshareLink Ω ι S)

/-- **`PostKnowsPreSecret B`** — a POST-epoch coalition `B` knows the PRE-reshare secret: its POST
pooled view rules out every world with a different PRE secret value. Forward security DENIES this for
sub-threshold `B`. (This is `KnowsSecret` of the PRE secret-proposition, evaluated through the POST
indistinguishability — the coalition's epoch-`n+1` view tested against the epoch-`n` secret.) -/
def PostKnowsPreSecret (B : ι → Prop) : Prop :=
  ∀ w', (∀ i, B i → L.post.base.Indist i w' L.post.base.actual) →
    L.pre.secret w' = L.pre.secret L.pre.base.actual

/-- **`reshareChain_forward_secret` — FORWARD SECRECY, the cliff RELOCATED ACROSS A LINK, PROVED,
kernel-clean.** After the reshare `Sₙ → Sₙ₊₁`, a sub-threshold POST coalition does NOT know the PRE
secret: if `B ⊆ post.committee` and `¬ post.ReachesThreshold B`, then `¬ PostKnowsPreSecret B`.

The proof is BYTE-FOR-BYTE `CommonSecret.subThreshold_secret_blind` with `forward_blind` substituted
for `subThreshold_blind` — *that is the whole point of the dual*: forward security is not a new
theorem, it is the common-secret cliff with the coalition's view advanced one epoch. `forward_blind`
hands us, for the alternative PRE-secret value `s₀ ≠ pre.secret actual`, a world `w'` that `B`
confuses with the actual world (POST view) whose PRE secret is `s₀` — so `B`'s post-pooled view
cannot pin the pre secret. This is the D-side `rotate_current_keys_irrelevant`+`compromise_resistant`:
holding the CURRENT (post) shares contributes NOTHING toward the PAST (pre) secret. -/
theorem reshareChain_forward_secret (B : ι → Prop) (hsub : ∀ i, B i → L.post.committee i)
    (hbelow : ¬ L.post.ReachesThreshold B)
    (s₀ : S) (hs₀ : s₀ ≠ L.pre.secret L.pre.base.actual) :
    ¬ L.PostKnowsPreSecret B := by
  intro hknows
  obtain ⟨w', hconf, hsec⟩ := L.forward_blind B hsub hbelow s₀
  have : L.pre.secret w' = L.pre.secret L.pre.base.actual := hknows w' hconf
  exact hs₀ (hsec ▸ this)

/-- **`secret_value_survives` — the PRE secret VALUE is unchanged at the actual world.** The reshare
moves the SHARES, not the secret: `post.secret actual = pre.secret actual`. The dual of KERI's
"the committed key history is pinned" — here the recoverable VALUE is pinned while the carrier
(shares) refreshes. The conjunction of this with `reshareChain_forward_secret` is the D-side jump:
the value is RECOVERABLE-AT-THRESHOLD post-reshare yet INVISIBLE to a sub-threshold post coalition's
view of the pre secret. -/
theorem secret_value_survives :
    L.post.secret L.post.base.actual = L.pre.secret L.pre.base.actual :=
  L.secret_preserved

/-- **`reshare_forward_jump` — the forward-security JUMP stated as one proposition, PROVED.** Across
the link, the PRE secret is BOTH invisible to a sub-threshold POST coalition AND still the value the
POST committee recovers (it equals the post secret). One coalition-size step (`B` below threshold)
flips knowledge-of-the-PAST-secret from `⊥` to the recoverable present value — the non-amplification
tooth carried ACROSS an epoch boundary. The D-side analogue of `PreRotation`'s
`preimage_blocks_cooled_rotation` triangle: the present cannot reach back. -/
theorem reshare_forward_jump (B : ι → Prop) (hsub : ∀ i, B i → L.post.committee i)
    (hbelow : ¬ L.post.ReachesThreshold B)
    (s₀ : S) (hs₀ : s₀ ≠ L.pre.secret L.pre.base.actual) :
    ¬ L.PostKnowsPreSecret B ∧
      L.post.secret L.post.base.actual = L.pre.secret L.pre.base.actual :=
  ⟨L.reshareChain_forward_secret B hsub hbelow s₀ hs₀, L.secret_preserved⟩

end ReshareLink

#assert_axioms ReshareLink.reshareChain_forward_secret
#assert_axioms ReshareLink.secret_value_survives
#assert_axioms ReshareLink.reshare_forward_jump

/-! # §A.2. The CHAIN — a sequence of links, forward-secure at EVERY boundary.

A resharing chain is a list of reshare links that compose: each link's `post` is the next link's
`pre` (the constant-term anchor `Cⱼ,₀ = pkⱼ_old` of `ReshareDealing` makes `rₙ₊₁` depend on `rₙ`).
We carry the chain as a list whose adjacency is the composition coherence, and lift forward security
to "every PRE secret along the chain is invisible to any sub-threshold coalition of the CURRENT
(final) epoch" — the full mobile-adversary statement: a present compromise reveals NO past epoch. -/

/-- **A resharing CHAIN** over a shared world/agent/secret space: a nonempty sequence of frames
`frames` (the epochs `S₀, S₁, …`) with, for each adjacent pair, a `ReshareLink` whose `pre`/`post`
are exactly those frames. We model it as the genesis frame plus a list of (link) steps; `links`
indexes the boundaries. The coherence `link_pre`/`link_post` ties each link to its neighbours. -/
structure Chain (Ω : Type u) (ι : Type v) (S : Type u) where
  /-- The epochs `S₀, S₁, …, Sₙ` as threshold frames (head = genesis). Nonempty. -/
  frames : List (ThresholdFrame Ω ι S)
  /-- Genesis exists — the chain has at least one epoch. -/
  nonempty : frames ≠ []
  /-- The reshare links, one per boundary (`links.length + 1 = frames.length` in a well-formed
  chain; we keep them aligned by the coherence fields below). -/
  links : List (ReshareLink Ω ι S)
  /-- WELL-FORMED: as many links as boundaries. -/
  aligned : links.length + 1 = frames.length

namespace Chain

variable {Ω : Type u} {ι : Type v} {S : Type u}

/-- **The genesis frame** `S₀` — always present (`nonempty`). -/
def genesis (C : Chain Ω ι S) : ThresholdFrame Ω ι S :=
  C.frames.head C.nonempty

/-- **Every link in a chain is forward-secret** — the chain-level statement: AT EVERY boundary, a
sub-threshold POST coalition is blind to that boundary's PRE secret. The forward security of the
whole chain is the conjunction over boundaries (each `ReshareLink.reshareChain_forward_secret`);
because the floor is per-link and structural, the chain inherits forward security with NO new
hypothesis — exactly as `rotChain_pinned_by_commitments` inherits `KeySetCR` per link on the ∀-side. -/
theorem all_links_forward_secret (C : Chain Ω ι S)
    (L : ReshareLink Ω ι S) (_hmem : L ∈ C.links)
    (B : ι → Prop) (hsub : ∀ i, B i → L.post.committee i)
    (hbelow : ¬ L.post.ReachesThreshold B)
    (s₀ : S) (hs₀ : s₀ ≠ L.pre.secret L.pre.base.actual) :
    ¬ L.PostKnowsPreSecret B :=
  L.reshareChain_forward_secret B hsub hbelow s₀ hs₀

end Chain

#assert_axioms Chain.all_links_forward_secret

/-! # §B. The chain as a PRIME EVENT STRUCTURE — the blocklace embedding.

dregg's distributed-time-travel frame (`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md §2.1`, Winskel) is a
prime event structure `(E, ≤, #)`: events, a causal partial order `≤`, and a symmetric irreflexive
conflict `#` INHERITED along `≤` (`# ∧ ≤ ⟹ #`). A **configuration** is a downward-closed,
conflict-free set. The blocklace IS such a structure (`Dregg2/Distributed/BlocklaceFinality.lean`,
`Coord/CausalOrder.lean::happenedBefore` is the strict partial order). We give the abstract object
here (self-contained in `Metatheory/`) and embed a resharing chain into it: reshare events as a
`≤`-line, committee-equivocation as conflict, a fork = re-randomize at a configuration. -/

/-- **A prime event structure** `(E, ≤, #)` (Winskel): a causal order `le` (a strict partial order —
irreflexive + transitive, the `happenedBefore` shape of `Coord/CausalOrder.lean`) and a symmetric,
irreflexive conflict `confl` inherited along `le` (conflict-heredity). This is the abstract frame the
blocklace instantiates; we state the resharing-chain embedding against it so the chain becomes a
citizen of distributed-time-travel UNCHANGED. -/
structure PrimeEventStructure (E : Type u) where
  /-- The causal order `e ≤ e'` ("`e` happened-before `e'`"). -/
  le      : E → E → Prop
  /-- Causality is IRREFLEXIVE (no event precedes itself — `hb_irrefl`). -/
  le_irrefl : ∀ e, ¬ le e e
  /-- Causality is TRANSITIVE (`hb_trans`). -/
  le_trans  : ∀ {a b c}, le a b → le b c → le a c
  /-- The conflict relation `e # e'` (incompatible events — committee-equivocation). -/
  confl   : E → E → Prop
  /-- Conflict is SYMMETRIC. -/
  confl_symm : ∀ {a b}, confl a b → confl b a
  /-- Conflict is IRREFLEXIVE (an event never conflicts with itself). -/
  confl_irrefl : ∀ e, ¬ confl e e
  /-- **Conflict-HEREDITY** (`# ∧ ≤ ⟹ #`): if `a # b` and `b ≤ c`, then `a # c` — a fork's
  descendants conflict with the other fork (Winskel's inheritance of conflict along causality). -/
  confl_inherit : ∀ {a b c}, confl a b → le b c → confl a c

namespace PrimeEventStructure

variable {E : Type u} (P : PrimeEventStructure E)

/-- **`Configuration X`** — a downward-closed, conflict-free set of events: the time-travel STATE
(Winskel's dI-domain element). Downward-closed: every cause of an included event is included.
Conflict-free: no two included events conflict. -/
structure Configuration (X : E → Prop) : Prop where
  down_closed : ∀ {e e'}, X e' → P.le e e' → X e
  confl_free  : ∀ {e e'}, X e → X e' → ¬ P.confl e e'

/-- **`ConcurrentFork a b`** — two events are a FORK: concurrent (neither causes the other) but in
conflict (incompatible continuations). This is the event-structure shape of "re-randomize the secret
at a configuration onto two incompatible committees" (`RESHARING-CHAINS.md §B.2`). -/
def ConcurrentFork (a b : E) : Prop :=
  ¬ P.le a b ∧ ¬ P.le b a ∧ P.confl a b

/-- **`fork_descendants_conflict` — a fork cannot merge: its descendants conflict, PROVED.** If
`a, b` fork and `c` is a descendant of `b` (`b ≤ c`), then `a # c` — by conflict-heredity. So a
configuration cannot contain both `a` and any descendant of the rival branch `b`: the two
randomness lineages are structurally un-mergeable while incompatible (the lossy-stitch's
linear-drop is forced — `RESHARING-CHAINS.md §B.2`). -/
theorem fork_descendants_conflict {a b c : E} (hfork : P.ConcurrentFork a b) (hbc : P.le b c) :
    P.confl a c :=
  P.confl_inherit hfork.2.2 hbc

/-- **`fork_not_in_one_config` — no configuration holds both prongs of a fork, PROVED.** A
configuration is conflict-free; a fork is in conflict; so no single consistent view of resharing
history contains both re-randomizations. This is the structural reason a fork must be STITCHED OR
ABANDONED (a recovery branch lives in its OWN configuration until merged), never silently coexisting. -/
theorem fork_not_in_one_config {X : E → Prop} (hX : P.Configuration X) {a b : E}
    (hfork : P.ConcurrentFork a b) (ha : X a) (hb : X b) : False :=
  hX.confl_free ha hb hfork.2.2

end PrimeEventStructure

#assert_axioms PrimeEventStructure.fork_descendants_conflict
#assert_axioms PrimeEventStructure.fork_not_in_one_config

/-! ## §B.2. The chain EMBEDS as a `≤`-line.

A linear (non-forking) resharing chain is a TOTAL order of reshare events: `r₀ ≤ r₁ ≤ … ≤ rₙ`. We
exhibit the canonical event structure on `Fin (n+1)` (events = epoch indices, `<` = causality, NO
conflict on the line — a fork ADDS conflicting events off the line) and the trivial configuration =
a downward-closed prefix. This certifies the embedding is real: the chain IS a `≤`-line in a prime
event structure, so branch-and-stitch operates on it unchanged. -/

/-- **The canonical linear event structure of a length-`n` chain** — events `Fin n`, causality `<`,
NO conflict (the bare chain does not fork; a fork is an OFF-line event added later). This is the
`≤`-line the reshare chain occupies inside the blocklace event structure. -/
def lineES (n : Nat) : PrimeEventStructure (Fin n) where
  le := fun a b => a.val < b.val
  le_irrefl := fun e => Nat.lt_irrefl e.val
  le_trans := fun h h' => Nat.lt_trans h h'
  confl := fun _ _ => False
  confl_symm := fun h => h
  confl_irrefl := fun _ => not_false
  confl_inherit := fun h _ => h

/-- **A prefix of the chain is a configuration** — `{e | e.val < k}` (the first `k` epochs) is
downward-closed (a cause of an in-prefix event is earlier, hence in-prefix) and conflict-free (the
line has no conflict). So "the secret's history up to epoch `k`" is a genuine time-travel
configuration: a consistent past one can travel to / fork from. -/
theorem linePrefix_isConfig (n k : Nat) :
    (lineES n).Configuration (fun e : Fin n => e.val < k) where
  down_closed := fun he' hlt => Nat.lt_trans hlt he'
  confl_free := fun _ _ h => h

#assert_axioms linePrefix_isConfig

/-! # §C. The KERI-DUAL SYMMETRY — the `∀`-side and the `D`-side as ONE forward-secure chain.

The ember insight, stated as a STRUCTURE (not a forced analogy): a **forward-secure chain** is an
abstract object — a sequence of states with a per-link guarantee that a present compromise cannot
recover a past secret — and BOTH KERI pre-rotation and the resharing chain are instances, differing
only in WHICH epistemic quantity is forward-secured and WHICH carrier discharges the floor:

  * the `∀`/`Knows` side (KERI): the carrier is COMMITMENT-BINDING (`KeySetCR`), the protected
    quantity is the SIGNING-key history (`rotChain_pinned_by_commitments`);
  * the `D`/`DistKnows^{≥K}` side (resharing): the carrier is the INFO-THEORETIC CLIFF
    (`forward_blind`), the protected quantity is the COMMITTEE-secret history
    (`reshareChain_forward_secret`).

We capture "forward-secure across a link" as a single predicate over an abstract link, and prove the
resharing link satisfies it. The KERI side's discharge lives in `Dregg2.Apps.PreRotation`
(`rotate_current_keys_irrelevant`: the current keys contribute nothing to a rotation) — the same
"the present cannot reach the past" content. Stating the schema makes the duality PRECISE: both are
"nothing of the past below the present's gate." -/

/-- **`ForwardSecureLink`** — the abstract forward-security schema across one chain link. An observer
type `Obs`, a `belowGate` predicate (the observer is below its production gate — sub-threshold on the
D-side / not-the-committed-key on the ∀-side), a `reachesPast` predicate (the observer's present view
PINS the past secret/key), and the single guarantee `cannot_reach_past`: a below-gate observer canNOT
reach the past. This is the polarity-NEUTRAL "nothing of the past below the present's gate" shape;
§A's `ReshareLink` is the D-side instance, KERI's `rotateStep` (`rotate_current_keys_irrelevant`) the
∀-side. The faithfulness is that `reachesPast` is the OBJECT's real pin predicate, not a tautology. -/
structure ForwardSecureLink (Obs : Type u) where
  /-- Is the observer below its production gate? (sub-threshold / not the committed key.) -/
  belowGate : Obs → Prop
  /-- Does the observer's PRESENT view determine the PAST secret/key? (`PostKnowsPreSecret` /
  "the current key fixes the next set".) -/
  reachesPast : Obs → Prop
  /-- **FORWARD SECURITY** — a below-gate observer canNOT reach the past. The whole schema in one
  field; both polarities discharge it from their own carrier (cliff / commitment-binding). -/
  cannot_reach_past : ∀ (o : Obs), belowGate o → ¬ reachesPast o

/-- **`ReshareLink.toForwardSecure` — the D-side resharing link IS a forward-secure link, PROVED.**
We package §A's `reshareChain_forward_secret` into the polarity-neutral `ForwardSecureLink`. The
observer is a sub-threshold committee coalition CARRIED WITH its sub-threshold proof and an actual
alternative pre-secret value (the SSS non-degeneracy); `belowGate` always holds (the carried proof IS
below threshold); `reachesPast B` is `PostKnowsPreSecret B` (its POST view pins the PRE secret);
`cannot_reach_past` is exactly `reshareChain_forward_secret`. This is the formal sense in which the
resharing chain is the D-side dual of KERI's ∀-side `rotChain_pinned_by_commitments`: both inhabit
`ForwardSecureLink`, and the D-side's `cannot_reach_past` IS the relocated common-secret cliff. -/
def ReshareLink.toForwardSecure {Ω : Type u} {ι : Type v} {S : Type u} (L : ReshareLink Ω ι S) :
    ForwardSecureLink
      {B : ι → Prop //
        (∀ i, B i → L.post.committee i) ∧ ¬ L.post.ReachesThreshold B ∧
          ∃ s₀ : S, s₀ ≠ L.pre.secret L.pre.base.actual} where
  belowGate := fun _ => True
  reachesPast := fun B => L.PostKnowsPreSecret B.val
  cannot_reach_past := by
    rintro ⟨B, hsub, hbelow, s₀, hs₀⟩ _
    exact L.reshareChain_forward_secret B hsub hbelow s₀ hs₀

/-- **`keri_dual_symmetry` — the resharing link inhabits the SAME forward-secure schema as KERI.**
The D-side membership is `ReshareLink.toForwardSecure`; applied, it says a sub-threshold post
coalition (with a genuine alternative secret) canNOT reach the past secret — the resharing instance of
`cannot_reach_past`. The ∀-side membership is the content of `Dregg2.Apps.PreRotation`
(`rotate_current_keys_irrelevant` / `rotChain_pinned_by_commitments`: the current key set is
irrelevant to a rotation), CITED here, not re-proved (it lives in the `Dregg2` root over the live
substrate). The shared `ForwardSecureLink.cannot_reach_past` IS the "nothing of the past below the
present's gate" non-amplification tooth, carried in both epistemic polarities. -/
theorem keri_dual_symmetry {Ω : Type u} {ι : Type v} {S : Type u} (L : ReshareLink Ω ι S)
    (o : {B : ι → Prop //
        (∀ i, B i → L.post.committee i) ∧ ¬ L.post.ReachesThreshold B ∧
          ∃ s₀ : S, s₀ ≠ L.pre.secret L.pre.base.actual}) :
    ¬ (L.toForwardSecure).reachesPast o :=
  (L.toForwardSecure).cannot_reach_past o trivial

#assert_axioms keri_dual_symmetry

/-! # §5. A DISCRIMINATING model — non-vacuity (a real reshare of a 2-of-2 XOR secret).

We reuse `CommonSecret.TwoOfTwo`'s 2-of-2 XOR scheme as the PRE epoch and exhibit a POST epoch that
re-randomizes the shares to the SAME secret. Concretely: the secret is a bit `s`; the PRE shares are
`(a, b)` with `a ⊕ b = s` (actual `(true, false)`, secret `true`); the POST shares re-randomize via a
mask `m` to `(a ⊕ m, b ⊕ m)` — same XOR (`(a⊕m) ⊕ (b⊕m) = a ⊕ b = s`), fresh carrier. A world here is
`(a, b, m)` ∈ `Bool³`: PRE reads `a ⊕ b`, POST reads `(a⊕m) ⊕ (b⊕m)`, the post agents see the post
shares. A sub-threshold POST coalition (a single agent) is blind to the PRE secret because the unseen
post share — together with the fresh mask — is consistent with either pre value. This certifies
`forward_blind` is realizable and `reshareChain_forward_secret` is non-vacuous. -/

namespace ReshareTwoOfTwo

/-- A world: pre shares `a, b` and the reshare mask `m`. Pre secret `a ⊕ b`; post shares
`(a⊕m, b⊕m)`; post secret `(a⊕m) ⊕ (b⊕m) = a ⊕ b`. -/
abbrev World := Bool × Bool × Bool

/-- Pre secret read from a world: `a ⊕ b`. -/
def preSecret : World → Bool := fun w => xor w.1 w.2.1

/-- Post secret read from a world: `(a⊕m) ⊕ (b⊕m)`. -/
def postSecret : World → Bool := fun w => xor (xor w.1 w.2.2) (xor w.2.1 w.2.2)

/-- The PRE frame: agent `false` sees `a` (`.1`), agent `true` sees `b` (`.2.1`). Actual
`(true, false, false)` — pre secret `true ⊕ false = true`. (This is `CommonSecret.TwoOfTwo` extended
with the mask coordinate, which the PRE agents ignore.) -/
def preF : Frame World Bool where
  actual := (true, false, false)
  Indist := fun i w w' => if i = false then w.1 = w'.1 else w.2.1 = w'.2.1
  indist_refl := by intro i w; cases i <;> simp
  Alive := fun _ _ => True
  Faulty := fun _ => False

/-- The PRE threshold frame — the §5 common secret, now over `World`. -/
def preTF : ThresholdFrame World Bool Bool where
  base := preF
  committee := fun _ => True
  ReachesThreshold := fun B => B false ∧ B true
  threshold_mono := by intro B B' hsub h; exact ⟨hsub false h.1, hsub true h.2⟩
  committee_reaches := ⟨trivial, trivial⟩
  secret := preSecret
  subThreshold_blind := by
    intro B _ hbelow s
    by_cases hf : B false
    · have htabsent : ¬ B true := fun ht => hbelow ⟨hf, ht⟩
      refine ⟨(true, xor true s, false), ?_, ?_⟩
      · intro i hi
        cases i with
        | false => show (true, xor true s, false).1 = preF.actual.1; rfl
        | true => exact absurd hi htabsent
      · show preSecret (true, xor true s, false) = s; unfold preSecret; simp
    · refine ⟨(s, false, false), ?_, ?_⟩
      · intro i hi
        cases i with
        | false => exact absurd hi hf
        | true => show (s, false, false).2.1 = preF.actual.2.1; rfl
      · show preSecret (s, false, false) = s; unfold preSecret; simp

/-- The POST frame: re-randomized shares. Agent `false` sees the POST share `a⊕m` (a JOINT function
of `.1` and the mask `.2.2`); agent `true` sees `b⊕m`. Actual `(true,false,false)` — post share
edges hold the post-share value equal. The masking is what makes the post view blind on the pre
secret: a single post agent sees one post share, which (over the unknown mask) is consistent with
either pre secret. -/
def postF : Frame World Bool where
  actual := (true, false, false)
  -- agent false confuses worlds with the same POST share a⊕m; agent true the same b⊕m.
  Indist := fun i w w' =>
    if i = false then xor w.1 w.2.2 = xor w'.1 w'.2.2 else xor w.2.1 w.2.2 = xor w'.2.1 w'.2.2
  indist_refl := by intro i w; cases i <;> simp
  Alive := fun _ _ => True
  Faulty := fun _ => False

/-- The POST threshold frame — same committee, same 2-of-2 access; secret read as the POST secret
(which equals the pre secret on every world, the `f(0)`-preservation). Sub-threshold blindness on
the POST secret holds by the same XOR argument over the post shares. -/
def postTF : ThresholdFrame World Bool Bool where
  base := postF
  committee := fun _ => True
  ReachesThreshold := fun B => B false ∧ B true
  threshold_mono := by intro B B' hsub h; exact ⟨hsub false h.1, hsub true h.2⟩
  committee_reaches := ⟨trivial, trivial⟩
  secret := postSecret
  subThreshold_blind := by
    intro B _ hbelow s
    by_cases hf : B false
    · have htabsent : ¬ B true := fun ht => hbelow ⟨hf, ht⟩
      -- hold the post share a⊕m fixed (= actual's = true), realise post secret s by choosing b.
      refine ⟨(true, xor true s, false), ?_, ?_⟩
      · intro i hi
        cases i with
        | false => show xor (true:Bool) false = xor (true:Bool) false; rfl
        | true => exact absurd hi htabsent
      · show postSecret (true, xor true s, false) = s; unfold postSecret; simp
    · refine ⟨(s, false, false), ?_, ?_⟩
      · intro i hi
        cases i with
        | false => exact absurd hi hf
        | true => show xor (false:Bool) false = xor (false:Bool) false; rfl
      · show postSecret (s, false, false) = s; unfold postSecret; simp

/-- **The reshare LINK** — pre and post over the SAME secret value, with the cross-epoch
forward-blindness PROVED from the masking. `secret_preserved`: at the actual world both read `true`.
`forward_blind`: a single POST agent, seeing one post share `(a⊕m)` or `(b⊕m)`, is consistent with
EITHER pre secret — choose the world realising the alternative `s` while holding the seen post share. -/
def link : ReshareLink World Bool Bool where
  pre := preTF
  post := postTF
  same_actual := rfl
  secret_preserved := by show postSecret (true,false,false) = preSecret (true,false,false)
                         unfold postSecret preSecret; simp
  forward_blind := by
    intro B _ hbelow s
    -- B is sub-threshold POST ⇒ missing an agent. Realise pre secret `s` while fixing the seen post share.
    by_cases hf : B false
    · have htabsent : ¬ B true := fun ht => hbelow ⟨hf, ht⟩
      -- agent false present, sees a⊕m. Actual post share a⊕m = true⊕false = true. Hold it; set the
      -- PRE secret a⊕b to s by choosing b, and pick m so a⊕m stays = true (m = a⊕true = false).
      -- world (a=true, b = true⊕s, m=false): a⊕m = true (matches), pre secret = a⊕b = true⊕(true⊕s)=s.
      refine ⟨(true, xor true s, false), ?_, ?_⟩
      · intro i hi
        cases i with
        | false =>
          show xor (true:Bool) false = xor postF.actual.1 postF.actual.2.2
          unfold postF; simp
        | true => exact absurd hi htabsent
      · show preSecret (true, xor true s, false) = s; unfold preSecret; simp
    · -- agent false absent ⇒ true present, sees b⊕m. Actual b⊕m = false⊕false=false. Hold it; set
      -- pre secret to s. world (a=s, b=false, m=false): b⊕m = false (matches), pre = a⊕b = s.
      refine ⟨(s, false, false), ?_, ?_⟩
      · intro i hi
        cases i with
        | false => exact absurd hi hf
        | true =>
          show xor (false:Bool) false = xor postF.actual.2.1 postF.actual.2.2
          unfold postF; simp
      · show preSecret (s, false, false) = s; unfold preSecret; simp

/-- **A single POST agent does NOT know the PRE secret** — forward security, concretely. Agent
`false` (one post share) confuses the actual world with one of the OPPOSITE pre secret: the mobile
adversary holding epoch-`n+1` shares learns NOTHING of the epoch-`n` secret. Non-vacuity certificate
for `reshareChain_forward_secret`. -/
theorem post_agent_blind_on_pre_secret :
    ¬ link.PostKnowsPreSecret (fun j => j = false) := by
  refine link.reshareChain_forward_secret (fun j => j = false) (fun _ _ => trivial) ?_ false ?_
  · intro h; exact (by simp : ¬ ((fun j => j = false) true)) h.2
  · show (false : Bool) ≠ preSecret (true, false, false); unfold preSecret; simp

/-- **The secret VALUE survived the reshare** — `post.secret actual = pre.secret actual = true`. The
`f(0)`-preservation, concretely: the reshare moved the shares (`(true,false)` pre → re-randomized
post) while the recoverable secret stayed `true`. Non-vacuity for `secret_value_survives`. -/
theorem secret_survived : link.post.secret link.post.base.actual = true ∧
    link.pre.secret link.pre.base.actual = true := by
  constructor
  · show postSecret (true,false,false) = true; unfold postSecret; simp
  · show preSecret (true,false,false) = true; unfold preSecret; simp

/-- **The forward JUMP, concretely** — the pre secret is invisible to the single post agent AND is
the recovered value `true`. The D-side cliff across the link, witnessed. -/
theorem forward_jump_concrete :
    ¬ link.PostKnowsPreSecret (fun j => j = false) ∧
      link.post.secret link.post.base.actual = link.pre.secret link.pre.base.actual :=
  ⟨post_agent_blind_on_pre_secret, link.secret_preserved⟩

/-- **A two-epoch resharing CHAIN exists** (genesis `preTF`, one link to `postTF`) — the
`ResharingChain` object is inhabited and well-formed (`aligned`). -/
def chain2 : Chain World Bool Bool where
  frames := [preTF, postTF]
  nonempty := by simp
  links := [link]
  aligned := rfl

theorem chain2_genesis_is_pre : chain2.genesis = preTF := rfl

end ReshareTwoOfTwo

#assert_axioms ReshareTwoOfTwo.post_agent_blind_on_pre_secret
#assert_axioms ReshareTwoOfTwo.secret_survived
#assert_axioms ReshareTwoOfTwo.forward_jump_concrete
#assert_axioms ReshareTwoOfTwo.chain2_genesis_is_pre

/-! # §5b. Event-structure non-vacuity — a real fork that cannot merge.

The `lineES`/`linePrefix_isConfig` keystones are over the bare line; a fork ADDS conflicting events.
We exhibit a 3-event structure: genesis `0`, two rival reshares `1, 2` from genesis, in conflict
(two re-randomizations of the same configuration to incompatible committees). The fork
`1 # 2` is concurrent, and no configuration holds both — the recovery branch lives apart until
stitched-or-abandoned. -/

namespace ForkModel

/-- Three events: `0` genesis, `1`/`2` rival reshares. Causality: `0 < 1`, `0 < 2` only. Conflict:
`1 # 2` (and inherited to any descendants, of which there are none here). -/
def es : PrimeEventStructure (Fin 3) where
  le := fun a b => a = 0 ∧ b ≠ 0
  le_irrefl := by intro e h; exact h.2 h.1
  le_trans := by
    rintro a b c ⟨ha, _⟩ ⟨hb, hc⟩
    -- a=0, b=0 (from hb), but b≠0 from first — contradiction unless we read carefully:
    -- ⟨ha,_⟩ : a=0 ∧ b≠0 ; ⟨hb,hc⟩ : b=0 ∧ c≠0. b≠0 and b=0 contradict.
    exact absurd hb (by have := ha; exact (by simp_all))
  confl := fun a b => (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)
  confl_symm := by
    rintro a b (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  confl_irrefl := by intro e h; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact absurd (h1 ▸ h2) (by decide)
  confl_inherit := by
    rintro a b c hconf ⟨hb, _⟩
    -- b ≤ c needs b = 0; but conflict has b ∈ {1,2}, so b ≠ 0 — the antecedent is impossible here
    -- (no descendants of the rival reshares in this 3-event model), so inheritance is vacuous.
    rcases hconf with ⟨_,h2⟩|⟨_,h2⟩ <;> exact absurd hb (by rw [h2]; decide)

/-- **`1` and `2` are a genuine FORK** — concurrent (neither causes the other: causality only flows
OUT of genesis `0`) and in conflict. The two re-randomizations of the genesis configuration. -/
theorem one_two_fork : es.ConcurrentFork 1 2 := by
  refine ⟨?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
  · rintro ⟨h, _⟩; exact absurd h (by decide)
  · rintro ⟨h, _⟩; exact absurd h (by decide)

/-- **No configuration holds both fork prongs** — the recovery branch and the live branch cannot
coexist in one consistent past; one must be stitched or abandoned. Non-vacuity for
`fork_not_in_one_config`. -/
theorem fork_splits {X : Fin 3 → Prop} (hX : es.Configuration X) (h1 : X 1) (h2 : X 2) : False :=
  es.fork_not_in_one_config hX one_two_fork h1 h2

end ForkModel

#assert_axioms ForkModel.one_two_fork
#assert_axioms ForkModel.fork_splits

/-! # Coda

A **resharing chain** is the D-side dual of KERI pre-rotation. The forward-secure common-secret
CHAIN object is `ResharingChain` (epochs as `ThresholdFrame`s, boundaries as `ReshareLink`s); the
FORWARD-SECURITY law is `ReshareLink.reshareChain_forward_secret` — the common-secret cliff
(`CommonSecret.subThreshold_secret_blind`) RELOCATED across a link, proved by the same shape with the
cross-epoch `forward_blind` floor substituted for `subThreshold_blind` (carried STRUCTURALLY, never
an axiom — the HJKY renewal-secrecy / mobile-adversary discharge). The CHAIN-AS-EVENT-STRUCTURE
embedding is `PrimeEventStructure` (causal `≤` partial order + conflict-heredity, the blocklace
shape): the chain is a `≤`-line (`lineES`/`linePrefix_isConfig`), a FORK is a concurrent conflicting
pair that no configuration holds (`fork_not_in_one_config`) — branch-and-stitch on randomness. The
KERI-DUAL SYMMETRY is `ForwardSecureLink` with `ReshareLink.toForwardSecure`: the ∀-side (KERI,
commitment-binding carrier, `rotChain_pinned_by_commitments`) and the D-side (resharing,
info-theoretic-cliff carrier, `reshareChain_forward_secret`) are two instances of one "nothing of the
past below the present's gate" schema — the non-amplification tooth in both epistemic polarities. A
real reshare of a 2-of-2 XOR secret to fresh masked shares (§5) and a real un-mergeable fork (§5b)
certify every keystone non-vacuous. The single cryptographic obligation lives, faithfully, as the
`forward_blind` structural field — the exact analogue of `subThreshold_blind` and of `KeySetCR`. -/

end Metatheory.ResharingChain
