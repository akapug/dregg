/-
# Dregg2.World — the portal for nondeterministic external inputs (network, clock, randomness).

The sibling of `CryptoKernel`: where `CryptoKernel.lean` is the portal for cryptographic
operations (hash/verify/commit/nullifier), `World` is the portal for the nondeterministic
external inputs consensus needs — the **network** (which messages/votes a round received),
the **clock** (a monotone logical time), and **randomness** (leader election / sortition).
Like crypto, these are supplied from outside and treated as an uninterpreted oracle whose
only Lean-side commitments are its stated laws.

Two realizations of the same interface:
  • **PROVING** — an abstract `[World Msg]` (uninterpreted symbols + their laws). Every
    Lean theorem here is parametric, holding for any lawful environment.
  • **RUNNING** — Rust (the node's runtime) supplies the concrete delivery, system clock,
    and randomness beacon via FFI (`@[extern "dregg_world_recv"] opaque recv …`,
    `dregg_world_clock`, `dregg_world_rand`). The `recv` oracle is the network adversary's
    delivery schedule as an interface; Lean assumes only the laws the runtime guarantees.

This lets us express real finality over the network: a concrete `quorumReached` vote-count
meeting `Finality`'s `½(n+f)` threshold, `Finality.Committed` instantiated as "a quorum of
votes was received over `World.recv`", and clean monotonicity facts. Byzantine / asynchrony
guarantees (safety under equivocation, liveness after GST) are NOT provable from this
interface alone — they need the full τ-BFT protocol — and are honest `OPEN`s.
-/
import Mathlib.Tactic
import Dregg2.Finality
import Dregg2.Execution
import Dregg2.Tactics

namespace Dregg2.World

open Dregg2

/-! ## Messages and votes — the network payloads.

`Msg` is a *parameter* (an interface type, like `CryptoKernel`'s `Digest`/`Proof`): the
network carries opaque messages whose internal structure Lean does not interpret. A `Vote`
is the one payload finality *does* need to interpret — a participant id endorsing a block —
so it is concrete here (the quorum model counts distinct voters). -/

/-- **A vote for a block** — the network payload consensus counts. `voter` is the
participant id (so a quorum is "enough *distinct* voters"); `block` is the (opaque) block
id being endorsed. Concrete because `quorumReached` must inspect it; the generic network
payload `Msg` stays a parameter. -/
structure Vote where
  /-- The endorsing participant's id (distinctness is what a quorum counts). -/
  voter : Nat
  /-- The block id this vote endorses. -/
  block : Nat
  deriving DecidableEq, Repr

/-! ## Partial synchrony — the delivery law, stated about data.

DLS88's partial-synchrony model: there is an (unknown) global stabilization time `gst` and an
(unknown) delay bound `Δ` such that a message sent by round `r` is received by round
`max r gst + Δ`. Before GST the adversary may hold any message; it must release it within `Δ` of
GST. The law relates two logs — what was SENT and what was RECEIVED — so it can fail: a network
that never delivers a sent message refutes it (`not_partialSynchrony_silent`), and one that
delivers everything at once satisfies it (`partialSynchrony_self`). -/

/-- **`PartialSynchrony sent recv`** — ∃ `gst`, `Δ`: every message in the send log by round `r`
is in the receive log by round `max r gst + Δ`. -/
def PartialSynchrony {Msg : Type} (sent recv : Nat → List Msg) : Prop :=
  ∃ gst Δ : Nat, ∀ (r : Nat) (m : Msg), m ∈ sent r → m ∈ recv (max r gst + Δ)

/-- Satisfiable pole: a network that receives each round exactly what was sent by it is
partially synchronous (`gst = Δ = 0`). -/
theorem partialSynchrony_self {Msg : Type} (log : Nat → List Msg) :
    PartialSynchrony log log :=
  ⟨0, 0, fun r m h => by simpa using h⟩

/-- Refutable pole: a network that never delivers a message that was sent at round 0 is not
partially synchronous, whatever `gst` and `Δ` are chosen. The fully-asynchronous adversary. -/
theorem not_partialSynchrony_silent {Msg : Type} (m : Msg) :
    ¬ PartialSynchrony (fun _ => [m]) (fun _ => ([] : List Msg)) := by
  rintro ⟨gst, Δ, h⟩
  exact absurd (h 0 m (by simp)) (by simp)

/-! ## The `World` interface — the network/clock/randomness oracle. -/

/-- **The `World` interface.** The sibling of `CryptoKernel`: `Msg` (the generic network
payload) is uninterpreted; the three operations are opaque; the fields ending in a law are
the obligations the runtime (Rust node + OS clock + randomness beacon) must satisfy
(assumed, never proved, in Lean — exactly as `CryptoKernel`'s `commit_hom`/`hash_inj` are
assumed). These are the nondeterministic external inputs: the Lean semantics is a *function
of* them, it does not generate them.

FFI/uninterpreted-symbols realization (mirrors `CryptoKernel`): for PROVING, an abstract
`[World Msg]`; for RUNNING, `@[extern "dregg_world_clock"] opaque clock`,
`@[extern "dregg_world_recv"] opaque recv`, `@[extern "dregg_world_rand"] opaque rand`
backed by the node runtime. -/
class World (Msg : Type) where
  /-- **The clock oracle** — a monotone-ish logical time. `clock ()` reads the current
  logical time; the runtime (OS / hybrid logical clock) supplies it. We do NOT read a
  global wall-clock into safety (the §2.2 "synchronized wall-clock deadline" globalism seam
  is rejected); this is a logical timestamp used for round bookkeeping only. Realized at
  runtime via `@[extern "dregg_world_clock"]`. -/
  clock : Unit → Nat
  /-- **The network oracle** — the messages/votes delivered *by* a given round. `recv r` is
  the multiset (as a `List`) of messages the local node has received up to round `r`. This
  IS the network adversary's delivery schedule made into an interface; Lean assumes only
  the law below about it. Realized at runtime via `@[extern "dregg_world_recv"]`. -/
  recv : Nat → List Msg
  /-- **The randomness oracle** — leader election / sortition (`rand r` = the beacon value
  for round `r`). Used to pick a τ-BFT wave leader; opaque, supplied by the runtime beacon.
  Realized at runtime via `@[extern "dregg_world_rand"]`. -/
  rand : Nat → Nat
  /-- **LAW — network monotonicity (no un-delivery).** What a round has received is never
  retracted: a later round has received (at least) everything an earlier round did. This is
  the only network guarantee Lean relies on — the message log grows; the adversary may
  delay and reorder but cannot make a delivered message *un*-happen. The runtime discharges
  it (an append-only receive log). (The GST/Δ delivery bound is the separate
  law `gst_delivery` below.) -/
  recv_mono : ∀ {r r' : Nat}, r ≤ r' → List.Sublist (recv r) (recv r')
  /-- **The send log (specification-side).** `sent r` is every message broadcast, by any
  participant, by round `r`. It is not a runtime oracle — the local node cannot observe other
  participants' sends — but the object the delivery law below is ABOUT: partial synchrony is a
  relation between what was sent and what was received. -/
  sent : Nat → List Msg
  /-- **LAW — partial-synchrony delivery (DLS88 GST/Δ).** There are a GST and a delay bound Δ
  such that every message sent by round `r` is received by round `max r gst + Δ`. This is the
  assumption a partially-synchronous runtime must meet, and it can fail: a network that holds a
  sent message forever refutes it (`not_partialSynchrony_silent`). Liveness is DERIVED from it
  plus an honest-sending premise (`liveness_after_gst`), not restated as a field.

  An earlier revision carried `gst_liveness : (∀ k, ∃ r, k ≤ count r) → ∃ r, threshold ≤ count r`
  here — provable by instantiating `k := threshold`, so it assumed nothing and described a law it
  did not state. -/
  gst_delivery : PartialSynchrony sent recv

variable {Msg : Type}

/-! ## The concrete quorum model — real finality over the network.

`Finality.lean` keeps `Committed`/quorum abstract and lifts the `½(n+f)` threshold into
`Config`. Here we give the *concrete* vote-counting predicate over a `World`-delivered vote
list and connect it to the abstract `Finality.Committed`. -/

/-- **The set of distinct voters that endorsed `block` in `votes`** (deduplicated by
`voter`, restricted to this block). A quorum counts *distinct* participants, so we
deduplicate: two votes from the same voter for the same block count once. -/
def votersFor (votes : List Vote) (block : Nat) : List Nat :=
  ((votes.filter (fun v => v.block = block)).map (·.voter)).dedup

/-- **`quorumReached votes cfg block`** — a vote count meets the lifted `½(n+f)` threshold.
The number of *distinct* voters that endorsed `block` is at least `cfg.threshold` (the
config's commit threshold, canonically `Config.halfQuorum n f = ⌊(n+f)/2⌋+1`). This is the
concrete realization of the quorum `Finality.Committed` leaves abstract; the `½(n+f)`
constant is read from `cfg`, never hardcoded (§2.2). -/
def quorumReached (votes : List Vote) (cfg : Finality.Config) (block : Nat) : Bool :=
  cfg.threshold ≤ (votersFor votes block).length

/-! ## Connecting the abstract `Finality.Committed` to the network quorum. -/

/-- **The block-id history substrate.** For the network-driven finality model a "history"
is just a block id (`Nat`) — the thing votes endorse and the thing `Committed` ranges over.
(`Finality.History` is `Type u`; we instantiate it at `Nat`.) -/
abbrev BlockId := Nat

/-- **`committedByQuorum` — the abstract `Finality.Committed` instantiated as "a quorum of
votes was received over `World.recv`".** Given a `World`, a round `r`, a way to read the
votes out of the received messages (`votesOf`), and a config, a block is *committed* exactly
when `quorumReached` holds over the votes the network delivered by round `r`. This is the
portal connection: `Finality`'s opaque `Committed` predicate is realized by a concrete count
over the `World` network oracle's output. -/
def committedByQuorum [World Msg] (votesOf : List Msg → List Vote)
    (r : Nat) (cfg : Finality.Config) : Finality.Committed BlockId :=
  fun block => quorumReached (votesOf (World.recv r)) cfg block = true

/-! ## PROVED facts about the quorum model. -/

/-- **Dedup never lengthens a list** (helper) — the deduplicated voter list is no longer
than the raw one. Used to bound a quorum from the underlying votes. -/
theorem votersFor_length_le (votes : List Vote) (block : Nat) :
    (votersFor votes block).length ≤
      ((votes.filter (fun v => v.block = block)).map (·.voter)).length := by
  simpa [votersFor] using
    List.Sublist.length_le (List.dedup_sublist
      ((votes.filter (fun v => v.block = block)).map (·.voter)))

/-- **A sublist of votes has a sublist of voters-for-a-block** (helper). If `votes₁` is a
sublist of `votes₂` (the network only ever *added* votes), then the distinct voters for any
block under `votes₁` are a subset of those under `votes₂`, hence no more numerous. The key
monotonicity step under the network's append-only delivery. -/
theorem votersFor_length_mono {votes₁ votes₂ : List Vote}
    (h : List.Sublist votes₁ votes₂)
    (block : Nat) :
    (votersFor votes₁ block).length ≤ (votersFor votes₂ block).length := by
  -- filtering preserves the sublist, mapping preserves it, and dedup is monotone in length
  -- under the subset induced by a sublist.
  have hfilt : List.Sublist (votes₁.filter (fun v => v.block = block))
      (votes₂.filter (fun v => v.block = block)) := h.filter _
  have hmap : List.Sublist ((votes₁.filter (fun v => v.block = block)).map (·.voter))
      ((votes₂.filter (fun v => v.block = block)).map (·.voter)) := hfilt.map _
  -- a sublist's dedup is contained in the larger list's dedup ⇒ length ≤.
  have hsub : ((votes₁.filter (fun v => v.block = block)).map (·.voter)).dedup
      ⊆ ((votes₂.filter (fun v => v.block = block)).map (·.voter)).dedup := by
    intro a ha
    rw [List.mem_dedup] at ha ⊢
    exact hmap.subset ha
  have hnd : ((votes₁.filter (fun v => v.block = block)).map (·.voter)).dedup.Nodup :=
    List.nodup_dedup _
  -- a nodup list that is a subset of another is a subperm of it, hence no longer.
  simpa [votersFor] using (List.subperm_of_subset hnd hsub).length_le

/-- **`quorum_monotone` — more votes preserve quorum-reached.** If a quorum was
reached over a vote list `votes₁`, then it is still reached over any larger list `votes₂`
(`votes₁ <+ votes₂`). Distinct-voter count is monotone under adding votes, and the threshold
is fixed; this is *safety of the count* under the network's append-only delivery — once a
quorum exists, delivering more messages cannot destroy it. -/
theorem quorum_monotone {votes₁ votes₂ : List Vote}
    (h : List.Sublist votes₁ votes₂)
    (cfg : Finality.Config) (block : Nat)
    (hq : quorumReached votes₁ cfg block = true) :
    quorumReached votes₂ cfg block = true := by
  simp only [quorumReached, decide_eq_true_eq] at hq ⊢
  exact le_trans hq (votersFor_length_mono h block)

/-- **Quorum is monotone *along network delivery*.** Combining `World.recv_mono`
with `quorum_monotone`: if a quorum for `block` was reached over the votes delivered by
round `r`, it is still reached over the votes delivered by any later round `r' ≥ r`, *for
any voter-extraction `votesOf` that respects sublists* (delivering more messages yields a
superlist of votes). So `committedByQuorum` is monotone in the round — a committed block
*stays* committed as the network log grows. This is the network-level statement that quorum
commits do not un-happen. -/
theorem committedByQuorum_mono [World Msg]
    (votesOf : List Msg → List Vote)
    (hvotesOf : ∀ {m₁ m₂ : List Msg}, List.Sublist m₁ m₂ →
      List.Sublist (votesOf m₁) (votesOf m₂))
    {r r' : Nat} (hrr : r ≤ r') (cfg : Finality.Config) (block : BlockId)
    (hc : committedByQuorum votesOf r cfg block) :
    committedByQuorum votesOf r' cfg block := by
  unfold committedByQuorum at hc ⊢
  exact quorum_monotone (hvotesOf (World.recv_mono hrr)) cfg block hc

/-! ## A `FinalityRule` built from the network quorum, and no-downgrade over it.

The quorum predicate supplies a *concrete* `Finality.FinalityRule` whose `committed` is
`committedByQuorum`. Its commit-soundness (`committed ⇒ canonical`) is, per §2.2, an
obligation each rule satisfies by construction; for the network model we take canonicity to
be *exactly* having-a-quorum, which makes the obligation hold definitionally. We then relay
`Finality.no_downgrade`'s tier-monotonicity shape over a `World`-driven finality run. -/

/-- **The network-quorum finality rule (a lawful `FinalityRule`).** A
tier-`tier` rule whose `committed` predicate is `committedByQuorum` over round `r`, and
whose `canonical` selector is the *same* predicate — so commit-soundness
(`committed h → canonical h`) holds by `id`. This is the §2.2 "tier-2 ack-threshold / tier-3
BFT quorum" rule made concrete over the `World` network oracle; the abstract
`Finality.Committed` of the rule is now the real vote count. -/
def quorumRule [World Msg] (tier : Finality.Tier) (votesOf : List Msg → List Vote)
    (r : Nat) (cfg : Finality.Config) : Finality.FinalityRule BlockId where
  tier := tier
  config := cfg
  committed := committedByQuorum votesOf r cfg
  canonical := committedByQuorum votesOf r cfg
  commit_canonical := fun _ h => h

/-- The network-quorum rule's `committed` is exactly `committedByQuorum` (definitional
unfolding — confirms the abstract predicate is wired to the concrete vote count). -/
@[simp] theorem quorumRule_committed [World Msg] (tier : Finality.Tier)
    (votesOf : List Msg → List Vote) (r : Nat) (cfg : Finality.Config) (block : BlockId) :
    (quorumRule tier votesOf r cfg).committed block
      = (quorumReached (votesOf (World.recv r)) cfg block = true) :=
  rfl

/-- **No-downgrade relayed over a `World`-driven finality run.** The
finality-strength transition system `Finality.finalitySystem` (configurations = `Tier`,
steps may only keep-or-strengthen the tier) is driven, in the real system, by network
events delivered through `World.recv`; this theorem instantiates `Finality.no_downgrade`'s
shape over such a run. Along ANY sequence of (re-)finalization events on one value — i.e.
any `Execution.Run finalitySystem t₀ t` whose steps are triggered by the `World` oracle —
the final tier `t` is no weaker than the initial tier `t₀`. The network can deliver more
votes, advance the clock, and re-run leader election, but it can never *downgrade* a
value's finality. Proved by relaying `Finality.no_downgrade` (which lifts the per-step
"a step never lowers the tier" through `Execution.invariant_run`). -/
theorem world_no_downgrade [World Msg] {t₀ t : Finality.Tier}
    (hrun : Execution.Run Finality.finalitySystem t₀ t) :
    t₀ ≤ t :=
  Finality.no_downgrade hrun

/-! ## Quorum intersection (via pigeonhole) and the GST liveness obligation.

The intersection *core* of BFT safety — that two quorums for distinct blocks must share a
voter — is pure counting from the `½(n+f)` threshold and a participant-membership bound, so
it is proved here with no external paper. The *full* honest-vote-once safety (a shared voter
is a CONTRADICTION because an honest node never double-votes) needs the adversary/honesty
model and Malkhi–Reiter; that part stays an explicit scope-note, not a discharged claim. Liveness after
GST is derived from the NAMED assumed `World` law `gst_delivery` (DLS88 partial synchrony: sent
messages arrive within Δ of `max(send, GST)`) plus an honest-sending premise — the same pattern
as `recv_mono`, not an axiom. -/

/-- **Quorum intersection (pigeonhole).** If `cfg.threshold` is the lifted
`halfQuorum = ⌊(n+f)/2⌋+1` and two quorums for blocks `b₁`, `b₂` have both formed over a
common vote list, and the union of their distinct voters is bounded by the participant
population `n + f` (the membership bound the protocol layer supplies — the network oracle
itself says nothing about *who* may vote), then the two quorums **share a voter**. This is
the seed of the BFT safety contradiction, established by pure counting:

  `|Q₁| + |Q₂| ≥ 2·(⌊(n+f)/2⌋+1) > n+f ≥ |Q₁ ∪ Q₂|`,

so by inclusion–exclusion `|Q₁ ∩ Q₂| = |Q₁| + |Q₂| − |Q₁ ∪ Q₂| ≥ 1`. No adversary model and
no external paper are needed for THIS step. (`hconflict`/`hbft` are recorded as the intended
protocol context — `n > 3f` is what makes the membership bound `≤ n+f` survive `f` Byzantine
voters — but the intersection itself follows from the threshold + union bound alone.)

**Honestly scoped-out (NOT proved here):** that a shared voter is a *contradiction* for
conflicting blocks. That is the full honest-vote-once argument (an honest node casts at most
one vote per height); it requires the adversary/honesty model and the per-node voting
discipline (Malkhi–Reiter style), which live with the τ-BFT protocol, not the bare network
oracle. This theorem closes the intersection core; the contradiction step is the protocol's. -/
theorem quorum_intersection_safety
    (cfg : Finality.Config) (votes : List Vote) (b₁ b₂ : Nat)
    (hconflict : b₁ ≠ b₂)
    (hquorum_is_half : cfg.threshold = Finality.Config.halfQuorum cfg.n cfg.f)
    (hbft : cfg.n > 3 * cfg.f)
    -- the participant-membership bound the protocol layer supplies: every distinct voter is
    -- one of the `n + f` participants, so the *union* of the two quorums' voters is no larger
    -- than the population. (`n > 3f` keeps this honest under `f` Byzantine voters.)
    (hbound : ((votersFor votes b₁).toFinset ∪ (votersFor votes b₂).toFinset).card
      ≤ cfg.n + cfg.f)
    (hq1 : quorumReached votes cfg b₁ = true) (hq2 : quorumReached votes cfg b₂ = true) :
    -- two quorums for distinct blocks must share a voter — quorum intersection.
    ∃ voter, voter ∈ votersFor votes b₁ ∧ voter ∈ votersFor votes b₂ := by
  -- the two voter lists are dedup'd, hence `Nodup`, so their `toFinset.card = length`.
  set Q1 := votersFor votes b₁ with hQ1
  set Q2 := votersFor votes b₂ with hQ2
  have hnd1 : Q1.Nodup := by rw [hQ1, votersFor]; exact List.nodup_dedup _
  have hnd2 : Q2.Nodup := by rw [hQ2, votersFor]; exact List.nodup_dedup _
  have hc1 : Q1.toFinset.card = Q1.length := List.toFinset_card_of_nodup hnd1
  have hc2 : Q2.toFinset.card = Q2.length := List.toFinset_card_of_nodup hnd2
  -- each quorum meets the threshold = halfQuorum.
  have hlen1 : Finality.Config.halfQuorum cfg.n cfg.f ≤ Q1.length := by
    simpa [quorumReached, hquorum_is_half] using hq1
  have hlen2 : Finality.Config.halfQuorum cfg.n cfg.f ≤ Q2.length := by
    simpa [quorumReached, hquorum_is_half] using hq2
  -- inclusion–exclusion: |Q1∪Q2| + |Q1∩Q2| = |Q1| + |Q2|.
  have hie : (Q1.toFinset ∪ Q2.toFinset).card + (Q1.toFinset ∩ Q2.toFinset).card
      = Q1.toFinset.card + Q2.toFinset.card := Finset.card_union_add_card_inter _ _
  -- pigeonhole: 2·(⌊(n+f)/2⌋+1) > n+f ≥ |Q1∪Q2| forces a nonempty intersection.
  have hinter_pos : 0 < (Q1.toFinset ∩ Q2.toFinset).card := by
    simp only [Finality.Config.halfQuorum] at hlen1 hlen2
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hinter_pos
  rw [Finset.mem_inter, List.mem_toFinset, List.mem_toFinset] at hv
  exact ⟨v, hv.1, hv.2⟩

/-- **Distinct-voter count is monotone under message-set inclusion** (helper). If every vote
of `votes₁` is a vote of `votes₂`, the distinct voters for `block` in `votes₁` are no more
numerous than in `votes₂`. Membership, not sublist: delivery may reorder. -/
theorem votersFor_length_le_of_subset {votes₁ votes₂ : List Vote}
    (h : ∀ v ∈ votes₁, v ∈ votes₂) (block : Nat) :
    (votersFor votes₁ block).length ≤ (votersFor votes₂ block).length := by
  have hsub : votersFor votes₁ block ⊆ votersFor votes₂ block := by
    intro a ha
    simp only [votersFor, List.mem_dedup, List.mem_map, List.mem_filter] at ha ⊢
    obtain ⟨v, ⟨hv, hb⟩, rfl⟩ := ha
    exact ⟨v, ⟨h v hv, hb⟩, rfl⟩
  exact (List.subperm_of_subset (List.nodup_dedup _) hsub).length_le

/-- **The delivery step, over raw logs.** If the logs are partially synchronous, `votesOf` reads
votes pointwise (a superset of messages yields a superset of votes), and by some round `r` at
least `cfg.threshold` distinct voters have SENT a vote for `block`, then some round RECEIVES that
many distinct voters for `block`: round `max r gst + Δ`. -/
theorem quorum_received_of_partialSynchrony (sent recv : Nat → List Msg)
    (hps : PartialSynchrony sent recv)
    (votesOf : List Msg → List Vote)
    (hvotesOf : ∀ {m₁ m₂ : List Msg}, (∀ x ∈ m₁, x ∈ m₂) → ∀ v ∈ votesOf m₁, v ∈ votesOf m₂)
    (cfg : Finality.Config) (block : BlockId)
    (hsent : ∃ r, cfg.threshold ≤ (votersFor (votesOf (sent r)) block).length) :
    ∃ r, cfg.threshold ≤ (votersFor (votesOf (recv r)) block).length := by
  obtain ⟨gst, Δ, hdel⟩ := hps
  obtain ⟨r, hr⟩ := hsent
  exact ⟨max r gst + Δ, le_trans hr
    (votersFor_length_le_of_subset (hvotesOf (fun m hm => hdel r m hm)) block)⟩

/-- **Liveness after GST (derived from the `gst_delivery` law).** If, by some round, at least
`cfg.threshold` distinct voters have broadcast a vote for `block` (the honest-supermajority
sending premise `hsent`), then under the partial-synchrony delivery law `World.gst_delivery` the
network reaches a round where `committedByQuorum` holds. UNCONDITIONAL liveness is FALSE for a
fully-asynchronous network (FLP): `silent_*` in `Reference` exhibits logs satisfying `hsent` and
`recv_mono` on which no round ever reaches the quorum, and on which `PartialSynchrony` fails — the
delivery law is what carries the conclusion. `hvotesOf` says votes are read pointwise from
messages (satisfied by any `filterMap`-style decoder). -/
theorem liveness_after_gst [World Msg]
    (votesOf : List Msg → List Vote)
    (hvotesOf : ∀ {m₁ m₂ : List Msg}, (∀ x ∈ m₁, x ∈ m₂) → ∀ v ∈ votesOf m₁, v ∈ votesOf m₂)
    (cfg : Finality.Config) (block : BlockId)
    (hsent : ∃ r, cfg.threshold ≤ (votersFor (votesOf (World.sent r)) block).length) :
    ∃ (r : Nat), committedByQuorum votesOf r cfg block := by
  obtain ⟨r, hq⟩ := quorum_received_of_partialSynchrony World.sent World.recv
    (World.gst_delivery (Msg := Msg)) votesOf hvotesOf cfg block hsent
  refine ⟨r, ?_⟩
  show committedByQuorum votesOf r cfg block
  unfold committedByQuorum
  simp only [quorumReached, decide_eq_true_eq]
  exact hq

/-! ## A reference (test) `World` — the Lean-as-host realization.

Mirrors `CryptoKernel.Reference`: a trivial lawful instance (over `Msg = Vote`) — enough to
`#eval`/test the network-driven finality WITHOUT a running node. The real instance is the
Rust FFI one. This witnesses that the interface is inhabitable (the `recv_mono` law is
satisfiable), so the parametric theorems above are not vacuous. -/
namespace Reference

/-- Reference message = a `Vote` (the test network carries only votes). -/
abbrev M := Vote

/-- A reference receive log: a fixed nondecreasing-by-construction schedule — round `r`
delivers the first `r` votes of a fixed list. `List.take` of a monotone index gives the
`recv_mono` sublist for free. -/
def fixedVotes : List Vote :=
  [⟨0, 7⟩, ⟨1, 7⟩, ⟨2, 7⟩, ⟨0, 7⟩]  -- note: voter 0 appears twice; dedup counts it once

instance : World M where
  clock := fun _ => 0
  recv := fun r => fixedVotes.take r
  rand := fun r => r
  recv_mono := by
    intro r r' h
    -- `take r = take r (take r')` when `r ≤ r'` (via `take_take`/`min`), and
    -- `take r (take r') <+ take r'`; compose.
    have hmin : min r r' = r := Nat.min_eq_left h
    have : fixedVotes.take r = (fixedVotes.take r').take r := by
      rw [List.take_take, hmin]
    rw [this]
    exact List.take_sublist r (fixedVotes.take r')
  sent := fun r => fixedVotes.take r
  gst_delivery := partialSynchrony_self _

/-- The reference world is lawful and the parametric defs compute: by round 3 the fixed
schedule has delivered 3 distinct voters (0,1,2) for block 7, meeting a threshold of 3. -/
example :
    quorumReached ((World.recv (Msg := M) 3)) ⟨3, 0, 3⟩ 7 = true := by
  decide

/-- The reference quorum config: `n = 3`, `f = 0`, threshold `3`. -/
def cfg3 : Finality.Config := ⟨3, 0, 3⟩

/-- **Satisfying pole — liveness follows.** On the reference world (partially synchronous by
`partialSynchrony_self`), three distinct voters have sent a vote for block `7` by round `3`, and
`liveness_after_gst` concludes a committed round. Derived through the theorem, not by evaluation
of the conclusion. -/
theorem reference_liveness :
    ∃ r, committedByQuorum (Msg := M) id r cfg3 7 :=
  liveness_after_gst (Msg := M) id (fun h v hv => h v hv) cfg3 7 ⟨3, by decide⟩

/-- The adversarial send log: every vote of `fixedVotes` is broadcast at round 0. -/
def silentSent : Nat → List M := fun _ => fixedVotes

/-- The adversarial receive log: nothing is ever delivered. -/
def silentRecv : Nat → List M := fun _ => []

/-- The adversarial logs meet the honest-sending premise: three distinct voters sent for `7`. -/
theorem silent_sends_quorum :
    ∃ r, cfg3.threshold ≤ (votersFor (id (silentSent r)) 7).length :=
  ⟨0, by decide⟩

/-- The adversarial receive log satisfies the other network law, `recv_mono`. -/
theorem silent_recv_mono {r r' : Nat} (_ : r ≤ r') :
    List.Sublist (silentRecv r) (silentRecv r') :=
  List.Sublist.slnil

/-- **Refuting pole — the law fails.** The adversarial logs are not partially synchronous. -/
theorem silent_not_partialSynchrony : ¬ PartialSynchrony silentSent silentRecv := by
  rintro ⟨gst, Δ, h⟩
  exact absurd (h 0 ⟨0, 7⟩ (by decide)) (by simp [silentRecv])

/-- **Refuting pole — liveness fails.** On the adversarial logs no round ever receives a
quorum, although the sending premise holds: without `gst_delivery`, liveness is not derivable. -/
theorem silent_no_liveness :
    ¬ ∃ r, cfg3.threshold ≤ (votersFor (id (silentRecv r)) 7).length := by
  rintro ⟨r, h⟩
  simp [silentRecv, votersFor, cfg3] at h

end Reference

/-! ## Axiom hygiene.

`quorum_intersection_safety` is a real pigeonhole proof; `liveness_after_gst` is derived from
`World.gst_delivery` (a class field / hypothesis, not an `axiom`) plus the sending premise. Neither pulls in
a faked-green axiom — `collectAxioms` sees only the three standard kernel axioms. -/
#assert_axioms quorum_intersection_safety
#assert_axioms liveness_after_gst
#assert_axioms partialSynchrony_self
#assert_axioms not_partialSynchrony_silent
#assert_axioms votersFor_length_le_of_subset
#assert_axioms quorum_received_of_partialSynchrony
#assert_axioms Reference.reference_liveness
#assert_axioms Reference.silent_sends_quorum
#assert_axioms Reference.silent_not_partialSynchrony
#assert_axioms Reference.silent_no_liveness

end Dregg2.World
