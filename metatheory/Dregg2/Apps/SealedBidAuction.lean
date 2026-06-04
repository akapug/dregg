/-
# Dregg2.Apps.SealedBidAuction — the gallery SEALED-BID AUCTION (Track-A Phase 4, the proving-ground app).

The first END-TO-END app on the intent-as-co-receipt stack (`docs/rebuild/INTENT-AS-CO-RECEIPT.md` §5/§7,
HANDOFF Track A). It is **composition, not new theory**: every keystone INSTANTIATES a proved abstract
lemma from the green Phase-1/2/3 modules. The auction proves, on the same-bundle settle (the
decision-free core — see the OPEN block below for the model-shape calls deferred to ember):

  * **(b) causal reveal-ordering EXCLUDES frontrunning** — a *lightcone fact*, not a gas race: a fill that
    does not causally follow the bid's reveal event fails the bid's validity window. The teeth: a bid
    revealed on the Byzantine fork `f1` is genuinely UNFILLABLE by a concurrent fill on `f2`
    (`no_frontrunning_teeth`), backed by `Time.Causal.demo_frontrun_caught` (`f1 ∦ f2`).
  * **(c) CONSERVATION across the settle** — no value minted: the settle receipt carries a conversion
    `offered ⟶ outcome`, hence `Converts offered outcome` (the thin Coecke–Fritz convertibility shadow,
    `fulfill_conserves`). The teeth: a cross-asset settle that WOULD mint (5 gold ⟶ 1 art with no market
    offer) is rejected — `no Converts`, so no fill, so nothing minted (`settle_cannot_mint`, via
    `res_no_convert`).
  * **one-shot (no double-settle)** — the settled escrow is released and can never fund a second settle
    (`settle_no_double`, the abstract `no_double_fulfill` instantiated).
  * **loser-refund LIVENESS** — the genuine `◇`: from a `JustProgress` package over a refund potential,
    `just_progress` yields `Eventually Refunded`. Carried as the abstract template
    (`loser_refunded_eventually`) AND de-vacuified by a concrete inhabited witness on the REAL executor
    (`auction_loser_refunded`, reusing `Fairness.refundDemo`'s B-just `transferSched` path). The teeth that
    keep this non-vacuous: `Fairness.badSched_not_just` (a starving schedule is genuinely REJECTED).

## The §8 carriers — kept honest (explicit, never faked)

The sealed-bid commitment is the COMMIT phase: a bidder publishes `commit value blinding` BEFORE the
reveal frontier, then the reveal "opens" it. The validity face is `causalAfter revealEvt` (the reveal
event), so anti-frontrunning needs **no clock, no authority, no δ** — `causalAfter_no_frame_dependency`.
The commitment binding/hiding (Pedersen) enters ONLY as the §8 carrier `CryptoKernel.commit` (NOT faked
here — the auction is parametric in the digest type; the headline (b) is a pure ORDER fact that does not
touch the commitment seam). A wall-clock auction-CLOSE (a separate `frameWithin` deadline) would carry its
own `δ` and the `commit_wait_bridge`; the headline does not use it.

## The (a) obligation — userspace-escrow ≥ kernel-escrow — is a CARRIED OPEN, not a stub

The §5/§7 inequality `kernelEscrow ⊑ userspaceEscrow` needs the userspace-escrow CELL-PROGRAM (`INTENT-AS-
CO-RECEIPT.md` §2 face 3) that does not yet exist in the green tree, and a state CLOCK dimension the
executor lacks (`EFFECT-FIDELITY-LEDGER.md`). Per MEMORY "Improve Don't Degrade" / "Don't Cheap Out": it
is NOT stubbed and NOT `sorry`'d — it is stated as a carried-hypothesis interface obligation
(`UserspaceDominatesKernel` + `escrow_refinement_sound`) whose precise model-shape is OPEN-flagged for
ember (see §5). Everything else ships green around it.

Built per the architect's PHASE-4 BUILD SPEC. Pure; no `axiom`/`sorry`/`admit`/`native_decide`. Every
keystone is `#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Intent.Kernel
import Dregg2.Proof.Fairness

namespace Dregg2.Apps.SealedBidAuction

open CategoryTheory
open Dregg2.Intent
open Dregg2.Time.Deadline (Deadline)
open Dregg2.Time.Causal (Frontier CausalAfter frontrunExcluded)
open Dregg2.Authority.Blocklace (demoLace g0 g1 f1 f2)

/-! ## 1. The per-bidder sealed-bid `KernelIntent` (the four faces, on the kernel resources).

A bid is a four-faced `Intent` over `DreggResources` (asset bundles) and the demo time-world
(`demoLace`, the empty registry `demoReg`, the constant encoder `demoStmtOf` — `Intent/Core.lean`). The
empty registry is LOAD-BEARING and correct: the causal reveal-ordering needs NO authority
(`causalAfter_no_frame_dependency`); only a frame-typed wall-clock close would need one.

DECISION-FREE DEFAULTS (the architect's Q1a / Q2-thin / Q5i — same-bundle settle, thin `Converts`
conservation, per-bid acceptance predicate):
  * `offered = wanted = alloc` — the WINNER's escrow is already in the settled allocation, so the fill is
    the identity conversion (`settleIntent` shape, `Intent/Kernel.lean`). The genuine cross-asset
    exchange (pay gold, get art) needs the market's offer-generated conversions — deferred (`crossBid`,
    the §3 teeth). -/

/-- A bidder is a cell on the lace, identified by its block's `creator` worldline (`Blocklace.Block`'s
`creator : Nat`). (Architect Q3 default: a worldline, not a bare `CellId`. The N-bidder protocol with a
purpose-built lace is the deferred build; here a bidder rides the demo lace's authors.) -/
abbrev Bidder := Nat

/-- **A per-bidder sealed-bid intent** over the kernel resources, with a CAUSAL validity window
`causalAfter revealEvt` — a lightcone fact: the fill MAY NOT happen before the reveal event `revealEvt`,
so reveal-ordering excludes frontrunning *structurally* (§3). `alloc` is the bidder's settled allocation
(same-bundle: offered = wanted = alloc); `accept` is the per-bid acceptance predicate (Q5i: "this is my
allocation"). The escrow is funded over `alloc`. -/
def bidIntent (_bidder : Bidder) (alloc : DreggResources) (revealEvt : Frontier) :
    KernelIntent demoLace demoReg demoStmtOf where
  offered   := alloc
  wanted    := alloc
  predicate := fun r => r = alloc
  resource  := EscrowWitness.fund alloc
  validity  := Deadline.causalAfter revealEvt

/-- A concrete winning bid: bidder `7` (the honest author), allocation "3 art" (`res 0 3`), reveal at the
genesis event `g0`. -/
def winningBid : KernelIntent demoLace demoReg demoStmtOf := bidIntent 7 (res 0 3) g0

/-- The winning bid's validity is a CAUSAL deadline (the §4 court read-off: a lightcone fact, no trust). -/
theorem winningBid_is_causal : winningBid.validity.kind = true := rfl

/-! ## 2. The SETTLE — the winning bid filled by the allocating conversion.

In the discrete `DemoRes` the same-bundle settle (offered = wanted = alloc) is filled by the IDENTITY
conversion (allocation = allocation) — exactly `fulfill` at `𝟙 alloc` (`Intent/Core.lean`). This is the
decision-free core; the cross-asset settle (§3) is the market-generated case deferred to ember (Q1). -/

/-- **`auctionSettle`** — settle a (same-bundle) bid `i` by a conversion `f : i.offered ⟶ i.wanted`, given
the acceptance predicate holds at `wanted` and the escrow is LOCKED (funded). Produces the discharging
receipt with the escrow RELEASED — the receipt⊣intent counit (`fulfill`). -/
def auctionSettle (i : KernelIntent demoLace demoReg demoStmtOf)
    (f : i.offered ⟶ i.wanted) (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true) :
    FillReceipt i :=
  fulfill i f hpred hlock

/-- The concrete settle of `winningBid`: the identity conversion `res 0 3 ⟶ res 0 3`, the predicate
accepts (`rfl`), the escrow is locked (`rfl`). The receipt attests "3 art" allocated to the winner. -/
def winningReceipt : FillReceipt winningBid :=
  auctionSettle winningBid (𝟙 (res 0 3)) rfl rfl

/-- The settle discharges to exactly the demanded allocation, the predicate holds there, and the escrow is
consumed — the discharge keystone (`fulfill_discharges`) at the auction settle. -/
theorem winning_discharges :
    winningReceipt.outcome = res 0 3 ∧
      winningBid.predicate winningReceipt.outcome ∧
      winningReceipt.spentEscrow.locked = false :=
  fulfill_discharges winningBid (𝟙 (res 0 3)) rfl rfl

/-! ## 3. KEYSTONE (b) — causal reveal-ordering EXCLUDES frontrunning.

Anti-frontrunning is "no one may fill before I reveal" = `revealEvt ≺ fill` = `frontrunExcluded demoLace
revealEvt fill` — a frame-invariant happens-before FACT (spine §4/§5), discharged exactly when the bid's
causal validity window is MET at the fill frontier. The `Deadline.Met` check on the bid's validity IS
`CausalAfter demoLace revealEvt fill` (definitional dispatch, `Deadline.lean`): one predicate, no
timestamp race. So MEV = control of a simultaneity surface a causal model simply does not have. -/

/-- **`met_iff_frontrunExcluded`** — the bid's validity window is MET at frontier `fillNow` EXACTLY when
the fill causally follows the reveal (frontrunning excluded). The two are *definitionally* the same
proposition: `Deadline.Met` of `causalAfter revealEvt` dispatches to `CausalAfter demoLace revealEvt
fillNow = frontrunExcluded …`. The anti-frontrunning gate and the deadline check are ONE predicate. -/
theorem met_iff_frontrunExcluded (bidder : Bidder) (alloc : DreggResources)
    (revealEvt fillNow : Frontier) :
    (bidIntent bidder alloc revealEvt).validity.Met fillNow ↔
      frontrunExcluded demoLace revealEvt fillNow :=
  Iff.rfl

/-- **`no_frontrunning` (KEYSTONE b)** — a fill that does NOT causally follow the reveal is REJECTED: the
bid's causal validity window is NOT met at a pre-reveal / concurrent fill frontier. The frontrun is
excluded by the ORDER, not adjudicated by a clock. Definitionally `h` (the validity-Met predicate IS the
frontrun-excluded predicate). -/
theorem no_frontrunning (bidder : Bidder) (alloc : DreggResources) (revealEvt fillNow : Frontier)
    (h : ¬ frontrunExcluded demoLace revealEvt fillNow) :
    ¬ (bidIntent bidder alloc revealEvt).validity.Met fillNow :=
  h

/-- **`honest_fill_admitted` (positive non-vacuity)** — the dual: an HONEST fill that observed the reveal
IS admitted. A bid revealed at genesis `g0` and filled at the honest successor `g1` (which acks `g0`, so
`g0 ≺ g1`) MEETS its validity window — the order admits the honest filler. Without this the (b) keystone
could be vacuously "everything is rejected". Discharged by `demo_frontrun_excluded` (`g0 ≺ g1`). -/
theorem honest_fill_admitted (bidder : Bidder) (alloc : DreggResources) :
    (bidIntent bidder alloc g0).validity.Met g1 :=
  Dregg2.Time.Causal.demo_frontrun_excluded

/-- **`no_frontrunning_teeth` (the (b) TEETH — a real adversarial frontrun REJECTED, proved).** A bid
revealed on the Byzantine fork branch `f1` is GENUINELY UNFILLABLE by a fill on the *concurrent* fork
branch `f2`: `f2` never observed `f1` (they are incomparable, `f1 ∦ f2`), so the fill does not causally
follow the reveal and the bid's validity window is NOT met. The frontrun is caught by the causal order —
not by a gas auction. Discharged via the abstract `no_frontrunning` fed `Time.Causal.demo_frontrun_caught`.
-/
theorem no_frontrunning_teeth (bidder : Bidder) (alloc : DreggResources) :
    ¬ (bidIntent bidder alloc f1).validity.Met f2 :=
  no_frontrunning bidder alloc f1 f2 Dregg2.Time.Causal.demo_frontrun_caught

/-! ## 4. KEYSTONE (c) — CONSERVATION across the settle (no value minted).

The settle receipt carries `conversion : offered ⟶ outcome`, hence `Converts offered outcome` — the fill
type-checks and conserves BY CONSTRUCTION (Spivak's functoriality of operadic substitution; the thin
Coecke–Fritz convertibility shadow of the Phase-3 per-asset `Σ in = Σ out` invariant). A settle that would
MINT value (no conversion exists) is therefore unfillable. -/

/-- **`settle_conserves` (KEYSTONE c)** — the settled outcome is convertible FROM the offered escrow: no
value is minted across the settle. By instantiating the abstract `fulfill_conserves` at the auction
settle. -/
theorem settle_conserves (i : KernelIntent demoLace demoReg demoStmtOf)
    (f : i.offered ⟶ i.wanted) (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true) :
    Converts i.offered (auctionSettle i f hpred hlock).outcome :=
  fulfill_conserves i f hpred hlock

/-- The concrete winning-settle conserves: `res 0 3 ⪰ res 0 3` (the winner's allocation is convertible
from the escrow). -/
theorem winning_settle_conserves : Converts winningBid.offered winningReceipt.outcome :=
  settle_conserves winningBid (𝟙 (res 0 3)) rfl rfl

/-- A **cross-asset bid** that would EXCHANGE value: offer "5 gold" (escrowed), want "1 art". A genuine
exchange intent whose causal validity excludes pre-reveal fills — the honest auction shape Phase 4
sharpens via the market's offer-generated conversions. -/
def crossBid (revealEvt : Frontier) : KernelIntent demoLace demoReg demoStmtOf where
  offered   := res 5 0
  wanted    := res 0 1
  predicate := fun r => r = res 0 1
  resource  := EscrowWitness.fund (res 5 0)
  validity  := Deadline.causalAfter revealEvt

/-- **`settle_cannot_mint` (the (c) TEETH — a real minting settle REJECTED, proved).** A cross-asset settle
that would mint value — turn "5 gold" into "1 art" with NO market offer — is UNFILLABLE: no conversion `5
gold ⟶ 1 art` exists in the discrete resource theory (`res_no_convert`). No conversion ⇒ no fill ⇒ nothing
minted. Conservation is enforced by the *absence* of a conversion, not by an after-the-fact audit. -/
theorem settle_cannot_mint (revealEvt : Frontier) :
    ¬ Converts (crossBid revealEvt).offered (crossBid revealEvt).wanted :=
  res_no_convert (by decide)

/-! ## 5. KEYSTONE one-shot — no double-settle from one escrow. -/

/-- **`settle_no_double` (the one-shot teeth)** — the settled escrow is RELEASED, so it can never again
satisfy `fulfill`'s `locked = true` precondition: no second settle from one funding. The abstract
`no_double_fulfill`, instantiated at the auction settle. -/
theorem settle_no_double (i : KernelIntent demoLace demoReg demoStmtOf)
    (f : i.offered ⟶ i.wanted) (hpred : i.predicate i.wanted) (hlock : i.resource.locked = true) :
    (auctionSettle i f hpred hlock).spentEscrow.locked ≠ true :=
  no_double_fulfill i f hpred hlock

/-- The concrete winning settle is one-shot: its released escrow cannot fund a second settle. -/
theorem winning_no_double : winningReceipt.spentEscrow.locked ≠ true :=
  settle_no_double winningBid (𝟙 (res 0 3)) rfl rfl

/-! ## 6. KEYSTONE — loser-refund LIVENESS (the genuine `◇`).

A losing bidder is EVENTUALLY refunded. From a `JustProgress` package (van Glabbeek reactive justness +
a well-founded refund potential), `just_progress` produces `Eventually Refunded` — the genuine `◇`, not a
trivial `□→◇`. Two faces:
  * the abstract TEMPLATE (`loser_refunded_eventually`): conditional on a supplied package — the escrow
    layer instantiates `Refunded`/`μ` with the holding-store refund-count;
  * the CONCRETE inhabited witness (`auction_loser_refunded`): UNCONDITIONAL on the REAL executor, reusing
    `Fairness.refundDemo` (the B-just `transferSched` path, all four `JustProgress` fields proved against
    the 46-effect executor) — proving the machinery is genuinely INHABITABLE, not a vacuous carried
    package. The teeth that keep `Just` non-vacuous is `Fairness.badSched_not_just` (a starving schedule
    REJECTED). -/

open Dregg2.Proof.Fairness (Just JustProgress Refunded just_progress refundDemo Pgoal
  badSched badSched_not_just)
open Dregg2.Proof.Temporal (Eventually transferSched)
open Dregg2.Exec.TurnExecutorFull (fma0)

/-- **`loser_refunded_eventually` (KEYSTONE liveness, the TEMPLATE)** — given a `JustProgress` package whose
potential is the pending-refund count and whose goal is `Refunded` (all refunds discharged),
`just_progress` yields `Eventually Refunded`: the loser IS eventually refunded. The escrow layer
instantiates `Refunded`/`μ` with the real holding-store (architect Q4a default: the abstract template
ships; the executor-wired `μ` is the Q4b ember decision). -/
theorem loser_refunded_eventually {B s sched} (jp : JustProgress B Refunded s sched) :
    Eventually Refunded s sched :=
  just_progress jp

/-- **`auction_loser_refunded` (the liveness TEETH — `◇` genuinely PRODUCED, UNCONDITIONAL).** The
concrete `refundDemo` package (the B-just `transferSched` path on the REAL executor, all four
`JustProgress` fields proved) feeds `just_progress` to yield `Eventually Pgoal fma0 transferSched` with NO
hypotheses: the refund goal IS eventually reached. This de-vacuifies `loser_refunded_eventually` — the
`JustProgress` machinery is genuinely inhabitable and `just_progress` truly produces a `◇`. (`Pgoal` =
"a receipt has landed", the concrete stand-in the escrow holding-store replaces.) -/
theorem auction_loser_refunded : Eventually Pgoal fma0 transferSched :=
  just_progress refundDemo

/-- **`auction_starvation_rejected` (the liveness NON-VACUITY teeth)** — the justness criterion genuinely
REJECTS a starving schedule: `badSched` (firing only an independent cell forever) is NOT B-just, so it
cannot underwrite a refund-liveness claim. Without this the `Just` premise of `loser_refunded_eventually`
could be vacuously `True` and the `◇` would be empty. dregg2's [Survey] Example 21 ("Bart never gets his
beer"), re-exported as the auction's anti-starvation guarantee. -/
theorem auction_starvation_rejected : ¬ Just (fun _ => True) fma0 badSched :=
  badSched_not_just

/-! ## 7. The (a) obligation — userspace-escrow ≥ kernel-escrow — a CARRIED OPEN (not a stub).

⚑ MODEL-SHAPE CALL FOR EMBER (architect Q6). The §5/§7 headline `kernelEscrow ⊑ userspaceEscrow` (anything
the kernel escrow conserves/guarantees, the userspace escrow does too) needs a definition that does NOT
yet exist in the green tree:
  * the userspace-escrow CELL-PROGRAM holding `offered`, released exactly on the discharging receipt
    (`INTENT-AS-CO-RECEIPT.md` §2 face 3) — the current `EscrowWitness` is the kernel side's thin one-shot
    lockbox (`locked : Bool`), not a userspace cell-program; and
  * a state CLOCK / block-height dimension the executor lacks (`EFFECT-FIDELITY-LEDGER.md`: `refund
    CommittedEscrowA` is a SHADOW that can refund before deadline; `RecChainedState` has no clock).

Per MEMORY "Improve Don't Degrade" + "Don't Cheap Out on Hard Proofs", this is NOT stubbed and NOT
`sorry`'d. It is stated as a carried-hypothesis INTERFACE obligation: a relation `UserspaceDominatesKernel`
(the simulation/refinement on the escrow guarantees) and the corollary `escrow_refinement_sound` that, ONCE
the refinement is supplied, every kernel-escrow guarantee transfers to the userspace escrow. The build ships
(b)+(c)+liveness green around it; ember picks the shape (cell-program refinement vs. abstract interface)
before the relation is *constructed*. -/

/-- **`EscrowGuarantee`** — a property an escrow witness must uphold (e.g. "locked ⇒ funds held",
"released ⟺ a discharging receipt exists", "refundable ⟺ expiry-without-fill"). Parametrized over the
offered bundle. A `Prop`-valued predicate on `EscrowWitness offered` — the abstract surface the (a)
inequality compares the two escrows on. -/
abbrev EscrowGuarantee (offered : DreggResources) := EscrowWitness offered → Prop

/-- **`UserspaceDominatesKernel` (the (a) OPEN, as a carried hypothesis)** — the userspace escrow over
`offered` UPHOLDS at least every guarantee the kernel escrow does. Formally: for every guarantee `G`, if
the kernel escrow `ke` satisfies `G` then the userspace escrow `ue` does too. This is the `⊑` refinement
typed at the abstract `EscrowWitness` layer (architect Q6 option (ii)); option (i) — a userspace-escrow
cell-program with its own release/refund semantics so `⊑` is an executable simulation against
`createEscrowKAsset` — is the deferred build. **CARRIED, never assumed of a specific escrow: a theorem
takes it as a hypothesis.** -/
def UserspaceDominatesKernel {offered : DreggResources}
    (ke ue : EscrowWitness offered) : Prop :=
  ∀ G : EscrowGuarantee offered, G ke → G ue

/-- **`escrow_refinement_sound` (the (a) corollary — sound the MOMENT the refinement is supplied)** — GIVEN
the carried refinement `UserspaceDominatesKernel ke ue`, any guarantee the KERNEL escrow upholds, the
USERSPACE escrow upholds too. This is the content of "userspace-escrow ≥ kernel-escrow" at the interface
layer: it is `h` applied to the guarantee. It does NOT assert the refinement exists (that is the OPEN
ember decides) — it shows the inequality is a one-line consequence once the refinement is constructed, so
the obligation is precisely localized to building `UserspaceDominatesKernel`. -/
theorem escrow_refinement_sound {offered : DreggResources} {ke ue : EscrowWitness offered}
    (h : UserspaceDominatesKernel ke ue) (G : EscrowGuarantee offered) (hk : G ke) : G ue :=
  h G hk

/-- **`escrow_refinement_reflexive` (non-vacuity of the interface)** — the refinement relation is
INHABITED: an escrow trivially dominates ITSELF (`UserspaceDominatesKernel e e`). This proves
`UserspaceDominatesKernel` is not the empty relation / not vacuously unsatisfiable — there is at least one
real witness, so `escrow_refinement_sound` has content. (The NON-trivial witness — the userspace
cell-program genuinely dominating the kernel lockbox — is the OPEN ember scopes.) -/
theorem escrow_refinement_reflexive {offered : DreggResources} (e : EscrowWitness offered) :
    UserspaceDominatesKernel e e :=
  fun _ hk => hk

/-! ## 8. `#eval` smoke — the auction's load-bearing bits, decided by the model alone. -/

#eval winningReceipt.outcome.as |>.toAdd      -- (0, 3)  the settled allocation (3 art to the winner)
#eval winningReceipt.spentEscrow.locked        -- false   the escrow is consumed (one-shot)
#eval winningBid.validity.kind                 -- true    causal reveal-ordering (anti-frontrunning)
-- (b): the honest fill saw the reveal (g0 ≺ g1) ⇒ admitted; the fork fill did not (f1 ∦ f2) ⇒ rejected.
#eval decide (g0.id ∈ g1.preds)                -- true    honest fill at g1 observed reveal at g0
#eval decide (f1.id ∈ f2.preds ∨ f2.id ∈ f1.preds)  -- false  fork fill at f2 never saw reveal at f1

/-! ## 9. Axiom hygiene — every keystone pinned to the standard kernel triple.

`#assert_axioms` walks each keystone and errors if any escapes `{propext, Classical.choice, Quot.sound}` —
a `sorryAx` anywhere would fail the build. No `sorry`/`admit`/`axiom`/`native_decide` leaked into the
decision-free core (the (a) obligation is a carried hypothesis, NOT an axiom). -/

#assert_axioms winning_discharges
#assert_axioms met_iff_frontrunExcluded
#assert_axioms no_frontrunning
#assert_axioms honest_fill_admitted
#assert_axioms no_frontrunning_teeth
#assert_axioms settle_conserves
#assert_axioms winning_settle_conserves
#assert_axioms settle_cannot_mint
#assert_axioms settle_no_double
#assert_axioms winning_no_double
#assert_axioms loser_refunded_eventually
#assert_axioms auction_loser_refunded
#assert_axioms auction_starvation_rejected
#assert_axioms escrow_refinement_sound
#assert_axioms escrow_refinement_reflexive

end Dregg2.Apps.SealedBidAuction
