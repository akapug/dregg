/-
# Metatheory.PolisPolitician — the politician capture-shape catalog, bound to deployed proofs.

gpt5.5's politician is a LAWFUL adversary who composes valid moves into domination; each
capture-shape is a public-trace property the polis floor forbids WITHOUT inspecting interiors
("govern trace-shape, not motive"). The census (`w9p6ffrrn`) found each shape already realized
by a DEPLOYED, kernel-clean dregg theorem — pinned here as the politician floor (a regression
fails this build). The flow/policy refinement shape (decidable via the Büchi game) is the
`Metatheory.PolisFlowRefine` companion; the broad interleaved-multi-agent hyperproperty family
stays the named research object.
-/
import Dregg2.Tactics
import Metatheory.EpistemicDial
import Dregg2.Finality
import Dregg2.World
import Dregg2.Exec.FullForestAuthPortal
import Dregg2.Exec.ConditionalTurn

namespace Metatheory.PolisPolitician

/-! ## disclosure-ratchet — disclosure cannot be forced upward as the price of participation.
Acceptance is the SAME at every dial rung (`accepts_invariant_under_dial`), preserved as one
descends (`accepts_preserved_down`), and a lower rung leaks no more (`leak_mono`): a participant
may always sit at the lowest disclosure and still be accepted. -/

#assert_axioms Metatheory.DiscloseAt.accepts_invariant_under_dial
#assert_axioms Metatheory.DiscloseAt.accepts_preserved_down
#assert_axioms Metatheory.DiscloseAt.leak_mono

/-! ## grade-laundering — weak finality cannot be laundered into strong; finality is monotone.
No run can downgrade (or unearned-upgrade) a value's finality tier (`no_downgrade`,
`world_no_downgrade`); the ladder is a genuine total order (`Tier.rank_injective`); re-tiering
cannot change the conservation verdict (`conservation_tier_independent`). -/

#assert_axioms Dregg2.Finality.no_downgrade
#assert_axioms Dregg2.World.world_no_downgrade
#assert_axioms Dregg2.Finality.Tier.rank_injective
#assert_axioms Dregg2.Finality.conservation_tier_independent

/-! ## clerk-monopoly / fungibility — validity depends on the PROOF, not the prover.
The portal verify accepts a genuine proof/custom arm regardless of who produced it
(`proof_arm_sound`, `custom_arm_sound`) and rejects the unchecked arm (`unchecked_arm_rejects`):
no clerk is a mandatory bottleneck — any valid proof from any path is accepted. -/

#assert_axioms Dregg2.Exec.FullForestAuthPortal.proof_arm_sound
#assert_axioms Dregg2.Exec.FullForestAuthPortal.custom_arm_sound
#assert_axioms Dregg2.Exec.FullForestAuthPortal.unchecked_arm_rejects

/-! ## hole-rent — an open obligation cannot be farmed for leverage: resolution is atomic/once.
A conditional turn commits atomically (`condTurn_atomic`); the one-shot resolver fires exactly
once (`commit_resumes_once`, `one_shot_is_static`, pinned in `PolisNonConfusion`): no
rent-extraction via an indefinitely-held, re-exploitable hole. -/

#assert_axioms Dregg2.Exec.ConditionalTurn.condTurn_atomic

end Metatheory.PolisPolitician
