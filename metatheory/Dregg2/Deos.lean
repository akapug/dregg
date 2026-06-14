/-
# Dregg2.Deos — the VERIFIED-DEOS crown: "a verified desktop OS" made literal.

`docs/deos/DEOS.md` §"the verified-deos program": *"every visual/interactive primitive reduces to a
kernel theorem. None are new mathematics — they are the firmament's existing proofs (attenuation,
gateOK, the receipt chain, unfoolability) restated for pixels, affordances, and rehydration."*

`deos` is the agentic desktop userlayer: cap-confined surfaces, the certified compositor, the
web-of-cells, the rehydratable frustum-snapshots — *dregg made visual, with zero new trust*. The Rust
realization already shipped (the rehydration + affordance steel in `starbridge-web-surface`); this lane
is the PROOF that it cannot amplify / the liveness-type IS the confined fragment. The four targets, each
a kernel theorem restated for the desktop:

  1. **Surface-as-capability** (`Dregg2.Deos.Surface`) — a `Target::Surface(cell)` is a kernel
     `Cap.endpoint cell rights`; a window confers no authority beyond its rights, and a view/notify-only
     surface confers NO Granovetter edge (`viewSurface_confers_no_edge`, the
     `notifyCap_confers_no_edge` shape). Projecting a surface to fewer rights cannot amplify
     (`surface_attenuate_no_amplify` = `Dregg2.Exec.attenuate_subset`).

  2. **Membrane non-amplification** (`Dregg2.Deos.Membrane`) — the rehydration membrane composes
     attenuation across hops: `reshare A→B→C ⟹ C ⊆ B ⊆ A` (`reshare_chain_attenuates`, the per-hop
     `attenuate_subset` lifted by `List.Subset.trans`), generalized to arbitrarily-long reshare chains
     (`reshareN_attenuates`). The Rust `Membrane` is the realization; this is the proof it cannot
     amplify. A widening is darkened, not granted (`reshare_refuses_amplification`).

  3. **Rehydration confinement = the liveness-type** (`Dregg2.Deos.Rehydration`) — THE CROWN.
     `ReplayedDeterministic` IS *exactly* the confined fragment: for a non-`Live` context,
     `classify = ReplayedDeterministic ↔ every interaction was a witnessed attested turn`
     (`replayedDeterministic_iff_confined`). The doc's "derived" row, as an `↔`. The replay payoff
     (`replayedDeterministic_replays`) rides the EXISTING receipt-chain tamper-evidence
     (`Dregg2.Exec.Receipts.chain_tamper_evident`) under the §8 digest oracle, carried as NAMED
     hypotheses.

  4. **Affordance soundness** (`Dregg2.Deos.Affordance`) — a cell-affordance interaction is a verified
     turn: an agent fires ONLY the affordances its caps authorize (`fire_authorized_iff`, the
     `is_attenuation` gate `required ⊆ held`), the post-state surface binds the attested root
     (`firedSurface_binds_attested_root`, the receipt's `newCommit`), and progressive enhancement is
     progressive ATTENUATION (`projectFor_monotone`).

## Honesty ledger (legs fully discharged vs carried as named hypotheses)

  * Legs 1, 2, 4 and the leg-3 CLASSIFIER CROWN (`replayedDeterministic_iff_confined` + its dual) are
    FULLY DISCHARGED — pure structural facts over the kernel cap/attenuation lattice and the receipt
    record, no oracle, every keystone `#assert_all_clean` (kernel-clean: only `propext` /
    `Classical.choice` / `Quot.sound`).
  * Leg 3's REPLAY PAYOFF (`replayedDeterministic_replays`) carries the receipt-digest
    collision-resistance as NAMED hypotheses `HInj : Function.Injective H` / `HFresh : ∀ p, H p ≠
    genesisSentinel` — the SAME `dregg2 §8` oracle `Dregg2.Exec.Receipts.chain_tamper_evident` already
    names, NEVER a Lean axiom and NEVER a `sorry`. This is the one honest seam (the digest's
    collision-resistance), in the house honesty-ledger style: a named crypto primitive, not a laundered
    vacuity. The CROWN itself (the confinement `↔`) needs no such hypothesis.

Everything builds LOCAL (`lake build Dregg2`, cwd `metatheory/`) green + axiom-clean. `metatheory/`
only; no core-`Auth`/`Cap`/`Receipt` edit — every theorem is an existing kernel proof restated for
surfaces / membranes / rehydration / affordances.
-/
import Dregg2.Deos.Surface
import Dregg2.Deos.Membrane
import Dregg2.Deos.Rehydration
import Dregg2.Deos.Affordance

namespace Dregg2.Deos

/-! ## The verified-deos namespace assembles the four legs. Each sub-module pins its own keystones
kernel-clean (`#assert_all_clean`); this umbrella re-exports them as the single `Dregg2.Deos` surface.

The four targets, as one sentence: a deos surface is a kernel cap (leg 1) whose per-viewer projection
and membrane reshares cannot amplify (legs 1+2), whose affordances fire only under the `is_attenuation`
gate and bind the attested root (leg 4), and whose rehydration liveness-type IS exactly the confined
fragment (leg 3, the crown). "A verified desktop OS": every visual/interactive primitive reduces to a
kernel theorem. -/

end Dregg2.Deos
