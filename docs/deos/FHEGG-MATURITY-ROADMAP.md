# fhEgg — the maturity roadmap: are we building the vision, or the easy waters?

*Written 2026-07-18 after ember's nudge: (1) the GPU residency insight — we measured transfer-bound loss
because the data was in the wrong memory space to begin with; (2) the harder question — make sure we build
toward the FULLEST, most mature fhEgg, not the tractable stones that are easy to finish but aren't the
vision. This doc is the honest carve. Companion to `FHEGG-KERNEL.md` (what-is), `FHEGG-SDK-READINESS.md`
(is-it-shippable), `DREGGFI-VISION.md` (the ambition), `FHEGG-MATHEMATICAL-BRIEF.md` §5-7 (the frontier).*

---

## 0. The honest self-assessment: where the effort has actually gone

The vision (from the genesis 2026-07-13 → the codex rounds) is a **private convex-derivatives factory**:
one homomorphic-fold kernel, three privacy tiers, a typed product DSL (`fhIR`), the convex engine at `T>1`,
real no-viewer — *"you shouldn't have to choose between a market that's private and one you can prove is
fair."*

What we have actually BUILT, honestly graded by **distance-to-vision**, not by effort:

| built | grade | is it the vision, or the tractable foundation? |
|---|---|---|
| addition fold (CPU, Lean-verified; GPU, parity-proven) | WORKING | **foundation.** The `T=1` linear primitive. Necessary, not the vision. |
| uniform-price auction clearing + Cert-F (ring-3 → market4) | WORKING | **foundation.** ONE product, `T=1`, one tier. |
| the settle/wire SDK surface | WORKING | **foundation.** Plumbing for the plaintext tier. |
| ct×ct multiply (oracle-anchored), one convex iteration, the mult-noise Lean | STONE-1 | **first reach at the vision** — the multiplicative + `T>1` frontier, but toy-scale. |
| GPU fold shader | WORKING-BUT-LOSES | **a detour** — correct, but measured to be a de-optimization for one-shot folds. |

**The honest verdict:** we have built an excellent *foundation* and taken the *first* step toward the
vision (multiply + one convex iteration). But the center of gravity has been the tractable layer. The five
things that make fhEgg the VISION — not a good private-auction demo — are each named-not-built. That is the
gravity to fight.

---

## 1. The residency insight — performance excellence is an ARCHITECTURE, not a shader tweak

**The mistake we measured:** the GPU fold "loses ~5-7×" because the benchmark uploads N ciphertexts,
does ONE streaming pass of adds (arithmetic intensity ≈ 0), and downloads. The transfer dominates *because
the data should never have been round-tripping*. We optimized a shader when the problem was the memory
model.

**The right architecture — GPU-RESIDENT end-to-end.** Encrypted orders are uploaded ONCE at ingress and
STAY on the device; the WHOLE clearing runs on-GPU:

```
ingress: encrypt orders ──upload once──▶  [ GPU-resident ciphertext arena ]
                                             │  fold        (add, resident — now FREE, no transfer)
                                             │  histogram   (measured 11.4× at N=1M)
                                             │  crossing / argmax
                                             │  convex iterations  x ← prox(x − τAx)   (T of them)
                                             │  ct×ct multiply  (NTT — the GPU-saturating kernel, Merkle-class 23×)
                                             ▼
egress: threshold-decrypt (p*, V*) ◀──download once (a few scalars)
```

The transfer then amortizes over a MINUTES-long homomorphic computation instead of over one add. Every
op that already wins on-device (histogram 11×, Merkle-class hashing 23×, DFT 4-6×) wins, and the fold
becomes *free* (already resident). **This is the performance north star: a resident ciphertext arena + a
scheduler that keeps data on-device across the whole pipeline, host↔device only at ingress/egress** — the
same shape real FHE accelerators (Zama CUDA, FPGA) use. `GpuResidentPipelineResidual` — the single
highest-leverage performance build, and it makes the fold-GPU "loss" evaporate by construction.

---

## 2. The five vision-critical builds (the "fullest fhEgg" — NOT the easy waters)

Ranked by how load-bearing they are to the VISION, with the honest "why it's hard" (which is exactly why
they get deferred for easier stones):

1. **REAL no-viewer — the threshold decrypt with proper smudging.** Today "nobody sees the orders" is
   *prose + a modeled seam*: the deployed path is single-key (caller decrypts everything), and the n-of-n
   collective decrypt lives in fhe.rs's `mbfv` whose smudging noise is an upstream `TODO`. **Without this,
   the ENTIRE privacy claim — the reason fhEgg exists — is a lie.** This is the vision's keystone, and it is
   the Lean-first BFV endgame (prove the smudging bound instead of inheriting the TODO). `NoViewerKeyCustodyResidual`.

2. **The convex engine at `T>1`.** We have ONE iteration. The vision is an ITERATED private convex solver —
   that is what turns "a call auction" into "a derivatives factory" (AMM curves, routing, portfolio
   rebalance are all convex programs). The hard part: the noise budget across `T` iterations (each add
   doubles, each public-scalar-mult grows noise) — the Lean `Bfv/` noise theory must bound the whole `T`-deep
   composition, or we bootstrap. `ConvexEngineTGt1Residual`.

3. **`fhIR` — the typed product DSL.** The vision's headline: a language where "admissible iff it compiles /
   passes the resource manifest," so a product's PRIVACY TIER is a TYPE. Nothing of it is built. Without it,
   every new product is a hand-rolled circuit; with it, products are *expressed and admitted*. This is the
   difference between a clearing engine and a *factory*. `FhIRLanguageResidual`.

4. **The GPU-resident pipeline** (§1) — performance excellence, the thing that makes minutes into seconds
   and makes realistic market sizes tractable. `GpuResidentPipelineResidual`.

5. **A REAL product cleared privately, end-to-end.** Not another primitive — an actual derivative (an
   option payoff `max(S−K,0)`, or an AMM `x·y=k` with hidden reserves) expressed in fhIR, cleared through
   the convex engine at Tier 0, with a Cert-F certificate, decrypted only at the threshold boundary. This is
   the integration proof that the vision holds — the thing none of the isolated stones prove. `EndToEndPrivateDerivativeResidual`.

---

## 3. The discipline this doc exists to enforce

**The easy waters are seductive because every stone compiles green.** Another SDK verb, another parity test,
another envelope re-measure — all real, all tractable, none of them the vision. The check, borrowed from the
session's frame: before starting a fhEgg unit, ask **"does this move us toward one of the five, or is it
another comfortable foundation stone?"** Foundation is not free to keep polishing when the keystone
(no-viewer) is still prose.

The one-line vision, to hold onto when the easy water is warm: **fhEgg is not a private auction — it is a
factory for markets that are private AND provably fair, and it is not done until a real derivative clears
end-to-end with nobody seeing the orders.**
