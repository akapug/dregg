# DEBT-A — the real target for an honest `instance : StarkSound`

**Honest scope, first sentence.** `AlgoStarkSound` and `DeployedRefines` are stated
over **abstract** parameters (`F = Int`, an abstract `perm`, and universally-quantified
`params : FriParams` / `vk : RecursionVk Int` / `checks : FriChecks Int` / `view` — NEVER
pinned to `ir2LeafWrapConfig`, the real Poseidon2 permutation, or `vkOfRegistry R`), and of
the chain that a real `StarkSound` needs, **zero links are PROVED as soundness**: the bridge
composition is a trivial one-liner, a family of *rejection* teeth are genuinely proven but
over abstract `F` and cover only specific tamperings, and the two load-bearing links
(`AlgoStarkSound`, `DeployedRefines`) are BOTH assumed. So the "verifier out of the TCB"
bridge replaced **one** assumed carrier (`StarkSound`) with **two** assumed carriers.

---

## 1. `AlgoStarkSound` — full statement (quoted)

`metatheory/Dregg2/Circuit/FriVerifierBridge.lean:75-84`:

```lean
class AlgoStarkSound (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Prop where
  extract : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace),
      Satisfied2 hash (R pi.effect) minit mfin maddrs t ∧
        tracePublishedCommit t = pi.toPublished
```

**Params: ABSTRACT, not deployed.** `F` is fixed to `Int`, not BabyBear. `perm`, `RATE`,
`toNat`, `params`, `vk`, `checks`, `initState`, `logN`, `view` are all **binders** of the
class — a caller may instantiate them with anything. Nothing forces `params = ir2LeafWrapConfig`
(`FriVerifier.lean:370`, the real `logBlowup 6 / numQueries 19 / powBits 16`), nothing forces
`perm` to be the real Poseidon2BabyBear<16>, nothing forces `vk = vkOfRegistry R`, nothing
forces `checks = fullChecks …`. The doc-comment calls it "the SPECIFIED algorithm" but the
class does not pin the algorithm to the deployment. **Zero instances exist** (grep across
`metatheory`: only the definition and `[carrier : AlgoStarkSound …]` hypothesis uses).

`FriParams` (`FriVerifier.lean:358`), `RecursionVk` (`:544`, a single-field
`shapeMatches : BatchProofData F → Bool` — the blake3 VK fingerprint is explicitly *out of
band*, so this is a shape predicate, not the real VK), `FriChecks` (`:480`, a record of four
Boolean sub-checks), `ProofView` (`FriVerifierBridge.lean:64`, the flat proof-data reading)
are all generic-`F` structures. They are the SHAPES of the deployed objects, over abstract `F`.

## 2. `DeployedRefines` — statement + proved-or-assumed

`FriVerifierBridge.lean:92-99`:

```lean
def DeployedRefines (R : Registry) (perm …) (params …) (vk …) (checks …) … (view …) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyBatch (vkOfRegistry R) pi π = accept →
    verifyAlgo perm RATE toNat params vk checks initState logN (view pi π).1 (view pi π).2 = true
```

It asserts the opaque deployed `verifyBatch` refines `verifyAlgo`. It is a `def`, taken as a
hypothesis `href` in `starkSound_of_verifyAlgo` (`:112`), `lightclient_unfoolable_via_algo`
(`:131`), and `deployed_rejects_tampered_quotient` (`:167`). **It is never proved and never
instantiated** — ASSUMED. Note the LHS uses the real `verifyBatch`/`vkOfRegistry R`, but the
RHS's `verifyAlgo` is fed the same abstract `params/vk/checks/perm/view` the def binds, so
"refines" here is "refines *some* abstract algorithm instance", not "refines the deployed p3
verifier at BabyBear params".

## 3. `StarkSound.extract` — what a real instance must produce

`CircuitSoundness.lean:382-387`:

```lean
class StarkSound (hash : List ℤ → ℤ) (R : Registry) : Prop where
  extract : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyBatch (vkOfRegistry R) pi π = accept →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (R pi.effect) minit mfin maddrs t ∧
        tracePublishedCommit t = pi.toPublished
```

A real instance must, from *only* the deployed verdict `verifyBatch (vkOfRegistry R) pi π =
accept`, PRODUCE a concrete satisfying VM trace `t` of the claimed descriptor whose published
old/new commitments equal `pi`. This is the FRI/p3 `verify ⟹ ∃ witness` extraction — the
irreducible content. `verifyBatch` is `opaque` (`CircuitSoundness.lean:353`); `tracePublishedCommit`
is `opaque` (`:366`).

## 4. The honest decomposition — each link marked

| # | Link | Status | Where |
|---|------|--------|-------|
| A | FRI proximity / low-degree soundness @ deployed BabyBear params (`ir2LeafWrapConfig`) | **MISSING** | no such theorem; folded into A′ below as an assumption |
| B | AIR soundness: batch constraints hold at OOD ζ ⟹ trace `Satisfied2` | **MISSING** (positive dir.) | reject-side only, `tableOk_rejects_*` `FriVerifier.lean:684,693` |
| C | ChipTable / logup-bus soundness @ real perm | **MISSING** (positive dir.) | reject-side only, `batchTablesCheck_rejects_unbalanced_bus :704` |
| D | a real `FriExtract` producing the `VmTrace` | **MISSING** | no algorithm produces the witness |
| A′ | `AlgoStarkSound.extract` (A+B+C+D bundled as one assumed field, abstract `F`) | **ASSUMED** | `FriVerifierBridge.lean:75` (0 instances) |
| E | `DeployedRefines` (Rust `verifyBatch` = spec `verifyAlgo`) | **ASSUMED** | `FriVerifierBridge.lean:92` (never proved) |
| F | `starkSound_of_verifyAlgo : [AlgoStarkSound] + DeployedRefines ⟹ StarkSound` | **PROVED (trivial)** | `FriVerifierBridge.lean:106-114`, body `carrier.extract pi π (href pi π hacc)` |
| G | reject-teeth: tampered-quotient / wrong-degree / bad-PoW / wrong-query-count ⟹ verifier rejects | **PROVED but TOY** (abstract `F`, rejection-only) | `verifyAlgo_full_rejects_tampered_quotient :752`, `verifyAlgo_concrete_rejects_wrong_query_count :584`, `deployed_rejects_tampered_quotient` (Bridge `:162`) |

**The biggest lever is A′ = `AlgoStarkSound`.** It bundles the entire hard content — FRI
low-degree soundness (A), AIR/quotient soundness (B, C), and witness extraction (D) — into a
single assumed `extract` field. This is *exactly the same opaque content* that was assumed in
`StarkSound`, merely re-hosted over `verifyAlgo` instead of `verifyBatch`. Discharging it is
the whole game; `DeployedRefines` (E) is a genuine but comparatively shallow code=spec
refinement obligation.

## 5. Architecture verdict — good decomposition vs laundering-by-indirection

**For "good decomposition":** the SHAPE is right and is the same shape as DEBT-B's `denote`
refinement — separate (i) algorithm soundness (`AlgoStarkSound` over the specified
`verifyAlgo`) from (ii) code refinement (`DeployedRefines`: the Rust verifier computes the
same accept Boolean). This correctly isolates the one thing that must stay trusted about the
*code* (E) from the math floor (A′), and it makes the Fiat-Shamir transcript derivation
(`deriveFri`/`deriveQueryIndices`, `FriVerifier.lean:426,450`) and the reject-checks
CONCRETE and specified rather than hidden in an opaque verdict. The reject-teeth (G) are
**real, non-vacuous** theorems (`deployed_rejects_tampered_quotient`, `FriVerifierBridge.lean:162`,
genuinely rules out a deployed accept of a tampered quotient via the refinement + a proven
`verifyAlgo` rejection) — that is real soundness work moved out of the TCB.

**For "laundering-by-indirection":** two objections. (1) `AlgoStarkSound.extract` still
bundles FRI-LDT + AIR-soundness + trace-decode into one assumed field — the *positive*
extraction (accept ⟹ ∃ satisfying trace), which is the hard direction, is untouched; only
the *rejection* contrapositive is proven, and only for a handful of specific tamperings. The
opaque content did not shrink; it moved. (2) The bridge turned ONE assumed carrier into
**TWO** assumed carriers (A′ and E), and both are stated over abstract `F = Int` / abstract
`perm` / free `params/vk/checks`, so neither is pinned to the deployed BabyBear + Poseidon2 +
`ir2LeafWrapConfig` + `vkOfRegistry R` objects the names ("Deployed", "the SPECIFIED
algorithm") imply. `DeployedRefines` sounds deployed; its `verifyAlgo` argument is an
abstract binder.

**Verdict: a GOOD decomposition SHAPE that is currently under-discharged and mildly
laundering.** The factoring (algorithm-soundness ⟂ code-refinement) is the correct target and
worth keeping. But as it stands it is honest only if the doc-comments stop calling A′/E
"the deployed verifier" and "the SPECIFIED algorithm": both are abstract, both assumed, and
the trusted surface grew from one carrier to two. The reject-teeth are the one genuine gain.

### What discharging `AlgoStarkSound` for real requires

Instantiate the class at the **deployed** objects — `F = BabyBear` (`p = 2^31 − 2^27 + 1`),
`perm = Poseidon2BabyBear<16>`, `params = ir2LeafWrapConfig`, `checks = fullChecks core A …`,
`vk = vkOfRegistry R`, `view = the faithful byte reading` — and PROVE `extract` from:

1. **FRI/Reed–Solomon proximity-gap soundness** at `logBlowup 6, numQueries 19, powBits 16`:
   an accepted codeword is δ-close to a degree-`< 2^k` polynomial except with the claimed
   ~130-bit error. Not in Mathlib; the genuinely deep obligation (link A).
2. **AIR quotient soundness (DEEP-ALI / batch-STARK):** the OOD quotient identity
   `C(ζ) = Z_H(ζ)·q(ζ)` holding at a Fiat-Shamir-random ζ ⟹ the low-degree trace satisfies
   the AIR constraints everywhere ⟹ a `Satisfied2` witness (links B, C — currently only the
   `rejects` contrapositive of the *identity check* is proven, `FriVerifier.lean:684`).
3. **Poseidon2 Merkle binding** at the real perm (already carried as `Poseidon2SpongeCR`,
   `CircuitSoundness.lean:471`) to bind the opened columns to the committed trace.
4. **A `FriExtract` algorithm** turning the accepted openings into the concrete `VmTrace`
   `t` and discharging `tracePublishedCommit t = pi.toPublished` (link D).

Then `DeployedRefines` (E) remains as the sole *code*-trust residual, and it too should be
pinned: its RHS `verifyAlgo` must be applied to `ir2LeafWrapConfig` + the real `perm`, and it
should be discharged by a Rust↔Lean differential (the analogue of `GnarkRefines`), not left as
a free hypothesis.
