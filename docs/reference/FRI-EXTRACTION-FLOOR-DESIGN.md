# FRI-EXTRACTION-FLOOR-DESIGN — discharging (or honestly grounding) the per-node FRI extraction hypothesis

**Status: design/thought document. No Lean changes accompany it — soundness-adjacent work gets
thought before edits.** File references are `file:line` at HEAD, 2026-07-16.

The subject is the ONE remaining assumed leg under the grounded apex: the per-node FRI extraction
floor. Everything above it is derived; everything below it is currently a deterministic universal
claim that — this document argues — can never be discharged *in its current shape*, and does not
need a cost model to be repaired. The repair is a re-basing of the SAME statement over a
query-counting oracle model, where each conjunct of the bundle either becomes a theorem or becomes
a citation-shaped probabilistic carrier with an adversary type.

---

## 1. The floor as it stands — the exact statements

### 1.1 `FriLdtExtractV3` — the leaf/slice extraction bundle

`metatheory/Dregg2/Circuit/AlgoStarkSoundTransferV3.lean:131`:

```lean
def FriLdtExtractV3
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN (view pi π).1 (view pi π).2 = true →
    ∃ (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      ...
```

with twelve conjuncts under the existential: the trace-capacity bound, the OOD-point pin, the
opened table's membership, the two Merkle recomputes binding `vCommitted` and
`topen.constraintEval` to a common `root`, the transferV3 COLUMN-LAYOUT equation
(`(batchResidual (Rfam transferV3 t ζ qp)).eval Λ = vCommitted − vanishing·quotient`, with the
BabyBear→ℤ bridge), **the FS non-exceptionality of Λ** (`Λ ∉ exceptionalSet …`), **the FS
non-exceptionality of ζ per arith constraint**, the non-arith `holdsAt` legs, the two
aux-table-emptiness facts, and `tracePublishedCommit t = pi.toPublished`.

`ProofView` (`FriVerifierBridge.lean:64`) is `BatchPublicInputs → BatchProof → BatchProofData ℤ ×
WrapPublics ℤ` — the marshaling view. The consumer is
`algoStarkSound_transferV3` (`AlgoStarkSoundTransferV3.lean:256`), which takes
`(hfri : FriLdtExtractV3 …)` plus `Poseidon2SpongeCR sponge` and produces the full
`AlgoStarkSound` class. That is the file whose §3 honestly derives `hood` and `MainAirAcceptF`
from the bundle's primitives — the derivation work is real and stays; only the bundle itself is
assumed.

### 1.2 `AggAirSound.FriExtract` — the recursion-node extraction

`metatheory/Dregg2/Circuit/AggAirSound.lean:140`:

```lean
def FriExtract (ChildVerifierSat : ℤ → Seg → Prop) : Prop :=
  ∀ c s, ChildVerifierSat c s → ∃ p, verify p = true ∧ vkCommit p = c ∧ exposedPI p = s
```

— a satisfied in-circuit child-verifier subcircuit (pinned at commitment `c`, claiming segment
`s`) yields a GENUINE child proof that verifies, with that VK core and that exposed segment. The
header calls it, correctly, "the standard 'SNARK of a fixed verifier circuit is sound'
obligation… localized to ONE child of ONE node."

### 1.3 The tree is done; the residual is exactly per-node

`RecursiveSoundFromNodes.lean` proves the whole-tree fold: `NodeCarrier`
(`RecursiveSoundFromNodes.lean:108`) is the function-form per-node reading

```lean
def NodeCarrier (verify : Proof → Bool) (H : ℤ → ℤ → ℤ) : PTree Proof → Prop
  | .leaf _ _   => True
  | .node p c l r =>
      (verify p = true →
        (verify (rootP l) = true ∧ verify (rootP r) = true)
          ∧ CombineOk H (segP l) (segP r) c)
      ∧ NodeCarrier verify H l ∧ NodeCarrier verify H r
```

and `recursive_sound_from_nodes` folds it by induction into the root→all-leaves shape
`recursive_sound` asserts. `GroundedApex.lean` then rests the whole-history apex on
{this per-node floor, `Poseidon2SpongeCR`, honest-prover realizer data} — the module headers of
`Dregg2.lean:896–898` state precisely this. **Nothing about the tree, the binding leg, the leaf
leg, or the per-effect family remains assumed. The per-node extraction is the entire residual.**

### 1.4 One more carrier wearing the same costume, noted for consolidation

`FriVerifier.lean:982` carries `class FriLowDegreeSound` whose `extract` field concludes
`∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment` — and
`GenuineWitness` (`FriVerifier.lean:973`) is `structure GenuineWitness (F : Type) where exists_ :
Prop`. Taking `w := ⟨True⟩` satisfies the witness leg vacuously; the class's only real content is
the segment equality. This is a deliberately-labeled placeholder from the wrap lane (its own
comment says "modeled opaquely here"), not a hidden hole — but it is a third name for the same
floor, and the re-basing below should end with ONE floor statement that `FriLowDegreeSound`,
`FriExtract`, and `FriLdtExtractV3` all consume, so the costume count goes to one.

---

## 2. Why the current shape can never be discharged

The three statements above share one shape: **a deterministic, universally-quantified extraction
over ALL accepting proofs, at a FIXED concrete permutation.** `verifyAlgo`
(`FriVerifier.lean:695`) is a `Bool`-valued function of a *supplied* proof; `perm` is the concrete
Poseidon2 permutation; `deriveTranscript` (`FriVerifier.lean:553`) derandomizes Fiat–Shamir
completely. So the set of accepting proofs is a fixed, definite set, and `FriLdtExtractV3` is a
fixed combinatorial claim about it. Three consequences:

**(a) It is unprovable-in-principle.** Proving it would require establishing concrete
cryptographic properties of the actual Poseidon2 permutation (that its FS transcript admits no
exceptional-challenge grinding, that its sponge admits no useful collisions along any accepting
path). Nobody on earth can prove these for a concrete permutation; the entire field works in the
random-oracle/random-permutation model precisely because of this.

**(b) It is very plausibly FALSE as stated** — the [[feedback-prove-the-floor-false]] tooth
applied to our own floor. Two of the bundle's conjuncts are non-exceptionality claims, and the
file itself concedes at `AlgoStarkSoundTransferV3.lean:24–28` that "the escape is real and cannot
be unconditional," quoting the honest ε-form (`ood_hnonexc_escape_prob_le`,
`batchResidual_exceptionalSet_card_lt`, ε ≤ deg/|F|). The existential does not rescue this: the
column-layout equation pins Λ to (essentially only) the transcript-derived value, so a proof whose
*derived* Λ lands in the exceptional set has no alternative Λ to offer. Whether an accepting proof
with exceptional derived Λ *exists* for the concrete Poseidon2 is exactly the kind of astronomical
counting fact that is true-by-pigeonhole in spirit for a compressing sponge and unprovable either
way in practice. A hypothesis that is (unprovable ∧ plausibly-refutable) is not a floor; it is a
name. Compare `FloorGames.hard_top_iff_solvableFrac_negl` (`FloorGames.lean:241`): at the
unrestricted adversary class, every game floor collapses to a density fact and every
deployed-parameter floor is false. The current `FriLdtExtractV3` is the *derandomized* cousin of
that collapse.

**(c) The ledger cannot reach it.** `FriLedgerSound.lean` proves real per-fold density bounds
(`ledger_perFold_soundness`, with the `hΦ`/`M = 1` fiber hypothesis DISCHARGED at every shipped
config via `FriArityFiberDischarge`) — but those are statements about *words and challenge
densities*, quantified over words, never over a strategy. There is no adversary type anywhere, so
there is nothing for the density bounds to bound the *success probability of*. This is the
[[project-fri-soundness-reality]] finding: the deployed "bits" are a calculator output because the
ledger never touches the apex — `StarkSound` assumes `FriLdtExtractV3`, and the two are not even
speaking the same language (densities vs. a deterministic ∀-proof claim). The re-basing below is
exactly the translation layer that lets the proven ledger columns finally *purchase* something at
the apex.

---

## 3. Why a grinding cost model is the WRONG target

The tempting repair is: "add a cost model, then quantify over cost-bounded adversaries, then the
grinding PoW buys 2^16 work." The project record says no, three times over:

1. **The SOTA tried it and deleted it.** EasyCrypt's adversarial-cost judgement (eprint 2021/156)
   was removed in commit `41c2667f` (Strub, 2024-03-29, −10,091 lines, "barely used"). Mathlib's
   `TM2ComputableInPolyTime` has zero uses outside its own file and one witness (the identity
   function). No cost/PPT model exists anywhere in formalized ZK — verified 07-16 by clone+grep
   across ArkLib, VCVio, CryptHOL, SSProve, Bailey's Groth16.

2. **The mechanism of failure is structural, not sociological.** In any free-monad program model,
   *pure computation is free*: `pure (bruteForceDiscreteLog y)` typechecks at cost 0. A cost
   judgement over the monad can only meter what the monad reifies — and the only resource these
   monads reify is *oracle queries*. A "cost model" is therefore either (i) query counting wearing
   a longer name, or (ii) a full machine-model formalization of concrete time, which is the
   research program EasyCrypt abandoned.

3. **Query counting is the escape, and the escape is already PROVEN in this tree.**
   `Dregg2/Crypto/RomQueryFloor.lean` builds `RomEff F Q` (`:442`) — the adversaries that factor
   through a `Q`-query decision tree over the oracle — and proves both directions of the
   separation: `romCollision_hard` (the query-bounded floor is TRUE, information-theoretically,
   via `birthday_cond`) against `romCollision_top_false` (the unrestricted floor is FALSE by
   pigeonhole); `choiceAdv_not_romEff` (`:548`) names why `Classical.choice` is excluded — it
   reads the whole oracle without querying it; `romEff_not_iff_solvableFrac_negl` (`:569`) states
   that the `hard_top_iff_solvableFrac_negl` collapse FAILS for `RomEff`;
   `binaryRom_budget_separates` (`RomQueryDial.lean:216`) shows the budget dial is real. The hard
   part of the escape was never the birthday bound — it was the *dichotomy*, and the dichotomy is
   ours, mechanized.

The grinding PoW illustrates the point perfectly. In a cost model, `powBits = 16` means "the
adversary pays 2^16 *time* per attempt" — unformalizable. In the query-counting ROM, each grinding
attempt IS one oracle query (`deriveQueryPow`, `FriVerifier.lean:536` region: observe witness,
squeeze masked bits, `decide (masked = 0)`), so the grinding term is
`Pr[some query hits the mask] ≤ Q / 2^powBits` — a *theorem* of exactly the `birthday_cond` genre,
with no time model anywhere. The thing the ledger could only bookkeep ("+powBits is a bare
constant; nothing relates grinding to a probability" — `johnsonBits`'s own caveat) becomes
provable the moment the adversary is a query tree.

**Conclusion: the target is not "extraction against cost-bounded adversaries." It is "extraction
against query-bounded oracle adversaries, with a concrete ε(Q, params)."** That statement class
has proofs in the literature (BCS 2016; BCIKS 2020 §8) and precedents in mechanization (VCVio's
Fischlin `knowledgeSoundness`, below).

---

## 4. The extraction-shaped floor, VCVio style

### 4.1 What VCVio actually provides (and where it is)

VCVio is **not vendored** in this metatheory: `metatheory/lake-manifest.json` carries only
{aesop, batteries, Cli, importGraph, LeanSearchClient, mathlib, plausible, proofwidgets, Qq}, and
the only in-tree mention is a design note (`metatheory/docs/HARVEST-KEEPERS.md:87`). A full clone
(a fork with substantial 2026 additions) sits at
`/private/tmp/claude-501/-Users-ember-dev-breadstuffs/b41a7fca-…/scratchpad/VCVio` from the 07-16
research session — **that path is session-scratchpad and will be garbage-collected; re-clone
before any adoption work.** What was verified by reading it:

- **The monad + query bounds:** `OracleComp spec α` (free monad over an `OracleSpec`), with
  `IsQueryBound` / `IsQueryBoundP` (`VCVio/OracleComp/QueryTracking/QueryBound.lean:54,231`) — a
  predicate-targeted bound "at most `n` queries to the oracles selected by `p`, along every path."
  Our `RomOracle.OracleComp`/`QueryBounded` is the same idea, ~2× looser in its bounds.
- **Binding as extraction-as-data:** `VCVio/CryptoFoundations/MerkleTree/Inductive/Binding.lean` —
  `findCollision` is a
  *computable function* that walks two Merkle branches and returns the hash collision as a tuple;
  `getPutativeRootWithHash_binding` proves it returns `some` whenever two distinct leaf values
  verify against the same root. **No adversary, no probability, no cost model in the statement —
  nothing to falsify.** This is the shape [[project-fri-soundness-reality]] says to steal.
- **Straight-line FS extraction, end to end:** `Fischlin/KnowledgeSoundness.lean:2522`:

  ```lean
  theorem knowledgeSoundness
      (hss : σ.SpeciallySound) (hur : σ.UniqueResponses)
      (adv : KnowledgeSoundnessAdv ρ b M) (Q : ℕ) (hρ : 0 < ρ)
      (hQ : ∀ x msg, ROQueryBound ρ b M (adv.run x msg) Q)
      (x : Stmt) (msg : M) :
      Pr[= true | knowledgeSoundnessExp σ hr ρ b S M adv.run x msg]
        ≤ knowledgeSoundnessError Q ρ b S
  ```

  — a cheating prover as an `OracleComp`, a structural query bound as hypothesis, an *online*
  (no-rewinding) extractor that reads the prover's oracle queries, and
  `Pr[verifier accepts ∧ extractor fails] ≤ ε(Q)` with a closed-form ε. There is also a mechanized
  forking lemma (`ReplayFork.lean`, `SeededFork.lean`) with a `QueryLog` erasure interface — but
  FRI does not need forking (next subsection).

### 4.2 The oracle model for OUR `verifyAlgo`

The single most fortunate fact in this whole design: **`verifyAlgo` is already parametric in
`perm : List F → List F`.** The Fiat–Shamir transcript (`deriveTranscript`), the challenger
squeezes, the PoW check — every use of the permutation flows through that one parameter. So the
ROM re-basing is a *re-interpretation*, not a rewrite:

- **The spec does not change.** Define (new file, additive)
  `verifyAlgoO : BatchProofData F → WrapPublics F → OracleComp permSpec Bool` by threading each
  `perm` application through an oracle query, and prove the **faithfulness lemma**
  `run verifyAlgoO (fun q => perm q) = verifyAlgo perm …` — running the oracle version against a
  deterministic oracle recovers the deployed Bool, definitionally or by structural induction. The
  deployed verifier stays the authority; the oracle version is its conservative image.
- **The oracle is the permutation, sampled.** `permSpec` has one index; domain and range are the
  sponge state `List F` (width-pinned). The model heuristic "Poseidon2 is a random function on
  sponge states" is the ONE permanent carrier this document does not propose to discharge — it is
  where every deployed SNARK on earth lives, and it is honest to carry it *named* (a random-
  *permutation* refinement is available later at the cost of a switching lemma, another
  birthday-genre theorem).
- **The adversary produces the proof.** `A : OracleComp permSpec (BatchPublicInputs × BatchProof)`
  with `QueryBounded A Q` (our `RomOracle` vocabulary; `IsQueryBoundP` if on VCVio). No strategy
  type, no rounds, no interaction machinery is needed beyond this — FS made the protocol
  non-interactive, so "the adversary" is just "a query-bounded proof-finder." This is what fixes
  the "no adversary, no grinding model" finding with the *smallest possible object*.

### 4.3 The target statement

```lean
/-- The FRI-LDT extraction floor, extraction-shaped: a Q-query adversary produces an
accepting proof whose extraction bundle FAILS with probability at most εFri. -/
theorem friLdtExtractV3_rom
    (A : OracleComp permSpec (BatchPublicInputs × BatchProof))
    (hQ : QueryBounded A Q) :
    Pr[ fun ((pi, π), permOracle) =>
          verifyAlgoO … (view pi π).1 (view pi π).2 = true
          ∧ ¬ ExtractBundle pi π ]   -- the TWELVE conjuncts of FriLdtExtractV3's body,
                                     -- verbatim, as a definition
      ≤ εFri Q params
```

where `ExtractBundle` is literally the existential body of today's `FriLdtExtractV3` — the
statement is preserved conjunct-for-conjunct; only the quantification changes from
"∀ accepting proof, deterministically" to "∀ Q-query adversary, except with probability ε." The
extractor is **straight-line**: it reads the committed word out of the adversary's Merkle-path
oracle queries (the BCS-style query-log extractor — VCVio's `QueryLog.getQueryValue?` /
`LoggingOracle` is exactly this machinery, and our `RomOracle` has the same lazy-sampling
counting core in `RomCounting.condProb_fresh_eq`). No rewinding, no forking — hash-based IOPs are
the good case.

And the error term is a SUM whose addends are the ledger's columns finally composed:

```
εFri Q params =
    εMerkle    -- birthday: Q-query collision in the sponge          [PROVABLE — §5 stage 3]
  + εFS        -- exceptional ζ or Λ ever derived: (Q+1)·deg/|F|     [PROVABLE — §5 stage 2]
  + εGrind     -- PoW mask hit accounting: folds into query budget   [PROVABLE — §5 stage 2]
  + εQuery     -- far word survives all numQueries spot checks       [stage 4: proven per-fold
                  density (ledger) + CARRIED correlated-agreement step]
```

### 4.4 What becomes provable, what stays a named carrier

**Becomes a theorem (no new mathematics, assembly of in-tree + VCVio-shaped pieces):**

- The FS non-exceptionality conjuncts. Today they are two *assumed* conjuncts inside the bundle;
  in the ROM they are theorems: the derived ζ and Λ are fresh oracle outputs after observation of
  the commitments they must be non-exceptional *for*, so
  `Pr[derived Λ ∈ exceptionalSet] ≤ (Q+1) · |exceptionalSet| / |F|`, and the cardinality bound is
  already proven (`batchResidual_exceptionalSet_card_lt`; `ood_hnonexc_escape_prob_le` —
  `AlgoStarkSoundTransferV3.lean` §4 already quotes both as "the honest bounded-advantage form").
  The `(Q+1)` factor is the grinding accounting, free of charge.
- The grinding PoW term (§3 above) — `deriveQueryPow`'s masked squeeze as a per-query event.
- Merkle binding. Steal `findCollision`'s shape for the deployed `merkleRecomputeZ`
  (`OodCommitmentBinding`): two openings to one root yield a collision *as data*, then
  `birthday_cond` (`RomQueryFloor` §5, already proven: `(Q·|S| + Q² + 1)/|R|`) bounds the
  probability the adversary ever *has* a collision. In the ROM leg, `Poseidon2SpongeCR` converts
  from an assumed Prop into a theorem-except-ε; the concrete-Poseidon2 instantiation remains the
  §4.2 permanent carrier.
- The transcript/query-index binding and the structural teeth — already theorems through the real
  `verifyAlgo` (`verifyAlgo_concrete_rejects_wrong_query_count` at `FriVerifier.lean:719`,
  `verifyAlgo_full_rejects_tampered_quotient` at `:900`); they lift through the faithfulness
  lemma unchanged.
- The whole-tree fold — already done (`recursive_sound_from_nodes`); the per-node ε union-bounds
  over the tree: a verifying root mis-extracts somewhere with probability ≤ (#nodes)·εFri. The
  recursion-node floor `AggAirSound.FriExtract` gets the identical re-basing (the child verifier
  inside a node IS `verifyAlgo` at the recursion VK), so ONE probabilistic floor serves both §1.1
  and §1.2 — and §1.4's placeholder retires into it.

**Stays a named carrier — but changes character:**

- **The core proximity/extraction step** (`εQuery`'s interior): "a committed word that is δ-far
  from the code survives one spot-check round with probability ≤ (1−δ) + per-fold-escape" and its
  composition across fold layers into "all-queries-pass ⟹ the query-log word is δ-close, and the
  close codeword's decoding is the `VmTrace t`." The per-fold density input is PROVEN
  (`ledger_perFold_soundness`, `hΦ` discharged at every shipped config); the *correlated
  agreement* step that turns per-fold densities into batched-word extraction is BCIKS20 §8 —
  carried, initially, as a named probabilistic hypothesis **about words and densities** (its
  honest home), not about adversaries. Radius honesty from [[project-fri-soundness-reality]]
  binds here: state it at the PROVEN radius (the unique-decoding/`M = 1`-discharged regime — the
  57-bit-honest column), NOT at Johnson 87.5% where `M = 1` is provably false
  (`deployed_M1_false_at_johnson`). A bigger ε that is *attached to an adversary* is worth more
  than a smaller one that is attached to nothing.
- **The ROM instantiation** ("Poseidon2's sponge behaves as a random function") — permanent,
  named, industry-standard, never discharged. This is the honest terminal floor.
- The gnark refinement obligation (`GnarkRefines`, `FriVerifier.lean:999`) — orthogonal
  lane, unchanged by this design.

The character change is the point: today's carrier is a deterministic claim nobody can prove or
refute (§2); the residual carrier after re-basing is the *statement of a published theorem*, with
an adversary type, a query budget, and a concrete ε — auditable, citable, and falsifiable at each
conjunct. That is the difference between a name and a floor
([[feedback-no-named-carrier-laundering]]).

### 4.5 Our `RomOracle` vs. vendoring VCVio

Two viable substrates:

- **(a) Our `Dregg2.Crypto.RomOracle`** — already in-tree, `#assert_axioms`-clean, with the
  counting core (`RomCounting`), `QueryBounded`, `eval_congr_of_agree_on_queried` (the
  determination lemma), and `birthday_cond` proven. Bounds ~2× looser than VCVio's
  (`C(n,2)/|Range|` vs. our cruder count); no PMF/ENNReal integration; no `QueryLog` erasure
  interface (extraction-from-the-log needs one — a modest addition).
- **(b) Vendor VCVio** — tighter bounds, real `PMF`/`ENNReal` probability, `LoggingOracle` +
  `QueryLog`, the Fischlin/forking precedents to imitate, and the field-standard vocabulary.
  Cost: a new dependency (with its own `sorry`s in unrelated corners —
  `docs/reference/ARKLIB-KZG-VACUITY.md:188` notes them, none load-bearing for us), toolchain
  pinning, and the memory's standing note that adopting it is an **ember-call**.

**Recommendation: start on (a), keep the statement VCVio-shaped.** Stage 1–2 below need nothing
VCVio has that `RomOracle` lacks; the statement of `friLdtExtractV3_rom` should use the neutral
vocabulary (an adversary IS an oracle computation; a bound IS a per-path query count) so that a
later port — or a rebuild of the escape ON VCVio, which the memory already flags as desirable for
tightness — is mechanical. The vendoring decision then arrives with evidence (how much of stage
3–4 wants `QueryLog`/PMF) instead of in advance of it.

---

## 5. The staged plan

Ordered so each stage is independently landable, smallest first, and no stage edits deployed
specs or existing proofs (additive files only, per the tree's standing discipline).

**Stage 0 — freeze the target (this document).** The target theorem statement is §4.3 verbatim;
the `ExtractBundle` definition must be the TWELVE conjuncts copied, not paraphrased. Adversarial
audit gate: diff `ExtractBundle` against `FriLdtExtractV3`'s body token-for-token.

**Stage 1 — the faithfulness bridge (the smallest first theorem).**
Define `verifyAlgoO` over `RomOracle.OracleComp` and prove

```lean
theorem verifyAlgoO_run_eq (perm) :
    OracleComp.eval (fun q => perm q) (verifyAlgoO … proof pub)
      = verifyAlgo perm RATE toNat params vk checks initState logN proof pub
```

plus `QueryBounded (verifyAlgoO … proof pub) (permCallCount params proof)` with `permCallCount`
an explicit arithmetic function of the proof shape (deriveTranscript's observe/squeeze count +
per-query Merkle recomputes). Purely structural — no probability, no crypto — and everything
downstream needs it. It is also the stage that proves the re-basing is *conservative*: the
deployed verifier is untouched and recoverable.

**Stage 2 — the FS terms become theorems (the smallest crypto payoff).**
Prove `Pr[derived Λ exceptional ∨ derived ζ exceptional ∨ PoW freebie] ≤ (Q+1)·deg/|F| + Q/2^pow`
by combining `RomCounting.condProb_fresh_eq` (what the adversary has not queried, it does not
know — the derived challenge is fresh relative to everything it must be non-exceptional for) with
the in-tree cardinality bounds (`batchResidual_exceptionalSet_card_lt`,
`ood_hnonexc_escape_prob_le`). Deliverable: a variant bundle `ExtractBundleSansFS` (ten
conjuncts) and the theorem that the two FS conjuncts hold except-with-ε. Two of twelve conjuncts
move from assumed to proven, and the `(Q+1)` grinding accounting exists for the first time.

**Stage 3 — Merkle binding as extraction-as-data + birthday.**
Port the `findCollision` shape to `merkleRecomputeZ`: a computable
`findCollisionZ : … → Option (List ℤ × List ℤ)` with soundness ("if `some`, a genuine sponge
collision") and completeness ("two distinct bound openings at one root ⟹ `some`"); then
`birthday_cond` bounds the probability the query log contains any collision. Deliverable: the two
Merkle-recompute conjuncts hold except-with-ε in the ROM, and `Poseidon2SpongeCR`'s *use* in this
leg is derived rather than assumed (the class stays for the concrete instantiation).

**Stage 4 — the query-phase composition (the hard stage, and the honest one).**
From: per-fold good-challenge density (`ledger_perFold_soundness` + the discharged `hΦ`), the
qidx-transcript binding (stage-1 lift of the `:719`/`:900` teeth), and a NAMED correlated-
agreement carrier stated over words at the proven radius — prove
`Pr[committed word far ∧ all numQueries checks pass] ≤ εQuery`. This is where `johnsonBits` stops
being `by norm_num` bookkeeping: the exponent arrives as a *theorem about an adversary's success*,
at whatever radius the carried agreement step honestly supports. Scope control: the carrier here
is a probabilistic statement about codes and densities (BCIKS20's own object), NOT about
adversaries or hashes — strictly narrower than what `FriLdtExtractV3` carries today.

**Stage 5 — assembly and the apex re-read.**
`friLdtExtractV3_rom` (§4.3) from stages 2–4; the same statement instantiated at the recursion VK
discharges a probabilistic `FriExtract`; a union bound over `PTree` nodes gives the probabilistic
`NodeCarrier`; `GroundedApex`'s conclusions re-read as "…except with probability
≤ (#nodes)·εFri(Q, params) for any Q-query adversary." Consolidate the §1.4 placeholder onto the
one floor. Only at this stage do the ledger's columns, the PoW bits, and the word "security"
compose into a sentence that means something: *the bits measure the query budget at which εFri
reaches 1/2.*

---

## 6. Falsifiers, per stage

Stated in advance so failure is cheap and early ([[feedback-prove-the-floor-false]]).

- **Global / stage 1:** if `verifyAlgoO_run_eq` cannot be proven without CHANGING `verifyAlgo` —
  i.e., if some use of `perm` cannot thread through a query tree (a higher-order use, an
  unbounded-call site) — the conservative-re-basing premise is wrong and the design must be
  rethought. (Reading `deriveTranscript`/`deriveFri`/`drawQueries`/`deriveQueryPow`: every call
  is first-order and proof-shape-bounded; this falsifier is expected to pass, which is why
  stage 1 is first.)
- **Stage 2:** if the derived Λ/ζ are NOT fresh relative to the objects their exceptional sets
  depend on — i.e., if the transcript order lets the adversary see the challenge before
  committing to what it must be non-exceptional for — the freshness lemma fails. That would be a
  real transcript-ordering bug in the deployed FS (exactly the class `deriveTranscript`'s header
  says it exists to expose), and finding it would be a *win*, not a failure of the approach.
- **Stage 3:** if `findCollisionZ` completeness fails — two distinct bound openings at one root
  with NO collision along the paths — then `merkleRecomputeZ`'s path structure differs from a
  Merkle tree's in a way `OodCommitmentBinding` glossed, and the current `Poseidon2SpongeCR`
  usage is itself suspect. Again: the falsifier firing is a discovery about deployed code.
- **Stage 4:** two. (i) If the per-fold density columns cannot compose into a per-query bound
  without assuming `M > 1` correlated agreement at Johnson radius — where `M = 1` is provably
  false (`deployed_M1_false_at_johnson`) — then stage 4 must stand at the unique-decoding radius
  and εFri is the 57-bit-honest figure. That is NOT approach failure; it is the approach
  *refusing to launder*. The approach FAILS only if even the proven-radius columns cannot attach
  to the adversary's acceptance event — e.g., if the qidx binding is too weak to force the
  adversary's opened positions to be the transcript's. (ii) If anyone attempts to read the
  ~112.6-bit number out of this pipeline at deployed configs, the pipeline is being misused; the
  design mandates the proven-radius instantiation.
- **Stage 5:** the union bound requires per-node εs over a SHARED oracle; if node events are not
  monotone in the query log (they are — acceptance and extraction-failure are both events over
  the adversary's single run), independence-shaped errors would appear. Falsifier: a two-node
  toy where the composed bound is violated by a coupled adversary. Build the toy FIRST, as the
  stage-5 canary.
- **Meta-falsifier for the whole design:** exhibit an accepting-proof-finding strategy whose
  success at the deployed parameters is *not* a function of its query count — i.e., a way to
  beat `verifyAlgo` that does useful work against Poseidon2 *between* queries (algebraic
  structure exploitation). That would show query-counting abstracts away a real resource, and
  is precisely the standard-model-vs-ROM gap: it would be a publishable attack on
  Poseidon2-as-FS, and the named §4.2 carrier is where the design already stores that risk,
  visibly.

---

## 7. What the bits mean afterward

Today (per [[project-fri-soundness-reality]]): the deployed posture is 57 calculator bits — a
Finset density ratio with no adversary, computed by a ledger that never touches the apex. After
stage 5: `εFri(Q, params)` is a proven bound on ANY Q-query adversary's probability of producing
an accepting proof that the straight-line extractor cannot open into the deployed `VmTrace`, with
one named word-level carrier (correlated agreement at the proven radius) and one named permanent
model carrier (Poseidon2-as-random-function). "b bits of security" then has a definition this
tree can defend: `εFri(2^b, params) ≤ 1/2`. The ledger's two-column law
(`FriLedgerSound.lean` §"THE FINDINGS": columns reported separately, never multiplied into a
headline) survives intact — the columns become the *inputs* to εFri, and the composition happens
inside a theorem instead of inside prose.

The through-line, for orientation: this is the same move the tree has already executed four
times — `hood` (assumed → derived, `AlgoStarkSoundTransferV3` §3), `binding_sound` (assumed →
`BindingAirSound`), `recursive_sound`'s tree fold (assumed → `RecursiveSoundFromNodes`),
`WitnessDecodes` (assumed → `WitnessRealizing`). Each time, the repair was not to prove the
assumption as stated but to RESTATE it over the right objects and then watch most of it become
derivable. The per-node FRI floor is the last one, and the right objects are query-counting
oracle adversaries — the one resource model with a proven escape and a mechanized precedent for
exactly this theorem shape.
