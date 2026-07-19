# HANDOFF — adversarial implementation of fhEgg + The Dark Bazaar

*For an implementation swarm: ember drives, agents inspect and change the real tree at
`/Users/ember/dev/breadstuffs`. Verify claims against files, theorems, tests, and captured artifacts; do not
accept this doc's summaries. The house style is honest grading (PROVED / WORKING / PROTOTYPE /
FRONTIER-unbuilt), but the purpose is not to stop at a verdict: turn every tractable objection into code,
proofs, protocol teeth, or an exact residual.*

---

## 0. YOUR MISSION (read this first, adopt this stance)

You are an **adversarial builder** — a skeptical cryptographer + optimization theorist + systems engineer.
Pressure-test every claim, then implement the strongest honest next layer. Find fatal flaws before they reach
the product; when a flaw is tractable, repair it in the same campaign and add both-polarity teeth. Where a
claim is sound, say why. Where it overreaches, name the precise theorem, protocol boundary, or missing wire:
**BLOCKED** means a real impossibility; **OPEN** means a concrete construction or proof remains; **BUILT**
means the artifact exists and its narrow gate is green.

Do not import conventional team-size/calendar estimates into this project. Dregg itself is evidence that
the local distribution is swarm-scale (the full project was a six-week build), and independent lanes are
expected to move concurrently. Unless ember explicitly asks for scheduling, report **technical dependency
edges and executable exit gates**, not weeks, quarters, staffing, dollar cost, or a sequential roadmap.

Bias check for yourself: this repo has a documented habit of honest self-audit and a session that just found
9 forgery-class bugs with exactly your stance. Do NOT soften because the docs are candid — candor is not
correctness. Verify from the artifact.

---

## 1. WHAT TO READ (and verify, in order)

- Vision + the unique claim: `docs/deos/THE-DARK-BAZAAR.md`, `docs/deos/DREGGFI-VISION.md`.
- The honest current state you must PRESSURE-TEST: `docs/deos/FHEGG-MATURITY-ROADMAP.md` (the 5 pillars +
  grades), `docs/deos/FHEGG-SDK-READINESS.md` (the shippability audit).
- The math: `docs/deos/FHEGG-MATHEMATICAL-BRIEF.md` (§0 notation, §5 the convex engine, §7 the six open
  questions), `docs/deos/FHEGG-PRODUCT-ORDER-FRONTIER.md` (the product surface incl. the exotic list).
- The ARTIFACTS behind the grades (verify these compile/prove what is claimed — do not trust the prose):
  - Cert-F (verify-not-find): `metatheory/Market/CertF.lean` (`certifies_epsilon_optimal`, `weak_duality`),
    `metatheory/Market/CertFDescriptor.lean` (generic emit-soundness), `circuit-prove/src/cert_f_air.rs`.
  - The BFV crypto: `fhegg-fhe/src/bfv_lean.rs` (fold), `bfv_mul.rs` (ct×ct multiply, fhe.rs-oracle-anchored),
    `bfv_gpu.rs` (GPU fold), `convex_engine.rs` (T>1), `threshold.rs` (no-viewer).
  - The Lean noise/security theory: `metatheory/Bfv/{Noise,Mul,Smudging}.lean`.
  - The prototype interfaces + review findings: `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md`, and search
    `TESTQALOG.md` for `proto/` (impl) and the opus review verdicts (3 named residuals).
- The trust/tally spine (why grading is load-bearing): the `GRADE` table in `DREGGFI-VISION.md` §1.

---

## 2. THE HARD QUESTIONS (organized by fatal-flaw risk — hammer these)

### A. The single biggest risk: does verify-not-find survive the jump from CONVEX to COMBINATORIAL?
The Dark Bazaar's flagship is a **blind combinatorial (bundle) auction with a welfare-optimality proof.**
Cert-F certifies **convex** optima because LP/QP have **strong duality** — a small primal-dual gap *is* the
certificate (`certifies_epsilon_optimal`). **Integer/combinatorial programs have an integrality gap; strong
duality FAILS.** So:
- Is a *cheap, valuation-hiding* certificate of INTEGER-optimal allocation even possible, or is this
  BLOCKED? (A branch-and-bound optimality proof is worst-case exponential and would leak the search.)
- The escape hatch to assess: **which combinatorial structures are LP-integral** (assignment, transportation,
  matroid intersection, unit-demand / gross-substitutes valuations, and TTC — which dregg ALREADY uses in
  `settleRing`, `intent/src/solver.rs`)? For those, the LP relaxation IS integral, so Cert-F applies
  unchanged. **Is the achievable Dark Bazaar exactly "combinatorial-but-gross-substitutes," and is general
  complementarity (bundle complementarities, AON across heterogeneous items) fundamentally out?** Give the
  precise boundary of what is certifiable-private-combinatorial. This is the crux; spend your best effort here.

### B. Performance: is FHE clearing fast enough for a GAME, ever?
Measured today: minutes at toy sizes (N≈32-512), CPU. The plan bets on a **GPU-RESIDENT** pipeline
(`FHEGG-MATURITY-ROADMAP.md` §1) + the histogram winning ~11× at N=1M (measured, `bin/gpu_saturate.rs`).
- What is a realistic end-to-end latency for a Tier-0 sealed clearing at game scale (N≈10²-10⁴ bids), on the
  resident pipeline, honestly? Is "batch clears once per Season/epoch" the only viable cadence, or can it be
  interactive? Does the cadence kill the game design or fit it?
- Is the residency thesis sound (upload once, fold/cross/multiply on-device, one readback), or does the
  argmax/crossing / the multiply's NTT / the threshold decrypt force round-trips that break residency?

### C. The no-viewer threshold: is the trust + liveness model real in a GAME?
`threshold.rs` (n-of-n collective decrypt) + `metatheory/Bfv/Smudging.lean` (a PROVEN smudging bound — verify
it is not vacuous; the opus reviewer called it tight, check yourself). But:
- **n-of-n** means all parties must be honest for privacy AND all must be online to decrypt (liveness). Who
  are the `n` in a game — players? an operator federation? — and does either make the trust story real or
  circular? Is **t-of-n** (which fhe.rs mbfv does NOT provide) actually required, and does that reintroduce a
  dealer?
- The opus review found the Rust no-viewer *tooth* is vacuous (`ThresholdNoViewerToothVacuous`) — the
  *proof* is in Lean, the *test* does not exercise it. Does the Lean theorem actually cover the deployed
  construction, or is there a gap between `Smudging.lean`'s model and `threshold.rs`'s code?

### D. Noise budget across the FULL pipeline.
Fold (add, noise doubles) → convex engine T iterations (public-scalar-mul, noise ×|c| per step) → ct×ct
multiply (noise SQUARES) → threshold decrypt (smudge adds). `Bfv/{Noise,Mul,Smudging}.lean` bound the pieces.
- Does the composed budget survive a realistic Dark-Bazaar computation without **bootstrapping** (which
  fhe.rs BFV does not implement and which would dominate cost)? Where does the budget actually run out, and
  which halls (dark AMM = multiply-heavy; combinatorial = deep) are budget-infeasible without bootstrap?
- `convex_engine`'s noise guard is flagged `ConvexNoiseGuardUntested` (window ceiling always preempts the
  noise ceiling). Is the noise bound even the binding constraint anywhere real, or is the whole guard theatre?

### E. The dependency + soundness substrate.
- `fhe.rs 0.1.1` is stalled research-grade with an upstream smudging `TODO` (`FheggBfvDependencyResidual`).
  Is building the no-viewer keystone on it defensible even short-term, or does it taint every privacy claim
  until the Lean-first BFV replaces it? For Lean-first BFV, identify the exact remaining primitives and
  proof/code gates after the existing addition, multiplication-oracle, noise, key-custody, and threshold work;
  then build independent pieces in parallel rather than turning their count into a calendar estimate.
- The STARK floor: Cert-F proofs inherit an undischarged FRI/STARK soundness floor.  The compatibility
  `prove_cert_f` entry point remains non-hiding, while `prove_cert_f_zk` now proves the same registered
  descriptor through `HidingFriPcs` and has a real mint/verify/tamper tooth.  Verify the remaining formal
  simulator floor, and do not confuse Tier-1 solver-sees witness hiding with Tier-0 no-viewer attestation.

### F. Economic / mechanism soundness (the game as an adversary).
- Does cryptographic hiding create NEW attack surfaces? (E.g., can a player submit a malformed encrypted bid
  that the blind clearer cannot reject without decrypting? Griefing via unsatisfiable bundles? Sybil across
  hidden positions? Is input-validity provable in-circuit without leaking?)
- Is the combinatorial exchange incentive-compatible (does hiding break VCG-style truthfulness, or is
  uniform-price the only IC mechanism that stays cheap)?

---

## 3. HOW EMBER DRIVES THIS (interactive swarm protocol)
- Ember may point at one component or ask for the whole frontier. Verify against the artifact, state the exact
  obstruction, and keep working through the strongest safe implementation step.
- When you claim BLOCKED, give the theorem/impossibility. When OPEN, give the concrete missing relation or
  protocol wire and attack it. When BUILT, cite the changed artifact and its narrow green gate.
- Swarm independent hard pieces concurrently: hiding proof path, attested clearing/source binding, no-viewer
  transport and preprocessing, Dark Bazaar market integration, Lean refinement, and adversarial teeth do not
  need to wait in a single-file queue.
- Push back on ember too. If the crawl slice (`dreggnet-market` → Tier-0 clearing → hiding Cert-F → exact
  settlement receipt) has a hidden blocker, expose it precisely; do not replace it with a smaller claim under
  the same name.

## 4. THE DELIVERABLE (what to converge on)
1. A per-component state (BLOCKED / OPEN / BUILT) with evidence, for the 5 pillars + 4 halls.
2. The **precise boundary** of the achievable Dark Bazaar — specifically the combinatorial-certificate line
   (question A), because that determines whether the flagship is real or must be scoped to gross-substitutes.
3. The **fatal-flaw list**, if any — the things that, unaddressed, make the vision hand-waving.
4. **Landed implementation artifacts** for every tractable frontier: code/proofs, positive and negative
   teeth, exact security scope, and narrow verification output. Parallel dependency edges may be recorded;
   calendar/team/cost projections are not a default deliverable.
5. The one honest sentence: **what works end-to-end now, and what exact cryptographic statement is still
   missing?**
