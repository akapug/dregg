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

---

## 5. CURRENT IMPLEMENTATION DELTA — atomic authenticated asset clearing (2026-07-19)

**BUILT, process-local:** `DarkBazaarOffering::settle_fhegg_asset_atomic` now composes the exact
source-bound fhEgg clear with the original provenance-carrying Descent asset and its `$DREGG`
countervalue. It performs every fallible source/session/BFV/result/attestation/replay/owner/balance/escrow/
provenance check against detached state, commits `close_commit + every reveal_bid + resolve` as one real
executor multi-action turn, and only then installs the already-executed `TradeWorld` plus staged replay
guard. A host hook runs after detached validation and before live mutation for durable-journal reservation
or deterministic fault injection.

The returned `AtomicFheggAssetSettlementReceipt` binds the fhEgg claim digest, exact live source-board
commitment, source-certified `AssetId`, seller, winner, price, before/after trade-world audit images, and
the executor settlement-turn receipt hash. Its audit digest is publicly recomputable; mutating a bound
field makes `audit_digest_verifies()` fail.

Implementation surfaces:

- `dreggnet-market/src/fhegg_atomic_asset.rs` — composed transaction, hook, receipt, audit binding, and
  full rollback/success matrix.
- `dreggnet-trade/src/lib.rs` — detached real-sale preparation and canonical asset+wallet state digest.
- `dreggnet-asset/src/lib.rs` — independent executor-state reconstruction and canonical ownership/
  lineage/spent/revocation digest.
- `fhegg-fhe/src/attestation.rs` — cloneable in-memory replay image for staged consumption.
- `dreggnet-market/tests/descent_fhegg_settlement.rs` — the real Descent loot + 3-of-4 custody +
  three-party clearing scenario now calls the atomic API instead of the former clear-then-cross pair.

Adversarial gate (ordinary local test profile, 3.76s):

```text
cargo nextest run -p dreggnet-market --features fhegg-settlement \
  -E 'test(atomic_fhegg_asset_cross_rolls_back_every_refusal_and_commits_every_leg_once)'
PASS: 1 passed, 16 skipped
```

That test drives wrong certified asset, insufficient `$DREGG`, wrong live owner, substituted source digest,
an injected refusal after all detached validation, and replay. Each refusal preserves the market phase,
market receipt count, clearing state, complete economic `TradeWorld` digest, and replay usability. The
positive case moves the exact asset, conserves the exact price, extends rather than restarts provenance,
lands one four-action market receipt, consumes replay once, and detects receipt tampering. The heavyweight
Descent integration target also compiles after its cutover; this sprint deliberately did not rerun its slow
cryptographic setup because the narrow composed behavior has the focused executable gate above and the
underlying cryptographic path already has its own captured heavy result.

**BUILT, durable one-host recovery:** `settle_fhegg_asset_atomic_durable` now binds transaction/replay ids,
the complete prepare audit, exact market turn and receipt, and before/after economic images in a strict
bounded `Prepared -> MarketApplied -> WorldApplied -> Committed` journal. Recovery classifies only exact
not-applied/fully-applied images and advances missing phases idempotently. `FileAtomicSettlementJournal`
persists the record map and global replay reservations in one canonical snapshot using an OS advisory lock,
file fsync, atomic rename, and directory fsync. Five injected crash boundaries drop and reopen a fresh file
journal; recovery lands exactly one market receipt, asset transfer, seller payment, and replay consumption,
while a second transaction id, corrupted bytes, and a third live state fail closed. The focused default
gate passes 6/6 in 19.313s; the file-corruption tooth also reruns alone 1/1 in 0.061s.

**Exact residual:** this remains one-host recovery under exclusive ownership. The host must durably restore
the market, `TradeWorld`, and replay images that the journal classifies; the crash tooth preserves those
images rather than killing/restarting a complete deployment. Advisory locking covers cooperating writers,
the public checksum is not rollback-resistant storage, and detached asset reconstruction does not copy old
executor receipt-chain histories (the new transfer still produces fresh real receipts). Independently
committing federation and asset ledgers still require a shared cross-ledger executor transaction or a
consensus-backed distributed commit protocol. Do not describe this API as that distributed hyperedge.

---

## 6. CURRENT IMPLEMENTATION DELTA — exact private AMM relation and owner-side lifecycle

**BUILT relation and prover:** `metatheory/Market/DarkAmmPrivateDescriptor.lean` emits the exact
private constant-product relation with public ABI `(session, rule, k, oldRoot[8], newRoot[8])` and hidden
`(x, y, dx, dy, oldBlind[8], newBlind[8])`. The witness is range-constrained, both amounts are nonzero,
`x*y = k` and `(x+dx)*(y-dy) = k`, and two arity-16 Poseidon2 lookups bind the old and new hidden states.
`circuit-prove/src/dark_amm_private.rs` consumes the checked-in emitted descriptor and supplies the
`HidingFriPcs` prover/verifier. The current Lean source has 19 `#assert_all_clean` keystones; the full
Market build completed successfully after that source revision. The focused release prover gate ran the
descriptor/boundary and hiding/tamper teeth 2/2.

**IMPLEMENTED owner-side lifecycle:** `dreggnet-market/src/bin/dark-amm-tool.rs` now has owner-only
`private-init`, `public-private`/`public-id-private`, `private-swap`, cursor advancement, independent
same-opening endorsement, and v3 assembly commands. A private swap publishes an atomic bundle containing
the encrypted request, public statement, next private state, and an owner-only authority artifact; the
integration scenario in `dreggnet-market/tests/dark_amm_private_tool.rs` chains `(100,900) -> (150,600) ->
(300,300)` and contains wrong-session, wrong-invariant, stale-root, checksum, permissions, tamper, and
no-overwrite teeth. Its release lifecycle gate passed 1/1. The separate two-issuer CLI lifecycle in
`dark_amm_same_opening_tool.rs` also passed 1/1 in 10.31s after the FHAS003 cutover and ends by submitting the assembled v3 body to
the real hosted operation.

**Boundary:** HidingFri hides the witness from proof consumers, not from the owner/prover. The host path is
still BFV and, absent §7's authority receipt, the proof and ciphertext can name different amounts. Private
state checksums detect corruption but are not rollback-resistant storage; the authority bundle deliberately
contains sensitive opening material and depends on owner-only filesystem custody.

## 7. CURRENT IMPLEMENTATION DELTA — Tier-1 BFV/HidingFri exact-opening receipt

**BUILT protocol surface:** `fhegg-fhe/src/amm_same_opening.rs` defines a canonical, bounded Tier-1
receipt. Each Ed25519 issuer receives the full private AMM witness and deterministic BFV encryption seeds,
re-encrypts `dx` and `dy` under the exact collective public key, reconstructs the exact Lean-authored
HidingFri statement, verifies the hiding proof, and signs one claim. The claim pins the hosted session and
sequence, proof session/rule/`k`/roots, complete BFV public identity, both ciphertext digests, statement,
proof and descriptor digests, both public BFV wrap-safety caps, ordered issuer roster/verifier/threshold,
privacy tier, full canonical BFV parameter digest, and replay domain. `FHASO003` refuses a zero cap, a cap at/above the plaintext modulus, and a
cap below the exact opened amount, closing the underdeclared-bound attack against `MulEngine`'s no-wrap
reasoning. Old `FHAS{O,E,R}001` and `FHAS{O,E,R}002` artifacts fail closed.
Receipt decoding requires canonical signer order and exact framing; verification reconstructs the claim
from independently supplied public objects, checks the quorum and proof, and consumes the exact hosted
replay slot.

The post-migration release codec gate ran 2/2 in 0.723s: round-trip/verification/restart replay plus
issuer- and consumer-side cross-representation, version, and bound-substitution refusals.

**Exact trust boundary:** this is issuer-visible authenticated same-opening, not lattice zero knowledge
against the issuers and not no-viewer witness production. A malicious threshold can sign a false claim;
the receipt proves which configured quorum endorsed it, while the reference issuer supplies the semantic
check. The deterministic encryption codec is version-pinned to fhe.rs 0.1.1 and `rand` 0.9 `StdRng`, seed
entropy is caller-owned, and durable replay still needs a rollback-resistant transactional anchor.

## 8. CURRENT IMPLEMENTATION DELTA — strict hosted v3 AMM boundary

**BUILT, CURRENT GATE GREEN:** `dreggnet-market/src/dark_amm_game.rs` defines strict magic
`DBAMv003` and operation `dark-bazaar.private-amm-swap.proved.same-opening.v3`. A
`*_same_opening_required` table exposes only v3, strictly decodes and re-encodes the nested request,
reconstructs the exact session/key/sequence/statement/ciphertext/proof/issuer context, verifies §7's receipt
against a staged replay image, evaluates the encrypted candidate, and installs pool, root, sequence, cap,
replay, receipt, and canonical request only on the accepting branch. Resume replays the canonical v3 body
through the same verifier.

The post-`FHASO003` release gate passed 1/1 in 12.25s. It includes both nested bound-mutation refusals,
exact v1/v2 downgrade refusal, signature/context/root/key/sequence/roster tamper, one successful transition,
duplicate refusal, process reconstruction, and a post-restart replay attempt; the durable operation log
remains exactly one canonical accepted entry throughout. The older captured two-entry failure is repaired
and must not be copied forward as current state.

**Boundary:** the deployed host construction is explicitly BFV `n=1/opening-threshold=1`; it retains the
secret and relinearization key, decrypts the candidate product, and sees rejected products. Issuer-visible
Tier-1 exact opening does not turn this into threshold/no-viewer custody. The v3 authority now binds the
complete canonical BFV parameters (including error variance) and both
caps and the hiding relation proves the actual ten-bit amounts/no-overdraw, but that guarantee still trusts
the issuer quorum with the witness. The cross-ledger economic commit is a different layer: use §5 for the implemented
one-host atomic asset settlement and its distributed-commit residual.

## 9. CURRENT IMPLEMENTATION DELTA — Lean model of the v3 host law

**PROVED semantic model, executable refinement still OPEN:** `metatheory/Market/DarkAmmBoundReceipt.lean`
models the strict v3 host step. Its `Binds` record enumerates version, hosted and proof sessions, sequence,
rule, invariant, old/new roots, both ciphertext identities, both public wrap-safety bounds, authority
identities/tier/threshold, and exact replay slot. Theorems state that proof-only v2 cannot accept, acceptance pins every binding and consumes the
fresh slot, reserve/root/sequence/replay advance as one state, the reserve transition refines the existing
private-commit law, refusal holds the complete state, and no partial third outcome exists. Eight keystones
are under `#assert_all_clean`, and `#assert_not_depends_on` keeps the structural binding predicate free of
the cryptographic/semantic verifier.

The current focused `lake env lean Market/DarkAmmBoundReceipt.lean` gate is green. The new
`accepted_bounds_are_sound` theorem proves that each hidden opened amount lies beneath the corresponding
request bound on every accepted step. More importantly, this file is honest about its seam: `CipherOpensTo`,
the exact-opening capability's `verifiedMeaning`, and the encrypted
candidate receipt's `TrustedMeaning` are premises. It proves what an accepted capability means and how a
host must transition; it does not prove that fhe.rs ciphertext bytes, HidingFri, or Ed25519 construct those
premises, nor yet refine the Rust v3 implementation.

## 10. CURRENT IMPLEMENTATION DELTA — public web, Telegram, Discord, and deployment contract

**IMPLEMENTED shared surface:** `dreggnet-web/src/fhegg_operation.rs` is the single descriptor/upload
adapter used by browser, Telegram Mini App, and Discord Activity routes. The v3 integration scenario in
`dreggnet-web/tests/dark_amm_proved_game.rs` constructs a real hiding proof and 2-of-3 exact-opening receipt,
checks that only the v3 descriptor/media type/disclosure is advertised, exercises the browser upload and
409 replay response, and confirms the Telegram/Discord routes share the same authenticated operation
boundary. The expanded test now mints a real HMAC-covered Telegram initData envelope and uses the production
verifier for a successful v3 upload; it also drives Discord's real `/da/token` handler through its intended
injected OAuth exchange, receives a production-minted activity ticket, and successfully uploads an
independent v3 request. Both surfaces pin the exact new root, commit one turn, refuse replay with 409, and
refuse the other surface's credential before mutation.

**IMPLEMENTED fail-closed configuration:** the `public-shielded-games` feature owns fhEgg settlement, all
four private dungeon families, and Dark AMM. Startup parsing pairs the Dark AMM key with the initial root
and pairs the ordered issuer keys with their threshold; the production validator requires all four values
together and refuses proof-only v2 as well as every half-configured authority.
`deploy/games/deploy-hbox.sh` additionally requires an absolute secret-key path, exactly eight BabyBear root
lanes, and builds the release server with that aggregate feature. The environment examples and runbooks
document the same contract without embedding key material.

The current release gates are green: the combined v2/v3 web/bot target passes 2/2 in 19.480s after the
DBAPv003/FHAS003 full-parameter cutover, and the aggregate
public-shielded startup/surface target passes 3/3 in 0.023s. A later complete public-shielded web run caught
and repaired the generic fhEgg fixture's legacy unbound listing/bids: it now drives exact source-certified
seller ask/asset plus bid ciphertext bindings and the derived BFV identity through the shared adapter. The
same run repaired Descent's fixed-seed/devnet move-generator drift; `demo_win_for_seed` now generates against
the exact opened world. The complete package passes 143/143 release. This proves the compiled shared interface and
strict startup policy; it does not mean a production instance has been provisioned with issuer secrets or
deployed during this sprint. Discord's external OAuth network call is replaced only at its documented
injected exchange seam; ticket minting and verification are the production handlers. The aggregate persvati
gate used the prescribed test-only `DREGG_REQUIRE_LEAN=0` override because that lane lacks the seeded Lean
archive; it is not a shipping configuration.

## 11. CURRENT IMPLEMENTATION DELTA — exact SDD implies PSD optimizer admission

**BUILT Rust admission, PROVED mathematical implication:** `fhir/src/compile.rs` canonicalizes a public
portfolio covariance matrix to the same rounded `10^-9` fixed-point problem sent to the solver, then uses
exact integer symmetry, nonnegative diagonal, and row diagonal dominance as its accepting certificate.
The floating LDL factorization is an additional fail-closed diagnostic, never the authority. It explicitly
refuses the tolerance attack, overflow of the exact lift, and the PSD rank-one matrix `[[1,2],[2,4]]`
because that matrix is outside the supported SDD family.

The admission is no longer an ephemeral compiler branch. Every compiled QP carries an
`ExactSddPsdCertificate` v1 with scale, dimension, the dense exact rounded matrix, and checked row radii.
`solver_bridge::run` independently rechecks its version/shape/2^53 envelope/symmetry/nonnegative diagonal,
overflow-safe radii, diagonal dominance, and bit-exact binding to the actual backend `QpProblem.p` before
ADMM; a missing, misplaced, tampered, or backend-mismatched artifact returns `InvalidCompiled`. The current
artifact also has strict non-serde `FHSDD001` transport with big-endian signed exact entries/radii, a hard
2048 dimension/derived-size ceiling checked before allocation, exact EOF/canonical re-encoding, and a
domain-separated corruption checksum. `FHQPB001` additionally packages this admission witness with the exact
fixed-point KKT witness, rechecks both from one standalone artifact, and refuses any scale or `P` mismatch;
its strict bounded/exact-EOF transport has valid-checksum version, dimension, and matrix-substitution teeth.
`Market.QpCertificateBundle` pins the admitted and optimizer matrices equal and composes SDD=>PSD with the
existing exact-zero KKT theorem to obtain global optimality (two clean keystones). This theorem deliberately
does not promote positive-tolerance `rustCertQpCheck` acceptance to exact KKT; fixed-point decode/wire
refinement and the remaining residual bound are explicit seams.
The current `fhir` release gate passes 58/58, including every wire
truncation/trailing/version/count/checksum/structural tamper, certificate/backend tamper, and rounding-boundary
teeth. The public checksum is not authentication.

`metatheory/Market/SddPsd.lean` proves over rationals that symmetric nonnegative-diagonal row dominance
implies `Market.PsdSymm`, exposes an executable exact-integer `sddCheck`, proves
`sddCheck_implies_psd`, and proves both acceptance and deliberate PSD-but-non-SDD refusal examples. The
current source carries 13 `#assert_all_clean` entries and a dependency pin keeping `sddCheck` purely
arithmetical. Its focused Lean gate is green; the combined `fhir` + `fhegg-solver` release gate passes
164/164.

**Boundary:** SDD is a sound sufficient family, not a complete PSD decision procedure. Carrying and
rechecking the exact artifact makes the runtime PSD premise explicit, but Rust's source-f64 tolerance,
symmetric averaging, scaling, rounding, row-major parsing, and bounds checks have not yet been proved to
refine Lean `sddCheck`; those parts remain structurally/KAT pinned rather than a floating-point theorem.
Likewise, the exact-integer positive-tolerance KKT checker is not the exact-zero premise of the global
optimality theorem.

## 12. CURRENT IMPLEMENTATION DELTA — authenticated, restartable threshold-relin transcript

**IMPLEMENTED public control plane:** `fhegg-fhe/src/threshold/relin/transport.rs` adds fixed-width
Ed25519 envelopes for both multiparty relinearization rounds. Each envelope binds party, exact relin
session, collective public-key digest, ordered roster, round, predecessor transcript, and nonzero public
message id. `RelinCoordinator` accepts each party once, computes canonical round transcripts, snapshots a
bounded signed public state, verifies exact EOF/checksum/signatures/order/phase/digests on restore, and
supports exact authenticated resend after a coordinator restart. The focused test source covers restart in
both rounds, all truncations/trailing bytes/corruption, forgery, cross-session/key/roster/phase/predecessor
substitution, duplicate replay, and atomic refusal.

The current normal release crate gate exercises `threshold_relin_transport` 3/3, the underlying real relin
algebra 2/2, and the expanded no-secret Dark-AMM decision composition 6/6. The complete default
`fhegg-fhe` gate is green 170/170 in 6.596s (one explicitly skipped heavy test).

**Exact residual:** fhe.rs exposes typed public `RelinKeyShare<R1/R2>` values without a canonical share
codec. The signed object is therefore a manifest, not a cryptographic commitment to the opaque share; a
restarted coordinator must obtain the typed share again and match its recorded manifest. Party-local
ephemeral `u` is not restartable across the rounds. This remains honest n-of-n, with trusted behavior for
share correctness: it is not `t<n`, malicious-share proof, VSS relin, or rollback-resistant persistence.

## 13. CURRENT IMPLEMENTATION DELTA — active private fhIR box projection

**BUILT first active private prox:** `fhegg-fhe/src/fhir/private_box.rs` clamps a mod-`t` additively shared
secret to a public interval using three party-MPC comparisons: canonical input-range, lower face, and upper
face. Operands, differences, residues, and output value stay out of the coordinator; output remains shared,
can be compared to a public oracle through an equality bit, and can feed a candidate-bound second box
without a share accessor. The exact session binds program, candidate, domain, roster, bounds, and timeout.
The current focused Rust gate is 6/6 in 0.082s, covering all branches, exact output-only comparison,
two-step chaining, range/domain/session/roster failures, comparison replay, and cross-session material.

`metatheory/Market/PrivateBoxProjection.lean` proves the exact clamp semantics, public branch convention,
mod-`t` share transformation, box membership, fixed points, idempotence, and endpoint cases. Its current
post-source focused build completed with eight clean keystones.

**Boundary:** the selected face (`lower`, `interior`, `upper`) is public, so this is value-hiding execution,
not branch-oblivious prox. The online protocol is semi-honest, n-of-n, in-memory, and uses the trusted
Beaver-triple helper; MPC MACs, malicious input-validity proofs, authenticated transport, crash recovery,
and a compiler proof that general fhIR programs route to this runtime remain open.

## 14. CURRENT IMPLEMENTATION DELTA — hosted private raid, preference, shuffle, and quest mechanics

**IMPLEMENTED through one generic host affordance:** `dreggnet-offerings/src/dungeon.rs` publishes bounded
`BinaryOperationDescriptor`s and atomic handlers for four game families, and the shared adapter in §10
makes the same descriptors available to browser, Telegram, and Discord:

- private raid verifies a HidingFri proof of an admissible globally optimal four-role permutation and lands
  the assignment once;
- private preference verifies four hidden score ballots, reveals only the lowest-index winning party plan
  plus the ballot root, journals the canonical receipt, and re-verifies it after restart;
- fair shuffle enforces eight actor-bound commitments, a proof of the accepted rejection-sampled deal, and
  seat-owned Merkle openings with replay refusal, then restores the public protocol state from the journal;
- private quest accepts two ordered HidingFri-proved graph reductions, binds root/index continuity, refuses
  corrupt/reordered/replayed receipts, and reconstructs only the public continuation after restart.

Focused offering and web integration tests exist for every family, and
`dreggnet-web/tests/public_shielded_games.rs` asserts that the aggregate deployment feature exposes all six
operation names (raid, preference, shuffle commit/prove/reveal, quest) with unique bounded descriptors. The
aggregate public-shielded startup/surface target is green 3/3; the private-shuffle prover is green 4/4, its
Lean semantics are clean, and the private-preference descriptor/cell registration gates are green
separately. The aggregate gate establishes registration/discovery, while each operation's own focused test
remains the authority for its proof, mutation, refusal, and restart semantics.

**Boundary:** raid and preference are Tier-1 producer-private—the producer sees the full inputs. The fair
shuffle producer sees all contributions and the host sees submitted openings. Quest hides its graph and
rules from the host, but its history is still a standalone offering journal. These are not distributed MPC
input assembly and are not yet folded into their available `Effect::Custom` cell carriers. Section §5 is
the separate, already-implemented atomic economic settlement layer; composing these game receipts into
assets, balances, and Descent turns should reuse that transaction boundary rather than inventing a second
commit path.

## 15. CURRENT IMPLEMENTATION DELTA — secretless collective Dark AMM host and attested commit

**BUILT public restart/evaluation substrate:** `fhegg-fhe/src/dark_amm.rs` now emits strict bounded
`FHDAP002` public-host material containing the exact BFV parameter identity, collective public key, public
relinearization key, invariant `k`, declared caps, and both reserve ciphertexts. Decode checks the fixed
allocation ceilings, checksum, exact EOF and canonical fhe.rs encodings, BFV dimensions/moduli/plaintext
modulus, no-wrap cap product, `k <= cap_x*cap_y`, and public multiplication-engine shape. A restored
`DarkPool` has no LP plaintext view, accepts no `SecretKey`, preserves exact ciphertext bytes across process
reconstruction, and can homomorphically produce the next private candidate.

**BUILT independent one-bit commit:** private candidates now bind their exact encrypted pre-state in the
candidate nonce as well as the invariant and post-state, so an old valid candidate cannot roll an advanced
pool backward. `fhegg-fhe/src/dark_amm_attested.rs` reconstructs `PartyMpcSession::equality` from
relying-party policy plus that nonce, requires an explicit `equal=true` reveal-only transcript, verifies the
strict `FHDAR001` receipt against the configured ordered Ed25519 quorum and replay guard, then installs the
already-encrypted candidate without a `SecretKey` or non-transportable `DistributedDecisionRun`. Pool,
candidate, modulus, transcript, bit, binding, verifier, and evidence refusals all precede replay consumption;
the mutation after replay acceptance is deliberately infallible.

The focused no-assembled-secret release gate is green 6/6 in 1.037s:

```text
scripts/pbuild srot cargo nextest run -p fhegg-fhe --release \
  --test threshold_relin_dark_amm_decision
PASS: 6 passed, 0 skipped
```

Its teeth cover collective keygen and real multiparty relin, masked threshold opening into party equality,
true and false bits, cross-candidate binding, adversarial/truncated/oversized/cross-parameter `FHDAP002`
material, two accepted swaps across public-host restarts, commit after dropping the in-process decision
capability, wrong independent policy with replay held, stale-candidate refusal, and replay refusal after both
pool and replay snapshots restart. This integration target imports neither `SecretKey` nor
`threshold::combine`.

`metatheory/Market/DarkAmmPublicHost.lean` now authors the matching public-host state law without promoting
cryptography into axioms. Ten clean keystones prove stale-state nonacceptance, exact candidate-after and
fresh replay installation, decision-nonce pinning, false-bit nonacceptance, false/refused complete-state
hold, no partial outcome, restart preservation under an explicit codec roundtrip premise, and separate
sequential barriers showing that neither an accepted non-stuttering candidate nor its exact receipt can run
again. Two dependency
pins keep structural candidate binding and restore free of receipt/acceptance semantics. Focused Lean,
aggregate `Market`, and orphan gates are green.

`metatheory/Market/DarkAmmPublicHostLifecycle.lean` authors the actual two-phase shape with fourteen clean
keystones: stage records exactly one candidate while preserving committed state/replay; no, wrong, or stale
pending work and false/unverified/replayed receipts cannot commit; success installs exactly the staged after
state, consumes one fresh replay id, and clears pending; refusal/abandonment cannot partially settle; and an
explicit codec roundtrip preserves committed plus pending state. Its dependency pins keep stage and abandon
independent of commit-verifier semantics.

**Exact residuals:** the initial carrier still needs trusted pool-creation binding; its public checksum is
not authentication or rollback resistance. Without a separate proof, public validation cannot establish
that PK, relin key, and ciphertexts share one secret-key domain or that the hidden initial reserves multiply
to `k`. `FHDAR001` authenticates quorum agreement on the public bit, not malicious correctness of BFV
decrypt shares, masks, Beaver triples, or MPC inputs. Carrier and replay images must be committed atomically
to rollback-resistant storage. Finally, this is the collective substrate needed to replace the hosted game
key; `dreggnet`'s current strict v3 offering in §8 still remains explicitly
`n=1/opening_threshold=1` and was not cut over by this lane.

## 16. CURRENT IMPLEMENTATION DELTA — two-phase collective Dark AMM game service

**BUILT secretless dreggnet service boundary:** `dreggnet-market/src/dark_amm_collective.rs` configures the
exact collective DKG public identity, validated `FHDAP002` material plus `DBAPv003` producer session,
Tier-1 `FHAS003` same-opening authority, and an
independent `FHDAR001` policy without importing `SecretKey`, decryption, or `threshold::combine`. Phase one
strictly decodes the same-opening request, reconstructs the collective HidingFri/BFV context, verifies proof
plus authority, and records one exact pending candidate while leaving pool/root/sequence and both replay
guards unchanged. Phase two re-verifies the pending authority into a cloned same-opening guard, reconstructs
the candidate against a detached public-only pool, verifies the reveal-only equality transcript and FHDAR
into a second cloned guard, then atomically installs public ciphertext material, root, sequence, both replay
images, and clears pending. The public commit result identifies both independent claim digests.

The first implementation review caught and repaired a real liveness bug before final gating: the
same-opening replay id is one slot per `(hosted session, sequence)`, so consuming it at stage would make an
abandoned candidate permanently deadlock every replacement at that sequence. The final code consumes neither
guard at stage; `abandon_pending` therefore restores the exact pre-stage checkpoint, and the request can be
staged again after restart. `Market.DarkAmmPublicHostLifecycle` authors the matching
stage-preserves-committed/replay law rather than treating the Rust test as proof.
`Market.DarkAmmCollectiveTwoAuthority` then models the two independent replay domains explicitly and proves
ten clean laws: stage consumes neither, `abandon (stage ...)` restores the exact prior image, acceptance
requires exact pending plus independently fresh/bound same-opening and FHDAR capabilities, and one atomic
commit installs the candidate after-state, advances sequence, consumes both exact ids, and clears pending;
missing/wrong/replayed/refused cases hold the complete state.

`DBACv001` checkpoints bound and canonically retain material, root, sequence, both replay snapshots, and the
optional public pending request/digests/nonce. Pending restore re-verifies the full proof/signatures against a
clone of the still-fresh guard; committed restore preserves both consumed replay images. The focused release
gate `dark_amm_collective_session` passes 1/1 in 2.99s after the full-parameter bump with real 3-party DKG and multiparty relin, a real
HidingFri transition, 2-of-3 Tier-1 same-opening, external 2-of-3 FHDAR, cross-session/false/cross-candidate/
residual-only refusal with byte-identical state, both-side restart, duplicate/stale refusal, and
abandon/restart/restage.

An independent identity audit then found that `FHDAP002`'s repair had not yet propagated to producer
sessions and same-opening claims: both still named degree/moduli/plaintext but omitted error variance.
`DBAPv003` and `FHAS{O,E,R}003` now bind the same full canonical parameter digest; DBAP v001/v002 and FHAS
v002 fail closed, and a variance-only substitution is refused. The shared non-AMM `BfvPublicIdentity` ABI
was deliberately left unchanged. Core same-opening passes 2/2; collective + separate-issuer CLI + hosted v3
pass 3/3 release; the shared web/Telegram/Discord regression passes 2/2.

**Boundary:** the same-opening issuers still see witness and seeds. The service test simulates the reveal-only
decision-worker transcript; `fhegg-fhe::threshold_relin_dark_amm_decision` is the separate real masked,
no-assembled-secret computation gate. Initial relin/reserve honesty and shared secret-key domain remain trusted
creation evidence, public checksums are not rollback resistance, and malicious share/MPC input correctness is
open. This service is not yet registered as the existing browser/Telegram/Discord binary operation; those
player surfaces still exercise the strict n=1 table from §10. The collective service is now a real
game-service cutover target, not yet the shared-interface deployment cutover.
