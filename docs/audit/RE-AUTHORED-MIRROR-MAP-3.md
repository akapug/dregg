# THE MIRROR MAP — SWEEP THREE

**1 further adversarially-verified finding (M35) of the same failure mode — and, more importantly, a
REFUTED verdict on the two highest-stakes targets the prior sweeps named and never covered: the
light-client trust roots and the Go apex-VK mirror.**

Swept 2026-07-17 against HEAD `9e76b6c40` (the prior two sweeps were against `c451eb1f2`; the tree has
MOVED — see §3). Companion to `RE-AUTHORED-MIRROR-MAP.md` (M01–M21) and `RE-AUTHORED-MIRROR-MAP-2.md`
(M22–M34). Every claim below survived the same refutation pass (labeled-double / legitimate-abstraction /
labeled-placeholder / live-path-uses-the-real-thing / claim-misread each tried); the trust-root targets
FAILED to yield a finding, which is itself the headline.

**Sweep three's headline is not the 1 finding. It is the trust-root verdict:**
1. **The sharpest UNMET prediction of sweep one — "the light clients, on a bridge already documented
   UNSOUND, is where a mirror is most dangerous" — is REFUTED.** All six bridge/chain light-client
   verifiers CARRY or DELEGATE to the canonical authority; every reconstruction is either the in-process
   verifier the live caller routes into, or a residual the code labels honestly (weak-subjectivity anchor
   / StructureOnly-grade / modeled wire / trusted oracle). The trust roots are the MOST-defended surface,
   not the least.
2. **The Go apex-VK mirror is a genuinely fail-closed, honestly-labeled weak-subjectivity anchor.** Its
   drift mode is a LIVENESS failure (a stale pin REJECTS the real new apex), not a soundness hole. It is
   not the M13-at-the-chain-layer shape it superficially resembles.
3. **The one confirmed mirror (M35) is in the one sdk-py surface that RE-AUTHORS rather than carries**
   (`pg_workflow.py`, a disclosed Python reimplementation of the Rust durable driver) — exactly where
   sweep two predicted the next one would be (§2: "the one place that re-types rather than path-deps").

## ID table

| ID | Where | Variant | Severity |
|----|-------|---------|----------|
| M35 | `sdk-py/python/dregg/pg_workflow.py:135` | re-authored-peer / doc-claims-absent-seam | **medium** (false-claim, exactly-once-adjacent) |

**Running total: 35 confirmed (M01–M35).**

---

# §1 — THE CONFIRMED FINDING

### M35 — the durable-workflow `idempotency_key` is an inert re-typed contract; crash-resume dedups on raw turn bytes, not the key it advertises · **medium / false-claim**

- **CLAIM** — four sites, at reader altitude:
  (1) module header, `pg_workflow.py:28-30`: "keyed here by a per-step **idempotency key** the runner
  stamps so a resumed run recognizes its own already-committed steps."
  (2) `resume()` docstring, `pg_workflow.py:359-361`: "Reads the submissions already present for this
  workflow's steps (**by idempotency key**, via `_committed_keys`)…"
  (3) `WorkflowStep.idempotency_key`, `pg_workflow.py:135-137`: "Override to pin idempotency to a domain
  id (an invoice number, a billing-cycle tag) so the same business action is **never charged twice even
  across distinct runner invocations**."
  (4) the shipped `README.md:140-144` reinforces the same recognition story.
- **TRUTH** — `_committed_keys` (`pg_workflow.py:487-505`) never consults the idempotency key to decide a
  match. It builds `want` keyed on `(agent_hex, signed_turn bytes)` (`:490`) and matches on those exact
  bytes: `step = want.get((agent_hex, turn_bytes))` (`:496`). The idempotency key appears only on the
  OUTPUT side (`found[step.idempotency_key] = _PriorSubmission(...)`, `:499,:502`), where `_drive`
  immediately re-looks-it-up by the same step (`already.get(step.idempotency_key)`, `:385`) — it round-
  trips trivially and gates nothing. The method's own docstring discloses the real mechanism inline,
  contradicting the four claims above: "the runner correlates by matching each step's `(agent,
  signed_turn)`" (`:480-483`).
- **THE CONTRACT IS NOT MERELY DECORATIVE — IT FAILS ITS OWN HEADLINE.** A `SignedTurn` is regenerated
  with a FRESH nonce and `valid_until = now + 3600` on each build (`src/lib.rs:707-724`). So override
  `idempotency_key="invoice-42"`, then on a later runner invocation rebuild the step (fresh nonce) → the
  turn BYTES differ → `_committed_keys` finds no match → the step is re-enqueued and **charged again**,
  the exact double-charge `:135-137` says the override prevents. The override changes nothing. Even the
  DEFAULT deterministic-key path (`{workflow_id}:{index}:{name}`, `:289`) inherits this: "a committed
  step is skipped, never double-submitted" (`:252-254`) holds ONLY if the byte-identical `signed_turn` is
  persisted and replayed, never if it is regenerated — an undisclosed precondition that contradicts the
  "recognizes … by idempotency key" framing.
- **THE TESTS ARE GREEN BECAUSE THEY TEST THE MIRROR.** `test_explicit_idempotency_key_pins_to_domain_id`
  (`tests/test_pg_workflow.py:222-225`) asserts only that the key is STORED — never that it affects
  reconciliation. Every resume test reuses byte-identical turn literals (`b"\xaa"`, or a stashed
  `alice_turn` replayed verbatim), and one states the real basis in a comment: "alice must be SKIPPED
  (already executed, **matched by `(agent, signed_turn)`**)" (`test_pg_workflow.py:324`). No test ever
  regenerates a step's turn bytes across a resume, so the gap between "matched by bytes" and "recognized
  by idempotency key" is never exercised.
- **LIVE?** YES — `DurableWorkflow` is the shipped `dregg.pg` durable runner (re-exported), and
  `pg_workflow.py` is a DISCLOSED Python reimplementation of the Rust `pg_dregg::workflow` driver "over
  the live, persisted submit-queue rows rather than the Rust engine's in-memory `MemLog`" (`:10-14`) — a
  re-authored peer, not a path-dep binding. Bounded because the conservative reconciliation "never skips
  a step it cannot positively match" (`:484-486`) — the failure is a **re-charge**, never a lost step;
  the chain's own stale-nonce refusal is the backstop. Not a value-theft hole, but the advertised
  exactly-once property is false.
- **FIX** — make the key the thing that gates, or stop advertising it:
  1. Persist the `idempotency_key` in the submit-queue row (a `dregg_idem` column / metadata field) and
     have `_iter_prior_submissions` return it, so `_committed_keys` can match on the KEY, not on
     regenerated bytes. Then `want` is keyed by `idempotency_key` and `:496` becomes a key lookup.
  2. If plumbing the key through the DDL is out of scope, DELETE the "never charged twice even across
     distinct runner invocations" promise from `:135-137`, strike "by idempotency key" from `:28-30` and
     `:359-361`, correct `README.md:140-144`, and state the real, narrower guarantee: dedup holds only
     when the identical `signed_turn` bytes are persisted and replayed within one run's lifetime.
- **CANARY (RED first)** — `resume_dedups_across_regenerated_turn_bytes`: build a workflow with an
  explicit `idempotency_key`, commit step 0, then resume with the SAME key but a REGENERATED
  `signed_turn` (fresh nonce). Assert the step is recognized as committed and NOT re-enqueued. **It fails
  today** — the resume re-submits. Under fix (1) it passes; if fix (2) is taken instead, delete the test
  and the claim together.
- **Provenance of the lie:** `pg_workflow.py` re-authors the Rust durable driver's dedup, keeps the Rust
  driver's VOCABULARY (`idempotency_key`) as the reader-facing recognition story, but implements the
  dedup against the only column the live outbox actually exposes (`signed_turn`). The name is the Rust
  contract; the mechanism is the local reconstruction. Same shape as M22 (the "verifiable bill" that
  re-declares the receipt payload and checks arithmetic instead of provenance): the vocabulary of the
  real guarantee, over a substitute mechanism.

---

# §2 — THE TRUST-ROOT VERDICT (the highest-stakes question)

The prompt named this the headline: **a mirror at a trust root is the most dangerous kind.** Both trust
roots the prior sweeps predicted were adversarially audited in full and both are REFUTED. This is a
substantive result, not an absence of effort — the audit read the live call sites, not just the verifier
bodies, and tried the x==x / dead-differential / stale-oracle refutations on each.

## 2.1 The light clients — REFUTED (6/6 carry or delegate)

Sweep one's UNMET prediction was that a light-client `verify` would re-author what the full verifier
checks and could drift. It does not. Verdicts, with the decisive fact:

| File | Verify fn | Carries / Re-authors | Verdict |
|---|---|---|---|
| `chain/src/verify.rs` | `verify_on_chain` (`:33`) | real `verifyProof` contract call (`:82`); default fails **closed** (`VerifierMissing`, `:51`) | REFUTED |
| `bridge/src/solana_trustless.rs` | `verify_lock_proof_consensus_anchored` (`:636`) | DELEGATES to derived-table + `solana_wire` inclusion; the supplied-table forgery path is `#[cfg(test/test-utils)]` and labeled "un-shippable" (`:473-495`) | REFUTED |
| `bridge/src/solana_holdings.rs` | `prove_holding_consensus_anchored` (`:465`) | same shape; test-only trusted-table path labeled "un-shippable" (`:300-325`) | REFUTED |
| `bridge/src/solana_consensus.rs` | `verify_supermajority` (`:392`) & friends | RE-AUTHORS Tower-BFT/bank-hash/PoH but the "modeled-vs-mainnet boundary (honest)" block (`:31-58`) names every reconstruction and points to the wire/provenance adapters the live path runs | REFUTED (labeled model) |
| `bridge/src/solana_mirror.rs` | `verify_under` (`:184`) | real Ed25519 verify against an EXTERNAL oracle key (`:188`); self-labeled "trusted-oracle … does NOT verify Solana consensus" (`:21-24`); carries an independently-sourced `GOLDEN_UNLOCK_HASH` cross-check (`:699`) | REFUTED |
| `bridge/src/mina_observer.rs` | `observe_settlement` (`:351`) | compares node-sourced on-chain root to caller's expected (`:388-392`); header names it "StructureOnly-grade … the fully-trustless path … is NOT this module" (`:29-34`) | REFUTED |

**The decisive pattern:** every seam a real attacker would reach — supplied-table tallies, self-declared
`valid` bits, modeled vote encodings — is either `#[cfg(test/test-utils)]`-gated with an "un-shippable" /
"TEST-ONLY" label, or disclosed in prose as a NAMED residual. The live callers (`solana_relayer.rs:833`,
`solana_feed.rs:277`, the default `verify_on_chain`) route into the delegating/real verifiers or fail
closed. **The closest historical instance — the default-build mock in `chain/src/verify.rs` that once
"verified" a minted fake by decoding its self-declared `valid` bit — is documented as a bug found
2026-07-16 and is now excised and pinned RED by `test_verify_fails_closed_without_verifier` (`:193`).**
The tree caught its own version of this class one day before this sweep.

## 2.2 The Go apex-VK mirror — REFUTED (fail-closed weak-subjectivity anchor, not the M13 shape)

`chain/gnark/settlement_circuit.go:122` pins `DreggApexRecursionVk = "3ad1c9c6…"`; `circuit-prove/src/
apex_shrink_gnark_export.rs:216` pins the byte-identical Rust twin `DREGG_APEX_RECURSION_VK`. Two hand-
copies — superficially the M31 shared-constant shape. It is NOT a concealed mirror, for three verified
reasons:

1. **The oracle is git-tracked, not gitignored (unlike M30).** `chain/gnark/fixtures/apex_vk_identity.json`
   is committed (`git ls-files` confirms), its `recursion_vk_hex` == the pinned value. Both constants are
   checked against it fail-closed at every load (`check_apex_vk_identity_pin` Rust-side, `:224`;
   `checkApexVkIdentityAnchor` Go-side, `stark_algebra_real_fixture_test.go:743`).
2. **The pin is actually WIRED on the deployed wrap.** The Groth16-wrapped circuit
   (`TestSettlementGroth16EndToEnd`, `settlement_snark_test.go:73`) assembles via the shared
   `allocSettlementCircuit` (`stark_algebra_real_fixture_test.go:658`), which sets
   `apexPreprocessedCommit: apexPreprocessedCommitConstants(t)` (`:672`). Tooth 2 (the same-shape-apex
   forgery block, `settlement_circuit.go:278-284`) is ON in the circuit behind
   `settlement_groth16.vk` / `DreggGroth16Verifier25.sol` — not a documented-but-nil no-op.
3. **Drift is FAIL-CLOSED (liveness, not soundness).** The only gate that binds the pin to the actual
   HEAD circuit is a FRESH 2-turn fold, `derive_deployed_apex_vk_identity_and_check_fixture`
   (`apex_shrink_gnark_fixture.rs:293`), which asserts the freshly-derived fingerprint == the pinned
   constant before emitting. If the apex circuit changes, that assert fails; if it is NOT re-run, the
   stale pin makes the settlement circuit REJECT a proof over the new (real) apex. A stale anchor
   rejects the truth — it does not accept a forgery.

**The one real residual (named, not concealed):** that fresh-fold gate is `#[ignore]` (SLOW, ~4 min) AND
explicitly excluded from the armed-teeth CI lane (`armed-teeth.yml:87-90` names "the apex-shrink/gnark-
fixture … probes, whose external prerequisites are a separate question"). So NO CI job re-derives the
pin against HEAD; the Rust/Go static checks (`apex_vk_identity_pin_rejects_mismatched_fingerprint`, the
Go `TestApexPinFixtureMatchesDerivedDeployedIdentity`, `:812`) only compare CHECKED-IN artifacts against
CHECKED-IN constants — self-consistent and green through any apex change. This matches the M30 shape
STRUCTURALLY (the binding oracle is out of automation) but diverges on the two facts that make M30 a sin:
the residual is DISCLOSED at length (the doc calls it a "weak-subjectivity anchor … trust a governance-
pinned recent fingerprint, NOT trust whoever compiled", `settlement_circuit.go:92-121`), and drift is
fail-closed rather than accept-a-forgery. **Verdict: REFUTED as a concealed mirror; the honest residual
worth a work-item is "the fresh-fold re-derivation is not in CI, so apex drift is caught only by a manual
run — a stale pin is a liveness stop, not a false accept."** This is the Solana weak-subjectivity anchor
class the launch-readiness audit already tracks, at the apex-VK layer.

---

# §3 — CALIBRATION UPDATE

**Where sweep three lands:** 1 confirmed (M35). Sweep one estimated 35–60 total concealed mirrors; sweep
two hit 34; sweep three brings the running total to **35** — into the low end of the estimate, and
DECELERATING hard in the high-stakes territory.

**Is the estimate holding? For concealed SOUNDNESS mirrors at trust roots — NO, and that is good news.**
The estimate was built on the premise that the dangerous mirrors cluster where trust concentrates (light
clients, VK pins, the wallet signing surface). Sweep three audited exactly those and found them the
BEST-defended surface in the tree: they carry, delegate, label their residuals, and in two cases
(`chain/src/verify.rs`, wire.ts provenance) had ALREADY caught and fixed their own instance of the class.
The remaining unfound mirrors are far likelier to be low-stakes DUPLICATION (disclosed re-typed
constants that fail loud) than concealed soundness holes. The 35–60 count may still be reachable if you
count every disclosed-duplication seam — but the SOUNDNESS-bearing subset appears close to exhausted, and
the trend across three sweeps is CRITICAL(M13)→HIGH(M26/M30/M33)→this one medium.

**The tree has MOVED since the prior sweeps' HEAD (`c451eb1f2` → `9e76b6c40`), and several prior findings
are FIXED — the map is being worked as a work order:**
- **M13 (CRITICAL, the hand-retyped 24→5-wide descriptor forgery) — FIXED.** `circuit/descriptors/
  by-name/predicate-arith.json` now carries `trace_width: 25`, aligned with the Lean emission.
- **M30 (HIGH, published, the TS wire encoder dropping `provenance`) — FIXED.** `sdk-ts/src/internal/
  wire.ts:319` now writes `cap.provenance`; `sdk-ts/PUBLISHED-VERIFY.md:7` carries a dated "⚠ CORRECTION
  (2026-07-16)" retracting the byte-faithful verdict. The `[sem <digest>]` explain surface (`explain.ts`)
  is consequently faithful — its `effectHash` (`wire.ts:441`) matches Rust `Effect::hash`
  (`turn/src/action.rs:148-168`) exactly (both omit `provenance` from the effect-identity hash; the
  omission is symmetric, so injectivity-on-semantics holds).
- **M33 (HIGH, DrEX `mirror_conserves` = x≤x) — STILL OPEN.** `intent/src/drex_routing.rs:257-259` still
  populates `locked` and `minted` from the same `leg.amount` in one loop; the book is still built from
  `parties`/`p.offer_amount` (`:267-274`); none of the prescribed `MissingLock`/`UnbackedOffer`/`backing`
  machinery exists. The comment was reworded to "minted == locked ≤ locked" (`:254`) — which now openly
  ADMITS the tautology rather than fixing it.

---

# §4 — STILL UNSWEPT AFTER THREE SWEEPS

1. **The Go `*_ref.go` twin-engine differentials.** `chain/gnark/` ships ~a dozen native-Go reference
   verifiers (`fri_verify_ref.go`, `stark_verify_native_ref.go`, `challenger_ref.go`, `grinding_ref.go`,
   `poseidon2_*_ref.go`, …) as independent oracles for the in-circuit gnark gadgets. This is the M11/M27
   dead-differential class if any `_ref.go` was authored from the SAME source it is meant to independently
   check. Test-only (the live path is the Groth16-wrapped `SettlementCircuit`), so lower-stakes — but the
   "is this differential actually independent, or two copies of one derivation" question was NOT settled
   here.
2. **The gnark STARK-algebra / FRI verifier internals.** `stark_verify_native.go`, `fri_verify_native.go`,
   `stark_open_input.go`, `stark_constraint_interp.go` — the in-circuit re-implementation of the Rust
   plonky3 verifier. Whether the Go in-circuit verify faithfully carries the Rust verifier's checks (vs
   re-authoring a subset) is the deepest and least-swept trust question in the repo; it needs a
   prover-side differential audit, not a read.
3. **`midnight_*` (Compact contract + gateway/observer/verified) and `ethereum*`/`interchain_adapter`
   bridge legs** — the non-Solana bridge surfaces were only glanced at (Solana got the deep read). The
   same "verify carries or re-authors" question is open for them.
4. **The remaining sdk-py PyO3 surface breadth** — `src/lib.rs` is 2886 lines; the audit read it in full
   and found it disciplined (path-deps the Rust types), but the organ/service-economy/deploy method
   contracts were spot-checked, not exhaustively pinned against their Rust originals.
5. **The `sdk-ts` non-wallet modules** (`trustline.ts`, `token.ts`, `predicates.ts`, `channels.ts`,
   `service-economy.ts`) — scanned for re-typed discriminants/status strings; the hits found
   (`pg.ts:107`, `types.ts:337`, `turns.ts:42`) are the disclosed-duplication class (`| string`
   fallbacks, fail-closed, Rust-parity labels), not concealed mirrors, but were not each traced to their
   Rust origin.

**Bottom line for the reader:** three sweeps have driven the concealed-soundness-mirror class from a
CRITICAL forgery down to a single medium false-claim, and the two trust roots that would have been the
worst place to find one are clean. The tree is actively hardening (M13, M30 fixed; `chain/src/verify.rs`
self-caught). The next real risk is not a wallet or a light client — it is the gnark verifier internals
(§4.1–4.2), which no sweep has yet audited for faithfulness against the Rust verifier they stand in for.
