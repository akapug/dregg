# Crypto Excellence Frontier — the redesign map (for codex, driven interactively)

> ⚠ **STATUS: HYPOTHESIS, not verified ground truth.** Written by the main loop (claude-of-dregg)
> synthesizing lane reports + docs — the same author who *conflated the receipt stack with fhegg
> attestation* and had to be corrected (see `FHEGG-ATTESTATION-GROUNDING.md`). So this map may contain
> more errors of that species. **CODEX'S FIRST TASK: factcheck / investigate / critique / REGROUND this
> against the real code, and propose otherwise where it's wrong — do NOT treat it as gospel.** Re-derive
> the frontier from source; if a claim here doesn't survive reading the code, the claim is the finding.
>
> **The claims most likely to be my synthesis (verify hardest):** (1) §V — that *one* hiding PCS
> discharges fhegg's `HidingFriPcs` AND gives the FRI decode a hiding form AND is the same object as the
> ArkLib KZG line — this "three payoffs, one scheme" is my extrapolation, not a proven connection; check
> whether these are the same commitment abstraction or a loose analogy. (2) §I.1 — that BFV-fold +
> MPC-crossing is the accurate *decomposition* and that PDHG-matvec is the real remaining perf frontier
> (read `MEASURED-ENVELOPE.md`, don't trust my paraphrase). (3) §III — whether the biased sampler's fix
> actually removes the εQuery uniformity-defect *cleanly*, or opens a new term. The Lean-proven facts
> (the biased-sampler non-uniformity itself, the 3/4 legs, the Market wounds) are cited to theorems and
> are firmer; the *redesign framings* around them are mine.

**Frame.** Every "honest endpoint" below is a **FLOOR to beat, not a ceiling to defend.** The
question is not "close the named gap" — it is *"is this the right cryptosystem at all, or does a
reapproach get us somewhere strictly better?"* Excellence > honesty. But the sufficient test still
rules: a redesign that is faster/cleaner AND vacuous is worse than the honest floor. Every claim
codex ships gets a KAT / a build / the sufficient test — the honest floors are what we refuse to
regress below.

**Ground truth first (do NOT reconstruct from this prose — read the real files).** Pointers are
`file:line@HEAD`. The honest current-state docs are the starting read:
`docs/reference/FHEGG-ATTESTATION-GROUNDING.md`, `MARKET-METATHEORY-REVIEW.md`,
`FRI-EXTRACTION-FLOOR-DESIGN.md`, `docs/deos/FHEGG-*.md`, and `GOAL-FRI-PRODUCT.md` (the day's ledger).

---

## I. fhegg — confidential market clearing (the biggest crypto surface)

**Honest state.** BFV carry-free additive fold (`fhegg-fhe/src/additive.rs`, 10⁵× fast, bit-exact,
mint-safe) → output-boundary MPC crossing (`src/mpc.rs` + `src/boundary.rs`, masked-decrypt-to-shares,
AGG→p\* = 17–76ms) → Cert-F convex ε-optimality certificate (`metatheory/Market/CertF.lean`, the
`(f,π,s)` linear check — **verify-not-find**, ring-3 only). Confidentiality conditional on the named
`HidingFriPcs` statistical-ZK floor + a proven `perfect_hiding`.

**⚑ REDESIGN QUESTIONS (the Excellence targets):**
1. **Scheme architecture.** BFV (exact) for the fold; the scheme-switch was *dissolved* by the
   output-boundary MPC. Is BFV-fold + MPC-crossing the best decomposition, or is there a **single
   unified scheme** end-to-end? The remaining perf frontier is the PDHG convex engine
   (`MEASURED-ENVELOPE.md` — matvec ~50% of the bill) — reapproach the convex solve on the additive
   carrier (proposed), or a different optimizer entirely?
2. **The crossing + minimal reveal.** The rule is the volume argmax, ties to the lowest bucket, and the
   party runtime now uses a balanced tournament rather than the old sequential scan. It reconstructs only
   `(p*,V*)`. `MpcClearingSecurity.lean` now models that exact leakage and proves the obsolete balance
   threshold/sign vector is both wrong and not simulable from the actual view. The remaining problem is
   authenticated malicious-secure deployment, not changing the economic rule to leak less by mis-clearing.
3. **⚑ Hiding commitment (CROSS-CUTTING — see §V).** Cert-F now has a real batch-STARK path through
   `HidingFriPcs`; its focused tooth asserts the random commitment/openings and refuses a public-output
   mutation. The open floor is the complete transcript-simulator theorem (plus FRI soundness), not routing.
4. **Runtime optimality certificate.** The full Cert-F descriptor relation and integer admission now hold
   for byte-pinned ring3 and market4, and the latter admits nonzero `ε`. The uniform-price/Tier-0 frontier
   is source binding: prove that the exact committed/encrypted order roster produced `(p*,V*)` and the
   settlement receipt without creating a plaintext prover.
5. **Threshold decrypt.** Party-owned n-of-n BFV, smudged masked opening, direct-peer arithmetic ingress,
   A2B/mod-t reduction, and the balanced crossing compose at local process scope. Authentication,
   malicious share/input validity, auditable/dealer-free triples, crash recovery, and `t<n` remain.

## II. DrEX — the trading cryptosystem

**Honest state.** Shielded Cert-F prove + reveal-nothing world-view (`drex-web-v2/serve.mjs`);
settlement lands real Transfer turns (`settleOnNode`); the SetField VK path is an ember-gated limitation.

**REDESIGN:** input-privacy via note-commitment matching (named lane); the SetField VK-epoch flip for
*attested per-trader allocation writes* (not just Transfer); a real shielded deposit bridge
(`SHIELDED-DEPOSIT-BRIDGE.md`); batched/scalable settlement. The excellence question: what is the
*minimal-trust* end-to-end trade — deposit → sealed order → confidential clear → attested settle —
and which links are still trusted vs proved?

## III. FRI soundness — the two named blockers, as redesign prompts

**Honest state (`FriVerifierCompose.lean`, 23 keystones clean).** εFri composed over a shared oracle,
3/4 legs proven at the L=1 radius; apex probabilistic; `friLdtExtractV3_rom` blocked on:
1. **⚑ Biased sampler — a REAL deployed-code defect.** `qidx = squeeze mod 2^logN` is *provably
   non-uniform* (`babybear_sampleBits_not_balanced`: |F| odd ⇒ 2^logN ∤ |F|). This is not just a proof
   gap — the **deployed FS query sampling is biased.** Redesign the FS challenge derivation to be
   uniform (rejection sampling / a wider squeeze / a different index map) — a real deployed improvement
   that *also* removes the εQuery uniformity-defect term. Tractable, high-value, ship a KAT.
2. **Word↔proof bridge** (`DeployedFriEmbedding` decode — the FRI-proximity-to-`VmTrace` decode, a
   hypothesis structure, not lemma-sized). The big leg. Redesign question: is the deployed FRI /
   commitment architecture the right IOP, or does a cleaner one (a different proximity test, a hiding
   PCS §V) give a *provable* decode instead of an assumed one?

## IV. Market metatheory — the 4 confidential-layer wounds (grounded repairs)

The older review findings must be checked against HEAD before reuse: the Cert-F gap/integer-admission
defects and the `MpcClearingSecurity` balance-threshold/sign-vector mismatch have been repaired. The live
frontier is the exact committed-source → private computation → `(p*,V*)` → settlement receipt join, plus
the remaining distributed-protocol and cryptographic proof floors.

## V. ⚑ CROSS-CUTTING EXCELLENCE — the hiding PCS

The common construction is now concrete: Plonky3 `HidingFriPcs` serves the DSL uni-STARK and the Cert-F
batch STARK. The remaining cross-cutting proof obligation is to establish the complete simulator/view
statement for the deployed batch transcript and compose it with the FRI decode/soundness theorem. That
same statement must stay distinct from Tier-0 no-viewer integrity, where no single plaintext witness-holder
exists to run an ordinary prover.

---

## Setup — unleashing codex in the live swarm

- **Shared-tree discipline:** work in the real `/Users/ember/dev/breadstuffs` tree and integrate active
  WIP when the lane requires it. No worktrees, stash, or branch switching; segregate files where possible
  and preserve unrelated edits. A separate clone is optional for genuinely destructive experiments, not
  the default place where useful work must later be hand-carried back.
- **Build/verify commands:** keep Lean local and run the narrow file/module gate. Use `cargo nextest` for
  focused Rust crates/tests; offload heavy crypto builds through a warm `scripts/pbuild` lane. The default
  nextest profile is the fast set; proof/recursion heavies run deliberately in the heavy/release lane, not
  as a per-edit tax. KATs remain the semantic gate for every performance or scheme change.
- **The discipline codex inherits (non-negotiable, even mid-redesign):** the sufficient test (a
  redesign that is vacuous is worse than the honest floor); no named-carrier laundering; additive
  where possible; `#assert_axioms`-clean for Lean; verify from committed source (the day's two misses
  were dangling commits caught only by from-scratch builds). We verify what codex ships.
- **The frame for codex:** "the honest endpoints in this doc are the floor. Beat them by *reapproach*,
  not patch, wherever a cleaner cryptosystem exists — but every green must RED-when-broken."
