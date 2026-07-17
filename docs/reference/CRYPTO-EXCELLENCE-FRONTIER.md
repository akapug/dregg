# Crypto Excellence Frontier — the redesign map (for codex, driven interactively)

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
2. **The crossing + minimal reveal.** Per the grounded Market-#4 resolution: the MPC must reveal
   ONLY the balance-threshold / clearing price — nothing else (currently `FhEggRustDenotation` reveals
   the *argmax*, which leaks more). Redesign the crossing reveal-minimal, and reconsider the protocol:
   Beaver-triple crossing + sequential K−1 argmax scan (~3.4k rounds) vs a **tournament-tree argmax**
   (log₂K depth) vs function-secret-sharing / garbled-circuit crossing. Round complexity is the driver
   once it's networked.
3. **⚑ Hiding commitment (CROSS-CUTTING — see §V).** `HidingFriPcs` is a *named floor*, not proved.
   A PCS with hiding built in discharges it — and the *same* redesign serves the FRI soundness (§III)
   and connects to the ArkLib KZG work (KZG is a PCS). Route Cert-F through a genuinely-hiding PCS.
4. **Runtime optimality certificate.** Extend Cert-F beyond ring-3 to the uniform-price fold + extract
   the descriptor gap-gate (`certFDescriptor_emit_sound` delivers ~2.5/5 — `MARKET-METATHEORY-REVIEW.md`)
   → a real runtime ε-optimality attestation of the *actual* clearing. This is "attested optimality"
   done right (Cert-F, verify-not-find — NOT per-step, NOT the receipt stack; that conflation is
   corrected in `FHEGG-ATTESTATION-GROUNDING.md`).
5. **Threshold decrypt.** Wire real threshold-BFV + smudging at the masked boundary (the noise-channel
   is currently named); the last networked seam to a live Tier-0 clear.

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

Per `MARKET-METATHEORY-REVIEW.md` + `FHEGG-ATTESTATION-GROUNDING.md`: (1) `FhIRAdmissible` mirror/vacuous
→ build a real syntactic⇒semantic bridge or drop the claim; (2) `InterchainCustody` laundered/vacuous
→ real cross-boundary conservation; (3) `CertFDescriptor` over-named → extract the ε-gap gate;
(4) **marquee `MpcClearingSecurity`** → reveal aligned DOWN to balance-threshold, headline =
conservation/value-neutral (runtime-attested), ε-optimality named model-level, strengthen via §I.4.

## V. ⚑ CROSS-CUTTING EXCELLENCE — the hiding PCS

The single redesign that serves the most: a **genuinely-hiding polynomial commitment scheme** would
(a) discharge fhegg's `HidingFriPcs` confidentiality floor, (b) give the FRI word↔proof bridge a
*hiding* decode, (c) connect directly to the ArkLib KZG line we just proved. One commitment scheme,
three payoffs. This is the highest-leverage architectural question in the whole subproject.

---

## Setup — unleashing codex (interactive, separate terminal)

- **Isolation: a separate CLONE, not a worktree** (the tree's discipline is NO WORKTREES, and codex
  may run big destructive redesign experiments). Suggested: a fresh clone (`~/dev/breadstuffs-codex`,
  or on persvati/hbox) so codex's experiments + builds never clobber the live swarm tree or contend
  the one cargo/lake target lock. ember merges the good deltas back surgically (pathspec, never `-A`).
- **Build/verify commands:** Lean → pinned toolchains (`metatheory/lean-toolchain` = v4.30.0; the
  ArkLib line is v4.31.0), `swarm-build` on hbox (MemoryMax cgroup — bare cargo/lake OOMs it), NEVER
  two concurrent `lake build`s. Rust fhegg → `cargo test --release` in `fhegg-fhe/`; KATs are the
  gate (every perf/scheme change proves equivalence to a plaintext reference).
- **The discipline codex inherits (non-negotiable, even mid-redesign):** the sufficient test (a
  redesign that is vacuous is worse than the honest floor); no named-carrier laundering; additive
  where possible; `#assert_axioms`-clean for Lean; verify from committed source (the day's two misses
  were dangling commits caught only by from-scratch builds). We verify what codex ships.
- **The frame for codex:** "the honest endpoints in this doc are the floor. Beat them by *reapproach*,
  not patch, wherever a cleaner cryptosystem exists — but every green must RED-when-broken."
