# fhEgg — Novelty & Paper-Worthiness Assessment (adversarial prior-art map)

*An honest, hostile-reviewer-calibrated answer to "what here is genuinely new vs. known
re-assembly, and is there a defensible academic paper?" The method is adversarial: for each
component the default verdict is **KNOWN** unless a hard search genuinely finds no prior art.
Every citation below was retrieved this session (arXiv IDs / IACR eprint numbers / venue pages
/ primary PDFs where noted); citations that could not be verified to a primary source are
flagged **[unverified-source]**. The construction summarized is the one in `FHEGG-KERNEL.md`,
`PRIVATE-CONVEX-ENGINE.md`, `DREGGFI-PRIVACY-TIERS.md`, `OUTPUT-BOUNDARY-MPC.md`,
`FHEGG-PRODUCT-ORDER-FRONTIER.md`, `PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md`, and the
`metatheory/Market/*.lean` cores. What-is, present tense; no marketing.*

---

## 0. The construction, stated precisely (what is being assessed)

The fhEgg line is a **private market-clearing engine** with five moving parts:

1. **Aggregation-monoid clearing + verify-not-find.** A clearing is a commutative, additively-
   homomorphic fold of per-order curve increments into demand/supply curves, resolved by a
   crossing (uniform price) or a convex optimum. The optimum is **not** trusted because a
   solver found it: an untrusted solver *proposes* a candidate, a linear **duality-gap
   certificate** (`Cert-F`: `Af=0, 0≤f≤c, s≥0, Aᵀπ+s≥w, cᵀs−wᵀf≤ε`) *disposes* it, and the
   certificate check emits as `O(m+nnz A)` circuit constraints carried in a PQ STARK
   (BabyBear/FRI). The solver is out of the trusted base.
2. **A convex-program mechanism family.** Uniform-price is `T=1`; the general engine is a
   fixed-`T`, data-independent (oblivious) first-order solve (PDHG/ADMM/mirror-descent) whose
   step is "public-matrix matvec + one prox," each member certified by the same duality/KKT
   gap (`CertQp`, `PriceCert`).
3. **Three privacy tiers over one kernel.** Dark (FHE, no-viewer), Shielded (STARK-ZK,
   solver-sees), Open (public). The soundness kernel is identical at every tier; only the
   privacy carrier and cost move. The tier is a **type** in `fhIR` (compiles ⇒ admissible).
4. **Output-boundary MPC (the Dark crossing).** Orders are folded under additive RLWE/BFV; at
   the boundary the `n` federation parties partial-decrypt only the aggregate curve **into
   additive secret shares** and run the crossing in a secret-shared MPC that reveals only
   `(p*, V*)`. The monotone sign vector is `p*`-determined (leaks nothing beyond `p*`); below
   the threshold `t`, no coalition learns any order or curve coefficient; no standing master
   decryption key exists.
5. **Formal verification in Lean + an anti-rug launchpad.** `metatheory/Market/*.lean` proves
   the fold homomorphism, order-independence, the monotone crossing, conservation, uniform-
   price optimality, the `Cert-F`/`CertQp` keystones, mint-safe quantization, and a
   reveal-nothing simulator `View = Sim∘Q` (conditional on a named `HidingFriPcs` statistical-
   ZK floor). A launchpad keeps custody in stable EVM contracts and consumes dregg only as a
   **boolean** from a pluggable `IClearingAttestor`, so a VK rotation cannot strand assets.

---

## 1. The adversarial prior-art table

Verdict legend: **KNOWN** = the idea is established prior art; **KNOWN-COMPOSITION** = each
ingredient is prior art and the assembly is expected, not surprising; **PLAUSIBLY-NOVEL** =
the hard search found no direct prior art for this *specific* claim (still likely combination-
novelty, not a new primitive).

| # | Component | Closest prior art (cited) | Verdict | One-line why |
|---|---|---|---|---|
| 1 | Private clearing revealing only the clearing price `p*` | Bogetoft et al., *Secure Multiparty Computation Goes Live* (FC 2009, Danish sugar-beet double auction, 3 Shamir servers, reveals only the MCP); Kikuchi, *(M+1)-st Price Auction Using HE* (FC 2001) | **KNOWN** | "Compute the market-clearing price over secret bids, reveal only `p*`" is 20–25 years old. |
| 2 | FHE aggregation of bids into a demand/supply curve → uniform price | Kikuchi (FC 2001); Abe–Suzuki *(M+1)-st Price Auction using HE* (PKC 2002); *Privacy-preserving Double Auction via HE & Sorting Networks* (arXiv 1909.07637, 2019); *Practical Verifiable & Privacy-Preserving Double Auctions* (ACM 2023) | **KNOWN** | Homomorphic fold into a demand curve then cross for the uniform price is the canonical HE-auction pattern since 2001. |
| 3 | **Verify-not-find**: check a duality-gap certificate in a ZK/STARK to certify clearing optimality without proving the solver | **Otti**, Angel–Blumberg–Ioannidis–Woods (USENIX Security 2022) — SNARK compiler that proves LP/SDP/SGD *optimality* via weak-duality certificates, "use solver to find witness / encode via certificates"; foundation: McConnell–Mehlhorn–Näher–Schweitzer, *Certifying Algorithms* (Computer Science Review 2011); Cheung–Gleixner–Steffy, *Verifying Integer Programming Results* (IPCO 2017); VeriPB/CakePB; market-clearing instance: *ZK Verification of P2P Energy Trading* (arXiv 2606.12085, 2026, KKT-in-circuit, private) | **KNOWN** | This is Otti's central contribution verbatim; certifying-algorithms + certified-LP is decades old. The central "verify-not-find clearing" claim is **not** a new technique. |
| 4 | Oblivious (fixed-`T`, data-independent) first-order convex solve as the private-friendly engine | Arjevani–Shamir, *oblivious first-order methods* (ICML 2016, arXiv 1605.03529); secure-simplex/interior-point cost analyses (Dreier–Kerschbaum, eprint 2011/108) | **KNOWN** | The obliviousness ↔ data-independent-schedule coincidence is stated in the optimization literature; PDHG/ADMM under MPC/HE is established. |
| 5 | Translation-validation framing ("approximation proposes, exact check disposes") | Pnueli–Siegel–Singerman, *Translation Validation* (TACAS 1998); Necula, *Translation Validation for an Optimizing Compiler* (PLDI 2000) | **KNOWN** | "Untrusted producer, verify each output exactly" is a named 25-year-old paradigm; applying it to a solver is a domain transplant. |
| 6 | Hybrid: additive/linear part under HE, nonlinear crossing in MPC, reveal only the output | **GAZELLE**, Juvekar–Vaikuntanathan–Chandrakasan (USENIX Security 2018, linear-in-HE / ReLU-in-GC / reveal-only-output); ABY (NDSS 2015), ABY3 (CCS 2018), Chameleon (AsiaCCS 2018), MOTION (TOPS 2022), MP2ML (ARES 2020) | **KNOWN** | The mixed-protocol linear↔nonlinear boundary is textbook; GAZELLE is the canonical "HE-linear + MPC-nonlinear + reveal-only-output" instance. |
| 7 | Additive HE fold + threshold-decrypt only the aggregate for a batch DEX | **Penumbra ZSwap** (Penumbra Labs, protocol spec ~2021–22; additively-homomorphic threshold ElGamal over decaf377, decrypt only the batch aggregate, clear against an AMM) | **KNOWN** | Penumbra is the same fold-then-threshold-decrypt-aggregate architecture — in classical DLog crypto, crossing computed in the clear. |
| 8 | MPC dark pool / private DEX with a verifiable correctness proof | **Renegade** (SPDZ 2PC + collaborative PLONK SNARK, crosses at external midpoint; classical BN254) [primitives from repo/docs, **[unverified-source]** on the primary whitepaper]; Cartlidge–Smart–Talibi, *MPC Joins the Dark Side* (AsiaCCS 2019) & *Turquoise Plato Uncross* MPC (eprint 2020/662, single-clearing-price periodic auction); Baum–David–Frederiksen, **P2DEX** (ACNS 2021, UC-secure private cross-chain matching) | **KNOWN** | A mature academic + industry line of private matching venues; Renegade is the closest *system* comparable. |
| 9 | Secure comparison / argmax over secret shares (the crossing primitive) | Damgård–Fitzi–Kiltz–Nielsen–Toft (TCC 2006); Nishide–Ohta (PKC 2007) | **KNOWN** | Textbook actively-secure MPC building block. |
| 10 | Threshold-FHE committee = a *policy* no-viewer (holds a reusable order-decryption key), not a cryptographic one | Shutter Network / encrypted-mempool literature (the keyper-set critique); Boneh et al., *Threshold Cryptosystems from Threshold FHE* (CRYPTO 2018) | **KNOWN** | The "standing decryption key is a trust assumption, mitigated by policy/economics" critique is established in the MEV/encrypted-mempool domain. |
| 11 | "No standing key: partial-decrypt only the selected aggregate into shares, reveal only `(p*,V*)`" as the fix | Bonawitz et al., *Practical Secure Aggregation* (CCS 2017, reveal only the sum) + the mixed-protocol works (#6) + Penumbra (#7) | **KNOWN-COMPOSITION** | Each half exists; keeping the crossing *inside MPC* (never decrypting the aggregate) rather than Penumbra's decrypt-the-aggregate is a sharpening, not a new primitive. |
| 12 | Monotone sign-vector leaks nothing beyond `p*` (flip-index = output) | Yao, *Millionaires' Problem* (FOCS 1982); Lindell, *How To Simulate It* (eprint 2016/046); Bogetoft (FC 2009); OPE/ORE leakage line (Boldyreva EUROCRYPT 2009; Chenette–Lewi–Weis–Wu FSE 2016) | **KNOWN** | "A monotone comparison reveals only the threshold/outcome" is standard simulation reasoning; the argument is a clean instance, not a new lemma. |
| 13 | `mint-safe quantization`: a *provable no-inflation invariant* for an *approximate* (lossy) FHE fold via directional rounding | CKKS (Cheon et al. ASIACRYPT 2017); IND-CPA-D (Li–Micciancio EUROCRYPT 2021, rounding as a *privacy* countermeasure); *Verifiable Computation for Approximate HE* (Cascudo et al. CRYPTO 2025, circuit-correctness, **not** conservation); exact-arithmetic conservation (Confidential Transactions / RingCT, fhEVM TFHE integers); directional-rounding-for-solvency (plaintext DeFi folk practice) | **PLAUSIBLY-NOVEL** | Every prior conservation-under-encryption result uses *exact* arithmetic (invariant is free); directional-rounding-for-solvency is *plaintext* and *informal*. No direct prior art joins "approximate HE" + "proved no-inflation invariant." Combination-novel. |
| 14 | Formally-verified market clearing (conservation + optimality) in a proof assistant | Sarswat–Singh, *Formally Verified Trades* (arXiv 2007.10805, 2020); Natarajan–Sarswat–Singh, *Verified Double Sided Auctions* (ITP 2021, proves **maximal volume + fairness + uniqueness**); *Double Auctions: Formalization and Automated Checkers* (JAR 2025); Caminati–Kerber–Lange–Rowat, *Sound Auction Specification* (ACM EC 2015, Isabelle VCG) | **KNOWN** | Verified clearing/matching with optimality and (implicit) conservation exists in Coq/Isabelle — on **cleartext** bids, no privacy content. The Lean re-derivation is not new *as verified clearing*. |
| 15 | Formally-verified *reveal-nothing simulator* (privacy) for a clearing/auction functionality | Verified *generic* MPC/ZK simulators: Haagh et al. (CSF 2018, EasyCrypt active-security MPC); Almeida et al. (CCS 2021, MPC-in-the-Head → ZK simulator); EasyUC (CSF 2019); SSProve (S&P 2021) — none instantiated on a clearing functionality | **PLAUSIBLY-NOVEL** | The two verified halves (#14 cleartext-clearing, and generic-MPC-simulators) have **never been joined**: no verified simulation-based *privacy* proof of a *clearing* mechanism surfaced, and no Lean simulation-based privacy proof of any MPC/clearing protocol at all. Combination-novel. |
| 16 | `p*`-determined-sign-vector-no-extra-leakage as a *proved* Lean statement | (#12 for the informal argument) + `RevealNothing.lean` `View=Sim∘Q` | **KNOWN-COMPOSITION** | The argument is textbook (#12); mechanizing it in Lean is the novel act, shared with #15. |
| 17 | Launchpad decoupled from the prover VK via a boolean attestor + epoch registry (safe-despite-rotation) | **StarkEx/StarkNet Fact Registry** (boolean `isValid` fact + upgradeable verifier proxy); zkVerify (Horizen Labs, 2025); ERC-1923 zk-SNARK Verifier Registry (2018, stagnant); universal L2 upgradeable-verifier proxies | **KNOWN** | "A boolean attestation decouples a consumer from the rotating VK behind an epoch registry" is the standard Fact-Registry pattern; "epoch" is not distinguishing. |
| 18 | Anti-rug launchpad (hard-cap mint, un-drainable floor pool, escrow-bounded settle) | Standard toolkit: hard-cap supply, LP locking (UNCX), LP burn / no-preallocation bonding curves (pump.fun), renounce + timelock; formal (generic) liquidity verification: *Solvent* (arXiv 2404.17864), FMBC 2025 *Validity/Liquidity/Fidelity* | **KNOWN** | The mechanisms are standard and mostly only *audited*; no anti-rug launchpad is itself formally verified un-ruggable, but the components are prior art. |
| 19 | Verifiable FHE (prove the encrypted clearing was computed correctly) | vFHE (Viand et al. / Knabenhans et al., WAHC 2023); SoK verifiable FHE; TFHE-bootstrap-in-plonky2 (eprint 2024/451) | **KNOWN** | Proving FHE correctness in a SNARK/STARK is an active published area; no novelty headroom for the category. |
| 20 | Post-quantum posture (lattice FHE + hash-STARK, vs. classical competitors) | Competitors (Penumbra, Renegade, Aztec, CoW) are classical DLog/pairing; FHE (lattice) and STARK (hash) are plausibly PQ | **KNOWN-COMPOSITION** (as posture) | Being PQ is a property of the chosen primitives, not an invention; but it is a genuine *differentiator* vs. every named competitor, and thin in the private-DEX field. |

---

## 2. Genuine-novelty distillation (what survives a hostile reviewer)

**Blunt headline: this is a systems/verification contribution of largely known parts,
well-assembled and — uniquely — formally verified. It is not a new cryptographic primitive,
and the central "verify-not-find clearing" idea is not new (Otti, 2022).** Do not claim
otherwise. What genuinely survives adversarial scrutiny:

1. **The formal-verification artifact joining verified-clearing with a reveal-nothing
   simulator (rows 14–16).** The literature splits into two halves nobody has joined:
   verified clearing exists only on *cleartext* bids (Sarswat/Singh Coq corpus; Caminati
   Isabelle VCG), and verified reveal-nothing simulators exist only for *generic* MPC/ZK
   (Haagh, Almeida, EasyUC, SSProve). No verified simulation-based *privacy* proof of a
   *clearing* mechanism exists, and no Lean simulation-based privacy proof of any MPC/clearing
   protocol exists (Lean crypto today — ArkLib, VCVio, Bailey–Miller Groth16 — is entirely
   soundness-side). This is **combination novelty**: defensible, but a reviewer will demand
   the simulator be shown *non-vacuous at the mechanism level* and that instantiating clearing
   over the generic machinery is *non-trivial*, not a plug-in. The sharpest un-occupied point:
   an **explicit named conservation/no-inflation theorem** of a clearing mechanism in a proof
   assistant (the Coq corpus conserves quantity only implicitly inside matching-validity).

2. **Mint-safe quantization for approximate-FHE conservation (row 13).** No direct prior art:
   prior conservation-under-encryption uses exact arithmetic (invariant free); directional-
   rounding-for-solvency is plaintext folk practice; CKKS soundness work is security or
   circuit-correctness, never a semantic conservation invariant. Defensible framing: "first to
   make conservative/directional rounding a *provable* no-inflation invariant in an
   *approximate* HE computation." The residual risk is an unindexed confidential-DeFi
   whitepaper, not a hidden academic paper.

3. **The specific system conjunction** — PQ lattice FHE fold + crossing kept *inside* MPC
   (never decrypting the aggregate, no standing key) + reveal only `(p*,V*)` + STARK
   verify-not-find certificate + tiered privacy + Lean-verified kernel. Each ingredient is
   prior art (rows 3, 6, 7, 11), so this is an *engineering/integration* contribution, not a
   mechanism invention. Reviewers will point to Penumbra ("same architecture, classical
   crypto") and GAZELLE/ABY ("same HE/MPC boundary"); the honest distinguishers are (i) the
   crossing never decrypts the aggregate, (ii) PQ, (iii) formally verified.

**What does NOT survive as novelty (claim these as prior art, cite-and-distinguish):** the
verify-not-find certificate idea (Otti); the hybrid HE→MPC-reveal-output pattern
(GAZELLE/ABY); FHE-demand-curve uniform-price clearing (Kikuchi); reveal-only-`p*` MPC
clearing (Bogetoft); the monotone-flip leakage argument (Yao/Lindell); the boolean-attestor
VK decoupling (StarkEx Fact Registry); verified cleartext double-auction clearing
(Sarswat/Singh); verifiable FHE (vFHE).

---

## 3. Paper-worthiness verdict

**Is there a legitimate paper? — Yes, one: a systems/applied-crypto paper of the form "a
formally-verified, post-quantum private market-clearing engine," honestly positioned as
known-parts-well-assembled-and-verified. It is NOT a new-primitive theory paper, and the
search does not support one.**

- **Kind & venue.** A **systems / applied-cryptography** paper. Natural homes, in order of
  fit: **Financial Cryptography (FC)** or **Advances in Financial Technologies (AFT)** — the
  private-DEX / auction-mechanism audience that will grade it on the right axis. A top-tier
  security venue (**USENIX Security / CCS / IEEE S&P**) is reachable *only if* the formal-
  verification contribution (rows 14–16) or mint-safe quantization (row 13) is developed into
  a standalone, evaluated technical result — otherwise the systems contribution reads as an
  integration of Otti + Penumbra + GAZELLE + the Sarswat corpus and will be desk-rejected as
  "known composition" at those venues. A **formal-methods** venue (**CPP / ITP / CAV**) is the
  right home for a *verification-first* framing (the Lean reveal-nothing simulator + conserved
  clearing as the headline).

- **Honest framing (the one that survives review).** "We build and formally verify (in Lean) a
  private market-clearing engine. Contributions: (1) the first machine-checked *privacy*
  (reveal-nothing simulator) proof instantiated on a *clearing* mechanism, joined to a
  machine-checked *conservation + uniform-price-optimality* proof — a combination absent from
  both the verified-auction and the verified-MPC literatures; (2) mint-safe quantization, a
  provable no-inflation invariant for approximate (lossy) HE folds; (3) a full system
  (verify-not-find certificate in a PQ STARK, additive-fold + output-boundary MPC crossing
  revealing only `(p*,V*)`, tiered privacy) that is post-quantum where all prior private DEXs
  are classical." Explicitly cite Otti, Penumbra, Renegade, Kikuchi, GAZELLE, and the
  Sarswat/Caminati corpus as prior art and state precisely what is *not* claimed.

- **Closest competing papers to position against.** Otti (USENIX Sec 2022, the verify-not-find
  technique); Penumbra ZSwap (the fold-then-threshold-decrypt architecture); Renegade (the
  verifiable MPC dark pool); Kikuchi FC 2001 / Cartlidge–Smart–Talibi (HE/MPC uniform-price
  auctions); Natarajan–Sarswat–Singh ITP 2021 (verified cleartext clearing); Almeida et al.
  CCS 2021 (verified generic MPC simulator).

- **What must be DONE for it to be publishable.**
  1. A **real simulation-based security proof** of the output-boundary MPC — the PoC's
     empirical indistinguishability (bias 0.0014 over 200 runs) is a demo, not a proof; a
     hostile reviewer rejects "statistically indistinguishable over N runs" outright. Needs a
     formal simulator + hybrid argument (semi-honest first).
  2. **Discharge the `HidingFriPcs` statistical-ZK floor** on which the whole reveal-nothing
     result is currently conditional — otherwise the headline privacy claim is
     floor-conditional and a reviewer treats it as unproven.
  3. **Malicious-security** analysis of the MPC (authenticated shares / SPDZ MACs, verifiable
     partial decryption, noise smudging), not just semi-honest.
  4. **A composition/UC argument** for the whole stack (certificate + STARK + MPC + tiers +
     the leakage functor `Q`) — the pieces are argued separately today.
  5. **A real evaluation**: the threshold-BFV partial-decrypt-into-shares built (not modelled),
     network-round latency among real `t` parties (not simulated in one process), and the FHE
     envelope at deployment scale.
  6. A **prior-art positioning section** matching §1 here, so the reviewer sees the honesty
     before they find the gap.

---

## 4. ⚑ Where the security arguments need strengthening (the Lean/security roadmap)

This is the load-bearing engineering direction, tied to ember's Lean point: the value is what
the system *proves*, so the proofs must reach what a reviewer and the literature expect. The
top three, ranked:

1. **A real simulation-based MPC security proof (replace the empirical PoC).** The
   `OUTPUT-BOUNDARY-MPC.md` §7B result is empirical indistinguishability (opened-bit bias
   0.0014, sign-vector/`V*` equality over 200 runs). That is a *demonstration*, not security.
   The literature (Haagh CSF 2018, Almeida CCS 2021, Lindell's tutorial) expects a **formal
   simulator** producing a view *identically/statistically-indistinguishably* distributed to
   the real one, with a **hybrid argument** across the online phase, first semi-honest then
   **malicious** (the PoC is semi-honest only; §8 names authenticated shares / verifiable
   partial decryption / smudging as unbuilt). The Lean `RevealNothing.lean` `View=Sim∘Q` is
   the *right shape* but sits at the clearing/transcript level; the MPC layer needs its own
   simulator theorem, and joining them is the combination-novel artifact of §2.1.

2. **Discharge the reveal-nothing floor (`HidingFriPcs`) and prove composition.** Two coupled
   gaps: (a) the deployed reveal-nothing consequence is *conditional* on the `HidingFriPcs`
   statistical-ZK + hash-hiding + nullifier-unlinkability floor (a bundle field, not yet a Lean
   theorem) — until discharged, the whole Shielded/Dark privacy claim is floor-conditional,
   exactly the posture a reviewer flags; (b) **composition security** — the certificate + STARK
   + MPC + tiers must compose without leaking, and today each is argued in isolation. A UC-style
   or explicit composition theorem over the leakage functor `Q` is what the literature expects
   for an end-to-end privacy claim; the `ZKOpenRel.lean` categorical frame is the right home but
   the *adaptive/feedback composition closure* is the known-open piece (`FHEGG-CODEX-INSIGHTS`
   Q2). Prove that the composed leakage is exactly `Q = (p*, V*, batch-root, conserved-total)`
   and nothing more.

3. **Malicious-model integrity + the `fhIR` admissibility / leakage-refinement theorem.** Two
   sub-items a reviewer will press: (a) the correctness/integrity claim currently rests on "the
   STARK boundary check catches a wrong `p*`" — this needs the boundary relation
   (`¬Clears(p*+1) ∧ Clears(p*)`, `V*=min(D[p*],S[p*])`) actually instantiated against the
   committed aggregate and proved to keep the comparator outside the soundness TCB under a
   *malicious* party; (b) the `fhIR` "admissible iff compiles" theorem — specifically the
   **leakage-refinement** part (`View(P,w) ≈ Sim(Leak(P,w))`) — is a named research target, not
   discharged, and it is the formal object that makes "the tier is a type" honest. Discharging
   it (even for the finite/monotone fragment, mirroring the proved `traceAdmissible_guarded`
   closure) is what upgrades the privacy-tier story from a product spine to a theorem.

**Lesser but real:** mint-safe quantization (row 13) should be published with its adversarial
teeth (`wrong_direction_admits_mint`, `genuine_mint_fails_gate`, `field_gate_without_range_mints`)
as the falsifiers — that is what distinguishes it from the informal DeFi folk practice and makes
the "provable no-inflation invariant" claim defensible.

---

## 5. One-paragraph honest answer

The fhEgg construction is **a solid systems / applied-crypto contribution of known parts,
well-assembled and — distinctively — formally verified.** The private-clearing idea
(reveal-only-`p*` MPC/HE auctions) is 20–25 years old (Bogetoft FC 2009, Kikuchi FC 2001); the
verify-not-find duality-certificate-in-ZK is Otti (USENIX Security 2022); the additive-HE-fold
+ threshold-decrypt-aggregate DEX is Penumbra; the HE-linear/MPC-nonlinear-reveal-output hybrid
is GAZELLE/ABY; the boolean-attestor VK decoupling is the StarkEx Fact Registry; verified
cleartext double-auction clearing is the Sarswat/Singh corpus. **None of the headline ideas is a
new primitive, and the assessment says so.** The genuinely defensible novelty is narrow and is
*combination* novelty: (1) a machine-checked *privacy* (reveal-nothing simulator) proof
instantiated on a *clearing* mechanism, joined to a machine-checked conservation +
optimality proof — an intersection empty in both the verified-auction and verified-MPC
literatures; (2) mint-safe quantization as a provable no-inflation invariant for *approximate*
HE (all prior encrypted-conservation uses exact arithmetic); and (3) the PQ + crossing-stays-in-
MPC + `(p*,V*)`-only system engineering. **There is one legitimate paper** — a systems/applied
paper at Financial Crypto or AFT (or a verification-first paper at CPP/ITP) framed exactly as
above — **provided** the MPC gets a real simulation-based proof (not the empirical PoC), the
`HidingFriPcs` floor is discharged, malicious security and stack composition are argued, and a
real (non-simulated) threshold + latency evaluation exists.

---

## 6. Verification caveats (honesty about sourcing)

- Verified to primary source: Otti (full PDF read); Bogetoft FC 2009 & eprint 2008/068
  (mirror); Cartlidge–Smart–Talibi eprint 2020/662; Penumbra protocol spec (note: flow
  encryption is flagged **not shipped in V1** — "designed," not necessarily live); Kikuchi,
  GAZELLE, ABY, Bonawitz, the Sarswat/Natarajan/Singh corpus, Caminati EC 2015, Haagh CSF 2018,
  Almeida CCS 2021 — confirmed by arXiv/eprint/venue.
- **[unverified-source]**: Renegade's precise primitives (SPDZ 2PC, PLONK/BN254, Binance
  midpoint) come from the GitHub repos + docs snippets + Kagi, **not** the primary whitepaper
  (renegade.fi was not fetchable this session). The Thorpe–Parkes cryptographic-exchange
  references, the exact DOIs for Bahr–Berthold–Elsman (ICFP 2015), the StarkEx `isValid`
  Solidity signature, and CRPWarner/Solvent/FMBC exact DOIs were surfaced but not each
  re-fetched — verify these strings before formal citation.
- Correction carried from the search: the EasyCrypt active-security MPC paper's fifth author is
  **Pierre-Yves Strub**, not "Zając" (no such paper exists).
- The search is not exhaustive. The two **PLAUSIBLY-NOVEL** verdicts (rows 13, 15) are
  "no direct prior art found," which is weaker than "provably first"; the residual risk is an
  unindexed whitepaper, not a hidden top-venue paper.
