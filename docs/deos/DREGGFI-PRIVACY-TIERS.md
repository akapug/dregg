# DreggFi Privacy Tiers — three postures, one verified kernel

*The product & deployment spine for DrEX. The `fhEgg` research line
(`FHEGG-KERNEL.md`, `PRIVATE-CONVEX-ENGINE.md`, the two codex-insight rounds,
`DREX-NO-VIEWER-SURPASS.md`) crystallizes into **three user-selectable privacy
tiers that share one verified soundness kernel**. This doc states the tiers
precisely, the load-bearing "one kernel, three postures" insight, the way a tier
is a **type in `fhIR`**, the honest deployment ladder, and the interchain/routing
composition — with each tier's privacy label stated as **exactly what it is**
(no dark-washing) and every research target flagged as a target. What-is,
present tense; every ambitious edge names its grade.*

---

## 0. Five-line summary

1. **Three tiers on one frontier.** DrEX offers three points on the
   privacy ↔ generality ↔ cost frontier — **Tier 0 DARK** (FHE, no-viewer),
   **Tier 1 SHIELDED** (STARK-ZK, private-from-the-world, solver-sees), **Tier 2
   OPEN** (public, fully general) — and the user (or market, or per-trade) picks.
2. **One verified kernel underneath all three.** Every tier runs the *same*
   machine-checked soundness core (`exact_clears_iff`, `toBal_mul`,
   `clearing_conserves_per_asset`, `uniform_price_optimal`,
   `created_value_conservation`, the `Cert-F`/duality certificate, the turn-kernel
   receipt). **Fair, conserving, no-mint, proven is identical at every tier;**
   only privacy, mechanism-generality, and cost vary.
3. **The tier is a type.** In `fhIR` (the typed order/product DSL, "admissible iff
   it compiles"), a product is well-typed at Tier 0 iff FHE-tractable, Tier 1 iff
   STARK-tractable, Tier 2 iff public-general. The compiler reports the **most
   private tier a given product can honestly run at** and refuses to promise more.
4. **An honest deployment ladder.** Tier 2 now (≈ the current DrEX ring/TTC), Tier 1
   soon (the Stage-1 verified-`Cert-F` + GPU-solver + STARK-ZK engine, buildable
   with today's parts), Tier 0 frontier (the FHE PoC bounding real feasibility).
   Each rung a real shippable product, each labeled exactly.
5. **Surpass at every rung.** Tier 2 is fair-by-proof even in the open; Tier 1 is
   no worse than Penumbra/Aztec on the trust model and strictly better on speed
   (GPU), verification (`Cert-F`), and PQ; Tier 0 is the **only DEX whose no-viewer
   is adversarial** — a `t`-of-`n` threshold cryptographic bound with no standing
   master decryption key (`OUTPUT-BOUNDARY-MPC.md`), where every competitor's
   "private" tier rests on a viewer or a policy. **The single sharpest framing:**
   competitors force you to pick one privacy posture and trust their one viewer;
   DrEX makes the viewer a *dial* over one kernel whose can't-be-cheated guarantee
   never moves — and at Tier 0 shrinks it to a threshold bound, not a promise.

---

## 1. The three tiers

Privacy, mechanism-generality, and cost trade off against each other; the three
tiers are three deliberate points on that frontier, not three separate systems.

| | **Tier 0 — DARK** | **Tier 1 — SHIELDED** | **Tier 2 — OPEN** |
|---|---|---|---|
| **Privacy posture** | **Adversarial no-viewer.** No solver or enclave ever sees an order; against the parties, a **`t`-of-`n` threshold cryptographic bound** (not a policy claim). | **Private-from-the-world.** The proof reveals nothing; the solver/prover sees plaintext. | **Public.** Orders are visible; no privacy. |
| **Who sees an order** | *Nobody below the threshold* — inputs stay encrypted; the crossing runs in output-boundary MPC and only `(p*,V*)` opens. `≥ t` colluding parties can reconstruct (the honest caveat). | The solver/prover (one computing party), plus whatever the transcript is *proved* to hide from everyone else. | Everyone. |
| **Crypto carrier** | Additive RLWE/BFV fold + **output-boundary MPC** among the federation parties revealing only `(p*,V*)`; no standing master decryption key; PQ by construction (lattice/LWE). | STARK-ZK (Poseidon2/FRI, statistical-ZK hiding PCS) + PQ hash-commitment (Option A). | STARK of correctness over a public book. |
| **Mechanism** | The FHE-tractable core: uniform-price aggregation (fold + one crossing) + the `Cert-F` convex engine, "matrices public, data encrypted." | The same aggregation/convex core, **richer** — the solver sees plaintext, so more products and richer clearing. | The **full** general intent-matcher: multilateral ring/TTC, Johnson cycles, any intent. |
| **Cost / cadence** | Highest; periodic batch (minute cadence, bounded N per pair). | Fast (GPU), cheap. | Cheapest, near-real-time. |
| **Generality** | Narrowest (bounded by the FHE envelope). | Broad (the convex-program product factory). | Widest (any intent the matcher expresses). |
| **For whom** | Those who *need* no-viewer: institutional dark flow, censorship-resistant trading. | Most people. | Those who do not need privacy and want maximum generality. |
| **Grade** | **Frontier** — FHE PoC bounds feasibility (`DREX-NO-VIEWER-SURPASS.md`). | **Building** — the Stage-1 engine, buildable from today's parts. | **Now** — ≈ the current DrEX. |

### Tier 0 — DARK (no-viewer)

The clearing runs **entirely on ciphertexts**. Traders post encrypted orders; the
additive RLWE/BFV fold aggregates them into an encrypted demand/supply curve; and
at the **output boundary** the `n` federation parties partial-decrypt only the
aggregate into additive secret shares and compute the crossing `p* = argmax_j
min(D[j],S[j])` in a **secret-shared MPC that reveals only `(p*, V*)`** — never an
order, never a curve coefficient (`OUTPUT-BOUNDARY-MPC.md`). This is the mechanism
the `fhEgg` kernel makes tractable: a uniform-price call auction is an
**aggregation, not a matching** (`FHEGG-KERNEL.md §2`) — an `O(N)` bootstrap-free
homomorphic fold into a price-indexed curve plus an `O(K)` crossing — so private
clearing lives in the *cheap half* of FHE, and the `Cert-F` convex engine extends
it to the "matrices public, data encrypted" regime (`PRIVATE-CONVEX-ENGINE.md`).

**Surpass, stated honestly.** No other DEX makes no-viewer *adversarial*. Penumbra's
committee decrypts the batch aggregate; Renegade's relayer pair holds the secret
shares and computes the match; Aztec's sequencer sees ordering; CoW's solvers see
every signed order. Tier 0's no-viewer is a **`t`-of-`n` threshold cryptographic
bound**: below the threshold, no coalition of parties learns any order — by the
math, not by policy — and there is **no standing master decryption key** (the load-
bearing contrast: a plain threshold-FHE committee holds a key that decrypts *any*
order ciphertext, so its "no-viewer" is only a policy choice). It is post-quantum by
construction (FHE is lattice/LWE). The honest caveat is stated with the claim (below).

**Honest bound (no overclaim).** The FHE performance envelope is real and it
bounds Tier 0. From `DREX-NO-VIEWER-SURPASS.md`: uniform-price FHE clearing is
tractable at **N ≈ 32–512 orders per pair at minute cadence** on one server today
(the additive BFV fold is sub-10 ms, `ADDITIVE-FOLD-ENVELOPE.md`; the output-boundary
MPC crossing is ~1–7 ms, `OUTPUT-BOUNDARY-MPC.md §7`); it **breaks** at N in the
thousands. Tier 0 is the uniform-price / `Cert-F`-convex product — *not* the
graph-hard multilateral ring, which is not FHE-computable and stays at Tier 1/2.

**The threshold model, stated precisely (no overclaim).** The no-viewer is a
`t`-of-`n` bound, and correctness and privacy are stated separately:

- *Below the threshold* (`< t` colluding parties): privacy is **cryptographic and
  unconditional** — no coalition learns any order or curve coefficient, only the
  revealed `(p*, V*)` (`OUTPUT-BOUNDARY-MPC.md §3`; the PoC demonstrates two books
  with the same `(p*,V*)` yield indistinguishable party views).
- *At or above the threshold* (`≥ t` colluding parties): they **can** reconstruct
  the shares (and, holding the key shares, could partial-decrypt orders). This is
  the honest ceiling — **"nobody even if all collude" is impossible** for clearing
  over hidden data. What output-boundary MPC removes is the *standing* liability: no
  reusable master key against order ciphertexts, and the revealed function is fixed
  to `(p*,V*)` by the protocol, so the trust is one threshold, one clearing.
- *Correctness* is a separate axis: a malicious party can force a *wrong* `p*`/`V*`,
  which the STARK boundary check catches (the comparator is outside the soundness
  TCB) — an integrity fault, not a privacy break.

End-to-end PQ additionally requires the `PQ-SHIELDED-COMMITMENT.md` DLog→Poseidon2
cutover on the settlement path.

### Tier 1 — SHIELDED (private-from-the-world)

The clearing runs in the clear for **one computing party** (the solver/prover),
and the **public transcript reveals nothing** to everyone else: value, owner, key,
Merkle path, offer/want, and allocation live only in the STARK witness under the
hiding PCS, and only `[nullifier, merkle_root, value_binding]` per leg is exposed.
The mechanism is the same aggregation/convex core as Tier 0 but **richer** —
because the solver sees plaintext, it can run the full convex product factory
(`PRIVATE-CONVEX-ENGINE.md §3`) and the general partial-fill ring — at GPU speed
and low cost. This is the Stage-1 engine being built.

**Surpass.** On the *trust model*, Tier 1 is **no worse** than Penumbra or Aztec —
they have a computing/decrypting viewer too (a committee; a sequencer), and so does
Tier 1 (the solver). On everything else it is **strictly better**: faster (GPU
STARK proving vs. their paths), better *verification* (the `Cert-F`/duality-gap
certificate is a cheap linear check that attests the result was fair and optimal —
translation validation, not "trust the solver"), and **post-quantum** (Poseidon2/FRI
+ the Option-A hash-commitment) where Penumbra, Aztec, Renegade, and CoW are all
classical.

**Honest label (no dark-washing).** Tier 1 is **not** Tier 0. The solver sees
plaintext orders; Tier 1's privacy is "the *world* learns nothing from the proof,"
not "*nobody* ever sees an order." Selling Tier 1 as no-viewer would be a lie the
architecture specifically refuses. And the clearing-level *reveal-nothing theorem*
(the transcript is provably independent of the trades, with a named statistical-ZK
floor for the deployed hiding FRI) is the **crux RESEARCH item** of
`SHIELDED-DREX-ASSURANCE-ROADMAP.md` component 3 — today Tier 1 is private *by
construction* (plaintext never leaves the witness; minimal PIs) with the hiding
property tested at the PCS layer; the reveal-nothing theorem is named, not yet
discharged.

### Tier 2 — OPEN (public, general)

No privacy: the book is public and the clearing is a STARK of correctness over it.
The mechanism is the **full general intent-matcher** — multilateral ring/TTC
(`solver.rs`: Johnson elementary-circuits + Shapley–Scarf top-trading-cycles),
partial fills, any intent the matcher expresses. It is the cheapest, most general,
near-real-time tier, and it is ≈ the DrEX that exists today.

**Surpass.** Even fully public, Tier 2 is **fair-by-proof**: the uniform-price
no-arbitrage / envy-free / optimality guarantee is machine-checked
(`uniform_price_optimal`, `uniform_price_no_arbitrage`, `uniform_price_envy_free`
in `Market/Optimality.lean`), the ring clears conserving + individually-rational
through the verified executor (`ringClearing_conserves`, `cycle_individuallyRational`),
and no batch can mint (`mint_refused`, the in-AIR conservation gate). A public DrEX
is not a public *unfair* DrEX — the fairness and no-mint properties hold in the open
exactly as they do under privacy, because they are the *same kernel* (§2). Contrast
CoW, where solvers see every order and there is no correctness proof of the clearing.

---

## 2. One kernel, three postures (the load-bearing insight)

The three tiers are **not** three exchanges. They are three privacy postures over
**one verified soundness kernel**. The kernel is the machine-checked core that says
a clearing is fair, conserving, mints nothing, and carries a proof-carrying
receipt — and that core is **identical at every tier**. Only the privacy carrier,
the mechanism-generality, and the cost change.

The shared kernel, all in `metatheory/Market/` + the shielded/turn layers, all
machine-checked at model/spec scope (grades per the source docs):

| Kernel guarantee | Theorem (file) | Same at every tier because |
|---|---|---|
| Clearing **is** Σ-balance (fair clearing) | `exact_clears_iff` (`Clearing.lean`) | clearability is an algebraic fact about the book, independent of who can see it |
| Additive homomorphism (the fold distributes) | `toBal_mul` (`Clearing.lean`) | Σ distributes over the fold whether the addends are public, committed, or encrypted |
| Per-asset conservation (no value leaks) | `clearing_conserves_per_asset`, `ringClearing_conserves` (`Clearing.lean`) | conservation is a ledger equation, tier-independent |
| No mint | `mint_refused` (`Clearing.lean`) + the in-AIR conservation gate | a non-conserving batch is refused/UNSAT regardless of visibility |
| Aggregation faithfulness (no drop/insert/reorder) | `aggregate_sound`, `pool_as_perm` (`Aggregation.lean`) | the fold is a commutative monoid; order-independence is intrinsic |
| Uniform-price optimality (no-arbitrage, envy-free) | `uniform_price_optimal` + siblings (`Optimality.lean`) | `p*` is a market fact, not anyone's private input |
| Conserve on commitments, decrypt nothing | `created_value_conservation`, `shielded_ring_clears` (`ShieldedValue.lean`, `ShieldedClearing.lean`) | the conservation check runs *on the commitments* — the plaintext is never needed |
| The optimality **certificate** (`Cert-F`) | duality/Fenchel-gap linear check (`PRIVATE-CONVEX-ENGINE.md §2.3`) — RESEARCH IR | the gap is a linear functional; the same cheap check certifies at every tier |
| The turn-kernel receipt | the fold-recursion apex (`accumulator.rs`, `joint_turn_aggregation.rs`) | every clearing folds into one proof exactly as turns do |

**What the tiers change, and only this:**

- **Privacy carrier.** Tier 0 wraps the addends in FHE ciphertexts and
  threshold-decrypts only `p*`. Tier 1 wraps them in the STARK witness under the
  hiding PCS and exposes minimal PIs. Tier 2 leaves them public. The *fold and the
  crossing are the same operation* — `⊕` is homomorphic addition over Pedersen /
  lattice-ciphertext / field / plaintext respectively (`FHEGG-KERNEL.md §2.1`).
- **Mechanism-generality.** Tier 0 is bounded to what FHE can compute (uniform-price
  + `Cert-F` convex); Tier 1 adds everything the solver can see to do (the convex
  factory, the partial-fill ring); Tier 2 adds the full graph-hard matcher.
- **Cost.** FHE > STARK-GPU > public.

Because the can't-be-cheated guarantee lives entirely in the shared kernel, **it is
the same everywhere**: a Tier-2 public trade and a Tier-0 dark trade are equally
un-mintable, equally fair, equally conserving, equally proof-carrying. The user
picks a *privacy posture*, not a *different set of guarantees*.

**The honesty discipline that comes with it.** Each tier's privacy label is
**exactly what it is**. Tier 0 is no-viewer and is sold as no-viewer. Tier 1 is
private-from-the-world-but-the-solver-sees, and is sold as exactly that — never as
Tier 0. Tier 2 is public, and is sold as public-but-fair-by-proof. The shared
kernel is what makes this honest labeling *cheap*: because the soundness guarantee
does not vary, the only thing a tier's label has to state precisely is its
**privacy**, and there is never a reason to blur it.

---

## 3. The tier is a type in `fhIR`

`fhIR` is the typed order/product DSL whose organizing theorem is **"admissible iff
it compiles / passes the resource manifest"** (`FHEGG-PRODUCT-ORDER-FRONTIER.md`
headline — a six-part admissibility theorem, flagged there as a **named research
target**, not a discharged proof). The tiered architecture is the elegant reading
of that theorem:

> **A product is admissible AT TIER T iff it compiles at tier T.**

- **Tier 0 admissible** iff the product is **FHE-tractable** — its compiled form is
  a public matrix + data-independent iteration + one packable prox, inside the FHE
  envelope (bounded N, price resolution K, precision bits). "Matrices public, data
  encrypted," `Cert-F` certificate cheap.
- **Tier 1 admissible** iff the product is **STARK-tractable** — its compiled form is
  a bounded, oblivious (or solver-visible) circuit the hiding STARK can carry.
- **Tier 2 admissible** iff the product is **public-general** — expressible to the
  general matcher at all.

Admissibility is monotone the easy way: Tier-0-admissible ⇒ Tier-1-admissible ⇒
Tier-2-admissible (more visibility only ever *adds* expressible mechanisms). So the
compiler computes, for any product, the **most private tier it can honestly run
at** — and **refuses to promise more privacy than the math delivers** (a product
that needs a private Hessian, an unapproved cone, or endogenous integrality simply
fails the Tier-0 typecheck and is offered at the tier it *does* compile to). This is
the honest-labeling discipline of §2, mechanized: the type system, not marketing,
decides the privacy label.

Mapping the built + designed product surface to its tier (grades from
`FHEGG-PRODUCT-ORDER-FRONTIER.md` and `PRIVATE-CONVEX-ENGINE.md`):

| Product | Compiled form | Most-private tier | Note |
|---|---|---|---|
| Uniform-price call auction | fold + one crossing (`T=1`) | **Tier 0** | the `fhEgg` base case; FHE-tractable at N ≤ few-hundred/pair |
| `Cert-F` convex clearing (volume-max circulation, `[0,1]` partial-fill) | oblivious PDHG, public `A`, `Cert-F` gap | **Tier 0** (small) / **Tier 1** (scale) | matrices public, data encrypted; scale is the FHE frontier |
| `Price-Cert` derivatives (European/basket/Asian, barrier, futures, perps) | state-price LP + superhedging dual | **Tier 0/1** | one certificate for the family; American = Snell-envelope LP |
| Portfolio / Markowitz QP | ADMM/OSQP, one public KKT factor | **Tier 1** | private covariance ⇒ private matrix ⇒ off the Tier-0 public-matrix line |
| Receipt-linked orders (bracket/OCO/if-then) | turn-kernel nullifier/receipt sequencing (shared-nullifier XOR) | **Tier 1** | integer semantics compiled onto the receipt layer, not into LP binaries |
| CFMM optimal routing | convex over public pool curve | **Tier 1** | public curve, private amounts |
| Full multilateral ring / TTC (any intent) | Johnson cycles + Shapley–Scarf | **Tier 2** | graph-hard; not FHE-computable; the general matcher |
| Endogenous tranche / AON-FOK optimization / private-matrix programs | integer / private-operator | **Tier 2** | fall off the cheap cliff; offered public-general only |

**Honest flag.** `fhIR` and its admissibility theorem are a **named research target**
(the theorem *shape* is written — semantic preservation, certificate soundness, cost
bound, conditional completeness, no-wrap, leakage refinement — but not discharged),
and the `ZKOpenRel_R` categorical frame that would unify all four objects
(turn-kernel, auction, ring, convex engine) is likewise a **target with the right
objects/morphisms identified, not a proved unification** (`FHEGG-CODEX-INSIGHTS.md`
Q2; the feedback + adaptive-composition closure theorem is the open piece). The
tier-as-type story is the *product spine* the theorem is being built to justify; it
is not claimed as proved.

---

## 4. The honest deployment ladder

Each rung is a real, shippable product with an honest privacy label. Nothing here
is a leap; it is scheduled sharpening on a chosen trajectory.

| Rung | Tier | What ships | Built-state today | Difficulty · timeline |
|---|---|---|---|---|
| **Now** | **Tier 2 OPEN** | The general ring/TTC DrEX — fair-by-proof, conserving, no-mint, public book. | `solver.rs` matcher + `Market/*` proofs + settlement live/demonstrated; the current DrEX. | **Shippable now.** |
| **Soon** | **Tier 1 SHIELDED** | The Stage-1 engine: verified `Cert-F` + GPU solver + STARK-ZK clearing over hidden commitments; the private node. | 2-leg shielded ring AIR folds green with tested teeth; hiding PCS path built; N-leg (M) + partial-fill inequality (M) + accumulator bind (M) + PQ commitment cutover (mostly built) + the reveal-nothing theorem (RESEARCH) remain. | **Building** from today's parts; the reveal-nothing theorem is the crux differentiator. |
| **Frontier** | **Tier 0 DARK** | Adversarial no-viewer clearing of the uniform-price / `Cert-F` product: additive BFV fold + **output-boundary MPC** revealing only `(p*,V*)` + correctness proof. | Fold + MPC crossing PoC built + measured (`fhegg-fhe/`, `OUTPUT-BOUNDARY-MPC.md §7`: BFV fold sub-10 ms, MPC crossing ~1–7 ms, correctness == plaintext, reveal-only-`(p*,V*)` demonstrated); rides `uniform_price_optimal` (model-proved, to be ledger-realized) + the threshold partial-decrypt-into-shares + the PQ-commitment cutover. | PoC now; production partial-decrypt-into-shares + malicious-secure online + ledger-realize ~1–2 yr; succinct-for-light-clients ~2–4 yr. |

**Tie to the make-it-real state.** The private node (Tier 1) is the near build: the
shielded ring clears with only `[nf, root, vb]` exposed, and the routing tiers
(`DREX-ROUTING.md`) already run in discrete batches over hidden commitments (rung-3
`shielded_ring_clears`) so no operator peeks and there is no decrypt committee. The
open items are named there too — the cross-vault atomicity/refund escrow is the
load-bearing unbuilt piece, independent of the privacy tier. **Surpass at every
rung, labeled at every rung:** Tier 2 fair-by-proof in the open; Tier 1 strictly
better than the shielded competitors on speed/verification/PQ; Tier 0 the only
no-viewer DEX — and never is a lower rung dressed as a higher one.

---

## 5. Interchain + routing composes with the tiers

The tiers and the cross-chain routing spine (`DREX-ROUTING.md`) are **orthogonal
and composable**. Routing answers "how does foreign value enter and leave the
clearing engine across chains"; the tier answers "what does the world see of the
clearing." A cross-chain trade picks a tier independently of its custody path.

- **The ring-of-locks is tier-agnostic.** Each counterparty locks its own asset
  into its own chain's proof-gated vault (`DreggVault.sol`, `solana_trustless.rs`),
  minting a native mirror into the unified value layer; the matcher clears over the
  mirrors and each vault **releases to the ring-matched recipient gated on the
  clearing proof** — no pre-funded LP, no bridge validators. Whether that clearing
  ran Tier 0 (FHE, no-viewer), Tier 1 (shielded), or Tier 2 (public) changes only
  *what the clearing proof reveals*, not how locks are re-assigned.
- **Settlement is proof-carrying regardless.** The vault gates on the settled
  clearing root (`settleRing`/`settleDrex`, `CrossChainSettlement.lean`); the root
  is conserving and atomic (`settleRing_conserves`, `settleRing_atomic`) whatever
  tier produced it — because that is the shared kernel again (§2). A dark cross-chain
  trade and a public cross-chain trade settle through the identical proof-gated
  release.
- **So a cross-chain trade can be Tier-0/1/2 per trade.** Institutional dark flow
  can route Tier 0 across chains; most flow routes Tier 1; latency-sensitive public
  flow routes Tier 2 — over the *same* lock-mirror-clear-release lifecycle.

**Honest carry-over.** The routing frontier is unchanged by the tiers and named as
in `DREX-ROUTING.md`: cross-vault atomic release across heterogeneous chains is
RESEARCH (clearing atomicity is proved; the timeout/refund escrow is the
load-bearing unbuilt piece; a censoring destination chain is a per-chain liveness
assumption, not a validator-trust one). The tier choice does not make that easier or
harder — it is a strictly separate axis.

---

## 6. The claim, stated exactly

> **DrEX is one exchange with a privacy dial.** Three tiers — DARK (adversarial
> no-viewer: a `t`-of-`n` threshold bound), SHIELDED (private from the world, the
> solver sees), OPEN (public) — sit on one
> frontier of privacy vs. generality vs. cost, and the user, the market, or the
> individual trade picks the point. Underneath, all three run the **same verified
> soundness kernel**: fair clearing, per-asset conservation, no mint, uniform-price
> optimality, and a proof-carrying receipt are **machine-checked and identical at
> every tier** — only privacy, mechanism-generality, and cost move. The tier a
> product can run at is a **type**: the `fhIR` compiler reports the most private
> tier the math actually delivers and refuses to promise more.

Contrast, stated fairly:

- **Penumbra:** one posture, threshold committee decrypts the batch aggregate,
  classical DLog. DrEX Tier 1 matches its trust model and beats it on speed/PQ;
  DrEX Tier 0 keeps even the aggregate curve in shares and opens only `(p*,V*)` —
  and against a below-threshold coalition that is a cryptographic bound, not a
  committee's discretion.
- **Aztec:** the sequencer sees; classical. DrEX has no sighted sequencer at Tier 0.
- **Renegade:** the relayer pair holds the secret shares and computes the match;
  classical. DrEX Tier 0 computes on ciphertexts/shares — no collective plaintext
  exists below the threshold; PQ by construction.

**The honesty guards, everywhere.** Tier 0's no-viewer is **`t`-of-`n`**, not
absolute: below the threshold it is a cryptographic bound (no order or coefficient
learnable, only `(p*,V*)`), but `≥ t` colluding parties can reconstruct —
"nobody even if all collude" is impossible for clearing over hidden data, and the
claim never says otherwise (`OUTPUT-BOUNDARY-MPC.md §3`). What is removed vs. plain
threshold-FHE is the *standing* liability: no reusable master key decrypts a
submitted order. Tier 0 is also bounded by the real FHE envelope
(uniform-price / `Cert-F` product, bounded N, minute cadence; not the graph-hard
ring; end-to-end PQ needs the DLog cutover). Tier 1's solver-sees-plaintext is
stated plainly and Tier 1 is never sold as Tier 0; its clearing-level
reveal-nothing theorem is named RESEARCH, not proved. `fhIR` and `ZKOpenRel_R` are
research targets with the right shape identified, not discharged. Each tier's label
is exactly what it is — and the shared kernel is what makes that discipline free,
because the can't-be-cheated guarantee never changes across the dial.

---

## 7. See also

- `docs/deos/FHEGG-KERNEL.md` — the aggregation-monoid kernel (Tier 0's mechanism).
- `docs/deos/PRIVATE-CONVEX-ENGINE.md` — the `Cert-F` oblivious convex engine (the product factory).
- `docs/deos/FHEGG-CODEX-INSIGHTS.md` — `Cert-F`, `ZKOpenRel_R` (targets), the seven framing corrections.
- `docs/deos/FHEGG-PRODUCT-ORDER-FRONTIER.md` — `fhIR`, the admissibility theorem, `Price-Cert`, the order lattice.
- `docs/deos/DREX-NO-VIEWER-SURPASS.md` — the FHE envelope and the Tier-0 ladder.
- `docs/deos/OUTPUT-BOUNDARY-MPC.md` — the adversarial-no-viewer crossing (the
  `t`-of-`n` threshold bound, the dissolved scheme-switch seam, the built PoC).
- `docs/deos/PQ-SHIELDED-COMMITMENT.md` — the Option-A DLog→Poseidon2 cutover (the PQ binding).
- `docs/deos/SHIELDED-DREX-ASSURANCE-ROADMAP.md` — the Tier-1 build map + the reveal-nothing crux (component 3).
- `docs/deos/DREX-ROUTING.md` — the tier-agnostic ring-of-locks and its honest frontier.
- `metatheory/Market/{Clearing,Aggregation,Optimality}.lean` — the shared verified kernel.
</content>
</invoke>
