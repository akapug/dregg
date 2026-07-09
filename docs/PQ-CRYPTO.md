# The verified post-quantum / hybrid crypto stack

This is the honest map of dregg's post-quantum posture as it stands at HEAD (2026-07-09). It has two
tracks that share one design law — **hybrid, not PQ-only**:

1. **The deployable hybrid perimeter** — every authority-bearing signature and every session KEM is a
   HYBRID: a classical component (ed25519 / X25519, hard iff discrete log is) welded to a post-quantum
   component (ML-DSA / ML-KEM, hard iff a module-lattice problem is), combined so that breaking ONE
   still leaves the other holding. This track is BUILT, machine-checked in Lean, wired into the turn
   perimeter, and staged default-off. It is the subject of the new §§1–6.
2. **The compact-future Hermine threshold quorum certificate** — a lattice threshold signature that
   drops into the hybrid's PQ slot once it earns deployment-grade maturity + audit. Verified to its
   irreducible line; §7.

The **discipline of this document** is the one the "no named-carrier laundering" lesson demands: for
every scheme we state its security as **"X REDUCES TO assumption Y"** and name Y — MLWE, MSIS,
discrete log, hash collision-resistance — as the **ASSUMPTION** the whole thing rests on. A hardness
predicate (`def MSISHard : Prop`) used as a hypothesis is an **assumption, not a theorem**, and it is
labelled as such everywhere below. We never write "proven secure" unconditionally.

Every Lean keystone cited carries an in-file `#assert_axioms` / `#assert_all_clean` guard (axioms ⊆
`{propext, Classical.choice, Quot.sound}`) — the guard fails the build if a keystone is not
axiom-clean. Citations are file:line at HEAD; verify against the module.

---

## The reduction chain at a glance

Each scheme reduces to a floor; the floor is an ASSUMPTION (never discharged), stated in the last
column. "Combiner" schemes reduce to a *disjunction* of floors — they hold if EITHER floor does.

| Scheme | Lean keystone (file) | Reduces to the ASSUMPTION |
|---|---|---|
| Hybrid signature EUF-CMA | `hybrid_secure_if_either_floor` (`HybridCombiner.lean:213`) | **discrete-log** `SchnorrDLHard` **OR** **Module-SIS** `MSISHard` |
| — classical leg (Schnorr/ed25519) | `schnorr_euf_cma_reduces_to_dl` (`SchnorrEufCma.lean:278`) | **discrete-log** `SchnorrDLHardF` / `SchnorrCurveField.SchnorrDLHard` |
| — PQ leg (ML-DSA) | `pq_euf_cma_grounded_in_msis` (`HybridCombiner.lean:194`) | **Module-SIS** `Lattice.MSISHard` |
| Hybrid KEM IND-CCA (X-Wing) | `hybrid_kem_ind_cca_if_either` (`HybridCombiner.lean:406`) | **MLWE** (pq leg) **OR** X25519 IND-CCA (**discrete-log**), under the **dual-PRF** assumption |
| — PQ leg (ML-KEM) | `ml_kem_ind_cca_reduces_to_mlwe` (`MlKemIndCca.lean:312`) | **MLWE** `Lattice.MLWESearchHard` + the **QROM** idealisation |
| Capability chain (biscuit) soundness | `chain_unforgeable_under_hybrid_floor` (`CapabilityChain.lean:237`) | the hybrid floor: **`SchnorrDLHard ∨ MSISHard`** |
| Joint-Feldman DKG secrecy | `dkg_secrecy_reduces` (`HermineDkg.lean:233`) | info-theoretic (pigeonhole + Shamir) legs proved; **computational hiding of the short secret = MLWE/MSIS** |
| VRF leader-sortition | `sortition_{unique,fair,unpredictable}` (`SortitionGame.lean:71,124,138`) | the **VRF security properties** `UniqueOutputs` + (perfect) `Pseudorandom` |
| Hermine threshold quorum cert (compact future) | `HybridQuorum` / `HermineHybrid` (§7) | **MLWE / MSIS** (to the invertibility line) |

**Named assumptions this stack rests on** (all `Prop`, used as hypotheses, never proved — the true
floor):
- `SchnorrCurveField.SchnorrDLHard` (`SchnorrCurveField.lean:414`) — discrete-log hardness on the curve.
- `Lattice.MSISHard` (`Lattice.lean:69`) — Module-SIS hardness.
- `Lattice.MLWESearchHard` (`Lattice.lean:81`) — Module-LWE (search) hardness.
- Poseidon2 / BLAKE3 collision-resistance and FRI/STARK soundness — the hash floor of the umem/proof
  side (see `docs/deos/UMEM-POSTQUANTUM.md`, `docs/STARK-FLOOR.md`), hash-based hence PQ-plausible.
- The named idealisations: the KEM's **dual-PRF** KDF (`DualPRF`, `HybridCombiner.lean:329`), the FO
  **QROM** (`QROMInjective`, `MlKemIndCca.lean:286`), and the VRF's **perfect Pseudorandom** game —
  standard cryptographic idealisations, stated explicitly and reduced to, NOT lattice carriers.

---

## §1. The hybrid signature combiner — the keystone ("hybrid, not PQ-only")

`Dregg2/Crypto/HybridCombiner.lean` (commit `a875a9104`, "hybrid-combiner security +
identity-commitment binding — the floor under the whole no-pq work") proves the formal content the
whole hybrid claim leans on.

The hybrid signature is `hybridVerify = classical ∧ pq` (`:104`): a signature is a pair `(σc, σpq)`,
valid iff BOTH halves verify over the SAME message. The load-bearing theorem is the **projection
reduction**:

- **`hybrid_euf_cma_if_either`** (`:155`) — the hybrid is EUF-CMA-unforgeable if EITHER component is.
  PROVED unconditionally: a hybrid forgery on a fresh `m*` is a pair both of whose halves verify on
  `m*`, so projecting each coordinate yields a forgery on that component. Whichever component is
  EUF-CMA refutes its projection, so no hybrid forger exists. This is "ed25519 OR ML-DSA suffices" as
  a theorem — the "either" hypothesis is the only input, and the teeth (`:272`, `:287`) show it is
  load-bearing (one secure component blocks the hybrid; both broken ⟹ forgeable).

Each component's EUF-CMA is then anchored to a floor — **not re-asserted as a carrier**:

- **`classical_euf_cma_grounded_in_dl`** (`:176`) — given the Schnorr forking→DL reduction (discharged
  for real in §2), discrete-log hardness `SchnorrDLHard` implies the classical scheme is EUF-CMA.
- **`pq_euf_cma_grounded_in_msis`** (`:194`) — a forked ML-DSA forgery yields two SelfTargetMSIS
  solutions on a shared commitment with distinct challenges; this runs THROUGH the proved extraction
  `HermineSelfTargetMSIS.no_forgery_under_msis_selftarget`, so the only floor invoked is `MSISHard`.

- **THE KEYSTONE — `hybrid_secure_if_either_floor`** (`:213`): the `ed25519 × ML-DSA` hybrid signature
  is EUF-CMA-unforgeable if **EITHER** the discrete-log floor `SchnorrDLHard` **OR** the Module-SIS
  floor `MSISHard` holds. A quantum adversary that breaks ed25519 still faces MSIS; a lattice
  cryptanalyst that breaks ML-DSA still faces discrete log. Only if BOTH floors fall does the hybrid
  fall.

**Honest boundary (stated, not hidden):** EUF-CMA is modelled at the predicate level (the signing
oracle is the set `Q` of queried messages; `Forgery` is a fresh verifying signature; `EufCma := ¬
Forgery`), the same style `VRF.lean` / `RandomnessBeacon.lean` use — the projection reduction is
faithful without probabilistic machinery. The `dlFork`/`msisFork` inputs to the keystone are
*reduction hypotheses*, each a theorem proved by the existing forking/extraction machinery (the pq one
inline through `no_forgery_under_msis_selftarget`; the classical one in §2), never a hardness carrier.

## §2. The classical leg, closed for real — Schnorr/ed25519 EUF-CMA ⟶ discrete log

`Dregg2/Crypto/SchnorrEufCma.lean` (commit `db1214a9f`) PROVES the content that
`classical_euf_cma_grounded_in_dl` takes as a bare `fork` hypothesis — the classical mirror of the
lattice SelfTargetMSIS argument:

- **`schnorr_forking_extracts_dl`** (`:129`) — two accepting Schnorr transcripts on a common nonce `R`
  with distinct challenges `c ≠ c'` extract the discrete log `pk = ((s−s')/(c−c'))·g` (the verify
  equations subtract to cancel `R`; `c−c' ≠ 0` is a field unit). Extraction is FREE from `c ≠ c'`.
- **`schnorr_sim_verifies`** (`:113`) — the signing oracle is HVZK / secret-free: the reduction
  answers every CMA signing query from the public key alone (program `c`, output `R := s·g − c·pk`), so
  a CMA forger is a bare-game forger. The rewind (`SchnorrForger.rewind`), the shared-nonce
  preservation (`fork_preserves_commitment`, DERIVED), and the forking probability
  (`schnorr_fork_probability_bound`, reusing `HermineTSUF.forking_probability_bound`) are all PROVED.
- **`schnorr_euf_cma_reduces_to_dl`** (`:278`) — **the reduction**: if discrete log is hard
  (`SchnorrDLHardF g`, the field-scalar form of `SchnorrCurveField.SchnorrDLHard`, `:239`), NO Schnorr
  forger exists. `hybrid_classical_leg_grounded_in_dl` (`:313`) is the discharged classical disjunct of
  the keystone.

`SchnorrDLHardF` / `SchnorrDLHard` is a named ASSUMPTION — the teeth (`ex_dl_not_hard`, `:342`) show
it is FALSE on the degenerate curve `g = 1`, so it is a genuine discriminating hypothesis, never
`:= True`.

## §3. The hybrid KEM (X-Wing) — IND-CCA ⟶ MLWE ∨ discrete log, under a dual-PRF

`HybridCombiner.lean` PART B and `Dregg2/Crypto/MlKemIndCca.lean` (commit `38e83fac8`) cover the
`X25519 × ML-KEM` session KEM (the transport/CapTP confidentiality leg).

- The hybrid shared secret is `ss = KDF(ss_x ‖ ss_pq ‖ transcript)` (`hybridKEM`,
  `HybridCombiner.lean:341`). **`hybrid_kem_ind_cca_if_either`** (`:406`): the hybrid is IND-CCA if
  EITHER X25519 OR ML-KEM is — **provided `KDF` is a dual-PRF** (`DualPRF`, `:329`, the standard X-Wing
  requirement, stated explicitly and reduced to). The teeth (`badKDF_pq_not_propagated`, `:464`) show
  the dual-PRF is load-bearing: a single-keyed combiner inherits security from only one fixed
  component.
- **`ml_kem_ind_cca_reduces_to_mlwe`** (`MlKemIndCca.lean:312`) discharges the ML-KEM leg to the
  lattice floor. The lattice core is proved: `ciphertext_is_masked_mlwe` (`:99`, the ciphertext minus
  the message IS an MLWE sample), `ind_cpa_reduces_to_mlwe` (`:149`, an IND-CPA distinguisher IS a
  decisional-MLWE distinguisher via the additive message-shift), and `pke_key_recovery_reduces_to_mlwe`
  (`:121`). The FO transform's decapsulation oracle is proved secret-free
  (`decaps_oracle_simulable`, `:245`: real decaps = a public-data-only simulator).

**Reduces to the ASSUMPTION `Lattice.MLWESearchHard`** plus **two explicitly-named idealisations**:
the **QROM** (`QROMInjective H := Function.Injective H`, `:286` — the random-oracle collision-freeness
proxy) and the **dual-PRF** KDF. **Honestly open:** the FULL probabilistic QROM FO reduction
(advantage bookkeeping, oracle reprogramming) is beyond this Prop-level model — captured structurally
by the decaps-oracle simulation, NOT proved probabilistically. No fresh `…Hard` carrier is introduced;
the lattice content bottoms out at MLWE for real.

## §4. The turn perimeter — where the hybrid signature is wired, staged default-off

`turn/src/pq.rs` is the PQ half of the HYBRID *turn*-authorization perimeter (end-to-end
quantum-safety for user/agent TURNS, not just consensus finality):

- **`Authorization::HybridSignature`** (`turn/src/action.rs:457`) carries `{ ed25519, ml_dsa,
  ml_dsa_pk }`. Both halves cover the SAME canonical signing message; a hybrid authorization verifies
  only when **`classical ∧ pq`** — forging a turn requires breaking ed25519 discrete-log AND
  module-lattice SIS/LWE simultaneously (exactly the §1 keystone, at the wire).
- **Deterministic derivation** (`MlDsaTurnKey::from_ed25519_seed`, `turn/src/pq.rs:65`, FIPS 204
  `ML-DSA.KeyGen(ξ = seed)`): the ML-DSA key derives from the same 32-byte ed25519 seed, so
  cipherclerk / node / genesis agree on the PQ public key with no separate ceremony. Domain-separated
  by `HYBRID_TURN_PQ_CTX = b"dregg-hybrid-turn-v1"` (`:37`), distinct from the consensus quorum ctx.
- **Staged, fail-CLOSED** (`turn/src/executor/authorize.rs:1054,1064`): the client always signs both
  halves; the verifier checks the PQ half when present and REJECTS a present-but-invalid PQ half even
  before the PQ half is mandatory (`ml_dsa_verify`, `turn/src/pq.rs:88`, never panics). Whether the PQ
  half is *required* is gated by `TurnExecutor::require_pq` (**default off**), matching the consensus
  HybridPq default-off rollout — the flip is a human decision, and the classical `Authorization::
  Signature` variant stays valid throughout the rollout.

**Implementation floor (not ours to prove — real, standardized crates):** ML-DSA-65 is `fips204 =
"0.4"` (`dregg-pq/src/mldsa.rs`); the X-Wing session KEM is `ml-kem = "0.2.3"` (ML-KEM-768, FIPS 203)
+ `x25519-dalek` + `hkdf` (`dregg-pq/src/hybrid_kem.rs`). Deployment-grade gaps remain a side-channel
audit and external cryptanalysis, exactly why the PQ leg lives *inside the hybrid* (hedged), never
solo.

## §5. Capability-chain (biscuit) soundness — the first protocol game on the keystone

`Dregg2/Crypto/CapabilityChain.lean` (commit `cc99ab01c`) lifts the one-signature keystone to a whole
credential *chain* — a root-keyed biscuit whose blocks each carry the next block's key and are signed
by the current key:

- **`chain_unforgeable_under_eufcma`** (`:168`) — SOUNDNESS: if every honest key is EUF-CMA, every
  `VerifyChain`-accepting credential rooted at an honest key was entirely honestly signed. A forged
  accepting chain would exhibit a fresh valid signature under an honest parent key — a `Forgery`
  refuting that key's `EufCma`.
- **`chain_only_attenuates`** (`:210`) — ATTENUATION-ONLY (PROVED unconditionally): a valid chain's
  leaf authority ≤ root authority; offline delegation can only SHRINK authority, never amplify.
- **`chain_unforgeable_under_hybrid_floor`** (`:237`) — the chain's signatures ARE the hybrid
  signatures, so each honest key's EUF-CMA is DISCHARGED by `hybrid_secure_if_either_floor`. **Chain
  soundness reduces to `SchnorrDLHard ∨ MSISHard`** through the combiner — break one component, the
  other still holds.

## §6. The DKG — joint-Feldman, no trusted dealer, now modelled in Lean

`Dregg2/Crypto/HermineDkg.lean` (commit `f59fab338`) closes the gap where the Rust impl
(`crypto-hermine/src/dkg.rs`, `federation/src/dkg.rs`) ran ahead of the metatheory. Pedersen's
joint-Feldman: each member `i` shares its own secret `sᵢ` as the constant term of a degree-`(t−1)`
polynomial, broadcasts Feldman commitments `Cᵢ,ₖ = A·aᵢ,ₖ`; the final share is `xⱼ = Σᵢ fᵢ(j)`, the
group key `t = A·s = Σᵢ Cᵢ,₀`, and `s = Σᵢ sᵢ` is NEVER materialized.

- **Correctness — `dkg_group_key_eq`** (`:105`) and `dkg_shares_reconstruct` (`:116`): PROVED
  unconditional module algebra — the broadcasts assemble to `A·s`, and any `t`-subset of the final
  shares Lagrange-reconstructs `s`.
- **Feldman soundness — `dkg_share_verify_sound`** (`:141`, + `dkg_share_verify_off_poly` `:147`):
  PROVED — a share passing `A·share = Σₖ jᵏ·Cᵢ,ₖ` IS the committed evaluation (mod `ker A`), so a
  cheating dealer's off-polynomial share is CAUGHT (matching Rust `verify_dkg_share`).
- **Secrecy — `dkg_secrecy_reduces`** (`:233`): a COMPOSITION, honestly reduced. It exhibits two
  distinct group secrets that reproduce a `t`-minority's ENTIRE view, from two legs, and **neither leg
  is an invented carrier**: the key-hiding leg (`dkg_collision_of_lossiness`, `:163`) is DISCHARGED
  from the proved pigeonhole `HermineLossiness.lossiness_of_card_lt`; the share-consistency leg
  (`dkg_shamir_leg`, `:208`) is DISCHARGED from the proved `ShamirPrivacy.shamir_t_privacy`.
  `secrecy_nonvacuous` (`:349`) composes both on a concrete compressing `ℚ² → ℚ` instance so the
  composition is not vacuous.

  **The honest floor, named not laundered:** what is PROVED is information-theoretic
  *non-determination* of the group secret. The **computational hiding of the SHORT secret is the
  separate MLWE/MSIS floor** (`Lattice.lean`), stated in the file header and explicitly NOT re-asserted
  here. DKG secrecy therefore reduces to MLWE/MSIS for computational hiding, on top of the two proved
  info-theoretic legs — it is not claimed as an unconditional secrecy proof.

## §7. VRF leader-sortition — fair, unpredictable, unique from the VRF properties

`Dregg2/Crypto/SortitionGame.lean` (commit `5baae1f25`) interprets a VRF output as an election ticket
(`elected := VRF(sk, epoch) < thr`) and DERIVES the sortition guarantees from `VRF.lean`'s own
security — no new carrier:

- **`sortition_unique`** (`:71`) — two verifying election claims for one `(pk, epoch)` force the SAME
  output (no grind, no double-claim). Directly `VRF.uniqueness_at_most_one` from the `UniqueOutputs`
  property; `double_claim_refutes_uniqueness` (`:84`) states the "Breaking X-VRF" failure as a
  refutation, showing uniqueness is load-bearing.
- **`sortition_fair`** (`:124`) and **`sortition_unpredictable`** (`:138`) — under `Pseudorandom V`,
  an honest validator is elected with exactly the uniform base rate `thr/|Output|`, and no `sk`-free
  predictor beats that rate.

**Reduces to the ASSUMPTIONS** `UniqueOutputs` and `Pseudorandom` (the VRF security properties). Note
`Pseudorandom` here is the *perfect* indistinguishability game — an idealisation stated as the modeling
boundary, not a probabilistic advantage bound.

---

## §8. The compact-future path — Hermine threshold quorum certificate

One deployable-now path (the FIPS hybrid above); one compact future. **Hermine** is a lattice
threshold signature yielding ONE `~3 KB` quorum certificate regardless of committee size, verified to
the irreducible line — it drops into the hybrid's PQ slot once it earns deployment-grade maturity +
audit.

**Machine-checked (Lean).** The threshold quorum-cert ladder (classical FROST and PQ Hermine, one
proof shape): correctness (`Frost`, `HermineThreshold`), t-privacy (`ShamirPrivacy` — a corrupt
minority learns nothing, unconditional), threshold-EUF-CMA reduces to single-signer
(`ThresholdReduction`), the special-soundness extractors (`SchnorrExtractor`, `HermineExtractor`), and
the capstone `ThresholdForking` (a forked forger hands you the group secret / an MSIS preimage).

**Hermine unforgeability, to the line** (`Lattice`, `HermineMSIS`, `HermineDischarge`): a forked
forgery yields a genuine MSIS solution — short, in-kernel, and nonzero (`u ≠ 0` **discharged** from
MLWE lossiness + challenge invertibility, not assumed). `MSISHard ⟹ no forgery`. Lossiness is proved
by pigeonhole (`HermineLossiness`); invertibility is proved general-n
(`InvertibilityHadamard.norm_lt_isUnit`: for any n=2^k and any prime q, a nonzero `v` with `‖v‖₂ⁿ < q`
is a unit — via a self-proved Hadamard determinant bound Mathlib lacks) and the tight
Lyubashevsky–Seiler `q^(d/n)` threshold is ALSO proved (`InvertibilityTight.norm_lt_isUnit_tight`).
Both are welded into `HermineDischarge`. The single honest edge that remains is the general
degree-d≥2 min-norm factor case (needs the LS complex-resultant bound, no Mathlib infra) — everything
provable with current tooling is proved.

**The hybrid at Hermine's verifier** (`HybridQuorum`, `HermineHybrid`): `hybridVerify = classical ∧
pq`, unforgeable if EITHER half holds, surviving a total classical break (ed25519 to Shor) while the
PQ half holds.

**Implemented + tested.** `crypto-hermine/` — `R_q = ℤ_q[X]/(Xⁿ+1)` (n=256 production dimension,
Dilithium prime, NTT `O(n log n)` verified against schoolbook), `verify` symbol-for-symbol with the
Lean spec, trusted-dealer threshold + the joint-Feldman DKG of §6, uniform and discrete-Gaussian
noise-flooding, a ChaCha20 CSPRNG driving a constant-time sampler. Deployment-grade gaps: RFC binding
factors, full-size external audit. `federation/src/frost.rs` + `node.rs` + genesis — the FROST+ML-DSA-65
hybrid QC wired into consensus, additive and default-OFF.

**The irreducible line (ASSUMED, never proved — the shared floor of all lattice crypto, FIPS ML-DSA
included):** MLWE and MSIS hardness (`Lattice.MSISHard` / `MLWESearchHard`). Non-Lean deployment gaps
(not ours to prove): a full side-channel audit of `crypto-hermine`, and external cryptanalysis of
Hermine — exactly why it belongs *inside the hybrid* rather than deployed solo.

---

## Audit note — every floor is a genuine assumption, not a relabeled hypothesis

Against the "no named-carrier laundering" lesson (a `def FooHard` used as a hypothesis is an
assumption, not a theorem — and must be labelled so), a read of the six modules finds **no laundering**:

- The three hardness floors are named `Prop` predicates used only as hypotheses, never discharged:
  `SchnorrDLHard` (`SchnorrCurveField.lean:414`), `MSISHard` (`Lattice.lean:69`), `MLWESearchHard`
  (`Lattice.lean:81`). Each is shown non-vacuous (it CAN be false — e.g. `ex_dl_not_hard` on the
  degenerate curve), so it is a genuine discriminating assumption, not `:= True`.
- The reductions run through PROVED machinery, not re-asserted carriers: the PQ signature leg through
  `no_forgery_under_msis_selftarget`, the classical leg through the fully-proved Schnorr forking
  extraction (`SchnorrEufCma.lean`), the ML-KEM leg through the proved lattice core + FO simulation,
  the DKG secrecy legs through the proved pigeonhole + Shamir `t`-privacy.
- The remaining inputs are **explicitly-named idealisations / modeling boundaries**, disclosed in each
  file, NOT hidden lattice carriers: the predicate-level EUF-CMA / IND-CCA games, the KEM's dual-PRF,
  the FO QROM injectivity, and the VRF's perfect `Pseudorandom`. The full probabilistic QROM-FO
  advantage bound is honestly flagged open.

The one place to read carefully is DKG **secrecy**: `dkg_secrecy_reduces` proves info-theoretic
non-determination, and the computational hiding of the short secret is the MLWE/MSIS floor named (not
re-asserted) in the header — do not read it as an unconditional secrecy proof. That distinction is made
in §6 and is the correct, non-laundered framing.

---

## File index

`metatheory/Dregg2/Crypto/`: HybridCombiner, SchnorrEufCma, MlKemIndCca, CapabilityChain, HermineDkg,
SortitionGame, VRF, RandomnessBeacon; and the Hermine stack — Frost, HermineThreshold, ShamirPrivacy,
ThresholdReduction, SchnorrExtractor, HermineExtractor, ThresholdForking, Lattice, HermineMSIS,
HermineSelfTargetMSIS, HermineTSUF, HermineDischarge, HermineConcrete, HermineLossiness,
HermineInvertibility, InvertibilityHadamard, InvertibilityTight, Smudging, HermineHiding, RenyiHiding,
GaussianRenyi, HybridQuorum, HermineHybrid.

Impl: `turn/src/pq.rs` (turn perimeter), `turn/src/action.rs` (`HybridSignature`),
`turn/src/executor/authorize.rs` (`require_pq`), `dregg-pq/` (ML-DSA-65 / ML-KEM-768 / X-Wing over
`fips204` + `ml-kem` + `x25519-dalek`), `crypto-hermine/`, `federation/src/{dkg,frost,vrf,beacon}.rs`.

Related docs: `docs/deos/UMEM-POSTQUANTUM.md` (the hash-based memory argument's PQ posture),
`docs/deos/VERIFIED-SURFACE-ROADMAP.md` (the DKG + hybrid-floor apex rows),
`docs/deos/RESHARING-CHAINS.md` (forward-secure committee secrets), `docs/STARK-FLOOR.md`.

Commits: `a875a9104` (hybrid combiner keystone), `db1214a9f` (Schnorr→DL), `38e83fac8` (ML-KEM→MLWE
FO), `cc99ab01c` (capability chain), `5baae1f25` (VRF sortition), `f59fab338` (joint-Feldman DKG in
Lean).
