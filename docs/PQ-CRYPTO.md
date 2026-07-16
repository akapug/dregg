# The verified post-quantum / hybrid crypto stack

This is the honest map of dregg's post-quantum posture at HEAD. It has two tracks that share one
design law — **hybrid, not PQ-only**:

1. **The deployed hybrid perimeter** — every authority-bearing signature and every session KEM is a
   HYBRID: a classical component (ed25519 / X25519, hard iff discrete log is) welded to a post-quantum
   component (ML-DSA / ML-KEM, hard iff a module-lattice problem is), combined so that breaking ONE
   still leaves the other holding. This track is BUILT and machine-checked in Lean. At the
   **consensus** perimeter the hybrid is MANDATORY and fail-closed (§4); at the **turn** perimeter the
   PQ half is verified when present but not yet required (`require_pq` default off). §§1–6.
2. **The compact-future Hermine threshold quorum certificate** — a lattice threshold signature that
   drops into the hybrid's PQ slot once it earns deployment-grade maturity + audit. Verified to its
   irreducible line; §8.

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
| Hybrid signature EUF-CMA | `hybrid_secure_if_either_floor_discharged` (`ForkingDischarge.lean:458`; the fork-hypothesis form `hybrid_secure_if_either_floor`, `HybridCombiner.lean:232`, is retained for existing call sites) | **discrete-log** `SchnorrDLHard` **OR** **Module-SIS** `MSISHard` |
| — classical leg (Schnorr/ed25519) | `schnorr_euf_cma_reduces_to_dl` (`SchnorrEufCma.lean:278`) | **discrete-log** `SchnorrDLHardF` / `SchnorrCurveField.SchnorrDLHard` |
| — PQ leg (ML-DSA) | `pq_euf_cma_grounded_in_msis_discharged` (`ForkingDischarge.lean:323`; fork-hypothesis form at `HybridCombiner.lean:207`) | **Module-SIS** `Lattice.MSISHard` |
| Hybrid KEM IND-CCA (X-Wing) | `hybrid_kem_ind_cca_if_either` (`HybridCombiner.lean:425`) | **MLWE** (pq leg) **OR** X25519 IND-CCA (**discrete-log**), under the **dual-PRF** assumption |
| — PQ leg (ML-KEM) | `ml_kem_ind_cca_reduces_to_mlwe` (`MlKemIndCca.lean:312`) | **MLWE** `Lattice.MLWESearchHard` + the **QROM** idealisation |
| Capability chain (biscuit) soundness | `chain_unforgeable_under_hybrid_floor` (`CapabilityChain.lean:237`) | the hybrid floor: **`SchnorrDLHard ∨ MSISHard`** |
| Joint-Feldman DKG secrecy | `dkg_secrecy_reduces` (`HermineDkg.lean:233`) | info-theoretic (pigeonhole + Shamir) legs proved; **computational hiding of the short secret = MLWE/MSIS** |
| VRF leader-sortition | `sortition_{unique,fair,unpredictable}` (`SortitionGame.lean:71,124,138`) | the **VRF security properties** `UniqueOutputs` + (perfect) `Pseudorandom` |
| Hermine threshold quorum cert (compact future) | `HybridQuorum` / `HermineHybrid` (§8) | **MLWE / MSIS** (to the invertibility line) |

**Named assumptions this stack rests on** (all `Prop`, used as hypotheses, never proved — the true
floor):
- `SchnorrCurveField.SchnorrDLHard` (`SchnorrCurveField.lean:432`) — discrete-log hardness on the curve.
- `Lattice.MSISHard` (`Lattice.lean:72`) — Module-SIS, **existence-form** (see the caveat below).
- `Lattice.MLWESearchHard` (`Lattice.lean:86`) — Module-LWE (search), **existence-form** (same caveat).
- Poseidon2 / BLAKE3 collision-resistance and FRI/STARK soundness — the hash floor of the umem/proof
  side (see `docs/deos/UMEM-POSTQUANTUM.md`, `docs/reference/STARK-SOUNDNESS-CENSUS.md`), hash-based hence
  PQ-plausible.
- The named idealisations: the KEM's **dual-PRF** KDF (`DualPRF`, `HybridCombiner.lean:348`), the FO
  **QROM** (`QROMInjective`, `MlKemIndCca.lean:286`), and the VRF's **perfect Pseudorandom** game —
  standard cryptographic idealisations, stated explicitly and reduced to, NOT lattice carriers.

**⚠ The existence-form floor caveat (read before trusting the floor rows).** THREE of the named floors
are existence-form and degenerate at deployed parameters — the two lattice predicates AND the DL floor.
The two lattice predicates are stated as **existence-refutations** (`¬ ∃` a short solution / a short
`(s, e)`), and their own files doc-mark them **BROKEN / VACUOUS AT DEPLOYMENT**: at compressing
(deployed-shape) parameters a short kernel vector always EXISTS by pigeonhole, and for a genuine public
key the short `(s, e)` ARE the secret key — so `MSISHard` / `MLWESearchHard` are FALSE there, and any
theorem conditioned on them is vacuously true at those parameters (`#assert_axioms` cannot see this; a
hypothesis is not an axiom). `SchnorrCurveField.SchnorrDLHard` is degenerate in the OPPOSITE direction:
its own doc-comment marks it `⚠ DEGENERATE AT FINITE PARAMETERS` — `DLSolver` demands `solve (sk·G) =
sk` for ALL `sk : ℕ`, on any FINITE point group `sk ↦ sk·G` is non-injective, so no solver can exist
and the floor is TRIVIALLY TRUE (satisfied by the addition group, by a broken curve, by anything
finite, with zero cryptographic content); its truth tracks injectivity-over-`ℕ`, not hardness.
`CryptoFloorTeeth.lean` carries the falsifiability teeth (`not_msisHard_of_short_ball` `:101`,
`not_mlweSearchHard_of_sample` `:152`, `schnorrDLHard_of_smul_collision` `:174` — the last proves the
DL floor HOLDS on the finite `ZMod 5` toy, vacuously) and the **proper adversary-indexed floor** — a
bounded-adversary advantage ensemble (§5) with the deployed keystone re-grounded on it (§6,
`dregg_pq_game_forger_negl_under_comp_floor` `:274`). Real hardness quantifies over EFFICIENT
ADVERSARIES, never over the existence of solutions. The existence-form reductions below remain honest
as *reductions* (their extraction machinery is proved); their hypotheses discriminate only away from
deployed parameters.

---

## §1. The hybrid signature combiner — the keystone ("hybrid, not PQ-only")

`Dregg2/Crypto/HybridCombiner.lean` proves the formal content the whole hybrid claim leans on.

The hybrid signature is `hybridVerify = classical ∧ pq` (`:104`): a signature is a pair `(σc, σpq)`,
valid iff BOTH halves verify over the SAME message. The load-bearing theorem is the **projection
reduction**:

- **`hybrid_euf_cma_if_either`** (`:155`) — the hybrid is EUF-CMA-unforgeable if EITHER component is.
  PROVED unconditionally: a hybrid forgery on a fresh `m*` is a pair both of whose halves verify on
  `m*`, so projecting each coordinate yields a forgery on that component. Whichever component is
  EUF-CMA refutes its projection, so no hybrid forger exists. This is "ed25519 OR ML-DSA suffices" as
  a theorem — the "either" hypothesis is the only input, and the teeth (`:291`, `:301`) show it is
  load-bearing (one secure component blocks the hybrid; both broken ⟹ forgeable).

Each component's EUF-CMA is then anchored to a floor — **not re-asserted as a carrier**:

- **`classical_euf_cma_grounded_in_dl`** (`:183`) — given the Schnorr forking→DL reduction (discharged
  for real in §2), discrete-log hardness `SchnorrDLHard` implies the classical scheme is EUF-CMA.
- **`pq_euf_cma_grounded_in_msis`** (`:207`) — a forked ML-DSA forgery yields two SelfTargetMSIS
  solutions on a shared commitment with distinct challenges; this runs THROUGH the proved extraction
  `HermineSelfTargetMSIS.no_forgery_under_msis_selftarget`, so the only floor invoked is `MSISHard`.

- **THE KEYSTONE — `hybrid_secure_if_either_floor`** (`:232`): the `ed25519 × ML-DSA` hybrid signature
  is EUF-CMA-unforgeable if **EITHER** the discrete-log floor `SchnorrDLHard` **OR** the Module-SIS
  floor `MSISHard` holds. A quantum adversary that breaks ed25519 still faces MSIS; a lattice
  cryptanalyst that breaks ML-DSA still faces discrete log. Only if BOTH floors fall does the hybrid
  fall.

**The forking hypotheses are RETIRED — use the discharged forms.** The `dlFork`/`msisFork` inputs to
the keystone (and the `fork` input to `pq_euf_cma_grounded_in_msis`) were reduction *hypotheses*, never
wired to the proved rewind. `Dregg2/Crypto/ForkingDischarge.lean` now DERIVES them:
`fork_of_realizable` (`:310`) proves the fork type from a realizability bridge plus the forking bound,
`pq_advantage_bounded_under_msis` (`:277`) states the reduction in its honest advantage-bounded form,
and the discharged keystones are **`pq_euf_cma_grounded_in_msis_discharged`** (`:323`) and
**`hybrid_secure_if_either_floor_discharged`** (`:458`). Every protocol consumer of the keystone has a
discharged sibling in `ForkingDischargeConsumers.lean` — including
`hybrid_secure_under_msis_alone` (`:84`), the deployed post-quantum statement, which needs NO classical
model at all. The fork-hypothesis forms above are kept only for existing call sites; their files carry
`⚠ RETIRED` markers saying exactly this.

**Honest boundary (stated, not hidden):** EUF-CMA is modelled at the predicate level (the signing
oracle is the set `Q` of queried messages; `Forgery` is a fresh verifying signature; `EufCma := ¬
Forgery`), the same style `VRF.lean` / `RandomnessBeacon.lean` use — the projection reduction is
faithful without probabilistic machinery.

## §2. The classical leg, closed for real — Schnorr/ed25519 EUF-CMA ⟶ discrete log

`Dregg2/Crypto/SchnorrEufCma.lean` PROVES the content that
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

`SchnorrDLHardF` / `SchnorrDLHard` are named ASSUMPTIONS. The tooth `ex_dl_not_hard` (`:342`) refutes
`SchnorrDLHardF` — the field-scalar form this reduction uses — on the infinite toy (`S = ℚ`, `g = 1`,
where `dlog = id` solves DL), so that form is a genuine discriminating hypothesis, never `:= True`.
The curve-group form `SchnorrCurveField.SchnorrDLHard` is the opposite pole — trivially true at finite
parameters (see the floor caveat at the top and the audit note).

## §3. The hybrid KEM (X-Wing) — IND-CCA ⟶ MLWE ∨ discrete log, under a dual-PRF

`HybridCombiner.lean` PART B and `Dregg2/Crypto/MlKemIndCca.lean` cover the
`X25519 × ML-KEM` session KEM (the transport/CapTP confidentiality leg).

- The hybrid shared secret is `ss = KDF(ss_x ‖ ss_pq ‖ transcript)` (`hybridKEM`,
  `HybridCombiner.lean:360`). **`hybrid_kem_ind_cca_if_either`** (`:425`): the hybrid is IND-CCA if
  EITHER X25519 OR ML-KEM is — **provided `KDF` is a dual-PRF** (`DualPRF`, `:348`, the standard X-Wing
  requirement, stated explicitly and reduced to). The teeth (`badKDF_pq_not_propagated`, `:483`) show
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

## §4. The wire — consensus mandatory, the turn perimeter staged

**Consensus: hybrid, MANDATORY, fail-closed.** A consensus block's identity IS the hybrid: `creator =
H(ed25519 ‖ ml_dsa)` (`dregg_types::hybrid_id_commitment`, bound at block construction,
`blocklace/src/finality.rs:462`). The node's consensus ingest receives blocks through
`Blocklace::receive_block_pinned` (`finality.rs:836`), which PINS the creator's PQ half to the
committee-enrolled ML-DSA key (`Blocklace::enroll_pq`; a self-carried key is never trusted), verifies
BOTH signature halves (`Block::verify_hybrid`), and REJECTS an unenrolled creator outright
(`BlockError::UnenrolledCreator`). There is no classical-only acceptance path on the live wire — a
quantum adversary who forges the ed25519 half cannot inject a block under an enrolled identity.

**The turn perimeter: hybrid wired, PQ half staged.** `turn/src/pq.rs` is the PQ half of the HYBRID
*turn*-authorization perimeter (end-to-end quantum-safety for user/agent TURNS, not just consensus
finality):

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
  before the PQ half is mandatory (`ml_dsa_verify`, `turn/src/pq.rs:99`, never panics). Whether the PQ
  half is *required* is gated by `TurnExecutor::require_pq` (`turn/src/executor/mod.rs:1089`,
  **default off** — the one remaining staged flip on this track; consensus, above, is already
  mandatory). The flip is a human decision, and the classical `Authorization::Signature` variant stays
  valid until it lands.

**Implementation floor (not ours to prove — real, standardized crates):** ML-DSA-65 is `fips204 =
"0.4"` (`dregg-pq/src/mldsa.rs`); the X-Wing session KEM is `ml-kem = "0.2.3"` (ML-KEM-768, FIPS 203)
+ `x25519-dalek` + `hkdf` (`dregg-pq/src/hybrid_kem.rs`). Deployment-grade gaps remain a side-channel
audit and external cryptanalysis, exactly why the PQ leg lives *inside the hybrid* (hedged), never
solo.

## §5. Capability-chain (biscuit) soundness — the first protocol game on the keystone

`Dregg2/Crypto/CapabilityChain.lean` lifts the one-signature keystone to a whole
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

`Dregg2/Crypto/HermineDkg.lean` models the Rust impl
(`crypto-hermine/src/dkg.rs`, `federation/src/dkg.rs`) in Lean. Pedersen's
joint-Feldman: each member `i` shares its own secret `sᵢ` as the constant term of a degree-`(t−1)`
polynomial, broadcasts Feldman commitments `Cᵢ,ₖ = A·aᵢ,ₖ`; the final share is `xⱼ = Σᵢ fᵢ(j)`, the
group key `t = A·s = Σᵢ Cᵢ,₀`, and `s = Σᵢ sᵢ` is NEVER materialized.

- **Correctness — `dkg_group_key_eq`** (`:105`) and `dkg_shares_reconstruct` (`:116`): PROVED
  unconditional module algebra — the broadcasts assemble to `A·s`, and any `t`-subset of the final
  shares Lagrange-reconstructs `s`.
- **Feldman soundness — `dkg_share_verify_sound`** (`:141`, + `dkg_share_verify_off_poly` `:150`):
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

`Dregg2/Crypto/SortitionGame.lean` interprets a VRF output as an election ticket
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
factors, full-size external audit. `federation/src/frost.rs` carries three hybrid quorum variants:
`QuorumScheme::Hybrid` (the FROST group key + per-member ML-DSA-65 combiner),
`QuorumScheme::HybridVotes` (per-member ed25519 votes + per-member ML-DSA-65 — the deployable PQ
quorum path), and `QuorumScheme::HermineHybrid` — the ed25519 vote quorum plus ONE
committee-independent Hermine threshold certificate (no FROST, no ML-DSA in it) as a STAGED
REFERENCE: additive, default-OFF, wired into no live consensus path. The genesis generator
(`node/src/genesis.rs`) derives each validator's ML-DSA-65 key from its ed25519 seed and emits
`ml_dsa_public_key: Some(...)` plus a pinning `hybrid_id` for every validator, with the
federation_id committing to the hybrid roster (`derive_federation_id_hybrid_with_epoch`); the field
is serde-optional only for parsing pre-hybrid genesis files, matching §4's mandatory-hybrid,
fail-closed ingest.

**The irreducible line (ASSUMED, never proved — the shared floor of all lattice crypto, FIPS ML-DSA
included):** MLWE and MSIS hardness (`Lattice.MSISHard` / `MLWESearchHard` — existence-form at HEAD;
the adversary-indexed statement is in `CryptoFloorTeeth`, see the audit note). Non-Lean deployment gaps
(not ours to prove): a full side-channel audit of `crypto-hermine`, and external cryptanalysis of
Hermine — exactly why it belongs *inside the hybrid* rather than deployed solo.

---

## Audit note — no laundering, but all three existence-form floors are degenerate at deployed parameters

Against the "no named-carrier laundering" lesson (a `def FooHard` used as a hypothesis is an
assumption, not a theorem — and must be labelled so), a read of the modules finds **no laundering** —
every floor is a named hypothesis, never discharged in disguise. But labelling is not the whole
audit; the floors' TRUE resolution differs by floor:

- **`SchnorrDLHard`** (`SchnorrCurveField.lean:432`) is the third degenerate floor, in the OPPOSITE
  direction from the lattice pair: its own doc-comment marks it `⚠ DEGENERATE AT FINITE PARAMETERS`.
  `DLSolver` demands `solve (sk·G) = sk` for ALL `sk : ℕ`; on any FINITE point group `sk ↦ sk·G` is
  non-injective, so no solver can exist and the floor is TRIVIALLY TRUE — satisfied by the addition
  group, by a broken curve, by anything finite, with zero cryptographic content. Its tooth is
  `schnorrDLHard_of_smul_collision` (`CryptoFloorTeeth.lean:174`), which proves it HOLDS on the finite
  `ZMod 5` toy, vacuously; the refutation tooth `ex_dl_not_hard` (`SchnorrEufCma.lean:342`) targets the
  DIFFERENT field-scalar predicate `SchnorrDLHardF` on the infinite `ℚ` toy, where `sk ↦ sk` IS
  injective. So the keystone `hybrid_secure_if_either_floor` (`HybridCombiner.lean:232`) takes a
  classical floor that is trivially true at finite-curve parameters; the discriminating classical
  statement is the advantage-based `SchnorrDLHardF` / `ProbSchnorrFamily` form (see
  `CryptoFloorTeeth`).
- **`MSISHard` / `MLWESearchHard`** (`Lattice.lean:72,86`) are **existence-form floors, REFUTED at
  deployed-shape parameters** — their own doc-comments mark them `⚠ BROKEN / VACUOUS AT DEPLOYMENT`.
  `CryptoFloorTeeth.lean` proves it: a compressing `A` always has a short nonzero kernel vector by
  pigeonhole (`not_msisHard_of_short_ball`), and a genuine public key's short `(s, e)` exist by
  construction — they ARE the secret key (`not_mlweSearchHard_of_sample`). Theorems conditioned on
  these floors are therefore VACUOUSLY true at those parameters, and `#assert_axioms` cannot flag it
  (a hypothesis is not an axiom). The proper floor — a bounded-adversary advantage ensemble — and the
  keystone re-grounded on it live in `CryptoFloorTeeth` §§5–6
  (`dregg_pq_game_forger_negl_under_comp_floor`), with teeth showing the proper floor is both
  satisfiable and refutable.
- The reductions run through PROVED machinery, not re-asserted carriers: the PQ signature leg through
  `no_forgery_under_msis_selftarget` (and, discharged, through `ForkingDischarge`), the classical leg
  through the fully-proved Schnorr forking extraction (`SchnorrEufCma.lean`), the ML-KEM leg through
  the proved lattice core + FO simulation, the DKG secrecy legs through the proved pigeonhole + Shamir
  `t`-privacy. The extraction content is real independently of the floor-form caveat above.
- The remaining inputs are **explicitly-named idealisations / modeling boundaries**, disclosed in each
  file, NOT hidden lattice carriers: the predicate-level EUF-CMA / IND-CCA games, the KEM's dual-PRF,
  the FO QROM injectivity, and the VRF's perfect `Pseudorandom`. The full probabilistic QROM-FO
  advantage bound is honestly flagged open.

The other place to read carefully is DKG **secrecy**: `dkg_secrecy_reduces` proves info-theoretic
non-determination, and the computational hiding of the short secret is the MLWE/MSIS floor named (not
re-asserted) in the header — do not read it as an unconditional secrecy proof. That distinction is made
in §6 and is the correct, non-laundered framing.

---

## File index

`metatheory/Dregg2/Crypto/`: HybridCombiner, ForkingDischarge, ForkingDischargeConsumers,
CryptoFloorTeeth, SchnorrEufCma, MlKemIndCca, CapabilityChain, HermineDkg,
SortitionGame, VRF, RandomnessBeacon; and the Hermine stack — Frost, HermineThreshold, ShamirPrivacy,
ThresholdReduction, SchnorrExtractor, HermineExtractor, ThresholdForking, Lattice, HermineMSIS,
HermineSelfTargetMSIS, HermineTSUF, HermineDischarge, HermineConcrete, HermineLossiness,
HermineInvertibility, InvertibilityHadamard, InvertibilityTight, Smudging, HermineHiding, RenyiHiding,
GaussianRenyi, HybridQuorum, HermineHybrid.

Impl: `blocklace/src/finality.rs` (hybrid block identity + pinned reception), `turn/src/pq.rs` (turn
perimeter), `turn/src/action.rs` (`HybridSignature`),
`turn/src/executor/authorize.rs` (`require_pq`), `dregg-pq/` (ML-DSA-65 / ML-KEM-768 / X-Wing over
`fips204` + `ml-kem` + `x25519-dalek`), `crypto-hermine/`, `federation/src/{dkg,frost,vrf,beacon}.rs`.

Related docs: `docs/deos/UMEM-POSTQUANTUM.md` (the hash-based memory argument's PQ posture),
`docs/deos/VERIFIED-SURFACE-ROADMAP.md` (the DKG + hybrid-floor apex rows),
`docs/deos/RESHARING-CHAINS.md` (forward-secure committee secrets), `docs/reference/STARK-SOUNDNESS-CENSUS.md`.
