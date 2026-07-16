# The Verified-Light-Client Fold PILOT — EVM-MPT inclusion as the rung-3 custom leaf

**The rung-2 → rung-3 pilot for folding ONE verified light-client verification as a
recursion-foldable `CellProgram` custom leaf, grounded in the deployed DECO/custom precedent.
Stage P0 is BUILT: `circuit-prove/src/mpt_holding_leaf.rs` (the MPT holding-commitment leaf)
with the end-to-end test `circuit-prove/tests/mpt_holding_fold_pilot.rs`. Stages P1
(rules-in-AIR) and P2 (TID_KECCAK) remain open, staged below.**

Companion to `docs/deos/VERIFIED-LIGHTCLIENT-FOLD-PATH.md` (the fold-path map). That doc maps
the road for any chain; this doc picks the pilot chain, sequences the increments, and corrects
one stale blocker in the map (§2, Route A — the multi-chunk PI sponge is CLOSED at HEAD).

---

## 1. THE PILOT CHOICE: EVM-MPT / keccak state-inclusion (`LightClientMpt.lean`)

Fold **EVM state inclusion** (EIP-1186 ERC-20 holding proofs) first — the verification whose
Lean lane is `metatheory/Dregg2/Bridge/LightClientMpt.lean` and whose Rust spec is
`eth-lightclient/src/evm.rs::verify_erc20_holding` (`evm.rs:167`). The constraint-cost
rationale, against the census numbers (BLS12-381 pairing ≈ millions of R1CS; Ed25519 ≈ 2–3M
per signature; keccak ≈ ~150k per permutation × ~12 nodes/path ≈ ~2M per opening):

| candidate | crypto the AIR must eventually carry | census cost | rules complexity |
|---|---|---|---|
| **EVM-MPT inclusion** (`LightClientMpt.lean`) | **keccak256 ONLY — zero signatures** (the lane's `CryptoLeaf.sigVerify` is the constant-`false` verifier, `LightClientMpt.lean:448`; state-root finality is the UPSTREAM sync-committee client's job, `LightClientMpt.lean:34–36`) | ~150k/keccak × ~12/path ≈ **~2M per two-tier opening** — the cheapest crypto in the census by an order of magnitude | trivial: two `verifyPath` walks + 4 equalities + the zero floor (`mptVerify`, `LightClientMpt.lean:306–313`) |
| Tendermint (`LightClientTendermint.lean`) | ed25519 per commit signature (`sigVerify` per validator, `LightClientTendermint.lean:129`) + SHA-256 valset hash | 2–3M **per signature**, × the ≥2/3-stake signer set (dozens–hundreds of sigs) | moderate (stake sum, quorum, time window) |
| Eth sync-committee (`LightClientEth.lean`) | BLS12-381 `fast_aggregate_verify` over up to 512 pubkeys + SHA-256 SSZ merkleization (`LightClientEth.lean:40–56`) | pairing ≈ millions + 512-key aggregation + hash-to-curve — the most expensive of the three | moderate (bitfield, 342/512 threshold, gindex branches) |
| a chain shipping its own succinct proof | that chain's verifier (foreign field/hash: Kimchi/pasta, Goldilocks-FRI, Groth16/BN254) | verifying a FOREIGN proof system in-AIR means its hash/field arithmetic in BabyBear — none is BabyBear-Poseidon2-native, so none beats one keccak path today | n/a |

Three further facts make MPT the pilot, not just the cheapest:

1. **The rules map 1:1 onto the already-mapped constraint alphabet.** `mptVerify` is
   equalities, a two-tier hash-linked walk, and a nonzero floor — every piece has a landed
   carrier in the `CellProgram → EffectVmDescriptor2` mapping table
   (`circuit-prove/src/custom_leaf_adapter.rs:30–42` + the `MerkleHash`/`ChainedHash2to1`/
   `TableFunction` extensions, lines 61–99). No quorum arithmetic, no time windows, no
   signature bookkeeping.
2. **The crypto seam is ONE primitive and it is already a lambda.** The entire Lean lane is
   parametric in the hash: `mptVerify (H : List Nat → Nat)` (`LightClientMpt.lean:306`),
   `Commits H` (line 144), `verifyPath H` (line 155). The factoring the fold-path map's Step 1
   demands (`FOLD-PATH.md` §1) is ALREADY the shape of the file — no refactor needed, only a
   verdict-extraction theorem.
3. **It is the load-bearing rung-2 verification today.** Non-custodial proof-of-holdings
   (`docs/deos/PROOF-OF-HOLDINGS.md`) runs `verify_erc20_holding` at rung 2; the pilot
   upgrades the highest-traffic foreign check first.

**Honest scope of the pilot statement:** the folded leaf certifies *inclusion under a
PI-pinned `state_root`*. The root's *finality* (the Eth sync-committee BLS check) stays rung-2
executor-verified — `verify_erc20_holding_finalized` (`evm.rs:155–158`) remains the composition
point, and BLS-in-AIR is explicitly NOT this pilot (it is the most expensive census line).

---

## 2. THE CONCRETE STEPS (every function real, every seam classified)

The pilot is a three-stage ladder. Each stage is independently shippable, each has teeth, and
only stage P2 touches circuit machinery. Stages P0/P1 ride **Route A — the generic custom arm,
zero new circuit code** (`FOLD-PATH.md` §2): register a `CellProgram`, carry
`CarrierWitness::Custom`, and the deployed arm folds it.

> **Correction to the fold-path map:** Route A's named blocker — "`incircuit_custom_pi_commitment`
> supports ≤ 4 PIs" — is **CLOSED at HEAD**. The in-circuit sponge now chains multi-chunk
> absorbs (`custom_leaf_adapter.rs:1146–1183` — `pi_targets.chunks(4)` with `new_start = false`
> continuation, mirroring the host schedule exactly), with the positive-pole tooth "a genuine
> 32-PI custom leaf proves" at `custom_leaf_adapter.rs:2023–2047`. The MPT leaf's natural PI
> tuple (8-felt state root + token + holder + slot + balance ≈ 12–16 felts) fits with NO
> pre-hash digest and NO VK movement. Route B (a dedicated `CarrierWitness::Mpt` arm + claim
> pin, the DECO shape) remains the long-term home once the leaf is load-bearing; it is
> VK-affecting (`carrier_claim_pins_admitted`, `ivc_turn_chain.rs:3154–3162` for the bridge
> twin) and rides the big-bang regen — NOT the pilot.

### P0 — the MPT holding-commitment leaf (BUILT: `circuit-prove/src/mpt_holding_leaf.rs`)

The DECO shape, exactly (`deco_leaf_adapter.rs:1–42` is the template): a Poseidon2-only
`CellProgram` that recomputes IN-AIR the holding identity over PI-pinned fields, plus the
Nomad floor. What it proves: *the published holding identity is welded to exactly these
committed fields* — MPT + keccak stay off-AIR, executor-verified named carriers (the deployed
DECO posture, `deco_leaf_adapter.rs:27–34`). The landed constraint list (the doc's one code
block):

```text
columns:  state_root[0..8], token, holder, slot, balance, holding_hash, bal_inv, + 30 range bits
gates:    PiBinding{First}  each pinned field ↔ its descriptor PI (13 PIs)  (First-row pin — the
                                                                             named narrowing at
                                                                             custom_leaf_adapter.rs:52–59)
          balance·bal_inv − 1 == 0 (balance ≠ 0) + 30 boolean bit columns   (the DECO AMOUNT_RANGE_BITS
          + recomposition (balance < 2^30)                                   precedent, deco_leaf_adapter.rs:70–74)
          FOUR Hash4to1/Hash2to1 chip sites (mpt_holding_hash_felt):
            holding_hash = H2(H2(H4(root[0..4]), H4(root[4..8])), H4(token, holder, slot, balance))
```

The build calls, in order (the ladder the landed leaf rides):

1. `CellProgram::new(descriptor, version)` (`circuit/src/dsl/circuit.rs:1217`) — mints
   `vk_hash` = BLAKE3(postcard(descriptor)) (`circuit.rs:1231–1235`). Pin the `vk_hash` as a
   KAT. Register in the host `ProgramRegistry` (`circuit.rs:1286+`) — an unknown program fails
   closed (`custom_proof_bind.rs::ProofBindError::UnknownProgram`, `custom_proof_bind.rs:150`).
2. `CellProgram::generate_trace(witness_values, num_rows)` (`circuit.rs:1248`) — the named
   trace-column witness.
3. Mint the **Some-witness** `BoundCustomProof` (`custom_proof_bind.rs:100–118`):
   `witness_values: Some(trace witness)` + `num_rows: Some(n)` — **the `Option` IS the rung
   discriminator** (line 107–114: `Some` = re-provable foldable leaf, `None` = the on-wire
   re-exec rung; the witness is NEVER serialized).
4. Leaf: `prove_custom_leaf_with_commitment(program, witness, rows, pis, config)`
   (`custom_leaf_adapter.rs:1211`) with `config = ir2_leaf_wrap_config()` (the ONE FRI engine,
   `ivc_turn_chain.rs:3064–3066`). Internally: `lower_cellprogram` → `cellprogram_to_descriptor2`
   (`custom_leaf_adapter.rs:670`) → `prove_vm_descriptor2_for_config` (line 1224) →
   `build_and_prove_next_layer_with_expose` (line 1271) with the `incircuit_custom_pi_commitment`
   expose hook (line 1117) — the leaf's exposed 8-felt claim is byte-identical to the host
   `custom_proof_pi_commitment` (`custom_proof_bind.rs:118`, the full `WideHash` squeeze). Read
   back host-side with `read_exposed_pi_commitment` (`custom_leaf_adapter.rs:1283`).
5. Wire the turn: put a `CustomWitnessBundle { program, witness_values, num_rows,
   public_inputs }` (`joint_turn_aggregation.rs:242–253`) on the leg —
   `RotatedParticipantLeg::with_custom_witness` (`joint_turn_aggregation.rs:561`, the test
   wiring) / the production twin (line 1149) — i.e. `carrier_witness:
   Some(CarrierWitness::Custom(bundle))` (`joint_turn_aggregation.rs:150–154`).
6. The deployed arm does the rest — `prove_chain_core_rotated` (`ivc_turn_chain.rs:3025`)
   matches `Some(CarrierWitness::Custom(bundle))` (line 3107): mints the dual-expose leg leaf
   `prove_descriptor_leaf_dual_expose` (line 3108, defined at `ivc_turn_chain.rs:1483` — one
   `expose_claim` carrying segment lanes `[0..SEG_WIDTH)` ++ the claimed 8-felt
   `custom_proof_commitment`, IR2 PI 46..53), calls `prove_custom_leaf_with_commitment` (line 3115),
   and folds both under `prove_custom_binding_node_segmented`
   (`joint_turn_recursive.rs:591`, called at line 3126) — the in-circuit `connect` of claimed
   vs genuine commitment, segment re-exposed, so the node enters `aggregate_tree` like any
   segment leaf. A forged claim has no satisfying `connect` partner ⇒ UNSAT ⇒ no
   `WholeChainProof` root exists. There is deliberately NO wildcard arm (lines 3096–3103), so
   nothing here is new dispatch — the pilot rides the ONE deployed carrier arm.
7. Teeth: honest-accept + ≥3 forged-rejects (forged commitment, forged balance, zero
   balance) end-to-end through `prove_turn_chain_recursive → verify_turn_chain_recursive` —
   `circuit-prove/tests/mpt_holding_fold_pilot.rs`, the `custom_binding_deployed_tooth.rs`
   shape with the demo program replaced by the real MPT holding-commitment `CellProgram`.

### P1 — the rules-in-AIR MPT leaf (verifyRules folds; keccak verdicts stay carried)

Extend the P0 program to prove `verifyRules` — the structural content of `mptVerify` — over
witnessed per-node digests, with the keccak links `dᵢ = keccak(encodeNode(nodeᵢ))` carried as
executor-certified verdict columns (the named-carrier posture; the executor's
`verify_erc20_holding` runs the REAL check, crypto included, before the turn is accepted, and
the leaf's PI commitment binds the same tuple into the turn hash — `custom_proof_bind.rs:47–49` —
so a verdict the executor did not certify cannot be substituted without changing the turn
identity). Per-row = one path step; the alphabet mapping:

| MPT rule (`LightClientMpt.lean`) | constraint carrier (`custom_leaf_adapter.rs:30–42, 61–99`) |
|---|---|
| parent's claimed child digest = child row's digest (`childAt`, walk chaining, lines 135–164) | `Transition` cross-row (→ `WindowGate`) |
| nibble selects the branch child (`childAt cs i`) | `TableFunction` bivariate-Lagrange grid gate (lines 93–99) |
| nibble-path derivation from the witnessed key digest (`nibbles`, line 267) | bit/nibble decomposition gates (`Binary` + `Polynomial` recompose) |
| terminal value = claimed balance / claimed account tuple (`verifyPath` leaf arm, line 158) | `Equality` against PI-pinned columns |
| trusted-state equality (root/token/slot, `mptVerify` conjuncts 2–4) | `PiBinding{First}` |
| zero floor (`claimedBalance != 0`, conjunct 1) | `ConditionalNonzero` |
| keccak digest links | **witnessed verdict columns — OFF-AIR named carrier (until P2)** |

### P2 — keccak in-AIR: the rung-3 crypto closure (the real new machinery)

Add a keccak-f[1600] chip table to the IR-v2 grammar — the analogue of `TID_P2`
(`circuit/src/descriptor_ir2.rs:243`; the table-id family at lines 241–257 has no keccak
entry today, so this is a genuine grammar extension, the ONE new circuit-machinery item in the
whole pilot). Then the P1 verdict columns become chip lookups and the leaf accepts **iff
`mptVerify H ts u = true` for the real keccak** — the full rung-3 statement. Notes:

* Shape: a Plonky3-style keccak-air is ~2,600 columns × 24 rows per permutation; a two-tier
  EIP-1186 opening needs roughly 40–80 permutations (each ≤532-byte branch node = up to 4
  rate-136 absorbs, ~12 nodes × 2 tries + the 2 key digests) → a ~2,048-row chip table.
* VK scope: the leaf descriptor is per-program (its `vk_hash` is its own identity;
  `custom_proof_bind.rs:37–41` binds it at EffectVM column 68), so TID_KECCAK does NOT touch
  the deployed effect-VM descriptor — but verify this VK-neutrality explicitly against
  `ir2_airs_and_common_for_config` (`custom_leaf_adapter.rs:1235–1237`) before building; if
  the shared table registry perturbs existing leaf VKs, P2 rides the big-bang regen instead.

---

## 3. THE LEAN-FIRST LINK: `LightClientMpt.lean` as the AIR's source of truth

Yes — and more cleanly than for any other chain, because the crypto seam is already a
parameter. The in-tree precedent is `metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean`, which
models the REAL `dregg-dfa-routing-v1` AIR constraint-for-constraint and proves
`air_run_is_table_run` — and that same program fully lowers to a foldable leaf
(`dsl_leaf_adapter.rs`). "Lean-modeled AIR" and "foldable AIR" are already the same object
once; the MPT leaf is the second instance. Three theorems, per the fold-path map's §4
discipline:

1. **Factoring** — mostly free: `mptVerify` is already `H`-parametric
   (`LightClientMpt.lean:306`). State `Verdicts` = the finite list of `H`-applications the
   walk makes (per-node digests + the two key digests) and prove
   `mptVerify H ts u = verifyRules ts u (cryptoVerdicts H u)` by `rfl`/`simp` — the crypto
   seam is pinned as data.
2. **AIR faithfulness** (the `air_run_is_table_run` shape): model the descriptor's
   `ConstraintExpr` list as `AirAccepts : Trace → PIs → Prop` and prove
   `AirAccepts tr pis ↔ verifyRules ts u verdicts = true`. The pin against drift: the shipped
   descriptor is pure data (postcard-serialized, BLAKE3-identified — `circuit.rs:1231–1235`;
   JSON under `circuit/descriptors/`), so EMIT it from the same constraint list the Lean model
   quantifies over and pin `vk_hash` as a KAT in the Rust tests. Drift = a hash mismatch,
   never a silent divergence. (The differential alternative — `@[export]`ing `mptVerify` and
   fuzzing it against the leaf — is weaker than the descriptor-emission pin and only worth
   adding as a belt once P1 lands.)
3. **Composed no-forgery**: chain 1 + 2 + `mpt_noForgery` (`LightClientMpt.lean:345` — which
   consumes the unpacked CR carrier `hCR`) to get
   `AirAccepts tr pis → MptForeignValid H u` — the AIR-level image of the adapter discharge
   (`mpt_adapter_accepts_and_discharges`, line 609), modulo the STARK-soundness carrier and,
   until P2, the keccak-verdict carrier. At P2 the verdict carrier collapses into the keccak
   chip's faithfulness (its own KAT-locked permutation model — the `DfaAcceptanceAir`
   treatment applied to keccak-f), leaving exactly the named keccak256-CR floor the Lean
   instance already declares (`mptLeaf` / production swap note, `LightClientMpt.lean:435–459`).

So the folded leaf is TIED to the proof, not just tested: `mptClient : ForeignLightClient`
(rules proven, `LightClientMpt.lean:569`), the descriptor (rules folded, emitted from the same
list), and the fold binding (`custom_binding_deployed_tooth.rs` — the
`CustomBindingFromFold` premise TRUE on the deployed path, `custom_leaf_adapter.rs:163–187`)
meet at one identity: `vk_hash`, bound at EffectVM column 68 and into the turn hash.

---

## 4. THE HONEST COST

* **Apex/wrap: UNCHANGED for the in-fold pilot.** The binding node re-exposes the same
  `SEG_WIDTH` segment and folds into `aggregate_tree` like any segment leaf
  (`deco_leaf_adapter.rs` binding-node design; `joint_turn_recursive.rs:591`), so the ROOT's
  shape — and therefore the gnark wrap's arithmetic residual (~752 opened cols × 19 queries ≈
  ~3.2M R1CS of the ~5.2M native-hash total, `docs/deos/WRAP-NATIVE-HASH-DECISION.md:119–121`)
  — is not grown by adding MPT leaves inside the tree. The prompt-level framing "the leaf AIR
  width × queries adds to the apex reduced-opening residual" holds ONLY for a chain wrapped as
  its OWN root: that costs a separate ~5.2M-R1CS gnark instance per chain. The in-fold
  binding-node architecture avoids exactly this; preserve it.
* **Where the width IS paid: the leaf-wrap + binding layers, in BabyBear recursion (prover
  time, per chain-turn).** Each wrap layer FRI-verifies its child, scaling with the child's
  opened-column count × query count (19 queries at the ir2 knobs). Estimates:
  * P0: DECO-class — base width ~40–70 incl. range bits + one TID_P2 chip
    (`deco_leaf_adapter.rs:94–97`, `BASE_WIDTH = 38` precedent). Negligible next to a standard
    segment leaf; the cost is the fold-path map's three extra recursion proofs per chain-turn
    (dual-expose re-wrap + sub-proof leaf-wrap + binding node).
  * P1: width ~60–100 (per-step columns + 16 child-digest slots + chip lanes), rows = path
    length (~16–32). Same class as P0.
  * P2: the keccak chip adds ~2,600 opened columns → the leaf's reduced-opening term at the
    wrap layer ≈ 2,600 × 19 ≈ ~50k opened values, ~3.5× the ROOT's own ~752 × 19 ≈ ~14k. The
    binding node over a P2 leaf is a several-× aggregation node — minutes-class prover cost
    per chain-turn, in BabyBear, never in gnark. This is the price of rung 3 and it is
    per-turn latency, not apex growth.
* **Wire cost: none.** `witness_values` never serializes (`custom_proof_bind.rs:112–114`);
  the light client sees only the folded root.
* **Fail-degraded is sanctioned:** `carrier_witness: None` takes the re-exec rung
  (`ivc_turn_chain.rs:3100–3102`) — visible in the artifact, never laundered.

---

## 5. NAMED RESIDUALS + the P0 increment (built)

Residuals, each named with its closure lane:

1. **TID_KECCAK chip table** (P2) — the rung-3 crypto closure; the one genuine
   circuit-machinery build. Verify VK-neutrality for deployed descriptors first (§2 P2 note).
2. **Keccak-verdict carrier at P0/P1** — until P2, digest links are executor-certified named
   carriers (the DECO ed25519/HMAC posture, `deco_leaf_adapter.rs:27–34`). State it in the
   leaf's doc header the way the DECO leaf does; never present P0/P1 as full rung 3.
3. **First-row `PiBinding` narrowing** (`custom_leaf_adapter.rs:52–59`) — PI-pinned values
   must sit on the first row (P0/P1 designs above respect this); the per-row PI gate remains
   the named IR follow-up.
4. **Lean modeling fidelity** (`LightClientMpt.lean:47–54`) — 4-nibble paths, model RLP;
   widen to 64 nibbles + real RLP alongside P1 (the theorems are structured to survive the
   widening: injectivity is proven, not assumed).
5. **Production keccak carrier discharge** — swap `toyKeccak` for a real keccak256 with the
   named CR floor (the `mptLeaf` swap note, `LightClientMpt.lean:435–445`); pairs with P2.
6. **Upstream finality composition** — the pilot leaf pins `state_root` as trusted-state PI;
   composing with a FOLDED Eth finality leaf (BLS in-AIR) is a separate, census-expensive
   campaign, not this pilot. Rung 2 (`verify_erc20_holding_finalized`, `evm.rs:155–158`)
   remains the finality gate.
7. **Route B carrier arm** (`CarrierWitness::Mpt` + descriptor claim pin) — the long-term
   home; VK-affecting, rides the big-bang regen tie. Open it only after P1 proves load-bearing.

**The P0 increment is built:** the holding-commitment `CellProgram`
(`circuit-prove/src/mpt_holding_leaf.rs` — 13 PIs through the multi-chunk sponge, the Nomad
floor, the four chip hash sites), `vk_hash` KAT, `ProgramRegistry` registration, one
`CustomWitnessBundle` on one leg via `with_custom_witness`, and the end-to-end
`prove_turn_chain_recursive → verify_turn_chain_recursive` run with honest-accept +
forged-reject teeth (`circuit-prove/tests/mpt_holding_fold_pilot.rs`). Zero new circuit code,
zero VK movement, one new `CellProgram` + one test file — the whole rung-3 pipe (Some-witness
→ foldable leaf → binding node → `aggregate_tree` → a pure light client's `WholeChainProof`)
exercised on a REAL chain verification. The open stages are P1 (rules-in-AIR) and P2
(TID_KECCAK — residual 1 above; the table-id family in `circuit/src/descriptor_ir2.rs` has no
keccak entry).
