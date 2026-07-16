# `Custom { vk_hash }` — what verifies, where, and how it relates to IVC

There are **three distinct `Custom`-by-32-byte-vk-hash surfaces** in dregg, and
they are easy to conflate because they share the "name a verifier by its hash"
pattern (the precedent noted at `cell/src/custom_effect.rs:1-12`). Only one of
them is recursive STARK verification; the others are programmable *authorization*
that the executor checks out-of-circuit. This note grounds each against code at
HEAD.

## The three surfaces

| Surface | Type | Where the vk_hash points | Where it's checked |
|---|---|---|---|
| **Programmable auth** | `AuthRequired::Custom { vk_hash }` (`cell/src/permissions.rs:21`) + `Authorization::Custom { predicate }` (`turn/src/action.rs:301`) | a Rust verifier registered in `WitnessedPredicateRegistry` | **executor-side, out-of-circuit** |
| **Predicate-algebra escape** | `WitnessedPredicateKind::Custom { vk_hash }` (`cell/src/predicate.rs:301`) | same registry (`register_custom`, `predicate.rs:967`) | **executor-side, out-of-circuit** |
| **Custom program dispatch** | `Effect::Custom { program_vk_hash, proof_commitment }` (`circuit/src/effect_vm/effect.rs:281-308`) | a `CellProgram` STARK whose descriptor IS its VK | **in-circuit, by the deployed recursion fold** |

The phrase *"Custom, vk hash, intended to model recursive STARK verification"*
lands on the **third** surface (`Effect::Custom` + the descriptor's `proof_bind`
op) — and at HEAD it is no longer "intended to model": the sub-proof binding is
enforced inside the recursion fold. The first two (`AuthRequired::Custom` /
`Authorization::Custom`) are ERC-1271-style *programmable authorization* — a
`WitnessedPredicate` proves an app-defined auth condition over the canonical
signing message; there is no STARK recursion in them, just a registered Rust
verifier dispatched by hash.

---

## 1. Programmable authorization (`AuthRequired::Custom` / `Authorization::Custom`)

A cell declares `AuthRequired::Custom { vk_hash }` on a permission slot
(`permissions.rs:21`). It is deliberately NOT satisfiable by a signature or a
generic proof — `AuthRequired::is_satisfied_by` returns `false` for `Custom`
(`permissions.rs:42`); the only thing that clears it is `Authorization::Custom`
carrying a `WitnessedPredicate` whose `kind == WitnessedPredicateKind::Custom {
vk_hash }` with the *same* hash.

**How it verifies (executor-side only):**
`Executor::verify_custom_authorization` (`turn/src/executor/authorize.rs:515`):

1. cell-consistency: the predicate's vk_hash must equal the slot's required
   vk_hash (`authorize.rs:543`);
2. registry lookup — fail-closed on miss → `AuthModeNotRegistered`
   (`authorize.rs:562`, `:571`);
3. build the canonical custom signing message (federation_id + turn_nonce +
   position + action body), `authorize.rs:604`;
4. resolve proof bytes from `action.witness_blobs[proof_witness_index]`;
5. `registry.verify(predicate, input, proof_bytes)` (`authorize.rs:658`).

The verifier is a Rust trait object (`WitnessedPredicateVerifier`) resolved from
`WitnessedPredicateRegistry` (`cell/src/predicate.rs:992`). The registry fails
closed: the default registry installs `NotYetWiredVerifier` (reject) for kinds
whose real cryptographic verifier isn't installed (`predicate.rs:943-953`), and
the host upgrades them via `register_builtin` / `register_custom`.

**Key point:** this entire path is executor / verifier-side Rust. The turn's
STARK does **not** witness the custom-auth predicate verification. The light
client re-runs the same Rust check from the on-chain Turn fields; it does not
get it "for free" from the aggregate proof. (This is the same posture as
signatures — auth in dregg is verified by re-execution, not folded into the
EffectVM proof.)

---

## 2. Custom program dispatch (`Effect::Custom`) — the recursive-STARK surface

`Effect::Custom { program_vk_hash: [BabyBear;8], proof_commitment: [BabyBear;8] }`
(`circuit/src/effect_vm/effect.rs:281-308`). The doc comment there states the
contract: domain-specific constraints are proven in a separate proof identified
by `custom_proof_commitment`; the Effect VM AIR does not verify the external
proof — it PUBLISHES `custom_proof_commitment` / `custom_program_vk_hash` as
public inputs for the fold to bind.

The deployed EffectVM descriptor `customVmDescriptor2R24` carries exactly one
`DescriptorIR2.ProofBind` op (`circuit/src/descriptor_ir2.rs:559-573`, variant at
`:667`) that names two row columns:

- col 68 (`custom_program_vk_hash` base) — the program VK handle;
- col 72 (`custom_proof_commitment` base) — the sub-proof's PI commitment.

### The load-bearing distinction: the in-AIR op is a declaration, the fold is the enforcement

The `proof_bind` op **inside the AIR is intentionally a declaration** (like
`mem_op` / `umem_op`; `descriptor_ir2.rs:5455-5477`): on its own, the Custom
row's claimed commitment is unbacked. It is backed **in-circuit** by the chain
prover's custom fold arm:

- the effect-vm leg is wrapped as a **dual-expose leaf**
  (`circuit-prove/src/ivc_turn_chain.rs::prove_descriptor_leaf_dual_expose`,
  ~`:1188`) that exposes both the chain segment and the leg's CLAIMED 8-felt
  `custom_proof_commitment`, read from the FRI-bound IR2 PI slots `46..53`
  (`CUSTOM_COMMIT_PI_LO = 46`, `CUSTOM_COMMIT_LEN = 8`,
  `joint_turn_recursive.rs:105-110`; the Lean `customPiExposure`);
- the custom **sub-proof is re-proven as a leaf** from the retained
  `CustomWitnessBundle`
  (`custom_leaf_adapter::prove_custom_leaf_with_commitment`), with its
  commitment computed in-circuit;
- `prove_custom_binding_node_segmented` (`joint_turn_recursive`) `connect`s the
  claimed lanes to the genuine ones, wired into the deployed chain prover
  `prove_chain_core_rotated` (`ivc_turn_chain.rs:2857-2868`).

**The tooth:** a turn whose effect-vm row claims a commitment no verifying
sub-proof backs is UNSAT — there is no satisfying custom leaf whose exposed
commitment equals the claimed slots, so the aggregate does not prove and no root
artifact exists. A pure light client that folds the recursion tree is therefore
covered **without any off-AIR step**.

**The teeth, and where they run:**
`every_forged_commitment_lane_is_rejected_by_the_fold` (in-lib,
`joint_turn_recursive`) forges each of the 8 commitment lanes independently and
runs on a plain `cargo test -p dregg-circuit-prove` — that is the connect
MECHANISM tooth. The DEPLOYED end-to-end poles (honest-accept + forged-reject
through `prove_turn_chain_recursive` → `verify_turn_chain_recursive`) are
`#[ignore]`d for plain CI: `custom_binding_deployed_tooth.rs` runs on the
nightly armed-teeth lane (`.github/workflows/armed-teeth.yml`, `--ignored`);
`custom_binding_production_path.rs` is `--ignored`-only and not yet on a
scheduled lane (a named automation seam).

### Provenance (why older references disagree)

An off-AIR Rust engine (`verify_proof_bind` / `prove_custom_program` /
`verify_bound_custom_proof`) used to perform this verification verifier-side;
it died with stark-kill (`dd038c08e`). Nothing in the tree verifies a proof-bind
off-AIR any more — `circuit-prove/src/custom_proof_bind.rs` now carries only the
types + the canonical `custom_proof_pi_commitment` derivation the fold binds
against, and its module doc states exactly this. Any text describing
`verify_proof_bind` as "the genuine engine the light client MUST run" describes
a deleted architecture.

---

## 3. Relationship to IVC / aggregation — the custom sub-proof IS folded

The whole-history recursion (`circuit-prove/src/ivc_turn_chain.rs`,
`joint_turn_recursive.rs`, `verify_turn_chain_recursive`) folds **per-turn
EffectVM proofs** into one running recursive proof:

- `ivc_turn_chain.rs` is a *temporal* accumulator: turn N's post-root must equal
  turn N+1's pre-root, over the finalized order; each leaf is the
  `EffectVmDescriptorAir` itself, wrapped in an in-circuit verifier and
  aggregated up a binary tree to one root batch-STARK.
- `joint_turn_recursive.rs` folds the N per-cell proofs of a *single* shared
  turn — and hosts the custom binding node.

**The custom sub-proof is one of the folded leaves.** When a turn's effect-vm
leg is `customVmDescriptor2R24`, the chain prover's custom fold arm
(`prove_chain_core_rotated`, `ivc_turn_chain.rs:2857-2868`) re-proves the
sub-proof from the retained `CustomWitnessBundle` as a leaf and binds its
in-circuit commitment to the leg's claimed lanes inside the aggregate. Custom
sub-proof verification and IVC-of-turns are **one mechanism**, not two: the IVC
root proof establishes the custom effect's program-correctness along with the
chain.

---

## Verdict on the framing this note exists to answer

> "how does our Custom (vk hash, intended to model recursive STARK verification)
> work / I guess we always had the ability to verify a sub-STARK but we never
> could aggregate/IVC them?"

- **"models recursive STARK verification"** — at HEAD, *realized, in-circuit.*
  The deployed fold re-proves the referenced program-STARK as a recursion leaf
  and `connect`s its in-circuit commitment to the effect-vm leg's claimed lanes;
  a claimed commitment with no verifying sub-proof is UNSAT. (The
  `Authorization` flavor of `Custom` is not STARK recursion at all — it's
  registry-Rust programmable auth, §1.)

- **"we always had the ability to verify a sub-STARK"** — *needs correction.*
  The column/op were present from the start, but the binding passed through a
  vacuous bounds-check-only stage and then an off-AIR Rust-engine stage before
  the in-circuit fold; the off-AIR engine is deleted (stark-kill `dd038c08e`).
  The standalone primitive (`CellProgram::prove/verify_transition`, the
  per-program STARK over a user descriptor that IS its VK) predates all of it.

- **"never could aggregate/IVC them"** — *no longer true.* The custom sub-proof
  is folded into the aggregate as a leaf (§3); it is not a separate inline
  verification.

## Soundness-surface findings (for the RUST-ONLY-LOGIC-CENSUS)

1. **Custom-auth (`Authorization::Custom`) is executor/verifier-side only.** The
   light client re-runs the registry verifier in Rust
   (`authorize.rs:658` → `predicate.rs:992`); the turn's STARK does not witness
   it. Soundness of the auth predicate rests on every verifier re-running the
   correct registered Rust verifier — not on the aggregate proof.

2. **`Effect::Custom` program-correctness is verified in-circuit by the fold.**
   The in-AIR `proof_bind` op is a declaration; the enforcement is
   `prove_custom_binding_node_segmented` wired into `prove_chain_core_rotated`.
   A pure light client that verifies the recursion root gets custom
   program-correctness with no additional off-AIR step. (The old census finding —
   "the light client MUST run `verify_proof_bind`" — is inverted at HEAD: that
   engine no longer exists.)

3. **`custom_proof_commitment` is an 8-felt (~124-bit) binding column** at IR2
   PI slots `46..53` (`joint_turn_recursive.rs:105-110`), matching the 8-felt
   posture of the other auth WideHash bindings. The 4-felt/~62-bit rotation
   surface older text names is rotated.

4. **Automation posture (named, not a hole):** the connect-mechanism forge tooth
   runs on every plain `cargo test -p dregg-circuit-prove`;
   `custom_binding_deployed_tooth.rs` runs on the nightly armed-teeth lane
   (`--ignored`); `custom_binding_production_path.rs` is `--ignored`-only and not
   yet on a scheduled lane.
