# `Custom { vk_hash }` — what verifies, where, and how it relates to IVC

There are **three distinct `Custom`-by-32-byte-vk-hash surfaces** in dregg, and
they are easy to conflate because they share the "name a verifier by its hash"
pattern (the precedent noted at `cell/src/custom_effect.rs:8`). Only one of them
"models recursive STARK verification"; the others are programmable *authorization*
that the executor checks out-of-circuit. This note grounds each against code at
HEAD.

## The three surfaces

| Surface | Type | Where the vk_hash points | Where it's checked |
|---|---|---|---|
| **Programmable auth** | `AuthRequired::Custom { vk_hash }` (`cell/src/permissions.rs:21`) + `Authorization::Custom { predicate }` (`turn/src/action.rs:301`) | a Rust verifier registered in `WitnessedPredicateRegistry` | **executor-side, out-of-circuit** |
| **Predicate-algebra escape** | `WitnessedPredicateKind::Custom { vk_hash }` (`cell/src/predicate.rs:301`) | same registry (`register_custom`, `predicate.rs:963`) | **executor-side, out-of-circuit** |
| **Custom program dispatch** | `Effect::Custom { program_vk_hash, proof_commitment }` (`circuit/src/effect_vm/effect.rs:281`) | a `CellProgram` STARK whose descriptor IS its VK | **light-client / SDK Rust re-verification, out-of-circuit** |

The owner's phrase *"Custom, vk hash, intended to model recursive STARK
verification"* lands on the **third** surface (`Effect::Custom` + the
descriptor's `proof_bind` op). The first two (`AuthRequired::Custom` /
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
   vk_hash (`authorize.rs:542`);
2. registry lookup — fail-closed on miss → `AuthModeNotRegistered`
   (`authorize.rs:560`, `:569`);
3. build the canonical custom signing message (federation_id + turn_nonce +
   position + action body), `authorize.rs:604`;
4. resolve proof bytes from `action.witness_blobs[proof_witness_index]`;
5. `registry.verify(predicate, input, proof_bytes)` (`authorize.rs:658`).

The verifier is a Rust trait object (`WitnessedPredicateVerifier`) resolved from
`WitnessedPredicateRegistry` (`cell/src/predicate.rs:989`). For example the
default `Dfa` verifier (`predicate.rs:939`) does an **out-of-circuit re-check of
a serialized `dregg_dfa::AirTrace`**. The registry fails closed: the default
registry installs `NotYetWiredVerifier` (reject) for kinds whose real
cryptographic verifier isn't installed (`predicate.rs:931-952`), and the host
upgrades them via `register_builtin` / `register_custom`.

**Key point:** this entire path is executor / verifier-side Rust. The turn's
STARK does **not** witness the custom-auth predicate verification. The light
client re-runs the same Rust check from the on-chain Turn fields; it does not
get it "for free" from the aggregate proof. (This is the same posture as
signatures — auth in dregg is verified by re-execution, not folded into the
EffectVM proof. There is an in-circuit *signature* AIR
`circuit/src/turn_auth_signature_air.rs`, but the `Custom` programmable-auth
path is registry-Rust, not in that AIR.)

---

## 2. Custom program dispatch (`Effect::Custom`) — the "recursive STARK" surface

`Effect::Custom { program_vk_hash: [BabyBear;8], proof_commitment: [BabyBear;4] }`
(`circuit/src/effect_vm/effect.rs:281`). The doc comment there states the intent:
*"Domain-specific constraints are proven in a separate proof identified by
`custom_proof_commitment`. The verifier checks that the external proof is valid
and that its hash matches this commitment."* (`effect.rs:279`).

The deployed EffectVM descriptor `customVmDescriptor2R24` carries exactly one
`DescriptorIR2.ProofBind` op (`circuit/src/descriptor_ir2.rs:478`, variant at
`:572`) that pins two row columns:

- col 68 (`PARAM_BASE + CUSTOM_VK_HASH_BASE`) — the program VK handle;
- col 72 (`PARAM_BASE + CUSTOM_PROOF_COMMIT_BASE`) — the sub-proof's PI
  commitment.

### The load-bearing distinction: the in-AIR op is NOT a verification

The `proof_bind` op **inside the AIR is only a bounds / declaration check**.
Stated verbatim at `circuit/src/effect_vm/trace_rotated.rs:3267`: *"The
`proof_bind` in-AIR op is a bounds/declaration check; the program-correctness
recursion is the external engine."* The EffectVM AIR's Custom leg explicitly does
**not** verify the external proof — it records the hash commitment and warns that
*"Verifiers MUST independently verify the external proof against the committed
program VK hash"* (quoted in `circuit-prove/src/custom_proof_bind.rs:10-16`).

### Where the actual sub-STARK verification lives

`dregg_circuit_prove::custom_proof_bind::verify_proof_bind`
(`circuit-prove/src/custom_proof_bind.rs:237`) is the genuine engine. Its four
fail-closed steps:

1. resolve the program by the bound 8-felt VK (unknown → reject);
2. confirm the program's self-computed VK equals the bound column;
3. **verify the external STARK** under the program's AIR —
   `program.verify_transition(public_inputs, proof_bytes)`
   (`custom_proof_bind.rs:268`); *"THIS is the recursion the bounds check
   skipped."*
4. require the verified sub-proof's PI commitment equals the bound column.

This runs in **Rust, out-of-circuit**. The commit that introduced it
(`b597fe342`) is explicit: *"verifier-side soundness, VK-free; no Lean… the
`EngineSound.recursive_sound` named obligation is exactly what this engine
realizes for custom."* The `(vk, commit)` columns are bound into the EffectVM PI
and the turn hash (`Turn::with_custom_program_proofs`, `turn/src/turn.rs:567`),
so the sub-proof bytes/PI cannot be swapped after the fact — but the *act of
verifying* the sub-STARK is a light-client Rust step, not a constraint inside the
turn's proof.

So: **genuine sub-STARK verification, yes; recursive-in-circuit, no.** It is
"the verifier independently verifies a referenced sub-proof," more ERC-1271-for-
programs than in-circuit recursion. The descriptor's prose ("rides the named
recursion argument", `descriptor_ir2.rs:475`) is aspirational framing; the
deployed realization is the external `verify_proof_bind` engine, and the
in-circuit tests use a `ToyEngine` model of the binding implication
(`descriptor_ir2.rs:6077`).

---

## 3. History — it was VACUOUS until recently

The owner's hypothesis: *"we always had the ability to verify a sub-STARK
(Custom)."* **This needs correction.** The capability is recent:

- `2a5b22a18` — graduated `Effect::Custom` (sel-8) via a new `ProofBind` IR
  constraint. This only *declared* the binding.
- For the interval after that, the gate was **vacuous**: per `b597fe342`'s
  message, *"the deployed proof_bind gate… only BOUNDS-CHECKED its
  commit(col72)+vk(col68) columns — it never verified the bound external STARK,
  so a custom effect's program-correctness was unenforced (the gate's
  descriptorRefines was VACUOUS — a prover could supply any sub-proof)."*
- `b597fe342` — *"custom proof_bind now GENUINELY verifies the bound external
  sub-proof (the last vacuous gate)."* This is when `verify_proof_bind` /
  `prove_custom_program` landed and the gate stopped being a no-op.
- `e8f5016a3` — lifted the collision-exposed WideHash auth bindings 4→8 felts
  (~62→~124 bit). (Note `custom_proof_commitment` is still a **4-felt / ~62-bit**
  column, `custom_proof_bind.rs:61-70`, a named remaining rotation surface.)
- `8f6f79348` — crate-split: the genuine verify engine lives in
  `dregg-circuit-prove`; the weak v1 floor was retired.

The "real external-proof primitive" (`CellProgram::prove_transition` /
`verify_transition`, the per-program STARK over a user `CircuitDescriptor` that
IS its VK) existed earlier but was **disconnected** from the custom gate until
`b597fe342` welded it in.

So a fair statement: *the column intended to model sub-proof verification was
always present; the actual verification was a no-op for a stretch and only became
real recently — and even now it is verifier-side Rust, not in-circuit recursion.*

---

## 4. Relationship to IVC / aggregation — they are SEPARATE mechanisms

The new whole-history recursion (`circuit-prove/src/ivc_turn_chain.rs`,
`joint_turn_recursive.rs`, `verify_turn_chain_recursive`) folds **per-turn
EffectVM proofs** into one running recursive proof:

- `ivc_turn_chain.rs` is a *temporal* accumulator: turn N's post-root must equal
  turn N+1's pre-root, over the finalized order; each leaf is the
  `EffectVmDescriptorAir` itself, wrapped in an in-circuit verifier and
  aggregated up a binary tree to one root batch-STARK
  (`ivc_turn_chain.rs:1-60`).
- `joint_turn_recursive.rs` folds the N per-cell proofs of a *single* shared
  turn.

**The custom sub-proof (`verify_proof_bind`) is NOT folded into the IVC chain.**
There is no `custom` / `proof_bind` / `BoundCustomProof` reference in
`ivc_turn_chain.rs` or `joint_turn_recursive.rs`. The IVC folds the EffectVM
turn-leaf (which *includes* the Custom row and its bounds-check `proof_bind` op +
the bound `(vk, commit)` columns), but the program-correctness recursion of the
custom sub-STARK remains a separate, single, out-of-circuit `verify_proof_bind`
check the light client runs per custom effect. They are orthogonal: one
aggregates turn proofs in-circuit; the other verifies one referenced sub-proof in
Rust.

---

## Verdict on the owner's framing

> "how does our Custom (vk hash, intended to model recursive STARK verification)
> work / I guess we always had the ability to verify a sub-STARK but we never
> could aggregate/IVC them?"

- **"models recursive STARK verification"** — *aspirational/approximate.* What it
  actually models: the verifier independently verifies a referenced external
  program-STARK (`verify_proof_bind`, four fail-closed checks) and the turn binds
  that proof's `(vk, commit)`. It is **out-of-circuit verifier-side recursion**,
  not a recursive STARK verifier embedded in the turn's AIR. (The `Authorization`
  flavor of `Custom` is not STARK recursion at all — it's registry-Rust
  programmable auth.)

- **"we always had the ability to verify a sub-STARK"** — *needs correction.* The
  column/op were present, but the gate was **vacuous** (bounds-check only, any
  sub-proof accepted) until `b597fe342`, which welded the genuine
  `verify_proof_bind` engine. The standalone primitive
  (`CellProgram::prove/verify_transition`) existed earlier but was disconnected.

- **"never could aggregate/IVC them"** — *true, and still true.* The IVC/aggregation
  machinery (`ivc_turn_chain.rs` etc.) is the separate, newer mechanism; it folds
  per-turn EffectVM proofs, not custom sub-proofs. A `Custom`-effect turn's
  sub-proof is still a single inline (out-of-circuit) verification, not
  aggregated. Custom-sub-proof-verification and IVC-of-turns are orthogonal; the
  custom sub-proof has never been folded into the IVC.

## Soundness-surface findings (for the RUST-ONLY-LOGIC-CENSUS)

1. **Custom-auth (`Authorization::Custom`) is executor/verifier-side only.** The
   light client re-runs the registry verifier in Rust
   (`authorize.rs:658` → `predicate.rs:989`); the turn's STARK does not witness
   it. Soundness of the auth predicate rests on every verifier re-running the
   correct registered Rust verifier — not on the aggregate proof.

2. **`Effect::Custom` program-correctness is verified out-of-circuit.** The in-AIR
   `proof_bind` op is a bounds/declaration check (`trace_rotated.rs:3267`); genuine
   verification is `verify_proof_bind` in Rust. The light client MUST run it; the
   IVC root proof alone does not establish that a custom effect's sub-STARK
   verified. A light client that checks only the aggregate turn proof and skips
   `verify_proof_bind` would accept a custom effect whose program-constraints were
   never proven.

3. **`custom_proof_commitment` is a 4-felt (~62-bit) binding column**
   (`custom_proof_bind.rs:61-70`), a named remaining rotation surface; the rest of
   the auth WideHash bindings were lifted to 8-felt/~124-bit in `e8f5016a3`.

4. **Liveness gap (not soundness)**, per `b597fe342`'s own REMAINING note: the
   deployed wide prover did not lay the 789-wide custom row and
   `Turn.custom_program_proofs` was `None` at construction, so a single-effect
   custom turn did not yet mint a wide receipt end-to-end. Verify the current
   state of `generate_rotated_custom_wide` (`trace_rotated.rs:3277`) and
   `Turn::with_custom_program_proofs` threading against HEAD.
