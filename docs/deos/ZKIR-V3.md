# ZKIR v3 — what it is, and what `gen_midnight.rs` emits

## The one-sentence answer

**ZKIR v3 is Midnight's own zero-knowledge intermediate representation — the
low-level circuit IR that the Compact contract language compiles *down to*, and
that Midnight's proof server consumes to produce a Halo2/KZG proof.** It is *not*
a route for verifying a foreign (dregg) STARK on Midnight. When `dregg-dsl`'s
`gen_midnight` backend "targets Midnight," it emits a program written **in** this
IR — i.e. it re-expresses a dregg caveat/effect's constraint semantics as a
*native Midnight circuit*, the same kind of object a Compact `circuit` produces.

Grounding: `~/midnight/midnight-ledger/zkir-v3/src/ir.rs` (the `IrSource`,
`Instruction`, `Operand`, `IrType` types), `midnight-architecture/proposals/0021-ZKIR-redesign.md`
(the redesign rationale), and `~/midnight/midnight-ledger/zkir-precompiles/*.zkir`
(real programs — note these committed samples are still **v2**).

## Where ZKIR sits in Midnight's stack

```
Compact source  ──compiler──▶  ZKIR (IrSource)  ──proof server──▶  Halo2/KZG proof
   (contract)                  (this IR)            (off-chain)       over BLS12-381
                                    │                                      │
                                    ▼                                      ▼
                              ProverKey (fixed                       ContractCall carries
                              per entry point)                       proof; on-chain verifier
                                                                     key is fixed at deploy
```

- The proving backend is **Halo2 + KZG over BLS12-381**, with **Jubjub** as the
  in-circuit embedded curve (`midnight-architecture/adrs/0013-proof-system.md`;
  the Pluto-Eris → BLS12-381 switch in `CHANGELOG_transient-crypto.md`). There is
  **no STARK/FRI backend**.
- A circuit's **verifier key is fixed per entry point at deployment**
  (`midnight-ledger/spec/contracts.md`). There is no generic in-circuit
  proof-verification / recursion primitive exposed to Compact authors, so a
  contract **cannot verify an arbitrary foreign proof**. This is the architectural
  fact that forecloses "verify a dregg STARK on Midnight" — see
  `plans/midnight-bridge-production.md`.

So ZKIR v3 is the IR you write **a Midnight circuit in**. Emitting it is how a
dregg predicate could become a *Midnight-native* circuit (the "Level 3 shared
program" path), proven by Midnight's own backend — **not** a way to carry a dregg
proof onto Midnight.

## v2 vs v3 (why the version field matters)

The committed `.zkir` precompiles (`zkir-precompiles/zswap/spend.zkir`, …) are
**v2**: register machine with numeric `var` indices, ops like `load_imm` /
`declare_pub_input` / `pi_skip`, and `"version": { "major": 2, "minor": 0 }`.

**v3** (`proposals/0021-ZKIR-redesign.md`, `zkir-v3/src/ir.rs`) is a redesign to
**named SSA**: variables are `%`-prefixed identifiers (`Operand::Variable`),
immediates are hex field elements (`Operand::Immediate`), and instructions carry
named `output` wires instead of pushing to a register stack. Crucially, in v3
`IrSource::version` is an **`IrMinorVersion`** — a `serde_repr` `u8` (currently
`V0 = 0`) — so the faithful serialized form is a bare integer:

```json
{ "version": 0, "inputs": [ … ], "outputs": [ … ],
  "do_communications_commitment": false, "instructions": [ … ] }
```

The major version "3" lives in the *type tag* `ir-source[v3-generic]`, **not** in
the serialized `version` field. (The codegen previously emitted the v2-style
`{ "major": 3, "minor": 0 }` object; that is now corrected — see below.)

## What `gen_midnight.rs` actually emits

`dregg-dsl/src/gen_midnight.rs` lowers a dregg `ConstraintIr` (the same IR the
Rust/AIR/Datalog/Kimchi/Plonky3/STARK/SP1 backends consume) into a JSON
`IrSource`. Each dregg parameter becomes a `TypedIdentifier` input wire; a mutable
effect parameter `t` becomes two wires `%t_old` / `%t_new`. Types map to real
`IrType`s — `IrType::Native` *is* `"Scalar<BLS12-381>"` (its serde rename in
`zkir-v3/src/ir_types.rs`), so a `u64` / 32-byte digest input is a `Native` field
element.

Mapping from dregg IR to **real** ZKIR v3 `Instruction`s
(`zkir-v3/src/ir.rs::Instruction`, snake_case `op` tags):

| dregg IR | ZKIR v3 instructions emitted |
|---|---|
| `require!(a <= b)` / `a >= b` | `neg`, `add` (form the difference), `constrain_bits(diff, 64)` (proves `diff ≥ 0`) |
| `require!(a == b)` | `constrain_eq(a, b)` |
| `require!(a != b)` | `test_eq` → `not` → `assert` |
| `in_range!(v, N)` (`BitRange`) | `constrain_bits(v, N)` |
| `*t -= x` / `*t += x` / `*t = x` (`Mutate`) | `neg`/`add` then `constrain_eq(result, %t_new)` |
| `match` | `constrain_to_boolean` on the discriminant + both arms inline |
| `set.contains(x)` (`Membership`) | `transient_hash([x])` → `constrain_eq` vs the set root |
| `merkle_member!(…)` (`MerkleAtPosition`) | depth-`N` fold: `div_mod_power_of_two` (peel path bit) · `private_input` (witness sibling) · two `cond_select` (order the pair) · `transient_hash([left,right])`, then `constrain_eq(folded_root, root)` |

`transient_hash` is Midnight's circuit-friendly hash (`Instruction::TransientHash`)
— it plays the 2-to-1 compression role that Poseidon2 plays on the dregg side. A
dregg `poseidon2_assert!` therefore lowers to `transient_hash` + `constrain_eq`,
**not** to a Poseidon2 gadget (Midnight has no Poseidon2 in-circuit).

### Faithfulness, and the lint that enforces it

`gen_midnight` is an **emit-only / lint-only** backend: it casts no vote in the
`dregg-dsl-differential` agreement set, because validating the emitted program
requires Midnight's off-chain proof server (and the `compact` toolchain), neither
of which is bundled here. Instead, `dregg-dsl-differential/src/midnight_lint.rs`
statically checks every emitted program:

- it parses as JSON;
- `version` is the numeric `IrMinorVersion` repr (not a `{major,minor}` object);
- every declared caveat parameter appears as an input wire;
- **every instruction's `op` is a real ZKIR v3 instruction** (whitelist mirrored
  from `zkir-v3/src/ir.rs::Instruction`) — this rejects any placeholder op;
- the program terminates with an `output` instruction.

This lint is the contract that keeps the emitter honest in the absence of the
real proving stack.

## Role in the bridge strategy

ZKIR v3 codegen is the **Level 3 ("shared program")** lane of the Midnight bridge
roadmap (`plans/midnight-bridge-production.md`): the same dregg predicate compiled
to a *Midnight-native* circuit so a capability check can be a real Compact entry
point. It is deliberately **decoupled** from the near-term bridge, which is
**Level 1.5 (optimistic + dispute)**: Midnight only ever checks the federation
attestation, and the dregg-side STARK proof is the objective fraud evidence a
watchtower uses to challenge a bad relay (`bridge/src/{midnight,midnight_verified,
midnight_gateway,midnight_observer}.rs`). The bridge's safety does **not** depend
on ZKIR codegen.

Where ZKIR codegen *does* pay off: it lets a dregg predicate run **on** Midnight
as a first-class contract circuit, proven by Midnight's own backend — a portable
predicate, not a cross-chain proof. The remaining work to make that real is
external-toolchain-gated, not design-gated:

1. **Schema fidelity (done for the constructs we emit).** `version`, input/output
   `IrType`s, and the Merkle/membership unrolls are real ZKIR v3 — no placeholder
   ops. Remaining drift to clean when needed: `ByteMatrix32` currently maps to a
   nominal `Array<Scalar<BLS12-381>>` (ZKIR v3 has no array type — a matrix should
   be flattened to `Native` wires or witnessed privately, as the Merkle siblings
   already are).
2. **Round-trip + prove (toolchain-gated).** Deserialize the emitted JSON with the
   real `zkir_v3::IrSource`, build a `ProverKey`, and prove against Midnight's
   proof server. This needs the Midnight crates / proof server, not present here;
   the lint is the in-repo stand-in.
3. **Compact entry point (toolchain-gated).** Wrap the circuit as a Compact
   contract entry point (`bridge/contracts/dregg_bridge.compact`) and deploy —
   gated on the `compact` toolchain (not installed) and a reachable devnet.

## Pointers

- IR types & instructions: `~/midnight/midnight-ledger/zkir-v3/src/{ir.rs,ir_types.rs}`
- Redesign rationale: `~/midnight/midnight-architecture/proposals/0021-ZKIR-redesign.md`
- Real (v2) sample programs: `~/midnight/midnight-ledger/zkir-precompiles/*.zkir`
- dregg emitter: `dregg-dsl/src/gen_midnight.rs` (+ its `#[cfg(test)]` module)
- emitter lint: `dregg-dsl-differential/src/midnight_lint.rs`
- bridge strategy & the foreclosed direct-proof path: `plans/midnight-bridge-production.md`
