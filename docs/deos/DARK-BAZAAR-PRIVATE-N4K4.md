# Dark Bazaar private N4K4 certificate — exact status

*2026-07-19. This is the first fixed-shape clearing family in which order values are witness data,
not public descriptor coefficients. It is a real shielded/operator-visible proof family, not yet a
house-blind FHE/MPC service.*

## What exists

`metatheory/Market/DarkBazaarPrivateDescriptor.lean` authors one fixed product family:

- at most four orders, canonically padded to four committed slots;
- four price buckets;
- four-bit quantities (`0..15`);
- deterministic uniform-price clearing `p* = lowest argmax_p min(D[p],S[p])`;
- public statement `session, rule, orderRoot[0..8), p*, V*` (12 BabyBear felts);
- private witness: four `(bid/ask, limit, quantity)` orders and eight blind felts.

The four order records are injectively packed as four base-128 digits (< `2^28`). One
domain-separated full-arity Poseidon2 permutation absorbs
`(root-tag, session, rule, packed-book, blind[0..8), 0, 0, 0, 0)` and exposes all eight output lanes.
The four explicit zeros select the chip's arity-16 seed mode, ensuring every blind lane enters the
constrained permutation. There is no 31-bit intermediate commitment. The 8-felt output is ~248 bits wide, hence ~124-bit generic
collision work. Rust rejects every blind limb and session integer `>= BabyBear::ORDER` before field
conversion, so `b` and `b+p` cannot alias silently.

The Lean checker proves that acceptance fixes the rule and opened source root, and makes `(p*,V*)`
the exact clearing output, with strict dominance over every earlier bucket and no bucket above
`V*`. A second theorem reduces two distinct accepted openings to an explicit wide-root collision;
it does not claim that a finite-field Poseidon map is injective.

The emitted IR-v2 descriptor recomputes the packed book, all four demand/supply/volume buckets,
each minimum, the unique selected output, global maximality, and lowest-price tie-break. It uses one
wide Poseidon chip lookup and exposes exactly the 12 public felts above. Every semantic gate is
emitted on transition rows and copied to the last-row boundary.

`circuit-prove/src/dark_bazaar_private.rs` consumes the exact Lean-emitted JSON, builds the fixed
witness, and has two deliberately separate proof APIs:

- `prove_zk` / `verify_zk`: `DreggZkStarkConfig` + `HidingFriPcs`, with fresh OS-seeded leaf salts,
  random trace rows, and random FRI codewords. This is the privacy-bearing path.
- `prove_orders_zk`: the ergonomic shielded entry point, additionally rejection-sampling all eight
  canonical commitment-blind felts from OS entropy. Distributed producers can supply jointly sampled
  limbs explicitly through `try_from_orders_with_blinding`.
- `prove_non_hiding` / `verify_non_hiding`: explicit compatibility/debug path. Witness columns are
  not PIs, but its PCS is not hiding and it makes no privacy claim.

The hiding test checks the random commitment and every random opening are present, two proofs of
the same statement have different random commitments, and changed root, price, or volume refuses.
It also proves a changed private order against its own root and verifies that proof does not verify
against the original root.

## Privacy audience

The verifier/public sees only the 12-felt statement, not the order openings. The process that calls
`prove_zk` constructs the trace from plaintext orders and therefore sees them. This is Tier-1
shielding from proof consumers, not Tier-0 house blindness. The future no-viewer path must either:

1. have the existing collective-FHE/output-boundary-MPC process construct or compose this relation
   without any single plaintext prover; or
2. prove a source relation directly from the FHE/MPC transcript/commitment into this public root and
   clearing output.

Neither composition is implied by `HidingFriPcs`.

## Formal boundary and named residual

`darkBazaarPrivateN4K4_emitted_air_sound` starts from the actual `Satisfied2` denotation, an arbitrary
external public-input assignment, canonical field cells, and `ChipTableSoundN`. It extracts:

- every Lean-authored semantic gate vanishing modulo BabyBear;
- every PI binding against the external verifier-supplied vector; and
- all eight public root lanes equal to the genuine wide Poseidon permutation output.

The remaining theorem is named `DarkBazaarDescriptorToAccepts`: lift the fixed modular gate bundle
to integer equalities using the 4/6-bit bounds, decode the unique order one-hots, identify the four
computed volume buckets with `privateBook`, and conclude the semantic `Accepts` relation. This is a
formalization residual, not an absent runtime gate: the Rust producer proves the emitted AIR and its
positive/tamper tests exercise the actual verifier, but the final Lean descriptor-to-market theorem
must close before calling the entire functional-correctness chain proved.

## Assumptions and non-claims

- Commitment uniqueness is computational wide-Poseidon collision resistance, not field-level
  injectivity.
- The standard STARK/FRI and Poseidon chip-arithmetization soundness floors still apply.
- Hiding uses the repository's `HidingFriPcs`; the complete batch-STARK transcript simulator theorem
  remains a separate formal floor.
- This family is deliberately tiny (`N<=4,K=4,qty<16`). It is a protocol-completion beachhead, not a
  throughput envelope or arbitrary runtime book.
- It does not yet allocate per-order fills, bind settlement/ledger effects, authenticate order
  ingestion, or provide malicious-secure no-viewer operation.
- The emitted bytes are Lean-parity checked. An authorized repo-wide provenance/VK regeneration is a
  separate epoch/install action; this WIP lane does not silently perform it.

## Narrow verification

```text
cd metatheory
lake env lean Market/DarkBazaarPrivateDescriptor.lean
lake build Market.DarkBazaarPrivateDescriptor

cd ..
scripts/pbuild srot cargo nextest run -p dregg-circuit-prove dark_bazaar_private
```

The default/heavy workspace gauntlets are intentionally not part of this edit loop.

Current narrow results: Lean file + module build green with 8 kernel-clean keystones; emitted bytes
compare exactly against a fresh `EmitByName` line; the faithful-commitment AST gate passes; focused
`nextest --lib` is 3/3 green, with the two-proof hiding/tamper test taking 0.347 s after build.
