# Codex re-review #2 — IVC #1 fix (2026-06-24)

VERDICT: the exposed-claim channel is SOUND (the old forgery rejects), but #1 NOT fully closed — a DEEPER mixed-root hole remains.

**Verdict**
Not fully closed.

The new exposed-claim channel appears locally sound: a prover cannot freely choose `expose_claim.public_values` without satisfying the WitnessChecks lookup and the AIR equality. The exact prior witness test shape, “A root + external B binding proof + B claims,” should now reject.

But there is still a critical whole-chain gap: tooth 4 links the carried claim to the binding leaf folded into the root, but I do not see any constraint linking that binding leaf’s `(old_root, new_root)` rows to the descriptor leaves folded in the same root.

**Critical Residual**
A malicious prover can build a same-shape root containing:

1. valid descriptor leaves for history A, from the independent descriptor wrapping path at [ivc_turn_chain.rs:1300](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1300)
2. a valid binding leaf for history B, wrapped with exposed claims at [ivc_turn_chain.rs:1313](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1313)
3. the normal aggregation tree, whose hook only re-exposes the child `expose_claim` targets at [ivc_turn_chain.rs:1416](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1416)

The aggregation circuit verifies left and right children independently, then invokes the expose hook; it does not add any cross-child equality between descriptor public roots and binding rows: [recursion.rs:751](/Users/ember/dev/plonky3-recursion/recursion/src/recursion.rs:751).

Then verification passes:

- tooth 1: same root circuit shape/VK, because values are excluded from the fingerprint and only shape/preprocessed material is pinned: [plonky3_recursion_impl.rs:650](/Users/ember/dev/breadstuffs/circuit-prove/src/plonky3_recursion_impl.rs:650)
- tooth 2: carried B binding proof verifies against B claims: [ivc_turn_chain.rs:1520](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1520)
- tooth 3: mixed root verifies: [ivc_turn_chain.rs:1537](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1537)
- tooth 4: root exposes B, carried claim is B, so equality passes: [ivc_turn_chain.rs:1545](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1545)

That is still a false whole-chain claim if “whole-chain” means the descriptor/execution leaves form the claimed root chain.

**Sound Pieces**
The channel itself looks binding:

- `ExposeClaimExecutor` records actual witness ids and current witness values, not free outputs: [expose_claim.rs:80](/Users/ember/dev/plonky3-recursion/circuit/src/ops/expose_claim.rs:80)
- preprocessing records the witness index and increments `ext_reads`, so the original `PublicAir` writer sends one extra copy: [expose_claim.rs:103](/Users/ember/dev/plonky3-recursion/circuit/src/ops/expose_claim.rs:103), [common.rs:350](/Users/ember/dev/plonky3-recursion/circuit-prover/src/common.rs:350)
- the `ExposeClaimAir` reads `WitnessChecks` with `read_mult` and enforces `public_value == v0` on active lanes: [expose_claim_air.rs:152](/Users/ember/dev/plonky3-recursion/circuit-prover/src/air/expose_claim_air.rs:152), [expose_claim_air.rs:168](/Users/ember/dev/plonky3-recursion/circuit-prover/src/air/expose_claim_air.rs:168)
- global lookup sums are checked to zero: [batch_stark.rs:1205](/Users/ember/dev/plonky3-recursion/recursion/src/verifier/batch_stark.rs:1205), [recursive.rs:64](/Users/ember/dev/plonky3-recursion/recursion/src/traits/recursive.rs:64)

The padding gate also looks okay: active is `-read_mult`, real rows get `-1`, and changing that requires changing committed preprocessed data/VK material: [expose_claim_air.rs:162](/Users/ember/dev/plonky3-recursion/circuit-prover/src/air/expose_claim_air.rs:162), [expose_claim.rs:75](/Users/ember/dev/plonky3-recursion/circuit-prover/src/batch_stark_prover/expose_claim.rs:75).

**Test Gap**
The flipped test at [ivc_turn_chain_rotated.rs:595](/Users/ember/dev/breadstuffs/circuit-prove/tests/ivc_turn_chain_rotated.rs:595) covers only the old external cross-pairing shape. It does not cover the mixed-root attack above. I would add a test that constructs descriptor leaves from A, binding leaf from B, aggregates them into one root, carries B’s binding proof/claims, and asserts rejection. I expect current code to accept unless there is another cross-leaf equality constraint outside the reviewed paths.
tokens used
302,791
**Verdict**
Not fully closed.

The new exposed-claim channel appears locally sound: a prover cannot freely choose `expose_claim.public_values` without satisfying the WitnessChecks lookup and the AIR equality. The exact prior witness test shape, “A root + external B binding proof + B claims,” should now reject.

But there is still a critical whole-chain gap: tooth 4 links the carried claim to the binding leaf folded into the root, but I do not see any constraint linking that binding leaf’s `(old_root, new_root)` rows to the descriptor leaves folded in the same root.

**Critical Residual**
A malicious prover can build a same-shape root containing:

1. valid descriptor leaves for history A, from the independent descriptor wrapping path at [ivc_turn_chain.rs:1300](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1300)
2. a valid binding leaf for history B, wrapped with exposed claims at [ivc_turn_chain.rs:1313](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1313)
3. the normal aggregation tree, whose hook only re-exposes the child `expose_claim` targets at [ivc_turn_chain.rs:1416](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1416)

The aggregation circuit verifies left and right children independently, then invokes the expose hook; it does not add any cross-child equality between descriptor public roots and binding rows: [recursion.rs:751](/Users/ember/dev/plonky3-recursion/recursion/src/recursion.rs:751).

Then verification passes:

- tooth 1: same root circuit shape/VK, because values are excluded from the fingerprint and only shape/preprocessed material is pinned: [plonky3_recursion_impl.rs:650](/Users/ember/dev/breadstuffs/circuit-prove/src/plonky3_recursion_impl.rs:650)
- tooth 2: carried B binding proof verifies against B claims: [ivc_turn_chain.rs:1520](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1520)
- tooth 3: mixed root verifies: [ivc_turn_chain.rs:1537](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1537)
