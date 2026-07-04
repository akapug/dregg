# Codex FINAL re-review — IVC #1 same-endpoint close (2026-06-25): NO CRITICAL HOLE

VERDICT: for the K-fold segment path, NO critical soundness hole — the same-endpoint mixed-root forgery is GENUINELY CLOSED under the Poseidon2 truncated-output commitment assumption.

## Why sound
- Bug A (dropped v_j==0): NOT reopened. expose_claim reads the FULL ext tuple [idx,c0,c1,c2,c3] on the WitnessChecks bus (bus-bound to the W24 output, so c1/c2/c3 can't be freely chosen), exposes only c0 as the public. A forgery requires a collision in the exposed digest.
- THE DIGEST IS NOT ~31-bit coeff-0-only: dregg compares a 7-felt segment claim — genesis, final, count, + FOUR BabyBear digest lanes (ivc_turn_chain.rs:224 + :1963). ~124-bit digest collision resistance.
- Bug B (off-bus capacity): AIR-constrained (noncompact Poseidon2 AIR ties absent next-row inputs to the prior row output; executor mirrors). Sound.

## Residuals (codex, NONE critical)
- MEDIUM (scope): the ONLINE ACCUMULATOR path (accumulator.rs:171/819/916) is still single-felt/zero-padded, explicitly scoped out — do NOT generalize the K-fold close to it. The named separate follow-up.
- LOW (doc drift): comments at expose_claim_air.rs:23 + circuit_builder.rs:486 still describe the old scalar-only expose — fix them (they now contradict the soundness-critical design).
- LOW (margin): the checked digest is 4 BabyBear lanes (~124 bit), not the full D-coeff tuple. Avoids the old one-felt hole; widening beyond 4 lanes would give a conservative 128-bit story.
