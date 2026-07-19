# Private raid assignment N4K4

`private-raid-assignment-n4::admissible-max-lex-v1` is the fixed-shape,
Lean-authored role-assignment organ for four public seats and four canonical
roles.  It is intended for raid composition, party/guild role allocation,
matchmaking, and other small-team assignments where preferences and hard role
constraints should remain hidden from proof consumers.

## Exact relation

For every `(seat, role)` pair the private witness contains two independent
values:

- a suitability score in `0..3`;
- an admissibility bit, where `1` means the assignment is permitted.

These are deliberately independent.  Score zero is a weak preference and is
not equivalent to a forbidden role.

The accepted public role vector must:

1. assign exactly one role to every seat and every role to exactly one seat;
2. use only private admissible edges;
3. maximize the sum of the four selected suitability scores over all 24 role
   permutations; and
4. among equal-score maximizers, be the lexicographically lowest role vector
   in public seat order.

The tie rule makes the result deterministic.  Lean proves that two assignments
satisfying this specification for the same private input are equal.

## Public ABI

The public statement contains exactly 14 canonical BabyBear felts:

| PI | Meaning |
|---:|---|
| 0 | session |
| 1 | fixed rule identifier `1380007220` (`RAM4`) |
| 2..9 | all eight lanes of the faithful private-input root |
| 10..13 | assigned role for public seats 0..3 |

No aggregate score, per-seat score, admissibility bit, blind, or losing
assignment score is public.  The Rust verifier returns a compact
`VerifiedAssignment` containing only this public ABI after successful HidingFri
verification.

## Private ABI and faithful commitment

The private input has 16 two-bit suitability scores, 16 independent
admissibility bits, and eight canonical blind felts.  Each participant's four
scores and four admissibility bits form one injective 12-bit pack.  Two
participant packs form each of two injective 24-bit BabyBear felts.

The full-arity-16 Poseidon2 preimage is exactly:

```text
[RAI4, session, RAM4, packedSeats01, packedSeats23,
 blind0, blind1, blind2, blind3, blind4, blind5, blind6, blind7,
 0, 0, 0]
```

All eight output lanes are public.  Lean proves the participant pack and paired
pack encodings injective; two distinct private openings of one accepted root
therefore reduce to a root collision rather than a lossy packing ambiguity.

## AIR and theorem boundary

The emitted fixed AIR has 299 trace columns, 14 public inputs, one genuine
full-arity Poseidon2 lookup, and 701 constraints including last-row copies.
It derives one-hot seat/role assignment, chosen-edge admissibility, a hidden
four-bit chosen total, and one bounded difference certificate for each of the
24 permutations.  A feasible candidate must have a nonnegative score
difference.  If it is lexicographically earlier than the chosen assignment,
an equal-score difference is forbidden.

The exact semantic layer proves:

- exhaustive coverage of all 24 role permutations;
- global score maximality and deterministic lexicographic tie-breaking;
- uniqueness of the accepted assignment; and
- checker soundness for the exact relation.

The current emitted-AIR theorem
`privateRaidAssignmentN4_emitted_air_sound` extracts every modular semantic
gate, the faithful root lookup, and every public-input pin from `Satisfied2`.
The finite modular-to-integer bridge from those facts to the exact `OptimalLex`
relation is the remaining proof gate before production registration.  Until
that bridge is closed, this descriptor is an isolated implementation artifact,
not a production semantic theorem.

## Visibility boundary

The shipped Rust API is honest Tier 1:

- `prove_zk` uses `HidingFriPcs`, so the proof does not reveal the private
  matrix to the verifier;
- the process assembling the trace necessarily sees scores, admissibility, and
  blinds; and
- no non-hiding public proof API is exposed.

Tier 0 input privacy would require distributed input assembly, MPC, or another
mechanism that prevents one coordinator from seeing the complete matrix.  That
is a separate protocol layer and is not implied by HidingFri.

## Tested teeth

The isolated Rust suite currently covers six boundaries:

- score range, canonical blind, and no-feasible-assignment rejection;
- score-zero versus forbidden-role distinction;
- global optimizer output and lexicographically lowest ties;
- faithful-root binding for score, admissibility, and blinding changes;
- AIR rejection of an admissible but globally suboptimal assignment after
  rebuilding a consistent row and public root;
- AIR rejection of a lexicographically later equal-score assignment; and
- HidingFri prove/verify plus root, session, rule, duplicate-role, and role-vector
  public-statement tampering.

The isolated remote run passed all six tests.  Registration and ordinary crate
module exposure intentionally wait on the emitted-AIR-to-`OptimalLex` proof
gate above.

## Intended consumption

A party, guild, raid, or matchmaking coordinator collects the four private
matrices, constructs the deterministic assignment, and publishes only the
public statement and HidingFri proof.  Every consumer verifies the proof and
uses only the resulting `VerifiedAssignment`.  Consumers must not accept a
bare role vector or a coordinator's claimed total score.

This organ chooses the best assignment for supplied inputs.  It does not prove
that participants reported preferences honestly, that a coordinator did not
omit a participant, or that Tier-1 input handling concealed the matrix from the
coordinator.  Identity/attestation, input-set binding, and Tier-0 collection
belong to the surrounding game protocol.
