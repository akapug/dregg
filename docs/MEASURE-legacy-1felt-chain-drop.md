# Sizing the legacy 1-felt chain in the deployed WIDE rotated descriptors

> **2026-07-18 — SUPERSEDED: THE DELETION LANDED (Epoch 1).** The S2 stratum (the two rotated
> 1-felt Merkle–Damgård chains) is DELETED from both wide registries at the Lean emit
> (`RotWideCompactS2.compactS2`, per-member `compactOk` emit gate; ACK-gated regen). Measured on
> the deployed compact `transferVmDescriptor2R24`: **proof 556,810 → 375,053 B (−32.6%),
> committed cells 578,720 → 394,400 (−31.8%), width 2664 → 1704, chip table stays 256** —
> the corrected E1 numbers of `docs/ARCH-REVIEW-rotated-commitment-chip.md` §3.0, not this
> note's naive ceiling. ⚠ §5's re-root/orphan plan rests on a REFUTED premise (the "graft"
> misreading — the review's §1.1 correction): the wide chain was already self-rooted in the raw
> limb columns; the classifier below sweeps the two wide heads into "legacy". Do not execute §5.
> The measurement harness in `circuit/tests/legacy_chain_drop_measurement.rs` now measures the
> DEPLOYED compact member (the drop-variant machinery is gone with its subject).

**Status:** measurement note. The deletion this note sized has since LANDED (banner above).
**Artifact:** `circuit/tests/legacy_chain_drop_measurement.rs`
**Substrate:** no AIR is authored here. The variant is a mechanical deletion + column compaction of
an already-Lean-emitted descriptor (drop lookups, drop columns nothing reads, renumber). A real
version of this change is a Lean emitter change; this file only produces a number.

## 1. Ground truth at HEAD

`circuit/descriptors/rotation-wide-registry-staged.tsv :: transferVmDescriptor2R24`,
`trace_width = 2664`, 68 PIs, 5 tables (main arity 2617, poseidon2_chip arity 25, range, memory,
map_ops), 481 constraints: 262 lookups, 174 gates, 31 PI bindings, 14 transitions.

Top-level `hash_sites` is **empty** — the sites are compiled down to chip lookups. Classifying the
254 poseidon2-chip lookups by how many of the 16 input slots hold a genuine `Var`:

| input arity | count | role |
|---|---|---|
| 4  | 133 | the legacy 1-felt Merkle–Damgard absorption chain |
| 11 | 116 | the 8-felt wide commitment chain |
| 9  | 2   | the two wide-chain terminators |
| 2  | 3   | `hash2` joins hanging off the 1-felt chain |

(The brief said "118 arity-11, 3 arity-2". The true split at HEAD is 116 arity-11 + 2 arity-9.)

This distribution is **identical across all 57 members** of the wide registry (129 or 137 arity-4 on
four members; 116 arity-11 and 2 legacy-seeded wide sites on every single one). Total arity-4 sites
across the registry: **7573**.

## 2. THE FINDING: the 1-felt chain is load-bearing, not an over-proof

The producer/consumer graph over the 254 chip lookups:

```
arity-4  -> arity-4  : 127 edges    the 1-felt chain proper
arity-4  -> arity-2  :   3 edges    hash2 joins (one output lands on PI 45)
arity-4  -> arity-11 :  16 edges    = 2 sites x 8 lanes  <-- THE SEED
arity-11 -> arity-11 : 912 edges    the 8-felt chain proper
arity-11 -> arity-9  :  16 edges    the two terminators
```

The last two arity-4 sites (chain indices 131, 132) expose **all eight** of their permutation lanes,
and those sixteen columns are exactly `inputs[0..8]` of the two arity-11 lookups that open the
BEFORE and AFTER 8-felt commitment chains.

**The published 8-felt commitment is rooted in the 1-felt chain's terminal permutation state.**

Additionally, `pi_binding{row: last, col: 88, pi_index: 8}` binds a legacy-chain digest column
directly to a public input — a legacy digest *is* published by this descriptor.

So the premise "the 133 sites survive only because the Lean soundness keystone is typed to walk
them" is **false at HEAD**. They are a data dependency of the thing we publish. Deleting them does
not remove an over-proof; it un-roots the commitment.

## 3. But the chain is still mostly redundant — and here is the exact surplus

Distinct trace columns each family absorbs as *fresh* input (not produced by another site):

| | distinct fresh columns |
|---|---|
| absorbed by the arity-4 chain | 397 |
| absorbed by the arity-11 chain | 348 |
| **overlap** | **348** |
| absorbed ONLY by the arity-4 chain | **49** |

The wide chain already re-absorbs every limb the 1-felt chain eats, save **49**. The 1-felt chain's
entire non-redundant content is those 49 limbs plus the seed relation.

**Therefore the sound refactor is well-defined:** re-root the wide chain on a domain constant
instead of the legacy terminal lanes, and absorb the 49 orphan limbs into additional arity-11 sites.
The arity-11 sites take 3 fresh felts each (348 fresh / 116 sites), so that is **~17 new sites**
replacing **133 dropped ones — a net −116 permutations and roughly −928 main columns per member.**

This is a real win, and it means the drop-everything variant measured below is a *close* proxy: it
overstates the sound refactor by ~17 sites / ~136 columns.

**Cost side:** this changes the published commitment value, so it is a VK-epoch flag day across all
57 members, plus a re-typing of `wideEmbedded_sound_v1` and the whole rotation/wide emit family in
Lean. It is not a quiet optimization.

## 4. The variant, and what "it proves" does and does not mean

`drop_legacy_chain` removes the 133 arity-4 lookups, then removes exactly the columns that go dead
*because of that removal* (columns already unread in the deployed descriptor are retained, so the
width delta is attributable to the chain and not to incidental dead-column GC), then renumbers.

Because the transform only deletes constraints and columns no surviving constraint reads, it is
**satisfiability-preserving by construction**. The variant proving is a sanity check on the
transform, not evidence that the chain is unnecessary — the real evidence is §2, and it points the
other way.

## 5. Measurements

Machine: this laptop, load average ~7.6 at run time (it had been ~93 earlier with other agents
active; these numbers were taken after it quieted). Release build, production `ir2_config`,
best-of-3. `prove_vm_descriptor2` self-verifies before returning, so prove time includes one
verification — both arms pay it.

The variant **PROVED and VERIFIED** through the real audited path (`prove_vm_descriptor2` /
`verify_vm_descriptor2`, plonky3 backend). As noted in §4 this is expected: the transform is
satisfiability-preserving by construction.

Widths and heights below are READ OFF THE PROOF (`opened_values.instances[i]` and `degree_bits`),
not hand-computed. Only the base-field-equivalent totals are arithmetic on those measured values
(`permutation` columns are degree-4 extension elements, so they count 4x).

### Per-instance committed geometry

| instance | | deployed | chain-dropped |
|---|---|---|---|
| 0 main | log2(height) | 6 (64) | 6 (64) |
| | main columns | 2726 | 1655 |
| | permutation columns (ext) | 1144 | 612 |
| | base-eq width `m + 4p` | 7302 | 4103 |
| 1 poseidon2 chip | **log2(height)** | **8 (256 rows)** | **7 (128 rows)** |
| | main columns | 386 | 386 |
| | permutation columns (ext) | 12 | 12 |
| 2 range | log2(height) | 4 (16) | 4 (16) |

### The table

| quantity | deployed | chain-dropped | absolute | percent |
|---|---|---|---|---|
| main `trace_width` | 2664 | 1593 | −1071 | **−40.2%** of main width |
| committed main cols (instance 0) | 2726 | 1655 | −1071 | −39.3% |
| committed aux cols (instance 0, ext) | 1144 | 612 | −532 | −46.5% |
| committed base-eq width, all instances | 7754 | 4555 | −3199 | −41.3% |
| **committed cells (width x height, all instances)** | **578,720** | **318,432** | **−260,288** | **−45.0%** |
| poseidon2 chip table height | 256 | 128 | −128 | −50.0% |
| proof size | 556,810 B | 355,210 B | −201,600 B | **−36.2% of proof bytes** |
| — `opened_values` | 122,820 B | 74,503 B | −48,317 B | −39.3% |
| — `opening_proof` | 425,674 B | 276,180 B | −149,494 B | −35.1% |
| — `global_lookup_data` | 8,193 B | 4,400 B | −3,793 B | −46.3% |
| — commitments | 119 B | 123 B | +4 B | (fixed) |
| prover wall clock (best of 3) | 637.9 ms | 344.9 ms | −293.0 ms | **−45.9% of prove time** |
| prover (median / max) | 641.0 / 643.1 ms | 351.9 / 360.4 ms | | variance <1% |
| verifier wall clock (best of 3) | 27.11 ms | 14.40 ms | −12.71 ms | **−46.9% of verify time** |

Be precise about the denominators: −40.2% is of *main trace width*; −36.2% is of *proof bytes*;
−45.9% is of *prover wall clock*. These are different denominators and they do not transfer.

## 6. Honest read

**Fixed costs do NOT dominate.** That was the failure mode this measurement existed to catch, and
it did not happen: proof bytes fall 36%, prover time 46%, verifier time 47%. The Merkle
commitments are the only genuinely fixed line (119 -> 123 B). So the *ceiling* on this campaign is
genuinely large.

**But the ceiling is not the yield, for two reasons, and the second one is nasty.**

1. **~17 sites come back.** The sound refactor (§3) must re-absorb the 49 orphan limbs into ~17
   new arity-11 sites. That is ~+136 main columns, so main width lands near 1736 rather than 1593
   — roughly −35% instead of −40%. Modest erosion.

2. **The chip-table halving is on a power-of-two cliff and is probably LOST.** The measured
   256 -> 128 chip height is worth a lot (it is a whole committed table halving, and the chip
   table is 386 columns wide). But the deployed descriptor issues 254 chip queries per row and
   the drop takes that to 121 — under the 128 boundary. The sound refactor lands at
   ~254 − 133 + 17 = **~138 queries, which is above 128**, so it would very likely keep a
   256-row chip table and forfeit that entire component. I did not measure this: I cannot author
   the ~17 replacement arity-11 sites here, because AIR belongs in Lean. **This is the single
   biggest open question and it should be settled by emitting the real Lean variant and reading
   its `degree_bits`, before anyone commits to the campaign.**

   Removing the chip halving from the ledger costs 55,552 committed cells (17.5% of the
   chain-dropped total), and the chip table is disproportionately expensive per row.

**So the realistic yield is meaningfully below the measured ceiling** — plausibly ~25-30% on proof
bytes and prover time rather than 36%/46%, and that estimate is soft precisely because of the
power-of-two cliff.

**Against that, the cost is not small:** the published commitment value changes, so this is a
VK-epoch flag day across all 57 wide members plus every light client, and it requires re-typing
`wideEmbedded_sound_v1` and the rotation/wide emit family in Lean.

**Recommendation.** Do not launch the campaign on these numbers. Launch one cheap Lean lane first:
emit the re-rooted wide transfer (wide chain seeded on a domain constant, 49 orphan limbs absorbed
into new arity-11 sites), prove it, and read its `degree_bits[1]`. If the chip table stays at 256,
the yield is roughly halved and the flag-day cost probably is not worth it. If it lands at 128, the
campaign is strong. That one lane is the decider, and it is far cheaper than the campaign.

Secondary note worth banking regardless: the ~31-bit legacy commit is **not** as retired as the
brief assumed. `pi_binding{last, col 88, pi 8}` publishes a legacy-chain digest, and the 8-felt
commit is a function of the 1-felt chain's terminal state. Whatever the perf decision, that is a
soundness-story correction — the 8-felt commitment does not stand on its own.
