# Decider Experiments D1–D7 — Rotated Commitment Chip Architecture

Date: 2026-07-18. Charter: `docs/ARCH-REVIEW-rotated-commitment-chip.md` (commit `1b6ef98ef`),
§Stage-0. Executed starting at HEAD `c68c4f5a9`; the co-tenant S2-deletion lane landed
Lean-side commits (through `df85c49ca`, incl. `RotWideCompactS2`) during the window, with
ZERO diff to the measured surfaces — `circuit/src/descriptor_ir2.rs`,
`circuit/src/effect_vm/trace_rotated.rs`, and the deployed wide staged registry, pinned at
`circuit/descriptors/rotation-wide-registry-staged.tsv` sha256 `07fa7e870bbf…d1fc7d86` and
verified unchanged before and after every measurement run (the measured baseline proof also
reproduced the MEASURE doc byte-for-byte, 556,810 B).

Instruments (measurement only; no deployed emit/descriptor/registry change):

- `circuit/tests/decider_experiments.rs` — D1, D2, D3, D6, D7 (this lane's named file).
- Two read-only repo censuses (D4, D5), summarized here with file:line evidence.

Run:

```text
CARGO_TARGET_DIR=/tmp/decider-check cargo test -p dregg-circuit --release \
  --test decider_experiments -- --nocapture
```

Verdict summary (details per section):

| # | experiment | verdict | gates |
|---|---|---|---|
| D1 | chip_hist dedup | **252 unique of 16,256 queries at HEAD (essentially zero dedup) → 256; post-S2 exactly 134 → 256; simulated rate-8 bundle 50–60 unique → HEIGHT 64 for the transfer family** | chip-64 conditionality (R1): resolved for the 34-member transfer class |
| D2 | LogUp aux provenance | **mechanism CONFIRMED (1 interaction = 1 ext col = 4 base cols, flattened at commit) + a 4× accounting error found in the review's aux cell figures (50.6% → 20.9%)** | the aux lever bound; every design's cell arithmetic |
| D3 | 2617 ≠ 2664 audit | **declared main arity is INERT in the Rust realization (byte-identical proofs under mutation)** | safe to retire the scar in the regen |
| D4 | external v9 holders | **no live external holder evidenced; UNKNOWN residue = hbox disk images + fixture testnet contract** | the Epoch-2 value flip |
| D5 | PI 9–41 census | **H4 retirement NOT blocked; ~7 live slots must be re-homed; record digest decodable as-is** | H4 retirement + PI-map regen |
| D6 | per-member cliff table | **post-S2 all 57 stay 256; post-bundle 34/57 → 64 and 23/57 → 128, with 19 of the 23 missing 64 by only 1–2 permutations; the 256-vs-512 tension localizes to the 23 members issuing >256 queries at HEAD** | honest per-member Epoch-2 claims |
| D7 | preprocessed-column spike | **GREEN end-to-end at the pin under production FRI knobs, incl. tamper rejection and LogUp-fields-over-preprocessed; +9,043 B fixed per proof for the extra round; the recursion fork also carries it** | B-vs-F floor-shape mechanism choice: B's mechanism unblocked |

---

## D1 — chip_hist dedup: how many unique permutations does the chip table hold?

**What was run.** The honest wide transfer witness is minted through the production dispatcher
(`generate_rotated_effect_vm_descriptor_and_trace_wide`), lanes are welded by the deployed
`fill_chip_lanes` (pub), and every one of the 254 chip-lookup tuples is evaluated on every row
— the exact key set `build_traces`' `chip_hist` deduplicates
(`circuit/src/descriptor_ir2.rs:4162-4210`; the transfer has no map ops and the fact bus has
zero senders, so absorb tuples are the whole histogram). Faithfulness is checked two ways:
every evaluated output octet must equal the genuine permutation of the evaluated inputs
(`chip_absorb_all_lanes`), and `next_pow2(unique)` must equal the chip instance height read
off a real proof's `degree_bits`.

**Raw numbers.**

```text
D1: site tag histogram      = {2: 3, 4: 133, 11: 118}
D1: site var-arity histogram = {2: 3, 4: 133, 9: 2, 11: 116}
D1: row-varying sites = 120 (distinct-tuples-per-site histogram {1: 134, 2: 120})
D1: DEPLOYED chip_hist unique permutations = 252 (254 sites x 64 rows = 16256 queries) -> chip height 256
D1: unique-by-tag = {2: 3, 4: 131, 11: 118}
D1: transitively-dead (S2) sites = 120 by tag {2: 2, 4: 118}
D1: surviving sites that vary by row = 60 (tags {4: 1, 11: 59})
D1: rows where any varying site deviates from its row-0 tuple = {1..63}
D1: POST-S2 unique permutations (all rows) = 134 (of 134 surviving sites) -> chip height 256
D1: wide chain 0/1 fresh stream = 179 felts each (4 head limbs + 174 body + iroot)
D1: rate-8 sim steps = 46 total; unique = 46 under shared AND per-object seeds
D1: non-wide survivors (post-S2, minus wide chains+heads) unique = 14
D1: EPOCH-2-A (rate-8 blocks, caveat kept, H4 kept) unique ~= 60 -> chip height 64
D1: EPOCH-2-B (+caveat rate-8)                      unique ~= 54 -> chip height 64
D1: EPOCH-2-C (+H4 retired)                         unique ~= 50 -> chip height 64
```

**Findings.**

- **The deployed table holds 252 unique permutations** (16,256 queries dedup 65:1 by
  multiplicity, but only 2 SITE-level coincidences — 133 tag-4 sites → 131 unique). The
  height-256 bracket is confirmed at the dedup level, and `next_pow2(unique)` equals the
  height read off the real proof's `degree_bits[1]` (asserted in-test).
- **A fill-structure artifact the review's "row-constant" description misses:** 120 sites
  take exactly TWO tuple values — row 0 vs rows 1–63 — and they are precisely the
  AFTER-side strata (the AFTER S2 chain among the dead; the AFTER wide head + 59 AFTER
  wide sites among the survivors). Every "second" tuple coincides with a BEFORE-side
  tuple, so the table is unchanged — but any future instrument that samples only row 0,
  or assumes tuple row-constancy, will miscount. (Interactions are row-constant in
  COUNT — 254/row — which is all the aux accounting needs.)
- **Post-S2: exactly 134 unique over all rows — zero dedup among survivors.** Epoch 1's
  "chip stays 256" is now dedup-proven, not query-counted. It also validates D6's static
  no-dedup counts as exact for this classification.
- **The simulated rate-8 bundle lands the transfer family at chip height 64 with slack:**
  two 179-felt streams → 23 steps/chain, 46 absorb permutations, no cross-chain dedup
  under either seed discipline (the streams diverge at the balance limb); Epoch-2
  variants measure 60 / 54 / 50 unique against the 64 cliff (slack 4–14).

**Verdict.** R1 is RESOLVED for the transfer-shaped class: chip height 64 holds for the
Epoch-2 bundle on these members (all three bundle variants), and every §3 number
conditioned on "chip-64" is unconditional for the 34-member class (see D6 for the other
23). Epoch 1 keeps chip 256 everywhere.

**Gates.** The chip-height-64 conditionality (open question R1) on every §3 Epoch-2 number in
the review; the 256-vs-512 static tension (localized by D6); the Stage-3 shape decision's
cell arithmetic.

---

## D2 — LogUp aux provenance: where the 1144 "permutation columns" come from

**What was run.** One real proof of the deployed transfer; per-instance
`opened_values.instances[i].permutation_local.len()` and the per-bus census of
`proof.global_lookup_data` (one `LookupData { name, aux_column, … }` per **global
interaction** — the exact interaction list, read off the wire object, no reconstruction).
Cross-checked against the pinned p3-lookup/batch-stark sources.

**The mechanism, pinned (p3 checkout `82cfad7`, the locked rev — verified in `Cargo.lock`):**

1. One `lookup_key`/`send`/`receive`/`table_entry` = ONE global interaction = ONE aux column
   **in the extension field** (`p3-lookup/src/types.rs:59-89`: `col += 1` per interaction —
   no splitting by field count anywhere in p3-lookup or batch-stark).
2. The ext-valued running-sum matrix is **flattened to base before commitment**
   (`p3-batch-stark/src/prover.rs:269`: `generated_perm.flatten_to_base()`), i.e. one
   interaction = 4 committed base columns at `EXT_DEGREE = 4`. **This is the
   "4-base-cols-per-interaction" accounting: CONFIRMED, with the flatten as the mechanism.**
3. `permutation_local.len()` counts columns of the **flattened base matrix** (each opened as
   one extension value), so the measured 1144 = 4 × 286 interactions, and the chip's 12 =
   4 × its exactly-3 interactions (`BUS_P2` + `BUS_P2_1` + `BUS_FACT` table entries,
   `descriptor_ir2.rs:2791-2824`) — an independent confirmation, since the chip's
   interaction count is known statically.

**Raw numbers.**

```text
D2: degree_bits = [6, 8, 4]
D2: instance 0 (main): h=2^6 main_cols=2726 perm_opened(base cols)=1144 quotient_chunks=2
D2: instance 1 (chip): h=2^8 main_cols=386  perm_opened(base cols)=12   quotient_chunks=8
D2: instance 2 (byte): h=2^4 main_cols=2    perm_opened(base cols)=4    quotient_chunks=2
D2: instance 0: 286 global interactions by bus = {"ir2_byte": 32, "ir2_p2": 254}
D2: instance 1:   3 global interactions by bus = {"ir2_fact": 1, "ir2_p2": 1, "ir2_p2_narrow": 1}
D2: instance 2:   1 global interactions by bus = {"ir2_byte": 1}
D2: proof bytes = 556810 (global_lookup_data 8193 B)   [byte-identical to the MEASURE baseline]
```

(In-test assertion: `permutation_local.len() == IR2_EXT_DEGREE × global_lookup_data[i].len()`
holds on every instance. Bonus datum: quotient chunks main 2 / chip 8 / byte 2 — the chip's
8 at degree 7 confirms the review's verified d∈{6..9}→8 schedule.)

**The accounting error this exposes in the review.** The review (and
`docs/MEASURE-legacy-1felt-chain-drop.md` §5 before it) treats the 1144 opened permutation
values as 1144 **extension** columns and books them at `4×` base-eq
(`main 7302×64`, "254 row-constant chip interactions × ~17.5 base-eq × 64 rows = 292,864
cells = 50.6%"). The committed object is 1144 **base** columns. Corrected committed-cell
decomposition of the deployed transfer proof:

| term | review's figure | corrected | corrected share |
|---|---|---|---|
| main base width | 174,464 | 174,464 | 49.9% |
| main LogUp aux | **292,864 (50.6%)** | **73,216** (1144 base cols × 64) | **20.9%** |
| chip table | 111,104 | 101,888 (398 base cols × 256) | **29.1%** |
| byte table | 288 | 96 (2 + 4 base cols × 16 rows) | 0.03% |
| **total** | 578,720 | **349,664** | |

Consequences, stated precisely:

- **"The in-row absorption tax is the single largest line item (50.6%)" is REFUTED as a
  committed-cells claim.** Corrected, the main base width is the largest term (49.9%), the
  chip is second (29.1%), and the aux is third (20.9%). The *wire* claims are unaffected —
  the byte model was calibrated per **opened column**, and 1144 opened columns is the true
  opened count either way; the −532-column measured drop delta is likewise real.
- Every design's committed-cells figure (and the 82,720-cell floor) inherits some of the ×4
  on its aux terms and needs re-derivation before it is quoted again; the *byte* figures and
  the lever *ranking by wire* survive.
- The 4.37→4.74 "ext-cols/interaction drift" the review flagged as ±10% model noise is now
  exact and closed-form: `aux_base_cols = 4 × (chip_lookups + non-chip interactions)`, and
  the drift was only the fixed non-chip term (32 byte-bus interactions on this member)
  diluted over fewer chip lookups on the drop variant (612 = 4×(121+32), 1144 = 4×(254+32);
  the review's ratios were `1144/262` and `612/129` over *descriptor lookups*).
- **Batching headroom:** at this pin, aux batching (many tuples in one aux column) exists
  ONLY for `push_local_interaction` (intra-AIR); every cross-table bus message is 1
  interaction = 1 ext col = 4 base cols, non-negotiable without gadget work. The review's
  "aux lever … currently ±2×" is therefore bounded: there is no in-realization batching
  knob to turn; the aux cost falls only by sending fewer interactions (rate-8, absorb
  instance) — which both Epoch-2 shapes already do.

**Verdict.** Mechanism CONFIRMED (1 interaction = 1 ext col = 4 base cols, flatten at
`prover.rs:269`); the review's aux **cell** accounting is 4× overstated and its "dominating
term" claim inverts; wire-side conclusions stand.

**Gates.** Bounds the aux lever for both Stage-3 branches; demotes the aux-tax motivation of
the floor shape from "50.6% of cells" to 20.9% of cells (the wire motivation — ~188 B per
absorbed column — is untouched and remains the operative argument).

---

## D3 — the 2617 ≠ 2664 ≠ 2726 width triple

**What was run.** Parse the deployed member (declared main arity 2617, `trace_width` 2664);
prove the honest witness; read committed main width off the proof (2726 =
`trace_width` + the range-decomposition appendage built by `MainLayout::build`,
`descriptor_ir2.rs:1254-1301`). Then the falsifier: set `tables[0].arity = 99_999`, re-prove,
cross-verify both proofs under both descriptors, and byte-compare.

**Raw numbers.**

```text
D3: widths: declared main arity 2617 != trace_width 2664 != committed main cols 2726
D3: proofs byte-identical under arity mutation (556810 B); cross-verification accepted
    BOTH ways (mutant proof under deployed descriptor, deployed proof under mutant)
```

**Code-level account (read, then confirmed by the falsifier):**

- The v2 prove/verify path bounds every constraint against `trace_width` alone
  (`check_descriptor2`, `descriptor_ir2.rs:1356-1481`) and sizes the committed matrix from
  `MainLayout::build`, which starts at `trace_width` (`:1254`). The parsed `TableDef2.arity`
  of the MAIN table is stored and **never read** anywhere in the realization.
- The discrepancy's origin is emitter-layer drift: the Lean weld layers L6 (membership
  teeth, +2) and L9 (gentian refuse, +45) bump `trace_width` without touching the main
  TableDef, while the Rust-side umem welds DO sync it
  (`effect_vm_descriptors.rs:1071-1075, 1135-1139`) — two conventions coexisting.
- The only place the 2617 binds anything is the registry fingerprint (the FP/VK pins hash
  the JSON text), which any regen re-pins anyway.

**Verdict.** The declared main-table arity is INERT in the Rust realization — proven by the
falsifier, not just by reading: an absurd mutation (99,999) produces byte-identical proofs
that cross-verify in both directions. The width triple decomposes as: 2617 = the L0–L5
emitter-layer fossil (L6/+2 and L9/+45 bumped `trace_width` without syncing the TableDef,
while the Rust-side umem welds do sync theirs); 2664 = the real bound on every constraint;
2726 = `MainLayout::build`'s committed width (trace_width + 62 range-decomposition columns,
read off the proof). The scar is NOT load-bearing by accident.

**Gates.** The review's U4 ("audit before the regen retires the class"): retiring the scar in
the Epoch-1 regen is safe; nothing in the Rust realization is load-bearing on the fossil
value. The Lean-side TableDef should be synced (or the field deleted) in the same regen.

---

## D4 — external v9 commitment holders (read-only census)

**What was run.** A full-repo consumer census of the v1 H4 commit / PI 8 (`pi::NEW_COMMIT`)
and the v9 commitment family, plus every durable-persistence surface for commitments.
"v9" concretely = `CANONICAL_COMMITMENT_CONTEXT = "dregg-cell:canonical-state-commitment v9"`
(`cell/src/commitment.rs:110`), covering both the BLAKE3 whole-cell form and the Poseidon2
`wireCommit` (`compute_canonical_state_commitment_v9_felt/_felt8`, `commitment.rs:1320-1377`)
that the wide 16-felt PI tail publishes.

**Findings (consumer classes; full table in the census record):**

- **LIVE consumers of PI 8 / H4:** the executor's atomic custom-leaf off-AIR check
  (`turn/src/executor/atomic.rs:738-830` — v3-layout path, not wide members); the SDK
  narrow cap-open residual (PI 0 / PI 8, `sdk/src/full_turn_proof.rs:5098-5159`); the
  discord bot mirrors the SDK classification; `node/src/turn_proving.rs:741-754` falls back
  to `pi[NEW_COMMIT]` on the narrow path. The rotated sovereign verify reconstructs the
  whole PI vector (H4 slots included) for Fiat–Shamir only.
- **VESTIGIAL:** `RotatedParticipantLeg::cell_commit()`
  (`circuit-prove/src/joint_turn_aggregation.rs:1215-1217`) — confirmed **zero live
  callers** (its one delegation wrapper has zero callers repo-wide). Confirms review §5.11.
- **Stale-constant hazard found:** `app-framework/src/stark_rehydrate.rs:83-85` hardcodes
  PI 34/35 for the rotated commits — the live slots are 42/43 (`V1_PI_COUNT = 42`); demo
  surface only, but it must not survive the PI-map regen.
- **Durable surfaces that would strand under a v9→v10 flip:** the redb
  `LedgerCheckpoint.sovereign_commitments` (`persist/src/ledger_store.rs:39-48`) written by
  the node durability spine and starbridge-v2 World images — any existing image on hbox or
  a laptop strands its sovereign cells at the flip. `commit_log` ledger roots are
  whole-cell-derived (recomputable, not stranded). Game stores (Descent sqlite, move-log
  files, bot sqlite) deliberately store moves/seeds, not commitments — re-derived on boot.
- **On-chain:** ONE deployment exists — Base-Sepolia `DreggSettlement`
  (`chain/DEPLOYMENTS.md`, `0x6c87…Bd87`) holding packed 8-lane roots of the wide-v9-anchor
  family from a **fixture turn** (dev single-party ceremony, height 2). The gnark wrap
  itself is transcript-aware but **not commitment-aware** (no PI-8/NEW_COMMIT indexing
  anywhere in `chain/` — confirms review §5.6's scoping). solana-settlement: code, no
  deployed program id; cosmos: local-demo only (`docs/reference/CHAIN-INVENTORY-GROUNDED.md:37-50`).
- **sdk-py / sdk-ts: zero consumers** (sdk-ts always encodes
  `execution_proof_new_commitment: None`).

**Verdict.** From the repo alone: **no live external v9 holder is evidenced, and the flip is
not blocked — but the confirmation has an irreducible repo-external residue.** The named
checks before the Epoch-2 flip: (1) sweep hbox + dev laptops for `dregg_persist` redb stores
/ starbridge World images with `sovereign_commitments` (the one artifact class that strands);
(2) treat the Base-Sepolia fixture contract as redeploy-or-declare-dead (it re-pins with the
gnark/VK regen Epoch 2 already scopes); (3) the devnet game ledger is non-durable by the
standing record (hand-run `:8420`, ledger lost on reboot), which is corroborating, not
proof. UNKNOWN beyond that: third parties running the standalone verifier binary cannot be
enumerated from the repo (it reads the narrow registry only, and rejects wide legs, so its
exposure to the flip is the narrow family, not v9-wide).

**Gates.** The Epoch-2 value flip (review §5.3): GREEN modulo the two named external checks.

---

## D5 — PI slots 9–41: live vs vestigial, and STATE_RECORD_DIGEST decodability

**What was run.** A per-slot census over `pi.rs`, the producer fills (`trace.rs`,
`trace_rotated.rs`), every in-AIR `pi_binding` across all 57 wide members (parsed from the
TSV), and every verify-path reader (executor, SDK, aggregation, conditional, verifier,
lightclient).

**The in-AIR pin map over the wide registry:** only PIs 0, 8, 20/21, 22/23, 41 are pinned by
any standard member (47/57, 35/57†, 47/57, 34/57, 47/57 respectively); **PIs 9–19 and 24–40
are pinned by ZERO standard members** — they are Fiat–Shamir-bound free inputs. Sole
exception: `heapWriteVmDescriptor2R24` repurposes indices 2–19 for its own wide-anchor shape
(no H4 semantics — the regen must special-case it, not "migrate" it).
† the census counts 35/57 for the PI-8 pin where the review's errata says 34/57 — one-member
counting discrepancy, flagged, immaterial to any decision (both counts include `custom`).

**Per-slot verdicts (9–41):**

- **9–15 (H4 tail), 16–19 (effects hash):** VESTIGIAL on wide members — no AIR pin, no
  verify-path reader; the executor recomputes them only to reconstruct the FS transcript,
  and since that reconstruction shares the producer's code path, dropping the fill changes
  both sides in lockstep. Nothing consumes them that the wide tail (52–67) could not serve.
- **20/21 (init balance), 22/23 (final balance), 41 (actor nonce):** LIVE — in-AIR pins plus
  executor-side anchoring to trusted ledger state. Must be preserved or re-homed by the
  PI-map regen.
- **33 (turn hash / shared turn id):** LIVE ×3 — aggregation equality across legs, the
  bundle digest, and the conditional `TurnProven` gate (which checks all four of 33–36).
  **Liveness gap found:** rotated producers fill TURN_HASH[1..3] with zeros while
  `turn/src/conditional.rs:735-747` checks all four felts — the conditional path currently
  has no non-test producer filling all four. A regen must decide this slot's contract, not
  inherit it.
- **24/25 (net delta):** prover-side conservation self-check + node/wasm record surface;
  no verifier gate. Keep as record-or-retire decision, not a soundness constraint.
- **26–32, 37–40:** vestigial (constants/sentinels/retired-verb slots; the 29–32 handoff
  block is a dead-slot compaction candidate alongside 42/43). 28 is live only in the v3
  custom-leaf layout, which wide-member H4 retirement does not touch.

**STATE_RECORD_DIGEST: DECODABLE AS-IS — no schedule limb needs adding.** The digest is
`compute_authority_digest_8(cell)[0]`, and the rotated limb schedule carries the full 8-felt
authority digest verbatim at limbs {24, 12–18} (`cell/src/commitment.rs:897-923, 1062-1117`;
`B_RECORD_DIGEST = 24`), byte-identical by stated invariant. The rotated block binds strictly
MORE than the ~31-bit column the H4 commit absorbs; the post-state movers are covered by the
`withRecordPin8Headroom2` members' 8-limb pins. Review §5.5's "one schedule limb is added"
contingency is NOT needed.

**Verdict.** H4 retirement is not blocked by any PI in 9–41. The regen's live-slot carry set
is {20, 21, 22, 23, 41, 33(–36 contract decision), 24/25 record-only}, plus the three named
cleanups: drop the PI-8 col-88 pin with the regen, delete the caller-less `cell_commit()`,
fix the stale 34/35 constants in `stark_rehydrate.rs`.

**Gates.** H4 retirement + the PI-map regen (review §5.5): GREEN with the named carry set.

---

## D6 — the per-member chip-cliff table

**What was run.** A static census over all 57 members of the wide staged registry: chip
sites by arity tag, the transitively-dead (S2) site set per member (the constraint-level
classifier: sites none of whose outputs reach a non-chip constraint, PI, or live site —
the same negative check the review reproduced), the wide-chain fresh-felt totals, and the
projected query counts after S2 deletion and after rate-8, against the 64/128/256 cliffs.
Static counts are NO-DEDUP upper bounds; D1's measurement calibrates them — post-S2 dedup
on the transfer is exactly ZERO (134 sites → 134 unique over all rows) and the rate-8
simulation showed no cross-chain dedup, so the static counts are treated as exact for this
classification; the one unmeasured dedup axis is the witness node8 rows on map-op members.
The census was implemented twice independently (this Rust instrument and a standalone
Python parser over the TSV); they agree on all 57 members across all 18 numeric columns.

Projection definitions:

- `postS2` = surviving (live) chip sites — the Epoch-1 chip query count.
- `rate8_A` = S2 gone + both block chains re-scheduled at rate 8 (heads kept as seed sites),
  caveat chain and H4 untouched.
- `rate8_B` = A + head limbs folded into the stream + the caveat chain at rate 8.
- `rate8_C` = B + H4 retired (the Stage-3 bundle endpoint).

**Raw table.** Full 57-row TSV in the test output (`D6:` lines). The shape is highly regular
— every member carries the same wide skeleton (118 tag-11 sites + 2 heads, 350 fresh felts
incl. the two iroots; +8 more with the head limbs folded), and the members differ only in
their caveat/H4/map-op decoration:

| class (members) | sites | S2 dead | live (postS2) | rate8_C | height after full bundle |
|---|---|---|---|---|---|
| transfer/burn/mint/… core verbs (33) | 254 | 120 | 134 (→256) | **49** | **64** |
| makeSovereign (1) | 258 | 120 | 138 (→256) | 51 | **64** |
| noteSpend / noteCreate / createCell (3) | 271 | 120 | 151 (→256) | **65** | **128** (over by 1) |
| the capOpen/WriteCapOpen family (16) | 271 | 120/124 | 147–151 (→256) | **66** | **128** (over by 2) |
| refusal, heapWrite (2) | 288/286 | 120/121 | 168/165 (→256) | 82 | 128 (over by 18) |
| attenuateCapOpenEff, refreshDelegationWriteCapOpen (2) | 288 | 124 | 164 (→256) | 83 | 128 (over by 19) |

`rate8_C` height histogram over the registry: `{64: 34 members, 128: 23}`; the same split
holds at `rate8_A` and `rate8_B` (the caveat-lift and H4-retirement steps move counts but
never move a member across a cliff by themselves).

**Findings.**

- **Post-S2 (Epoch 1): every one of the 57 members stays at chip height 256.** Live site
  counts run 130–168, all above 128. The review's "134 > 128, chip stays 256" is confirmed
  REGISTRY-WIDE, not just on the transfer.
- **Post-rate-8 (the full Epoch-2 bundle): 34 members land at 64, 23 at 128 — and the
  128-class is dominated by members over the cliff by ONE or TWO permutations.** The
  noteSpend/createCell family sits at 65, the entire capOpen family at 66. One more
  consolidation (e.g. merging the two spare hash2/caveat joins, or one fewer terminator)
  flips 19 of the 23 down to 64. Only refusal/heapWrite/attenuateCapOpenEff/
  refreshDelegationWriteCapOpen (82–83) genuinely need 128.
- The tag-16 (node8) sites are IN-DESCRIPTOR: 23 members carry 16 or 32 of them, 432
  total — reproducing the review's registry census `{16: 432}` exactly. They survive every
  projection above as ordinary live sites. Members with `map_op` constraints additionally
  get witness-time node8 rows from the map-heap openings (`build_traces`' fold at
  `descriptor_ir2.rs:5148-5199`, two 17-permutation paths per op at
  `HEAP_TREE_DEPTH = 16`) — 0..34 extra unique rows per op depending on how far the
  witness paths coincide with the in-descriptor sites and each other. The map-op members'
  post-bundle brackets are therefore 65..134: the three at 65 and the spawn-capOpen pair
  at 66 can stay under 128 only if the witness rows dedup almost entirely — a
  witness-level measurement (the D1 instrument pointed at a noteSpend leg) decides it.
- **The review's unresolved "256-vs-512 static tension" localizes to exactly these
  members AT HEAD:** noteSpend/noteCreate/createCell and the capOpen family issue 271
  static chip queries, refusal 288, heapWrite 286 — all ABOVE 256 — so at HEAD they
  commit a 512-row chip table unless ≥15–32 tuples dedup (plus whatever the witness
  node8 rows add back). The transfer's measured 256 does NOT generalize to them. Every
  chip-cost figure in the review that scales from the transfer member understates these
  23 members' chip term by up to 2× at HEAD.
- **A dead stratum the review did not count: on 21 members the v1 H4 sites are emitted but
  transitively DEAD** (S2-dead = 124 there, not 120 — attenuate, revokeCapability,
  grantCap, the 8 setField members, and 10 of the capOpen family carry four H4
  permutations that feed nothing; they have no PI-8 pin). Two members (custom,
  setFieldDyn) do not emit H4 at all; 33 carry it live. (The PI-8-pin member count is
  33/34/35 depending on the counter — heapWrite repurposes pi_index 8 for its own shape —
  which reconciles the review-vs-D5 count discrepancy.)

**Verdict.** The Epoch-1 chip stays 256 on all 57 members (no dedup surprise pending D1's
measured check). The Epoch-2 bundle reaches chip-64 on 34/57 members as-specced; the
capOpen/note family misses 64 by 1–2 permutations (a cheap consolidation target the review
should add to the Stage-3 scope decision), and the four heavy members plus witness-rich
map-op members ride at 128. **No member needs 256 after the bundle on static counts** —
but noteSpend-class members can only be pinned under 128 by a witness-dedup measurement,
not statically.

**Gates.** Honest per-member Epoch-2 claims; the registry-wide totals every design quotes;
which members ride which side of the 128 cliff (review §Stage-0 D6, the noteSpend/capOpen
question).

---

## D7 — the preprocessed-column spike

**What was run.** Against the PINNED plonky3 (`82cfad7`, the locked rev) and the PRODUCTION
IR-v2 FRI knobs (lb=6, 19 queries, PoW 16): one row-constant column carried as a
`BaseAir::preprocessed_trace()` matrix through `ProverData::from_instances` →
`prove_batch` → `verify_batch`; a tamper-rejection check (proof against commitment A
verified under commitment B); and the adoption probe design B actually needs — a LogUp
interaction whose FIELD reads the preprocessed column (send+receive of the same
preprocessed-valued tuple, balancing to zero but forcing the field-evaluation path through
the preprocessed matrix).

**Raw numbers.**

```text
D7: GREEN at the pin — preprocessed column proves+verifies under the PRODUCTION IR-v2 FRI
    config; commitment lives in CommonData (VK-side, committed once); tamper REJECTED;
    LogUp-field-over-preprocessed GREEN.
D7: proof bytes: with prep 39587 vs plain 30544 (delta +9043 B/column at h=64)
```

**Support surface at the pin (read + exercised):**

- `p3-batch-stark` carries preprocessed end-to-end: per-instance
  `preprocessed_trace()/preprocessed_width()`, ONE global PCS commitment across instances
  stored in `CommonData` (the VK side — committed once per descriptor set, NOT per proof:
  `common.rs:183-270`, `pcs.commit_preprocessing`), transcript observation
  (`prover.rs:222 observe_preprocessed`), opening at zeta (+ next-row only when
  `preprocessed_next_row_columns()` is non-empty), and verifier-side enforcement.
- The lookup path evaluates interaction fields over main AND preprocessed
  (`logup.rs generate_permutation(main, preprocessed, …)`) — the "preprocessed-masked
  multiset equality" design B wants is expressible at the pin, and the probe EXERCISED it:
  a send+receive pair whose field is the preprocessed value proved and verified.
- **The recursion fork at ITS pin (`plonky3-recursion` `0a4a554`) also supports
  preprocessed** — `recursion/src/generation.rs:187-234, 377-396` sizes widths, observes the
  commitment into the transcript, and wires `preprocessed_local/_next` openings. The
  dregg leaf wrap does not currently exercise it, but adoption does not require forking the
  recursion surface.
- The dregg hook (`Ir2RowLocalBuilder.empty_prep`, `descriptor_ir2.rs:1503-1528`) is empty
  as the review says; the substrate under it is not.

**Verdict.** GREEN — the spike is not red and not equivocal. The pinned batch STARK carries
row-constant columns as committed-once, VK-side, tamper-binding preprocessed matrices under
the production FRI knobs, with LogUp fields free to read them, and the pinned recursion
fork already knows the shape. The measured adoption cost is **+9,043 B per proof** for the
extra PCS round at one column / h=64 — a fixed round cost (marginal per additional column
is per-opened-column scale, ~30 B), which counts against but does not dent the ~95–100 KB
per-proof wire delta the floor shape buys. What p3 does NOT provide is the verified
surface: the preprocessed grammar (Lean semantics + the VK-commitment story +
`chipTableFaithful` closure) is exactly the work the review already priced as design B's
novelty.

**Gates.** The B-vs-F mechanism choice (review §Stage-3): the preprocessed mechanism is
VIABLE at the pin, so the choice reverts to the review's stated default logic — it is now a
risk/verification-surface choice (B's Lean-verified preprocessed grammar vs F's
anchor-echo with no new PCS round), not a p3-capability constraint. D7 being green removes
the "if D7 is red → F" forcing; the +9 KB fixed round cost is the one new number the
Stage-3 decision should weigh against F's anchor-echo (~1K cells, no new round).

---

## Honest limits

- D1's dedup and D6's projections are measured on the honest transfer witness and static
  descriptors respectively; per-member DEDUP (not just query counts) for the other 56
  members would need 56 more witness minters — the D1 transfer measurement is the
  calibration point, and it measured essentially zero dedup (252/254 deployed, 134/134
  post-S2, 46/46 in the rate-8 simulation), which is why the static counts are treated
  as exact everywhere except the witness node8 axis.
- D6's map-op members contribute additional witness-dependent node8 rows (two Merkle paths
  per op at the fixed heap depth); the census flags `map_ops` per member rather than
  guessing the witness. Their `rate8_*` columns are lower bounds on those members.
- D4/D5 are repo censuses; anything running outside the repo (hbox disk state, third-party
  verifier processes) is named UNKNOWN, not asserted.
- The rate-8 simulation fixes one concrete schedule (state8 ‖ 8 fresh felts per step,
  arity-16 compression, domain-seeded) — the review's Lean-side tag retype decides the
  final encoding; the COUNT is robust to the encoding, the tuples are not.
- D2's corrected cell accounting does not re-derive the three designs' full cost tables;
  it corrects the shared aux term and flags every downstream figure that inherits it.

## Named follow-ups (each is a bounded lane, in priority order)

1. **noteSpend-class witness dedup** — point the D1 instrument at a real noteSpend/
   createCell leg: settles both the at-HEAD 256-vs-512 bracket for the 23 heavy members
   and their post-bundle 128-vs-under-128 bracket (the map-heap node8 dedup axis).
2. **The over-by-1-2 consolidation** — the Stage-3 scope decision should explicitly weigh
   one extra site-merge (caveat join / terminator shape) on the capOpen family: it flips
   19 members from 128 to 64 for what looks like one emit-level change.
3. **hbox persistence sweep before the Epoch-2 flip** — `dregg_persist` redb stores and
   starbridge World images with `sovereign_commitments` are the one strandable artifact
   class (D4); plus the Base-Sepolia fixture contract redeploy-or-retire decision.
4. **Re-derive the three designs' committed-cell tables under the corrected aux
   accounting (D2)** before any of those figures is quoted again; wire figures stand.
5. **The AFTER-side row-0 fill artifact (D1)** — hand to the S2-deletion lane: the
   "stop filling the dead regions" step and any future instrument must not assume tuple
   row-constancy; the AFTER strata legitimately take two values per column today.

---

## Appendix — D6 full per-member table

Columns: sites · S2-dead · live(postS2) · postS2 height · wide sites · heads · freshA ·
freshB · caveat sites · caveat fresh · H4 sites · map_ops · rate8_A · h_A · rate8_B · h_B ·
rate8_C · h_C. (Output of `d6_per_member_chip_cliff_census`; reproduce with the run command
at the top.)

```text
    transferVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    burnVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    mintVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    noteSpendVmDescriptor2R24	271	120	151	256	118	2	350	358	11	31	4	2	77	128	69	128	65	128
    noteCreateVmDescriptor2R24	271	120	151	256	118	2	350	358	11	31	4	1	77	128	69	128	65	128
    cellSealVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    cellDestroyVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    refusalVmDescriptor2R24	288	120	168	256	118	2	350	358	12	33	4	1	94	128	86	128	82	128
    setPermsVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    setVKVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    exerciseVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    pipelinedSendVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    refreshVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    incrementNonceVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    revokeVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	2	60	64	53	64	49	64
    introduceVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    attenuateVmDescriptor2R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    revokeCapabilityVmDescriptor2R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    customVmDescriptor2R24	250	120	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    setFieldDynVmDescriptor2R24	250	120	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    grantCapVmDescriptor2R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    makeSovereignVmDescriptor2R24	258	120	138	256	118	2	350	358	14	45	4	0	64	64	55	64	51	64
    createCellVmDescriptor2R24	271	120	151	256	118	2	350	358	11	31	4	2	77	128	69	128	65	128
    factoryVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	2	60	64	53	64	49	64
    spawnVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	2	60	64	53	64	49	64
    receiptArchiveVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    cellUnsealVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    emitEventVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    setFieldVmDescriptor2-0R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    setFieldVmDescriptor2-1R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    setFieldVmDescriptor2-2R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    setFieldVmDescriptor2-3R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    setFieldVmDescriptor2-4R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    setFieldVmDescriptor2-5R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    setFieldVmDescriptor2-6R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    setFieldVmDescriptor2-7R24	254	124	130	256	118	2	350	358	10	29	0	0	56	64	49	64	49	64
    delegateCapOpenVmDescriptor2R24	271	124	147	256	118	2	350	358	10	29	0	0	73	128	66	128	66	128
    introduceCapOpenVmDescriptor2R24	271	120	151	256	118	2	350	358	10	29	4	0	77	128	70	128	66	128
    grantCapCapOpenVmDescriptor2R24	271	124	147	256	118	2	350	358	10	29	0	0	73	128	66	128	66	128
    revokeCapOpenVmDescriptor2R24	271	120	151	256	118	2	350	358	10	29	4	0	77	128	70	128	66	128
    refreshDelegationCapOpenVmDescriptor2R24	271	120	151	256	118	2	350	358	10	29	4	0	77	128	70	128	66	128
    revokeCapabilityCapOpenVmDescriptor2R24	271	124	147	256	118	2	350	358	10	29	0	0	73	128	66	128	66	128
    transferCapOpenEffVmDescriptor2R24	271	120	151	256	118	2	350	358	10	29	4	0	77	128	70	128	66	128
    attenuateCapOpenEffVmDescriptor2R24	288	124	164	256	118	2	350	358	10	29	0	0	90	128	83	128	83	128
    transferFeeVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
    transferCapOpenTBVmDescriptor2R24	271	120	151	256	118	2	350	358	10	29	4	0	77	128	70	128	66	128
    heapWriteVmDescriptor2R24	286	121	165	256	118	2	350	358	13	35	0	1	91	128	82	128	82	128
    delegateWriteCapOpenVmDescriptor2R24	271	124	147	256	118	2	350	358	10	29	0	0	73	128	66	128	66	128
    introduceWriteCapOpenVmDescriptor2R24	271	124	147	256	118	2	350	358	10	29	0	0	73	128	66	128	66	128
    delegateAttenWriteCapOpenVmDescriptor2R24	271	124	147	256	118	2	350	358	10	29	0	0	73	128	66	128	66	128
    revokeDelegationWriteCapOpenVmDescriptor2R24	271	124	147	256	118	2	350	358	10	29	0	0	73	128	66	128	66	128
    revokeCapabilityWriteCapOpenVmDescriptor2R24	271	124	147	256	118	2	350	358	10	29	0	0	73	128	66	128	66	128
    refreshDelegationWriteCapOpenVmDescriptor2R24	288	124	164	256	118	2	350	358	10	29	0	0	90	128	83	128	83	128
    spawnWriteCapOpenVmDescriptor2R24	271	120	151	256	118	2	350	358	10	29	4	2	77	128	70	128	66	128
    spawnCapOpenVmDescriptor2R24	271	120	151	256	118	2	350	358	10	29	4	2	77	128	70	128	66	128
    exerciseCapOpenVmDescriptor2R24	271	120	151	256	118	2	350	358	10	29	4	0	77	128	70	128	66	128
    supplyMintVmDescriptor2R24	254	120	134	256	118	2	350	358	10	29	4	0	60	64	53	64	49	64
```

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>
