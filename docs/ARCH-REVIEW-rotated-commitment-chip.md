# Architecture Review — Rotated Commitment Chain and the Poseidon2 Chip

Date: 2026-07-18. Baseline member: `transferVmDescriptor2R24` in
`circuit/descriptors/rotation-wide-registry-staged.tsv` (trace_width 2664, 68 PIs, 481
constraints, 254 chip lookups), registry of 57 members.

Inputs: four constraint-level censuses (commitment palimpsest, chip architecture,
single-row layout, weld tower), three candidate designs (rotV4 minimal consolidation,
R8-SPONGE clean slate, cost-model-first floor), and three independent adversarial
verification passes (graft claim, chip degree arithmetic, cost-delta recomputation).
Every number below carries its evidence class; every claim a verifier refuted is shown
as REFUTED with the corrected value, not silently adopted.

Evidence classes:

- **[M]** measured on a real verified proof (`docs/MEASURE-legacy-1felt-chain-drop.md:108-138`).
- **[P]** parsed/read directly from the TSV descriptor or source at HEAD (reproduced
  independently by at least two of the census/verify lanes).
- **[A]** analytical, from the byte/cell model calibrated against BOTH measured proofs
  (reproduces them to 0.03–3.5%; the only byte model of the three that does).
- **[X]** extrapolated (elasticity-1 scaling); unverified below ~200 ms prover / at
  untested scales.
- **[U]** unknown or unverifiable from the repository.

Status vocabulary: **BUILT** (deployed at HEAD), **DEAD** (present at HEAD, consumed by
nothing), **PROPOSED** (design only), **REFUTED** (claim contradicted by a verification
pass), **UNVERIFIED** (claim neither reproduced nor refuted).

---

## 1. The architecture as it is

### 1.1 The commitment palimpsest

Four strata of commitment machinery coexist in every wide member. One is dead.

| stratum | machinery | published at | status |
|---|---|---|---|
| S1 — v1 H4 CellState commit | 4 chip sites: `[76..79]→98`, `[80..83]→99`, `[84..87]→100`, `[98,99,100,186]→88` (`metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:210-221`) | col 88 → PI 8 (`pi::NEW_COMMIT`, `circuit/src/effect_vm/pi.rs:29-40`), bound on **34/57 members** [P] | **BUILT, load-bearing** |
| S2 — rotated 1-felt chains (v3) | 120 sites/member (2×59 arity-4 + 2 arity-2 finals), carriers 378..436 / 617..675, digests 377/616 (`EffectVmEmitRotationV3.lean:306-366`) | nothing — PIs 42/43 retired by `wideAppend` (`EffectVmEmitRotationWide.lean:883-924`), producer zeroes the slots for Fiat–Shamir alignment (`circuit/src/effect_vm/trace_rotated.rs:4103-4116`) | **DEAD** |
| S3 — caveat 1-felt chain | 10 sites, manifest cols 676..704, carriers 705..713 | col 714 → PI 45 (1 felt, ~31-bit) | **BUILT, alive** |
| S4 — wide 8-felt chains | 2×60 carriers (cols 1657..2136 / 2137..2616), 116 arity-11 steps + 2 tag-11/9-var terminators (`trace_rotated.rs:3909-3925`) | PIs 52..59 (first row) / 60..67 (last row) — the real ~124-bit anchor | **BUILT, alive** |

The S2 verdict is a constraint-level negative check, reproduced adversarially: over all
481 constraints of the transfer member (including transition hi/lo) and over all 57
members, zero constraints outside the 1-felt lookups themselves read the legacy
carriers, digests, or their 840 exposed lane columns [P, CONFIRMED]. S2 persists only
because `wideAppend` is conjunctive — the emitter never stopped emitting the stratum
below it (`EffectVmEmitRotationV3.lean:554-555`).

**The graft claim, corrected.** The prior reading (`docs/MEASURE-legacy-1felt-chain-drop.md:43-47`,
repeated by the weld-tower census) — that the 8-felt chain is *seeded from the 1-felt
chain's terminal permutation state* — is **REFUTED** at the constraint level, registry-wide.
The wide openers' `inputs[0..8]` are the output lanes of two fresh arity-4 sites
(#134/#194) whose inputs are the raw limb columns 198..201 / 437..440 (`cells_root,
balance_lo, nonce, balance_hi`, `cell/src/commitment.rs:1074-1081`). No output column of
any legacy-chain site appears in any arity-11 input tuple on any of the 57 members [P,
CONFIRMED by independent re-parse]. The seed numerically equals the legacy chain's
*head* (first) state, computed in independent columns — never its terminal state. The
misreading originated in the measurement classifier `is_legacy_1felt_site :=
chip_input_arity == 4` (`circuit/tests/legacy_chain_drop_measurement.rs:155-157`), which
sweeps the two wide heads into "legacy"; the drop variant deleted them too, and *that* —
not removal of the legacy chain — is what un-rooted the commit in the experiment.

Consequences, all verified:

- **The wide chain is already self-rooted.** Deleting S2 changes no published value
  (every published value traced: PI 8 ← col 88, PI 44 ← col 468, PI 45 ← col 714,
  PIs 46..49 ← 715..718, PIs 52..67 ← wide carriers) [P, CONFIRMED].
- **"49 orphan limbs" is REFUTED.** The true 1-felt-only column set is **42**: 13
  host-v1 (v1 after-state + `STATE_RECORD_DIGEST`) + 29 caveat manifest. The 49 is
  arithmetically reproduced as the classifier artifact (13 + 28 + 8 shared head limbs)
  [P, CONFIRMED].
- The MEASURE doc's "re-root on a domain constant + absorb 49 orphans + flag day" plan
  (`MEASURE-legacy-1felt-chain-drop.md:71-81`) is scoped against the misreading.

PI 8 is *not* a rotated-block digest: it is the v1 H4 commit, and it is load-bearing —
producer fills PIs 8..15 from `CellState::compute_commitment_8`
(`circuit/src/effect_vm/trace.rs:1158-1168`), the executor's custom-leaf path checks all
8 felts off-AIR (`turn/src/executor/atomic.rs:784-830`), and the SDK's cap-open residual
legs still bind PI 0 / PI 8 — "the residual ~31-bit waist for cap-gated turns"
(`sdk/src/full_turn_proof.rs:5106-5150, 11051`) [P, CONFIRMED]. Verification errata on
the census itself: the binding exists on 34/57 members, not 31/57 (`custom` carries it),
and one vestigial PI-8 reader exists with no live caller found —
`RotatedParticipantLeg::cell_commit()` (`circuit-prove/src/joint_turn_aggregation.rs:1215-1217`).

### 1.2 The chip table

One Poseidon2 table, 386 committed columns: `[arity | in0..15 | out0..7 | mult |
is_fact | big | S4,S5,S6 | wide | node8 | 352 perm aux | mult_narrow]`
(`circuit/src/descriptor_ir2.rs:2044-2081`; aux width `plonky3_prover.rs:313`). The
layout comments are a fossil record carrying indices from two retired strata (`:2046`
says `// 9` for a column at 17, etc.) — stratigraphy legible in the source.

**Arity encoding.** Admissible set {0, 2, 3, 4, 7, 11, 16} via a 7-factor membership
product; flags `is_fact`/`big`/`wide`/`node8` each need booleanity + flag⇒arity +
a 6-factor complement product. Max constraint degree **7**, frozen twice
(`Ir2Air::max_constraint_degree → Some(7)`, `:2147-2160`; `ir2_degree_budget` `"chip" => 7`,
`:5969`), and attained simultaneously by four families: the membership product, the
three complement products, the in0/in1 lane pins, and every x⁷ S-box round [P,
CONFIRMED by independent re-derivation, including the constant 29568 = 2·3·4·7·11·16].
Adding **one** new arity value pushes all four families to degree 8 [CONFIRMED,
structural]. The wall is policy, not physics: the FRI floor `log_blowup ≥
log2_ceil(d−1)` (`:5895-5896`) at deployed lb=6 (`:5452-5456`) admits degree 65, and the
batch already carries a degree-8 main gate (setFieldDyn, `:5418-5420`). Quotient-chunk
schedule (verified against pinned plonky3, `batch-stark/src/symbolic.rs:94`): d=5 → 4
chunks (the census's "d∈{5..9} all cost 8" is **REFUTED at d=5**, non-load-bearing),
d∈{6..9} → 8, d=10 → 16. Net: one or two more arity values are ~free at the prover; the
compounding-per-arity is the structural defect.

**The real blocker for arity-16-as-absorber is tag collision, not degree** [CONFIRMED].
node8 is domain-separated "by the arity tag itself" (`:316-322`) and Lean ties tag =
input length (`chipRow` head is `ins.length`, `metatheory/Dregg2/Circuit/DescriptorIR2.lean:1138-1139`;
`chip_lookup_sound` rests on it, `:1164-1191`). A 16-input absorb row and a node8 tree
node would be one indistinguishable row family — a cross-domain forgery. The fix is a
Lean retype decoupling tag from length (injective code→length map; `padTo_inj` survives
verbatim).

**Vestiges** [P]: the fact bus has a provide side and **zero senders** (`:2815-2824`;
`fact_hist` never inserted into) — 2 of the chip's 3 LogUp interactions are inert (8 of
12 ext cols dead). Arity 3 has zero main-table uses; its doc-comment describes a retired
consumer. The narrow bus (BUS_P2_1, 18-wide, `:2796-2813`; `NarrowChip.lean:121-140`) is
fully built — AIR, parser, histogram, Lean defs, six proof layers — and routed by **zero
descriptors**.

**Meta-scar.** The chip AIR is hand-written Rust (`descriptor_ir2.rs:2582-2825`);
`chipTableFaithful : ChipTableSoundN …` enters the metatheory as a structure **field**,
i.e. a hypothesis (`metatheory/Dregg2/Circuit/Satisfied2Faithful.lean:118`). Nothing in
Lean discharges it against the Rust constraint family. This is the one standing
violation of the Lean-authored-AIR law, and any re-architecture is the window to close it.

Registry arity usage [P]: `{4: 7573, 11: 6726, 16: 432, 2: 180, 7: 20}` across 57
members; node8 (432 uses, 23 members) is live, not vestigial.

### 1.3 Single-row width decomposition and the measured cost shape

The 2664 columns of the transfer member, verified band by band (sums exactly) [P]:

| band | cols | width |
|---|---|---|
| v1 executor face (54 sel + 14 before + 8 param + 14 after + 98 aux) | 0..188 | 188 |
| availability-weld pad | 188..198 | 10 |
| BEFORE rotated block (178 limbs + iroot + 1-felt commit + 59 carriers) | 198..437 | 239 |
| AFTER rotated block | 437..676 | 239 |
| caveat region (29 manifest + 9 carriers + commit + 4 DFA rc) | 676..719 | 43 |
| graduated chip lanes, 7 × 134 sites | 719..1657 | 938 |
| BEFORE wide carriers (60 × 8) | 1657..2137 | 480 |
| AFTER wide carriers | 2137..2617 | 480 |
| membership-teeth claims | 2617..2619 | 2 |
| gentian refuse aux | 2619..2664 | 45 |

Semantic content: 638 cols (24%). Hash plumbing: **2026 cols (76%)**. Witnessed-dead
columns (read by no constraint or PI): **940 = 35.3%** of the width, 917 of them the
legacy chain's exposed lanes [P].

Measured proof at HEAD [M]: committed cells 578,720 base-eq (main 7302×64 = 467,328;
chip 434×256 = 111,104; range 288); proof 556,810 B (opened_values 122,820 +
opening_proof 425,674 + lookup data 8,193 + commitments 119 — components sum to
556,806, a 4 B bookkeeping discrepancy in both measured proofs); prover 637.9 ms; FRI
lb=6, 19 queries, PoW 16 (`descriptor_ir2.rs:5452-5456`; "38" seen elsewhere = 19
queries × 2 out-of-domain points).

Cell budget decomposition [M+P] — the dominating term is not the dead chains and not
the chip:

| term | cells | share |
|---|---|---|
| main LogUp aux (254 row-constant chip interactions × ~17.5 base-eq × 64 rows) | 292,864 | **50.6%** |
| main base width | 174,464 | 30.1% |
| chip | 111,104 | 19.2% |

Wire model, calibrated on both measured proofs [A]: opened_values ≈ 28.5 B **per
column** (zero height term); opening_proof ≈ 19 queries × (2.48 B/base-eq) width term
plus a **stable structural residual of ~60–62 KB** (Merkle paths, FRI fold, PoW). The
single-row census's decomposition "width term ~25× height term" is **REFUTED** — the
structural share is 14–22% of opening_proof, and this error propagated into two of the
three designs' byte headlines (§3). Height is nearly free (+608 B per instance per
doubling); width costs ~188 B/col composite [M, from the drop experiment: −1071 cols →
−201,600 B]. Elasticity of bytes and prover wall-clock to committed width/cells ≈ 1.0 [M].

The shape verdict: every per-turn absorption felt occupies a *column* (~188 B wire)
where a cell of a tall narrow instance costs ~1–3 B, and every in-row hash step is a
separate *row-constant* LogUp interaction billed on all 64 rows. Width≫height is
backwards for a 19-query FRI batch, twice over. Three width figures coexist — declared
main-table arity 2617, trace_width 2664, committed main width 2726 (range-decomposition
appendage, `descriptor_ir2.rs:1254-1283`) — and how Rust treats the 2617≠2664
discrepancy is untraced [U].

### 1.4 The weld tower

The deployed member is an 11-layer composition, each layer historically constrained to
be byte-preserving over the last (`trace_rotated.rs:31-32`):

| layer | content | source |
|---|---|---|
| L0 | v1 face, width 188 | `EffectVmEmitTransfer.lean:217` |
| L1 | availability borrow/carry weld (+13 gates, +6 teeth) | `:903-908` |
| L2 | rotation: 2×239-col blocks + caveat region + welds + 1-felt chains | `EffectVmEmitRotationV3.lean:547-557` |
| L3 | frozen-authority: 83 colEq freezes | `:3115-3123` |
| L4 | graduation to IR2: sites → chip lookups + 938 lane cols | `EffectVmEmitV2.lean:1652-1666` |
| L5 | DFA rc pins | `AvailWireMembers.lean:110-115` |
| L6 | membership-teeth pins | `CarrierComposed.lean:474` |
| L7 | `wideAppend`: +120 arity-11 lookups, +960 cols, retires 2 pins, leaves S2 dead | `EffectVmEmitRotationWide.lean:906-919` |
| L8 | width bump +2 (as a layer) | `AvailWideMembers.lean:203-205` |
| L9 | gentian refuse (+45 aux) | `AvailWireMembers.lean:100-104` |
| L10 | umem weld (registry twin, width 2671) | `EffectVmEmitUMemWeldWide.lean:90` |

Scars in the object: the member *name* is a fossil chain
(`…-v1-avail-rot24-v3-staged-gentian-deployed-bare-refuse…`); L7 is the only non-append
layer and it is conjunctive (keeps the stratum it supersedes); narrow-wire and wide
registries compose the same wrappers in different orders; soundness is one-directional
above the base (no completeness twin exists for L5–L10); `satisfiedVm`
(`EffectVmEmit.lean:520`) is one conjunction serving two disjoint consumer classes
(kernel refinement discards the sites conjunct ~11 times; the commit-binding class
depends on it).

**The velocity exhibit.** The tuple-narrowing campaign — a single representation change
(25-wide → 18-wide bus) with no value change — required **six ordered proof layers**
(`NarrowChip` → `GraduateNarrow` → `GraduateWideNarrow` → `RotatedKernelRefinementAvail`
§1N → `AvailWideMembersNarrow` → `RotatedKernelRefinementAvailWideNarrow`), and after
all six the wire objects were still not twinned and the EFF facet tooth had no narrow
twin (recorded in file 6's header). The campaign's product is routed by zero
descriptors. This is the current price of one representation change, and it is rising.

---

## 2. Costed scars

| # | scar | cost today | evidence |
|---|---|---|---|
| 1 | **S2 dead stratum** (120 sites, 120 carriers, 840 lanes, their aux) | ~182–196K committed cells (~32% of prover time at elasticity 1); ~180 KB wire (960 cols × 188 B/col) | [A] from [M] elasticity; corrected from the refuted 202.6K/-43% figures |
| 2 | **940 witnessed-dead columns** (35.3% of width; 917 = legacy lanes) | subsumed mostly by #1; residual ~100 lane cols after S2 deletion | [P] |
| 3 | **In-row absorption tax** — 254 row-constant interactions | 292,864 cells = 50.6% of the whole proof, the single largest line item | [M+P] |
| 4 | **Absorb-as-width habit** — 76% of width is hash plumbing at ~188 B/col | ~380 KB of the 557 KB wire is width-proportional | [M]/[A] |
| 5 | **Chip arity encoding** — 4 constraint families at frozen degree 7 | zero degree headroom: +1 arity = 4 families → deg 8; 10th value → 16 quotient chunks; no per-shape tuples → the #2 class was inevitable | [P, CONFIRMED] |
| 6 | **~31-bit waists** — PI 8 (cap-open residual, 34/57 members) and PI 45 (caveat commit, 1 felt) | security posture, not bytes; both below the ~124-bit wide anchors | [P] |
| 7 | **Hand-Rust chip AIR** — `chipTableFaithful` assumed, never discharged | the metatheory's chip leg rests on a hypothesis; Lean-authored-AIR law violated | [P] |
| 8 | **Proof-engineering velocity** — 6 layers per representation change (narrow campaign); ~20-lemma `wideAppend_*` transport family; per-member `hclean`/`hemb` decides × 57 × 2 registries | every future change prices at this rate until the tower is flattened | [P, structural] |
| 9 | Dead freight: fact bus (8/12 chip ext cols inert), PIs 42/43 zero slots, stale layout comments, arity-3 doc rot, L8-as-a-layer, arity 2617 ≠ width 2664 | small individually; collectively the accretion signature | [P] |

---

## 3. Candidate architectures, with verified deltas

### 3.0 Where all three designs converge (and where the verifiers corrected them)

**The common first move** — value-preserving deletion of S2 (Lean emitter stops
emitting `rotV3Appendix`'s two block chains; keeps caveat chain, welds, and the two
wide heads; drops zeroed PI slots 42/43). Sound because the wide chain is already
self-rooted [CONFIRMED]. One VK/FP regen across 57×2 registries; **zero commitment
migration, zero light-client format change**.

Corrected expectation for this move (three of the three designs mis-stated it in some
form):

| metric | corrected value | refuted versions |
|---|---|---|
| chip queries / height | **134 → height stays 256** (134 > 128; the measured variant's 128 came from the unsound classifier that also deleted the wide heads; even +H4 retirement only reaches 130) | minimal-consolidation "chip 128"; palimpsest's "~136 = 254−120+2" (double-counts wide heads) |
| committed cells | **~383–397K (−31 to −34%)** [A] | minimal "−43.4%"; cost-model "−35%" (used naive width 1655 vs sound 1766); clean-slate bracket's lower half |
| proof bytes | **~372–380 KB (−32%)** [A] | cost-model "~354 KB" (quoted the naive measurement) |
| prover | **~425–440 ms** [X] | minimal "~361 ms" |

The naive-drop ceiling (−36.2% B / −45.9% prover [M]) is **not** recovered by this move
alone; the missing points live in the chip halving, which genuinely requires the rate
change [CONFIRMED].

**The common second tier** — all three designs share, and the verifiers confirmed:
one-hot chip flags (+2 cols; every non-permutation constraint ≤ deg 2; chip degree
pinned at 7 by the S-box permanently; each future arity = +1 flag) [CONFIRMED as
arithmetic over proposed constraint forms; nothing at HEAD to check against];
tag-decoupled-from-length retype in Lean (closes the absorb-16/node8 collision
structurally) [CONFIRMED]; rate-8 absorption (348 fresh limbs → 44 steps, −62%, exact)
[CONFIRMED]; chip height 64 at ~52–56 queries — **conditional on the unresolved
unique-permutation instrumentation (R1)** [U]; a 2× shape surprise puts all designs at
128 (+~27K cells, ~+5%). And all three converge on **exactly two VK epochs**, with
every value-changing component bundled into the second.

### 3.1 Design A — rotV4 minimal consolidation (single-row kept) — PROPOSED

Drop S2, rate-8 both block chains + caveat chain in-row, one-hot chip, route single-out
sites on the narrow bus, fold L7/L8 into the rotation emit. No new instance; no
Fiat–Shamir shape change beyond PI count; the recursion-leaf instance set is untouched.

Verified deltas (Epoch 2 endpoint): width 2664 → 1052 (band arithmetic exact
[CONFIRMED]); cells **~170–182K (−69 to −71%)** [A, conditional on chip-64];
bytes **~246–254 KB (−54 to −56%)** — the design's own empirical-composite method
(556,810 − 1612×188 = 253,754) is the endorsed estimate; its structural "−64% /
200 KB" is **REFUTED** (per-column opened-values billing + the ~60 KB structural floor
give ~240–246 KB). Prover 190–240 ms [X]. Its Epoch-1 headline row is REFUTED per §3.0.

Effort: author's estimate 13–18 swarms core (its Epoch 1 alone 2–3); the cost-model
lane prices the equivalent lever set at ~4–7 swarms — the discrepancy is scope (depth of
the 57-member proof re-typing, chip Lean-emission in or out) and is itself an open
question (§5.10). VK epochs: 2. Risk profile: lowest structural novelty; leaves ~90–95K
cells and ~95–100 KB wire on the table relative to the floor — its residual is exactly
the absorb-instance move.

### 3.2 Design B — R8-SPONGE clean slate (merged sponge-chip + preprocessed columns) — PROPOSED

Semantic-only main (~302 base cols); the chip becomes simultaneously permutation table
and absorption instance (chain state threads as an in-chip transition; carriers and
lanes never exist); per-object domain-seeded rate-8 chains; frame law (L3's 83 freezes)
as a preprocessed-masked multiset equality; weld/frame/commit buses; chip AIR
Lean-emitted, discharging `chipTableFaithful` for the first time.

Verified deltas (Stage 1): cells **~82K (−86%)** [A, arithmetic CONFIRMED]; bytes
headline "~110 KB (−80%)" is **REFUTED** → **~146–156 KB (−73%)** [A] (same two model
errors: base-eq-ratio opened scaling and a 4% structural allowance vs the measured
~60 KB floor); prover "90–200 ms" as stated (the 91 ms point is [X]). Stage-0 row:
lower half of its "~324–380K" bracket REFUTED (chip stays 256 → ~379–395K).

Effort: Stage 0 = 1–2 swarms; Stage 1 = 8–12; optional Stage 2 (flatten per-effect
corpus) 4–6. VK epochs: 2 mandatory (+ possible third for Stage 2). Risk profile:
highest proof novelty — preprocessed-column grammar is a new verified surface (the
plonky3 hook exists and is empty, `descriptor_ir2.rs:1503-1526` [P]); `spongeChip_sound`
(chained transitions + domain separation) has no in-tree precedent; the preprocessed
commitment enters Fiat–Shamir, so `ir2LeafWrapConfig`-pinned FriLedgerSound statements
and the recursion leaf are restated. Fallbacks are costed in the design (accumulator
columns, or frozen limbs resident in main at −21% of the main win).

### 3.3 Design C — Floor F, cost-model-first (separate tall-narrow absorb instance ⊗ rate-8) — PROPOSED

Derived from the calibrated cost function rather than from the code shape: semantic
main (~339 base × 64), a 19-col absorb instance (one row per absorption step, chip
lookup per row via the next-row window), one-hot/tag-decoupled chip at height 64,
anchor-echo into main (16 cols, ~1K cells) instead of per-instance PIs — no
`verify_batch` plumbing change; Fiat–Shamir changes by one instance.

Verified deltas: cells **82,720 (−85.7%)**, exact [A, reproduced]; bytes **~151 KB
(−73%)** [A, reproduced — this is the model validated against both measured proofs];
prover ~91 ms [X, explicitly unverified below ~200 ms]. Its E1 row was modestly
inflated (naive width/wire; corrected per §3.0); its lever ranking survives the
correction. The design's analytic contribution, verified: **designs A and B land within
2% of each other on cells (~80% of the savings pool each), and each one's residual is
precisely the other's core lever** — A dodges the chip cliff but pays width; B collapses
width but sits on the chip cliff at rate 3. The floor is B's shape ⊗ A's rate, and the
single-row census's own multi-row sketch at rate 3 ("100–140 KB") is REFUTED → ~174 KB.
Below ~140 KB the stable ~60–80 KB structural wire floor dominates and further width
work buys little; at the floor the proof costs what Poseidon2 costs (chip ≈ 32% of
cells).

Effort: E1 ≈ 0.5–1 swarm; E2 ≈ 9–13 via the flattened `emitEffectMember` (vs an
extrapolated 18–24 tower-style — the flatten is the cheaper path, not gold-plating). VK
epochs: exactly 2. Risk: new `Ir2Air` arm + weld bus; gnark wrap regen scope under the
FS change is the one external-facing unknown [U].

### 3.4 Comparison (corrected numbers only)

| point | committed cells | Δcells | proof bytes | Δbytes | prover | VK epochs | effort (swarms) |
|---|---|---|---|---|---|---|---|
| deployed | 578,720 [M] | — | 556,810 B [M] | — | 638 ms [M] | — | — |
| E1 sound drop (all designs) | 383–397K [A] | −31..34% | 372–380 KB [A] | −32% | 425–440 ms [X] | regen only | 0.5–3 |
| A: rotV4 Epoch 2 | 170–182K [A]† | −69..71% | 246–254 KB [A] | −54..56% | 190–240 ms [X] | 2 total | 13–18 (author) / 4–7 (cost model) |
| B: R8-SPONGE Stage 1 | ~82K [A]† | −86% | 146–156 KB [A] | −73% | 90–200 ms [X/U] | 2 (+opt. 3) | 9–14 |
| F: floor (B⊗A) | 82,720 [A]† | −85.7% | ~151 KB [A] | −73% | ~91 ms [X/U] | 2 | 10–14 |
| structural wire floor | — | — | ~60–80 KB [A] | — | — | — | — |

† conditional on chip height 64 (open question R1); a shape surprise adds ~+27K cells
(~+5%) uniformly.

B and F are, at the resolution of the verified numbers, the same design point reached
by two independent routes (their cells and bytes agree once B's byte model is
corrected); they differ in mechanism — merged chip with preprocessed masks (B) versus a
separate absorb instance with anchor-echo (F) — which is a risk choice, not a cost
choice.

---

## 4. Recommendation

The window (no live federations; devnet ledger non-durable; VK regeneration cheap)
prices the one mandatory flag day at its historical minimum. The recurring cost of the
current architecture is not only the ~2× proof size — it is scar #8: six proof layers
per representation change, rising. Both should be bought out in the same window, in
exactly **two VK epochs**, with a bounded decider step first.

### Stage 0 — decider experiments (first bounded step; ~1 swarm total; no epoch, no cuts)

| # | experiment | decides |
|---|---|---|
| D1 | instrument `chip_hist.len()` on the deployed fill and on a simulated rate-8 schedule (minutes; the layout census's 256-vs-512 tension is the same measurement) | chip height 64 vs 128 for every Epoch-2 number; risk R1 |
| D2 | one instrumented build of the LogUp aux path: provenance of the 4.37 ext-cols/interaction ratio (4.74 on the drop variant), how much batching the realization already does | bounds the aux lever (up to ~123K cells, currently ±2×) and every design's aux extrapolation |
| D3 | trace how Rust treats declared main arity 2617 vs trace_width 2664 | whether the scar is load-bearing by accident before any regen "fixes" it |
| D4 | confirm no external deployment holds live v9 commitments (hbox devnet, on-chain) — repo-external | gates the Epoch-2 value flip |
| D5 | PI slots 9–41 consumer census + STATE_RECORD_DIGEST decodability from the rotated limb set | gates H4 retirement and the PI-map regen |
| D6 | per-member chip-cliff table at rate-8 (noteSpend/capOpen family ≈ 70 perms → 128?) | honest per-member claims; registry-wide totals |
| D7 | preprocessed-column spike behind the empty plonky3 hook (smallest possible: one constant column, one VK commit) | B-vs-F mechanism choice; if red, F's anchor-echo path or B's costed fallbacks |

### Stage 1 — Epoch 1, immediately (runs in parallel with Stage 0; they contend on nothing)

Delete S2 at the emitter (`rotV3Appendix`'s two block chains; keep caveat chain, welds,
wide heads), drop PI slots 42/43, regenerate 57×2 registries and FP/VK pins, stop
filling the dead regions in `trace_rotated.rs`. Expect and state the *corrected*
numbers: −31 to −34% cells, −32% bytes, chip stays 256. This move is pure deletion, is
CONFIRMED value-preserving at the constraint level, functions as the live falsifier for
the self-rooting finding, and banks roughly half the total wire savings for ~1/10 the
effort of anything else. Land a correction to
`docs/MEASURE-legacy-1felt-chain-drop.md`'s graft/orphan analysis in the same commit.

### Stage 2 — chip re-architecture, built now, landed with Epoch 2

One-hot flags, tag-decoupled `chipRow` retype, fact-bus deletion, per-shape tuple
routing at the emit. All verified as arithmetic; none of it changes commitment values,
so it rides the Epoch-2 regen rather than spending its own epoch. Chip AIR authorship
moves to the Lean emit path (this is Lean-authored AIR; the current Rust arm is the
debt). If generic evaluation of the 352-col permutation regresses the prover (U5):
Lean-emitted mirror + byte-guards, hypothesis retained and labeled — a named seam, with
its closure lane, not a silent one.

### Stage 3 — Epoch 2: one bundled flag day

Contents: rate-8 domain-seeded chains (blocks + caveat), caveat commit lifted to 8 felts
(closes waist #2), H4 retirement + SDK cap-open re-anchor onto the last-16 wide PIs
(closes waist #1; requires the adversarial test that a cap-gated turn cannot bind
through any retired slot), narrow-tower retirement, PI-map regen, commitment v9→v10
consumer sweep (the palimpsest §5 list), recursion/FS re-pin.

Shape decision, gated on Stage 0: **default to the floor shape** (absorb rows separated
from main — F's separate instance if D7 is red or unpersuasive, B's merged chip if the
preprocessed spike is clean), because the verified wire delta between in-row rate-8 and
the floor is ~95–100 KB per proof (246–254 vs 146–156 KB) against a ~60–80 KB structural
floor, for ~2–4 additional swarms. **Fall back to Design A's in-row rate-8** — still
−69% cells, no new instance, no FS shape change — if D2 reveals the aux model is
substantially wrong, if D7 and the accumulator fallback both look expensive, or if the
Stage-3 lane budget must shrink. Either branch retires the same scars (#1–#5, #9);
the branches differ only in how far toward the wire floor they reach.

### What NOT to do

- **Do not execute the MEASURE doc's re-root-and-migrate plan** ("re-root on a domain
  constant + absorb 49 orphans + flag day"): its premise is REFUTED; the sound
  equivalent is the Epoch-1 deletion plus the Epoch-2 schedule change.
- **Do not route the narrow bus as its own campaign.** Its target (940 dead lanes) dies
  with Epoch 1 for free; the six narrow twin layers should be retired, not completed.
- **Do not promise the naive ceiling (−36.2%/−45.9%) or a chip halving from Epoch 1.**
  134 queries > 128; the halving requires the rate change.
- **Do not ship a 16-input absorb before the tag retype** — it is a cross-domain forgery
  against node8, not a degree problem. (Rate-7/arity-15 is the no-retype fallback,
  costed at ~+6 sites.)
- **Do not hand-write any new Rust AIR** — the absorb instance, the one-hot chip, and
  every new constraint family are Lean-emitted. Extending the existing Rust chip arm is
  the drift.
- **Do not split per-arity chip tables** (each pays the 352-col aux, pow2 padding, and
  an instance).
- **Do not compress the permutation aux via degree-49 two-round constraints** — verified
  net loss (+224 base-eq of quotient vs −176 cols).
- **Do not un-bundle Epoch 2.** Each value-changing component shipped standalone is its
  own 57-member flag day; the bundling is the entire operational point of the window.
- **Do not treat sub-200 ms prover figures as commitments** — every one of them is
  elasticity-1 extrapolation with an unmeasured fixed-overhead floor.

---

## 5. Open questions before the big cuts

1. **Unique-permutation count (R1/D1).** Every "chip height 64" number in §3 is
   conditional on it; also resolves the deployed 256-vs-512 static-estimate tension.
2. **LogUp aux provenance and batching headroom (D2).** The 4.37→4.74 ext/interaction
   drift between the two measured proofs leaves all aux arithmetic at ±10%, and the
   batching lever at ±2×.
3. **External v9 commitment holders (D4)** — unverifiable from the repo; hard gate on
   the Epoch-2 value flip.
4. **The 2617 ≠ 2664 ≠ 2726 width triple (D3)** — how the Rust realization treats the
   declared main arity; audit before the regen retires the class.
5. **PI slots 9–41 semantics and STATE_RECORD_DIGEST coverage (D5)** — gates H4
   retirement; if the record digest is not decodable from the rotated limb set, one
   schedule limb is added (trivial, but it must be decided, not discovered).
6. **gnark wrap regen scope [U]** — the FS shape changes in both floor-shape branches;
   the wrap is not commitment-aware but is transcript-aware; effort unknown and
   external-facing.
7. **Prover fixed-overhead floor** below ~200 ms / ~170K cells — one measurement at
   Epoch-1 scale plus one at a mocked floor-scale instance would calibrate it.
8. **Preprocessed-column grammar acceptance (D7)** — new verified surface (Lean
   semantics + VK commitment); B's fallbacks are costed but change its economics.
9. **Lean-emitted chip AIR prover cost (U5)** — mirror+guard measurement lane before
   cutover; must not block Epoch 2.
10. **Effort calibration** — the same lever set is priced at 4–7 swarms (cost-model) and
    13–18 (rotV4 author); the divergence is the depth of the 57-member proof re-typing
    and whether chip Lean-emission is in scope. Resolve by scoping one member end-to-end
    in the Stage-2 lane before committing the Stage-3 budget.
11. **Vestigial PI-8 reader** — `RotatedParticipantLeg::cell_commit()`
    (`joint_turn_aggregation.rs:1215-1217`) has no live caller found; confirm and delete
    at Epoch 2 rather than leaving a re-entry path to the retired slot.
12. **The 4 B proof-split discrepancy** (both measured proofs) — bookkeeping, but the
    measurement harness should account for it before it is quoted as exact again.
