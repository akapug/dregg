# The Verified Layout Allocator + Optimizer — design (the snarky we never finished)

**Status:** Phases 1–2 built (the allocator `RotatedLayout` and the emit-derivation bridge are in-tree,
`metatheory/Dregg2/Circuit/Emit/RotatedLayout{,Bridge}.lean`); Phase 3 (the optimizer) is design.
**Author:** a Fable session, for ember. **Origin:** the revoked-root 178 geometry migration paid the
tuition — one added limb caused a 14-file re-grind, a design fork (the 170-leftover), a constraint bug
(cells relocation), a producer carrier stride bug, and 5 stale limb assertions. All **one disease**.

## 1. The disease (one sentence)

**The disease the allocator kills: a circuit layout held as a pile of hand-carried column integers, the
invariants that make a layout legal held as unchecked comment conventions, and proofs that pin the concrete
integers — so every flag-day is a 14-file act of faith that plonky3 audits *after* a VK regen instead of the
type system at construction.**

Ground truth at HEAD: the disjointness invariant ("no two things write the same limb" — the exact cause of
both the cells/revoked overlap AND the producer-carrier drift) is **machine-checked**: the `Legal` structure
carries it as a proof obligation (`disjoint : L.occupied.Nodup`,
`metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean`), the deployed geometry discharges it as the
`rotated178` instance (`rotated178_legal`, plus the stronger complete-tiling `rotated178_complete`), and a
Rust mirror test (`rotated_layout_is_a_complete_disjoint_tiling`, `circuit/src/effect_vm/trace_rotated.rs`)
asserts the same tiling on the producer/circuit side. Named seam: the producer copies still hand-declare
positions (`cell/src/commitment.rs::V9_NUM_PRE_LIMBS`, `turn/src/rotation_witness.rs`) — they are pinned by
the mirror-tooth test against the Lean-exported `effect_vm::layout_generated` rather than deriving by
construction; making them literal projections is a proof-backed pure refactor, not yet taken.

## 2. The thesis

dregg uniquely already has the half nobody else has — a **verified EMIT** (descriptors are projections of proven
Lean; `emit_descriptors.py` byte-golden loop, `check-descriptor-drift.sh`). The layer *below* the emit — the
**allocator** (snarky/halo2/circom all have one, but *unverified*) — is now built and verified
(`RotatedLayout`). What is missing is the layer *above*: the **optimizer**. The allocator makes the layout a
**verified object**; the optimizer makes it **cheap** — and the key unlock is that **the optimizer's search is
untrusted; only its output + a refinement proof are checked** (translation validation).

## 3. Ground truth the design is built on (Phase-0 census)

- **Parametric scaffolding** (scholar 1): every `*GroupCol (blockBase)` and `rotV3SitesAt (base)` is
  parametric over the block offset, with proven `_lane0` projections. The within-block positions are literal
  limb-lists in the deployed emit (`68..74`, `75..81`, `82..88`, `169..175`) — each now **proven equal
  lane-for-lane to the layout's projection** (`RotatedLayoutBridge.lean`'s seven `*GroupCol_eq_layout`
  theorems), so the allocator's parametricity reaches inward without moving a descriptor byte.
- **The gadget algebra is clean and minimal** (scholar 2): `EmittedExpr = var(Nat) | const(Int) | add | mul`
  with a *proved* round-trip to the Rust mirror (`emit_faithful`); gadgets exist (`MerkleHash8`,
  `ChainedHash2to1`, `Lookup`, `MapOp`, `VmHashSite`). The allocator now exists (`RotatedLayout`); **no
  optimizer/CSE exists anywhere** (crate-wide grep). The poster child: `rotV3SitesAt` is a **hand-unrolled
  48-row Merkle–Damgård chain** — a `chainBody(base, depth)` combinator would *generate and prove* it (still
  open).
- **The cost objective is measured** (scholar 3): proof cost ≈ `num_queries × Σ(committed table widths)`;
  queries pinned by the security floor ⇒ **the only lever is committed width**, dominated by Poseidon2 aux.
  Degree is a **closed book** (the degree-3 S-box variant was built and measured *worse*). The single biggest
  win is a **proven technique**: map-ops went **12,007 → 71 columns** by table-izing hashes onto the shared chip
  bus — *not yet applied* to the rotated main table's inline hash sites (938 IR-v2 / 1,408 v1 columns of fat).
  Some pad columns exist "only to hit a grouping aesthetic" (the 58×3 body) — fat by construction.
- **The proof rails exist, transform-scoped** (scholar 4 — the pivotal one):
  - A descriptor's **denotation is `Satisfied2 hash d minit mfin maddrs t`** (a first-class accepting-traces
    Prop). Two-sided: completeness (`descriptorComplete`, accepts honest) + soundness (`descriptorRefines`,
    rejects dishonest), with non-vacuity teeth. Descriptor equivalence
    `Satisfied2 (opt d) ↔ Satisfied2 d` is **expressible today** — no new type needed.
  - **Genuine, parametric, translation-validation-shaped preservation lemmas already exist**:
    `graduateV1_faithful` (a real ↔, both directions, over any graduable d), `embedV1_satisfied_iff`,
    `rotV3_sound_v1` (rotation = a column relocation *shipping with* a parametric preservation proof — the exact
    pattern the optimizer wants), `normalize_to_shape_sound` (closest to a general TV lemma). The **discipline**
    (`#assert_axioms`-clean, `@[load_bearing]` lint, `#guard` non-vacuity, false-pole teeth) is reusable
    off-the-shelf.
  - **Honest floor:** AIR soundness is a **proven reduction**, not an opaque assumption: `starkSound_of_core`
    derives `StarkSound` from `RSProximityCore` (`StarkSoundReduction.lean`, `#assert_axioms`-clean),
    `DeployedTraceExtract` is itself derived from the proven FRI keystone
    (`deployedTraceExtract_of_embedding`, `DeployedTraceExtract.lean`) with the residual an explicit
    hypothesis structure (`DeployedFriEmbedding`'s two named maps, `accept_folds` + `decode_trace`), and
    `DeployedRefines` is discharged for the faithful model (`DeployedRefinesProof.lean`). An optimized AIR
    gets its `StarkSound R'` through the **same reduction instantiated for it** — the TV equivalence neither
    worsens nor discharges the floor; it preserves refinement/completeness through the transform.

## 4. The design (phased)

### Phase 1 — `RotatedLayout` (the verified allocator) — **BUILT**
`metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean`: a Lean structure carrying the ABSTRACT layout —
base-region assignments, the 8-felt completion groups, octets, pads — with the previously-unchecked
invariants as the **`Legal` proof obligations**:
- **Disjointness** (`disjoint : L.occupied.Nodup` — the invariant that was a comment).
- **Bounds** (`inBounds` — every index < NUM_PRE_LIMBS) and alignment discipline.

The deployed 178 geometry is the **`rotated178` instance**, discharging the obligations by
`native_decide` (`rotated178_legal`), plus the stronger complete-tiling fact
(`rotated178_complete : rotated178.occupied.length = 178`). An ill-aligned layout is unconstructable-as-`Legal`;
a flag-day becomes a new instance + its obligation proof, not a 14-file re-grind. Not taken from the original
plan: `rotV3SitesAt` remains a hand-unrolled chain in `EffectVmEmitRotationV3.lean` — the verified
`chainBody(base, depth)` combinator (scholar 2's poster child) is a named, still-open refactor.

### Phase 2 — producer derivation — **BUILT (non-invasive form) + one named seam**
`RotatedLayoutBridge.lean` proves each of the seven deployed `*GroupCol` defs equals
`rotated178.groupCol`'s projection at every lane — the verified layout is the proven source of truth for the
emit geometry **without changing a single emitted byte** (no descriptor/VK movement). On the Rust side, the
mirror-tooth test pins the circuit's hand-declared constants to the Lean-exported
`effect_vm::layout_generated`, and `rotated_layout_is_a_complete_disjoint_tiling` asserts the full tiling.
Named seam: the producer copies (`cell/src/commitment.rs`, `turn/src/rotation_witness.rs`) are test-pinned,
not derived by construction — refactoring them to literal projections is a proof-backed pure refactor.

### Phase 3 — the optimizer (translation validation) — **DESIGN, unbuilt**
`nice model → (UNTRUSTED search) → efficient AIR + a checked Satisfied2-equivalence proof`. The search may be
arbitrarily aggressive/heuristic/ML-driven; a wrong optimization simply fails to close its proof and never
ships. Targets the **`Satisfied2` accept-set layer** (where all the machinery lives). Passes, in payoff order:
1. **Table-ize the rotated hash sites** (the de-risked first pass): apply the *proven* map-ops technique
   (12,007→71) to the rotated main table — move inline Poseidon2 aux onto the shared chip bus. ~938–1,408 column
   win. This is a **CSE-class** transform (share the hash computation) ⇒ needs the one new foundational lemma
   (§5). Highest value, and the technique already works elsewhere.
2. **Pad/zero-column elimination** — drop the aesthetic pads the allocator exposes (column-relocation class).
3. **Degree rewrites** (pure-algebraic) — wiring on existing mod-p `holdsVm`-iff rails.
4. **Column-packing** — reuse columns across disjoint lifetimes (column-permutation class).

Objective = the measured cost model: minimize `Σ(committed table widths)` (queries pinned). Cost model needs no
soundness proof (it is the objective, not the guarantee).

## 5. Proof strategy per optimization class (scholar 4's verdict, made a plan)
| Class | Verdict | What it needs |
|---|---|---|
| Degree reduction (pure-algebraic) | **wiring** | per-rewrite `holdsVm c₁ ↔ holdsVm c₂` by `ring`/mod-p (rails exist — DEBT-A's `gate_modEq_iff`) |
| Column relocation / pad-drop | **mechanical new lemma** | a general `Satisfied2 (relocate π d) (permute π t) ↔ Satisfied2 d t` (the bespoke `rotV3_sound_v1` pattern, generalized) |
| CSE / witness-introducing degree reduction | **one foundational lemma** | `∃-witness-column preserves accept-set` — **raw material present** (the aux-column mechanism in `graduateV1` already does exactly this shape: pinned aux columns, existentially witnessed by the honest prover) |

Reusable off-the-shelf: `#assert_axioms` gating, `#guard` non-vacuity, the false-pole tooth (a *non*-equivalent
rewrite must NOT be provable). `LoadBearingLint`'s not-defeq-to-gate check is executor-spec-specific and would
need a small analogue (a "transform is non-trivial" check).

## 6. Honest scope (what it does NOT do)
- It does **not** move the STARK-soundness floor in either direction. `StarkSound` is a proven reduction to
  `RSProximityCore` (`starkSound_of_core`), with `DeployedTraceExtract` derived from the proven FRI keystone
  and the residual named precisely (`DeployedFriEmbedding`'s `accept_folds` + `decode_trace`); an optimized
  AIR gets its `StarkSound R'` through the same reduction instantiated for it. The optimizer makes circuits
  *efficient* and *preserves refinement*; the proximity floor stands for the optimized circuit exactly as for
  the current one.
- It is orthogonal to circuit-level soundness discharges. The transfer template's `guardAvail` availability
  wrap is closed in-proof on the deployed wide+welded registry rows (`RotatedKernelRefinementAvail` on the
  narrow hardened transfer; `RotatedKernelRefinementAvailWide` carries the discharge to the post-retarget wide
  rows, `transfer_descriptorRefinesAvail_weldedWide` assembling the full `BalanceMovementSpec` refinement) —
  the optimizer neither depends on nor touches that discharge.
- The verified part is the **equivalence between two same-kernel descriptors**, at the `Satisfied2` layer.

## 7. The scope call (resolved: vertical slice, taken)
The vertical slice (rotated-commitment family) is the built state: Phase 1–2 on the rotated block kill the
exact bug class the 178 migration hit, and campaigns that touch geometry next become layout instances. The
remaining open call is **when to generalize to all-AIR authoring** — after Phase 3's first pass (table-ize the
rotated hashes, a *proven*-payoff technique) proves the optimizer pattern on the slice.

## 8. Why the optimizer is worthy + de-risked
Not one speculative link in the chain: the allocator it builds on is **in-tree and verified**; the invariants
it enforces are **the bugs already hit**; the optimizer's first win is a **proven technique** with a
**measured** objective; and the proof rails (denotation, two-sided legs, parametric preservation lemmas, the
non-vacuity discipline) **already exist** — the optimizer is a *wiring job* for degree, a *mechanical lemma*
for relocation, and *one foundational lemma* (raw material present) for CSE. It is the natural completion of
dregg's verified-circuit thesis: the only verified snarky.
