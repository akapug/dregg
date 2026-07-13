# The Verified Layout Allocator + Optimizer — design (the snarky we never finished)

**Status:** design, post-Phase-0 census (2026-07-12, 4 read-only scholars). **Author:** this session (Fable),
for ember. **Origin:** the revoked-root 178 geometry migration paid the tuition — one added limb caused a
14-file re-grind, a design fork (the 170-leftover), a constraint bug (cells relocation), a producer carrier
stride bug, and 5 stale limb assertions. All **one disease**.

## 1. The disease (one sentence)

**The circuit layout is a pile of hand-carried column integers, the invariants that make a layout legal are
unchecked comment conventions, and the proofs pin the concrete integers — so every flag-day is a 14-file act of
faith that plonky3 audits *after* a VK regen instead of the type system at construction.**

Ground truth (census scholar 1): the disjointness invariant ("no two things write the same limb" — the exact
cause of both the cells/revoked overlap AND the producer-carrier drift) is **NOT machine-checked anywhere**;
it is held by a comment (`EffectVmEmitRotationV3.lean:1695`). The +1-shift consistency is "held by hand, no
cross-file check." `NUM_PRE_LIMBS = 178` is declared **three times independently** (commitment.rs,
rotation_witness.rs, trace_rotated.rs); the two producers are byte-identical copies. Six enumerated
producer↔circuit duplication points.

## 2. The thesis

dregg uniquely already has the half nobody else has — a **verified EMIT** (descriptors are projections of proven
Lean; `emit_descriptors.py` byte-golden loop, `check-descriptor-drift.sh`). What is missing is the layer *below*
the emit — the **allocator** (snarky/halo2/circom all have one, but *unverified*) — and, above it, an
**optimizer**. We build both, verified. The allocator makes the layout a **verified object**; the optimizer
makes it **cheap** — and the key unlock is that **the optimizer's search is untrusted; only its output + a
refinement proof are checked** (translation validation).

## 3. Ground truth the design is built on (Phase-0 census)

- **Parametric scaffolding half-exists** (scholar 1): every `*GroupCol (blockBase)` and `rotV3SitesAt (base)`
  is *already* parametric over the block offset, with proven `_lane0` projections — but the **within-block
  positions are hardcoded literal limb-lists** (`68..74`, `75..81`, `82..88`, `169..175`). The allocator
  **extends existing parametricity inward**; it does not reinvent it.
- **The gadget algebra is clean and minimal** (scholar 2): `EmittedExpr = var(Nat) | const(Int) | add | mul`
  with a *proved* round-trip to the Rust mirror (`emit_faithful`); gadgets exist (`MerkleHash8`,
  `ChainedHash2to1`, `Lookup`, `MapOp`, `VmHashSite`). **No allocator/optimizer/CSE exists anywhere** (crate-wide
  grep). The poster child: `rotV3SitesAt` is a **hand-unrolled 48-row Merkle–Damgård chain** — a `chainBody(base,
  depth)` combinator would *generate and prove* it.
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
  - **Honest floor:** AIR soundness is **ASSUMED** via the `StarkSound` class, *reduced* (not eliminated) to two
    named residuals (`DeployedTraceExtract` = FRI-proximity-onto-deployed-trace + `DeployedRefines` = Rust
    verify_batch ↔ Lean verifyAlgo). An optimized AIR inherits a **fresh** `StarkSound R'` — the TV equivalence
    does NOT discharge it. The optimizer **neither worsens nor discharges** the floor; it preserves
    refinement/completeness through the transform.

## 4. The design (phased)

### Phase 1 — `RotatedLayout` (the verified allocator)
A Lean structure carrying the ABSTRACT layout — base-region assignments, the 8-felt completion groups, octets,
pads, and the chain-site graph *shape* — with the currently-unchecked invariants as **constructor obligations**:
- **Disjointness** (`Nodup` over every occupied limb — the invariant that is a comment today).
- **Multiple-of-3 body** (the 58×3 discipline; the leftover-chunk fork becomes unrepresentable).
- **Bounds** (every index < NUM_PRE_LIMBS) and **arity discipline** (4-head/3-body; the wide-chip arity-11-or-refuse).

The **spine lemmas** (`preLimbsAt_length`, the `*GroupCol_lane0` projections, `rotV3SitesAt` chain
well-formedness) are proven **once, parametrically** over any layout satisfying the invariants. The current 178
layout is re-expressed as an **INSTANCE** that discharges the obligations by `decide`/`native_decide`
(stays `#assert_axioms`-clean). `rotV3SitesAt`'s hand-unroll is replaced by a verified `chainBody(base, depth)`
combinator (scholar 2's poster child). **Result:** a flag-day becomes a new instance + its obligation proof, not
a 14-file re-grind; an ill-aligned layout is a *type error at construction*.

### Phase 2 — producer derivation
The Rust producer (both byte-identical copies: `commitment.rs`, `rotation_witness.rs`) and the circuit derive
column positions **from the one layout instance**. Collapses the six duplication points; the producer↔circuit
drift bug **class** (the carrier bug) dies — they cannot diverge because they read one source.

### Phase 3 — the optimizer (translation validation)
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
- It does **not** discharge the `StarkSound` (AIR-soundness) assumption. Each optimized AIR gets a fresh assumed
  `StarkSound R'`. The optimizer makes circuits *efficient* and *preserves refinement*; the FRI-extraction floor
  is assumed for the optimized circuit exactly as for the current one. (See [[project-circuit-soundness-apex]] —
  `StarkSound` is assumed, reduced to `DeployedTraceExtract` + `DeployedRefines`.)
- It does not fix the live named residuals (the `guardAvail` mod-p wrap gap in the transfer template) — those
  are pre-existing and orthogonal.
- The verified part is the **equivalence between two same-kernel descriptors**, at the `Satisfied2` layer.

## 7. The open scope call (ember's)
**Vertical-slice-first (rotated-commitment family) vs general-AIR-authoring-from-day-one.** Recommendation:
**vertical slice.** Phase 1–2 on the rotated block alone kills the exact bug class we just fought and de-risks
the two campaigns that touch geometry next (the light-client `MapAbsent`-lift + epoch-first revocation, both
become layout instances). Phase 3's first pass (table-ize the rotated hashes) has a *proven* payoff. Generalize
to all-AIR authoring after the slice proves the pattern.

## 8. Why this is worthy + de-risked
Not one speculative link in the chain: the allocator **extends** existing parametricity; the invariants it
enforces are **already the bugs we hit**; the optimizer's first win is a **proven technique** with a **measured**
objective; and the proof rails (denotation, two-sided legs, parametric preservation lemmas, the non-vacuity
discipline) **already exist** — the optimizer is a *wiring job* for degree, a *mechanical lemma* for relocation,
and *one foundational lemma* (raw material present) for CSE. It is the natural completion of dregg's
verified-circuit thesis: the only verified snarky.
