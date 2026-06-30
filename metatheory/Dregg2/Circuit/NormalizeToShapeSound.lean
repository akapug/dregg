/-
# Dregg2.Circuit.NormalizeToShapeSound — the SOUNDNESS TWIN of the `normalize_to_shape` fork primitive.

This module is the Lean obligation the recursion-fork engineering
(`build_and_prove_normalization_layer`) carries from line one. The fork RE-PROVES any recursion proof
to a CANONICAL fixed-length `non_primitives` manifest — padding the manifest with zero-width DUMMY
tables (Pickles step∘wrap) so the parent verifier's op-list is INVARIANT and the running VK reaches a
fixed point at **DEPTH 1** (instead of the measured depth-4 transient in
`RecursiveAggregation.running_vk_perpetually_constant`). It must ship WITH its soundness theorem; this
is that theorem.

## What "normalize to shape" preserves (the bar)

A recursion-layer proof exposes, at the shape level the parent aggregation circuit reads:

  * a `non_primitives` manifest — a list of tables, each with `(op_type, rows, lanes)` AND the
    `public_values` it contributes to the published PI digest;
  * a published commitment `publish hash m` — the Poseidon2 sponge over the manifest's concatenated
    `public_values`;
  * a committed-execution semantics — the NON-dummy tables (the real constraint content), in order.

A DUMMY table is **zero-width**: `rows = 0`, `lanes = 0`, AND `public_values = []`. Padding the
manifest with dummies is the shape morphism the fork applies (`pad K m = m ++ replicate (K-|m|) dummy`).
Because a dummy contributes EMPTY public-values, padding adds NO committed content; because it is
zero-width, it carries NO semantics. So padding is a **semantics-preserving shape morphism**:

  * `publishedContent_pad` / `publish_pad` — the published commitment is byte-identical (the sponge
    INPUT is unchanged, so the digest is too — this direction needs no crypto at all);
  * `semantics_pad` — the non-dummy content is unchanged (unconditional);
  * `canonical_pad` — the padded manifest has the canonical fixed length `K` (for `|m| ≤ K`).

## The apex (the census shape, faithfully)

`normalize_to_shape_sound`: a proof `m` satisfying the descriptor circuit (`Sat m`) with published
commitment `pi`, when normalized to the canonical shape, yields a proof `m'` that STILL satisfies the
(content-equal) circuit, STILL publishes `pi`, is CANONICAL, and whose semantics are preserved.

`Sat` is the descriptor's satisfaction predicate (the `Satisfied2`-leg — kept ABSTRACT here exactly as
`CircuitSoundness` keeps the published commitment abstract and `RecursiveAggregation` keeps the
`VkShape` opaque; binding the concrete `Satisfied2 hash d t` trace-transform is the heavier
per-descriptor bridge). The one carrier the apex takes is `ShapeContentDetermined Sat` — that the
circuit's satisfaction depends ONLY on the manifest's non-dummy semantic content. This is the FORK's
content-independence, the SAME discharged fact `RecursiveAggregation` already encodes by modeling its
fold transition as `step : VkShape → VkShape` (a function of SHAPE alone, value-independent):
`recursion_vk_fingerprint` is content-independent, and zero-width dummies add no constraints. It is a
NAMED hypothesis (a `Prop` premise), never an axiom.

## The DEPTH-1 fixed point (the fork's whole point, proved STRUCTURALLY)

`RecursiveAggregation.running_vk_perpetually_constant` mechanizes that the running VK is constant PAST
the MEASURED depth-4 fixed point. The fork's deliverable is to KILL the transient: with canonical
normalization the fixed point is reached at the FIRST fold.

  * `canonical_is_fixed_point` — `canonStep K m = m` for any canonical `m` (`canonStep := pad K` is the
    fork's per-fold canonicalization; padding an already-canonical manifest is the identity, since
    `K - K = 0` dummies are appended). This is `step_canonical(canonical) = canonical`, STRUCTURAL — not
    measured.
  * `canon_fixed_at_depth_one` — ONE canonicalization lands at the fixed point:
    `canonStep K (canonStep K m) = canonStep K m`. Depth 1, no transient.
  * `canon_perpetually_constant` — `∀ n, (canonStep K)^[n] m = m` for canonical `m`, off the DEPTH-1
    fixed point (the same `Function.iterate_fixed` backbone as the depth-4 theorem, now anchored at
    depth 1).
  * `step_canonical_id` — folding two canonical-shaped proofs yields a canonical-shaped proof: the
    manifest count is STABLE at `K` (`foldStep K a b` recanonicalizes the combined real tables).

## The crypto floor (reduces to `Poseidon2SpongeCR` ONLY — no new axiom)

The FORWARD soundness (`normalize_to_shape_sound`) needs NO crypto: equal sponge input ⟹ equal digest.
The only place a hash fact is consumed is `publish_binds_content` — the faithfulness/anti-ghost
companion: two proofs publishing the SAME commitment commit the SAME content. That is exactly
`Poseidon2SpongeCR` (the existing carrier from `Poseidon2Binding`), applied once. No other crypto fact,
no new axiom. Everything is `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).

Non-vacuity (§NV): a real canonical shape is exhibited (`real_canonical`), the morphism genuinely moves
a non-canonical shape (`non_canonical_not_fixed`) while preserving its semantics
(`real_semantics_preserved`), and the depth-1 fixed point FIRES on it (`real_depth_one`).
-/
import Dregg2.Tactics
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.NormalizeToShapeSound

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §1 — the recursion-layer shape: a `non_primitives` manifest of tables. -/

/-- One entry of the `non_primitives` manifest: a table's `(op_type, rows, lanes)` plus the
`public_values` it contributes to the published PI digest. A DUMMY table is zero-width
(`rows = 0`, `lanes = 0`) and contributes NO public values (`pubVals = []`). -/
structure TableShape where
  opType  : Nat
  rows    : Nat
  lanes   : Nat
  pubVals : List ℤ

/-- The zero-width dummy table the fork pads with: no rows, no lanes, no public values. Padding the
manifest with these is the canonicalizing shape morphism (Pickles step∘wrap). -/
def dummy : TableShape := { opType := 0, rows := 0, lanes := 0, pubVals := [] }

/-- The Boolean dummy test: zero rows, zero lanes, empty public values. -/
def isDummyB (ts : TableShape) : Bool :=
  ts.rows == 0 && ts.lanes == 0 && ts.pubVals.isEmpty

/-- The published CONTENT: the manifest's `public_values`, concatenated in table order. The published
commitment is the Poseidon2 sponge over THIS list — dummies add nothing because their `pubVals` is `[]`. -/
def publishedContent (m : List TableShape) : List ℤ :=
  (m.map TableShape.pubVals).flatten

/-- The published PI commitment: the sponge digest of the published content. -/
def publish (hash : List ℤ → ℤ) (m : List TableShape) : ℤ :=
  hash (publishedContent m)

/-- The committed-execution SEMANTICS: the NON-dummy tables (the real constraint content), in order.
Dummies carry no semantics, so they are filtered out. -/
def semantics (m : List TableShape) : List TableShape :=
  m.filter (fun ts => !isDummyB ts)

/-- A manifest is CANONICAL at length `K` iff its table count is exactly `K` — the fixed shape the fork
forces so the parent verifier's op-list is invariant. -/
def Canonical (K : Nat) (m : List TableShape) : Prop := m.length = K

/-- **The shape morphism — `pad`.** Pad the manifest with zero-width dummy tables to the canonical
length `K`. For `|m| ≤ K` this lands at exactly `K`; padding an already-canonical manifest is identity. -/
def pad (K : Nat) (m : List TableShape) : List TableShape :=
  m ++ List.replicate (K - m.length) dummy

/-! ## §2 — the morphism is length-canonicalizing and an identity on canonical shapes. -/

/-- The padded manifest has the canonical length `K` (when the input fits, `|m| ≤ K`). -/
theorem length_pad_le {K : Nat} {m : List TableShape} (h : m.length ≤ K) :
    (pad K m).length = K := by
  simp only [pad, List.length_append, List.length_replicate]
  omega

/-- `pad K m` is CANONICAL at `K` (for `|m| ≤ K`) — the canonicalization lands at the fixed length. -/
theorem canonical_pad {K : Nat} {m : List TableShape} (h : m.length ≤ K) :
    Canonical K (pad K m) := length_pad_le h

/-- **Padding an already-canonical manifest is the IDENTITY.** `K - |m| = 0` dummies are appended.
This is the structural fixed point: the canonical shape is fixed by canonicalization. -/
theorem pad_canonical_id {K : Nat} {m : List TableShape} (h : m.length = K) :
    pad K m = m := by
  simp only [pad, h, Nat.sub_self, List.replicate_zero, List.append_nil]

/-! ## §3 — padding preserves the published commitment (the sponge input is unchanged). -/

/-- The published content of a run of dummies is empty (each contributes `pubVals = []`). -/
theorem publishedContent_replicate_dummy (n : Nat) :
    publishedContent (List.replicate n dummy) = [] := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    simp [publishedContent, List.map_cons, dummy]

/-- **`publishedContent_pad`.** Padding leaves the published content byte-identical: the appended
dummies contribute the empty list. -/
theorem publishedContent_pad (K : Nat) (m : List TableShape) :
    publishedContent (pad K m) = publishedContent m := by
  unfold publishedContent pad
  rw [List.map_append, List.flatten_append]
  have hd : publishedContent (List.replicate (K - m.length) dummy) = [] :=
    publishedContent_replicate_dummy _
  unfold publishedContent at hd
  rw [hd, List.append_nil]

/-- **`publish_pad`.** Padding preserves the published PI commitment — the sponge INPUT is unchanged,
so the digest is too. This direction needs NO collision-resistance. -/
theorem publish_pad (hash : List ℤ → ℤ) (K : Nat) (m : List TableShape) :
    publish hash (pad K m) = publish hash m := by
  unfold publish; rw [publishedContent_pad]

/-! ## §4 — padding preserves the committed-execution semantics (dummies carry none). -/

/-- A run of dummies filters to nothing (they fail the non-dummy predicate). -/
theorem filter_replicate_dummy (n : Nat) :
    (List.replicate n dummy).filter (fun ts => !isDummyB ts) = [] := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.filter_cons]
    simp [isDummyB, dummy]

/-- **`semantics_pad`.** Padding preserves the non-dummy semantic content, UNCONDITIONALLY — the
appended dummies are filtered away. -/
theorem semantics_pad {K : Nat} {m : List TableShape} :
    semantics (pad K m) = semantics m := by
  unfold semantics pad
  rw [List.filter_append, filter_replicate_dummy, List.append_nil]

/-! ## §5 — the carrier: the circuit's satisfaction is content-determined (the fork's content
independence — the SAME discharged fact `RecursiveAggregation.step : VkShape → VkShape` encodes). -/

/-- **`ShapeContentDetermined Sat`** — the fork's content-independence, NAMED. The descriptor circuit's
satisfaction depends ONLY on the manifest's non-dummy semantic content: two manifests with equal
`semantics` are satisfied together. Realized by `recursion_vk_fingerprint`'s content-independence +
zero-width dummies adding no constraints. A `Prop` PREMISE, never an axiom. -/
def ShapeContentDetermined (Sat : List TableShape → Prop) : Prop :=
  ∀ m m', semantics m = semantics m' → (Sat m ↔ Sat m')

/-- The preservation bundle the apex delivers: semantics AND published content unchanged. -/
structure SemanticsPreserved (m m' : List TableShape) : Prop where
  /-- the non-dummy semantic content is unchanged. -/
  sem : semantics m' = semantics m
  /-- the published content (hence the PI commitment) is unchanged. -/
  pub : publishedContent m' = publishedContent m

/-! ## §6 — THE APEX: `normalize_to_shape_sound`. -/

/-- **`normalize_to_shape_sound` (THE CENSUS SHAPE).** Normalizing a proof to the canonical shape
PRESERVES (a) its published commitment and (b) its committed-execution semantics. Concretely: a proof
`m` satisfying the descriptor circuit (`Sat m`) with published commitment `pi` yields a normalized `m'`
that STILL satisfies the content-equal circuit, STILL publishes `pi`, is CANONICAL at `K`, and whose
semantics are preserved. The witness is `pad K m`. Reduces to: `ShapeContentDetermined` (the named fork
carrier) for the satisfaction leg; pure equational shape lemmas for publish + semantics. No crypto, no
new axiom. -/
theorem normalize_to_shape_sound
    (hash : List ℤ → ℤ)
    (Sat : List TableShape → Prop) (hSat : ShapeContentDetermined Sat)
    (K : Nat) (m : List TableShape) (hlen : m.length ≤ K)
    (pi : ℤ) (hpub : publish hash m = pi) (hsat : Sat m) :
    ∃ m', Sat m'
        ∧ publish hash m' = pi
        ∧ Canonical K m'
        ∧ SemanticsPreserved m m' := by
  refine ⟨pad K m, ?_, ?_, ?_, ?_⟩
  · -- satisfaction is preserved under the content-determined circuit
    exact (hSat m (pad K m) (semantics_pad).symm).mp hsat
  · -- the published commitment is unchanged
    rw [publish_pad]; exact hpub
  · -- the normalized manifest is canonical
    exact canonical_pad hlen
  · -- semantics + published content preserved
    exact ⟨semantics_pad, publishedContent_pad K m⟩

/-- **`publish_binds_content` (the faithfulness/anti-ghost — THE SOLE crypto consumer).** Under
Poseidon2-sponge collision-resistance, two proofs publishing the SAME commitment commit the SAME
content. This is the ONLY place a hash fact is used in the whole module — `Poseidon2SpongeCR`, applied
once. It makes the published-commitment preservation BINDING (a normalized proof can't silently swap
content behind an equal digest). -/
theorem publish_binds_content (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {m m' : List TableShape} (h : publish hash m = publish hash m') :
    publishedContent m = publishedContent m' :=
  hCR _ _ h

/-! ## §7 — THE DEPTH-1 FIXED POINT (the structural version of `running_vk_perpetually_constant`). -/

/-- The fork's per-fold canonicalization map: re-normalize the running manifest to the canonical
shape. The VK-shape transition `RecursiveAggregation.step` projects through this. -/
def canonStep (K : Nat) : List TableShape → List TableShape := pad K

/-- **`canonical_is_fixed_point` (= `step_canonical(canonical) = canonical`).** The canonical shape is a
FIXED POINT of canonicalization — STRUCTURALLY, not measured. (`RecursiveAggregation` carries the depth-4
fixed point as a MEASURED hypothesis `hfix : step anchor = anchor`; here it is PROVED for the canonical
shape, with no measurement.) -/
theorem canonical_is_fixed_point {K : Nat} {m : List TableShape} (h : Canonical K m) :
    canonStep K m = m := pad_canonical_id h

/-- **`canon_fixed_at_depth_one` (THE FORK'S DELIVERABLE — fixed point at DEPTH 1).** ONE
canonicalization lands at the fixed point: applying `canonStep` again is the identity. This is the
transient-killer — `RecursiveAggregation`'s fixed point sits at the MEASURED depth 4 (after a 2-step
transient); canonical normalization reaches it at depth 1. -/
theorem canon_fixed_at_depth_one {K : Nat} {m : List TableShape} (hlen : m.length ≤ K) :
    canonStep K (canonStep K m) = canonStep K m :=
  canonical_is_fixed_point (canonical_pad hlen)

/-- **`canon_perpetually_constant` (the structural twin of `running_vk_perpetually_constant`).** Off the
DEPTH-1 fixed point, every further fold leaves the shape unchanged: `∀ n, (canonStep K)^[n] m = m` for
canonical `m`. Same `Function.iterate_fixed` backbone as the depth-4 theorem — but anchored at depth 1,
so a light client pins the ONE canonical anchor from the FIRST aggregation, no transient. -/
theorem canon_perpetually_constant {K : Nat} {m : List TableShape} (h : Canonical K m) :
    ∀ n, (canonStep K)^[n] m = m :=
  fun n => Function.iterate_fixed (canonical_is_fixed_point h) n

/-- The running fold's shape step: combine the two children's real (non-dummy) tables, then
re-canonicalize to the fixed length `K`. -/
def foldStep (K : Nat) (a b : List TableShape) : List TableShape :=
  pad K (semantics a ++ semantics b)

/-- **`step_canonical_id` (folding two canonical-shaped proofs yields a canonical-shaped proof — the
manifest count is STABLE at `K`).** Given the combined real tables fit (`|semantics a ++ semantics b| ≤
K`, the aggregation circuit's bounded-non-primitives design invariant), the fold's output is canonical
at `K`. So the running VK's manifest count is a fixed point — depth-invariant from the first fold. -/
theorem step_canonical_id {K : Nat} {a b : List TableShape}
    (hcomb : (semantics a ++ semantics b).length ≤ K) :
    Canonical K (foldStep K a b) :=
  canonical_pad hcomb

/-! ## §NV — non-vacuity: the morphism FIRES on a real canonical shape. -/

/-- A genuine non-dummy table: a real op with rows, lanes, and a published value. -/
def realTable : TableShape := { opType := 1, rows := 4, lanes := 2, pubVals := [7] }

/-- `realTable` is genuinely NOT a dummy. -/
theorem realTable_not_dummy : isDummyB realTable = false := by decide

/-- A concrete canonical shape: pad the single real table to canonical length 3. -/
def realCanon : List TableShape := pad 3 [realTable]

/-- **A real canonical shape EXISTS** — `realCanon` has the canonical length 3 (one real table + two
dummies). The morphism's target is inhabited, not a husk. -/
theorem real_canonical : Canonical 3 realCanon := by
  unfold Canonical realCanon
  simp [pad]

/-- **The morphism preserves semantics on the witness** — the canonical shape carries EXACTLY the one
real table the input did. -/
theorem real_semantics_preserved : semantics realCanon = semantics [realTable] :=
  semantics_pad

/-- **A NON-canonical shape is NOT a fixed point (the A/B non-vacuity half).** The bare single-table
manifest (length 1 ≠ 3) is genuinely MOVED by canonicalization — so the fixed-point equalities above
are LOAD-BEARING (the early shape really differs), the companion of
`RecursiveAggregation.real_running_vk_transient_is_real`. -/
theorem non_canonical_not_fixed : canonStep 3 [realTable] ≠ [realTable] := by
  intro h
  have hcl := congrArg List.length h
  simp [canonStep, pad] at hcl

/-- **The DEPTH-1 fixed point FIRES on the witness** — one canonicalization of the real single-table
manifest lands at a fixed point: applying `canonStep` again is the identity. A real, non-vacuous
instance of the transient-killer. -/
theorem real_depth_one : canonStep 3 (canonStep 3 [realTable]) = canonStep 3 [realTable] :=
  canon_fixed_at_depth_one (by decide)

/-! ## §AX — axiom hygiene: every keystone is `#assert_axioms`-clean (no new axiom; the sole crypto
carrier is `Poseidon2SpongeCR`, taken as a hypothesis). -/

#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.length_pad_le
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.canonical_pad
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.pad_canonical_id
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publishedContent_pad
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publish_pad
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.semantics_pad
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.normalize_to_shape_sound
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.publish_binds_content
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.canonical_is_fixed_point
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.canon_fixed_at_depth_one
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.canon_perpetually_constant
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.step_canonical_id
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.realTable_not_dummy
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.real_canonical
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.real_semantics_preserved
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.non_canonical_not_fixed
#assert_axioms Dregg2.Circuit.NormalizeToShapeSound.real_depth_one

end Dregg2.Circuit.NormalizeToShapeSound
