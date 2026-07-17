/-
# Market.CertFDescriptor — the Cert-F AIR, AUTHORED IN LEAN as an `EffectVmDescriptor2`.

`Market.CertF` proves the fhEgg Cert-F soundness core (`weak_duality`,
`certifies_epsilon_optimal`) and — at the toy `Dregg2.Circuit.ConstraintSystem` level —
emits the *equality* part of the certificate check (`certCircuit`, `certCircuit_sound`),
NAMING the feasibility inequalities as riding "the standard AIR range gadget".

The historical `circuit-prove/src/cert_f_air.rs::cert_f_descriptor` hand-built the full
`EffectVmDescriptor2` in Rust. This module closes that gap: it
AUTHORS the exact same descriptor in Lean as a total function of the public program, and
PROVES the emit-SOUNDNESS bridge (`certFDescriptor_emit_sound`, §6), GENERIC over every
`p : CertFProg`:

    Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)
      →  a is a valid Cert-F certificate for p

i.e. ANY assignment whose constant trace satisfies the deployed IR-v2 denotation `Satisfied2`
carries a certificate obeying ALL FIVE families over the BabyBear field — `A f = 0`, `0 ≤ f ≤ c`,
`s ≥ 0`, `Aᵀπ + s ≥ w`, `cᵀs − wᵀf ≤ ε` — plus the objective pin `obj ≡ wᵀf`. This is the SECURITY
direction (a satisfying trace cannot lie) — the theorem the hand-written Rust could only *test*.
The feasibility inequalities ride the range-gadget tooth `rangeGadget_forces_range` (§5), exactly
the gadget `Market.CertF` deferred to "the standard AIR range gadget", now PROVED. The
COMPLETENESS direction (a valid certificate has a satisfying trace) is witnessed executably by the
byte-identical Rust STARK (`cert_f_air.rs::air_accepts_valid_ring3` /
`stark_proves_and_verifies_ring3`).

The Rust is re-pointed onto this Lean-authored descriptor via the byte-pinned-twin discipline the
effect_vm family uses: `emitVmJson2 certFDescriptor` is the canonical wire string (committed at
`circuit/descriptors/dregg-cert-f-ir2.json`) and is exact-equality pinned against the literal in
`Market.CertFGolden`. Rust `include_str!`s and parses committed artifacts; it authors no Cert-F
constraint. A different public `(A,w,c,ε)` program is deliberately fail-closed until its own
emitted artifact, byte pin, and registry entry exist — but (since the §6 bridge is generic) it
needs NO new proof: emission + pinning is the whole registration cost.

## The five constraint families (mirroring `cert_f_air.rs` exactly)

For the circulation LP `max wᵀf s.t. Af=0, 0≤f≤c`, dual `(π, s)`, a certificate `(f,π,s)`
is ε-optimal iff `Af=0 ∧ 0≤f≤c ∧ s≥0 ∧ Aᵀπ+s≥w ∧ cᵀs−wᵀf≤ε`. Over the witness columns
`(f, s, π)` + slack columns `(u, d, g)` + objective `obj`:

  1. conservation `Σ_{head=i} f_e − Σ_{tail=i} f_e = 0` — one arithmetic gate per node.
  2. box lower `f_e ≥ 0` — the range gadget on `f_e`.
  3. box upper `c_e − f_e ≥ 0` — `u_e == c_e − f_e` (gate) + range gadget on `u_e`.
  4. slack sign `s_e ≥ 0` — the range gadget on `s_e`.
  5. dual feas `π_head − π_tail + s_e − w_e ≥ 0` — `d_e == …` (gate) + range gadget on `d_e`.
  6. gap `cᵀs − wᵀf ≤ ε` — `g == ε − (cᵀs − wᵀf)` (gate) + range gadget on `g`.
  7. objective `obj == wᵀf` (gate) + expose `obj` as the one public input (`wᵀf`).

The range gadget is `certFValueBits` boolean gates `b(b−1)==0` plus one recompose gate
`col − Σⱼ 2ʲ·bⱼ == 0`, forcing `col ∈ [0, 2^bits)` — the field-soundness tooth.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Market.CertF
import Market.CertFGolden

namespace Market.CertFDescriptor

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2

/-! ## §1 — The public program + column layout (byte-identical to `cert_f_air.rs`). -/

/-- The in-AIR range-gadget bit-width (`cert_f_air.rs::VALUE_BITS = 28`). -/
def certFValueBits : Nat := 28

/-- The public program a Cert-F descriptor rides on: the incidence (edge list `(tail, head)`),
the objective weights `w`, the capacities `c`, and the accuracy target `ε`. The private
witness `(f, π, s)` is NOT here — it lives only in the trace. -/
structure CertFProg where
  nNodes : Nat
  edges  : List (Nat × Nat)
  w      : List Int
  c      : List Int
  eps    : Int
  deriving Repr

namespace CertFProg

def m (p : CertFProg) : Nat := p.edges.length
def tailAt (p : CertFProg) (e : Nat) : Nat := (p.edges.getD e (0, 0)).1
def headAt (p : CertFProg) (e : Nat) : Nat := (p.edges.getD e (0, 0)).2
def wAt (p : CertFProg) (e : Nat) : Int := p.w.getD e 0
def cAt (p : CertFProg) (e : Nat) : Int := p.c.getD e 0

/-- Column layout — the EXACT `CertFWitness::*_col` offsets. -/
def fCol   (_p : CertFProg) (e : Nat) : Nat := e
def sCol   (p : CertFProg) (e : Nat) : Nat := p.m + e
def piCol  (p : CertFProg) (i : Nat) : Nat := 2 * p.m + i
def objCol (p : CertFProg) : Nat := 2 * p.m + p.nNodes
def uCol   (p : CertFProg) (e : Nat) : Nat := p.objCol + 1 + e
def dCol   (p : CertFProg) (e : Nat) : Nat := p.objCol + 1 + p.m + e
def gCol   (p : CertFProg) : Nat := p.objCol + 1 + 2 * p.m
def bitBase (p : CertFProg) : Nat := p.gCol + 1
/-- Range-bit column: `bit_base + target·VALUE_BITS + j` (`range_bit_col`). -/
def rangeBitCol (p : CertFProg) (target j : Nat) : Nat := p.bitBase + target * certFValueBits + j
/-- Full trace width: scalars + the `(4m+1)·VALUE_BITS` range bits. -/
def width (p : CertFProg) : Nat := p.bitBase + (4 * p.m + 1) * certFValueBits

end CertFProg

/-! ## §2 — Expression / gate constructors (byte-identical to `cert_f_air.rs`). -/

/-- `x − y` as an `EmittedExpr` (`cert_f_air.rs::sub`). -/
def esub (x y : EmittedExpr) : EmittedExpr := .add x (.mul (.const (-1)) y)

/-- A pure per-row vanishing gate `body == 0` (`cert_f_air.rs::gate`). -/
def egate (body : EmittedExpr) : VmConstraint2 := .base (.gate body)

/-- The `j`-th boolean gate body `bⱼ·(bⱼ−1)` of a range gadget. -/
def boolExpr (bitCol : Nat → Nat) (j : Nat) : EmittedExpr :=
  let b := EmittedExpr.var (bitCol j)
  .mul b (esub b (.const 1))

/-- The recompose gate body `col − Σⱼ 2ʲ·bⱼ` of a range gadget. -/
def recomposeExpr (col : Nat) (bitCol : Nat → Nat) : EmittedExpr :=
  (List.range certFValueBits).foldl
    (fun acc j => esub acc (.mul (.const ((2 : Int) ^ j)) (EmittedExpr.var (bitCol j))))
    (EmittedExpr.var col)

/-- The range gadget for one target column: `certFValueBits` boolean gates `b(b−1)==0` plus one
recompose gate `col − Σⱼ 2ʲ·bⱼ == 0` (`cert_f_air.rs::range_gadget`). -/
def rangeGadget (col : Nat) (bitCol : Nat → Nat) : List VmConstraint2 :=
  ((List.range certFValueBits).map (fun j => egate (boolExpr bitCol j))) ++
  [ egate (recomposeExpr col bitCol) ]

/-! ## §3 — The descriptor (the five families, in `cert_f_air.rs` order). -/

/-- Conservation body at node `i`: `Σ_{head=i} f_e − Σ_{tail=i} f_e` (`cert_f_descriptor` step 1). -/
def consBody (p : CertFProg) (i : Nat) : EmittedExpr :=
  (List.range p.m).foldl
    (fun body e =>
      let body := if p.headAt e == i then .add body (EmittedExpr.var (p.fCol e)) else body
      if p.tailAt e == i then esub body (EmittedExpr.var (p.fCol e)) else body)
    (.const 0)

/-- The full Cert-F constraint list, in the exact order `cert_f_air.rs::cert_f_descriptor` builds. -/
def certFConstraints (p : CertFProg) : List VmConstraint2 :=
  -- 1. conservation: one gate per node.
  ((List.range p.nNodes).map (fun i => egate (consBody p i)))
  -- 2. box lower f_e ≥ 0.
  ++ (((List.range p.m).map (fun e =>
        rangeGadget (p.fCol e) (fun j => p.rangeBitCol e j))).flatten)
  -- 3. box upper c_e − f_e ≥ 0: u_e == c_e − f_e (gate) + range gadget on u_e.
  ++ (((List.range p.m).map (fun e =>
        egate (.add (esub (EmittedExpr.var (p.uCol e)) (.const (p.cAt e))) (EmittedExpr.var (p.fCol e)))
        :: rangeGadget (p.uCol e) (fun j => p.rangeBitCol (p.m + e) j))).flatten)
  -- 4. slack sign s_e ≥ 0.
  ++ (((List.range p.m).map (fun e =>
        rangeGadget (p.sCol e) (fun j => p.rangeBitCol (2 * p.m + e) j))).flatten)
  -- 5. dual feas: d_e == π_head − π_tail + s_e − w_e (gate) + range gadget on d_e.
  ++ (((List.range p.m).map (fun e =>
        let dualExpr :=
          esub (.add (esub (EmittedExpr.var (p.piCol (p.headAt e))) (EmittedExpr.var (p.piCol (p.tailAt e))))
                     (EmittedExpr.var (p.sCol e)))
               (.const (p.wAt e))
        egate (esub (EmittedExpr.var (p.dCol e)) dualExpr)
        :: rangeGadget (p.dCol e) (fun j => p.rangeBitCol (3 * p.m + e) j))).flatten)
  -- 6. gap cᵀs − wᵀf ≤ ε: g == ε − (cᵀs − wᵀf) (gate) + range gadget on g.
  ++ ( egate ((List.range p.m).foldl
        (fun body e =>
          esub (.add body (.mul (.const (p.cAt e)) (EmittedExpr.var (p.sCol e))))
               (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
        (esub (EmittedExpr.var p.gCol) (.const p.eps)))
      :: rangeGadget p.gCol (fun j => p.rangeBitCol (4 * p.m) j))
  -- 7. objective obj == wᵀf (gate) + expose it as the public clearing volume.
  ++ [ egate ((List.range p.m).foldl
         (fun body e => esub body (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
         (EmittedExpr.var p.objCol))
     , .base (.piBinding .first p.objCol 0) ]

/-- **The Lean-authored Cert-F descriptor**, a total function of the public program: the exact
`EffectVmDescriptor2` that `cert_f_air.rs::cert_f_descriptor` hand-builds. -/
def certFDescriptorOf (p : CertFProg) : EffectVmDescriptor2 :=
  { name        := "cert-f"
  , traceWidth  := p.width
  , piCount     := 1
  , tables      := []
  , constraints := certFConstraints p
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — The worked 3-cycle instance (the twin of `cert_f_air.rs::ring3_cert`). -/

/-- The directed triangle `0→1→2→0`, unit weights + caps, `ε = 0` — the public program of
`Market.CertF.ringLP` and `cert_f_air.rs::ring3_cert`. -/
def ring3Prog : CertFProg :=
  { nNodes := 3, edges := [(0, 1), (1, 2), (2, 0)], w := [1, 1, 1], c := [1, 1, 1], eps := 0 }

/-- The Lean-authored Cert-F descriptor for the worked 3-cycle. -/
def certFDescriptor : EffectVmDescriptor2 := certFDescriptorOf ring3Prog

/-! ### Structural shape pins (byte-agreement with the Rust layout). -/

-- ring3: m = 3, n = 3 ⇒ width = bit_base(17) + (4·3+1)·28 = 17 + 364 = 381.
#guard certFDescriptor.name == "cert-f"
#guard certFDescriptor.piCount == 1
#guard certFDescriptor.traceWidth == 381
#guard ring3Prog.width == 381
-- constraint count: 3 (cons) + 3·29 (f) + 3·30 (u) + 3·29 (s) + 3·30 (d) + 30 (g) + 2 (obj) = 389.
#guard certFDescriptor.constraints.length == 389
#guard certFDescriptor.tables.length == 0
#guard certFDescriptor.hashSites.length == 0
#guard certFDescriptor.ranges.length == 0

/- Exact provenance pin: the committed Rust `include_str!` artifact is this
literal, and any emitter drift fails the Lean build. -/
#guard emitVmJson2 certFDescriptor == Market.CertFGolden.CERT_F_RING3_GOLDEN

/-! ## §4b — The first REAL market shape past the toy: a 3-asset / 4-order DrEX batch.

`fhegg-solver/src/bin/fhegg_clear.rs` maps a revealed DrEX batch to the trade-circulation LP:
nodes = assets, one edge per order `(wantAsset → offerAsset)`, `cap = offerAmount`,
`weight = priority`. This program is that LP for a concrete 4-order batch over assets
`{0, 1, 2}` — a 3-ring of trades plus one reverse pair (the smallest shape with BOTH a
multi-hop ring and a bilateral leg, i.e. a genuine multi-edge circulation, not a bare cycle):

  order 0: offers 5 of asset 1 for asset 0, priority 1  →  edge (0,1), c 5, w 1
  order 1: offers 5 of asset 2 for asset 1, priority 1  →  edge (1,2), c 5, w 1
  order 2: offers 5 of asset 0 for asset 2, priority 1  →  edge (2,0), c 5, w 1
  order 3: offers 3 of asset 0 for asset 1, priority 3  →  edge (1,0), c 3, w 3

at FIXED-POINT SCALE 100 (the `from_solution_json` scale — `w, c` are the solver's f64 program
×100, so a bridged real solve matches these constants exactly), with a PRESCRIPTIVE accuracy
budget `ε = 2000` (~1.1% of the optimum `wᵀf = 180000`): a REAL solver output with a nonzero
achieved gap ≤ ε registers and proves — the ε=0-only trap the ring-3 era had is structurally
gone. Unique optimum `f = (500, 200, 200, 300)`, dual `π = (200, 0, 100)`, tight gap 0. -/
def market4Prog : CertFProg :=
  { nNodes := 3
  , edges  := [(0, 1), (1, 2), (2, 0), (1, 0)]
  , w      := [100, 100, 100, 300]
  , c      := [500, 500, 500, 300]
  , eps    := 2000 }

/-- The Lean-authored Cert-F descriptor for the 3-asset/4-order market batch. -/
def certFMarket4Descriptor : EffectVmDescriptor2 := certFDescriptorOf market4Prog

-- market4: m = 4, n = 3 ⇒ bit_base = 21, width = 21 + (4·4+1)·28 = 21 + 476 = 497.
#guard certFMarket4Descriptor.name == "cert-f"
#guard certFMarket4Descriptor.piCount == 1
#guard certFMarket4Descriptor.traceWidth == 497
#guard market4Prog.width == 497
-- constraint count: 3 (cons) + 4·29 (f) + 4·30 (u) + 4·29 (s) + 4·30 (d) + 30 (g) + 2 (obj) = 507.
#guard certFMarket4Descriptor.constraints.length == 507
-- the no-wrap side condition the AIR's field-soundness rides: max node degree (3) · 2^28 < p.
#guard 3 * 2 ^ certFValueBits < 2013265921

/- Exact provenance pin: the committed `dregg-cert-f-market4-ir2.json` artifact is this literal,
and any emitter drift fails the Lean build. (No new proof needed: §6's emit-soundness is generic
over the program — this pin plus the registry entry IS the whole registration.) -/
#guard emitVmJson2 certFMarket4Descriptor == Market.CertFGolden.CERT_F_MARKET4_GOLDEN

/-! ## §5 — The RANGE-GADGET soundness lemma (the tooth `Market.CertF` deferred to "the standard
AIR range gadget"). This is the reusable core: a satisfied range gadget FORCES its target into
`[0, 2^bits)` over ℤ (under the deployed canonicality range-check invariant). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)

/-- The deployed range-check invariant: a cell is a canonical representative `0 ≤ x < p`. -/
def CanonCell (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

/-- Two canonical representatives congruent mod `p` are equal. -/
theorem eq_of_modEq_of_canon {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha : CanonCell a) (hb : CanonCell b) : a = b := by
  obtain ⟨ha0, ha1⟩ := ha; obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨k, hk⟩ := h.dvd; omega

/-- A canonical cell whose booleanity gate vanishes mod `p` is `0` or `1` over ℤ. -/
theorem binary_of_boolExpr {a : Assignment} {bc : Nat → Nat} {j : Nat}
    (h : (boolExpr bc j).eval a ≡ 0 [ZMOD 2013265921]) (hc : CanonCell (a (bc j))) :
    a (bc j) = 0 ∨ a (bc j) = 1 := by
  obtain ⟨h0, h1⟩ := hc
  have hev : (boolExpr bc j).eval a = a (bc j) * (a (bc j) - 1) := by
    simp only [boolExpr, esub, EmittedExpr.eval]; ring
  rw [hev] at h
  have hd : (2013265921 : ℤ) ∣ a (bc j) * (a (bc j) - 1) := Int.modEq_zero_iff_dvd.mp h
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-- `esub x y` evaluates to `x − y`. -/
theorem esub_eval (x y : EmittedExpr) (a : Assignment) :
    (esub x y).eval a = x.eval a - y.eval a := by
  simp [esub, EmittedExpr.eval]; ring

/-- The recompose fold evaluates to `col − Σⱼ 2ʲ·bⱼ` (over the bit list). -/
theorem recompose_foldl_eval (a : Assignment) (bc : Nat → Nat) :
    ∀ (l : List Nat) (e0 : EmittedExpr),
      (l.foldl (fun acc j => esub acc (.mul (.const ((2 : Int) ^ j)) (EmittedExpr.var (bc j)))) e0).eval a
        = e0.eval a - ((l.map (fun j => (2 : Int) ^ j * a (bc j))).sum) := by
  intro l
  induction l with
  | nil => intro e0; simp
  | cons x xs ih =>
      intro e0
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons, esub, EmittedExpr.eval]
      ring

theorem recomposeExpr_eval (col : Nat) (bc : Nat → Nat) (a : Assignment) :
    (recomposeExpr col bc).eval a
      = a col - (((List.range certFValueBits).map (fun j => (2 : Int) ^ j * a (bc j))).sum) := by
  have := recompose_foldl_eval a bc (List.range certFValueBits) (EmittedExpr.var col)
  simpa [recomposeExpr, EmittedExpr.eval] using this

/-- The weighted bit sum of `n` booleans lies in `[0, 2^n)`. -/
theorem bitsum_bounds (a : Assignment) (bc : Nat → Nat) :
    ∀ n, (∀ j < n, a (bc j) = 0 ∨ a (bc j) = 1) →
      0 ≤ ((List.range n).map (fun j => (2 : Int) ^ j * a (bc j))).sum
       ∧ ((List.range n).map (fun j => (2 : Int) ^ j * a (bc j))).sum < 2 ^ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ k ih =>
      intro hbit
      obtain ⟨ih0, ih1⟩ := ih (fun j hj => hbit j (by omega))
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have h2k : (0 : ℤ) ≤ 2 ^ k := by positivity
      have hpow : (2 : ℤ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      rcases hbit k (by omega) with h | h <;> rw [h] <;> constructor <;> nlinarith [ih0, ih1, h2k]

/-- **THE RANGE-GADGET SOUNDNESS TOOTH.** If every boolean gate and the recompose gate of a range
gadget vanish mod `p`, and the target + its bits are canonical, then the target lies in
`[0, 2^certFValueBits)` over ℤ. This is exactly the feasibility inequality `Market.CertF` named as
"riding the standard AIR range gadget" — now PROVED, not deferred. -/
theorem rangeGadget_forces_range (a : Assignment) (col : Nat) (bc : Nat → Nat)
    (hbool : ∀ j < certFValueBits, (boolExpr bc j).eval a ≡ 0 [ZMOD 2013265921])
    (hrec : (recomposeExpr col bc).eval a ≡ 0 [ZMOD 2013265921])
    (hcolCanon : CanonCell (a col))
    (hbitCanon : ∀ j < certFValueBits, CanonCell (a (bc j))) :
    0 ≤ a col ∧ a col < 2 ^ certFValueBits := by
  set S := ((List.range certFValueBits).map (fun j => (2 : Int) ^ j * a (bc j))).sum with hS
  have hbitBool : ∀ j < certFValueBits, (a (bc j) = 0 ∨ a (bc j) = 1) := fun j hj =>
    binary_of_boolExpr (hbool j hj) (hbitCanon j hj)
  -- the recompose gate pins `a col ≡ S`
  have hcolS : a col ≡ S [ZMOD 2013265921] := by
    have h : (a col - S) ≡ 0 [ZMOD 2013265921] := by rw [← recomposeExpr_eval]; exact hrec
    obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
    exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩
  -- `S ∈ [0, 2^bits)`
  obtain ⟨hS0, hS1⟩ := bitsum_bounds a bc certFValueBits hbitBool
  have hcol : a col = S :=
    eq_of_modEq_of_canon hcolS hcolCanon ⟨hS0, lt_trans hS1 (by norm_num [certFValueBits])⟩
  exact ⟨by rw [hcol]; exact hS0, by rw [hcol]; exact hS1⟩

/-! ## §6 — The EMIT-SOUNDNESS BRIDGE: a `Satisfied2`-satisfying Cert-F trace forces the certificate.

GENERIC over the public program `p : CertFProg` — NOT just `ring3Prog`. Registering a new
`(A, w, c, ε)` therefore needs only an EMITTED + byte-pinned artifact (`emitVmJson2
(certFDescriptorOf p)`), never a new proof: the soundness below covers every program the total
function `certFDescriptorOf` can produce.

The honest trace is `TRACE_HEIGHT = 8` identical rows of one assignment `a` (the twin of
`cert_f_air.rs::base_trace`, whose every row is the same certificate data). We extract, from
`Satisfied2`, that every gate body vanishes on `a`, then read the certificate soundness off `a`
using §5's range-gadget tooth for the feasibility families and the arithmetic gates for
conservation, the slack pins, the gap, and the objective. This is the theorem `cert_f_air.rs`
could only *test*. -/

/-- The all-present flat memory boundary is irrelevant here (the descriptor declares no mem/map ops),
so the boundary images are free — take the zero images over the empty address list. -/
def m0 : ℤ → ℤ := fun _ => 0
def f0 : ℤ → ℤ × Nat := fun _ => (0, 0)

/-- The honest constant trace: `TRACE_HEIGHT = 8` identical rows of `a`, empty auxiliary tables
(no mem/map ops), and the objective column published as the single public input. -/
def constTrace (p : CertFProg) (a : Assignment) : VmTrace :=
  { rows := List.replicate 8 a
  , pub  := fun _ => a p.objCol
  , tf   := fun _ => [] }

@[simp] theorem constTrace_rows_length (p : CertFProg) (a : Assignment) :
    (constTrace p a).rows.length = 8 := by
  simp [constTrace]

@[simp] theorem constTrace_loc0 (p : CertFProg) (a : Assignment) :
    (envAt (constTrace p a) 0).loc = a := by
  funext k; simp [envAt, constTrace, List.getD]

/-- **Extraction: a satisfied descriptor makes every one of its gate bodies vanish on `a`.** Read off
row 0 (which is NOT the last row, `1 ≠ 8`, so the `when_transition` gate fires). -/
theorem gate_vanishes {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    {body : EmittedExpr} (hmem : egate body ∈ certFConstraints p) :
    body.eval a ≡ 0 [ZMOD 2013265921] := by
  have hc : egate body ∈ (certFDescriptorOf p).constraints := hmem
  have h := hsat.rowConstraints 0 (by simp) (egate body) hc
  simpa [egate, VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

/-- **Extraction: the objective public-input binding.** On the first row (`isFirst = true`) the
`piBinding` forces the objective column to equal the published clearing volume. -/
theorem obj_pi_bound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    a p.objCol ≡ (constTrace p a).pub 0 [ZMOD 2013265921] := by
  have hmem : (VmConstraint2.base (.piBinding .first p.objCol 0)) ∈ (certFDescriptorOf p).constraints := by
    show _ ∈ certFConstraints p
    simp only [certFConstraints]
    apply List.mem_append_right; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  have h := hsat.rowConstraints 0 (by simp) _ hmem
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using h

/-! ### Membership helpers for the constraint families (byte-position bookkeeping). -/

/-- The conservation gate for node `i` is in the constraint list (the leftmost family). -/
theorem cons_mem (p : CertFProg) (i : Nat) (hi : i < p.nNodes) :
    egate (consBody p i) ∈ certFConstraints p := by
  have hin : egate (consBody p i)
      ∈ (List.range p.nNodes).map (fun i => egate (consBody p i)) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hin)))))

/-- The box-lower range gadget for edge `e` sits in the second family (`FLO`); every one of its
boolean gates and its recompose gate is in the constraint list. -/
theorem boxLower_gadget_mem (p : CertFProg) (e : Nat) (he : e < p.m) :
    ∀ c ∈ rangeGadget (p.fCol e) (fun j => p.rangeBitCol e j),
      c ∈ certFConstraints p := by
  intro c hc
  have hflat : c ∈ ((List.range p.m).map (fun e =>
      rangeGadget (p.fCol e) (fun j => p.rangeBitCol e j))).flatten := by
    apply List.mem_flatten.mpr
    exact ⟨_, List.mem_map.mpr ⟨e, List.mem_range.mpr he, rfl⟩, hc⟩
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hflat)))))

/-- Generic: membership in a `(map f l).flatten`. -/
theorem flatten_map_mem {α β : Type*} (f : α → List β) (l : List α) (x : β) (a : α)
    (ha : a ∈ l) (hx : x ∈ f a) : x ∈ (l.map f).flatten :=
  List.mem_flatten.mpr ⟨f a, List.mem_map.mpr ⟨a, ha, rfl⟩, hx⟩

/-- The slack range gadget for edge `e` (fourth family, `FSL`). -/
theorem slack_gadget_mem (p : CertFProg) (e : Nat) (he : e < p.m) :
    ∀ c ∈ rangeGadget (p.sCol e) (fun j => p.rangeBitCol (2 * p.m + e) j),
      c ∈ certFConstraints p := by
  intro c hc
  have hflat := flatten_map_mem
    (fun e => rangeGadget (p.sCol e) (fun j => p.rangeBitCol (2 * p.m + e) j))
    (List.range p.m) c e (List.mem_range.mpr he) hc
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ hflat)))

/-- The box-upper gate + range gadget for edge `e` (third family, `FUP`). -/
theorem boxUpper_cell_mem (p : CertFProg) (e : Nat) (he : e < p.m) :
    ∀ c ∈ (egate (.add (esub (EmittedExpr.var (p.uCol e)) (.const (p.cAt e)))
              (EmittedExpr.var (p.fCol e)))
          :: rangeGadget (p.uCol e) (fun j => p.rangeBitCol (p.m + e) j)),
      c ∈ certFConstraints p := by
  intro c hc
  have hflat := flatten_map_mem
    (fun e => egate (.add (esub (EmittedExpr.var (p.uCol e)) (.const (p.cAt e)))
                (EmittedExpr.var (p.fCol e)))
              :: rangeGadget (p.uCol e) (fun j => p.rangeBitCol (p.m + e) j))
    (List.range p.m) c e (List.mem_range.mpr he) hc
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ hflat))))

/-- The dual-feas gate + range gadget for edge `e` (fifth family, `FDU`). -/
theorem dual_cell_mem (p : CertFProg) (e : Nat) (he : e < p.m) :
    ∀ c ∈ (egate (esub (EmittedExpr.var (p.dCol e))
              (esub (.add (esub (EmittedExpr.var (p.piCol (p.headAt e)))
                              (EmittedExpr.var (p.piCol (p.tailAt e))))
                        (EmittedExpr.var (p.sCol e)))
                    (.const (p.wAt e))))
          :: rangeGadget (p.dCol e) (fun j => p.rangeBitCol (3 * p.m + e) j)),
      c ∈ certFConstraints p := by
  intro c hc
  have hflat := flatten_map_mem
    (fun e => egate (esub (EmittedExpr.var (p.dCol e))
                (esub (.add (esub (EmittedExpr.var (p.piCol (p.headAt e)))
                                (EmittedExpr.var (p.piCol (p.tailAt e))))
                          (EmittedExpr.var (p.sCol e)))
                      (.const (p.wAt e))))
              :: rangeGadget (p.dCol e) (fun j => p.rangeBitCol (3 * p.m + e) j))
    (List.range p.m) c e (List.mem_range.mpr he) hc
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hflat))

/-- The gap gate + range gadget (sixth family, `GAP`). -/
theorem gap_mem (p : CertFProg) : ∀ c ∈
    (egate ((List.range p.m).foldl
        (fun body e =>
          esub (.add body (.mul (.const (p.cAt e)) (EmittedExpr.var (p.sCol e))))
               (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
        (esub (EmittedExpr.var p.gCol) (.const p.eps)))
      :: rangeGadget p.gCol (fun j => p.rangeBitCol (4 * p.m) j)),
      c ∈ certFConstraints p := by
  intro c hc
  simp only [certFConstraints]
  exact List.mem_append_left _ (List.mem_append_right _ hc)

/-- The objective gate `obj == wᵀf` (seventh family, head of the final chunk). -/
theorem obj_gate_mem (p : CertFProg) :
    egate ((List.range p.m).foldl
        (fun body e => esub body (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
        (EmittedExpr.var p.objCol)) ∈ certFConstraints p := by
  simp only [certFConstraints]
  exact List.mem_append_right _ List.mem_cons_self

/-! ### The per-gadget gate membership within one `rangeGadget`. -/

theorem boolGate_in_gadget (col : Nat) (bc : Nat → Nat) (j : Nat) (hj : j < certFValueBits) :
    egate (boolExpr bc j) ∈ rangeGadget col bc :=
  List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

theorem recGate_in_gadget (col : Nat) (bc : Nat → Nat) :
    egate (recomposeExpr col bc) ∈ rangeGadget col bc :=
  List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-! ### §6.1 — The emit-soundness theorems: a satisfied Cert-F trace forces the certificate.
All GENERIC over the public program `p : CertFProg`. -/

/-- **CONSERVATION SOUNDNESS.** A `Satisfied2`-satisfying trace makes every node's conservation
residual `Σ_{head=i} f_e − Σ_{tail=i} f_e` vanish mod `p` — `A f = 0` over the field. -/
theorem certFDescriptor_conservation_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (i : Nat) (hi : i < p.nNodes) :
    (consBody p i).eval a ≡ 0 [ZMOD 2013265921] :=
  gate_vanishes hsat (cons_mem p i hi)

/-- **BOX-LOWER SOUNDNESS `f_e ≥ 0`.** The box-lower range gadget forces every flow into
`[0, 2^certFValueBits)` — the primal box lower bound (via §5's tooth). -/
theorem certFDescriptor_box_lower_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (e : Nat) (he : e < p.m) :
    0 ≤ a (p.fCol e) ∧ a (p.fCol e) < 2 ^ certFValueBits := by
  refine rangeGadget_forces_range a (p.fCol e) (fun j => p.rangeBitCol e j)
    (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat (boxLower_gadget_mem p e he _ (boolGate_in_gadget _ _ j hj))
  · exact gate_vanishes hsat (boxLower_gadget_mem p e he _ (recGate_in_gadget _ _))

/-- **SLACK-SIGN SOUNDNESS `s_e ≥ 0`.** The slack range gadget forces every dual slack into
`[0, 2^certFValueBits)` — the dual sign constraint (via §5's tooth). -/
theorem certFDescriptor_slack_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (e : Nat) (he : e < p.m) :
    0 ≤ a (p.sCol e) ∧ a (p.sCol e) < 2 ^ certFValueBits := by
  refine rangeGadget_forces_range a (p.sCol e)
    (fun j => p.rangeBitCol (2 * p.m + e) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat (slack_gadget_mem p e he _ (boolGate_in_gadget _ _ j hj))
  · exact gate_vanishes hsat (slack_gadget_mem p e he _ (recGate_in_gadget _ _))

/-- **GAP-SLACK RANGE `g ≥ 0`.** The gap slack `g` is forced into `[0, 2^certFValueBits)` by its
range gadget. Combined with `certFDescriptor_gap_gate_sound` (the pin `g ≡ ε − (cᵀs − wᵀf)`),
this is the ε-optimality clause over the field. -/
theorem certFDescriptor_gap_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    0 ≤ a p.gCol ∧ a p.gCol < 2 ^ certFValueBits := by
  refine rangeGadget_forces_range a p.gCol
    (fun j => p.rangeBitCol (4 * p.m) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _)
  · exact gate_vanishes hsat (gap_mem p _ (List.mem_cons_of_mem _ (boolGate_in_gadget _ _ j hj)))
  · exact gate_vanishes hsat (gap_mem p _ (List.mem_cons_of_mem _ (recGate_in_gadget _ _)))

/-- **BOX-UPPER SOUNDNESS `f_e ≤ c_e`.** The box-upper slack `u_e` is forced `≥ 0` by its range
gadget, and its gate pins `u_e == c_e − f_e` — so `c_e − f_e ≥ 0` over the field, i.e. the primal
box upper bound. -/
theorem certFDescriptor_box_upper_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (e : Nat) (he : e < p.m) :
    (0 ≤ a (p.uCol e) ∧ a (p.uCol e) < 2 ^ certFValueBits)
    ∧ (a (p.uCol e) - p.cAt e + a (p.fCol e)) ≡ 0 [ZMOD 2013265921] := by
  refine ⟨rangeGadget_forces_range a (p.uCol e)
      (fun j => p.rangeBitCol (p.m + e) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _), ?_⟩
  · exact gate_vanishes hsat (boxUpper_cell_mem p e he _ (List.mem_cons_of_mem _ (boolGate_in_gadget _ _ j hj)))
  · exact gate_vanishes hsat (boxUpper_cell_mem p e he _ (List.mem_cons_of_mem _ (recGate_in_gadget _ _)))
  · have h := gate_vanishes hsat (boxUpper_cell_mem p e he _ (List.mem_cons_self))
    have : ((esub (EmittedExpr.var (p.uCol e)) (.const (p.cAt e))).add
              (EmittedExpr.var (p.fCol e))).eval a
            = a (p.uCol e) - p.cAt e + a (p.fCol e) := by
      simp only [esub, EmittedExpr.eval]; ring
    rw [this] at h; exact h

/-- **DUAL-FEASIBILITY SOUNDNESS `π_head − π_tail + s_e − w_e ≥ 0`.** The dual slack `d_e` is forced
`≥ 0` by its range gadget, and its gate pins `d_e == π_head − π_tail + s_e − w_e` — so `Aᵀπ + s ≥ w`
over the field. -/
theorem certFDescriptor_dual_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a))
    (e : Nat) (he : e < p.m) :
    (0 ≤ a (p.dCol e) ∧ a (p.dCol e) < 2 ^ certFValueBits)
    ∧ (a (p.dCol e)
        - (a (p.piCol (p.headAt e)) - a (p.piCol (p.tailAt e))
           + a (p.sCol e) - p.wAt e)) ≡ 0 [ZMOD 2013265921] := by
  refine ⟨rangeGadget_forces_range a (p.dCol e)
      (fun j => p.rangeBitCol (3 * p.m + e) j) (fun j hj => ?_) ?_ (hcanon _) (fun j _ => hcanon _), ?_⟩
  · exact gate_vanishes hsat (dual_cell_mem p e he _ (List.mem_cons_of_mem _ (boolGate_in_gadget _ _ j hj)))
  · exact gate_vanishes hsat (dual_cell_mem p e he _ (List.mem_cons_of_mem _ (recGate_in_gadget _ _)))
  · have h := gate_vanishes hsat (dual_cell_mem p e he _ (List.mem_cons_self))
    have : (esub (EmittedExpr.var (p.dCol e))
              (esub (.add (esub (EmittedExpr.var (p.piCol (p.headAt e)))
                              (EmittedExpr.var (p.piCol (p.tailAt e))))
                        (EmittedExpr.var (p.sCol e)))
                    (.const (p.wAt e)))).eval a
            = a (p.dCol e)
              - (a (p.piCol (p.headAt e)) - a (p.piCol (p.tailAt e))
                 + a (p.sCol e) - p.wAt e) := by
      simp only [esub, EmittedExpr.eval]; ring
    rw [this] at h; exact h

/-! ### §6.2 — The gap and objective GATE pins (previously only range-checked, never extracted:
without `g ≡ ε − (cᵀs − wᵀf)` the bundle's `g ≥ 0` said nothing about ε). -/

/-- `cᵀs − wᵀf` read off the trace columns — the duality gap over the field. -/
def gapOf (p : CertFProg) (a : Assignment) : ℤ :=
  ((List.range p.m).map (fun e => p.cAt e * a (p.sCol e) - p.wAt e * a (p.fCol e))).sum

/-- `wᵀf` read off the trace columns — the cleared volume over the field. -/
def objOf (p : CertFProg) (a : Assignment) : ℤ :=
  ((List.range p.m).map (fun e => p.wAt e * a (p.fCol e))).sum

/-- The gap-gate fold evaluates to `e0 + Σ_e (c_e·s_e − w_e·f_e)`. -/
theorem gap_foldl_eval (p : CertFProg) (a : Assignment) :
    ∀ (l : List Nat) (e0 : EmittedExpr),
      (l.foldl (fun body e =>
          esub (.add body (.mul (.const (p.cAt e)) (EmittedExpr.var (p.sCol e))))
               (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e)))) e0).eval a
        = e0.eval a
          + ((l.map (fun e => p.cAt e * a (p.sCol e) - p.wAt e * a (p.fCol e))).sum) := by
  intro l
  induction l with
  | nil => intro e0; simp
  | cons x xs ih =>
      intro e0
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons, esub, EmittedExpr.eval]
      ring

/-- The objective-gate fold evaluates to `e0 − Σ_e w_e·f_e`. -/
theorem obj_foldl_eval (p : CertFProg) (a : Assignment) :
    ∀ (l : List Nat) (e0 : EmittedExpr),
      (l.foldl (fun body e =>
          esub body (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e)))) e0).eval a
        = e0.eval a - ((l.map (fun e => p.wAt e * a (p.fCol e))).sum) := by
  intro l
  induction l with
  | nil => intro e0; simp
  | cons x xs ih =>
      intro e0
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons, esub, EmittedExpr.eval]
      ring

/-- **GAP-GATE SOUNDNESS.** The gap gate pins the gap slack: `g ≡ ε − (cᵀs − wᵀf)` mod `p`.
Together with `certFDescriptor_gap_sound` (`g ≥ 0`), this is `cᵀs − wᵀf ≤ ε` over the field —
the ε-optimality clause, the whole point of the certificate
(`Market.certifies_epsilon_optimal`). -/
theorem certFDescriptor_gap_gate_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    a p.gCol ≡ p.eps - gapOf p a [ZMOD 2013265921] := by
  have h := gate_vanishes hsat (gap_mem p _ List.mem_cons_self)
  have hev : ((List.range p.m).foldl
      (fun body e =>
        esub (.add body (.mul (.const (p.cAt e)) (EmittedExpr.var (p.sCol e))))
             (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
      (esub (EmittedExpr.var p.gCol) (.const p.eps))).eval a
      = a p.gCol - p.eps + gapOf p a := by
    rw [gap_foldl_eval]
    simp only [esub, EmittedExpr.eval, gapOf]
    ring
  rw [hev] at h
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
  exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩

/-- **OBJECTIVE-GATE SOUNDNESS.** The objective gate pins the published column: `obj ≡ wᵀf` mod `p`
— with `obj_pi_bound`, the world-visible public input IS the cleared volume of the hidden flow. -/
theorem certFDescriptor_obj_gate_sound {hash : List ℤ → ℤ} {p : CertFProg} {a : Assignment}
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    a p.objCol ≡ objOf p a [ZMOD 2013265921] := by
  have h := gate_vanishes hsat (obj_gate_mem p)
  have hev : ((List.range p.m).foldl
      (fun body e =>
        esub body (.mul (.const (p.wAt e)) (EmittedExpr.var (p.fCol e))))
      (EmittedExpr.var p.objCol)).eval a
      = a p.objCol - objOf p a := by
    rw [obj_foldl_eval]
    simp only [EmittedExpr.eval, objOf]
  rw [hev] at h
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
  exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩

/-- **THE EMIT-SOUNDNESS BRIDGE (the theorem `cert_f_air.rs` could only TEST), GENERIC over the
public program.** A `Satisfied2`-satisfying Cert-F trace (over a canonical assignment — the
deployed range-check invariant) forces the FULL Cert-F certificate over the BabyBear field, for
ANY `p : CertFProg`, ALL FIVE families PLUS the gate pins:

  * `A f = 0` (conservation);
  * `f ≥ 0` (box lower) and `u ≥ 0` with `u ≡ c − f` (box upper);
  * `s ≥ 0` (slack sign);
  * `d ≥ 0` with `d ≡ Aᵀπ + s − w` (dual feasibility);
  * `g ≥ 0` with `g ≡ ε − (cᵀs − wᵀf)` (the ε-optimality gap);
  * `obj ≡ wᵀf` (the published cleared volume is the real objective).

This is exactly the certificate `Market.Certified` decides — the linear check `Market.CertF` proves
sound (`certifies_epsilon_optimal`), now realized at the DEPLOYED IR-v2 descriptor level for every
registrable program: a new `(A, w, c, ε)` needs only emission + byte-pinning, no new proof. -/
theorem certFDescriptor_emit_sound {hash : List ℤ → ℤ} (p : CertFProg) {a : Assignment}
    (hcanon : ∀ col, CanonCell (a col))
    (hsat : Satisfied2 hash (certFDescriptorOf p) m0 f0 [] (constTrace p a)) :
    (∀ i < p.nNodes, (consBody p i).eval a ≡ 0 [ZMOD 2013265921])
    ∧ (∀ e < p.m, 0 ≤ a (p.fCol e))
    ∧ (∀ e < p.m, 0 ≤ a (p.uCol e)
         ∧ (a (p.uCol e) - p.cAt e + a (p.fCol e)) ≡ 0 [ZMOD 2013265921])
    ∧ (∀ e < p.m, 0 ≤ a (p.sCol e))
    ∧ (∀ e < p.m, 0 ≤ a (p.dCol e)
         ∧ (a (p.dCol e)
             - (a (p.piCol (p.headAt e)) - a (p.piCol (p.tailAt e))
                + a (p.sCol e) - p.wAt e)) ≡ 0 [ZMOD 2013265921])
    ∧ (0 ≤ a p.gCol ∧ a p.gCol ≡ p.eps - gapOf p a [ZMOD 2013265921])
    ∧ a p.objCol ≡ objOf p a [ZMOD 2013265921] :=
  ⟨fun i hi => certFDescriptor_conservation_sound hsat i hi
  , fun e he => (certFDescriptor_box_lower_sound hcanon hsat e he).1
  , fun e he => ⟨(certFDescriptor_box_upper_sound hcanon hsat e he).1.1
               , (certFDescriptor_box_upper_sound hcanon hsat e he).2⟩
  , fun e he => (certFDescriptor_slack_sound hcanon hsat e he).1
  , fun e he => ⟨(certFDescriptor_dual_sound hcanon hsat e he).1.1
               , (certFDescriptor_dual_sound hcanon hsat e he).2⟩
  , ⟨(certFDescriptor_gap_sound hcanon hsat).1, certFDescriptor_gap_gate_sound hsat⟩
  , certFDescriptor_obj_gate_sound hsat⟩

/-! ### Axiom hygiene — the emit-soundness keystones pinned kernel-clean. -/

#assert_all_clean [Market.CertFDescriptor.rangeGadget_forces_range,
  Market.CertFDescriptor.certFDescriptor_conservation_sound,
  Market.CertFDescriptor.certFDescriptor_box_lower_sound,
  Market.CertFDescriptor.certFDescriptor_box_upper_sound,
  Market.CertFDescriptor.certFDescriptor_slack_sound,
  Market.CertFDescriptor.certFDescriptor_dual_sound,
  Market.CertFDescriptor.certFDescriptor_gap_sound,
  Market.CertFDescriptor.certFDescriptor_gap_gate_sound,
  Market.CertFDescriptor.certFDescriptor_obj_gate_sound,
  Market.CertFDescriptor.certFDescriptor_emit_sound]

end Market.CertFDescriptor

-- Stronger than pinning only the eight public keystones above: audit every theorem in the emitted
-- descriptor namespace, including all range/membership plumbing used to derive them.
#assert_namespace_axioms Market.CertFDescriptor
