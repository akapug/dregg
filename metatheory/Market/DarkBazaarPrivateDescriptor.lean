/-
# Market.DarkBazaarPrivateDescriptor

The first fixed-shape Dark Bazaar proof family whose order values are private
witness columns rather than public Cert-F coefficients.

Family: exactly four committed slots (zero-quantity padding is canonical at the
Rust boundary), four price buckets, quantities in `[0,15]`, and a fixed rule id.
Public inputs are only `(session, rule, orderRoot[0..8), pStar, vStar)`.  Each private
order is an eight-way one-hot `(bid/ask × limit 0..3)` plus a four-bit quantity.
The four seven-bit order codes are injectively packed into one 28-bit felt.  A
single domain-separated full-arity Poseidon2 permutation absorbs
`(session,rule,packedBook)`, eight canonical blind felts, and four explicit zero
framing lanes, exposing all eight output lanes (~248 bits, ~124-bit collision
work).  There is no narrow intermediate carrier.

The AIR recomputes all four demand/supply buckets, each `min(D,S)`, the maximum
volume, and the LOWEST maximizing price.  No order value occurs in descriptor
constants or public inputs.  Rust only fills this Lean-authored layout and proves
the emitted descriptor.
-/
import Market.FhEggClearing
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Tactics

namespace Market.DarkBazaarPrivateDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
    ChipTableSoundN chipLookupTupleN chip_lookup_sound_N envAt emitVmJson2)

set_option autoImplicit false

/-! ## 1. Exact semantic certificate checker. -/

def ORDER_COUNT : Nat := 4
def PRICE_COUNT : Nat := 4
def QTY_BITS : Nat := 4
def DIFF_BITS : Nat := 6

def DIGEST_WIDTH : Nat := 8

/-- Poseidon input domain separator for this exact commitment encoding. -/
def ROOT_DOMAIN_TAG : Int := 1145194322

def BABYBEAR_MODULUS : Int := 2013265921

/-- Stable public rule/domain separator for `N=4,K=4,qty<16,lowest-price-tie`. -/
def RULE_ID : Int := 1430520836

/-- Private order code: `kind<4` is a bid at `kind`; `kind>=4` is an ask at `kind-4`. -/
structure PrivateOrder where
  kind : Fin 8
  qty : Fin 16
  deriving DecidableEq, Repr

structure PrivateWitness where
  orders : Fin 4 → PrivateOrder
  blinding : Fin 8 → Int

structure PublicStatement where
  session : Int
  rule : Int
  orderRoot : Fin 8 → Int
  pStar : Nat
  vStar : Int
  deriving DecidableEq, Repr

def PrivateOrder.toLimitOrder (o : PrivateOrder) : LimitOrder where
  side := if o.kind.val < 4 then .bid else .ask
  qty := o.qty.val
  limit := o.kind.val % 4

def privateBook (w : PrivateWitness) : OrderBook :=
  List.ofFn (fun i : Fin 4 => (w.orders i).toLimitOrder)

/-- Host integers for blind limbs are canonical field representatives.  This
rules out the trivial `b` versus `b + p` alias before the cryptographic binding
assumption is even discussed. -/
def CanonicalBlinding (w : PrivateWitness) : Prop :=
  ∀ i, 0 ≤ w.blinding i ∧ w.blinding i < BABYBEAR_MODULUS

def canonicalBlindingCheck (w : PrivateWitness) : Bool :=
  (List.ofFn w.blinding).all fun z => decide (0 ≤ z ∧ z < BABYBEAR_MODULUS)

theorem canonicalBlindingCheck_iff (w : PrivateWitness) :
    canonicalBlindingCheck w = true ↔ CanonicalBlinding w := by
  simp [canonicalBlindingCheck, CanonicalBlinding]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩

/-- Seven-bit injective order code: `kind + 8*qty ∈ [0,127]`. -/
def orderCode (o : PrivateOrder) : Int := o.kind.val + 8 * o.qty.val

theorem orderCode_injective : Function.Injective orderCode := by
  intro left right h
  have hkind : left.kind.val = right.kind.val := by
    simp only [orderCode] at h
    have hl := left.kind.isLt
    have hr := right.kind.isLt
    omega
  have hqty : left.qty.val = right.qty.val := by
    simp only [orderCode] at h
    omega
  cases left with
  | mk lk lq =>
    cases right with
    | mk rk rq =>
      cases Fin.ext hkind
      cases Fin.ext hqty
      rfl

/-- Four base-128 digits, hence `< 128^4 = 2^28 < BabyBear`. -/
def packedBook (w : PrivateWitness) : Int :=
  (List.ofFn (fun i : Fin 4 => (128 : Int) ^ i.val * orderCode (w.orders i))).sum

/-- The committed 28-bit pack loses no fixed-slot order information. -/
theorem packedBook_injective_on_orders {left right : PrivateWitness}
    (hpack : packedBook left = packedBook right) : left.orders = right.orders := by
  have codeBounds (w : PrivateWitness) (i : Fin 4) :
      0 ≤ orderCode (w.orders i) ∧ orderCode (w.orders i) < 128 := by
    simp only [orderCode]
    have hk := (w.orders i).kind.isLt
    have hq := (w.orders i).qty.isLt
    omega
  have hp :
      orderCode (left.orders 0) + 128 * orderCode (left.orders 1) +
          16384 * orderCode (left.orders 2) + 2097152 * orderCode (left.orders 3) =
        orderCode (right.orders 0) + 128 * orderCode (right.orders 1) +
          16384 * orderCode (right.orders 2) + 2097152 * orderCode (right.orders 3) := by
    simpa [packedBook, List.ofFn_succ, add_assoc] using hpack
  have h0 : orderCode (left.orders 0) = orderCode (right.orders 0) := by
    have l0 := codeBounds left 0; have l1 := codeBounds left 1
    have l2 := codeBounds left 2; have l3 := codeBounds left 3
    have r0 := codeBounds right 0; have r1 := codeBounds right 1
    have r2 := codeBounds right 2; have r3 := codeBounds right 3
    omega
  have h1 : orderCode (left.orders 1) = orderCode (right.orders 1) := by
    have l1 := codeBounds left 1; have l2 := codeBounds left 2; have l3 := codeBounds left 3
    have r1 := codeBounds right 1; have r2 := codeBounds right 2; have r3 := codeBounds right 3
    omega
  have h2 : orderCode (left.orders 2) = orderCode (right.orders 2) := by
    have l2 := codeBounds left 2; have l3 := codeBounds left 3
    have r2 := codeBounds right 2; have r3 := codeBounds right 3
    omega
  have h3 : orderCode (left.orders 3) = orderCode (right.orders 3) := by
    omega
  funext i
  fin_cases i
  · exact orderCode_injective h0
  · exact orderCode_injective h1
  · exact orderCode_injective h2
  · exact orderCode_injective h3

/-- Canonical source commitment input.  Twelve meaningful inputs plus four
explicit zero framing lanes use the chip's full arity-16 seed mode, so every
blind limb is absorbed and no scalar intermediate can launder the width. -/
def rootPreimage (session : Int) (w : PrivateWitness) : List Int :=
  [ROOT_DOMAIN_TAG, session, RULE_ID, packedBook w] ++ List.ofFn w.blinding ++ [0, 0, 0, 0]

/-- Canonical eight-felt source commitment. -/
def orderRoot (hash8 : List Int → Fin 8 → Int) (session : Int) (w : PrivateWitness) : Fin 8 → Int :=
  hash8 (rootPreimage session w)

/-- The exact bad event behind the external commitment-binding claim: two distinct
packed source openings for one session produce the same root.  We deliberately do
NOT assert that a field-valued Poseidon map is injective (it cannot be globally
injective at finite cardinality).  Protocol binding is the computational
assumption that no feasible adversary finds a value of this predicate. -/
def RootCollision (hash8 : List Int → Fin 8 → Int) (session : Int)
    (left right : PrivateWitness) : Prop :=
  (packedBook left ≠ packedBook right ∨ left.blinding ≠ right.blinding) ∧
  orderRoot hash8 session left = orderRoot hash8 session right

/-- The exact private-order statement checked by the family. -/
def Accepts (hash8 : List Int → Fin 8 → Int) (pub : PublicStatement) (w : PrivateWitness) : Prop :=
  CanonicalBlinding w ∧
  pub.rule = RULE_ID ∧
  pub.orderRoot = orderRoot hash8 pub.session w ∧
  pub.pStar = crossing (privateBook w) PRICE_COUNT ∧
  pub.vStar = clearedVolume (privateBook w) PRICE_COUNT

/-- Executable, exact certificate checker authored in Lean. -/
def check (hash8 : List Int → Fin 8 → Int) (pub : PublicStatement) (w : PrivateWitness) : Bool :=
  canonicalBlindingCheck w &&
  (pub.rule == RULE_ID) &&
  (pub.orderRoot == orderRoot hash8 pub.session w) &&
  (pub.pStar == crossing (privateBook w) PRICE_COUNT) &&
  (pub.vStar == clearedVolume (privateBook w) PRICE_COUNT)

theorem check_iff (hash8 : List Int → Fin 8 → Int) (pub : PublicStatement) (w : PrivateWitness) :
    check hash8 pub w = true ↔ Accepts hash8 pub w := by
  simp [check, Accepts, canonicalBlindingCheck_iff, and_assoc]

/-- Earlier buckets are strictly below `argmaxUpto`: this is the formal
lowest-price tie tooth missing from the older output-only join. -/
theorem argmaxUpto_strict_before (bk : OrderBook) :
    ∀ n q, q < argmaxUpto bk n → execVol bk q < execVol bk (argmaxUpto bk n) := by
  intro n
  induction n with
  | zero =>
      intro q hq
      simp [argmaxUpto] at hq
  | succ n ih =>
      intro q hq
      by_cases h : execVol bk (argmaxUpto bk n) < execVol bk (n + 1)
      · have harg : argmaxUpto bk (n + 1) = n + 1 := by
          simp [argmaxUpto, h]
        rw [harg] at hq ⊢
        exact lt_of_le_of_lt (argmaxUpto_max bk n q (by omega)) h
      · have harg : argmaxUpto bk (n + 1) = argmaxUpto bk n := by
          simp [argmaxUpto, h]
        rw [harg] at hq ⊢
        exact ih q hq

theorem crossing_strict_before (bk : OrderBook) {q : Nat}
    (hq : q < crossing bk PRICE_COUNT) :
    execVol bk q < clearedVolume bk PRICE_COUNT := by
  exact argmaxUpto_strict_before bk (PRICE_COUNT - 1) q hq

/-- **Checker soundness.** Acceptance binds the opened private orders to the
public root and makes `(pStar,vStar)` the exact deterministic volume argmax,
including strict dominance over every earlier bucket. -/
theorem check_sound {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement} {w : PrivateWitness}
    (h : check hash8 pub w = true) :
    CanonicalBlinding w ∧
    pub.rule = RULE_ID ∧
    pub.orderRoot = orderRoot hash8 pub.session w ∧
    pub.pStar = crossing (privateBook w) PRICE_COUNT ∧
    pub.vStar = clearedVolume (privateBook w) PRICE_COUNT ∧
    (∀ q < PRICE_COUNT, execVol (privateBook w) q ≤ pub.vStar) ∧
    (∀ q < pub.pStar, execVol (privateBook w) q < pub.vStar) := by
  have ha : Accepts hash8 pub w := (check_iff hash8 pub w).mp h
  rcases ha with ⟨hcanon, hrule, hroot, hp, hV⟩
  refine ⟨hcanon, hrule, hroot, hp, hV, ?_, ?_⟩
  · intro q hq
    rw [hV]
    exact clearedVolume_optimal (privateBook w) PRICE_COUNT hq
  · intro q hq
    rw [hp] at hq
    rw [hV]
    exact crossing_strict_before (privateBook w) hq

/-- Two accepted, distinct source openings for the same public statement reduce
directly to a commitment collision.  This is the formal boundary: exact checker
soundness is unconditional; uniqueness of the opening is computational Poseidon
binding and is never smuggled in as a false field-level injectivity theorem. -/
theorem two_distinct_openings_yield_root_collision
    {hash8 : List Int → Fin 8 → Int} {pub : PublicStatement} {left right : PrivateWitness}
    (hl : check hash8 pub left = true) (hr : check hash8 pub right = true)
    (hdiff : packedBook left ≠ packedBook right ∨ left.blinding ≠ right.blinding) :
    RootCollision hash8 pub.session left right := by
  have al := (check_iff hash8 pub left).mp hl
  have ar := (check_iff hash8 pub right).mp hr
  exact ⟨hdiff, al.2.2.1.symm.trans ar.2.2.1⟩

/-! A non-vacuous executable workbook and tamper teeth. -/

def fixtureOrder (i : Fin 4) : PrivateOrder :=
  match i.val with
  | 0 => ⟨⟨2, by omega⟩, ⟨10, by omega⟩⟩ -- bid 10 @ 2
  | 1 => ⟨⟨1, by omega⟩, ⟨6, by omega⟩⟩  -- bid 6 @ 1
  | 2 => ⟨⟨4, by omega⟩, ⟨5, by omega⟩⟩  -- ask 5 @ 0
  | _ => ⟨⟨5, by omega⟩, ⟨8, by omega⟩⟩  -- ask 8 @ 1

def fixtureWitness : PrivateWitness := ⟨fixtureOrder, fun i => 777 + i.val⟩
def toyHash8 (xs : List Int) (lane : Fin 8) : Int := xs.sum + 17 + lane.val
def fixturePublic : PublicStatement where
  session := 99
  rule := RULE_ID
  orderRoot := orderRoot toyHash8 99 fixtureWitness
  pStar := 1
  vStar := 13

def tamperedOrderWitness : PrivateWitness where
  orders := fun i => if i = 0 then ⟨⟨2, by omega⟩, ⟨11, by omega⟩⟩ else fixtureOrder i
  blinding := fixtureWitness.blinding

def noncanonicalBlindWitness : PrivateWitness where
  orders := fixtureWitness.orders
  blinding := fun i => if i = 0 then BABYBEAR_MODULUS else fixtureWitness.blinding i

#guard check toyHash8 fixturePublic fixtureWitness
#guard !check toyHash8 { fixturePublic with orderRoot := fun i => fixturePublic.orderRoot i + 1 }
  fixtureWitness
#guard !check toyHash8 { fixturePublic with pStar := 2 } fixtureWitness
#guard !check toyHash8 { fixturePublic with vStar := 12 } fixtureWitness
#guard !check toyHash8 fixturePublic tamperedOrderWitness
#guard !check toyHash8 fixturePublic noncanonicalBlindWitness

/-! ## 2. Lean-authored fixed AIR descriptor. -/

/- Column layout.  Public: session/rule 0..1, root8 2..9, p*/V* 10..11.
Private blind8: 12..19. Private order rows: 21..76. -/
def SESSION : Nat := 0
def RULE : Nat := 1
def ROOT_BASE : Nat := 2
def PSTAR : Nat := 10
def VSTAR : Nat := 11
def BLINDING_BASE : Nat := 12
def PACKED_BOOK : Nat := 20

def ROOT (lane : Nat) : Nat := ROOT_BASE + lane
def BLINDING (lane : Nat) : Nat := BLINDING_BASE + lane

def ORDER_BASE : Nat := 21
def ORDER_STRIDE : Nat := 14
def KIND (i t : Nat) : Nat := ORDER_BASE + ORDER_STRIDE * i + t
def QTY (i : Nat) : Nat := ORDER_BASE + ORDER_STRIDE * i + 8
def QTY_BIT (i b : Nat) : Nat := ORDER_BASE + ORDER_STRIDE * i + 9 + b
def ORDER_PACK (i : Nat) : Nat := ORDER_BASE + ORDER_STRIDE * i + 13

def DEMAND_BASE : Nat := 77
def SUPPLY_BASE : Nat := 81
def VOLUME_BASE : Nat := 85
def MIN_CHOOSE_BASE : Nat := 89
def MIN_DIFF_BASE : Nat := 93
def MIN_DIFF_BITS_BASE : Nat := 97
def SELECT_BASE : Nat := 121
def MAX_DIFF_BASE : Nat := 125
def MAX_DIFF_BITS_BASE : Nat := 129
def LOW_SLACK_BASE : Nat := 153
def LOW_SLACK_BITS_BASE : Nat := 157
def TRACE_WIDTH : Nat := 181

def DEMAND (p : Nat) : Nat := DEMAND_BASE + p
def SUPPLY (p : Nat) : Nat := SUPPLY_BASE + p
def VOLUME (p : Nat) : Nat := VOLUME_BASE + p
def MIN_CHOOSE (p : Nat) : Nat := MIN_CHOOSE_BASE + p
def MIN_DIFF (p : Nat) : Nat := MIN_DIFF_BASE + p
def MIN_DIFF_BIT (p b : Nat) : Nat := MIN_DIFF_BITS_BASE + DIFF_BITS * p + b
def SELECT (p : Nat) : Nat := SELECT_BASE + p
def MAX_DIFF (p : Nat) : Nat := MAX_DIFF_BASE + p
def MAX_DIFF_BIT (p b : Nat) : Nat := MAX_DIFF_BITS_BASE + DIFF_BITS * p + b
def LOW_SLACK (p : Nat) : Nat := LOW_SLACK_BASE + p
def LOW_SLACK_BIT (p b : Nat) : Nat := LOW_SLACK_BITS_BASE + DIFF_BITS * p + b

def v (col : Nat) : EmittedExpr := .var col
def c (z : Int) : EmittedExpr := .const z
def add (x y : EmittedExpr) : EmittedExpr := .add x y
def mul (x y : EmittedExpr) : EmittedExpr := .mul x y
def neg (x : EmittedExpr) : EmittedExpr := mul (c (-1)) x
def sub (x y : EmittedExpr) : EmittedExpr := add x (neg y)
def sumE (xs : List EmittedExpr) : EmittedExpr := xs.foldr add (c 0)
def weighted (k : Int) (x : EmittedExpr) : EmittedExpr := mul (c k) x

def binaryBody (col : Nat) : EmittedExpr := mul (v col) (sub (v col) (c 1))

def recompose (col : Nat) (bit : Nat → Nat) (bits : Nat) : EmittedExpr :=
  sub (sumE ((List.range bits).map (fun b => weighted ((2 : Int) ^ b) (v (bit b))))) (v col)

def kindValue (i : Nat) : EmittedExpr :=
  sumE ((List.range 8).map (fun (t : Nat) => weighted (t : Int) (v (KIND i t))))

def bidActive (i p : Nat) : EmittedExpr :=
  sumE ((List.range (4 - p)).map (fun j => v (KIND i (p + j))))

def askActive (i p : Nat) : EmittedExpr :=
  sumE ((List.range (p + 1)).map (fun j => v (KIND i (4 + j))))

def demandExpr (p : Nat) : EmittedExpr :=
  sumE ((List.range 4).map (fun i => mul (v (QTY i)) (bidActive i p)))

def supplyExpr (p : Nat) : EmittedExpr :=
  sumE ((List.range 4).map (fun i => mul (v (QTY i)) (askActive i p)))

def laterSelected (p : Nat) : EmittedExpr :=
  sumE ((List.range (3 - p)).map (fun j => v (SELECT (p + 1 + j))))

def orderBodies (i : Nat) : List EmittedExpr :=
  ((List.range 8).map (fun t => binaryBody (KIND i t))) ++
  [ sub (sumE ((List.range 8).map (fun t => v (KIND i t)))) (c 1)
  , recompose (QTY i) (QTY_BIT i) QTY_BITS ] ++
  ((List.range QTY_BITS).map (fun b => binaryBody (QTY_BIT i b))) ++
  [sub (v (ORDER_PACK i)) (add (kindValue i) (weighted 8 (v (QTY i))))]

def priceBodies (p : Nat) : List EmittedExpr :=
  [ sub (v (DEMAND p)) (demandExpr p)
  , sub (v (SUPPLY p)) (supplyExpr p)
  , binaryBody (MIN_CHOOSE p)
  , sub (v (VOLUME p))
      (add (mul (v (MIN_CHOOSE p)) (v (DEMAND p)))
        (mul (sub (c 1) (v (MIN_CHOOSE p))) (v (SUPPLY p))))
  , sub (v (MIN_DIFF p))
      (add (mul (v (MIN_CHOOSE p)) (sub (v (SUPPLY p)) (v (DEMAND p))))
        (mul (sub (c 1) (v (MIN_CHOOSE p))) (sub (v (DEMAND p)) (v (SUPPLY p)))))
  , recompose (MIN_DIFF p) (MIN_DIFF_BIT p) DIFF_BITS ] ++
  ((List.range DIFF_BITS).map (fun b => binaryBody (MIN_DIFF_BIT p b))) ++
  [ binaryBody (SELECT p)
  , sub (v (MAX_DIFF p)) (sub (v VSTAR) (v (VOLUME p)))
  , recompose (MAX_DIFF p) (MAX_DIFF_BIT p) DIFF_BITS ] ++
  ((List.range DIFF_BITS).map (fun b => binaryBody (MAX_DIFF_BIT p b))) ++
  [ sub (v (LOW_SLACK p)) (sub (v (MAX_DIFF p)) (laterSelected p))
  , recompose (LOW_SLACK p) (LOW_SLACK_BIT p) DIFF_BITS ] ++
  ((List.range DIFF_BITS).map (fun b => binaryBody (LOW_SLACK_BIT p b)))

def semanticBodies : List EmittedExpr :=
  [ sub (v RULE) (c RULE_ID)
  , sub (v PACKED_BOOK)
      (sumE ((List.range 4).map (fun i => weighted ((128 : Int) ^ i) (v (ORDER_PACK i))))) ] ++
  ((List.range 4).flatMap orderBodies) ++
  ((List.range 4).flatMap priceBodies) ++
  [ sub (sumE ((List.range 4).map (fun p => v (SELECT p)))) (c 1)
  , sub (v PSTAR)
      (sumE ((List.range 4).map (fun (p : Nat) => weighted (p : Int) (v (SELECT p)))))
  , sub (v VSTAR)
      (sumE ((List.range 4).map (fun p => mul (v (SELECT p)) (v (VOLUME p))))) ]

def rootInputExprs : List EmittedExpr :=
  [c ROOT_DOMAIN_TAG, v SESSION, v RULE, v PACKED_BOOK] ++
    (List.range DIGEST_WIDTH).map (fun i => v (BLINDING i)) ++ [c 0, c 0, c 0, c 0]

def rootDigestCols : List Nat := (List.range DIGEST_WIDTH).map ROOT

def rootLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN rootInputExprs rootDigestCols⟩

def hashLookups : List VmConstraint2 := [rootLookup]

def publicPins : List VmConstraint2 :=
  [ .base (.piBinding .first SESSION 0)
  , .base (.piBinding .first RULE 1) ] ++
  (List.range DIGEST_WIDTH).map (fun i => .base (.piBinding .first (ROOT i) (2 + i))) ++
  [ .base (.piBinding .first PSTAR 10)
  , .base (.piBinding .first VSTAR 11) ]

/-- Gates are transition-domain plus an exact last-row copy, avoiding the
height-one/last-row semantic drop that older descriptors suffered. -/
def darkBazaarPrivateN4K4Descriptor : EffectVmDescriptor2 :=
  { name := "dark-bazaar-private-n4k4::wide-poseidon2-v2"
  , traceWidth := TRACE_WIDTH
  , piCount := 12
  , tables := []
  , constraints := hashLookups ++
      semanticBodies.map (fun body => .base (.gate body)) ++ publicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard darkBazaarPrivateN4K4Descriptor.traceWidth == 181
#guard darkBazaarPrivateN4K4Descriptor.piCount == 12
#guard hashLookups.length == 1
#guard darkBazaarPrivateN4K4Descriptor.constraints.length == 1 + 2 * semanticBodies.length + 12
#guard !(emitVmJson2 darkBazaarPrivateN4K4Descriptor).contains "1430520837"

/-! ## 3. Honest emitted-AIR extraction boundary.

This section connects `Satisfied2` to the descriptor bytes: every semantic gate
vanishes modulo BabyBear, every public pin is enforced, and the wide lookup binds
all eight root columns to the genuine full-arity permutation output under
`ChipTableSoundN`.  It is deliberately NOT mislabeled as the final
`Satisfied2 → Accepts` theorem.  The named residual
`DarkBazaarDescriptorToAccepts` is the remaining fixed-size decode/no-wrap lift:
extract the unique kind one-hot and 4-bit quantities, turn all modular equations
into integer equalities using the explicit bounds, then identify the four volume
columns and lowest argmax with `privateBook`. -/

def dbM0 : Int → Int := fun _ => 0
def dbF0 : Int → Int × Nat := fun _ => (0, 0)

def publicCols : List Nat :=
  [SESSION, RULE] ++ rootDigestCols ++ [PSTAR, VSTAR]

def constTrace (a pis : Assignment) (tf : TraceFamily) : VmTrace where
  rows := List.replicate 4 a
  pub := pis
  tf := tf

@[simp] theorem constTrace_rows_length (a pis : Assignment) (tf : TraceFamily) :
    (constTrace a pis tf).rows.length = 4 := by
  simp [constTrace]

@[simp] theorem constTrace_loc0 (a pis : Assignment) (tf : TraceFamily) :
    (envAt (constTrace a pis tf) 0).loc = a := by
  funext col
  simp [envAt, constTrace]

def CanonicalAssignment (a : Assignment) : Prop :=
  ∀ col, 0 ≤ a col ∧ a col < BABYBEAR_MODULUS

theorem semantic_gate_mem {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    VmConstraint2.base (.gate body) ∈ darkBazaarPrivateN4K4Descriptor.constraints := by
  simp [darkBazaarPrivateN4K4Descriptor, hbody]

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ darkBazaarPrivateN4K4Descriptor.constraints := by
  simp [darkBazaarPrivateN4K4Descriptor, hpin]

theorem root_lookup_mem :
    rootLookup ∈ darkBazaarPrivateN4K4Descriptor.constraints := by
  simp [darkBazaarPrivateN4K4Descriptor, hashLookups]

/-- A satisfying constant trace forces every Lean-authored semantic gate modulo
the deployed BabyBear modulus. -/
theorem semantic_gate_vanishes {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (semantic_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

/-- Every declared PI binding is real at row zero. -/
theorem public_pin_sound {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (public_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

/-- Under the genuine wide Poseidon chip-table hypothesis, the descriptor binds
ALL eight public root lanes to the one-permutation output over the exact
domain-separated 12-felt source plus four zero framing lanes. -/
theorem wide_root_lookup_sound {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    rootDigestCols.map a = permOut (rootInputExprs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp) rootLookup root_lookup_mem
  have hlookup :
      (chipLookupTupleN rootInputExprs rootDigestCols).map (·.eval a) ∈ tf TableId.poseidon2 := by
    simpa [rootLookup, VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    rootInputExprs rootDigestCols (by decide) hlookup

structure EmittedAirFacts (permOut : List Int → List Int)
    (a pis : Assignment) (tf : TraceFamily) : Prop where
  canonicalCells : CanonicalAssignment a
  semanticGates : ∀ body ∈ semanticBodies, body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS]
  wideRoot : rootDigestCols.map a = permOut (rootInputExprs.map (·.eval a))
  publicPins : ∀ col pi,
    VmConstraint2.base (.piBinding .first col pi) ∈ publicPins →
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS]

/-- **The strongest closed emitted-AIR bridge in this module today.**  This is
load-bearing (not a guard): it starts from the actual `Satisfied2` denotation and
extracts every gate, every PI, and the full wide commitment lookup.  The exact
integer decode/argmax lift is named above and remains visibly outside this
theorem rather than being assumed. -/
theorem darkBazaarPrivateN4K4_emitted_air_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkBazaarPrivateN4K4Descriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    EmittedAirFacts permOut a pis tf :=
  ⟨hcanon,
   fun _ hbody => semantic_gate_vanishes hsat hbody,
   wide_root_lookup_sound permOut hChip hsat,
   fun _ _ hpin => public_pin_sound hsat hpin⟩

/-- Binary gates really pin a bit; the range decompositions rely on this tooth. -/
theorem binaryBody_zero_iff (a : Assignment) (col : Nat) :
    (binaryBody col).eval a = 0 ↔ a col = 0 ∨ a col = 1 := by
  simp [binaryBody, sub, neg, mul, add, v, c, EmittedExpr.eval]
  omega

#assert_all_clean [
  Market.DarkBazaarPrivateDescriptor.orderCode_injective,
  Market.DarkBazaarPrivateDescriptor.packedBook_injective_on_orders,
  Market.DarkBazaarPrivateDescriptor.argmaxUpto_strict_before,
  Market.DarkBazaarPrivateDescriptor.crossing_strict_before,
  Market.DarkBazaarPrivateDescriptor.check_sound,
  Market.DarkBazaarPrivateDescriptor.two_distinct_openings_yield_root_collision,
  Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4_emitted_air_sound,
  Market.DarkBazaarPrivateDescriptor.binaryBody_zero_iff]

end Market.DarkBazaarPrivateDescriptor
