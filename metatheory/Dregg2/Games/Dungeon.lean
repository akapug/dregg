/-
# Dregg2.Games.Dungeon — THE DESCENT, reimagined natively in Lean.

This is NOT a port of the Rust dungeon. It is a fresh authoring of the descent as the
dreggic object it wants to be:

> **a turn = the exercise of an attenuable proof-carrying token over OWNED state,
> leaving a receipt.**

## The reimagined design, stated as law (each law is a THEOREM below, not prose)

1. **Relics are owned objects with provenance, not counters.** The state carries a
   CUSTODY code per relic (`deep at floor d` → `carried` → `banked`) and custody is a
   MONOTONE RATCHET (`custody_ratchet`): a relic moves down its provenance pipeline and
   never back. A banked relic's history is exactly the receipted turn chain back to the
   world's mint. The counters the deployed teeth read (`pack`, `bank`, `hoard_d`) are
   PROJECTIONS of custody (they are *definitions* here), not independent facts.

2. **Descent attenuates capability.** Carrying rights shrink with depth: every reachable
   state satisfies `pack + depth ≤ CAP` (`capacity_attenuates`). Descending with a full
   pack is not "discouraged" — the deeper turn is *unprovable*. Attenuation as
   arithmetic, not flavor. Corollary `crowned_bank_le_four`: a run that banks THE PRIZE
   (relic 0, floor 4) banks at most `CAP − FLOORS = 4` relics — reaching the bottom
   costs half your carrying rights. And `no_run_banks_everything`: no receipt chain
   whatsoever banks all `RELICS` relics.

3. **The light is the clock.** Every verb has a posted price in `spent`; `spent`
   strictly increases on every turn and is capped at `BREATH`. Permadeath is a theorem:
   a run is at most `BREATH` turns (`run_bounded`) and at `spent = BREATH` no verb is
   legal (`the_light_dies`).

4. **Keys are capabilities.** The way to floor `w` opens only by EXERCISING the carried
   key-relic for `w` (`keyless_unlock_impossible`): a key is an owned, un-dupable relic
   whose own provenance chain proves where it was won.

5. **Banking is terminal.** `flee` banks the pack and writes the run's fate exactly
   once; a banked run is a frozen tomb (`banked_run_frozen`).

6. **The world is minted once**; every relic's provenance replays to the mint
   (`genesisState` is the only entry; `Reachable` quantifies over receipt chains).

The deployed teeth for this design are the `CellProgram` value in
`Dregg2.Games.DungeonProgram` (emitted to `dungeon-on-dregg/program/dungeon_program.json`
and loaded by `dungeon_on_dregg::descent`); the refinement/attack theorems live there.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Dregg2.Tactics

namespace Dregg2.Games.Dungeon

/-! ## 1. The world constants (the balance is part of the design). -/

/-- Number of floors below the surface. Depth `0` is the surface. -/
abbrev FLOORS : Nat := 4

/-- Number of relics minted into the world; conservation is over this total. -/
abbrev RELICS : Nat := 8

/-- The light: total exertion a run may spend. A perfect crowned run costs 24; a full
clear is impossible (see `no_run_banks_everything` — by capacity, not by breath). -/
abbrev BREATH : Nat := 26

/-- Carrying rights at the surface; the capacity law is `pack + depth ≤ CAP`. -/
abbrev CAP : Nat := 8

/-- Per-floor guardian vitality (wounds required to slay). The surface has no guardian. -/
def guardHp : Nat → Nat
  | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | _ => 0

/-! ### Custody codes — the provenance ratchet's ordered alphabet.

`1..FLOORS` = lying in that floor's hoard; `CARRIED = 8` = in the pack; `BANKED = 9`.
The order `floor < CARRIED < BANKED` IS the provenance direction; monotonicity of the
code is the no-return ratchet. -/

abbrev CARRIED : Nat := 8
abbrev BANKED : Nat := 9

/-- Where each relic is minted. Relic 0 is THE PRIZE (floor `FLOORS`); relics 1–3 are
the KEYS to ways 2–4, each found one floor above the way it opens; relics 4–7 are
treasures. -/
def homeFloors : List Nat := [4, 1, 2, 3, 1, 1, 2, 3]

/-- The key-relic that opens way `w` (ways 2..FLOORS ⇒ relics 1..3). -/
def keyFor (w : Nat) : Nat := w - 1

/-! ## 2. The model state — relics first; counters are projections. -/

/-- The descent state. `ways = [way2, way3, way4]` (way 1 is always open);
`custody` is the per-relic custody code list. -/
structure DState where
  depth   : Nat
  spent   : Nat
  wounds  : Nat
  fate    : Nat          -- 0 = alive, 1 = banked
  ways    : List Nat     -- 0/1 each
  custody : List Nat
deriving Repr, DecidableEq

/-- The minted world: surface, full light, ways shut, every relic at its home floor. -/
def genesisState : DState :=
  { depth := 0, spent := 0, wounds := 0, fate := 0
    ways := [0, 0, 0], custody := homeFloors }

/-- Pack size — a PROJECTION of custody (design law 1). -/
def pack (s : DState) : Nat := s.custody.countP (· == CARRIED)

/-- Banked count — a projection of custody. -/
def bank (s : DState) : Nat := s.custody.countP (· == BANKED)

/-- Hoard size at floor `d` — a projection of custody. -/
def hoardAt (s : DState) (d : Nat) : Nat := s.custody.countP (· == d)

/-- Is way `d` open? Way 1 (the first stair) is always open. -/
def wayOpen (s : DState) (d : Nat) : Bool :=
  if d ≤ 1 then true
  else match s.ways[d - 2]? with
       | some v => v == 1
       | none   => false

/-! ## 3. The verbs. Every verb's price is posted; every check IS the rule. -/

inductive Move where
  | delve                  -- descend one floor (the way must be open; wounds reset)
  | unlock (w : Nat)       -- exercise the carried key-relic to open way w
  | smite                  -- wound the standing floor's guardian (price 2 — it strikes back)
  | loot (r : Nat)         -- take relic r from the standing floor's hoard (guardian slain)
  | flee                   -- surface and bank the pack; the run ends
deriving Repr, DecidableEq

/-- The posted price of a verb in breath. -/
def price : Move → Nat
  | .smite => 2
  | _      => 1

/-- One receipted turn of the descent: `step s m = some s'` iff `m` is LEGAL at `s`.
This function IS the rulebook; everything else is proved about it. -/
def step (s : DState) : Move → Option DState
  | .delve =>
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ s.depth < FLOORS
          ∧ wayOpen s (s.depth + 1) = true
          ∧ pack s + (s.depth + 1) ≤ CAP then       -- attenuated carrying rights
        some { s with depth := s.depth + 1, wounds := 0, spent := s.spent + 1 }
      else none
  | .unlock w =>
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ 2 ≤ w ∧ w ≤ FLOORS
          ∧ s.ways[w - 2]? = some 0
          ∧ s.custody[keyFor w]? = some CARRIED then
        some { s with ways := s.ways.set (w - 2) 1, spent := s.spent + 1 }
      else none
  | .smite =>
      if s.fate = 0 ∧ s.spent + 2 ≤ BREATH ∧ 1 ≤ s.depth
          ∧ s.wounds + 1 ≤ guardHp s.depth then
        some { s with wounds := s.wounds + 1, spent := s.spent + 2 }
      else none
  | .loot r =>
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ 1 ≤ s.depth
          ∧ s.custody[r]? = some s.depth              -- the relic lies HERE
          ∧ s.wounds = guardHp s.depth                -- the guardian is slain
          ∧ pack s + 1 + s.depth ≤ CAP then           -- attenuated carrying rights
        some { s with custody := s.custody.set r CARRIED, spent := s.spent + 1 }
      else none
  | .flee =>
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH then
        some { s with fate := 1, spent := s.spent + 1, custody := s.custody.map (fun c => if c = CARRIED then BANKED else c) }
      else none

/-! ## 4. Runs and reachability. A run IS its receipt chain. -/

/-- Replay a move script from the mint; `none` as soon as any move is illegal —
there is no partially-legal run. -/
def replay (ms : List Move) : Option DState :=
  ms.foldl (fun acc m => acc.bind (fun s => step s m)) (some genesisState)

/-- Reachable = some receipt chain replays to it from the mint. -/
def Reachable (s : DState) : Prop := ∃ ms, replay ms = some s

/-- A refused prefix refuses the whole run (folding from `none` stays `none`). -/
private theorem foldl_none (ms : List Move) :
    ms.foldl (fun acc m => acc.bind (fun t => step t m)) none = none := by
  induction ms with
  | nil => rfl
  | cons m rest ih => exact ih

/-! ## 5. Counting helpers (custody projections under `set` / the flee map). -/

private theorem countP_set_bump {l : List Nat} {i a v : Nat} (p : Nat → Bool)
    (hget : l[i]? = some a) (hpa : p a = false) (hpv : p v = true) :
    (l.set i v).countP p = l.countP p + 1 := by
  induction l generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [List.set, List.countP_cons, hpa, hpv]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.set, List.countP_cons, ih hget]
      omega

private theorem countP_set_same {l : List Nat} {i a v : Nat} (p : Nat → Bool)
    (hget : l[i]? = some a) (heq : p a = p v) :
    (l.set i v).countP p = l.countP p := by
  induction l generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp only [List.set, List.countP_cons, heq]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.set, List.countP_cons, ih hget]

private def fleeMap (c : Nat) : Nat := if c = CARRIED then BANKED else c

private theorem countP_fleeMap_carried (l : List Nat) :
    (l.map fleeMap).countP (· == CARRIED) = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, ih]
    by_cases h : hd = CARRIED
    · have h1 : fleeMap hd = BANKED := by simp [fleeMap, h]
      rw [h1]; rfl
    · have h1 : fleeMap hd = hd := by simp [fleeMap, h]
      rw [h1]
      have h2 : (hd == CARRIED) = false := beq_eq_false_iff_ne.mpr h
      simp [h2]

private theorem countP_fleeMap_banked (l : List Nat) :
    (l.map fleeMap).countP (· == BANKED)
      = l.countP (· == CARRIED) + l.countP (· == BANKED) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, List.countP_cons, List.countP_cons, ih]
    by_cases h : hd = CARRIED
    · have h1 : fleeMap hd = BANKED := by simp [fleeMap, h]
      have h2 : (hd == BANKED) = false := by
        subst h; decide
      rw [h1, h2]
      have h3 : (hd == CARRIED) = true := beq_iff_eq.mpr h
      rw [h3]
      simp
      omega
    · have h1 : fleeMap hd = hd := by simp [fleeMap, h]
      have h3 : (hd == CARRIED) = false := beq_eq_false_iff_ne.mpr h
      rw [h1, h3]
      by_cases h9 : hd = BANKED
      · have h4 : (hd == BANKED) = true := beq_iff_eq.mpr h9
        rw [h4]; simp; omega
      · have h4 : (hd == BANKED) = false := beq_eq_false_iff_ne.mpr h9
        rw [h4]; simp

private theorem mem_of_mem_set {l : List Nat} {i v c : Nat}
    (hc : c ∈ l.set i v) : c ∈ l ∨ c = v := by
  induction l generalizing i with
  | nil => simp [List.set] at hc
  | cons hd tl ih =>
    cases i with
    | zero => simp only [List.set, List.mem_cons] at hc ⊢; tauto
    | succ j =>
      simp only [List.set, List.mem_cons] at hc ⊢
      rcases hc with h | h
      · tauto
      · rcases ih h with h' | h' <;> tauto

private theorem countP_pos_of_mem {l : List Nat} {v : Nat} (hmem : v ∈ l) :
    1 ≤ l.countP (· == v) := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.countP_cons]
    rcases List.mem_cons.mp hmem with h | h
    · have h1 : (hd == v) = true := beq_iff_eq.mpr h.symm
      rw [h1]; simp
    · have := ih h; omega

private theorem countP_pos_of_getElem {l : List Nat} {i v : Nat}
    (hget : l[i]? = some v) : 1 ≤ l.countP (· == v) :=
  countP_pos_of_mem (List.mem_of_getElem? hget)

/-! ## 6. The inductive invariant — the design laws as one package. -/

/-- Custody well-formedness: exactly `RELICS` relics forever (no mint, no burn — the
no-dupe law is STRUCTURAL: a relic is one list entry), every code legal. -/
def CustodyWF (s : DState) : Prop :=
  s.custody.length = RELICS ∧
  ∀ c ∈ s.custody, (1 ≤ c ∧ c ≤ FLOORS) ∨ c = CARRIED ∨ c = BANKED

def Inv (s : DState) : Prop :=
  CustodyWF s
    ∧ s.spent ≤ BREATH
    ∧ s.depth ≤ FLOORS
    ∧ s.fate ≤ 1
    ∧ s.ways.length = FLOORS - 1
    ∧ pack s + s.depth ≤ CAP
    ∧ (s.fate = 0 → bank s = 0)
    ∧ (s.fate = 1 → pack s = 0 ∧ bank s + s.depth ≤ CAP)
    ∧ (s.depth = 0 → pack s = 0 ∧ bank s = 0)
    ∧ (s.custody[0]? = some FLOORS ∨ s.depth = FLOORS)

theorem inv_genesis : Inv genesisState := by
  refine ⟨⟨rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (intro c hc
         simp only [genesisState, homeFloors, List.mem_cons, List.not_mem_nil, or_false] at hc
         rcases hc with h | h | h | h | h | h | h | h <;>
           simp [h, FLOORS, CARRIED, BANKED])
      | decide

/-- **Invariant preservation** — every legal turn preserves the design laws. -/
theorem inv_step {s s' : DState} {m : Move} (hInv : Inv s) (h : step s m = some s') :
    Inv s' := by
  obtain ⟨⟨hlen, hcodes⟩, hspent, hdepth, hfate, hways, hcap, hb0, hb1, hd0, hprize⟩ := hInv
  cases m with
  | delve =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3, h4⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, ?_, ?_, hways, ?_, ?_, ?_, ?_, ?_⟩
      · show s.spent + 1 ≤ BREATH; omega
      · show s.depth + 1 ≤ FLOORS; omega
      · exact hfate
      · exact h4
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · intro hd; exact absurd (show s.depth + 1 = 0 from hd) (by omega)
      · rcases hprize with hp | hp
        · exact Or.inl hp
        · exact absurd hp (by omega)
    case isFalse => exact absurd h (by simp)
  | unlock w =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, hdepth, hfate, ?_, hcap, ?_, ?_, hd0, ?_⟩
      · show s.spent + 1 ≤ BREATH; omega
      · show (s.ways.set (w - 2) 1).length = FLOORS - 1
        simpa using hways
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · rcases hprize with hp | hp
        · exact Or.inl hp
        · exact Or.inr hp
    case isFalse => exact absurd h (by simp)
  | smite =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, hdepth, hfate, hways, hcap, ?_, ?_, hd0, ?_⟩
      · show s.spent + 2 ≤ BREATH; omega
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · rcases hprize with hp | hp
        · exact Or.inl hp
        · exact Or.inr hp
    case isFalse => exact absurd h (by simp)
  | loot r =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcond
      cases h
      have hd4 : s.depth ≤ 4 := hdepth
      have hdC : (s.depth == CARRIED) = false :=
        beq_eq_false_iff_ne.mpr (show s.depth ≠ 8 by omega)
      have hdB : (s.depth == BANKED) = false :=
        beq_eq_false_iff_ne.mpr (show s.depth ≠ 9 by omega)
      have hpackBump :
          (s.custody.set r CARRIED).countP (· == CARRIED)
            = s.custody.countP (· == CARRIED) + 1 :=
        countP_set_bump _ h3 hdC (by simp)
      have hbankSame :
          (s.custody.set r CARRIED).countP (· == BANKED)
            = s.custody.countP (· == BANKED) :=
        countP_set_same _ h3 (by simp [hdB])
      refine ⟨⟨?_, ?_⟩, ?_, hdepth, hfate, hways, ?_, ?_, ?_, ?_, ?_⟩
      · show (s.custody.set r CARRIED).length = RELICS
        simpa using hlen
      · intro c hc
        rcases mem_of_mem_set hc with hcl | hcv
        · exact hcodes c hcl
        · right; left; exact hcv
      · show s.spent + 1 ≤ BREATH; omega
      · show (s.custody.set r CARRIED).countP (· == CARRIED) + s.depth ≤ CAP
        rw [hpackBump]
        exact h5
      · intro _
        show (s.custody.set r CARRIED).countP (· == BANKED) = 0
        rw [hbankSame]; exact hb0 h0
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · intro hdz; exact absurd (show s.depth = 0 from hdz) (by omega)
      · rcases hprize with hp | hp
        · by_cases hr0 : r = 0
          · subst hr0
            rw [hp] at h3
            injection h3 with heq
            right
            show s.depth = FLOORS
            omega
          · left
            show (s.custody.set r CARRIED)[0]? = some FLOORS
            rw [List.getElem?_set_ne (by omega)]
            exact hp
        · exact Or.inr hp
    case isFalse => exact absurd h (by simp)
  | flee =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1⟩ := hcond
      cases h
      have hpack0 : (s.custody.map fleeMap).countP (· == CARRIED) = 0 :=
        countP_fleeMap_carried _
      have hbank : (s.custody.map fleeMap).countP (· == BANKED)
          = s.custody.countP (· == CARRIED) + s.custody.countP (· == BANKED) :=
        countP_fleeMap_banked _
      refine ⟨⟨?_, ?_⟩, ?_, hdepth, ?_, hways, ?_, ?_, ?_, ?_, ?_⟩
      · show (s.custody.map fleeMap).length = RELICS
        simpa using hlen
      · intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨a, ha, hEq⟩ := hc
        by_cases hA : a = CARRIED
        · right; right
          rw [← hEq]
          simp [fleeMap, hA]
        · have hca : c = a := by rw [← hEq]; simp [fleeMap, hA]
          subst hca; exact hcodes c ha
      · show s.spent + 1 ≤ BREATH; omega
      · show (1 : Nat) ≤ 1; exact Nat.le_refl 1
      · show (s.custody.map fleeMap).countP (· == CARRIED) + s.depth ≤ CAP
        rw [hpack0]; omega
      · intro hf; exact absurd (show (1 : Nat) = 0 from hf) (by omega)
      · intro _
        refine ⟨hpack0, ?_⟩
        show (s.custody.map fleeMap).countP (· == BANKED) + s.depth ≤ CAP
        rw [hbank]
        have hbz := hb0 h0
        simp only [bank] at hbz
        rw [hbz]
        simpa [pack] using hcap
      · intro hdz
        have hdz' : s.depth = 0 := hdz
        obtain ⟨hp, hb⟩ := hd0 hdz'
        refine ⟨hpack0, ?_⟩
        show (s.custody.map fleeMap).countP (· == BANKED) = 0
        rw [hbank]
        simp only [pack] at hp
        simp only [bank] at hb
        rw [hp, hb]
      · rcases hprize with hp | hp
        · left
          show (s.custody.map fleeMap)[0]? = some FLOORS
          rw [List.getElem?_map, hp]
          rfl
        · exact Or.inr hp
    case isFalse => exact absurd h (by simp)

/-- Every reachable state satisfies the design laws. -/
theorem inv_reachable {s : DState} (h : Reachable s) : Inv s := by
  obtain ⟨ms, hms⟩ := h
  -- generalize over the seed state
  suffices H : ∀ (ms : List Move) (s0 s1 : DState), Inv s0 →
      (ms.foldl (fun acc m => acc.bind (fun t => step t m)) (some s0)) = some s1 →
      Inv s1 by
    exact H ms genesisState s inv_genesis hms
  intro ms
  induction ms with
  | nil => intro s0 s1 h0 h1; simp at h1; exact h1 ▸ h0
  | cons m rest ih =>
    intro s0 s1 h0 h1
    simp only [List.foldl_cons, Option.bind_some] at h1
    cases hstep : step s0 m with
    | none =>
      rw [hstep, foldl_none] at h1
      simp at h1
    | some smid =>
      rw [hstep] at h1
      exact ih smid s1 (inv_step h0 hstep) h1

/-! ## 7. The design laws as standalone theorems. -/

/-- **Law 2 — descent attenuates capability**: carried relics + depth never exceed CAP. -/
theorem capacity_attenuates {s : DState} (h : Reachable s) :
    pack s + s.depth ≤ CAP :=
  (inv_reachable h).2.2.2.2.2.1

/-- **Law 3a — the light dies**: at `spent = BREATH` no verb is legal. Permadeath is a
theorem, not a timer. -/
theorem the_light_dies {s : DState} (hs : s.spent = BREATH) (m : Move) :
    step s m = none := by
  cases m <;> simp only [step] <;> split <;>
    first
      | rfl
      | (rename_i hc; exact absurd hc.2.1 (by omega))
      | (rename_i hc; exact absurd hc.2 (by omega))

/-- Every legal turn strictly spends breath. -/
theorem step_spends {s s' : DState} {m : Move} (h : step s m = some s') :
    s.spent < s'.spent := by
  cases m <;> simp only [step] at h <;> split at h <;>
    (cases h; try (show s.spent < s.spent + _; omega))

/-- **Law 3b — a run is at most `BREATH` turns long.** -/
theorem run_bounded {ms : List Move} {s : DState} (h : replay ms = some s) :
    ms.length ≤ BREATH := by
  suffices H : ∀ (ms : List Move) (s0 s1 : DState),
      (ms.foldl (fun acc m => acc.bind (fun t => step t m)) (some s0)) = some s1 →
      s0.spent + ms.length ≤ s1.spent by
    have hlen := H ms genesisState s h
    have hspent : s.spent ≤ BREATH := (inv_reachable ⟨ms, h⟩).2.1
    have hg : genesisState.spent = 0 := rfl
    omega
  intro ms
  induction ms with
  | nil => intro s0 s1 h1; simp at h1; subst h1; simp
  | cons m rest ih =>
    intro s0 s1 h1
    simp only [List.foldl_cons, Option.bind_some] at h1
    cases hstep : step s0 m with
    | none =>
      rw [hstep, foldl_none] at h1
      simp at h1
    | some smid =>
      rw [hstep] at h1
      have h2 := ih smid s1 h1
      have h3 := step_spends hstep
      simp only [List.length_cons]
      omega

/-- **Law 5 — banking is terminal**: a banked run is a frozen tomb. -/
theorem banked_run_frozen {s : DState} (hf : s.fate = 1) (m : Move) :
    step s m = none := by
  cases m <;> simp only [step] <;> split <;>
    first
      | rfl
      | (rename_i hc; exact absurd hc.1 (by omega))

/-- **Law 4 — keys are capabilities**: an admitted `unlock w` EXERCISED the carried
key-relic for `w`; there is no other way to open a way. -/
theorem keyless_unlock_impossible {s s' : DState} {w : Nat}
    (h : step s (.unlock w) = some s') :
    s.custody[keyFor w]? = some CARRIED := by
  simp only [step] at h
  split at h
  · rename_i hc; exact hc.2.2.2.2.2
  · exact absurd h (by simp)

/-- **Law 1 — the custody ratchet**: a relic's custody code never decreases; provenance
runs one way (floor → carried → banked), so a banked relic's history is a straight
receipt chain back to the mint. -/
theorem custody_ratchet {s s' : DState} {m : Move} (hInv : Inv s)
    (h : step s m = some s') :
    ∀ (i a b : Nat), s.custody[i]? = some a → s'.custody[i]? = some b → a ≤ b := by
  intro i a b hga hgb
  cases m with
  | delve =>
    simp only [step] at h; split at h
    · cases h; simp only at hgb; rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | unlock w =>
    simp only [step] at h; split at h
    · cases h; simp only at hgb; rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | smite =>
    simp only [step] at h; split at h
    · cases h; simp only at hgb; rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | loot r =>
    simp only [step] at h; split at h
    · rename_i hc
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hc
      cases h
      simp only at hgb
      by_cases hir : i = r
      · subst hir
        rw [hga] at h3; cases h3
        have : b = CARRIED := by
          have hlt : i < s.custody.length := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hga
            cases hga
          rw [List.getElem?_set_self (by simpa using hlt)] at hgb
          simpa using hgb.symm
        subst this
        obtain ⟨hlen, hcodes⟩ := hInv.1
        have hd4 : s.depth ≤ FLOORS := hInv.2.2.1
        simp only [CARRIED, FLOORS] at *
        omega
      · rw [List.getElem?_set_ne (by omega)] at hgb
        rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | flee =>
    simp only [step] at h; split at h
    · cases h
      simp only [List.getElem?_map, hga, Option.map_some] at hgb
      cases hgb
      by_cases hA : a = CARRIED <;> simp [fleeMap, hA, CARRIED, BANKED] <;> omega
    · exact absurd h (by simp)

/-- **Law 2 corollary — no receipt chain banks everything**: the full hoard can never
be banked; the capacity attenuation makes a full clear UNPROVABLE, not merely hard. -/
theorem no_run_banks_everything {s : DState} (h : Reachable s) :
    bank s < RELICS := by
  have hInv := inv_reachable h
  obtain ⟨⟨hlen, _⟩, _, hdepth, hfate, _, hcap, hb0, hb1, hd0, _⟩ := hInv
  by_cases hf : s.fate = 0
  · have := hb0 hf
    simp [RELICS] at *
    omega
  · have hf1 : s.fate = 1 := by omega
    obtain ⟨hp, hb⟩ := hb1 hf1
    by_cases hdz : s.depth = 0
    · have := (hd0 hdz).2
      simp [RELICS] at *
      omega
    · simp [CAP, RELICS] at *
      omega

/-- **The crowned run banks at most half the hoard**: banking THE PRIZE (relic 0)
means the run stood at the bottom, and capacity at the bottom is `CAP − FLOORS = 4`.
Glory costs carrying rights. -/
theorem crowned_bank_le_four {s : DState} (h : Reachable s)
    (hcrown : s.custody[0]? = some BANKED) :
    bank s ≤ CAP - FLOORS := by
  have hInv := inv_reachable h
  obtain ⟨⟨hlen, _⟩, _, hdepth, hfate, _, hcap, hb0, hb1, hd0, hprize⟩ := hInv
  have hdF : s.depth = FLOORS := by
    rcases hprize with hp | hp
    · rw [hcrown] at hp
      simp only [Option.some.injEq] at hp
      simp [BANKED, FLOORS] at hp
    · exact hp
  have hbank1 : 1 ≤ bank s := countP_pos_of_getElem hcrown
  by_cases hf : s.fate = 0
  · have := hb0 hf; omega
  · have hf1 : s.fate = 1 := by omega
    obtain ⟨_, hb⟩ := hb1 hf1
    simp [CAP, FLOORS] at *
    omega

/-! ## 8. The driven crowned run — the design is PLAYABLE (`#guard`, executable). -/

/-- The perfect crowned descent: win the keys floor by floor, slay each guardian,
take the prize at the bottom, flee. 16 verbs, 24 breath. -/
def crownedRun : List Move :=
  [ .delve,                      -- to floor 1 (way 1 always open)          spent 1
    .smite,                      -- guardian 1 (hp 1) falls                 spent 3
    .loot 1,                     -- the key to way 2                        spent 4
    .unlock 2,                   -- exercise it                             spent 5
    .delve,                      -- floor 2                                 spent 6
    .smite,                      -- guardian 2 (hp 1) falls                 spent 8
    .loot 2,                     -- the key to way 3                        spent 9
    .unlock 3,                   --                                        spent 10
    .delve,                      -- floor 3                                 spent 11
    .smite, .smite,              -- guardian 3 (hp 2) falls                 spent 15
    .loot 3,                     -- the key to way 4                        spent 16
    .unlock 4,                   --                                        spent 17
    .delve,                      -- floor 4 — the bottom                    spent 18
    .smite, .smite,              -- guardian 4 (hp 2) falls                 spent 22
    .loot 0,                     -- THE PRIZE                               spent 23
    .flee ]                      -- bank it                                 spent 24

-- The crowned run replays, ends banked, with the prize + three keys banked (bank = 4,
-- the `crowned_bank_le_four` bound met with equality) and 2 breath to spare.
#guard (replay crownedRun).isSome
#guard (replay crownedRun).map (·.fate) = some 1
#guard (replay crownedRun).map bank = some 4
#guard (replay crownedRun).map (·.spent) = some 24
#guard (replay crownedRun).map (fun s => s.custody[0]?) = some (some BANKED)

-- Illegal moves are REFUSED by the rulebook (driven, not asserted):
-- keyless descent past floor 1 (way 2 shut):
#guard (replay [.delve, .delve]) = none
-- looting under a living guardian:
#guard (replay [.delve, .loot 1]) = none
-- a second unlock of the same way (the way is no longer 0):
#guard (replay [.delve, .smite, .loot 1, .unlock 2, .unlock 2]) = none
-- moving after banking (the frozen tomb):
#guard (replay [.delve, .flee, .delve]) = none
-- fleeing twice:
#guard (replay [.delve, .flee, .flee]) = none

/-! ## 9. Axiom hygiene. -/

#assert_axioms capacity_attenuates
#assert_axioms the_light_dies
#assert_axioms run_bounded
#assert_axioms banked_run_frozen
#assert_axioms keyless_unlock_impossible
#assert_axioms custody_ratchet
#assert_axioms no_run_banks_everything
#assert_axioms crowned_bank_le_four

end Dregg2.Games.Dungeon
