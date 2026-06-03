/-
# Dregg2.Exec.CodecRoundtrip — parse∘encode roundtrip theorems for the wire codec.

For each grammar production this file proves:

    parseX (sufficient fuel) (encodeX v).toList = some (v, [])

The parser, fed exactly the encoder's output, recovers `v` and consumes the whole string (no
trailing bytes), with no fuel exhaustion. A symmetric codec bug passes a differential silently;
only these theorems, pinning the decoder as the genuine left-inverse of the encoder, catch it.

## Honest receipt — PROVED vs DEFERRED.

**PROVED (all sorry-free, `#assert_axioms`-pinned):**
  * §0 — every leaf: `lit`, `parseInt`/`parseNat`, `parseStr` (escape-free), `ofHex32 ∘ toHex32`
    (lossless on the full 256-bit range), `parseFlag`, the `Auth` tag, dispatch fail-closure lemmas;
  * §1–§3 — `Value`/`FIELDS` scalar leaf, per-asset `BAL` ledger entry, headline `fillJ_*` facts;
  * §5–§6 — recursive `Value`/`FIELDS` tree and the security-critical `Authorization` decoder
    (all 10 variants + recursive `oneOf`, by strong induction on fuel);
  * §7 — the `FullActionA` decoder, complete at all 46 arms;
  * §8–§11c — every wide-state side-table list (AUTHS, Nat-list, BAL-list, ESCROWS, QUEUES, SWISS).

**DEFERRED (codec is TCB — `#eval`-cross-validated at each codec site, no proof here yet):**
`parseCaveatsW` (per-node caveat array); `parseForestW`/`parseChildrenW` (recursive action-tree +
delegation edges); `parseWState`/`parseWTurn`/`parseWWire` (wide-state record + Turn envelope +
whole-wire object). The side-table list productions they assemble are all proved above (§9–§11c).

Every digest/commitment field is the low 256 bits of a `Nat`. Proved roundtrips are the identity on
the well-formed value space (`< 2^256`). NON-VACUOUS: the `Wf` hypothesis is satisfiable (demo values
witness it) and the theorem fails without the digest bound (a `2^256`-wrap value is a genuine
counterexample) — real teeth, not a triviality.

Soundness note: no new axioms; keystones are `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}` (a `sorryAx` would fail the pin and the build).
-/
import Dregg2.Exec.FFI
import Mathlib.Tactic

namespace Dregg2.Exec.CodecRoundtrip

open Dregg2.Exec
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide

/-! ## §0a — the decimal-number leaf (`parseInt` / `parseNat` invert `toString`).

The encoder emits numbers via `toString` (= `Nat.repr` / `Int.repr`), which is
`String.ofList (Nat.toDigits 10 n)`. The parser's `digitsGo` greedily collects leading digit chars
and `parseInt` folds them MSB-first. We prove the parser is the exact inverse, PROVIDED the byte
after the number is not itself a digit (the grammar always emits a delimiter `,`/`]`/`}` next — the
encoder NEVER abuts two numbers). -/

/-- The parser's per-char decode step (the body of `parseInt`'s fold). -/
private def decStep (acc : Nat) (c : Char) : Nat := acc * 10 + (c.toNat - '0'.toNat)

/-- A nibble `< 10`'s `digitChar` decodes back to itself. -/
theorem digitChar_decStep (m : Nat) :
    (Nat.digitChar (m % 10)).toNat - '0'.toNat = m % 10 := by
  have : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 10) <;> rfl

/-- `digitChar` of a nibble `< 10` IS a digit char. -/
theorem digitChar_isDigit (m : Nat) : (Nat.digitChar (m % 10)).isDigit = true := by
  have : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
  interval_cases (m % 10) <;> rfl

/-- `toDigitsCore` threads its accumulator as a pure SUFFIX. -/
theorem toDigitsCore_append (b f : Nat) : ∀ (n : Nat) (ds : List Char),
    Nat.toDigitsCore b f n ds = Nat.toDigitsCore b f n [] ++ ds := by
  induction f with
  | zero => intro n ds; rfl
  | succ k ih =>
    intro n ds
    rw [Nat.toDigitsCore, Nat.toDigitsCore]
    by_cases hn0 : n / b = 0
    · rw [if_pos hn0, if_pos hn0]; rfl
    · rw [if_neg hn0, if_neg hn0, ih (n/b) (Nat.digitChar (n % b) :: ds),
          ih (n/b) [Nat.digitChar (n % b)]]
      simp [List.append_assoc]

/-- EVERY char of `Nat.toDigits 10 n` is a digit char (the decimal repr is all digits). -/
theorem toDigitsCore_all_digits (f : Nat) : ∀ (n : Nat) (ds : List Char),
    (∀ c ∈ ds, c.isDigit = true) →
    (∀ c ∈ Nat.toDigitsCore 10 f n ds, c.isDigit = true) := by
  induction f with
  | zero => intro n ds hds; exact hds
  | succ k ih =>
    intro n ds hds
    rw [Nat.toDigitsCore]
    by_cases hn0 : n / 10 = 0
    · rw [if_pos hn0]; intro c hc
      rcases List.mem_cons.mp hc with h1 | h1
      · subst h1; exact digitChar_isDigit n
      · exact hds c h1
    · rw [if_neg hn0]
      apply ih (n/10) (Nat.digitChar (n%10) :: ds)
      intro c hc
      rcases List.mem_cons.mp hc with h1 | h1
      · subst h1; exact digitChar_isDigit n
      · exact hds c h1

/-- The bridge: `(toString n).toList` IS `Nat.toDigitsCore 10 (n+1) n []` (decimal repr). -/
theorem toString_toList (n : Nat) :
    (toString n).toList = Nat.toDigitsCore 10 (n+1) n [] := by
  show (Nat.repr n).toList = _
  unfold Nat.repr Nat.toDigits
  rw [String.toList_ofList]

/-- `Nat.repr n` is all digits. -/
theorem repr_all_digits (n : Nat) : ∀ c ∈ (toString n).toList, c.isDigit = true := by
  rw [toString_toList]
  exact toDigitsCore_all_digits (n+1) n [] (by simp)

/-- The folded value-recovery: `digitsGo`/`foldl` over `toDigitsCore 10 f n []` recovers
`a * 10^(#digits) + n`, when `n < 10^f` (the *fuel adequacy* for the number). -/
theorem foldl_toDigitsCore (f : Nat) : ∀ (n a : Nat), n < 10 ^ f →
    List.foldl decStep a (Nat.toDigitsCore 10 f n [])
      = a * 10 ^ (Nat.toDigitsCore 10 f n []).length + n := by
  induction f with
  | zero => intro n a h; simp only [pow_zero, Nat.lt_one_iff] at h; subst h; simp [Nat.toDigitsCore]
  | succ k ih =>
    intro n a h
    rw [Nat.toDigitsCore]
    by_cases hn0 : n / 10 = 0
    · have hlt : n < 10 := by rcases Nat.lt_or_ge n 10 with h1|h1; exact h1; exfalso; omega
      rw [if_pos hn0]
      simp only [List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil]
      unfold decStep; rw [digitChar_decStep, Nat.mod_eq_of_lt hlt]; ring
    · have hrec : n / 10 < 10 ^ k := by have h2 : n < 10 ^ (k+1) := h; rw [pow_succ] at h2; omega
      rw [if_neg hn0, toDigitsCore_append 10 k (n/10) [Nat.digitChar (n%10)], List.foldl_append,
          ih (n/10) a hrec]
      simp only [List.foldl_cons, List.foldl_nil, List.length_append, List.length_cons,
                 List.length_nil]
      unfold decStep; rw [digitChar_decStep]
      set P := (Nat.toDigitsCore 10 k (n / 10) []).length with hP
      have hpow : (10:Nat) ^ (P + 1) = 10 ^ P * 10 := by rw [pow_succ]
      have hdm : n / 10 * 10 + n % 10 = n := by omega
      calc (a * 10 ^ P + n / 10) * 10 + n % 10
          = a * (10 ^ P * 10) + (n / 10 * 10 + n % 10) := by ring
        _ = a * 10 ^ (P + 1) + n := by rw [hpow, hdm]

/-- `digitsGo` over an all-digit list followed by a NON-digit (or end) returns the digit list and the
rest verbatim — the greedy collection consumes EXACTLY the number. -/
theorem digitsGo_append (ds : List Char) :
    ∀ (acc rest : List Char),
    (∀ c ∈ ds, c.isDigit = true) →
    (rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) →
    digitsGo (ds ++ rest) acc = (acc ++ ds, rest) := by
  induction ds with
  | nil =>
    intro acc rest _ hrest
    simp only [List.nil_append, List.append_nil]
    rcases hrest with h | ⟨c, rs, hc, hd⟩
    · subst h; rfl
    · subst hc; unfold digitsGo; rw [if_neg (by rw [hd]; simp)]
  | cons d ds ih =>
    intro acc rest hds hrest
    simp only [List.cons_append]
    unfold digitsGo
    rw [if_pos (hds d (List.mem_cons_self)),
        ih (acc ++ [d]) rest (fun c hc => hds c (List.mem_cons_of_mem d hc)) hrest]
    simp [List.append_assoc]

/-- **`parseInt` on a digit-led, non-`'-'`-led list** computes from the greedy-digit recovery: if
`digitsGo` returns `(h0 :: t0, rest)` (nonempty digit prefix) and the fold gives `v`, `parseInt`
returns `(↑v, rest)`. The structural workhorse (handles the sign-decompose match fail-closed). -/
theorem parseInt_cons (h0 : Char) (t0 rest : List Char)
    (hh0ne : h0 ≠ '-')
    (hgo : digitsGo (h0 :: (t0 ++ rest)) [] = (h0 :: t0, rest))
    (v : Nat)
    (hfold : (h0 :: t0).foldl (fun a d => a * 10 + (Char.toNat d - Char.toNat '0')) 0 = v) :
    parseInt (h0 :: (t0 ++ rest)) = some ((v : Int), rest) := by
  unfold parseInt
  split
  rename_i neg cs heq
  split at heq
  · rename_i r heq2; rw [List.cons.injEq] at heq2; exact absurd heq2.1 hh0ne
  · rw [Prod.mk.injEq] at heq
    obtain ⟨hneg, hcs⟩ := heq
    subst hneg; subst hcs
    simp only [hgo, List.isEmpty_cons]
    rw [if_neg (by simp)]
    simp only [hfold]; simp

/-- The fuel adequacy for the decimal number: `n < 10^(n+1)`, so `foldl_toDigitsCore` applies on the
full repr (the parser never starves). -/
theorem nat_lt_pow (n : Nat) : n < 10 ^ (n+1) := by
  calc n < 2 ^ n := Nat.lt_two_pow_self
    _ ≤ 10 ^ n := Nat.pow_le_pow_left (by norm_num) n
    _ ≤ 10 ^ (n+1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The repr of a `Nat` is a NONEMPTY all-digit list — expose head/tail with the head a digit. -/
theorem repr_cons (n : Nat) :
    ∃ h0 t0, (toString n).toList = h0 :: t0 ∧ h0.isDigit = true ∧ h0 ≠ '-'
      ∧ (∀ c ∈ (toString n).toList, c.isDigit = true) := by
  have hdigits : (toString n).toList = Nat.toDigitsCore 10 (n+1) n [] := toString_toList n
  have halldig : ∀ c ∈ (toString n).toList, c.isDigit = true := repr_all_digits n
  have hne2 : (toString n).toList ≠ [] := by
    rw [hdigits, Nat.toDigitsCore]
    by_cases hn0 : n / 10 = 0
    · rw [if_pos hn0]; simp
    · rw [if_neg hn0, toDigitsCore_append]; simp
  obtain ⟨h0, t0, ht0⟩ := List.exists_cons_of_ne_nil hne2
  have hh0dig : h0.isDigit = true := halldig h0 (by rw [ht0]; exact List.mem_cons_self)
  exact ⟨h0, t0, ht0, hh0dig, by intro h; rw [h] at hh0dig; simp at hh0dig, halldig⟩

/-- **`parseInt` inverts `toString` on a `Nat`-valued `Int`** — fed `(toString n) ++ rest` where the
post-byte is not a digit, it recovers `(↑n, rest)`. -/
theorem parseInt_toString_nat (n : Nat) (rest : PState)
    (hrest : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    parseInt ((toString n).toList ++ rest) = some ((n : Int), rest) := by
  obtain ⟨h0, t0, ht0, _, hh0ne, halldig⟩ := repr_cons n
  rw [ht0]
  have hgo : digitsGo (h0 :: (t0 ++ rest)) [] = (h0 :: t0, rest) := by
    have := digitsGo_append (h0 :: t0) [] rest (by rw [← ht0]; exact halldig) hrest
    simpa using this
  have hfuel := foldl_toDigitsCore (n+1) n 0 (nat_lt_pow n)
  have hfold : (h0 :: t0).foldl (fun a d => a * 10 + (Char.toNat d - Char.toNat '0')) 0 = n := by
    have hbridge : (h0 :: t0) = Nat.toDigitsCore 10 (n+1) n [] := by rw [← ht0]; exact toString_toList n
    rw [hbridge]
    have : List.foldl (fun a d => a * 10 + (Char.toNat d - Char.toNat '0')) 0
              (Nat.toDigitsCore 10 (n+1) n []) = List.foldl decStep 0 (Nat.toDigitsCore 10 (n+1) n []) := rfl
    rw [this, hfuel]; simp
  simpa using parseInt_cons h0 t0 rest hh0ne hgo n hfold

/-- **`parseNat` inverts `toString` on a `Nat`** — provided the byte after is not a digit. -/
theorem parseNat_toString (n : Nat) (rest : PState)
    (hrest : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    parseNat ((toString n).toList ++ rest) = some (n, rest) := by
  unfold parseNat
  rw [parseInt_toString_nat n rest hrest]
  simp

/-! ## §0b — the SIGNED-Int leaf (`parseInt` inverts `toString` on a NEGATIVE `Int`). -/

/-- `toString (Int.negSucc m)` is `'-' :: (toString (m+1)).toList`. -/
theorem toString_negSucc (m : Nat) :
    (toString (Int.negSucc m)).toList = '-' :: (toString (m+1)).toList := by
  show (("-" ++ Nat.repr (m+1)) : String).toList = _
  rw [String.toList_append]; rfl

/-- **`parseInt` inverts `toString` on EVERY `Int`** (both signs) — the post-byte not a digit. -/
theorem parseInt_toString (i : Int) (rest : PState)
    (hrest : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    parseInt ((toString i).toList ++ rest) = some (i, rest) := by
  cases i with
  | ofNat n =>
      have : (toString (Int.ofNat n)) = toString n := rfl
      rw [this]; exact parseInt_toString_nat n rest hrest
  | negSucc m =>
      rw [toString_negSucc]
      simp only [List.cons_append]
      -- the sign branch picks neg = true, cs = (toString (m+1)) ++ rest
      unfold parseInt
      split
      rename_i neg cs heq
      split at heq
      · rename_i r heq2
        rw [List.cons.injEq] at heq2
        obtain ⟨_, hr⟩ := heq2
        -- heq : (true, r) = (neg, cs); and r = (toString (m+1)).toList ++ rest
        rw [Prod.mk.injEq] at heq
        obtain ⟨hneg, hcs⟩ := heq
        subst hneg; subst hcs; subst hr
        -- now digitsGo over (toString (m+1)).toList ++ rest:
        obtain ⟨h0, t0, ht0, _, hh0ne, halldig⟩ := repr_cons (m+1)
        rw [ht0]
        have hgo : digitsGo (h0 :: (t0 ++ rest)) [] = (h0 :: t0, rest) := by
          have := digitsGo_append (h0 :: t0) [] rest (by rw [← ht0]; exact halldig) hrest
          simpa using this
        have hfold : (h0 :: t0).foldl (fun a d => a * 10 + (Char.toNat d - Char.toNat '0')) 0 = m+1 := by
          have hbridge : (h0 :: t0) = Nat.toDigitsCore 10 (m+2) (m+1) [] := by
            rw [← ht0]; exact toString_toList (m+1)
          rw [hbridge]
          have heq3 : List.foldl (fun a d => a * 10 + (Char.toNat d - Char.toNat '0')) 0
                  (Nat.toDigitsCore 10 (m+2) (m+1) []) = List.foldl decStep 0 (Nat.toDigitsCore 10 (m+2) (m+1) []) := rfl
          rw [heq3, foldl_toDigitsCore (m+2) (m+1) 0 (by have := nat_lt_pow (m+1); simpa using this)]
          simp
        split
        rename_i ds rst hgoeq
        rw [show (h0 :: t0 ++ rest) = h0 :: (t0 ++ rest) from rfl, hgo] at hgoeq
        rw [Prod.mk.injEq] at hgoeq
        obtain ⟨hds, hrst⟩ := hgoeq
        subst hds; subst hrst
        rw [if_neg (by simp)]
        simp only [hfold]
        -- neg = true ⇒ -(Int.ofNat (m+1)) = Int.negSucc m
        simp [Int.negSucc_eq]
      · -- the '-' branch must fire since head IS '-': contradiction with the default arm
        rename_i heq2
        simp at heq2

/-! ## §0c — the `lit` literal-prefix leaf. -/

/-- **`lit s` consumes EXACTLY the prefix it expects** — fed `s ++ rest`, it returns `rest`. The
delimiter workhorse: every fixed literal the encoder emits (`{"int":`, `,`, `]}`, …) round-trips. -/
theorem litGo_append : ∀ (s rest : List Char), litGo s (s ++ rest) = some rest := by
  intro s
  induction s with
  | nil => intro rest; rfl
  | cons c cs ih => intro rest; simp only [List.cons_append, litGo, beq_self_eq_true, if_true]; exact ih rest

/-- `lit s (s.toList ++ rest) = some rest` — the string-keyed form used throughout the codec. -/
theorem lit_append (s : String) (rest : PState) : lit s (s.toList ++ rest) = some rest := by
  unfold lit; exact litGo_append s.toList rest

/-! ## §0d — the JSON-STRING leaf (field names with no `"`/`\`). -/

/-- One non-escape char steps `parseStrGo` (skips the `"`/`\\` escape patterns). -/
theorem parseStrGo_step (c : Char) (tail acc : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') :
    parseStrGo (c :: tail) acc = parseStrGo tail (acc ++ [c]) := by
  conv_lhs => unfold parseStrGo
  split <;> rename_i heq <;>
    first
    | (injection heq with ha hb; first | exact absurd ha h1 | exact absurd ha h2)
    | (injection heq with ha hb; subst ha; subst hb; rfl)
    | simp_all

/-- `parseStrGo` over `(escape-free chars) ++ '"' :: rest` recovers the chars (as a `String`). -/
theorem parseStrGo_clean (cs : List Char)
    (hcl : ∀ c ∈ cs, c ≠ '"' ∧ c ≠ '\\') :
    ∀ acc rest, parseStrGo (cs ++ '"' :: rest) acc = some (String.ofList (acc ++ cs), rest) := by
  induction cs with
  | nil => intro acc rest; simp [parseStrGo]
  | cons c cs ih =>
    intro acc rest
    have hc := hcl c (List.mem_cons_self)
    rw [List.cons_append, parseStrGo_step c (cs ++ '"' :: rest) acc hc.1 hc.2,
        ih (fun x hx => hcl x (List.mem_cons_of_mem c hx)) (acc ++ [c]) rest]
    simp [List.append_assoc]

/-- The `jsonEscape` fold's `.toList` over an escape-free list appends verbatim. -/
theorem foldl_jsonEscape_toList (l : List Char) :
    ∀ (acc : String), (∀ c ∈ l, c ≠ '"' ∧ c ≠ '\\') →
    (l.foldl (fun acc c => acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\"
                                  else String.singleton c)) acc).toList = acc.toList ++ l := by
  induction l with
  | nil => intro acc _; simp
  | cons c cs ih =>
    intro acc hcl
    have hc := hcl c (List.mem_cons_self)
    have h1 : (c == '"') = false := by simp [hc.1]
    have h2 : (c == '\\') = false := by simp [hc.2]
    simp only [List.foldl_cons, h1, h2, Bool.false_eq_true, if_false]
    rw [ih (acc ++ String.singleton c) (fun x hx => hcl x (List.mem_cons_of_mem c hx)),
        String.toList_append, String.toList_singleton]
    simp [List.append_assoc]

/-- `jsonEscape` is the IDENTITY on an escape-free string (no `"`/`\`). -/
theorem jsonEscape_clean (s : String)
    (hcl : ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\\') : jsonEscape s = s := by
  apply String.toList_inj.mp
  unfold jsonEscape
  rw [String.foldl_eq_foldl_toList, foldl_jsonEscape_toList s.toList "" hcl]
  simp

/-- A `String` whose chars are escape-free round-trips through `"NAME"` quoting via `parseStr`. -/
theorem parseStr_clean (s : String) (rest : PState)
    (hcl : ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\\') :
    parseStr ('"' :: (jsonEscape s).toList ++ '"' :: rest) = some (s, rest) := by
  unfold parseStr
  rw [jsonEscape_clean s hcl]
  show parseStrGo (s.toList ++ '"' :: rest) [] = some (s, rest)
  rw [parseStrGo_clean s.toList hcl [] rest]
  simp [String.ofList_toList]

/-! ## §0e — the `[u8;32]` DIGEST field (`ofHex32 ∘ toHex32`, lossless on the full 256-bit range).

The digest field is the dregg1 `[u8;32]` width-pinned to EXACTLY 64 lowercase hex chars (`§W1`). The
roundtrip is the identity precisely on the 256-bit value space (`< 2^256`); a `2^256`-wrap value is a
genuine counterexample (so the bound is REAL teeth, not vacuous). -/

/-- A nibble `< 16` round-trips through `hexDigitOfNat`/`natOfHexDigit`. -/
theorem nibble_roundtrip (d : Nat) (h : d < 16) : natOfHexDigit (hexDigitOfNat d) = some d := by
  interval_cases d <;> rfl

/-- `toHex32.go` threads its accumulator as a pure SUFFIX (low nibbles prepended). -/
theorem toHex32go_append (fuel : Nat) : ∀ (acc : List Char) (m : Nat),
    toHex32.go fuel acc m = toHex32.go fuel [] m ++ acc := by
  induction fuel with
  | zero => intro acc m; simp [toHex32.go]
  | succ k ih => intro acc m; simp only [toHex32.go]
                 rw [ih (hexDigitOfNat (m % 16) :: acc), ih [hexDigitOfNat (m % 16)]]
                 simp [List.append_assoc]

/-- `ofHex32.go` distributes over an append via `Option.bind` (the MSB-first fold). -/
theorem ofHex32go_append (xs : List Char) : ∀ (ys : List Char) (acc : Nat),
    ofHex32.go (xs ++ ys) acc = (ofHex32.go xs acc).bind (fun a => ofHex32.go ys a) := by
  induction xs with
  | nil => intro ys acc; simp [ofHex32.go]
  | cons c cs ih =>
    intro ys acc
    simp only [List.cons_append, ofHex32.go]
    cases hc : natOfHexDigit c with
    | none => rfl
    | some d => simp only []; rw [ih ys (acc * 16 + d)]

/-- The 64-nibble recovery: `ofHex32.go (toHex32.go fuel [] n) acc = acc·16^fuel + n mod 16^fuel`. -/
theorem hex_recovery (fuel : Nat) : ∀ (n acc : Nat),
    ofHex32.go (toHex32.go fuel [] n) acc = some (acc * 16 ^ fuel + n % 16 ^ fuel) := by
  induction fuel with
  | zero => intro n acc; simp [toHex32.go, ofHex32.go, Nat.mod_one]
  | succ k ih =>
    intro n acc
    have hstep : toHex32.go (k+1) [] n = toHex32.go k [] (n/16) ++ [hexDigitOfNat (n%16)] := by
      simp only [toHex32.go]; rw [toHex32go_append k [hexDigitOfNat (n%16)] (n/16)]
    rw [hstep, ofHex32go_append, ih (n/16) acc]
    simp only [Option.bind_some, ofHex32.go]
    rw [nibble_roundtrip (n % 16) (Nat.mod_lt _ (by norm_num))]
    simp only [ofHex32.go]
    congr 1
    have h16 : (16:Nat)^(k+1) = 16^k * 16 := by rw [pow_succ]
    have hmm : n % (16 * 16^k) = n % 16 + 16 * (n/16 % 16^k) := Nat.mod_mul
    rw [h16, Nat.mul_comm (16^k) 16, hmm]; ring

/-- **The digest field is LOSSLESS on the full 256-bit range** — `ofHex32 (toHex32 n) = some (n %
2^256)`. NON-VACUOUS: the RHS is `n` for every `n < 2^256` (the whole `[u8;32]` value space), and the
`2^256`-wrap is a real counterexample (a 5-byte stand-in would lose the high bytes). -/
theorem ofHex32_toHex32 (n : Nat) : ofHex32 (toHex32 n).toList = some (n % 2 ^ 256) := by
  unfold ofHex32 toHex32
  rw [String.toList_ofList]
  have hlen : (toHex32.go 64 [] n).length = 64 := by
    have hgo : ∀ (fuel : Nat) (acc : List Char) (m : Nat),
        (toHex32.go fuel acc m).length = fuel + acc.length := by
      intro fuel; induction fuel with
      | zero => intro acc m; simp [toHex32.go]
      | succ k ih => intro acc m; simp only [toHex32.go]; rw [ih]; simp [List.length_cons]; omega
    rw [hgo]; simp
  rw [if_neg (by rw [hlen]; omega)]
  rw [hex_recovery 64 n 0]
  norm_num

/-- `n < 2^256` ⇒ the digest field is the IDENTITY (the well-formed regime). -/
theorem ofHex32_toHex32_wf (n : Nat) (h : n < 2 ^ 256) :
    ofHex32 (toHex32 n).toList = some n := by
  rw [ofHex32_toHex32, Nat.mod_eq_of_lt h]

/-- `parseHex32 (toHex32 n).toList ++ rest = some (n % 2^256, rest)`. -/
theorem parseHex32_toHex32 (n : Nat) (rest : PState) :
    parseHex32 ((toHex32 n).toList ++ rest) = some (n % 2 ^ 256, rest) := by
  unfold parseHex32
  have hlen : (toHex32 n).toList.length = 64 := toHex32_length n
  have htake : ((toHex32 n).toList ++ rest).take 64 = (toHex32 n).toList := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hdrop : ((toHex32 n).toList ++ rest).drop 64 = rest := by
    rw [List.drop_append_of_le_length (by omega)]; simp [hlen]
  rw [htake, if_neg (by omega)]
  rw [show ofHex32 (toHex32 n).toList = some (n % 2^256) from ofHex32_toHex32 n]
  rw [hdrop]

/-- The QUOTED digest field `"H64"` round-trips via `parseDig` (well-formed: `< 2^256`). -/
theorem parseDig_encDig (d : Nat) (rest : PState) (hd : d < 2 ^ 256) :
    parseDig ((encDig d).toList ++ rest) = some (d, rest) := by
  unfold parseDig encDig
  -- encDig d = ("\"" ++ toHex32 d ++ "\"").toList ++ rest. Rebracket as ("\"").toList ++ (...).
  rw [show ((("\"" ++ toHex32 d ++ "\"") : String).toList ++ rest)
        = ("\"" : String).toList ++ ((toHex32 d).toList ++ (("\"" : String).toList ++ rest)) by
        rw [String.toList_append, String.toList_append]; simp [List.append_assoc]]
  rw [lit_append]
  simp only []
  rw [parseHex32_toHex32 d (("\"" : String).toList ++ rest), Nat.mod_eq_of_lt hd]
  simp only []
  rw [lit_append]
  simp

/-! ## §0f — the 0/1 FLAG and the `Auth` enum tag (narrow auth-list). -/

/-- A `Bool` flag round-trips: `parseFlag` of `"0"`/`"1"` recovers it (post-byte non-digit). -/
theorem parseFlag_bool (b : Bool) (rest : PState)
    (hrest : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    parseFlag (((if b then "1" else "0") : String).toList ++ rest) = some (b, rest) := by
  unfold parseFlag
  cases b with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [show (("0":String).toList) = (toString (0:Nat)).toList from rfl,
          parseNat_toString 0 rest hrest]; simp
  | true =>
      simp only [if_true]
      rw [show (("1":String).toList) = (toString (1:Nat)).toList from rfl,
          parseNat_toString 1 rest hrest]; simp

/-- The `Auth` enum tag round-trips: `authOfTag (authTag a) = some a`. -/
theorem authOfTag_authTag (a : Authority.Auth) : authOfTag (authTag a) = some a := by
  cases a <;> rfl

/-! ## §0g — DISPATCH helpers: a literal CONSUMES its prefix, FAILS on a mismatched tag, and the
closing delimiters are non-digit (so the number-leaf's post-byte side condition is discharged). -/

/-- `lit s (s.toList ++ mid ++ rest)` returns `mid ++ rest` (the `++`-associated form). -/
theorem lit_app2 (s : String) (mid rest : PState) :
    lit s (s.toList ++ (mid ++ rest)) = some (mid ++ rest) := lit_append s (mid ++ rest)

/-- `litGo` peels a MATCHING head char. -/
theorem litGo_cons_match (a : Char) (as : List Char) (bs : PState) :
    litGo (a :: as) (a :: bs) = litGo as bs := by
  conv_lhs => rw [litGo]
  rw [if_pos (by simp)]

/-- `litGo` FAILS on a MISMATCHED head char (fail-closed dispatch on a wrong tag). -/
theorem litGo_ne_head (a : Char) (as : List Char) (b : Char) (bs : PState) (h : a ≠ b) :
    litGo (a :: as) (b :: bs) = none := by
  conv_lhs => rw [litGo]
  rw [if_neg (by simp [h])]

/-- A `]`-led rest is non-digit (the closing-bracket post-byte condition). -/
theorem nd_brack (rest : PState) :
    (']' :: rest = [] ∨ ∃ c rs, ']' :: rest = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨']', rest, rfl, by decide⟩
/-- A `}`-led rest is non-digit. -/
theorem nd_brace (rest : PState) :
    ('}' :: rest = [] ∨ ∃ c rs, '}' :: rest = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨'}', rest, rfl, by decide⟩
/-- A `,`-led rest is non-digit. -/
theorem nd_comma (rest : PState) :
    (',' :: rest = [] ∨ ∃ c rs, ',' :: rest = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨',', rest, rfl, by decide⟩

/-! ## §1 — the wide `Value` / `FIELDS` / `CELLS` roundtrip.

The well-formedness `WfValue` pins exactly the codec's boundary constraints: every `dig` digest is
`< 2^256` (the `[u8;32]` width) and every record field NAME is escape-free (no `"`/`\`). These are
the SAME constraints the differential's value space lives in; the demo values satisfy them (so the
theorem is non-vacuous), and dropping the `dig` bound is a real counterexample (the `2^256`-wrap). -/

/-! Well-formed `Value`: digests `< 2^256`, field names escape-free (mutually over records). -/
mutual
/-- Well-formed `Value`: digest `< 2^256` (else the digest field wraps). -/
def WfValue : Value → Prop
  | .int _    => True
  | .dig d    => d < 2 ^ 256
  | .sym _    => True
  | .record fs => WfFields fs
def WfFields : List (FieldName × Value) → Prop
  | []          => True
  | (n, v) :: fs => (∀ c ∈ n.toList, c ≠ '"' ∧ c ≠ '\\') ∧ WfValue v ∧ WfFields fs
end

/-! A structural size for `Value` (the fuel measure: parse-depth bound). -/
mutual
/-- A structural size for `Value` (the fuel measure). -/
def valueSize : Value → Nat
  | .int _    => 1
  | .dig _    => 1
  | .sym _    => 1
  | .record fs => 1 + fieldsSize fs
def fieldsSize : List (FieldName × Value) → Nat
  | []          => 0
  | (_, v) :: fs => 1 + valueSize v + fieldsSize fs
end

/-- **`parseValueW` inverts `encodeValueW` on a SCALAR leaf** (`int`/`dig`/`sym`) — the parser
dispatches on the tag (earlier-tag literals FAIL fail-closed), then recovers the payload via the
number/digest leaf. NON-VACUOUS on `dig`: the `< 2^256` hypothesis is REAL teeth (the `2^256`-wrap is
a genuine counterexample). The `record` arm needs the mutual fields recursion (the remaining FILL-J
structural layer); the scalar arms — which carry every BALANCE (`int`), DIGEST (`dig`), and SYMBOL
(`sym`) leaf the ledger reads — are removed from the TCB here. -/
theorem parseValueW_scalar (fuel : Nat) (v : Value) (rest : PState)
    (hwf : WfValue v) (hscalar : ∀ fs, v ≠ .record fs) :
    parseValueW (fuel+1) ((encodeValueW v).toList ++ rest) = some (v, rest) := by
  cases v with
  | record fs => exact absurd rfl (hscalar fs)
  | int i =>
      unfold encodeValueW parseValueW
      rw [show (("{\"int\":" ++ toString i ++ "}"):String).toList ++ rest
            = ("{\"int\":":String).toList ++ ((toString i).toList ++ ('}' :: rest)) by
            rw [String.toList_append, String.toList_append,
                show ("}":String).toList = ['}'] from rfl]; simp [List.append_assoc]]
      rw [lit_append]; simp only []
      rw [parseInt_toString i _ (nd_brace rest)]; simp only []
      rw [show lit "}" ('}' :: rest) = some rest from by
            rw [show ('}'::rest) = ("}":String).toList ++ rest from rfl, lit_append]]
      simp
  | sym s =>
      unfold encodeValueW parseValueW
      rw [show (("{\"sym\":" ++ toString s ++ "}"):String).toList ++ rest
            = '{'::'"'::'s'::(("ym\":".toList ++ (toString s).toList) ++ ('}' :: rest)) by
            rw [String.toList_append, String.toList_append,
                show ("{\"sym\":":String).toList = '{'::'"'::'s'::"ym\":".toList from rfl,
                show ("}":String).toList = ['}'] from rfl]; simp [List.append_assoc]]
      rw [show lit "{\"int\":" _ = none by
            simp only [lit, show ("{\"int\":":String).toList = ['{','"','i','n','t','"',':'] from rfl, litGo,
              show (('{':Char)=='{')=true from by decide, show (('"':Char)=='"')=true from by decide,
              show (('i':Char)=='s')=false from by decide, if_true, Bool.false_eq_true, if_false]]
      simp only []
      rw [show lit "{\"dig\":\"" _ = none by
            simp only [lit, show ("{\"dig\":\"":String).toList = ['{','"','d','i','g','"',':','"'] from rfl, litGo,
              show (('{':Char)=='{')=true from by decide, show (('"':Char)=='"')=true from by decide,
              show (('d':Char)=='s')=false from by decide, if_true, Bool.false_eq_true, if_false]]
      simp only []
      rw [show lit "{\"sym\":" ('{'::'"'::'s'::(("ym\":".toList ++ (toString s).toList) ++ ('}' :: rest)))
            = some ((toString s).toList ++ ('}' :: rest)) by
            rw [show ('{'::'"'::'s'::(("ym\":".toList ++ (toString s).toList) ++ ('}' :: rest)))
                  = ("{\"sym\":":String).toList ++ ((toString s).toList ++ ('}' :: rest)) by
                  rw [show ("{\"sym\":":String).toList = '{'::'"'::'s'::"ym\":".toList from rfl]
                  simp]
            rw [lit_append]]
      simp only []
      rw [parseNat_toString s _ (nd_brace rest)]; simp only []
      rw [show lit "}" ('}' :: rest) = some rest from by
            rw [show ('}'::rest) = ("}":String).toList ++ rest from rfl, lit_append]]
      simp
  | dig d =>
      have hd : d < 2^256 := hwf
      unfold encodeValueW parseValueW
      rw [show (("{\"dig\":\"" ++ toHex32 d ++ "\"}"):String).toList ++ rest
            = '{'::'"'::'d'::(("ig\":\"".toList ++ (toHex32 d).toList) ++ ("\"}".toList ++ rest)) by
            rw [String.toList_append, String.toList_append,
                show ("{\"dig\":\"":String).toList = '{'::'"'::'d'::"ig\":\"".toList from rfl]
            simp [List.append_assoc]]
      rw [show lit "{\"int\":" _ = none by
            simp only [lit, show ("{\"int\":":String).toList = ['{','"','i','n','t','"',':'] from rfl, litGo,
              show (('{':Char)=='{')=true from by decide, show (('"':Char)=='"')=true from by decide,
              show (('i':Char)=='d')=false from by decide, if_true, Bool.false_eq_true, if_false]]
      simp only []
      rw [show lit "{\"dig\":\"" ('{'::'"'::'d'::(("ig\":\"".toList ++ (toHex32 d).toList) ++ ("\"}".toList ++ rest)))
            = some ((toHex32 d).toList ++ ("\"}".toList ++ rest)) by
            rw [show ('{'::'"'::'d'::(("ig\":\"".toList ++ (toHex32 d).toList) ++ ("\"}".toList ++ rest)))
                  = ("{\"dig\":\"":String).toList ++ ((toHex32 d).toList ++ ("\"}".toList ++ rest)) by
                  rw [show ("{\"dig\":\"":String).toList = '{'::'"'::'d'::"ig\":\"".toList from rfl]
                  simp]
            rw [lit_append]]
      simp only []
      rw [parseHex32_toHex32 d ("\"}".toList ++ rest), Nat.mod_eq_of_lt hd]; simp only []
      rw [show lit "\"}" ("\"}".toList ++ rest) = some rest from lit_append "\"}" rest]
      simp

/-! ## §2 — the per-asset `BAL` ledger roundtrip (the CONSERVED MEASURE the executor reads).

`BAL` is the list of `(cell, asset, amount)` triples — the per-asset ledger `execFullForestA`'s
conservation theorem is stated over. Each entry is `[N,N,Z]`; the parser recovers it exactly. This is
the load-bearing FULLY-GENERIC structural roundtrip: ANY balance ledger round-trips (no Wf needed —
ids are `Nat`, amounts `Int`, both total). -/

/-- One `BALENTRY` `[cell,asset,amt]` round-trips. -/
theorem parseBalEntry_encode (c a : Nat) (amt : Int) (rest : PState) :
    parseBalEntry (("[" ++ toString c ++ "," ++ toString a ++ "," ++ toString amt ++ "]").toList ++ rest)
      = some ((c, a, amt), rest) := by
  unfold parseBalEntry
  rw [show (("[" ++ toString c ++ "," ++ toString a ++ "," ++ toString amt ++ "]"):String).toList ++ rest
        = '[' :: ((toString c).toList ++ (',' :: ((toString a).toList ++ (',' :: ((toString amt).toList
            ++ (']' :: rest)))))) by
        simp only [String.toList_append, show ("]":String).toList = [']'] from rfl,
            show ("[":String).toList = ['['] from rfl, show (",":String).toList = [','] from rfl]
        simp [List.append_assoc]]
  rw [show ('[' :: ((toString c).toList ++ (',' :: ((toString a).toList ++ (',' :: ((toString amt).toList
            ++ (']' :: rest)))))))
        = ("[":String).toList ++ ((toString c).toList ++ (',' :: ((toString a).toList
            ++ (',' :: ((toString amt).toList ++ (']' :: rest)))))) from rfl]
  rw [lit_append]; simp only []
  rw [parseNat_toString c _ (nd_comma _)]; simp only []
  rw [show (',' :: ((toString a).toList ++ (',' :: ((toString amt).toList ++ (']' :: rest)))))
        = (",":String).toList ++ ((toString a).toList ++ (',' :: ((toString amt).toList ++ (']' :: rest)))) from rfl]
  rw [lit_append]; simp only []
  rw [parseNat_toString a _ (nd_comma _)]; simp only []
  rw [show (',' :: ((toString amt).toList ++ (']' :: rest)))
        = (",":String).toList ++ ((toString amt).toList ++ (']' :: rest)) from rfl]
  rw [lit_append]; simp only []
  rw [parseInt_toString amt _ (nd_brack rest)]; simp only []
  rw [show lit "]" (']' :: rest) = some rest from by
        rw [show (']'::rest) = ("]":String).toList ++ rest from rfl, lit_append]]
  simp

/-! ## §2b — the DISPATCH toolkit: a TAG literal FAILS fail-closed on a DIFFERENT tag's encoding.

The recursive productions (`Value`, `Authorization`, `FullActionA`, the action-TREE) are all
fail-closed per-tag DISPATCHES: the parser tries `lit TAG₀`, then on `none` tries `lit TAG₁`, …. To
reach arm `J`'s body we must discharge that `lit TAGₖ` FAILS for every EARLIER arm `k < J` when fed
arm `J`'s encoding (which begins with the concrete string `TAGⱼ`). The workhorse is *failure
monotonicity*: if `lit p` already fails on a CONCRETE finite prefix `q`, it fails on `q ++ rest` for
any tail — so each (k, J) obligation reduces to a `decide` over the two SHORT concrete tag strings.
This is what makes the 10-arm and 45-arm case-splits MECHANICAL rather than O(n²) hand-work. -/

/-- **Failure monotonicity for `litGo` (clash form).** If `litGo p q = none` because of a GENUINE
char CLASH — i.e. `litGo q p = none` ALSO fails (so `q` is NOT a prefix of `p`; the failure is a real
mismatch, not `q` simply running out) — then `litGo p (q ++ rest) = none` for ANY tail. Both
directions failing is exactly "neither is a prefix of the other", the precise condition under which
extra bytes can't rescue the mismatch. (For two concrete distinct tag strings, BOTH `litGo` directions
are `decide`-checkable.) -/
theorem litGo_none_mono : ∀ (p q : List Char) (rest : PState),
    litGo p q = none → litGo q p = none → litGo p (q ++ rest) = none := by
  intro p
  induction p with
  | nil => intro q rest h _; simp [litGo] at h
  | cons c cs ih =>
    intro q rest h hsym
    cases q with
    | nil => simp [litGo] at hsym  -- `litGo [] (c::cs) = some _`, contradicting `hsym`
    | cons d ds =>
      simp only [List.cons_append]
      unfold litGo at h hsym ⊢
      by_cases hcd : (c == d) = true
      · rw [if_pos hcd] at h ⊢
        have hdc : (d == c) = true := by rw [beq_iff_eq] at hcd ⊢; exact hcd.symm
        rw [if_pos hdc] at hsym
        exact ih ds rest h hsym
      · rw [if_neg hcd]

/-- The dispatch obligation in its USABLE form: `tag` (the literal the parser is currently trying) FAILS
on input that BEGINS with the concrete string `b` (a DIFFERENT arm's tag), for any tail. Both `litGo`
directions are concrete; the two hypotheses are closed by `decide`. -/
theorem lit_ne_pre (tag b : String) (rest : PState)
    (h : litGo tag.toList b.toList = none)
    (hsym : litGo b.toList tag.toList = none) :
    lit tag (b.toList ++ rest) = none := by
  unfold lit; exact litGo_none_mono tag.toList b.toList rest h hsym

/-! ## §3 — the HEADLINE FILL-J assurances (the TCB-removing roundtrip facts).

These are the load-bearing parse∘encode theorems the wholesale swap rests on: a symmetric codec bug
(encoder + decoder agree on a WRONG grammar) passes the differential silently — only these theorems,
pinning the decoder as the genuine left-inverse of the encoder, catch it. All are NON-VACUOUS (each
states real teeth; the digest one fails on a `2^256`-wrap; the witnesses below show satisfiability). -/

/-- **FILL J (digest field).** The `[u8;32]` digest round-trips LOSSLESSLY on the full 256-bit range —
the most subtle silent-bug surface (a width truncation passes the differential). -/
theorem fillJ_digest (d : Nat) (hd : d < 2 ^ 256) (rest : PState) :
    parseDig ((encDig d).toList ++ rest) = some (d, rest) := parseDig_encDig d rest hd

/-- **FILL J (balance).** EVERY signed balance round-trips (the `i128` amount; a sign-handling bug is
caught). NON-VACUOUS over all of `ℤ` (both witnesses below are real). -/
theorem fillJ_amount (i : Int) (rest : PState)
    (hrest : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    parseInt ((toString i).toList ++ rest) = some (i, rest) := parseInt_toString i rest hrest

/-- **FILL J (scalar value leaf).** Every `int`/`dig`/`sym` `Value` leaf round-trips (the ledger reads
exactly these). -/
theorem fillJ_value_scalar (v : Value) (rest : PState) (hwf : WfValue v)
    (hscalar : ∀ fs, v ≠ .record fs) (fuel : Nat) :
    parseValueW (fuel+1) ((encodeValueW v).toList ++ rest) = some (v, rest) :=
  parseValueW_scalar fuel v rest hwf hscalar

/-- **FILL J (per-asset ledger entry).** Every conserved-measure entry round-trips (fully generic). -/
theorem fillJ_bal_entry (c a : Nat) (amt : Int) (rest : PState) :
    parseBalEntry (("[" ++ toString c ++ "," ++ toString a ++ "," ++ toString amt ++ "]").toList ++ rest)
      = some ((c, a, amt), rest) := parseBalEntry_encode c a amt rest

/-! ### NON-VACUITY witnesses (the teeth are satisfiable AND the bound is real). -/

-- The digest field is the identity for a non-trivial value < 2^256 (a 5-byte stand-in would differ):
example : parseDig ((encDig 6599973602).toList ++ ['x']) = some (6599973602, ['x']) :=
  fillJ_digest 6599973602 (by norm_num) ['x']
-- ...and the digest roundtrip WRAPS at 2^256 (so the `< 2^256` hypothesis is REAL teeth, not vacuous):
example : ofHex32 (toHex32 (2 ^ 256)).toList = some 0 := by rw [ofHex32_toHex32]; norm_num
-- A NEGATIVE balance round-trips (the sign is load-bearing — a debit is a negative delta):
example : parseInt ((toString (-42 : Int)).toList ++ ['}']) = some (-42, ['}']) :=
  fillJ_amount (-42) ['}'] (Or.inr ⟨'}', [], rfl, by decide⟩)
-- A digest VALUE leaf round-trips (carrying a 256-bit content hash):
example : parseValueW 5 ((encodeValueW (.dig 255)).toList ++ ['x'])
            = some (.dig 255, ['x']) :=
  fillJ_value_scalar (.dig 255) ['x'] (show (255:Nat) < 2^256 by norm_num) (by intro fs h; cases h) 4

/-! ## §5 — the RECURSIVE `Value` / `FIELDS` production (FILL-J production (a)).

This COMPLETES the scalar leaf into the FULL `parseValueW ∘ encodeValueW = id` on the WHOLE `Value`
algebra — including the `record` arm, which is mutually recursive with the fields list (a fold of
`["name",valueW]` pairs). The fuel is threaded as the structural `valueSize`/`fieldsSize` measure; the
*fuel-adequacy* obligation is that this measure DOMINATES the parse depth, so the fail-closed `fuel=0`
branch is unreachable on well-formed input. We prove the pair by mutual structural induction, mirroring
the `parseValueW`/`parseFieldsLoopW` recursion exactly: lit-the-tag, subparse, close-the-delimiter.

`WfValue` (§1) pins the codec's boundary: digests `< 2^256` and field names escape-free. Both are
satisfied by the demo values (non-vacuous) and load-bearing (the digest wrap / a `"`-bearing name are
genuine counterexamples). -/

/-- The three EARLIER `Value` tags (`int`/`dig`/`sym`) all FAIL on a `{"rec":…` prefix — the dispatch
discharge for the `record` arm. -/
private theorem value_tags_fail_on_rec (rest : PState) :
    lit "{\"int\":" (("{\"rec\":" : String).toList ++ rest) = none
    ∧ lit "{\"dig\":\"" (("{\"rec\":" : String).toList ++ rest) = none
    ∧ lit "{\"sym\":" (("{\"rec\":" : String).toList ++ rest) = none := by
  refine ⟨?_, ?_, ?_⟩
  · exact lit_ne_pre "{\"int\":" "{\"rec\":" rest (by decide) (by decide)
  · exact lit_ne_pre "{\"dig\":\"" "{\"rec\":" rest (by decide) (by decide)
  · exact lit_ne_pre "{\"sym\":" "{\"rec\":" rest (by decide) (by decide)

/-- Rebracket the `int` value's encoding into `lit`-then-`parseInt`-then-`}` shape. -/
private theorem encInt_shape (i : Int) (rest : PState) :
    (encodeValueW (.int i)).toList ++ rest
      = ("{\"int\":":String).toList ++ ((toString i).toList ++ ('}' :: rest)) := by
  unfold encodeValueW
  rw [String.toList_append, String.toList_append, show ("}":String).toList = ['}'] from rfl]
  simp [List.append_assoc]

/-- `lit "}" ('}' :: rest) = some rest` — the closing-brace consume. -/
private theorem lit_brace (rest : PState) : lit "}" ('}' :: rest) = some rest := by
  rw [show ('}'::rest) = ("}":String).toList ++ rest from rfl, lit_append]

/-- `lit "]" (']' :: rest) = some rest` — the closing-bracket consume. -/
private theorem lit_brack (rest : PState) : lit "]" (']' :: rest) = some rest := by
  rw [show (']'::rest) = ("]":String).toList ++ rest from rfl, lit_append]

/-- `lit "," (',' :: rest) = some rest`. -/
private theorem lit_commaC (rest : PState) : lit "," (',' :: rest) = some rest := by
  rw [show (','::rest) = (",":String).toList ++ rest from rfl, lit_append]

/-- Rebracket a NON-EMPTY fields array's encoding `[FIELD ++ TAIL ++ ]` into open-`[`-then-body form. -/
private theorem encFieldsW_cons_shape (n : FieldName) (v : Value) (gs : List (FieldName × Value)) (rest : PState) :
    (encodeFieldsW ((n, v) :: gs)).toList ++ rest
      = '[' :: ((("[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"):String).toList
          ++ ((encodeFieldsTailW gs).toList ++ (']' :: rest))) := by
  unfold encodeFieldsW
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

/-- Rebracket a NON-EMPTY fields TAIL `,FIELD ++ TAIL` into comma-then-field-then-tail form. -/
private theorem encFieldsTailW_cons_shape (n2 : FieldName) (v2 : Value) (gs2 : List (FieldName × Value)) (rest : PState) :
    (encodeFieldsTailW ((n2, v2) :: gs2)).toList ++ rest
      = ',' :: ((("[\"" ++ jsonEscape n2 ++ "\"," ++ encodeValueW v2 ++ "]"):String).toList
          ++ ((encodeFieldsTailW gs2).toList ++ rest)) := by
  rw [show encodeFieldsTailW ((n2, v2) :: gs2)
        = ",[\"" ++ jsonEscape n2 ++ "\"," ++ encodeValueW v2 ++ "]" ++ encodeFieldsTailW gs2 from rfl]
  simp only [String.toList_append, show (",[\"":String).toList = ',' :: ("[\"":String).toList from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

/-! ### The combined `Value`/`FIELDS` roundtrip, proved by induction on FUEL with the value case-split
inside. Fuel is bounded BELOW by the structural `valueSize`/`fieldsSize` (the *fuel-adequacy*); the
`≥` form gives fuel-MONOTONICITY for free (any sufficient fuel works), which is exactly what the loop's
`parseValueW fuel` sub-call needs. -/

/-- The mutual roundtrip statement at a given fuel: BOTH the value parser AND the fields loop recover
their argument whenever the fuel meets the structural bound. The fields clause is stated over the LOOP
BODY (post opening-`[`): the first field, the comma-prefixed tail of the rest, then the closing `]`. -/
private def ValueGoal (fuel : Nat) : Prop :=
  (∀ (v : Value) (rest : PState), WfValue v → valueSize v ≤ fuel →
      parseValueW fuel ((encodeValueW v).toList ++ rest) = some (v, rest))
  ∧ (∀ (fs : List (FieldName × Value)) (rest : PState), WfFields fs → fieldsSize fs ≤ fuel →
      parseFieldsW fuel ((encodeFieldsW fs).toList ++ rest) = some (fs, rest))
  ∧ (∀ (fs : List (FieldName × Value)) (rest : PState), WfFields fs → fs ≠ [] → fieldsSize fs ≤ fuel →
      parseFieldsLoopW fuel
        ((("[\"" ++ jsonEscape (fs.headD default).1 ++ "\"," ++ encodeValueW (fs.headD default).2 ++ "]"):String).toList
          ++ ((encodeFieldsTailW fs.tail).toList ++ (']' :: rest))) = some (fs, rest))

/-- **The combined `Value`/`FIELDS` fuel-adequate roundtrip.** By STRONG induction on fuel: each
recursive sub-call lands at strictly-smaller fuel, so the IH applies. This is the engine; the public
`parseValueW_roundtrip` / `parseFieldsW_roundtrip` below unwrap it. -/
private theorem valueGoal_all : ∀ fuel, ValueGoal fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    -- FIRST establish the LOOP clause (depends only on IH at strictly-smaller fuel), then the
    -- fields-W and value clauses can re-use it at the SAME fuel.
    have hloop : ∀ (fs : List (FieldName × Value)) (rest : PState), WfFields fs → fs ≠ [] → fieldsSize fs ≤ fuel →
        parseFieldsLoopW fuel
          ((("[\"" ++ jsonEscape (fs.headD default).1 ++ "\"," ++ encodeValueW (fs.headD default).2 ++ "]"):String).toList
            ++ ((encodeFieldsTailW fs.tail).toList ++ (']' :: rest))) = some (fs, rest) := by
      intro fs rest hwf hne hsz
      match fs, hwf, hne, hsz with
      | (n, v) :: gs, hwf, _, hsz =>
        obtain ⟨hn, hv, hgs⟩ := hwf
        have hszsplit : fieldsSize ((n,v)::gs) = 1 + valueSize v + fieldsSize gs := by simp only [fieldsSize]
        have hfpos : 0 < fuel := by rw [hszsplit] at hsz; omega
        obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
        have hsz' : 1 + valueSize v + fieldsSize gs ≤ fuel' + 1 := by rw [hszsplit] at hsz; exact hsz
        have hvfuel : valueSize v ≤ fuel' := by omega
        have hgsfuel : fieldsSize gs ≤ fuel' := by omega
        simp only [List.headD, List.tail]
        unfold parseFieldsLoopW
        rw [show (("[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"):String).toList
                  ++ ((encodeFieldsTailW gs).toList ++ (']' :: rest))
              = ("[":String).toList ++ (('"' :: (jsonEscape n).toList) ++ ('"' :: (','
                  :: ((encodeValueW v).toList ++ (']' :: ((encodeFieldsTailW gs).toList ++ (']' :: rest)))))) ) by
              simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
                show ("\"":String).toList = ['"'] from rfl, show (",":String).toList = [','] from rfl,
                show ("]":String).toList = [']'] from rfl]
              simp [List.append_assoc]]
        rw [lit_append]; simp only []
        rw [parseStr_clean n (',' :: ((encodeValueW v).toList ++ (']' :: ((encodeFieldsTailW gs).toList ++ (']' :: rest))))) hn]
        simp only []
        rw [lit_commaC]; simp only []
        have hval := (IH fuel' (by omega)).1 v (']' :: ((encodeFieldsTailW gs).toList ++ (']' :: rest))) hv hvfuel
        rw [hval]; simp only []
        rw [lit_brack]; simp only []
        match gs, hgs, hgsfuel with
        | [], _, _ =>
            show (match lit "," ((encodeFieldsTailW ([]:List (FieldName × Value))).toList ++ (']' :: rest)) with
                  | some r5 => match parseFieldsLoopW fuel' r5 with
                               | some (rest', r6) => some ((n, v) :: rest', r6)
                               | none => none
                  | none => match lit "]" ((encodeFieldsTailW ([]:List (FieldName × Value))).toList ++ (']' :: rest)) with
                            | some r6 => some ([(n, v)], r6)
                            | none => none) = _
            simp only [encodeFieldsTailW, show ("":String).toList = [] from rfl, List.nil_append]
            rw [show lit "," (']' :: rest) = none from by
                  rw [show (']'::rest) = ("]":String).toList ++ rest from rfl]
                  exact lit_ne_pre "," "]" rest (by decide) (by decide)]
            simp only []
            rw [lit_brack]
        | (n2, v2) :: gs2, hgs', hgsfuel' =>
            obtain ⟨hn2, hv2, hgs2⟩ := hgs'
            rw [encFieldsTailW_cons_shape n2 v2 gs2 (']' :: rest)]
            rw [show (',' :: ((("[\"" ++ jsonEscape n2 ++ "\"," ++ encodeValueW v2 ++ "]"):String).toList
                      ++ ((encodeFieldsTailW gs2).toList ++ (']' :: rest))))
                  = (",":String).toList ++ ((("[\"" ++ jsonEscape n2 ++ "\"," ++ encodeValueW v2 ++ "]"):String).toList
                      ++ ((encodeFieldsTailW gs2).toList ++ (']' :: rest))) from rfl]
            rw [lit_append]; simp only []
            -- the loop RECURSES at the DECREMENTED fuel `fuel'` (see `parseFieldsLoopW`); the IH at
            -- `fuel' < fuel'+1` supplies the loop clause of `ValueGoal fuel'`:
            have hrec := (IH fuel' (by omega)).2.2 ((n2,v2)::gs2) rest ⟨hn2, hv2, hgs2⟩ (by simp) hgsfuel'
            simp only [List.headD, List.tail] at hrec
            rw [hrec]
    -- now the FIELDS-W clause (`[]` vs `[FIELD...]`), reducing to `hloop`:
    have hfieldsW : ∀ (fs : List (FieldName × Value)) (rest : PState), WfFields fs → fieldsSize fs ≤ fuel →
        parseFieldsW fuel ((encodeFieldsW fs).toList ++ rest) = some (fs, rest) := by
      intro fs rest hwf hsz
      match fs with
      | [] =>
          unfold encodeFieldsW parseFieldsW
          rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
      | (n, v) :: gs =>
          unfold parseFieldsW
          rw [encFieldsW_cons_shape n v gs rest]
          -- the body is `'[' :: '[' :: '"' :: …` (the field's own open bracket follows): so `lit "[]"`
          -- mismatches at the 2nd char (`[` ≠ `]`) — fail-closed via the `[[`-prefix dispatch:
          have hbody : ('[' :: ((("[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"):String).toList
                ++ ((encodeFieldsTailW gs).toList ++ (']' :: rest))))
              = ("[[":String).toList ++ (('"' :: (jsonEscape n).toList ++ '"' :: ',' :: (encodeValueW v).toList)
                  ++ (']' :: ((encodeFieldsTailW gs).toList ++ (']' :: rest)))) := by
            simp only [String.toList_append, show ("[[":String).toList = ['[','['] from rfl,
              show ("[\"":String).toList = ['[','"'] from rfl, show ("\",":String).toList = ['"',','] from rfl,
              show ("]":String).toList = [']'] from rfl, show ("\"":String).toList = ['"'] from rfl,
              show (",":String).toList = [','] from rfl]
            simp [List.append_assoc]
          rw [hbody]
          have hlitempty := lit_ne_pre "[]" "[["
              (('"' :: (jsonEscape n).toList ++ '"' :: ',' :: (encodeValueW v).toList)
                  ++ (']' :: ((encodeFieldsTailW gs).toList ++ (']' :: rest))))
              (by decide) (by decide)
          rw [hlitempty]; simp only []
          rw [← hbody]
          rw [show ('[' :: ((("[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"):String).toList
                    ++ ((encodeFieldsTailW gs).toList ++ (']' :: rest))))
                = ("[":String).toList ++ ((("[\"" ++ jsonEscape n ++ "\"," ++ encodeValueW v ++ "]"):String).toList
                    ++ ((encodeFieldsTailW gs).toList ++ (']' :: rest))) from rfl]
          rw [lit_append]; simp only []
          have := hloop ((n,v)::gs) rest hwf (by simp) hsz
          simp only [List.headD, List.tail] at this
          exact this
    refine ⟨?_, hfieldsW, hloop⟩
    -- the VALUE clause, reducing the record arm to `hfieldsW`:
    intro v rest hwf hsz
    have hfpos : 0 < fuel := lt_of_lt_of_le (by cases v <;> simp [valueSize] <;> omega) hsz
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    match v with
      | .int i =>
          unfold parseValueW
          rw [encInt_shape i rest, lit_append]; simp only []
          rw [parseInt_toString i _ (nd_brace rest)]; simp only []
          rw [lit_brace rest]; simp
      | .sym s =>
          exact parseValueW_scalar fuel' (.sym s) rest hwf (by intro fs h; cases h)
      | .dig d =>
          exact parseValueW_scalar fuel' (.dig d) rest hwf (by intro fs h; cases h)
      | .record fs =>
          have hwff : WfFields fs := hwf
          have hfssz : fieldsSize fs ≤ fuel' := by simp only [valueSize] at hsz; omega
          unfold encodeValueW parseValueW
          obtain ⟨h1, h2, h3⟩ := value_tags_fail_on_rec ((encodeFieldsW fs).toList ++ ('}' :: rest))
          rw [show (("{\"rec\":" ++ encodeFieldsW fs ++ "}"):String).toList ++ rest
                = ("{\"rec\":":String).toList ++ ((encodeFieldsW fs).toList ++ ('}' :: rest)) by
                rw [String.toList_append, String.toList_append,
                    show ("}":String).toList = ['}'] from rfl]; simp [List.append_assoc]]
          rw [h1]; simp only []
          rw [h2]; simp only []
          rw [h3]; simp only []
          rw [lit_append]; simp only []
          -- the parser calls `parseFieldsW fuel'` (the DECREMENTED fuel); use the IH's fields clause:
          rw [(IH fuel' (by omega)).2.1 fs ('}' :: rest) hwff hfssz]; simp only []
          rw [lit_brace rest]; rfl

/-- **FILL J production (a): the FULL `Value`/`record` roundtrip.** Every reachable `Value` —
including the recursive `record`/fields fold — round-trips through `encodeValueW`/`parseValueW`, given
enough fuel (`valueSize v`, the structural depth bound). The `record` arm was the missing piece beyond
the scalar leaf; this REMOVES the whole `Value` algebra from the codec TCB. -/
theorem parseValueW_roundtrip (v : Value) (rest : PState) (hwf : WfValue v) (fuel : Nat)
    (hfuel : valueSize v ≤ fuel) :
    parseValueW fuel ((encodeValueW v).toList ++ rest) = some (v, rest) :=
  (valueGoal_all fuel).1 v rest hwf hfuel

/-- **The `FIELDS` array roundtrip** (`parseFieldsW ∘ encodeFieldsW = id`) — the record body, empty or
non-empty, given fuel ≥ `fieldsSize fs`. -/
theorem parseFieldsW_roundtrip (fs : List (FieldName × Value)) (rest : PState) (hwf : WfFields fs)
    (fuel : Nat) (hfuel : fieldsSize fs ≤ fuel) :
    parseFieldsW fuel ((encodeFieldsW fs).toList ++ rest) = some (fs, rest) :=
  (valueGoal_all fuel).2.1 fs rest hwf hfuel

/-! ### NON-VACUITY witnesses for the record recursion (the teeth are satisfiable AND non-trivial). -/

-- A NESTED record (record-inside-record, with a digest field) round-trips — the recursion is real
-- (the `record` arm calls back into `parseFieldsW`, which calls back into `parseValueW`):
private def witNestedRec : Value :=
  .record [("a", .int 7), ("b", .record [("h", .dig 255), ("k", .sym 3)])]

private theorem witNestedRec_wf : WfValue witNestedRec := by
  show WfFields [("a", .int 7), ("b", .record [("h", .dig 255), ("k", .sym 3)])]
  refine ⟨?_, trivial, ?_, ?_, trivial⟩
  · intro c h; fin_cases h <;> decide   -- name "a" escape-free
  · intro c h; fin_cases h <;> decide   -- name "b" escape-free
  · -- WfValue (.record [("h", .dig 255), ("k", .sym 3)])
    show WfFields [("h", .dig 255), ("k", .sym 3)]
    refine ⟨?_, show (255:Nat) < 2^256 by norm_num, ?_, trivial, trivial⟩
    · intro c h; fin_cases h <;> decide  -- name "h"
    · intro c h; fin_cases h <;> decide  -- name "k"

example : parseValueW 10 ((encodeValueW witNestedRec).toList ++ ['x']) = some (witNestedRec, ['x']) :=
  parseValueW_roundtrip witNestedRec ['x'] witNestedRec_wf 10 (by unfold witNestedRec; decide)

/-! ## §6 — the `Authorization` (WHO) decoder roundtrip (FILL-J production (b): the 10-variant sum +
the recursive `oneOf` candidate list).

The WHO decoder is the SECURITY-CRITICAL wire layer — a symmetric codec bug here forges authority
silently past the differential (the encoder and decoder agree on a wrong grammar, so a round-trip
`#eval` passes; only a parse∘encode THEOREM, pinning the decoder as the genuine left-inverse, catches
it). This §6 removes `parseAuthW` from the Lean-side TCB.

It mirrors §5's `valueGoal_all` exactly: a bundled mutual goal (`parseAuthW` / `parseAuthListW` / the
loop body), strong-induction on fuel, the recursive `oneOf` arm threading fuel through the candidate
list as `record` threads it through the fields. The 10-arm fail-closed DISPATCH is discharged
MECHANICALLY by `lit_ne_pre` (failure-monotonicity over the two concrete tag strings); the per-arm
payload WALK is three tactic macros. `WfAuth` pins the codec boundary (every digest `< 2^256`, the
`[u8;32]` width), recursively over `oneOf`. -/

/-! ### §6a — the per-arm tactic combinators (the payload walk + the fail-closed dispatch).

`lit_ok` consumes the literal at the head; `lit_fail k b` discharges a WRONG-tag `lit k` on input that
begins with the concrete tag `b` (both `decide`-checkable); `dig_ok h` consumes a `"H64"` digest field
(`h : d < 2^256`); `nat_ok` consumes a decimal number whose post-byte is `,`/`]}`/`]` (the three
non-digit closers, tried in turn). After the big `String.toList_append`/`List.append_assoc`
right-association, exactly one of these fires per parser step — turning the 10×(dispatch+walk) into a
mechanical script rather than O(n²) hand-work. -/

/-- A `,`-led closer (after right-association the byte after a number is this) is non-digit. -/
private theorem nd_litComma (X : PState) :
    ((",":String).toList ++ X = [] ∨ ∃ c rs, (",":String).toList ++ X = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨',', X, rfl, by decide⟩
/-- A `]}`-led closer is non-digit. -/
private theorem nd_litClose (X : PState) :
    (("]}":String).toList ++ X = [] ∨ ∃ c rs, ("]}":String).toList ++ X = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨']', '}' :: X, rfl, by decide⟩
/-- A `]`-led closer is non-digit. -/
private theorem nd_litBrack (X : PState) :
    (("]":String).toList ++ X = [] ∨ ∃ c rs, ("]":String).toList ++ X = c :: rs ∧ c.isDigit = false) :=
  Or.inr ⟨']', X, rfl, by decide⟩

/-- Consume the literal at the head and reduce the resulting `some`-match. -/
local macro "lit_ok" : tactic => `(tactic| (rw [lit_append]; try simp only []))
/-- Discharge a WRONG-tag dispatch: `lit k` fails on input beginning with the concrete tag `b`. -/
local macro "lit_fail" k:str b:str : tactic =>
  `(tactic| (rw [lit_ne_pre $k $b _ (by decide) (by decide)]; simp only []))
/-- Consume a `"H64"` digest field (`h : d < 2^256`) and reduce the `some`-match. -/
local macro "dig_ok" h:term : tactic => `(tactic| (rw [parseDig_encDig _ _ $h]; simp only []))
/-- Consume a decimal number whose post-byte is a non-digit closer (`,` / `]}` / `]`). -/
local macro "nat_ok" : tactic =>
  `(tactic| ((first
    | rw [parseNat_toString _ _ (nd_litComma _)]
    | rw [parseNat_toString _ _ (nd_litClose _)]
    | rw [parseNat_toString _ _ (nd_litBrack _)]); simp only []))

/-! ### §6b — well-formedness and the structural fuel measure (mutual over `oneOf`). -/

/-! Well-formed `AuthW`: every digest field `< 2^256` (the `[u8;32]` width), recursively over `oneOf`. -/
mutual
/-- Well-formed `AuthW`: every digest field `< 2^256` (the `[u8;32]` width), recursively over `oneOf`. -/
def WfAuth : AuthW → Prop
  | .signature pk _            => pk < 2 ^ 256
  | .proof vk _ _ _            => vk < 2 ^ 256
  | .breadstuff _              => True
  | .bearer dm _ _             => dm < 2 ^ 256
  | .unchecked                 => True
  | .capTpDelivered im sm _ _  => im < 2 ^ 256 ∧ sm < 2 ^ 256
  | .custom st _               => st < 2 ^ 256
  | .oneOf cands _             => WfAuthList cands
  | .stealth otp eph _         => otp < 2 ^ 256 ∧ eph < 2 ^ 256
  | .token key _               => key < 2 ^ 256
def WfAuthList : List AuthW → Prop
  | []      => True
  | a :: as => WfAuth a ∧ WfAuthList as
end

/-! Structural size (the fuel measure): `oneOf` is `1 + Σ candidates`; every other arm is `1`. -/
mutual
/-- Structural size (the fuel measure): `oneOf` is `1 + Σ candidates`; every other arm is `1`. -/
def authSize : AuthW → Nat
  | .oneOf cands _ => 1 + authListSize cands
  | _              => 1
def authListSize : List AuthW → Nat
  | []      => 0
  | a :: as => 1 + authSize a + authListSize as
end

/-! ### §6c — the 9 NON-recursive arms (no induction; the dispatch+walk script per arm).

This standalone helper closes every arm EXCEPT `oneOf`; the bundled `authGoal_all` (§6e) delegates its
9 flat cases straight to here, so the recursive proof carries no duplication. -/

/-- **`parseAuthW` inverts `encodeAuthW` on the 9 non-recursive arms.** Each is a fixed dispatch
(earlier tags fail fail-closed) then a fixed payload walk (digest/number fields, closer). -/
theorem parseAuthW_flat (a : AuthW) (rest : PState) (fuel : Nat)
    (hwf : WfAuth a) (hno : ∀ cs i, a ≠ .oneOf cs i) :
    parseAuthW (fuel + 1) ((encodeAuthW a).toList ++ rest) = some (a, rest) := by
  cases a with
  | oneOf cs i => exact absurd rfl (hno cs i)
  | signature pk sig =>
      have hpk : pk < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_ok; dig_ok hpk; lit_ok; nat_ok; lit_ok; rfl
  | proof vk pf ba br =>
      have hvk : vk < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"pf\":["
      lit_ok; dig_ok hvk; lit_ok; nat_ok; lit_ok; nat_ok; lit_ok; nat_ok; lit_ok; rfl
  | breadstuff tok =>
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"bread\":["
      lit_fail "{\"pf\":[" "{\"bread\":["
      lit_ok; nat_ok; lit_ok; rfl
  | bearer dm ds stark =>
      have hdm : dm < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"bearer\":["
      lit_fail "{\"pf\":[" "{\"bearer\":["
      lit_fail "{\"bread\":[" "{\"bearer\":["
      lit_ok; dig_ok hdm; lit_ok; nat_ok; lit_ok
      cases stark with
      | true =>
          rw [show ((if true then "1" else "0" : String)) = "1" from rfl,
              show (("1":String).toList) = (toString (1:Nat)).toList from rfl,
              parseNat_toString 1 _ (nd_litClose _)]
          simp only []
          rw [if_pos (by norm_num : (1:Nat) ≤ 1)]
          lit_ok; rfl
      | false =>
          rw [show ((if false then "1" else "0" : String)) = "0" from rfl,
              show (("0":String).toList) = (toString (0:Nat)).toList from rfl,
              parseNat_toString 0 _ (nd_litClose _)]
          simp only []
          rw [if_pos (by norm_num : (0:Nat) ≤ 1)]
          lit_ok; rfl
  | unchecked =>
      unfold parseAuthW
      simp only [encodeAuthW]
      lit_fail "{\"sig\":[" "{\"unchecked\":0}"
      lit_fail "{\"pf\":[" "{\"unchecked\":0}"
      lit_fail "{\"bread\":[" "{\"unchecked\":0}"
      lit_fail "{\"bearer\":[" "{\"unchecked\":0}"
      lit_ok
  | capTpDelivered im sm isig ss =>
      obtain ⟨him, hsm⟩ : im < 2 ^ 256 ∧ sm < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"captp\":["
      lit_fail "{\"pf\":[" "{\"captp\":["
      lit_fail "{\"bread\":[" "{\"captp\":["
      lit_fail "{\"bearer\":[" "{\"captp\":["
      lit_fail "{\"unchecked\":0}" "{\"captp\":["
      lit_ok; dig_ok him; lit_ok; dig_ok hsm; lit_ok; nat_ok; lit_ok; nat_ok; lit_ok; rfl
  | custom st pf =>
      have hst : st < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"custom\":["
      lit_fail "{\"pf\":[" "{\"custom\":["
      lit_fail "{\"bread\":[" "{\"custom\":["
      lit_fail "{\"bearer\":[" "{\"custom\":["
      lit_fail "{\"unchecked\":0}" "{\"custom\":["
      lit_fail "{\"captp\":[" "{\"custom\":["
      lit_ok; dig_ok hst; lit_ok; nat_ok; lit_ok; rfl
  | stealth otp eph sig =>
      obtain ⟨hotp, heph⟩ : otp < 2 ^ 256 ∧ eph < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"stealth\":["
      lit_fail "{\"pf\":[" "{\"stealth\":["
      lit_fail "{\"bread\":[" "{\"stealth\":["
      lit_fail "{\"bearer\":[" "{\"stealth\":["
      lit_fail "{\"unchecked\":0}" "{\"stealth\":["
      lit_fail "{\"captp\":[" "{\"stealth\":["
      lit_fail "{\"custom\":[" "{\"stealth\":["
      lit_fail "{\"oneof\":[" "{\"stealth\":["
      lit_ok; dig_ok hotp; lit_ok; dig_ok heph; lit_ok; nat_ok; lit_ok; rfl
  | token key sig =>
      have hkey : key < 2 ^ 256 := hwf
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"token\":["
      lit_fail "{\"pf\":[" "{\"token\":["
      lit_fail "{\"bread\":[" "{\"token\":["
      lit_fail "{\"bearer\":[" "{\"token\":["
      lit_fail "{\"unchecked\":0}" "{\"token\":["
      lit_fail "{\"captp\":[" "{\"token\":["
      lit_fail "{\"custom\":[" "{\"token\":["
      lit_fail "{\"oneof\":[" "{\"token\":["
      lit_fail "{\"stealth\":[" "{\"token\":["
      lit_ok; dig_ok hkey; lit_ok; nat_ok; lit_ok; rfl

/-! ### §6d — the candidate-list encoder shape (normalizing the `foldl` into peelable cons form).

`encodeAuthListW`'s tail is a left-`foldl` accumulator (FFI.lean:1384), which does NOT syntactically
expose the `","`-prefixed head the cons-recursive `parseAuthLoopW` peels. So — unlike §5, whose
`encodeFieldsTailW` was already cons-recursive at the FFI site — we must NORMALIZE the fold. The
accumulator-pull-out lemma (`foldl_authtail`) turns it into the clean `',' :: enc b ++ tail` shape. This
is the one genuinely-new structural lemma with no §5 analogue. -/

/-- Every `encodeAuthW` arm opens with `'{'` — the head char that makes `lit "[]"` fail on a `[{`-led
list body. (`String ++` is opaque to defeq, so the head is exposed via `String.toList_append` + a
`decide` on the concrete tag literal — the same `decide`-evaluates-`toList` route the dispatch uses.) -/
private theorem encodeAuthW_head (a : AuthW) : ∃ t, (encodeAuthW a).toList = '{' :: t := by
  cases a <;> exact ⟨_, by
    simp only [encodeAuthW, String.toList_append, List.cons_append,
      show ("{\"sig\":[":String).toList = '{' :: "\"sig\":[".toList from by decide,
      show ("{\"pf\":[":String).toList = '{' :: "\"pf\":[".toList from by decide,
      show ("{\"bread\":[":String).toList = '{' :: "\"bread\":[".toList from by decide,
      show ("{\"bearer\":[":String).toList = '{' :: "\"bearer\":[".toList from by decide,
      show ("{\"unchecked\":0}":String).toList = '{' :: "\"unchecked\":0}".toList from by decide,
      show ("{\"captp\":[":String).toList = '{' :: "\"captp\":[".toList from by decide,
      show ("{\"custom\":[":String).toList = '{' :: "\"custom\":[".toList from by decide,
      show ("{\"oneof\":[":String).toList = '{' :: "\"oneof\":[".toList from by decide,
      show ("{\"stealth\":[":String).toList = '{' :: "\"stealth\":[".toList from by decide,
      show ("{\"token\":[":String).toList = '{' :: "\"token\":[".toList from by decide]
    rfl⟩

/-- The `oneOf` candidate-list TAIL encoder (the `foldl` body, named for the cons-recursion). -/
private def encodeAuthTailW (as : List AuthW) : String :=
  as.foldl (fun acc x => acc ++ "," ++ encodeAuthW x) ""

/-- **The accumulator pulls OUT of the tail fold** (the standard `foldl`-with-`++` factoring) — proved
at the `List Char` level (`String` is not a `simp`-known free monoid). -/
private theorem foldl_authtail (as : List AuthW) : ∀ (acc : String),
    as.foldl (fun s x => s ++ "," ++ encodeAuthW x) acc
      = acc ++ as.foldl (fun s x => s ++ "," ++ encodeAuthW x) "" := by
  induction as with
  | nil =>
      intro acc
      apply String.toList_inj.mp
      simp
  | cons b bs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeAuthW b), ih ("" ++ "," ++ encodeAuthW b)]
      apply String.toList_inj.mp
      simp [String.toList_append, List.append_assoc]

/-- Rebracket a NON-EMPTY candidate TAIL `,AUTH ++ TAIL` into comma-then-auth-then-tail (peelable). -/
private theorem encAuthTailW_cons_shape (b : AuthW) (bs : List AuthW) (rest : PState) :
    (encodeAuthTailW (b :: bs)).toList ++ rest
      = ',' :: ((encodeAuthW b).toList ++ ((encodeAuthTailW bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeAuthTailW (b :: bs)
                    = ("" ++ "," ++ encodeAuthW b) ++ encodeAuthTailW bs from by
                  show (b :: bs).foldl (fun s x => s ++ "," ++ encodeAuthW x) "" = _
                  rw [List.foldl_cons]; exact foldl_authtail bs ("" ++ "," ++ encodeAuthW b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

/-- Rebracket a NON-EMPTY candidate LIST `[AUTH ++ TAIL ++ ]` into open-`[`-then-body form. -/
private theorem encAuthListW_cons_shape (a : AuthW) (as : List AuthW) (rest : PState) :
    (encodeAuthListW (a :: as)).toList ++ rest
      = '[' :: ((encodeAuthW a).toList ++ ((encodeAuthTailW as).toList ++ (']' :: rest))) := by
  simp only [encodeAuthListW]
  rw [show (as.foldl (fun acc x => acc ++ "," ++ encodeAuthW x) "") = encodeAuthTailW as from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

/-! ### §6e — the bundled fuel-adequate roundtrip (`parseAuthW`/`parseAuthListW`/loop, by strong
induction on fuel). Mirrors §5's `valueGoal_all`: establish the LOOP clause (depends on the IH at
strictly-smaller fuel), then the LIST clause re-uses it at the same fuel, then the AUTH clause delegates
its 9 flat arms to `parseAuthW_flat` and routes `oneOf` through the LIST clause at decremented fuel. -/

/-- The bundled mutual goal at a given fuel: the auth parser, the list parser, and the loop body all
recover their argument whenever the fuel meets the structural `authSize`/`authListSize` bound. -/
private def AuthGoal (fuel : Nat) : Prop :=
  (∀ (a : AuthW) (rest : PState), WfAuth a → authSize a ≤ fuel →
      parseAuthW fuel ((encodeAuthW a).toList ++ rest) = some (a, rest))
  ∧ (∀ (as : List AuthW) (rest : PState), WfAuthList as → authListSize as ≤ fuel →
      parseAuthListW fuel ((encodeAuthListW as).toList ++ rest) = some (as, rest))
  ∧ (∀ (a : AuthW) (as' : List AuthW) (rest : PState), WfAuth a → WfAuthList as' →
        authListSize (a :: as') ≤ fuel →
      parseAuthLoopW fuel ((encodeAuthW a).toList ++ ((encodeAuthTailW as').toList ++ (']' :: rest)))
        = some (a :: as', rest))

/-- **The combined `Authorization` fuel-adequate roundtrip.** By STRONG induction on fuel; each
recursive sub-call lands at strictly-smaller fuel, so the IH applies. The engine; the public
`parseAuthW_roundtrip` / `parseAuthListW_roundtrip` below unwrap it. -/
private theorem authGoal_all : ∀ fuel, AuthGoal fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    -- LOOP clause first (depends only on IH at strictly-smaller fuel).
    have hloop : ∀ (a : AuthW) (as' : List AuthW) (rest : PState), WfAuth a → WfAuthList as' →
        authListSize (a :: as') ≤ fuel →
        parseAuthLoopW fuel ((encodeAuthW a).toList ++ ((encodeAuthTailW as').toList ++ (']' :: rest)))
          = some (a :: as', rest) := by
      intro a as' rest hwfa hwfas hsz
      have hsz' : 1 + authSize a + authListSize as' ≤ fuel := by
        simpa only [authListSize] using hsz
      obtain ⟨g, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have hsza : authSize a ≤ g := by omega
      unfold parseAuthLoopW
      rw [(IH g (by omega)).1 a ((encodeAuthTailW as').toList ++ (']' :: rest)) hwfa hsza]
      simp only []
      cases as' with
      | nil =>
          simp only [show (encodeAuthTailW ([] : List AuthW)).toList = [] from rfl, List.nil_append]
          rw [show lit "," (']' :: rest) = none from by
                rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
                exact lit_ne_pre "," "]" rest (by decide) (by decide)]
          simp only []
          rw [lit_brack]
      | cons a2 as2 =>
          obtain ⟨hwfa2, hwfas2⟩ : WfAuth a2 ∧ WfAuthList as2 := hwfas
          rw [encAuthTailW_cons_shape a2 as2 (']' :: rest), lit_commaC]
          simp only []
          have hszrec : authListSize (a2 :: as2) ≤ g := by omega
          rw [(IH g (by omega)).2.2 a2 as2 rest hwfa2 hwfas2 hszrec]
    -- LIST clause (re-uses `hloop` at the SAME fuel).
    have hlistW : ∀ (as : List AuthW) (rest : PState), WfAuthList as → authListSize as ≤ fuel →
        parseAuthListW fuel ((encodeAuthListW as).toList ++ rest) = some (as, rest) := by
      intro as rest hwf hsz
      match as with
      | [] =>
          unfold encodeAuthListW parseAuthListW
          rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
      | a :: as' =>
          obtain ⟨hwfa, hwfas⟩ : WfAuth a ∧ WfAuthList as' := hwf
          unfold parseAuthListW
          rw [encAuthListW_cons_shape a as' rest]
          have hempty : lit "[]"
              ('[' :: ((encodeAuthW a).toList ++ ((encodeAuthTailW as').toList ++ (']' :: rest)))) = none := by
            obtain ⟨t, ht⟩ := encodeAuthW_head a
            rw [ht, List.cons_append]; rfl
          rw [hempty]; simp only []
          rw [show ('[' :: ((encodeAuthW a).toList ++ ((encodeAuthTailW as').toList ++ (']' :: rest))))
                = ("[":String).toList ++ ((encodeAuthW a).toList ++ ((encodeAuthTailW as').toList ++ (']' :: rest)))
                from rfl, lit_append]
          simp only []
          exact hloop a as' rest hwfa hwfas hsz
    refine ⟨?_, hlistW, hloop⟩
    -- AUTH clause: flat arms delegate to `parseAuthW_flat`; `oneOf` routes through `hlistW` at `f'`.
    intro a rest hwf hsz
    have ha1 : 1 ≤ authSize a := by cases a <;> simp [authSize]
    obtain ⟨f', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    by_cases hoo : ∃ cands i, a = .oneOf cands i
    · obtain ⟨cands, i, rfl⟩ := hoo
      have hwfc : WfAuthList cands := hwf
      have hszc : authListSize cands ≤ f' := by simp only [authSize] at hsz; omega
      unfold parseAuthW
      simp only [encodeAuthW, String.toList_append, List.append_assoc]
      lit_fail "{\"sig\":[" "{\"oneof\":["
      lit_fail "{\"pf\":[" "{\"oneof\":["
      lit_fail "{\"bread\":[" "{\"oneof\":["
      lit_fail "{\"bearer\":[" "{\"oneof\":["
      lit_fail "{\"unchecked\":0}" "{\"oneof\":["
      lit_fail "{\"captp\":[" "{\"oneof\":["
      lit_fail "{\"custom\":[" "{\"oneof\":["
      lit_ok
      rw [(IH f' (by omega)).2.1 cands _ hwfc hszc]
      simp only []
      lit_ok; nat_ok; lit_ok; rfl
    · exact parseAuthW_flat a rest f' hwf (fun cs i h => hoo ⟨cs, i, h⟩)

/-! ### §6f — the public FILL-J `Authorization` roundtrip facts (the WHO decoder leaves the TCB). -/

/-- **FILL J production (b): the FULL `Authorization` roundtrip.** Every well-formed `AuthW` — including
the recursive `oneOf` candidate disjunction — round-trips through `encodeAuthW`/`parseAuthW`, given fuel
`≥ authSize a`. This REMOVES the security-critical WHO decoder from the codec TCB. -/
theorem parseAuthW_roundtrip (a : AuthW) (rest : PState) (hwf : WfAuth a) (fuel : Nat)
    (hfuel : authSize a ≤ fuel) :
    parseAuthW fuel ((encodeAuthW a).toList ++ rest) = some (a, rest) :=
  (authGoal_all fuel).1 a rest hwf hfuel

/-- **The candidate-LIST roundtrip** (`parseAuthListW ∘ encodeAuthListW = id`) — the `oneOf` body,
empty or non-empty, given fuel `≥ authListSize as`. -/
theorem parseAuthListW_roundtrip (as : List AuthW) (rest : PState) (hwf : WfAuthList as) (fuel : Nat)
    (hfuel : authListSize as ≤ fuel) :
    parseAuthListW fuel ((encodeAuthListW as).toList ++ rest) = some (as, rest) :=
  (authGoal_all fuel).2.1 as rest hwf hfuel

/-! ### NON-VACUITY witnesses for the WHO decoder (the teeth are satisfiable AND the recursion real). -/

-- A digest-bearing auth round-trips (the `< 2^256` bound is REAL teeth):
example : parseAuthW 5 ((encodeAuthW (.signature 7 9)).toList ++ ['x']) = some (.signature 7 9, ['x']) :=
  parseAuthW_roundtrip (.signature 7 9) ['x'] (show (7:Nat) < 2^256 by norm_num) 5 (by decide)
-- A NESTED `oneOf` round-trips (the recursion is real — `oneOf` calls back into the list/loop/auth):
private def witNestedAuth : AuthW := .oneOf [.oneOf [.unchecked] 0, .breadstuff 3] 1
example : parseAuthW 10 ((encodeAuthW witNestedAuth).toList ++ ['x']) = some (witNestedAuth, ['x']) :=
  parseAuthW_roundtrip witNestedAuth ['x'] (by unfold witNestedAuth WfAuth WfAuthList; trivial) 10
    (by unfold witNestedAuth; decide)

/-! ## §8 — the narrow `AUTHS` list (`parseAuths`) roundtrip — the INPUT-LENGTH-FUEL `let rec` loop
pattern (the gateway reused by every remaining FILL-J production: `parseNats`/`parseEscrow`/`parseQueue`/
`parseSwiss`/`parseForest` all share it). `parseAuths`'s inner `loop` runs on `cs.length + 1` fuel; the
adequacy is carried by the invariant `input.length < fuel` (each iteration consumes ≥1 char while fuel
drops by 1, so it is self-maintaining) — NO separate length-bound lemma is needed. Tags are single
digits (`0..6`) and `authOfTag_authTag` (§0f) is already proved, so the per-element parse is trivial. -/

/-- The `AUTHS` tail encoder (the `foldl` body in cons-recursive form, mirroring §6d). -/
private def encodeAuthsTail (as : List Authority.Auth) : String :=
  as.foldl (fun acc x => acc ++ "," ++ toString (authTag x)) ""

/-- The accumulator pulls OUT of the tail fold (`List Char`-level, mirroring `foldl_authtail`). -/
private theorem foldl_authsTail (as : List Authority.Auth) : ∀ (acc : String),
    as.foldl (fun s x => s ++ "," ++ toString (authTag x)) acc
      = acc ++ as.foldl (fun s x => s ++ "," ++ toString (authTag x)) "" := by
  induction as with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ toString (authTag b)), ih ("" ++ "," ++ toString (authTag b))]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

/-- Rebracket a NON-EMPTY tag TAIL into comma-then-tag-then-tail (peelable). -/
private theorem encAuthsTail_cons_shape (b : Authority.Auth) (bs : List Authority.Auth) (rest : PState) :
    (encodeAuthsTail (b :: bs)).toList ++ rest
      = ',' :: ((toString (authTag b)).toList ++ ((encodeAuthsTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeAuthsTail (b :: bs)
      = ("" ++ "," ++ toString (authTag b)) ++ encodeAuthsTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ toString (authTag x)) "" = _
      rw [List.foldl_cons]; exact foldl_authsTail bs ("" ++ "," ++ toString (authTag b))]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

/-- Rebracket a NON-EMPTY tag LIST into open-`[`-then-body form. -/
private theorem encodeAuths_cons_shape (a : Authority.Auth) (as : List Authority.Auth) (rest : PState) :
    (encodeAuths (a :: as)).toList ++ rest
      = '[' :: ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest))) := by
  simp only [encodeAuths]
  rw [show (as.foldl (fun acc x => acc ++ "," ++ toString (authTag x)) "") = encodeAuthsTail as from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

/-- A tag's `toString` is a nonempty digit string (length ≥ 1) — the per-iteration consume bound. -/
private theorem tag_toString_len (a : Authority.Auth) : 1 ≤ (toString (authTag a)).toList.length := by
  obtain ⟨h0, t0, ht0, _, _, _⟩ := repr_cons (authTag a)
  rw [ht0]; simp

/-- **The loop recovers the candidate list**, given the `input.length < fuel` invariant. By induction
on the tail (the head `a` generalized); the recursive call lands at `fuel-1` with a strictly-shorter
input, so the invariant is preserved (`omega`, using `tag_toString_len`). -/
private theorem parseAuths_loop_works : ∀ (as : List Authority.Auth) (a : Authority.Auth) (rest : PState) (fuel : Nat),
    ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest))).length < fuel →
    parseAuths.loop fuel
        ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeAuthsTail ([] : List Authority.Auth)).toList = [] from rfl, List.nil_append]
      unfold parseAuths.loop
      rw [parseNat_toString (authTag a) (']' :: rest) (nd_brack rest)]
      simp only []
      rw [authOfTag_authTag]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      have hlen : 1 ≤ (toString (authTag a)).toList.length := tag_toString_len a
      rw [encAuthsTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseAuths.loop
      rw [parseNat_toString (authTag a) _ (nd_comma _)]
      simp only []
      rw [authOfTag_authTag]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((toString (authTag a2)).toList ++ ((encodeAuthsTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **FILL J production (d): the narrow `AUTHS` list roundtrip** (`parseAuths ∘ encodeAuths = id`). The
`oneOf`-free `Auth` tag array the wide `cA` action field carries; the gateway for the length-fuel loops. -/
theorem parseAuths_encode (rs : List Authority.Auth) (rest : PState) :
    parseAuths ((encodeAuths rs).toList ++ rest) = some (rs, rest) := by
  cases rs with
  | nil =>
      unfold parseAuths
      simp only [encodeAuths]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseAuths
      rw [encodeAuths_cons_shape a as rest]
      obtain ⟨h0, t0, ht0, hh0dig, _, _⟩ := repr_cons (authTag a)
      have hempty : lit "[]"
          ('[' :: ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest)))) = none := by
        rw [ht0, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] h0 _ (by intro heq; subst heq; exact absurd hh0dig (by decide))]
      rw [hempty]; simp only []
      rw [show ('[' :: ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest))))
            = ("[":String).toList ++ ((toString (authTag a)).toList ++ ((encodeAuthsTail as).toList ++ (']' :: rest)))
            from rfl, lit_append]
      simp only []
      apply parseAuths_loop_works as a rest
      simp only [List.length_append, List.length_cons]; omega

/-! ## §7 — the `FullActionA` (WHAT) decoder roundtrip (FILL-J production (c): the 46-arm effect sum).

`parseActionW` is FLAT (no fuel recursion) and uses `do`-notation over the `cN`/`cI`/`cS`/`cA` field
combinators, dispatching on a 46-deep fail-closed tag cascade. The 41 `simple` arms (every arm whose
fields are all `Nat`/`Int` — which is EVERY conserved-measure effect: balances, mints/burns, escrows,
queues, notes, bridges, seals, sovereign) are closed UNIFORMLY by `parseActionW_roundtrip`: the
`skip_to_arm` macro auto-discharges the dispatch (no per-tag lines — `rw [lit_ne_pre]` infers the tags &
defers the `decide`s), then one `simp only` collapses the `do`-block. The 5 remaining arms (the JSON-
string `setFieldA` + the 4 AUTHS-bearing arms) are the documented follow-on (see `isSimpleArm`). -/

/-- **Auto-dispatch:** advance past every WRONG tag in the fail-closed cascade. `rw [lit_ne_pre]` infers
the two concrete tags by unification and DEFERS the `litGo … = none` obligations as side-goals, which
`decide` then closes (sidestepping the eager-`by decide`-with-metavars problem). `repeat` stops exactly
at the matching tag (where the `decide` side-goal is `… = some _`, false, so the step fails & rolls back). -/
local macro "skip_to_arm" : tactic =>
  `(tactic| repeat (rw [lit_ne_pre] <;> first | (simp only []) | decide))

/-- `cN` (read `,` then a `Nat`) on a `toString`-led tail whose post-byte is a non-digit closer. -/
private theorem cN_step (n : Nat) (rest : PState)
    (hnd : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    cN ((",":String).toList ++ ((toString n).toList ++ rest)) = some (n, rest) := by
  unfold cN; rw [lit_append]; simp only []; exact parseNat_toString n rest hnd

/-- `cI` (read `,` then an `Int`) on a `toString`-led tail whose post-byte is a non-digit closer. -/
private theorem cI_step (i : Int) (rest : PState)
    (hnd : rest = [] ∨ ∃ c rs, rest = c :: rs ∧ c.isDigit = false) :
    cI ((",":String).toList ++ ((toString i).toList ++ rest)) = some (i, rest) := by
  unfold cI; rw [lit_append]; simp only []; exact parseInt_toString i rest hnd

/-- `cA` (read `,` then an `AUTHS` tag array) on an `encodeAuthsW`-led tail — via §8's `parseAuths_encode`.
This is the combinator that lets the 4 AUTHS-bearing action arms join the `simple` sweep. -/
private theorem cA_step (rs : List Authority.Auth) (rest : PState) :
    cA ((",":String).toList ++ ((encodeAuthsW rs).toList ++ rest)) = some (rs, rest) := by
  unfold cA; rw [lit_append]; simp only []
  unfold parseAuthsW encodeAuthsW
  exact parseAuths_encode rs rest

/-- `cS` (read `,` then a quoted JSON string) on an escape-free field — via §0d's `parseStr_clean`. The
input is the SPLIT form (`","`/`"\""` as SEPARATE literals — `setFieldA` first splits its COMBINED
`,"`/`",` separators so every comma is a plain `","`, matching `cN_step`/`nd_litComma`); the bridge to
`parseStr_clean`'s `'"' :: …` is the `decide`-rewrite of `("\"").toList = ['"']`. -/
private theorem cS_step (s : String) (rest : PState) (hcl : ∀ c ∈ s.toList, c ≠ '"' ∧ c ≠ '\\') :
    cS ((",":String).toList ++ (("\"":String).toList ++ ((jsonEscape s).toList
        ++ (("\"":String).toList ++ rest)))) = some (s, rest) := by
  unfold cS; rw [lit_append]; simp only []
  rw [show (("\"":String).toList ++ ((jsonEscape s).toList ++ (("\"":String).toList ++ rest)))
        = '"' :: ((jsonEscape s).toList ++ ('"' :: rest)) from by
        simp only [show ("\"":String).toList = ['"'] from by decide, List.cons_append, List.nil_append]]
  exact parseStr_clean s rest hcl

/-- The ONE arm needing more than the `N`/`I`/`A` field toolkit: `setFieldA`, whose `cS` JSON-string
field needs an escape-free `Wf` hypothesis (it cannot be a hypothesis-free `simp` lemma). Every other
arm — including the 4 AUTHS-bearing arms (`delegateAttenA`/`attenuateA`/`exportSturdyRefA`/`enlivenRefA`),
now that §8's `cA_step`/`parseAuths_encode` closes the `cA` field — is `simple`. -/
def isSimpleArm : TurnExecutorFull.FullActionA → Bool
  | .setFieldA .. => false
  | .exerciseA .. => false   -- RECURSES: carries a nested `;`-joined inner-effect array, not a flat arm.
  | .sealA ..     => false   -- carries a `Cap` PAYLOAD field (not a flat `N`/`I`/`A`); see `parseActionW_seal`.
  | _             => true

/-- One `simple` arm, fully automatic: auto-dispatch to its tag, then collapse the `do`-block of `N`/`I`
fields (`simp` selects the matching `nd_*` closer per field). `done` makes it all-or-nothing, so the
bundle's `first | action_arm | …` cleanly falls through on the 5 non-simple arms. -/
local macro "action_arm" : tactic =>
  `(tactic| (
    unfold parseActionW parseActionWFuel
    simp only [encodeActionW, String.toList_append, List.append_assoc]
    skip_to_arm
    simp only [lit_append,
      parseNat_toString _ _ (nd_litComma _), parseNat_toString _ _ (nd_litClose _),
      cN_step _ _ (nd_litComma _), cN_step _ _ (nd_litClose _),
      cI_step _ _ (nd_litComma _), cI_step _ _ (nd_litClose _), cA_step _ _,
      Option.bind_eq_bind, Option.bind]
    done))

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **FILL J production (c): the `FullActionA` (WHAT) decoder roundtrip — 45 of 46 arms.** Every
`isSimpleArm` action (all but `setFieldA`) round-trips through `encodeActionW`/`parseActionW`, now
INCLUDING the 4 AUTHS-bearing arms (via §8's `cA_step`). This removes nearly all of the WHAT decoder —
EVERY conserved-measure arm (`bal`/`mint`/`burn`/escrow/queue/note/bridge/seal/sovereign…) the
executor's per-asset laws range over, AND the capability-delegation/export arms — from the codec TCB. A
symmetric bug in the WHAT layer (wrong effect tag/args agreed by encoder+decoder) is caught here. -/
theorem parseActionW_roundtrip (act : TurnExecutorFull.FullActionA) (rest : PState)
    (h : isSimpleArm act = true) :
    parseActionW ((encodeActionW act).toList ++ rest) = some (act, rest) := by
  cases act <;> first | action_arm | simp [isSimpleArm] at h

/-! ### NON-VACUITY witnesses for the WHAT decoder (distinct clusters round-trip via one theorem). -/

-- A BALANCE effect (the conserved-measure arm, `[N,N,N,I,N]` with a `Turn` record) round-trips:
example : parseActionW ((encodeActionW (.balanceA ⟨1, 2, 3, 5⟩ 0)).toList ++ ['x'])
            = some (.balanceA ⟨1, 2, 3, 5⟩ 0, ['x']) :=
  parseActionW_roundtrip (.balanceA ⟨1, 2, 3, 5⟩ 0) ['x'] (by decide)
-- ...and an UNSEAL effect (`[N,N,N]`, a different cluster + later in the dispatch cascade) round-trips
-- too (the DE-SHADOWED unseal carries pid/actor/recipient — all flat `N`s; the Cap-bearing `sealA` is the
-- one non-simple seal arm, closed separately by `parseActionW_seal`):
example : parseActionW ((encodeActionW (.unsealA 7 8 9)).toList ++ ['x']) = some (.unsealA 7 8 9, ['x']) :=
  parseActionW_roundtrip (.unsealA 7 8 9) ['x'] (by decide)

set_option maxHeartbeats 1000000 in
/-- **The last `FullActionA` arm: `setFieldA`** — proved SEPARATELY because (a) its `cS` JSON-string
field needs the escape-free `Wf` hypothesis `hcl`, and (b) its encoder uses COMBINED separators `,"`/`",`
which we first SPLIT into single `","` literals so the standard field combinators apply. With this +
`parseActionW_roundtrip`, ALL 46 WHAT-decoder arms carry a parse∘encode theorem — the entire effect
decoder is out of the Lean-side TCB. -/
theorem parseActionW_setfield (actor cell : CellId) (field : String) (v : Int) (rest : PState)
    (hcl : ∀ c ∈ field.toList, c ≠ '"' ∧ c ≠ '\\') :
    parseActionW ((encodeActionW (.setFieldA actor cell field v)).toList ++ rest)
      = some (.setFieldA actor cell field v, rest) := by
  unfold parseActionW parseActionWFuel
  simp only [encodeActionW]
  rw [show (",\"" : String) = "," ++ "\"" from by decide,
      show ("\"," : String) = "\"" ++ "," from by decide]
  simp only [String.toList_append, List.append_assoc]
  skip_to_arm
  simp only [lit_append, parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    cS_step _ _ hcl, cI_step _ _ (nd_litClose _), Option.bind_eq_bind, Option.bind]

-- A setField effect with an escape-free field name round-trips (the WHAT decoder is now COMPLETE, 46/46):
example : parseActionW ((encodeActionW (.setFieldA 1 2 "balance" 99)).toList ++ ['x'])
            = some (.setFieldA 1 2 "balance" 99, ['x']) :=
  parseActionW_setfield 1 2 "balance" 99 ['x'] (by decide)

/-! ## §9 — the `[N,N,…]` Nat-list (`parseNats`) roundtrip — the SAME length-fuel loop as §8 (the
`nullifiers`/`commitments` `WState` fields). This CONFIRMS §8's recipe is reusable verbatim for every
length-fuel list: it is §8 with the element `toString (authTag a)`→`toString a` and the `authOfTag`
step dropped (the element is the `Nat` directly). The first STATE-decoder sub-production. -/

private def encodeNatsTail (ns : List Nat) : String :=
  ns.foldl (fun acc x => acc ++ "," ++ toString x) ""

private theorem foldl_natsTail (ns : List Nat) : ∀ (acc : String),
    ns.foldl (fun s x => s ++ "," ++ toString x) acc
      = acc ++ ns.foldl (fun s x => s ++ "," ++ toString x) "" := by
  induction ns with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ toString b), ih ("" ++ "," ++ toString b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encNatsTail_cons_shape (b : Nat) (bs : List Nat) (rest : PState) :
    (encodeNatsTail (b :: bs)).toList ++ rest
      = ',' :: ((toString b).toList ++ ((encodeNatsTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeNatsTail (b :: bs) = ("" ++ "," ++ toString b) ++ encodeNatsTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ toString x) "" = _
      rw [List.foldl_cons]; exact foldl_natsTail bs ("" ++ "," ++ toString b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeNats_cons_shape (a : Nat) (as : List Nat) (rest : PState) :
    (encodeNats (a :: as)).toList ++ rest
      = '[' :: ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest))) := by
  simp only [encodeNats]
  rw [show (as.foldl (fun acc x => acc ++ "," ++ toString x) "") = encodeNatsTail as from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

private theorem nat_toString_len (a : Nat) : 1 ≤ (toString a).toList.length := by
  obtain ⟨h0, t0, ht0, _, _, _⟩ := repr_cons a
  rw [ht0]; simp

private theorem parseNats_loop_works : ∀ (as : List Nat) (a : Nat) (rest : PState) (fuel : Nat),
    ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest))).length < fuel →
    parseNats.loop fuel ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeNatsTail ([] : List Nat)).toList = [] from rfl, List.nil_append]
      unfold parseNats.loop
      rw [parseNat_toString a (']' :: rest) (nd_brack rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      have hlen : 1 ≤ (toString a).toList.length := nat_toString_len a
      rw [encNatsTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseNats.loop
      rw [parseNat_toString a _ (nd_comma _)]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((toString a2).toList ++ ((encodeNatsTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **FILL J production (e): the `[N,N,…]` Nat-list roundtrip** (`parseNats ∘ encodeNats = id`) — the
`nullifiers`/`commitments` `WState` fields, and the first confirmation that §8's length-fuel recipe is a
verbatim template. -/
theorem parseNats_encode (ns : List Nat) (rest : PState) :
    parseNats ((encodeNats ns).toList ++ rest) = some (ns, rest) := by
  cases ns with
  | nil =>
      unfold parseNats
      simp only [encodeNats]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseNats
      rw [encodeNats_cons_shape a as rest]
      obtain ⟨h0, t0, ht0, hh0dig, _, _⟩ := repr_cons a
      have hempty : lit "[]"
          ('[' :: ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest)))) = none := by
        rw [ht0, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] h0 _ (by intro heq; subst heq; exact absurd hh0dig (by decide))]
      rw [hempty]; simp only []
      rw [show ('[' :: ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest))))
            = ("[":String).toList ++ ((toString a).toList ++ ((encodeNatsTail as).toList ++ (']' :: rest)))
            from rfl, lit_append]
      simp only []
      apply parseNats_loop_works as a rest
      simp only [List.length_append, List.length_cons]; omega

/-! ## §10 — the `BAL` ledger-list (`parseBal`) roundtrip — the CONSERVED-MEASURE `WState` field (what
the executor's per-asset conservation laws range over). The length-fuel loop of §8/§9, but the element
is the SELF-DELIMITING `[c,a,amt]` entry (`parseBalEntry`, already proved in §2) — so it round-trips for
ANY tail, with NO non-digit post-byte condition. A `bal`-list codec bug is now caught. -/

/-- One `BALENTRY` `[c,a,amt]` (matching `encodeBal`'s local `one`). -/
private def balOne (p : CellId × AssetId × Int) : String :=
  "[" ++ toString p.1 ++ "," ++ toString p.2.1 ++ "," ++ toString p.2.2 ++ "]"

private def encodeBalTail (es : List (CellId × AssetId × Int)) : String :=
  es.foldl (fun acc p => acc ++ "," ++ balOne p) ""

/-- One entry round-trips for ANY tail (self-delimiting) — from §2's `parseBalEntry_encode`. -/
private theorem parseBalEntry_one (e : CellId × AssetId × Int) (rest : PState) :
    parseBalEntry ((balOne e).toList ++ rest) = some (e, rest) := by
  obtain ⟨c, a, amt⟩ := e
  exact parseBalEntry_encode c a amt rest

/-- A `BALENTRY` opens with `'['` (so the `bal` list body is `[[…`, making `lit "[]"` fail). Explicit
witness ⇒ no metavar; `simp` normalizes the left-assoc append on both sides. -/
private theorem balOne_head (a : CellId × AssetId × Int) : ∃ t, (balOne a).toList = '[' :: t := by
  refine ⟨((toString a.1 ++ "," ++ toString a.2.1 ++ "," ++ toString a.2.2 ++ "]" : String)).toList, ?_⟩
  unfold balOne
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_balTail (es : List (CellId × AssetId × Int)) : ∀ (acc : String),
    es.foldl (fun s p => s ++ "," ++ balOne p) acc
      = acc ++ es.foldl (fun s p => s ++ "," ++ balOne p) "" := by
  induction es with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ balOne b), ih ("" ++ "," ++ balOne b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encBalTail_cons_shape (b : CellId × AssetId × Int) (bs : List (CellId × AssetId × Int))
    (rest : PState) :
    (encodeBalTail (b :: bs)).toList ++ rest
      = ',' :: ((balOne b).toList ++ ((encodeBalTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeBalTail (b :: bs) = ("" ++ "," ++ balOne b) ++ encodeBalTail bs from by
      show (b :: bs).foldl (fun s p => s ++ "," ++ balOne p) "" = _
      rw [List.foldl_cons]; exact foldl_balTail bs ("" ++ "," ++ balOne b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeBal_cons_shape (a : CellId × AssetId × Int) (as : List (CellId × AssetId × Int))
    (rest : PState) :
    (encodeBal (a :: as)).toList ++ rest
      = '[' :: ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest))) := by
  rw [show encodeBal (a :: as) = "[" ++ balOne a ++ encodeBalTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

private theorem parseBal_loop_works : ∀ (as : List (CellId × AssetId × Int)) (a : CellId × AssetId × Int)
    (rest : PState) (fuel : Nat),
    ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest))).length < fuel →
    parseBal.loop fuel ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeBalTail ([] : List (CellId × AssetId × Int))).toList = [] from rfl, List.nil_append]
      unfold parseBal.loop
      rw [parseBalEntry_one a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encBalTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseBal.loop
      rw [parseBalEntry_one a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((balOne a2).toList ++ ((encodeBalTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **FILL J production (f): the `BAL` ledger-list roundtrip** (`parseBal ∘ encodeBal = id`) — the
CONSERVED-MEASURE `WState` field. The self-delimiting `[c,a,amt]` element makes this the cleanest
length-fuel instance (no post-byte condition). -/
theorem parseBal_encode (es : List (CellId × AssetId × Int)) (rest : PState) :
    parseBal ((encodeBal es).toList ++ rest) = some (es, rest) := by
  cases es with
  | nil =>
      unfold parseBal
      rw [show (encodeBal ([] : List (CellId × AssetId × Int))) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseBal
      rw [encodeBal_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := balOne_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [show ('[' :: ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest))))
            = ("[":String).toList ++ ((balOne a).toList ++ ((encodeBalTail as).toList ++ (']' :: rest)))
            from rfl, lit_append]
      simp only []
      apply parseBal_loop_works as a rest
      simp only [List.length_append, List.length_cons]; omega

/-! ## §11 — the `ESCROWS` side-table (`parseEscrows`) roundtrip. Length-fuel loop (§10 template), but
the element `parseEscrow` is a 7-field `do`-block with two 0/1 FLAGS (`parseFlag_bool`, §0f). The first
side-table whose element itself needs a `do`-block roundtrip proof. -/

/-- `lit "[" ('[' :: rest) = some rest` — GENERIC (proved once, no per-element defeq), so consuming the
list-open `[` never whnf-reduces a big element term. -/
private theorem lit_lbrack (rest : PState) : lit "[" ('[' :: rest) = some rest := by
  unfold lit; rw [show ("[":String).toList = ['['] from by decide, litGo_cons_match]; rfl

set_option maxHeartbeats 1000000 in
/-- **The `ESC` entry roundtrip** — the 7-field record `[id,creator,recipient,amount,resolved,asset,
bridge]` (flags via §0f's `parseFlag_bool`); self-delimiting, so round-trips for ANY tail. -/
theorem parseEscrow_encode (e : EscrowRecord) (rest : PState) :
    parseEscrow ((encodeEscrow e).toList ++ rest) = some (e, rest) := by
  unfold parseEscrow encodeEscrow
  simp only [String.toList_append, List.append_assoc]
  simp only [lit_append, parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    cI_step _ _ (nd_litComma _), parseFlag_bool _ _ (nd_litComma _), parseFlag_bool _ _ (nd_litBrack _),
    Option.bind_eq_bind, Option.bind]

private def encodeEscrowsTail (es : List EscrowRecord) : String :=
  es.foldl (fun acc x => acc ++ "," ++ encodeEscrow x) ""

/-- An `ESC` entry opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). -/
private theorem encodeEscrow_head (e : EscrowRecord) : ∃ t, (encodeEscrow e).toList = '[' :: t := by
  refine ⟨(toString e.id ++ "," ++ toString e.creator ++ "," ++ toString e.recipient ++ ","
    ++ toString e.amount ++ "," ++ (if e.resolved then "1" else "0") ++ "," ++ toString e.asset ++ ","
    ++ (if e.bridge then "1" else "0") ++ "]" : String).toList, ?_⟩
  unfold encodeEscrow
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_escrowsTail (es : List EscrowRecord) : ∀ (acc : String),
    es.foldl (fun s x => s ++ "," ++ encodeEscrow x) acc
      = acc ++ es.foldl (fun s x => s ++ "," ++ encodeEscrow x) "" := by
  induction es with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeEscrow b), ih ("" ++ "," ++ encodeEscrow b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encEscrowsTail_cons_shape (b : EscrowRecord) (bs : List EscrowRecord) (rest : PState) :
    (encodeEscrowsTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeEscrow b).toList ++ ((encodeEscrowsTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeEscrowsTail (b :: bs) = ("" ++ "," ++ encodeEscrow b) ++ encodeEscrowsTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeEscrow x) "" = _
      rw [List.foldl_cons]; exact foldl_escrowsTail bs ("" ++ "," ++ encodeEscrow b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeEscrows_cons_shape (a : EscrowRecord) (as : List EscrowRecord) (rest : PState) :
    (encodeEscrows (a :: as)).toList ++ rest
      = '[' :: ((encodeEscrow a).toList ++ ((encodeEscrowsTail as).toList ++ (']' :: rest))) := by
  rw [show encodeEscrows (a :: as) = "[" ++ encodeEscrow a ++ encodeEscrowsTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
private theorem parseEscrows_loop_works : ∀ (as : List EscrowRecord) (a : EscrowRecord)
    (rest : PState) (fuel : Nat),
    ((encodeEscrow a).toList ++ ((encodeEscrowsTail as).toList ++ (']' :: rest))).length < fuel →
    parseEscrows.loop fuel ((encodeEscrow a).toList ++ ((encodeEscrowsTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeEscrowsTail ([] : List EscrowRecord)).toList = [] from rfl, List.nil_append]
      unfold parseEscrows.loop
      rw [parseEscrow_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encEscrowsTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseEscrows.loop
      rw [parseEscrow_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeEscrow a2).toList ++ ((encodeEscrowsTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

set_option maxHeartbeats 1000000 in
/-- **FILL J production (g): the `ESCROWS` side-table roundtrip** (`parseEscrows ∘ encodeEscrows = id`). -/
theorem parseEscrows_encode (es : List EscrowRecord) (rest : PState) :
    parseEscrows ((encodeEscrows es).toList ++ rest) = some (es, rest) := by
  cases es with
  | nil =>
      unfold parseEscrows
      rw [show (encodeEscrows ([] : List EscrowRecord)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseEscrows
      rw [encodeEscrows_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeEscrow a).toList ++ ((encodeEscrowsTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeEscrow_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseEscrows_loop_works as a rest
      simp only [List.length_cons]; omega

/-! ## §11b — the `QUEUES` side-table (`parseQueues`) roundtrip. Length-fuel loop (§11 template), and
the element `parseQueue` is a 4-field `do`-block `[id,owner,capacity,buffer]` whose LAST field `buffer`
is a NESTED `Nat`-list — reusing §9's `parseNats_encode` for that field (the first side-table whose
element embeds another array codec). Self-delimiting, so it round-trips for ANY tail. -/

set_option maxHeartbeats 1000000 in
/-- **The `Q` entry roundtrip** — the 4-field record `[id,owner,capacity,buffer]`, where `buffer` is a
nested `[N,N,…]` array discharged by §9's `parseNats_encode`. The three leading `Nat`s walk via
`parseNat_toString`/`cN_step` (post-byte `,`); the `,` before `buffer` and the closing `]` are plain
`lit_append`s (the buffer's `parseNats` leaves its argument `rest`, so the outer `]` is a clean literal
consume). Self-delimiting, so it round-trips for ANY tail. -/
theorem parseQueue_encode (q : QueueRecord) (rest : PState) :
    parseQueue ((encodeQueue q).toList ++ rest) = some (q, rest) := by
  unfold parseQueue encodeQueue
  simp only [String.toList_append, List.append_assoc]
  simp only [lit_append, parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    parseNats_encode, Option.bind_eq_bind, Option.bind]

private def encodeQueuesTail (qs : List QueueRecord) : String :=
  qs.foldl (fun acc x => acc ++ "," ++ encodeQueue x) ""

/-- A `Q` entry opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). -/
private theorem encodeQueue_head (q : QueueRecord) : ∃ t, (encodeQueue q).toList = '[' :: t := by
  refine ⟨(toString q.id ++ "," ++ toString q.owner ++ "," ++ toString q.capacity ++ ","
    ++ encodeNats q.buffer ++ "]" : String).toList, ?_⟩
  unfold encodeQueue
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_queuesTail (qs : List QueueRecord) : ∀ (acc : String),
    qs.foldl (fun s x => s ++ "," ++ encodeQueue x) acc
      = acc ++ qs.foldl (fun s x => s ++ "," ++ encodeQueue x) "" := by
  induction qs with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeQueue b), ih ("" ++ "," ++ encodeQueue b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encQueuesTail_cons_shape (b : QueueRecord) (bs : List QueueRecord) (rest : PState) :
    (encodeQueuesTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeQueue b).toList ++ ((encodeQueuesTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeQueuesTail (b :: bs) = ("" ++ "," ++ encodeQueue b) ++ encodeQueuesTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeQueue x) "" = _
      rw [List.foldl_cons]; exact foldl_queuesTail bs ("" ++ "," ++ encodeQueue b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeQueues_cons_shape (a : QueueRecord) (as : List QueueRecord) (rest : PState) :
    (encodeQueues (a :: as)).toList ++ rest
      = '[' :: ((encodeQueue a).toList ++ ((encodeQueuesTail as).toList ++ (']' :: rest))) := by
  rw [show encodeQueues (a :: as) = "[" ++ encodeQueue a ++ encodeQueuesTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
private theorem parseQueues_loop_works : ∀ (as : List QueueRecord) (a : QueueRecord)
    (rest : PState) (fuel : Nat),
    ((encodeQueue a).toList ++ ((encodeQueuesTail as).toList ++ (']' :: rest))).length < fuel →
    parseQueues.loop fuel ((encodeQueue a).toList ++ ((encodeQueuesTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeQueuesTail ([] : List QueueRecord)).toList = [] from rfl, List.nil_append]
      unfold parseQueues.loop
      rw [parseQueue_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encQueuesTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseQueues.loop
      rw [parseQueue_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeQueue a2).toList ++ ((encodeQueuesTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

set_option maxHeartbeats 1000000 in
/-- **FILL J production (h): the `QUEUES` side-table roundtrip** (`parseQueues ∘ encodeQueues = id`) —
the storage-queue FIFO side-table whose element embeds a nested `buffer` array (closed via §9). -/
theorem parseQueues_encode (qs : List QueueRecord) (rest : PState) :
    parseQueues ((encodeQueues qs).toList ++ rest) = some (qs, rest) := by
  cases qs with
  | nil =>
      unfold parseQueues
      rw [show (encodeQueues ([] : List QueueRecord)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseQueues
      rw [encodeQueues_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeQueue a).toList ++ ((encodeQueuesTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeQueue_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseQueues_loop_works as a rest
      simp only [List.length_cons]; omega

/-! ## §11c — the `SWISS` side-table (`parseSwissTable`) roundtrip. Length-fuel loop (§11/§11b template),
and the element `parseSwiss` is a 6-field `do`-block `[swiss,exporter,target,rights,refcount,cert]` whose
4th field `rights` is an AUTHS tag array (reusing §8's `parseAuths_encode` via §7's `cA_step`) and whose
LAST field `cert` is an OPTIONAL `Nat` (`{"none":0}`/`{"some":N}`, discharged by the `parseOptNat_encode`
leaf below). The first side-table element combining an AUTHS field AND an Option field. Self-delimiting,
so it round-trips for ANY tail. -/

/-- **The optional-`cert` leaf** (`parseOptNat ∘ encodeOptNat = id`). The `none` arm is a single literal
consume; the `some n` arm fails the `{"none":0}` prefix (`lit_ne_pre` over the two concrete tags), opens
`{"some":`, reads the `Nat` (post-byte `}`, non-digit), then closes `}`. Self-delimiting. -/
theorem parseOptNat_encode (o : Option Nat) (rest : PState) :
    parseOptNat ((encodeOptNat o).toList ++ rest) = some (o, rest) := by
  cases o with
  | none =>
      unfold parseOptNat encodeOptNat
      rw [show (("{\"none\":0}":String).toList ++ rest) = ("{\"none\":0}":String).toList ++ rest from rfl,
        lit_append]
  | some n =>
      unfold parseOptNat encodeOptNat
      rw [show (("{\"some\":" ++ toString n ++ "}":String).toList ++ rest)
            = ("{\"some\":":String).toList ++ ((toString n).toList ++ ('}' :: rest)) from by
          simp only [String.toList_append, show ("}":String).toList = ['}'] from by decide,
            List.append_assoc, List.cons_append, List.nil_append]]
      rw [lit_ne_pre "{\"none\":0}" "{\"some\":" _ (by decide) (by decide)]
      simp only []
      rw [lit_append]
      simp only []
      rw [parseNat_toString n ('}' :: rest) (nd_brace rest)]
      simp only []
      rw [show lit "}" ('}' :: rest) = some rest from by
            rw [show ('}' :: rest) = ("}":String).toList ++ rest from by
              simp only [show ("}":String).toList = ['}'] from by decide, List.cons_append,
                List.nil_append]]
            exact lit_append "}" rest]
      simp only [Option.map_some]

set_option maxHeartbeats 1000000 in
/-- **The `SW` entry roundtrip** — the 6-field record `[swiss,exporter,target,rights,refcount,cert]`,
where `rights` is an AUTHS array discharged by §7's `cA_step` (→ §8) and `cert` is an `Option Nat`
discharged by `parseOptNat_encode`. The three leading `Nat`s walk via `parseNat_toString`/`cN_step`
(post-byte `,`); the `,` before `cert` and the closing `]` are plain `lit_append`s (`parseOptNat`
leaves its argument `rest`, so the outer `]` is a clean literal consume). Self-delimiting. -/
theorem parseSwiss_encode (e : SwissRecord) (rest : PState) :
    parseSwiss ((encodeSwiss e).toList ++ rest) = some (e, rest) := by
  unfold parseSwiss encodeSwiss
  simp only [String.toList_append, List.append_assoc]
  simp only [lit_append, parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    cA_step _ _, parseOptNat_encode, Option.bind_eq_bind, Option.bind]

private def encodeSwissTail (es : List SwissRecord) : String :=
  es.foldl (fun acc x => acc ++ "," ++ encodeSwiss x) ""

/-- A `SW` entry opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). -/
private theorem encodeSwiss_head (e : SwissRecord) : ∃ t, (encodeSwiss e).toList = '[' :: t := by
  refine ⟨(toString e.swiss ++ "," ++ toString e.exporter ++ "," ++ toString e.target ++ ","
    ++ encodeAuthsW e.rights ++ "," ++ toString e.refcount ++ "," ++ encodeOptNat e.cert ++ "]"
    : String).toList, ?_⟩
  unfold encodeSwiss
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_swissTail (es : List SwissRecord) : ∀ (acc : String),
    es.foldl (fun s x => s ++ "," ++ encodeSwiss x) acc
      = acc ++ es.foldl (fun s x => s ++ "," ++ encodeSwiss x) "" := by
  induction es with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeSwiss b), ih ("" ++ "," ++ encodeSwiss b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encSwissTail_cons_shape (b : SwissRecord) (bs : List SwissRecord) (rest : PState) :
    (encodeSwissTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeSwiss b).toList ++ ((encodeSwissTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeSwissTail (b :: bs) = ("" ++ "," ++ encodeSwiss b) ++ encodeSwissTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeSwiss x) "" = _
      rw [List.foldl_cons]; exact foldl_swissTail bs ("" ++ "," ++ encodeSwiss b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeSwissTable_cons_shape (a : SwissRecord) (as : List SwissRecord) (rest : PState) :
    (encodeSwissTable (a :: as)).toList ++ rest
      = '[' :: ((encodeSwiss a).toList ++ ((encodeSwissTail as).toList ++ (']' :: rest))) := by
  rw [show encodeSwissTable (a :: as) = "[" ++ encodeSwiss a ++ encodeSwissTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
private theorem parseSwissTable_loop_works : ∀ (as : List SwissRecord) (a : SwissRecord)
    (rest : PState) (fuel : Nat),
    ((encodeSwiss a).toList ++ ((encodeSwissTail as).toList ++ (']' :: rest))).length < fuel →
    parseSwissTable.loop fuel ((encodeSwiss a).toList ++ ((encodeSwissTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeSwissTail ([] : List SwissRecord)).toList = [] from rfl, List.nil_append]
      unfold parseSwissTable.loop
      rw [parseSwiss_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encSwissTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseSwissTable.loop
      rw [parseSwiss_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeSwiss a2).toList ++ ((encodeSwissTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

set_option maxHeartbeats 1000000 in
/-- **FILL J production (i): the `SWISS` side-table roundtrip** (`parseSwissTable ∘ encodeSwissTable =
id`) — the CapTP swiss-table side-table whose element carries an AUTHS rights array (closed via §8) and
an optional handoff `cert` (closed via `parseOptNat_encode`). -/
theorem parseSwissTable_encode (ss : List SwissRecord) (rest : PState) :
    parseSwissTable ((encodeSwissTable ss).toList ++ rest) = some (ss, rest) := by
  cases ss with
  | nil =>
      unfold parseSwissTable
      rw [show (encodeSwissTable ([] : List SwissRecord)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseSwissTable
      rw [encodeSwissTable_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeSwiss a).toList ++ ((encodeSwissTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeSwiss_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseSwissTable_loop_works as a rest
      simp only [List.length_cons]; omega

/-! ## §12 — the WIDE `CELLS` array (`parseCellsW`) roundtrip — the STATE DECODER's cell store.

The `CELLS` field is `[[id,valueW],…]`: a length-fuel loop (§8 recipe) whose element `parseCellW`
embeds the FULL recursive wide-`Value` codec (§5's `parseValueW_roundtrip`) for the payload. The one
genuinely-new obligation versus the side-tables: the loop calls `parseCellW (cs.length+1) cs` —
re-deriving the element's value-fuel from the REMAINING input length — so the per-element
`parseValueW` adequacy is `valueSize v ≤ (remaining).length + 1`, which the byte-length lower bound
`valueSize_le_encodeLen` (the parse-depth never exceeds the encoded width) discharges with slack. The
codec boundary is §1's `WfValue` (digests `< 2^256`, names escape-free), so the list roundtrip carries
a per-cell `WfCells` hypothesis (the SAME non-vacuous boundary the value roundtrip lives on). -/

/-! A structural-size LOWER bound on the encoded width: the parse-depth `valueSize v` never exceeds the
byte length of `encodeValueW v` (so the loop's `(remaining).length + 1` element-fuel always suffices).
By the §5 mutual induction; every constructor emits strictly more bytes than its size counts. -/
mutual
theorem valueSize_le_encodeLen (v : Value) : valueSize v ≤ (encodeValueW v).toList.length := by
  cases v with
  | int i => simp only [valueSize, encodeValueW, String.toList_append]; simp
  | dig d => simp only [valueSize, encodeValueW, String.toList_append]; simp
  | sym s => simp only [valueSize, encodeValueW, String.toList_append]; simp
  | record fs =>
      simp only [valueSize, encodeValueW, String.toList_append, List.length_append]
      have := fieldsSize_le_encodeLen fs
      simp only [show ("{\"rec\":":String).toList.length = 7 from by decide,
        show ("}":String).toList.length = 1 from by decide]
      omega
theorem fieldsSize_le_encodeLen (fs : List (FieldName × Value)) :
    fieldsSize fs ≤ (encodeFieldsW fs).toList.length := by
  cases fs with
  | nil => simp [fieldsSize, encodeFieldsW]
  | cons p gs =>
      obtain ⟨n, v⟩ := p
      simp only [fieldsSize, encodeFieldsW, String.toList_append, List.length_append]
      have hv := valueSize_le_encodeLen v
      have ht := fieldsTailSize_le_encodeLen gs
      simp only [show ("[":String).toList.length = 1 from by decide,
        show ("]":String).toList.length = 1 from by decide,
        show ("[\"":String).toList.length = 2 from by decide,
        show ("\",":String).toList.length = 2 from by decide]
      omega
theorem fieldsTailSize_le_encodeLen (fs : List (FieldName × Value)) :
    fieldsSize fs ≤ (encodeFieldsTailW fs).toList.length := by
  cases fs with
  | nil => simp [fieldsSize, encodeFieldsTailW]
  | cons p gs =>
      obtain ⟨n, v⟩ := p
      simp only [fieldsSize, encodeFieldsTailW, String.toList_append, List.length_append]
      have hv := valueSize_le_encodeLen v
      have ht := fieldsTailSize_le_encodeLen gs
      simp only [show (",[\"":String).toList.length = 3 from by decide,
        show ("\",":String).toList.length = 2 from by decide,
        show ("]":String).toList.length = 1 from by decide]
      omega
end

/-- Well-formed `CELLS`: every cell's payload satisfies the §1 `WfValue` boundary. -/
def WfCells : List (CellId × Value) → Prop
  | []          => True
  | p :: ps     => WfValue p.2 ∧ WfCells ps

/-- The wide-cell encoder (the inline `one` lambda of `encodeCellsW`, named for the proof). -/
def encodeCellW (p : CellId × Value) : String :=
  "[" ++ toString p.1 ++ "," ++ encodeValueW p.2 ++ "]"

/-- **One wide `CELL` `[id,valueW]` round-trips** for ANY sufficient value-fuel — the `id` `Nat`
(post-byte `,`) then the recursive payload via §5's `parseValueW_roundtrip`, then the closing `]`
(`parseValueW` leaves its argument `rest`). Self-delimiting. -/
theorem parseCellW_encode (p : CellId × Value) (rest : PState) (hwf : WfValue p.2)
    (fuel : Nat) (hf : valueSize p.2 ≤ fuel) :
    parseCellW fuel ((encodeCellW p).toList ++ rest) = some (p, rest) := by
  obtain ⟨id, v⟩ := p
  unfold parseCellW encodeCellW
  -- After `String.toList_append`, the input is the right-associated
  -- `"[".toList ++ (id.toList ++ (",".toList ++ ((encodeValueW v).toList ++ ("]".toList ++ rest))))`;
  -- each literal is consumed via `lit_append` in its `"…".toList ++ _` form (NO `show` over the big
  -- `encodeValueW v` body — that would WHNF-reduce it and time out; the §11/parseBalEntry recipe).
  simp only [String.toList_append, List.append_assoc]
  rw [lit_append]
  simp only []
  rw [parseNat_toString id _ (nd_litComma _)]
  simp only []
  rw [lit_append]
  simp only []
  rw [parseValueW_roundtrip v (("]":String).toList ++ rest) hwf fuel hf]
  simp only []
  rw [lit_append]
  simp only [Option.map_some]

private def encodeCellsTail (ps : List (CellId × Value)) : String :=
  ps.foldl (fun acc x => acc ++ "," ++ encodeCellW x) ""

/-- A wide `CELL` opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). -/
private theorem encodeCellW_head (p : CellId × Value) : ∃ t, (encodeCellW p).toList = '[' :: t := by
  refine ⟨(toString p.1 ++ "," ++ encodeValueW p.2 ++ "]" : String).toList, ?_⟩
  unfold encodeCellW
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_cellsTail (ps : List (CellId × Value)) : ∀ (acc : String),
    ps.foldl (fun s x => s ++ "," ++ encodeCellW x) acc
      = acc ++ ps.foldl (fun s x => s ++ "," ++ encodeCellW x) "" := by
  induction ps with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeCellW b), ih ("" ++ "," ++ encodeCellW b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encCellsTail_cons_shape (b : CellId × Value) (bs : List (CellId × Value)) (rest : PState) :
    (encodeCellsTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeCellW b).toList ++ ((encodeCellsTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeCellsTail (b :: bs) = ("" ++ "," ++ encodeCellW b) ++ encodeCellsTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeCellW x) "" = _
      rw [List.foldl_cons]; exact foldl_cellsTail bs ("" ++ "," ++ encodeCellW b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeCellsW_cons_shape (a : CellId × Value) (as : List (CellId × Value)) (rest : PState) :
    (encodeCellsW (a :: as)).toList ++ rest
      = '[' :: ((encodeCellW a).toList ++ ((encodeCellsTail as).toList ++ (']' :: rest))) := by
  rw [show encodeCellsW (a :: as) = "[" ++ encodeCellW a ++ encodeCellsTail as ++ "]" from by
        show "[" ++ encodeCellW a ++ (as.foldl (fun acc p => acc ++ "," ++ encodeCellW p) "") ++ "]" = _
        rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
private theorem parseCellsW_loop_works : ∀ (as : List (CellId × Value)) (a : CellId × Value)
    (rest : PState) (fuel : Nat) (hwf : WfCells (a :: as)),
    ((encodeCellW a).toList ++ ((encodeCellsTail as).toList ++ (']' :: rest))).length < fuel →
    parseCellsW.loop fuel ((encodeCellW a).toList ++ ((encodeCellsTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hwf hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeCellsTail ([] : List (CellId × Value))).toList = [] from rfl, List.nil_append]
      unfold parseCellsW.loop
      rw [parseCellW_encode a (']' :: rest) hwf.1 _ (le_trans (valueSize_le_encodeLen a.2) (by
        rw [show ((encodeCellW a).toList ++ (']' :: rest)).length + 1
              = (encodeCellW a).toList.length + ((']' :: rest).length + 1) from by
            simp only [List.length_append]; omega]
        unfold encodeCellW
        simp only [String.toList_append, List.length_append]; omega))]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hwf hf
      rw [encCellsTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseCellsW.loop
      rw [parseCellW_encode a _ hwf.1 _ (le_trans (valueSize_le_encodeLen a.2) (by
        rw [show ((encodeCellW a).toList ++ (',' :: ((encodeCellW a2).toList ++ ((encodeCellsTail as2).toList ++ (']' :: rest))))).length + 1
              = (encodeCellW a).toList.length + ((',' :: ((encodeCellW a2).toList ++ ((encodeCellsTail as2).toList ++ (']' :: rest)))).length + 1) from by
            simp only [List.length_append]; omega]
        -- expose that `(encodeValueW a.2).length` is a summand of `(encodeCellW a).length`
        -- (else omega treats the cell-encoding as an opaque atom — same step the nil branch uses).
        unfold encodeCellW
        simp only [String.toList_append, List.length_append]; omega))]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeCellW a2).toList ++ ((encodeCellsTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hwf.2 hrec]

/-- **FILL J production (j): the WIDE `CELLS` array roundtrip** (`parseCellsW ∘ encodeCellsW = id`) — the
STATE DECODER's cell store, each element embedding the recursive `Value` payload (§5). Carries the §1
`WfCells` boundary (digests `< 2^256`, names escape-free); fuel-adequate whenever the OUTER loop fuel
exceeds the encoded width (the `parseWState` caller passes the whole-input length, so this is met). -/
theorem parseCellsW_encode (cs : List (CellId × Value)) (rest : PState) (hwf : WfCells cs)
    (fuel : Nat) (hf : ((encodeCellsW cs).toList ++ rest).length ≤ fuel) :
    parseCellsW fuel ((encodeCellsW cs).toList ++ rest) = some (cs, rest) := by
  cases cs with
  | nil =>
      unfold parseCellsW
      rw [show (encodeCellsW ([] : List (CellId × Value))) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseCellsW
      rw [encodeCellsW_cons_shape a as rest] at hf ⊢
      have hempty : lit "[]"
          ('[' :: ((encodeCellW a).toList ++ ((encodeCellsTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeCellW_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseCellsW_loop_works as a rest _ hwf
      -- `hf` charges the `'['`-prefixed body; the loop wants the body itself (one byte shorter).
      -- Expose both as sums of the same length-atoms (`simp only`, leaf lengths) so omega aligns them.
      simp only [List.length_cons, List.length_append] at hf ⊢; omega

/-! ## §13 — the `CAPS` table (`parseCapsEntries`) roundtrip — the STATE DECODER's capability store.

Three NESTED length-fuel loops: the `CAPS` array `[[holder,CAPLIST],…]` whose element `parseCapEntry`
embeds a `CAPLIST` array `[CAP,…]` whose element `parseCap` is the 3-arm capability sum
(`{"null":0}`/`{"node":N}`/`{"ep":[N,AUTHS]}`) — the `ep` arm carrying a narrow `AUTHS` tag array
(§8's `parseAuths_encode`). No `Wf` hypothesis: `Cap` carries only `Nat` targets + narrow-`Auth` tags
(all total). Each loop is the §8 length-fuel recipe; the `CAP` element dispatches fail-closed via
`lit_ne_pre` over the three concrete tags, mirroring §6's `parseAuthW` arm walk. -/

/-- **One `CAP` round-trips** (`parseCap ∘ encodeCap = id`) — the 3-arm capability sum. `null` is a
single literal consume; `node`/`ep` fail the earlier tags (`lit_ne_pre`), open their tag, read the
target `Nat`, and (for `ep`) the rights `AUTHS` array via §8's `parseAuths_encode`, then close. The `ep`
encoder's trailing `]}` is the AUTHS-array close (consumed by `parseAuths`) then the two literal
closers. Self-delimiting. -/
theorem parseCap_encode (c : Authority.Cap) (rest : PState) :
    parseCap ((encodeCap c).toList ++ rest) = some (c, rest) := by
  cases c with
  | null =>
      unfold parseCap encodeCap
      rw [show (("{\"null\":0}":String).toList ++ rest) = ("{\"null\":0}":String).toList ++ rest from rfl,
        lit_append]
  | node t =>
      unfold parseCap encodeCap
      rw [show (("{\"node\":" ++ toString t ++ "}":String).toList ++ rest)
            = ("{\"node\":":String).toList ++ ((toString t).toList ++ ('}' :: rest)) from by
          simp only [String.toList_append, show ("}":String).toList = ['}'] from by decide,
            List.append_assoc, List.cons_append, List.nil_append]]
      rw [lit_ne_pre "{\"null\":0}" "{\"node\":" _ (by decide) (by decide)]
      simp only []
      rw [lit_append]
      simp only []
      rw [parseNat_toString t ('}' :: rest) (nd_brace rest)]
      simp only []
      rw [show lit "}" ('}' :: rest) = some rest from by
            rw [show ('}' :: rest) = ("}":String).toList ++ rest from by
              simp only [show ("}":String).toList = ['}'] from by decide, List.cons_append,
                List.nil_append]]
            exact lit_append "}" rest]
      simp only [Option.map_some]
  | endpoint t r =>
      unfold parseCap encodeCap
      rw [show (("{\"ep\":[" ++ toString t ++ "," ++ encodeAuths r ++ "]}":String).toList ++ rest)
            = ("{\"ep\":[":String).toList ++ ((toString t).toList ++ (',' :: ((encodeAuths r).toList
                ++ (']' :: ('}' :: rest))))) from by
          simp only [String.toList_append, show (",":String).toList = [','] from by decide,
            show ("]}":String).toList = [']', '}'] from by decide, List.append_assoc, List.cons_append,
            List.nil_append]]
      rw [lit_ne_pre "{\"null\":0}" "{\"ep\":[" _ (by decide) (by decide)]
      simp only []
      rw [lit_ne_pre "{\"node\":" "{\"ep\":[" _ (by decide) (by decide)]
      simp only []
      rw [lit_append]
      simp only []
      rw [parseNat_toString t _ (nd_comma _)]
      simp only []
      rw [show lit "," (',' :: ((encodeAuths r).toList ++ (']' :: ('}' :: rest))))
            = some ((encodeAuths r).toList ++ (']' :: ('}' :: rest))) from by
          rw [show (',' :: ((encodeAuths r).toList ++ (']' :: ('}' :: rest))))
                = ("," : String).toList ++ ((encodeAuths r).toList ++ (']' :: ('}' :: rest))) from by
              simp only [show (",":String).toList = [','] from by decide, List.cons_append,
                List.nil_append]]
          exact lit_append "," _]
      simp only []
      rw [parseAuths_encode r (']' :: ('}' :: rest))]
      simp only []
      rw [show lit "]" (']' :: ('}' :: rest)) = some ('}' :: rest) from by
            rw [show (']' :: ('}' :: rest)) = ("]" : String).toList ++ ('}' :: rest) from by
              simp only [show ("]":String).toList = [']'] from by decide, List.cons_append,
                List.nil_append]]
            exact lit_append "]" _]
      simp only []
      rw [show lit "}" ('}' :: rest) = some rest from by
            rw [show ('}' :: rest) = ("}" : String).toList ++ rest from by
              simp only [show ("}":String).toList = ['}'] from by decide, List.cons_append,
                List.nil_append]]
            exact lit_append "}" rest]
      simp only [Option.map_some]

set_option maxHeartbeats 1000000 in
/-- **The Wave-3 `sealA` arm (the one Cap-bearing action arm) round-trips** — `{"seal":[pid,actor,CAP]}`.
The DE-SHADOWED seal carries a `Cap` PAYLOAD field (the sealed capability the box binds), so it is NOT a
flat `N`/`I`/`A` arm (`isSimpleArm .sealA = false`); it is closed SEPARATELY here, reusing §C's
`parseCap_encode` for the cap field. With this + `parseActionW_roundtrip` + `parseActionW_setfield`, EVERY
`FullActionA` arm (incl. the Wave-3 lifecycle/seal arms) carries a parse∘encode theorem. -/
theorem parseActionW_seal (pid : Nat) (actor : CellId) (payload : Authority.Cap) (rest : PState) :
    parseActionW ((encodeActionW (.sealA pid actor payload)).toList ++ rest)
      = some (.sealA pid actor payload, rest) := by
  unfold parseActionW parseActionWFuel
  simp only [encodeActionW, String.toList_append, List.append_assoc]
  skip_to_arm
  -- dispatched to the `seal` tag: parse `pid` (post-`,`), `actor` (post-`,`), then `,` + the CAP, then `]}`.
  rw [lit_append]
  simp only [parseNat_toString _ _ (nd_litComma _), cN_step _ _ (nd_litComma _),
    parseCap_encode payload (("]}":String).toList ++ rest), lit_append,
    Option.bind_eq_bind, Option.bind]

-- A Wave-3 SEAL effect (the Cap-bearing arm) round-trips (the WHAT decoder is COMPLETE, every arm):
example : parseActionW ((encodeActionW (.sealA 7 8 (Authority.Cap.endpoint 9 [.read]))).toList ++ ['x'])
            = some (.sealA 7 8 (Authority.Cap.endpoint 9 [.read]), ['x']) :=
  parseActionW_seal 7 8 (Authority.Cap.endpoint 9 [.read]) ['x']

private def encodeCapListTail (cs : List Authority.Cap) : String :=
  cs.foldl (fun acc x => acc ++ "," ++ encodeCap x) ""

/-- Every `CAP` opens with `'{'` — the head char that makes `lit "[]"` fail on a `[{`-led `CAPLIST`. -/
private theorem encodeCap_head (c : Authority.Cap) : ∃ t, (encodeCap c).toList = '{' :: t := by
  cases c with
  | null => exact ⟨"\"null\":0}".toList, by unfold encodeCap; rfl⟩
  | node t => refine ⟨("\"node\":" ++ toString t ++ "}" : String).toList, ?_⟩
              unfold encodeCap
              simp only [String.toList_append, show ("{\"node\":":String).toList = '{' :: "\"node\":".toList from by decide,
                List.cons_append, List.nil_append, List.append_assoc]
  | endpoint t r => refine ⟨("\"ep\":[" ++ toString t ++ "," ++ encodeAuths r ++ "]}" : String).toList, ?_⟩
                    unfold encodeCap
                    simp only [String.toList_append, show ("{\"ep\":[":String).toList = '{' :: "\"ep\":[".toList from by decide,
                      List.cons_append, List.nil_append, List.append_assoc]

private theorem foldl_capListTail (cs : List Authority.Cap) : ∀ (acc : String),
    cs.foldl (fun s x => s ++ "," ++ encodeCap x) acc
      = acc ++ cs.foldl (fun s x => s ++ "," ++ encodeCap x) "" := by
  induction cs with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeCap b), ih ("" ++ "," ++ encodeCap b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encCapListTail_cons_shape (b : Authority.Cap) (bs : List Authority.Cap) (rest : PState) :
    (encodeCapListTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeCap b).toList ++ ((encodeCapListTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeCapListTail (b :: bs) = ("" ++ "," ++ encodeCap b) ++ encodeCapListTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeCap x) "" = _
      rw [List.foldl_cons]; exact foldl_capListTail bs ("" ++ "," ++ encodeCap b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeCapList_cons_shape (a : Authority.Cap) (as : List Authority.Cap) (rest : PState) :
    (encodeCapList (a :: as)).toList ++ rest
      = '[' :: ((encodeCap a).toList ++ ((encodeCapListTail as).toList ++ (']' :: rest))) := by
  rw [show encodeCapList (a :: as) = "[" ++ encodeCap a ++ encodeCapListTail as ++ "]" from by
        show "[" ++ encodeCap a ++ (as.foldl (fun acc x => acc ++ "," ++ encodeCap x) "") ++ "]" = _
        rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

private theorem parseCapList_loop_works : ∀ (as : List Authority.Cap) (a : Authority.Cap)
    (rest : PState) (fuel : Nat),
    ((encodeCap a).toList ++ ((encodeCapListTail as).toList ++ (']' :: rest))).length < fuel →
    parseCapList.loop fuel ((encodeCap a).toList ++ ((encodeCapListTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeCapListTail ([] : List Authority.Cap)).toList = [] from rfl, List.nil_append]
      unfold parseCapList.loop
      rw [parseCap_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encCapListTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseCapList.loop
      rw [parseCap_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeCap a2).toList ++ ((encodeCapListTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **The `CAPLIST` array roundtrip** (`parseCapList ∘ encodeCapList = id`) — a holder's cap list. -/
theorem parseCapList_encode (cs : List Authority.Cap) (rest : PState) :
    parseCapList ((encodeCapList cs).toList ++ rest) = some (cs, rest) := by
  cases cs with
  | nil =>
      unfold parseCapList
      rw [show (encodeCapList ([] : List Authority.Cap)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseCapList
      rw [encodeCapList_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeCap a).toList ++ ((encodeCapListTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeCap_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '{' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseCapList_loop_works as a rest
      simp only [List.length_cons]; omega

/-- The `CAPENTRY` encoder (the inline `one` lambda of `encodeCapsEntries`, named for the proof). -/
def encodeCapEntry (p : CellId × List Authority.Cap) : String :=
  "[" ++ toString p.1 ++ "," ++ encodeCapList p.2 ++ "]"

/-- **One `CAPENTRY` `[holder,CAPLIST]` round-trips** — the holder `Nat` (post-byte `,`) then the
`CAPLIST` via `parseCapList_encode`, then the closing `]` (`parseCapList` leaves its argument `rest`).
Self-delimiting. -/
theorem parseCapEntry_encode (p : CellId × List Authority.Cap) (rest : PState) :
    parseCapEntry ((encodeCapEntry p).toList ++ rest) = some (p, rest) := by
  obtain ⟨holder, cl⟩ := p
  unfold parseCapEntry encodeCapEntry
  rw [show (("[" ++ toString holder ++ "," ++ encodeCapList cl ++ "]":String).toList ++ rest)
        = ("[":String).toList ++ ((toString holder).toList ++ (',' :: ((encodeCapList cl).toList
            ++ (']' :: rest)))) from by
      simp only [String.toList_append, show (",":String).toList = [','] from by decide,
        show ("]":String).toList = [']'] from by decide, List.append_assoc, List.cons_append,
        List.nil_append]]
  rw [lit_append]
  simp only []
  rw [parseNat_toString holder _ (nd_comma _)]
  simp only []
  rw [show lit "," (',' :: ((encodeCapList cl).toList ++ (']' :: rest)))
        = some ((encodeCapList cl).toList ++ (']' :: rest)) from by
      rw [show (',' :: ((encodeCapList cl).toList ++ (']' :: rest)))
            = ("," : String).toList ++ ((encodeCapList cl).toList ++ (']' :: rest)) from by
          simp only [show (",":String).toList = [','] from by decide, List.cons_append,
            List.nil_append]]
      exact lit_append "," _]
  simp only []
  rw [parseCapList_encode cl (']' :: rest)]
  simp only []
  rw [show lit "]" (']' :: rest) = some rest from by
        rw [show (']' :: rest) = ("]" : String).toList ++ rest from by
          simp only [show ("]":String).toList = [']'] from by decide, List.cons_append,
            List.nil_append]]
        exact lit_append "]" rest]
  simp only [Option.map_some]

private def encodeCapsEntriesTail (es : List (CellId × List Authority.Cap)) : String :=
  es.foldl (fun acc x => acc ++ "," ++ encodeCapEntry x) ""

/-- A `CAPENTRY` opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). -/
private theorem encodeCapEntry_head (p : CellId × List Authority.Cap) : ∃ t, (encodeCapEntry p).toList = '[' :: t := by
  refine ⟨(toString p.1 ++ "," ++ encodeCapList p.2 ++ "]" : String).toList, ?_⟩
  unfold encodeCapEntry
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_capsEntriesTail (es : List (CellId × List Authority.Cap)) : ∀ (acc : String),
    es.foldl (fun s x => s ++ "," ++ encodeCapEntry x) acc
      = acc ++ es.foldl (fun s x => s ++ "," ++ encodeCapEntry x) "" := by
  induction es with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeCapEntry b), ih ("" ++ "," ++ encodeCapEntry b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encCapsEntriesTail_cons_shape (b : CellId × List Authority.Cap)
    (bs : List (CellId × List Authority.Cap)) (rest : PState) :
    (encodeCapsEntriesTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeCapEntry b).toList ++ ((encodeCapsEntriesTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeCapsEntriesTail (b :: bs) = ("" ++ "," ++ encodeCapEntry b) ++ encodeCapsEntriesTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeCapEntry x) "" = _
      rw [List.foldl_cons]; exact foldl_capsEntriesTail bs ("" ++ "," ++ encodeCapEntry b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeCapsEntries_cons_shape (a : CellId × List Authority.Cap)
    (as : List (CellId × List Authority.Cap)) (rest : PState) :
    (encodeCapsEntries (a :: as)).toList ++ rest
      = '[' :: ((encodeCapEntry a).toList ++ ((encodeCapsEntriesTail as).toList ++ (']' :: rest))) := by
  rw [show encodeCapsEntries (a :: as) = "[" ++ encodeCapEntry a ++ encodeCapsEntriesTail as ++ "]" from by
        show "[" ++ (fun (p : CellId × List Authority.Cap) => "[" ++ toString p.1 ++ "," ++ encodeCapList p.2 ++ "]") a
            ++ (as.foldl (fun acc p => acc ++ "," ++ (fun (p : CellId × List Authority.Cap) => "[" ++ toString p.1 ++ "," ++ encodeCapList p.2 ++ "]") p) "") ++ "]" = _
        rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

private theorem parseCapsEntries_loop_works : ∀ (as : List (CellId × List Authority.Cap))
    (a : CellId × List Authority.Cap) (rest : PState) (fuel : Nat),
    ((encodeCapEntry a).toList ++ ((encodeCapsEntriesTail as).toList ++ (']' :: rest))).length < fuel →
    parseCapsEntries.loop fuel ((encodeCapEntry a).toList ++ ((encodeCapsEntriesTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeCapsEntriesTail ([] : List (CellId × List Authority.Cap))).toList = [] from rfl, List.nil_append]
      unfold parseCapsEntries.loop
      rw [parseCapEntry_encode a (']' :: rest)]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hf
      rw [encCapsEntriesTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseCapsEntries.loop
      rw [parseCapEntry_encode a _]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeCapEntry a2).toList ++ ((encodeCapsEntriesTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hrec]

/-- **FILL J production (k): the `CAPS` table roundtrip** (`parseCapsEntries ∘ encodeCapsEntries = id`) —
the STATE DECODER's capability store: `(holder, capList)` entries, each cap a `null`/`node`/`ep` sum (the
`ep` arm carrying a narrow AUTHS rights array via §8). No `Wf` hypothesis (all `Nat`/narrow-tag). -/
theorem parseCapsEntries_encode (es : List (CellId × List Authority.Cap)) (rest : PState) :
    parseCapsEntries ((encodeCapsEntries es).toList ++ rest) = some (es, rest) := by
  cases es with
  | nil =>
      unfold parseCapsEntries
      rw [show (encodeCapsEntries ([] : List (CellId × List Authority.Cap))) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      unfold parseCapsEntries
      rw [encodeCapsEntries_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeCapEntry a).toList ++ ((encodeCapsEntriesTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeCapEntry_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseCapsEntries_loop_works as a rest
      simp only [List.length_cons]; omega

/-! ## §11d — the per-node `CAVEATS` array (`parseCaveatsW`) roundtrip — the SOUNDNESS-FIX discharge leg
(§W5c). The transported tiered caveat thread that gives `caveatsDischarged` real teeth over the swap
boundary. Length-fuel loop (§10/§11 template); the element is the SELF-DELIMITING `[tier,cell,asset,min]`
tuple (`parseCaveatW`), where `tier ∈ {0,1,2,3}` (the `DriftStable.DriftTier` ordinal) is the codec's ONE
boundary constraint — the parser's `if tier > 3 then none` guard rejects an out-of-range tier, so the
roundtrip carries a per-element `WfCaveat` (`c.tier ≤ 3`), exactly the §1-`WfValue`/§6-`WfAuthList`
boundary discipline. (`cell`/`asset` are unconstrained `Nat`; `min` is signed `Int` via `cI`.) A
caveat-codec bug — a dropped tier, a sign flip on the threshold, a mis-bracketed body — is now caught. -/

/-- The per-caveat well-formedness boundary: the `tier` ordinal is in `{0,1,2,3}` (the four
`DriftStable.DriftTier` levels). This is exactly the constraint `parseCaveatW`'s `if tier > 3` guard
pins; the encoder writes the tier verbatim, so the round-trip holds precisely on well-formed tiers. -/
def WfCaveat (c : WCaveat) : Prop := c.tier ≤ 3

/-- A `CAVEATS` array is well-formed iff every caveat is (every `tier ∈ {0,1,2,3}`). -/
def WfCaveats : List WCaveat → Prop
  | []      => True
  | c :: cs => WfCaveat c ∧ WfCaveats cs

set_option maxHeartbeats 1000000 in
/-- **The `WCAVEAT` entry roundtrip** — the 4-field tuple `[tier,cell,asset,min]`. The leading `tier`
walks via `parseNat` (post-byte `,`); its `if tier > 3` guard is discharged `else`-ward by `htier`
(`c.tier ≤ 3`, so `¬ (3 < c.tier)`). The `cell`/`asset` `Nat`s and signed `min` `Int` walk via
`cN_step`/`cI_step` (post-byte `,`/`]`); self-delimiting, so it round-trips for ANY tail. -/
theorem parseCaveatW_encode (c : WCaveat) (rest : PState) (htier : WfCaveat c) :
    parseCaveatW ((encodeCaveatW c).toList ++ rest) = some (c, rest) := by
  unfold parseCaveatW encodeCaveatW WfCaveat at *
  simp only [String.toList_append, List.append_assoc]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString c.tier _ (nd_litComma _)]; simp only [Option.bind]
  rw [if_neg (by omega : ¬ c.tier > 3)]
  simp only [cN_step _ _ (nd_litComma _), cI_step _ _ (nd_litBrack _), Option.bind_eq_bind, Option.bind]
  rw [lit_append]

private def encodeCaveatsWTail (cs : List WCaveat) : String :=
  cs.foldl (fun acc x => acc ++ "," ++ encodeCaveatW x) ""

/-- A `WCAVEAT` entry opens with `'['` (so the list body is `[[…`, making `lit "[]"` fail). Explicit
witness ⇒ no metavar. -/
private theorem encodeCaveatW_head (c : WCaveat) : ∃ t, (encodeCaveatW c).toList = '[' :: t := by
  refine ⟨(toString c.tier ++ "," ++ toString c.cell ++ "," ++ toString c.asset ++ ","
    ++ toString c.min ++ "]" : String).toList, ?_⟩
  unfold encodeCaveatW
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl, List.cons_append,
    List.nil_append, List.append_assoc]

private theorem foldl_caveatsWTail (cs : List WCaveat) : ∀ (acc : String),
    cs.foldl (fun s x => s ++ "," ++ encodeCaveatW x) acc
      = acc ++ cs.foldl (fun s x => s ++ "," ++ encodeCaveatW x) "" := by
  induction cs with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeCaveatW b), ih ("" ++ "," ++ encodeCaveatW b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

private theorem encCaveatsWTail_cons_shape (b : WCaveat) (bs : List WCaveat) (rest : PState) :
    (encodeCaveatsWTail (b :: bs)).toList ++ rest
      = ',' :: ((encodeCaveatW b).toList ++ ((encodeCaveatsWTail bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeCaveatsWTail (b :: bs) = ("" ++ "," ++ encodeCaveatW b) ++ encodeCaveatsWTail bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeCaveatW x) "" = _
      rw [List.foldl_cons]; exact foldl_caveatsWTail bs ("" ++ "," ++ encodeCaveatW b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

private theorem encodeCaveatsW_cons_shape (a : WCaveat) (as : List WCaveat) (rest : PState) :
    (encodeCaveatsW (a :: as)).toList ++ rest
      = '[' :: ((encodeCaveatW a).toList ++ ((encodeCaveatsWTail as).toList ++ (']' :: rest))) := by
  rw [show encodeCaveatsW (a :: as) = "[" ++ encodeCaveatW a ++ encodeCaveatsWTail as ++ "]" from rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

set_option maxHeartbeats 1000000 in
/-- **The loop recovers the caveat list**, given the `input.length < fuel` invariant AND that every
caveat is well-formed (each `tier ≤ 3`, threaded through `parseCaveatW_encode`). By induction on the
tail (the head `a` generalized); the recursive call lands at `fuel-1` with strictly-shorter input. -/
private theorem parseCaveatsW_loop_works : ∀ (as : List WCaveat) (a : WCaveat)
    (rest : PState) (fuel : Nat), WfCaveat a → WfCaveats as →
    ((encodeCaveatW a).toList ++ ((encodeCaveatsWTail as).toList ++ (']' :: rest))).length < fuel →
    parseCaveatsW.loop fuel ((encodeCaveatW a).toList ++ ((encodeCaveatsWTail as).toList ++ (']' :: rest)))
      = some (a :: as, rest) := by
  intro as
  induction as with
  | nil =>
      intro a rest fuel hwfa _ hf
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      rw [show (encodeCaveatsWTail ([] : List WCaveat)).toList = [] from rfl, List.nil_append]
      unfold parseCaveatsW.loop
      rw [parseCaveatW_encode a (']' :: rest) hwfa]
      simp only []
      rw [show lit "," (']' :: rest) = none from by
            rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
            exact lit_ne_pre "," "]" rest (by decide) (by decide)]
      simp only []
      rw [lit_brack]
  | cons a2 as2 ih =>
      intro a rest fuel hwfa hwfas hf
      obtain ⟨hwfa2, hwfas2⟩ : WfCaveat a2 ∧ WfCaveats as2 := hwfas
      rw [encCaveatsWTail_cons_shape a2 as2 (']' :: rest)] at hf ⊢
      obtain ⟨f, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by
        simp only [List.length_append, List.length_cons] at hf; omega⟩
      unfold parseCaveatsW.loop
      rw [parseCaveatW_encode a _ hwfa]
      simp only []
      rw [lit_commaC]
      simp only []
      have hrec : ((encodeCaveatW a2).toList ++ ((encodeCaveatsWTail as2).toList ++ (']' :: rest))).length < f := by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega
      rw [ih a2 rest f hwfa2 hwfas2 hrec]

set_option maxHeartbeats 1000000 in
/-- **FILL J production (l): the per-node `CAVEATS` array roundtrip** (`parseCaveatsW ∘ encodeCaveatsW =
id`) — the SOUNDNESS-FIX discharge leg (§W5c). The transported tiered caveat thread, round-tripped
FAITHFULLY (every `tier ∈ {0,1,2,3}` via `WfCaveats`; a dropped tier / sign-flipped threshold is caught),
so a violated caveat fail-closes the gate over the swap boundary. -/
theorem parseCaveatsW_encode (cs : List WCaveat) (rest : PState) (hwf : WfCaveats cs) :
    parseCaveatsW ((encodeCaveatsW cs).toList ++ rest) = some (cs, rest) := by
  cases cs with
  | nil =>
      unfold parseCaveatsW
      rw [show (encodeCaveatsW ([] : List WCaveat)) = "[]" from rfl]
      rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
  | cons a as =>
      obtain ⟨hwfa, hwfas⟩ : WfCaveat a ∧ WfCaveats as := hwf
      unfold parseCaveatsW
      rw [encodeCaveatsW_cons_shape a as rest]
      have hempty : lit "[]"
          ('[' :: ((encodeCaveatW a).toList ++ ((encodeCaveatsWTail as).toList ++ (']' :: rest)))) = none := by
        obtain ⟨t, ht⟩ := encodeCaveatW_head a
        rw [ht, List.cons_append]
        unfold lit
        rw [show ("[]":String).toList = ['[', ']'] from by decide]
        rw [litGo_cons_match, litGo_ne_head ']' [] '[' _ (by decide)]
      rw [hempty]; simp only []
      rw [lit_lbrack]
      simp only []
      apply parseCaveatsW_loop_works as a rest _ hwfa hwfas
      simp only [List.length_cons]; omega

/-- NON-VACUITY: a real tiered caveat list round-trips (a `.locked`/tier-2 threshold and a `.monotone`/
tier-0 read, the `min` a NEGATIVE bound — the sign is load-bearing). -/
example : parseCaveatsW ((encodeCaveatsW
    [{ tier := 2, cell := 7, asset := 3, min := -5 }, { tier := 0, cell := 1, asset := 1, min := 9 }]).toList
      ++ ['x'])
    = some ([{ tier := 2, cell := 7, asset := 3, min := -5 }, { tier := 0, cell := 1, asset := 1, min := 9 }], ['x']) :=
  -- `WfCaveats [c₁,c₂]` is DEFINITIONALLY `c₁.tier ≤ 3 ∧ c₂.tier ≤ 3 ∧ True`; give each leaf as the
  -- bare `≤` (whnf checks it against the folded `WfCaveat` — avoids needing a `Decidable (WfCaveat …)`).
  parseCaveatsW_encode _ ['x'] ⟨(by decide : (2:Nat) ≤ 3), (by decide : (0:Nat) ≤ 3), trivial⟩

/-! ## §15 — the RECURSIVE action-TREE (`parseForestW`/`parseChildrenW`) roundtrip — FILL-J production
(the call-FOREST + delegation edges). THE hardest production: a four-way mutual recursion (`parseForestW`
/ `parseChildrenW` / `parseChildrenLoopW` / `parseChildW`), each fuel-bounded for structural termination.
A node `{"auth":AUTH,"caveats":WCAVEATS,"action":ACTIONW,"children":KIDS}` carries the per-node credential
(§6 `parseAuthW_roundtrip`, the WHO), the tiered caveats (§11d `parseCaveatsW_encode`, the discharge leg),
the 51-arm action (§7 `parseActionW_roundtrip`/`_setfield`, the WHAT), and the delegated children, each a
`{"holder":N,"keep":AUTHS,"cap":CAP,"sub":NODE}` edge carrying its attenuation `keep` (§8
`parseAuths_encode`), the delegated `parentCap` (§13 `parseCap_encode`), and the recursive sub-tree.

It mirrors §6's `authGoal_all` exactly: a bundled mutual goal (forest / children-list / children-loop),
strong-induction on fuel, the recursive `children` arm threading fuel through the edge list as §6's
`oneOf` threads it through the candidate list. The ONE structural delta from §6 is the EXTRA `parseChildW`
fuel layer between the children-loop and the recursive `parseForestW` call: the loop decrements once to
reach `parseChildW`, which decrements again to reach `parseForestW`. So `childrenSize` charges `+2` per
edge (vs §6's `+1`), guaranteeing two fuel units survive each descent. A symmetric codec bug anywhere in
the tree — a forged credential on a deep node, a dropped delegation edge, a mis-bracketed sub-tree —
passes the differential silently; this theorem, pinning `parseForestW` as the genuine left-inverse of
`encodeForestW`, catches it, removing the whole action-tree codec from the Lean-side TCB. -/

/-! ### §15a — well-formedness (the codec boundary, mutual over the tree). The node's `auth` carries the
§6 `WfAuth` boundary (digests `< 2^256`), its `caveats` the §11d `WfCaveats` (`tier ≤ 3`), and its
`action` an escape-free `setFieldA` field name (every other arm is unconstrained); children recurse. -/

/-- The per-node ACTION boundary: a `setFieldA` field name must be escape-free (no `"`/`\`), exactly the
§7 `parseActionW_setfield` hypothesis; an `exerciseA`'s codec-roundtrip boundary is `inner = []` (the
bare cap-exercise — the de-shadowed EXECUTOR runs ANY inner list, proven in `TurnExecutorFull`; the
codec roundtrip THEOREM for a NON-empty nested inner array is the FILL-J recursive-grammar followup,
`#136` — it needs a fuel-threaded mutual `parseActionsWFuel`-inverts-`encodeActionsW` lemma); every
other (`simple`) arm is unconstrained. -/
def WfActionW : TurnExecutorFull.FullActionA → Prop
  | .setFieldA _ _ field _ => ∀ c ∈ field.toList, c ≠ '"' ∧ c ≠ '\\'
  | .exerciseA _ _ inner   => inner = []
  | _                      => True

/-- `parseActionsWFuel` on a leading `]` is the empty-array base case, for ANY successor fuel. -/
private theorem parseActionsWFuel_leadBracket (n : Nat) (X : PState) :
    parseActionsWFuel (n + 1) (']' :: X) = some ([], ']' :: X) := by
  simp only [parseActionsWFuel]

/-- **The empty-inner `exerciseA` arm round-trips** — `{"exercise":[actor,target,[]]}` parses back to
`.exerciseA actor target []`. The bare cap-exercise wire form (the inner array is the empty `[]`); the
fuel never recurses (the inner-array parser hits the `']' :: _` base case immediately). The non-empty
nested case is the FILL-J followup (`#136`). -/
theorem parseActionW_exercise_nil (actor target : CellId) (rest : PState) :
    parseActionW ((encodeActionW (.exerciseA actor target [])).toList ++ rest)
      = some (.exerciseA actor target [], rest) := by
  unfold parseActionW parseActionWFuel
  simp only [encodeActionW, encodeActionsW, String.toList_append, List.append_assoc]
  skip_to_arm
  -- read actor (`parseNat`, closer `,`) + target (`cN`, whose closer is the `,` of the `,[` separator —
  -- proved non-digit by the inline `hnd`). The post-target tail is `,[` ++ `]]}` ++ rest: `lit ",["`
  -- fires, then `parseActionsWFuel` sees the leading `]` of `]]}` (base case ⇒ `[]`), then `lit "]"` +
  -- `lit "]}"` close the two brackets.
  have hnd : ∀ rest' : PState, (",[":String).toList ++ rest' = []
      ∨ ∃ c rs, (",[":String).toList ++ rest' = c :: rs ∧ c.isDigit = false :=
    fun rest' => Or.inr ⟨',', ('[' :: rest'), by rfl, by decide⟩
  -- the inner-array parse on a leading `]` ⇒ `[]` (`parseActionsWFuel_leadBracket` over the successor
  -- seed fuel), then `lit "]"`/`lit "]}"` consume the closing brackets.
  have hb1 : ∀ X : PState, lit "]" (']' :: X) = some X := fun X => by
    rw [show (']' :: X) = ("]" : String).toList ++ X from by
          rw [show ("]" : String).toList = [']'] from by decide]; rfl]
    exact lit_append _ _
  -- read actor (`parseNat`) + target (`cN`) + `lit ",["`, exposing the inner-array parse. `List.cons_append`
  -- normalizes `(']' :: …) ++ …` (note `::` binds TIGHTER than `++`) to `']' :: (… ++ …)` so the leading
  -- `]` is exposed for the base case.
  simp only [lit_append, parseNat_toString _ _ (nd_litComma _), cN_step _ _ (hnd _),
    show ("]]}" : String).toList = ']' :: "]}".toList from by decide,
    show ("" : String).toList = [] from by decide, List.nil_append, List.cons_append,
    parseActionsWFuel_leadBracket, hb1, Option.bind_eq_bind, Option.bind]

/-- **`parseActionW` inverts `encodeActionW` on EVERY arm** — the `simple` arms via §7's
`parseActionW_roundtrip`, the `setFieldA` arm via §7's `parseActionW_setfield` (under its escape-free
`WfActionW`), and the bare `exerciseA` (`inner = []`) via `parseActionW_exercise_nil`. The unified
WHAT-decoder leaf the node element calls. -/
theorem parseActionW_any (act : TurnExecutorFull.FullActionA) (rest : PState) (hwf : WfActionW act) :
    parseActionW ((encodeActionW act).toList ++ rest) = some (act, rest) := by
  cases act with
  | setFieldA actor cell field v => exact parseActionW_setfield actor cell field v rest hwf
  | sealA pid actor payload => exact parseActionW_seal pid actor payload rest   -- Wave-3 Cap-bearing arm
  | exerciseA actor target inner =>
      -- `WfActionW` pins `inner = []` (the codec boundary); the empty-inner arm round-trips.
      simp only [WfActionW] at hwf; subst hwf
      exact parseActionW_exercise_nil actor target rest
  | _ => exact parseActionW_roundtrip _ rest rfl

mutual
/-- Well-formed `WForest`: a well-formed credential (§6), well-formed caveats (§11d), a well-formed action
(escape-free `setFieldA` name), and well-formed children (recursively). Constructor-pattern form (the
structural recursion the termination checker needs sees `sub`/`kids` as subterms). -/
def WfForest : WForest → Prop
  | ⟨na, cavs, a, kids⟩ => WfAuth na ∧ WfCaveats cavs ∧ WfActionW a ∧ WfChildren kids
/-- Well-formed child-edge list: each edge's sub-tree is well-formed (the `keep`/`parentCap` are narrow
total codecs — no boundary). -/
def WfChildren : List WChild → Prop
  | []                  => True
  | ⟨_, _, _, sub⟩ :: cs => WfForest sub ∧ WfChildren cs
end

/-! ### §15b — the structural fuel measure (mutual). Each EDGE charges `+2` (the children-loop +
`parseChildW` double fuel descent to the recursive sub-tree), plus the sub-tree's own size; the node
charges `+1` over its credential and children. The fuel-adequacy: this measure DOMINATES the parse depth,
so each `fuel=0`/decremented sub-call lands with fuel to spare. -/
mutual
/-- Structural size of a `WForest`: `1 + authSize auth + childrenSize children`. Constructor-pattern form. -/
def forestSize : WForest → Nat
  | ⟨na, _, _, kids⟩ => 1 + authSize na + childrenSize kids
/-- Structural size of a child-edge list: `Σ (2 + forestSize sub)` (the `+2` covers the two fuel layers
between the children-loop and the recursive `parseForestW`). -/
def childrenSize : List WChild → Nat
  | []                  => 0
  | ⟨_, _, _, sub⟩ :: cs => 2 + forestSize sub + childrenSize cs
end

/-! ### §15c — the EDGE-list (KIDS) tail encoder normalized into peelable cons form (mirroring §6d). -/

/-- The `KIDS` tail encoder (the `foldl` body in cons-recursive form). -/
private def encodeChildrenTailW (cs : List WChild) : String :=
  cs.foldl (fun acc x => acc ++ "," ++ encodeChildW x) ""

/-- Every `encodeChildW` edge opens with `'{'` — the head making `lit "[]"` fail on a `[{`-led KIDS body.
Explicit witness ⇒ no metavar. -/
private theorem encodeChildW_head (c : WChild) : ∃ t, (encodeChildW c).toList = '{' :: t := by
  obtain ⟨h, k, pc, sub⟩ := c
  refine ⟨("\"holder\":" ++ toString h ++ ",\"keep\":" ++ encodeAuthsW k ++ ",\"cap\":" ++ encodeCap pc
    ++ ",\"sub\":" ++ encodeForestW sub ++ "}" : String).toList, ?_⟩
  show (encodeChildW ⟨h, k, pc, sub⟩).toList = _
  unfold encodeChildW
  simp only [String.toList_append, show ("{\"holder\":":String).toList = '{' :: "\"holder\":".toList from by decide,
    List.cons_append, List.nil_append, List.append_assoc]

/-- The accumulator pulls OUT of the tail fold (`List Char`-level, mirroring `foldl_authtail`). -/
private theorem foldl_childrenTailW (cs : List WChild) : ∀ (acc : String),
    cs.foldl (fun s x => s ++ "," ++ encodeChildW x) acc
      = acc ++ cs.foldl (fun s x => s ++ "," ++ encodeChildW x) "" := by
  induction cs with
  | nil => intro acc; apply String.toList_inj.mp; simp
  | cons b bs ih =>
      intro acc; simp only [List.foldl_cons]
      rw [ih (acc ++ "," ++ encodeChildW b), ih ("" ++ "," ++ encodeChildW b)]
      apply String.toList_inj.mp; simp [String.toList_append, List.append_assoc]

/-- Rebracket a NON-EMPTY edge TAIL `,EDGE ++ TAIL` into comma-then-edge-then-tail (peelable). -/
private theorem encChildrenTailW_cons_shape (b : WChild) (bs : List WChild) (rest : PState) :
    (encodeChildrenTailW (b :: bs)).toList ++ rest
      = ',' :: ((encodeChildW b).toList ++ ((encodeChildrenTailW bs).toList ++ rest)) := by
  conv_lhs => rw [show encodeChildrenTailW (b :: bs)
      = ("" ++ "," ++ encodeChildW b) ++ encodeChildrenTailW bs from by
      show (b :: bs).foldl (fun s x => s ++ "," ++ encodeChildW x) "" = _
      rw [List.foldl_cons]; exact foldl_childrenTailW bs ("" ++ "," ++ encodeChildW b)]
  simp only [String.toList_append, show ("":String).toList = [] from rfl,
    show (",":String).toList = [','] from rfl, List.nil_append, List.cons_append, List.append_assoc]

/-- Rebracket a NON-EMPTY edge LIST `[EDGE ++ TAIL ++ ]` into open-`[`-then-body form. -/
private theorem encodeChildrenW_cons_shape (a : WChild) (as : List WChild) (rest : PState) :
    (encodeChildrenW (a :: as)).toList ++ rest
      = '[' :: ((encodeChildW a).toList ++ ((encodeChildrenTailW as).toList ++ (']' :: rest))) := by
  conv_lhs => rw [show encodeChildrenW (a :: as)
                = "[" ++ encodeChildW a ++ encodeChildrenTailW as ++ "]" from by
              unfold encodeChildrenW; rfl]
  simp only [String.toList_append, show ("[":String).toList = ['['] from rfl,
    show ("]":String).toList = [']'] from rfl]
  simp [List.append_assoc]

/-! ### §15d — the NODE/EDGE `do`-block element shapes (rebracket into the parser-step sequence).

`encodeForestW`/`encodeChildW` are `String ++` chains; we rebracket each into the right-associated
`tag ++ (field ++ (sep ++ …))` form the `lit`/sub-parse steps consume. Following §11's perf gotchas: a
single `String.toList_append`/`List.append_assoc` `simp only` (NOT full `simp`) right-associates the
whole chain, and the closing `}` is exposed as `'}' :: rest`. -/

/-- Rebracket the NODE encoding into the `{"auth":` ++ AUTH ++ ,"caveats": ++ … sequence. -/
private theorem encForestW_node_shape (na : AuthW) (cavs : List WCaveat) (a : TurnExecutorFull.FullActionA)
    (kids : List WChild) (rest : PState) :
    (encodeForestW ⟨na, cavs, a, kids⟩).toList ++ rest
      = ("{\"auth\":":String).toList ++ ((encodeAuthW na).toList
          ++ ((",\"caveats\":":String).toList ++ ((encodeCaveatsW cavs).toList
          ++ ((",\"action\":":String).toList ++ ((encodeActionW a).toList
          ++ ((",\"children\":":String).toList ++ ((encodeChildrenW kids).toList
          ++ ('}' :: rest)))))))) := by
  show (encodeForestW ⟨na, cavs, a, kids⟩).toList ++ rest = _
  unfold encodeForestW
  simp only [String.toList_append, show ("}":String).toList = ['}'] from by decide,
    List.append_assoc, List.cons_append, List.nil_append]

/-- Rebracket one EDGE encoding into the `{"holder":` ++ N ++ ,"keep": ++ … sequence. -/
private theorem encChildW_edge_shape (h : CellId) (k : List Authority.Auth) (pc : Authority.Cap)
    (sub : WForest) (rest : PState) :
    (encodeChildW ⟨h, k, pc, sub⟩).toList ++ rest
      = ("{\"holder\":":String).toList ++ ((toString h).toList
          ++ ((",\"keep\":":String).toList ++ ((encodeAuthsW k).toList
          ++ ((",\"cap\":":String).toList ++ ((encodeCap pc).toList
          ++ ((",\"sub\":":String).toList ++ ((encodeForestW sub).toList
          ++ ('}' :: rest)))))))) := by
  show (encodeChildW ⟨h, k, pc, sub⟩).toList ++ rest = _
  unfold encodeChildW
  simp only [String.toList_append, show ("}":String).toList = ['}'] from by decide,
    List.append_assoc, List.cons_append, List.nil_append]

/-! ### §15e — the bundled fuel-adequate roundtrip (forest / children-list / children-loop, by strong
induction on fuel). Mirrors §6e: establish the LOOP clause (depends on the IH at strictly-smaller fuel
through `parseChildW`'s sub-tree call), then the LIST clause re-uses it at the same fuel, then the FOREST
clause runs the node `do`-block (auth §6 → caveats §11d → action §7 → children via the LIST clause). -/

/-- The bundled mutual goal at a given fuel: the forest parser, the children-list parser, and the
children-loop body all recover their argument whenever the fuel meets the `forestSize`/`childrenSize`
bound. The loop clause is stated over the loop BODY (post opening-`[`): the first edge, the
comma-prefixed tail, then the closing `]`. -/
private def ForestGoal (fuel : Nat) : Prop :=
  (∀ (f : WForest) (rest : PState), WfForest f → forestSize f ≤ fuel →
      parseForestW fuel ((encodeForestW f).toList ++ rest) = some (f, rest))
  ∧ (∀ (cs : List WChild) (rest : PState), WfChildren cs → childrenSize cs ≤ fuel →
      parseChildrenW fuel ((encodeChildrenW cs).toList ++ rest) = some (cs, rest))
  ∧ (∀ (a : WChild) (as' : List WChild) (rest : PState), WfForest a.sub → WfChildren as' →
        childrenSize (a :: as') ≤ fuel →
      parseChildrenLoopW fuel ((encodeChildW a).toList ++ ((encodeChildrenTailW as').toList ++ (']' :: rest)))
        = some (a :: as', rest))

set_option maxHeartbeats 1000000 in
/-- **The combined action-TREE fuel-adequate roundtrip.** By STRONG induction on fuel; each recursive
sub-call lands at strictly-smaller fuel (the `+2` edge charge guarantees the `parseChildW`→`parseForestW`
double descent stays funded), so the IH applies. The engine; the public `parseForestW_roundtrip` /
`parseChildrenW_roundtrip` below unwrap it. -/
private theorem forestGoal_all : ∀ fuel, ForestGoal fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    -- LOOP clause first (depends only on IH at strictly-smaller fuel through `parseChildW`).
    have hloop : ∀ (a : WChild) (as' : List WChild) (rest : PState), WfForest a.sub → WfChildren as' →
        childrenSize (a :: as') ≤ fuel →
        parseChildrenLoopW fuel ((encodeChildW a).toList ++ ((encodeChildrenTailW as').toList ++ (']' :: rest)))
          = some (a :: as', rest) := by
      intro a as' rest hwfa hwfas hsz
      obtain ⟨h, k, pc, sub⟩ := a
      -- `childrenSize (⟨h,k,pc,sub⟩::as')` reduces DEFINITIONALLY (constructor match) to the RHS:
      have hsz' : 2 + forestSize sub + childrenSize as' ≤ fuel := hsz
      -- two fuel layers: loop (g+1) → childW (g) where g ≥ 1 + forestSize sub + ...
      obtain ⟨g, rfl⟩ : ∃ k', fuel = k' + 1 := ⟨fuel - 1, by omega⟩
      unfold parseChildrenLoopW
      -- the loop's `parseChildW g` step: rebracket the edge, walk holder/keep/cap, then the sub-tree.
      obtain ⟨g', rfl⟩ : ∃ k', g = k' + 1 := ⟨g - 1, by omega⟩
      have hsubfuel : forestSize sub ≤ g' := by omega
      have hparseChild : parseChildW (g' + 1) ((encodeChildW ⟨h, k, pc, sub⟩).toList
            ++ ((encodeChildrenTailW as').toList ++ (']' :: rest)))
          = some (⟨h, k, pc, sub⟩, ((encodeChildrenTailW as').toList ++ (']' :: rest))) := by
        unfold parseChildW
        rw [encChildW_edge_shape h k pc sub ((encodeChildrenTailW as').toList ++ (']' :: rest))]
        rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
        rw [parseNat_toString h _ (Or.inr ⟨',', _, by
              rw [show (",\"keep\":":String).toList = ',' :: ("\"keep\":":String).toList from by decide]; rfl,
            by decide⟩)]
        simp only [Option.bind_eq_bind, Option.bind]
        rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
        rw [show parseAuthsW = parseAuths from rfl, show encodeAuthsW k = encodeAuths k from rfl,
            parseAuths_encode k _]
        simp only [Option.bind_eq_bind, Option.bind]
        rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
        rw [parseCap_encode pc _]; simp only [Option.bind_eq_bind, Option.bind]
        rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
        -- the recursive sub-tree via the IH at g' < g'+1 = g < g+1 = fuel:
        rw [(IH g' (by omega)).1 sub _ hwfa hsubfuel]
        simp only [Option.bind_eq_bind, Option.bind]
        rw [lit_brace]
      rw [hparseChild]
      simp only []
      cases as' with
      | nil =>
          simp only [show (encodeChildrenTailW ([] : List WChild)).toList = [] from rfl, List.nil_append]
          rw [show lit "," (']' :: rest) = none from by
                rw [show (']' :: rest) = ("]":String).toList ++ rest from rfl]
                exact lit_ne_pre "," "]" rest (by decide) (by decide)]
          simp only []
          rw [lit_brack]
      | cons a2 as2 =>
          obtain ⟨h2, k2, pc2, sub2⟩ := a2
          -- `WfChildren (⟨..⟩::as2)` / `childrenSize (⟨..⟩::as2)` now reduce (constructor match):
          obtain ⟨hwfa2, hwfas2⟩ : WfForest sub2 ∧ WfChildren as2 := hwfas
          rw [encChildrenTailW_cons_shape ⟨h2, k2, pc2, sub2⟩ as2 (']' :: rest), lit_commaC]
          simp only []
          -- the loop RECURSES at `g'+1` (`parseChildrenLoopW (g+1)` calls `parseChildrenLoopW g`, g=g'+1):
          have hszrec : childrenSize (⟨h2, k2, pc2, sub2⟩ :: as2) ≤ g' + 1 := by
            have hh : 2 + forestSize sub + (2 + forestSize sub2 + childrenSize as2) ≤ g' + 1 + 1 := hsz'
            show 2 + forestSize sub2 + childrenSize as2 ≤ g' + 1
            omega
          rw [(IH (g' + 1) (by omega)).2.2 ⟨h2, k2, pc2, sub2⟩ as2 rest hwfa2 hwfas2 hszrec]
    -- LIST clause (re-uses `hloop` at the SAME fuel).
    have hlistW : ∀ (cs : List WChild) (rest : PState), WfChildren cs → childrenSize cs ≤ fuel →
        parseChildrenW fuel ((encodeChildrenW cs).toList ++ rest) = some (cs, rest) := by
      intro cs rest hwf hsz
      match cs with
      | [] =>
          unfold parseChildrenW
          simp only [encodeChildrenW]
          rw [show (("[]":String).toList ++ rest) = ("[]":String).toList ++ rest from rfl, lit_append]
      | a :: as' =>
          obtain ⟨h, k, pc, sub⟩ := a
          obtain ⟨hwfa, hwfas⟩ : WfForest sub ∧ WfChildren as' := hwf
          unfold parseChildrenW
          rw [encodeChildrenW_cons_shape ⟨h, k, pc, sub⟩ as' rest]
          have hempty : lit "[]"
              ('[' :: ((encodeChildW ⟨h, k, pc, sub⟩).toList ++ ((encodeChildrenTailW as').toList ++ (']' :: rest)))) = none := by
            obtain ⟨t, ht⟩ := encodeChildW_head ⟨h, k, pc, sub⟩
            rw [ht, List.cons_append]; rfl
          rw [hempty]; simp only []
          rw [lit_lbrack]
          exact hloop ⟨h, k, pc, sub⟩ as' rest hwfa hwfas hsz
    refine ⟨?_, hlistW, hloop⟩
    -- FOREST clause: the node `do`-block (auth §6 → caveats §11d → action §7 → children via `hlistW`).
    intro f rest hwf hsz
    obtain ⟨na, cavs, a, kids⟩ := f
    -- `WfForest ⟨..⟩` / `forestSize ⟨..⟩` reduce DEFINITIONALLY (constructor match):
    obtain ⟨hwfna, hwfcavs, hwfa, hwfkids⟩ : WfAuth na ∧ WfCaveats cavs ∧ WfActionW a ∧ WfChildren kids := hwf
    have hsz' : 1 + authSize na + childrenSize kids ≤ fuel := hsz
    obtain ⟨f', rfl⟩ : ∃ k', fuel = k' + 1 := ⟨fuel - 1, by omega⟩
    have hnafuel : authSize na ≤ f' := by omega
    have hkidsfuel : childrenSize kids ≤ f' := by omega
    unfold parseForestW
    rw [encForestW_node_shape na cavs a kids rest]
    rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
    -- auth via §6 (parser calls `parseAuthW f'`; the IH-independent public roundtrip suffices):
    rw [parseAuthW_roundtrip na _ hwfna f' hnafuel]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
    -- caveats via §11d:
    rw [parseCaveatsW_encode cavs _ hwfcavs]; simp only [Option.bind_eq_bind, Option.bind]
    rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
    -- action via §7 (the unified leaf):
    rw [parseActionW_any a _ hwfa]; simp only [Option.bind_eq_bind, Option.bind]
    rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
    -- children: the parser calls `parseChildrenW f'` (DECREMENTED) — use the IH's LIST clause at `f'`:
    rw [(IH f' (by omega)).2.1 kids _ hwfkids hkidsfuel]; simp only [Option.bind_eq_bind, Option.bind]
    rw [lit_brace]

/-! ### §15f — the public FILL-J action-TREE roundtrip facts (the call-forest decoder leaves the TCB). -/

/-- **FILL J production (the action-TREE): the FULL `WForest` roundtrip.** Every well-formed action tree —
including the recursive delegated children — round-trips through `encodeForestW`/`parseForestW`, given
fuel `≥ forestSize f` (the structural tree-depth bound). The node's credential (§6), caveats (§11d),
action (§7), and each child's `keep`/`parentCap` (§8/§13) round-trip; the recursion is REAL (children call
back into the forest parser). This REMOVES the whole action-tree codec — the call-forest the wholesale
swap marshals — from the Lean-side TCB. -/
theorem parseForestW_roundtrip (f : WForest) (rest : PState) (hwf : WfForest f) (fuel : Nat)
    (hfuel : forestSize f ≤ fuel) :
    parseForestW fuel ((encodeForestW f).toList ++ rest) = some (f, rest) :=
  (forestGoal_all fuel).1 f rest hwf hfuel

/-- **The KIDS (children edge-list) roundtrip** (`parseChildrenW ∘ encodeChildrenW = id`) — the delegation
edges, empty or non-empty, given fuel `≥ childrenSize cs`. -/
theorem parseChildrenW_roundtrip (cs : List WChild) (rest : PState) (hwf : WfChildren cs) (fuel : Nat)
    (hfuel : childrenSize cs ≤ fuel) :
    parseChildrenW fuel ((encodeChildrenW cs).toList ++ rest) = some (cs, rest) :=
  (forestGoal_all fuel).2.1 cs rest hwf hfuel

/-! ### NON-VACUITY witnesses for the action-tree decoder (the recursion + every node field are real). -/

/-- A well-formedness proof for the §W5-eval `demoTree` (the 2-level tree with a credential + caveat on
each node): every digest `< 2^256`, every tier `≤ 3`, every action `simple`. -/
private theorem demoTree_wf : WfForest demoTree :=
  -- the nested `And` of `WfForest`/`WfChildren`/`WfCaveats` (anonymous-ctor notation whnf-reduces each
  -- mutual def against the expected type); the two `2^256` digest bounds are `signature 7`/`token 3`,
  -- the one caveat tier is `0 ≤ 3` (each leaf `show`n in its unfolded `WfAuth`/`WfCaveat` form).
  ⟨show (7:Nat) < 2^256 by norm_num, ⟨show (0:Nat) ≤ 3 by decide, trivial⟩, trivial,
    ⟨show (3:Nat) < 2^256 by norm_num, trivial, trivial,
      ⟨⟨trivial, trivial, trivial, trivial⟩, trivial⟩⟩, trivial⟩

-- The whole `demoTree` round-trips through the wire (the recursion is real — the root's child + grandchild
-- each call back into the forest parser; fuel `forestSize demoTree` is adequate):
example : parseForestW (forestSize demoTree) ((encodeForestW demoTree).toList ++ ['x'])
            = some (demoTree, ['x']) :=
  parseForestW_roundtrip demoTree ['x'] demoTree_wf (forestSize demoTree) (le_refl _)

/-! ## §14 — the WIDE STATE record (`parseWState`) roundtrip — THE STATE DECODER (the differential's
core). The 9-field `do`-block assembling every side-table proved above: cells (§12), caps (§13),
bal (§10), escrows (§11), nullifiers/commitments/revoked (§9), queues (§11b), swiss (§11c). Strict on
field ORDER + the closing `}`. Carries one `Wf` hypothesis (`WfCells w.cells`, the §1 value boundary on
the cell payloads); every other field is a total-codec side-table. Fuel-adequate whenever the outer fuel
exceeds the encoded width (the `parseWWire` caller passes the whole-input length). -/

set_option maxHeartbeats 2000000 in
/-- **FILL J production (the STATE DECODER): the WIDE STATE record roundtrip**
(`parseWState ∘ encodeWState = id`) — the post-state object the differential re-decodes. Composes the
nine side-table roundtrips through the `do`-block: each `lit ",\"field\":"` is a clean literal consume;
each field arm is its proved leaf; the cells loop's outer fuel is met by the width hypothesis. This
removes the STATE codec — the heart of the wholesale-swap differential — from the Lean-side TCB. -/
theorem parseWState_encode (w : WState) (rest : PState) (hwf : WfCells w.cells) (fuel : Nat)
    (hf : ((encodeWState w).toList ++ rest).length ≤ fuel) :
    parseWState fuel ((encodeWState w).toList ++ rest) = some (w, rest) := by
  obtain ⟨cells, caps, bal, escrows, nullifiers, commitments, queues, swiss, revoked⟩ := w
  unfold parseWState
  -- unfold `encodeWState` in BOTH `hf` and the goal (so the width hypothesis expands to the SAME
  -- field-length sum the per-field fuel obligations reference; `unfold` alone misses `hf`).
  simp only [encodeWState, String.toList_append, List.append_assoc] at hf ⊢
  -- open `{"cells":`, then the cells store (outer fuel ≥ width)
  rw [lit_append]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [parseCellsW_encode cells _ hwf fuel (by
    simp only [List.length_append] at hf ⊢; omega)]
  simp only [Option.bind_eq_bind, Option.bind]
  -- the remaining 8 fields: each a clean `lit ",\"field\":"` then its proved leaf
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseCapsEntries_encode caps _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseBal_encode bal _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseEscrows_encode escrows _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNats_encode nullifiers _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNats_encode commitments _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseQueues_encode queues _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseSwissTable_encode swiss _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNats_encode revoked _]; simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]

/-! ## §16 — the complete-turn ENVELOPE (`parseWTurn`/`parseWWire`) roundtrip — the OUTER WIRE
(the last FILL-J leaf). The Turn envelope `{"agent":N,"nonce":N,"fee":Z,"valid_until":N,"prev":"H64",
"root":NODE}` carries the dregg1 outer fields (`parseNat`/`parseInt`/`parseHex32` leaves, §0) wrapping the
recursive action-tree root (§15 `parseForestW_roundtrip`); the wire `{"state":STATEW,"turn":TURNW}` then
composes the §14 wide-state decoder with this envelope, requiring the WHOLE input consumed (`lit "}"` must
yield `some []` — fail-closed on trailing bytes). This removes the OUTERMOST codec layer — the envelope the
wholesale swap actually hands the C entry point — from the Lean-side TCB.

### §16a — the structural-fuel ADEQUACY bridge: `forestSize f ≤ (encodeForestW f).length`. The envelope
parser funds the tree recursion with `cs.length + 1` (the whole-input length); since the encoded tree is a
SUBSTRING of the input, this bound dominates `forestSize`. The bound itself: every `+1`/`+2` charge in the
size measure is paid by ≥1 literal byte the encoder emits (the credential by its `{…}` body, each edge by
its `{"holder":…}` body). Mutual over auth / auth-list / auth-tail / forest / children. -/

/-! Each charge in `authSize`/`authListSize` is paid by ≥1 encoded byte. Mutual: the `oneOf` body's `+1`
by the `{"oneof":[` prefix, each candidate by its own encoding (recursively), each tail comma by `,`. -/
mutual
private theorem authSize_le_encode (a : AuthW) : authSize a ≤ (encodeAuthW a).toList.length := by
  -- every arm's encoding opens with `'{'` (length ≥ 1); `ht` specializes per case below.
  obtain ⟨t, ht⟩ := encodeAuthW_head a
  cases a with
  | oneOf cands i =>
      -- `authSize (.oneOf …) = 1 + authListSize cands`; the encoding holds the candidate list verbatim,
      -- prefixed by `{"oneof":[` (length 9) — slack covers the `+1`.
      have hl := authListSize_le_encode cands
      show 1 + authListSize cands ≤ (encodeAuthW (.oneOf cands i)).toList.length
      -- `encodeAuthW` is mutual ⇒ doesn't reduce by `rfl`; unfold its oneOf equation via `simp only`.
      simp only [encodeAuthW, String.toList_append, List.length_append,
        show ("{\"oneof\":[":String).toList.length = 10 from by decide]
      omega
  | _ =>
      -- every other arm has `authSize = 1`; its encoding (now `'{' :: t` via `ht`) has length ≥ 1.
      rw [ht]; simp only [authSize, List.length_cons]; omega
private theorem authListSize_le_encode (as : List AuthW) : authListSize as ≤ (encodeAuthListW as).toList.length := by
  cases as with
  | nil => simp [authListSize]
  | cons a as' =>
      -- `[` + first auth + tail + `]`; the first via `authSize_le_encode`, the tail via the tail bound.
      have ha := authSize_le_encode a
      have ht := authTailSize_le_encode as'
      have hshape := encAuthListW_cons_shape a as' []
      simp only [List.append_nil] at hshape
      show 1 + authSize a + authListSize as' ≤ (encodeAuthListW (a :: as')).toList.length
      rw [hshape]
      simp only [List.length_cons, List.length_append]
      omega
private theorem authTailSize_le_encode (as : List AuthW) : authListSize as ≤ (encodeAuthTailW as).toList.length := by
  cases as with
  | nil => simp [authListSize, encodeAuthTailW]
  | cons a as' =>
      -- `,` + auth + tail; the auth via `authSize_le_encode`, the tail by self-recursion.
      have ha := authSize_le_encode a
      have ht := authTailSize_le_encode as'
      have hshape := encAuthTailW_cons_shape a as' []
      simp only [List.append_nil] at hshape
      show 1 + authSize a + authListSize as' ≤ (encodeAuthTailW (a :: as')).toList.length
      rw [hshape]
      simp only [List.length_cons, List.length_append]
      omega
end

/-! Each charge in `forestSize`/`childrenSize` is paid by ≥1 encoded byte. Mutual: the node's `+1` by the
`{"auth":` prefix, the credential by `authSize_le_encode`, each edge's `+2` by its `{"holder":`-led body and
the `sub` recursion. The fuel-adequacy fact the envelope parser relies on. -/
mutual
private theorem forestSize_le_encode (f : WForest) : forestSize f ≤ (encodeForestW f).toList.length := by
  obtain ⟨na, cavs, a, kids⟩ := f
  have hna := authSize_le_encode na
  have hkids := childrenSize_le_encode kids
  -- the node opens with `{"auth":` (length 8) then the credential, …, then the children array.
  have hshape := encForestW_node_shape na cavs a kids []
  simp only [List.append_nil] at hshape
  show 1 + authSize na + childrenSize kids ≤ (encodeForestW ⟨na, cavs, a, kids⟩).toList.length
  rw [hshape]
  simp only [List.length_cons, List.length_append,
    show ("{\"auth\":":String).toList.length = 8 from by decide]
  omega
private theorem childrenSize_le_encode (cs : List WChild) : childrenSize cs ≤ (encodeChildrenW cs).toList.length := by
  cases cs with
  | nil => simp [childrenSize, encodeChildrenW]
  | cons c cs' =>
      obtain ⟨h, k, pc, sub⟩ := c
      have hsub := forestSize_le_encode sub
      have htail := childrenTailSize_le_encode cs'
      -- `[` + first edge + tail + `]`; the edge `+2` charge is covered by its `{"holder":` body (length 10),
      -- the sub-tree by `forestSize_le_encode`, the tail by the tail bound.
      have hshape := encodeChildrenW_cons_shape ⟨h, k, pc, sub⟩ cs' []
      simp only [List.append_nil] at hshape
      have hedge := encChildW_edge_shape h k pc sub []
      simp only [List.append_nil] at hedge
      show 2 + forestSize sub + childrenSize cs' ≤ (encodeChildrenW (⟨h, k, pc, sub⟩ :: cs')).toList.length
      rw [hshape, hedge]
      simp only [List.length_cons, List.length_append,
        show ("{\"holder\":":String).toList.length = 10 from by decide]
      omega
private theorem childrenTailSize_le_encode (cs : List WChild) : childrenSize cs ≤ (encodeChildrenTailW cs).toList.length := by
  cases cs with
  | nil => simp [childrenSize, encodeChildrenTailW]
  | cons c cs' =>
      obtain ⟨h, k, pc, sub⟩ := c
      have hsub := forestSize_le_encode sub
      have htail := childrenTailSize_le_encode cs'
      -- `,` + edge + tail; the edge `{"holder":` body (length 10) covers the `+2`, the sub via the forest bound.
      have hshape := encChildrenTailW_cons_shape ⟨h, k, pc, sub⟩ cs' []
      simp only [List.append_nil] at hshape
      have hedge := encChildW_edge_shape h k pc sub []
      simp only [List.append_nil] at hedge
      show 2 + forestSize sub + childrenSize cs' ≤ (encodeChildrenTailW (⟨h, k, pc, sub⟩ :: cs')).toList.length
      rw [hshape, hedge]
      simp only [List.length_cons, List.length_append,
        show ("{\"holder\":":String).toList.length = 10 from by decide]
      omega
end

/-! ### §16b — the Turn ENVELOPE roundtrip (a fixed-field `do`-block; the tree via §15). -/

/-- Well-formed Turn: the `prev` digest fits the `[u8;32]` width (`< 2^256`, else `parseHex32` wraps) and
the root tree is well-formed (§15a). The `agent`/`nonce`/`valid_until` are `Nat`, `fee` an `Int` — total. -/
def WfTurn (t : WTurn) : Prop := t.prevHash < 2 ^ 256 ∧ WfForest t.root

set_option maxHeartbeats 1000000 in
/-- **FILL J production (the ENVELOPE): the Turn-envelope roundtrip** (`parseWTurn ∘ encodeWTurn = id`).
The dregg1 outer fields (`agent`/`nonce`/`fee`/`valid_until`/`prev`) walk their `parseNat`/`parseInt`/
`parseHex32` leaves (§0), the `prev` digest losslessly under the `< 2^256` boundary, then the action-tree
root via §15's `parseForestW_roundtrip` (fuel `≥ forestSize root`). Strict on field ORDER + the closing
`}`. The wire-envelope decoder the wholesale swap hands the C entry point — out of the Lean TCB. -/
theorem parseWTurn_encode (t : WTurn) (rest : PState) (hwf : WfTurn t) (fuel : Nat)
    (hfuel : forestSize t.root ≤ fuel) :
    parseWTurn fuel ((encodeWTurn t).toList ++ rest) = some (t, rest) := by
  obtain ⟨agent, nonce, fee, validUntil, prevHash, root⟩ := t
  obtain ⟨hprev, hroot⟩ : prevHash < 2 ^ 256 ∧ WfForest root := hwf
  unfold parseWTurn
  -- rebracket the `++` chain into the right-associated field sequence the parser steps consume.
  rw [show (encodeWTurn ⟨agent, nonce, fee, validUntil, prevHash, root⟩).toList ++ rest
        = ("{\"agent\":":String).toList ++ ((toString agent).toList
            ++ ((",\"nonce\":":String).toList ++ ((toString nonce).toList
            ++ ((",\"fee\":":String).toList ++ ((toString fee).toList
            ++ ((",\"valid_until\":":String).toList ++ ((toString validUntil).toList
            ++ ((",\"prev\":\"":String).toList ++ ((toHex32 prevHash).toList
            ++ (("\",\"root\":":String).toList ++ ((encodeForestW root).toList
            ++ ('}' :: rest)))))))))))) from by
        show (encodeWTurn ⟨agent, nonce, fee, validUntil, prevHash, root⟩).toList ++ rest = _
        unfold encodeWTurn
        simp only [String.toList_append, show ("}":String).toList = ['}'] from by decide,
          show ("\",\"root\":":String).toList = ("\"":String).toList ++ (",\"root\":":String).toList from by decide,
          List.append_assoc, List.cons_append, List.nil_append]]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString agent _ (Or.inr ⟨',', _, by
        rw [show (",\"nonce\":":String).toList = ',' :: ("\"nonce\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString nonce _ (Or.inr ⟨',', _, by
        rw [show (",\"fee\":":String).toList = ',' :: ("\"fee\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseInt_toString fee _ (Or.inr ⟨',', _, by
        rw [show (",\"valid_until\":":String).toList = ',' :: ("\"valid_until\":":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseNat_toString validUntil _ (Or.inr ⟨',', _, by
        rw [show (",\"prev\":\"":String).toList = ',' :: ("\"prev\":\"":String).toList from by decide]; rfl, by decide⟩)]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseHex32_toHex32 prevHash _, Nat.mod_eq_of_lt hprev]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [lit_append]; simp only [Option.bind_eq_bind, Option.bind]
  rw [parseForestW_roundtrip root _ hroot fuel hfuel]
  simp only [Option.bind_eq_bind, Option.bind]
  rw [show lit "}" ('}' :: rest) = some rest from by
        rw [show ('}' :: rest) = ("}":String).toList ++ rest from rfl, lit_append]]

/-! ### §16c — the complete-turn WIRE roundtrip (state §14 ∘ envelope §16b; the WHOLE input consumed). -/

/-- The complete-turn wire ENCODER (the inline `{"state":STATEW,"turn":TURNW}` the C entry point reads —
matching `wideDemoInput`/`execFullTurnWide`'s input shape). -/
def encodeWWire (w : WWire) : String :=
  "{\"state\":" ++ encodeWState w.state ++ ",\"turn\":" ++ encodeWTurn w.turn ++ "}"

set_option maxHeartbeats 1000000 in
/-- **FILL J production (the OUTERMOST WIRE): the complete-turn wire roundtrip**
(`parseWWire ∘ encodeWWire = id`). Composes the §14 wide-state decoder with the §16b envelope, then
requires the WHOLE input consumed (`lit "}"` yields `some []` — trailing bytes fail-closed). The fuel
(`input.length + 1`) dominates both the state width and `forestSize root` (each `≤` the encoded length, the
encoded objects being substrings of the input, §16a). This removes the OUTERMOST codec — the envelope the
wholesale swap hands `execFullTurnWide` — from the Lean-side TCB; with §14/§15 the wire codec is FULLY out. -/
theorem parseWWire_encode (w : WWire) (hcells : WfCells w.state.cells) (hturn : WfTurn w.turn) :
    parseWWire (encodeWWire w) = some w := by
  obtain ⟨state, turn⟩ := w
  -- `parseWWire` runs on `(encodeWWire ⟨state,turn⟩).toList` at fuel `len + 1`; expose the field layout.
  have hwire : (encodeWWire ⟨state, turn⟩).toList
      = ("{\"state\":":String).toList ++ ((encodeWState state).toList
          ++ ((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList))) := by
    show (encodeWWire ⟨state, turn⟩).toList = _
    unfold encodeWWire
    simp only [String.toList_append, List.append_assoc]
  unfold parseWWire
  -- zeta-reduce the `let cs`/`let fuel` bindings so the input expression is exposed for `rw [hwire]`.
  simp only []
  -- the outer fuel: the whole-input length + 1, which dominates every inner width.
  set fuel := (encodeWWire ⟨state, turn⟩).toList.length + 1 with hfueldef
  -- open `{"state":`
  rw [hwire]
  rw [show lit "{\"state\":" (("{\"state\":":String).toList ++ ((encodeWState state).toList
          ++ ((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList))))
        = some ((encodeWState state).toList ++ ((",\"turn\":":String).toList
            ++ ((encodeWTurn turn).toList ++ "}".toList))) from
        lit_append "{\"state\":" _]
  -- reduce the `match some _ with | some r0 => …` so `parseWState_encode` can rewrite the exposed input.
  simp only []
  -- the wide STATE via §14 (outer fuel ≥ encoded width; the rest is `,"turn":TURN}`):
  rw [parseWState_encode state (((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList)))
        hcells fuel (by
        rw [hfueldef, hwire]
        simp only [List.length_append]
        omega)]
  -- iota-reduce the `match some (state, _) with | some (state, r1) => …` pair-pattern match.
  dsimp only
  -- `,"turn":` then the envelope via §16b (outer fuel ≥ forestSize root via §16a):
  rw [show lit ",\"turn\":" ((",\"turn\":":String).toList ++ ((encodeWTurn turn).toList ++ "}".toList))
        = some ((encodeWTurn turn).toList ++ "}".toList) from lit_append ",\"turn\":" _]
  simp only []
  rw [parseWTurn_encode turn "}".toList hturn fuel (by
        -- `forestSize turn.root ≤ (encodeForestW turn.root).length ≤ full input length < fuel`.
        have hbridge := forestSize_le_encode turn.root
        rw [hfueldef, hwire]
        -- the encoded forest is a substring of the envelope, hence of the whole input.
        have hsub : (encodeForestW turn.root).toList.length ≤ (encodeWTurn turn).toList.length := by
          obtain ⟨agent, nonce, fee, validUntil, prevHash, root⟩ := turn
          show (encodeForestW root).toList.length ≤ (encodeWTurn ⟨agent, nonce, fee, validUntil, prevHash, root⟩).toList.length
          rw [show (encodeWTurn ⟨agent, nonce, fee, validUntil, prevHash, root⟩)
                = "{\"agent\":" ++ toString agent ++ ",\"nonce\":" ++ toString nonce ++ ",\"fee\":" ++ toString fee
                    ++ ",\"valid_until\":" ++ toString validUntil ++ ",\"prev\":\"" ++ toHex32 prevHash ++ "\""
                    ++ ",\"root\":" ++ encodeForestW root ++ "}" from rfl]
          simp only [String.toList_append, List.length_append]
          omega
        simp only [List.length_append]
        omega)]
  dsimp only
  -- the closing `}` must consume the WHOLE remaining input (`some []` ⇒ accept):
  rw [show lit "}" "}".toList = some [] from by
        rw [show ("}":String).toList = ("}":String).toList ++ ([] : PState) from by simp, lit_append]]

/-! ### §16d — NON-VACUITY: a complete wire WITH a delegation edge round-trips (the recursion + the
envelope + every state field are real). -/

/-- A real multi-node turn: the root credential bears a delegation EDGE (`keep`/`cap`/`sub`), so the wire
exercises the §15 children recursion, not just a leaf root; wrapped in a populated wide state. -/
private def wireWitness : WWire :=
  { state := { cells := [(0, .record [("balance", .int 100)])], caps := [(9, [.node 0])], bal := [(0, 0, 100)],
               escrows := [], nullifiers := [], commitments := [], queues := [], swiss := [] }
    turn  := { agent := 0, nonce := 1, fee := 2, validUntil := 9, prevHash := 7
               root := ⟨ .signature 3 3, [{ tier := 0, cell := 0, asset := 0, min := 1 }],
                         .balanceA { actor := 0, src := 0, dst := 1, amt := 10 } 0,
                         [⟨1, [.read], .node 0, ⟨.unchecked, [], .revoke 0 0, []⟩⟩] ⟩ } }

/-- The witness state's cells are well-formed (the one digest-free `int` balance). -/
private theorem wireWitness_cells_wf : WfCells wireWitness.state.cells := by
  show WfCells [(0, .record [("balance", .int 100)])]
  exact ⟨⟨by decide, trivial, trivial⟩, trivial⟩

/-- The witness turn is well-formed: `prev = 7 < 2^256`, root credential `signature 3 < 2^256`, the one
caveat tier `0 ≤ 3`, every action `simple`/total, and the one delegation edge's sub-tree well-formed. -/
private theorem wireWitness_turn_wf : WfTurn wireWitness.turn := by
  refine ⟨by decide, ?_⟩
  show WfForest ⟨ .signature 3 3, [{ tier := 0, cell := 0, asset := 0, min := 1 }],
                  .balanceA { actor := 0, src := 0, dst := 1, amt := 10 } 0,
                  [⟨1, [.read], .node 0, ⟨.unchecked, [], .revoke 0 0, []⟩⟩] ⟩
  -- the sub-tree's credential is `.unchecked` (`WfAuth = True`), its caveats/action/children all trivial.
  exact ⟨show (3:Nat) < 2^256 by norm_num, ⟨by unfold WfCaveat; decide, trivial⟩, trivial,
    ⟨⟨trivial, trivial, trivial, trivial⟩, trivial⟩⟩

-- The WHOLE wire — populated state + a delegation-bearing tree — round-trips through `parseWWire`:
example : parseWWire (encodeWWire wireWitness) = some wireWitness :=
  parseWWire_encode wireWitness wireWitness_cells_wf wireWitness_turn_wf

/-! ## §4 — axiom hygiene (the FILL-J no-`sorryAx` pins).

Every keystone is `#assert_axioms`-pinned to the standard kernel triple `{propext, Classical.choice,
Quot.sound}` — a `sorryAx` ANYWHERE in their dependency closure FAILS the build (the strongest
zero-sorry guarantee on the codec roundtrip). -/

#assert_axioms ofHex32_toHex32
#assert_axioms parseDig_encDig
#assert_axioms parseInt_toString
#assert_axioms parseNat_toString
#assert_axioms parseStr_clean
#assert_axioms parseValueW_scalar
#assert_axioms parseBalEntry_encode
#assert_axioms fillJ_digest
#assert_axioms fillJ_amount
#assert_axioms fillJ_value_scalar
#assert_axioms fillJ_bal_entry
#assert_axioms litGo_none_mono
#assert_axioms parseValueW_roundtrip
#assert_axioms parseFieldsW_roundtrip
#assert_axioms parseAuthW_flat
#assert_axioms parseAuthW_roundtrip
#assert_axioms parseAuthListW_roundtrip
#assert_axioms parseActionW_roundtrip
#assert_axioms parseActionW_setfield
#assert_axioms parseAuths_encode
#assert_axioms parseNats_encode
#assert_axioms parseBal_encode
#assert_axioms parseEscrow_encode
#assert_axioms parseEscrows_encode
#assert_axioms parseQueue_encode
#assert_axioms parseQueues_encode
#assert_axioms parseOptNat_encode
#assert_axioms parseSwiss_encode
#assert_axioms parseSwissTable_encode
#assert_axioms parseCellW_encode
#assert_axioms parseCellsW_encode
#assert_axioms parseCap_encode
#assert_axioms parseCapList_encode
#assert_axioms parseCapEntry_encode
#assert_axioms parseCapsEntries_encode
#assert_axioms parseWState_encode
#assert_axioms parseCaveatW_encode
#assert_axioms parseCaveatsW_encode
#assert_axioms parseActionW_any
#assert_axioms parseForestW_roundtrip
#assert_axioms parseChildrenW_roundtrip
#assert_axioms forestSize_le_encode
#assert_axioms parseWTurn_encode
#assert_axioms parseWWire_encode

end Dregg2.Exec.CodecRoundtrip
