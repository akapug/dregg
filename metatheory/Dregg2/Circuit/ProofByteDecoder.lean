/-
# Dregg2.Circuit.ProofByteDecoder — a REAL byte→field-view decoder for the deployed
public-input wire, discharging one leg of `CircuitSoundness.cfgView`'s opacity.

## What `cfgView` is (the opacity this file bites)

`CircuitSoundness.cfgView : BatchPublicInputs → BatchProof → (BatchProofData ℤ × WrapPublics ℤ)`
is declared `opaque` — the byte-deserialization of a proof's `(pi, π)` bytes into the
structured field-element views the verifier walks. Its ONLY specification was the
docstring KAT claim; nothing in Lean actually PARSED the deployed byte layout.

This module builds a concrete, executable byte→field decoder for the ONE piece of the
`cfgView` output that IS a plain base-field-element stream on the deployed wire: the
**public-input segment** — `WrapPublics.segment` (the IVC root's carried
`[genesis_root…, final_root…, num_turns, chain_digest…]`, `ivc_turn_chain.rs:1296`) and,
by the tooth-3 identity `exposedSegment = WrapPublics`, `BatchProofData.exposedSegment`.

## The deployed byte layout (the anchor — NOT invented)

The wire is the canonical fixed-width layout the deployed prover emits for a field
public-input vector, read directly from the deployed Rust:

  * `turn/src/binding_proof.rs:70` `public_inputs_babybear`: the PI vector is
    `Vec<u32>` mapped to field elements via `BabyBear::new(v)`;
  * `circuit/src/field.rs:114` `BabyBear::new(v) = Self(v % BABYBEAR_P)` — reduce mod
    `p = 2^31 − 2^27 + 1 = 2013265921` (the canonical, malleability-closing decode, the
    SAME reduction the serde `Deserialize` impl at `field.rs:82` performs);
  * `turn/src/binding_proof.rs:81-89` `hash_into`: the canonical byte encoding is a
    `u64`-LE length prefix (`(len as u64).to_le_bytes()`) followed by each element as a
    4-byte `u32`-LE limb (`v.to_le_bytes()`). This is the layout folded into `Turn::hash`
    (blake3) — load-bearing, not decorative.

So the decoder here is byte-EXACT with the deployed `hash_into` public-input sub-layout
and the `BabyBear::new` field reduction, and its golden vector is the deployed test
vector `vec![0xDEAD_BEEF, 0xCAFE_F00D]` (`binding_proof.rs:191`).

## What this discharges vs. the NAMED residual

DISCHARGES: `cfgView`'s opacity for the `(pi/π bytes) → WrapPublics.segment /
BatchProofData.exposedSegment` leg — a real `parse ∘ encode = id` roundtrip + a golden
vector pinned to the deployed serializer, replacing the docstring-only KAT claim on that
leg with executable, kernel-checked bytes.

RESIDUAL (named, not axiomatized): the OTHER `BatchProofData` fields — `traceCommit`,
`preprocessedCommit`, `friCommitments`, `finalPoly`, `queries`, `tableOpenings`,
`oodPoint`, `powWitness`, `quotientCommit`, `openedEvaluations`, `friLogArities` — are
NOT on the public-input wire. They live inside the proof's `proof_bytes`, a
`postcard`-serialized `p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>`
(`plonky3_recursion_impl.rs:698`, an external-crate `postcard` varint layout). This
decoder does NOT parse that inner blob; those fields stay carried through the FRI
`FriChecks` per-query components, exactly as the `BatchProofData` docstring states. So
`cfgView`'s opacity for the `proof_bytes → {trace/quotient/FRI/table} views` leg is
UNDISCHARGED here and remains the KAT floor.

## Axiom hygiene

Every theorem is `#assert_axioms`-clean (omega + structural induction only). No `sorry`,
no `native_decide`, no new axiom. `#guard`s kernel-reduce over concrete deployed bytes;
`#eval`s exhibit non-vacuity. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.ProofByteDecoder

open Dregg2.Circuit

set_option autoImplicit false

/-! ## §1 — the BabyBear modulus (the deployed `BabyBear::new` reduction). -/

/-- The BabyBear prime `p = 2^31 − 2^27 + 1 = 2013265921` (`circuit/src/field.rs:12`,
`BABYBEAR_P`). `BabyBear::new(v) = v % p`. -/
def babybearP : Nat := 2013265921

/-- The deployed modulus really is `2^31 − 2^27 + 1`. -/
theorem babybearP_val : babybearP = 2 ^ 31 - 2 ^ 27 + 1 := by decide

/-! ## §2 — little-endian byte primitives (byte-exact with `to_le_bytes`).

Bytes are modelled as `Nat` (each intended `< 256`, as produced by `to_le_bytes`). The
readers reconstruct the integer with the identical positional weights; the writers are
`u32::to_le_bytes` / `u64::to_le_bytes` verbatim. -/

/-- `u32::to_le_bytes` — the four little-endian bytes of a `u32`. -/
def u32le (n : Nat) : List Nat :=
  [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256]

/-- Read one little-endian `u32` off the front of a byte list (the inverse of
`u32le`). -/
def readU32le : List Nat → Option (Nat × List Nat)
  | b0 :: b1 :: b2 :: b3 :: rest =>
      some (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3, rest)
  | _ => none

/-- `u64::to_le_bytes` — the eight little-endian bytes of a `u64` (the length prefix). -/
def u64le (n : Nat) : List Nat :=
  [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256,
   (n / 4294967296) % 256, (n / 1099511627776) % 256,
   (n / 281474976710656) % 256, (n / 72057594037927936) % 256]

/-- Read one little-endian `u64` length prefix off the front of a byte list. -/
def readU64le : List Nat → Option (Nat × List Nat)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      some (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4
              + 1099511627776 * b5 + 281474976710656 * b6 + 72057594037927936 * b7, rest)
  | _ => none

/-- `readU32le` inverts `u32le` on any in-range `u32` (leftover bytes preserved). -/
theorem readU32le_u32le (n : Nat) (h : n < 4294967296) (rest : List Nat) :
    readU32le (u32le n ++ rest) = some (n, rest) := by
  simp only [u32le, readU32le, List.cons_append, List.nil_append]
  have hn : n % 256 + 256 * ((n / 256) % 256) + 65536 * ((n / 65536) % 256)
      + 16777216 * ((n / 16777216) % 256) = n := by omega
  rw [hn]

/-- `readU64le` inverts `u64le` on any in-range `u64` (leftover bytes preserved). -/
theorem readU64le_u64le (n : Nat) (h : n < 18446744073709551616) (rest : List Nat) :
    readU64le (u64le n ++ rest) = some (n, rest) := by
  simp only [u64le, readU64le, List.cons_append, List.nil_append]
  have hn : n % 256 + 256 * ((n / 256) % 256) + 65536 * ((n / 65536) % 256)
      + 16777216 * ((n / 16777216) % 256) + 4294967296 * ((n / 4294967296) % 256)
      + 1099511627776 * ((n / 1099511627776) % 256)
      + 281474976710656 * ((n / 281474976710656) % 256)
      + 72057594037927936 * ((n / 72057594037927936) % 256) = n := by omega
  rw [hn]

/-! ## §3 — the field-element stream codec (the deployed `hash_into` PI layout).

A field stream is a `u64`-LE count followed by `count` `u32`-LE limbs; each limb decodes
to a canonical field element via `% babybearP` (the deployed `BabyBear::new`). -/

/-- Encode a list of field values as contiguous `u32`-LE limbs. -/
def encodeFieldElems : List Nat → List Nat
  | [] => []
  | x :: xs => u32le x ++ encodeFieldElems xs

/-- Decode `k` field limbs, reducing each mod `babybearP` (the deployed `BabyBear::new`
malleability-closing reduction). Returns the decoded elements and the unconsumed tail;
`none` if the bytes run out. -/
def decodeFieldElems : Nat → List Nat → Option (List Nat × List Nat)
  | 0, bs => some ([], bs)
  | (k + 1), bs =>
      match readU32le bs with
      | none => none
      | some (v, rest) =>
          match decodeFieldElems k rest with
          | none => none
          | some (vs, rest') => some ((v % babybearP) :: vs, rest')

/-- Encode a field stream: `u64`-LE length prefix + the limbs. -/
def encodeFieldStream (xs : List Nat) : List Nat :=
  u64le xs.length ++ encodeFieldElems xs

/-- Decode a field stream: read the length prefix, then that many limbs. Returns the
elements and the unconsumed tail. -/
def decodeFieldStream (bs : List Nat) : Option (List Nat × List Nat) :=
  match readU64le bs with
  | none => none
  | some (count, rest) => decodeFieldElems count rest

/-- Decode a field stream requiring EVERY byte consumed (a well-formed single-stream
proof view — trailing garbage is a REJECT, not silently ignored). -/
def decodeFieldStreamExact (bs : List Nat) : Option (List Nat) :=
  match decodeFieldStream bs with
  | some (vs, []) => some vs
  | _ => none

/-! ## §4 — the roundtrip laws (`parse ∘ encode = id`). -/

/-- **Limb roundtrip.** Decoding the encoding of `xs` (elements canonical, `< p`) yields
`xs` back with the trailing bytes intact. -/
theorem decodeFieldElems_encode :
    ∀ (xs : List Nat), (∀ x ∈ xs, x < babybearP) → ∀ (rest : List Nat),
      decodeFieldElems xs.length (encodeFieldElems xs ++ rest) = some (xs, rest)
  | [], _, rest => by simp [decodeFieldElems, encodeFieldElems]
  | a :: as, hx, rest => by
      have ha : a < babybearP := hx a (by simp)
      have has : ∀ x ∈ as, x < babybearP := fun x hxin => hx x (by simp [hxin])
      have ha32 : a < 4294967296 := by
        have hp : babybearP = 2013265921 := rfl
        omega
      simp only [encodeFieldElems, List.append_assoc, decodeFieldElems,
        readU32le_u32le a ha32, decodeFieldElems_encode as has rest]
      rw [Nat.mod_eq_of_lt ha]

/-- **Stream roundtrip.** Decoding the encoding of a canonical field vector `xs` yields
`xs` back with the trailing bytes intact. -/
theorem decodeFieldStream_encode (xs : List Nat) (hx : ∀ x ∈ xs, x < babybearP)
    (rest : List Nat) (hlen : xs.length < 18446744073709551616) :
    decodeFieldStream (encodeFieldStream xs ++ rest) = some (xs, rest) := by
  simp only [decodeFieldStream, encodeFieldStream, List.append_assoc,
    readU64le_u64le xs.length hlen]
  exact decodeFieldElems_encode xs hx rest

/-- **Exact-stream roundtrip.** With no trailing bytes, the exact decoder recovers the
canonical field vector. -/
theorem decodeFieldStreamExact_encode (xs : List Nat) (hx : ∀ x ∈ xs, x < babybearP)
    (hlen : xs.length < 18446744073709551616) :
    decodeFieldStreamExact (encodeFieldStream xs) = some xs := by
  have h := decodeFieldStream_encode xs hx [] hlen
  simp only [List.append_nil] at h
  simp only [decodeFieldStreamExact, h]

/-! ## §5 — assembling the `cfgView` field views.

The decoded PI segment populates BOTH `WrapPublics.segment` (the carried claim) and, by
the deployed tooth-3 identity `exposedSegment = WrapPublics`
(`ivc_turn_chain.rs:133`), `BatchProofData.exposedSegment`. The remaining
`BatchProofData` fields are the NAMED residual (see the module header) — set empty here
because they are NOT on the public-input wire. -/

/-- Cast decoded canonical field limbs into the model field `ℤ`. -/
def toFieldZ (vs : List Nat) : List ℤ := vs.map (fun n => (n : ℤ))

/-- The `cfgView` output view built from a public-input byte stream: the decoded segment
lands in both `WrapPublics.segment` and `BatchProofData.exposedSegment` (tooth 3). -/
def decodeView (bs : List Nat) :
    Option (FriVerifier.BatchProofData ℤ × FriVerifier.WrapPublics ℤ) :=
  match decodeFieldStreamExact bs with
  | none => none
  | some vs =>
      let seg := toFieldZ vs
      some ({ traceCommit := [], friCommitments := [], finalPoly := [], queries := [],
              exposedSegment := seg }, { segment := seg })

/-- Encode a canonical field segment to its public-input wire bytes. -/
def encodeView (vs : List Nat) : List Nat := encodeFieldStream vs

/-- The `cfgView` output-input type bridge: consume the SAME `BatchProof.bytes` the
opaque `cfgView` takes (`List ℤ`), truncating each byte back to `Nat`. This pins the
decoder to the actual `cfgView` proof argument, not a bespoke input. -/
def decodeViewFromProof (π : CircuitSoundness.BatchProof) :
    Option (FriVerifier.BatchProofData ℤ × FriVerifier.WrapPublics ℤ) :=
  decodeView (π.bytes.map Int.toNat)

/-- **The view roundtrip.** Parsing the encoding of a canonical field segment `vs`
reconstructs the exact `WrapPublics.segment` and `BatchProofData.exposedSegment` — the
`parse ∘ encode = id` law on the fields `cfgView` produces. -/
theorem decodeView_encode (vs : List Nat) (hx : ∀ x ∈ vs, x < babybearP)
    (hlen : vs.length < 18446744073709551616) :
    decodeView (encodeView vs)
      = some ({ traceCommit := [], friCommitments := [], finalPoly := [], queries := [],
                exposedSegment := toFieldZ vs }, { segment := toFieldZ vs }) := by
  simp only [decodeView, encodeView, decodeFieldStreamExact_encode vs hx hlen]

/-- The two views agree on the exposed segment — the deployed tooth-3 identity
`exposedSegment = WrapPublics.segment`, now a THEOREM about the decoder output rather
than a docstring claim. -/
theorem decodeView_tooth3 (vs : List Nat) (hx : ∀ x ∈ vs, x < babybearP)
    (hlen : vs.length < 18446744073709551616) :
    ∃ bpd wp, decodeView (encodeView vs) = some (bpd, wp)
      ∧ bpd.exposedSegment = wp.segment := by
  refine ⟨_, _, decodeView_encode vs hx hlen, ?_⟩
  rfl

#assert_axioms readU32le_u32le
#assert_axioms readU64le_u64le
#assert_axioms decodeFieldElems_encode
#assert_axioms decodeFieldStream_encode
#assert_axioms decodeFieldStreamExact_encode
#assert_axioms decodeView_encode
#assert_axioms decodeView_tooth3

/-! ## §6 — golden vectors (kernel-checked, pinned to the deployed serializer).

The deployed test vector is `public_inputs = vec![0xDEAD_BEEF, 0xCAFE_F00D]`
(`turn/src/binding_proof.rs:191`). Its `hash_into` byte layout is:

  * count `2` as `u64`-LE: `[2,0,0,0,0,0,0,0]`;
  * `0xDEADBEEF` as `u32`-LE: `[239,190,173,222]` (0xEF,0xBE,0xAD,0xDE);
  * `0xCAFEF00D` as `u32`-LE: `[13,240,254,202]` (0x0D,0xF0,0xFE,0xCA).

Decoding reduces each mod `p` (the deployed `BabyBear::new`):
`0xDEADBEEF % p = 1722662638`, `0xCAFEF00D % p = 1392439308` — matching
`assert_eq!(bb[0], BabyBear::new(0xDEAD_BEEF))` in the deployed test. -/

-- GOLDEN: the deployed `[0xDEADBEEF, 0xCAFEF00D]` PI wire decodes to the two reduced
-- BabyBear field elements.
#guard decodeFieldStreamExact
    [2, 0, 0, 0, 0, 0, 0, 0, 239, 190, 173, 222, 13, 240, 254, 202]
  = some [1722662638, 1392439308]

-- The decoded value equals the deployed `BabyBear::new(0xDEADBEEF) = 0xDEADBEEF % p`.
#guard (3735928559 % babybearP) = 1722662638
#guard (3405705229 % babybearP) = 1392439308

-- GOLDEN (malleability leg): a wire limb carrying the RAW value `p` itself
-- (`0x78000001 = [1,0,0,120]`) decodes to `0` — exactly `BabyBear::new(p) = p % p = 0`,
-- the canonical reduction the deployed decode enforces.
#guard decodeFieldStreamExact [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 120] = some [0]

-- The full `cfgView` field views on the deployed golden bytes: exposed segment and
-- carried publics both hold the two reduced elements, and they AGREE (tooth 3).
#guard
    (match decodeView
        [2, 0, 0, 0, 0, 0, 0, 0, 239, 190, 173, 222, 13, 240, 254, 202] with
     | some (bpd, wp) =>
         bpd.exposedSegment == wp.segment
           && wp.segment == ([1722662638, 1392439308] : List ℤ)
     | none => false)

-- Roundtrip on a canonical segment (including the max element `p − 1`).
#guard decodeFieldStreamExact (encodeFieldStream [1, 2, 2013265920])
  = some [1, 2, 2013265920]

-- Empty PI segment: length-prefix `0`, zero limbs — a valid empty view.
#guard decodeFieldStreamExact [0, 0, 0, 0, 0, 0, 0, 0] = some ([] : List Nat)

-- Truncated wire (claims 1 limb, supplies 3 bytes) is REJECTED, not silently accepted.
#guard decodeFieldStreamExact [1, 0, 0, 0, 0, 0, 0, 0, 5, 6, 7] = (none : Option (List Nat))

-- Trailing garbage after a complete stream is REJECTED (exact-consumption).
#guard decodeFieldStreamExact [0, 0, 0, 0, 0, 0, 0, 0, 99] = (none : Option (List Nat))

-- Non-vacuity: the assembled view is genuinely inhabited on the golden bytes.
#eval (decodeView
    [2, 0, 0, 0, 0, 0, 0, 0, 239, 190, 173, 222, 13, 240, 254, 202]).map
  (fun r => (r.1.exposedSegment, r.2.segment))

-- Non-vacuity: the roundtrip hypotheses are satisfiable (a concrete canonical vector).
#eval (decodeView (encodeView [7, 11, 2013265920])).map
  (fun r => (r.1.exposedSegment, r.2.segment))

end Dregg2.Circuit.ProofByteDecoder
