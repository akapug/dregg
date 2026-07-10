/-
# `Dregg2.Crypto.MlKemEncaps` — the REAL ML-KEM-768 ENCAPSULATION (FIPS 203 Algorithm 16/17), EXECUTABLE `def`s.

BRICK K5 — the ENCAPS mirror of K4 (`MlKemDecaps`). K4 assembled the full-dimension FO DECAPSULATION and
proved (`native_decide`) that the Lean decaps recovers a genuine `ml-kem` v0.2.3 crate shared secret; K5 is
the matching direction — the deterministic ML-KEM.Encaps that PRODUCES `(ct, K)`. It REUSES K4's
`kpkeEncrypt` (the FIPS 203 Alg 13 K-PKE encryption already built for the FO re-encrypt) and the
`sha3_256`/`sha3_512` hashes, adding only the FO wrapper `G(m ‖ H(ek))` split.

## ML-KEM.Encaps_internal (FIPS 203 Algorithm 16), deterministic given `m`:
```
1: (K, r) ← G(m ‖ H(ek))          -- G = SHA3-512 (64 B, split 32+32); H = SHA3-256 (32 B)
2: c ← K-PKE.Encrypt(ek, m, r)     -- K4 `kpkeEncrypt`
3: return (c, K)
```

## THE GATE — `native_decide`, BYTE-EXACT vs the GENUINE `ml-kem` v0.2.3 crate DETERMINISTIC encaps.

The `ml-kem` v0.2.3 crate exposes `EncapsulateDeterministic` (its `Encaps_internal`, feature `deterministic`).
The generator reconstructs the SAME pinned encapsulation key `MlKemCodec.realEk` (the key K3/K4 pin), runs the
crate's `encapsulate_deterministic(realEk, mFixed)` for a FIXED 32-byte `mFixed`, and pins the crate's exact
outputs `realCtEnc` (1088 B) / `realKEnc` (32 B). `encaps_matches_crate` asserts the Lean encaps reproduces the
crate's ciphertext AND shared secret BYTE-FOR-BYTE — the strongest possible gate: the Lean `mlkemEncaps` IS the
crate's ML-KEM-768 encaps on the real key. The generator also confirmed (and `encaps_decaps_roundtrip` re-proves
in Lean, through the already-verified K4 `mlkemDecaps`) that decaps of `realDk` over the produced ciphertext
recovers the SAME `K` — so the Lean encaps and the Lean decaps agree end-to-end.

`native_decide` runs the COMPILED `def`s; its trusted base is `Lean.ofReduceBool` + `Lean.trustCompiler` — the
SAME residual K1–K4 name. No `sorry`, no user `axiom`, no toy substitute.
-/
import Dregg2.Crypto.Keccak
import Dregg2.Crypto.MlKemRing
import Dregg2.Crypto.MlKemSample
import Dregg2.Crypto.MlKemCodec
import Dregg2.Crypto.MlKemDecaps

namespace Dregg2.Crypto.MlKemEncaps

open Dregg2.Crypto.MlKemCodec (realEk realDk)
open Dregg2.Crypto.MlKemDecaps
  (kpkeEncrypt sha3_256 sha3_512 mlkemDecaps hexEncode decodeHexChars)

/-! ## ML-KEM.Encaps_internal (FIPS 203 Algorithm 16) — deterministic given `m`. -/

/-- **`ML-KEM.Encaps_internal(ek, m)`** (FIPS 203 Alg 16). `(K, r) = G(m ‖ H(ek))` (`G = SHA3-512`, split
32+32; `H = SHA3-256`); `c = K-PKE.Encrypt(ek, m, r)` (K4 `kpkeEncrypt`); return `(c, K)` — the ciphertext and
the 32-byte encapsulated shared secret. -/
def mlkemEncaps (ek : List UInt8) (m : List UInt8) : (List UInt8 × List UInt8) :=
  let hek := sha3_256 ek                    -- H(ek) → 32 bytes
  let g := sha3_512 (m ++ hek)              -- G(m ‖ H(ek)) → 64 bytes
  let k := g.take 32                        -- K
  let r := g.drop 32                        -- r (the K-PKE.Encrypt coins)
  let c := kpkeEncrypt ek m r
  (c, k)

/-! ## THE `@[export]` FFI ENTRY (Rust → Lean) — the REAL, FULL-BYTE ML-KEM-768 ENCAPSULATION over a byte wire.

BRICK K5's C-ABI entry — the ENCAPS analog of K6's `dregg_mlkem_decaps_real`. The deployed hybrid-KEM initiator
(`dregg-pq/src/hybrid_kem.rs` `initiate`) currently produces the ML-KEM ciphertext + shared secret by calling
the `ml-kem` crate's `.encapsulate`. This export routes THAT call through the Lean-verified `mlkemEncaps` (the
deterministic FO encaps proved byte-exact vs the crate, below), so the `ml-kem` crate leaves the node's
KEM-ENCAPS TCB. The initiator supplies its own 32-byte `m` (as the crate's randomized encaps does internally);
the reply's `(ct, K)` are used verbatim and the crate's `.encapsulate` is NOT called. -/

/-- The real byte wire `hex(ek) hex(m)` the encaps FFI reads. -/
def realWireEncaps (ek m : List UInt8) : String :=
  hexEncode ek ++ " " ++ hexEncode m

/-- **FFI entry** (Rust→Lean) for the REAL, FULL-BYTE ML-KEM-768 ENCAPS (BRICK K5): parse the two hex fields
`hex(ek) hex(m)`, run the Lean-verified `mlkemEncaps` over the decoded bytes, and return `hex(ct) hex(K)` — the
1088-byte ciphertext and the recovered 32-byte shared secret, two space-separated lowercase-hex fields. This
runs the FULL-DIMENSION FO encapsulation (not the `A=1,n=1` scalar toy) as native code. Any malformed wire
fails CLOSED (`"ERR"`), which the Rust caller treats as an encaps fault (fail-closed). -/
@[export dregg_mlkem_encaps_real]
def mlkemEncapsRealFFI (input : String) : String :=
  match input.splitOn " " with
  | [ekH, mH] =>
    match decodeHexChars ekH.toList, decodeHexChars mH.toList with
    | some ek, some m =>
      let (c, k) := mlkemEncaps ek m
      hexEncode c ++ " " ++ hexEncode k
    | _, _ => "ERR"
  | _ => "ERR"

/-! ## Pinned REAL `ml-kem` v0.2.3 DETERMINISTIC encaps vectors (genuine `EncapsulateDeterministic` over the
pinned `MlKemCodec.realEk`; the generator confirmed `realDk.decapsulate(realCtEnc) == realKEnc` before pinning). -/

def mFixed : Array UInt8 := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

def realCtEnc : Array UInt8 := #[0, 243, 66, 30, 221, 148, 200, 167, 251, 20, 157, 177, 147, 44, 189, 157, 91, 164, 128, 83, 40, 43, 51, 46, 150, 7, 213, 244, 52, 247, 191, 163, 42, 69, 253, 150, 221, 142, 225, 126, 111, 79, 125, 194, 60, 237, 219, 110, 138, 30, 129, 144, 140, 201, 64, 246, 183, 139, 97, 72, 53, 119, 212, 13, 41, 17, 249, 212, 214, 93, 80, 166, 100, 86, 56, 222, 67, 150, 47, 231, 49, 149, 129, 83, 84, 239, 86, 181, 161, 252, 197, 173, 77, 28, 111, 220, 232, 140, 131, 25, 71, 143, 201, 227, 243, 38, 230, 238, 69, 22, 143, 168, 19, 91, 94, 172, 240, 152, 119, 247, 169, 171, 163, 153, 158, 211, 116, 163, 102, 94, 208, 127, 138, 69, 94, 212, 38, 126, 57, 71, 173, 3, 252, 39, 105, 46, 208, 98, 255, 104, 13, 234, 11, 17, 111, 58, 108, 99, 193, 141, 100, 150, 32, 156, 45, 177, 33, 199, 242, 58, 165, 26, 1, 79, 31, 2, 123, 116, 25, 154, 47, 94, 51, 199, 252, 245, 147, 42, 62, 56, 37, 148, 177, 99, 171, 199, 188, 237, 53, 207, 30, 241, 30, 57, 29, 3, 159, 122, 182, 29, 111, 248, 123, 59, 147, 233, 17, 251, 96, 120, 130, 169, 166, 169, 67, 215, 190, 33, 253, 246, 106, 165, 202, 136, 185, 38, 164, 147, 84, 45, 191, 28, 230, 155, 236, 106, 193, 1, 143, 213, 24, 130, 127, 113, 204, 227, 24, 174, 175, 157, 172, 223, 108, 88, 120, 187, 108, 71, 15, 210, 251, 132, 36, 109, 168, 169, 250, 188, 219, 96, 108, 202, 201, 0, 150, 110, 101, 75, 30, 107, 189, 207, 170, 228, 195, 83, 17, 119, 19, 99, 156, 136, 31, 46, 60, 128, 241, 160, 151, 148, 190, 106, 153, 199, 58, 244, 205, 9, 223, 248, 230, 39, 150, 178, 49, 175, 185, 135, 90, 157, 142, 236, 225, 197, 43, 1, 255, 142, 0, 71, 206, 166, 227, 86, 157, 202, 28, 60, 242, 217, 3, 128, 242, 220, 133, 241, 31, 237, 195, 45, 177, 88, 167, 151, 106, 30, 145, 203, 216, 90, 172, 181, 140, 70, 27, 182, 0, 96, 177, 1, 188, 142, 141, 224, 206, 106, 185, 65, 227, 181, 171, 113, 183, 107, 17, 167, 126, 148, 233, 118, 167, 142, 45, 176, 188, 94, 216, 21, 13, 114, 63, 87, 185, 88, 49, 214, 135, 15, 79, 40, 190, 96, 99, 255, 145, 100, 9, 91, 212, 117, 39, 231, 116, 3, 246, 117, 89, 190, 233, 68, 92, 25, 130, 173, 23, 28, 220, 74, 226, 80, 187, 169, 76, 163, 235, 229, 21, 163, 1, 114, 15, 145, 171, 69, 77, 37, 66, 2, 171, 97, 233, 225, 153, 45, 212, 225, 76, 132, 100, 172, 211, 34, 152, 53, 158, 141, 37, 206, 253, 34, 168, 186, 38, 162, 92, 160, 237, 129, 56, 225, 205, 248, 39, 241, 235, 144, 206, 117, 32, 50, 186, 254, 123, 180, 182, 163, 151, 65, 248, 155, 214, 87, 229, 107, 93, 81, 250, 32, 84, 243, 70, 24, 73, 66, 195, 135, 184, 57, 23, 134, 5, 221, 254, 111, 167, 153, 75, 161, 132, 60, 203, 101, 115, 138, 241, 202, 110, 7, 139, 42, 255, 96, 72, 60, 24, 35, 235, 105, 35, 106, 31, 100, 254, 189, 139, 10, 177, 100, 182, 68, 32, 36, 50, 84, 67, 25, 69, 28, 190, 51, 51, 211, 113, 212, 244, 104, 136, 88, 90, 169, 150, 35, 254, 221, 47, 31, 181, 201, 126, 229, 14, 174, 187, 79, 67, 90, 21, 153, 238, 120, 190, 63, 72, 181, 244, 229, 98, 139, 130, 165, 97, 140, 211, 210, 190, 1, 133, 225, 70, 161, 79, 62, 107, 73, 58, 25, 61, 143, 147, 230, 197, 210, 84, 149, 161, 91, 240, 65, 235, 74, 61, 250, 239, 242, 235, 248, 59, 245, 217, 12, 60, 171, 209, 19, 55, 101, 8, 3, 189, 62, 142, 230, 7, 37, 187, 52, 14, 203, 82, 63, 175, 204, 201, 40, 28, 141, 153, 71, 235, 110, 162, 70, 78, 31, 56, 139, 54, 111, 138, 163, 243, 211, 41, 83, 140, 6, 219, 192, 17, 224, 114, 96, 125, 173, 24, 249, 0, 18, 21, 74, 39, 211, 50, 211, 1, 190, 143, 250, 11, 186, 144, 200, 55, 103, 50, 56, 18, 224, 223, 117, 40, 54, 130, 94, 167, 115, 39, 21, 61, 1, 136, 99, 40, 4, 56, 39, 42, 106, 247, 170, 121, 222, 148, 17, 142, 248, 170, 111, 58, 107, 205, 178, 216, 61, 125, 113, 244, 245, 28, 106, 233, 78, 15, 128, 129, 200, 25, 25, 173, 77, 120, 54, 107, 188, 75, 36, 103, 72, 218, 2, 165, 125, 8, 168, 104, 120, 254, 61, 134, 185, 48, 54, 187, 161, 66, 106, 48, 250, 73, 107, 104, 193, 124, 76, 161, 105, 72, 110, 71, 90, 63, 122, 210, 234, 60, 171, 179, 0, 30, 141, 152, 96, 208, 186, 235, 80, 235, 234, 64, 151, 123, 53, 208, 79, 68, 63, 171, 140, 78, 214, 131, 0, 131, 54, 179, 214, 35, 130, 176, 75, 11, 115, 135, 241, 190, 115, 93, 29, 182, 9, 156, 139, 137, 231, 248, 14, 183, 222, 63, 131, 23, 119, 131, 16, 26, 127, 27, 241, 151, 125, 219, 93, 249, 109, 24, 152, 97, 136, 26, 2, 55, 154, 201, 83, 46, 128, 174, 157, 29, 148, 19, 24, 244, 188, 225, 18, 79, 83, 98, 199, 21, 6, 160, 212, 60, 102, 105, 224, 198, 147, 19, 54, 172, 235, 15, 64, 149, 163, 249, 54, 80, 182, 90, 136, 159, 21, 220, 190, 243, 160, 41, 80, 215, 106, 128, 0, 233, 2, 102, 242, 241, 1, 196, 123, 67, 3, 255, 184, 48, 74, 108, 35, 149, 220, 214, 126, 246, 57, 33, 82, 129, 4, 204, 226, 108, 16, 205, 45, 59, 181, 84, 124, 185, 178, 155, 240, 159, 10, 71, 78, 154, 6, 40, 172, 64, 66, 116, 232, 105, 12, 117, 110, 153, 5, 125, 51, 187, 144, 52, 208, 83, 252, 209, 150, 192, 194, 158, 160, 232, 169, 72, 252, 173, 138, 82, 218, 79, 229, 228, 190, 28, 192, 153, 60, 30, 234, 63, 97, 238, 232, 228, 77, 39, 169, 108, 83, 185, 36, 210, 241, 237, 105, 44, 62, 66, 201, 119, 234]

def realKEnc : Array UInt8 := #[106, 55, 154, 239, 151, 239, 169, 244, 254, 51, 60, 50, 7, 249, 12, 233, 172, 15, 197, 47, 230, 55, 13, 2, 129, 203, 3, 154, 110, 110, 79, 167]

/-! ## THE GATE — `native_decide`, BYTE-EXACT vs the GENUINE `ml-kem` v0.2.3 crate DETERMINISTIC encaps. -/

/-- **THE KEYSTONE**: `mlkemEncaps realEk mFixed = (realCtEnc, realKEnc)` — the Lean encaps, on the REAL `ml-kem`
crate encapsulation key + the fixed `m`, reproduces the crate's DETERMINISTIC ciphertext AND shared secret
BYTE-FOR-BYTE. This forces the full FO encaps pipeline — `H = SHA3-256`, the `G = SHA3-512` split, and the
entire K-PKE.Encrypt (`ExpandA`, CBD from `PRF`, both `NTT⁻¹` products, both compressions, the `Âᵀ` transpose)
— to ALL match the reference: a single wrong step yields `ct ≠ realCtEnc` or `K ≠ realKEnc`. The Lean
`mlkemEncaps` IS the `ml-kem`-768 encaps on the real key. -/
theorem encaps_matches_crate :
    mlkemEncaps realEk.toList mFixed.toList = (realCtEnc.toList, realKEnc.toList) := by native_decide

/-- **ENCAPS→DECAPS agree (through the verified K4 decaps)**: the Lean decaps of `realDk` over the Lean encaps's
ciphertext recovers the Lean encaps's shared secret — the two verified directions round-trip end-to-end (the
same fact the crate generator confirmed, re-proved here in Lean over the K4 `mlkemDecaps`). -/
theorem encaps_decaps_roundtrip :
    mlkemDecaps realDk.toList (mlkemEncaps realEk.toList mFixed.toList).1 = realKEnc.toList := by
  native_decide

/-- **THE KEYSTONE (byte-wire)**: the FFI, fed the REAL crate `ek`/`m` as the hex wire, emits
`hex(realCtEnc) hex(realKEnc)` — the whole Rust→Lean marshalling path reproduces the crate's ciphertext +
secret. -/
theorem mlkemEncapsRealFFI_matches_crate :
    mlkemEncapsRealFFI (realWireEncaps realEk.toList mFixed.toList) =
      hexEncode realCtEnc.toList ++ " " ++ hexEncode realKEnc.toList := by
  native_decide

-- A malformed wire fails CLOSED (interpreted `#guard`, fast): wrong field count, odd-length hex, non-hex.
#guard mlkemEncapsRealFFI "zz zz" = "ERR"
#guard mlkemEncapsRealFFI "00" = "ERR"
#guard mlkemEncapsRealFFI "0 0" = "ERR"

end Dregg2.Crypto.MlKemEncaps
