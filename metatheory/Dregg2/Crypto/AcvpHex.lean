/-
# `Dregg2.Crypto.AcvpHex` -- hex decoding for the NIST ACVP vector pins.

The ACVP `internalProjection.json` files carry every field as a lowercase hex string. Pinning the hex
VERBATIM (rather than a decoded byte array) keeps the Lean constants diff-able by eye against the
published JSON; this module decodes them at evaluation time.

`decodeHexChars` is fail-closed: it returns `none` on an odd length or any non-hex character, and each
pinning module `#guard`s that every one of its pinned strings decodes and has the FIPS-mandated length.
So a truncated or corrupted transcription cannot silently become a shorter byte string.
-/

namespace Dregg2.Crypto.AcvpHex

/-- One lowercase/uppercase hex nibble to its `[0,16)` value; `none` on a non-hex char. -/
def hexNibble? (c : Char) : Option UInt8 :=
  if '0' <= c && c <= '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' <= c && c <= 'f' then some (UInt8.ofNat (c.toNat - 'a'.toNat + 10))
  else if 'A' <= c && c <= 'F' then some (UInt8.ofNat (c.toNat - 'A'.toNat + 10))
  else none

/-- Decode a hex char list to bytes; `none` on an odd length or any non-hex char (fail-closed). -/
def decodeHexChars : List Char -> Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest => do
      let hi <- hexNibble? a
      let lo <- hexNibble? b
      let tl <- decodeHexChars rest
      return (hi * 16 + lo) :: tl

/-- Decode a hex string to bytes, `[]` on malformed input. Never reached for a pinned vector: the
`wellFormed` `#guard` in each pinning module rejects any string this would fail on. -/
def hexBytes (s : String) : List UInt8 := (decodeHexChars s.toList).getD []

/-- The pinned string is even-length, all-hex, and decodes to exactly `n` bytes. -/
def hexOfLen (s : String) (n : Nat) : Bool :=
  (decodeHexChars s.toList).isSome && (hexBytes s).length == n

end Dregg2.Crypto.AcvpHex
