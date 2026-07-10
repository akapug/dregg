//! Internal hashing helpers shared by every domain-separated object in the crate.

/// Absorb a length-prefixed byte field into a BLAKE3 hasher.
///
/// Every variable-length field (a domain tag, a `game_binding`, an `event_kind`
/// string, a source output) is written as `len_le_u64 || bytes`. Without the
/// length prefix, two different `(a, b)` splits could hash to the same byte
/// stream (a concatenation collision); the prefix makes the encoding injective.
#[inline]
pub(crate) fn absorb_len_prefixed(h: &mut blake3::Hasher, field: &[u8]) {
    h.update(&(field.len() as u64).to_le_bytes());
    h.update(field);
}
