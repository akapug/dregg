//! Serde helpers: 32-byte digests travel as hex strings on the wire (the
//! node's existing convention for `receipt_hash` etc.).

use serde::{Deserialize, Deserializer, Serializer};

fn parse32<E: serde::de::Error>(s: &str) -> Result<[u8; 32], E> {
    let v = hex::decode(s).map_err(E::custom)?;
    v.try_into()
        .map_err(|_| E::custom("expected 32 hex-encoded bytes"))
}

pub mod serde_hex32 {
    use super::*;

    pub fn serialize<S: Serializer>(v: &[u8; 32], s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&hex::encode(v))
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 32], D::Error> {
        let s = String::deserialize(d)?;
        parse32(&s)
    }
}

pub mod serde_vec_vec_hex32 {
    use super::*;

    pub fn serialize<S: Serializer>(v: &[Vec<[u8; 32]>], s: S) -> Result<S::Ok, S::Error> {
        s.collect_seq(
            v.iter()
                .map(|inner| inner.iter().map(hex::encode).collect::<Vec<_>>()),
        )
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<Vec<[u8; 32]>>, D::Error> {
        let strs = Vec::<Vec<String>>::deserialize(d)?;
        strs.iter()
            .map(|inner| inner.iter().map(|s| parse32(s.as_str())).collect())
            .collect()
    }
}
