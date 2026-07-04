//! `object` — content-addressed objects and the bucket's object map.
//!
//! An [`Object`] is the storage analog of a hosted [`Asset`]: bytes + a
//! `Content-Type`. Where a hosted site keys assets by *request path*, an object
//! store keys objects by an arbitrary *object key* (`reports/2026/q2.json`,
//! `images/logo.png`, …) and carries a **content address** — a deterministic
//! digest of `(content_type, body)` — so an object is identified by what it *is*,
//! not only by where it sits. Two buckets storing identical bytes commit the same
//! content address; a single changed byte moves it.
//!
//! [`Asset`]: ../../dreggnet_webapp/hosting/struct.Asset.html

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// One stored object: the bytes + the `Content-Type` to serve them with, plus a
/// deterministic [`content_address`] over both.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Object {
    /// The `Content-Type` of the object (`application/json`, `image/png`, …).
    pub content_type: String,
    /// The object bytes.
    pub body: Vec<u8>,
}

impl Object {
    /// An object with an explicit content-type.
    pub fn new(content_type: impl Into<String>, body: impl Into<Vec<u8>>) -> Object {
        Object {
            content_type: content_type.into(),
            body: body.into(),
        }
    }

    /// An object whose content-type is inferred from `key`'s extension
    /// ([`content_type_for`]).
    pub fn at(key: &str, body: impl Into<Vec<u8>>) -> Object {
        Object {
            content_type: content_type_for(key).to_string(),
            body: body.into(),
        }
    }

    /// The number of stored bytes (the unit storage is metered on).
    pub fn size(&self) -> usize {
        self.body.len()
    }

    /// This object's **content address** — a deterministic digest of
    /// `(content_type, body)`. Identifies the object by its content; the same
    /// bytes always address the same, and any changed byte moves it — the bytes are
    /// packed into the field **injectively** (see [`poseidon2::digest8`]), so a
    /// same-length adversarial byte substitution cannot alias to the same address.
    ///
    /// The object's REAL Poseidon2 leaf hash — the wide 8-felt (~124-bit)
    /// collision-resistant digest the dregg kernel commits a cell value with, on
    /// every build (no FNV stand-in).
    pub fn content_address(&self) -> String {
        poseidon2::felts8_to_hex(&poseidon2::digest8(&[
            self.content_type.as_bytes(),
            &self.body,
        ]))
    }
}

/// The content of a bucket: object key → [`Object`].
///
/// Keys are canonical object keys (no leading slash required; normalized by
/// [`normalize_key`]). A `BTreeMap` so the content — and thus the bucket's
/// content commitment — is canonically ordered.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BucketContent {
    /// key → object, canonically ordered.
    pub objects: BTreeMap<String, Object>,
}

impl BucketContent {
    /// Empty content.
    pub fn new() -> BucketContent {
        BucketContent {
            objects: BTreeMap::new(),
        }
    }

    /// Insert/replace the object at `key`, content-type inferred from the
    /// extension. Returns the previous object at that key, if any.
    pub fn put(&mut self, key: &str, body: impl Into<Vec<u8>>) -> Option<Object> {
        let object = Object::at(key, body);
        self.objects.insert(normalize_key(key), object)
    }

    /// Insert/replace the object at `key` with an explicit content-type.
    pub fn put_object(&mut self, key: &str, object: Object) -> Option<Object> {
        self.objects.insert(normalize_key(key), object)
    }

    /// Remove the object at `key`, returning it if present.
    pub fn remove(&mut self, key: &str) -> Option<Object> {
        self.objects.remove(&normalize_key(key))
    }

    /// The object at `key`, if present.
    pub fn get(&self, key: &str) -> Option<&Object> {
        self.objects.get(&normalize_key(key))
    }

    /// The object keys present, sorted (canonical listing order).
    pub fn keys(&self) -> Vec<String> {
        self.objects.keys().cloned().collect()
    }

    /// Keys with a given prefix, sorted (the standard object-store `list` filter).
    pub fn keys_with_prefix(&self, prefix: &str) -> Vec<String> {
        let prefix = normalize_key(prefix);
        // An empty/`/` prefix lists everything.
        let all = prefix == "/";
        self.objects
            .keys()
            .filter(|k| all || k.starts_with(&prefix))
            .cloned()
            .collect()
    }

    /// Whether the bucket holds no objects.
    pub fn is_empty(&self) -> bool {
        self.objects.is_empty()
    }

    /// Number of objects.
    pub fn len(&self) -> usize {
        self.objects.len()
    }

    /// Total stored bytes across all objects (the storage-meter base).
    pub fn total_bytes(&self) -> usize {
        self.objects.values().map(Object::size).sum()
    }
}

/// Normalize an object key to a canonical form: trim, ensure a single leading
/// `/`, collapse to `/` if empty. Keeping a leading `/` makes prefixes and the
/// content commitment unambiguous, and `keys_with_prefix("/images")` work.
pub fn normalize_key(key: &str) -> String {
    let key = key.trim();
    if key.is_empty() {
        return "/".to_string();
    }
    if key.starts_with('/') {
        key.to_string()
    } else {
        format!("/{key}")
    }
}

/// Whether `key` is a usable object key: non-empty after normalization, ≤1024
/// bytes, no NUL or control bytes. (Object keys are far freer than DNS labels —
/// any path-like string is fine — but they must be clean commitment keys.)
pub fn is_valid_key(key: &str) -> bool {
    let key = key.trim();
    if key.is_empty() || key.len() > 1024 {
        return false;
    }
    !key.bytes().any(|b| b == 0 || b.is_ascii_control())
}

/// Infer a `Content-Type` from a key's file extension. Unknown extensions get
/// `application/octet-stream` (the safe, downloadable default an object store
/// uses).
pub fn content_type_for(key: &str) -> &'static str {
    let ext = key.rsplit('.').next().unwrap_or("").to_ascii_lowercase();
    match ext.as_str() {
        "html" | "htm" => "text/html; charset=utf-8",
        "css" => "text/css; charset=utf-8",
        "js" | "mjs" => "text/javascript; charset=utf-8",
        "json" => "application/json",
        "ndjson" | "jsonl" => "application/x-ndjson",
        "csv" => "text/csv; charset=utf-8",
        "wasm" => "application/wasm",
        "svg" => "image/svg+xml",
        "png" => "image/png",
        "jpg" | "jpeg" => "image/jpeg",
        "gif" => "image/gif",
        "webp" => "image/webp",
        "avif" => "image/avif",
        "ico" => "image/x-icon",
        "txt" | "text" | "log" => "text/plain; charset=utf-8",
        "md" => "text/markdown; charset=utf-8",
        "xml" => "application/xml",
        "pdf" => "application/pdf",
        "zip" => "application/zip",
        "gz" | "tgz" => "application/gzip",
        "tar" => "application/x-tar",
        "bin" | "dat" => "application/octet-stream",
        "woff2" => "font/woff2",
        "woff" => "font/woff",
        "ttf" => "font/ttf",
        "otf" => "font/otf",
        _ => "application/octet-stream",
    }
}

/// Hash an arbitrary byte slice to the canonical digest (used for ad-hoc leaf
/// digests): the wide 8-felt (64-hex) collision-resistant Poseidon2 digest, the
/// same hash family the dregg kernel commits a cell value with.
pub fn digest(bytes: &[u8]) -> String {
    poseidon2::felts8_to_hex(&poseidon2::digest8(&[bytes]))
}

/// The REAL Poseidon2 object/bucket commitment primitives. Wide 8-felt (~124-bit)
/// digests over the kernel's Poseidon2 sponge, the same hash family the dregg umem
/// heap commits with (see `crate::bucket` for the sorted cell-heap root these
/// leaves fold into).
pub(crate) mod poseidon2 {
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::poseidon2::hash_many_8;

    /// A WIDE (8-felt, ~124-bit) Poseidon2 digest over the length-delimited parts.
    /// Each part is prefixed by its byte length so field-domain concatenation is
    /// unambiguous (a server cannot shift bytes between parts without moving it),
    /// and each part's bytes are packed with the **injective** [`pack_bytes`]
    /// (3 bytes/felt, no modular wraparound) so distinct byte strings always map to
    /// distinct felt sequences — the content commitment is a true injective function
    /// of the bytes, so a same-length adversarial byte substitution cannot alias.
    pub(crate) fn digest8(parts: &[&[u8]]) -> [BabyBear; 8] {
        let mut input: Vec<BabyBear> = Vec::new();
        for p in parts {
            input.push(BabyBear::new(p.len() as u32));
            input.extend(pack_bytes(p));
        }
        hash_many_8(&input)
    }

    /// **Injective** byte → field packing for the content commitment.
    ///
    /// Packs **3 little-endian bytes per element** (a u24 value `< 2^24 ≤ p`, so
    /// `BabyBear::new` performs no modular reduction). This is deliberately NOT the
    /// shared `dregg_circuit::field::from_bytes_packed`, which packs **4** bytes into
    /// a u32 and reduces `% p`: since `p ≈ 2^30.9 < 2^32`, ~53% of 4-byte chunks
    /// alias their `+p` partner (`v ≡ v + p`), so two distinct equal-length byte
    /// strings could produce the identical digest and pass the trustless read.
    ///
    /// With 3 bytes/felt there is no wraparound, so within a fixed length two byte
    /// strings differing at any position produce a different felt at that chunk;
    /// combined with the byte-length prefix in [`digest8`] the map is injective for
    /// same-length **and** different-length inputs. The real Poseidon2 `hash_many_8`
    /// stays the hash.
    fn pack_bytes(bytes: &[u8]) -> Vec<BabyBear> {
        let mut out = Vec::with_capacity(bytes.len() / 3 + 1);
        for chunk in bytes.chunks(3) {
            let mut val: u32 = 0;
            for (j, &b) in chunk.iter().enumerate() {
                val |= (b as u32) << (j * 8);
            }
            // val < 2^24 < p, so `new` is the identity (no reduction, injective).
            out.push(BabyBear::new(val));
        }
        out
    }

    /// Lower-hex encode an 8-felt digest (8 × u32 → 64 hex chars).
    pub(crate) fn felts8_to_hex(f: &[BabyBear; 8]) -> String {
        use std::fmt::Write as _;
        let mut s = String::with_capacity(64);
        for x in f {
            let _ = write!(s, "{:08x}", x.as_u32());
        }
        s
    }

    /// Parse a 64-hex 8-felt digest back into its felts (round-trips
    /// [`felts8_to_hex`]; values are canonical `< p`, so the round-trip is exact).
    /// `None` on a wrong length or a non-hex chunk.
    pub(crate) fn parse_felts8(hex: &str) -> Option<[BabyBear; 8]> {
        if hex.len() != 64 {
            return None;
        }
        let mut out = [BabyBear::ZERO; 8];
        for (i, slot) in out.iter_mut().enumerate() {
            let chunk = hex.get(i * 8..i * 8 + 8)?;
            *slot = BabyBear::new(u32::from_str_radix(chunk, 16).ok()?);
        }
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn content_address_is_deterministic_and_sensitive() {
        let a = Object::new("application/json", b"{\"x\":1}".to_vec());
        let b = Object::new("application/json", b"{\"x\":1}".to_vec());
        assert_eq!(a.content_address(), b.content_address());
        // A changed byte moves the address.
        let c = Object::new("application/json", b"{\"x\":2}".to_vec());
        assert_ne!(a.content_address(), c.content_address());
        // A changed content-type moves the address.
        let d = Object::new("text/plain", b"{\"x\":1}".to_vec());
        assert_ne!(a.content_address(), d.content_address());
    }

    /// The anti-aliasing tooth. Under the OLD 4-byte `from_bytes_packed` (u32 `% p`)
    /// two distinct, EQUAL-LENGTH byte strings differing by `+p` on a chunk produced
    /// the identical digest — a same-length adversarial substitution passed the
    /// trustless read. The injective 3-byte packing catches it: the content address
    /// now MOVES, while the underlying `from_bytes_packed` primitive still aliases
    /// (proving these bytes are a genuine old-collision pair, not a random flip).
    #[test]
    fn same_length_alias_substitution_is_caught() {
        use dregg_circuit::field::BabyBear;

        // A concrete `+p` alias pair over one 4-byte chunk (both length 4):
        //   value 1              → LE [01,00,00,00]
        //   value 1 + p          → LE [02,00,00,78]   (p = 0x78000001)
        let honest = vec![0x01u8, 0x00, 0x00, 0x00];
        let forged = vec![0x02u8, 0x00, 0x00, 0x78];
        assert_eq!(
            honest.len(),
            forged.len(),
            "the substitution is same-length"
        );
        assert_ne!(honest, forged, "the bytes genuinely differ");

        // Witness: the SHARED circuit primitive the old code used DOES alias these —
        // so this pair is exactly the collision class the old packing accepted.
        assert_eq!(
            BabyBear::from_bytes_packed(&honest),
            BabyBear::from_bytes_packed(&forged),
            "the old 4-byte %p packing aliases this pair (the pre-fix hole)"
        );

        // After the fix the content address MOVES (would have been equal before).
        let a = Object::new("application/octet-stream", honest.clone());
        let b = Object::new("application/octet-stream", forged.clone());
        assert_ne!(
            a.content_address(),
            b.content_address(),
            "the injective packing separates the aliasing pair"
        );

        // The normal round-trip: identical bytes still address identically.
        let a2 = Object::new("application/octet-stream", honest);
        assert_eq!(a.content_address(), a2.content_address());
    }

    #[test]
    fn key_normalization_and_prefix() {
        let mut c = BucketContent::new();
        c.put("images/logo.png", b"PNG".to_vec());
        c.put("/images/banner.jpg", b"JPG".to_vec());
        c.put("reports/q2.json", b"{}".to_vec());
        assert_eq!(c.len(), 3);
        // Leading slash is canonicalized so both spellings address one namespace.
        assert!(c.get("images/logo.png").is_some());
        assert!(c.get("/images/logo.png").is_some());
        let imgs = c.keys_with_prefix("images");
        assert_eq!(imgs, vec!["/images/banner.jpg", "/images/logo.png"]);
        assert_eq!(c.keys_with_prefix("/").len(), 3);
    }

    #[test]
    fn content_type_inference() {
        assert_eq!(content_type_for("reports/q2.json"), "application/json");
        assert_eq!(content_type_for("a/b/logo.png"), "image/png");
        assert_eq!(content_type_for("notes.md"), "text/markdown; charset=utf-8");
        assert_eq!(content_type_for("blob"), "application/octet-stream");
    }

    #[test]
    fn key_validation() {
        assert!(is_valid_key("reports/2026/q2.json"));
        assert!(is_valid_key("logo.png"));
        assert!(!is_valid_key(""));
        assert!(!is_valid_key("   "));
        assert!(!is_valid_key("has\0nul"));
        assert!(!is_valid_key("has\nnewline"));
    }
}
