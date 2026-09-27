//! The Sandstorm `.spk` package — read it, verify it, unpack it.
//!
//! A Sandstorm app ships as a `.spk` file: an Ed25519-signed, **xz**-compressed
//! Cap'n Proto archive (the chroot tree the supervisor read-only-mounts as the
//! grain's app image). Two facts make the format load-bearing for the dregg
//! integration, and this module realizes both *for real* (real crypto, real xz):
//!
//! 1. **The App ID *is* the signing key.** The package is signed with an Ed25519
//!    key; the App ID is the Crockford-base32 of that public key (Sandstorm's
//!    32-symbol alphabet `0123456789acdefghjkmnpqrstuvwxyz`). There is no CA: "this
//!    grain runs the app signed by key K" is an intrinsic, verifiable fact. dregg
//!    reuses it directly — the App ID doubles as the app's issuer/publisher identity.
//! 2. **The signature binds the whole app image.** Verifying the Ed25519 signature
//!    over the archive bytes is what lets a host (or a light client) trust that the
//!    chroot it is about to run is exactly the release the key signed — tamper any
//!    byte and the signature fails. This is the integrity root the whole grain rests
//!    on, so we verify it before a grain ever launches ([`Spk::parse`]).
//!
//! ## The real wire — no projection
//!
//! Every layer of the `.spk` is real, including the inner Cap'n Proto messages:
//!
//! ```text
//! [magic : 8 bytes, uncompressed]
//! [xz-stream] ──decompresses to──▶ [capnp Signature message][capnp Archive message]
//! ```
//!
//! confirmed against upstream `spk.c++` + `package.capnp`. Concretely (see those
//! sources):
//!
//! - **Container** — the 8-byte [`SPK_MAGIC`], then a real xz stream (`lzma-rs`).
//! - **`Signature`** (`{ publicKey @0 :Data, signature @1 :Data }`) — a genuine
//!   Cap'n Proto message decoded via [`crate::capnp_wire`]. `publicKey` is the 32-byte
//!   Ed25519 key; the App ID is its Sandstorm-base32.
//! - **The signature** — libsodium's *combined* `crypto_sign` over `SHA-512(archive
//!   bytes)`: the 128-byte `signature` field is `[ed25519 sig : 64][SHA-512 hash : 64]`.
//!   Verifying mirrors `spk.c++`'s `crypto_sign_open`: check the Ed25519 signature over
//!   the embedded hash, then require that hash to equal `SHA-512` of the archive message
//!   bytes (the bytes that follow the `Signature` message). A grain never launches from
//!   an image whose signature does not bind it.
//! - **`Archive`** (`List(File)`; a `File` is regular / executable / symlink /
//!   directory + `lastModificationTimeNs`) — decoded from the genuine capnp wire
//!   (multi-segment, far pointers and all) via [`crate::capnp_wire`].
//!
//! [`SpkBuilder`] packs a synthetic, *genuinely signed* `.spk` in this exact wire
//! (real capnp messages, real combined Ed25519/SHA-512 signature), so the reader, the
//! manifest decode, and the grain launch are exercised against the real format — and
//! the same code reads a real catalog package (`fixtures/sample.spk`).

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;

use data_encoding::Specification;
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use sha2::{Digest, Sha512};

use crate::capnp_wire::{self, Message, WireContent, WireFile};
use crate::manifest::AppId;

/// Default cap on accepted decompressed bytes. `lzma-rs` first buffers each whole
/// XZ block internally, so this is **not a peak-memory bound**. Parse untrusted
/// packages in a process with an independent memory and time limit. Large real apps
/// (e.g. Wekan) require an explicit larger [`Spk::parse_with_limit`] bound.
pub const MAX_DECOMPRESSED_BYTES: usize = 256 * 1024 * 1024;

const MAX_ARCHIVE_DEPTH: usize = 64;
const MAX_ARCHIVE_FILES: usize = 100_000;
const MAX_ARCHIVE_NAME_BYTES: usize = 16 * 1024 * 1024;
const MAX_FILE_NAME_BYTES: usize = 255;

/// A `std::io::Write` sink that appends into a `Vec` but **refuses** to grow past a
/// byte limit. On overflow it flips `overflowed` and returns an error so the
/// decompressor stops after its internally buffered block is written.
struct BoundedSink<'a> {
    buf: &'a mut Vec<u8>,
    limit: usize,
    overflowed: &'a Cell<bool>,
}

impl Write for BoundedSink<'_> {
    fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
        if self.buf.len().saturating_add(data.len()) > self.limit {
            self.overflowed.set(true);
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "xz output exceeds the maximum decompressed size",
            ));
        }
        self.buf.extend_from_slice(data);
        Ok(data.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// The 8-byte magic prefix every `.spk` file begins with.
///
/// This is the **canonical Sandstorm value**, confirmed verbatim against the
/// upstream source: `package.capnp` defines `const magicNumber :Data =
/// "\x8f\xc6\xcd\xef\x45\x1a\xea\x96"`, and `spk.c++` writes it uncompressed
/// ahead of the xz stream (`spk::MAGIC_NUMBER`). Cross-checked against the Go
/// port `zenhack/go.sandstorm` (`[]byte{143, 198, 205, 239, 69, 26, 234, 150}`).
/// A real catalog `.spk` therefore begins with exactly these bytes.
pub const SPK_MAGIC: [u8; 8] = [0x8f, 0xc6, 0xcd, 0xef, 0x45, 0x1a, 0xea, 0x96];

/// The conventional archive path of the package manifest. The supervisor and
/// `sandstorm-http-bridge` read the `Manifest` from this file at the chroot root.
pub const MANIFEST_PATH: &str = "sandstorm-manifest";

/// Sandstorm's base32 alphabet (Douglas-Crockford-style, 32 symbols, no `b i l o`,
/// no padding) — used for App IDs and for `dga1_` cap tokens.
const SANDSTORM_BASE32: &str = "0123456789acdefghjkmnpqrstuvwxyz";

/// Encode bytes in Sandstorm's base32 alphabet (App ID / token encoding).
pub fn base32(bytes: &[u8]) -> String {
    let mut spec = Specification::new();
    spec.symbols.push_str(SANDSTORM_BASE32);
    // No padding — Sandstorm app ids are bare base32.
    spec.encoding().expect("valid base32 spec").encode(bytes)
}

/// One entry in the package archive (mirrors `package.capnp:Archive.File`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FileContent {
    /// A normal file's bytes.
    Regular(Vec<u8>),
    /// A file the supervisor marks executable (`+x` in the chroot).
    Executable(Vec<u8>),
    /// A symlink target.
    Symlink(String),
    /// A subdirectory (nested entries).
    Directory(Vec<File>),
}

/// A file in the package's chroot tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct File {
    /// The entry name (one path component; directories nest).
    pub name: String,
    pub content: FileContent,
    /// `lastModificationTimeNs` — preserved for reproducibility.
    pub mtime_ns: i64,
}

impl File {
    pub fn regular(name: impl Into<String>, bytes: impl Into<Vec<u8>>) -> Self {
        File {
            name: name.into(),
            content: FileContent::Regular(bytes.into()),
            mtime_ns: 0,
        }
    }
    pub fn executable(name: impl Into<String>, bytes: impl Into<Vec<u8>>) -> Self {
        File {
            name: name.into(),
            content: FileContent::Executable(bytes.into()),
            mtime_ns: 0,
        }
    }
}

/// The package archive: the whole chroot tree (`package.capnp:Archive`).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Archive {
    pub files: Vec<File>,
}

impl Archive {
    /// Look up a file's bytes by path. Matches either a flat entry whose `name` is
    /// the whole path (`"app/server"`), or a nested directory walk (`app` → `server`).
    pub fn find(&self, path: &str) -> Option<&[u8]> {
        // Flat match first: an entry whose name is the full path.
        if let Some(f) = self.files.iter().find(|f| f.name == path) {
            if let FileContent::Regular(b) | FileContent::Executable(b) = &f.content {
                return Some(b);
            }
        }
        let mut parts = path.split('/').filter(|p| !p.is_empty());
        let mut files = &self.files;
        let mut target = parts.next()?;
        loop {
            let f = files.iter().find(|f| f.name == target)?;
            match (&f.content, parts.next()) {
                (FileContent::Regular(b) | FileContent::Executable(b), None) => return Some(b),
                (FileContent::Directory(sub), Some(next)) => {
                    files = sub;
                    target = next;
                }
                _ => return None,
            }
        }
    }

    /// Flatten to `path -> bytes` (regular + executable files), for the read-only
    /// chroot image the grain workload mounts.
    pub fn flatten(&self) -> BTreeMap<String, Vec<u8>> {
        fn walk(prefix: &str, files: &[File], out: &mut BTreeMap<String, Vec<u8>>) {
            for f in files {
                let path = if prefix.is_empty() {
                    f.name.clone()
                } else {
                    format!("{prefix}/{}", f.name)
                };
                match &f.content {
                    FileContent::Regular(b) | FileContent::Executable(b) => {
                        out.insert(path, b.clone());
                    }
                    FileContent::Directory(sub) => walk(&path, sub, out),
                    FileContent::Symlink(_) => {}
                }
            }
        }
        let mut out = BTreeMap::new();
        walk("", &self.files, &mut out);
        out
    }

    /// Serialize the archive to its canonical **capnp `Archive` message** bytes — the
    /// bytes the package signature is computed over (a framed, single-segment capnp
    /// message a stock `capnp` tool reads back).
    fn to_bytes(&self) -> Vec<u8> {
        capnp_wire::write_archive(&to_wire(&self.files))
    }

    /// Decode an `Archive` from the real capnp `Archive` message bytes (the second
    /// message in a `.spk`'s decompressed stream). Handles the genuine multi-segment,
    /// far-pointer wire a real catalog package uses; bounded against over-count bombs.
    fn from_bytes(buf: &[u8], max_data_bytes: usize) -> Result<Archive, SpkError> {
        let (msg, _consumed) =
            Message::parse_prefix(buf).map_err(|e| SpkError::Archive(e.to_string()))?;
        let root = msg.root().map_err(|e| SpkError::Archive(e.to_string()))?;
        let files = match root
            .get_list(0)
            .map_err(|e| SpkError::Archive(e.to_string()))?
        {
            Some(list) => decode_files(&list, 0, &mut ArchiveBudget::new(max_data_bytes))?,
            None => Vec::new(),
        };
        Ok(Archive { files })
    }
}

/// Build the borrowing [`WireFile`] tree the capnp writer consumes from a `File` tree.
fn to_wire(files: &[File]) -> Vec<WireFile<'_>> {
    files
        .iter()
        .map(|f| {
            let content = match &f.content {
                FileContent::Regular(b) => WireContent::Regular(b),
                FileContent::Executable(b) => WireContent::Executable(b),
                FileContent::Symlink(t) => WireContent::Symlink(t),
                FileContent::Directory(sub) => WireContent::Directory(to_wire(sub)),
            };
            WireFile {
                name: &f.name,
                content,
                mtime_ns: f.mtime_ns,
            }
        })
        .collect()
}

/// Decode a composite `List(File)` from the capnp wire into the `File` tree. The
/// discriminant (data byte 0) selects the union member in declaration order
/// (`regular=0, executable=1, symlink=2, directory=3`); `lastModificationTimeNs` is the
/// `Int64` at data byte 8; `name` is pointer slot 0 and the union value pointer slot 1.
struct ArchiveBudget {
    files: usize,
    name_bytes: usize,
    data_bytes: usize,
    max_data_bytes: usize,
}

impl ArchiveBudget {
    fn new(max_data_bytes: usize) -> Self {
        Self {
            files: 0,
            name_bytes: 0,
            data_bytes: 0,
            max_data_bytes,
        }
    }
}

fn decode_files(
    list: &capnp_wire::List<'_, '_>,
    depth: usize,
    budget: &mut ArchiveBudget,
) -> Result<Vec<File>, SpkError> {
    if depth > MAX_ARCHIVE_DEPTH {
        return Err(SpkError::Archive("archive directory depth exceeded".into()));
    }
    if list.len() > MAX_ARCHIVE_FILES.saturating_sub(budget.files) {
        return Err(SpkError::Archive("archive file count exceeded".into()));
    }
    let structs = list
        .structs()
        .map_err(|e| SpkError::Archive(e.to_string()))?;
    if structs.len() > MAX_ARCHIVE_FILES.saturating_sub(budget.files) {
        return Err(SpkError::Archive("archive file count exceeded".into()));
    }
    let mut out = Vec::with_capacity(structs.len());
    let mut names = BTreeSet::new();
    for s in structs {
        budget.files += 1;
        let name = s
            .get_text(0)
            .map_err(|e| SpkError::Archive(e.to_string()))?;
        if name.is_empty()
            || name == "."
            || name == ".."
            || name.contains('/')
            || name.contains('\0')
            || name.len() > MAX_FILE_NAME_BYTES
        {
            return Err(SpkError::Archive("invalid archive file name".into()));
        }
        if !names.insert(name.clone()) {
            return Err(SpkError::Archive("duplicate archive file name".into()));
        }
        budget.name_bytes = budget.name_bytes.saturating_add(name.len());
        if budget.name_bytes > MAX_ARCHIVE_NAME_BYTES {
            return Err(SpkError::Archive("archive name bytes exceeded".into()));
        }
        let mtime_ns = s.get_i64(8);
        let get_data = |i| s.get_data(i).map_err(|e| SpkError::Archive(e.to_string()));
        let content = match s.get_u16(0) {
            0 | 1 => {
                let data = get_data(1)?;
                budget.data_bytes = budget.data_bytes.saturating_add(data.len());
                if budget.data_bytes > budget.max_data_bytes {
                    return Err(SpkError::Archive("archive file bytes exceeded".into()));
                }
                if s.get_u16(0) == 0 {
                    FileContent::Regular(data)
                } else {
                    FileContent::Executable(data)
                }
            }
            2 => FileContent::Symlink(
                s.get_text(1)
                    .map_err(|e| SpkError::Archive(e.to_string()))?,
            ),
            3 => {
                let sub = match s
                    .get_list(1)
                    .map_err(|e| SpkError::Archive(e.to_string()))?
                {
                    Some(l) => decode_files(&l, depth + 1, budget)?,
                    None => Vec::new(),
                };
                FileContent::Directory(sub)
            }
            other => return Err(SpkError::Archive(format!("bad file union tag {other}"))),
        };
        out.push(File {
            name,
            content,
            mtime_ns,
        });
    }
    Ok(out)
}

/// A parsed, signature-verified `.spk` package.
#[derive(Clone, Debug)]
pub struct Spk {
    /// The Ed25519 public key that signed the package — the App ID's source.
    pub public_key: [u8; 32],
    /// The chroot tree (read-only app image).
    pub archive: Archive,
}

/// Why reading a `.spk` failed.
#[derive(Debug, PartialEq, Eq)]
pub enum SpkError {
    /// The magic prefix did not match — not a `.spk` (or a wrong magic constant).
    BadMagic,
    /// xz decompression failed (corrupt container).
    Decompress(String),
    /// The decompressed output exceeded the selected limit; the XZ decoder may
    /// still allocate an uncapped temporary block before detecting this.
    TooLarge,
    /// The decompressed stream was too short / malformed (pubkey/sig/archive split).
    Truncated,
    /// The Ed25519 signature did not verify against the archive bytes — tampered or
    /// mis-signed. The grain MUST NOT launch.
    BadSignature,
    /// The inner archive codec failed.
    Archive(String),
}

impl std::fmt::Display for SpkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpkError::BadMagic => write!(f, "not a .spk: bad magic prefix"),
            SpkError::Decompress(e) => write!(f, ".spk xz decompress failed: {e}"),
            SpkError::TooLarge => write!(f, ".spk exceeds the selected decompressed size limit"),
            SpkError::Truncated => write!(f, ".spk payload truncated"),
            SpkError::BadSignature => {
                write!(f, ".spk signature does not verify — tampered or mis-signed")
            }
            SpkError::Archive(e) => write!(f, ".spk archive decode failed: {e}"),
        }
    }
}
impl std::error::Error for SpkError {}

impl Spk {
    /// Read and **verify** a `.spk` from its raw bytes: check the magic, xz-decompress,
    /// split out the public key + signature + archive, verify the Ed25519 signature
    /// over the archive bytes, and decode the archive. A failed signature is a hard
    /// error — a grain never launches from an unverified image.
    pub fn parse(bytes: &[u8]) -> Result<Spk, SpkError> {
        Self::parse_with_limit(bytes, MAX_DECOMPRESSED_BYTES)
    }

    /// Like [`parse`](Self::parse) but with an explicit decompressed-size cap. The
    /// public [`parse`] uses [`MAX_DECOMPRESSED_BYTES`]; this exists so a host can pin
    /// a tighter bound (and so the bomb defense is exercised cheaply in tests). The xz
    /// stream is decompressed into a [`BoundedSink`]; once output would exceed `limit`
    /// the decompressor is stopped and [`SpkError::TooLarge`] is returned before
    /// signature checking. The decoder may buffer a whole block before writing.
    pub fn parse_with_limit(bytes: &[u8], limit: usize) -> Result<Spk, SpkError> {
        let body = bytes
            .strip_prefix(&SPK_MAGIC[..])
            .ok_or(SpkError::BadMagic)?;

        // xz-decompress the container into a size-bounded sink (refuse a bomb).
        let mut plain = Vec::new();
        let overflowed = Cell::new(false);
        {
            let mut sink = BoundedSink {
                buf: &mut plain,
                limit,
                overflowed: &overflowed,
            };
            let res = lzma_rs::xz_decompress(&mut std::io::Cursor::new(body), &mut sink);
            if overflowed.get() {
                // The sink aborted decompression at the cap — a decompression bomb.
                return Err(SpkError::TooLarge);
            }
            res.map_err(|e| SpkError::Decompress(e.to_string()))?;
        }

        // The decompressed stream is `[capnp Signature message][capnp Archive message]`.
        // Decode the first (Signature) message and learn where it ends; the rest is the
        // archive message bytes (== sandstorm's `tmpData`, what the signature binds).
        let (sig_msg, consumed) = Message::parse_prefix(&plain).map_err(|_| SpkError::Truncated)?;
        let sig_root = sig_msg.root().map_err(|_| SpkError::Truncated)?;
        let public_key_vec = sig_root.get_data(0).map_err(|_| SpkError::Truncated)?;
        // The `signature` field is libsodium's combined `crypto_sign` output:
        // `[ed25519 sig : 64][SHA-512 of the archive : 64]` = 128 bytes.
        let sig_field = sig_root.get_data(1).map_err(|_| SpkError::Truncated)?;
        if public_key_vec.len() != 32 || sig_field.len() != 64 + 64 {
            return Err(SpkError::BadSignature);
        }
        let mut public_key = [0u8; 32];
        public_key.copy_from_slice(&public_key_vec);
        let archive_bytes = plain.get(consumed..).ok_or(SpkError::Truncated)?;

        // Verify exactly as `spk.c++`'s `crypto_sign_open` does: the Ed25519 signature
        // is over the embedded 64-byte message, and that message must be SHA-512 of the
        // archive bytes. Both must hold, or the image is tampered / mis-signed.
        let mut sig_bytes = [0u8; 64];
        sig_bytes.copy_from_slice(&sig_field[..64]);
        let embedded_hash = &sig_field[64..];
        let mut hasher = Sha512::new();
        hasher.update(archive_bytes);
        let computed = hasher.finalize();
        if embedded_hash != computed.as_slice() {
            return Err(SpkError::BadSignature);
        }
        let vk = VerifyingKey::from_bytes(&public_key).map_err(|_| SpkError::BadSignature)?;
        let sig = Signature::from_bytes(&sig_bytes);
        vk.verify(embedded_hash, &sig)
            .map_err(|_| SpkError::BadSignature)?;

        let archive = Archive::from_bytes(archive_bytes, limit)?;
        Ok(Spk {
            public_key,
            archive,
        })
    }

    /// The App ID — the Crockford-base32 of the signing public key. Intrinsic and
    /// verifiable: all packages signed by this key are releases of one app.
    pub fn app_id(&self) -> AppId {
        AppId(base32(&self.public_key))
    }

    /// The raw manifest bytes (from [`MANIFEST_PATH`] in the archive), if present.
    pub fn manifest_bytes(&self) -> Option<&[u8]> {
        self.archive.find(MANIFEST_PATH)
    }
}

/// Pack a synthetic, genuinely-signed `.spk` — for tests and for exercising the
/// reader/manifest/grain path against the real format before a real package lands.
pub struct SpkBuilder {
    files: Vec<File>,
}

impl SpkBuilder {
    pub fn new() -> Self {
        SpkBuilder { files: Vec::new() }
    }

    /// Add the manifest (its bytes go to [`MANIFEST_PATH`]).
    pub fn manifest_json(mut self, json: &str) -> Self {
        self.files
            .push(File::regular(MANIFEST_PATH, json.as_bytes().to_vec()));
        self
    }

    /// Add an arbitrary file to the chroot image.
    pub fn file(mut self, f: File) -> Self {
        self.files.push(f);
        self
    }

    /// Sign with `signing_key` and produce the `.spk` bytes in the **real Sandstorm
    /// wire**: `magic ++ xz(capnp Signature ++ capnp Archive)`, where the signature is
    /// libsodium's combined `crypto_sign` over `SHA-512` of the archive message bytes
    /// (`[ed25519 sig : 64][SHA-512 : 64]`). The App ID is the base32 of the public key.
    pub fn pack(self, signing_key: &SigningKey) -> Vec<u8> {
        let archive = Archive { files: self.files };
        let archive_msg = archive.to_bytes();

        // libsodium combined `crypto_sign(SHA-512(archive))`: sign the 64-byte hash,
        // then store `sig || hash` (exactly `spk.c++`'s 128-byte signature field).
        let mut hasher = Sha512::new();
        hasher.update(&archive_msg);
        let hash = hasher.finalize();
        let sig = signing_key.sign(&hash);
        let mut sig_field = Vec::with_capacity(128);
        sig_field.extend_from_slice(&sig.to_bytes());
        sig_field.extend_from_slice(&hash);

        let pubkey = signing_key.verifying_key().to_bytes();
        let sig_msg = capnp_wire::write_signature(&pubkey, &sig_field);

        let mut plain = sig_msg;
        plain.extend_from_slice(&archive_msg);

        let mut compressed = Vec::new();
        lzma_rs::xz_compress(&mut std::io::Cursor::new(&plain), &mut compressed)
            .expect("xz compress");

        let mut out = Vec::with_capacity(8 + compressed.len());
        out.extend_from_slice(&SPK_MAGIC);
        out.extend_from_slice(&compressed);
        out
    }
}

impl Default for SpkBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
pub(crate) fn test_signing_key() -> SigningKey {
    // A fixed seed → deterministic App ID across runs (Ed25519 signing is
    // deterministic, so no RNG is needed).
    SigningKey::from_bytes(&[7u8; 32])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn etherpad_manifest_json() -> &'static str {
        r#"{
          "app_id": "ignored-the-real-id-comes-from-the-signing-key",
          "app_title": "Etherpad",
          "app_version": 33,
          "continue_command": { "argv": ["/sandstorm-http-bridge", "8000", "--", "/start.sh"] },
          "bridge_config": { "api_port": 8000, "permissions": ["view", "edit"], "roles": [] }
        }"#
    }

    fn sample_spk() -> Vec<u8> {
        SpkBuilder::new()
            .manifest_json(etherpad_manifest_json())
            .file(File::executable(
                "start.sh",
                b"#!/bin/sh\nexec /app/server\n".to_vec(),
            ))
            .file(File {
                name: "app".into(),
                content: FileContent::Directory(vec![File::regular(
                    "server",
                    b"<binary>".to_vec(),
                )]),
                mtime_ns: 0,
            })
            .pack(&test_signing_key())
    }

    #[test]
    fn roundtrips_a_signed_spk() {
        let bytes = sample_spk();
        let spk = Spk::parse(&bytes).expect("valid spk");
        // The manifest is reachable at the conventional path.
        assert!(spk.manifest_bytes().is_some());
        // The chroot files survived the round trip.
        assert_eq!(spk.archive.find("app/server"), Some(&b"<binary>"[..]));
        assert!(spk.archive.find("start.sh").is_some());
    }

    #[test]
    fn app_id_is_the_base32_of_the_signing_key() {
        let spk = Spk::parse(&sample_spk()).unwrap();
        let expected = base32(test_signing_key().verifying_key().as_bytes());
        assert_eq!(spk.app_id(), AppId(expected));
        // App IDs are Sandstorm-base32: no padding, none of b/i/l/o.
        let id = spk.app_id().0;
        assert!(!id.contains('='));
        assert!(!id.contains('b') && !id.contains('i') && !id.contains('l') && !id.contains('o'));
    }

    #[test]
    fn a_tampered_image_fails_the_signature() {
        let mut bytes = sample_spk();
        // Flip a byte deep in the xz container (corrupts the signed archive).
        let n = bytes.len();
        bytes[n - 8] ^= 0xff;
        match Spk::parse(&bytes) {
            // Either the xz frame check or the Ed25519 signature catches it; both
            // refuse to hand back a launchable image.
            Err(SpkError::BadSignature)
            | Err(SpkError::Decompress(_))
            | Err(SpkError::Archive(_)) => {}
            other => panic!("tamper not caught: {other:?}"),
        }
    }

    #[test]
    fn a_resigned_archive_changes_the_app_id() {
        // A different key signing the same files → a different app (App ID = key).
        let other = SigningKey::from_bytes(&[9u8; 32]);
        let a = Spk::parse(&sample_spk()).unwrap().app_id();
        let bytes_b = SpkBuilder::new()
            .manifest_json(etherpad_manifest_json())
            .pack(&other);
        let b = Spk::parse(&bytes_b).unwrap().app_id();
        assert_ne!(a, b);
    }

    #[test]
    fn wrong_magic_is_rejected() {
        let mut bytes = sample_spk();
        bytes[0] ^= 0xff;
        assert!(matches!(Spk::parse(&bytes), Err(SpkError::BadMagic)));
    }

    /// An xz decompression bomb is refused: the **decompressed output size** is
    /// bounded during the xz stream, *before* the signature check — so a package
    /// whose body expands past the cap is refused as [`SpkError::TooLarge`]. The cap
    /// bounds accepted output, though lzma-rs may buffer an XZ block internally.
    /// A real xz bomb is tiny on the wire and huge in memory; the cap applies
    /// regardless of compression ratio
    /// (lzma-rs's bundled encoder happens to store raw, so we size the payload past the
    /// cap directly — the `BoundedSink` path exercised is identical to a real bomb's).
    #[test]
    fn an_xz_bomb_is_refused_before_signature() {
        let key = test_signing_key();
        let payload = 256 * 1024; // a body that decompresses past the 64 KiB test cap
        let spk = SpkBuilder::new()
            .file(File::regular("big", vec![0u8; payload]))
            .pack(&key);
        // A 64 KiB output cap is blown and the package is refused.
        match Spk::parse_with_limit(&spk, 64 * 1024) {
            Err(SpkError::TooLarge) => {}
            other => panic!("xz bomb not refused: {:?}", other.map(|_| "ok")),
        }
        // The same package parses cleanly under the real (generous) cap.
        assert!(Spk::parse(&spk).is_ok());
    }

    /// A capnp over-count bomb is refused: a crafted `Archive`
    /// message whose `List(File)` composite tag claims a huge element count with no
    /// backing words is rejected before allocation by the capnp reader's count guard —
    /// a naive `Vec::with_capacity(n)` would have attempted a multi-GB allocation.
    #[test]
    fn a_bomb_file_count_is_refused_before_allocation() {
        // Frame: 1 segment, 3 words. word0 = root struct ptr (0 data, 1 ptr).
        // word1 = the Archive's files list pointer (composite, points at word2 tag).
        // word2 = a composite tag claiming ~5.4e8 elements with no bodies behind it.
        let mut buf = Vec::new();
        buf.extend_from_slice(&0u32.to_le_bytes()); // segcount-1
        buf.extend_from_slice(&3u32.to_le_bytes()); // 3 words
                                                    // root struct pointer: offset 0 (points to word1), 0 data words, 1 ptr word.
        let root: u64 = (0u64 << 2) | (0u64 << 32) | (1u64 << 48);
        buf.extend_from_slice(&root.to_le_bytes());
        // files list pointer: type=1, offset=0 (tag is the next word), elem=7 composite,
        // count(word-count) = max.
        let lp: u64 = 1 | (0u64 << 2) | (7u64 << 32) | (0x1fff_ffffu64 << 35);
        buf.extend_from_slice(&lp.to_le_bytes());
        // composite tag: element count = max, stride 1 word (claims a giant body).
        let tag: u64 = (0x1fff_ffffu64 << 2) | (1u64 << 32);
        buf.extend_from_slice(&tag.to_le_bytes());
        match Archive::from_bytes(&buf, buf.len()) {
            Err(SpkError::Archive(_)) => {}
            other => panic!("capnp over-count bomb not refused: {other:?}"),
        }
    }

    fn frame(words: &[u64]) -> Vec<u8> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&0u32.to_le_bytes());
        bytes.extend_from_slice(&(words.len() as u32).to_le_bytes());
        for word in words {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        bytes
    }

    #[test]
    fn zero_stride_composite_count_is_refused() {
        // One tag can claim many zero-sized File structs without any body words.
        let bytes = frame(&[1u64 << 48, 1 | (7u64 << 32), 4096u64 << 2]);
        assert_eq!(
            Archive::from_bytes(&bytes, bytes.len())
                .unwrap_err()
                .to_string(),
            ".spk archive decode failed: capnp list count exceeds message bytes"
        );
    }

    #[test]
    fn aggregate_file_count_is_refused_before_struct_allocation() {
        // The declared count exceeds the archive budget; no body allocation is needed.
        let count = (MAX_ARCHIVE_FILES + 1) as u64;
        let bytes = frame(&[
            1u64 << 48,
            1 | (7u64 << 32) | (count << 35),
            (count << 2) | (1u64 << 32),
        ]);
        assert_eq!(
            Archive::from_bytes(&bytes, bytes.len())
                .unwrap_err()
                .to_string(),
            ".spk archive decode failed: archive file count exceeded"
        );
    }

    #[test]
    fn recursive_directory_is_refused_at_depth_budget() {
        // The directory's pointer loops back to the same composite File list.
        let back = 1 | (((1u64 << 30) - 5) << 2) | (7u64 << 32) | (4u64 << 35);
        let name = 1 | (1u64 << 2) | (2u64 << 32) | (2u64 << 35);
        let bytes = frame(&[
            1u64 << 48,
            1 | (7u64 << 32) | (4u64 << 35),
            (1u64 << 2) | (2u64 << 32) | (2u64 << 48),
            3,
            0,
            name,
            back,
            b'x' as u64,
        ]);
        assert_eq!(
            Archive::from_bytes(&bytes, bytes.len())
                .unwrap_err()
                .to_string(),
            ".spk archive decode failed: archive directory depth exceeded"
        );
    }

    #[test]
    fn duplicate_and_invalid_names_are_refused() {
        for names in [vec!["same", "same"], vec![".."], vec!["a/b"]] {
            let files: Vec<File> = names
                .into_iter()
                .map(|name| File::regular(name, b"x".to_vec()))
                .collect();
            let bytes = Archive { files }.to_bytes();
            assert!(matches!(
                Archive::from_bytes(&bytes, bytes.len()),
                Err(SpkError::Archive(_))
            ));
        }
    }

    #[test]
    fn aggregate_file_bytes_are_refused() {
        let bytes = Archive {
            files: vec![File::regular("data", b"abc".to_vec())],
        }
        .to_bytes();
        assert_eq!(
            Archive::from_bytes(&bytes, 2).unwrap_err().to_string(),
            ".spk archive decode failed: archive file bytes exceeded"
        );
    }

    #[test]
    fn aggregate_name_bytes_are_refused() {
        let bytes = Archive {
            files: vec![File::regular("name", b"x".to_vec())],
        }
        .to_bytes();
        let (msg, _) = Message::parse_prefix(&bytes).unwrap();
        let list = msg.root().unwrap().get_list(0).unwrap().unwrap();
        let mut budget = ArchiveBudget::new(bytes.len());
        budget.name_bytes = MAX_ARCHIVE_NAME_BYTES;
        assert_eq!(
            decode_files(&list, 0, &mut budget).unwrap_err().to_string(),
            ".spk archive decode failed: archive name bytes exceeded"
        );
    }

    /// The magic prefix is the canonical Sandstorm `magicNumber`, pinned so an
    /// accidental edit can't silently diverge from a real `.spk`. Confirmed
    /// verbatim against upstream `package.capnp`
    /// (`const magicNumber :Data = "\x8f\xc6\xcd\xef\x45\x1a\xea\x96"`) and the
    /// Go port `zenhack/go.sandstorm` (`[]byte{143,198,205,239,69,26,234,150}`).
    /// A real catalog `.spk` begins with exactly these 8 bytes.
    #[test]
    fn magic_matches_the_canonical_sandstorm_value() {
        assert_eq!(SPK_MAGIC, [0x8f, 0xc6, 0xcd, 0xef, 0x45, 0x1a, 0xea, 0x96]);
        assert_eq!(SPK_MAGIC, [143, 198, 205, 239, 69, 26, 234, 150]);
        // And a packed package actually leads with it.
        assert!(sample_spk().starts_with(&SPK_MAGIC));
    }
}
