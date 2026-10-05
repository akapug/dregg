//! Offline admission reader for a byte-COPY of a `dregg.redb` store (task/4268).
//!
//! A copied store is evidence, never authority. This reader audits a copy —
//! taken from a live or retired node — without ever mutating it and without
//! booting a node: no node constructors, no key creation, no network, no
//! repair, no write transaction.
//!
//! ## Why `PersistentStore::open` is inadmissible here
//!
//! `PersistentStore::open` goes through `redb::Database::create`, which opens
//! the file `O_RDWR` and writes on open whenever the super-header's
//! `RECOVERY_REQUIRED` god-byte bit is set or the stored layout length differs
//! from the file length (`TransactionalMemory::new`, redb 2.6.3
//! `page_manager.rs`). A copy taken while the source was mid-commit — or of a
//! node that was killed — is exactly such a file: a normal open *repairs* it,
//! silently rewriting the evidence under audit. `Database::drop` also flushes
//! allocator state (v2 format), so even a clean open mutates the copy on the
//! way out. Neither is admissible for an offline audit reader.
//!
//! ## The read-only envelope
//!
//! 1. The file is opened `O_RDONLY` — no write permission exists on the fd.
//! 2. A fixed pre-flight reads the 320-byte redb v2 super-header itself and
//!    refuses *named* cases before redb sees the file: bad magic or a short
//!    image (`Layout`), `RECOVERY_REQUIRED` or a layout/file-length mismatch
//!    (`Dirty` — the two conditions under which `Database::open` would write a
//!    recovery header), a non-4KiB page size or a non-v2 commit-slot version
//!    (`Header` — a v3 image would take the repair path in redb 2.6.3).
//! 3. `redb::ReadOnlyDatabase` (the `vendor/redb-readonly` seam, task/4268
//!    DATA 011ceec2) opens the image through `TransactionalMemory`'s read-only
//!    mode: it re-checks every refusal above inside the library, never runs the
//!    writable open or drop protocol, and structurally cannot `begin_write`,
//!    `upgrade`, or `compact`. Behind it sits [`ReadOnlyBackend`], whose
//!    `write`/`set_len` fail closed even if a code path tried.
//! 4. Exactly ONE `ReadTransaction` is taken at open and owned by the handle.
//!    It is never handed out owned — every read goes through `&self` methods —
//!    and [`Self::close`] reaps it through `ReadTransaction::close`, which
//!    fails if any table or iterator escaped. The transaction therefore cannot
//!    outlive the handle in any representable use.
//!
//! ## Trust model
//!
//! The caller supplies the trust roots out of band: the expected faithful
//! note-root anchor (the externally-trusted start), the enrolled committee
//! (ed25519 roster, index-aligned enrolled ML-DSA-65 roster, threshold), and
//! the expected head coordinates. The store's self-carried anchor is EVIDENCE
//! that must equal the supplied anchor; every history record is authenticated
//! under the enrolled-roster hybrid quorum (Ed25519 AND enrolled-pinned
//! ML-DSA — a classical-only quorum can never admit), and the replayed head
//! must equal the supplied expectation. Fail-closed throughout. The replay
//! itself is [`crate::faithful_note_root_history::audit_faithful_note_root_history_in`],
//! helm-codex task/4268 DATA f9fd27 — the serial boot-replay gate ported onto
//! the caller's read transaction, with the anchor pinned from outside.

use std::io;
use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use redb::{ReadOnlyDatabase, ReadTransaction, ReadableTableMetadata, StorageBackend};

use dregg_federation::frost::MlDsaPublicKey;
use dregg_types::PublicKey;

use crate::faithful_note_root_history::{
    FaithfulNoteRootAnchorV1, FaithfulNoteRootExpectationV1, FaithfulNoteRootHistoryError,
    FaithfulNoteRootHistoryV1, HeadSealV1, audit_faithful_note_root_history_in,
};
use crate::{Result as StoreResult, StoreError, tables};

// ---- redb 2.6.3 v2 super-header layout (tree_store/page_store/header.rs) ----
// Re-derived here because upstream marks every constant `pub(super)`. The
// pre-flight must answer "would `Database::open` have written?" WITHOUT opening
// — and must name the refusal, which `ReadOnlyDatabase`'s single `Corrupted`
// arm cannot.
const MAGIC_NUMBER: [u8; 9] = [b'r', b'e', b'd', b'b', 0x1A, 0x0A, 0xA9, 0x0D, 0x0A];
const GOD_BYTE_OFFSET: usize = MAGIC_NUMBER.len();
const PRIMARY_BIT: u8 = 1;
const RECOVERY_REQUIRED: u8 = 2;
const PAGE_SIZE_OFFSET: usize = GOD_BYTE_OFFSET + 1 + 2; // god byte + padding
const REGION_HEADER_PAGES_OFFSET: usize = PAGE_SIZE_OFFSET + 4;
const REGION_MAX_DATA_PAGES_OFFSET: usize = REGION_HEADER_PAGES_OFFSET + 4;
const NUM_FULL_REGIONS_OFFSET: usize = REGION_MAX_DATA_PAGES_OFFSET + 4;
const TRAILING_REGION_DATA_PAGES_OFFSET: usize = NUM_FULL_REGIONS_OFFSET + 4;
const TRANSACTION_0_OFFSET: usize = 64;
const TRANSACTION_SLOT_BYTES: usize = 128;
const SUPER_HEADER_BYTES: usize = TRANSACTION_0_OFFSET + 2 * TRANSACTION_SLOT_BYTES; // 320
const REDB_PAGE_SIZE: u32 = 4096;
const FILE_FORMAT_VERSION2: u8 = 2;

/// Why a copied store was refused. Every arm is a named, distinct refusal —
/// a copy never fails "generically".
#[derive(Debug)]
pub enum CopiedStoreAdmissionError {
    /// The file could not be opened or read at all.
    Io(io::Error),
    /// The file is not a redb store image: too short for a super-header, or the
    /// magic number does not match. Covers "the copy is of the wrong file" and
    /// "the path is empty" — a reader never creates a missing file.
    Layout(&'static str),
    /// The redb v2 header parsed but carries values this reader does not admit:
    /// a non-4096 page size, an unknown or v3 commit-slot format version (a v3
    /// image would take the repair path), or an out-of-bounds region geometry.
    Header(&'static str),
    /// The copy would require repair — `Database::open` would have WRITTEN a
    /// recovery header. Either `RECOVERY_REQUIRED` is set (copied mid-commit or
    /// from a killed node) or the stored layout length differs from the file
    /// length (truncated/extended copy). Refused, never repaired.
    Dirty(&'static str),
    /// Defensive fail-closed: the read-only backend observed a `write` or
    /// `set_len` attempt during open. A clean v2 image triggers none; an
    /// attempt means the pre-flight has a hole, and refusing is the only honest
    /// answer.
    WriteAttempted,
    /// redb itself refused the image after pre-flight passed (e.g. a corrupted
    /// commit slot on a nominally clean file). Still read-only: the backend
    /// refused every write, so the refusal cost nothing.
    Database(String),
    /// A store-level integrity/authentication refusal during admission. The
    /// replay port's `FaithfulNoteRootHistoryError` arms surface through here
    /// as `StoreError::Integrity` with the variant name in the message.
    Store(StoreError),
}

impl std::fmt::Display for CopiedStoreAdmissionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "copied store unreadable: {e}"),
            Self::Layout(what) => write!(f, "copied store is not a redb image: {what}"),
            Self::Header(what) => write!(f, "copied store header refused: {what}"),
            Self::Dirty(what) => write!(
                f,
                "copied store would need repair ({what}); refusing rather than mutating it"
            ),
            Self::WriteAttempted => write!(
                f,
                "copied-store open attempted a write; the read-only contract was violated"
            ),
            Self::Database(msg) => write!(f, "copied store refused by redb: {msg}"),
            Self::Store(e) => write!(f, "copied store admission refused: {e}"),
        }
    }
}

impl std::error::Error for CopiedStoreAdmissionError {}

impl From<StoreError> for CopiedStoreAdmissionError {
    fn from(e: StoreError) -> Self {
        Self::Store(e)
    }
}

/// A `redb::StorageBackend` over an `O_RDONLY` file whose write paths fail
/// closed. `sync_data` is a no-op (nothing of ours is ever buffered); `len`
/// and `read` delegate to [`redb::FileBackend`], which also holds the
/// exclusive `flock` on the copy for the handle's life — nothing else can
/// RW-open this file while it is under audit. Every refused mutation is
/// counted so a holder can prove the refusal path existed and stayed cold.
#[derive(Debug)]
struct ReadOnlyBackend {
    inner: redb::backends::FileBackend,
    refused_writes: Arc<AtomicU64>,
}

impl ReadOnlyBackend {
    fn refused(&self) -> io::Error {
        self.refused_writes.fetch_add(1, Ordering::Relaxed);
        io::Error::new(
            io::ErrorKind::PermissionDenied,
            "copied-store reader is read-only",
        )
    }
}

impl StorageBackend for ReadOnlyBackend {
    fn len(&self) -> io::Result<u64> {
        self.inner.len()
    }

    fn read(&self, offset: u64, len: usize) -> io::Result<Vec<u8>> {
        self.inner.read(offset, len)
    }

    fn set_len(&self, _len: u64) -> io::Result<()> {
        Err(self.refused())
    }

    fn sync_data(&self, _eventual: bool) -> io::Result<()> {
        Ok(())
    }

    fn write(&self, _offset: u64, _data: &[u8]) -> io::Result<()> {
        Err(self.refused())
    }
}

/// Acquire the copy `O_RDONLY|O_NONBLOCK`. A FIFO (or any other special file)
/// with no writer would otherwise block `File::open` forever, before any
/// refusal could be named. The flag is a no-op once the fd is proven a regular
/// file, so it is handed to `FileBackend` unchanged.
fn open_readonly_nonblocking(path: &Path) -> io::Result<std::fs::File> {
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    // Solaris/illumos spell O_NONBLOCK as 0x80 (0x4 is O_NDELAY there) — rather
    // than carry a wrong value, those targets take the plain blocking open.
    #[cfg(all(unix, not(any(target_os = "solaris", target_os = "illumos"))))]
    {
        use std::os::unix::fs::OpenOptionsExt;
        // std exposes no named O_NONBLOCK; Linux/Android and the BSDs spell it
        // differently. This fleet is Linux — other values are carried, not
        // exercised here.
        const O_NONBLOCK: i32 = if cfg!(any(
            target_os = "macos",
            target_os = "ios",
            target_os = "freebsd",
            target_os = "dragonfly",
            target_os = "netbsd",
            target_os = "openbsd",
        )) {
            0x4
        } else {
            0o4000 // Linux, Android and other linux-ABI unixes
        };
        options.custom_flags(O_NONBLOCK);
    }
    options.open(path)
}

fn read_super_header(file: &std::fs::File, file_len: u64) -> io::Result<[u8; SUPER_HEADER_BYTES]> {
    let mut header = [0u8; SUPER_HEADER_BYTES];
    if file_len > 0 {
        let take = usize::try_from(file_len)
            .unwrap_or(SUPER_HEADER_BYTES)
            .min(SUPER_HEADER_BYTES);
        read_exact_at(file, &mut header[..take], 0)?;
    }
    Ok(header)
}

#[cfg(unix)]
fn read_exact_at(file: &std::fs::File, buf: &mut [u8], offset: u64) -> io::Result<()> {
    use std::os::unix::fs::FileExt;
    file.read_exact_at(buf, offset)
}

/// Minimal portable fallback for non-unix targets: serialize seek+read so
/// concurrent pre-flight reads cannot interleave a seek. Unused on this
/// fleet's targets.
#[cfg(not(unix))]
fn read_exact_at(file: &std::fs::File, buf: &mut [u8], offset: u64) -> io::Result<()> {
    use std::io::{Read, Seek, SeekFrom};
    use std::sync::Mutex;
    static LOCK: Mutex<()> = Mutex::new(());
    let _guard = LOCK.lock().expect("read lock");
    let mut file = file;
    file.seek(SeekFrom::Start(offset))?;
    file.read_exact(buf)
}

/// Read and admit the 320-byte super-header, answering the only question that
/// matters: *would `Database::open` have written to this file?* Anything where
/// the answer is yes (or where we cannot prove no) refuses here with a named
/// arm — `ReadOnlyDatabase` then re-derives the same refusals internally.
fn preflight_super_header(
    bytes: &[u8; SUPER_HEADER_BYTES],
    file_len: u64,
) -> Result<(), CopiedStoreAdmissionError> {
    if file_len < SUPER_HEADER_BYTES as u64 {
        return Err(CopiedStoreAdmissionError::Layout(
            "shorter than a super-header",
        ));
    }
    if bytes[..MAGIC_NUMBER.len()] != MAGIC_NUMBER {
        return Err(CopiedStoreAdmissionError::Layout("magic number mismatch"));
    }
    let god = bytes[GOD_BYTE_OFFSET];
    if god & RECOVERY_REQUIRED != 0 {
        return Err(CopiedStoreAdmissionError::Dirty(
            "recovery-required bit set (mid-commit or killed source)",
        ));
    }
    let page_size = u32::from_le_bytes(
        bytes[PAGE_SIZE_OFFSET..PAGE_SIZE_OFFSET + 4]
            .try_into()
            .expect("fixed field"),
    );
    if page_size != REDB_PAGE_SIZE {
        return Err(CopiedStoreAdmissionError::Header("non-default page size"));
    }
    let primary_slot = usize::from(god & PRIMARY_BIT != 0);
    let version = bytes[TRANSACTION_0_OFFSET + primary_slot * TRANSACTION_SLOT_BYTES];
    if version != FILE_FORMAT_VERSION2 {
        return Err(CopiedStoreAdmissionError::Header(
            "commit slot is not file-format v2 (a v3 image would take the repair path)",
        ));
    }
    let u32_at = |offset: usize| -> u32 {
        u32::from_le_bytes(bytes[offset..offset + 4].try_into().expect("fixed field"))
    };
    let region_header_pages = u64::from(u32_at(REGION_HEADER_PAGES_OFFSET));
    let region_max_data_pages = u64::from(u32_at(REGION_MAX_DATA_PAGES_OFFSET));
    let num_full_regions = u64::from(u32_at(NUM_FULL_REGIONS_OFFSET));
    let trailing_data_pages = u64::from(u32_at(TRAILING_REGION_DATA_PAGES_OFFSET));
    if region_max_data_pages == 0 {
        return Err(CopiedStoreAdmissionError::Header("zero-capacity region"));
    }
    let ps = u64::from(page_size);
    // DatabaseLayout::len() = super-header page + full regions + optional
    // trailing partial region, where each region is (header_pages + data_pages)
    // pages.
    let full_region_bytes = region_header_pages
        .checked_add(region_max_data_pages)
        .and_then(|pages| pages.checked_mul(ps))
        .ok_or(CopiedStoreAdmissionError::Header("region geometry overflow"))?;
    let trailing_region_bytes = if trailing_data_pages > 0 {
        region_header_pages
            .checked_add(trailing_data_pages)
            .and_then(|pages| pages.checked_mul(ps))
            .ok_or(CopiedStoreAdmissionError::Header("region geometry overflow"))?
    } else {
        0
    };
    let expected = ps
        .checked_add(
            num_full_regions
                .checked_mul(full_region_bytes)
                .ok_or(CopiedStoreAdmissionError::Header("region geometry overflow"))?,
        )
        .and_then(|len| len.checked_add(trailing_region_bytes))
        .ok_or(CopiedStoreAdmissionError::Header("layout length overflow"))?;
    if expected != file_len {
        return Err(CopiedStoreAdmissionError::Dirty(
            "stored layout length differs from file length (truncated or extended copy)",
        ));
    }
    Ok(())
}

/// A read-only, non-repairing, single-transaction view over a byte-copy of a
/// `dregg.redb` store. See the module docs for the full contract.
pub struct CopiedStoreReader {
    /// Kept only to own the backend and produce `txn`; writes through it are
    /// structurally impossible — `ReadOnlyDatabase` has no `begin_write`, and
    /// the backend would refuse regardless.
    db: ReadOnlyDatabase,
    /// The ONE read transaction this handle lives inside. Taken at open so a
    /// caller can never observe the copy under two different snapshots.
    txn: ReadTransaction,
    /// Total `write`/`set_len` calls redb attempted and this backend refused
    /// since open (diagnostic; expected to stay 0 — the read-only
    /// `TransactionalMemory` never even attempts its drop-time flush).
    refused_writes: Arc<AtomicU64>,
}

impl std::fmt::Debug for CopiedStoreReader {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CopiedStoreReader")
            .field("refused_writes", &self.refused_writes.load(Ordering::Relaxed))
            .finish_non_exhaustive()
    }
}

impl CopiedStoreReader {
    /// Open a copied store read-only. Never creates, never repairs, never
    /// mutates: the fd is `O_RDONLY`, and every write the library attempts is
    /// refused. A file requiring repair is refused as
    /// [`CopiedStoreAdmissionError::Dirty`].
    pub fn open(path: &Path) -> Result<Self, CopiedStoreAdmissionError> {
        let file = open_readonly_nonblocking(path).map_err(CopiedStoreAdmissionError::Io)?;
        // Regularity is decided from the OPEN fd (fstat) — a path stat would
        // TOCTOU between check and open. A FIFO, socket, or directory never
        // reaches header I/O.
        let metadata = file.metadata().map_err(CopiedStoreAdmissionError::Io)?;
        if !metadata.file_type().is_file() {
            return Err(CopiedStoreAdmissionError::Layout("not a regular file"));
        }
        let file_len = metadata.len();
        let header = read_super_header(&file, file_len).map_err(CopiedStoreAdmissionError::Io)?;
        preflight_super_header(&header, file_len)?;

        let refused_writes = Arc::new(AtomicU64::new(0));
        let backend = ReadOnlyBackend {
            inner: redb::backends::FileBackend::new(file)
                .map_err(|e| CopiedStoreAdmissionError::Database(e.to_string()))?,
            refused_writes: refused_writes.clone(),
        };
        let db = match ReadOnlyDatabase::open_with_backend(backend) {
            Ok(db) => db,
            Err(e) => {
                // A write refused during open IS the diagnosis — name it instead
                // of surfacing a bare backend error that hides the attempt count.
                if refused_writes.load(Ordering::Relaxed) != 0 {
                    return Err(CopiedStoreAdmissionError::WriteAttempted);
                }
                return Err(CopiedStoreAdmissionError::Database(e.to_string()));
            }
        };
        if refused_writes.load(Ordering::Relaxed) != 0 {
            return Err(CopiedStoreAdmissionError::WriteAttempted);
        }
        let txn = db
            .begin_read()
            .map_err(|e| CopiedStoreAdmissionError::Database(e.to_string()))?;
        Ok(Self {
            db,
            txn,
            refused_writes,
        })
    }

    /// Refused write attempts observed so far (diagnostic; stays 0 on a clean
    /// open — the read-only `TransactionalMemory` never attempts a write, so a
    /// nonzero count means something reached for a mutation anyway).
    pub fn refused_write_attempts(&self) -> u64 {
        self.refused_writes.load(Ordering::Relaxed)
    }

    /// Read the store-carried faithful note-root anchor — EVIDENCE, not trust.
    /// The caller compares it to the independently supplied expected anchor;
    /// [`Self::admit_faithful_note_root_history_hybrid`] performs that pin
    /// internally as well.
    ///
    /// `None` means the copy carries no v1 segment. A half-installed
    /// anchor/head or a record-count disagreement is an integrity error, never
    /// an empty legacy store.
    pub fn installed_faithful_note_root_anchor(
        &self,
    ) -> StoreResult<Option<FaithfulNoteRootAnchorV1>> {
        let table = self.txn.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        let metadata = self.txn.open_table(tables::METADATA_BYTES)?;
        let anchor = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
            .map(|guard| guard.value().to_vec());
        let seal = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
            .map(|guard| guard.value().to_vec());
        match (anchor, seal) {
            (None, None) if table.is_empty()? => Ok(None),
            (Some(anchor), Some(seal)) => {
                let anchor = FaithfulNoteRootAnchorV1::from_bytes(&anchor).map_err(integrity)?;
                let seal = HeadSealV1::from_bytes(&seal).map_err(integrity)?;
                if table.len()? != seal.records {
                    return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                        "persisted record count",
                    )));
                }
                Ok(Some(anchor))
            }
            _ => Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "partial anchor/head",
            ))),
        }
    }

    /// Exact externally-checkable seal coordinates of the copy's sealed head —
    /// the same shape [`PersistentStore::faithful_note_root_expectation`]
    /// reports on the authoritative store, read here under the single
    /// transaction. This is what the copy CLAIMS; admission still requires the
    /// caller to supply the independently trusted expectation.
    pub fn faithful_note_root_expectation(
        &self,
    ) -> StoreResult<Option<FaithfulNoteRootExpectationV1>> {
        let table = self.txn.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)?;
        let metadata = self.txn.open_table(tables::METADATA_BYTES)?;
        let anchor = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR)?
            .map(|guard| guard.value().to_vec());
        let seal = metadata
            .get(tables::META_FAITHFUL_NOTE_ROOT_HEAD)?
            .map(|guard| guard.value().to_vec());
        match (anchor, seal) {
            (None, None) if table.is_empty()? => Ok(None),
            (Some(anchor), Some(seal)) => {
                // Intact presence is not evidence: the stored anchor bytes must
                // decode through the same gate `installed_faithful_note_root_anchor`
                // and the admission replay apply, or this surface reports a valid
                // expectation over a malformed/foreign anchor.
                FaithfulNoteRootAnchorV1::from_bytes(&anchor).map_err(integrity)?;
                let seal = HeadSealV1::from_bytes(&seal).map_err(integrity)?;
                if table.len()? != seal.records {
                    return Err(integrity(FaithfulNoteRootHistoryError::SnapshotMismatch(
                        "persisted record count",
                    )));
                }
                Ok(Some(FaithfulNoteRootExpectationV1 {
                    records: seal.records,
                    height: seal.head.height,
                    note_count: seal.head.note_count,
                    root: seal.head.root,
                }))
            }
            _ => Err(integrity(FaithfulNoteRootHistoryError::Malformed(
                "partial anchor/head",
            ))),
        }
    }

    /// Admit the copy's complete faithful note-root history under an
    /// INDEPENDENT trust anchor, all inside this handle's single read
    /// transaction:
    ///
    /// 1. The copy's installed anchor must equal `expected_anchor` — the store
    ///    cannot choose its own trust root.
    /// 2. Every record in `FAITHFUL_NOTE_ROOT_HISTORY` is replayed in key order
    ///    through the same structural gate as the authoritative boot replay AND
    ///    authenticated under the enrolled-roster hybrid quorum
    ///    (`verify_hybrid_quorum_sigs`: Ed25519 AND enrolled-pinned ML-DSA-65).
    ///    A classical-only quorum — an envelope whose `pq_signature` or
    ///    `ml_dsa_pubkey` is absent or wrong — refuses the whole admission;
    ///    there is no ed25519-only downgrade anywhere in this reader.
    /// 3. The replayed head must equal `expected_head` on all four coordinates
    ///    (records, height, note_count, root).
    ///
    /// The ML-DSA half of the quorum runs through `dregg-pq`: the embedding
    /// process must have installed the verified PQ cores (as node startup does)
    /// or verification aborts the process — an offline tool must install them
    /// the same way before calling this.
    pub fn admit_faithful_note_root_history_hybrid(
        &self,
        expected_anchor: &FaithfulNoteRootAnchorV1,
        committee: &[PublicKey],
        ml_dsa_committee: &[MlDsaPublicKey],
        threshold: usize,
        expected_head: FaithfulNoteRootExpectationV1,
    ) -> Result<FaithfulNoteRootHistoryV1, CopiedStoreAdmissionError> {
        audit_faithful_note_root_history_in(
            &self.txn,
            expected_anchor,
            committee,
            ml_dsa_committee,
            threshold,
            expected_head,
        )
        .map_err(CopiedStoreAdmissionError::Store)
    }

    /// Close the handle. `ReadTransaction::close` fails if any table or
    /// iterator obtained through this handle is still live — the runtime half
    /// of "the transaction cannot outlive the handle" (the other half is that
    /// this API never hands one out owned). Returns the total number of write
    /// attempts the read-only backend refused over the handle's life.
    pub fn close(self) -> Result<u64, CopiedStoreAdmissionError> {
        let Self {
            db,
            txn,
            refused_writes,
        } = self;
        txn.close()
            .map_err(|e| CopiedStoreAdmissionError::Database(e.to_string()))?;
        drop(db);
        Ok(refused_writes.load(Ordering::Relaxed))
    }
}

fn integrity(error: FaithfulNoteRootHistoryError) -> StoreError {
    StoreError::Integrity(error.to_string())
}

#[cfg(test)]
mod tests {
    //! RED-first contract for the copied-store admission reader (task/4268).
    //! Every test asserts both the refusal/admission outcome AND that the copy's
    //! bytes are untouched — a reader that mutates the evidence is worse than
    //! none.

    use super::*;
    use crate::PersistentStore;
    use crate::faithful_note_root_history::{
        CanonicalFaithfulRoot, FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES, FaithfulNoteRootEnvelopeV1,
        FaithfulNoteRootRecordV1, plan_faithful_note_root_transition_v1,
    };
    use dregg_federation::frost::MlDsaSigningKey;
    use dregg_types::{HybridQuorumSig, SigningKey};

    struct HybridSigner {
        ed: SigningKey,
        ed_pk: PublicKey,
        pq_pk: MlDsaPublicKey,
        pq: MlDsaSigningKey,
    }

    impl HybridSigner {
        fn new(seed: u8) -> Self {
            // ML-DSA-65 keygen goes through `dregg-pq`, which aborts the process
            // with no verified core installed — the lib-test binary installs it
            // at start; keep the defensive install for the fixture itself.
            dregg_pq_testkit::install_or_panic();
            let bytes = [seed; 32];
            let ed = SigningKey::from_bytes(&bytes);
            let ed_pk = ed.public_key();
            let (pq_pk, pq) = MlDsaSigningKey::from_seed(&bytes);
            Self {
                ed,
                ed_pk,
                pq_pk,
                pq,
            }
        }

        fn hybrid_sig(&self, record: &FaithfulNoteRootRecordV1) -> HybridQuorumSig {
            let message = record.signing_message();
            HybridQuorumSig {
                pubkey: self.ed_pk,
                signature: dregg_types::sign(&self.ed, &message),
                ml_dsa_pubkey: self.pq_pk.0.to_vec(),
                pq_signature: self.pq.sign(&message).expect("ML-DSA signs"),
            }
        }
    }

    fn tag(byte: u8) -> [u8; 32] {
        let mut out = [0u8; 32];
        out[0] = byte;
        out
    }

    struct Fixture {
        anchor: FaithfulNoteRootAnchorV1,
        committee: Vec<PublicKey>,
        ml_dsa_committee: Vec<MlDsaPublicKey>,
        threshold: usize,
        expected_head: FaithfulNoteRootExpectationV1,
        record_height: u64,
        ed_only_envelope: FaithfulNoteRootEnvelopeV1,
    }

    /// Build a store at `path` carrying one genuinely hybrid-signed faithful
    /// history record, then drop it cleanly so the on-disk god byte is clean.
    fn write_history_store(path: &Path) -> Fixture {
        let signer = HybridSigner::new(0x42);
        let committee = vec![signer.ed_pk];
        let ml_dsa_committee = vec![signer.pq_pk.clone()];
        let threshold = 1;

        let tree = crate::Poseidon2NoteTree::with_depth(4);
        let root = CanonicalFaithfulRoot::from_faithful(tree.faithful_root_immutable());
        let anchor = FaithfulNoteRootAnchorV1::new(tag(1), tag(2), 7, 40, 0, root).unwrap();

        let store = PersistentStore::open(path).unwrap();
        store.initialize_faithful_note_root_history(&anchor).unwrap();

        let record =
            plan_faithful_note_root_transition_v1(&tree, &anchor, tag(3), &[[0x61; 32]]).unwrap();
        let record_height = record.height;
        let envelope = FaithfulNoteRootEnvelopeV1 {
            record: record.clone(),
            hybrid_quorum: vec![signer.hybrid_sig(&record)],
        };
        store
            .append_faithful_note_root_hybrid(&envelope, &committee, &ml_dsa_committee, threshold)
            .unwrap();

        // The same record authenticated by a CLASSICAL-ONLY quorum: a genuine
        // ed25519 half and no enrolled-pinned ML-DSA half at all.
        let ed_only_envelope = FaithfulNoteRootEnvelopeV1 {
            record,
            hybrid_quorum: vec![HybridQuorumSig {
                pubkey: signer.ed_pk,
                signature: dregg_types::sign(&signer.ed, &envelope.record.signing_message()),
                ml_dsa_pubkey: Vec::new(),
                pq_signature: Vec::new(),
            }],
        };
        let expected_head = store.faithful_note_root_expectation().unwrap().unwrap();
        drop(store);
        Fixture {
            anchor,
            committee,
            ml_dsa_committee,
            threshold,
            expected_head,
            record_height,
            ed_only_envelope,
        }
    }

    fn file_bytes(path: &Path) -> Vec<u8> {
        std::fs::read(path).expect("copied store bytes")
    }

    #[test]
    fn clean_copy_admits_under_external_anchor_and_never_mutates() {
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let fixture = write_history_store(&live);
        std::fs::copy(&live, &copy).unwrap();
        let before = file_bytes(&copy);

        let reader = CopiedStoreReader::open(&copy).expect("clean v2 copy opens");
        assert_eq!(reader.refused_write_attempts(), 0);

        // The installed anchor is evidence the holder reads back.
        assert_eq!(
            reader.installed_faithful_note_root_anchor().unwrap(),
            Some(fixture.anchor.clone())
        );
        assert_eq!(
            reader.faithful_note_root_expectation().unwrap(),
            Some(fixture.expected_head)
        );

        let history = reader
            .admit_faithful_note_root_history_hybrid(
                &fixture.anchor,
                &fixture.committee,
                &fixture.ml_dsa_committee,
                fixture.threshold,
                fixture.expected_head,
            )
            .expect("a genuine hybrid history admits under the external anchor");
        assert_eq!(history.envelopes().len(), 1);
        assert_eq!(history.head().height, fixture.expected_head.height);

        let refused = reader.close().expect("no table or txn escaped the handle");
        let _ = refused;
        assert_eq!(
            file_bytes(&copy),
            before,
            "open + admit + close must leave the copy byte-identical"
        );
    }

    #[test]
    fn wrong_external_anchor_is_refused() {
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let fixture = write_history_store(&live);
        std::fs::copy(&live, &copy).unwrap();
        let before = file_bytes(&copy);
        let reader = CopiedStoreReader::open(&copy).unwrap();

        // Same shape, different session: not this deployment's trust root.
        let foreign_anchor = FaithfulNoteRootAnchorV1::new(
            tag(9),
            fixture.anchor.federation_id,
            fixture.anchor.committee_epoch,
            fixture.anchor.height,
            fixture.anchor.note_count,
            fixture.anchor.root,
        )
        .unwrap();
        let err = reader
            .admit_faithful_note_root_history_hybrid(
                &foreign_anchor,
                &fixture.committee,
                &fixture.ml_dsa_committee,
                fixture.threshold,
                fixture.expected_head,
            )
            .unwrap_err();
        assert!(
            matches!(err, CopiedStoreAdmissionError::Store(StoreError::Integrity(ref m)) if m.contains("anchor")),
            "a self-carried anchor must not substitute for the external one: {err}"
        );
        assert_eq!(file_bytes(&copy), before);
    }

    #[test]
    fn wrong_expected_head_is_refused() {
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let fixture = write_history_store(&live);
        std::fs::copy(&live, &copy).unwrap();
        let before = file_bytes(&copy);
        let reader = CopiedStoreReader::open(&copy).unwrap();

        let mut wrong = fixture.expected_head;
        wrong.height += 1;
        let err = reader
            .admit_faithful_note_root_history_hybrid(
                &fixture.anchor,
                &fixture.committee,
                &fixture.ml_dsa_committee,
                fixture.threshold,
                wrong,
            )
            .unwrap_err();
        assert!(
            matches!(err, CopiedStoreAdmissionError::Store(StoreError::Integrity(_))),
            "a head the external trust anchor did not predict must refuse: {err}"
        );
        assert_eq!(file_bytes(&copy), before);
    }

    #[test]
    fn ed25519_only_quorum_never_admits() {
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let fixture = write_history_store(&live);

        // Rewrite the one stored row with a CLASSICAL-ONLY envelope: genuine
        // ed25519 signature, both ML-DSA halves empty. The head seal is keyed to
        // the record — identical — so the store still LOOKS sealed and complete;
        // only the hybrid quorum leg is missing.
        {
            let store = PersistentStore::open(&live).unwrap();
            let write = store.db.begin_write().unwrap();
            {
                let mut table = write
                    .open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY)
                    .unwrap();
                table
                    .insert(
                        fixture.record_height,
                        fixture.ed_only_envelope.to_bytes().unwrap().as_slice(),
                    )
                    .unwrap();
            }
            write.commit().unwrap();
        }
        std::fs::copy(&live, &copy).unwrap();
        let before = file_bytes(&copy);
        let reader = CopiedStoreReader::open(&copy).unwrap();

        let err = reader
            .admit_faithful_note_root_history_hybrid(
                &fixture.anchor,
                &fixture.committee,
                &fixture.ml_dsa_committee,
                fixture.threshold,
                fixture.expected_head,
            )
            .unwrap_err();
        assert!(
            matches!(err, CopiedStoreAdmissionError::Store(StoreError::Integrity(ref m)) if m.contains("authentication")),
            "an ed25519-only quorum must fail closed, not downgrade: {err}"
        );
        assert_eq!(file_bytes(&copy), before);

        // And a caller that forgot the enrolled ML-DSA roster at all is refused
        // before any row is read — never an implicit classical admission.
        let err = reader
            .admit_faithful_note_root_history_hybrid(
                &fixture.anchor,
                &fixture.committee,
                &[],
                fixture.threshold,
                fixture.expected_head,
            )
            .unwrap_err();
        assert!(
            matches!(err, CopiedStoreAdmissionError::Store(StoreError::Integrity(_))),
            "an unenrolled roster cannot judge a copied store: {err}"
        );
        assert_eq!(file_bytes(&copy), before);
    }

    #[test]
    fn dirty_copy_is_refused_without_repair() {
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let _fixture = write_history_store(&live);
        std::fs::copy(&live, &copy).unwrap();

        // A mid-commit / killed-source copy carries RECOVERY_REQUIRED in the
        // god byte. `Database::open` would silently repair it — we refuse.
        let mut bytes = file_bytes(&copy);
        bytes[GOD_BYTE_OFFSET] |= RECOVERY_REQUIRED;
        std::fs::write(&copy, &bytes).unwrap();
        let dirty_bytes = file_bytes(&copy);

        let err = CopiedStoreReader::open(&copy).unwrap_err();
        assert!(
            matches!(err, CopiedStoreAdmissionError::Dirty(_)),
            "a recovery-required copy must refuse, not repair: {err}"
        );
        assert_eq!(file_bytes(&copy), dirty_bytes, "refusal must not mutate");
    }

    #[test]
    fn layout_and_header_refusals_are_named() {
        let dir = tempfile::tempdir().unwrap();

        // Missing path: refused, and NOT created (a reader never writes).
        let missing = dir.path().join("absent.redb");
        let err = CopiedStoreReader::open(&missing).unwrap_err();
        assert!(matches!(err, CopiedStoreAdmissionError::Io(_)), "{err}");
        assert!(!missing.exists(), "the reader created the file it read");

        // Empty file.
        let empty = dir.path().join("empty.redb");
        std::fs::write(&empty, b"").unwrap();
        let err = CopiedStoreReader::open(&empty).unwrap_err();
        assert!(matches!(err, CopiedStoreAdmissionError::Layout(_)), "{err}");
        assert_eq!(file_bytes(&empty), b"");

        // Garbage long enough to hold a header, wrong magic.
        let foreign = dir.path().join("foreign.redb");
        let garbage = vec![0xABu8; 8192];
        std::fs::write(&foreign, &garbage).unwrap();
        let err = CopiedStoreReader::open(&foreign).unwrap_err();
        assert!(matches!(err, CopiedStoreAdmissionError::Layout(_)), "{err}");
        assert_eq!(file_bytes(&foreign), garbage);

        let live = dir.path().join("live.redb");
        let _fixture = write_history_store(&live);

        // A v3 commit slot would take the repair path in this redb — refused.
        let v3 = dir.path().join("v3.redb");
        let mut bytes = file_bytes(&live);
        let primary = usize::from(bytes[GOD_BYTE_OFFSET] & PRIMARY_BIT != 0);
        bytes[TRANSACTION_0_OFFSET + primary * TRANSACTION_SLOT_BYTES] = 3;
        std::fs::write(&v3, &bytes).unwrap();
        let err = CopiedStoreReader::open(&v3).unwrap_err();
        assert!(matches!(err, CopiedStoreAdmissionError::Header(_)), "{err}");

        // Truncation and extension both change layout length — Dirty, not repaired.
        let truncated = dir.path().join("truncated.redb");
        std::fs::write(&truncated, &file_bytes(&live)[..file_bytes(&live).len() - 1]).unwrap();
        let err = CopiedStoreReader::open(&truncated).unwrap_err();
        assert!(matches!(err, CopiedStoreAdmissionError::Dirty(_)), "{err}");

        let extended = dir.path().join("extended.redb");
        let mut ext = file_bytes(&live);
        ext.push(0);
        std::fs::write(&extended, &ext).unwrap();
        let err = CopiedStoreReader::open(&extended).unwrap_err();
        assert!(matches!(err, CopiedStoreAdmissionError::Dirty(_)), "{err}");
    }

    #[test]
    fn malformed_anchor_bytes_refuse_the_expectation() {
        // CL99 control: intact PRESENCE of the anchor key cannot stand in for a
        // decodable anchor — `faithful_note_root_expectation` must run the same
        // from_bytes gate as the installed-anchor and admission paths.
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let fixture = write_history_store(&live);

        // Positive control: the valid fixture reports its claimed expectation.
        std::fs::copy(&live, &copy).unwrap();
        let reader = CopiedStoreReader::open(&copy).unwrap();
        assert_eq!(
            reader.faithful_note_root_expectation().unwrap(),
            Some(fixture.expected_head)
        );
        reader.close().unwrap();

        // Negatives: same valid seal, same matching record count — only the
        // anchor bytes are malformed. The writer store is opened once (open
        // does not read the faithful note-root anchor) and each corruption is
        // committed, copied, audited, then restored for the next variant.
        let good_anchor = fixture.anchor.to_bytes();
        let mut short = good_anchor.to_vec();
        short.truncate(FAITHFUL_NOTE_ROOT_ANCHOR_V1_BYTES - 1);
        let mut bad_header = good_anchor;
        bad_header[0] ^= 0xFF; // magic byte
        let mut bad_root = good_anchor;
        bad_root[96..100].copy_from_slice(&u32::MAX.to_le_bytes()); // lane >= BABYBEAR_P
        let store = PersistentStore::open(&live).unwrap();
        for (name, bytes) in [
            ("length", short.as_slice()),
            ("header", bad_header.as_slice()),
            ("root", bad_root.as_slice()),
        ] {
            let write = store.db.begin_write().unwrap();
            {
                let mut metadata = write.open_table(tables::METADATA_BYTES).unwrap();
                metadata
                    .insert(tables::META_FAITHFUL_NOTE_ROOT_ANCHOR, bytes)
                    .unwrap();
            }
            write.commit().unwrap();
            std::fs::copy(&live, &copy).unwrap();
            let before = file_bytes(&copy);

            let reader = CopiedStoreReader::open(&copy).unwrap();
            let err = reader.faithful_note_root_expectation().unwrap_err();
            assert!(
                matches!(err, StoreError::Integrity(_)),
                "{name}: a malformed anchor must refuse the expectation, not claim it: {err}"
            );
            let err = reader.installed_faithful_note_root_anchor().unwrap_err();
            assert!(
                matches!(err, StoreError::Integrity(_)),
                "{name}: a malformed anchor must refuse on the installed path too: {err}"
            );
            let err = reader
                .admit_faithful_note_root_history_hybrid(
                    &fixture.anchor,
                    &fixture.committee,
                    &fixture.ml_dsa_committee,
                    fixture.threshold,
                    fixture.expected_head,
                )
                .unwrap_err();
            assert!(
                matches!(err, CopiedStoreAdmissionError::Store(StoreError::Integrity(_))),
                "{name}: a malformed anchor must refuse admission: {err}"
            );
            assert_eq!(file_bytes(&copy), before, "{name}: refusal must not mutate");
            reader.close().unwrap();
        }
    }

    #[test]
    fn the_single_read_transaction_cannot_outlive_the_handle() {
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let fixture = write_history_store(&live);
        std::fs::copy(&live, &copy).unwrap();

        let reader = CopiedStoreReader::open(&copy).unwrap();
        // Exercise the read surface inside the one transaction.
        let _ = reader.faithful_note_root_expectation().unwrap();
        let _ = reader.installed_faithful_note_root_anchor().unwrap();
        let _ = reader
            .admit_faithful_note_root_history_hybrid(
                &fixture.anchor,
                &fixture.committee,
                &fixture.ml_dsa_committee,
                fixture.threshold,
                fixture.expected_head,
            )
            .unwrap();
        // `close` consumes the handle and calls `ReadTransaction::close`, which
        // fails with ReadTransactionStillInUse if any table, iterator, or
        // transaction derived from this handle is still alive. `Ok` here is the
        // runtime proof that nothing escaped the single-txn scope.
        reader
            .close()
            .expect("the only read transaction must be scoped to the handle");
    }

    /// A backend whose `len()` reports a different file length on every call —
    /// the deterministic stand-in for a file appended mid-open. Its `write`
    /// and `set_len` SUCCEED on a permissive shared counter so the test
    /// measures whether a write was attempted, not whether one failed.
    #[derive(Debug)]
    struct DriftingLenBackend {
        inner: redb::backends::FileBackend,
        base_len: u64,
        len_calls: AtomicU64,
        writes_attempted: Arc<AtomicU64>,
    }

    impl StorageBackend for DriftingLenBackend {
        fn len(&self) -> io::Result<u64> {
            let call = self.len_calls.fetch_add(1, Ordering::Relaxed);
            Ok(if call == 0 {
                self.base_len
            } else {
                self.base_len + 4096
            })
        }

        fn read(&self, offset: u64, len: usize) -> io::Result<Vec<u8>> {
            self.inner.read(offset, len)
        }

        fn set_len(&self, _len: u64) -> io::Result<()> {
            self.writes_attempted.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }

        fn sync_data(&self, _eventual: bool) -> io::Result<()> {
            Ok(())
        }

        fn write(&self, _offset: u64, _data: &[u8]) -> io::Result<()> {
            self.writes_attempted.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
    }

    fn file_backend_reader(
        copy: &Path,
    ) -> (ReadOnlyBackend, Arc<AtomicU64>) {
        let file = open_readonly_nonblocking(copy).unwrap();
        let refused = Arc::new(AtomicU64::new(0));
        let backend = ReadOnlyBackend {
            inner: redb::backends::FileBackend::new(file).unwrap(),
            refused_writes: refused.clone(),
        };
        (backend, refused)
    }

    #[test]
    fn a_read_transaction_can_outlive_the_database_handle() {
        // The vendored seam documents "dropping the handle before this
        // transaction is safe" — the txn owns an Arc of the memory, not a
        // borrow of the db. Prove it at the boundary: reads issued after the
        // handle is gone still resolve, and close succeeds once nothing is
        // outstanding. `CopiedStoreReader`'s lifetime discipline lives above
        // this floor, not under it.
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let _fixture = write_history_store(&live);
        std::fs::copy(&live, &copy).unwrap();
        let before = file_bytes(&copy);

        let (backend, refused) = file_backend_reader(&copy);
        let db = ReadOnlyDatabase::open_with_backend(backend).unwrap();
        let txn = db.begin_read().unwrap();
        drop(db); // the handle is gone; the transaction lives on

        let table = txn.open_table(tables::FAITHFUL_NOTE_ROOT_HISTORY).unwrap();
        assert_eq!(table.len().unwrap(), 1, "reads resolve with the handle dropped");
        drop(table);
        txn.close()
            .expect("the outliving transaction still closes cleanly");
        assert_eq!(refused.load(Ordering::Relaxed), 0);
        assert_eq!(file_bytes(&copy), before);
    }

    #[test]
    fn the_read_only_backend_fails_closed_and_counts_every_attempt() {
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let _fixture = write_history_store(&live);
        std::fs::copy(&live, &copy).unwrap();
        let before = file_bytes(&copy);

        let (backend, refused) = file_backend_reader(&copy);
        assert_eq!(
            backend.write(0, &[0xAA]).unwrap_err().kind(),
            io::ErrorKind::PermissionDenied
        );
        assert_eq!(
            backend.set_len(before.len() as u64).unwrap_err().kind(),
            io::ErrorKind::PermissionDenied
        );
        assert_eq!(refused.load(Ordering::Relaxed), 2);
        // Reads and len still delegate — the backend is read-capable, not dead.
        assert_eq!(backend.len().unwrap(), before.len() as u64);
        assert_eq!(backend.read(0, 4).unwrap(), &before[..4]);
        backend.sync_data(true).unwrap();
        assert_eq!(file_bytes(&copy), before);
    }

    #[test]
    fn length_drift_during_open_is_refused_without_writes() {
        // A backend reporting L then L+4096 passes the layout check against the
        // first measurement, then drifts. The read-only open must refuse with a
        // named diagnostic — and never reach the repair write at all.
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let _fixture = write_history_store(&live);
        std::fs::copy(&live, &copy).unwrap();
        let before = file_bytes(&copy);

        let file = open_readonly_nonblocking(&copy).unwrap();
        let writes = Arc::new(AtomicU64::new(0));
        let backend = DriftingLenBackend {
            inner: redb::backends::FileBackend::new(file).unwrap(),
            base_len: before.len() as u64,
            len_calls: AtomicU64::new(0),
            writes_attempted: writes.clone(),
        };
        let err = ReadOnlyDatabase::open_with_backend(backend)
            .err()
            .expect("a drifting backend must not open");
        let msg = format!("{err}");
        assert!(
            msg.contains("moved") || msg.contains("mismatch") || msg.contains("Corrupted"),
            "length drift must refuse with a diagnostic: {err}"
        );
        assert_eq!(file_bytes(&copy), before, "refusal must not mutate");
        // The drift was caught before any writable branch: a permissive
        // backend records ZERO attempted writes.
        assert_eq!(writes.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn malformed_region_header_is_never_parsed() {
        // Region 0's header begins at file offset 4096 with the format-version
        // byte. Corrupting it used to PANIC inside `RegionHeader::deserialize`
        // via `Allocators::from_bytes`. On a read-only handle allocator state
        // is dead weight — every path that consults it is unreachable — so the
        // parse is skipped and the bytes are never interpreted.
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let fixture = write_history_store(&live);
        std::fs::copy(&live, &copy).unwrap();
        let mut bytes = file_bytes(&copy);
        assert_eq!(bytes[4096], 1, "expected REGION_FORMAT_VERSION at region 0 base");
        bytes[4096] = 0;
        std::fs::write(&copy, &bytes).unwrap();
        let before = file_bytes(&copy);

        let reader = CopiedStoreReader::open(&copy)
            .expect("a corrupted allocator header must not panic or refuse a read-only open");
        // The faithful-history audit is unaffected — allocator metadata is not
        // evidence this reader consumes.
        reader
            .admit_faithful_note_root_history_hybrid(
                &fixture.anchor,
                &fixture.committee,
                &fixture.ml_dsa_committee,
                fixture.threshold,
                fixture.expected_head,
            )
            .unwrap();
        reader.close().unwrap();
        assert_eq!(file_bytes(&copy), before);
    }

    #[cfg(unix)]
    #[test]
    fn a_fifo_is_refused_without_blocking() {
        // A FIFO with no writer hangs a plain File::open forever — the reader
        // would block before reaching any named refusal. O_NONBLOCK open +
        // fd-level regularity check refuses it as a layout error. Completion
        // of this test is the proof it did not hang.
        let dir = tempfile::tempdir().unwrap();
        let fifo = dir.path().join("pipe.redb");
        let status = std::process::Command::new("mkfifo").arg(&fifo).status().unwrap();
        assert!(status.success(), "mkfifo failed");
        let err = CopiedStoreReader::open(&fifo).unwrap_err();
        assert!(
            matches!(err, CopiedStoreAdmissionError::Layout(_)),
            "a FIFO must refuse as a layout error, not block: {err}"
        );
    }

    #[test]
    fn duplicated_pq_enrollment_cannot_share_one_authority() {
        // [E1, E2] with enrolled [P, P] counts two signers whose PQ halves both
        // verify under the SAME enrolled key — at threshold 1 the single
        // envelope would satisfy the verifier, so the roster guard must refuse
        // before any row is read.
        let dir = tempfile::tempdir().unwrap();
        let live = dir.path().join("live.redb");
        let copy = dir.path().join("copy.redb");
        let fixture = write_history_store(&live);
        std::fs::copy(&live, &copy).unwrap();
        let before = file_bytes(&copy);
        let reader = CopiedStoreReader::open(&copy).unwrap();

        let second = HybridSigner::new(0x77);
        let committee = vec![fixture.committee[0], second.ed_pk];
        let dup_pq = vec![
            fixture.ml_dsa_committee[0].clone(),
            fixture.ml_dsa_committee[0].clone(),
        ];
        let err = reader
            .admit_faithful_note_root_history_hybrid(
                &fixture.anchor,
                &committee,
                &dup_pq,
                1,
                fixture.expected_head,
            )
            .unwrap_err();
        assert!(
            matches!(err, CopiedStoreAdmissionError::Store(StoreError::Integrity(_))),
            "a duplicated enrolled PQ key must refuse: {err}"
        );
        // Control: the same roster shape with DISTINCT PQ keys is judged on
        // the quorum, not refused by the guard — threshold 1 with one genuine
        // hybrid signer admits.
        let distinct_pq = vec![fixture.ml_dsa_committee[0].clone(), second.pq_pk.clone()];
        reader
            .admit_faithful_note_root_history_hybrid(
                &fixture.anchor,
                &committee,
                &distinct_pq,
                1,
                fixture.expected_head,
            )
            .expect("a well-formed roster is judged on the quorum, not the guard");
        assert_eq!(file_bytes(&copy), before);
        reader.close().unwrap();
    }
}
