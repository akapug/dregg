//! Archive-first custody of one grain: the exact signed `.spk` bytes plus the
//! digest-chained `/var` checkpoint history, replayed byte-exactly on reopen.
//!
//! The contract shape is cribbed from `dreggcloud-universe-house-custody`: an
//! exclusively locked archive directory of canonical, bounded, single-link
//! record files; every mutation is appended durably (fsync, hard-link
//! publication, directory sync) BEFORE the caller's live state advances; a
//! restart that finds the archive exactly one generation ahead of the
//! operator's retained anchor surfaces a typed recovery obligation instead of
//! guessing; any other divergence, and any tampered/substituted record,
//! refuses open outright.
//!
//! What replay re-verifies (not merely re-reads):
//!
//! * the install record's `.spk` bytes re-parse under [`Spk::parse`] — the real
//!   Ed25519 signature over the archive is checked again on every open, and the
//!   recorded App ID must equal the signing-key-derived one;
//! * every checkpoint's `/var` entries recommit (through the real
//!   `sandstorm-bridge` cell module, the Poseidon2 heap-root scheme) to exactly
//!   the recorded `DataRoot`;
//! * every record's self-digest and the previous-record digest chain hold.

use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Component, Path, PathBuf};

use fs2::FileExt;
use sandstorm_bridge::cell::Umem;
use sandstorm_bridge::grain::GrainSpec;
use sandstorm_bridge::manifest::SpkManifest;
use sandstorm_bridge::spk::Spk;
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub const GRAIN_CUSTODY_PROTOCOL_V1: &str = "sandstorm-serve.grain-custody/v1";
pub const GRAIN_RECORD_PROTOCOL_V1: &str = "sandstorm-serve.grain-record/v1";
/// Bounded checkpoint history — a grain whose serve loop outgrows this must be
/// compacted by an operator (a named residual), not silently truncated.
pub const MAX_RETAINED_RECORDS_V1: usize = 1024;
pub const MAX_GRAIN_CELL_ID_BYTES: usize = 128;
/// One record file's bounded envelope (the `.spk` bytes ride inside the
/// install record; a checkpoint carries the whole `/var` image).
const RECORD_FILE_BYTES_MAX: usize = 16 * 1024 * 1024;
const LOCK_FILENAME: &str = ".grain-custody.lock";

type Digest32 = [u8; 32];

/// The operator-retained anchor: the exact archive head this custody was last
/// settled at. The operator (today: the daemon's supervisor; the named future
/// step: a House schema slot) persists it after every mutation; `open_or_create`
/// compares it against the replayed archive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GrainCustodyAnchorV1 {
    pub generation: u64,
    pub head_record_digest: Digest32,
    /// The committed `/var` heap root at this head (`heap1…`).
    pub data_root: String,
    /// The blake3 digest of the exact installed `.spk` bytes.
    pub spk_digest: Digest32,
}

/// The verified installation the archive custodies: the exact `.spk` bytes plus
/// everything re-derived from them on replay.
#[derive(Clone, Debug)]
pub struct GrainInstallation {
    pub grain_cell_id: String,
    pub owner: String,
    /// The signing-key-derived App ID (Sandstorm base32 of the Ed25519 key).
    pub app_id: String,
    pub spk_digest: Digest32,
    pub manifest: SpkManifest,
    pub spec: GrainSpec,
    /// The exact bytes retained; reopen hands back these bytes byte-for-byte.
    pub spk_bytes: Vec<u8>,
}

/// Why a reopened archive requires typed settlement before serving resumes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GrainRecoveryReasonV1 {
    /// The archive holds exactly one record the operator's anchor never
    /// acknowledged — the process stopped between durable append and anchor
    /// persistence. Acknowledging the exact head candidate recovers.
    RestartedArchiveAheadWithoutAnchor,
    /// A durable append failed ambiguously mid-mutation; the runtime refuses
    /// every further mutation until reopened.
    DurabilityAmbiguous,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GrainCustodyStatusV1 {
    /// No grain installed yet (empty archive).
    Empty,
    Ready {
        anchor: GrainCustodyAnchorV1,
    },
    RecoveryRequired {
        /// The archive base the operator's anchor matches.
        acknowledged_base: Option<GrainCustodyAnchorV1>,
        /// The unacknowledged archive head; `acknowledge_archive_head` with
        /// exactly this candidate settles it.
        candidate: GrainCustodyAnchorV1,
        reason: GrainRecoveryReasonV1,
    },
    Poisoned {
        reason: GrainRecoveryReasonV1,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
enum GrainRecordBodyV1 {
    Install {
        grain_cell_id: String,
        owner: String,
        app_id: String,
        spk_digest: Digest32,
        spk_bytes: Vec<u8>,
        /// The genesis `/var` root (the committed empty heap).
        data_root: String,
    },
    Checkpoint {
        /// The whole `/var` image at this checkpoint (`key -> bytes`, sorted).
        var_entries: Vec<(String, Vec<u8>)>,
        /// The committed heap root the entries must recommit to on replay.
        data_root: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct GrainArchiveRecordV1 {
    protocol: String,
    generation: u64,
    previous_record_digest: Digest32,
    body: GrainRecordBodyV1,
    record_digest: Digest32,
}

enum RuntimeState {
    Ready,
    RecoveryRequired {
        acknowledged_base: Option<GrainCustodyAnchorV1>,
        candidate: GrainCustodyAnchorV1,
        reason: GrainRecoveryReasonV1,
    },
    Poisoned(GrainRecoveryReasonV1),
}

/// Single-writer custody runtime over one locked archive directory.
pub struct GrainCustodyRuntime {
    archive_path: PathBuf,
    records: Vec<GrainArchiveRecordV1>,
    installation: Option<GrainInstallation>,
    head_var: Umem,
    state: RuntimeState,
    _archive_lock: File,
    archive_directory: File,
}

#[derive(Debug, Error)]
pub enum GrainCustodyError {
    #[error(".spk refused: {0}")]
    Spk(String),
    #[error("grain manifest refused: {0}")]
    Manifest(String),
    #[error("grain identity is empty, oversized, or non-canonical")]
    InvalidGrainIdentity,
    #[error("a grain is already installed in this archive")]
    AlreadyInstalled,
    #[error("no grain is installed in this archive")]
    NotInstalled,
    #[error("grain archive reached its bounded record capacity")]
    ArchiveCapacityExceeded,
    #[error("archive-ahead recovery is required before another mutation")]
    RecoveryRequired,
    #[error("acknowledgement does not match the exact archive head candidate")]
    AcknowledgementSubstitution,
    #[error("no unacknowledged archive head awaits settlement")]
    NoRecoveryPending,
    #[error("grain custody runtime is poisoned")]
    Poisoned,
    #[error("operator anchor and grain archive diverged")]
    AnchorArchiveDiverged,
    #[error("grain archive is already exclusively open")]
    ArchiveLocked,
    #[error("grain archive path is a symlink, hardlink, or non-regular object")]
    UnsafeArchivePath,
    #[error("grain archive path changed during checked open")]
    ConcurrentReplacement,
    #[error("grain archive durability is ambiguous: {0}")]
    DurabilityAmbiguous(String),
    #[error("grain archive is malformed: {0}")]
    MalformedArchive(String),
}

impl GrainCustodyRuntime {
    /// Open and deeply replay the archive, comparing it against the operator's
    /// retained `expected_anchor`. Archive exactly one record ahead of the
    /// anchor is surfaced as typed recovery; any other divergence refuses open.
    ///
    /// # Errors
    ///
    /// Refuses unsafe filesystem geometry, lock contention, malformed or
    /// tampered records, a failed `.spk` re-verification, a checkpoint whose
    /// entries do not recommit to its recorded root, and anchor divergence.
    pub fn open_or_create(
        archive_path: impl AsRef<Path>,
        expected_anchor: Option<&GrainCustodyAnchorV1>,
    ) -> Result<Self, GrainCustodyError> {
        let archive_path = archive_path.as_ref().to_path_buf();
        let (archive_lock, archive_directory) = lock_archive_directory(&archive_path)?;
        let (records, installation, head_var) = replay_archive(&archive_path, &archive_directory)?;

        let head = head_anchor(&records);
        let base_anchor = records
            .len()
            .checked_sub(2)
            .and_then(|index| anchor_at(&records, index));

        let state = match (head, expected_anchor) {
            (None, None) => RuntimeState::Ready,
            (Some(head), Some(expected)) if head == *expected => RuntimeState::Ready,
            (Some(head), expected) if base_anchor.as_ref() == expected => {
                RuntimeState::RecoveryRequired {
                    acknowledged_base: base_anchor,
                    candidate: head,
                    reason: GrainRecoveryReasonV1::RestartedArchiveAheadWithoutAnchor,
                }
            }
            _ => return Err(GrainCustodyError::AnchorArchiveDiverged),
        };

        Ok(Self {
            archive_path,
            records,
            installation,
            head_var,
            state,
            _archive_lock: archive_lock,
            archive_directory,
        })
    }

    #[must_use]
    pub fn status(&self) -> GrainCustodyStatusV1 {
        match &self.state {
            RuntimeState::Ready => match head_anchor(&self.records) {
                None => GrainCustodyStatusV1::Empty,
                Some(anchor) => GrainCustodyStatusV1::Ready { anchor },
            },
            RuntimeState::RecoveryRequired {
                acknowledged_base,
                candidate,
                reason,
            } => GrainCustodyStatusV1::RecoveryRequired {
                acknowledged_base: acknowledged_base.clone(),
                candidate: candidate.clone(),
                reason: *reason,
            },
            RuntimeState::Poisoned(reason) => GrainCustodyStatusV1::Poisoned { reason: *reason },
        }
    }

    /// The verified installation, if the archive holds one.
    #[must_use]
    pub fn installation(&self) -> Option<&GrainInstallation> {
        self.installation.as_ref()
    }

    /// The `/var` heap at the archive head, rebuilt from the last checkpoint.
    #[must_use]
    pub fn head_var(&self) -> Umem {
        self.head_var.clone()
    }

    /// Install a signed `.spk` into an empty archive: verify the Ed25519
    /// signature (tamper refuses HERE, before anything is retained), decode
    /// the manifest, derive the `GrainSpec`, and durably append the exact
    /// bytes archive-first. Returns the head anchor the operator must persist.
    ///
    /// # Errors
    ///
    /// Refuses a non-ready or non-empty archive, an invalid or tampered
    /// `.spk`, an undecodable manifest, non-canonical identities, and any
    /// ambiguous durability (which poisons the runtime).
    pub fn install(
        &mut self,
        grain_cell_id: &str,
        owner: &str,
        spk_bytes: &[u8],
    ) -> Result<(GrainInstallation, GrainCustodyAnchorV1), GrainCustodyError> {
        self.require_ready()?;
        if self.installation.is_some() {
            return Err(GrainCustodyError::AlreadyInstalled);
        }
        if !canonical_identity(grain_cell_id) || owner.is_empty() {
            return Err(GrainCustodyError::InvalidGrainIdentity);
        }
        let installation = verify_install(grain_cell_id, owner, spk_bytes)?;
        let genesis_root = Umem::new().commit().0;
        let record = build_record(
            &self.records,
            GrainRecordBodyV1::Install {
                grain_cell_id: installation.grain_cell_id.clone(),
                owner: installation.owner.clone(),
                app_id: installation.app_id.clone(),
                spk_digest: installation.spk_digest,
                spk_bytes: installation.spk_bytes.clone(),
                data_root: genesis_root,
            },
        )?;
        self.append(record)?;
        let anchor = head_anchor(&self.records).ok_or_else(|| {
            GrainCustodyError::MalformedArchive("appended install record vanished".into())
        })?;
        self.installation = Some(installation.clone());
        self.head_var = Umem::new();
        Ok((installation, anchor))
    }

    /// Durably checkpoint the grain's `/var` archive-first. Idempotent: a heap
    /// committing to the current head root appends nothing. Returns the head
    /// anchor the operator must persist.
    ///
    /// # Errors
    ///
    /// Refuses a non-ready or uninstalled archive, bounded capacity, and any
    /// ambiguous durability (which poisons the runtime).
    pub fn checkpoint(&mut self, var: &Umem) -> Result<GrainCustodyAnchorV1, GrainCustodyError> {
        self.require_ready()?;
        if self.installation.is_none() {
            return Err(GrainCustodyError::NotInstalled);
        }
        let data_root = var.commit().0;
        let head = head_anchor(&self.records).ok_or(GrainCustodyError::NotInstalled)?;
        if head.data_root == data_root {
            return Ok(head);
        }
        let var_entries: Vec<(String, Vec<u8>)> = var
            .iter()
            .map(|(key, value)| (key.to_string(), value.to_vec()))
            .collect();
        let record = build_record(
            &self.records,
            GrainRecordBodyV1::Checkpoint {
                var_entries,
                data_root,
            },
        )?;
        self.append(record)?;
        self.head_var = var.clone();
        head_anchor(&self.records).ok_or_else(|| {
            GrainCustodyError::MalformedArchive("appended checkpoint record vanished".into())
        })
    }

    /// Settle an archive-ahead reopen by acknowledging the exact head
    /// candidate the recovery obligation named.
    ///
    /// # Errors
    ///
    /// Refuses when no recovery is pending, when the runtime is poisoned, or
    /// when the acknowledgement is not the exact candidate.
    pub fn acknowledge_archive_head(
        &mut self,
        acknowledged: &GrainCustodyAnchorV1,
    ) -> Result<(), GrainCustodyError> {
        match &self.state {
            RuntimeState::RecoveryRequired { candidate, .. } => {
                if candidate != acknowledged {
                    return Err(GrainCustodyError::AcknowledgementSubstitution);
                }
                self.state = RuntimeState::Ready;
                Ok(())
            }
            RuntimeState::Ready => Err(GrainCustodyError::NoRecoveryPending),
            RuntimeState::Poisoned(_) => Err(GrainCustodyError::Poisoned),
        }
    }

    fn require_ready(&self) -> Result<(), GrainCustodyError> {
        match self.state {
            RuntimeState::Ready => Ok(()),
            RuntimeState::RecoveryRequired { .. } => Err(GrainCustodyError::RecoveryRequired),
            RuntimeState::Poisoned(_) => Err(GrainCustodyError::Poisoned),
        }
    }

    fn append(&mut self, record: GrainArchiveRecordV1) -> Result<(), GrainCustodyError> {
        if let Err(error) = append_record(&self.archive_path, &self.archive_directory, &record) {
            self.state = RuntimeState::Poisoned(GrainRecoveryReasonV1::DurabilityAmbiguous);
            return Err(error);
        }
        self.records.push(record);
        Ok(())
    }
}

/// Signature-verifying install parse: the one place `.spk` bytes become a
/// [`GrainInstallation`], used identically at first install and at replay.
fn verify_install(
    grain_cell_id: &str,
    owner: &str,
    spk_bytes: &[u8],
) -> Result<GrainInstallation, GrainCustodyError> {
    let spk = Spk::parse(spk_bytes).map_err(|error| GrainCustodyError::Spk(error.to_string()))?;
    let manifest = SpkManifest::from_spk(&spk)
        .map_err(|error| GrainCustodyError::Manifest(error.to_string()))?;
    let spec = manifest.grain_spec();
    Ok(GrainInstallation {
        grain_cell_id: grain_cell_id.to_string(),
        owner: owner.to_string(),
        app_id: spk.app_id().0,
        spk_digest: spk_digest(spk_bytes),
        manifest,
        spec,
        spk_bytes: spk_bytes.to_vec(),
    })
}

fn spk_digest(spk_bytes: &[u8]) -> Digest32 {
    let mut hasher = blake3::Hasher::new_derive_key("sandstorm-serve.spk-digest.v1");
    hasher.update(&(spk_bytes.len() as u64).to_le_bytes());
    hasher.update(spk_bytes);
    *hasher.finalize().as_bytes()
}

fn canonical_identity(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= MAX_GRAIN_CELL_ID_BYTES
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b':' | b'.'))
}

fn record_data_root(record: &GrainArchiveRecordV1) -> &str {
    match &record.body {
        GrainRecordBodyV1::Install { data_root, .. }
        | GrainRecordBodyV1::Checkpoint { data_root, .. } => data_root,
    }
}

/// The INSTALL record's `.spk` digest — every anchor carries it, so an anchor
/// at any generation is bound to the exact installed bytes (checkpoints extend
/// the install through the record-digest chain).
fn install_spk_digest(records: &[GrainArchiveRecordV1]) -> Digest32 {
    records
        .first()
        .map_or([0; 32], |record| match &record.body {
            GrainRecordBodyV1::Install { spk_digest, .. } => *spk_digest,
            GrainRecordBodyV1::Checkpoint { .. } => [0; 32],
        })
}

fn anchor_at(records: &[GrainArchiveRecordV1], index: usize) -> Option<GrainCustodyAnchorV1> {
    let record = records.get(index)?;
    Some(GrainCustodyAnchorV1 {
        generation: record.generation,
        head_record_digest: record.record_digest,
        data_root: record_data_root(record).to_string(),
        spk_digest: install_spk_digest(records),
    })
}

fn head_anchor(records: &[GrainArchiveRecordV1]) -> Option<GrainCustodyAnchorV1> {
    records
        .len()
        .checked_sub(1)
        .and_then(|i| anchor_at(records, i))
}

fn build_record(
    records: &[GrainArchiveRecordV1],
    body: GrainRecordBodyV1,
) -> Result<GrainArchiveRecordV1, GrainCustodyError> {
    if records.len() >= MAX_RETAINED_RECORDS_V1 {
        return Err(GrainCustodyError::ArchiveCapacityExceeded);
    }
    let generation = records.last().map_or(1, |record| record.generation + 1);
    let previous_record_digest = records
        .last()
        .map_or([0; 32], |record| record.record_digest);
    let mut record = GrainArchiveRecordV1 {
        protocol: GRAIN_RECORD_PROTOCOL_V1.into(),
        generation,
        previous_record_digest,
        body,
        record_digest: [0; 32],
    };
    record.record_digest = record_digest(&record)?;
    Ok(record)
}

fn record_digest(record: &GrainArchiveRecordV1) -> Result<Digest32, GrainCustodyError> {
    let mut payload = record.clone();
    payload.record_digest = [0; 32];
    let bytes = postcard::to_stdvec(&payload)
        .map_err(|error| GrainCustodyError::MalformedArchive(error.to_string()))?;
    let mut hasher = blake3::Hasher::new_derive_key("sandstorm-serve.grain-record.v1");
    hasher.update(&(bytes.len() as u64).to_le_bytes());
    hasher.update(&bytes);
    Ok(*hasher.finalize().as_bytes())
}

#[allow(clippy::type_complexity)]
fn replay_archive(
    archive_path: &Path,
    archive_directory: &File,
) -> Result<(Vec<GrainArchiveRecordV1>, Option<GrainInstallation>, Umem), GrainCustodyError> {
    require_directory_identity(archive_path, archive_directory)?;
    let mut paths = fs::read_dir(archive_path)
        .map_err(|error| GrainCustodyError::MalformedArchive(error.to_string()))?
        .map(|entry| {
            entry
                .map(|value| value.path())
                .map_err(|error| GrainCustodyError::MalformedArchive(error.to_string()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    paths.retain(|path| path.file_name().and_then(|name| name.to_str()) != Some(LOCK_FILENAME));
    paths.sort();
    if paths.len() > MAX_RETAINED_RECORDS_V1 {
        return Err(GrainCustodyError::ArchiveCapacityExceeded);
    }
    let mut records: Vec<GrainArchiveRecordV1> = Vec::with_capacity(paths.len());
    let mut installation: Option<GrainInstallation> = None;
    let mut head_var = Umem::new();
    for (index, path) in paths.into_iter().enumerate() {
        let generation =
            u64::try_from(index + 1).map_err(|_| GrainCustodyError::ArchiveCapacityExceeded)?;
        if path.file_name().and_then(|name| name.to_str()) != Some(&record_filename(generation)) {
            return Err(GrainCustodyError::DurabilityAmbiguous(format!(
                "unexpected archive entry {}",
                path.display()
            )));
        }
        let bytes = read_bounded_regular_nofollow(&path, RECORD_FILE_BYTES_MAX)?;
        let record: GrainArchiveRecordV1 = postcard::from_bytes(&bytes)
            .map_err(|error| GrainCustodyError::MalformedArchive(error.to_string()))?;
        if record.protocol != GRAIN_RECORD_PROTOCOL_V1
            || record.generation != generation
            || record.record_digest != record_digest(&record)?
        {
            return Err(GrainCustodyError::MalformedArchive(
                "record identity or digest mismatch".into(),
            ));
        }
        let expected_previous = records.last().map_or([0; 32], |value| value.record_digest);
        if record.previous_record_digest != expected_previous {
            return Err(GrainCustodyError::MalformedArchive(
                "record does not extend the exact prior head".into(),
            ));
        }
        match &record.body {
            GrainRecordBodyV1::Install {
                grain_cell_id,
                owner,
                app_id,
                spk_digest: recorded_digest,
                spk_bytes,
                data_root,
            } => {
                if generation != 1 || installation.is_some() {
                    return Err(GrainCustodyError::MalformedArchive(
                        "install record is not the unique first record".into(),
                    ));
                }
                // Re-verify the Ed25519 signature over the exact retained bytes.
                let replayed = verify_install(grain_cell_id, owner, spk_bytes)?;
                if replayed.app_id != *app_id
                    || replayed.spk_digest != *recorded_digest
                    || !canonical_identity(grain_cell_id)
                    || owner.is_empty()
                    || Umem::new().commit().0 != *data_root
                {
                    return Err(GrainCustodyError::MalformedArchive(
                        "install record identity does not match its signed bytes".into(),
                    ));
                }
                installation = Some(replayed);
                head_var = Umem::new();
            }
            GrainRecordBodyV1::Checkpoint {
                var_entries,
                data_root,
            } => {
                if installation.is_none() {
                    return Err(GrainCustodyError::MalformedArchive(
                        "checkpoint precedes the install record".into(),
                    ));
                }
                let mut var = Umem::new();
                for (key, value) in var_entries {
                    var.put(key.clone(), value.clone());
                }
                // Recommit through the real cell heap scheme; a substituted
                // entry or root refuses the whole open.
                if var.commit().0 != *data_root {
                    return Err(GrainCustodyError::MalformedArchive(
                        "checkpoint entries do not recommit to their recorded data_root".into(),
                    ));
                }
                head_var = var;
            }
        }
        records.push(record);
    }
    require_directory_identity(archive_path, archive_directory)?;
    Ok((records, installation, head_var))
}

fn record_filename(generation: u64) -> String {
    format!("{generation:020}.grain")
}

// ---------------------------------------------------------------------------
// Filesystem teeth, cribbed from dreggcloud-universe-house-custody: exclusive
// lock, symlink/hardlink refusal, fsync-then-hardlink publication, identity
// re-checks around every durable operation.
// ---------------------------------------------------------------------------

fn lock_archive_directory(path: &Path) -> Result<(File, File), GrainCustodyError> {
    reject_symlink_components(path)?;
    fs::create_dir_all(path)
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))?;
    reject_symlink_components(path)?;
    let named_directory = fs::symlink_metadata(path)
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))?;
    if !named_directory.is_dir() || named_directory.file_type().is_symlink() {
        return Err(GrainCustodyError::UnsafeArchivePath);
    }
    let directory = open_directory_nofollow(path)?;
    let opened_directory = directory
        .metadata()
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))?;
    if named_directory.dev() != opened_directory.dev()
        || named_directory.ino() != opened_directory.ino()
    {
        return Err(GrainCustodyError::ConcurrentReplacement);
    }
    directory
        .sync_all()
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))?;

    let lock_path = path.join(LOCK_FILENAME);
    match fs::symlink_metadata(&lock_path) {
        Ok(metadata) => check_regular_single_link(&metadata)?,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => {
            return Err(GrainCustodyError::DurabilityAmbiguous(error.to_string()));
        }
    }
    let mut options = OpenOptions::new();
    options
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC);
    let lock = options
        .open(&lock_path)
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))?;
    let opened = lock
        .metadata()
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))?;
    check_regular_single_link(&opened)?;
    FileExt::try_lock_exclusive(&lock).map_err(|error| {
        if error.kind() == std::io::ErrorKind::WouldBlock {
            GrainCustodyError::ArchiveLocked
        } else {
            GrainCustodyError::DurabilityAmbiguous(error.to_string())
        }
    })?;
    let named = fs::symlink_metadata(&lock_path)
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))?;
    check_regular_single_link(&named)?;
    if named.dev() != opened.dev() || named.ino() != opened.ino() {
        return Err(GrainCustodyError::ConcurrentReplacement);
    }
    directory
        .sync_all()
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))?;
    Ok((lock, directory))
}

fn append_record(
    archive_path: &Path,
    archive_directory: &File,
    record: &GrainArchiveRecordV1,
) -> Result<(), GrainCustodyError> {
    require_directory_identity(archive_path, archive_directory)?;
    let bytes = postcard::to_stdvec(record)
        .map_err(|error| GrainCustodyError::MalformedArchive(error.to_string()))?;
    if bytes.len() > RECORD_FILE_BYTES_MAX {
        return Err(GrainCustodyError::MalformedArchive(
            "record exceeds bounded file envelope".into(),
        ));
    }
    let target = archive_path.join(record_filename(record.generation));
    match fs::symlink_metadata(&target) {
        Ok(_) => {
            return Err(GrainCustodyError::MalformedArchive(
                "record generation already exists".into(),
            ));
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => {
            return Err(GrainCustodyError::DurabilityAmbiguous(error.to_string()));
        }
    }
    let temporary = archive_path.join(format!(".pending-{:020}", record.generation));
    let result = (|| {
        let mut options = OpenOptions::new();
        options
            .create_new(true)
            .write(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC);
        let mut file = options.open(&temporary)?;
        let opened_metadata = file.metadata()?;
        check_regular_single_link_io(&opened_metadata)?;
        file.write_all(&bytes)?;
        file.sync_all()?;
        let named_temporary = fs::symlink_metadata(&temporary)?;
        check_regular_single_link_io(&named_temporary)?;
        if named_temporary.dev() != opened_metadata.dev()
            || named_temporary.ino() != opened_metadata.ino()
        {
            return Err(std::io::Error::other(
                "temporary record changed during publication",
            ));
        }
        fs::hard_link(&temporary, &target)?;
        fs::remove_file(&temporary)?;
        let target_metadata = fs::symlink_metadata(&target)?;
        check_regular_single_link_io(&target_metadata)?;
        if target_metadata.dev() != opened_metadata.dev()
            || target_metadata.ino() != opened_metadata.ino()
        {
            return Err(std::io::Error::other(
                "published record is not the fsynced temporary inode",
            ));
        }
        archive_directory.sync_all()
    })();
    if let Err(error) = result {
        return Err(GrainCustodyError::DurabilityAmbiguous(error.to_string()));
    }
    require_directory_identity(archive_path, archive_directory)?;
    Ok(())
}

fn reject_symlink_components(path: &Path) -> Result<(), GrainCustodyError> {
    let mut current = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Prefix(_)
            | Component::RootDir
            | Component::Normal(_)
            | Component::CurDir => current.push(component.as_os_str()),
            Component::ParentDir => return Err(GrainCustodyError::UnsafeArchivePath),
        }
        match fs::symlink_metadata(&current) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(GrainCustodyError::UnsafeArchivePath);
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => break,
            Err(error) => {
                return Err(GrainCustodyError::DurabilityAmbiguous(error.to_string()));
            }
        }
    }
    Ok(())
}

fn open_directory_nofollow(path: &Path) -> Result<File, GrainCustodyError> {
    let mut options = OpenOptions::new();
    options
        .read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC);
    options
        .open(path)
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))
}

fn require_directory_identity(
    path: &Path,
    opened_directory: &File,
) -> Result<(), GrainCustodyError> {
    let named = fs::symlink_metadata(path)
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))?;
    let opened = opened_directory
        .metadata()
        .map_err(|error| GrainCustodyError::DurabilityAmbiguous(error.to_string()))?;
    if !named.is_dir()
        || named.file_type().is_symlink()
        || named.dev() != opened.dev()
        || named.ino() != opened.ino()
    {
        return Err(GrainCustodyError::ConcurrentReplacement);
    }
    Ok(())
}

fn check_regular_single_link(metadata: &fs::Metadata) -> Result<(), GrainCustodyError> {
    if !metadata.is_file() || metadata.file_type().is_symlink() || metadata.nlink() != 1 {
        return Err(GrainCustodyError::UnsafeArchivePath);
    }
    Ok(())
}

fn check_regular_single_link_io(metadata: &fs::Metadata) -> std::io::Result<()> {
    if !metadata.is_file() || metadata.file_type().is_symlink() || metadata.nlink() != 1 {
        return Err(std::io::Error::other(
            "archive entry is not a single-link regular file",
        ));
    }
    Ok(())
}

fn read_bounded_regular_nofollow(
    path: &Path,
    maximum: usize,
) -> Result<Vec<u8>, GrainCustodyError> {
    let named = fs::symlink_metadata(path)
        .map_err(|error| GrainCustodyError::MalformedArchive(error.to_string()))?;
    check_regular_single_link(&named)?;
    if named.len() > maximum as u64 {
        return Err(GrainCustodyError::MalformedArchive(
            "record exceeds bounded file envelope".into(),
        ));
    }
    let mut options = OpenOptions::new();
    options
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC);
    let file = options
        .open(path)
        .map_err(|error| GrainCustodyError::MalformedArchive(error.to_string()))?;
    let opened = file
        .metadata()
        .map_err(|error| GrainCustodyError::MalformedArchive(error.to_string()))?;
    check_regular_single_link(&opened)?;
    if named.dev() != opened.dev() || named.ino() != opened.ino() {
        return Err(GrainCustodyError::ConcurrentReplacement);
    }
    let capacity = usize::try_from(named.len()).map_err(|_| {
        GrainCustodyError::MalformedArchive("record length does not fit usize".into())
    })?;
    let mut bytes = Vec::with_capacity(capacity);
    file.take((maximum as u64).saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|error| GrainCustodyError::MalformedArchive(error.to_string()))?;
    if bytes.len() > maximum {
        return Err(GrainCustodyError::MalformedArchive(
            "record exceeds bounded file envelope".into(),
        ));
    }
    Ok(bytes)
}
