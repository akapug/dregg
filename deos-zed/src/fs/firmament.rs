//! `FirmamentFs` — the firmament-backed [`Fs`](super::Fs) impl. Documented stub.
//!
//! This is the deos-integration payoff: an editor whose every file operation is
//! a capability-checked, receipted operation over sovereign cells — NOT raw
//! `std::fs`. Because the editor only ever speaks the [`Fs`](super::Fs) trait,
//! turning the editor "firmament-backed" is exactly this one impl. No editor or
//! file-tree code changes.
//!
//! # The mapping (path → cell, save → receipted turn)
//!
//! | `Fs` method     | firmament realization                                              |
//! |-----------------|--------------------------------------------------------------------|
//! | `load(path)`    | resolve `path` → a read cap via the directory namespace; read the  |
//! |                 | cell's content substance. A read is authority-checked but does not |
//! |                 | mutate state, so it needs no turn.                                  |
//! | `save(path, c)` | a dregg TURN: exercise a write cap over the file-cell, replacing    |
//! |                 | its content; the turn leaves a verifiable RECEIPT. "Save" becomes  |
//! |                 | an attestable event, not an opaque syscall.                        |
//! | `read_dir(p)`   | `DirectoryCell::list()` — the scoped, capability-secure listing    |
//! |                 | (`rbg/src/directory.rs`). Holding the directory cap IS the authority|
//! |                 | to enumerate it.                                                    |
//! | `metadata(p)`   | `DirectoryCell::get(name)` → resolve to a sturdy ref + cell kind.   |
//!
//! # The path → cap namespace
//!
//! A path like `/proj/src/main.rs` resolves component-by-component through
//! `DirectoryCell`s (`rbg/src/directory.rs`): each component is a `get(name)`
//! that returns a `(cap, version)`, and directories contain directories
//! (recursive scoping). The leaf is the file-cell; its content substance is the
//! editable text. The root `DirectoryCell` cap is the editor's mount point — the
//! editor can only see/edit what that cap reaches, which is the firmament
//! confinement story (one cap across distance: `sel4/dregg-firmament/`).
//!
//! # What `save` actually is
//!
//! `save` is the one mutating op, so it is the one that becomes a turn:
//!
//! 1. Build a turn that spends a write cap on the file-cell and binds the new
//!    content as the cell's next content substance (Σδ=0 over the content-cell:
//!    the old content note is nullified, the new one created).
//! 2. Submit through the executor; obtain the receipt (the proof-carrying token
//!    that this exact edit happened under this exact authority).
//! 3. The receipt is the editor's "saved" acknowledgement — and it is
//!    independently verifiable. A light client can confirm the file now holds
//!    this content WITHOUT trusting the editor.
//!
//! This is why the seam matters: it upgrades "the editor wrote a file" from an
//! unwitnessed side effect to a witnessed, attenuable, receipted turn.
//!
//! # Why this is a stub today
//!
//! Wiring it needs a live executor handle + a mounted root `DirectoryCell` cap,
//! which the editor obtains from its host deos image (starbridge-v2's `World`),
//! not from `deos-zed` standalone. The constructor below takes those handles as
//! opaque parameters precisely so the seam is shaped and ready: when the host is
//! wired, fill the four method bodies against the live executor and this file is
//! the ONLY thing that changes.

use std::path::Path;

use anyhow::{bail, Result};

use super::{DirEntry, Fs, Metadata};

/// The firmament-backed filesystem: file = cell, save = receipted turn.
///
/// Construct with a root directory cap + an executor handle obtained from the
/// host deos image. Today this carries no live handles and every method returns
/// a "not yet wired" error — but it satisfies the [`Fs`](super::Fs) trait, so it
/// is already a drop-in replacement for [`RealFs`](super::RealFs) the moment its
/// bodies are filled.
pub struct FirmamentFs {
    /// Opaque handle to the mount-point directory cap (a `dregg://` sturdy ref
    /// into a `DirectoryCell`). `()` until the host wires it.
    _root_cap: (),
    /// Opaque handle to the live executor that runs the save-turn. `()` until
    /// the host wires it.
    _executor: (),
}

impl FirmamentFs {
    /// Build a firmament fs over a mounted root directory cap.
    ///
    /// The real signature, once the host crate provides the types, is roughly:
    /// `fn new(root_cap: DirectoryCap, executor: ExecutorHandle) -> Self`.
    /// Kept as `()` here so deos-zed has no dependency on the executor crates
    /// while standalone; the host wires the real handles.
    pub fn new() -> Self {
        FirmamentFs {
            _root_cap: (),
            _executor: (),
        }
    }

    fn not_wired<T>(what: &str) -> Result<T> {
        bail!(
            "FirmamentFs::{what} is a documented seam stub: it needs a live \
             executor handle + mounted root DirectoryCell cap from the host deos \
             image. See deos-zed/src/fs/firmament.rs and FIRMAMENT-FS-SEAM.md. \
             Use RealFs until the host wires it."
        )
    }
}

impl Default for FirmamentFs {
    fn default() -> Self {
        Self::new()
    }
}

impl Fs for FirmamentFs {
    fn load(&self, _path: &Path) -> Result<String> {
        // resolve path → read cap via DirectoryCell; read content substance.
        Self::not_wired("load")
    }

    fn save(&self, _path: &Path, _content: &str) -> Result<()> {
        // build + submit the write turn; the receipt is the ack.
        Self::not_wired("save")
    }

    fn read_dir(&self, _path: &Path) -> Result<Vec<DirEntry>> {
        // DirectoryCell::list() over the resolved directory cap.
        Self::not_wired("read_dir")
    }

    fn metadata(&self, _path: &Path) -> Result<Metadata> {
        // DirectoryCell::get(name) → sturdy ref + cell kind.
        Self::not_wired("metadata")
    }

    fn backend_label(&self) -> &'static str {
        "FirmamentFs (cell=file, save=receipted turn) — STUB"
    }
}
