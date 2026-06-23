//! Integration test for the FirmamentFs document-substrate ride: a file is a
//! cell, and a SAVE is a receipted dregg turn.
//!
//! Gated on the `firmament` feature (the whole file compiles away without it, so
//! the default `cargo test` is unaffected). Run with:
//!   cargo test --features firmament --test firmament_fs

#![cfg(feature = "firmament")]

use std::path::{Path, PathBuf};
use std::sync::Arc;

use deos_zed::fs::{Fs, FirmamentFs};

#[test]
fn open_edit_save_reload_is_a_receipted_turn_round_tripping_through_the_ledger() {
    // Drive the editor's exact I/O path (the `Fs` trait) against the firmament
    // backend, but through an `Arc<dyn Fs>` — proving FirmamentFs is a genuine
    // drop-in for RealFs (the same handle EditorPane holds).
    let firm = Arc::new(FirmamentFs::new());

    let path = PathBuf::from("/proj/lib.rs");
    let original = "pub fn answer() -> i32 { 41 }\n";
    let edited = "pub fn answer() -> i32 { 42 }\n";

    // Seed the file as a cell (the read-side fixture: a file on the ledger).
    let file = firm.seed_file(&path, original).expect("seed file cell");

    // The editor opens via the `Fs` trait — content comes FROM THE CELL.
    let fs: Arc<dyn Fs> = firm.clone();
    assert_eq!(fs.load(&path).unwrap(), original, "open reads the cell content");
    assert_eq!(firm.receipt_count(), 0, "a seed is genesis, not a turn");

    // The editor saves via the `Fs` trait — a REAL cap-gated turn.
    fs.save(&path, edited).expect("save commits a turn");
    assert_eq!(firm.receipt_count(), 1, "save produced one receipt");

    let receipt = firm.last_receipt().expect("a receipt was recorded");
    assert_eq!(receipt.agent, firm.editor_id(), "the editor cell is the agent");
    assert_ne!(
        receipt.pre_state_hash, receipt.post_state_hash,
        "the edit landed on-ledger (state moved)"
    );
    assert!(receipt.action_count >= 1);

    // Re-open: the edited content round-trips through the LEDGER, not disk.
    assert_eq!(
        fs.load(&path).unwrap(),
        edited,
        "re-load reads the turn's committed content from the cell"
    );

    // The namespace resolves the path to the same file cell throughout.
    assert_eq!(firm.cell_for(&path), Some(file));

    // The file-tree path (read_dir + metadata) works over cells too.
    let entries = fs.read_dir(Path::new("/proj")).unwrap();
    assert!(entries.iter().any(|e| e.path == path && !e.is_dir));
    let md = fs.metadata(&path).unwrap();
    assert!(!md.is_dir && md.len as usize == edited.len());

    assert_eq!(fs.backend_label(), "FirmamentFs (cell=file, save=receipted turn)");
}

#[test]
fn sequential_saves_chain_their_receipts() {
    // Each save's receipt chains off the previous (the executor's genuine
    // per-agent receipt chain) — the provenance of the document's edit history.
    let firm = FirmamentFs::new();
    let path = "/notes.md";
    firm.seed_file(path, "# notes\n").unwrap();

    let fs: &dyn Fs = &firm;
    fs.save(Path::new(path), "# notes\nfirst\n").unwrap();
    let r1 = firm.last_receipt().unwrap();
    fs.save(Path::new(path), "# notes\nfirst\nsecond\n").unwrap();
    let r2 = firm.last_receipt().unwrap();

    assert_eq!(firm.receipt_count(), 2);
    assert_eq!(
        r2.previous_receipt_hash,
        Some(r1.receipt_hash()),
        "the second save's receipt chains off the first"
    );
    assert_eq!(fs.load(Path::new(path)).unwrap(), "# notes\nfirst\nsecond\n");
}
