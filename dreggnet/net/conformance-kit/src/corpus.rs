//! The corpus loader + ledger-keying coverage-matrix skeleton (43 §9).
//!
//! The corpus is content-addressed and backend-agnostic: ONE vector set runs
//! against ALL backends, so the generated engine slots in with **zero corpus
//! change**. This module pins the on-disk store seam ([`CasStore`]/[`CorpusStore`]/
//! [`Corpus`]) and the static keying half of the non-vacuity meta
//! ([`CoverageMatrix`] — every non-OOS `40-LEDGER` row owns ≥1 vector). The actual
//! `corpus.pack` encode/decode (dCBOR) and the curl/fuzz importers are deferred to
//! the corpus unit — `todo!()` bodies here.

use std::path::Path;

use crate::hash::{ContentHash, GoldenHash, ProjectionId, SpecId, VectorId};
use crate::ids::{CaseKey, Kind, LedgerKey, Primitive, UnitId};
use crate::observation::{Event, Observation, ResourceOp, Schedule, Spec};
use crate::vector::{Projection, Vector};

// ── content-addressed storage ───────────────────────────────────────────────────
pub trait CasStore {
    fn get(&self, h: ContentHash) -> Option<&[u8]>;
    fn contains(&self, h: ContentHash) -> bool;
    /// Returns `of_bytes(bytes)`.
    fn put(&mut self, bytes: &[u8]) -> ContentHash;
}

/// `_blobs/<hh>/<hash>` on disk.
pub struct DirCasStore {
    pub root: std::path::PathBuf,
}
/// An mmap'd CAS region of `corpus.pack`.
pub struct PackCasStore<'a>(pub &'a [u8]);

pub trait CorpusStore {
    fn get_vector(&self, id: VectorId) -> Option<Vector>;
    fn resolve_input(&self, v: &Vector) -> ResolvedInput<'_>;
    fn resolve_golden(&self, h: GoldenHash) -> Option<Observation>;
    fn get_projection(&self, id: ProjectionId) -> Option<Projection>;
    fn get_spec(&self, id: SpecId) -> Option<Spec>;
    /// Recompute ALL ids, fail-closed (loaders MUST NOT trust the stored id).
    fn verify(&self) -> Result<(), CorpusIntegrityError>;
}

/// The runner resolves the stored [`Input`](crate::vector::Input) to this before
/// calling the adapter — `decode_region` takes `&[u8]`, `run_machine` takes
/// `&[Event]`, etc. (48 §4 Spec/SpecRef boundary).
pub enum ResolvedInput<'a> {
    Bytes(&'a [u8]),
    EventSeq(&'a [Event]),
    ResourceOps(&'a [ResourceOp]),
    Schedule(&'a Schedule),
}

pub struct CorpusIntegrityError {
    pub id: VectorId,
    pub stored: ContentHash,
    pub recomputed: ContentHash,
}

/// Owns a [`CorpusStore`] + a corpus index. The authored tree is
/// `corpus/<primitive>/<unit>/…`; `compile` packs it into a single `corpus.pack`.
pub struct Corpus {
    vectors: Vec<Vector>,
}

impl Corpus {
    pub fn load_authored(_root: &Path) -> Result<Corpus, CorpusError> {
        todo!("walk corpus/<primitive>/<unit>/, parse vectors + dir-inherited keys (43 §9)")
    }
    pub fn load_pack(_pack: &Path) -> Result<Corpus, CorpusError> {
        todo!("mmap corpus.pack, verify all VectorIds fail-closed (43 §9)")
    }
    pub fn compile(_root: &Path, _out: &Path) -> Result<PackStats, CorpusError> {
        todo!("pack authored tree → corpus.pack + _blobs CAS (43 §9)")
    }
    pub fn vectors(&self) -> impl Iterator<Item = &Vector> {
        self.vectors.iter()
    }
    pub fn by_id(&self, _id: VectorId) -> Option<&Vector> {
        todo!("index lookup (43 §9)")
    }
    pub fn by_primitive(&self, _p: Primitive) -> &[VectorId] {
        todo!("index lookup (43 §9)")
    }
    pub fn by_unit(&self, _u: &UnitId) -> &[VectorId] {
        todo!("index lookup (43 §9)")
    }
    pub fn by_ledger(&self, _k: &LedgerKey) -> &[VectorId] {
        todo!("index lookup (43 §9)")
    }
    pub fn by_suite(&self, _c: &CaseKey) -> &[VectorId] {
        todo!("index lookup (43 §9)")
    }
    pub fn by_kind(&self, _k: Kind) -> &[VectorId] {
        todo!("index lookup (43 §9)")
    }
}

#[derive(Debug)]
pub enum CorpusError {
    Io(String),
    Decode(String),
    Integrity,
}
pub struct PackStats {
    pub vectors: usize,
    pub blobs: usize,
}
pub struct ImportStats {
    pub imported: usize,
    pub skipped: usize,
}
pub struct ExportStats {
    pub exported: usize,
}

// ── ledger / suite models + the static coverage meta ────────────────────────────
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RowStatus {
    Modeled,
    Gap,
    Oos,
}
pub struct LedgerRow {
    pub key: LedgerKey,
    pub section: char,
    pub status: RowStatus,
    pub reason: Option<String>,
}
pub struct Ledger {
    rows: Vec<LedgerRow>,
}
pub struct Suite;

impl Ledger {
    pub fn load(_path: &Path) -> Result<Ledger, CorpusError> {
        todo!("parse 40-COMPLETENESS-LEDGER.md rows (43 §9)")
    }
    pub fn rows(&self) -> impl Iterator<Item = &LedgerRow> {
        self.rows.iter()
    }
    pub fn non_oos(&self) -> impl Iterator<Item = &LedgerRow> {
        self.rows.iter().filter(|r| r.status != RowStatus::Oos)
    }
}

/// The per-vector runtime outcome the coverage matrix folds in (CR-6 runtime
/// half). Maps onto the runner's [`Verdict`](crate::Verdict).
pub enum VectorOutcome {
    Agree { backends: u8 },
    Divergence,
    AllAbsent,
    Rejected,
}

pub struct CoverageMatrix {
    /// row → vectors keyed to it (static) + folded runtime agreement counts.
    rows: std::collections::BTreeMap<LedgerKey, RowCoverage>,
}
#[derive(Default)]
struct RowCoverage {
    vectors: Vec<VectorId>,
    genuine_agreements: usize,
}

impl CoverageMatrix {
    pub fn build(_corpus: &Corpus, _ledger: &Ledger, _suite: &Suite) -> CoverageMatrix {
        todo!("cross every non-OOS row with its keyed vectors (41 §F.2)")
    }
    pub fn vectors_for(&self, k: &LedgerKey) -> &[VectorId] {
        self.rows
            .get(k)
            .map(|c| c.vectors.as_slice())
            .unwrap_or(&[])
    }
    /// STATIC keying half of `41:345-347` — every non-OOS row owns ≥1 vector.
    pub fn assert_every_non_oos_row_covered(&self) -> Result<(), Vec<LedgerKey>> {
        let missing: Vec<LedgerKey> = self
            .rows
            .iter()
            .filter(|(_, c)| c.vectors.is_empty())
            .map(|(k, _)| *k)
            .collect();
        if missing.is_empty() {
            Ok(())
        } else {
            Err(missing)
        }
    }
    pub fn rows_without_vectors(&self) -> Vec<LedgerKey> {
        self.rows
            .iter()
            .filter(|(_, c)| c.vectors.is_empty())
            .map(|(k, _)| *k)
            .collect()
    }
    /// RUNTIME non-vacuity half (CR-6) — fold the runner's per-vector outcomes in.
    pub fn fold_runtime(&mut self, results: &[(VectorId, VectorOutcome)]) {
        for (_id, outcome) in results {
            if let VectorOutcome::Agree { .. } = outcome {
                // a real impl maps the VectorId → its rows and credits each.
                todo!("credit genuine agreement to the vector's ledger rows (41 §F.2)")
            }
        }
    }
    pub fn assert_every_non_oos_row_genuinely_covered(&self) -> Result<(), Vec<LedgerKey>> {
        let missing: Vec<LedgerKey> = self
            .rows
            .iter()
            .filter(|(_, c)| c.genuine_agreements == 0)
            .map(|(k, _)| *k)
            .collect();
        if missing.is_empty() {
            Ok(())
        } else {
            Err(missing)
        }
    }
    pub fn render_markdown(&self) -> String {
        todo!("render the coverage table (43 §9)")
    }
}

// ── migration tooling (curl replay + fuzz bridge) ───────────────────────────────
pub fn import_curl(_curl_data_dir: &Path, _out_root: &Path) -> Result<ImportStats, CorpusError> {
    todo!("generalize net/httpe/tests/curl_test_vectors.rs CurlTestCase → Vector (43 §9)")
}

pub struct FuzzRoot {
    pub crate_dir: std::path::PathBuf,
}
/// EXHAUSTIVE, totality-checked: a missing target ⇒ hard error (anti-launder).
pub struct FuzzKeyMap(
    pub std::collections::BTreeMap<String, (Primitive, UnitId, Vec<LedgerKey>, Vec<CaseKey>)>,
);
pub fn bridge_fuzz_corpus(
    _roots: &[FuzzRoot],
    _map: &FuzzKeyMap,
    _out_root: &Path,
) -> Result<ImportStats, CorpusError> {
    todo!("bridge net/*/fuzz corpora → un-golden Vectors (43 §9, 47)")
}
pub fn export_fuzz_view(_corpus: &Corpus, _fuzz_root: &Path) -> Result<ExportStats, CorpusError> {
    todo!("export the corpus as a libFuzzer seed view (43 §9, 47)")
}
