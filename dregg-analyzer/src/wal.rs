//! Persist/WAL commit-log capture analysis (replay/recovery + crash overlay).
//!
//! ## Input format ([`WalCapture`])
//!
//! The node's durable, append-only commit log is a sequence of the node's own
//! [`dregg_persist::commit_log::CommitRecord`]s — one per finalized turn applied
//! to the ledger, keyed by a dense gap-free commit ordinal. A capture is the
//! `Vec<CommitRecord>` (in ordinal order) plus the durable `commit_cursor` the
//! node read at capture time (so we can model the crash-recovery overlay).
//!
//! ## What is ATTESTED / CHECKED (the log's own crash-consistency invariants)
//!
//! The commit log is engineered so that across an arbitrary crash:
//!   * `commit_cursor() == commit_log.len()` (no torn cursor),
//!   * every ordinal in `0..cursor` resolves to a record (dense, gap-free),
//!   * the cursor advances once per applied turn inside the atomic transaction.
//!
//! This analyzer checks those invariants over the capture directly (the same
//! conditions [`dregg_persist`]'s `IndexAuditReport::ok` and the module's
//! crash-consistency contract assert). A violation means the capture is a TORN
//! or CORRUPTED log — precisely the failure the commit log exists to make
//! impossible, so seeing it is a real anomaly.
//!
//! ## What is the RECOVERY OVERLAY (replay analysis)
//!
//!   * The replay set: records at `ordinal >= cursor` would be re-applied on
//!     restart (idempotently). We surface how many turns recovery would replay
//!     and from which block high-water mark (`block_executed_up_to`).
//!   * `ledger_root` continuity: each record binds the post-state root; the
//!     chain of roots is the convergence trail recovery asserts.

use serde::{Deserialize, Serialize};

use dregg_persist::commit_log::CommitRecord;

use crate::findings::{short_hex, AnalysisReport, Finding, Severity};

/// A captured WAL / commit-log: the durable commit records in ordinal order plus
/// the durable commit cursor at capture time.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WalCapture {
    /// The commit records, expected in ascending ordinal order.
    pub records: Vec<CommitRecord>,
    /// The durable `commit_cursor` the node read at capture time. For a
    /// crash-consistent store this MUST equal `records.len()`. A value below it
    /// models a crash mid-batch: records at `ordinal >= cursor` are the replay
    /// set. `None` ⇒ assume `records.len()` (a clean, fully-flushed capture).
    #[serde(default)]
    pub commit_cursor: Option<u64>,
}

/// Analyze a WAL capture for crash-consistency + replay/recovery.
pub fn analyze(capture: &WalCapture) -> AnalysisReport {
    let mut report = AnalysisReport::new("wal");
    let records = &capture.records;
    let len = records.len() as u64;
    let cursor = capture.commit_cursor.unwrap_or(len);
    report.summarize("commit_records", len);
    report.summarize("commit_cursor", cursor);

    if records.is_empty() {
        report.push(Finding::observed(
            Severity::Notice,
            "wal.empty",
            "the commit log is empty — a fresh node (nothing applied yet)",
        ));
        return report;
    }

    // ── CHECK: dense, gap-free, ascending ordinals ────────────────────────────
    // `ordinal == n` MUST mean exactly n turns were applied before it: ordinals
    // are 0,1,2,... with no gaps and no repeats.
    let mut ordinal_violations = 0usize;
    for (expected, rec) in records.iter().enumerate() {
        if rec.ordinal != expected as u64 {
            ordinal_violations += 1;
            report.push(Finding::verified(
                Severity::Critical,
                "dregg_persist::commit_log (dense-ordinal invariant)",
                "wal.ordinal_gap",
                format!(
                    "commit log is not dense/gap-free: record at position {expected} \
                     carries ordinal {} (expected {expected}) — a torn or corrupted \
                     log; recovery's gap-free resume contract is violated",
                    rec.ordinal
                ),
            ));
        }
    }
    if ordinal_violations == 0 {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_persist::commit_log (dense-ordinal invariant)",
            "wal.ordinals_dense",
            format!("all {len} commit ordinal(s) are dense, ascending, and gap-free"),
        ));
    }

    // ── CHECK: cursor agrees with log length (no torn cursor) ─────────────────
    if cursor == len {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_persist::commit_log (commit_cursor == log.len)",
            "wal.cursor_consistent",
            format!(
                "commit_cursor ({cursor}) == commit_log length ({len}): the cursor \
                 is not torn ahead of (or behind) the durable record set — a \
                 crash-consistent log"
            ),
        ));
    } else if cursor < len {
        // Records at ordinal >= cursor are the replay set (the atomic-commit
        // contract: such a record's transaction may not have advanced the
        // cursor; it is re-applied idempotently on restart).
        report.push(Finding::observed(
            Severity::Notice,
            "wal.replay_pending",
            format!(
                "commit_cursor ({cursor}) is BELOW log length ({len}): {} record(s) \
                 at ordinal >= {cursor} are the crash-recovery REPLAY set — recovery \
                 re-applies them idempotently on restart",
                len - cursor
            ),
        ));
    } else {
        report.push(Finding::verified(
            Severity::Critical,
            "dregg_persist::commit_log (commit_cursor == log.len)",
            "wal.cursor_torn",
            format!(
                "commit_cursor ({cursor}) is AHEAD of the durable log length ({len}): \
                 the cursor claims more turns committed than records exist — a TORN \
                 cursor, exactly the lost-finalized-turn hazard the commit log \
                 exists to prevent"
            ),
        ));
    }

    // ── RECOVERY OVERLAY: replay set + block high-water mark ───────────────────
    if cursor < len {
        let replay = &records[cursor as usize..];
        let resume_from = records
            .get(cursor.saturating_sub(1) as usize)
            .map(|r| r.block_executed_up_to)
            .unwrap_or(0);
        report.summarize("replay_turns", replay.len());
        report.summarize("recovery_resumes_block_hwm", resume_from);
    } else {
        report.summarize("replay_turns", 0);
    }
    if let Some(last) = records.last() {
        report.summarize("latest_height", last.height);
        report.summarize("latest_ledger_root", short_hex(&last.ledger_root));
        report.summarize("latest_block_hwm", last.block_executed_up_to);
    }

    // ── CHECK: per-record self-coherence + monotone block high-water mark ─────
    let mut height_regressions = 0usize;
    let mut hwm_regressions = 0usize;
    let mut prev_height: Option<u64> = None;
    let mut prev_hwm: Option<u64> = None;
    for rec in records {
        if let Some(ph) = prev_height {
            if rec.height < ph {
                height_regressions += 1;
            }
        }
        if let Some(pw) = prev_hwm {
            // The block high-water mark is monotone non-decreasing: each turn's
            // `block_executed_up_to` is >= the previous turn's.
            if rec.block_executed_up_to < pw {
                hwm_regressions += 1;
                report.push(Finding::verified(
                    Severity::Critical,
                    "dregg_persist::commit_log (monotone block_executed_up_to)",
                    "wal.hwm_regression",
                    format!(
                        "commit ordinal {} regresses the block high-water mark \
                         ({} < previous {pw}) — a turn was recorded as committed \
                         against an EARLIER block cursor than a prior turn; the \
                         recovery anchor is non-monotone",
                        rec.ordinal, rec.block_executed_up_to
                    ),
                ));
            }
        }
        prev_height = Some(rec.height);
        prev_hwm = Some(rec.block_executed_up_to);
    }
    report.summarize("touched_cells_total", records.iter().map(|r| r.touched_cells.len()).sum::<usize>());
    if height_regressions > 0 {
        report.push(Finding::observed(
            Severity::Notice,
            "wal.height_regression",
            format!(
                "{height_regressions} record(s) commit at a height below a prior \
                 record's — expected when several ROUTE-level turns share an \
                 attested height, but worth noting"
            ),
        ));
    }
    if hwm_regressions == 0 {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_persist::commit_log (monotone block_executed_up_to)",
            "wal.hwm_monotone",
            "the block high-water mark is monotone non-decreasing across the log: \
             the recovery anchor never moves backward",
        ));
    }

    report
}
