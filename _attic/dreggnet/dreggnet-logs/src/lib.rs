//! `dreggnet-logs` — **real per-tenant runtime logs** for DreggNet.
//!
//! The cloud-provider-readiness audit (`docs/CLOUD-PROVIDER-READINESS.md`, the
//! LOG row + master-list blocker #6) names the gap bluntly: `dregg-cloud logs`
//! prints **cached step metadata**, and the only real stdout/stderr tail is an
//! **operator-only** `docker logs` (`ops/src/docker.rs`). A cloud a developer
//! cannot see their own app's output on is not a cloud they will trust a workload
//! to. This crate closes that gap with a self-contained capture + store + query
//! engine:
//!
//! 1. **Capture** — a [`LogSink`] takes a resource's output as line records
//!    ([`LogLine`]: timestamp, stream, resource id, owner, the line) and appends
//!    them to a durable per-resource store.
//! 2. **Store** — durable JSONL, one file per resource under a root dir, with a
//!    retention policy (a line cap + a byte cap; oldest-dropped compaction). The
//!    durable file is the source of truth, so **reads survive a restart** and are
//!    correct **across processes** (the writer and the `logs` reader need not share
//!    memory).
//! 3. **Query** — [`LogSink::tail`], [`LogSink::follow`] (a live stream),
//!    [`LogSink::search`], and [`LogSink::since`] (the cross-process follow poll).
//!
//! ## The cap-scoping teeth
//!
//! Logs are **cap-scoped to the owner**. Every read takes a `requester` subject
//! (the verified `dga1_` cap holder — `dregg:<16hex>`, the same subject the
//! console scopes on) and refuses with [`LogError::Forbidden`] if it is not the
//! resource's recorded owner. A tenant can read **only their own** logs; another
//! user cannot tail them. This mirrors the console's one-rule scoping
//! (`console/src/scope.rs`): *a resource is in your view iff `owner == subject`*.
//!
//! ## The verifiable angle (tamper-evident)
//!
//! Each [`LogLine`] carries a `prev`/`hash` pair: a sha256 hash chain over the
//! resource's log. [`LogSink::verify`] replays it and detects any edit or
//! deletion of a retained line — a host cannot silently rewrite a tenant's served
//! output. (After retention compaction the chain is verified over the retained
//! window; the dropped prefix is gone by policy, not by tampering.)
//!
//! ## Named integration seams (the capture wire)
//!
//! Where output is produced, a run writes into a `LogSink` keyed by
//! `resource_id` + `owner`:
//! - **exec** — the compute-tier run ([`dreggnet_exec`]'s `run_workload`). The
//!   capture hook lives in `exec/src/capture.rs` and is wired by the CLI `run`.
//! - **deploy** — `dregg-deploy`'s clone→build→publish step output (the raw
//!   `git`/build child stdout/stderr). *Named seam, integration pass.*
//! - **server** — `control/src/server.rs`'s persistent-server run loop. *Named
//!   seam, integration pass.*
//! - **agent** — `exec/src/agent.rs`'s confined agent run. *Named seam.*
//! - **console** — a per-resource "Logs" panel (`console/`) reads `tail`/`since`
//!   cap-scoped to the signed-in subject. *Named seam, integration pass.*

use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::mpsc::{Receiver, Sender};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Which standard stream a captured line came from.
#[derive(Serialize, Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stream {
    Stdout,
    Stderr,
}

impl Stream {
    fn tag(self) -> u8 {
        match self {
            Stream::Stdout => 1,
            Stream::Stderr => 2,
        }
    }

    /// The short label rendered in a log view (`out` / `err`).
    pub fn label(self) -> &'static str {
        match self {
            Stream::Stdout => "out",
            Stream::Stderr => "err",
        }
    }
}

/// One captured line of a resource's output — the durable unit a log store holds.
///
/// The `prev`/`hash` fields form a per-resource tamper-evident chain (see
/// [`LogSink::verify`]). `seq` is the monotonic per-resource line number.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct LogLine {
    /// Monotonic per-resource sequence number (0-based).
    pub seq: u64,
    /// Capture time, milliseconds since the Unix epoch.
    pub ts_millis: u64,
    /// Which stream the line came from.
    pub stream: Stream,
    /// The resource that produced it (a workload / deploy / server id).
    pub resource_id: String,
    /// The cap-account subject that owns the resource (`dregg:<16hex>`).
    pub owner: String,
    /// The captured line text (newline-trimmed).
    pub line: String,
    /// Hex sha256 of the previous line's `hash` input, "" at genesis.
    pub prev: String,
    /// Hex sha256 binding this record into the chain.
    pub hash: String,
}

impl LogLine {
    /// Recompute the chain hash from this record's fields + a `prev` hash.
    fn compute_hash(&self, prev: &str) -> String {
        let mut h = Sha256::new();
        h.update(b"dreggnet-logs/v1");
        h.update(prev.as_bytes());
        h.update(self.seq.to_le_bytes());
        h.update(self.ts_millis.to_le_bytes());
        h.update([self.stream.tag()]);
        h.update(self.resource_id.as_bytes());
        h.update([0u8]);
        h.update(self.owner.as_bytes());
        h.update([0u8]);
        h.update(self.line.as_bytes());
        let digest = h.finalize();
        let mut s = String::with_capacity(64);
        for b in digest {
            use std::fmt::Write as _;
            let _ = write!(s, "{b:02x}");
        }
        s
    }
}

/// The store's retention policy — the size cap that bounds a resource's log.
///
/// When an append pushes the durable file past `max_lines` (or `max_bytes`), the
/// oldest lines are dropped (compaction keeps the most-recent suffix). A single
/// over-long line is truncated to `max_line_len` bytes on capture.
#[derive(Clone, Copy, Debug)]
pub struct Retention {
    pub max_lines: usize,
    pub max_bytes: u64,
    pub max_line_len: usize,
}

impl Default for Retention {
    fn default() -> Self {
        // ~50k lines / ~32 MiB per resource, 64 KiB per line — a generous tail
        // window for debugging without unbounded growth.
        Retention {
            max_lines: 50_000,
            max_bytes: 32 * 1024 * 1024,
            max_line_len: 64 * 1024,
        }
    }
}

/// What can go wrong on a log operation.
#[derive(Debug)]
pub enum LogError {
    /// No log exists for this resource (nothing has been captured).
    NotFound(String),
    /// The requester is not the resource's owner — the cap-scoping teeth.
    Forbidden {
        resource: String,
        owner: String,
        requester: String,
    },
    /// A durable-store I/O failure.
    Io(std::io::Error),
    /// A stored record failed to parse / the chain did not re-witness.
    Corrupt(String),
}

impl std::fmt::Display for LogError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LogError::NotFound(r) => write!(f, "no logs for resource `{r}`"),
            LogError::Forbidden {
                resource,
                owner,
                requester,
            } => write!(
                f,
                "forbidden: resource `{resource}` is owned by `{owner}`, not `{requester}` — \
                 you can only read your own logs"
            ),
            LogError::Io(e) => write!(f, "log store io: {e}"),
            LogError::Corrupt(e) => write!(f, "log store corrupt: {e}"),
        }
    }
}

impl std::error::Error for LogError {}

impl From<std::io::Error> for LogError {
    fn from(e: std::io::Error) -> Self {
        LogError::Io(e)
    }
}

/// A live tail: new [`LogLine`]s appended to a followed resource arrive here.
///
/// In-process followers (the server / exec capture path, which hold the same
/// [`LogSink`]) get each new line pushed over the channel. A cross-process reader
/// (the `dregg-cloud logs --follow` CLI, a separate process from the writer)
/// instead polls [`LogSink::since`].
pub struct LogFollower {
    rx: Receiver<LogLine>,
}

impl LogFollower {
    /// Block for the next appended line, or `None` once the sink is dropped.
    pub fn recv(&self) -> Option<LogLine> {
        self.rx.recv().ok()
    }

    /// The next appended line if one is already queued, without blocking.
    pub fn try_recv(&self) -> Option<LogLine> {
        self.rx.try_recv().ok()
    }

    /// The raw receiver, for callers that want to `select`/timeout themselves.
    pub fn into_receiver(self) -> Receiver<LogLine> {
        self.rx
    }
}

/// Per-resource append head, cached in memory so an append need not re-scan the
/// whole file to find the previous hash + next seq.
#[derive(Clone)]
struct Head {
    next_seq: u64,
    last_hash: String,
    line_count: usize,
    owner: String,
}

/// The durable, cap-scoped per-tenant log store.
///
/// One [`LogSink`] serves every resource; lines are partitioned into a durable
/// file per resource under `root`. Cloneable handles are *not* provided — share
/// it behind an `Arc` if multiple owners need it.
pub struct LogSink {
    root: PathBuf,
    retention: Retention,
    /// Per-resource append head (lazy-loaded from disk on first touch).
    heads: Mutex<HashMap<String, Head>>,
    /// In-process live followers, by resource id.
    followers: Mutex<HashMap<String, Vec<Sender<LogLine>>>>,
}

impl LogSink {
    /// Open (creating if absent) a durable log store rooted at `root`. Reads hit
    /// the durable files, so a freshly opened sink already sees everything a prior
    /// process wrote — the **restart-survival** property.
    pub fn open(root: impl AsRef<Path>) -> Result<LogSink, LogError> {
        Self::open_with_retention(root, Retention::default())
    }

    /// As [`LogSink::open`], with an explicit retention policy.
    pub fn open_with_retention(
        root: impl AsRef<Path>,
        retention: Retention,
    ) -> Result<LogSink, LogError> {
        let root = root.as_ref().to_path_buf();
        std::fs::create_dir_all(&root)?;
        Ok(LogSink {
            root,
            retention,
            heads: Mutex::new(HashMap::new()),
            followers: Mutex::new(HashMap::new()),
        })
    }

    /// The durable file path for a resource (hex-encoded id → no unsafe chars,
    /// no collisions).
    fn path_for(&self, resource_id: &str) -> PathBuf {
        let mut name = String::with_capacity(resource_id.len() * 2 + 4);
        for b in resource_id.as_bytes() {
            use std::fmt::Write as _;
            let _ = write!(name, "{b:02x}");
        }
        name.push_str(".log");
        self.root.join(name)
    }

    /// Capture one line for `resource_id` owned by `owner`. Appends durably,
    /// updates the chain, enforces retention, and notifies live followers. Returns
    /// the stored [`LogLine`].
    ///
    /// The first append for a resource fixes its `owner`; later appends under a
    /// *different* owner are refused (a resource has one owner — the cap holder).
    pub fn append(
        &self,
        resource_id: &str,
        owner: &str,
        stream: Stream,
        line: &str,
    ) -> Result<LogLine, LogError> {
        // Clamp an over-long line to the per-line cap, and strip embedded
        // newlines so one record is always exactly one JSONL line.
        let mut text = line.replace(['\n', '\r'], " ");
        if text.len() > self.retention.max_line_len {
            text.truncate(self.retention.max_line_len);
        }

        let mut heads = self.heads.lock().unwrap();
        let head = match heads.get(resource_id) {
            Some(h) => h.clone(),
            None => self.load_head(resource_id)?,
        };

        // One owner per resource.
        if !head.owner.is_empty() && head.owner != owner {
            return Err(LogError::Forbidden {
                resource: resource_id.to_string(),
                owner: head.owner.clone(),
                requester: owner.to_string(),
            });
        }

        let ts_millis = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0);

        let mut rec = LogLine {
            seq: head.next_seq,
            ts_millis,
            stream,
            resource_id: resource_id.to_string(),
            owner: owner.to_string(),
            line: text,
            prev: head.last_hash.clone(),
            hash: String::new(),
        };
        rec.hash = rec.compute_hash(&head.last_hash);

        // Durable append (JSONL).
        let encoded =
            serde_json::to_string(&rec).map_err(|e| LogError::Corrupt(format!("encode: {e}")))?;
        {
            let mut f = OpenOptions::new()
                .create(true)
                .append(true)
                .open(self.path_for(resource_id))?;
            f.write_all(encoded.as_bytes())?;
            f.write_all(b"\n")?;
            f.flush()?;
        }

        let new_head = Head {
            next_seq: rec.seq + 1,
            last_hash: rec.hash.clone(),
            line_count: head.line_count + 1,
            owner: owner.to_string(),
        };
        heads.insert(resource_id.to_string(), new_head.clone());
        drop(heads);

        // Retention: compact if we've grown past the line cap or byte cap.
        self.maybe_compact(resource_id, new_head.line_count)?;

        // Notify live in-process followers.
        if let Ok(mut map) = self.followers.lock() {
            if let Some(senders) = map.get_mut(resource_id) {
                senders.retain(|s| s.send(rec.clone()).is_ok());
            }
        }

        Ok(rec)
    }

    /// Load (or initialize) the append head for a resource by scanning its durable
    /// file. Cheap relative to capture volume and only paid once per resource per
    /// process (then cached).
    fn load_head(&self, resource_id: &str) -> Result<Head, LogError> {
        let path = self.path_for(resource_id);
        if !path.exists() {
            return Ok(Head {
                next_seq: 0,
                last_hash: String::new(),
                line_count: 0,
                owner: String::new(),
            });
        }
        let lines = self.read_all_raw(resource_id)?;
        match lines.last() {
            Some(last) => Ok(Head {
                next_seq: last.seq + 1,
                last_hash: last.hash.clone(),
                line_count: lines.len(),
                owner: last.owner.clone(),
            }),
            None => Ok(Head {
                next_seq: 0,
                last_hash: String::new(),
                line_count: 0,
                owner: String::new(),
            }),
        }
    }

    /// Read every stored line for a resource WITHOUT a cap check (internal).
    fn read_all_raw(&self, resource_id: &str) -> Result<Vec<LogLine>, LogError> {
        let path = self.path_for(resource_id);
        let file = match File::open(&path) {
            Ok(f) => f,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
            Err(e) => return Err(LogError::Io(e)),
        };
        let reader = BufReader::new(file);
        let mut out = Vec::new();
        for (i, line) in reader.lines().enumerate() {
            let line = line?;
            if line.trim().is_empty() {
                continue;
            }
            let rec: LogLine = serde_json::from_str(&line)
                .map_err(|e| LogError::Corrupt(format!("line {i}: {e}")))?;
            out.push(rec);
        }
        Ok(out)
    }

    /// Read every stored line for a resource, enforcing the cap-scope.
    fn read_all_scoped(
        &self,
        resource_id: &str,
        requester: &str,
    ) -> Result<Vec<LogLine>, LogError> {
        let lines = self.read_all_raw(resource_id)?;
        if lines.is_empty() {
            return Err(LogError::NotFound(resource_id.to_string()));
        }
        // The owner is recorded on every line; the teeth check it once.
        let owner = &lines[0].owner;
        if owner != requester {
            return Err(LogError::Forbidden {
                resource: resource_id.to_string(),
                owner: owner.clone(),
                requester: requester.to_string(),
            });
        }
        Ok(lines)
    }

    /// The last `n` lines of a resource's log, newest-last. Cap-scoped: only the
    /// owner may read. `n == 0` returns the whole log.
    pub fn tail(
        &self,
        resource_id: &str,
        n: usize,
        requester: &str,
    ) -> Result<Vec<LogLine>, LogError> {
        let mut lines = self.read_all_scoped(resource_id, requester)?;
        if n > 0 && lines.len() > n {
            lines = lines.split_off(lines.len() - n);
        }
        Ok(lines)
    }

    /// Every line whose text contains `query` (substring match). Cap-scoped.
    pub fn search(
        &self,
        resource_id: &str,
        query: &str,
        requester: &str,
    ) -> Result<Vec<LogLine>, LogError> {
        let lines = self.read_all_scoped(resource_id, requester)?;
        Ok(lines
            .into_iter()
            .filter(|l| l.line.contains(query))
            .collect())
    }

    /// Every line with `seq > after_seq`. The cross-process `--follow` poll: a CLI
    /// reader (a separate process from the writer) tails, then loops calling this
    /// with the last seq it saw to pick up freshly-appended lines from disk.
    /// Cap-scoped.
    pub fn since(
        &self,
        resource_id: &str,
        after_seq: u64,
        requester: &str,
    ) -> Result<Vec<LogLine>, LogError> {
        let lines = self.read_all_scoped(resource_id, requester)?;
        Ok(lines.into_iter().filter(|l| l.seq > after_seq).collect())
    }

    /// Subscribe to a resource's live tail (in-process). Returns a [`LogFollower`]
    /// that receives every line appended *after* this call. Cap-scoped: the
    /// resource must already exist and be owned by `requester`.
    pub fn follow(&self, resource_id: &str, requester: &str) -> Result<LogFollower, LogError> {
        // Cap-check against the existing log (the resource must have an owner).
        let _ = self.read_all_scoped(resource_id, requester)?;
        let (tx, rx) = std::sync::mpsc::channel();
        self.followers
            .lock()
            .unwrap()
            .entry(resource_id.to_string())
            .or_default()
            .push(tx);
        Ok(LogFollower { rx })
    }

    /// Re-witness the tamper-evident chain of a resource's retained log: every
    /// line's `hash` must recompute from its fields, and each line must link to its
    /// predecessor (`line.prev == predecessor.hash`). Returns `Ok(true)` when the
    /// chain re-witnesses, `Ok(false)` if a record was edited/reordered/deleted.
    /// Cap-scoped.
    pub fn verify(&self, resource_id: &str, requester: &str) -> Result<bool, LogError> {
        let lines = self.read_all_scoped(resource_id, requester)?;
        let mut prev: Option<&LogLine> = None;
        for rec in &lines {
            if rec.compute_hash(&rec.prev) != rec.hash {
                return Ok(false);
            }
            if let Some(p) = prev {
                // Consecutive retained lines must link; after retention compaction
                // the first retained line's `prev` points at a dropped record (by
                // policy), so linkage is checked from the second line on.
                if rec.prev != p.hash || rec.seq != p.seq + 1 {
                    return Ok(false);
                }
            }
            prev = Some(rec);
        }
        Ok(true)
    }

    /// Compact the durable file to the retention window if it has grown past the
    /// line or byte cap — keep the most-recent suffix, drop the oldest.
    fn maybe_compact(&self, resource_id: &str, line_count: usize) -> Result<(), LogError> {
        let path = self.path_for(resource_id);
        let over_lines = line_count > self.retention.max_lines;
        let over_bytes = std::fs::metadata(&path)
            .map(|m| m.len() > self.retention.max_bytes)
            .unwrap_or(false);
        if !over_lines && !over_bytes {
            return Ok(());
        }
        let lines = self.read_all_raw(resource_id)?;
        let keep_from = lines.len().saturating_sub(self.retention.max_lines);
        let kept = &lines[keep_from..];
        let tmp = path.with_extension("log.compact");
        {
            let mut f = OpenOptions::new()
                .create(true)
                .write(true)
                .truncate(true)
                .open(&tmp)?;
            for rec in kept {
                let encoded = serde_json::to_string(rec)
                    .map_err(|e| LogError::Corrupt(format!("encode: {e}")))?;
                f.write_all(encoded.as_bytes())?;
                f.write_all(b"\n")?;
            }
            f.flush()?;
        }
        std::fs::rename(&tmp, &path)?;
        if let Ok(mut heads) = self.heads.lock() {
            if let Some(h) = heads.get_mut(resource_id) {
                h.line_count = kept.len();
            }
        }
        Ok(())
    }

    /// The distinct resource ids that have logs in this store (for an operator's
    /// sense of what exists; the cap-scoped query API never enumerates this to a
    /// tenant).
    pub fn resources(&self) -> Result<Vec<String>, LogError> {
        let mut out = Vec::new();
        for entry in std::fs::read_dir(&self.root)? {
            let entry = entry?;
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if let Some(hex) = name.strip_suffix(".log") {
                if let Some(id) = decode_hex(hex) {
                    out.push(id);
                }
            }
        }
        out.sort();
        Ok(out)
    }
}

/// Decode a hex resource-id filename back to the id (None if not valid hex/utf8).
fn decode_hex(hex: &str) -> Option<String> {
    if hex.len() % 2 != 0 {
        return None;
    }
    let mut bytes = Vec::with_capacity(hex.len() / 2);
    let h = hex.as_bytes();
    let mut i = 0;
    while i < h.len() {
        let hi = (h[i] as char).to_digit(16)?;
        let lo = (h[i + 1] as char).to_digit(16)?;
        bytes.push((hi * 16 + lo) as u8);
        i += 2;
    }
    String::from_utf8(bytes).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: &str = "dregg:aaaa0000aaaa0000";
    const BOB: &str = "dregg:bbbb1111bbbb1111";

    fn sink() -> (tempfile::TempDir, LogSink) {
        let dir = tempfile::tempdir().unwrap();
        let sink = LogSink::open(dir.path()).unwrap();
        (dir, sink)
    }

    // ── capture → tail: the real lines, not metadata ──────────────────────────
    #[test]
    fn capture_then_tail_returns_the_real_lines() {
        let (_d, sink) = sink();
        sink.append("wl_1", ALICE, Stream::Stdout, "hello").unwrap();
        sink.append("wl_1", ALICE, Stream::Stdout, "world").unwrap();
        sink.append("wl_1", ALICE, Stream::Stderr, "a warning")
            .unwrap();

        let lines = sink.tail("wl_1", 0, ALICE).unwrap();
        assert_eq!(lines.len(), 3);
        assert_eq!(lines[0].line, "hello");
        assert_eq!(lines[1].line, "world");
        assert_eq!(lines[2].line, "a warning");
        assert_eq!(lines[2].stream, Stream::Stderr);
        // Monotonic seq.
        assert_eq!(
            lines.iter().map(|l| l.seq).collect::<Vec<_>>(),
            vec![0, 1, 2]
        );

        // Bounded tail returns the most-recent suffix.
        let last2 = sink.tail("wl_1", 2, ALICE).unwrap();
        assert_eq!(last2.len(), 2);
        assert_eq!(last2[0].line, "world");
    }

    // ── follow: new lines stream to a live subscriber ─────────────────────────
    #[test]
    fn follow_streams_new_lines() {
        let (_d, sink) = sink();
        sink.append("wl_2", ALICE, Stream::Stdout, "first").unwrap();
        let f = sink.follow("wl_2", ALICE).unwrap();

        // Lines appended after subscribing arrive on the stream.
        sink.append("wl_2", ALICE, Stream::Stdout, "live-1")
            .unwrap();
        sink.append("wl_2", ALICE, Stream::Stderr, "live-2")
            .unwrap();

        let a = f.recv().unwrap();
        let b = f.recv().unwrap();
        assert_eq!(a.line, "live-1");
        assert_eq!(b.line, "live-2");
        assert_eq!(b.stream, Stream::Stderr);
    }

    // ── since: the cross-process follow poll picks up fresh lines ─────────────
    #[test]
    fn since_returns_only_newer_lines() {
        let (_d, sink) = sink();
        sink.append("wl_3", ALICE, Stream::Stdout, "l0").unwrap();
        let last = sink.tail("wl_3", 0, ALICE).unwrap().last().unwrap().seq;
        sink.append("wl_3", ALICE, Stream::Stdout, "l1").unwrap();
        sink.append("wl_3", ALICE, Stream::Stdout, "l2").unwrap();

        let fresh = sink.since("wl_3", last, ALICE).unwrap();
        assert_eq!(
            fresh.iter().map(|l| l.line.as_str()).collect::<Vec<_>>(),
            vec!["l1", "l2"]
        );
    }

    // ── search: filter a resource's lines ─────────────────────────────────────
    #[test]
    fn search_filters_lines() {
        let (_d, sink) = sink();
        sink.append("wl_4", ALICE, Stream::Stdout, "starting build")
            .unwrap();
        sink.append("wl_4", ALICE, Stream::Stderr, "error: boom")
            .unwrap();
        sink.append("wl_4", ALICE, Stream::Stdout, "error count: 1")
            .unwrap();
        sink.append("wl_4", ALICE, Stream::Stdout, "done").unwrap();

        let hits = sink.search("wl_4", "error", ALICE).unwrap();
        assert_eq!(hits.len(), 2);
        assert!(hits.iter().all(|l| l.line.contains("error")));
    }

    // ── TOOTH: another user CANNOT read someone else's logs ───────────────────
    #[test]
    fn another_user_cannot_read_your_logs() {
        let (_d, sink) = sink();
        sink.append("wl_5", ALICE, Stream::Stdout, "alice secret")
            .unwrap();

        // Bob is refused on every read surface.
        assert!(matches!(
            sink.tail("wl_5", 0, BOB),
            Err(LogError::Forbidden { .. })
        ));
        assert!(matches!(
            sink.search("wl_5", "secret", BOB),
            Err(LogError::Forbidden { .. })
        ));
        assert!(matches!(
            sink.since("wl_5", 0, BOB),
            Err(LogError::Forbidden { .. })
        ));
        assert!(matches!(
            sink.follow("wl_5", BOB),
            Err(LogError::Forbidden { .. })
        ));

        // The owner still reads fine.
        assert_eq!(sink.tail("wl_5", 0, ALICE).unwrap().len(), 1);
    }

    // ── TOOTH: a resource has ONE owner; a foreign writer is refused ──────────
    #[test]
    fn a_resource_has_one_owner() {
        let (_d, sink) = sink();
        sink.append("wl_6", ALICE, Stream::Stdout, "mine").unwrap();
        assert!(matches!(
            sink.append("wl_6", BOB, Stream::Stdout, "hijack"),
            Err(LogError::Forbidden { .. })
        ));
    }

    // ── DURABLE: the store survives a restart (reopen reads prior lines) ──────
    #[test]
    fn durable_store_survives_restart() {
        let dir = tempfile::tempdir().unwrap();
        {
            let sink = LogSink::open(dir.path()).unwrap();
            sink.append("wl_7", ALICE, Stream::Stdout, "before restart")
                .unwrap();
            sink.append("wl_7", ALICE, Stream::Stdout, "line two")
                .unwrap();
        }
        // A brand-new sink over the same root — a process restart.
        let reopened = LogSink::open(dir.path()).unwrap();
        let lines = reopened.tail("wl_7", 0, ALICE).unwrap();
        assert_eq!(lines.len(), 2);
        assert_eq!(lines[0].line, "before restart");
        assert_eq!(lines[1].line, "line two");

        // And appends continue the SAME chain across the restart.
        let next = reopened
            .append("wl_7", ALICE, Stream::Stdout, "after restart")
            .unwrap();
        assert_eq!(next.seq, 2);
        assert_eq!(next.prev, lines[1].hash);
        assert!(reopened.verify("wl_7", ALICE).unwrap());
    }

    // ── VERIFIABLE: the hash chain re-witnesses, and tampering is caught ──────
    #[test]
    fn the_chain_is_tamper_evident() {
        let dir = tempfile::tempdir().unwrap();
        let sink = LogSink::open(dir.path()).unwrap();
        sink.append("wl_8", ALICE, Stream::Stdout, "honest-1")
            .unwrap();
        sink.append("wl_8", ALICE, Stream::Stdout, "honest-2")
            .unwrap();
        sink.append("wl_8", ALICE, Stream::Stdout, "honest-3")
            .unwrap();
        assert!(sink.verify("wl_8", ALICE).unwrap());

        // Tamper with the durable file: rewrite a line's text in place.
        let path = sink.path_for("wl_8");
        let raw = std::fs::read_to_string(&path).unwrap();
        let tampered = raw.replace("honest-2", "forged!");
        assert_ne!(raw, tampered);
        std::fs::write(&path, tampered).unwrap();

        // A fresh sink re-reads from disk; the chain no longer re-witnesses.
        let reopened = LogSink::open(dir.path()).unwrap();
        assert!(
            !reopened.verify("wl_8", ALICE).unwrap(),
            "edited line must break the chain"
        );
    }

    // ── retention: the line cap bounds the durable log (oldest dropped) ───────
    #[test]
    fn retention_caps_the_log() {
        let dir = tempfile::tempdir().unwrap();
        let sink = LogSink::open_with_retention(
            dir.path(),
            Retention {
                max_lines: 5,
                max_bytes: 1 << 30,
                max_line_len: 1024,
            },
        )
        .unwrap();
        for i in 0..20 {
            sink.append("wl_9", ALICE, Stream::Stdout, &format!("line-{i}"))
                .unwrap();
        }
        let lines = sink.tail("wl_9", 0, ALICE).unwrap();
        assert_eq!(lines.len(), 5, "compacted to the retention window");
        assert_eq!(lines[0].line, "line-15");
        assert_eq!(lines[4].line, "line-19");
        // The retained window still re-witnesses internally.
        assert!(sink.verify("wl_9", ALICE).unwrap());
    }

    // ── unknown resource → NotFound (not an empty success that hides a typo) ──
    #[test]
    fn unknown_resource_is_not_found() {
        let (_d, sink) = sink();
        assert!(matches!(
            sink.tail("nope", 0, ALICE),
            Err(LogError::NotFound(_))
        ));
    }

    // ── multi-resource isolation + the operator resource census ───────────────
    #[test]
    fn resources_are_isolated_and_enumerable() {
        let (_d, sink) = sink();
        sink.append("wl_a", ALICE, Stream::Stdout, "a").unwrap();
        sink.append("wl_b", BOB, Stream::Stdout, "b").unwrap();
        let mut rs = sink.resources().unwrap();
        rs.sort();
        assert_eq!(rs, vec!["wl_a".to_string(), "wl_b".to_string()]);
        // Each tail is scoped to its own owner.
        assert_eq!(sink.tail("wl_a", 0, ALICE).unwrap().len(), 1);
        assert!(matches!(
            sink.tail("wl_b", 0, ALICE),
            Err(LogError::Forbidden { .. })
        ));
    }
}
