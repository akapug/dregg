//! # `link_registry` — the verified cross-platform link record + the `resolve_root` seam.
//!
//! After [`crate::link_claim::verify_link_claim`] proves that root key K controls a platform
//! account, the frontend RECORDS the binding here. Then anywhere the offerings stack compares
//! actors (leaderboards, council membership, session grants, a portfolio), it first
//! [`resolve_root`](LinkStore::resolve_root)s the custodial pubkey to its root — collapsing a
//! Discord-you and a Telegram-you (different custodial keys) into ONE human whenever both have
//! linked to the same K.
//!
//! Storage is an APPEND-ONLY TSV log (the cross-process-simplest shared store — all three dregg
//! processes on one box append to and read the same file; `O_APPEND` keeps concurrent writes from
//! interleaving a single record, and resolution is latest-record-wins). A relink or a rebind is
//! just another appended line; history is preserved (the deep version lifts this onto K's identity
//! cell so links become receipt-signed turns — see the design doc).
//!
//! The record binds the RAW pubkeys (hex), never a cell id: `link_claim` uses the framework
//! `"default"`-domain cell derivation while `account_id` uses `"dregg:account-identity:v1"` — same
//! key, two cell flavors, so the join key is the pubkey and each consumer derives its own cell id.

use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};

/// One verified link: root key K attests it controls `(platform, platform_uid)` whose custodial
/// dregg key is `custodial_pubkey_hex`, recorded at `verified_at` (unix seconds). All fields are
/// TAB- and NEWLINE-free by construction (hex / ascii-platform / decimal uid), so the TSV encoding
/// is injective.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkRecord {
    /// The user-held ROOT key K's pubkey (lowercase hex) — the join key one human resolves to.
    pub root_pubkey_hex: String,
    /// The platform this link is for (`"discord"`, `"telegram"`, ...).
    pub platform: String,
    /// The platform account id (Discord/Telegram uid as a decimal string).
    pub platform_uid: String,
    /// The platform's CUSTODIAL dregg pubkey (lowercase hex) — what turns on that platform are
    /// signed/attributed under, and the key `resolve_root` maps FROM.
    pub custodial_pubkey_hex: String,
    /// When the link was verified (unix seconds).
    pub verified_at: u64,
}

impl LinkRecord {
    /// A field is storable iff it carries no TAB or NEWLINE (the TSV delimiters).
    fn field_ok(s: &str) -> bool {
        !s.as_bytes().iter().any(|&b| b == b'\t' || b == b'\n')
    }

    /// Render as one TSV line (no trailing newline). `None` if any field carries a delimiter.
    pub fn to_line(&self) -> Option<String> {
        for f in [
            &self.root_pubkey_hex,
            &self.platform,
            &self.platform_uid,
            &self.custodial_pubkey_hex,
        ] {
            if !Self::field_ok(f) {
                return None;
            }
        }
        Some(format!(
            "{}\t{}\t{}\t{}\t{}",
            self.root_pubkey_hex,
            self.platform,
            self.platform_uid,
            self.custodial_pubkey_hex,
            self.verified_at
        ))
    }

    /// Parse one TSV line. `None` on the wrong field count / a bad `verified_at` (a malformed
    /// line is skipped, never crashes resolution).
    pub fn from_line(line: &str) -> Option<LinkRecord> {
        let f: Vec<&str> = line.split('\t').collect();
        if f.len() != 5 {
            return None;
        }
        Some(LinkRecord {
            root_pubkey_hex: f[0].to_string(),
            platform: f[1].to_string(),
            platform_uid: f[2].to_string(),
            custodial_pubkey_hex: f[3].to_string(),
            verified_at: f[4].parse().ok()?,
        })
    }
}

/// The store both the frontends (append a verified link) and the offerings stack (resolve) use.
pub trait LinkStore {
    /// Append a verified link. The caller has ALREADY run `verify_link_claim` — this store does
    /// not re-verify (it is a record, not a gate).
    fn record(&mut self, rec: &LinkRecord) -> std::io::Result<()>;

    /// All records, oldest-first (the resolution helpers scan these).
    fn all(&self) -> std::io::Result<Vec<LinkRecord>>;

    /// Resolve a custodial pubkey to its ROOT pubkey — the LATEST link for that custodial wins
    /// (a rebind supersedes). `None` if the custodial key was never linked (it is then its own
    /// identity, unchanged — resolution is additive, never breaks the unlinked case).
    fn resolve_root(&self, custodial_pubkey_hex: &str) -> std::io::Result<Option<String>> {
        let mut latest: Option<(u64, String)> = None;
        for r in self.all()? {
            if r.custodial_pubkey_hex
                .eq_ignore_ascii_case(custodial_pubkey_hex)
            {
                match &latest {
                    Some((t, _)) if *t >= r.verified_at => {}
                    _ => latest = Some((r.verified_at, r.root_pubkey_hex)),
                }
            }
        }
        Ok(latest.map(|(_, root)| root))
    }

    /// Every platform link currently attributed to a root key (latest per (platform, uid)).
    fn platforms_for_root(&self, root_pubkey_hex: &str) -> std::io::Result<Vec<LinkRecord>> {
        let mut out: std::collections::HashMap<(String, String), LinkRecord> =
            std::collections::HashMap::new();
        for r in self.all()? {
            if r.root_pubkey_hex.eq_ignore_ascii_case(root_pubkey_hex) {
                let k = (r.platform.clone(), r.platform_uid.clone());
                match out.get(&k) {
                    Some(prev) if prev.verified_at >= r.verified_at => {}
                    _ => {
                        out.insert(k, r);
                    }
                }
            }
        }
        Ok(out.into_values().collect())
    }
}

/// The cross-process shared store: an append-only TSV file. Point all frontends at ONE path.
pub struct FileLinkStore {
    path: PathBuf,
}

impl FileLinkStore {
    /// Open (creating the parent dir + file on first write) a store at `path`.
    pub fn new(path: impl AsRef<Path>) -> Self {
        FileLinkStore {
            path: path.as_ref().to_path_buf(),
        }
    }
}

impl LinkStore for FileLinkStore {
    fn record(&mut self, rec: &LinkRecord) -> std::io::Result<()> {
        let line = rec.to_line().ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "link record field carries a TAB/NEWLINE delimiter",
            )
        })?;
        if let Some(parent) = self.path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)?;
        writeln!(f, "{line}")
    }

    fn all(&self) -> std::io::Result<Vec<LinkRecord>> {
        let f = match std::fs::File::open(&self.path) {
            Ok(f) => f,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
            Err(e) => return Err(e),
        };
        let mut out = Vec::new();
        for line in BufReader::new(f).lines() {
            let line = line?;
            if line.trim().is_empty() {
                continue;
            }
            if let Some(r) = LinkRecord::from_line(&line) {
                out.push(r);
            }
        }
        Ok(out)
    }
}

/// A memory-backed store — for tests and single-process callers.
#[derive(Default)]
pub struct InMemoryLinkStore {
    records: Vec<LinkRecord>,
}

impl LinkStore for InMemoryLinkStore {
    fn record(&mut self, rec: &LinkRecord) -> std::io::Result<()> {
        self.records.push(rec.clone());
        Ok(())
    }
    fn all(&self) -> std::io::Result<Vec<LinkRecord>> {
        Ok(self.records.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rec(root: &str, plat: &str, uid: &str, cust: &str, at: u64) -> LinkRecord {
        LinkRecord {
            root_pubkey_hex: root.into(),
            platform: plat.into(),
            platform_uid: uid.into(),
            custodial_pubkey_hex: cust.into(),
            verified_at: at,
        }
    }

    /// THE payoff: a Discord custodial key and a Telegram custodial key, both linked to the SAME
    /// root K, resolve to ONE root — one human across platforms.
    #[test]
    fn two_platforms_linked_to_one_root_resolve_to_the_same_human() {
        let mut s = InMemoryLinkStore::default();
        s.record(&rec("K", "discord", "111", "custD", 100)).unwrap();
        s.record(&rec("K", "telegram", "222", "custT", 101))
            .unwrap();
        assert_eq!(s.resolve_root("custD").unwrap(), Some("K".into()));
        assert_eq!(s.resolve_root("custT").unwrap(), Some("K".into()));
        assert_eq!(s.platforms_for_root("K").unwrap().len(), 2);
    }

    /// An unlinked custodial key is its own identity — resolution is additive, never breaks the
    /// common case.
    #[test]
    fn an_unlinked_key_resolves_to_none() {
        let s = InMemoryLinkStore::default();
        assert_eq!(s.resolve_root("stranger").unwrap(), None);
    }

    /// A rebind supersedes: the LATEST link for a custodial key wins.
    #[test]
    fn the_latest_link_wins() {
        let mut s = InMemoryLinkStore::default();
        s.record(&rec("K1", "discord", "111", "custD", 100))
            .unwrap();
        s.record(&rec("K2", "discord", "111", "custD", 200))
            .unwrap();
        assert_eq!(s.resolve_root("custD").unwrap(), Some("K2".into()));
    }

    /// The file store round-trips + survives a reopen (durable, cross-process shape).
    #[test]
    fn file_store_persists_and_reopens() {
        let dir = std::env::temp_dir().join(format!("dregg-link-test-{}", std::process::id()));
        let path = dir.join("links.tsv");
        let _ = std::fs::remove_file(&path);
        {
            let mut s = FileLinkStore::new(&path);
            s.record(&rec("K", "discord", "111", "custD", 100)).unwrap();
            s.record(&rec("K", "telegram", "222", "custT", 101))
                .unwrap();
        }
        let s2 = FileLinkStore::new(&path); // a fresh handle = a different "process"
        assert_eq!(s2.resolve_root("custD").unwrap(), Some("K".into()));
        assert_eq!(s2.resolve_root("custT").unwrap(), Some("K".into()));
        assert_eq!(s2.all().unwrap().len(), 2);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_delimiter_in_a_field_is_refused_by_the_encoder() {
        assert!(rec("K", "dis\tcord", "1", "c", 1).to_line().is_none());
        assert!(rec("K", "discord", "1", "c", 1).to_line().is_some());
    }
}
