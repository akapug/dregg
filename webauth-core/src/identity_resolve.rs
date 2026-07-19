//! # `identity_resolve` — ONE join key, loaded ONCE, for every board that shows a human.
//!
//! [`link_registry`](crate::link_registry) can already answer "which human is this custodial key?".
//! What was missing is the thing that makes "one you everywhere" TRUE on the surfaces people
//! actually look at: a resolver a **board render** can use.
//!
//! Three things this fixes, all of which were real:
//!
//! 1. **ONE join key.** [`LinkStore::resolve_root_account`](crate::link_registry::LinkStore::resolve_root_account)
//!    — the rotation-ready account id that is byte-identical to the future identity CELL's id — had
//!    ZERO callers; every resolution site used the raw root pubkey instead, so the shallow TSV and
//!    the coming cell would have keyed differently. [`RootResolver`] resolves to the ACCOUNT ID
//!    everywhere, so both agree by construction.
//! 2. **Loaded ONCE per render.** The old sites constructed a `FileLinkStore` and rescanned the
//!    whole TSV *per row*. [`RootResolver::load`] scans once and answers from an index.
//! 3. **Truncated identities still resolve.** Some boards store a SHORTENED identity (The Descent's
//!    Discord board stores a 12-hex prefix as its completion PK — see [`RootResolver::resolve`]),
//!    so a full-key lookup could never match and those boards resolved nothing at all. The resolver
//!    matches a stored prefix against the linked custodial keys, and — fail-closed — refuses an
//!    AMBIGUOUS prefix (two linked keys sharing it) rather than merging two humans into one.
//!
//! ## What this is NOT
//!
//! A DISPLAY / GROUPING concern only, exactly as `resolve_display_root` always was. Attribution is
//! untouched: a turn, its proof, and its receipt are still signed by and attributed to the custodial
//! key. An UNLINKED key resolves to ITSELF, so a board with no links rendered through this resolver
//! is byte-identical to one rendered without it.

use std::collections::HashMap;

use crate::link_registry::{FileLinkStore, LinkStore, account_id_of_root, default_store_path};

/// A resolver over ONE snapshot of the link store: custodial pubkey (full, or a stored prefix) →
/// the human's stable ACCOUNT ID. Build one per board render and resolve every row against it.
#[derive(Debug, Default, Clone)]
pub struct RootResolver {
    /// Lowercased full custodial pubkey hex → the account id of the root it last linked to.
    by_custodial: HashMap<String, String>,
}

impl RootResolver {
    /// **Load a snapshot from the shared link store** (`$DREGG_LINK_DIR/links.tsv`) — ONE file scan
    /// for a whole board render. A missing / unreadable store yields an EMPTY resolver, in which
    /// every key resolves to itself: an unavailable link file degrades a board to its un-resolved
    /// rendering, never to an error.
    pub fn load() -> RootResolver {
        RootResolver::from_store(&FileLinkStore::new(default_store_path()))
    }

    /// Load a snapshot from an explicit store (a test's [`InMemoryLinkStore`], a non-default path).
    ///
    /// [`InMemoryLinkStore`]: crate::link_registry::InMemoryLinkStore
    pub fn from_store(store: &dyn LinkStore) -> RootResolver {
        let mut latest: HashMap<String, (u64, String)> = HashMap::new();
        for r in store.all().unwrap_or_default() {
            let custodial = r.custodial_pubkey_hex.to_ascii_lowercase();
            match latest.get(&custodial) {
                // strict `>`: on a same-second tie the LATER file-order record wins, matching
                // `LinkStore::resolve_root`'s rebind tie-break exactly.
                Some((t, _)) if *t > r.verified_at => {}
                _ => {
                    latest.insert(custodial, (r.verified_at, r.root_pubkey_hex));
                }
            }
        }
        let by_custodial = latest
            .into_iter()
            .filter_map(|(custodial, (_, root))| {
                // THE ONE JOIN KEY: the rotation-ready account id (byte-identical to the identity
                // cell's id), never the raw root pubkey. A malformed root hex drops the link rather
                // than resolving to something the cell will not agree with.
                account_id_of_root(&root).map(|acct| (custodial, acct))
            })
            .collect();
        RootResolver { by_custodial }
    }

    /// How many custodial keys this snapshot can resolve (0 = every row renders un-resolved).
    pub fn len(&self) -> usize {
        self.by_custodial.len()
    }

    /// Whether the snapshot holds no links at all.
    pub fn is_empty(&self) -> bool {
        self.by_custodial.is_empty()
    }

    /// **Resolve one board identity to its human's account id.**
    ///
    /// `stored` is whatever the board keyed on: the FULL custodial pubkey hex (the crown board, the
    /// web descent board), or a stored PREFIX of it (The Descent's Discord board stores 12 hex
    /// chars). Resolution is:
    ///
    /// - an exact match on a linked custodial key ⇒ that human's account id;
    /// - else, if `stored` is a hex-ish prefix that matches EXACTLY ONE linked custodial key ⇒ that
    ///   human's account id;
    /// - else — unlinked, or an AMBIGUOUS prefix (two linked keys share it) — `stored` itself.
    ///
    /// The ambiguity refusal is the fail-closed edge: merging two humans because their stored
    /// prefixes collide would be worse than leaving both un-resolved, so the collision resolves to
    /// nothing and both rows render as they do today.
    pub fn resolve(&self, stored: &str) -> String {
        self.resolve_opt(stored)
            .unwrap_or_else(|| stored.to_string())
    }

    /// [`resolve`](Self::resolve), but `None` when the identity is unlinked / ambiguous rather than
    /// falling back to the stored label. Use this when a caller must distinguish "this row IS a
    /// known human" from "this row is its own identity".
    pub fn resolve_opt(&self, stored: &str) -> Option<String> {
        let needle = stored.trim().to_ascii_lowercase();
        if needle.is_empty() {
            return None;
        }
        if let Some(acct) = self.by_custodial.get(&needle) {
            return Some(acct.clone());
        }
        // A stored PREFIX (a board that truncated the identity for display/PK reasons). Require a
        // UNIQUE match; an ambiguous prefix resolves to nothing.
        let mut hit: Option<&String> = None;
        for (custodial, acct) in &self.by_custodial {
            if custodial.starts_with(&needle) {
                match hit {
                    // Two DISTINCT humans share this prefix — refuse (never merge on a collision).
                    Some(prev) if prev != acct => return None,
                    _ => hit = Some(acct),
                }
            }
        }
        hit.cloned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::link_registry::{InMemoryLinkStore, LinkRecord};

    fn rec(root: &str, plat: &str, uid: &str, cust: &str, at: u64) -> LinkRecord {
        LinkRecord {
            root_pubkey_hex: root.into(),
            platform: plat.into(),
            platform_uid: uid.into(),
            custodial_pubkey_hex: cust.into(),
            verified_at: at,
        }
    }

    fn root(byte: u8) -> String {
        format!("{byte:02x}").repeat(32)
    }

    /// THE PAYOFF: a Discord-you and a Telegram-you (different custodial keys, one root) resolve to
    /// the SAME account id — so a board grouping on this shows ONE human, not two rows.
    #[test]
    fn two_platforms_of_one_human_resolve_to_one_account_id() {
        let k = root(0xaa);
        let mut s = InMemoryLinkStore::default();
        s.record(&rec(&k, "discord", "1", &"11".repeat(32), 100))
            .unwrap();
        s.record(&rec(&k, "telegram", "2", &"22".repeat(32), 101))
            .unwrap();
        let r = RootResolver::from_store(&s);
        let a = r.resolve(&"11".repeat(32));
        let b = r.resolve(&"22".repeat(32));
        assert_eq!(a, b, "one human, one id");
        // It is the ACCOUNT ID (the cell's key), not the raw root pubkey — the whole point of #6.
        assert_eq!(Some(a.clone()), account_id_of_root(&k));
        assert_ne!(a, k, "not the raw root pubkey");
    }

    /// An UNLINKED key is its own identity — resolution stays additive, so an un-linked board is
    /// byte-identical to today.
    #[test]
    fn an_unlinked_key_resolves_to_itself() {
        let r = RootResolver::from_store(&InMemoryLinkStore::default());
        assert!(r.is_empty());
        assert_eq!(r.resolve("stranger"), "stranger");
        assert_eq!(r.resolve_opt("stranger"), None);
    }

    /// A board that stores a TRUNCATED identity (The Descent's 12-hex Discord PK) STILL resolves —
    /// the hole that made #4 unfixable without touching the completion PK.
    #[test]
    fn a_truncated_stored_identity_resolves_by_prefix() {
        let k = root(0xbb);
        let cust = "abcdef0123456789".to_string() + &"00".repeat(24);
        let mut s = InMemoryLinkStore::default();
        s.record(&rec(&k, "discord", "1", &cust, 100)).unwrap();
        let r = RootResolver::from_store(&s);
        let short: String = cust.chars().take(12).collect();
        assert_eq!(
            r.resolve(&short),
            r.resolve(&cust),
            "the 12-hex prefix resolves to the same human as the full key"
        );
    }

    /// FAIL-CLOSED on an ambiguous prefix: two DIFFERENT humans whose custodial keys share the
    /// stored prefix resolve to NOTHING rather than being merged into one row.
    #[test]
    fn an_ambiguous_prefix_refuses_rather_than_merging_two_humans() {
        let mut s = InMemoryLinkStore::default();
        s.record(&rec(
            &root(0xcc),
            "discord",
            "1",
            &("aaaaaaaaaaaa".to_string() + &"11".repeat(26)),
            100,
        ))
        .unwrap();
        s.record(&rec(
            &root(0xdd),
            "telegram",
            "2",
            &("aaaaaaaaaaaa".to_string() + &"22".repeat(26)),
            101,
        ))
        .unwrap();
        let r = RootResolver::from_store(&s);
        assert_eq!(r.resolve_opt("aaaaaaaaaaaa"), None, "ambiguous ⇒ no merge");
        assert_eq!(r.resolve("aaaaaaaaaaaa"), "aaaaaaaaaaaa");
        // NON-VACUOUS: each FULL key still resolves, to two DIFFERENT humans.
        let a = r.resolve(&("aaaaaaaaaaaa".to_string() + &"11".repeat(26)));
        let b = r.resolve(&("aaaaaaaaaaaa".to_string() + &"22".repeat(26)));
        assert_ne!(a, b);
    }

    /// A REBIND supersedes (latest link wins), matching `LinkStore::resolve_root`.
    #[test]
    fn a_rebind_supersedes() {
        let cust = "33".repeat(32);
        let mut s = InMemoryLinkStore::default();
        s.record(&rec(&root(0x01), "discord", "1", &cust, 100))
            .unwrap();
        s.record(&rec(&root(0x02), "discord", "1", &cust, 200))
            .unwrap();
        let r = RootResolver::from_store(&s);
        assert_eq!(r.resolve(&cust), account_id_of_root(&root(0x02)).unwrap());
    }

    /// The snapshot agrees with the per-row `LinkStore::resolve_root_account` it replaces — the
    /// cross-check that the ONE-scan index is not a re-implementation that drifted.
    #[test]
    fn the_snapshot_agrees_with_resolve_root_account_per_row() {
        let mut s = InMemoryLinkStore::default();
        let keys: Vec<String> = (0u8..6)
            .map(|i| format!("{:02x}", i + 0x40).repeat(32))
            .collect();
        for (i, cust) in keys.iter().enumerate() {
            s.record(&rec(
                &root(0x50 + (i as u8 % 3)),
                "discord",
                "1",
                cust,
                100 + i as u64,
            ))
            .unwrap();
        }
        let r = RootResolver::from_store(&s);
        for cust in &keys {
            assert_eq!(
                Some(r.resolve(cust)),
                s.resolve_root_account(cust).unwrap(),
                "the loaded-once index matches the per-row seam for {cust}"
            );
        }
    }
}
