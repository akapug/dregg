//! **Cap-gate the CONTENT PROVIDER.** The confined Android app's `content://` access
//! reforged from ambient cross-app data-sharing into a cap-bounded, spotter-resolved,
//! receipted grant — `GRAPHIDEOS.md §1` (the content-providers row) made real, in the
//! same shape as the proven [`crate::intentgate`] / [`crate::netgate`] / [`crate::input`]
//! gates.
//!
//! # What Android does (the ambient mechanism deos replaces)
//!
//! In stock Android an app reads or writes shared data through a `content://authority/path`
//! URI handed to the framework's **`ContentResolver`**. The resolver matches the URI's
//! **authority** against **every installed app's `<provider android:authorities=…>`** and
//! routes the `query`/`insert`/`update`/`delete` into the owning **`ContentProvider`** — a
//! privileged cross-app data conduit. This is **ambient authority**: the originating app
//! names an authority string, reaches the *whole device's* provider set, and a provider
//! `android:exported="true"` (or a remembered `grantUriPermission`) is an invisible standing
//! grant over its data.
//!
//! # What graphideOS does (the cap-bounded reforge)
//!
//! `GRAPHIDEOS.md §1`: *"sharing data = handing a (attenuated) cap to a cell, or sending a
//! `MembraneEnvelope`; a read is authority-checked, a write is a receipted turn; no ambient
//! provider."* This module is that:
//!
//! 1. **Resolution is over the cap-reachable provider neighborhood, not the device.** The
//!    [`ContentResolver`] (the deos one — decidedly NOT the framework's global
//!    `ContentResolver`) holds exactly the provider cells the android-cell was *granted* a
//!    cap to reach. A `content://` URI whose authority matches no cap-reachable provider is
//!    [`ContentDecision::RefusedNoProvider`]: **the app cannot read a provider it was never
//!    handed a cap to.**
//! 2. **A read is a cap-bounded authorized query; a write is a receipted turn.** Exactly
//!    one cap-reachable provider answers the authority ⟹ [`ContentDecision::Granted`] naming
//!    that one provider cell + the access — a cap-bounded hand to the data, not an ambient
//!    `ContentResolver` route.
//! 3. **Write authority is the attenuation tooth.** A *write* against a provider the holder
//!    was granted only **read** ([`ProviderGrant::ReadOnly`]) is
//!    [`ContentDecision::RefusedReadOnly`] — a read cap does not amplify to a write (the
//!    `granted ⊆ held` lattice, content-side). AOSP's `android:readPermission` /
//!    `android:writePermission` split becomes a cap attenuation.
//! 4. **Ambiguity is an explicit chooser, never a silent route.** Two cap-reachable
//!    providers answering one authority ⟹ [`ContentDecision::Ambiguous`] (the powerbox-style
//!    ceremony). AOSP forbids duplicate device-wide authorities; a cap-neighborhood can still
//!    hold two granted providers claiming one authority, and deos refuses to silently pick.
//!
//! Every decision leaves a content-addressed [`ContentReceipt`], so the android-cell's
//! `content://` traffic is auditable end to end exactly like the intent / net / input
//! receipts.
//!
//! # The depth (honest, like the intent + net + input gates')
//!
//! This is the **resolution-and-authority** layer: the gate decides, against the held grant
//! + the granted provider set, whether (and how) a `content://` access may proceed, and
//!   records it. The **cross-domain** variant — a share that crosses a confinement border
//!   becomes a `MembraneEnvelope` (`deos-matrix/src/membrane.rs`'s frustum-culled, cap-bounded
//!   world-fork) rather than an in-graph cap hand — and the in-runtime interposition of the
//!   actual binder `ContentResolver` transaction are the same not-yet-claimed depth the intent
//!   gate names. What IS real today: the authority-resolution algebra + the read/write
//!   attenuation teeth + the receipt, testable on any node with no device.

use dregg_firmament::CellId;

/// A parsed `content://authority/path` URI — the unit the framework's `ContentResolver`
/// routes on. graphideOS routes on the **authority** (the provider key) exactly as AOSP
/// does; the `path` is carried for the receipt + the eventual in-provider sub-grant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContentUri {
    /// The provider authority, e.g. `com.android.contacts` or `media`. Lower-cased: AOSP
    /// authorities are case-insensitive for matching.
    pub authority: String,
    /// The path under the authority, e.g. `contacts/12`. May be empty (the authority root).
    pub path: String,
}

impl ContentUri {
    /// Parse a `content://authority/path` URI. Returns `None` for a non-`content` scheme or
    /// a missing authority — those carry no provider to resolve against.
    pub fn parse(uri: &str) -> Option<Self> {
        let rest = uri.strip_prefix("content://")?;
        let (authority, path) = match rest.split_once('/') {
            Some((a, p)) => (a, p),
            None => (rest, ""),
        };
        if authority.is_empty() {
            return None;
        }
        Some(ContentUri {
            authority: authority.to_ascii_lowercase(),
            path: path.to_string(),
        })
    }

    /// A short tag for the receipt digest + status line.
    fn tag(&self) -> String {
        if self.path.is_empty() {
            format!("content://{}", self.authority)
        } else {
            format!("content://{}/{}", self.authority, self.path)
        }
    }
}

/// The access an app requests against a `content://` URI. AOSP's `query` is a **read**;
/// `insert`/`update`/`delete` are all **writes** (they mutate the provider's data). The
/// read/write split is exactly the grant attenuation this gate enforces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContentAccess {
    /// A `query` — an authorized read of the provider's data.
    Read,
    /// An `insert` / `update` / `delete` — a mutation, which in deos is a **receipted turn**
    /// against the provider cell's substance (and needs a write-granting cap).
    Write,
}

impl ContentAccess {
    fn tag(&self) -> &'static str {
        match self {
            ContentAccess::Read => "read",
            ContentAccess::Write => "write",
        }
    }
}

/// What a holder was granted over a provider — the deos form of AOSP's
/// `android:readPermission` / `android:writePermission` split, expressed as a cap
/// attenuation. A [`ReadOnly`](Self::ReadOnly) grant cannot amplify to a write.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProviderGrant {
    /// The holder may `query` (read) the provider only — a write is refused (the
    /// attenuation tooth).
    ReadOnly,
    /// The holder may read AND write (a write commits as a receipted turn against the
    /// provider cell).
    ReadWrite,
}

impl ProviderGrant {
    /// Does this grant admit `access`? `ReadOnly` admits only [`ContentAccess::Read`].
    pub fn admits(&self, access: ContentAccess) -> bool {
        match (self, access) {
            (ProviderGrant::ReadWrite, _) => true,
            (ProviderGrant::ReadOnly, ContentAccess::Read) => true,
            (ProviderGrant::ReadOnly, ContentAccess::Write) => false,
        }
    }
}

/// A cap-reachable content provider in the android-cell's bounded neighborhood — the deos
/// form of an AOSP `<provider android:authorities=…>`. The data is the provider **cell**'s
/// substance/subgraph; a read is authority-checked, a write is a receipted turn against it.
/// Held by the [`ContentResolver`] only for providers the android-cell holds a cap to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContentProvider {
    /// The provider cell — the named capability holder whose substance the data is.
    pub cell: CellId,
    /// The `content://` authority this provider answers (lower-cased for matching).
    pub authority: String,
    /// A short human label for the chooser / status line (e.g. "Contacts").
    pub label: String,
    /// The access the holder was granted over this provider (the cap attenuation).
    pub grant: ProviderGrant,
}

impl ContentProvider {
    /// A provider answering one authority with a given grant.
    pub fn new(
        cell: CellId,
        authority: impl Into<String>,
        label: impl Into<String>,
        grant: ProviderGrant,
    ) -> Self {
        ContentProvider {
            cell,
            authority: authority.into().to_ascii_lowercase(),
            label: label.into(),
            grant,
        }
    }

    /// Does this provider answer `uri`'s authority? (The AOSP provider-match key.)
    pub fn answers(&self, uri: &ContentUri) -> bool {
        self.authority == uri.authority
    }
}

/// The four distinguishable ends a `content://` access can reach — the content-side analogue
/// of [`crate::intentgate::IntentDecision`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContentDecision {
    /// Exactly one cap-reachable provider answered the authority AND the grant admits the
    /// requested access: a cap-bounded hand to the data (a read = an authorized query; a
    /// write = a receipted turn against the provider cell).
    Granted {
        provider: CellId,
        label: String,
        access: ContentAccess,
    },
    /// Two+ cap-reachable providers answered one authority: deos refuses to silently route
    /// and surfaces the candidates for an explicit chooser.
    Ambiguous { candidates: Vec<(CellId, String)> },
    /// NO cap-reachable provider answered this authority — the no-ambient-`ContentResolver`
    /// property: the app cannot reach a provider it was never granted a cap to.
    RefusedNoProvider { authority: String },
    /// A WRITE against a provider the holder was granted only READ — refused by the cap
    /// attenuation (a read cap does not amplify to a write).
    RefusedReadOnly { provider: CellId, authority: String },
}

impl ContentDecision {
    pub fn granted(&self) -> bool {
        matches!(self, ContentDecision::Granted { .. })
    }
    pub fn refused_no_provider(&self) -> bool {
        matches!(self, ContentDecision::RefusedNoProvider { .. })
    }
    pub fn refused_read_only(&self) -> bool {
        matches!(self, ContentDecision::RefusedReadOnly { .. })
    }
    pub fn ambiguous(&self) -> bool {
        matches!(self, ContentDecision::Ambiguous { .. })
    }
}

/// **The receipt left by a gated content access.** Every decision produces one, so the
/// android-cell's `content://` traffic is auditable end to end exactly like the intent /
/// egress / input receipts. Content-addressed:
/// `decision_digest = blake3(cell? ‖ uri_tag ‖ access ‖ outcome ‖ provider?)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContentReceipt {
    /// The android-cell whose held cap + granted provider set decided this access.
    pub cell: Option<CellId>,
    /// The URI the confined app accessed.
    pub uri: ContentUri,
    /// The access the app requested.
    pub access: ContentAccess,
    /// The decision reached.
    pub decision: ContentDecision,
    /// `blake3(…)[..32]` — the content-addressed witness a verifier reconstructs.
    pub decision_digest: [u8; 32],
}

impl ContentReceipt {
    fn digest(
        cell: Option<CellId>,
        uri: &ContentUri,
        access: ContentAccess,
        decision: &ContentDecision,
    ) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        if let Some(c) = cell {
            h.update(b"\x01cell");
            h.update(c.as_bytes());
        }
        h.update(uri.tag().as_bytes());
        h.update(b"\x00");
        h.update(access.tag().as_bytes());
        match decision {
            ContentDecision::Granted {
                provider, access, ..
            } => {
                h.update(b"\x01granted");
                h.update(provider.as_bytes());
                h.update(access.tag().as_bytes());
            }
            ContentDecision::Ambiguous { candidates } => {
                h.update(b"\x02ambiguous");
                for (c, _) in candidates {
                    h.update(c.as_bytes());
                }
            }
            ContentDecision::RefusedNoProvider { authority } => {
                h.update(b"\x03refused-no-provider");
                h.update(authority.as_bytes());
            }
            ContentDecision::RefusedReadOnly {
                provider,
                authority,
            } => {
                h.update(b"\x04refused-read-only");
                h.update(provider.as_bytes());
                h.update(authority.as_bytes());
            }
        }
        *h.finalize().as_bytes()
    }

    /// A one-line audit truth for the cockpit status line — which end, named exactly.
    pub fn status_line(&self) -> String {
        match &self.decision {
            ContentDecision::Granted { label, access, .. } => format!(
                "android-content: ✔ {} {} → granted over «{label}» as a cap-bounded {} — a named provider cell, not an ambient ContentResolver",
                self.access.tag(),
                self.uri.tag(),
                match access {
                    ContentAccess::Read => "query",
                    ContentAccess::Write => "receipted turn",
                }
            ),
            ContentDecision::Ambiguous { candidates } => format!(
                "android-content: ◈ {} matches {} cap-reachable providers — surfaced for an explicit chooser (no silent route)",
                self.uri.tag(),
                candidates.len()
            ),
            ContentDecision::RefusedNoProvider { authority } => format!(
                "android-content: ✖ {} REFUSED — no cap-reachable provider answers «{authority}» (the app cannot read a provider it was never granted)",
                self.uri.tag()
            ),
            ContentDecision::RefusedReadOnly { authority, .. } => format!(
                "android-content: ✖ write {} REFUSED — the held cap grants only READ over «{authority}» (a read cap does not amplify to a write)",
                self.uri.tag()
            ),
        }
    }
}

/// The cap-gated content resolver for one android-cell — **the spotter over the cell's
/// bounded, cap-reachable provider neighborhood**, NOT the framework's global
/// `ContentResolver`. Holds the granted provider set + the cell it speaks for; holds NO
/// ambient authority — every [`resolve`](Self::resolve) is a pure function of its providers.
pub struct ContentResolver {
    providers: Vec<ContentProvider>,
    cell: Option<CellId>,
}

impl ContentResolver {
    /// Build a resolver over the granted provider neighborhood and the cell it speaks for.
    pub fn new(providers: impl IntoIterator<Item = ContentProvider>, cell: Option<CellId>) -> Self {
        ContentResolver {
            providers: providers.into_iter().collect(),
            cell,
        }
    }

    /// The granted provider neighborhood (the cap-reachable set the spotter ranges over).
    pub fn providers(&self) -> &[ContentProvider] {
        &self.providers
    }

    /// **THE CONTENT GATE.** The confined app accessed `uri` with `access`. Decide against
    /// the granted provider set + its grants, and return the decision AND its
    /// [`ContentReceipt`].
    ///
    /// Order of teeth (fail-closed):
    /// 1. **Spotter over the cap-reachable set** — match `uri`'s authority against the
    ///    granted providers. Zero ⟹ [`ContentDecision::RefusedNoProvider`] (no ambient
    ///    `ContentResolver`); two+ ⟹ [`ContentDecision::Ambiguous`] (the explicit chooser).
    /// 2. **The grant attenuation** — one match, but a WRITE against a `ReadOnly` grant ⟹
    ///    [`ContentDecision::RefusedReadOnly`]. Otherwise [`ContentDecision::Granted`].
    pub fn resolve(&self, uri: &ContentUri, access: ContentAccess) -> ContentReceipt {
        let mut matches: Vec<&ContentProvider> =
            self.providers.iter().filter(|p| p.answers(uri)).collect();
        matches.sort_by(|a, b| a.cell.as_bytes().cmp(b.cell.as_bytes()));
        matches.dedup_by(|a, b| a.cell == b.cell);

        let decision = match matches.len() {
            0 => ContentDecision::RefusedNoProvider {
                authority: uri.authority.clone(),
            },
            1 => {
                let p = matches[0];
                if p.grant.admits(access) {
                    ContentDecision::Granted {
                        provider: p.cell,
                        label: p.label.clone(),
                        access,
                    }
                } else {
                    ContentDecision::RefusedReadOnly {
                        provider: p.cell,
                        authority: uri.authority.clone(),
                    }
                }
            }
            _ => ContentDecision::Ambiguous {
                candidates: matches.iter().map(|p| (p.cell, p.label.clone())).collect(),
            },
        };
        self.receipt(uri, access, decision)
    }

    fn receipt(
        &self,
        uri: &ContentUri,
        access: ContentAccess,
        decision: ContentDecision,
    ) -> ContentReceipt {
        let decision_digest = ContentReceipt::digest(self.cell, uri, access, &decision);
        ContentReceipt {
            cell: self.cell,
            uri: uri.clone(),
            access,
            decision,
            decision_digest,
        }
    }
}

/// The authorities a provider-bearing app would publish — a small representative set of the
/// AOSP system authorities, plus a `Custom` long-tail, mirroring [`crate::AndroidPermission`]'s
/// shape. Used by the install↔content bridge ([`crate::apps`]) to register an installed app's
/// `<provider>` authorities as cap-reachable providers.
pub mod authorities {
    /// `com.android.contacts` — the contacts provider.
    pub const CONTACTS: &str = "com.android.contacts";
    /// `media` — the `MediaStore` provider.
    pub const MEDIA: &str = "media";
    /// `com.android.calendar` — the calendar provider.
    pub const CALENDAR: &str = "com.android.calendar";
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_firmament::cell_seed;

    fn contacts_provider() -> ContentProvider {
        ContentProvider::new(
            cell_seed(0x41),
            "com.android.contacts",
            "Contacts",
            ProviderGrant::ReadOnly,
        )
    }
    fn notes_provider() -> ContentProvider {
        ContentProvider::new(
            cell_seed(0x42),
            "com.example.notes",
            "Notes",
            ProviderGrant::ReadWrite,
        )
    }

    #[test]
    fn uri_parse_is_faithful() {
        let u = ContentUri::parse("content://com.android.Contacts/contacts/12").unwrap();
        assert_eq!(u.authority, "com.android.contacts"); // lower-cased
        assert_eq!(u.path, "contacts/12");

        let root = ContentUri::parse("content://media").unwrap();
        assert_eq!(root.authority, "media");
        assert_eq!(root.path, "");

        // A non-content scheme / empty authority carries no provider to resolve.
        assert!(ContentUri::parse("https://example.com").is_none());
        assert!(ContentUri::parse("content:///x").is_none());
    }

    /// **THE LOAD-BEARING TEST: a `content://` whose authority no cap-reachable provider
    /// answers is refused — the app cannot read a provider it was never granted.**
    #[test]
    fn unreachable_authority_is_refused() {
        let me = cell_seed(9);
        // The neighborhood holds contacts only — no media provider was granted.
        let resolver = ContentResolver::new([contacts_provider()], Some(me));
        let uri = ContentUri::parse("content://media/external/images").unwrap();
        let receipt = resolver.resolve(&uri, ContentAccess::Read);

        assert!(
            receipt.decision.refused_no_provider(),
            "media has no cap-reachable provider (no ambient ContentResolver)"
        );
        assert_eq!(receipt.cell, Some(me));
        assert!(receipt.status_line().contains("never granted"));
        assert_eq!(
            receipt.decision_digest,
            ContentReceipt::digest(Some(me), &uri, ContentAccess::Read, &receipt.decision)
        );
    }

    /// Exactly one cap-reachable provider answers ⟹ a cap-bounded grant to that one cell.
    #[test]
    fn single_provider_grants_a_named_cell() {
        let me = cell_seed(9);
        let resolver = ContentResolver::new([contacts_provider(), notes_provider()], Some(me));
        let uri = ContentUri::parse("content://com.android.contacts/people").unwrap();
        let receipt = resolver.resolve(&uri, ContentAccess::Read);
        match &receipt.decision {
            ContentDecision::Granted {
                provider,
                label,
                access,
            } => {
                assert_eq!(*provider, cell_seed(0x41));
                assert_eq!(label, "Contacts");
                assert_eq!(*access, ContentAccess::Read);
            }
            other => panic!("expected Granted, got {other:?}"),
        }
        assert!(receipt.status_line().contains("cap-bounded query"));
    }

    /// **THE ATTENUATION TOOTH: a WRITE against a ReadOnly grant is refused — a read cap
    /// does not amplify to a write.**
    #[test]
    fn write_against_read_only_grant_is_refused() {
        let me = cell_seed(9);
        let resolver = ContentResolver::new([contacts_provider()], Some(me));
        let uri = ContentUri::parse("content://com.android.contacts/people/3").unwrap();

        // A read is granted...
        assert!(resolver
            .resolve(&uri, ContentAccess::Read)
            .decision
            .granted());
        // ...but a write against the read-only grant is refused (no amplification).
        let w = resolver.resolve(&uri, ContentAccess::Write);
        assert!(w.decision.refused_read_only());
        assert!(w.status_line().contains("does not amplify to a write"));
        assert_eq!(
            w.decision,
            ContentDecision::RefusedReadOnly {
                provider: cell_seed(0x41),
                authority: "com.android.contacts".into()
            }
        );
    }

    /// A ReadWrite grant admits a write (which commits as a receipted turn).
    #[test]
    fn write_against_read_write_grant_is_a_receipted_turn() {
        let me = cell_seed(9);
        let resolver = ContentResolver::new([notes_provider()], Some(me));
        let uri = ContentUri::parse("content://com.example.notes/n/1").unwrap();
        let w = resolver.resolve(&uri, ContentAccess::Write);
        assert!(w.decision.granted());
        assert!(w.status_line().contains("receipted turn"));
    }

    /// Two cap-reachable providers answering one authority ⟹ an EXPLICIT chooser, never a
    /// silent route.
    #[test]
    fn duplicate_authority_surfaces_a_chooser() {
        let me = cell_seed(9);
        let other_contacts = ContentProvider::new(
            cell_seed(0x43),
            "com.android.contacts",
            "Contacts (work)",
            ProviderGrant::ReadOnly,
        );
        let resolver = ContentResolver::new([contacts_provider(), other_contacts], Some(me));
        let uri = ContentUri::parse("content://com.android.contacts/people").unwrap();
        let r = resolver.resolve(&uri, ContentAccess::Read);
        match &r.decision {
            ContentDecision::Ambiguous { candidates } => assert_eq!(candidates.len(), 2),
            other => panic!("expected Ambiguous, got {other:?}"),
        }
        assert!(r.status_line().contains("explicit chooser"));
    }
}
