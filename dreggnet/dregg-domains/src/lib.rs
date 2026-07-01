//! `dregg-domains` — BYO custom domains for DreggNet hosting: **a domain binding is a cell.**
//!
//! Where [`dreggnet_webapp::hosting`] hosts a minisite at `<name>.example.com`
//! (the wildcard path — a site IS a cell), this module lets an owner point *their
//! own* domain (`blog.example.com`) at a published site cell, with the standard
//! ACME-style proof-of-control before any traffic — or any certificate — is served.
//!
//! ```text
//!   BIND (cap-gated)              CHALLENGE                 VERIFY            ROUTE / CERT
//!   ───────────────────          ─────────────────         ──────────        ─────────────
//!   DomainCap domain-bind/<d>     _dregg-verify.<d> TXT     a DNS lookup      gateway Host → site
//!     └─ DomainRegistry::bind       = <nonce>                proves control     ask → 200 (verified)
//!          DomainBinding              OR  <d> CNAME           → Verified
//!          { domain, site,                <site>.example.com
//!            owner, Pending }
//! ```
//!
//! ## A domain binding is a cell (the model)
//!
//! A [`DomainBinding`] is a dregg cell, cap-gated and receipted exactly like a
//! [`SiteCell`](dreggnet_webapp::hosting::SiteCell): its committed state holds the
//! **custom domain**, the **bound site** (the `<name>` whose `<name>.example.com`
//! cell serves the bytes), the **owner** (the binding cap holder — so *who bound
//! what* is provable), and a **verification state**. Binding is a *turn* gated by a
//! [`DomainCap`] (`domain-bind/<domain>` only authorizes binding that domain) and
//! leaving a [`BindReceipt`]. The verification turn records *who proved control,
//! when* ([`DomainBinding::verified_seq`]) — re-witnessable, not a server flag.
//!
//! ## Verification — challenge then check (the standard DNS proof)
//!
//! Binding issues a [`DnsChallenge`] the owner satisfies in their DNS:
//!
//! - **TXT** (the default): publish `_dregg-verify.<domain>` = the binding's nonce
//!   ([`DomainBinding::challenge`]). Control of the domain's DNS proves control of
//!   the domain.
//! - **CNAME**: point `<domain>` at `<site>.example.com`. The CNAME both proves
//!   control *and* is the record that actually routes traffic at the edge.
//!
//! [`DomainRegistry::verify`] resolves the record through a [`DnsResolver`] and
//! flips the binding to [`VerificationState::Verified`] iff the record proves
//! control. The resolver is a trait so the check is driven by a real DNS client in
//! production and a deterministic [`MockDns`] in tests (and never mints a cert nor
//! routes a byte for an unverified — i.e. squatted — domain).
//!
//! ## The gateway tie-in (resolution + the on-demand-TLS ask)
//!
//! [`DomainRegistry::site_for_host`] maps an inbound custom `Host` → its bound site
//! name *only when verified*, the extension of `<name>.example.com` host resolution
//! beyond the wildcard. [`DomainRegistry::is_verified`] is what the gateway's Caddy
//! on-demand-TLS `ask` (`/internal/site-exists`) consults, so a per-domain
//! certificate is minted only for a domain a tenant has *proven* they control.

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use serde::{Deserialize, Serialize};

use dreggnet_umem::{Record, UmemRegistry};
use dreggnet_webapp::hosting::is_valid_name;
use dreggnet_webapp::receipt::{BodyHasher, ReceiptAttestation, ReceiptBody, ReceiptChain};
use dreggnet_webapp::{SiteRegistry, WebRequest, WebResponse};
use dreggnet_webauth::cred::{Credential, PublicKey};
use dreggnet_webauth::grant::cap_context;
use dreggnet_webauth::subject_of;

mod live;
pub use live::LiveDns;

/// The cap-token prefix a domain-binding capability carries: `domain-bind/<domain>`.
/// A holder of `domain-bind/blog.example.com` may bind (only) that domain. This
/// mirrors the `site-host/<name>` publish cap — the binding turn's attenuation.
pub const BIND_CAP_PREFIX: &str = "domain-bind/";

/// The DNS label a TXT challenge is published under: `_dregg-verify.<domain>`.
pub const TXT_CHALLENGE_PREFIX: &str = "_dregg-verify.";

/// The apex custom domains bind *onto* — a binding's site `<name>` serves at
/// `<name>.example.com`, and a CNAME challenge points the custom domain here.
pub const HOSTING_APEX: &str = "example.com";

/// Which DNS record proves control of a custom domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChallengeMethod {
    /// Publish a TXT record at `_dregg-verify.<domain>` equal to the nonce.
    Txt,
    /// Point `<domain>` (CNAME) at `<site>.example.com`.
    Cname,
}

/// Whether a binding has proven control of its domain yet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VerificationState {
    /// Bound, challenge issued, control not yet proven. Not routed; no cert.
    Pending,
    /// Control proven — the binding routes and is eligible for a certificate.
    Verified,
}

/// A **domain binding cell** — the dregg cell backing a custom-domain → site map.
///
/// The committed state: the custom `domain`, the bound `site` (`<name>`, whose
/// `<name>.example.com` site cell serves the content), the `owner` (the binding cap
/// holder), the chosen challenge `method`, the `challenge` nonce, and the
/// verification `state`. On a real dregg node this is a cap-bounded cell whose umem
/// heap holds these fields; here it is the in-process value the [`DomainRegistry`]
/// serves and the bind/verify turns write.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DomainBinding {
    /// The custom domain bound (e.g. `blog.example.com`), lowercased.
    pub domain: String,
    /// The bound site `<name>` — the `<name>.example.com` cell that serves the bytes.
    pub site: String,
    /// The owner cell/agent that bound this domain (the cap holder). Provable: the
    /// bind receipt binds `(domain, site, owner)`.
    pub owner: String,
    /// Which DNS record proves control.
    pub method: ChallengeMethod,
    /// The challenge nonce (the TXT value to publish; carried for both methods so
    /// the record's expected value is re-derivable).
    pub challenge: String,
    /// Whether control has been proven.
    pub state: VerificationState,
    /// The registry-monotonic sequence of the verifying turn (who proved control,
    /// when), `None` while [`VerificationState::Pending`].
    pub verified_seq: Option<u64>,
}

impl DomainBinding {
    /// The DNS record an owner must publish to satisfy this binding's challenge.
    pub fn dns_challenge(&self) -> DnsChallenge {
        match self.method {
            ChallengeMethod::Txt => DnsChallenge {
                record_type: ChallengeMethod::Txt,
                record_name: format!("{TXT_CHALLENGE_PREFIX}{}", self.domain),
                expected_value: self.challenge.clone(),
            },
            ChallengeMethod::Cname => DnsChallenge {
                record_type: ChallengeMethod::Cname,
                record_name: self.domain.clone(),
                expected_value: format!("{}.{HOSTING_APEX}", self.site),
            },
        }
    }

    /// Whether this binding has proven control.
    pub fn is_verified(&self) -> bool {
        self.state == VerificationState::Verified
    }
}

/// A [`DomainBinding`] is a durable record keyed by its custom domain — the unit the
/// [`DomainRegistry`]'s durable backend persists on bind + verify, so a restart
/// reconstructs the bindings (including their Verified state, so routing + the cert
/// ask survive a restart rather than every domain reverting to unproven).
impl Record for DomainBinding {
    fn store_key(&self) -> String {
        self.domain.clone()
    }
}

/// The DNS record that proves control of a custom domain — what the owner publishes
/// and what [`DomainRegistry::verify`] checks for.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DnsChallenge {
    /// TXT or CNAME.
    pub record_type: ChallengeMethod,
    /// The DNS name the record lives at (`_dregg-verify.<domain>` for TXT, the
    /// `<domain>` itself for CNAME).
    pub record_name: String,
    /// The value the record must carry (the nonce for TXT, `<site>.example.com`
    /// for CNAME).
    pub expected_value: String,
}

/// The broad capability the developer account is minted with (`dregg login`) —
/// authority to bind a custom domain. A credential granting `domains` may bind any
/// domain it can DNS-prove control of; the per-domain `domain-bind/<domain>` cap is
/// the attenuated form that confines a delegate to one domain. Either satisfies a
/// bind (see [`DomainRegistry::bind`]).
pub const DOMAINS_CAP: &str = "domains";

/// A capability authorizing a domain binding: a **real dregg credential**
/// (`dga1_…`, an ed25519 caveat-chain) presented for a domain. It is *not* a
/// self-asserted token — [`DomainRegistry::bind`] verifies it offline under the
/// registry's trusted root authority as granting the binding cap for `domain`, and
/// derives the binding's `owner` from the credential's stable subject (so only that
/// owner may later rebind/unbind — no takeover/takedown of a victim's binding).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DomainCap {
    /// The presented dregg credential (`dga1_…`) proving binding authority.
    pub credential: String,
    /// The domain this cap is exercised for (lowercased).
    pub domain: String,
}

impl DomainCap {
    /// A binding cap presenting `credential` for `domain`.
    pub fn new(credential: impl Into<String>, domain: &str) -> DomainCap {
        DomainCap {
            credential: credential.into(),
            domain: domain.trim().to_ascii_lowercase(),
        }
    }

    /// The per-domain cap token a delegate credential may carry to bind exactly
    /// `domain`: `domain-bind/<domain>` (the attenuated authority).
    pub fn cap_token(domain: &str) -> String {
        format!("{BIND_CAP_PREFIX}{}", domain.trim().to_ascii_lowercase())
    }
}

/// Verify `credential` under the trusted `root` as authorizing a bind of `domain`,
/// returning the credential's stable subject (the binding owner) on success.
///
/// Fully offline + fail-closed: the credential must verify (proof-of-possession +
/// the ed25519 chain from `root` + the caveat meet) for **either** the broad
/// [`DOMAINS_CAP`] or the per-domain `domain-bind/<domain>` cap. A self-fabricated /
/// wrong-root / insufficient credential is refused.
fn verify_bind_authority(
    credential: &str,
    root: &PublicKey,
    domain: &str,
) -> Result<String, DomainError> {
    let cred = Credential::decode(credential).map_err(|e| DomainError::CapRefused {
        domain: domain.to_string(),
        reason: format!("credential did not decode: {e}"),
    })?;
    let now = unix_now();
    let mut last_refusal: Option<String> = None;
    for cap in [DOMAINS_CAP.to_string(), DomainCap::cap_token(domain)] {
        match cred.verify(root, &cap_context(&cap, now)) {
            Ok(()) => {
                return subject_of(credential).ok_or_else(|| DomainError::CapRefused {
                    domain: domain.to_string(),
                    reason: "credential verified but yields no subject".to_string(),
                });
            }
            Err(refusal) => last_refusal = Some(refusal.to_string()),
        }
    }
    Err(DomainError::CapRefused {
        domain: domain.to_string(),
        reason: last_refusal
            .unwrap_or_else(|| "credential grants no domain-binding cap".to_string()),
    })
}

/// The verifier's clock (unix seconds) — for the credential's `NotAfter` caveats.
fn unix_now() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// The verifiable record a bind leaves: who bound which domain to which site, under
/// what challenge. The dregg analog is the bind turn's receipt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BindReceipt {
    /// The registry-monotonic sequence of this bind (bind order).
    pub seq: u64,
    /// The custom domain bound.
    pub domain: String,
    /// The site `<name>` it was bound to.
    pub site: String,
    /// The owner (the cap holder) that bound it.
    pub owner: String,
    /// The DNS challenge the owner must satisfy to verify.
    pub challenge: DnsChallenge,
    /// The chained, signed attestation lifting this bind into the receipt
    /// contract (prev-hash link + ed25519 signature). Present when the
    /// [`DomainRegistry`] was given a receipt chain; `None` is the unsigned
    /// default. A bind IS a turn — this is its turn receipt. See [`ReceiptBody`].
    #[serde(default)]
    pub attest: Option<ReceiptAttestation>,
}

impl ReceiptBody for BindReceipt {
    fn body_hash(&self) -> [u8; 32] {
        let mut h = BodyHasher::new(b"bind-receipt-v1");
        h.u64(self.seq)
            .field(self.domain.as_bytes())
            .field(self.site.as_bytes())
            .field(self.owner.as_bytes())
            .u64(match self.challenge.record_type {
                ChallengeMethod::Txt => 0,
                ChallengeMethod::Cname => 1,
            })
            .field(self.challenge.record_name.as_bytes())
            .field(self.challenge.expected_value.as_bytes());
        h.finalize()
    }
    fn seq(&self) -> u64 {
        self.seq
    }
    fn attestation(&self) -> Option<&ReceiptAttestation> {
        self.attest.as_ref()
    }
}

/// Why a domain operation was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DomainError {
    /// The presented credential does not authorize binding `domain` (it did not
    /// decode, did not verify under the trusted root, or grants no binding cap).
    CapRefused { domain: String, reason: String },
    /// A rebind/repoint was attempted by a credential whose subject is not the
    /// existing binding's owner — only the owner may rebind/unbind (no takeover).
    OwnerMismatch { domain: String },
    /// The registry has no trusted root authority configured, so no credential can
    /// be verified — every bind is refused (fail-closed). Construct the registry
    /// with [`DomainRegistry::with_authority`].
    NoAuthority,
    /// `domain` is not a usable custom domain (not an FQDN, a bad label, or it is a
    /// `*.example.com` host — that is the wildcard path, not a custom domain).
    InvalidDomain(String),
    /// `site` is not a valid site `<name>` (the `<name>.example.com` label rules).
    InvalidSite(String),
    /// No binding exists for `domain` (verify/lookup on an unbound domain).
    NotBound(String),
    /// The DNS challenge is not (yet) satisfied — control is unproven.
    ChallengeUnmet { domain: String },
    /// The bind/verify was valid but the durable backend could not persist the
    /// binding (a disk/fsync fault). The operation is refused rather than reported as
    /// durable when it is not — a binding that would vanish on restart is not a
    /// successful bind.
    Persist { domain: String, reason: String },
}

impl std::fmt::Display for DomainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DomainError::CapRefused { domain, reason } => {
                write!(
                    f,
                    "credential does not authorize binding domain `{domain}`: {reason}"
                )
            }
            DomainError::OwnerMismatch { domain } => {
                write!(
                    f,
                    "only the owner of the existing binding for `{domain}` may rebind it"
                )
            }
            DomainError::NoAuthority => {
                write!(
                    f,
                    "no trusted root authority configured — binding is refused (fail-closed)"
                )
            }
            DomainError::InvalidDomain(d) => write!(f, "`{d}` is not a valid custom domain"),
            DomainError::InvalidSite(s) => write!(f, "`{s}` is not a valid site name"),
            DomainError::NotBound(d) => write!(f, "no binding for domain `{d}`"),
            DomainError::ChallengeUnmet { domain } => {
                write!(
                    f,
                    "DNS challenge for `{domain}` is not satisfied (control unproven)"
                )
            }
            DomainError::Persist { domain, reason } => {
                write!(f, "could not persist the binding for `{domain}`: {reason}")
            }
        }
    }
}

impl std::error::Error for DomainError {}

/// A DNS resolver the verify check queries. The production instance is [`LiveDns`]
/// (real TXT/CNAME lookups over a live DNS client); tests use [`MockDns`]. Kept
/// minimal — only the two record types a challenge needs.
pub trait DnsResolver {
    /// The TXT values published at `name` (empty if none / NXDOMAIN).
    fn txt(&self, name: &str) -> Vec<String>;
    /// The CNAME target of `name`, if any. The returned target may carry a trailing
    /// dot (FQDN form); the verify check compares case-insensitively without it.
    fn cname(&self, name: &str) -> Option<String>;
}

/// An in-memory [`DnsResolver`] for tests: a fixed set of TXT and CNAME records.
/// Drives the verify path deterministically with no live DNS.
#[derive(Debug, Default, Clone)]
pub struct MockDns {
    txt: BTreeMap<String, Vec<String>>,
    cname: BTreeMap<String, String>,
}

impl MockDns {
    /// An empty resolver (no records — every lookup misses).
    pub fn new() -> MockDns {
        MockDns::default()
    }

    /// Add a TXT value at `name`.
    pub fn with_txt(mut self, name: &str, value: &str) -> MockDns {
        self.txt
            .entry(name.to_ascii_lowercase())
            .or_default()
            .push(value.to_string());
        self
    }

    /// Add a CNAME target at `name`.
    pub fn with_cname(mut self, name: &str, target: &str) -> MockDns {
        self.cname
            .insert(name.to_ascii_lowercase(), target.to_string());
        self
    }
}

impl DnsResolver for MockDns {
    fn txt(&self, name: &str) -> Vec<String> {
        self.txt
            .get(&name.to_ascii_lowercase())
            .cloned()
            .unwrap_or_default()
    }
    fn cname(&self, name: &str) -> Option<String> {
        self.cname.get(&name.to_ascii_lowercase()).cloned()
    }
}

/// The registry of domain bindings — the custom-domain **control plane**.
///
/// Binding inserts a cap-gated, receipted [`DomainBinding`] (Pending); verify
/// resolves its challenge through a [`DnsResolver`] and flips it to Verified.
/// Resolution ([`DomainRegistry::site_for_host`]) and the cert ask
/// ([`DomainRegistry::is_verified`]) read only *verified* bindings — the gateway
/// adopts this beside the `<name>.example.com` [`SiteRegistry`].
#[derive(Default)]
pub struct DomainRegistry {
    bindings: Mutex<BTreeMap<String, DomainBinding>>,
    next_seq: AtomicU64,
    /// The trusted root authority that mints domain-binding credentials. A bind /
    /// rebind must present a credential verifying under this root for the domain.
    /// `None` (the [`DomainRegistry::new`] default) = no authority → every bind is
    /// refused (fail-closed); verify/route/`ask` read-only paths do not need it.
    authority: Option<PublicKey>,
    /// The receipt chain a successful bind is sealed into — prev-hash-chained +
    /// ed25519-signed, so a client can verify a bind without trusting the host.
    /// `None` leaves the unsigned default ([`BindReceipt::attest`] is `None`).
    receipt_chain: Option<ReceiptChain>,
    /// The durable backend — when set, the registry IS a **umem cell**: every bound /
    /// verified [`DomainBinding`] is laid into the cell's `(collection,key) -> value`
    /// heap and committed to the real sorted-Poseidon2 boundary root
    /// ([`dreggnet_umem::UmemRegistry`]), so a gateway restart RECONSTRUCTS the
    /// bindings FROM the committed heap (the data-plane durability blocker) — including
    /// their Verified state, so a proven domain keeps routing + minting certs after a
    /// restart rather than reverting to unproven. This replaces the from-scratch
    /// JSON-lines log with the real substrate (the #2 re-dregg move,
    /// `docs/REGISTRIES-AS-UMEM.md`) — unlocking fork/time-travel/merge-readiness.
    /// `None` is the in-memory-only default;
    /// [`with_durable_store`](DomainRegistry::with_durable_store) attaches it.
    store: Option<UmemRegistry<DomainBinding>>,
}

impl DomainRegistry {
    /// A fresh, empty registry with **no** binding authority configured — verify /
    /// route / cert-`ask` work, but [`bind`](Self::bind) is refused (fail-closed)
    /// until a root is set. The gateway adopts this read side; the binding control
    /// surface uses [`with_authority`](Self::with_authority).
    pub fn new() -> DomainRegistry {
        DomainRegistry::default()
    }

    /// A registry whose binds are gated by credentials verifying under `root` — the
    /// trusted domain-binding authority. Only a holder of a credential this root
    /// minted (or attenuated) may bind, and the binding's owner is that credential's
    /// subject.
    pub fn with_authority(root: PublicKey) -> DomainRegistry {
        DomainRegistry {
            authority: Some(root),
            ..Default::default()
        }
    }

    /// Attach a receipt chain so successful binds are sealed (prev-hash-chained +
    /// ed25519-signed) and re-witnessable by a non-witness
    /// ([`dreggnet_webapp::receipt::verify_chain`] against
    /// [`Self::receipt_signer`]). A real binding host configures a persistent
    /// secret; tests use a fixed seed.
    pub fn with_receipt_chain(mut self, chain: ReceiptChain) -> DomainRegistry {
        self.receipt_chain = Some(chain);
        self
    }

    /// The public key a non-witness verifies this registry's bind receipts under,
    /// if it is a signed registry.
    pub fn receipt_signer(&self) -> Option<[u8; 32]> {
        self.receipt_chain.as_ref().map(|c| c.signer_public())
    }

    /// Attach a **durable umem backend** at `path` and **reconstruct** the prior data
    /// plane: open the [`UmemRegistry`](dreggnet_umem::UmemRegistry) (the registry AS a
    /// umem cell), [`adopt`](Self::adopt) every persisted [`DomainBinding`] restored
    /// FROM the committed heap back into the live registry (without re-issuing a
    /// challenge nonce), and commit every future bind/verify to the heap — so a gateway
    /// restart keeps routing the verified custom domains a prior process bound (the
    /// data-plane durability blocker) instead of losing them.
    ///
    /// Builder form: chains after [`new`](Self::new) /
    /// [`with_authority`](Self::with_authority) /
    /// [`with_receipt_chain`](Self::with_receipt_chain). The restore **fails closed**
    /// if the committed heap does not bind its sealed boundary root (the
    /// `root_binds_get` discipline).
    pub fn with_durable_store(
        mut self,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<DomainRegistry> {
        let store = UmemRegistry::<DomainBinding>::open(path).map_err(|e| e.into_io())?;
        let loaded = store.all();
        self.store = Some(store);
        // Reconstruct via the existing adopt path (also keeps `next_seq` monotonic).
        for binding in loaded {
            self.adopt(binding);
        }
        Ok(self)
    }

    /// The durable backend path, if this registry persists its bindings.
    pub fn durable_path(&self) -> Option<&std::path::Path> {
        self.store.as_ref().map(|s| s.path())
    }

    /// The registry's **committed umem boundary root** (hex), if it is durably backed:
    /// the real sorted-Poseidon2 `compute_heap_root` over the domain-binding cell's heap
    /// — the 32-byte commitment a dregg light client understands for the WHOLE set of
    /// bound domains. `None` when the registry is in-memory-only. The same primitive the
    /// compute-as-cell + account-recovery lanes commit with (`docs/REGISTRIES-AS-UMEM.md`).
    pub fn umem_root(&self) -> Option<String> {
        self.store.as_ref().map(|s| s.boundary_root())
    }

    /// **Time-travel — checkpoint** the current bound-domain set: the committed boundary
    /// root, retained so [`restore_to`](Self::restore_to) can return to it ("my domains
    /// as of now"). `None` when in-memory-only.
    pub fn checkpoint(&self) -> Option<String> {
        self.store.as_ref().map(|s| s.checkpoint())
    }

    /// **Time-travel — restore** the bound-domain set to an earlier committed `root`
    /// (from [`checkpoint`](Self::checkpoint)): the bindings revert to that committed
    /// state, durably (the rollback survives a restart), and the in-memory routing view
    /// is re-seeded from the restored committed heap. A no-op `Ok(())` when
    /// in-memory-only.
    pub fn restore_to(&self, root: &str) -> std::io::Result<()> {
        if let Some(store) = &self.store {
            store.restore(root).map_err(|e| e.into_io())?;
            let mut bindings = self.bindings.lock().expect("bindings poisoned");
            bindings.clear();
            for binding in store.all() {
                bindings.insert(binding.domain.clone(), binding);
            }
        }
        Ok(())
    }

    /// Persist a binding through the durable backend (no-op when in-memory-only).
    /// A store fault surfaces as [`DomainError::Persist`].
    fn persist(&self, binding: &DomainBinding) -> Result<(), DomainError> {
        if let Some(store) = &self.store {
            store.append(binding).map_err(|e| DomainError::Persist {
                domain: binding.domain.clone(),
                reason: e.to_string(),
            })?;
        }
        Ok(())
    }

    /// Bind a custom domain to a site as a cap-gated, receipted turn (Pending).
    ///
    /// Verifies `cap`'s credential under the trusted root authority as granting the
    /// binding cap for `domain` (NOT a self-asserted token — a forged/wrong-root
    /// credential is refused), validates the domain as a custom FQDN and the site as
    /// a valid `<name>` label, then — **only if the domain is unbound or already
    /// owned by this credential's subject** — issues the challenge nonce and writes
    /// the [`DomainBinding`] (owner = the credential subject, state = Pending). A
    /// rebind by any other subject is refused ([`DomainError::OwnerMismatch`]); a
    /// rebind by the owner replaces the binding (a fresh nonce, back to Pending).
    pub fn bind(
        &self,
        cap: &DomainCap,
        domain: &str,
        site: &str,
        method: ChallengeMethod,
    ) -> Result<BindReceipt, DomainError> {
        let domain = domain.trim().to_ascii_lowercase();
        if !is_valid_domain(&domain) {
            return Err(DomainError::InvalidDomain(domain));
        }
        if cap.domain != domain {
            return Err(DomainError::CapRefused {
                domain,
                reason: format!(
                    "cap is exercised for `{}`, not the bound domain",
                    cap.domain
                ),
            });
        }
        // Real cap authority: verify the credential under the trusted root. A
        // registry with no authority refuses every bind (fail-closed).
        let root = self.authority.as_ref().ok_or(DomainError::NoAuthority)?;
        let owner = verify_bind_authority(&cap.credential, root, &domain)?;
        if !is_valid_name(site) {
            return Err(DomainError::InvalidSite(site.to_string()));
        }

        let seq = self.next_seq.fetch_add(1, Ordering::Relaxed);
        let challenge = challenge_token(&domain, &owner, seq);
        let binding = DomainBinding {
            domain: domain.clone(),
            site: site.to_string(),
            owner: owner.clone(),
            method,
            challenge,
            state: VerificationState::Pending,
            verified_seq: None,
        };
        let mut receipt = BindReceipt {
            seq,
            domain: domain.clone(),
            site: site.to_string(),
            owner: owner.clone(),
            challenge: binding.dns_challenge(),
            attest: None,
        };
        // Owner-gated rebind, atomic with the insert: a different subject cannot
        // overwrite (takeover) or reset (takedown) a victim's existing binding.
        let mut guard = self.bindings.lock().expect("bindings poisoned");
        if let Some(existing) = guard.get(&domain) {
            if existing.owner != owner {
                return Err(DomainError::OwnerMismatch { domain });
            }
        }
        // Durable-first: persist the binding (append + fsync) before the in-memory
        // insert and before sealing the receipt, so a bind is never reported
        // successful unless it survives a restart (the data-plane durability blocker).
        self.persist(&binding)?;
        guard.insert(domain, binding);
        drop(guard);
        // Seal ONLY on success (after the insert): a bind IS a turn, sealed into
        // the registry's signed chain. Sealing before the owner-gate could
        // advance the chain head for a rejected bind and orphan the next link.
        if let Some(chain) = &self.receipt_chain {
            receipt.attest = Some(chain.seal(receipt.body_hash(), receipt.seq(), None));
        }
        Ok(receipt)
    }

    /// Verify a binding's control by resolving its challenge through `dns`.
    ///
    /// On a satisfied challenge the binding flips to [`VerificationState::Verified`]
    /// (recording the verifying turn) and the now-verified binding is returned. An
    /// unmet challenge leaves the binding Pending and returns
    /// [`DomainError::ChallengeUnmet`]; an unbound domain is
    /// [`DomainError::NotBound`]. Idempotent: verifying an already-verified binding
    /// re-checks and is a no-op success.
    pub fn verify(
        &self,
        domain: &str,
        dns: &impl DnsResolver,
    ) -> Result<DomainBinding, DomainError> {
        let domain = domain.trim().to_ascii_lowercase();
        // Snapshot the binding, then release the lock for the (slow, ≤10s) DNS
        // lookup so a black-holed resolver cannot stall all routing / cert asks
        // while it runs (the lock is held only for the cheap map operations).
        let snapshot = {
            let guard = self.bindings.lock().expect("bindings poisoned");
            guard
                .get(&domain)
                .cloned()
                .ok_or_else(|| DomainError::NotBound(domain.clone()))?
        };
        if !challenge_satisfied(&snapshot, dns) {
            return Err(DomainError::ChallengeUnmet { domain });
        }
        // Re-acquire to commit. The binding may have been rebound (a fresh nonce)
        // while the lock was dropped — only flip the binding whose challenge is the
        // one we actually proved, so a concurrent rebind is not wrongly verified.
        let mut guard = self.bindings.lock().expect("bindings poisoned");
        let binding = guard
            .get_mut(&domain)
            .ok_or_else(|| DomainError::NotBound(domain.clone()))?;
        if binding.challenge != snapshot.challenge || binding.method != snapshot.method {
            return Err(DomainError::ChallengeUnmet { domain });
        }
        let changed = binding.state != VerificationState::Verified;
        if changed {
            binding.state = VerificationState::Verified;
            binding.verified_seq = Some(self.next_seq.fetch_add(1, Ordering::Relaxed));
        }
        let updated = binding.clone();
        drop(guard);
        // Persist the now-Verified binding so its proven state survives a restart
        // (a restart must keep routing + minting certs for an already-proven domain,
        // not revert it to unproven). Idempotent re-verify writes nothing.
        if changed {
            self.persist(&updated)?;
        }
        Ok(updated)
    }

    /// Look up a binding by domain (a clone of the committed cell).
    pub fn get(&self, domain: &str) -> Option<DomainBinding> {
        self.bindings
            .lock()
            .expect("bindings poisoned")
            .get(&domain.to_ascii_lowercase())
            .cloned()
    }

    /// The bound site `<name>` for an inbound `Host`, **only when verified**.
    ///
    /// Strips a `:port` suffix and lowercases, then returns the verified binding's
    /// site. An unbound or still-Pending host yields `None` — the gateway routes (and
    /// the edge mints a cert for) only proven domains.
    pub fn site_for_host(&self, host: &str) -> Option<String> {
        let domain = host_key(host)?;
        let guard = self.bindings.lock().expect("bindings poisoned");
        let binding = guard.get(&domain)?;
        binding.is_verified().then(|| binding.site.clone())
    }

    /// Whether `host` is a verified custom domain — the gateway's on-demand-TLS
    /// `ask` gate (a cert is minted only for a proven domain).
    pub fn is_verified(&self, host: &str) -> bool {
        host_key(host)
            .and_then(|d| {
                self.bindings
                    .lock()
                    .expect("bindings poisoned")
                    .get(&d)
                    .map(|b| b.is_verified())
            })
            .unwrap_or(false)
    }

    /// Resolve + serve a request whose `Host` is a verified custom domain against
    /// the bound site cell in `sites`. Returns `None` if `host` is not a verified
    /// custom domain (so the caller falls through to the `<name>.example.com` path);
    /// `Some(404)` if it is verified but its bound site is (no longer) published.
    pub fn resolve(
        &self,
        sites: &SiteRegistry,
        host: &str,
        req: &WebRequest,
    ) -> Option<WebResponse> {
        let site = self.site_for_host(host)?;
        Some(match sites.get(&site) {
            Some(cell) => cell.serve(req),
            None => WebResponse::error(
                404,
                format!("domain `{host}` bound to unpublished site `{site}`"),
            ),
        })
    }

    /// All bindings, sorted by domain (a snapshot of the committed set).
    pub fn list(&self) -> Vec<DomainBinding> {
        self.bindings
            .lock()
            .expect("bindings poisoned")
            .values()
            .cloned()
            .collect()
    }

    /// Adopt a pre-existing [`DomainBinding`] (e.g. one loaded from a persisted
    /// store) into this registry, so a fresh process can drive
    /// [`verify`](Self::verify) / [`list`](Self::list) / routing over bindings a
    /// prior turn created — without re-issuing the challenge nonce (which would
    /// invalidate a published record). The registry's sequence is bumped past the
    /// adopted binding's verifying turn so later turns stay monotonic.
    pub fn adopt(&self, binding: DomainBinding) {
        if let Some(seq) = binding.verified_seq {
            self.next_seq.fetch_max(seq + 1, Ordering::Relaxed);
        }
        self.bindings
            .lock()
            .expect("bindings poisoned")
            .insert(binding.domain.clone(), binding);
    }
}

/// Whether a binding's DNS challenge is satisfied by `dns`.
fn challenge_satisfied(binding: &DomainBinding, dns: &impl DnsResolver) -> bool {
    let challenge = binding.dns_challenge();
    match challenge.record_type {
        ChallengeMethod::Txt => dns
            .txt(&challenge.record_name)
            .iter()
            .any(|v| v == &challenge.expected_value),
        ChallengeMethod::Cname => dns
            .cname(&challenge.record_name)
            .map(|t| {
                let got = t.trim_end_matches('.');
                got.eq_ignore_ascii_case(&challenge.expected_value)
            })
            .unwrap_or(false),
    }
}

/// Normalize an inbound `Host` to a binding key: strip `:port`, trim, lowercase.
/// `None` for an empty host.
fn host_key(host: &str) -> Option<String> {
    let bare = host.split(':').next().unwrap_or(host).trim();
    if bare.is_empty() {
        return None;
    }
    Some(bare.to_ascii_lowercase())
}

/// Whether `domain` is a usable custom domain: a multi-label FQDN whose labels are
/// each valid DNS labels, and which is NOT a `*.example.com` host (that is the
/// wildcard hosting path, served without a binding) and not the bare apex.
pub fn is_valid_domain(domain: &str) -> bool {
    let domain = domain.trim_end_matches('.');
    if domain.is_empty() || domain.len() > 253 {
        return false;
    }
    // A custom domain owns its own apex; the example.com wildcard is not "custom".
    if domain == HOSTING_APEX || domain.ends_with(&format!(".{HOSTING_APEX}")) {
        return false;
    }
    let labels: Vec<&str> = domain.split('.').collect();
    if labels.len() < 2 {
        return false;
    }
    labels.iter().all(|l| is_valid_label(l))
}

/// A single DNS label: non-empty, ≤63, `[a-z0-9-]`, not edge-`-` — the same shape
/// [`is_valid_name`] enforces for a site label, applied per domain label.
fn is_valid_label(label: &str) -> bool {
    is_valid_name(&label.to_ascii_lowercase())
}

/// A deterministic challenge nonce for `(domain, owner, seq)`. FNV-1a/64 hex,
/// prefixed `dregg-verify-`. Deterministic so a bind receipt is re-derivable; bound
/// to the owner + the registry seq so two binds never collide. (On a dregg node the
/// nonce is drawn from the cell's commitment; the property — a value the owner must
/// place in DNS to prove control — is the same.)
fn challenge_token(domain: &str, owner: &str, seq: u64) -> String {
    const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut h: u64 = OFFSET;
    let mut mix = |bytes: &[u8]| {
        for &b in bytes {
            h ^= b as u64;
            h = h.wrapping_mul(PRIME);
        }
        h ^= 0xff;
        h = h.wrapping_mul(PRIME);
    };
    mix(domain.as_bytes());
    mix(owner.as_bytes());
    mix(&seq.to_le_bytes());
    format!("dregg-verify-{h:016x}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_webapp::hosting::{PublishCap, SiteContent};
    use dreggnet_webauth::cred::RootKey;
    use dreggnet_webauth::grant::mint_caps;

    /// The trusted root authority for the test registry (deterministic seed).
    fn root() -> RootKey {
        RootKey::from_seed([7u8; 32])
    }

    /// A registry gated by the test root — the real cap chain, not a self-asserted
    /// token.
    fn registry() -> DomainRegistry {
        DomainRegistry::with_authority(root().public())
    }

    /// A real credential the test root minted, granting the broad `domains` cap.
    fn domains_cred() -> String {
        mint_caps(&root(), [DOMAINS_CAP], None).encode()
    }

    /// The owner (subject) a credential resolves to — what a binding records.
    fn owner_of(cred: &str) -> String {
        subject_of(cred).expect("credential yields a subject")
    }

    /// A binding cap presenting a freshly-minted `domains` credential for `domain`.
    fn cap(domain: &str) -> DomainCap {
        DomainCap::new(domains_cred(), domain)
    }

    #[test]
    fn domain_validation() {
        assert!(is_valid_domain("blog.example.com"));
        assert!(is_valid_domain("shop.example.co.uk"));
        assert!(is_valid_domain("example.com"));
        assert!(!is_valid_domain(""));
        assert!(!is_valid_domain("localhost")); // single label
        assert!(!is_valid_domain("has space.com"));
        assert!(!is_valid_domain("-bad.com"));
        // The wildcard path is not a "custom" domain.
        assert!(!is_valid_domain("example.com"));
        assert!(!is_valid_domain("blog.example.com"));
    }

    #[test]
    fn bind_requires_a_real_authorized_credential() {
        // No authority configured → every bind is refused (fail-closed).
        let no_auth = DomainRegistry::new();
        assert_eq!(
            no_auth.bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt
            ),
            Err(DomainError::NoAuthority),
        );

        // A credential minted by a DIFFERENT (attacker) root does not verify under
        // the trusted root → CapRefused. This is the self-asserted-cap attack: an
        // attacker who fabricates their own credential cannot bind.
        let attacker_root = RootKey::from_seed([99u8; 32]);
        let forged = mint_caps(&attacker_root, [DOMAINS_CAP], None).encode();
        let reg = registry();
        assert!(matches!(
            reg.bind(
                &DomainCap::new(forged, "blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt
            ),
            Err(DomainError::CapRefused { .. }),
        ));

        // The rightful, root-minted credential binds; the owner is its subject.
        let c = cap("blog.example.com");
        let want_owner = owner_of(&c.credential);
        let r = reg
            .bind(&c, "blog.example.com", "blog", ChallengeMethod::Txt)
            .expect("bind");
        assert_eq!(r.domain, "blog.example.com");
        assert_eq!(r.site, "blog");
        assert_eq!(r.owner, want_owner);
        assert_eq!(r.challenge.record_type, ChallengeMethod::Txt);
        assert_eq!(r.challenge.record_name, "_dregg-verify.blog.example.com");

        // A cap exercised for a different domain cannot bind blog.example.com.
        assert!(matches!(
            reg.bind(
                &cap("shop.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt
            ),
            Err(DomainError::CapRefused { .. }),
        ));

        // Invalid domain / invalid site refused.
        assert!(matches!(
            reg.bind(&cap("localhost"), "localhost", "blog", ChallengeMethod::Txt),
            Err(DomainError::InvalidDomain(_)),
        ));
        assert!(matches!(
            reg.bind(
                &cap("x.example.com"),
                "x.example.com",
                "Bad.Name",
                ChallengeMethod::Txt
            ),
            Err(DomainError::InvalidSite(_)),
        ));
    }

    #[test]
    fn signed_binds_form_a_verifiable_receipt_chain() {
        use dreggnet_webapp::receipt::{ChainError, verify_chain, verify_chain_from};

        // A signed binding registry: the real cap authority + a receipt chain.
        let reg = registry().with_receipt_chain(ReceiptChain::from_seed([21u8; 32]));

        let r0 = reg
            .bind(
                &cap("a.example.com"),
                "a.example.com",
                "alpha",
                ChallengeMethod::Txt,
            )
            .expect("bind a");
        let r1 = reg
            .bind(
                &cap("b.example.com"),
                "b.example.com",
                "beta",
                ChallengeMethod::Cname,
            )
            .expect("bind b");
        let r2 = reg
            .bind(
                &cap("c.example.com"),
                "c.example.com",
                "gamma",
                ChallengeMethod::Txt,
            )
            .expect("bind c");

        // Each bind IS a turn — signed + chained, re-witnessable by a non-witness.
        let chain = vec![r0.clone(), r1.clone(), r2.clone()];
        assert_eq!(verify_chain(&chain), Ok(()));
        assert!(r0.attest.as_ref().unwrap().prev_receipt_hash.is_none());
        assert_eq!(
            r1.attest.as_ref().unwrap().prev_receipt_hash,
            r0.receipt_hash()
        );
        assert_eq!(
            reg.receipt_signer(),
            Some(r0.attest.as_ref().unwrap().signer)
        );

        // A rejected bind (an unauthorized credential) must NOT advance the chain:
        // the attacker's bind is refused, and the next legitimate link still points
        // at r2 (no orphaned head — only a sealed-on-success bind moves it).
        let attacker = mint_caps(&RootKey::from_seed([55u8; 32]), [DOMAINS_CAP], None).encode();
        let _ = reg.bind(
            &DomainCap::new(attacker, "b.example.com"),
            "b.example.com",
            "evil",
            ChallengeMethod::Txt,
        );
        let r3 = reg
            .bind(
                &cap("d.example.com"),
                "d.example.com",
                "delta",
                ChallengeMethod::Txt,
            )
            .expect("bind d");
        assert_eq!(
            r3.attest.as_ref().unwrap().prev_receipt_hash,
            r2.receipt_hash()
        );
        assert_eq!(verify_chain(&[r0, r1, r2, r3]), Ok(()));

        // Tamper the recorded site after sealing → the signature fails.
        let mut forged = reg
            .bind(
                &cap("e.example.com"),
                "e.example.com",
                "epsilon",
                ChallengeMethod::Txt,
            )
            .expect("bind e");
        let good_prev = forged.attest.as_ref().unwrap().prev_receipt_hash;
        forged.site = "hijacked".into();
        assert_eq!(
            verify_chain_from(&[forged], good_prev),
            Err(ChainError::BadSignature { seq: 4 }),
        );

        // The unsigned default leaves a bare projection.
        let plain = registry();
        let bare = plain
            .bind(
                &cap("z.example.com"),
                "z.example.com",
                "zeta",
                ChallengeMethod::Txt,
            )
            .expect("bind z");
        assert!(bare.attest.is_none());
    }

    #[test]
    fn per_domain_cap_only_binds_its_domain() {
        // A delegate confined to `domain-bind/blog.example.com` (the attenuated
        // form) binds only that domain — not any other.
        let cred = mint_caps(&root(), [DomainCap::cap_token("blog.example.com")], None).encode();
        let reg = registry();
        assert!(
            reg.bind(
                &DomainCap::new(cred.clone(), "blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt
            )
            .is_ok()
        );
        assert!(matches!(
            reg.bind(
                &DomainCap::new(cred, "shop.example.com"),
                "shop.example.com",
                "shop",
                ChallengeMethod::Txt
            ),
            Err(DomainError::CapRefused { .. }),
        ));
    }

    #[test]
    fn attacker_cannot_overwrite_a_victims_binding() {
        let reg = registry();
        // Victim Alice binds + verifies blog.example.com (a distinct credential).
        let alice = mint_caps(&root(), [DOMAINS_CAP], None).encode();
        let r = reg
            .bind(
                &DomainCap::new(alice.clone(), "blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .expect("alice binds");
        let alice_owner = owner_of(&alice);
        assert_eq!(r.owner, alice_owner);
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        reg.verify("blog.example.com", &dns)
            .expect("alice verifies");
        assert!(reg.is_verified("blog.example.com"));

        // Attacker Mallory holds her OWN valid root-minted credential — a different
        // subject. She cannot rebind/repoint/takedown Alice's binding.
        let mallory = mint_caps(&root(), [DOMAINS_CAP], None).encode();
        assert_ne!(owner_of(&mallory), alice_owner, "distinct subjects");
        assert_eq!(
            reg.bind(
                &DomainCap::new(mallory, "blog.example.com"),
                "blog.example.com",
                "evil",
                ChallengeMethod::Txt
            ),
            Err(DomainError::OwnerMismatch {
                domain: "blog.example.com".into()
            }),
        );
        // Alice's binding is untouched: still verified, still pointing at `blog`.
        assert!(reg.is_verified("blog.example.com"));
        assert_eq!(
            reg.site_for_host("blog.example.com").as_deref(),
            Some("blog")
        );
        assert_eq!(reg.get("blog.example.com").unwrap().owner, alice_owner);
    }

    #[test]
    fn txt_challenge_verify_round_trip() {
        let reg = registry();
        let r = reg
            .bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .unwrap();

        // Before the record exists, verify fails and the binding stays Pending.
        let empty = MockDns::new();
        assert_eq!(
            reg.verify("blog.example.com", &empty),
            Err(DomainError::ChallengeUnmet {
                domain: "blog.example.com".into()
            }),
        );
        assert!(!reg.is_verified("blog.example.com"));
        assert_eq!(reg.site_for_host("blog.example.com"), None);

        // Publish the challenged TXT record → verify succeeds → Verified.
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        let b = reg.verify("blog.example.com", &dns).expect("verify");
        assert_eq!(b.state, VerificationState::Verified);
        assert!(b.verified_seq.is_some());
        assert!(reg.is_verified("blog.example.com"));
        assert_eq!(
            reg.site_for_host("blog.example.com").as_deref(),
            Some("blog")
        );
        // Port-stripping + case on the inbound host.
        assert_eq!(
            reg.site_for_host("Blog.Example.Com:443").as_deref(),
            Some("blog")
        );
    }

    #[test]
    fn cname_challenge_verify_round_trip() {
        let reg = registry();
        let r = reg
            .bind(
                &cap("www.example.com"),
                "www.example.com",
                "blog",
                ChallengeMethod::Cname,
            )
            .unwrap();
        assert_eq!(r.challenge.record_type, ChallengeMethod::Cname);
        assert_eq!(r.challenge.record_name, "www.example.com");
        assert_eq!(r.challenge.expected_value, "blog.example.com");

        // A CNAME to the wrong target does not verify.
        let wrong = MockDns::new().with_cname("www.example.com", "evil.example.com");
        assert!(reg.verify("www.example.com", &wrong).is_err());

        // The right CNAME (trailing-dot FQDN form tolerated) verifies.
        let dns = MockDns::new().with_cname("www.example.com", "blog.example.com.");
        let b = reg.verify("www.example.com", &dns).expect("verify");
        assert!(b.is_verified());
        assert_eq!(
            reg.site_for_host("www.example.com").as_deref(),
            Some("blog")
        );
    }

    #[test]
    fn verify_unbound_is_not_bound() {
        let reg = registry();
        assert_eq!(
            reg.verify("nope.example.com", &MockDns::new()),
            Err(DomainError::NotBound("nope.example.com".into())),
        );
    }

    #[test]
    fn owner_can_rebind_resets_to_pending_with_fresh_nonce() {
        let reg = registry();
        // The SAME credential is reused across binds (a stable owner subject).
        let cred = domains_cred();
        let r1 = reg
            .bind(
                &DomainCap::new(cred.clone(), "blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .unwrap();
        let dns = MockDns::new().with_txt(&r1.challenge.record_name, &r1.challenge.expected_value);
        reg.verify("blog.example.com", &dns).unwrap();
        assert!(reg.is_verified("blog.example.com"));

        // The owner re-binds (e.g. point at a different site) → back to Pending, new
        // nonce.
        let r2 = reg
            .bind(
                &DomainCap::new(cred, "blog.example.com"),
                "blog.example.com",
                "shop",
                ChallengeMethod::Txt,
            )
            .unwrap();
        assert_eq!(r1.owner, r2.owner, "same owner across the rebind");
        assert_ne!(r1.challenge.expected_value, r2.challenge.expected_value);
        assert!(!reg.is_verified("blog.example.com"));
        assert_eq!(reg.site_for_host("blog.example.com"), None);
    }

    #[test]
    fn resolve_serves_the_bound_site_only_when_verified() {
        // A published site to bind onto.
        let sites = SiteRegistry::new();
        sites
            .publish(
                &PublishCap::for_site("agent:ember", "blog"),
                "blog",
                SiteContent::new().with("/index.html", "<h1>custom domain</h1>"),
            )
            .unwrap();

        let reg = registry();
        let r = reg
            .bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .unwrap();

        // Pending → resolve declines (None → gateway falls through to example.com).
        assert!(
            reg.resolve(&sites, "blog.example.com", &WebRequest::get("/"))
                .is_none()
        );

        // Verified → resolve serves the bound site's content.
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        reg.verify("blog.example.com", &dns).unwrap();
        let resp = reg
            .resolve(&sites, "blog.example.com", &WebRequest::get("/"))
            .expect("served");
        assert_eq!(resp.status, 200);
        assert!(resp.body_str().contains("custom domain"));

        // Verified but bound to an unpublished site → 404 (not a fall-through).
        let r2 = reg
            .bind(
                &cap("ghost.example.com"),
                "ghost.example.com",
                "ghost",
                ChallengeMethod::Txt,
            )
            .unwrap();
        let dns2 = MockDns::new().with_txt(&r2.challenge.record_name, &r2.challenge.expected_value);
        reg.verify("ghost.example.com", &dns2).unwrap();
        let resp = reg
            .resolve(&sites, "ghost.example.com", &WebRequest::get("/"))
            .expect("resolved");
        assert_eq!(resp.status, 404);
    }
}
