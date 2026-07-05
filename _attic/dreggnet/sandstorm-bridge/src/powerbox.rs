//! **The powerbox = dregg caps** — the keystone of the integration.
//!
//! Sandstorm's *powerbox* is its capability-delegation mechanism. A grain that
//! lacks the authority to reach some resource (another grain, a file, an external
//! API) **requests** it *by type* — a `PowerboxDescriptor` query (a list of typed
//! tags, not a named instance). The **trusted system UI** (NOT the requesting app)
//! shows the user a picker of the capabilities they actually hold that match the
//! query; the user **designates** one; the system hands the grain that capability,
//! nothing else. Persisted, the capability is a **`SturdyRef`** — a token sealed to
//! its owner under a host-held secret, so a leaked token is inert and a *forged* one
//! (minted without the host secret) never restores. This is pure object-capability
//! security: no ambient authority, designation = authorization.
//!
//! dregg is the *same discipline* and already implements the *same ceremony*
//! (`starbridge-v2/src/powerbox.rs` / the cipherclerk): a trusted-UI picker that
//! mints a strictly-attenuated cap into a confined app-cell's c-list via a real
//! `Effect::GrantCapability` turn. The mapping is therefore not a shim — it is an
//! identity, plus the half Sandstorm lacks: **the delegation is witnessed.** A
//! Sandstorm grant is enforced by the (trusted) supervisor; a dregg cap grant leaves
//! a receipt a *light client* can verify, so "user A delegated cap C (facets {view})
//! over grain G to app B" is provable to a third party who trusts neither host nor
//! app.
//!
//! This module realizes the three weld points the plan (§4.2) names:
//!   1. **descriptor → `Pred`** — parse a `PowerboxDescriptor` into a boolean
//!      predicate over a candidate cap, and filter the principal's held caps by it
//!      (the trusted picker). dregg's one matching algebra, applied to the powerbox.
//!   2. **grant → turn** — the designation mints a strictly-attenuating grant
//!      (`granted ⊆ held`, refused in-band otherwise) leaving a `TurnReceipt`.
//!   3. **SturdyRef ↔ `dga1_` cap** — `seal_for()` seals the cap to the owner key
//!      under the **host's [`SealKey`]** (an HMAC, not an unkeyed hash) as a `dga1_…`
//!      token; [`SturdyRef::restore`] re-verifies that host MAC *and* the owner
//!      binding, so a token this host did not seal — or one presented by anyone but
//!      its owner — is inert (`sealFor`). The seal key is a host secret an attacker
//!      does not hold, which is what makes the token unforgeable (red-team #PB-1).

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::spk::base32;

/// A **host-held seal secret**. The durable `dga1_…` SturdyRef is sealed (HMAC'd)
/// under this key, so only a holder of the host secret can mint a token that
/// [`SturdyRef::restore`] will honor. An attacker who fabricates a token without the
/// secret produces an invalid MAC and the token is inert — this is the keyed
/// integrity that closes the universal-forgery hole (red-team #PB-1). Keep one per
/// host; never serialize or log it.
#[derive(Clone)]
pub struct SealKey {
    secret: [u8; 32],
}

impl std::fmt::Debug for SealKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Never print the secret.
        f.write_str("SealKey(<redacted>)")
    }
}

impl SealKey {
    /// Derive a host seal key from arbitrary secret material (a host master secret,
    /// a KMS-held key, …). Domain-separated so this key is never confused with any
    /// other use of the same material.
    pub fn from_secret(material: &[u8]) -> Self {
        let mut h = Sha256::new();
        h.update(b"dregg-sandstorm-sturdyref-seal-v1");
        h.update(material);
        SealKey {
            secret: h.finalize().into(),
        }
    }

    /// Construct directly from a 32-byte secret (e.g. a freshly generated random key).
    pub fn from_bytes(secret: [u8; 32]) -> Self {
        SealKey { secret }
    }

    /// HMAC-SHA256 of `msg` under this host secret (RFC 2104). Pure-`sha2`, no extra
    /// dependency; the seal an attacker cannot recompute without the secret.
    fn mac(&self, msg: &[u8]) -> [u8; 32] {
        const BLOCK: usize = 64;
        let mut k = [0u8; BLOCK];
        // The key is already 32 bytes (< BLOCK), so it is right-zero-padded.
        k[..32].copy_from_slice(&self.secret);
        let mut ipad = [0x36u8; BLOCK];
        let mut opad = [0x5cu8; BLOCK];
        for i in 0..BLOCK {
            ipad[i] ^= k[i];
            opad[i] ^= k[i];
        }
        let mut inner = Sha256::new();
        inner.update(ipad);
        inner.update(msg);
        let inner = inner.finalize();
        let mut outer = Sha256::new();
        outer.update(opad);
        outer.update(inner);
        outer.finalize().into()
    }
}

/// Constant-time equality over two base32 seal strings (avoid a MAC-comparison
/// timing oracle). Both are fixed-shape host-produced strings.
fn ct_eq(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for i in 0..a.len() {
        diff |= a[i] ^ b[i];
    }
    diff == 0
}

/// A capability over a target resource, carrying a set of **effect facets** (the
/// named rights it confers) and the **interface id** of the resource kind (the
/// Cap'n Proto interface type-id the powerbox matches on). The prototype's stand-in
/// for a dregg `CapabilityRef` + its `EffectMask`/facet set.
///
/// Note: a `DreggCapRef` is a plain *value* anyone can construct — it carries **no**
/// authority on its own. Authority comes only from a [`SturdyRef`] sealed under the
/// host [`SealKey`]; a bare `DreggCapRef` is honored by no enforcement point
/// (see [`crate::bridge::HttpBridge::serve`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DreggCapRef {
    /// The target cell/resource this cap names (a grain's `CellId`, a file cell, …).
    pub target: String,
    /// The resource *kind* — the capnp interface type-id the powerbox requests by
    /// (e.g. a calendar API, a file). `0` = untyped/any. The picker matches on this.
    pub interface_id: u64,
    /// The named rights conferred — the powerbox-permission ⇒ dregg-facet mapping.
    /// A subset relation on these sets is the attenuation order.
    pub facets: Vec<String>,
}

impl DreggCapRef {
    /// An untyped cap (interface id `0`) — the common grain-over-cell case.
    pub fn new(target: impl Into<String>, facets: &[&str]) -> Self {
        DreggCapRef {
            target: target.into(),
            interface_id: 0,
            facets: facets.iter().map(|s| s.to_string()).collect(),
        }
    }

    /// A typed cap — names the resource-kind interface id the powerbox matches on.
    pub fn new_typed(target: impl Into<String>, interface_id: u64, facets: &[&str]) -> Self {
        DreggCapRef {
            target: target.into(),
            interface_id,
            facets: facets.iter().map(|s| s.to_string()).collect(),
        }
    }

    fn sorted_facets(&self) -> Vec<String> {
        let mut f = self.facets.clone();
        f.sort();
        f.dedup();
        f
    }

    /// `self ⊒ other`: does this cap dominate (carry at least the authority of)
    /// `other`? Same target, and every facet of `other` is held — the submask order
    /// that is the basis of attenuation.
    pub fn dominates(&self, other: &DreggCapRef) -> bool {
        self.target == other.target && other.facets.iter().all(|f| self.facets.contains(f))
    }

    /// **Save** this cap as a persistent **SturdyRef** sealed to `owner_key` under the
    /// host [`SealKey`]. The token is a `dga1_…` string carrying the cap + a one-link
    /// caveat chain, stamped with an HMAC that only a holder of `seal` can produce;
    /// only `owner_key` can [`SturdyRef::restore`] it (the `sealFor: Owner`
    /// discipline). A token minted without `seal` will not restore on this host.
    pub fn seal_for(&self, owner_key: impl Into<String>, seal: &SealKey) -> SturdyRef {
        let sealed = SealedCap {
            target: self.target.clone(),
            interface_id: self.interface_id,
            base_facets: self.sorted_facets(),
            owner: owner_key.into(),
            caveats: Vec::new(),
        };
        sealed.encode(seal)
    }

    /// Back-compat alias used by the lifecycle tests: a SturdyRef bearer-bound to the
    /// cap's own target (owner = target). Prefer [`seal_for`](Self::seal_for).
    pub fn to_sturdyref(&self, seal: &SealKey) -> SturdyRef {
        self.seal_for(self.target.clone(), seal)
    }
}

// ---------------------------------------------------------------------------
// SturdyRef ↔ dga1_ cap (sealed, attenuable, re-verifiable on restore).
// ---------------------------------------------------------------------------

/// A caveat in a SturdyRef's chain — a restriction applied on every restore. Here:
/// narrow the facet set (delegation that only ever attenuates). Mirrors dregg's
/// `cipherclerk` caveat-chain re-verification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Caveat {
    /// Restrict the effective facets to (at most) this set — an attenuation step.
    RestrictFacets(Vec<String>),
}

/// The decoded contents of a SturdyRef (what `dga1_…` encodes). Opaque to a holder;
/// only its owner can restore it to a live cap, and only on the host that sealed it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct SealedCap {
    target: String,
    interface_id: u64,
    /// The facets at seal time, before the caveat chain narrows them.
    base_facets: Vec<String>,
    /// The owner this ref is sealed to — `restore` requires this key.
    owner: String,
    /// The attenuation chain, re-applied (and integrity-checked) on every restore.
    caveats: Vec<Caveat>,
}

impl SealedCap {
    /// The **host MAC** over the token's fields — an HMAC-SHA256 under the host
    /// [`SealKey`], re-derived and checked on restore so a *tampered or forged* token
    /// (one not produced with the host secret) is rejected. This is the keyed seal
    /// that closes the universal-forgery hole: without `seal` the attacker cannot
    /// compute this value, so any token they fabricate fails the check.
    fn seal(&self, key: &SealKey) -> String {
        let mut msg = Vec::new();
        msg.extend_from_slice(self.target.as_bytes());
        msg.push(0);
        msg.extend_from_slice(&self.interface_id.to_le_bytes());
        msg.extend_from_slice(&(self.base_facets.len() as u64).to_le_bytes());
        for f in &self.base_facets {
            msg.extend_from_slice(f.as_bytes());
            msg.push(0);
        }
        msg.extend_from_slice(self.owner.as_bytes());
        msg.push(0);
        for c in &self.caveats {
            match c {
                Caveat::RestrictFacets(fs) => {
                    msg.push(1);
                    msg.extend_from_slice(&(fs.len() as u64).to_le_bytes());
                    for f in fs {
                        msg.extend_from_slice(f.as_bytes());
                        msg.push(0);
                    }
                }
            }
        }
        base32(&key.mac(&msg))
    }

    /// The live facets after applying the whole caveat chain to the base set.
    fn effective_facets(&self) -> Vec<String> {
        let mut facets = self.base_facets.clone();
        for Caveat::RestrictFacets(allow) in &self.caveats {
            facets.retain(|f| allow.contains(f));
        }
        facets
    }

    fn encode(&self, key: &SealKey) -> SturdyRef {
        // Bind the host MAC into the encoded token.
        let mut doc = serde_json::to_value(self).expect("serialize sealed cap");
        doc["seal"] = serde_json::Value::String(self.seal(key));
        let json = serde_json::to_vec(&doc).expect("serialize token");
        SturdyRef(format!("dga1_{}", base32(&json)))
    }
}

/// A persisted, restorable capability token (Sandstorm `SturdyRef`; dregg `dga1_…`).
/// Sealed to its owner under the host [`SealKey`]: restored to a live [`DreggCapRef`]
/// only by re-verifying its host MAC *and* the presenter being the owner. A leaked
/// token is inert; a forged token (sealed without the host secret) never restores.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SturdyRef(pub String);

/// Why restoring a SturdyRef failed.
#[derive(Debug, PartialEq, Eq)]
pub enum RestoreError {
    /// The token did not decode as a `dga1_…` SturdyRef.
    Malformed,
    /// The presenter is not the owner the token is sealed to — a leaked/stolen token
    /// is inert (`sealFor: Owner`).
    Inert,
    /// The host MAC did not re-verify: the token was tampered, or it was **forged**
    /// (sealed without this host's secret — the universal-forgery defense). Either
    /// way the token confers nothing.
    BadSeal,
}

impl std::fmt::Display for RestoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RestoreError::Malformed => write!(f, "not a dga1_ SturdyRef"),
            RestoreError::Inert => {
                write!(f, "SturdyRef inert: presenter is not the sealed owner")
            }
            RestoreError::BadSeal => write!(
                f,
                "SturdyRef seal failed to re-verify (tampered or not sealed by this host)"
            ),
        }
    }
}
impl std::error::Error for RestoreError {}

impl SturdyRef {
    fn decode(&self) -> Result<(SealedCap, String), RestoreError> {
        let b32 = self
            .0
            .strip_prefix("dga1_")
            .ok_or(RestoreError::Malformed)?;
        let mut spec = data_encoding::Specification::new();
        spec.symbols.push_str("0123456789acdefghjkmnpqrstuvwxyz");
        let json = spec
            .encoding()
            .map_err(|_| RestoreError::Malformed)?
            .decode(b32.as_bytes())
            .map_err(|_| RestoreError::Malformed)?;
        let mut doc: serde_json::Value =
            serde_json::from_slice(&json).map_err(|_| RestoreError::Malformed)?;
        let stamped = doc
            .get("seal")
            .and_then(|v| v.as_str())
            .ok_or(RestoreError::Malformed)?
            .to_string();
        if let serde_json::Value::Object(m) = &mut doc {
            m.remove("seal");
        }
        let sealed: SealedCap = serde_json::from_value(doc).map_err(|_| RestoreError::Malformed)?;
        Ok((sealed, stamped))
    }

    /// **Restore** the token to a live cap under the host [`SealKey`]. Fails
    /// [`BadSeal`](RestoreError::BadSeal) if the host MAC does not re-verify (tampered
    /// or forged), then [`Inert`](RestoreError::Inert) if `presenter_key` is not the
    /// sealed owner. On success the returned cap reflects the *whole* attenuation
    /// chain.
    pub fn restore(
        &self,
        presenter_key: &str,
        seal: &SealKey,
    ) -> Result<DreggCapRef, RestoreError> {
        let (sealed, stamped) = self.decode()?;
        // Authenticity first: a token not sealed by THIS host (forged) or altered
        // (tampered) is rejected before its claimed fields are trusted at all.
        if !ct_eq(&sealed.seal(seal), &stamped) {
            return Err(RestoreError::BadSeal);
        }
        if sealed.owner != presenter_key {
            return Err(RestoreError::Inert);
        }
        Ok(DreggCapRef {
            target: sealed.target.clone(),
            interface_id: sealed.interface_id,
            facets: sealed.effective_facets(),
        })
    }

    /// **Attenuate** a persisted SturdyRef: append a facet-restriction caveat and
    /// re-seal (same owner, same host key). Attenuation only ever narrows — restricting
    /// to facets the chain does not already grant simply yields the intersection, never
    /// more. The input token must itself re-verify under `seal` (no attenuating a forgery
    /// into validity).
    pub fn attenuate(
        &self,
        restrict_to: &[&str],
        seal: &SealKey,
    ) -> Result<SturdyRef, RestoreError> {
        let (mut sealed, stamped) = self.decode()?;
        if !ct_eq(&sealed.seal(seal), &stamped) {
            return Err(RestoreError::BadSeal);
        }
        sealed.caveats.push(Caveat::RestrictFacets(
            restrict_to.iter().map(|s| s.to_string()).collect(),
        ));
        Ok(sealed.encode(seal))
    }
}

// ---------------------------------------------------------------------------
// descriptor → Pred (the typed powerbox request, over dregg's matching algebra).
// ---------------------------------------------------------------------------

/// A boolean predicate over a candidate cap — the prototype's projection of dregg's
/// one matching algebra (`Pred`). A `PowerboxDescriptor` compiles to one of these,
/// and the trusted picker filters held caps by it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pred {
    /// Always matches (the empty query).
    Any,
    /// The cap's resource kind is this interface id.
    InterfaceIs(u64),
    /// The cap names this exact target.
    TargetIs(String),
    /// The cap carries this facet.
    HasFacet(String),
    /// All sub-predicates hold.
    AllOf(Vec<Pred>),
    /// At least one sub-predicate holds.
    AnyOf(Vec<Pred>),
}

impl Pred {
    pub fn matches(&self, cap: &DreggCapRef) -> bool {
        match self {
            Pred::Any => true,
            Pred::InterfaceIs(id) => cap.interface_id == *id,
            Pred::TargetIs(t) => &cap.target == t,
            Pred::HasFacet(f) => cap.facets.iter().any(|x| x == f),
            Pred::AllOf(ps) => ps.iter().all(|p| p.matches(cap)),
            Pred::AnyOf(ps) => ps.iter().any(|p| p.matches(cap)),
        }
    }
}

/// One typed tag of a powerbox descriptor (`PowerboxDescriptor.Tag`): the interface
/// type-id of the resource kind, plus the facets the value asks for.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Tag {
    /// The capnp interface type-id — the *kind* of resource requested.
    pub interface_id: u64,
    /// The facets the descriptor's `value` implies the app needs.
    #[serde(default)]
    pub required_facets: Vec<String>,
}

/// A Sandstorm powerbox descriptor: a list of tags that must all match (one shape of
/// request). A full query is a list of descriptors (alternatives) — see [`compile`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PowerboxDescriptor {
    pub tags: Vec<Tag>,
}

impl PowerboxDescriptor {
    /// Compile this descriptor to a `Pred`: each tag becomes `InterfaceIs(id)` ∧ the
    /// facet requirements; all tags must hold.
    pub fn to_pred(&self) -> Pred {
        let mut conj = Vec::new();
        for tag in &self.tags {
            conj.push(Pred::InterfaceIs(tag.interface_id));
            for f in &tag.required_facets {
                conj.push(Pred::HasFacet(f.clone()));
            }
        }
        if conj.is_empty() {
            Pred::Any
        } else {
            Pred::AllOf(conj)
        }
    }
}

/// Compile a powerbox **query** (a list of descriptors, matched as alternatives) to a
/// single `Pred`. This is the descriptor↔Pred weld the plan §4.2(1) calls for.
pub fn compile(query: &[PowerboxDescriptor]) -> Pred {
    match query.len() {
        0 => Pred::Any,
        1 => query[0].to_pred(),
        _ => Pred::AnyOf(query.iter().map(|d| d.to_pred()).collect()),
    }
}

/// The trusted **picker**: from the principal's *own* held caps, return those that
/// satisfy the query — exactly the set the system UI would show the user, and never
/// any cap the principal does not hold. (`Powerbox::present`.)
pub fn present<'a>(held: &'a [DreggCapRef], query: &[PowerboxDescriptor]) -> Vec<&'a DreggCapRef> {
    let pred = compile(query);
    held.iter().filter(|c| pred.matches(c)).collect()
}

// ---------------------------------------------------------------------------
// The grant ceremony (the designation → a strictly-attenuating, witnessed turn).
// ---------------------------------------------------------------------------

/// A capability an app **lacks and requests** through the powerbox, named by the
/// *shape* of authority it needs (a descriptor query + the facets it ultimately
/// wants), never a specific resource it was not granted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PowerboxRequest {
    /// The requesting grain/app-cell (who will receive the grant).
    pub requester: String,
    /// The facets of authority requested (e.g. ["view"] to read another grain).
    pub requested_facets: Vec<String>,
}

/// A powerbox **grant**: the trusted UI minting a fresh, attenuated cap into the
/// requester's c-list. The dregg `Effect::GrantCapability` turn, modeled.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PowerboxGrant {
    /// The principal whose held authority backs the grant (the user / cockpit
    /// principal — the powerbox holds NO ambient authority of its own).
    pub from_principal: String,
    /// The app-cell receiving the cap.
    pub to_app: String,
    /// The cap conferred — necessarily `⊆` the principal's held cap.
    pub conferred: DreggCapRef,
    /// The persisted, owner-sealed SturdyRef for the conferred cap (sealed to the
    /// receiving app under the host key) — the durable form of the grant.
    pub sturdyref: SturdyRef,
    /// A stand-in for the real `TurnReceipt`: the grant is a witnessed turn, so the
    /// delegation is provable to a light client (the half Sandstorm lacks).
    pub receipt: String,
}

/// Why a powerbox grant was refused.
#[derive(Debug, PartialEq, Eq)]
pub enum GrantError {
    /// The principal does not hold a cap that dominates the request → designating it
    /// would **amplify** authority. Refused in-band (the anti-ghost tooth).
    Amplification,
    /// The held cap names a different target than the request expects.
    WrongTarget,
}

impl std::fmt::Display for GrantError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GrantError::Amplification => {
                write!(
                    f,
                    "powerbox grant refused: would amplify authority (granted ⊄ held)"
                )
            }
            GrantError::WrongTarget => write!(f, "powerbox grant refused: target mismatch"),
        }
    }
}
impl std::error::Error for GrantError {}

impl PowerboxGrant {
    /// The **grant ceremony**, modeled. The trusted UI mints `conferred` to the
    /// requester, backed by `held` (the principal's own cap), and seals a SturdyRef
    /// for the receiving app under the host [`SealKey`]. Refuses any grant that is not
    /// a strict attenuation of the held authority — `granted ⊆ held` — so you can
    /// never confer authority you do not hold (no amplification, no ambient authority).
    /// Mirrors `starbridge-v2/src/powerbox.rs::Powerbox::grant`.
    pub fn mint(
        from_principal: impl Into<String>,
        to_app: impl Into<String>,
        held: &DreggCapRef,
        conferred: DreggCapRef,
        seal: &SealKey,
    ) -> Result<PowerboxGrant, GrantError> {
        if held.target != conferred.target {
            return Err(GrantError::WrongTarget);
        }
        // The load-bearing check: granted ⊆ held.
        if !held.dominates(&conferred) {
            return Err(GrantError::Amplification);
        }
        let from_principal = from_principal.into();
        let to_app = to_app.into();
        // The durable form: a SturdyRef sealed to the *receiving app* under the host
        // key — only it can restore the cap; a leaked token is inert, a forged one
        // never restores.
        let sturdyref = conferred.seal_for(&to_app, seal);
        let receipt = format!(
            "receipt:grant:{}->{}:{}",
            from_principal, to_app, sturdyref.0
        );
        Ok(PowerboxGrant {
            from_principal,
            to_app,
            conferred,
            sturdyref,
            receipt,
        })
    }

    /// Satisfy a [`PowerboxRequest`] from a principal's held cap, attenuating the
    /// held authority down to *exactly* the requested facets (never more). This is
    /// the picker→designate→mint path in one call.
    pub fn satisfy(
        held: &DreggCapRef,
        principal: impl Into<String>,
        request: &PowerboxRequest,
        seal: &SealKey,
    ) -> Result<PowerboxGrant, GrantError> {
        let conferred = DreggCapRef {
            target: held.target.clone(),
            interface_id: held.interface_id,
            facets: request.requested_facets.clone(),
        };
        PowerboxGrant::mint(principal, request.requester.clone(), held, conferred, seal)
    }

    /// The full powerbox flow from a typed query: compile the descriptor → pick the
    /// designated held cap (must satisfy the query) → mint the attenuated grant,
    /// sealed for the requester. Returns `WrongTarget` if `designated` is not among
    /// the principal's held caps that match the query.
    pub fn from_query(
        held: &[DreggCapRef],
        principal: impl Into<String>,
        requester: impl Into<String>,
        query: &[PowerboxDescriptor],
        designated: &DreggCapRef,
        requested_facets: &[&str],
        seal: &SealKey,
    ) -> Result<PowerboxGrant, GrantError> {
        // The picker only ever offers caps the principal holds that match the query.
        let offered = present(held, query);
        if !offered.contains(&designated) {
            return Err(GrantError::WrongTarget);
        }
        let conferred = DreggCapRef {
            target: designated.target.clone(),
            interface_id: designated.interface_id,
            facets: requested_facets.iter().map(|s| s.to_string()).collect(),
        };
        PowerboxGrant::mint(principal, requester, designated, conferred, seal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A deterministic host seal key for the tests — the secret the host holds and an
    /// attacker does not.
    fn host_seal() -> SealKey {
        SealKey::from_secret(b"test-host-secret")
    }

    // ----- the grant ceremony (preserved from the prototype) -----

    #[test]
    fn a_grant_within_held_authority_succeeds_and_is_receipted() {
        let seal = host_seal();
        let held = DreggCapRef::new("cell:pad7", &["view", "edit"]);
        let conferred = DreggCapRef::new("cell:pad7", &["view"]);
        let grant =
            PowerboxGrant::mint("user:alice", "app:reader", &held, conferred, &seal).unwrap();
        assert_eq!(grant.conferred.facets, vec!["view"]);
        assert!(grant.receipt.contains("user:alice->app:reader"));
        // The grant carries a durable SturdyRef sealed to the receiving app.
        assert!(grant.sturdyref.0.starts_with("dga1_"));
    }

    #[test]
    fn over_granting_is_refused_in_band() {
        let seal = host_seal();
        let held = DreggCapRef::new("cell:pad7", &["view"]);
        let conferred = DreggCapRef::new("cell:pad7", &["view", "edit"]);
        assert_eq!(
            PowerboxGrant::mint("user:alice", "app:evil", &held, conferred, &seal),
            Err(GrantError::Amplification)
        );
    }

    #[test]
    fn you_cannot_grant_over_a_target_you_do_not_hold() {
        let seal = host_seal();
        let held = DreggCapRef::new("cell:pad7", &["view", "edit"]);
        let conferred = DreggCapRef::new("cell:OTHER", &["view"]);
        assert_eq!(
            PowerboxGrant::mint("user:alice", "app:x", &held, conferred, &seal),
            Err(GrantError::WrongTarget)
        );
    }

    #[test]
    fn powerbox_request_is_satisfied_by_attenuation() {
        let seal = host_seal();
        let held = DreggCapRef::new("cell:pad7", &["view", "edit"]);
        let req = PowerboxRequest {
            requester: "app:reader".into(),
            requested_facets: vec!["view".into()],
        };
        let grant = PowerboxGrant::satisfy(&held, "user:alice", &req, &seal).unwrap();
        assert_eq!(grant.to_app, "app:reader");
        assert_eq!(grant.conferred.facets, vec!["view"]);
    }

    #[test]
    fn a_request_for_more_than_held_is_refused() {
        let seal = host_seal();
        let held = DreggCapRef::new("cell:pad7", &["view"]);
        let req = PowerboxRequest {
            requester: "app:reader".into(),
            requested_facets: vec!["view".into(), "edit".into()],
        };
        assert_eq!(
            PowerboxGrant::satisfy(&held, "user:alice", &req, &seal),
            Err(GrantError::Amplification)
        );
    }

    // ----- descriptor → Pred → the picker -----

    #[test]
    fn descriptor_compiles_to_a_pred_and_filters_the_picker() {
        // The principal holds three caps of different kinds.
        const CALENDAR: u64 = 0xca1_e9da_0000_0001;
        const FILE: u64 = 0xf11e_0000_0000_0002;
        let held = vec![
            DreggCapRef::new_typed("cell:cal1", CALENDAR, &["view", "edit"]),
            DreggCapRef::new_typed("cell:cal2", CALENDAR, &["view"]),
            DreggCapRef::new_typed("cell:file1", FILE, &["view", "edit"]),
        ];
        // An app requests "any calendar I can edit" — by type, not instance.
        let query = vec![PowerboxDescriptor {
            tags: vec![Tag {
                interface_id: CALENDAR,
                required_facets: vec!["edit".into()],
            }],
        }];
        let offered = present(&held, &query);
        // Only the editable calendar matches (not the view-only one, not the file).
        assert_eq!(offered.len(), 1);
        assert_eq!(offered[0].target, "cell:cal1");
    }

    #[test]
    fn an_empty_query_matches_anything_a_disjunction_matches_either() {
        let held = vec![DreggCapRef::new_typed("cell:a", 7, &["view"])];
        assert_eq!(present(&held, &[]).len(), 1);
        let q = vec![
            PowerboxDescriptor {
                tags: vec![Tag {
                    interface_id: 7,
                    required_facets: vec![],
                }],
            },
            PowerboxDescriptor {
                tags: vec![Tag {
                    interface_id: 99,
                    required_facets: vec![],
                }],
            },
        ];
        assert_eq!(present(&held, &q).len(), 1);
    }

    #[test]
    fn the_full_query_flow_grants_the_designated_cap() {
        const CALENDAR: u64 = 42;
        let seal = host_seal();
        let held = vec![DreggCapRef::new_typed(
            "cell:cal1",
            CALENDAR,
            &["view", "edit"],
        )];
        let query = vec![PowerboxDescriptor {
            tags: vec![Tag {
                interface_id: CALENDAR,
                required_facets: vec!["view".into()],
            }],
        }];
        let designated = held[0].clone();
        let grant = PowerboxGrant::from_query(
            &held,
            "user:alice",
            "app:scheduler",
            &query,
            &designated,
            &["view"],
            &seal,
        )
        .unwrap();
        assert_eq!(grant.conferred.facets, vec!["view"]);
        assert_eq!(grant.conferred.interface_id, CALENDAR);
    }

    #[test]
    fn from_query_refuses_a_cap_the_principal_does_not_hold() {
        let seal = host_seal();
        let held = vec![DreggCapRef::new_typed("cell:cal1", 42, &["view"])];
        let query = vec![PowerboxDescriptor {
            tags: vec![Tag {
                interface_id: 42,
                required_facets: vec![],
            }],
        }];
        // Designate a cap that is NOT in the held set — the picker never offered it.
        let forged = DreggCapRef::new_typed("cell:cal2", 42, &["view", "edit"]);
        assert_eq!(
            PowerboxGrant::from_query(&held, "u", "app:x", &query, &forged, &["edit"], &seal),
            Err(GrantError::WrongTarget)
        );
    }

    // ----- SturdyRef ↔ dga1_ cap: seal / restore / leak / attenuate -----

    #[test]
    fn sturdyref_roundtrips_for_its_owner() {
        let seal = host_seal();
        let cap = DreggCapRef::new_typed("cell:pad7", 5, &["view", "edit"]);
        let sref = cap.seal_for("key:app-reader", &seal);
        assert!(sref.0.starts_with("dga1_"));
        let restored = sref.restore("key:app-reader", &seal).unwrap();
        assert_eq!(restored.target, "cell:pad7");
        assert_eq!(restored.interface_id, 5);
        assert_eq!(restored.facets, vec!["edit", "view"]);
    }

    #[test]
    fn a_leaked_sturdyref_is_inert() {
        let seal = host_seal();
        let cap = DreggCapRef::new("cell:pad7", &["view", "edit"]);
        let sref = cap.seal_for("key:owner", &seal);
        // Anyone but the sealed owner gets nothing — sealFor: Owner.
        assert_eq!(sref.restore("key:thief", &seal), Err(RestoreError::Inert));
        // The owner still restores it fine.
        assert!(sref.restore("key:owner", &seal).is_ok());
    }

    /// **Red-team #PB-1 PoC (forgery refused).** An attacker fabricates a SturdyRef
    /// with an attacker-chosen owner/target/facets — but *without* the host secret.
    /// They can only seal under a key they control (or stamp a hand-computed hash);
    /// either way the host MAC does not re-verify, so `restore` on the real host
    /// refuses. Under the old unkeyed-SHA-256 scheme this `restore` *succeeded* and
    /// minted `["admin","edit","view"]` over `cell:victim-secret`.
    #[test]
    fn a_forged_sturdyref_not_sealed_by_this_host_is_refused() {
        let host = host_seal();
        // The attacker does not hold the host secret; the best they can do is seal
        // under their own guessed key.
        let attacker_key = SealKey::from_secret(b"attacker-guess");
        let forged = DreggCapRef::new("cell:victim-secret", &["view", "edit", "admin"])
            .seal_for("u:mallory", &attacker_key);
        // Presented to the host, which restores under ITS secret → inert (bad seal).
        assert_eq!(
            forged.restore("u:mallory", &host),
            Err(RestoreError::BadSeal)
        );
    }

    /// Even hand-stamping the *previous* (unkeyed SHA-256) integrity hash an attacker
    /// could compute does not help: the host MAC under the secret is what is checked.
    #[test]
    fn a_hand_stamped_integrity_hash_does_not_forge_a_seal() {
        let host = host_seal();
        // Build a token JSON exactly as `encode` would, but stamp the OLD unkeyed
        // hash the attacker can compute over the public fields.
        let sealed = SealedCap {
            target: "cell:victim".into(),
            interface_id: 0,
            base_facets: vec!["admin".into()],
            owner: "u:mallory".into(),
            caveats: Vec::new(),
        };
        let mut doc = serde_json::to_value(&sealed).unwrap();
        let mut h = Sha256::new();
        h.update(sealed.target.as_bytes());
        h.update(sealed.owner.as_bytes());
        doc["seal"] = serde_json::Value::String(base32(&h.finalize()));
        let json = serde_json::to_vec(&doc).unwrap();
        let forged = SturdyRef(format!("dga1_{}", base32(&json)));
        assert_eq!(
            forged.restore("u:mallory", &host),
            Err(RestoreError::BadSeal)
        );
    }

    /// The host-sealed legit path still works end-to-end (sanity that the fix did not
    /// break the honest flow).
    #[test]
    fn a_host_sealed_sturdyref_restores_for_the_owner() {
        let host = host_seal();
        let sref = DreggCapRef::new("cell:pad7", &["view"]).seal_for("u:alice", &host);
        let cap = sref.restore("u:alice", &host).unwrap();
        assert_eq!(cap.target, "cell:pad7");
        assert_eq!(cap.facets, vec!["view"]);
    }

    /// A token sealed by host A does not restore on host B (a different secret).
    #[test]
    fn a_token_sealed_by_another_host_is_inert_here() {
        let host_a = SealKey::from_secret(b"host-a");
        let host_b = SealKey::from_secret(b"host-b");
        let sref = DreggCapRef::new("cell:pad7", &["view"]).seal_for("u:alice", &host_a);
        assert_eq!(sref.restore("u:alice", &host_b), Err(RestoreError::BadSeal));
        assert!(sref.restore("u:alice", &host_a).is_ok());
    }

    #[test]
    fn a_tampered_sturdyref_fails_to_restore() {
        let seal = host_seal();
        let cap = DreggCapRef::new("cell:pad7", &["view"]);
        let sref = cap.seal_for("key:owner", &seal);
        // Corrupt one base32 symbol of the token body.
        let mut s = sref.0.clone();
        let last = s.pop().unwrap();
        s.push(if last == '0' { '1' } else { '0' });
        let bad = SturdyRef(s);
        // Either it no longer decodes, or the seal no longer re-verifies.
        match bad.restore("key:owner", &seal) {
            Err(RestoreError::BadSeal) | Err(RestoreError::Malformed) => {}
            other => panic!("tamper not caught: {other:?}"),
        }
    }

    #[test]
    fn attenuating_a_sturdyref_only_narrows() {
        let seal = host_seal();
        let cap = DreggCapRef::new("cell:pad7", &["view", "edit"]);
        let sref = cap.seal_for("key:owner", &seal);
        // Delegate a view-only persistent sub-cap.
        let narrowed = sref.attenuate(&["view"], &seal).unwrap();
        let restored = narrowed.restore("key:owner", &seal).unwrap();
        assert_eq!(restored.facets, vec!["view"]);
        // Asking for `edit` back via a later caveat cannot re-grant it: the chain
        // intersection has already dropped it.
        let reamped = narrowed.attenuate(&["view", "edit"], &seal).unwrap();
        assert_eq!(
            reamped.restore("key:owner", &seal).unwrap().facets,
            vec!["view"]
        );
    }

    #[test]
    fn sturdyref_is_stable_in_the_caps_facet_order() {
        let seal = host_seal();
        let a = DreggCapRef::new("cell:pad7", &["edit", "view"]).seal_for("k", &seal);
        let b = DreggCapRef::new("cell:pad7", &["view", "edit"]).seal_for("k", &seal);
        assert_eq!(a, b);
    }
}
