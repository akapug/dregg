//! The caveat layer (`Caveat`) and the verification context (`Context`).
//!
//! `Caveat` mirrors `Dregg2.Authority.Caveat.Caveat` exactly: a caveat is
//! either **local** (a checkable predicate over the request context — here the
//! [`Pred`] algebra) or **third-party** (names a gateway whose *discharge* must
//! be presented). The two layers are deliberately separate types so that
//! Boolean negation/disjunction over a third-party caveat is inexpressible —
//! the same stratification the Lean inductive has.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use super::chain::Discharge;
use super::pred::Pred;

/// One caveat installed on a credential block.
///
/// Lean: `Dregg2.Authority.Caveat.Caveat` — `local (check : Ctx → Bool)` or
/// `thirdParty (gateway : Gateway)`. A credential admits a request iff **all**
/// caveats across all blocks are satisfied (`Token.admits`, the fail-closed
/// meet); satisfaction per caveat is `Caveat.ok`: the local predicate holds,
/// or the named gateway has discharged.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Caveat {
    /// A first-party caveat: a [`Pred`] over the verification context.
    /// Lean: `Caveat.local`.
    FirstParty(Pred),
    /// A third-party caveat: verification additionally requires a
    /// [`Discharge`] token signed by `gateway` and **bound to this exact
    /// credential** (the macaroon discharge pattern,
    /// `Dregg2.Authority.MacaroonDischarge`). Lean: `Caveat.thirdParty`.
    ThirdParty {
        /// The gateway's ed25519 public key (32 bytes): the key the discharge
        /// must verify under. Offline-verifiable like everything else — the
        /// verifier needs no contact with the gateway, only its key.
        gateway: [u8; 32],
        /// An opaque identifier correlating this caveat with its discharge
        /// (the macaroon caveat id): the gateway knows what predicate it
        /// stands for; the verifier only matches it byte-for-byte.
        caveat_id: Vec<u8>,
        /// Human-readable statement of what the gateway attests (rides into
        /// [`Caveat::explain`]; never evaluated).
        hint: String,
    },
}

impl Caveat {
    /// One-line human prose (the `sdk/src/explain.rs` convention).
    pub fn explain(&self) -> String {
        match self {
            Caveat::FirstParty(p) => format!("requires {}", p.explain()),
            Caveat::ThirdParty {
                gateway,
                caveat_id,
                hint,
            } => format!(
                "requires third-party approval from gateway {} for caveat id {}{}",
                super::hex(&gateway[..8]),
                super::hex(caveat_id),
                if hint.is_empty() {
                    String::new()
                } else {
                    format!(" ({hint:?})")
                }
            ),
        }
    }
}

/// The verification context — everything a caveat may be evaluated against.
///
/// Lean: the abstract `Ctx` binding-site of `Dregg2.Authority.Caveat` ("the
/// `AuthRequest` facts a caveat is evaluated against: block height, action,
/// resource, sender, …"), instantiated concretely as one monotone clock plus a
/// bag of request attributes; plus the `Discharges` map (which gateways have
/// produced a resolution), carried here as the presented discharge tokens
/// themselves.
///
/// Supplied entirely by the caller: verification is offline and deterministic —
/// same context, same verdict.
#[derive(Clone, Debug, Default)]
pub struct Context {
    clock: Option<u64>,
    attrs: BTreeMap<String, String>,
    discharges: Vec<Discharge>,
}

impl Context {
    /// An empty context: no clock, no attributes, no discharges. Temporal
    /// caveats evaluated against it refuse (fail-closed — see
    /// [`Unbound`](super::Unbound)).
    pub fn new() -> Self {
        Self::default()
    }

    /// Supply the clock reading (unix seconds or block height — whichever one
    /// monotone clock the deployment standardizes on; mint and verify must
    /// agree on the unit). Explicit, never wall-clock: offline checks are
    /// reproducible.
    pub fn at(mut self, clock: u64) -> Self {
        self.clock = Some(clock);
        self
    }

    /// Bind a request attribute (e.g. `tool` = `read`).
    pub fn attr(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.attrs.insert(key.into(), value.into());
        self
    }

    /// Present a third-party [`Discharge`] alongside the credential.
    pub fn discharge(mut self, d: Discharge) -> Self {
        self.discharges.push(d);
        self
    }

    pub(crate) fn clock(&self) -> Option<u64> {
        self.clock
    }

    pub(crate) fn lookup_attr(&self, key: &str) -> Option<&str> {
        self.attrs.get(key).map(String::as_str)
    }

    pub(crate) fn discharges(&self) -> &[Discharge] {
        &self.discharges
    }
}
