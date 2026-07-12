//! The transport-free serving core: one custodied grain, served through the
//! upstream `HttpBridge` with capability-derived headers, checkpointed
//! archive-first after every state-moving request.
//!
//! Everything capability-shaped is REUSED from `sandstorm-bridge`, not
//! reimplemented: `HttpBridge::serve` derives the permission set on the real
//! `dregg-auth` rail (`derive_permissions` re-verifies the `dga1_` ed25519
//! caveat chain per request), injects the `X-Sandstorm-*` headers, refuses an
//! empty permission set with `403` before the body runs, and recommits the
//! `/var` heap to its Poseidon2 [`DataRoot`]. This module adds the operated
//! pieces: custody-backed durability and the grain lifecycle bookkeeping.

use dregg_auth::credential::PublicKey;
use sandstorm_bridge::bridge::{GrainWorkload, HttpBridge, HttpRequest, HttpResponse, Session};
use sandstorm_bridge::cell::{DataRoot, Umem};
use sandstorm_bridge::grain::{GrainCell, GrainError, GrainState};
use thiserror::Error;

use crate::body::{GrainBody, GrainBodyKind};
use crate::custody::{
    GrainCustodyAnchorV1, GrainCustodyError, GrainCustodyRuntime, GrainCustodyStatusV1,
};

/// The principal one HTTP request presents: transport-carried identity fields
/// plus the `dga1_` grain capability token. The token is re-verified on the
/// real rail per request; `presenter_subject` is matched against the token's
/// `subject` caveat. NOTE the honest residual: the transport client ASSERTS
/// the presenter subject — binding it to an authenticated principal is the
/// forward-auth seam, not this weld (see `RESIDUALS`).
#[derive(Clone, Debug)]
pub struct PresentedSession {
    pub user_id: String,
    pub username: String,
    pub session_id: String,
    /// The presented `dga1_…` capability token.
    pub cap_token: String,
    pub presenter_subject: String,
}

/// One served request's outcome: the grain response plus the committed root
/// evidence (and, when the root moved, the durable custody anchor advance).
#[derive(Clone, Debug)]
pub struct GrainServed {
    pub response: HttpResponse,
    /// The `/var` commitment after this request.
    pub data_root: DataRoot,
    /// Whether this request moved the root and was durably checkpointed.
    pub checkpointed: bool,
    /// The custody head anchor after this request — the value an operator
    /// (later: the House schema slot) persists.
    pub anchor: GrainCustodyAnchorV1,
}

#[derive(Debug, Error)]
pub enum GrainServeError {
    #[error("grain custody refused: {0}")]
    Custody(#[from] GrainCustodyError),
    #[error("grain lifecycle refused: {0}")]
    Grain(#[from] GrainError),
    #[error("custody archive holds no installed grain")]
    NotInstalled,
    #[error("custody archive is not settled: {0}")]
    CustodyNotReady(&'static str),
    #[error("daemon transport refused: {0}")]
    Transport(String),
}

/// One custodied grain behind the serving surface.
pub struct GrainServer {
    custody: GrainCustodyRuntime,
    grain: GrainCell,
    var: Umem,
    body: Box<dyn GrainBody>,
    host_public: PublicKey,
    anchor: GrainCustodyAnchorV1,
}

impl GrainServer {
    /// Open the serving core over settled custody: requires an installed grain
    /// and a `Ready` archive, wakes the grain under the caller-attested funded
    /// lease, and adopts the custody head `/var` and anchor.
    ///
    /// # Errors
    ///
    /// Refuses an empty or unsettled archive and an unfunded wake.
    pub fn open(
        custody: GrainCustodyRuntime,
        host_public: PublicKey,
        body: Box<dyn GrainBody>,
        lease_funded: bool,
    ) -> Result<Self, GrainServeError> {
        let anchor = match custody.status() {
            GrainCustodyStatusV1::Ready { anchor } => anchor,
            GrainCustodyStatusV1::Empty => return Err(GrainServeError::NotInstalled),
            GrainCustodyStatusV1::RecoveryRequired { .. } => {
                return Err(GrainServeError::CustodyNotReady(
                    "archive-ahead recovery must be acknowledged before serving",
                ));
            }
            GrainCustodyStatusV1::Poisoned { .. } => {
                return Err(GrainServeError::CustodyNotReady("custody is poisoned"));
            }
        };
        let installation = custody
            .installation()
            .ok_or(GrainServeError::NotInstalled)?;
        let mut grain = GrainCell::create(
            installation.grain_cell_id.clone(),
            installation.owner.clone(),
            installation.spec.clone(),
        );
        grain.wake(lease_funded)?;
        grain.data_root = Some(anchor.data_root.clone());
        let var = custody.head_var();
        Ok(Self {
            custody,
            grain,
            var,
            body,
            host_public,
            anchor,
        })
    }

    #[must_use]
    pub fn grain_cell_id(&self) -> &str {
        &self.grain.cell_id
    }

    #[must_use]
    pub fn app_id(&self) -> &str {
        &self.grain.spec.app_id.0
    }

    #[must_use]
    pub fn body_kind(&self) -> GrainBodyKind {
        self.body.kind()
    }

    #[must_use]
    pub fn grain_state(&self) -> GrainState {
        self.grain.state
    }

    /// The current committed `/var` root.
    #[must_use]
    pub fn data_root(&self) -> DataRoot {
        self.var.commit()
    }

    /// The custody head anchor an operator persists.
    #[must_use]
    pub fn anchor(&self) -> &GrainCustodyAnchorV1 {
        &self.anchor
    }

    /// Serve one request end-to-end: derive the presented cap's permission set
    /// on the real rail, inject the `X-Sandstorm-*` headers, run the mounted
    /// body over the grain's real `/var` heap, and — when the committed root
    /// moved — durably checkpoint archive-first before answering.
    ///
    /// An empty derived permission set (missing/forged/leaked/expired cap, a
    /// cap for another grain, or no declared facet granted) is answered `403`
    /// by the upstream bridge with no effect. [`crate::body::NoBody`] answers
    /// `503` naming the missing exec weld.
    ///
    /// # Errors
    ///
    /// Refuses when the durable checkpoint cannot be appended (the response is
    /// NOT returned in that case — durability precedes acknowledgement).
    pub fn serve(
        &mut self,
        presented: &PresentedSession,
        request: &HttpRequest,
        now_unix_secs: u64,
    ) -> Result<GrainServed, GrainServeError> {
        let session = Session::presenting(
            presented.user_id.clone(),
            presented.username.clone(),
            presented.session_id.clone(),
            presented.cap_token.clone(),
            presented.presenter_subject.clone(),
        );
        let workload: &dyn GrainWorkload = self.body.as_ref();
        let served = HttpBridge::serve(
            workload,
            &self.grain.cell_id,
            &session,
            &self.host_public,
            &self.grain.spec.declared_permissions,
            now_unix_secs,
            &mut self.var,
            request,
        );
        self.grain.touch(now_unix_secs);
        let checkpointed = served.new_data_root.0 != self.anchor.data_root;
        if checkpointed {
            // Archive-first: the durable append happens BEFORE the response is
            // acknowledged; a failed append poisons custody and refuses.
            self.anchor = self.custody.checkpoint(&self.var)?;
            self.grain.data_root = Some(self.anchor.data_root.clone());
        }
        Ok(GrainServed {
            response: served.response,
            data_root: served.new_data_root,
            checkpointed,
            anchor: self.anchor.clone(),
        })
    }

    /// Sleep the grain (checkpointing its current `/var` commitment) — the
    /// daemon calls this on shutdown so the lifecycle state is honest.
    ///
    /// # Errors
    ///
    /// Refuses a sleep from any state but `Running`, or a failed durable
    /// checkpoint.
    pub fn sleep(&mut self) -> Result<GrainCustodyAnchorV1, GrainServeError> {
        self.anchor = self.custody.checkpoint(&self.var)?;
        self.grain.sleep(self.var.commit())?;
        Ok(self.anchor.clone())
    }
}
