//! SDK adapter for the SDK-free `dregg-tool-gateway` core.
//!
//! The extracted core owns the delegated-policy gate, rate meter, routed inbox,
//! and `TurnReceipt` envelope. This module keeps the previous SDK-facing API:
//! it admits a real [`SubAgent`] through [`AgentRuntime`], installs the mandate
//! program on the worker cell, and maps core execution errors back to
//! [`SdkError`].

use dregg_cell::CellId;
use dregg_token::Attenuation;
use dregg_tool_gateway as core;
use dregg_turn::{Effect, Turn, TurnReceipt};

use crate::cipherclerk::HeldToken;
use crate::error::SdkError;
use crate::runtime::{AgentRuntime, SubAgent};

pub use core::{
    CALLS_MADE_SLOT, DeliveryReceipt, GatewayRefusal, RoutedHandle, RoutedResult, RoutedStatus,
    ToolGrant, ToolReceipt, deleg_admit, mandate_program,
};

/// The error surface of [`ToolGateway::invoke`]: either an in-band mandate
/// refusal, or an underlying SDK/executor error.
#[derive(Debug)]
pub enum ToolCallError {
    /// The delegated policy refused the call in-band.
    Refused(GatewayRefusal),
    /// An underlying SDK/executor error.
    Sdk(SdkError),
}

impl std::fmt::Display for ToolCallError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ToolCallError::Refused(r) => write!(f, "mandate refused tool call: {r}"),
            ToolCallError::Sdk(e) => write!(f, "tool call execution error: {e}"),
        }
    }
}

impl std::error::Error for ToolCallError {}

impl From<SdkError> for ToolCallError {
    fn from(e: SdkError) -> Self {
        ToolCallError::Sdk(e)
    }
}

fn map_core_error(err: core::ToolCallError<SdkError>) -> ToolCallError {
    match err {
        core::ToolCallError::Refused(r) => ToolCallError::Refused(r),
        core::ToolCallError::Execution(e) => ToolCallError::Sdk(e),
        core::ToolCallError::Route(reason) => ToolCallError::Sdk(SdkError::Rejected(reason)),
    }
}

/// SDK-owned turn acceptor: a cap-gated worker [`SubAgent`].
struct SdkTurnAcceptor {
    worker: SubAgent,
}

impl SdkTurnAcceptor {
    fn worker(&self) -> &SubAgent {
        &self.worker
    }
}

impl core::GatewayTurnAcceptor for SdkTurnAcceptor {
    type Error = SdkError;

    fn cell_id(&self) -> CellId {
        self.worker.cell_id()
    }

    fn accept_turn(&self, method: &str, effects: Vec<Effect>) -> Result<TurnReceipt, Self::Error> {
        self.worker.execute_method(method, effects)
    }

    fn build_routed_turn(&self, method: &str, nonce: u64, effects: Vec<Effect>) -> Turn {
        core::build_token_routed_turn(
            self.worker.cell_id(),
            method,
            nonce,
            self.worker.cap_token().to_vec(),
            [0u8; 32],
            effects,
        )
    }
}

/// THE GATEWAY — a mandated inhabitant wrapping a cap-gated SDK worker.
pub struct ToolGateway {
    inner: core::ToolGateway<SdkTurnAcceptor>,
}

impl ToolGateway {
    /// Admit a worker into the world under a delegated tool mandate.
    pub fn admit(
        runtime: &AgentRuntime,
        parent_token: &HeldToken,
        grant: ToolGrant,
    ) -> Result<Self, SdkError> {
        let worker = runtime.spawn_sub_agent_scoped(
            &Attenuation::default(),
            parent_token,
            &[grant.tool_method.as_str()],
        )?;
        let worker_cell = worker.cell_id();

        {
            let mut ledger = runtime.ledger().lock().unwrap();
            ledger
                .update_with(&worker_cell, |cell| {
                    cell.program = mandate_program(grant.rate_limit);
                })
                .map_err(|e| SdkError::Rejected(format!("install mandate program: {e}")))?;
        }

        Ok(Self {
            inner: core::ToolGateway::new(grant, SdkTurnAcceptor { worker }),
        })
    }

    /// The grantor's pinned mandate.
    pub fn grant(&self) -> &ToolGrant {
        self.inner.grant()
    }

    /// The worker cell id.
    pub fn worker_cell(&self) -> CellId {
        self.inner.worker_cell()
    }

    /// The calls made so far under this mandate.
    pub fn calls_made(&self) -> i64 {
        self.inner.calls_made()
    }

    /// Test-only direct access to the cap-gated worker.
    #[doc(hidden)]
    pub fn worker_for_test(&self) -> &SubAgent {
        self.inner.acceptor().worker()
    }

    /// The calls remaining on the mandate.
    pub fn remaining(&self) -> i64 {
        self.inner.remaining()
    }

    /// Admit and submit one inline tool call.
    pub fn invoke(
        &mut self,
        tool: i64,
        now: i64,
        work: Vec<Effect>,
    ) -> Result<ToolReceipt, ToolCallError> {
        self.inner.invoke(tool, now, work).map_err(map_core_error)
    }

    /// Admit and enqueue one non-blocking routed tool call.
    pub fn enqueue(
        &mut self,
        tool: i64,
        now: i64,
        work: Vec<Effect>,
    ) -> Result<RoutedHandle, ToolCallError> {
        self.inner.enqueue(tool, now, work).map_err(map_core_error)
    }

    /// Drain the routed inbox through the worker executor.
    pub fn drive_executor(&mut self, now: i64) -> Vec<[u8; 32]> {
        self.inner.drive_executor(now)
    }

    /// Poll a routed handle without consuming the result.
    pub fn status(&self, handle: &RoutedHandle) -> RoutedStatus {
        self.inner.status(handle)
    }

    /// Resolve and consume a routed result.
    pub fn resolve(&mut self, handle: &RoutedHandle) -> Result<RoutedResult, ToolCallError> {
        self.inner.resolve(handle).map_err(map_core_error)
    }

    /// The number of routed calls currently enqueued.
    pub fn inbox_depth(&self) -> usize {
        self.inner.inbox_depth()
    }

    /// Register a routed dependency in the pending registry.
    pub fn await_routed(&mut self, handle: &RoutedHandle, on: [u8; 32]) {
        self.inner.await_routed(handle, on);
    }
}
