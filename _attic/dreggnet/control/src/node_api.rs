//! `node_api` — the **GO-REAL** wire: the orchestration loop reads funded
//! execution-leases and settles metered work over a live dregg node's HTTP API,
//! as a plain network client.
//!
//! ## Why this is the clean path (no AGPL link, no manifest change)
//!
//! DreggNet **operates its own dregg node** (the recovered node on the edge,
//! `:8420`). This module talks to that node over its HTTP API the way any client
//! would: it `GET`s the public cell-read endpoints and `POST`s a settlement turn
//! to the node's submit endpoint. It links **no dregg kernel crate** — there is
//! no `dregg-verify` feature, no `the owned sandbox-dregg-bridge` dep, no arkworks /
//! `serde_with` fork, and no root `[patch]` change. DreggNet stays a clean network
//! client of a separate (AGPL) node *process*, exactly as a Postgres client is not
//! a derivative of Postgres. The verified decode and the conserving execution
//! happen **inside the node**, behind the wire.
//!
//! ## The two real seams this fills
//!
//! - [`NodeApiLeaseSource`] implements [`crate::orchestrator::LeaseSource`]: it
//!   polls `GET /api/cells` + `GET /api/cell/{id}` and decodes each funded,
//!   active execution-lease cell into an [`OrchestratedLease`]. This replaces the
//!   in-memory [`ChannelLeaseSource`](crate::orchestrator::ChannelLeaseSource).
//!   The lease-cell schema is breadstuffs' `starbridge-apps/execution-lease`:
//!   `RENT_SLOT` (4), `PERIOD_SLOT` (5), `LAPSED_SLOT` (2), `PROVIDER_SLOT` (6),
//!   the cell's `token_id` is the rent asset, and the cell's balance is the
//!   prepaid reserve (the budget). A lease cell is the rent obligor AND payer.
//! - [`NodeApiSettlement`] implements [`dreggnet_durable::Settlement`]: each
//!   metered period is settled as ONE real conserving `Effect::Transfer`
//!   (lessee cell → backend cell) submitted to `POST /api/turns/submit`. The node
//!   signs it with the operator's cipherclerk and executes it through its verified
//!   producer, so the move is conserving (per-asset Σδ = 0) and yields a real
//!   on-chain receipt. Exactly-once is enforced per `(lease, period)`: a local
//!   dedup record AND the on-chain `memo` (`dreggnet-settle:<lease>:<period>`)
//!   that makes the idempotency key auditable in the receipt log.
//!
//! ## Wire details (honest)
//!
//! Both [`LeaseSource::poll`](crate::orchestrator::LeaseSource::poll) and
//! [`Settlement::settle`](dreggnet_durable::Settlement::settle) are **synchronous**
//! seams (the in-memory twins are sync). This module therefore speaks a minimal
//! **blocking** HTTP/1.1 client over `std::net::TcpStream` with timeouts — no new
//! dependency, the same raw-wire approach [`crate::mesh`] uses for `POST /fulfill`.
//! A settlement / poll is an infrequent control-plane step, so the brief blocking
//! call is acceptable on the daemon loop.
//!
//! `https` is not spoken by the raw client: the node is reached over the private
//! mesh overlay or loopback (the edge reaches `127.0.0.1:8420`; a remote operator
//! tunnels). A `node_url` is accepted with or without an `http://` scheme and any
//! trailing path is ignored — only `host:port` is used.

use std::collections::{HashMap, HashSet};
use std::io::{Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use serde::Deserialize;

use dreggnet_bridge::{CapGrade, Lease};
use dreggnet_durable::{LeaseCharge, SettleError, SettleReceipt, Settlement};

use crate::orchestrator::{LeaseSource, OrchestratedLease};
use crate::settle_ledger::{DurableSettleLedger, Reserved};

/// The execution-lease cell heap-slot schema (breadstuffs
/// `starbridge-apps/execution-lease/src/lib.rs`). Each slot is one
/// `[FieldElement; 16]` entry; the integer-valued ones are canonical
/// little-endian `i64` in the low 8 bytes (`obligation_standing::encode_i64`).
mod slot {
    /// `lapsed` — `0` while live; nonzero once the provider has reclaimed the slot.
    pub const LAPSED: usize = 2;
    /// `rent_per_period` — the metered price of one period.
    pub const RENT: usize = 4;
    /// `period` — block length of one rent period.
    pub const PERIOD: usize = 5;
    /// `provider` — the rent beneficiary's cell id (the full 32-byte field).
    pub const PROVIDER: usize = 6;
}

/// Why a node-API call failed.
#[derive(Debug, Clone)]
pub enum NodeApiError {
    /// The `node_url` could not be resolved to a `host:port` socket address.
    BadEndpoint(String),
    /// A transport fault (connect/read/write/timeout).
    Transport(String),
    /// The node answered with a non-success HTTP status.
    Http { status: u16, body: String },
    /// The response body did not decode as the expected JSON.
    Decode(String),
}

impl std::fmt::Display for NodeApiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NodeApiError::BadEndpoint(e) => write!(f, "bad node endpoint: {e}"),
            NodeApiError::Transport(e) => write!(f, "node transport error: {e}"),
            NodeApiError::Http { status, body } => write!(f, "node HTTP {status}: {body}"),
            NodeApiError::Decode(e) => write!(f, "node response decode error: {e}"),
        }
    }
}

impl std::error::Error for NodeApiError {}

/// A minimal blocking HTTP/1.1 client for one dregg node.
///
/// Holds the resolved `host:port` (the `Host:` header value and the connect
/// target) and an optional operator bearer token for the node's protected submit
/// endpoint. Cloneable so a source and a settlement can share one endpoint.
#[derive(Debug, Clone)]
pub struct NodeApiClient {
    /// `host:port` — the connect target and `Host:` header.
    host_port: String,
    /// The operator bearer token for protected routes (e.g. `/api/turns/submit`),
    /// derived from the node's passphrase. `None` for read-only use.
    bearer: Option<String>,
    /// Per-request connect/IO timeout.
    timeout: Duration,
}

impl NodeApiClient {
    /// A client for the node at `node_url` (`host:port`, or a full
    /// `http://host:port/…` whose scheme + path are ignored).
    pub fn new(node_url: &str) -> NodeApiClient {
        NodeApiClient {
            host_port: normalize_host_port(node_url),
            bearer: None,
            timeout: Duration::from_secs(15),
        }
    }

    /// Attach the operator bearer token used for the protected submit endpoint.
    pub fn with_bearer(mut self, bearer: impl Into<String>) -> NodeApiClient {
        self.bearer = Some(bearer.into());
        self
    }

    /// Override the per-request timeout (default 15s).
    pub fn with_timeout(mut self, timeout: Duration) -> NodeApiClient {
        self.timeout = timeout;
        self
    }

    /// The `host:port` this client targets.
    pub fn endpoint(&self) -> &str {
        &self.host_port
    }

    /// `GET {path}` and decode the JSON body as `T`.
    fn get_json<T: for<'de> Deserialize<'de>>(&self, path: &str) -> Result<T, NodeApiError> {
        let (status, body) = self.request("GET", path, None)?;
        if !(200..300).contains(&status) {
            return Err(NodeApiError::Http {
                status,
                body: String::from_utf8_lossy(&body).trim().to_string(),
            });
        }
        serde_json::from_slice(&body).map_err(|e| NodeApiError::Decode(e.to_string()))
    }

    /// `POST {path}` with a JSON `body`, attaching the bearer token, and decode the
    /// JSON response as `T`. A non-2xx status surfaces as [`NodeApiError::Http`].
    fn post_json<T: for<'de> Deserialize<'de>>(
        &self,
        path: &str,
        body: &str,
    ) -> Result<T, NodeApiError> {
        let (status, resp) = self.request("POST", path, Some(body))?;
        if !(200..300).contains(&status) {
            return Err(NodeApiError::Http {
                status,
                body: String::from_utf8_lossy(&resp).trim().to_string(),
            });
        }
        serde_json::from_slice(&resp).map_err(|e| NodeApiError::Decode(e.to_string()))
    }

    /// `GET {path}` and return the raw 2xx body as a UTF-8 string.
    fn get_text(&self, path: &str) -> Result<String, NodeApiError> {
        let (status, body) = self.request("GET", path, None)?;
        if !(200..300).contains(&status) {
            return Err(NodeApiError::Http {
                status,
                body: String::from_utf8_lossy(&body).trim().to_string(),
            });
        }
        Ok(String::from_utf8_lossy(&body).to_string())
    }

    /// All cells the node holds (`GET /api/cells`).
    pub fn list_cells(&self) -> Result<Vec<CellListEntry>, NodeApiError> {
        self.get_json("/api/cells")
    }

    /// The node's committed receipt-chain MMR root + log length
    /// (`GET /api/receipts/index/root`) — the trusted root the light-client
    /// verified read checks the certified slice against.
    pub fn receipt_index_root(&self) -> Result<(String, u64), NodeApiError> {
        #[derive(Deserialize)]
        struct IndexRoot {
            root: String,
            len: u64,
        }
        let r: IndexRoot = self.get_json("/api/receipts/index/root")?;
        Ok((r.root, r.len))
    }

    /// The certified receipt slice `[lo, hi]` as raw JSON
    /// (`GET /api/receipts/index/range`) — the rows + the non-omission opening the
    /// verified read assembles into an attested slice.
    pub fn receipt_index_range_json(&self, lo: u64, hi: u64) -> Result<String, NodeApiError> {
        self.get_text(&format!("/api/receipts/index/range?lo={lo}&hi={hi}"))
    }

    /// One cell's detail, including its heap-slot `fields` (`GET /api/cell/{id}`).
    pub fn cell_detail(&self, id: &str) -> Result<CellDetail, NodeApiError> {
        self.get_json(&format!("/api/cell/{id}"))
    }

    /// The node's latest **finalized** checkpoint (`GET /checkpoint/latest`) — a
    /// federation-quorum-certified state snapshot. Used by the trusted-root
    /// hardening to confirm the node still recognizes a finalized anchor (its QC
    /// and its non-regressed height) before a verified read trusts the anchored
    /// receipt-index root. A node with no checkpoint yet yields
    /// [`NodeApiError::Http`] `404`.
    pub fn checkpoint_latest(&self) -> Result<CheckpointInfo, NodeApiError> {
        self.get_json("/checkpoint/latest")
    }

    /// Submit a conserving `Transfer` of `amount` from `from` to `to`, tagged with
    /// `memo` (`POST /api/turns/submit`). The node signs + executes it through its
    /// verified producer; the response carries the on-chain turn hash.
    pub fn submit_transfer(
        &self,
        from: &str,
        to: &str,
        amount: u64,
        memo: &str,
    ) -> Result<SubmitTurnResponse, NodeApiError> {
        let body = serde_json::json!({
            "agent": from,
            "nonce": 0,
            "fee": 0,
            "memo": memo,
            "actions": [{
                "target": from,
                "method": "submit",
                "effects": [{
                    "kind": "transfer",
                    "from": from,
                    "to": to,
                    "amount": amount,
                }],
            }],
        })
        .to_string();
        self.post_json("/api/turns/submit", &body)
    }

    /// Issue one blocking HTTP/1.1 request and read the response to EOF
    /// (`Connection: close`). Returns `(status, body_bytes)`.
    fn request(
        &self,
        method: &str,
        path: &str,
        body: Option<&str>,
    ) -> Result<(u16, Vec<u8>), NodeApiError> {
        let addr = self
            .host_port
            .to_socket_addrs()
            .map_err(|e| NodeApiError::BadEndpoint(format!("{}: {e}", self.host_port)))?
            .next()
            .ok_or_else(|| NodeApiError::BadEndpoint(format!("{}: no address", self.host_port)))?;

        let mut stream = TcpStream::connect_timeout(&addr, self.timeout)
            .map_err(|e| NodeApiError::Transport(format!("connect {addr}: {e}")))?;
        stream
            .set_read_timeout(Some(self.timeout))
            .and_then(|_| stream.set_write_timeout(Some(self.timeout)))
            .map_err(|e| NodeApiError::Transport(format!("set timeout: {e}")))?;

        let mut req = format!(
            "{method} {path} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\n",
            host = self.host_port,
        );
        if let Some(token) = &self.bearer {
            req.push_str(&format!("Authorization: Bearer {token}\r\n"));
        }
        if let Some(b) = body {
            req.push_str("Content-Type: application/json\r\n");
            req.push_str(&format!("Content-Length: {}\r\n", b.len()));
        }
        req.push_str("\r\n");
        if let Some(b) = body {
            req.push_str(b);
        }

        stream
            .write_all(req.as_bytes())
            .and_then(|_| stream.flush())
            .map_err(|e| NodeApiError::Transport(format!("write {addr}: {e}")))?;

        let mut raw = Vec::with_capacity(8 * 1024);
        stream
            .read_to_end(&mut raw)
            .map_err(|e| NodeApiError::Transport(format!("read {addr}: {e}")))?;

        split_http_response(&raw)
            .map(|(status, b)| (status, b.to_vec()))
            .ok_or_else(|| NodeApiError::Transport(format!("{addr}: malformed HTTP response")))
    }
}

/// `GET /api/cells` row — the node's cell summary (`api::CellListEntry`).
#[derive(Debug, Clone, Deserialize)]
pub struct CellListEntry {
    pub id: String,
    pub balance: i64,
    pub nonce: u64,
    #[serde(default)]
    pub has_program: bool,
}

/// `GET /api/cell/{id}` body — the node's cell detail (`api::CellDetailResponse`),
/// projected to the fields the lease decode needs.
#[derive(Debug, Clone, Deserialize)]
pub struct CellDetail {
    pub id: String,
    pub found: bool,
    pub balance: i64,
    #[serde(default)]
    pub has_program: bool,
    /// The rent asset (the lease cell's `token_id`), hex-encoded.
    #[serde(default)]
    pub token_id: String,
    /// The `[FieldElement; 16]` state slots, each 64-char hex.
    #[serde(default)]
    pub fields: Vec<String>,
}

/// `POST /api/turns/submit` body — the node's submit result (`api::SubmitTurnResponse`).
#[derive(Debug, Clone, Deserialize)]
pub struct SubmitTurnResponse {
    pub accepted: bool,
    #[serde(default)]
    pub turn_hash: Option<String>,
    #[serde(default)]
    pub error: Option<String>,
}

/// `GET /checkpoint/latest` body — the node's latest finalized checkpoint
/// (`api::CheckpointResponse`), projected to the fields the trusted-root
/// hardening needs: the finalized `height`, the federation `epoch`, and the
/// quorum-certificate vote count (`qc_votes`) that makes the checkpoint
/// *finalized* rather than merely proposed.
#[derive(Debug, Clone, Deserialize)]
pub struct CheckpointInfo {
    pub height: u64,
    #[serde(default)]
    pub epoch: u64,
    /// The number of federation quorum-certificate votes on this checkpoint. A
    /// checkpoint is *finalized* once this meets the operator's finality threshold.
    #[serde(default)]
    pub qc_votes: usize,
}

// ---------------------------------------------------------------------------
// The REAL lease source — funded execution-leases read from a live node.
// ---------------------------------------------------------------------------

/// Reads funded, active execution-lease cells from a live dregg node and yields
/// each as an [`OrchestratedLease`] — the real replacement for
/// [`ChannelLeaseSource`](crate::orchestrator::ChannelLeaseSource).
///
/// Each [`poll`](LeaseSource::poll): `GET /api/cells`, then for every cell that
/// carries a program, `GET /api/cell/{id}` and decode the execution-lease terms
/// from its heap slots. A cell is yielded only if it is a *funded, active* lease
/// (positive rent + period, not lapsed, a real provider, balance ≥ 0), and only
/// once — already-seen lease cells are skipped so a re-poll never re-dispatches.
pub struct NodeApiLeaseSource {
    client: NodeApiClient,
    /// Lease instance ids already yielded — `poll` yields each lease once.
    seen: HashSet<String>,
}

impl NodeApiLeaseSource {
    /// A lease source reading from the node at `node_url`.
    pub fn new(node_url: &str) -> NodeApiLeaseSource {
        NodeApiLeaseSource {
            client: NodeApiClient::new(node_url),
            seen: HashSet::new(),
        }
    }

    /// A lease source over an existing client (shares the endpoint with a settlement).
    pub fn with_client(client: NodeApiClient) -> NodeApiLeaseSource {
        NodeApiLeaseSource {
            client,
            seen: HashSet::new(),
        }
    }

    /// Read + decode every funded, active lease the node holds right now (ignoring
    /// already-seen ones). Surfaces the node-API error rather than swallowing it, so
    /// [`poll`](LeaseSource::poll) can log it and a caller can drive it directly.
    pub fn read_active_leases(&mut self) -> Result<Vec<OrchestratedLease>, NodeApiError> {
        let cells = self.client.list_cells()?;
        let mut out = Vec::new();
        for cell in cells {
            if !cell.has_program {
                continue;
            }
            let instance = lease_instance(&cell.id);
            if self.seen.contains(&instance) {
                continue;
            }
            let detail = match self.client.cell_detail(&cell.id) {
                Ok(d) => d,
                Err(_) => continue, // a single unreadable cell does not fail the poll
            };
            if let Some(lease) = lease_from_cell(&detail) {
                self.seen.insert(instance.clone());
                out.push(OrchestratedLease::new(instance, lease));
            }
        }
        Ok(out)
    }
}

impl LeaseSource for NodeApiLeaseSource {
    fn poll(&mut self) -> Vec<OrchestratedLease> {
        match self.read_active_leases() {
            Ok(leases) => leases,
            Err(e) => {
                eprintln!("dreggnet: node-API lease poll failed: {e}");
                Vec::new()
            }
        }
    }
}

/// Decode a node cell-detail into a funded, active [`Lease`], or `None` if it is
/// not an active execution-lease cell.
///
/// The lease cell is the rent obligor AND payer (breadstuffs' execution-lease
/// model), so the cell id is the lessee, its `token_id` the asset, its balance the
/// prepaid reserve (budget), and `RENT_SLOT` the per-period cost. The cap-grade is
/// not a heap slot (it lives in the factory's allowed cap-templates); the only
/// tier wired into `dreggnet-exec` is the wasmi sandbox, so the decoded lease runs
/// at [`CapGrade::Sandboxed`] (a stronger grade would only relax the floor).
fn lease_from_cell(cell: &CellDetail) -> Option<Lease> {
    if !cell.found || !cell.has_program {
        return None;
    }
    let rent = decode_i64_slot(&cell.fields, slot::RENT);
    let period = decode_i64_slot(&cell.fields, slot::PERIOD);
    let lapsed = decode_i64_slot(&cell.fields, slot::LAPSED);
    let has_provider = cell
        .fields
        .get(slot::PROVIDER)
        .is_some_and(|f| !is_zero_field(f));

    // Funded + ACTIVE: positive rent + period, a real provider, not lapsed, and a
    // non-negative prepaid reserve. Anything else is not a billable lease.
    if rent <= 0 || period <= 0 || lapsed != 0 || !has_provider || cell.balance < 0 {
        return None;
    }

    let asset = if cell.token_id.is_empty() {
        "computrons".to_string()
    } else {
        cell.token_id.clone()
    };
    Some(Lease::funded(
        cell.id.clone(),
        CapGrade::Sandboxed,
        asset,
        cell.balance,
        rent,
    ))
}

/// The durable instance id a lease cell is orchestrated under (stable per cell).
fn lease_instance(cell_id: &str) -> String {
    format!("lease-{cell_id}")
}

// ---------------------------------------------------------------------------
// The trusted-root anchor — CommitBindsMMR, DreggNet-side.
// ---------------------------------------------------------------------------

/// The node's single-range span cap: `GET /api/receipts/index/range` rejects a
/// span of `>= 1024` rows (`node/src/api.rs::get_receipt_index_range`, `MAX_SPAN`).
/// A whole-log verified read over a longer log is paginated into windows of this
/// many rows each ([`fetch_index_windows`]).
#[cfg(feature = "dregg-verify")]
const RANGE_WINDOW: u64 = 1024;

/// A finalized-checkpoint anchor for the receipt-index MMR root — the DreggNet-side
/// instantiation of the **`CommitBindsMMR`** trust anchor
/// (`metatheory/Dregg2/Lightclient/MMR.lean` §6; `docs/deos/COMMIT-BINDS-MMR.md`).
///
/// The light-client verified read in [`dreggnet_bridge::dregg_verify`] checks the
/// certified slice's non-omission against a *trusted root* it takes as a parameter.
/// On its own, that root is whatever the node serves at `/api/receipts/index/root`
/// — a compromised / forking node can serve a self-consistent forged root. This
/// anchor closes that seam: it pins a receipt-index root to a **finalized
/// checkpoint** (a federation-quorum-certified state), so the verified read trusts
/// the anchored root rather than the node's bare say-so.
///
/// The anchored prefix `[0, len-1]` is read against `mmr_root`; the read also
/// confirms (via `/checkpoint/latest`) that the node still recognizes a finalized
/// checkpoint at `height` or beyond (a fork that rolls back below the finalized
/// point is rejected). The binding the read enforces is exactly
/// **`commit_pins_mmr`**: the verified read's root MUST equal the
/// finalized-checkpoint's committed MMR root.
///
/// ## Provenance of `mmr_root` (honest)
///
/// `CommitBindsMMR` Gap B — welding `mroot` into the EPOCH commitment so the
/// checkpoint *carries* the receipt-index root — is VK-affecting and gated to the
/// rotation epoch (`COMMIT-BINDS-MMR.md` §2/§5), so today's `/checkpoint/latest`
/// does not yet expose the MMR root field. Until it does, the anchor's
/// `(height, len, mmr_root)` is established out-of-band from a finalized checkpoint
/// (the operator channel / TOFU the doc names), and this code enforces the binding
/// equality + the finality + the no-rollback checks against it. When Gap B lands,
/// the only change is the *provenance* of `mmr_root` — read it from the verified
/// checkpoint instead of the operator — a caller-side change in
/// [`VerifiedNodeLeaseSource::read_verified_leases`], exactly as the crate's
/// verifier (`dregg-query`, the trust-anchor note) is written to allow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckpointAnchor {
    /// The finalized checkpoint height this anchor pins. The node's latest
    /// checkpoint must be at this height or beyond (no rollback below finality).
    pub height: u64,
    /// The root-pinned length of the receipt log at the anchored checkpoint — the
    /// finalized prefix `[0, len-1]` the verified read covers.
    pub len: u64,
    /// The receipt-index MMR root committed by that finalized checkpoint, hex. The
    /// verified read trusts THIS, not the node's `/api/receipts/index/root`.
    pub mmr_root: String,
    /// The minimum quorum-certificate vote count for a checkpoint to count as
    /// finalized (`0` accepts any served checkpoint — use the federation's QC size).
    pub min_qc_votes: usize,
}

/// Where the verified read's trusted receipt-index root comes from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustedRoot {
    /// **Interim (TOFU):** trust the node's own `/api/receipts/index/root`. The
    /// non-omission machinery is still genuine, but the *root* is the node's
    /// say-so — a compromised node can serve a self-consistent forged root.
    NodeServed,
    /// **Hardened (`CommitBindsMMR`):** the root is pinned to a finalized
    /// checkpoint; a forking / compromised node cannot feed a fake root.
    CheckpointBound(CheckpointAnchor),
}

impl Default for TrustedRoot {
    fn default() -> Self {
        TrustedRoot::NodeServed
    }
}

/// Fetch the certified receipt-index windows tiling `[0, len-1]`, each at most
/// [`RANGE_WINDOW`] rows, so a log longer than the node's single-range span cap is
/// read whole. The windows are contiguous and gap-free by construction; the
/// verifier ([`dreggnet_bridge::dregg_verify::verified_leases_windowed`]) re-checks
/// the tiling against the certificates (it trusts this assembly for nothing).
#[cfg(feature = "dregg-verify")]
fn fetch_index_windows(client: &NodeApiClient, len: u64) -> Result<Vec<String>, NodeApiError> {
    let mut windows = Vec::new();
    let mut lo = 0u64;
    while lo < len {
        let hi = (lo + RANGE_WINDOW - 1).min(len - 1);
        windows.push(client.receipt_index_range_json(lo, hi)?);
        lo = hi + 1;
    }
    Ok(windows)
}

// ---------------------------------------------------------------------------
// The VERIFIED lease source — a light-client-verified on-chain read.
// ---------------------------------------------------------------------------

/// Reads funded execution-leases from a live dregg node with a full **light-client
/// verification** of the on-chain receipt log — the verified counterpart to
/// [`NodeApiLeaseSource`] (which trusts the node's cell-read API).
///
/// Each [`poll`](LeaseSource::poll) verifies the on-chain receipt log against a
/// trusted root and decodes every funded execution-lease grant it attests. The
/// verification is fail-closed: a forged / truncated / root-mismatched log yields
/// no leases. Each verified lease is yielded once (dedup by instance).
///
/// ## Trusted root
///
/// - [`TrustedRoot::NodeServed`] (default) — the trusted root is the node's
///   `/api/receipts/index/root`. The non-omission certificate is genuine, but the
///   root is the node's own say-so (TOFU).
/// - [`TrustedRoot::CheckpointBound`] — the trusted root is pinned to a finalized
///   checkpoint ([`CheckpointAnchor`], `CommitBindsMMR`): the read confirms the
///   node still recognizes a finalized checkpoint (its QC + non-regressed height)
///   and verifies the anchored prefix against the anchor's root, NOT the node's.
///
/// ## Long logs
///
/// The whole-log read is **windowed** ([`fetch_index_windows`] →
/// [`dreggnet_bridge::dregg_verify::verified_leases_windowed`]): a log longer than
/// the node's single-range span cap (1024 rows) is read as contiguous windows that
/// tile `[0, len-1]`, each verified against the same trusted root.
///
/// Available only under the `dregg-verify` feature (which links the dregg verified
/// core); on the default build use [`NodeApiLeaseSource`].
#[cfg(feature = "dregg-verify")]
pub struct VerifiedNodeLeaseSource {
    client: NodeApiClient,
    trusted_root: TrustedRoot,
    seen: HashSet<String>,
}

#[cfg(feature = "dregg-verify")]
impl VerifiedNodeLeaseSource {
    /// A verified lease source reading from the node at `node_url`, trusting the
    /// node's served receipt-index root (TOFU). Harden it with
    /// [`with_checkpoint_anchor`](Self::with_checkpoint_anchor).
    pub fn new(node_url: &str) -> VerifiedNodeLeaseSource {
        VerifiedNodeLeaseSource {
            client: NodeApiClient::new(node_url),
            trusted_root: TrustedRoot::NodeServed,
            seen: HashSet::new(),
        }
    }

    /// A verified source over an existing client (TOFU trusted root).
    pub fn with_client(client: NodeApiClient) -> VerifiedNodeLeaseSource {
        VerifiedNodeLeaseSource {
            client,
            trusted_root: TrustedRoot::NodeServed,
            seen: HashSet::new(),
        }
    }

    /// Pin the trusted receipt-index root to a finalized checkpoint
    /// (`CommitBindsMMR`) — the trusted-root hardening. After this the verified
    /// read trusts the anchor's root, not the node's `/api/receipts/index/root`.
    pub fn with_checkpoint_anchor(mut self, anchor: CheckpointAnchor) -> VerifiedNodeLeaseSource {
        self.trusted_root = TrustedRoot::CheckpointBound(anchor);
        self
    }

    /// The trusted-root provenance this source verifies against.
    pub fn trusted_root(&self) -> &TrustedRoot {
        &self.trusted_root
    }

    /// Light-client-verify the on-chain log and decode every funded execution-lease
    /// it attests (ignoring already-seen ones). Surfaces the error so
    /// [`poll`](LeaseSource::poll) can log it.
    pub fn read_verified_leases(&mut self) -> Result<Vec<OrchestratedLease>, NodeApiError> {
        // Resolve the trusted (root, len) to verify against.
        let (root, len) = match &self.trusted_root {
            TrustedRoot::NodeServed => self.client.receipt_index_root()?,
            TrustedRoot::CheckpointBound(anchor) => self.verify_anchor(anchor)?,
        };
        if len == 0 {
            return Ok(Vec::new());
        }
        // Read the whole anchored prefix [0, len-1], windowed past the node's
        // single-range span cap, and verify every window against the trusted root.
        let windows = fetch_index_windows(&self.client, len)?;
        let items = dreggnet_bridge::dregg_verify::verified_leases_windowed(&windows, &root)
            .map_err(NodeApiError::Decode)?;
        let mut out = Vec::new();
        for item in items {
            if self.seen.insert(item.instance.clone()) {
                out.push(OrchestratedLease::new(item.instance, item.lease));
            }
        }
        Ok(out)
    }

    /// Confirm the node still recognizes the finalized anchor, and return the
    /// anchored `(mmr_root, len)` to verify against — the `CommitBindsMMR` binding.
    ///
    /// Fail-closed checks (any failure aborts the read, yielding no leases):
    /// 1. the node's latest checkpoint is **finalized** — its QC vote count meets
    ///    the anchor's `min_qc_votes` threshold;
    /// 2. the node has **not rolled back** below the finalized anchor — its latest
    ///    checkpoint height is `>= anchor.height` (a fork that rewinds finalized
    ///    history is rejected).
    ///
    /// On success the verified read uses the anchor's `mmr_root` as the trusted
    /// root: the verified read's root therefore *equals the finalized-checkpoint's
    /// committed MMR root* by construction (`commit_pins_mmr`).
    fn verify_anchor(&self, anchor: &CheckpointAnchor) -> Result<(String, u64), NodeApiError> {
        let cp = self.client.checkpoint_latest()?;
        if cp.qc_votes < anchor.min_qc_votes {
            return Err(NodeApiError::Decode(format!(
                "latest checkpoint is not finalized: {} QC vote(s) < required {} (refusing to trust an unfinalized root)",
                cp.qc_votes, anchor.min_qc_votes
            )));
        }
        if cp.height < anchor.height {
            return Err(NodeApiError::Decode(format!(
                "node rolled back below the finalized anchor: latest checkpoint height {} < anchored {} (fork rejected)",
                cp.height, anchor.height
            )));
        }
        Ok((anchor.mmr_root.clone(), anchor.len))
    }
}

#[cfg(feature = "dregg-verify")]
impl LeaseSource for VerifiedNodeLeaseSource {
    fn poll(&mut self) -> Vec<OrchestratedLease> {
        match self.read_verified_leases() {
            Ok(leases) => leases,
            Err(e) => {
                eprintln!("dreggnet: verified node-API lease poll failed: {e}");
                Vec::new()
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The REAL settlement — a conserving Transfer turn per metered period.
// ---------------------------------------------------------------------------

/// Settles each metered period as ONE real conserving `Effect::Transfer`
/// (lessee → backend) on a live dregg node — the real replacement for
/// [`ConservingLedger`](dreggnet_durable::ConservingLedger).
///
/// [`settle`](Settlement::settle) submits the transfer to `POST /api/turns/submit`
/// (the node signs + executes it through its verified producer). It is **conserving**
/// because the node's executor enforces per-asset Σδ = 0 on every `Transfer`, and
/// **exactly-once** because each `(lease, period)` is settled at most once.
///
/// ## Exactly-once across a restart (red-team LEASE-3)
///
/// With a [`DurableSettleLedger`] attached
/// ([`with_durable_ledger`](Self::with_durable_ledger)), the dedup is **durable**:
/// each `(lease, period)` is reserved (persisted, fsync'd) **before** the on-chain
/// `Transfer` is submitted, and a key already settled — in this process OR in a
/// prior process's persisted ledger — is replayed without submitting a second
/// transfer. So a settler **restart** (or a second instance sharing the ledger
/// path) cannot double-charge the lessee: the on-chain submission is at-most-once
/// per key across restarts. Without a ledger the dedup is in-memory only (the dev /
/// single-tick path), which a restart would forget. The on-chain `memo`
/// (`dreggnet-settle:<lease>:<period>`) records the key in the receipt log for
/// audit and ties the durable record to the on-chain settlement.
///
/// `backend_cells` maps a fleet backend's name (the [`LeaseCharge::beneficiary`]
/// the orchestrator passes) to its **payable cell id**. A beneficiary that is
/// already a 64-char hex cell id is used verbatim, so a deployment can also name
/// backends by their cell id directly.
pub struct NodeApiSettlement {
    client: NodeApiClient,
    /// Backend name → payable cell id (hex). Empty if backends are named by cell id.
    backend_cells: HashMap<String, String>,
    /// `(lease_id, period)` → the receipt settled for it (the in-memory exactly-once
    /// record; used only when no durable ledger is attached).
    settled: Mutex<HashMap<(String, i64), SettleReceipt>>,
    /// The durable, restart-surviving `(lease, period)` ledger. When present it is
    /// the authoritative dedup: a restart loads it and refuses to re-submit an
    /// already-settled period (LEASE-3). When `None`, dedup is in-memory only.
    ledger: Option<Arc<DurableSettleLedger>>,
}

impl NodeApiSettlement {
    /// A settlement against the node at `node_url` using the operator `bearer`
    /// token (the protected submit endpoint requires it).
    pub fn new(node_url: &str, bearer: impl Into<String>) -> NodeApiSettlement {
        NodeApiSettlement {
            client: NodeApiClient::new(node_url).with_bearer(bearer),
            backend_cells: HashMap::new(),
            settled: Mutex::new(HashMap::new()),
            ledger: None,
        }
    }

    /// A settlement over an existing (bearer-bearing) client.
    pub fn with_client(client: NodeApiClient) -> NodeApiSettlement {
        NodeApiSettlement {
            client,
            backend_cells: HashMap::new(),
            settled: Mutex::new(HashMap::new()),
            ledger: None,
        }
    }

    /// Attach a [`DurableSettleLedger`] so the exactly-once dedup survives a restart
    /// — the LEASE-3 fix. Settlement then reserves each `(lease, period)` durably
    /// before submitting the on-chain `Transfer`, so a restart cannot double-charge.
    pub fn with_durable_ledger(mut self, ledger: Arc<DurableSettleLedger>) -> Self {
        self.ledger = Some(ledger);
        self
    }

    /// Open (or create) a [`DurableSettleLedger`] at `path` and attach it — the
    /// convenience form of [`with_durable_ledger`](Self::with_durable_ledger).
    pub fn with_ledger_path(self, path: impl AsRef<std::path::Path>) -> std::io::Result<Self> {
        let ledger = Arc::new(DurableSettleLedger::open(path)?);
        Ok(self.with_durable_ledger(ledger))
    }

    /// Register a backend's payable cell id (the beneficiary a `Transfer` pays).
    pub fn map_backend(mut self, name: impl Into<String>, cell_id: impl Into<String>) -> Self {
        self.backend_cells.insert(name.into(), cell_id.into());
        self
    }

    /// Resolve a beneficiary name to a hex cell id: a registered backend, or a name
    /// that is itself already a 64-char hex cell id.
    fn resolve_beneficiary(&self, beneficiary: &str) -> Result<String, SettleError> {
        if let Some(cell) = self.backend_cells.get(beneficiary) {
            return Ok(cell.clone());
        }
        if is_hex_cell_id(beneficiary) {
            return Ok(beneficiary.to_string());
        }
        Err(SettleError::Backend(format!(
            "no payable cell id for backend `{beneficiary}` (register it or name it by cell id)"
        )))
    }
}

impl Settlement for NodeApiSettlement {
    fn settle(&self, charge: &LeaseCharge) -> Result<SettleReceipt, SettleError> {
        if charge.amount <= 0 {
            return Err(SettleError::NonPositiveAmount(charge.amount));
        }

        // Exactly-once dedup. With a durable ledger the reservation is persisted
        // (write-ahead, fsync'd) BEFORE the on-chain submit, so a restart cannot
        // re-submit an already-settled period (LEASE-3). Without one, the dedup is
        // in-memory only (a restart would forget it — the dev / single-tick path).
        let key = (charge.lease_id.clone(), charge.period);
        if let Some(ledger) = &self.ledger {
            match ledger.reserve_or_replay(charge)? {
                Reserved::Replay(receipt) => return Ok(receipt),
                Reserved::Fresh => {}
            }
        } else {
            let settled = self.settled.lock().expect("settlement record poisoned");
            if let Some(prior) = settled.get(&key) {
                if prior.amount != charge.amount || prior.asset != charge.asset {
                    return Err(SettleError::Conflict {
                        lease_id: charge.lease_id.clone(),
                        period: charge.period,
                    });
                }
                let mut replay = prior.clone();
                replay.replayed = true;
                return Ok(replay);
            }
        }

        let from = &charge.payer;
        if !is_hex_cell_id(from) {
            return Err(SettleError::Backend(format!(
                "payer `{from}` is not a hex cell id (a real lease's lessee is its cell id)"
            )));
        }
        let to = self.resolve_beneficiary(&charge.beneficiary)?;
        let memo = format!("dreggnet-settle:{}:{}", charge.lease_id, charge.period);

        // The real conserving move: ONE Effect::Transfer the node signs + executes.
        // The period is already reserved durably (when a ledger is attached), so an
        // at-most-once submission holds even across a crash here.
        let resp = self
            .client
            .submit_transfer(from, &to, charge.amount as u64, &memo)
            .map_err(|e| SettleError::Backend(e.to_string()))?;
        if !resp.accepted {
            return Err(SettleError::Backend(
                resp.error
                    .unwrap_or_else(|| "turn not accepted".to_string()),
            ));
        }

        // Read the post-transfer balances back so the receipt carries the real
        // conservation witness (best-effort: a read fault leaves them at 0 but the
        // transfer already committed on-chain).
        let payer_balance = self
            .client
            .cell_detail(from)
            .map(|c| c.balance)
            .unwrap_or(0);
        let beneficiary_balance = self.client.cell_detail(&to).map(|c| c.balance).unwrap_or(0);

        // Confirm the settlement durably (ties the persisted record to the on-chain
        // turn hash), or record it in-memory when no ledger is attached.
        if let Some(ledger) = &self.ledger {
            return ledger.confirm(charge, payer_balance, beneficiary_balance, resp.turn_hash);
        }
        let receipt = SettleReceipt {
            lease_id: charge.lease_id.clone(),
            period: charge.period,
            asset: charge.asset.clone(),
            amount: charge.amount,
            payer_balance,
            beneficiary_balance,
            replayed: false,
        };
        self.settled
            .lock()
            .expect("settlement record poisoned")
            .insert(key, receipt.clone());
        Ok(receipt)
    }

    fn settled_total(&self, lease_id: &str) -> i64 {
        if let Some(ledger) = &self.ledger {
            return ledger.settled_total(lease_id);
        }
        self.settled
            .lock()
            .expect("settlement record poisoned")
            .iter()
            .filter(|((l, _), _)| l == lease_id)
            .map(|(_, r)| r.amount)
            .sum()
    }

    /// The real on-chain reserve `holder` (a cell id) holds — read from the live node.
    /// A read fault is fail-closed (`0` ⇒ refuse admission): no provisioning real
    /// machines for a lessee whose funded balance the node cannot confirm.
    fn funded_balance(&self, _asset: &str, holder: &str) -> i64 {
        if !is_hex_cell_id(holder) {
            return 0;
        }
        self.client
            .cell_detail(holder)
            .map(|c| c.balance)
            .unwrap_or(0)
    }
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

/// Strip an optional `http://` / `https://` scheme and any trailing path from a
/// `node_url`, leaving `host:port`. A bare `host:port` passes through unchanged.
fn normalize_host_port(node_url: &str) -> String {
    let s = node_url
        .strip_prefix("http://")
        .or_else(|| node_url.strip_prefix("https://"))
        .unwrap_or(node_url);
    s.split('/').next().unwrap_or(s).trim().to_string()
}

/// Whether `s` is a 64-char hex string (a dregg cell id).
fn is_hex_cell_id(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

/// Whether a 64-char hex field element is all zero.
fn is_zero_field(hex: &str) -> bool {
    hex.bytes().all(|b| b == b'0')
}

/// Decode a heap slot as a canonical little-endian `i64` (low 8 bytes), matching
/// `obligation_standing::encode_i64`. Returns `0` for a missing / malformed slot.
fn decode_i64_slot(fields: &[String], idx: usize) -> i64 {
    let Some(hex) = fields.get(idx) else {
        return 0;
    };
    if hex.len() < 16 {
        return 0;
    }
    let mut bytes = [0u8; 8];
    for (i, byte) in bytes.iter_mut().enumerate() {
        let Ok(b) = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16) else {
            return 0;
        };
        *byte = b;
    }
    i64::from_le_bytes(bytes)
}

/// Split a raw HTTP/1.1 response into `(status_code, body_bytes)`. Returns `None`
/// if the status line or the header/body separator is missing.
fn split_http_response(raw: &[u8]) -> Option<(u16, &[u8])> {
    let sep = raw.windows(4).position(|w| w == b"\r\n\r\n")?;
    let head = &raw[..sep];
    let body = &raw[sep + 4..];
    let line_end = head
        .windows(2)
        .position(|w| w == b"\r\n")
        .unwrap_or(head.len());
    let status_line = std::str::from_utf8(&head[..line_end]).ok()?;
    let code = status_line.split_whitespace().nth(1)?.parse::<u16>().ok()?;
    Some((code, body))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::TcpListener;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    /// A field-element hex (64 chars) holding `v` as a little-endian i64.
    fn i64_field(v: i64) -> String {
        let mut bytes = [0u8; 32];
        bytes[..8].copy_from_slice(&v.to_le_bytes());
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    fn zero_field() -> String {
        "0".repeat(64)
    }

    /// A 64-char hex cell id with every byte = `b`.
    fn cell_id(b: u8) -> String {
        std::iter::repeat_n(format!("{b:02x}"), 32).collect()
    }

    /// Build the 16-slot `fields` of an execution-lease cell.
    fn lease_fields(rent: i64, period: i64, lapsed: i64, provider: &str) -> Vec<String> {
        let mut f = vec![zero_field(); 16];
        f[slot::RENT] = i64_field(rent);
        f[slot::PERIOD] = i64_field(period);
        f[slot::LAPSED] = i64_field(lapsed);
        f[slot::PROVIDER] = provider.to_string();
        f
    }

    #[test]
    fn normalizes_host_port_from_a_url() {
        assert_eq!(normalize_host_port("http://1.2.3.4:8420/x"), "1.2.3.4:8420");
        assert_eq!(normalize_host_port("https://node:9090"), "node:9090");
        assert_eq!(normalize_host_port("127.0.0.1:8420"), "127.0.0.1:8420");
    }

    #[test]
    fn decodes_i64_slot_little_endian() {
        assert_eq!(decode_i64_slot(&[i64_field(100)], 0), 100);
        assert_eq!(decode_i64_slot(&[i64_field(0)], 0), 0);
        assert_eq!(decode_i64_slot(&[], 0), 0);
    }

    #[test]
    fn decodes_an_active_lease_cell() {
        let detail = CellDetail {
            id: cell_id(0xab),
            found: true,
            has_program: true,
            token_id: cell_id(0x01),
            balance: 5_000,
            fields: lease_fields(100, 50, 0, &cell_id(0x07)),
        };
        let lease = lease_from_cell(&detail).expect("an active lease");
        assert_eq!(lease.lessee, cell_id(0xab));
        assert_eq!(lease.asset, cell_id(0x01));
        assert_eq!(lease.budget_units, 5_000);
        assert_eq!(lease.per_period_units, 100);
        assert_eq!(lease.cap_grade, CapGrade::Sandboxed);
        assert!(lease.is_active());
    }

    #[test]
    fn skips_non_lease_and_inactive_cells() {
        // No program → not a lease.
        let mut no_prog = CellDetail {
            id: cell_id(1),
            found: true,
            has_program: false,
            token_id: cell_id(1),
            balance: 100,
            fields: lease_fields(100, 50, 0, &cell_id(7)),
        };
        assert!(lease_from_cell(&no_prog).is_none());
        no_prog.has_program = true;
        assert!(lease_from_cell(&no_prog).is_some());

        // Lapsed → not active.
        let lapsed = CellDetail {
            id: cell_id(2),
            found: true,
            has_program: true,
            token_id: cell_id(1),
            balance: 100,
            fields: lease_fields(100, 50, 1, &cell_id(7)),
        };
        assert!(lease_from_cell(&lapsed).is_none());

        // Zero rent → not billable.
        let no_rent = CellDetail {
            id: cell_id(3),
            found: true,
            has_program: true,
            token_id: cell_id(1),
            balance: 100,
            fields: lease_fields(0, 50, 0, &cell_id(7)),
        };
        assert!(lease_from_cell(&no_rent).is_none());

        // No provider → not a lease.
        let no_provider = CellDetail {
            id: cell_id(4),
            found: true,
            has_program: true,
            token_id: cell_id(1),
            balance: 100,
            fields: lease_fields(100, 50, 0, &zero_field()),
        };
        assert!(lease_from_cell(&no_provider).is_none());
    }

    /// A blocking stub node on its own OS thread: serves a canned response for the
    /// first matching path. Returns `host:port` and a shared capture of the last
    /// request. `submit_balance` lets a /api/cell/{id} read after a transfer return
    /// a chosen balance.
    fn spawn_stub_node(
        cells_json: String,
        detail_json: String,
        submit_json: String,
        captured: Arc<Mutex<Vec<String>>>,
        submit_count: Arc<AtomicUsize>,
    ) -> String {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap();
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(mut stream) = stream else { return };
                let mut buf = [0u8; 8192];
                let n = stream.read(&mut buf).unwrap_or(0);
                let req = String::from_utf8_lossy(&buf[..n]).to_string();
                let first_line = req.lines().next().unwrap_or("").to_string();
                captured.lock().unwrap().push(req.clone());
                let body = if first_line.starts_with("GET /api/cells") {
                    cells_json.clone()
                } else if first_line.starts_with("POST /api/turns/submit") {
                    submit_count.fetch_add(1, Ordering::SeqCst);
                    submit_json.clone()
                } else if first_line.starts_with("GET /api/cell/") {
                    detail_json.clone()
                } else {
                    "{}".to_string()
                };
                let resp = format!(
                    "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\
                     Content-Length: {}\r\nConnection: close\r\n\r\n{body}",
                    body.len()
                );
                let _ = stream.write_all(resp.as_bytes());
                let _ = stream.flush();
            }
        });
        format!("127.0.0.1:{}", addr.port())
    }

    #[test]
    fn lease_source_reads_a_lease_over_the_wire() {
        let lessee = cell_id(0xab);
        let provider = cell_id(0x07);
        let cells = serde_json::json!([
            { "id": lessee, "balance": 5000, "nonce": 0, "has_program": true },
            { "id": cell_id(0x99), "balance": 10, "nonce": 0, "has_program": false },
        ])
        .to_string();
        let detail = serde_json::json!({
            "id": lessee, "found": true, "has_program": true,
            "balance": 5000, "token_id": cell_id(0x01),
            "fields": lease_fields(100, 50, 0, &provider),
        })
        .to_string();

        let captured = Arc::new(Mutex::new(Vec::new()));
        let host_port = spawn_stub_node(
            cells,
            detail,
            "{}".to_string(),
            captured,
            Arc::new(AtomicUsize::new(0)),
        );

        let mut source = NodeApiLeaseSource::new(&host_port);
        let leases = source.poll();
        assert_eq!(
            leases.len(),
            1,
            "only the program-bearing lease cell decodes"
        );
        assert_eq!(leases[0].instance, lease_instance(&lessee));
        assert_eq!(leases[0].lease.lessee, lessee);
        assert_eq!(leases[0].lease.budget_units, 5000);
        assert_eq!(leases[0].lease.per_period_units, 100);

        // A re-poll yields nothing (the lease was already seen).
        assert!(source.poll().is_empty());
    }

    #[test]
    fn settlement_submits_a_real_transfer_and_is_exactly_once() {
        let lessee = cell_id(0xab);
        let backend = cell_id(0x07);
        let detail = serde_json::json!({
            "id": lessee, "found": true, "has_program": false,
            "balance": 4900, "token_id": cell_id(0x01), "fields": [],
        })
        .to_string();
        let submit = serde_json::json!({
            "accepted": true, "turn_hash": "deadbeef", "error": null,
        })
        .to_string();

        let captured = Arc::new(Mutex::new(Vec::new()));
        let submit_count = Arc::new(AtomicUsize::new(0));
        let host_port = spawn_stub_node(
            "[]".to_string(),
            detail,
            submit,
            captured.clone(),
            submit_count.clone(),
        );

        let settlement = NodeApiSettlement::new(&host_port, "test-bearer");
        let charge = LeaseCharge::new(&lessee, &backend, cell_id(0x01), "lease-x", 1, 100);

        let receipt = settlement.settle(&charge).expect("a real settlement");
        assert!(!receipt.replayed);
        assert_eq!(receipt.amount, 100);
        assert_eq!(submit_count.load(Ordering::SeqCst), 1);

        // The POST carried a conserving Transfer lessee → backend with the
        // exactly-once memo.
        let posts: Vec<String> = captured
            .lock()
            .unwrap()
            .iter()
            .filter(|r| r.starts_with("POST /api/turns/submit"))
            .cloned()
            .collect();
        assert_eq!(posts.len(), 1);
        let post = &posts[0];
        assert!(post.contains("Authorization: Bearer test-bearer"));
        assert!(post.contains("\"kind\":\"transfer\""));
        assert!(post.contains(&format!("\"from\":\"{lessee}\"")));
        assert!(post.contains(&format!("\"to\":\"{backend}\"")));
        assert!(post.contains("dreggnet-settle:lease-x:1"));

        // Re-settling the SAME (lease, period) submits NO second turn (exactly-once).
        let again = settlement.settle(&charge).expect("replay");
        assert!(again.replayed);
        assert_eq!(submit_count.load(Ordering::SeqCst), 1, "no second submit");
        assert_eq!(settlement.settled_total("lease-x"), 100);
    }

    #[test]
    fn settlement_maps_a_named_backend_and_reports_node_refusal() {
        let lessee = cell_id(0xab);
        let refusal = serde_json::json!({
            "accepted": false, "turn_hash": null, "error": "insufficient balance",
        })
        .to_string();
        let host_port = spawn_stub_node(
            "[]".to_string(),
            "{}".to_string(),
            refusal,
            Arc::new(Mutex::new(Vec::new())),
            Arc::new(AtomicUsize::new(0)),
        );

        let settlement =
            NodeApiSettlement::new(&host_port, "b").map_backend("persvati", cell_id(0x07));
        // A named backend resolves to its payable cell id.
        let charge = LeaseCharge::new(&lessee, "persvati", cell_id(1), "lease-y", 1, 50);
        match settlement.settle(&charge) {
            Err(SettleError::Backend(why)) => assert!(why.contains("insufficient balance")),
            other => panic!("expected a backend refusal, got {other:?}"),
        }

        // An unknown, non-hex beneficiary is refused before any wire call.
        let bad = LeaseCharge::new(&lessee, "not-a-cell", cell_id(1), "lease-z", 1, 50);
        assert!(matches!(
            settlement.settle(&bad),
            Err(SettleError::Backend(_))
        ));
    }
}
