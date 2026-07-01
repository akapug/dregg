//! The inner host-API spine — a workload as a **transacting agent** (§3).
//!
//! Fly Machines and Cloudflare Workers can sandbox your code; what they
//! structurally cannot give you is a guest that — *from inside the sandbox,
//! mid-execution* — calls a verified service, reads and writes its own
//! committed state, and leaves a receipt for each move. That inner affordance
//! is what this module wires.
//!
//! polyana already gives every native tier a duplex newline-JSON wire and a
//! generic [`HostBroker`](polyana_core::provider::HostBroker) hook on the
//! python / node providers (the `with_host_broker` builder). This module is
//! DreggNet's concrete broker over that hook: [`ExecHostBroker`] services each
//! guest-emitted host call —
//!
//! - **`invoke(service, args)`** — call a real **gateway-registered** dregg
//!   service through the ToolGateway rail (the agent-economy cap-gated
//!   service-call rail: *may A call this? cap ✓ · budget ✓ · charge Σδ=0 ·
//!   else 402*). The call is admitted IFF the lease grants the cap AND the
//!   consumer is in budget; the service's per-call PRICE moves value
//!   consumer → provider as a CONSERVING (`Σδ=0`) charge riding the same call,
//!   and an over-budget / insolvent call is refused `402` *before* it runs.
//! - **`cell_read(path)` / `cell_write(path, val)`** — read / write the
//!   workload's own committed cell (its umem state), so a workload is *stateful*
//!   across calls.
//!
//! Each call is:
//!
//! - **cap-gated** — the requested effect's *class* is run through
//!   [`gate_effect_set`](polyana_dregg_bridge::gate_effect_set) (dregg's proven
//!   monotone attenuation law) against the lease's [`CapBundle`]: `invoke` →
//!   `tool-call`, `cell_read` → `filesystem:read`, `cell_write` →
//!   `filesystem:write` (the bridge's interned effect vocabulary). A lease that
//!   doesn't grant the class is refused `not-an-attenuation` by the proven gate
//!   (e.g. a lease without `filesystem:write` genuinely cannot `cell_write`).
//!   A finer per-service allow-set (the lease's authorized `invoke` targets)
//!   then scopes `invoke` below the coarse class — both checked before any
//!   effect commits, fail-closed;
//! - **metered** — charged against the lease budget *before* the commit; an
//!   over-budget call is refused `over-budget` (the spend is refused before the
//!   commit, never after);
//! - **paid** — a priced `invoke` additionally moves the service's per-call
//!   `price` from the consumer (the workload's spend account) to the provider
//!   (the gateway-registered service owner) as a CONSERVING value move
//!   (`Σδ=0` — the payer is debited exactly what the provider is credited), the
//!   in-process twin of the dregg `Payable` `Effect::Transfer` the breadstuffs
//!   `ToolGateway` charges over. An insolvent or over-(value-)budget call is
//!   refused `402` before the call runs, so no value moves and no service runs;
//! - **receipted** — a committed call emits a
//!   [`TurnShadowReceipt`](polyana_dregg_bridge::TurnShadowReceipt) chained into
//!   the workload's receipt chain (`previous_receipt_hash`), naming the service
//!   AND the amount paid, so the whole run is a re-witnessable audit of
//!   *who-called-what-service / paid-whom / wrote-which-cell*.
//!
//! ## The ToolGateway rail (what `invoke` realizes)
//!
//! breadstuffs' `dregg-sdk::ToolGateway` is the canonical agent-economy rail: it
//! admits an inbound tool-call IFF the delegated mandate admits it (scope ·
//! deadline · rate), charges the consumer the provider's per-call `price` as a
//! conserving `Effect::Transfer`, and receipts the metered turn. That type pulls
//! the whole dregg verified core (circuit / lean-ffi / lightclient), which the
//! `polyana-dregg-bridge` deliberately does **not** link (it isolates only the
//! thin proven cap-gate + receipt surface). So `invoke` here is the **faithful
//! in-process realization** of that rail over the surface DreggNet *can* link:
//! the cap-gate is the REAL proven `gate_effect_set` attenuation law; the charge
//! is a conserving `Σδ=0` move mirroring `dregg-payable` (the same shape as
//! `dreggnet-durable`'s `ConservingLedger`, the sanctioned twin of the dregg
//! `Payable`); the receipt is the real chained `turn_shadow_receipt`. A workload
//! `invoke`-ing a registered service is therefore a real metered, cap-gated,
//! conserving, receipted service call — a transacting agent, not a stub.
//!
//! ## Deferred (value-moving + hardware — later / reviewed)
//!
//! `transfer` (a `Σδ=0`-conserved value move) and `subturn` (a general nested
//! turn) are **not** in this batch: they move value and want the lease's value
//! authority + a wider review. The firecracker (`MicroVm`) tier carries the
//! identical frames over vsock but needs a live KVM boot; this batch is the
//! safe-autonomous native python / node tiers only.

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use async_trait::async_trait;
use polyana_core::provider::HostBroker;
use polyana_dregg_bridge::{CapBundle, TurnShadowReceipt, gate_effect_set, turn_shadow_receipt};
use serde_json::Value as Json;
use tokio::sync::Mutex;

use crate::{CapTier, ExecError, Input};

/// A gateway-registered service's handler: `args` → `Ok(result)` / `Err(reason)`.
/// The work the service actually performs once the call is admitted (cap-gated,
/// in-budget, and paid). The cap-gate / meter / conserving charge / receipt
/// around it is the ToolGateway rail this module realizes.
pub type ServiceFn = Arc<dyn Fn(Json) -> std::result::Result<Json, String> + Send + Sync>;

/// **A gateway-registered service** — the unit a workload's `invoke` targets,
/// the in-process realization of a breadstuffs `ToolGateway` provider offering.
///
/// A service carries its `provider` (the holder credited for each call — agent
/// B in the "pay to call agent B's tool" economy), a per-call `price` (the
/// conserving value moved consumer → provider; `0` for a free/unpriced service),
/// and the `handler` that does the work. Registering a service makes it
/// *callable*; the lease's authorized-services allow-set decides whether a given
/// workload *may* call it (the finer scope under the coarse `tool-call` cap).
#[derive(Clone)]
pub struct GatewayService {
    /// The holder credited each call's payment (the service owner / provider B).
    provider: String,
    /// The per-call price moved consumer → provider as a conserving charge
    /// (`0` = a free service: cap-gated + metered + receipted, but no value move).
    price: u64,
    /// The work performed once the call is admitted.
    handler: ServiceFn,
}

/// The bridge-interned effect *class* a host method gates against. These are
/// tokens the dregg bridge's `gate_effect_set` knows how to intern + attenuate;
/// an un-interned token would fail closed, so the host-API maps each method onto
/// the proven vocabulary.
fn coarse_class(method: &str) -> &'static str {
    match method {
        // Calling a service / tool is the `tool-call` EffectIntent kind.
        "invoke" => "tool-call",
        // Reading / writing the workload's own committed cell is a
        // filesystem-shaped effect on its state.
        "cell_read" => "filesystem:read",
        "cell_write" => "filesystem:write",
        _ => "",
    }
}

/// A workload's lease: its ambient authority + budget + cell identity.
///
/// `caps` is the coarse effect-class bundle the lease granted (the bridge's
/// interned vocabulary — `tool-call` / `filesystem:read` / `filesystem:write` /
/// …); every host call attenuates its class from it via `gate_effect_set`.
/// `services` is the finer allow-set of `invoke` targets the lease authorizes
/// (a service may be *implemented* on the broker yet not *authorized* by the
/// lease). `budget` is the meter ceiling; `agent_seed` roots the receipt chain.
#[derive(Clone)]
pub struct Lease {
    /// The coarse effect-class bundle the lease granted (interned vocabulary).
    pub caps: CapBundle,
    /// The `invoke` targets the lease authorizes (finer than the `tool-call`
    /// class). Empty = no service authorized.
    pub services: Vec<String>,
    /// Metering ceiling, in host-call units. Each call costs a base unit + a
    /// per-byte charge; the running spend may never exceed this.
    pub budget: u64,
    /// 32-byte cell identity the workload's receipt chain is rooted at.
    pub agent_seed: [u8; 32],
}

impl Lease {
    /// A lease granting effect classes `caps` (interned tokens) + authorized
    /// `services` (invoke targets), with `budget` meter units and an
    /// `agent_seed` cell identity.
    pub fn new<C, S, T, U>(caps: C, services: S, budget: u64, agent_seed: [u8; 32]) -> Self
    where
        C: IntoIterator<Item = T>,
        T: AsRef<str>,
        S: IntoIterator<Item = U>,
        U: AsRef<str>,
    {
        let caps: Vec<String> = caps.into_iter().map(|s| s.as_ref().to_string()).collect();
        Lease {
            caps: CapBundle::new(caps.iter().map(|s| s.as_str())),
            services: services
                .into_iter()
                .map(|s| s.as_ref().to_string())
                .collect(),
            budget,
            agent_seed,
        }
    }
}

/// Mutable broker state behind one lock: the cell heap + its committed root +
/// the receipt chain + the conserving value ledger.
struct BrokerState {
    cells: HashMap<String, Json>,
    root: [u8; 32],
    receipts: Vec<TurnShadowReceipt>,
    prev_hash: Option<[u8; 32]>,
    /// The CONSERVING value ledger: `holder -> balance` for this gateway's
    /// asset. The consumer (the workload's spend account) is debited and the
    /// provider credited by exactly the per-call price on each paid `invoke`, so
    /// the sum over holders is invariant (`Σδ=0`). The in-process twin of the
    /// dregg `Payable` balance the ToolGateway charge moves.
    balances: HashMap<String, i64>,
    /// Cumulative value moved out of the consumer under this lease (the market
    /// spend, capped at `value_budget` in-band — the `402` ceiling).
    value_spent: u64,
}

/// DreggNet's concrete [`HostBroker`]: the ToolGateway rail realized — cap-gated,
/// metered, **conserving-charged**, receipted host-API.
pub struct ExecHostBroker {
    caps: CapBundle,
    services_allowed: Vec<String>,
    budget: u64,
    agent_seed: [u8; 32],
    services: HashMap<String, GatewayService>,
    spent: AtomicU64,
    calls: AtomicU64,
    seq: AtomicU64,
    start: Instant,
    state: Mutex<BrokerState>,
    /// The consumer holder id — the workload's spend account, derived from its
    /// `agent_seed`. The `from` of every per-call conserving charge.
    consumer: String,
    /// The asset value is denominated in (the gateway's `token_id` analogue).
    asset: String,
    /// The market spend ceiling: cumulative paid value may never exceed this
    /// (the in-band `OverBudget` → `402` cap, the value analogue of `budget`).
    /// `u64::MAX` for an un-capped (free/rate-only) mandate.
    value_budget: u64,
}

/// Content root of the cell heap → the receipt's `*_state_root`. A blake3 hash
/// over the heap's `(key, value)` pairs in sorted-key order, so the root binds
/// the committed contents and a write moves it.
fn cell_root(cells: &HashMap<String, Json>) -> [u8; 32] {
    let mut keys: Vec<&String> = cells.keys().collect();
    keys.sort();
    let mut h = blake3::Hasher::new();
    for k in keys {
        h.update(k.as_bytes());
        h.update(b"=");
        h.update(&serde_json::to_vec(&cells[k]).unwrap_or_default());
        h.update(b";");
    }
    *h.finalize().as_bytes()
}

/// The default asset the conserving value rail denominates in.
const DEFAULT_ASSET: &str = "DREGG";

/// Derive a stable consumer holder id from the workload's `agent_seed` — the
/// spend account the per-call charge debits.
fn consumer_id(agent_seed: &[u8; 32]) -> String {
    let mut s = String::with_capacity(23);
    s.push_str("agent:");
    for b in &agent_seed[..8] {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

impl ExecHostBroker {
    /// A broker over `lease`, with no services registered and an un-capped value
    /// budget. Add `invoke` targets with [`ExecHostBroker::with_service`] (free)
    /// or [`ExecHostBroker::with_priced_service`] (paid), fund the consumer's
    /// spend account with [`ExecHostBroker::with_funding`], and cap the market
    /// spend with [`ExecHostBroker::with_value_budget`].
    pub fn new(lease: Lease) -> Self {
        let consumer = consumer_id(&lease.agent_seed);
        ExecHostBroker {
            caps: lease.caps,
            services_allowed: lease.services,
            budget: lease.budget,
            agent_seed: lease.agent_seed,
            services: HashMap::new(),
            spent: AtomicU64::new(0),
            calls: AtomicU64::new(0),
            seq: AtomicU64::new(0),
            start: Instant::now(),
            state: Mutex::new(BrokerState {
                cells: HashMap::new(),
                root: cell_root(&HashMap::new()),
                receipts: Vec::new(),
                prev_hash: None,
                balances: HashMap::new(),
                value_spent: 0,
            }),
            consumer,
            asset: DEFAULT_ASSET.to_string(),
            value_budget: u64::MAX,
        }
    }

    /// Register a FREE service `invoke` may target (cap-gated by the lease's
    /// service allow-set; metered + receipted, but no value move).
    pub fn with_service(
        self,
        name: impl Into<String>,
        f: impl Fn(Json) -> std::result::Result<Json, String> + Send + Sync + 'static,
    ) -> Self {
        self.with_priced_service(name, "", 0, f)
    }

    /// Register a PAID service: each admitted `invoke` charges `price` from the
    /// consumer (the workload's spend account) to `provider` as a conserving
    /// (`Σδ=0`) value move riding the call — the ToolGateway "pay to call agent
    /// B's tool" shape. A `price` exceeding the consumer's funds or the value
    /// budget refuses the call `402` before it runs.
    pub fn with_priced_service(
        mut self,
        name: impl Into<String>,
        provider: impl Into<String>,
        price: u64,
        f: impl Fn(Json) -> std::result::Result<Json, String> + Send + Sync + 'static,
    ) -> Self {
        self.services.insert(
            name.into(),
            GatewayService {
                provider: provider.into(),
                price,
                handler: Arc::new(f),
            },
        );
        self
    }

    /// Cap the market spend: cumulative paid value may never exceed `budget`
    /// (the in-band `OverBudget` → `402` ceiling, the value analogue of the
    /// call-meter `budget`).
    pub fn with_value_budget(mut self, budget: u64) -> Self {
        self.value_budget = budget;
        self
    }

    /// Fund the consumer's spend account with `amount` of the gateway asset — the
    /// reserve the per-call charges are paid out of (the funded lease's value
    /// budget made real). A construction-time builder (it predates any concurrent
    /// access), so it takes the state by `get_mut` without locking.
    pub fn with_funding(mut self, amount: u64) -> Self {
        let st = self.state.get_mut();
        *st.balances.entry(self.consumer.clone()).or_insert(0) += amount as i64;
        self
    }

    /// The consumer's current spend-account balance.
    pub async fn consumer_balance(&self) -> i64 {
        self.state
            .lock()
            .await
            .balances
            .get(&self.consumer)
            .copied()
            .unwrap_or(0)
    }

    /// A provider's current credited balance.
    pub async fn provider_balance(&self, provider: &str) -> i64 {
        self.state
            .lock()
            .await
            .balances
            .get(provider)
            .copied()
            .unwrap_or(0)
    }

    /// The total value across all holders of the gateway asset — the
    /// conservation witness. Funding aside, every paid call leaves it unchanged
    /// (`Σδ=0`).
    pub async fn value_supply(&self) -> i64 {
        self.state.lock().await.balances.values().sum()
    }

    /// Cumulative value paid out of the consumer under this lease.
    pub async fn value_spent(&self) -> u64 {
        self.state.lock().await.value_spent
    }

    /// Host calls serviced so far (allowed + committed). Refusals don't count.
    pub fn calls(&self) -> u64 {
        self.calls.load(Ordering::Relaxed)
    }

    /// Meter units spent (the running total charged against the lease budget).
    pub fn meter_spent(&self) -> u64 {
        self.spent.load(Ordering::Relaxed)
    }

    /// Number of receipts in the chain.
    pub async fn receipt_count(&self) -> usize {
        self.state.lock().await.receipts.len()
    }

    /// The latest committed receipt hash (chain tip), or `None` before any
    /// committed call.
    pub async fn final_receipt_hash(&self) -> Option<[u8; 32]> {
        self.state.lock().await.prev_hash
    }

    /// Snapshot of the committed cell heap.
    pub async fn cells(&self) -> HashMap<String, Json> {
        self.state.lock().await.cells.clone()
    }

    /// Charge `cost` against the budget, committing the spend. Returns
    /// `Err("over-budget")` (without charging) when it would exceed the lease.
    fn charge(&self, cost: u64) -> std::result::Result<(), String> {
        // Reserve via a CAS loop so a would-be over-budget call never charges.
        let mut cur = self.spent.load(Ordering::Relaxed);
        loop {
            let next = cur.saturating_add(cost);
            if next > self.budget {
                return Err(format!(
                    "over-budget: this call costs {cost}, {cur}/{} already spent",
                    self.budget
                ));
            }
            match self
                .spent
                .compare_exchange_weak(cur, next, Ordering::SeqCst, Ordering::Relaxed)
            {
                Ok(_) => return Ok(()),
                Err(observed) => cur = observed,
            }
        }
    }
}

#[async_trait]
impl HostBroker for ExecHostBroker {
    async fn dispatch(&self, method: &str, frame: &Json) -> std::result::Result<Json, String> {
        // (1) AUTHORITY — gate the effect CLASS through dregg's proven monotone
        // attenuation law (gate_effect_set), then scope `invoke` to the lease's
        // authorized services. A call outside the lease is refused before
        // anything commits; the guest never escalates past its lease.
        match method {
            // `transfer` / `subturn` are deliberately not in this batch.
            "transfer" | "subturn" => {
                return Err(format!(
                    "host method `{method}` is deferred (value-moving / nested turn — \
                     not in the safe-autonomous batch)"
                ));
            }
            "invoke" | "cell_read" | "cell_write" => {}
            other => return Err(format!("unknown host method `{other}`")),
        }
        let class = coarse_class(method);
        let requested = CapBundle::new([class]);
        if gate_effect_set(&self.caps, &requested).is_err() {
            // The proven gate refuses: the lease does not grant this class
            // (e.g. a lease without `filesystem:write` cannot `cell_write`).
            return Err(format!(
                "not-an-attenuation: `{method}` needs the `{class}` class, outside the lease"
            ));
        }
        // Finer per-service scope for `invoke`: a registered service that the
        // lease does not authorize is still refused.
        if method == "invoke" {
            let service = frame.get("service").and_then(|v| v.as_str()).unwrap_or("");
            if !self.services_allowed.iter().any(|s| s == service) {
                return Err(format!(
                    "not-an-attenuation: service `{service}` is outside the lease"
                ));
            }
        }

        // Resolve a priced `invoke`'s registered service up-front: its per-call
        // price + provider drive the conserving charge, its handler does the
        // work. (The lease's service allow-set was already checked above; this is
        // the registered-implementation lookup.)
        let invoke_target: Option<(u64, String, ServiceFn)> = if method == "invoke" {
            let service = frame.get("service").and_then(|v| v.as_str()).unwrap_or("");
            let svc = self
                .services
                .get(service)
                .ok_or_else(|| format!("no such service `{service}`"))?;
            Some((svc.price, svc.provider.clone(), svc.handler.clone()))
        } else {
            None
        };
        let price = invoke_target.as_ref().map(|(p, _, _)| *p).unwrap_or(0);

        // (2) ADMIT — every refusal fires BEFORE any commit (the payment, the
        // metered resource, and the value budget are each refused before the call
        // runs, never after a partial effect). One lock spans admission → commit.
        let mut st = self.state.lock().await;

        // Guard the i64 value domain ONCE: a `price` exceeding `i64::MAX` would
        // sign-cast NEGATIVE in the solvency check and the conserving debit below —
        // solvency would pass spuriously and the debit would *credit* the consumer (a
        // conservation break). Refuse such a call outright; every charge below uses the
        // checked `price_i64`, never a `price as i64` cast.
        let price_i64: i64 = i64::try_from(price).map_err(|_| {
            format!("invalid-price: service price {price} exceeds the i64 value domain (refused)")
        })?;

        // (2a) VALUE BUDGET (priced invoke) — over the market spend ceiling →
        // `402`, before the call. The value analogue of the call-meter budget.
        if price > 0 {
            let next = st.value_spent.saturating_add(price);
            if next > self.value_budget {
                return Err(format!(
                    "over-budget: paying {price} for this call would push spend to {next}, \
                     past the {} value budget (402)",
                    self.value_budget
                ));
            }
            // (2b) SOLVENCY — the consumer must actually hold the price (the
            // conserved backstop under the in-band cap) → `402`, before the call.
            let bal = st.balances.get(&self.consumer).copied().unwrap_or(0);
            if bal < price_i64 {
                return Err(format!(
                    "insufficient-funds: consumer `{}` holds {bal} of `{}`, the call costs \
                     {price} (402)",
                    self.consumer, self.asset
                ));
            }
        }

        // (2c) CALL METER — the per-call resource cost (base + per-byte). Over the
        // lease budget → refused here, never after a partial effect.
        let payload_bytes = serde_json::to_vec(frame).map(|b| b.len()).unwrap_or(0) as u64;
        let cost = 1 + payload_bytes / 64;
        self.charge(cost)?;

        // (3) RUN the effect + (3b) the CONSERVING CHARGE + (4) RECEIPT it.
        let pre_root = st.root;
        let (ret, fn_name): (Json, String) = match method {
            "invoke" => {
                let (_p, provider, handler) = invoke_target.expect("invoke target resolved above");
                let service = frame.get("service").and_then(|v| v.as_str()).unwrap_or("");
                let args = frame.get("args").cloned().unwrap_or(Json::Array(vec![]));
                // The work runs FIRST: a failing service moves no value (no
                // payment for work not done).
                let out = handler(args)?;
                // (3b) the CONSERVING CHARGE — debit consumer, credit provider by
                // exactly `price` (`Σδ=0`), riding this same call. Pre-checked
                // solvent + in-budget above, so it cannot fail here.
                if price > 0 {
                    *st.balances.entry(self.consumer.clone()).or_insert(0) -= price_i64;
                    *st.balances.entry(provider.clone()).or_insert(0) += price_i64;
                    st.value_spent += price;
                }
                (
                    out,
                    format!("host.invoke:{service}#paid={price}->{provider}"),
                )
            }
            "cell_read" => {
                let path = frame
                    .get("path")
                    .and_then(|v| v.as_str())
                    .ok_or("cell_read: missing `path`")?;
                let out = st.cells.get(path).cloned().unwrap_or(Json::Null);
                (out, format!("host.cell_read:{path}"))
            }
            "cell_write" => {
                let path = frame
                    .get("path")
                    .and_then(|v| v.as_str())
                    .ok_or("cell_write: missing `path`")?
                    .to_string();
                let val = frame.get("val").cloned().unwrap_or(Json::Null);
                st.cells.insert(path.clone(), val);
                // Move the cell to its new committed root.
                st.root = cell_root(&st.cells);
                (Json::Bool(true), format!("host.cell_write:{path}"))
            }
            _ => unreachable!("authority match already covered the method set"),
        };
        let post_root = st.root;

        let seq = self.seq.fetch_add(1, Ordering::Relaxed);
        let args_canonical = serde_json::to_vec(frame).unwrap_or_default();
        let ret_canonical = serde_json::to_vec(&ret).unwrap_or_default();
        let receipt = turn_shadow_receipt(
            seq,
            self.start.elapsed().as_nanos(),
            fn_name,
            args_canonical,
            ret_canonical,
            self.agent_seed,
            pre_root,
            post_root,
            st.prev_hash,
        )
        .map_err(|e| format!("receipt: {e:?}"))?;
        st.prev_hash = Some(receipt.receipt_hash);
        st.receipts.push(receipt);
        drop(st);

        self.calls.fetch_add(1, Ordering::Relaxed);
        Ok(ret)
    }
}

/// The result of a transacting run: the entrypoint's values + the achieved
/// enforcement, plus the host-API transaction summary (calls / meter / receipt
/// chain / committed cell heap).
#[derive(Debug, Clone)]
pub struct TransactingOutput {
    pub values: Vec<String>,
    pub enforcement: String,
    /// Host calls serviced (allowed + committed).
    pub host_calls: u64,
    /// Meter units charged against the lease budget.
    pub meter_spent: u64,
    /// Receipts emitted (one per committed host call).
    pub receipts: usize,
    /// The receipt-chain tip (the final committed receipt hash).
    pub final_receipt_hash: Option<[u8; 32]>,
    /// The workload's committed cell heap after the run.
    pub cells: HashMap<String, Json>,
    /// Cumulative value moved consumer → provider by priced `invoke`s (the
    /// conserving market spend; `0` if every service called was free).
    pub value_paid: u64,
    /// The conserving value ledger after the run (`holder -> balance`) — the
    /// witness that a paid call moved value consumer → provider and conserved it.
    pub balances: HashMap<String, i64>,
}

/// Run a workload that **transacts** — the python / node guest may call the
/// host-API (`invoke` / `cell_read` / `cell_write`) mid-execution against
/// `broker`, each call cap-gated / metered / receipted. `cap_tier` must be a
/// native interpreter tier ([`CapTier::Caged`]); the wasm / firecracker tiers
/// don't speak the host-call wire in this batch.
///
/// The `broker` is returned-through via the `Arc` the caller holds, so after
/// the run the caller can read its receipts / meter / cells — and
/// [`TransactingOutput`] carries a snapshot for convenience.
pub fn run_workload_transacting(
    lang: &str,
    source: &str,
    cap_tier: CapTier,
    input: &[Input],
    broker: Arc<ExecHostBroker>,
) -> std::result::Result<TransactingOutput, ExecError> {
    if cap_tier != CapTier::Caged {
        return Err(ExecError::TierNotServed {
            lang: lang.to_string(),
            tier: cap_tier,
            detail: "the host-API wire is wired on the native interpreter tiers \
                     (python / node at Caged) in this batch; the wasm + firecracker \
                     tiers carry it in a later rung"
                .into(),
        });
    }
    let output = match lang {
        "python" | "py" => run_on_python_brokered(source, input, broker.clone())?,
        "node" | "js" => run_on_node_brokered(source, input, broker.clone())?,
        other => return Err(ExecError::UnsupportedLang(other.to_string())),
    };
    // Drive the broker snapshots on a tiny runtime (its accessors are async).
    let rt = tokio::runtime::Builder::new_current_thread()
        .build()
        .map_err(|e| ExecError::Runtime(e.to_string()))?;
    let (receipts, final_receipt_hash, cells, value_paid, balances) = rt.block_on(async {
        let st = broker.state.lock().await;
        (
            st.receipts.len(),
            st.prev_hash,
            st.cells.clone(),
            st.value_spent,
            st.balances.clone(),
        )
    });
    Ok(TransactingOutput {
        values: output.values,
        enforcement: output.enforcement,
        host_calls: broker.calls(),
        meter_spent: broker.meter_spent(),
        receipts,
        final_receipt_hash,
        cells,
        value_paid,
        balances,
    })
}

/// Drive the CPython provider with `broker` bound (the transacting variant of
/// `run_on_python`).
fn run_on_python_brokered(
    source: &str,
    input: &[Input],
    broker: Arc<ExecHostBroker>,
) -> std::result::Result<crate::Output, ExecError> {
    use polyana_core::artifact::{ArtifactKind, ArtifactMetadata, ArtifactStore};
    use polyana_core::provider::ExecutionProvider;
    use polyana_python_provider::PythonProvider;

    let args: Vec<_> = input.iter().map(Input::to_value).collect();
    let timeout = crate::workload_timeout();
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| ExecError::Runtime(e.to_string()))?;
    rt.block_on(async move {
        let provider = PythonProvider::new().with_host_broker(broker as Arc<dyn HostBroker>);
        let enforcement = format!("{:?}", provider.enforcement_level());
        let store = ArtifactStore::new();
        let id = store
            .store(
                ArtifactKind::NativeBinary,
                source.as_bytes().to_vec(),
                ArtifactMetadata::default(),
            )
            .map_err(|e| ExecError::Load(e.to_string()))?;
        let component = provider
            .load_component(&store, id)
            .await
            .map_err(|e| ExecError::Load(e.to_string()))?;
        let mut instance = provider
            .instantiate_with_caps(&component, &[], crate::TENANT)
            .await
            .map_err(|e| ExecError::Instantiate(e.to_string()))?;
        let call = provider.call(&mut instance, crate::ENTRYPOINT, &args);
        let values = match tokio::time::timeout(timeout, call).await {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => return Err(ExecError::Call(e.to_string())),
            Err(_elapsed) => {
                drop(instance);
                return Err(ExecError::Timeout {
                    secs: timeout.as_secs(),
                });
            }
        };
        Ok(crate::Output {
            values: values.iter().map(crate::value_to_string).collect(),
            enforcement,
        })
    })
}

/// Drive the Node provider with `broker` bound (the transacting variant of
/// `run_on_node`).
fn run_on_node_brokered(
    source: &str,
    input: &[Input],
    broker: Arc<ExecHostBroker>,
) -> std::result::Result<crate::Output, ExecError> {
    use polyana_core::artifact::{ArtifactKind, ArtifactMetadata, ArtifactStore};
    use polyana_core::provider::ExecutionProvider;
    use polyana_node_provider::NodeProvider;

    let args: Vec<_> = input.iter().map(Input::to_value).collect();
    let timeout = crate::workload_timeout();
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| ExecError::Runtime(e.to_string()))?;
    rt.block_on(async move {
        let provider = NodeProvider::new().with_host_broker(broker as Arc<dyn HostBroker>);
        let enforcement = format!("{:?}", provider.enforcement_level());
        let store = ArtifactStore::new();
        let id = store
            .store(
                ArtifactKind::NativeBinary,
                source.as_bytes().to_vec(),
                ArtifactMetadata::default(),
            )
            .map_err(|e| ExecError::Load(e.to_string()))?;
        let component = provider
            .load_component(&store, id)
            .await
            .map_err(|e| ExecError::Load(e.to_string()))?;
        let mut instance = provider
            .instantiate_with_caps(&component, &[], crate::TENANT)
            .await
            .map_err(|e| ExecError::Instantiate(e.to_string()))?;
        let call = provider.call(&mut instance, crate::ENTRYPOINT, &args);
        let values = match tokio::time::timeout(timeout, call).await {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => return Err(ExecError::Call(e.to_string())),
            Err(_elapsed) => {
                drop(instance);
                return Err(ExecError::Timeout {
                    secs: timeout.as_secs(),
                });
            }
        };
        Ok(crate::Output {
            values: values.iter().map(crate::value_to_string).collect(),
            enforcement,
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn python3_available() -> bool {
        let bin = std::env::var("POLYANA_PYTHON_BIN").unwrap_or_else(|_| "python3".into());
        std::process::Command::new(bin)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    fn node_available() -> bool {
        let bin = std::env::var("POLYANA_NODE_BIN").unwrap_or_else(|_| "node".into());
        std::process::Command::new(bin)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// A lease granting the cell read/write classes + the `tool-call` class,
    /// authorizing the `echo` service, with a budget big enough for the happy
    /// path; an `echo` service that returns its args.
    fn echo_broker() -> Arc<ExecHostBroker> {
        let lease = Lease::new(
            ["tool-call", "filesystem:read", "filesystem:write"],
            ["echo"],
            1_000,
            [0xA5; 32],
        );
        Arc::new(ExecHostBroker::new(lease).with_service("echo", |args| Ok(args)))
    }

    /// A python guest that transacts mid-`run`: writes its cell, reads it back,
    /// invokes the permitted `echo` service, returns the round-tripped value.
    const PY_TRANSACTING: &str = r#"import __polyana__ as p
def handler(name, args):
    p.cell_write("counter", 41)
    v = p.cell_read("counter")
    echoed = p.invoke("echo", [v + 1])
    return [echoed[0]]
p.dispatch(handler)
p.serve_forever()
"#;

    const JS_TRANSACTING: &str = r#"const p = require('__polyana__');
p.serveForever((name, args) => {
  p.cellWrite('counter', 41);
  const v = p.cellRead('counter');
  const echoed = p.invoke('echo', [v + 1]);
  return [echoed[0]];
});
"#;

    /// CPython transacts: cell write/read persists + reads back, invoke is
    /// allowed by the cap, the calls are metered + receipted (chained).
    #[test]
    fn python_workload_transacts() {
        if !python3_available() {
            eprintln!("skipping: no python3 on PATH");
            return;
        }
        let broker = echo_broker();
        let out = run_workload_transacting("python", PY_TRANSACTING, CapTier::Caged, &[], broker)
            .expect("python transacting run");
        assert_eq!(out.values, vec!["42".to_string()]);
        assert_eq!(out.host_calls, 3, "3 host calls serviced");
        assert!(out.meter_spent >= 3, "metered: {}", out.meter_spent);
        assert_eq!(out.receipts, 3, "one receipt per committed call");
        assert!(out.final_receipt_hash.is_some(), "receipt chain has a tip");
        assert_eq!(
            out.cells.get("counter"),
            Some(&serde_json::json!(41)),
            "cell committed on the host side"
        );
    }

    /// Node transacts: same affordance on the real `node` tier.
    #[test]
    fn node_workload_transacts() {
        if !node_available() {
            eprintln!("skipping: no node on PATH");
            return;
        }
        let broker = echo_broker();
        let out = run_workload_transacting("node", JS_TRANSACTING, CapTier::Caged, &[], broker)
            .expect("node transacting run");
        assert_eq!(out.values, vec!["42".to_string()]);
        assert_eq!(out.host_calls, 3);
        assert_eq!(out.receipts, 3);
        assert!(out.final_receipt_hash.is_some());
        assert_eq!(out.cells.get("counter"), Some(&serde_json::json!(41)));
    }

    /// A workload WITHOUT the cap for a service is refused IN-BAND: the lease
    /// grants `invoke:echo` only, so invoking `secret` is refused
    /// `not-an-attenuation` and the run surfaces a clean error — the guest
    /// never reaches a service outside its lease.
    #[test]
    fn invoke_outside_lease_is_refused() {
        if !python3_available() {
            eprintln!("skipping: no python3 on PATH");
            return;
        }
        // The lease authorizes `echo`, NOT `secret` — even though `secret` is
        // registered (implemented) on the broker, the cap-gate refuses it.
        let lease = Lease::new(["tool-call"], ["echo"], 1_000, [0x5A; 32]);
        let broker = Arc::new(
            ExecHostBroker::new(lease)
                .with_service("echo", |a| Ok(a))
                .with_service("secret", |_| Ok(serde_json::json!("leaked"))),
        );
        let guest = r#"import __polyana__ as p
def handler(name, args):
    return [p.invoke("secret", [])]
p.dispatch(handler)
p.serve_forever()
"#;
        let err = run_workload_transacting("python", guest, CapTier::Caged, &[], broker.clone())
            .expect_err("a service outside the lease must be refused");
        assert!(
            format!("{err}").contains("not-an-attenuation"),
            "refusal names the cap-gate: {err}"
        );
        // Fail-closed: the refused call did NOT commit a receipt or charge meter.
        assert_eq!(broker.calls(), 0, "refused call is not counted");
        assert_eq!(broker.meter_spent(), 0, "refused call charges nothing");
    }

    /// Over-budget is refused before the commit: a tiny budget lets the first
    /// call through but refuses the next, and the refused call leaves no
    /// receipt — the spend is refused before the commit, never after.
    #[test]
    fn over_budget_is_refused_before_commit() {
        if !python3_available() {
            eprintln!("skipping: no python3 on PATH");
            return;
        }
        // Budget = 1 unit: the first cell_write (cost >= 1) consumes it; the
        // second host call is over-budget.
        let lease = Lease::new(
            ["filesystem:read", "filesystem:write"],
            Vec::<String>::new(),
            1,
            [0x11; 32],
        );
        let broker = Arc::new(ExecHostBroker::new(lease));
        let guest = r#"import __polyana__ as p
def handler(name, args):
    p.cell_write("a", 1)
    p.cell_write("b", 2)
    return [0]
p.dispatch(handler)
p.serve_forever()
"#;
        let err = run_workload_transacting("python", guest, CapTier::Caged, &[], broker.clone())
            .expect_err("second write must be over-budget");
        assert!(format!("{err}").contains("over-budget"), "got {err}");
        // Exactly one call committed (a receipt + the meter spent on it).
        assert_eq!(broker.calls(), 1, "only the funded call committed");
        let rt = tokio::runtime::Runtime::new().unwrap();
        assert_eq!(rt.block_on(broker.receipt_count()), 1);
    }

    /// The cap-gate is dregg's real attenuation law, not a stub: a lease's
    /// bundle accepts a granted class and rejects an ungranted one.
    #[test]
    fn cap_gate_is_a_real_attenuation_check() {
        let lease = Lease::new(["tool-call", "filesystem:read"], ["echo"], 10, [0; 32]);
        let granted = CapBundle::new(["filesystem:read"]);
        let ungranted = CapBundle::new(["filesystem:write"]);
        assert!(gate_effect_set(&lease.caps, &granted).is_ok());
        assert!(gate_effect_set(&lease.caps, &ungranted).is_err());
    }

    /// The proven gate itself bites at the host-API layer: a lease that grants
    /// `filesystem:read` but NOT `filesystem:write` genuinely cannot
    /// `cell_write` — refused `not-an-attenuation` before any commit, by
    /// `gate_effect_set` on the coarse class (not merely the service allow-set).
    #[test]
    fn cell_write_refused_without_the_write_class() {
        if !python3_available() {
            eprintln!("skipping: no python3 on PATH");
            return;
        }
        let lease = Lease::new(
            ["filesystem:read"], // read but NOT write
            Vec::<String>::new(),
            1_000,
            [0x77; 32],
        );
        let broker = Arc::new(ExecHostBroker::new(lease));
        let guest = r#"import __polyana__ as p
def handler(name, args):
    return [p.cell_write("x", 1)]
p.dispatch(handler)
p.serve_forever()
"#;
        let err = run_workload_transacting("python", guest, CapTier::Caged, &[], broker.clone())
            .expect_err("cell_write without filesystem:write must be refused");
        assert!(format!("{err}").contains("not-an-attenuation"), "got {err}");
        assert!(
            format!("{err}").contains("filesystem:write"),
            "names the class: {err}"
        );
        assert_eq!(broker.calls(), 0, "refused call commits nothing");
    }

    // ── The ToolGateway rail behind `invoke`: cap ✓ · budget ✓ · charge Σδ=0 · else 402 ──
    //
    // These drive the broker's `dispatch` directly on a runtime (no python on
    // PATH needed), so the metered cap-gated conserving-charge enforcement is
    // proven unconditionally; the python/node tests above prove the same rail
    // reached from a REAL guest mid-execution.

    /// A workload `invoke`s a real gateway-registered PAID service: admitted by
    /// the cap + budget, the per-call price moves consumer → provider CONSERVING
    /// (`Σδ=0`), and the call is metered + receipted. The transacting agent made
    /// real — a real metered cap-gated service call that moves value.
    #[test]
    fn priced_invoke_charges_conserving_and_is_receipted() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            // Lease grants the `tool-call` class + authorizes `search`; a paid
            // `search` service (price 7, provider B); consumer funded with 20.
            let lease = Lease::new(["tool-call"], ["search"], 1_000, [0x42; 32]);
            let broker = ExecHostBroker::new(lease)
                .with_priced_service("search", "provider:B", 7, |a| Ok(a))
                .with_value_budget(100)
                .with_funding(20);
            assert_eq!(broker.value_supply().await, 20, "the funded reserve");

            let frame = serde_json::json!({"service": "search", "args": [1]});
            let out = broker.dispatch("invoke", &frame).await.expect("admitted");
            assert_eq!(out, serde_json::json!([1]), "the service ran + returned");

            // CHARGED Σδ=0: consumer 20-7=13, provider 0+7=7, supply unchanged.
            assert_eq!(
                broker.consumer_balance().await,
                13,
                "consumer debited the price"
            );
            assert_eq!(
                broker.provider_balance("provider:B").await,
                7,
                "provider credited"
            );
            assert_eq!(broker.value_supply().await, 20, "Σδ=0 across the charge");
            assert_eq!(
                broker.value_spent().await,
                7,
                "the market spend advanced by the price"
            );
            // METERED + RECEIPTED.
            assert_eq!(broker.calls(), 1, "one committed call");
            assert!(broker.meter_spent() >= 1, "the call was metered");
            assert_eq!(
                broker.receipt_count().await,
                1,
                "the paid call is receipted"
            );
            assert!(
                broker.final_receipt_hash().await.is_some(),
                "the receipt chain has a tip"
            );
        });
    }

    /// 402 on over-(value-)budget: the value budget admits the first paid call
    /// but refuses the next BEFORE it runs — no value moves, no receipt. The
    /// market analogue of the call-meter `over-budget`.
    #[test]
    fn over_value_budget_invoke_refused_402() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            // Value budget = 10, price = 7: the 1st call (7) fits, the 2nd (14 > 10)
            // is over-budget. Funded generously so SOLVENCY is not what bites.
            let lease = Lease::new(["tool-call"], ["search"], 1_000, [0x43; 32]);
            let broker = ExecHostBroker::new(lease)
                .with_priced_service("search", "provider:B", 7, |a| Ok(a))
                .with_value_budget(10)
                .with_funding(100);
            let frame = serde_json::json!({"service": "search", "args": [1]});
            broker
                .dispatch("invoke", &frame)
                .await
                .expect("first call fits the budget");

            let err = broker
                .dispatch("invoke", &frame)
                .await
                .expect_err("second call is over the value budget");
            assert!(err.contains("over-budget"), "402 names the budget: {err}");
            assert!(err.contains("402"), "the refusal is the 402 shape: {err}");
            // Fail-closed: the refused call moved no value + left no receipt.
            assert_eq!(broker.value_spent().await, 7, "only the first call paid");
            assert_eq!(
                broker.provider_balance("provider:B").await,
                7,
                "no second charge"
            );
            assert_eq!(
                broker.value_supply().await,
                100,
                "Σδ=0 — nothing created/destroyed"
            );
            assert_eq!(broker.calls(), 1, "the refused call is not counted");
            assert_eq!(
                broker.receipt_count().await,
                1,
                "the refused call left no receipt"
            );
        });
    }

    /// 402 on insolvency: the consumer cannot actually pay the price (the
    /// conserved backstop under the in-band budget cap) — refused before the
    /// call, no value moves.
    #[test]
    fn insolvent_invoke_refused_402() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            // Price 7, but the consumer is funded only 3 — insufficient funds.
            let lease = Lease::new(["tool-call"], ["search"], 1_000, [0x44; 32]);
            let broker = ExecHostBroker::new(lease)
                .with_priced_service("search", "provider:B", 7, |a| Ok(a))
                .with_value_budget(100)
                .with_funding(3);
            let frame = serde_json::json!({"service": "search", "args": [1]});
            let err = broker
                .dispatch("invoke", &frame)
                .await
                .expect_err("an insolvent consumer cannot pay");
            assert!(
                err.contains("insufficient-funds"),
                "402 names insolvency: {err}"
            );
            assert_eq!(
                broker.consumer_balance().await,
                3,
                "no debit on a refused call"
            );
            assert_eq!(broker.provider_balance("provider:B").await, 0, "no credit");
            assert_eq!(broker.calls(), 0, "the refused call is not counted");
        });
    }

    /// A price beyond the i64 value domain is refused — it would otherwise sign-cast
    /// NEGATIVE, pass the solvency check spuriously, and *credit* the consumer on the
    /// "debit" (a conservation break). No value moves.
    #[test]
    fn out_of_domain_price_refused_no_conservation_break() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            // A price > i64::MAX (the sign-cast hazard).
            let lease = Lease::new(["tool-call"], ["search"], 1_000, [0x44; 32]);
            let broker = ExecHostBroker::new(lease)
                .with_priced_service("search", "provider:B", u64::MAX, |a| Ok(a))
                .with_value_budget(u64::MAX)
                .with_funding(100);
            let frame = serde_json::json!({"service": "search", "args": [1]});
            let err = broker
                .dispatch("invoke", &frame)
                .await
                .expect_err("an out-of-domain price is refused");
            assert!(
                err.contains("invalid-price"),
                "names the domain refusal: {err}"
            );
            // No conservation break: the consumer is NOT credited, the provider not paid.
            assert_eq!(
                broker.consumer_balance().await,
                100,
                "consumer balance unchanged (not credited)"
            );
            assert_eq!(
                broker.provider_balance("provider:B").await,
                0,
                "provider not paid"
            );
            assert_eq!(broker.calls(), 0, "the refused call is not counted");
        });
    }

    /// cap-refused: a service outside the lease's caps is refused
    /// `not-an-attenuation` by the proven gate BEFORE any charge — even though
    /// it is registered + paid + the consumer is funded.
    #[test]
    fn priced_invoke_outside_lease_caps_refused() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            // The lease authorizes `search`, NOT `secret`.
            let lease = Lease::new(["tool-call"], ["search"], 1_000, [0x45; 32]);
            let broker = ExecHostBroker::new(lease)
                .with_priced_service("search", "provider:B", 7, |a| Ok(a))
                .with_priced_service("secret", "provider:C", 1, |_| Ok(serde_json::json!("x")))
                .with_funding(100);
            let frame = serde_json::json!({"service": "secret", "args": []});
            let err = broker
                .dispatch("invoke", &frame)
                .await
                .expect_err("a service outside the lease's caps is refused");
            assert!(
                err.contains("not-an-attenuation"),
                "cap-gate names it: {err}"
            );
            // No charge, no meter, no receipt on a cap-refusal.
            assert_eq!(
                broker.value_spent().await,
                0,
                "cap-refused call pays nothing"
            );
            assert_eq!(broker.provider_balance("provider:C").await, 0, "no credit");
            assert_eq!(broker.calls(), 0);
        });
    }

    /// The same rail, reached from a REAL CPython guest mid-execution: the guest
    /// `invoke`s a paid service; the host charges consumer → provider Σδ=0,
    /// surfaced in the run's transaction summary.
    #[test]
    fn python_workload_invokes_a_paid_service() {
        if !python3_available() {
            eprintln!("skipping: no python3 on PATH");
            return;
        }
        let lease = Lease::new(["tool-call"], ["search"], 1_000, [0x33; 32]);
        let broker = Arc::new(
            ExecHostBroker::new(lease)
                .with_priced_service("search", "provider:B", 5, |a| Ok(a))
                .with_value_budget(100)
                .with_funding(50),
        );
        let guest = r#"import __polyana__ as p
def handler(name, args):
    r = p.invoke("search", ["q"])
    return [r[0]]
p.dispatch(handler)
p.serve_forever()
"#;
        let out = run_workload_transacting("python", guest, CapTier::Caged, &[], broker)
            .expect("python paid-service run");
        assert_eq!(
            out.values,
            vec!["q".to_string()],
            "the service result came back"
        );
        assert_eq!(out.value_paid, 5, "the call paid the per-call price");
        assert_eq!(
            out.balances.get("provider:B"),
            Some(&5),
            "provider credited Σδ=0"
        );
        assert_eq!(
            out.balances.values().sum::<i64>(),
            50,
            "Σδ=0 — value conserved"
        );
        assert_eq!(out.receipts, 1, "the paid call is receipted");
    }
}
