//! `egress` — deny-by-default outbound network control for compute workloads
//! (audit risk **E-5**, existential).
//!
//! ## The vector this closes
//!
//! A sandboxed workload that can still open an arbitrary outbound socket can
//! mine, DDoS, spam, or exfil — and the first time one does, the upstream
//! provider null-routes the WHOLE fleet's egress IP. Process / fs isolation
//! (seccomp, Landlock, the WASI preopen deny-default) bounds what a workload
//! reads on the host; it does NOT bound what it *reaches on the network*. This
//! module is the missing wall: **a workload reaches NOTHING on the network
//! unless its cap bundle explicitly granted that destination.**
//!
//! ## The policy
//!
//! [`EgressPolicy`] is an allowlist built from the lease's capability strings.
//! It is **deny-by-default**: an [`EgressPolicy`] with no rules ([`EgressPolicy::deny_all`])
//! refuses every destination. A workload reaches a destination ONLY if one of
//! its caps named it. The cap grammar is
//!
//! ```text
//! egress:<host>:<port>
//! ```
//!
//! where `<host>` is an IPv4/IPv6 literal, a CIDR block (`10.0.0.0/8`,
//! `[2001:db8::]/32`), a domain (`api.example.com`), a wildcard subdomain
//! (`*.example.com`), or `*` (any host); and `<port>` is a `u16` or `*` (any
//! port). Examples:
//!
//! ```text
//! egress:api.openai.com:443     — exactly that host, exactly :443
//! egress:*.internal:8080        — any subdomain of `internal`, :8080
//! egress:10.0.0.0/8:*           — the 10/8 block, any port
//! egress:*                      — any host, any port (the full grant)
//! ```
//!
//! This is the same shape as the rest of DreggNet's cap vocabulary: a lease
//! carries a flat `Vec<String>` of granted caps (see `host_api::Lease`,
//! `webauth::grant`), and attenuation can only ever REMOVE an `egress:` cap —
//! so a sub-agent's reach is a subset of its parent's, never a superset (the
//! no-amplify property the `webauth` credential chain proves on the wire).
//!
//! ## Enforcement
//!
//! * **In-process (proven here).** [`EgressPolicy::allows_addr`] is the exact
//!   deny-by-default predicate an owned sandbox engine consults per socket:
//!   deny-all admits nothing; a granted destination admits ONLY the granted
//!   (ip, port) pairs. It is unit-testable without a live socket, so the
//!   in-process decision is proven here regardless of which engine backs the
//!   wasm tier.
//! * **microVM / Caged (live host enforcement, NAMED seam).** A microVM / netns
//!   tier enforces egress at the host: no tap device / no route / a filtered tap
//!   to the allowed destinations unless an `egress:` cap grants it. The policy +
//!   the destination allowlist are computed here; the live
//!   `Capability → tap/MMDS/route` translation is the named host-netns seam —
//!   see [`firecracker_netns_seam`].
//!
//! ## Metering + receipts
//!
//! Egress is metered like bandwidth: [`EgressGuard`] draws a connection (and,
//! optionally, bytes) from a [`Meter`](crate::meter::Meter) cell on every
//! admitted connection, so a workload's outbound rate is bounded by the same
//! replenishing-budget primitive that bounds its compute — a mining / DDoS /
//! spam loop hits a hard `402` ceiling, not an open pipe. Every decision (a
//! grant exercised OR a destination refused) is appended to an [`EgressLog`],
//! so the audit trail shows exactly what a workload reached and what it was
//! refused.

use std::net::IpAddr;

use crate::meter::{Meter, MeterError, MeterKey};

// ===========================================================================
// Destinations
// ===========================================================================

/// The transport a workload is reaching a destination over. The `egress:` cap
/// grammar is protocol-agnostic (a granted destination is reachable over TCP
/// and UDP alike — the threat is *reaching the host at all*), but the protocol
/// is carried on the destination + the receipt for the audit trail and for a
/// future proto-scoped grant form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EgressProtocol {
    Tcp,
    Udp,
}

impl std::fmt::Display for EgressProtocol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            EgressProtocol::Tcp => "tcp",
            EgressProtocol::Udp => "udp",
        })
    }
}

/// How a workload named a destination host: a resolved IP literal, or a name it
/// asked to connect to (resolved by the runtime). Both forms are matched
/// against the policy; the in-process `socket_addr_check` path only ever sees
/// the resolved [`HostId::Ip`] form (WASI hands the closure a `SocketAddr`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostId {
    Ip(IpAddr),
    Name(String),
}

/// One outbound destination a workload is attempting to reach.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EgressDest {
    pub host: HostId,
    pub port: u16,
    pub protocol: EgressProtocol,
}

impl EgressDest {
    /// A TCP destination named by resolved IP — the form the wasmtime
    /// `socket_addr_check` closure sees.
    pub fn ip(ip: IpAddr, port: u16) -> EgressDest {
        EgressDest {
            host: HostId::Ip(ip),
            port,
            protocol: EgressProtocol::Tcp,
        }
    }

    /// A TCP destination named by hostname (resolved by the runtime).
    pub fn host(name: impl Into<String>, port: u16) -> EgressDest {
        EgressDest {
            host: HostId::Name(name.into()),
            port,
            protocol: EgressProtocol::Tcp,
        }
    }

    /// Re-tag this destination as UDP.
    #[must_use]
    pub fn udp(mut self) -> EgressDest {
        self.protocol = EgressProtocol::Udp;
        self
    }

    fn host_str(&self) -> String {
        match &self.host {
            HostId::Ip(ip) => ip.to_string(),
            HostId::Name(n) => n.clone(),
        }
    }
}

impl std::fmt::Display for EgressDest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{} ({})", self.host_str(), self.port, self.protocol)
    }
}

// ===========================================================================
// Rules
// ===========================================================================

/// The host half of an [`EgressRule`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostMatch {
    /// `*` — any host.
    Any,
    /// An exact IP literal.
    Ip(IpAddr),
    /// A CIDR block: a network address + a prefix length in bits.
    Cidr(IpAddr, u8),
    /// An exact domain (matched case-insensitively).
    Domain(String),
    /// A wildcard subdomain `*.example.com` — matches any strict subdomain of
    /// `example.com` (not the apex; grant `egress:example.com:…` for that).
    DomainSuffix(String),
}

impl HostMatch {
    fn matches(&self, host: &HostId) -> bool {
        match (self, host) {
            (HostMatch::Any, _) => true,
            (HostMatch::Ip(a), HostId::Ip(b)) => a == b,
            (HostMatch::Cidr(net, prefix), HostId::Ip(b)) => cidr_contains(*net, *prefix, *b),
            (HostMatch::Domain(d), HostId::Name(n)) => n.eq_ignore_ascii_case(d),
            (HostMatch::DomainSuffix(base), HostId::Name(n)) => {
                let n = n.to_ascii_lowercase();
                let suffix = format!(".{}", base.to_ascii_lowercase());
                n.ends_with(&suffix) && n.len() > suffix.len()
            }
            // An IP rule never matches a bare name, and a domain rule never
            // matches a bare IP — fail-closed, no implicit resolution.
            _ => false,
        }
    }
}

/// The port half of an [`EgressRule`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PortMatch {
    Any,
    Exact(u16),
}

impl PortMatch {
    fn matches(&self, port: u16) -> bool {
        match self {
            PortMatch::Any => true,
            PortMatch::Exact(p) => *p == port,
        }
    }
}

/// One parsed `egress:<host>:<port>` grant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EgressRule {
    pub host: HostMatch,
    pub port: PortMatch,
}

impl EgressRule {
    fn matches(&self, dest: &EgressDest) -> bool {
        self.host.matches(&dest.host) && self.port.matches(dest.port)
    }
}

/// A malformed `egress:` cap — fail-closed: a grant that cannot be parsed is an
/// ERROR (it is never silently dropped, which could widen or narrow reach
/// invisibly).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EgressParseError {
    pub cap: String,
    pub reason: String,
}

impl std::fmt::Display for EgressParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "malformed egress cap `{}`: {}", self.cap, self.reason)
    }
}

impl std::error::Error for EgressParseError {}

/// The prefix that marks a capability string as an egress grant.
pub const EGRESS_CAP_PREFIX: &str = "egress:";

/// Parse the body of one `egress:` cap (the part AFTER `egress:`) into a rule.
fn parse_rule(body: &str, full: &str) -> Result<EgressRule, EgressParseError> {
    let err = |reason: &str| EgressParseError {
        cap: full.to_string(),
        reason: reason.to_string(),
    };

    // `egress:*` — the full grant (any host, any port).
    if body == "*" {
        return Ok(EgressRule {
            host: HostMatch::Any,
            port: PortMatch::Any,
        });
    }

    // Split host from port. IPv6 / bracketed CIDR hosts are wrapped in `[...]`
    // so the port colon is unambiguous; otherwise the port is after the LAST
    // colon (IPv4 / CIDR / domain hosts carry no colons).
    let (host_str, port_str) = if let Some(rest) = body.strip_prefix('[') {
        let close = rest
            .find(']')
            .ok_or_else(|| err("missing `]` closing a bracketed host"))?;
        let inner = &rest[..close];
        // After `]` comes either `:<port>` (a bracketed IPv6 literal) or
        // `/<prefix>:<port>` (a bracketed IPv6 CIDR — the `/prefix` re-joins the
        // host so `parse_host` sees `<addr>/<prefix>`).
        let after = &rest[close + 1..];
        if let Some(cidr) = after.strip_prefix('/') {
            let idx = cidr
                .find(':')
                .ok_or_else(|| err("a bracketed CIDR must be followed by `/<prefix>:<port>`"))?;
            (
                format!("{inner}/{}", &cidr[..idx]),
                cidr[idx + 1..].to_string(),
            )
        } else {
            let port = after
                .strip_prefix(':')
                .ok_or_else(|| err("a bracketed host must be followed by `:<port>`"))?;
            (inner.to_string(), port.to_string())
        }
    } else {
        let idx = body
            .rfind(':')
            .ok_or_else(|| err("expected `<host>:<port>`"))?;
        (body[..idx].to_string(), body[idx + 1..].to_string())
    };

    if host_str.is_empty() {
        return Err(err("empty host"));
    }

    let port = if port_str == "*" {
        PortMatch::Any
    } else {
        PortMatch::Exact(
            port_str
                .parse::<u16>()
                .map_err(|_| err("port is not `*` or a u16"))?,
        )
    };

    let host = parse_host(&host_str).map_err(|reason| err(&reason))?;
    Ok(EgressRule { host, port })
}

fn parse_host(s: &str) -> Result<HostMatch, String> {
    if s == "*" {
        return Ok(HostMatch::Any);
    }
    if let Some(base) = s.strip_prefix("*.") {
        if base.is_empty() {
            return Err("empty wildcard domain base".to_string());
        }
        return Ok(HostMatch::DomainSuffix(base.to_string()));
    }
    // CIDR `addr/prefix`.
    if let Some((addr, prefix)) = s.split_once('/') {
        let ip: IpAddr = addr
            .parse()
            .map_err(|_| format!("CIDR network `{addr}` is not an IP literal"))?;
        let bits: u8 = prefix
            .parse()
            .map_err(|_| format!("CIDR prefix `{prefix}` is not a u8"))?;
        let max = if ip.is_ipv4() { 32 } else { 128 };
        if bits > max {
            return Err(format!(
                "CIDR prefix /{bits} exceeds /{max} for this family"
            ));
        }
        return Ok(HostMatch::Cidr(ip, bits));
    }
    // Bare IP literal, else a domain.
    if let Ok(ip) = s.parse::<IpAddr>() {
        return Ok(HostMatch::Ip(ip));
    }
    Ok(HostMatch::Domain(s.to_string()))
}

/// `true` iff `ip` lies within the CIDR block `net/prefix`. Std-only bit
/// compare over the address octets (no external `ipnet` dep).
fn cidr_contains(net: IpAddr, prefix: u8, ip: IpAddr) -> bool {
    match (net, ip) {
        (IpAddr::V4(net), IpAddr::V4(ip)) => {
            if prefix > 32 {
                return false;
            }
            let mask: u32 = if prefix == 0 {
                0
            } else {
                u32::MAX << (32 - prefix)
            };
            (u32::from(net) & mask) == (u32::from(ip) & mask)
        }
        (IpAddr::V6(net), IpAddr::V6(ip)) => {
            if prefix > 128 {
                return false;
            }
            let mask: u128 = if prefix == 0 {
                0
            } else {
                u128::MAX << (128 - prefix)
            };
            (u128::from(net) & mask) == (u128::from(ip) & mask)
        }
        // Cross-family never matches.
        _ => false,
    }
}

// ===========================================================================
// The policy
// ===========================================================================

/// A workload's outbound destination allowlist — **deny-by-default**.
///
/// Built from the lease's cap strings ([`EgressPolicy::from_caps`]); a workload
/// reaches a destination iff some rule admits it ([`EgressPolicy::decide`]). An
/// empty policy ([`EgressPolicy::deny_all`]) refuses everything.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EgressPolicy {
    rules: Vec<EgressRule>,
}

impl EgressPolicy {
    /// The deny-everything policy — no destination is reachable. This is the
    /// default a workload runs under until a cap grants reach.
    pub fn deny_all() -> EgressPolicy {
        EgressPolicy { rules: Vec::new() }
    }

    /// Build a policy from a lease's cap strings. Caps that do not start with
    /// `egress:` are ignored (they address other subsystems — `cap=`,
    /// `secret://`, …). A cap that DOES start with `egress:` but is malformed
    /// is a fail-closed ERROR — a grant that cannot be parsed never silently
    /// becomes "allow nothing" *or* "allow something".
    pub fn from_caps<I, S>(caps: I) -> Result<EgressPolicy, EgressParseError>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut rules = Vec::new();
        for cap in caps {
            let cap = cap.as_ref();
            if let Some(body) = cap.strip_prefix(EGRESS_CAP_PREFIX) {
                rules.push(parse_rule(body, cap)?);
            }
        }
        Ok(EgressPolicy { rules })
    }

    /// The parsed rules backing this policy.
    pub fn rules(&self) -> &[EgressRule] {
        &self.rules
    }

    /// `true` iff this policy grants nothing (the deny-default state).
    pub fn is_deny_all(&self) -> bool {
        self.rules.is_empty()
    }

    /// Decide a destination against the allowlist. The first matching rule
    /// admits; no match refuses (deny-by-default).
    pub fn decide(&self, dest: &EgressDest) -> EgressDecision {
        for rule in &self.rules {
            if rule.matches(dest) {
                return EgressDecision::Allow { rule: rule.clone() };
            }
        }
        EgressDecision::Deny {
            reason: if self.rules.is_empty() {
                "no egress cap granted — deny-by-default".to_string()
            } else {
                format!("destination {dest} matches no granted egress cap")
            },
        }
    }

    /// `true` iff `dest` is admitted.
    pub fn allows(&self, dest: &EgressDest) -> bool {
        matches!(self.decide(dest), EgressDecision::Allow { .. })
    }

    /// The exact predicate the wasmtime `socket_addr_check` closure runs: a
    /// resolved `(ip, port)` is admitted iff an IP / CIDR / `*` host rule covers
    /// it. (Domain rules cannot apply here — the closure has already resolved
    /// the name to an address; domain-scoped grants are enforced at the
    /// name-resolution / live-netns layer.) A no-egress policy admits NOTHING,
    /// which is the deny-by-default proof for the in-process path.
    pub fn allows_addr(&self, ip: IpAddr, port: u16) -> bool {
        let dest = EgressDest::ip(ip, port);
        self.rules.iter().any(|r| r.matches(&dest))
    }
}

/// The outcome of an [`EgressPolicy::decide`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EgressDecision {
    /// Admitted by `rule`.
    Allow { rule: EgressRule },
    /// Refused — `reason` is the audit string.
    Deny { reason: String },
}

impl EgressDecision {
    pub fn is_allow(&self) -> bool {
        matches!(self, EgressDecision::Allow { .. })
    }
}

// ===========================================================================
// Receipts (the audit log)
// ===========================================================================

/// One auditable egress decision — a grant exercised or a destination refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EgressEvent {
    /// The destination the workload tried to reach.
    pub dest: EgressDest,
    /// Whether it was admitted, and (if refused) why.
    pub outcome: EgressOutcome,
    /// Bytes attributed to this event (0 for a bare connection check).
    pub bytes: u64,
    /// The block the decision was made at (the meter's draw block).
    pub at_block: i64,
}

/// The audited result of an egress attempt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EgressOutcome {
    /// The connection was admitted by the policy (and the meter, if present).
    Allowed,
    /// The connection was refused; the string is the audit reason.
    Refused(String),
}

/// An append-only log of egress decisions — the receipted half: every grant
/// exercised and every refusal is recorded, so an operator can see exactly what
/// a workload reached and what it was denied.
#[derive(Clone, Debug, Default)]
pub struct EgressLog {
    events: Vec<EgressEvent>,
}

impl EgressLog {
    pub fn new() -> EgressLog {
        EgressLog::default()
    }

    /// Append a decision to the log.
    pub fn record(&mut self, event: EgressEvent) {
        self.events.push(event);
    }

    /// Every recorded event, in order.
    pub fn events(&self) -> &[EgressEvent] {
        &self.events
    }

    /// The refused events (the security-relevant tail: what a workload TRIED
    /// to reach but could not).
    pub fn refusals(&self) -> impl Iterator<Item = &EgressEvent> {
        self.events
            .iter()
            .filter(|e| matches!(e.outcome, EgressOutcome::Refused(_)))
    }

    /// The admitted events.
    pub fn allowed(&self) -> impl Iterator<Item = &EgressEvent> {
        self.events
            .iter()
            .filter(|e| matches!(e.outcome, EgressOutcome::Allowed))
    }
}

// ===========================================================================
// The guard (policy + meter + log)
// ===========================================================================

/// Why an egress attempt was refused at the [`EgressGuard`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EgressRefusal {
    /// The policy admits no rule for this destination (deny-by-default or
    /// outside the allowlist).
    NotPermitted { dest: String, reason: String },
    /// The destination is permitted, but the egress meter is over budget — the
    /// workload's outbound rate ceiling (anti-mining / anti-DDoS bound) is hit.
    OverBudget { dest: String, headroom: i64 },
    /// The meter refused for a structural reason.
    Meter(String),
}

impl std::fmt::Display for EgressRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EgressRefusal::NotPermitted { dest, reason } => {
                write!(f, "egress to {dest} refused: {reason}")
            }
            EgressRefusal::OverBudget { dest, headroom } => {
                write!(
                    f,
                    "egress to {dest} refused: over budget (headroom {headroom})"
                )
            }
            EgressRefusal::Meter(e) => write!(f, "egress meter refused: {e}"),
        }
    }
}

impl std::error::Error for EgressRefusal {}

/// The enforcement seam a provider / host-broker calls before letting a
/// workload reach the network: it ties the [`EgressPolicy`] (the allowlist), a
/// [`Meter`] (the bandwidth/connection ceiling), and an [`EgressLog`] (the
/// receipted audit trail) into one fail-closed check.
///
/// `connect` is the per-connection gate; `transfer` meters bytes on an
/// already-admitted connection. Both refuse fail-closed: a refused destination
/// or an over-budget draw returns `Err` and is logged, never a partial reach.
pub struct EgressGuard<'a> {
    policy: EgressPolicy,
    meter: Option<&'a dyn Meter>,
    /// The meter subject (e.g. `egress:lease-7`); the budget must be opened on
    /// the meter by the caller.
    subject: String,
    log: EgressLog,
    /// Monotonic draw ordinal → the exactly-once `(subject, period)` half.
    period: i64,
}

impl<'a> EgressGuard<'a> {
    /// A guard over `policy` with no metering (policy + log only).
    pub fn new(policy: EgressPolicy) -> EgressGuard<'a> {
        EgressGuard {
            policy,
            meter: None,
            subject: String::new(),
            log: EgressLog::new(),
            period: 0,
        }
    }

    /// A guard that also meters egress against `subject`'s budget on `meter`
    /// (which the caller must have [`open`](Meter::open)ed). Each admitted
    /// connection draws a connection unit; [`transfer`](Self::transfer) draws
    /// bytes — so a workload's outbound rate is bounded like bandwidth.
    pub fn metered(
        policy: EgressPolicy,
        meter: &'a dyn Meter,
        subject: impl Into<String>,
    ) -> EgressGuard<'a> {
        EgressGuard {
            policy,
            meter: Some(meter),
            subject: subject.into(),
            log: EgressLog::new(),
            period: 0,
        }
    }

    /// The policy this guard enforces.
    pub fn policy(&self) -> &EgressPolicy {
        &self.policy
    }

    /// The audit log accumulated so far.
    pub fn log(&self) -> &EgressLog {
        &self.log
    }

    /// Gate one outbound connection to `dest` at meter block `at_block`.
    ///
    /// Fail-closed order: (1) the policy must admit `dest` (else refuse +
    /// log); (2) if metered, draw one connection unit against the headroom
    /// (over-budget refuses + logs). Only then is the connection admitted and
    /// logged. `cost` is the connection's unit weight (default 1 via
    /// [`connect`](Self::connect)).
    pub fn connect_weighted(
        &mut self,
        dest: &EgressDest,
        cost: i64,
        at_block: i64,
    ) -> Result<(), EgressRefusal> {
        // (1) policy.
        if let EgressDecision::Deny { reason } = self.policy.decide(dest) {
            self.log.record(EgressEvent {
                dest: dest.clone(),
                outcome: EgressOutcome::Refused(reason.clone()),
                bytes: 0,
                at_block,
            });
            return Err(EgressRefusal::NotPermitted {
                dest: dest.to_string(),
                reason,
            });
        }
        // (2) meter (anti-DDoS / anti-mining rate ceiling).
        if let Some(meter) = self.meter {
            let key = MeterKey::new(&self.subject, self.period);
            self.period += 1;
            match meter.draw(&key, cost, at_block) {
                Ok(_) => {}
                Err(MeterError::OverBudget { headroom, .. }) => {
                    self.log.record(EgressEvent {
                        dest: dest.clone(),
                        outcome: EgressOutcome::Refused(format!(
                            "over budget (headroom {headroom})"
                        )),
                        bytes: 0,
                        at_block,
                    });
                    return Err(EgressRefusal::OverBudget {
                        dest: dest.to_string(),
                        headroom,
                    });
                }
                Err(e) => {
                    self.log.record(EgressEvent {
                        dest: dest.clone(),
                        outcome: EgressOutcome::Refused(format!("meter: {e}")),
                        bytes: 0,
                        at_block,
                    });
                    return Err(EgressRefusal::Meter(e.to_string()));
                }
            }
        }
        self.log.record(EgressEvent {
            dest: dest.clone(),
            outcome: EgressOutcome::Allowed,
            bytes: 0,
            at_block,
        });
        Ok(())
    }

    /// Gate one outbound connection (unit cost 1).
    pub fn connect(&mut self, dest: &EgressDest, at_block: i64) -> Result<(), EgressRefusal> {
        self.connect_weighted(dest, 1, at_block)
    }

    /// Meter `bytes` of egress on an already-admitted connection to `dest`. The
    /// destination is re-checked (defense in depth) and the byte count is drawn
    /// from the budget — a high-volume exfil / DDoS stream hits the ceiling.
    pub fn transfer(
        &mut self,
        dest: &EgressDest,
        bytes: u64,
        at_block: i64,
    ) -> Result<(), EgressRefusal> {
        if let EgressDecision::Deny { reason } = self.policy.decide(dest) {
            self.log.record(EgressEvent {
                dest: dest.clone(),
                outcome: EgressOutcome::Refused(reason.clone()),
                bytes,
                at_block,
            });
            return Err(EgressRefusal::NotPermitted {
                dest: dest.to_string(),
                reason,
            });
        }
        if let Some(meter) = self.meter {
            let key = MeterKey::new(&self.subject, self.period);
            self.period += 1;
            let units = bytes.min(i64::MAX as u64) as i64;
            match meter.draw(&key, units, at_block) {
                Ok(_) => {}
                Err(MeterError::OverBudget { headroom, .. }) => {
                    self.log.record(EgressEvent {
                        dest: dest.clone(),
                        outcome: EgressOutcome::Refused(format!(
                            "over budget (headroom {headroom})"
                        )),
                        bytes,
                        at_block,
                    });
                    return Err(EgressRefusal::OverBudget {
                        dest: dest.to_string(),
                        headroom,
                    });
                }
                Err(e) => return Err(EgressRefusal::Meter(e.to_string())),
            }
        }
        self.log.record(EgressEvent {
            dest: dest.clone(),
            outcome: EgressOutcome::Allowed,
            bytes,
            at_block,
        });
        Ok(())
    }
}

// ===========================================================================
// The firecracker / live-netns seam (NAMED, not yet live)
// ===========================================================================

/// The destination allowlist this policy grants, rendered as
/// `host:port` strings — the input a live host-netns enforcer (firecracker tap
/// filter / nftables / a netns route set) consumes to admit ONLY these
/// destinations and drop everything else.
///
/// This is the policy half of the **named host-netns seam**: DreggNet computes
/// the allowlist here; the live `Capability → tap/MMDS/route` translation that
/// installs it in the guest's network namespace is the remaining work of an
/// owned microVM engine (the `Capability → tap-device gating` item). Until
/// that lands, a microVM tier MUST be launched with NO tap device unless this
/// list is non-empty — i.e. the deny-default holds at the VM boundary by
/// withholding the network interface entirely, never by trusting the guest.
pub fn firecracker_netns_seam(policy: &EgressPolicy) -> Vec<String> {
    policy
        .rules
        .iter()
        .map(|r| {
            let host = match &r.host {
                HostMatch::Any => "*".to_string(),
                HostMatch::Ip(ip) => ip.to_string(),
                HostMatch::Cidr(net, prefix) => format!("{net}/{prefix}"),
                HostMatch::Domain(d) => d.clone(),
                HostMatch::DomainSuffix(b) => format!("*.{b}"),
            };
            let port = match r.port {
                PortMatch::Any => "*".to_string(),
                PortMatch::Exact(p) => p.to_string(),
            };
            format!("{host}:{port}")
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::budget::BudgetTerms;
    use crate::meter::ReplenishingMeter;
    use std::net::{Ipv4Addr, Ipv6Addr};

    fn v4(a: u8, b: u8, c: u8, d: u8) -> IpAddr {
        IpAddr::V4(Ipv4Addr::new(a, b, c, d))
    }

    // ── deny-by-default ───────────────────────────────────────────────────

    #[test]
    fn no_egress_cap_denies_every_destination() {
        let policy = EgressPolicy::from_caps(["cap=run", "secret://OPENAI_KEY"]).unwrap();
        assert!(policy.is_deny_all(), "non-egress caps grant no egress");
        assert!(!policy.allows(&EgressDest::host("api.openai.com", 443)));
        assert!(!policy.allows(&EgressDest::ip(v4(1, 1, 1, 1), 53)));
        // the in-process socket_addr_check predicate: nothing is admitted.
        assert!(!policy.allows_addr(v4(8, 8, 8, 8), 443));
        assert!(!policy.allows_addr(IpAddr::V6(Ipv6Addr::LOCALHOST), 443));
    }

    #[test]
    fn deny_all_is_the_default() {
        let policy = EgressPolicy::deny_all();
        assert!(policy.is_deny_all());
        assert!(!policy.allows(&EgressDest::ip(v4(10, 0, 0, 1), 80)));
    }

    // ── cap grants exactly one destination ────────────────────────────────

    #[test]
    fn one_egress_cap_grants_only_that_destination() {
        let policy = EgressPolicy::from_caps(["egress:93.184.216.34:443"]).unwrap();
        // the granted dest is reachable…
        assert!(policy.allows(&EgressDest::ip(v4(93, 184, 216, 34), 443)));
        assert!(policy.allows_addr(v4(93, 184, 216, 34), 443));
        // …a different host is NOT…
        assert!(!policy.allows(&EgressDest::ip(v4(1, 2, 3, 4), 443)));
        assert!(!policy.allows_addr(v4(1, 2, 3, 4), 443));
        // …and a different port on the SAME host is NOT (port is scoped).
        assert!(!policy.allows(&EgressDest::ip(v4(93, 184, 216, 34), 8080)));
        assert!(!policy.allows_addr(v4(93, 184, 216, 34), 8080));
    }

    #[test]
    fn domain_cap_grants_only_that_domain() {
        let policy = EgressPolicy::from_caps(["egress:api.openai.com:443"]).unwrap();
        assert!(policy.allows(&EgressDest::host("api.openai.com", 443)));
        assert!(
            policy.allows(&EgressDest::host("API.OpenAI.com", 443)),
            "case-insensitive"
        );
        assert!(!policy.allows(&EgressDest::host("evil.com", 443)));
        assert!(!policy.allows(&EgressDest::host("api.openai.com", 80)));
        // a domain grant does NOT admit a bare resolved IP at the in-process
        // layer (the resolver/live tier enforces the name binding).
        assert!(!policy.allows_addr(v4(1, 1, 1, 1), 443));
    }

    #[test]
    fn wildcard_subdomain_matches_subdomains_not_apex_or_siblings() {
        let policy = EgressPolicy::from_caps(["egress:*.svc.internal:8080"]).unwrap();
        assert!(policy.allows(&EgressDest::host("a.svc.internal", 8080)));
        assert!(policy.allows(&EgressDest::host("deep.a.svc.internal", 8080)));
        assert!(
            !policy.allows(&EgressDest::host("svc.internal", 8080)),
            "apex needs its own grant"
        );
        assert!(!policy.allows(&EgressDest::host("svc.evil.com", 8080)));
    }

    #[test]
    fn cidr_cap_scopes_to_the_block() {
        let policy = EgressPolicy::from_caps(["egress:10.0.0.0/8:*"]).unwrap();
        assert!(policy.allows_addr(v4(10, 1, 2, 3), 443));
        assert!(policy.allows_addr(v4(10, 255, 255, 255), 22));
        assert!(!policy.allows_addr(v4(11, 0, 0, 1), 443), "outside the /8");
        assert!(!policy.allows_addr(v4(192, 168, 0, 1), 443));
    }

    #[test]
    fn ipv6_cidr_bracketed_host_parses_and_scopes() {
        let policy = EgressPolicy::from_caps(["egress:[2001:db8::]/32:443"]).unwrap();
        let inside = IpAddr::V6("2001:db8:1234::1".parse().unwrap());
        let outside = IpAddr::V6("2001:dead::1".parse().unwrap());
        assert!(policy.allows_addr(inside, 443));
        assert!(!policy.allows_addr(outside, 443));
        assert!(!policy.allows_addr(inside, 80), "port scoped");
    }

    #[test]
    fn star_grants_everything_but_only_when_explicitly_named() {
        let policy = EgressPolicy::from_caps(["egress:*"]).unwrap();
        assert!(policy.allows_addr(v4(8, 8, 8, 8), 443));
        assert!(policy.allows(&EgressDest::host("anything.com", 1234)));
    }

    #[test]
    fn port_wildcard_any_port_one_host() {
        let policy = EgressPolicy::from_caps(["egress:1.1.1.1:*"]).unwrap();
        assert!(policy.allows_addr(v4(1, 1, 1, 1), 53));
        assert!(policy.allows_addr(v4(1, 1, 1, 1), 443));
        assert!(!policy.allows_addr(v4(1, 1, 1, 2), 53));
    }

    // ── attenuation: a child policy is a subset ───────────────────────────

    #[test]
    fn malformed_egress_cap_fails_closed() {
        assert!(EgressPolicy::from_caps(["egress:noport"]).is_err());
        assert!(EgressPolicy::from_caps(["egress:host:notaport"]).is_err());
        assert!(EgressPolicy::from_caps(["egress:10.0.0.0/99:443"]).is_err());
        assert!(EgressPolicy::from_caps(["egress:[bad:443"]).is_err());
        // a well-formed grant alongside a malformed one still fails closed.
        assert!(EgressPolicy::from_caps(["egress:ok.com:443", "egress:bad"]).is_err());
    }

    // ── metering (egress bounded like bandwidth) ──────────────────────────

    fn meter_for(subject: &str, budget: i64) -> ReplenishingMeter {
        let m = ReplenishingMeter::new();
        m.open(subject, BudgetTerms::ceiling("DREGG", budget, 1_000_000, 0))
            .unwrap();
        m
    }

    #[test]
    fn egress_is_metered_and_refuses_when_over_budget() {
        let policy = EgressPolicy::from_caps(["egress:*"]).unwrap();
        let meter = meter_for("egress:lease-1", 3);
        let mut guard = EgressGuard::metered(policy, &meter, "egress:lease-1");
        let dest = EgressDest::ip(v4(1, 1, 1, 1), 443);
        // three admitted connections draw the whole budget…
        assert!(guard.connect(&dest, 0).is_ok());
        assert!(guard.connect(&dest, 0).is_ok());
        assert!(guard.connect(&dest, 0).is_ok());
        // …the fourth is refused over-budget (the anti-DDoS / anti-mining ceiling).
        match guard.connect(&dest, 0) {
            Err(EgressRefusal::OverBudget { .. }) => {}
            other => panic!("expected over-budget, got {other:?}"),
        }
        assert_eq!(meter.drawn_total("egress:lease-1"), 3);
    }

    #[test]
    fn transfer_meters_bytes_like_bandwidth() {
        let policy = EgressPolicy::from_caps(["egress:*"]).unwrap();
        let meter = meter_for("egress:lease-2", 1000);
        let mut guard = EgressGuard::metered(policy, &meter, "egress:lease-2");
        let dest = EgressDest::ip(v4(1, 1, 1, 1), 443);
        assert!(guard.transfer(&dest, 600, 0).is_ok());
        assert!(guard.transfer(&dest, 400, 0).is_ok());
        // the next byte is over the ceiling.
        match guard.transfer(&dest, 1, 0) {
            Err(EgressRefusal::OverBudget { .. }) => {}
            other => panic!("expected over-budget, got {other:?}"),
        }
    }

    // ── the refusal is logged (the audit trail) ───────────────────────────

    #[test]
    fn an_outside_destination_is_refused_and_logged() {
        let policy = EgressPolicy::from_caps(["egress:allowed.com:443"]).unwrap();
        let mut guard = EgressGuard::new(policy);
        let allowed = EgressDest::host("allowed.com", 443);
        let blocked = EgressDest::host("evil.com", 443);
        assert!(guard.connect(&allowed, 0).is_ok());
        assert!(guard.connect(&blocked, 0).is_err());
        // the log shows exactly one allow and one refusal naming the blocked dest.
        assert_eq!(guard.log().allowed().count(), 1);
        let refusals: Vec<_> = guard.log().refusals().collect();
        assert_eq!(refusals.len(), 1);
        assert_eq!(refusals[0].dest, blocked);
    }

    #[test]
    fn deny_default_guard_logs_the_refusal_with_a_reason() {
        let mut guard = EgressGuard::new(EgressPolicy::deny_all());
        let dest = EgressDest::host("anywhere.com", 443);
        match guard.connect(&dest, 0) {
            Err(EgressRefusal::NotPermitted { reason, .. }) => {
                assert!(reason.contains("deny-by-default"));
            }
            other => panic!("expected NotPermitted, got {other:?}"),
        }
        assert_eq!(guard.log().refusals().count(), 1);
    }

    // ── the firecracker host-netns seam (named) ───────────────────────────

    #[test]
    fn firecracker_seam_renders_the_allowlist_for_the_host_enforcer() {
        let policy =
            EgressPolicy::from_caps(["egress:10.0.0.0/8:443", "egress:api.x.com:*"]).unwrap();
        let list = firecracker_netns_seam(&policy);
        assert_eq!(
            list,
            vec!["10.0.0.0/8:443".to_string(), "api.x.com:*".to_string()]
        );
        // deny-all → an EMPTY allowlist → the host launches the VM with no tap.
        assert!(firecracker_netns_seam(&EgressPolicy::deny_all()).is_empty());
    }
}
