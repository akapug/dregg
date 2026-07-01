//! The named wire to a REAL dregg lease — where `dreggnet-bridge` meets polyana's
//! own `polyana-dregg-bridge` (the dregg verified-core surface).
//!
//! At this rung the [`crate::Lease`] is a MOCK struct. This module names — in
//! compile-checked detail — exactly how the real funded-lease wire lands, and
//! where it meets the surface polyana already carries.
//!
//! # Where it meets polyana
//!
//! polyana carries `polyana-dregg-bridge` (`polyana/src/dregg-bridge`), a
//! feature-isolated adapter that re-exports the pinned `emberian/dregg`
//! `polyana-bridge` crate (rev `a0a0a019692870d9ec992744042de2df8c19be0c`) behind
//! its **`dregg-verify`** feature. That crate exposes the dregg verified-core
//! surface DreggNet wants for a REAL lease:
//!
//! - **Cap-gate** — `gate_effect_set(held, requested)`/`gate_auth(..)`: the dregg
//!   attenuation check. A lease's authorized [`crate::CapGrade`] is a `CapBundle`;
//!   verifying that the workload's requested effects are an attenuation of what the
//!   lease grants is `gate_effect_set` returning `Ok` (else `GateRefusal`). THIS is
//!   the real form of [`crate::workflow_input_for_lease`]'s `GradeBelowFloor` check.
//! - **Receipt witness** — `witness_receipt(..)` / `turn_shadow_receipt(..)`: turns
//!   a metered step into a chained dregg receipt. The bridge's `MeterTick` (today an
//!   in-process ledger) becomes a real dregg `Payable` charge whose receipt is
//!   witnessed here — a light client then sees each metered step, not just a
//!   re-executing validator.
//! - **Verified query** — `query_shadow_attest_whole_log(records, query)` /
//!   `attest_whole_log` + `answer_whole_log`: answer a query over the receipt log
//!   with a verifiable attestation. This is the doorway to READING a lease's
//!   committed state from a dregg light client: the lease cell's budget, cap-grade,
//!   and meter cursor are committed fields a `dregg-query` answer attests to.
//!
//! # The wire (now real behind `dregg-verify`)
//!
//! [`read_funded_leases`] is the live read: given a dregg node's receipt-log
//! records, it builds the funded-lease query, attests it over the whole log
//! (`query_shadow_attest_whole_log` — fails closed if the log does not verify
//! against its MMR root), and decodes each attested funded execution-lease grant
//! into a [`crate::Lease`]. [`crate::watch::DreggNodeFeed::from_node_log`] drives
//! this and yields the decoded leases to the watch→fulfill→reap loop.
//!
//! The three moves the wire makes:
//!
//! 1. **The dep is taken** (off by default). `bridge/Cargo.toml`:
//!    ```toml
//!    [dependencies]
//!    polyana-dregg-bridge = { path = "../polyana/src/dregg-bridge", optional = true }
//!    [features]
//!    dregg-verify = ["dep:polyana-dregg-bridge", "polyana-dregg-bridge/dregg-verify"]
//!    ```
//! 2. **The lease is read.** [`read_funded_leases`] attests the whole receipt log
//!    and decodes the funded execution-lease grants (lessee + cap-grade + the
//!    budget/rent the granted cap's caveats bound) into a [`crate::Lease`]. This
//!    is the dregg model directly: a capability's CAVEATS bound the budget, so the
//!    granted lease cap carries its sealed terms (`exec-lease/<grade>/<asset>/
//!    <budget>/<rent>`) — the same terms breadstuffs' `execution-lease` factory
//!    seals into the lease cell (`RENT_SLOT`/`PERIOD_SLOT`/cap-grade).
//! 3. **Charge for real** (the next sub-step, named not yet wired). Replace the
//!    durable layer's in-process `MeterTick` ledger with a dregg `Payable` charge
//!    (one conserving `Effect::Transfer`, lease → provider) witnessed by
//!    `witness_receipt`. `dreggnet-durable`'s `ACTIVITY_METER_TICK` is the single
//!    place that charge lands.
//!
//! ## What is real vs compile-checked-pending-a-live-node
//!
//! - **Real + exercised feature-on:** the verified whole-log attestation and the
//!   funded-lease decode ([`read_funded_leases`]) — a tampered/empty/unverifiable
//!   log fails closed; a funded execution-lease grant decodes into a usable,
//!   budget-bearing [`crate::Lease`].
//! - **Pending a live node:** the *transport* that fetches the receipt-log
//!   records from a real dregg node / light client over `node_endpoint`
//!   ([`crate::watch::DreggNodeFeed`]). Today the records are handed in
//!   (`from_node_log`); the live light-client RPC that produces them is the
//!   remaining step. The richer alternative — reading budget/rent straight from
//!   the lease cell's committed heap (`dregg_cell`'s heap-root surface) rather
//!   than the granted cap's caveats — needs a cell-state read not re-exported by
//!   `polyana-bridge` today; the caveat-bound terms above are the surface that IS.
//!
//! # LICENSE — load-bearing, do not break the isolation
//!
//! `emberian/dregg` is **AGPL-3.0-or-later**. polyana ships Apache-2.0 and keeps
//! the dregg lane behind its default-OFF `dregg-verify` feature; DreggNet keeps the
//! default `dreggnet-bridge` build off that lane too, so `cargo test -p
//! dreggnet-bridge` resolves and builds with **zero dregg git in the lock**. A
//! build produced with `dregg-verify` ENABLED is a combined/derivative work of AGPL
//! code (DreggNet is itself AGPL-3.0, so such a build is an AGPL combined work — the
//! licenses are compatible, but the AGPL obligation still attaches — never ship a binary built
//! with this feature under a non-AGPL license). This is why the wire above is the
//! deliberate flip-on step, not a default dependency.

/// Whether this build links the real dregg verified-core surface (polyana's
/// `polyana-dregg-bridge`). `false` on the default, Apache/offline-pure build.
///
/// Mirrors `polyana_dregg_bridge::DREGG_VERIFY_ENABLED`. When the wire named in
/// this module's docs is taken, this gates the real-lease read path.
pub const DREGG_VERIFY_ENABLED: bool = cfg!(feature = "dregg-verify");

/// The pinned `emberian/dregg` rev `polyana-dregg-bridge` re-exports — the exact
/// dregg verified-core the real-lease wire binds against. Recorded here so the
/// version the bridge would meet is explicit even on the default build.
pub const DREGG_BRIDGE_REV: &str = "a0a0a019692870d9ec992744042de2df8c19be0c";

/// The `polyana-dregg-bridge` surface functions the real-lease wire lands on.
/// (Documentation constant — the actual symbols become available once the
/// `dregg-verify` dep named in this module's docs is taken.)
pub const DREGG_BRIDGE_SURFACE: &[&str] = &[
    "gate_effect_set",  // cap-grade attenuation check (the real GradeBelowFloor gate)
    "gate_auth",        // auth-kind attenuation
    "witness_receipt",  // witness a metered step as a chained dregg receipt
    "attest_whole_log", // build a verifiable attestation over the receipt log
    "answer_whole_log", // answer a query over the attested log
    "query_shadow_attest_whole_log", // read+attest committed lease state (the lease read)
];

/// The cap-token prefix a funded execution-lease grant carries. The granted
/// capability's caveats bound the lease's sealed terms; we encode them as
/// `exec-lease/<grade>/<asset>/<budget>/<rent>` (mirroring breadstuffs'
/// `execution-lease` cell: cap-grade + asset + budget + `RENT_SLOT`). A grant
/// without this prefix is not an execution-lease and is skipped.
#[cfg(feature = "dregg-verify")]
const EXEC_LEASE_CAP_PREFIX: &str = "exec-lease/";

/// Read funded execution-leases from a dregg node's receipt log.
///
/// Builds the funded-lease query, attests it over the whole log with
/// [`query_shadow_attest_whole_log`](polyana_dregg_bridge::query_shadow_attest_whole_log)
/// — which **fails closed** (`Err`) if `records` is empty or the answer does not
/// verify against the log's MMR root — then decodes each attested funded
/// execution-lease grant into a [`FeedItem`](crate::watch::FeedItem) the watcher
/// can fulfill. Grants that are not execution-leases, or whose decoded terms are
/// inactive (unfunded / non-positive rent / negative budget), are filtered out.
///
/// The returned items are ordered by the log's receipt order, each keyed by a
/// stable durable instance id derived from the grant's `(chain_index, height)`.
#[cfg(feature = "dregg-verify")]
pub fn read_funded_leases(
    records: &[polyana_dregg_bridge::QueryShadowRecord],
) -> Result<Vec<crate::watch::FeedItem>, polyana_dregg_bridge::QueryShadowError> {
    use polyana_dregg_bridge::{
        Pred, Query, QueryShadowEffect, Term, query_shadow_attest_whole_log,
    };

    // The verified read: attest a whole-log query over the granted caps. This is
    // the security gate — a log that does not verify against its root returns
    // `Err` here and yields no leases (fail-closed), as does an empty log.
    let query = Query::new().atom(
        Pred::Granted,
        vec![
            Term::var("From"),
            Term::var("To"),
            Term::var("Cap"),
            Term::var("Height"),
        ],
    );
    let attestation = query_shadow_attest_whole_log(records, query)?;

    // The log verified against its root; decode the funded execution-lease grants
    // it attests into fulfillable feed items.
    let mut items = Vec::new();
    for record in records {
        for effect in &record.effects {
            if let QueryShadowEffect::Granted { from, to, cap } = effect {
                if let Some(lease) = lease_from_grant(from, to, cap) {
                    let instance = format!("lease-{}-{}", record.chain_index, record.height);
                    items.push(crate::watch::FeedItem::new(instance, lease));
                }
            }
        }
    }
    // The attestation's verified row set is the universe the grants are drawn
    // from; every decoded lease came from an attested `Granted` row.
    debug_assert!(items.len() <= attestation.row_count);
    Ok(items)
}

/// Read funded execution-leases from a dregg node's **certified receipt-index
/// slice** with a full **light-client verification** against the node's published
/// receipt-chain MMR root — the real, transport-complete verified read.
///
/// `range_json` is the body of `GET /api/receipts/index/range?lo=0&hi=head` (a
/// [`dregg_query::client::IndexRangeResponse`]: the receipt rows + the
/// `RangeOpening` non-omission certificate). `index_root_hex` is the body's
/// `root` field of `GET /api/receipts/index/root` — the node's committed
/// receipt-chain MMR root, fetched independently.
///
/// The verification (all fail-closed — any failure yields `Err` and NO leases):
/// 1. the range response's self-reported root MUST equal the independently
///    fetched `index_root_hex` (the range is bound to the published root);
/// 2. the slice's non-omission certificate verifies against that root — the rows
///    are EXACTLY positions `[0, head]` of the genuine log, length pinned by the
///    root (`server_cannot_omit_position`);
/// 3. the answer's coverage is the whole-log prefix and its rows recompute from
///    the certified input ([`AttestedAnswer::verify`](dregg_query::AttestedAnswer)).
///
/// Only after that verification are the verified receipts' `Granted` effects
/// decoded into funded, active [`crate::Lease`]s. A node that serves a forged /
/// truncated / root-mismatched slice is rejected.
///
/// The trusted root is fetched from the same node today; binding it to a
/// finalized checkpoint (the `CommitBindsMMR` weld) is the named trust-root
/// hardening — the verification machinery here is already the genuine one.
#[cfg(feature = "dregg-verify")]
pub fn verified_leases_from_range(
    range_json: &str,
    index_root_hex: &str,
) -> Result<Vec<crate::watch::FeedItem>, String> {
    use dregg_query::client::IndexRangeResponse;
    use dregg_query::{EffectSummary, answer_whole_log};
    use polyana_dregg_bridge::{Blake3Mmr, Pred, Query, Term};

    let resp: IndexRangeResponse =
        serde_json::from_str(range_json).map_err(|e| format!("decode index range: {e}"))?;

    // (1) bind the range to the independently-fetched published root.
    if !resp.root.eq_ignore_ascii_case(index_root_hex.trim()) {
        return Err(format!(
            "range root {} != published index root {index_root_hex}",
            resp.root
        ));
    }
    let root_bytes = decode_hex32(index_root_hex.trim())
        .ok_or_else(|| format!("malformed index root hex: {index_root_hex}"))?;

    let slice = resp
        .into_slice()
        .map_err(|e| format!("assemble attested slice: {e}"))?;
    // Keep the certified receipts for decoding after the slice is consumed by the
    // verifier (the decode reads ONLY verified rows).
    let receipts = slice.receipts.clone();

    // (2)+(3) build the whole-log answer and verify it against the trusted root.
    let query = Query::new().atom(
        Pred::Granted,
        vec![
            Term::var("From"),
            Term::var("To"),
            Term::var("Cap"),
            Term::var("Height"),
        ],
    );
    let answer = answer_whole_log(slice, query).map_err(|e| format!("answer whole log: {e}"))?;
    answer
        .verify(&Blake3Mmr, &root_bytes)
        .map_err(|e| format!("light-client verify failed (fail-closed): {e}"))?;

    // Verified: decode every funded execution-lease grant the certified rows attest.
    let mut items = Vec::new();
    for record in &receipts {
        for effect in &record.effects {
            if let EffectSummary::Granted { from, to, cap } = effect {
                if let Some(lease) = lease_from_grant(from, to, cap) {
                    let instance = format!("lease-{}-{}", record.chain_index, record.height);
                    items.push(crate::watch::FeedItem::new(instance, lease));
                }
            }
        }
    }
    Ok(items)
}

/// Read funded execution-leases from a dregg node's **whole receipt log,
/// windowed** — the long-chain verified read that paginates the single-range
/// span cap (the node caps one `/api/receipts/index/range` at 1024 rows).
///
/// `windows` is the ordered list of `/api/receipts/index/range?lo=&hi=` bodies
/// that TILE the log: window 0 starts at position 0, each next window starts where
/// the previous ended (+1), and the last reaches the root-pinned head.
/// `index_root_hex` is the single trusted receipt-chain MMR root every window's
/// non-omission certificate opens against (the same whole-log root — each window's
/// `RangeOpening` verifies against it independently).
///
/// The verification (all fail-closed — any failure yields `Err` and NO leases):
/// 1. every window's self-reported root MUST equal the trusted `index_root_hex`;
/// 2. the windows are **contiguous and gap-free** — window 0 at position 0, each
///    next at `prev.hi + 1`, the last at `len - 1` of the root-pinned length — so
///    a server cannot drop a window (a gap or a missing tail is rejected);
/// 3. each window's non-omission certificate verifies against the trusted root and
///    its rows recompute from the certified input ([`dregg_query::AttestedAnswer`],
///    [`Coverage::Range`](dregg_query::Coverage) per window).
///
/// The union of all windows' verified rows is provably the whole genuine log with
/// nothing omitted (each window is exactly its dense slice and the windows tile
/// `[0, len-1]`). Only then are the verified `Granted` effects decoded into funded
/// execution-leases. A single window response decodes identically to
/// [`verified_leases_from_range`]; this is its multi-window generalization.
#[cfg(feature = "dregg-verify")]
pub fn verified_leases_windowed(
    windows: &[String],
    index_root_hex: &str,
) -> Result<Vec<crate::watch::FeedItem>, String> {
    use dregg_query::client::IndexRangeResponse;
    use dregg_query::{EffectSummary, answer};
    use polyana_dregg_bridge::{Blake3Mmr, Pred, Query, Term};

    if windows.is_empty() {
        return Err("windowed verified read: no windows supplied".to_string());
    }
    let trusted = index_root_hex.trim();
    let root_bytes =
        decode_hex32(trusted).ok_or_else(|| format!("malformed index root hex: {trusted}"))?;

    let build_query = || {
        Query::new().atom(
            Pred::Granted,
            vec![
                Term::var("From"),
                Term::var("To"),
                Term::var("Cap"),
                Term::var("Height"),
            ],
        )
    };

    let mut items = Vec::new();
    let mut expected_lo: u64 = 0;
    let mut root_pinned_len: u64 = 0;
    for (w, window_json) in windows.iter().enumerate() {
        let resp: IndexRangeResponse = serde_json::from_str(window_json)
            .map_err(|e| format!("window {w}: decode index range: {e}"))?;
        // (1) bind every window to the SAME trusted whole-log root.
        if !resp.root.eq_ignore_ascii_case(trusted) {
            return Err(format!(
                "window {w}: range root {} != trusted index root {trusted}",
                resp.root
            ));
        }
        let slice = resp
            .into_slice()
            .map_err(|e| format!("window {w}: assemble attested slice: {e}"))?;
        let receipts = slice.receipts.clone();
        // (2) contiguous, gap-free tiling against the previous window.
        if slice.cert.lo != expected_lo {
            return Err(format!(
                "window {w}: starts at position {} but expected {expected_lo} (a window was skipped)",
                slice.cert.lo
            ));
        }
        // (3) non-omission of THIS window against the trusted root (+ the dense
        // positions + the root-pinned length), then the row recompute over the
        // certified window (Coverage::Range — completeness is per-window; the
        // whole-log claim is discharged by the tiling check below).
        let len = slice
            .verify(&Blake3Mmr, &root_bytes)
            .map_err(|e| format!("window {w}: light-client verify failed (fail-closed): {e}"))?;
        let hi = slice.cert.hi;
        let answer =
            answer(slice, build_query()).map_err(|e| format!("window {w}: answer range: {e}"))?;
        answer
            .verify(&Blake3Mmr, &root_bytes)
            .map_err(|e| format!("window {w}: answer verify failed (fail-closed): {e}"))?;
        expected_lo = hi + 1;
        root_pinned_len = len;

        for record in &receipts {
            for effect in &record.effects {
                if let EffectSummary::Granted { from, to, cap } = effect {
                    if let Some(lease) = lease_from_grant(from, to, cap) {
                        let instance = format!("lease-{}-{}", record.chain_index, record.height);
                        items.push(crate::watch::FeedItem::new(instance, lease));
                    }
                }
            }
        }
    }
    // The tiling must reach the root-pinned head — otherwise the tail was omitted.
    if expected_lo != root_pinned_len {
        return Err(format!(
            "windowed read covers [0, {expected_lo}) but the root pins length {root_pinned_len} (the tail was omitted)"
        ));
    }
    Ok(items)
}

/// Decode a 64-char hex string into a 32-byte array (`None` if malformed).
#[cfg(feature = "dregg-verify")]
fn decode_hex32(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(hex.get(i * 2..i * 2 + 2)?, 16).ok()?;
    }
    Some(out)
}

/// Decode one attested `Granted` grant into an active funded [`crate::Lease`], or
/// `None` if it is not an execution-lease grant or its terms are inactive.
///
/// `lessee` (the grant's `to`) becomes the lease holder; `provider` (the `from`)
/// is the meter beneficiary, carried in dregg rather than the bridge's mock
/// [`crate::Lease`]. The cap token's caveats carry the sealed terms.
#[cfg(feature = "dregg-verify")]
fn lease_from_grant(provider: &str, lessee: &str, cap: &str) -> Option<crate::Lease> {
    let _provider = provider; // the meter beneficiary (dregg-side, not in the mock Lease)
    let terms = cap.strip_prefix(EXEC_LEASE_CAP_PREFIX)?;
    let mut parts = terms.split('/');
    let grade = parse_cap_grade(parts.next()?)?;
    let asset = parts.next()?;
    let budget_units: i64 = parts.next()?.parse().ok()?;
    let per_period_units: i64 = parts.next()?.parse().ok()?;
    // Reject trailing junk: a well-formed lease cap has exactly four fields.
    if parts.next().is_some() {
        return None;
    }
    let lease = crate::Lease::funded(lessee, grade, asset, budget_units, per_period_units);
    // Filter for funded + ACTIVE: positive per-period cost, non-negative budget.
    lease.is_active().then_some(lease)
}

/// Parse a cap-grade token (matching [`crate::CapGrade`]'s `Display`).
#[cfg(feature = "dregg-verify")]
fn parse_cap_grade(s: &str) -> Option<crate::CapGrade> {
    match s {
        "sandboxed" => Some(crate::CapGrade::Sandboxed),
        "caged" => Some(crate::CapGrade::Caged),
        "microvm" => Some(crate::CapGrade::MicroVm),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verify_flag_matches_cfg() {
        assert_eq!(DREGG_VERIFY_ENABLED, cfg!(feature = "dregg-verify"));
    }

    #[test]
    fn the_named_wire_surface_is_recorded() {
        // The real-lease read lands on a verified-query answer; the cap gate is a
        // real attenuation check. Both are named so the wire is mechanical.
        assert!(DREGG_BRIDGE_SURFACE.contains(&"query_shadow_attest_whole_log"));
        assert!(DREGG_BRIDGE_SURFACE.contains(&"gate_effect_set"));
        assert_eq!(DREGG_BRIDGE_REV.len(), 40);
    }

    /// Feature-on: a verified whole-log read decodes a funded execution-lease
    /// grant into a usable, budget-bearing `Lease`, and skips non-lease grants.
    #[cfg(feature = "dregg-verify")]
    #[test]
    fn read_funded_leases_decodes_a_real_grant() {
        use polyana_dregg_bridge::{QueryShadowEffect, QueryShadowRecord};

        let records = vec![
            QueryShadowRecord {
                chain_index: 0,
                receipt_hash: [0x11; 32],
                height: 7,
                agent: "provider:slot-factory".into(),
                effects: vec![QueryShadowEffect::Granted {
                    from: "provider:slot-factory".into(),
                    to: "agent:lessee-1".into(),
                    cap: "exec-lease/caged/USD/500/5".into(),
                }],
            },
            // A non-lease grant in the same log is filtered out.
            QueryShadowRecord {
                chain_index: 1,
                receipt_hash: [0x22; 32],
                height: 8,
                agent: "agent:lessee-1".into(),
                effects: vec![QueryShadowEffect::Granted {
                    from: "x".into(),
                    to: "y".into(),
                    cap: "tool-call".into(),
                }],
            },
        ];

        let items = super::read_funded_leases(&records).expect("verified whole-log read");
        assert_eq!(items.len(), 1, "only the exec-lease grant decodes");
        let item = &items[0];
        assert_eq!(item.instance, "lease-0-7");
        assert_eq!(item.lease.lessee, "agent:lessee-1");
        assert_eq!(item.lease.cap_grade, crate::CapGrade::Caged);
        assert_eq!(item.lease.asset, "USD");
        assert_eq!(item.lease.budget_units, 500);
        assert_eq!(item.lease.per_period_units, 5);
        assert!(item.lease.is_active());
    }

    /// Feature-on: an empty log fails closed (no node, no leases) — the verified
    /// read returns `Err`, never a silent empty success.
    #[cfg(feature = "dregg-verify")]
    #[test]
    fn read_funded_leases_empty_log_fails_closed() {
        assert!(super::read_funded_leases(&[]).is_err());
    }
}
