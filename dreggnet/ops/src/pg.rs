//! The durable layer's live state, read from the `dreggnet_meter` transactional
//! outbox in Postgres.
//!
//! `dreggnet-durable` records every metered workflow step as an idempotent charge
//! row `(lease_id, period, amount, running_total, charged_at)` keyed by
//! `(lease_id, period)`, where **`lease_id` is the durable workflow instance id**
//! (see `dreggnet_durable::pg`). So the outbox is a faithful live ledger of the
//! durable jobs and the lease economy:
//!
//! - **a durable job** = one `lease_id`; its `MAX(period)` is its step count, its
//!   `MAX(running_total)` is the units charged so far, its `MAX(charged_at)` is its
//!   last activity. A job with a charge in the recent window is "active"; otherwise
//!   it is "idle" (last seen at that time).
//! - **the lease economy (spent)** = `SUM(amount)` across the outbox.
//!
//! Honest scope: the outbox is the *spent* side of the lease economy. The *minted*
//! / *conserved* sides live in the dregg lease-cell ledger on the node (a dregg
//! `Payable`'s funded budget), which is per-cell rather than a single endpoint;
//! the dashboard reports spent as real and labels minted/conserved accordingly.

use std::time::Duration;

use serde::Serialize;

/// One durable job (one lease / workflow instance), as projected from the outbox.
#[derive(Debug, Clone, Serialize)]
pub struct DurableJob {
    /// The lease id = the durable workflow instance id.
    pub lease_id: String,
    /// Steps metered so far (`MAX(period)`).
    pub periods: i64,
    /// Units charged against the lease so far (`MAX(running_total)`).
    pub units_charged: i64,
    /// Last charge timestamp (RFC3339), if any.
    pub last_charge_at: Option<String>,
    /// "active" (charged within the recent window) or "idle".
    pub status: String,
}

/// One raw meter charge row from the outbox — a single `(lease_id, period)` debit.
/// This is the per-event economy ledger (one row per metered step), the granular
/// companion to the per-lease [`DurableJob`] rollup.
#[derive(Debug, Clone, Serialize)]
pub struct MeterCharge {
    /// The lease id (a compute workflow instance, or a `host:<resource>:<key>`
    /// hosting lease — see [`classify_resource`]).
    pub lease_id: String,
    /// The step ordinal within the lease (1-based).
    pub period: i64,
    /// Units debited for THIS step (the flow), `payer → beneficiary`, Σδ=0.
    pub amount: i64,
    /// The running total for the lease after this step.
    pub running_total: i64,
    /// When the charge landed (RFC3339), if recorded.
    pub charged_at: Option<String>,
    /// The metered resource this charge bills: a hosting resource
    /// (`bandwidth`/`uptime`/`publish`/`cert`/`build`) or `compute`.
    pub resource: String,
}

/// A per-resource spend rollup across the whole outbox (the hosting-vs-compute
/// split of the lease economy).
#[derive(Debug, Clone, Serialize)]
pub struct ResourceTotal {
    /// `bandwidth`/`uptime`/`publish`/`cert`/`build`/`compute`.
    pub resource: String,
    /// How many charge rows fall in this class.
    pub charges: i64,
    /// Total units billed in this class.
    pub units: i64,
}

/// Classify a `lease_id` into the metered resource it bills. Hosting leases are
/// keyed `host:<resource>:<key>` (see `dreggnet_control::hosting_meter`); anything
/// else is a compute workflow lease.
pub fn classify_resource(lease_id: &str) -> &'static str {
    match lease_id.strip_prefix("host:") {
        Some(rest) => match rest.split(':').next().unwrap_or("") {
            "bandwidth" => "bandwidth",
            "uptime" => "uptime",
            "publish" => "publish",
            "cert" => "cert",
            "build" => "build",
            _ => "hosting",
        },
        None => "compute",
    }
}

/// The durable layer's aggregated view.
#[derive(Debug, Clone, Serialize, Default)]
pub struct DurableView {
    /// Whether a `DATABASE_URL` was configured at all.
    pub configured: bool,
    /// Whether the Postgres connection succeeded.
    pub reachable: bool,
    /// A non-fatal note (e.g. connected but the outbox table does not exist yet).
    pub error: Option<String>,
    /// Recent durable jobs, newest activity first.
    pub jobs: Vec<DurableJob>,
    /// Recent raw meter charges (one per metered step), newest first — the
    /// per-event economy ledger that feeds the history viewer's economy rows.
    pub charges: Vec<MeterCharge>,
    /// The per-resource spend rollup across all history (hosting vs compute).
    pub resource_totals: Vec<ResourceTotal>,
    /// Distinct leases ever metered.
    pub total_leases: i64,
    /// Total units charged across the whole outbox (the spent side of the economy).
    pub total_units_spent: i64,
    /// Jobs with a charge within the recent "in-flight" window.
    pub jobs_in_flight: i64,
    /// Backend connection slots currently in use (`pg_stat_activity`). A
    /// postgres-pressure signal when it nears [`DurableView::max_connections`].
    pub active_connections: Option<i64>,
    /// The server's `max_connections` setting (the ceiling for the above).
    pub max_connections: Option<i64>,
    /// The database's on-disk size in bytes (`pg_database_size`), for disk pressure.
    pub db_size_bytes: Option<i64>,
}

/// Read the durable view from `database_url`. Connects with a short timeout; a
/// connect failure → `reachable=false`; a missing outbox table → `reachable=true`
/// with a friendly `error` and no jobs. Never panics.
pub async fn fetch_durable(database_url: &str, timeout: Duration) -> DurableView {
    use sqlx::postgres::PgPoolOptions;

    let mut view = DurableView {
        configured: true,
        ..Default::default()
    };

    let pool = match PgPoolOptions::new()
        .max_connections(2)
        .acquire_timeout(timeout)
        .connect(database_url)
        .await
    {
        Ok(p) => p,
        Err(e) => {
            view.error = Some(format!("postgres connect: {e}"));
            return view;
        }
    };
    view.reachable = true;

    // Postgres-pressure signals — cheap server-wide reads that work even before the
    // meter outbox table exists (so they are read up front, independent of it).
    if let Ok((active, max)) = sqlx::query_as::<_, (i64, i64)>(
        "SELECT (SELECT count(*) FROM pg_stat_activity), \
                (SELECT setting::bigint FROM pg_settings WHERE name = 'max_connections')",
    )
    .fetch_one(&pool)
    .await
    {
        view.active_connections = Some(active);
        view.max_connections = Some(max);
    }
    if let Ok((size,)) =
        sqlx::query_as::<_, (i64,)>("SELECT pg_database_size(current_database())::bigint")
            .fetch_one(&pool)
            .await
    {
        view.db_size_bytes = Some(size);
    }

    // The recent-activity window that marks a job "in flight".
    const IN_FLIGHT_SECS: i64 = 300;

    // Per-lease projection. If the table is absent, this errors — caught below.
    let rows = sqlx::query_as::<_, (String, i64, i64, Option<time::OffsetDateTime>)>(
        "SELECT lease_id, \
                MAX(period)        AS periods, \
                MAX(running_total) AS units, \
                MAX(charged_at)    AS last_charge \
         FROM dreggnet_meter \
         GROUP BY lease_id \
         ORDER BY last_charge DESC NULLS LAST \
         LIMIT 200",
    )
    .fetch_all(&pool)
    .await;

    let now = time::OffsetDateTime::now_utc();
    match rows {
        Ok(rows) => {
            for (lease_id, periods, units, last) in rows {
                let (last_str, active) = match last {
                    Some(ts) => {
                        let active = (now - ts).whole_seconds() <= IN_FLIGHT_SECS;
                        (
                            ts.format(&time::format_description::well_known::Rfc3339)
                                .ok(),
                            active,
                        )
                    }
                    None => (None, false),
                };
                if active {
                    view.jobs_in_flight += 1;
                }
                view.jobs.push(DurableJob {
                    lease_id,
                    periods,
                    units_charged: units,
                    last_charge_at: last_str,
                    status: if active { "active" } else { "idle" }.to_string(),
                });
            }
        }
        Err(e) => {
            // Most commonly: the outbox table has not been created yet (no durable
            // job has metered into this database). Report it, don't fail the page.
            view.error = Some(format!(
                "no durable jobs read ({e}); the dreggnet_meter outbox appears empty/absent"
            ));
            pool.close().await;
            return view;
        }
    }

    // Totals across the whole outbox.
    if let Ok((leases, spent)) = sqlx::query_as::<_, (i64, i64)>(
        "SELECT COUNT(DISTINCT lease_id), COALESCE(SUM(amount), 0) FROM dreggnet_meter",
    )
    .fetch_one(&pool)
    .await
    {
        view.total_leases = leases;
        view.total_units_spent = spent;
    }

    // The per-event charge ledger (newest first) — the granular economy history.
    if let Ok(rows) = sqlx::query_as::<_, (String, i64, i64, i64, Option<time::OffsetDateTime>)>(
        "SELECT lease_id, period, amount, running_total, charged_at \
         FROM dreggnet_meter \
         ORDER BY charged_at DESC NULLS LAST \
         LIMIT 500",
    )
    .fetch_all(&pool)
    .await
    {
        for (lease_id, period, amount, running_total, charged) in rows {
            let charged_at = charged.and_then(|ts| {
                ts.format(&time::format_description::well_known::Rfc3339)
                    .ok()
            });
            let resource = classify_resource(&lease_id).to_string();
            view.charges.push(MeterCharge {
                lease_id,
                period,
                amount,
                running_total,
                charged_at,
                resource,
            });
        }
    }

    // The hosting-vs-compute spend split (across ALL history, in SQL so it is not
    // capped by the recent-charge window above). `host:<resource>:<key>` →
    // `<resource>`; everything else is a compute workflow lease.
    if let Ok(rows) = sqlx::query_as::<_, (String, i64, i64)>(
        "SELECT CASE WHEN lease_id LIKE 'host:%' THEN split_part(lease_id, ':', 2) \
                     ELSE 'compute' END AS resource, \
                COUNT(*)::bigint AS charges, \
                COALESCE(SUM(amount), 0)::bigint AS units \
         FROM dreggnet_meter \
         GROUP BY 1 \
         ORDER BY units DESC",
    )
    .fetch_all(&pool)
    .await
    {
        for (resource, charges, units) in rows {
            view.resource_totals.push(ResourceTotal {
                resource,
                charges,
                units,
            });
        }
    }

    pool.close().await;
    view
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classifies_hosting_and_compute_leases() {
        assert_eq!(classify_resource("host:bandwidth:site-7"), "bandwidth");
        assert_eq!(classify_resource("host:uptime:site-7"), "uptime");
        assert_eq!(classify_resource("host:publish:doc-1"), "publish");
        assert_eq!(classify_resource("host:cert:example.com"), "cert");
        assert_eq!(classify_resource("host:build:deploy-9"), "build");
        assert_eq!(classify_resource("host:weird:thing"), "hosting");
        assert_eq!(classify_resource("9f3c-instance-uuid"), "compute");
        assert_eq!(classify_resource(""), "compute");
    }
}
