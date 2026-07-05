//! LEASE-1a (CRITICAL) — the public create API cannot mint **free compute**.
//!
//! The hole: `create` synthesized a `funded: true` lease from the caller's
//! requested guest size, so a fabricated `memory_mb` produced a big funded lease
//! and ran compute with zero payment. The fix: a create is admitted only against a
//! **funded lease the chain attests** (via a [`FundingSource`]) whose real on-chain
//! reserve covers the request — self-asserted funding is never trusted.
//!
//! These tests prove:
//! 1. with **no** funding source the gateway fails closed (admits nothing);
//! 2. a fabricated, over-reserve guest is **refused** even when the app is funded —
//!    a big request cannot buy compute the chain did not fund;
//! 3. a create within the real on-chain reserve is admitted, using the REAL lease
//!    budget (not anything derived from the request);
//! 4. under `dregg-verify`, the funding comes from the **light-client-verified**
//!    on-chain read — a chain that attests nothing funds nothing (no free compute).

use std::sync::Arc;

use dreggnet_bridge::CapGrade;
use dreggnet_gateway::types::{GuestConfig, MachineConfig};
use dreggnet_gateway::{AttestedFunding, CreateMachineRequest, GatewayError, MachineGateway};

/// A funded on-chain lease for `app` with reserve `budget` at `grade`.
fn funded_lease(app: &str, grade: CapGrade, budget: i64) -> dreggnet_bridge::Lease {
    dreggnet_bridge::Lease::funded(app, grade, "computrons", budget, 1)
}

fn guest(cpu_kind: &str, cpus: u32, memory_mb: u32) -> CreateMachineRequest {
    CreateMachineRequest {
        config: MachineConfig {
            guest: GuestConfig {
                cpu_kind: cpu_kind.into(),
                cpus,
                memory_mb,
            },
            ..Default::default()
        },
        ..Default::default()
    }
}

#[test]
fn no_funding_source_admits_nothing() {
    let gw = MachineGateway::new();
    match gw.create("victim-app", &CreateMachineRequest::default()) {
        Err(GatewayError::Unfunded(_)) => {}
        other => panic!("expected Unfunded with no funding source, got {other:?}"),
    }
    assert_eq!(gw.count(), 0);
}

#[test]
fn a_fabricated_guest_cannot_buy_unfunded_compute() {
    // The chain funds `app` with a tiny reserve only.
    let funding = AttestedFunding::from_leases([funded_lease("app", CapGrade::MicroVm, 8)]);
    let gw = MachineGateway::new().funded_by(Arc::new(funding));

    // The attacker fabricates a huge guest to mint a big budget — but the on-chain
    // reserve does not cover it, so it is refused. No machine, no free compute.
    let huge = guest("performance", 16, 1_048_576);
    match gw.create("app", &huge) {
        Err(GatewayError::Unfunded(_)) => {}
        other => panic!("expected Unfunded for an over-reserve request, got {other:?}"),
    }
    assert_eq!(gw.count(), 0, "no machine recorded for free compute");

    // An app the chain does not fund at all is likewise refused.
    match gw.create("not-funded", &CreateMachineRequest::default()) {
        Err(GatewayError::Unfunded(_)) => {}
        other => panic!("expected Unfunded for an unfunded app, got {other:?}"),
    }
}

#[test]
fn a_covered_request_is_admitted_against_the_real_reserve() {
    // The chain attests a funded lease with a 500-unit reserve.
    let funding = AttestedFunding::from_leases([funded_lease("app", CapGrade::Caged, 500)]);
    let gw = MachineGateway::new().funded_by(Arc::new(funding));

    // A modest guest within the reserve at a met floor is admitted.
    let m = gw
        .create("app", &CreateMachineRequest::default())
        .expect("a request within the real on-chain reserve is admitted");
    assert_eq!(gw.count(), 1);
    assert_eq!(gw.list("app").len(), 1);
    assert!(!m.id.is_empty());
}

/// Under `dregg-verify`, the funding source IS the light-client-verified on-chain
/// read. A node that attests an empty chain funds nothing, so every create fails
/// closed — the verified read gates compute, no free ride from the request.
#[cfg(feature = "dregg-verify")]
#[test]
fn verified_read_gates_compute_empty_chain_funds_nothing() {
    use std::io::{Read, Write};
    use std::net::TcpListener;

    use dreggnet_control::VerifiedNodeLeaseSource;

    // A stub node serving an EMPTY verified receipt index (len 0): the verified read
    // attests no leases.
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let host = format!("127.0.0.1:{}", listener.local_addr().unwrap().port());
    let root = "00".repeat(32);
    let index_root = serde_json::json!({ "root": root, "len": 0 }).to_string();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { return };
            let mut buf = [0u8; 8192];
            let n = stream.read(&mut buf).unwrap_or(0);
            let req = String::from_utf8_lossy(&buf[..n]);
            let first = req.lines().next().unwrap_or("");
            let body = if first.starts_with("GET /api/receipts/index/root") {
                index_root.clone()
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

    // The gateway funding comes from the VERIFIED on-chain read.
    let mut source = VerifiedNodeLeaseSource::new(&host);
    let funding = AttestedFunding::from_verified_source(&mut source)
        .expect("the verified read of an empty chain succeeds with no leases");
    assert!(
        funding.is_empty(),
        "an empty chain attests no funded leases"
    );

    let gw = MachineGateway::new().funded_by(Arc::new(funding));
    match gw.create("any-app", &CreateMachineRequest::default()) {
        Err(GatewayError::Unfunded(_)) => {}
        other => panic!("expected Unfunded against an empty verified chain, got {other:?}"),
    }
    assert_eq!(gw.count(), 0);
}
