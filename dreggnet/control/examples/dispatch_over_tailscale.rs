//! Drive a funded lease through the control plane onto a fleet node over the
//! tailnet/headscale overlay — the live `gateway→node-a` dispatch, *not* a raw
//! curl. This is the runnable proof that [`dreggnet_control::dispatch_lease_over_mesh`]
//! issues the real `POST <overlay-addr>:8021/fulfill` and decodes the durable
//! metered result the node-agent returns.
//!
//! Run it on a host already joined to the overlay (e.g. the DreggNet edge
//! `100.64.0.1`):
//!
//! ```text
//! dispatch_over_tailscale [overlay_addr] [agent_port] [lessee] [budget] [per_period]
//! # defaults: 100.64.0.2 8021 agent-edge 100 1
//! ```
//!
//! It prints the decoded [`dreggnet_control::DurableOutput`] (`step1/step2/outputs/
//! meter_units`) on success, or the provider error (a lapse for a refused lease).

use std::net::Ipv4Addr;

use dreggnet_control::{
    CapGrade, Lease, MachineId, MeshNode, TailscaleMesh, dispatch_lease_over_mesh,
};

#[tokio::main]
async fn main() {
    let mut args = std::env::args().skip(1);
    let overlay_addr: Ipv4Addr = args
        .next()
        .unwrap_or_else(|| "100.64.0.2".into())
        .parse()
        .expect("overlay_addr must be an IPv4 address");
    let agent_port: u16 = args
        .next()
        .unwrap_or_else(|| "8021".into())
        .parse()
        .expect("agent_port must be a u16");
    let lessee = args.next().unwrap_or_else(|| "agent-edge".into());
    let budget: i64 = args
        .next()
        .unwrap_or_else(|| "100".into())
        .parse()
        .unwrap_or(100);
    let per_period: i64 = args
        .next()
        .unwrap_or_else(|| "1".into())
        .parse()
        .unwrap_or(1);

    // The node to reach over the overlay. For a tailnet link the public_key/endpoint
    // are unused (the host overlay carries the bytes); only the overlay address +
    // agent port are dialed.
    let mut node = MeshNode::new(
        MachineId("edge-dispatch".into()),
        "tailnet-carried", // unused on the tailscale backend
        format!("{overlay_addr}:0"),
        overlay_addr,
    );
    node.agent_port = agent_port;

    let lease = Lease::funded(lessee, CapGrade::Sandboxed, "USD-mesh", budget, per_period);
    let instance = format!("edge-dispatch-{}", std::process::id());

    eprintln!(
        "dispatching lease (lessee={}, budget={budget}, per_period={per_period}) \
         to {overlay_addr}:{agent_port} over the tailscale overlay, instance={instance}",
        lease.lessee,
    );

    let mesh = TailscaleMesh::new();
    match dispatch_lease_over_mesh(&mesh, &node, &lease, &instance).await {
        Ok(out) => {
            println!("OK — durable metered result from the bridge agent:");
            println!("  step1       = {}", out.step1);
            println!("  step2       = {}", out.step2);
            println!("  outputs     = {:?}", out.outputs);
            println!("  meter_units = {}", out.meter_units);
        }
        Err(e) => {
            eprintln!("dispatch failed: {e}");
            std::process::exit(1);
        }
    }
}
