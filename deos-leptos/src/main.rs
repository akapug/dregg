//! `deos_leptos` SSR demo — render the deos council cell as a Leptos reactive
//! surface, per-viewer, and print the HTML each viewer's island would hydrate.
//!
//! Run: `cargo run` (native, the gate-linkable side). It renders the SAME council
//! surface for three viewers and shows that the membrane re-expands it to DIFFERENT
//! per-viewer surfaces — the runtime form of frustum-snapshot rehydration — and
//! that the vote button is lit/dark by the REAL `ReactiveAffordance` gate.

use deos_leptos::server::{fire_affordance, reset_executor_cell, FireRequest};
use deos_leptos::{council_surface, member_held, observer_held, render_council_for};
use dregg_types::CellId;
use starbridge_web_surface::{AuthRequired, Rehydration, Viewer};

fn cid(b: u8) -> CellId {
    let mut k = [0u8; 32];
    k[0] = b;
    CellId::derive_raw(&k, &[0u8; 32])
}

fn main() {
    let doc = cid(7);
    let surface = council_surface(doc);
    let height = 15; // inside the vote window [10, 20]

    // Viewer A — a council MEMBER (holds the ballot cap `Either`; frustum permits
    // everything). The membrane shows {tally, vote}; the vote button is LIT.
    let member = Viewer::new(member_held(cid(10)), Box::new(|_| true));

    // Viewer B — an OBSERVER (holds only `Signature`; frustum permits everything).
    // The membrane shows {tally} only — vote needs the ballot cap.
    let observer = Viewer::new(observer_held(cid(11)), Box::new(|_| true));

    // Viewer C — a GUEST at EQUAL authority to the observer (also `Signature`) but
    // whose witness-graph frustum permits NOTHING. The membrane shows {} — distinct
    // from the observer DESPITE equal caps (the keystone: divides beyond caps).
    let guest = Viewer::new(observer_held(cid(12)), Box::new(|_| false));

    println!("== deos council cell, rendered per-viewer by the Leptos runtime ==\n");

    for (label, viewer, liveness) in [
        (
            "MEMBER  (Either / ballot cap, permits all)",
            &member,
            Rehydration::ReplayedDeterministic,
        ),
        (
            "OBSERVER(Signature, permits all)",
            &observer,
            Rehydration::Live,
        ),
        (
            "GUEST   (Signature, permits NONE — equal caps to observer)",
            &guest,
            Rehydration::ReconstructedApproximate,
        ),
    ] {
        let html = render_council_for(&surface, viewer, height, liveness);
        println!("--- {label} ---");
        println!("{html}\n");
    }

    println!(
        "Note: MEMBER's surface carries the vote button (lit); OBSERVER's drops it \n\
         (no ballot cap); GUEST's is empty (witness-graph permits nothing) — the \n\
         SAME server render, re-expanded to DISTINCT per-viewer surfaces by the \n\
         REAL membrane. That is frustum-snapshot rehydration in the Leptos runtime."
    );

    // ════════════════════════════════════════════════════════════════════════
    // THE SEAM, CLOSED — a button-press is a REAL verified turn. The island's
    // fire goes through `fire_affordance` → the REAL `ReactiveAffordance` gate →
    // the REAL `dregg_turn` executor (owned by `dregg_sdk::AgentRuntime`) → a real
    // `TurnReceipt`. We drive it here exactly as the island would: POST a
    // FireRequest, reflect the committed state.
    // ════════════════════════════════════════════════════════════════════════
    println!("\n== the vote button's press is a REAL verified turn (not a mock) ==\n");
    let start = reset_executor_cell();
    println!(
        "fresh council cell (server-side, real executor): tally {}\n",
        start.tally
    );

    // A COUNCILLOR (holds the ballot cap `Either`) presses vote — both teeth pass,
    // the gate dispatches through the real executor, a real receipt comes back.
    println!("councillor (ballot cap) presses vote ×3 — each a verified turn:");
    for _ in 0..3 {
        let resp = fire_affordance(FireRequest::at("vote", AuthRequired::Either));
        match resp.result {
            Ok(c) => {
                let h = c.turn_hash;
                println!(
                    "  → COMMITTED tally={} (real turn {:02x}{:02x}{:02x}{:02x}…)",
                    c.slots.tally, h[0], h[1], h[2], h[3]
                );
            }
            Err(e) => println!("  → unexpectedly refused: {}", e.reason),
        }
    }

    // An OBSERVER (holds only `Signature`, NOT the ballot cap) presses vote — the
    // CAP tooth refuses IN-BAND and NOTHING is committed (the anti-ghost tooth).
    println!("\nobserver (no ballot cap) presses vote — refused, nothing committed:");
    let resp = fire_affordance(FireRequest::at("vote", AuthRequired::Signature));
    match resp.result {
        Ok(_) => println!("  → ERROR: an observer must NOT be able to commit a vote"),
        Err(refused) => println!(
            "  → REFUSED ({}); the committed tally is STILL {} (anti-ghost)",
            refused.reason, refused.slots.tally
        ),
    }

    // The councillor RESOLVES the proposal; now even the councillor's vote is refused
    // on the TRANSITION tooth (the vote gate's `pre` is PENDING, but the proposal is
    // now RESOLVED) — and again, nothing commits.
    println!("\ncouncillor resolves the proposal, then tries to vote (transition tooth):");
    let _ = fire_affordance(FireRequest::at("resolve", AuthRequired::Either));
    let resp = fire_affordance(FireRequest::at("vote", AuthRequired::Either));
    match resp.result {
        Ok(_) => println!("  → ERROR: a vote on a RESOLVED proposal must be refused"),
        Err(refused) => println!(
            "  → REFUSED ({}); nothing committed, tally STILL {}",
            refused.reason, refused.slots.tally
        ),
    }

    println!(
        "\nThe island is the WILL (it reacts + POSTs); the server is the LAW (the real\n\
         `dregg_turn` executor commits the verified turn). The MockExecutor seam is\n\
         CLOSED: every fire above is a genuine verified turn returning a real receipt."
    );
}
