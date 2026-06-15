//! `deos_leptos` SSR demo — render the deos council cell as a Leptos reactive
//! surface, per-viewer, and print the HTML each viewer's island would hydrate.
//!
//! Run: `cargo run` (native, the gate-linkable side). It renders the SAME council
//! surface for three viewers and shows that the membrane re-expands it to DIFFERENT
//! per-viewer surfaces — the runtime form of frustum-snapshot rehydration — and
//! that the vote button is lit/dark by the REAL `ReactiveAffordance` gate.

use deos_leptos::{council_surface, render_council_for, member_held, observer_held};
use starbridge_web_surface::{Rehydration, Viewer};
use dregg_types::CellId;

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
        ("MEMBER  (Either / ballot cap, permits all)", &member, Rehydration::ReplayedDeterministic),
        ("OBSERVER(Signature, permits all)", &observer, Rehydration::Live),
        ("GUEST   (Signature, permits NONE — equal caps to observer)", &guest, Rehydration::ReconstructedApproximate),
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
}
