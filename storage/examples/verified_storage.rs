//! `verified_storage` — a runnable, end-to-end demo of dregg's **formally-verified
//! decentralized storage**, tied at every step to the Lean theorem that proves it sound.
//!
//! Run it:  `cargo run -p dregg-storage --example verified_storage`
//!
//! This is a thin colour-printer over [`dregg_storage::demo::run_verified_storage_demo`] — the SAME
//! structured steps a web frontend renders, so there is one source of truth. Every step runs the
//! real codec/commitment (no mocks). Unlike Filecoin / Arweave / Storj ("trust the incentives"),
//! each step is machine-checked in Lean (`metatheory/Dregg2/Storage/`), `#assert_axioms`-clean, and
//! the ONLY cryptographic assumption is that Poseidon2 is collision-resistant.

use dregg_storage::demo::run_verified_storage_demo;

fn main() {
    println!("\x1b[1;35m╔══════════════════════════════════════════════════════════════╗");
    println!("║   dregg · FORMALLY-VERIFIED DECENTRALIZED STORAGE (live demo) ║");
    println!("╚══════════════════════════════════════════════════════════════╝\x1b[0m");

    for (i, s) in run_verified_storage_demo().into_iter().enumerate() {
        let mark = if s.ok {
            "\x1b[32m✓\x1b[0m"
        } else {
            "\x1b[1;31m✗ BUG!\x1b[0m"
        };
        let bar = "─".repeat(50usize.saturating_sub(s.title.len()));
        println!("\n\x1b[1;36m── {}. {} {bar}\x1b[0m  {mark}", i + 1, s.title);
        for line in &s.lines {
            println!("     {line}");
        }
        if let Some(t) = &s.theorem {
            println!("     \x1b[2m↳ proven: Dregg2/Storage/{t}\x1b[0m");
        }
    }

    println!("\n\x1b[1;35m╔══════════════════════════════════════════════════════════════╗\x1b[0m");
    println!("\x1b[1m  Every step above is a THEOREM, not a test.\x1b[0m");
    println!("  17 machine-checked theorems in metatheory/Dregg2/Storage/, #assert_axioms-clean");
    println!("  — sole assumption: Poseidon2 collision-resistance.");
    println!(
        "  commitment · erasure · fountain · proof-of-retrievability · availability · market."
    );
    println!("\x1b[1;35m╚══════════════════════════════════════════════════════════════╝\x1b[0m");
}
