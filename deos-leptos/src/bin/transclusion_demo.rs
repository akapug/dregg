//! `deos_leptos` LIVE TRANSCLUSION demo — Ted Nelson's "live quote", made runnable.
//!
//! Run: `cargo run --bin transclusion_demo` (native, the side that links the real
//! `dregg://` attested fetch + the verified read).
//!
//! It founds a **constitution** SOURCE cell carrying a `threshold` field, renders a
//! **council** page that **transcludes** that threshold as a LIVE quote (value +
//! provenance + backlinks) through the REAL
//! `starbridge_web_surface::transclusion::TranscludedField`, and then — THE PAYOFF —
//! **amends the constitution** (a genuine source state-advance) and re-renders,
//! showing the quote tracking the source REACTIVELY: the displayed value advances
//! (e.g. 3 → 5 → 7) and the provenance height advances with it, never the stale prior
//! value. That sequence is exactly what the Leptos quote `Memo`
//! (`CouncilTransclusionView`) recomputes when its `source_height` trigger is bumped —
//! the headless form of the in-browser live update.
//!
//! Finally it shows the **anti-forge tooth**: a forged quote (tampered bytes) is
//! REFUSED by the verification chain — it never renders as a verified quote.

use deos_leptos::transclusion_demo::{forge_a_quote, live_quote_sequence};

fn main() {
    println!("== deos LIVE TRANSCLUSION — Ted Nelson's live quote, on the verified substrate ==\n");
    println!(
        "A `council` page transcludes a `constitution` cell's `threshold` as a LIVE\n\
         quote, through the REAL `TranscludedField::include` (the verified cross-cell\n\
         finalized read). When the constitution is AMENDED, the quote tracks the\n\
         source — the value AND its provenance height advance, reactively.\n"
    );

    // Found the constitution at threshold 3, then amend it twice (→ 5 → 7), rendering
    // the council's live quote after each. 4 sibling surfaces also quote it.
    let steps = live_quote_sequence(3, 2, 4);

    for (i, step) in steps.iter().enumerate() {
        println!("─── step {i}: {} ───", step.label);
        println!(
            "  live quote value : constitution threshold = {}",
            step.threshold
        );
        println!("  provenance       : {}", step.provenance);
        println!();
        // The rendered council surface the viewer's island shows (the live quote +
        // provenance + backlinks, as HTML).
        println!("{}\n", step.html);
    }

    // The reactive payoff, stated plainly from the sequence.
    let first = steps.first().expect("a founded step");
    let last = steps.last().expect("an amended step");
    println!(
        "THE LIVE UPDATE: the quote showed threshold={} (height {}), and after the\n\
         amendments it shows threshold={} (height {}) — the SAME `dregg://constitution`\n\
         ref (the unbreakable link), re-resolved to the source's NEW committed value.\n\
         NOT a frozen copy: the live quote tracked the source reactively.\n",
        first.threshold, first.height, last.threshold, last.height
    );

    // ════════════════════════════════════════════════════════════════════════
    // THE ANTI-FORGE TOOTH — a forged quote does NOT render as verified.
    // ════════════════════════════════════════════════════════════════════════
    println!("== a FORGED quote is refused (no opened provenance ⇒ no quote) ==\n");
    let (forged_bytes, refusal) = forge_a_quote(3, 999);
    println!(
        "  a forger took a genuine attested constitution (threshold 3) and tampered\n\
         the served bytes to claim threshold {} — the verification chain refused it:\n\
           → REFUSED: {}\n\
         so the forged value NEVER renders as a verified quote (a tampered quote's\n\
         content_hash no longer matches its bytes). The quote cannot be faked.",
        String::from_utf8_lossy(&forged_bytes),
        refusal
    );

    println!(
        "\nWhat you'd see in a BROWSER: the council page shows \"constitution threshold\n\
         (live quote): 3\" with its provenance line; pressing \"amend constitution\"\n\
         advances the source and the quote updates IN PLACE to 5 (then 7) — the live,\n\
         unbreakable Nelson link, with no page reload. (The resolve runs server-side\n\
         atop native crypto — the deos will/law seam — and the island POSTs to it.)"
    );
}
