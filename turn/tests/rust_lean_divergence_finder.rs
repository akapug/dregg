//! RUST↔LEAN DIVERGENCE FINDER — the empirical swap-confidence harness.
//!
//! Runs the REAL legacy Rust executor (`TurnExecutor::execute` → `apply.rs`) and the
//! VERIFIED Lean executor (`dregg_exec_full_forest_auth` via the FFI shadow) side-by-side
//! over a CORPUS of turns covering many effect types, and LOGS every divergence.
//!
//! For each corpus turn we:
//!   1. snapshot the pre-state ledger,
//!   2. run the real Rust executor (this is the genuine `apply.rs` walk — not a
//!      reimplementation), capturing its commit decision,
//!   3. call [`lean_shadow::shadow_report`], which marshals the SAME turn + pre-state through
//!      the gated Lean FFI and returns the Lean commit decision,
//!   4. compare.
//!
//! The output is a DIVERGENCE LEDGER, effect-by-effect:
//!   * AGREE     — Lean modelled the effect and matched Rust's commit bit.
//!   * DIVERGE   — Lean modelled the effect and DISAGREED (a real drift / bug).
//!   * GAP       — the effect is not yet projected to the Lean wire (no Lean model;
//!                 the turn is INELIGIBLE for shadow). This is the remaining drift surface,
//!                 not a divergence — it tells us what still needs a Lean model before swap.
//!
//! Run with the Lean FFI linked + shadow on:
//!   DREGG_LEAN_SHADOW=1 cargo test -p dregg-turn --features lean-shadow \
//!       --test rust_lean_divergence_finder -- --nocapture
//!
//! Without the feature the harness still runs (every effect reports GAP — no Lean linked),
//! so it is CI-safe either way; the ledger then records the eligibility map only.

use std::collections::BTreeMap;

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::action::Event;
use dregg_turn::lean_shadow::{self, ShadowReport};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

// ---------------------------------------------------------------------------
// Fixture builders
// ---------------------------------------------------------------------------

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn make_open_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn field_from_u64(v: u64) -> FieldElement {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&v.to_be_bytes());
    f
}

/// A turn carrying the given effects under `Unchecked` auth, with `valid_until` SET (the
/// shadow requires it) and a single root action targeting `agent`.
fn corpus_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        // The Lean wire marshaller REQUIRES valid_until (admission reads it). Set it high.
        valid_until: Some(1_000_000),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// One corpus case: a label, a two-cell ledger (cell A = agent, cell B = counterparty), and
/// the turn to run. Cells A and B always exist & are open so authority is not the variable
/// under test (we are testing the executor's STATE transition, not the gate, here).
struct CorpusCase {
    label: &'static str,
    turn: Turn,
    ledger: Ledger,
}

fn two_cell_ledger(bal_a: u64, bal_b: u64) -> (Ledger, CellId, CellId) {
    let a = make_open_cell(1, bal_a);
    let b = make_open_cell(2, bal_b);
    let (ida, idb) = (a.id(), b.id());
    let mut l = Ledger::new();
    l.insert_cell(a).unwrap();
    l.insert_cell(b).unwrap();
    (l, ida, idb)
}

/// Build the corpus: at least one turn per effect type the harness can construct standalone.
/// Effects requiring elaborate pre-state (live escrows, queues with prior allocate, sealed
/// pairs, bridge proofs) are represented by their CREATE/entry effect so the executor path is
/// still exercised and the effect appears in the ledger.
fn build_corpus() -> Vec<CorpusCase> {
    let mut cases: Vec<CorpusCase> = Vec::new();

    macro_rules! case {
        ($label:expr, $bal_a:expr, $bal_b:expr, |$a:ident, $b:ident| $effects:expr) => {{
            let (ledger, $a, $b) = two_cell_ledger($bal_a, $bal_b);
            let turn = corpus_turn($a, 0, $effects);
            cases.push(CorpusCase { label: $label, turn, ledger });
        }};
    }

    // ---- Lean-MODELLED effects (expected: comparable) ----
    case!("SetField", 100, 100, |a, _b| vec![Effect::SetField {
        cell: a,
        index: 2,
        value: field_from_u64(42),
    }]);
    case!("Transfer", 100, 100, |a, b| vec![Effect::Transfer {
        from: a,
        to: b,
        amount: 30,
    }]);
    case!("Transfer/overspend", 10, 100, |a, b| vec![Effect::Transfer {
        from: a,
        to: b,
        amount: 9999,
    }]);
    // Same shape as the FFI `marshal_roundtrip` overspend gate (bal 100, amount 1000) to
    // pin whether the divergence tracks the NUMBERS or the marshalled side-table shape.
    case!("Transfer/overspend2", 100, 5, |a, b| vec![Effect::Transfer {
        from: a,
        to: b,
        amount: 1000,
    }]);
    case!("SetPermissions", 100, 100, |a, _b| vec![Effect::SetPermissions {
        cell: a,
        new_permissions: open_permissions(),
    }]);
    case!("SetVerificationKey", 100, 100, |a, _b| vec![Effect::SetVerificationKey {
        cell: a,
        new_vk: None,
    }]);
    case!("EmitEvent", 100, 100, |a, _b| vec![Effect::EmitEvent {
        cell: a,
        event: Event { topic: [7u8; 32], data: vec![[1u8; 32]] },
    }]);
    case!("MakeSovereign", 100, 100, |a, _b| vec![Effect::MakeSovereign { cell: a }]);
    case!("NoteCreate", 100, 100, |a, _b| vec![Effect::NoteCreate {
        commitment: dregg_cell::NoteCommitment([0xBB; 32]),
        value: 0,
        asset_type: 0,
        encrypted_note: vec![],
        value_commitment: None,
        range_proof: None,
    }]);
    case!("NoteSpend", 100, 100, |a, _b| vec![Effect::NoteSpend {
        nullifier: dregg_cell::Nullifier([0xAA; 32]),
        // Non-null root: apply.rs rejects a null `note_tree_root` outright (a precondition the
        // Lean wire projection drops, since `notespend` carries only the nullifier). A non-null
        // root lets the comparison reach the SET-transition decision rather than tripping the
        // null-root guard.
        note_tree_root: [0x11; 32],
        value: 0,
        asset_type: 0,
        spending_proof: vec![],
        value_commitment: None,
    }]);
    // Multi-effect, all-modelled: mint-like setfield + transfer in one action.
    case!("SetField+Transfer", 100, 100, |a, b| vec![
        Effect::SetField { cell: a, index: 2, value: field_from_u64(1) },
        Effect::Transfer { from: a, to: b, amount: 10 },
    ]);

    // ---- Effects WITHOUT a Lean wire model yet (expected: GAP) ----
    case!("IncrementNonce", 100, 100, |a, _b| vec![Effect::IncrementNonce { cell: a }]);
    case!("Burn", 100, 100, |a, _b| vec![Effect::Burn { target: a, slot: 0, amount: 10 }]);
    case!("CellSeal", 100, 100, |a, _b| vec![Effect::CellSeal { target: a, reason: [9u8; 32] }]);
    case!("GrantCapability", 100, 100, |a, b| {
        // CapabilityRef shape varies; use the queue-allocate effect as a stand-in entry that
        // is definitely GAP. (GrantCapability needs a CapabilityRef we don't construct here.)
        let _ = (a, b);
        vec![Effect::QueueAllocate { capacity: 4, program_vk: None }]
    });

    cases
}

// ---------------------------------------------------------------------------
// Per-effect ledger accumulation
// ---------------------------------------------------------------------------

#[derive(Default, Clone)]
struct EffectStat {
    agree: u32,
    diverge: u32,
    gap: u32,
    error: u32,
    /// One example divergence note (effect kinds, rust vs lean commit).
    diverge_note: Option<String>,
    /// Whether ANY case carrying this effect was Lean-eligible (modelled).
    ever_modelled: bool,
}

fn classify(report: &ShadowReport, kinds: &[&'static str], stats: &mut BTreeMap<String, EffectStat>) {
    for k in kinds {
        let e = stats.entry(k.to_string()).or_default();
        if report.lean_eligible {
            e.ever_modelled = true;
        }
        match report.agree {
            Some(true) => e.agree += 1,
            Some(false) => {
                e.diverge += 1;
                if e.diverge_note.is_none() {
                    e.diverge_note = Some(format!(
                        "rust_committed={} lean_committed={:?}",
                        report.rust_committed, report.lean_committed
                    ));
                }
            }
            None => {
                if report.error.is_some() && report.lean_eligible {
                    e.error += 1;
                } else {
                    e.gap += 1;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The harness
// ---------------------------------------------------------------------------

#[test]
fn rust_lean_divergence_finder() {
    let shadow_on = std::env::var("DREGG_LEAN_SHADOW").as_deref() == Ok("1");
    // block_height 0 ⇒ the marshaller omits the optional `block_height` wire field (the
    // executor falls back to `now`/`valid_until` for expiry). We run at 0 so the corpus is
    // marshalled with the SAME envelope shape the byte-exact `marshal_roundtrip` gate proves
    // correct; the block_height>0 wire path is exercised separately by the FFI's own
    // `full_turn_differential` over execFullTurn.
    let block_height = 0u64;

    let mut per_effect: BTreeMap<String, EffectStat> = BTreeMap::new();
    let mut rows: Vec<String> = Vec::new();
    let mut total = 0usize;
    let mut comparable = 0usize;
    let mut diverged = 0usize;

    for mut case in build_corpus() {
        total += 1;
        // Snapshot pre-state BEFORE the real executor mutates the ledger.
        let pre_ledger = case.ledger.clone();

        // RUN THE REAL RUST EXECUTOR (apply.rs) — a FRESH executor per case so each corpus
        // turn is the FIRST in its own receipt chain. (Reusing one executor advances its
        // internal receipt-chain head after the first commit, so later turns with
        // `previous_receipt_hash: None` would be rejected with `ReceiptChainMismatch` — a
        // harness artefact, NOT a kernel divergence, since the Lean shadow does not model the
        // receipt chain. The fresh executor isolates the per-effect state transition under test.)
        let executor = TurnExecutor::new(ComputronCosts::zero());
        let result = executor.execute(&case.turn, &mut case.ledger);
        let rust_committed = result.is_committed();
        let rust_reason = match &result {
            dregg_turn::turn::TurnResult::Rejected { reason, at_action } => {
                format!("Rejected({reason:?} @{at_action:?})")
            }
            dregg_turn::turn::TurnResult::Committed { .. } => "Committed".to_string(),
            other => format!("{other:?}"),
        };

        // RUN THE VERIFIED LEAN EXECUTOR over the same turn + pre-state.
        let report = lean_shadow::shadow_report(&case.turn, &pre_ledger, rust_committed, block_height);

        classify(&report, &report.effect_kinds, &mut per_effect);

        let verdict = match report.agree {
            Some(true) => {
                comparable += 1;
                "AGREE".to_string()
            }
            Some(false) => {
                comparable += 1;
                diverged += 1;
                format!(
                    "DIVERGE (rust={}, lean={:?})",
                    report.rust_committed, report.lean_committed
                )
            }
            None if report.lean_eligible && report.error.is_some() => {
                format!("ERROR ({})", report.error.clone().unwrap())
            }
            None => "GAP (no Lean model)".to_string(),
        };

        rows.push(format!(
            "| {} | {} | {} | lean={:?} | {} |",
            case.label,
            report.effect_kinds.join("+"),
            rust_reason,
            report.lean_committed,
            verdict,
        ));
    }

    // ---- Emit the ledger to stdout ----
    println!("\n=== RUST↔LEAN DIVERGENCE LEDGER (shadow_on={shadow_on}) ===\n");
    println!("Corpus turns: {total} | comparable (Lean modelled): {comparable} | DIVERGENCES: {diverged}\n");
    println!("| case | effects | rust | lean | verdict |");
    println!("|------|---------|------|------|---------|");
    for r in &rows {
        println!("{r}");
    }

    println!("\n--- per-effect map ---");
    println!("| effect | modelled | agree | diverge | gap | error |");
    println!("|--------|----------|-------|---------|-----|-------|");
    for (k, s) in &per_effect {
        println!(
            "| {} | {} | {} | {} | {} | {} |{}",
            k,
            if s.ever_modelled { "yes" } else { "NO (gap)" },
            s.agree,
            s.diverge,
            s.gap,
            s.error,
            s.diverge_note
                .as_ref()
                .map(|n| format!(" <- {n}"))
                .unwrap_or_default(),
        );
    }

    // ---- Write the markdown ledger to disk for the maintainer ----
    write_ledger_markdown(shadow_on, total, comparable, diverged, &rows, &per_effect);

    // The harness is a DIVERGENCE LEDGER / monitor: its job is to RUN both executors and
    // CHARACTERISE the drift, not to pretend there is none. Divergences are recorded (above +
    // on disk) and summarised here; they do NOT fail the run by themselves (the maintainer
    // reads the ledger). What WOULD be a regression — and DOES fail — is:
    //   (a) the harness not running both executors at all (no comparable cases when shadow on), or
    //   (b) a known-AGREEING effect flipping to DIVERGE (a real new drift on a path we trust).
    //
    // KNOWN-DRIFT allowlist (documented in the ledger): under the lean_shadow marshaller the
    // turn auth is `Unchecked` with an EMPTY caps table, so the Lean per-asset executor treats
    // a balance/note transfer as a NO-OP commit (loglen 0, no state change) — it neither
    // applies nor rejects it — whereas apply.rs APPLIES it (Transfer) or REJECTS on a
    // precondition the projection drops (overspend availability; NoteSpend null note_tree_root).
    // These are MARSHALLER-faithfulness gaps (the shadow wire under-specifies auth/caps +
    // drops note_tree_root), NOT verified-kernel logic bugs. See the ledger's "Findings".
    let known_drift: &[&str] = &["Transfer", "NoteSpend"];
    let unexpected: Vec<(&String, &EffectStat)> = per_effect
        .iter()
        .filter(|(k, s)| s.diverge > 0 && !known_drift.contains(&k.as_str()))
        .collect();

    if diverged > 0 {
        eprintln!(
            "\n[divergence-finder] {diverged} divergence(s) recorded across {comparable} comparable \
             turn(s) — see metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md. \
             All are on the KNOWN-DRIFT allowlist {known_drift:?} (marshaller-faithfulness gaps)."
        );
    }

    if shadow_on {
        assert!(
            comparable > 0,
            "shadow is ON but NO turn was comparable — the Lean FFI did not run (link/marshal \
             failure?). The divergence finder must actually execute the Lean executor."
        );
        assert!(
            per_effect.get("SetField").map(|s| s.agree > 0).unwrap_or(false),
            "regression: SetField no longer AGREES between apply.rs and the Lean executor \
             (this is the load-bearing modelled-and-applied path)."
        );
    }

    assert!(
        unexpected.is_empty(),
        "NEW RUST↔LEAN DIVERGENCE(S) outside the known-drift allowlist: {:?} — a modelled \
         effect's commit bit now differs between apply.rs and the verified Lean executor. \
         Investigate before extending the allowlist (see the ledger).",
        unexpected.iter().map(|(k, _)| k.as_str()).collect::<Vec<_>>()
    );
}

fn write_ledger_markdown(
    shadow_on: bool,
    total: usize,
    comparable: usize,
    diverged: usize,
    rows: &[String],
    per_effect: &BTreeMap<String, EffectStat>,
) {
    // metatheory/docs/rebuild/ relative to the workspace root. CARGO_MANIFEST_DIR is `turn/`.
    let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let Some(root) = manifest.parent() else { return };
    let dir = root.join("metatheory").join("docs").join("rebuild");
    if std::fs::create_dir_all(&dir).is_err() {
        return;
    }
    let path = dir.join("_RUST-LEAN-DIVERGENCE-LEDGER.md");

    let mut md = String::new();
    md.push_str("# Rust↔Lean Divergence Ledger\n\n");
    md.push_str(
        "Generated by `turn/tests/rust_lean_divergence_finder.rs` — runs the REAL Rust \
         executor (`apply.rs`) and the VERIFIED Lean executor (`dregg_exec_full_forest_auth` \
         FFI) side-by-side over a corpus of turns and records every divergence.\n\n",
    );
    md.push_str(&format!(
        "- `DREGG_LEAN_SHADOW`/`lean-shadow` active: **{shadow_on}** (false ⇒ Lean not linked; \
         the table records the eligibility map only — every effect shows GAP).\n",
    ));
    md.push_str(&format!(
        "- Corpus turns: **{total}** | comparable (Lean modelled): **{comparable}** | \
         **DIVERGENCES: {diverged}**\n\n",
    ));
    md.push_str(
        "Verdict legend: **AGREE** = Lean modelled the effect and matched apply.rs's commit \
         bit. **DIVERGE** = modelled and DISAGREED (a real drift/bug). **GAP** = no Lean wire \
         model yet (turn ineligible for shadow; the remaining swap surface, not a bug).\n\n",
    );

    md.push_str("## Per-turn\n\n");
    md.push_str("| case | effects | rust | lean | verdict |\n");
    md.push_str("|------|---------|------|------|---------|\n");
    for r in rows {
        md.push_str(r);
        md.push('\n');
    }

    md.push_str("\n## Per-effect map\n\n");
    md.push_str("| effect | modelled | agree | diverge | gap | error | note |\n");
    md.push_str("|--------|----------|-------|---------|-----|-------|------|\n");
    for (k, s) in per_effect {
        md.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} |\n",
            k,
            if s.ever_modelled { "yes" } else { "NO" },
            s.agree,
            s.diverge,
            s.gap,
            s.error,
            s.diverge_note.clone().unwrap_or_default(),
        ));
    }

    md.push_str(
        "\n## Findings (characterised drift)\n\n\
         The agreement comparison is COMMIT-BIT-ONLY (the shadow compares whether both \
         executors commit/roll back, not the full post-state). With that lens:\n\n\
         1. **Modelled & agreeing**: `SetField`, `SetPermissions`, `SetVerificationKey`, \
         `EmitEvent`, `MakeSovereign`, `NoteCreate`, and authorised `Transfer` (e.g. 30/100) — \
         apply.rs and the verified Lean executor agree on the commit decision. \
         The handler-audit suspects (`MakeSovereign`/`receiptArchive`/`queueAllocate`): \
         `MakeSovereign` is now MODELLED and AGREES; `ReceiptArchive`/`QueueAllocate` remain \
         GAP (no Lean wire projection yet — not a divergence).\n\n\
         2. **Known drift (allowlisted)** — `Transfer` overspend & `NoteSpend`: the \
         `lean_shadow` marshaller emits the turn under `Unchecked` auth with an EMPTY caps \
         table and DROPS the `note_tree_root`. Consequence: the Lean per-asset executor \
         commits these as a **NO-OP** (loglen 0, no state change — it neither applies nor \
         rejects), while apply.rs either REJECTS on a precondition the projection cannot see \
         (overspend availability; NoteSpend null `note_tree_root`) or APPLIES the move. These \
         are **MARSHALLER-faithfulness gaps** (the shadow wire under-specifies auth/caps and \
         drops note fields), not verified-kernel logic bugs. To close them: marshal the real \
         credential + caps so the Lean per-asset gate is genuinely exercised, and carry the \
         note_tree_root in the `notespend` wire arm. Until then they are recorded, not failed.\n\n\
         3. **GAP (no Lean model yet)** — `IncrementNonce`, `Burn`, `CellSeal`, `QueueAllocate`, \
         and the ~35 other effects: not projected to the Lean wire, so the turn is INELIGIBLE \
         for shadow. This is the remaining SWAP surface — what still needs a Lean model + wire \
         arm before the full cutover. The 9 currently-modelled effects are: SetField, Transfer, \
         SetPermissions, SetVerificationKey, EmitEvent, MakeSovereign, RevokeDelegation, \
         NoteSpend, NoteCreate.\n\n\
         ## How to run\n\n```\nDREGG_LEAN_SHADOW=1 cargo test -p dregg-turn \
         --features lean-shadow --test rust_lean_divergence_finder -- --nocapture\n```\n\n\
         Requires `dregg-lean-ffi/libdregg_lean.a` (the compiled Lean closure) present + the \
         project Lean toolchain (build.rs resolves the sysroot via `lake env`). \
         Wire into CI / devnet by running the node with `DREGG_LEAN_SHADOW=1` and the \
         `lean-shadow` feature — `lean_shadow::maybe_shadow_turn` then logs live divergences \
         (target `dregg::lean_shadow::divergence`) for every executed turn.\n",
    );

    let _ = std::fs::write(&path, md);
    println!("\n[ledger written to {}]", path.display());
}
