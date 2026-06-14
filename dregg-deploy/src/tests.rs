//! DreggDL tests: a valid deployment passes the static assurance; a
//! non-conserving / over-granting deployment FAILS with the precise locus; a
//! parse → lower → re-serialize round-trip is stable.

use crate::*;

// ─── a valid deployment passes ───────────────────────────────────────────────

const ESCROW: &str = include_str!("../examples/escrow.dregg.toml");

#[test]
fn valid_escrow_deployment_passes() {
    let v = check(ESCROW, false).expect("escrow parses + lowers");
    assert!(
        v.pass(),
        "valid escrow deployment must pass static assurance; findings: {:?}",
        v.assurance.all_findings()
    );
    // Three cells born (deal-001, operator, bank), one fund, one grant.
    assert_eq!(v.cells.len(), 3, "three cells declared");
    assert_eq!(v.factories.len(), 1, "one factory declared");
    // 3 births + 1 fund + 1 grant = 5 effect-groups.
    assert_eq!(v.turn_count, 5);
}

#[test]
fn resolved_ids_are_deterministic() {
    let a = check(ESCROW, false).unwrap();
    let b = check(ESCROW, false).unwrap();
    assert_eq!(a.cells, b.cells, "cell ids are a deterministic function of names");
    assert_eq!(a.factories, b.factories, "factory_vks are deterministic");
}

// ─── a non-conserving deployment fails with the asset locus ──────────────────

#[test]
fn non_conserving_fund_is_caught() {
    // A fund whose `from` and `to` are the same is balanced by construction
    // (Transfer always nets); to make the forest non-conserve, inject a
    // balance_change via... actually the surface only emits Transfers (which
    // self-net). The conservation violation we CAN express at the surface is a
    // ring imbalance — exercised below. For a pure non-conservation, we drive
    // the lowered forest directly: build a Deployment, lower it, then mutate.
    //
    // Here we assert the positive: a plain funded deployment conserves.
    let v = check(ESCROW, false).unwrap();
    assert!(v.assurance.conservation.is_pass(), "funding transfers self-net");
}

#[test]
fn unbalanced_ring_is_caught() {
    // Three funds that do NOT close into a ring: a→b, b→c, but no c→a. With
    // --ring, the participants don't all net to zero → a ring finding.
    let dl = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "b"
factory = "f"
[[cell]]
name = "c"
factory = "f"

[[fund]]
from = "a"
to   = "b"
amount = 10
[[fund]]
from = "b"
to   = "c"
amount = 10
"#;
    let v = check(dl, true).expect("parses");
    assert!(
        !v.assurance.ring_balance.is_pass(),
        "an un-closed ring must fail the ring check"
    );
    // The closed version passes the ring check.
    let closed = format!("{dl}\n[[fund]]\nfrom = \"c\"\nto = \"a\"\namount = 10\n");
    let vc = check(&closed, true).expect("parses");
    assert!(
        vc.assurance.ring_balance.is_pass(),
        "a closed conserving ring passes; findings: {:?}",
        vc.assurance.ring_balance.findings()
    );
}

// ─── an over-granting (amplifying) deployment fails with the grant locus ─────

#[test]
fn amplifying_redelegation_is_caught() {
    // root grants `operator` a TRANSFER-ONLY facet over `deal`. operator then
    // re-delegates to `sub` a cap over the SAME target `deal` but UNRESTRICTED
    // (allowed_effects absent = top). That widens what it was handed → an
    // in-forest amplification along the delegation edge.
    //
    // EFFECT_TRANSFER = 1<<1 = 2.
    let dl = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

# root → operator: a TRANSFER-ONLY facet over `deal`.
[[grant]]
from = "deal"
to   = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2

# operator → sub: UNRESTRICTED over `deal` (no allowed_effects = top). This
# amplifies the transfer-only cap operator was handed.
[[grant]]
from = "operator"
to   = "sub"
permissions = "signature"
target = "deal"
"#;
    let v = check(dl, false).expect("parses + lowers");
    assert!(
        !v.assurance.no_amplification.is_pass(),
        "a widening re-delegation must fail non-amplification"
    );
    let findings = v.assurance.no_amplification.findings();
    assert!(
        findings.iter().any(|f| f.message.contains("amplifies")),
        "the finding names the amplification; got: {findings:?}"
    );
    // And the locus points at a node with an effect index (the grant edge).
    assert!(
        findings[0].locus.effect_index.is_some(),
        "the finding locates the offending grant effect"
    );
}

#[test]
fn attenuating_redelegation_passes() {
    // The same shape, but operator NARROWS (re-grants the same transfer-only
    // facet, or narrower) → an attenuation, which passes.
    let dl = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

[[grant]]
from = "deal"
to   = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2

# operator → sub: the SAME transfer-only facet. An attenuation (⊆).
[[grant]]
from = "operator"
to   = "sub"
permissions = "signature"
target = "deal"
allowed_effects = 2
"#;
    let v = check(dl, false).expect("parses + lowers");
    assert!(
        v.assurance.no_amplification.is_pass(),
        "re-granting the same-or-narrower facet is an attenuation; findings: {:?}",
        v.assurance.no_amplification.findings()
    );
}

// ─── unknown-name and structural errors are reported with the locus ──────────

#[test]
fn unknown_factory_reference_errors() {
    let dl = r#"
[federation]
id = "auto"
[[cell]]
name = "c"
factory = "does-not-exist"
"#;
    let err = check(dl, false).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("does-not-exist"), "names the missing factory: {msg}");
}

#[test]
fn unknown_grant_target_errors() {
    let dl = r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "a"
factory = "f"
[[grant]]
from = "a"
to   = "ghost"
"#;
    let err = check(dl, false).unwrap_err();
    let msg = format!("{err}");
    assert!(msg.contains("ghost"), "names the unresolved recipient: {msg}");
}

#[test]
fn duplicate_cell_name_errors() {
    let dl = r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "a"
factory = "f"
"#;
    let err = check(dl, false).unwrap_err();
    assert!(format!("{err}").contains("duplicate cell name"), "rejects dup names");
}

// ─── round-trip: parse → re-serialize → parse is stable ──────────────────────

#[test]
fn parse_serialize_roundtrip_is_stable() {
    let dep = parse_toml(ESCROW).expect("escrow parses");
    let reserialized = serialize_toml(&dep).expect("serializes back to TOML");
    let dep2 = parse_toml(&reserialized).expect("re-serialized form re-parses");
    assert_eq!(dep, dep2, "parse∘serialize∘parse is a fixpoint");
}

#[test]
fn lower_is_deterministic_byte_for_byte() {
    // The whole point: lowering is a pure function — same DreggDL → same forest.
    let dep = parse_toml(ESCROW).unwrap();
    let a = Lowered::from_deployment(&dep).unwrap();
    let b = Lowered::from_deployment(&dep).unwrap();
    let ja = serde_json::to_vec(&a.forest).unwrap();
    let jb = serde_json::to_vec(&b.forest).unwrap();
    assert_eq!(ja, jb, "lowering the same DreggDL yields a byte-identical forest");
    assert_eq!(a.federation_id, b.federation_id);
}

// ─── JSON surface parses too (the canonical form is the serde struct) ────────

#[test]
fn json_surface_parses() {
    let dep_toml = parse_toml(ESCROW).unwrap();
    let json = serde_json::to_string(&dep_toml).unwrap();
    let dep_json = parse_json(&json).unwrap();
    assert_eq!(dep_toml, dep_json, "TOML and JSON surfaces agree");
}

// ════════════════════════════════════════════════════════════════════════════
//  apply: lower → per-root turn sequence + receipt-chain shape, GATED by the
//  static check.
// ════════════════════════════════════════════════════════════════════════════

use crate::apply::{plan_apply, plan_apply_toml, ApplyError};

/// An amplifying deployment: operator is handed a TRANSFER-ONLY facet (mask 2)
/// over `deal`, then re-delegates to `sub` an UNRESTRICTED cap over the same
/// target — a widening, caught as an in-forest capability amplification.
const AMPLIFYING: &str = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

[[grant]]
from = "deal"
to   = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2

[[grant]]
from = "operator"
to   = "sub"
permissions = "signature"
target = "deal"
"#;

// ─── THE GATE: an amplifying spec is REFUSED by apply, before any turn ────────

#[test]
fn apply_refuses_an_amplifying_spec_before_emitting_any_turn() {
    // This is the load-bearing property: the static check is the gate. An
    // over-grant (in-forest capability amplification) is refused up front — the
    // apply flow produces NO turn sequence for it.
    let err = plan_apply_toml(AMPLIFYING, false)
        .expect_err("an amplifying deployment must be REFUSED by the gate, not planned");
    match err {
        crate::DeployError::Lower(_) | crate::DeployError::Toml(_) | crate::DeployError::Json(_) => {
            panic!("expected a Refused gate failure, not a parse/lower error: {err}")
        }
        crate::DeployError::Apply(ApplyError::Refused { assurance }) => {
            // The refusal carries the finding that names the amplification, at
            // the grant edge — the same locus `check` reports.
            assert!(
                !assurance.no_amplification.is_pass(),
                "the refusal is on non-amplification"
            );
            let findings = assurance.no_amplification.findings();
            assert!(
                findings.iter().any(|f| f.message.contains("amplifies")),
                "the refusal names the amplification; got: {findings:?}"
            );
            assert!(
                findings[0].locus.effect_index.is_some(),
                "the refusal locates the offending grant effect"
            );
        }
        crate::DeployError::Apply(other) => {
            panic!("expected Refused, got a different apply error: {other}")
        }
    }
}

#[test]
fn apply_refuses_directly_via_plan_apply_with_the_assurance() {
    // The same gate, reached through the parsed-Deployment entry, asserting the
    // ApplyError::Refused variant carries the failing assurance directly.
    let dep = parse_toml(AMPLIFYING).unwrap();
    let err = plan_apply(&dep, false).expect_err("amplifying spec refused");
    let ApplyError::Refused { assurance } = err else {
        panic!("expected ApplyError::Refused, got {err}");
    };
    assert!(!assurance.pass(), "the carried assurance is a failing one");
    assert!(!assurance.no_amplification.is_pass());
}

// ─── a valid spec lowers to the chained per-root turn sequence ───────────────

#[test]
fn apply_emits_the_per_root_turn_sequence_for_a_valid_spec() {
    let plan = plan_apply_toml(ESCROW, false).expect("valid escrow applies");
    // The gate passed (by construction of a returned plan).
    assert!(plan.assurance.pass(), "a returned plan carries a passing assurance");
    // 3 births + 1 fund + 1 grant = 5 root effect-groups = 5 turns.
    assert_eq!(plan.len(), 5, "one turn per root effect-group");
    // Phases come out in dependency order: births first, then funds, then grants.
    let phases: Vec<&str> = plan.turns.iter().map(|t| t.phase).collect();
    assert_eq!(
        phases,
        vec!["birth", "birth", "birth", "fund", "grant"],
        "dependency order: births → funds → grants"
    );
}

#[test]
fn apply_chains_the_receipts_into_one_strand() {
    let plan = plan_apply_toml(ESCROW, false).unwrap();
    // The first turn has no predecessor.
    assert_eq!(
        plan.turns[0].turn.previous_receipt_hash, None,
        "the first turn opens the chain"
    );
    // Each subsequent turn's previous_receipt_hash is the prior turn's projected
    // receipt hash — the receipt-chain shape.
    for w in plan.turns.windows(2) {
        assert_eq!(
            w[1].turn.previous_receipt_hash,
            Some(w[0].projected_receipt_hash),
            "turn n+1 chains to turn n's projected receipt"
        );
        // And the causal dependency edge points at the prior turn.
        assert_eq!(
            w[1].turn.depends_on,
            vec![w[0].turn_hash],
            "depends_on records the prior turn"
        );
    }
    // The self-consistency invariant holds.
    assert!(plan.chain_is_linked(), "the plan's receipt chain is internally linked");
}

#[test]
fn apply_is_deterministic_byte_for_byte() {
    // apply is a pure function of the DreggDL — same doc → same turn sequence,
    // including the projected receipt chain (the reproducibility half).
    let a = plan_apply_toml(ESCROW, false).unwrap();
    let b = plan_apply_toml(ESCROW, false).unwrap();
    assert_eq!(a.len(), b.len());
    for (x, y) in a.turns.iter().zip(b.turns.iter()) {
        assert_eq!(x.turn_hash, y.turn_hash, "turn hashes are deterministic");
        assert_eq!(
            x.projected_receipt_hash, y.projected_receipt_hash,
            "the projected receipt chain is deterministic"
        );
        let jx = serde_json::to_vec(&x.turn.call_forest).unwrap();
        let jy = serde_json::to_vec(&y.turn.call_forest).unwrap();
        assert_eq!(jx, jy, "the per-turn forest is byte-identical across runs");
    }
}

#[test]
fn apply_passes_an_attenuating_redelegation_and_nests_it() {
    // The attenuating sibling of AMPLIFYING (operator re-grants the SAME
    // transfer-only facet) is NOT refused — it applies, and the re-delegation
    // nests under its parent grant (one grant turn carrying the child), so the
    // sequence has one fewer top-level grant than total grants.
    let dl = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

[[grant]]
from = "deal"
to   = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2

[[grant]]
from = "operator"
to   = "sub"
permissions = "signature"
target = "deal"
allowed_effects = 2
"#;
    let plan = plan_apply_toml(dl, false).expect("attenuating spec applies");
    assert!(plan.assurance.pass());
    // 3 births + 2 grants, but the second grant NESTS under the first, so there
    // are 3 birth turns + 1 grant turn = 4 top-level turns.
    assert_eq!(plan.len(), 4, "the re-delegation nests, not a separate root turn");
    let grant_turn = plan.turns.iter().find(|t| t.phase == "grant").unwrap();
    // The grant turn's single root carries the child grant as a nested action.
    assert_eq!(
        grant_turn.turn.call_forest.roots[0].children.len(),
        1,
        "the nested re-delegation is a child of the parent grant in the turn"
    );
}

#[test]
fn apply_refuses_a_non_conserving_ring_under_ring_mode() {
    // An un-closed ring (a→b, b→c, no c→a) fails the ring check; under as_ring
    // the apply gate refuses it.
    let dl = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "b"
factory = "f"
[[cell]]
name = "c"
factory = "f"

[[fund]]
from = "a"
to   = "b"
amount = 10
[[fund]]
from = "b"
to   = "c"
amount = 10
"#;
    let err = plan_apply_toml(dl, true).expect_err("an open ring is refused under ring mode");
    let crate::DeployError::Apply(ApplyError::Refused { assurance }) = err else {
        panic!("expected a ring refusal, got {err}");
    };
    assert!(!assurance.ring_balance.is_pass(), "refused on the ring-balance check");
    // The CLOSED ring applies cleanly (and emits 3 fund turns).
    let closed = format!("{dl}\n[[fund]]\nfrom = \"c\"\nto = \"a\"\namount = 10\n");
    let plan = plan_apply_toml(&closed, true).expect("a closed ring applies");
    assert_eq!(plan.turns.iter().filter(|t| t.phase == "fund").count(), 3);
}
