//! Two-device sync via branch-and-stitch — the firmament made concrete.
//!
//! THE THROUGH-LINE: a turn is the exercise of an attenuable proof-carrying
//! token over owned state, leaving a verifiable receipt. Here the "turn" is a
//! patch; the "owned state" is a per-device document replica; and the
//! "verifiable receipt" is the stitch verdict (clean merge, or refused at
//! settlement). Sync IS the distributed merge.
//!
//! ## The shape (BRANCH-AND-STITCH-PROTOCOL.md, mapped onto two devices)
//!
//! - A **device replica** is a [`History`]: it shares a genesis prefix with its
//!   sibling and then diverges while offline. An offline divergence is exactly a
//!   **Virtual branch** (§1) — confined, holding no cap to the other device's
//!   live state, so its edits stay imaginary until a deliberate stitch.
//! - **Coming back online is a `Stitch`** (§3): the two histories reconcile
//!   through [`History::stitch`], whose engine is [`merge`] — the categorical
//!   pushout/union (Mimram–Di Giusto). The I-confluent / monotone parts merge
//!   *clean* by union (no order to decide); the non-monotone parts surface as
//!   first-class [`Regime::Field`] conflicts.
//! - The **single door to settled reality is the Settlement Soundness gate**
//!   (`metatheory/Dregg2/Circuit/SettlementSoundness.lean`): an authority-bearing
//!   field assignment is honored at the merge ONLY IF its credential is live in
//!   the **settlement-tip revocation view** (`settledRevView`), not branch-time
//!   authority. A device that edited an authority field offline with a
//!   credential that the settlement tip has since revoked is **refused at
//!   settlement** — the branch-vs-settlement authority gap the keystone closes.
//!
//! Everything below the [`SettlementGate`] is REUSED verbatim from the in-tree
//! patch-theory core (`History` / `merge` / `content` / `Regime`); the gate is
//! the thin, faithful demo face of the Settlement Soundness keystone.
//!
//! ## Both polarities (the standing law: bite TRUE and bite FALSE)
//!
//! - `concurrent_compatible_edits_merge_clean` — two devices append disjoint
//!   prose offline; the stitch unions them with NO conflict, and BOTH devices'
//!   text survives. (The I-confluent fragment: the demo's TRUE bite.)
//! - `authority_violating_merge_refused_at_settlement` — a device sets a
//!   single-valued authority field offline using a credential the settlement tip
//!   has revoked; the gate REFUSES it (and accepts a sibling assignment whose
//!   credential is live). (The conservation/authority fragment: the FALSE bite.)
//!
//! Plus the discriminating controls (a gate that only ever accepts, or only ever
//! refuses, is vacuous): a live credential clears the gate; a same-value
//! concurrent authority assign is I-confluent and needs no gate at all.

use dregg_doc::{
    Author, History, Patch, Regime, content, merge,
};

// ─────────────────────────────────────────────────────────────────────────────
// The settlement view — the finalized-tip revocation registry (the keystone).
//
// `SettlementGate` mirrors `SettlementSoundness.lean`'s `settledRevView`: the
// set of credentials the settlement tip believes revoked. An authority field
// assignment carries the id of the credential under which the assigning device
// authored it; the gate honors the assignment iff that credential is NOT in the
// settlement-tip revocation set. This is authority evaluated AT SETTLEMENT, not
// at branch time — a credential live when the offline device used it but revoked
// by the settlement tip is refused.
// ─────────────────────────────────────────────────────────────────────────────

/// A device's authoring credential id (its branch-time authority token). The
/// `author: Author` the patch carries IS the on-substrate identity; we map each
/// device's author to its credential id 1:1 for the demo.
type CredentialId = u64;

/// The settlement view: the finalized-tip revocation set + the field-name set we
/// treat as **authority fields** (single-valued, conservation/authority regime —
/// `DOCUMENT-LANGUAGE.md` §2.4). A field NOT in this set is ordinary prose and
/// never gated.
struct SettlementGate {
    /// The `settledRevView`: credential ids revoked as of the settlement tip.
    /// (`SettlementSoundness.lean` §1: read at `(nSettle, tSettle)`.)
    revoked_at_settlement: Vec<CredentialId>,
    /// Which field names are authority/conservation fields (must clear the gate).
    authority_fields: Vec<String>,
    /// Maps a device's `Author` to the credential it authored under.
    cred_of_author: fn(Author) -> CredentialId,
}

/// The verdict of a stitch-at-settlement: either the settled merged content, or
/// a refusal naming the offending field + credential. The verdict IS the
/// verifiable receipt of the merge (the through-line's "receipt").
#[derive(Debug, PartialEq, Eq)]
enum StitchVerdict {
    /// The merge settled: the I-confluent parts unioned clean and every
    /// authority field assignment cleared the settlement gate. Carries the
    /// flat textual rendering (for inspection) and the count of surviving prose
    /// conflicts (benign first-class states, NOT failures).
    Settled {
        text: String,
        prose_conflicts: usize,
    },
    /// The merge was REFUSED at settlement: an authority field assignment was
    /// authored under a credential the settlement tip has revoked. Names the
    /// field and the revoked credential (the receipt of WHY).
    RefusedAtSettlement {
        field: String,
        revoked_credential: CredentialId,
    },
}

impl SettlementGate {
    /// Stitch `branch` into `main` and adjudicate at settlement.
    ///
    /// 1. **Merge (the pushout).** `History::stitch` unions the two folds — the
    ///    I-confluent fragment merges with no decision to make.
    /// 2. **The authority gate (`settledRevView`).** For each authority field,
    ///    every live assignment's credential must be honored at the settlement
    ///    tip; the first revoked one REFUSES the whole stitch (fail-closed — a
    ///    settlement either admits a sound transition or admits none).
    ///
    /// Returns the verdict; on refusal, `main` is left untouched (the door did
    /// not open — confinement holds).
    fn stitch_at_settlement(&self, main: &mut History, branch: &History) -> StitchVerdict {
        // Compute the candidate merge WITHOUT mutating main, so a refusal leaves
        // main's settled state intact (the branch's side-effects stay imaginary).
        let mut candidate = main.branch();
        let merged = candidate.stitch(branch);

        // The authority gate: read each authority field's live assignments and
        // honor them against the settlement-tip revocation view.
        for name in &self.authority_fields {
            for assign in merged.field(name) {
                let cred = (self.cred_of_author)(assign.provenance.author);
                if self.revoked_at_settlement.contains(&cred) {
                    return StitchVerdict::RefusedAtSettlement {
                        field: name.clone(),
                        revoked_credential: cred,
                    };
                }
            }
        }

        // Settled: commit the merge into main (the door opens) and report.
        let settled = main.stitch(branch);
        let rendered = content(&settled);
        let prose_conflicts = rendered
            .conflicts()
            .filter(|c| c.regime == Regime::Prose)
            .count();
        StitchVerdict::Settled {
            text: rendered.to_marked_string(),
            prose_conflicts,
        }
    }
}

/// Identity credential map: device author N authors under credential N.
fn cred_is_author(a: Author) -> CredentialId {
    a.0
}

// ─────────────────────────────────────────────────────────────────────────────
// A tiny two-device fixture: one shared genesis document, then two replicas.
// ─────────────────────────────────────────────────────────────────────────────

const DEVICE_A: Author = Author(1);
const DEVICE_B: Author = Author(2);

/// Build a shared base document both devices have synced, then hand back a
/// replica per device (each a `History::branch` of the shared base — the two
/// replicas share the genesis prefix and diverge from here while offline).
fn paired_devices(base_text_atoms: &[(u64, &str)]) -> (History, History) {
    let mut base = History::new();
    let mut prev = dregg_doc::AtomId::ROOT;
    for (seed, text) in base_text_atoms {
        let (id, op) = Patch::add(*seed, text, prev);
        base.commit(Patch::by(Author::SYSTEM, [op]));
        prev = id;
    }
    // Two devices, each holding a replica of the synced base.
    (base.branch(), base.branch())
}

/// The last atom id of a shared base (the tail both devices append after).
fn tail_of(base: &[(u64, &str)]) -> dregg_doc::AtomId {
    base.iter().fold(dregg_doc::AtomId::ROOT, |prev, (seed, text)| {
        let (id, _) = Patch::add(*seed, text, prev);
        id
    })
}

// ═════════════════════════════════════════════════════════════════════════════
// TRUE bite: concurrent COMPATIBLE offline edits merge CLEAN (I-confluent).
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn concurrent_compatible_edits_merge_clean() {
    let base = [(10u64, "shared "), (11u64, "note.")];
    let (mut device_a, mut device_b) = paired_devices(&base);
    let tail = tail_of(&base);

    // ── OFFLINE ── each device edits its own replica with the other unreachable.
    // Device A appends at a DISTINCT position (after the tail) ...
    let (_a_atom, a_op) = Patch::add(20, " [A: groceries]", tail);
    device_a.commit(Patch::by(DEVICE_A, [a_op]));
    // ... Device B appends at ANOTHER distinct position (after A-less tail too).
    // Concurrent + disjoint => the union has nothing to decide.
    let (_b_atom, b_op) = Patch::add(21, " [B: errands]", tail);
    device_b.commit(Patch::by(DEVICE_B, [b_op]));

    // ── ONLINE ── the stitch. Pure prose: no authority fields in play.
    let gate = SettlementGate {
        revoked_at_settlement: vec![],
        authority_fields: vec![],
        cred_of_author: cred_is_author,
    };
    let verdict = gate.stitch_at_settlement(&mut device_a, &device_b);

    // The merge SETTLED — both devices' offline work survives the union.
    match verdict {
        StitchVerdict::Settled { text, .. } => {
            assert!(text.contains("shared note."), "base survives: {text:?}");
            assert!(text.contains("[A: groceries]"), "device A survives: {text:?}");
            assert!(text.contains("[B: errands]"), "device B survives: {text:?}");
        }
        other => panic!("expected a clean settled stitch, got {other:?}"),
    }

    // And the merge is the SAME whichever direction we stitch (commutativity of
    // the pushout — the offline order does not matter). Cross-check via `merge`.
    let (mut a2, mut b2) = paired_devices(&base);
    a2.commit(Patch::by(DEVICE_A, [Patch::add(20, " [A: groceries]", tail).1]));
    b2.commit(Patch::by(DEVICE_B, [Patch::add(21, " [B: errands]", tail).1]));
    let ab = merge(&a2.stitch(&b2), &b2.replay());
    let ba = merge(&b2.replay(), &a2.replay());
    assert_eq!(
        content(&ab).to_marked_string(),
        content(&ba).to_marked_string(),
        "the stitch is direction-independent (pushout commutativity)"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// FALSE bite: an AUTHORITY-VIOLATING merge is REFUSED at settlement.
//
// Device B, while offline, reassigns a single-valued AUTHORITY field (the
// document's pinned "owner") under credential 2. By the time B comes online,
// credential 2 has been REVOKED at the settlement tip. Branch-time, B's edit was
// authorized; at settlement it is NOT — and the gate refuses it.
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn authority_violating_merge_refused_at_settlement() {
    let base = [(10u64, "doc")];
    let (mut device_a, mut device_b) = paired_devices(&base);

    // ── OFFLINE ── Device B grabs the authority field under credential 2.
    device_b.commit(Patch::by(
        DEVICE_B,
        [dregg_doc::Op::SetField {
            name: "owner".into(),
            value: "device-b".into(),
            superseding: false,
        }],
    ));

    // ── ONLINE ── but the settlement tip has REVOKED credential 2 in the
    // meantime (e.g. the device was reported lost; `#139` registry update read
    // at the finalized tip). Authority is evaluated AT SETTLEMENT.
    let gate = SettlementGate {
        revoked_at_settlement: vec![2], // credential 2 revoked at the settlement tip
        authority_fields: vec!["owner".into()],
        cred_of_author: cred_is_author,
    };
    let verdict = gate.stitch_at_settlement(&mut device_a, &device_b);

    // REFUSED — the branch-vs-settlement authority gap the keystone closes.
    assert_eq!(
        verdict,
        StitchVerdict::RefusedAtSettlement {
            field: "owner".into(),
            revoked_credential: 2,
        },
        "an authority field written under a settlement-revoked credential must be refused"
    );

    // Confinement holds: the refused branch did NOT touch main. Device A's
    // settled replica still carries NO owner assignment from B.
    assert!(
        device_a.replay().field("owner").is_empty(),
        "the refused stitch left main untouched (confinement)"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// DISCRIMINATING CONTROL #1 — the gate is not vacuously-refusing: the SAME
// authority edit clears settlement when its credential is LIVE at the tip.
// (Without this, "refused" could just mean "the gate always refuses".)
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn live_credential_clears_the_settlement_gate() {
    let base = [(10u64, "doc")];
    let (mut device_a, mut device_b) = paired_devices(&base);

    device_b.commit(Patch::by(
        DEVICE_B,
        [dregg_doc::Op::SetField {
            name: "owner".into(),
            value: "device-b".into(),
            superseding: false,
        }],
    ));

    // SAME edit, SAME field — but credential 2 is LIVE at the settlement tip.
    let gate = SettlementGate {
        revoked_at_settlement: vec![99], // some OTHER credential revoked; not 2
        authority_fields: vec!["owner".into()],
        cred_of_author: cred_is_author,
    };
    let verdict = gate.stitch_at_settlement(&mut device_a, &device_b);

    match verdict {
        StitchVerdict::Settled { .. } => {
            // The door opened: device A now sees B's owner assignment.
            let owner = device_a.replay();
            assert_eq!(owner.field("owner").len(), 1, "B's owner assign settled");
            assert_eq!(owner.field("owner")[0].value, "device-b");
        }
        other => panic!("a live credential must clear the gate, got {other:?}"),
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// DISCRIMINATING CONTROL #2 — a CONCURRENT authority field CLASH (two devices
// pick DIFFERENT owners offline) surfaces as a first-class `Regime::Field`
// conflict that the gate's authority check is the settlement-time arbiter of.
// Demonstrates the conservation/authority regime is genuinely non-monotone
// (NOT silently unioned like prose), and that the gate decides it per-credential.
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn concurrent_authority_clash_is_arbitrated_at_settlement() {
    let base = [(10u64, "doc")];
    let (mut device_a, mut device_b) = paired_devices(&base);

    // Both devices, offline, claim ownership with DIFFERENT values => a clash.
    device_a.commit(Patch::by(
        DEVICE_A,
        [dregg_doc::Op::SetField {
            name: "owner".into(),
            value: "device-a".into(),
            superseding: false,
        }],
    ));
    device_b.commit(Patch::by(
        DEVICE_B,
        [dregg_doc::Op::SetField {
            name: "owner".into(),
            value: "device-b".into(),
            superseding: false,
        }],
    ));

    // First, prove it IS a real (Field-regime) conflict, not a benign prose one.
    let merged = merge(&device_a.replay(), &device_b.replay());
    let rendered = content(&merged);
    let field_clashes: Vec<_> = rendered
        .conflicts()
        .filter(|c| c.regime == Regime::Field)
        .collect();
    assert_eq!(field_clashes.len(), 1, "the owner field is a real clash");
    assert!(
        Regime::Field.needs_consensus(),
        "an authority/conservation clash needs settlement arbitration, not unilateral merge"
    );

    // Now: the settlement tip has revoked DEVICE A's credential (1). The gate
    // refuses the whole stitch because A's losing claim is unauthorized at
    // settlement — the clash is arbitrated by current authority, not branch time.
    let gate = SettlementGate {
        revoked_at_settlement: vec![1],
        authority_fields: vec!["owner".into()],
        cred_of_author: cred_is_author,
    };
    let verdict = gate.stitch_at_settlement(&mut device_a.clone(), &device_b);
    assert_eq!(
        verdict,
        StitchVerdict::RefusedAtSettlement {
            field: "owner".into(),
            revoked_credential: 1,
        },
        "the clash is arbitrated against the settlement-tip revocation view"
    );
}

// ═════════════════════════════════════════════════════════════════════════════
// I-CONFLUENT control — two devices assign the SAME authority value offline.
// Single-valued field, same value => NO clash (the I-confluent case): the gate
// settles it with no arbitration needed. Proves the non-monotone field is only
// a conflict when the VALUES genuinely diverge.
// ═════════════════════════════════════════════════════════════════════════════

#[test]
fn same_value_authority_assign_is_iconfluent() {
    let base = [(10u64, "doc")];
    let (mut device_a, mut device_b) = paired_devices(&base);

    for (dev, who) in [(&mut device_a, DEVICE_A), (&mut device_b, DEVICE_B)] {
        dev.commit(Patch::by(
            who,
            [dregg_doc::Op::SetField {
                name: "owner".into(),
                value: "the-household".into(), // SAME value on both devices
                superseding: false,
            }],
        ));
    }

    let merged = merge(&device_a.replay(), &device_b.replay());
    assert_eq!(
        merged.field("owner").len(),
        1,
        "same value on both devices is I-confluent — a single live assignment, no clash"
    );

    // Because it is I-confluent (one surviving assignment, both devices agree),
    // settlement needs no arbitration: with no revocation in force the single
    // kept assignment clears the gate and settles. (Which provenance the union
    // keeps is decided by content-addressed patch-id order — a deterministic
    // detail of the union, NOT by who is live; the I-confluent claim is that
    // there is nothing to arbitrate, so an empty revocation view settles it.)
    let gate = SettlementGate {
        revoked_at_settlement: vec![],
        authority_fields: vec!["owner".into()],
        cred_of_author: cred_is_author,
    };
    let verdict = gate.stitch_at_settlement(&mut device_a, &device_b);
    match verdict {
        StitchVerdict::Settled { .. } => {
            // Exactly one owner value settled — the agreed one.
            let settled = device_a.replay();
            assert_eq!(settled.field("owner").len(), 1);
            assert_eq!(settled.field("owner")[0].value, "the-household");
        }
        other => panic!("an I-confluent same-value assign settles with nothing to arbitrate: {other:?}"),
    }
}
