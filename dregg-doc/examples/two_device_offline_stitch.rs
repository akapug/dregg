//! Two-device offline-then-stitch — the cross-device firmament, end to end, headless.
//!
//! THE THROUGH-LINE: a turn is the exercise of an attenuable proof-carrying token
//! over owned state, leaving a verifiable receipt. Here each "turn" is a patch; the
//! "owned state" is a per-device document replica; and the "verifiable receipt" is
//! the stitch verdict (a clean settlement, or a refusal at settlement).
//!
//! This is a RUNNABLE driver (`cargo run --example two_device_offline_stitch`), not
//! a test harness. It narrates the full lifecycle the cross-device firmament scopes
//! (`docs/deos/CROSS-DEVICE-FIRMAMENT.md` §2.4, `BRANCH-AND-STITCH-PROTOCOL.md`):
//!
//!   shared image  ──►  device goes OFFLINE (a confined Virtual branch)
//!                 ──►  edits offline (side-effects structurally IMAGINARY)
//!                 ──►  device comes back ONLINE
//!                 ──►  STITCH: I-confluent parts union clean, the settlement gate
//!                              adjudicates the non-monotone (authority) parts.
//!
//! It fuses the TWO halves the in-tree organs each model separately, into one
//! end-to-end walk over two in-memory replicas:
//!
//!   1. THE CONFINEMENT TOOTH (offline = a Virtual branch, side-effects imaginary).
//!      The operable shadow of `Dregg2.Deos.BranchStitch.branch_cannot_drain_main`
//!      (= `Confinement.confined_cannot_debit_attacker`): an offline device holds no
//!      cap to settled-main value it has not seen, so a debit of a main cell while
//!      offline is REFUSED by the gate and stays imaginary until a deliberate stitch.
//!      Mirrors `starbridge-v2/src/branch_stitch.rs::VirtualBranch` (re-homed locally
//!      so this example rides only the standalone dregg-doc crate — no cross-workspace
//!      dep; the Lean keystone is the authority, this is its operable face).
//!
//!   2. THE STITCH (I-confluent union + the Settlement Soundness gate). The document
//!      merge IS the pushout (`dregg_doc::merge`, Mimram–Di Giusto); the I-confluent
//!      / monotone prose merges with NO decision; an authority field is gated at the
//!      SETTLEMENT tip (`metatheory/Dregg2/Circuit/SettlementSoundness.lean`'s
//!      `settledRevView`) — authority read at settlement, NOT at branch time.
//!
//! BOTH POLARITIES (the standing law: bite TRUE and bite FALSE, never vacuous):
//!   ✓ ACT  — concurrent COMPATIBLE offline edits + a live-credential authority claim
//!            merge CLEAN and SETTLE; both devices' offline work survives.
//!   ✗ REFUSE — an authority field written offline under a credential the settlement
//!            tip has REVOKED is refused at settlement; main is left untouched
//!            (confinement holds). And an offline debit of an unseen main cell was
//!            imaginary all along (the confinement tooth).
//!
//! Plus the discriminating controls baked into the run (a gate that only-accepts or
//! only-refuses is vacuous): the SAME authority edit under a LIVE credential clears
//! the gate; an UN-confined "offline" branch (holding a debit-cap it should not) CAN
//! drain main — proving the confinement hypothesis is load-bearing.
//!
//! Exit code 0 iff every checkpoint held. The driver is its own oracle.

use dregg_doc::{Author, History, Op, Patch, Regime, content, merge};
use std::collections::BTreeSet;

// ═════════════════════════════════════════════════════════════════════════════
// PART 1 — the confinement tooth: an offline branch is structurally imaginary.
//
// Re-homed from `starbridge-v2/src/branch_stitch.rs::VirtualBranch` so the example
// needs only the standalone dregg-doc crate. Same vocabulary, same teeth; the Lean
// `BranchStitch.branch_cannot_drain_main` is the authority this mirrors.
// ═════════════════════════════════════════════════════════════════════════════

/// A capability the offline device holds: a target cell and whether it confers
/// debit (drain) reach to it. The shadow of `Confinement.reachesCell`.
#[derive(Clone, Debug)]
struct Cap {
    target: u64,
    debit_reach: bool,
}

/// The MAIN frontier: the cells belonging to settled, official reality — the cells
/// an offline branch must be confined away from (`Confinement.attackerFrontier`,
/// with the offline branch as the "attacker").
type MainFrontier = BTreeSet<u64>;

/// An offline device, as a confined Virtual branch off the last shared cursor.
/// It holds ONLY branch-caps; honest confinement = it owns no main cell and reaches
/// none by a debit-cap, so its side-effects on main are structurally imaginary.
struct OfflineBranch {
    author: u64,
    main: MainFrontier,
    caps: Vec<Cap>,
}

impl OfflineBranch {
    /// `BranchHonest M caps author` (= `Confinement.Confined`): the author is not a
    /// main cell AND reaches no main cell via a debit-cap.
    fn confined(&self) -> bool {
        if self.main.contains(&self.author) {
            return false;
        }
        !self
            .caps
            .iter()
            .any(|c| c.debit_reach && self.main.contains(&c.target))
    }

    /// The no-drain tooth (`branch_cannot_drain_main`): would the kernel gate admit
    /// this offline device's debit of `src`? A confined branch may debit a cell it
    /// owns or reaches off-main, but NEVER a main cell.
    fn admits_debit(&self, src: u64) -> bool {
        if self.confined() && self.main.contains(&src) {
            return false; // confined + main src ⇒ imaginary
        }
        if src == self.author {
            return true;
        }
        self.caps.iter().any(|c| c.debit_reach && c.target == src)
    }

    /// True iff debiting `src` while offline is STRUCTURALLY IMAGINARY: it targets
    /// main yet the gate refuses it. "The errors remain imaginary" as a cap fact.
    fn debit_is_imaginary(&self, src: u64) -> bool {
        self.main.contains(&src) && !self.admits_debit(src)
    }
}

// ═════════════════════════════════════════════════════════════════════════════
// PART 2 — the settlement gate: authority adjudicated at the settlement tip.
//
// Mirrors `SettlementSoundness.lean`'s `settledRevView`: an authority field
// assignment carries the credential the device authored it under; the gate honors
// it iff that credential is NOT revoked AT THE SETTLEMENT TIP — branch-time
// authority does not count.
// ═════════════════════════════════════════════════════════════════════════════

type CredentialId = u64;

struct SettlementGate {
    /// `settledRevView`: credential ids revoked as of the settlement tip.
    revoked_at_settlement: Vec<CredentialId>,
    /// Field names that are authority/conservation fields (must clear the gate).
    authority_fields: Vec<String>,
}

/// The verdict of a stitch-at-settlement — the verifiable receipt of the merge.
#[derive(Debug, PartialEq, Eq)]
enum StitchVerdict {
    /// The merge settled: I-confluent parts unioned clean, every authority field
    /// cleared the gate. Carries the flat rendering and the count of benign prose
    /// conflicts (first-class states, NOT failures).
    Settled {
        text: String,
        prose_conflicts: usize,
    },
    /// REFUSED at settlement: an authority field was authored under a credential the
    /// settlement tip has revoked. Names the field + the revoked credential (WHY).
    RefusedAtSettlement {
        field: String,
        revoked_credential: CredentialId,
    },
}

impl SettlementGate {
    /// Stitch `branch` into `main` and adjudicate at settlement. On refusal, `main`
    /// is left untouched (the door did not open — confinement holds).
    ///
    /// Device author N authors under credential N (identity map for the demo).
    fn stitch_at_settlement(&self, main: &mut History, branch: &History) -> StitchVerdict {
        // Compute the candidate merge WITHOUT mutating main, so a refusal leaves
        // main's settled state intact (the branch's side-effects stay imaginary).
        let mut candidate = main.branch();
        let merged = candidate.stitch(branch);

        for name in &self.authority_fields {
            for assign in merged.field(name) {
                let cred = assign.provenance.author.0; // credential = author id
                if self.revoked_at_settlement.contains(&cred) {
                    return StitchVerdict::RefusedAtSettlement {
                        field: name.clone(),
                        revoked_credential: cred,
                    };
                }
            }
        }

        // Settled: the door opens — commit the merge into main and report.
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

// ═════════════════════════════════════════════════════════════════════════════
// The two-device fixture: one shared genesis image, then a replica per device.
// ═════════════════════════════════════════════════════════════════════════════

const DEVICE_A: Author = Author(1); // the laptop (credential 1)
const DEVICE_B: Author = Author(2); // the phone  (credential 2)

/// Build a shared base image both devices have synced, then hand back a replica per
/// device (each a `History::branch` of the shared base — sharing the genesis prefix,
/// diverging from here while offline). Returns the replicas + the tail atom id.
fn paired_devices(base: &[(u64, &str)]) -> (History, History, dregg_doc::AtomId) {
    let mut img = History::new();
    let mut prev = dregg_doc::AtomId::ROOT;
    for (seed, text) in base {
        let (id, op) = Patch::add(*seed, text, prev);
        img.commit(Patch::by(Author::SYSTEM, [op]));
        prev = id;
    }
    (img.branch(), img.branch(), prev)
}

// ── tiny check harness: every checkpoint prints and tallies ──────────────────────

struct Run {
    pass: u32,
    fail: u32,
}
impl Run {
    fn check(&mut self, label: &str, ok: bool) {
        if ok {
            self.pass += 1;
            println!("   ✓ {label}");
        } else {
            self.fail += 1;
            println!("   ✗ FAILED: {label}");
        }
    }
}

fn main() {
    let mut run = Run { pass: 0, fail: 0 };
    println!("two-device offline-then-stitch — the cross-device firmament, headless\n");

    // ─────────────────────────────────────────────────────────────────────────
    // ACT I — the confinement tooth: offline edits are structurally imaginary.
    //
    // The phone (device B) goes offline. Its offline branch is confined away from
    // the settled-main frontier {100, 101} (cells it holds no cap to). It tries to
    // debit a main cell — and that debit is IMAGINARY (the gate refuses it), so it
    // can never corrupt official reality. Meanwhile it CAN spend its own branch
    // value (real, branch-local).
    // ─────────────────────────────────────────────────────────────────────────
    println!("ACT I  the phone goes offline — its side-effects on main are imaginary");
    let main_frontier: MainFrontier = [100u64, 101u64].into_iter().collect();
    let phone_offline = OfflineBranch {
        author: 7, // the phone's branch-author cell, distinct from any main cell
        main: main_frontier.clone(),
        caps: vec![Cap {
            target: 9,
            debit_reach: true,
        }], // a cap to a BRANCH cell only
    };
    run.check(
        "offline phone is confined (owns no main cell, reaches none)",
        phone_offline.confined(),
    );
    run.check(
        "offline debit of a main cell (100) is IMAGINARY — never reaches official reality",
        phone_offline.debit_is_imaginary(100),
    );
    run.check(
        "offline phone CAN spend its own branch value (9) — branch-local, real",
        phone_offline.admits_debit(9),
    );

    // The load-bearing control: drop confinement (an un-confined "offline" branch
    // illicitly holding a debit-cap to main cell 100). NOW the same debit IS
    // admitted — proving confinement is the hypothesis that makes the tooth bite.
    let phone_unconfined = OfflineBranch {
        author: 7,
        main: main_frontier.clone(),
        caps: vec![Cap {
            target: 100,
            debit_reach: true,
        }], // reaches MAIN ⇒ NOT confined
    };
    run.check(
        "control: an UN-confined branch is not confined (load-bearing hypothesis)",
        !phone_unconfined.confined(),
    );
    run.check(
        "control: an un-confined branch CAN drain main (the tooth is non-vacuous)",
        phone_unconfined.admits_debit(100) && !phone_unconfined.debit_is_imaginary(100),
    );

    // ─────────────────────────────────────────────────────────────────────────
    // ACT II — the clean stitch (ACCEPT polarity): concurrent compatible edits.
    //
    // Both devices edit offline at DISTINCT positions (disjoint prose). Coming back
    // online, the stitch unions them with NOTHING to decide (the I-confluent
    // fragment) — both devices' offline work survives. No authority fields in play.
    // ─────────────────────────────────────────────────────────────────────────
    println!("\nACT II  both devices edit offline, then reconcile — I-confluent CLEAN merge");
    let base = [(10u64, "shared "), (11u64, "note.")];
    let (mut device_a, mut device_b, tail) = paired_devices(&base);

    // OFFLINE: each device appends disjoint prose after the shared tail.
    device_a.commit(Patch::by(
        DEVICE_A,
        [Patch::add(20, " [A: groceries]", tail).1],
    ));
    device_b.commit(Patch::by(
        DEVICE_B,
        [Patch::add(21, " [B: errands]", tail).1],
    ));

    // ONLINE: the stitch. Pure prose — no authority fields.
    let gate = SettlementGate {
        revoked_at_settlement: vec![],
        authority_fields: vec![],
    };
    let verdict = gate.stitch_at_settlement(&mut device_a, &device_b);
    match &verdict {
        StitchVerdict::Settled { text, .. } => {
            println!("   settled image: {text:?}");
            run.check("base survives the union", text.contains("shared note."));
            run.check(
                "device A's offline work survives",
                text.contains("[A: groceries]"),
            );
            run.check(
                "device B's offline work survives",
                text.contains("[B: errands]"),
            );
        }
        other => run.check(
            &format!("expected a clean settled stitch, got {other:?}"),
            false,
        ),
    }

    // The stitch is direction-independent (pushout commutativity — offline order is
    // irrelevant). Cross-check by merging both directions.
    let (mut a2, mut b2, t2) = paired_devices(&base);
    a2.commit(Patch::by(
        DEVICE_A,
        [Patch::add(20, " [A: groceries]", t2).1],
    ));
    b2.commit(Patch::by(DEVICE_B, [Patch::add(21, " [B: errands]", t2).1]));
    let ab = merge(&a2.replay(), &b2.replay());
    let ba = merge(&b2.replay(), &a2.replay());
    run.check(
        "the stitch is direction-independent (pushout commutativity)",
        content(&ab).to_marked_string() == content(&ba).to_marked_string(),
    );

    // ─────────────────────────────────────────────────────────────────────────
    // ACT III — the settlement gate ACCEPTS a live-credential authority claim.
    //
    // The discriminating ACCEPT control for the authority axis: device B sets a
    // single-valued authority field offline, and its credential is LIVE at the
    // settlement tip — so the gate opens the door (main now carries B's assignment).
    // Without this, "refused" below could just mean "the gate always refuses".
    // ─────────────────────────────────────────────────────────────────────────
    println!("\nACT III  an authority claim under a LIVE credential clears settlement");
    let abase = [(10u64, "doc")];
    let (mut a3, mut b3, _) = paired_devices(&abase);
    b3.commit(Patch::by(
        DEVICE_B,
        [Op::SetField {
            name: "owner".into(),
            value: "device-b".into(),
            superseding: false,
        }],
    ));
    let gate_live = SettlementGate {
        revoked_at_settlement: vec![99], // some OTHER credential revoked — NOT 2
        authority_fields: vec!["owner".into()],
    };
    let verdict = gate_live.stitch_at_settlement(&mut a3, &b3);
    run.check(
        "live-credential authority claim SETTLES (gate is non-vacuous)",
        matches!(verdict, StitchVerdict::Settled { .. }),
    );
    let owner = a3.replay();
    run.check(
        "the door opened: main now carries B's owner assignment",
        owner.field("owner").len() == 1 && owner.field("owner")[0].value == "device-b",
    );

    // ─────────────────────────────────────────────────────────────────────────
    // ACT IV — the settlement gate REFUSES (REFUSE polarity): the keystone bite.
    //
    // Device B sets the SAME authority field offline under credential 2 — but by the
    // time it reconnects, credential 2 has been REVOKED at the settlement tip (e.g.
    // the phone was reported lost). Branch-time the edit was authorized; AT
    // SETTLEMENT it is not — the gate refuses, and main is left untouched.
    // This is the branch-vs-settlement authority gap SettlementSoundness closes.
    // ─────────────────────────────────────────────────────────────────────────
    println!("\nACT IV  an authority claim under a SETTLEMENT-REVOKED credential is REFUSED");
    let (mut a4, mut b4, _) = paired_devices(&abase);
    b4.commit(Patch::by(
        DEVICE_B,
        [Op::SetField {
            name: "owner".into(),
            value: "device-b".into(),
            superseding: false,
        }],
    ));
    let gate_revoked = SettlementGate {
        revoked_at_settlement: vec![2], // credential 2 revoked AT THE SETTLEMENT TIP
        authority_fields: vec!["owner".into()],
    };
    let verdict = gate_revoked.stitch_at_settlement(&mut a4, &b4);
    println!("   verdict: {verdict:?}");
    run.check(
        "authority under a settlement-revoked credential is REFUSED at settlement",
        verdict
            == StitchVerdict::RefusedAtSettlement {
                field: "owner".into(),
                revoked_credential: 2,
            },
    );
    run.check(
        "confinement holds: the refused stitch left main untouched (no owner from B)",
        a4.replay().field("owner").is_empty(),
    );

    // ─────────────────────────────────────────────────────────────────────────
    // ACT V — a concurrent authority CLASH is a real (non-monotone) conflict, and
    // it is arbitrated at the settlement tip — NOT silently unioned like prose.
    // ─────────────────────────────────────────────────────────────────────────
    println!("\nACT V  a concurrent authority clash is non-monotone — arbitrated at settlement");
    let (mut a5, mut b5, _) = paired_devices(&abase);
    a5.commit(Patch::by(
        DEVICE_A,
        [Op::SetField {
            name: "owner".into(),
            value: "device-a".into(),
            superseding: false,
        }],
    ));
    b5.commit(Patch::by(
        DEVICE_B,
        [Op::SetField {
            name: "owner".into(),
            value: "device-b".into(),
            superseding: false,
        }],
    ));
    let merged = merge(&a5.replay(), &b5.replay());
    let field_clashes = content(&merged)
        .conflicts()
        .filter(|c| c.regime == Regime::Field)
        .count();
    run.check(
        "the owner field is a REAL non-monotone clash (Regime::Field, needs consensus)",
        field_clashes == 1 && Regime::Field.needs_consensus(),
    );
    // Arbitrate: the settlement tip has revoked device A's credential (1), so A's
    // losing claim is unauthorized at settlement — the whole stitch is refused.
    let gate_clash = SettlementGate {
        revoked_at_settlement: vec![1],
        authority_fields: vec!["owner".into()],
    };
    let verdict = gate_clash.stitch_at_settlement(&mut a5.branch(), &b5);
    run.check(
        "the clash is arbitrated by the settlement-tip revocation view (A revoked ⇒ refused)",
        verdict
            == StitchVerdict::RefusedAtSettlement {
                field: "owner".into(),
                revoked_credential: 1,
            },
    );

    // ─────────────────────────────────────────────────────────────────────────
    println!("\n────────────────────────────────────────────────────────");
    println!("checkpoints: {} passed, {} failed", run.pass, run.fail);
    if run.fail == 0 {
        println!("ALL GREEN — offline divergence stitched soundly, both polarities bit.");
        println!("\n   one cap, two devices — the distance is just n;");
        println!("   go dark on the train, come home, and stitch it back again. ( ◕‿◕ )");
    } else {
        eprintln!("\nFAILED — {} checkpoint(s) did not hold.", run.fail);
        std::process::exit(1);
    }
}
