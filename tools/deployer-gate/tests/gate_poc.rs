//! The deployer-gate PoC — both polarities, composing the REAL `dregg-macaroon`.
//!
//! GATED deployer (bond / interview-PASS / audit-cleared) → capability issues and
//! the launchpad authorizes the deploy. UNGATED deployer (no capability / forged
//! token / no bond / interview-FAIL / failed audit / slashed after issue /
//! expired / wrong scope) → REJECTED. Plus the private layer: authorization
//! reveals only "gated: true".

use std::collections::{HashMap, HashSet};

use dregg_deployer_gate::interview::InterviewVerdict;
use dregg_deployer_gate::private::{self, zktls::AttestedInterview};
use dregg_deployer_gate::{
    launch_params_hash, DeployRequest, DeployerGate, GateArm, GateContext, GateError,
};

const OPERATOR_ROOT_KEY: [u8; 32] = [7u8; 32];
const DEPLOYER: [u8; 32] = [42u8; 32];
const OTHER_DEPLOYER: [u8; 32] = [99u8; 32];
const NOW: i64 = 1_800_000_000;
const HORIZON: i64 = 1_900_000_000;
// Pins the operator's Opus-4.8 interview endpoint (cert+model hash, stand-in).
const ENDPOINT: &[u8] = b"opus-4-8@interview.launchpad.dregg.net";
const NONCE: [u8; 32] = [3u8; 32];

// The two REAL interview runs (Claude Opus 4.8, briefed hard-to-convince).
const VERDICT_LEGIT: &str = include_str!("../interview/runs/verdict-legit.txt");
const VERDICT_RUG: &str = include_str!("../interview/runs/verdict-rug.txt");

fn gate() -> DeployerGate {
    DeployerGate::new(
        OPERATOR_ROOT_KEY,
        "https://launchpad.dregg.net/deployer-gate",
    )
}

fn scope() -> [u8; 32] {
    launch_params_hash(b"Meridian Grid schedule: cap=10_000_000, sale=60%, team=15% locked")
}

// ─────────────────────────── (a) BOND ARM ────────────────────────────────────

#[test]
fn bond_arm_gated_deployer_is_authorized() {
    let mut ctx = GateContext::default();
    ctx.bonds.insert(DEPLOYER, 50_000_000_000_000_000_000); // 50 ETH staked

    let arm = GateArm::Bond {
        min_bond_wei: 10_000_000_000_000_000_000,
    }; // 10 ETH floor
    let cap = gate()
        .issue(DEPLOYER, arm, scope(), HORIZON, &ctx)
        .expect("gated: issues");

    let req = DeployRequest::new(NOW, &DEPLOYER, scope(), &ctx);
    assert!(
        gate().authorize_deploy(&cap, &req).is_ok(),
        "bonded deployer deploys"
    );
}

#[test]
fn bond_arm_ungated_deployer_gets_no_capability() {
    let ctx = GateContext::default(); // no bond posted
    let arm = GateArm::Bond {
        min_bond_wei: 10_000_000_000_000_000_000,
    };
    let err = gate()
        .issue(DEPLOYER, arm, scope(), HORIZON, &ctx)
        .unwrap_err();
    assert!(
        matches!(err, GateError::NotGated),
        "no bond => no capability, got {err:?}"
    );
}

#[test]
fn bond_slashed_after_issue_is_rejected_at_deploy() {
    // The live-recheck tooth: a capability issued when bonded is REJECTED once
    // the bond is slashed below the floor before the deploy is authorized.
    let mut ctx = GateContext::default();
    ctx.bonds.insert(DEPLOYER, 50_000_000_000_000_000_000);
    let arm = GateArm::Bond {
        min_bond_wei: 10_000_000_000_000_000_000,
    };
    let cap = gate()
        .issue(DEPLOYER, arm, scope(), HORIZON, &ctx)
        .expect("issues while bonded");

    // Slash the bond to 1 ETH (below the 10 ETH floor).
    ctx.bonds.insert(DEPLOYER, 1_000_000_000_000_000_000);
    let req = DeployRequest::new(NOW, &DEPLOYER, scope(), &ctx);
    let err = gate().authorize_deploy(&cap, &req).unwrap_err();
    assert!(
        matches!(err, GateError::CaveatRejected(_)),
        "slashed => rejected, got {err:?}"
    );
}

// ─────────────────────── (b) INTERVIEW ARM (marquee) ─────────────────────────

#[test]
fn interview_pass_issues_capability_and_authorizes() {
    let verdict = InterviewVerdict::parse(VERDICT_LEGIT).expect("parses");
    assert!(verdict.pass, "the skeptic PASSED the real project");
    assert!(verdict.confidence >= 0.8);

    // Operator admits the PASS commitment (attested) to the trusted set.
    let commitment = verdict
        .to_commitment(&NONCE, ENDPOINT)
        .expect("pass => commitment");
    let mut ctx = GateContext::default();
    ctx.trusted_interview_commitments.insert(commitment);

    let arm = GateArm::Interview {
        verdict_commitment: commitment,
    };
    let cap = gate()
        .issue(DEPLOYER, arm, scope(), HORIZON, &ctx)
        .expect("gated by interview");

    let req = DeployRequest::new(NOW, &DEPLOYER, scope(), &ctx);
    assert!(
        gate().authorize_deploy(&cap, &req).is_ok(),
        "passed-interview deployer deploys"
    );
}

#[test]
fn interview_fail_yields_no_capability() {
    let verdict = InterviewVerdict::parse(VERDICT_RUG).expect("parses");
    assert!(!verdict.pass, "the skeptic FAILED the rug");
    assert!(!verdict.scam_signals.is_empty(), "rug had scam signals");

    // A FAIL produces no admissible commitment.
    assert!(
        verdict.to_commitment(&NONCE, ENDPOINT).is_none(),
        "fail => no commitment"
    );

    // And even if a scammer fabricates an interview commitment, it is not in the
    // operator's trusted set, so issuance is refused.
    let forged = private::verdict_commitment(true, &[0xAB; 32], ENDPOINT);
    let ctx = GateContext::default(); // trusted set is empty of this commitment
    let arm = GateArm::Interview {
        verdict_commitment: forged,
    };
    let err = gate()
        .issue(DEPLOYER, arm, scope(), HORIZON, &ctx)
        .unwrap_err();
    assert!(
        matches!(err, GateError::NotGated),
        "untrusted commitment => NotGated, got {err:?}"
    );
}

#[test]
fn interview_attestation_revoked_after_issue_is_rejected() {
    let verdict = InterviewVerdict::parse(VERDICT_LEGIT).unwrap();
    let commitment = verdict.to_commitment(&NONCE, ENDPOINT).unwrap();
    let mut ctx = GateContext::default();
    ctx.trusted_interview_commitments.insert(commitment);
    let arm = GateArm::Interview {
        verdict_commitment: commitment,
    };
    let cap = gate().issue(DEPLOYER, arm, scope(), HORIZON, &ctx).unwrap();

    // Attestation revoked (e.g. the interview endpoint binding was found fake).
    ctx.trusted_interview_commitments.remove(&commitment);
    let req = DeployRequest::new(NOW, &DEPLOYER, scope(), &ctx);
    assert!(matches!(
        gate().authorize_deploy(&cap, &req).unwrap_err(),
        GateError::CaveatRejected(_)
    ));
}

// ─────────────────────────── (c) AUDIT ARM ───────────────────────────────────

#[test]
fn audit_cleared_is_authorized_and_failed_is_refused() {
    let report_hash = [0x5Au8; 32];
    let mut ctx = GateContext::default();
    ctx.audit_registry.insert(report_hash);

    let cap = gate()
        .issue(
            DEPLOYER,
            GateArm::Audit { report_hash },
            scope(),
            HORIZON,
            &ctx,
        )
        .expect("audit-cleared issues");
    let req = DeployRequest::new(NOW, &DEPLOYER, scope(), &ctx);
    assert!(gate().authorize_deploy(&cap, &req).is_ok());

    // A token whose audit did NOT clear (unknown report hash) gets no capability.
    let bad = [0xEEu8; 32];
    let err = gate()
        .issue(
            DEPLOYER,
            GateArm::Audit { report_hash: bad },
            scope(),
            HORIZON,
            &ctx,
        )
        .unwrap_err();
    assert!(matches!(err, GateError::NotGated));
}

// ─────────────────── FORGERY / TAMPER SOUNDNESS ──────────────────────────────

#[test]
fn forged_capability_without_root_key_is_rejected() {
    // An attacker mints their own macaroon with a guessed root key and stuffs in
    // an ArmCaveat claiming a satisfied bond. Without the operator's root key the
    // HMAC chain cannot match — the real gate rejects it. This is the soundness
    // core: a capability is unforgeable without the issuing key.
    use dregg_macaroon::Macaroon;
    let attacker_key = [0xFFu8; 32];
    let mut forged = Macaroon::new(&attacker_key, DEPLOYER.to_vec(), "evil".into());
    forged.add_first_party(&dregg_deployer_gate::ScopeCaveat {
        launch_params_hash: scope(),
    });
    forged.add_first_party(&dregg_deployer_gate::ArmCaveat {
        arm: GateArm::Bond { min_bond_wei: 0 },
    });
    forged.add_first_party(&dregg_deployer_gate::ExpiryCaveat { not_after: HORIZON });

    // Even with a context that would satisfy the arm, verification fails first.
    let mut ctx = GateContext::default();
    ctx.bonds.insert(DEPLOYER, u128::MAX);
    let req = DeployRequest::new(NOW, &DEPLOYER, scope(), &ctx);
    assert!(matches!(
        gate().authorize_deploy(&forged, &req).unwrap_err(),
        GateError::BadCapability(_)
    ));
}

#[test]
fn capability_from_wrong_operator_is_rejected() {
    // A capability legitimately issued by a DIFFERENT operator (different root
    // key) does not authorize against this operator's gate.
    let other_gate = DeployerGate::new([1u8; 32], "other-launchpad");
    let mut ctx = GateContext::default();
    ctx.bonds.insert(DEPLOYER, u128::MAX);
    let cap = other_gate
        .issue(
            DEPLOYER,
            GateArm::Bond { min_bond_wei: 0 },
            scope(),
            HORIZON,
            &ctx,
        )
        .unwrap();
    let req = DeployRequest::new(NOW, &DEPLOYER, scope(), &ctx);
    assert!(matches!(
        gate().authorize_deploy(&cap, &req).unwrap_err(),
        GateError::BadCapability(_)
    ));
}

// ─────────────────── SCOPE / EXPIRY / ATTENUATION ────────────────────────────

#[test]
fn capability_for_a_different_launch_is_rejected() {
    let mut ctx = GateContext::default();
    ctx.audit_registry.insert([0x5A; 32]);
    let cap = gate()
        .issue(
            DEPLOYER,
            GateArm::Audit {
                report_hash: [0x5A; 32],
            },
            scope(),
            HORIZON,
            &ctx,
        )
        .unwrap();

    // Present it to deploy a DIFFERENT launch (different params hash).
    let other_scope = launch_params_hash(b"a totally different token schedule");
    let req = DeployRequest::new(NOW, &DEPLOYER, other_scope, &ctx);
    assert!(matches!(
        gate().authorize_deploy(&cap, &req).unwrap_err(),
        GateError::CaveatRejected(_)
    ));
}

#[test]
fn expired_capability_is_rejected() {
    let mut ctx = GateContext::default();
    ctx.audit_registry.insert([0x5A; 32]);
    let past = NOW - 1;
    let cap = gate()
        .issue(
            DEPLOYER,
            GateArm::Audit {
                report_hash: [0x5A; 32],
            },
            scope(),
            past,
            &ctx,
        )
        .unwrap();
    let req = DeployRequest::new(NOW, &DEPLOYER, scope(), &ctx);
    assert!(matches!(
        gate().authorize_deploy(&cap, &req).unwrap_err(),
        GateError::CaveatRejected(_)
    ));
}

#[test]
fn attenuation_only_restricts_never_expands() {
    // The deployer receives a capability valid until HORIZON and ATTENUATES it
    // (adds a tighter expiry) before delegating. The tighter bound binds; the
    // caveat can only restrict. Caveats cannot be removed — the HMAC chain would
    // break (covered by the forgery test).
    let mut ctx = GateContext::default();
    ctx.audit_registry.insert([0x5A; 32]);
    let mut cap = gate()
        .issue(
            DEPLOYER,
            GateArm::Audit {
                report_hash: [0x5A; 32],
            },
            scope(),
            HORIZON,
            &ctx,
        )
        .unwrap();

    let tighter = NOW + 10;
    cap.add_first_party(&dregg_deployer_gate::ExpiryCaveat { not_after: tighter });

    // Before the tighter expiry: still valid.
    let ok_req = DeployRequest::new(NOW, &DEPLOYER, scope(), &ctx);
    assert!(gate().authorize_deploy(&cap, &ok_req).is_ok());

    // After the tighter expiry (but before HORIZON): the attenuation binds.
    let late_req = DeployRequest::new(tighter + 1, &DEPLOYER, scope(), &ctx);
    assert!(matches!(
        gate().authorize_deploy(&cap, &late_req).unwrap_err(),
        GateError::CaveatRejected(_)
    ));
}

// ─────────────────── PRIVATE LAYER (reveal-nothing) ──────────────────────────

#[test]
fn authorization_reveals_only_gated_bit() {
    // The gate's whole view of an interview-gated deploy is one bit: membership.
    let verdict = InterviewVerdict::parse(VERDICT_LEGIT).unwrap();
    let commitment = verdict.to_commitment(&NONCE, ENDPOINT).unwrap();
    let mut trusted = HashSet::new();
    trusted.insert(commitment);

    assert!(
        private::membership_only_reveals_gated(&trusted, &commitment),
        "gated: true"
    );

    // A different (untrusted) commitment: the gate learns only "false" — nothing
    // about the interview or the presenter.
    let other = private::verdict_commitment(true, &[0x11; 32], ENDPOINT);
    assert!(!private::membership_only_reveals_gated(&trusted, &other));

    // The FAIL verdict never even produces an admissible commitment.
    let rug = InterviewVerdict::parse(VERDICT_RUG).unwrap();
    assert!(rug.to_commitment(&NONCE, ENDPOINT).is_none());
}

#[test]
fn zktls_attested_interview_admissible_only_on_pass() {
    let good = AttestedInterview {
        endpoint_binding: ENDPOINT.to_vec(),
        verdict_field: "PASS".into(),
        content_commitment: [1u8; 32],
    };
    let bad = AttestedInterview {
        endpoint_binding: ENDPOINT.to_vec(),
        verdict_field: "FAIL".into(),
        content_commitment: [2u8; 32],
    };
    assert!(good.is_admissible());
    assert!(!bad.is_admissible());
}

// Silence unused-import lint on OTHER_DEPLOYER/HashMap kept for readability.
#[allow(dead_code)]
fn _uses() {
    let _ = OTHER_DEPLOYER;
    let _: HashMap<[u8; 32], u128> = HashMap::new();
}
