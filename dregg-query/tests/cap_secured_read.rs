//! CAP-SECURED STORE — the ATTESTED READ FACE (the dregg-query first slice).
//!
//! The cap-secured store (`docs/deos/DREGG-DATA-STORE.md`) has two trust legs:
//!
//!   * the WRITE/ROW leg (pg-dregg RLS): a row a token cannot cap-reach is
//!     INVISIBLE — the kernel decision filters it out per row;
//!   * the READ leg (dregg-query, this test): a query over the receipt
//!     fact-base cannot SILENTLY OMIT rows it should return. The answer carries
//!     a non-omission certificate — a range opening against the receipt-log MMR
//!     root — so a verifier re-derives the answer from EXACTLY the committed
//!     receipt range. The server is trusted for nothing but availability.
//!
//! The two compose into the one trust story: RLS controls what you are
//! ALLOWED to see; the certificate proves that, of what you are allowed to see,
//! NOTHING was hidden. A cap-secured store that could silently drop rows from a
//! query answer would be no better than a hand-rolled SQL view.
//!
//! This slice proves, over a synthetic receipt chain (the deos app's verified
//! turn history):
//!   1. an attested conjunctive read returns rows + a verifying certificate;
//!   2. the CALM grade rides along (monotone vs finalized-dependent);
//!   3. a server that OMITS a qualifying row is CAUGHT (the answer no longer
//!      matches the re-derivation, or the certificate fails) — non-omission;
//!   4. the certificate survives serde (it crosses the wire to the verifier).

use dregg_query::*;

/// A synthetic 32-byte receipt hash (stands in for `TurnReceipt::receipt_hash`).
fn rhash(i: u64) -> [u8; 32] {
    *blake3::hash(format!("cap-store-receipt-{i}").as_bytes()).as_bytes()
}

fn record(i: u64, height: u64, agent: &str, effects: Vec<EffectSummary>) -> ReceiptRecord {
    ReceiptRecord {
        chain_index: i,
        receipt_hash: hex::encode(rhash(i)),
        height,
        agent: agent.to_string(),
        effects,
    }
}

/// A deos app's verified turn history: grants and a revocation across two
/// tenants. The canonical cap-secured-store query is "who currently holds a
/// capability" = `granted ∧ ¬revoked` — a FINALIZED-DEPENDENT query (a later
/// revocation can retract a row), which is exactly what the CALM grade flags.
fn history() -> Vec<ReceiptRecord> {
    vec![
        record(0, 1, "org42", vec![EffectSummary::Created {
            agent: "org42".into(),
            cell: "doc-a".into(),
        }]),
        record(1, 2, "org42", vec![EffectSummary::Granted {
            from: "org42".into(),
            to: "alice".into(),
            cap: "read-doc-a".into(),
        }]),
        record(2, 3, "org42", vec![EffectSummary::Granted {
            from: "org42".into(),
            to: "bob".into(),
            cap: "read-doc-b".into(),
        }]),
        record(3, 4, "org99", vec![EffectSummary::Granted {
            from: "org99".into(),
            to: "carol".into(),
            cap: "read-doc-c".into(),
        }]),
        // bob's cap is later revoked — the finalized-dependent retraction.
        record(4, 5, "org42", vec![EffectSummary::Revoked {
            cap: "read-doc-b".into(),
        }]),
    ]
}

fn mmr_of(receipts: &[ReceiptRecord]) -> Mmr<Blake3Mmr> {
    let mut m = Mmr::new(Blake3Mmr);
    for r in receipts {
        m.push(r.receipt_hash_bytes().unwrap());
    }
    m
}

/// Build a certified slice over the whole receipt log `[0, len-1]`.
fn whole_log_slice(receipts: &[ReceiptRecord]) -> (AttestedSlice, [u8; 32]) {
    let m = mmr_of(receipts);
    let root = m.root();
    let hi = receipts.len() as u64 - 1;
    let (_vals, opening) = m.open_range(0, hi);
    let slice = AttestedSlice {
        receipts: receipts.to_vec(),
        cert: RangeCertificate { root, lo: 0, hi, opening },
    };
    (slice, root)
}

/// The cap-secured-store read: "which capabilities are currently HELD" =
/// `granted(_, Holder, Cap, _) ∧ ¬revoked(Cap, _)`.
fn caps_currently_held() -> Query {
    Query::new()
        .atom(Pred::Granted, vec![Term::Wild, Term::var("Holder"), Term::var("Cap"), Term::Wild])
        .not_atom(Pred::Revoked, vec![Term::var("Cap"), Term::Wild])
}

#[test]
fn attested_read_returns_rows_with_a_verifying_certificate() {
    let receipts = history();
    let (slice, trusted_root) = whole_log_slice(&receipts);

    // Over the whole verified history, the answer is the unqualified
    // "provably omitted nothing" claim for this query.
    let ans = answer_whole_log(slice, caps_currently_held()).unwrap();

    // The certificate verifies against the trusted root: the answer was computed
    // from EXACTLY positions [0, 4] of the genuine receipt log.
    ans.verify(&Blake3Mmr, &trusted_root)
        .expect("the attested read must verify against the receipt-log root");

    // alice + carol hold caps; bob's was revoked. The held set is exactly those
    // two — the not_atom prunes the revoked one.
    let holders: Vec<String> = ans
        .rows
        .iter()
        .map(|r| match r.get("Holder").unwrap() {
            Value::Sym(s) => s.clone(),
            v => panic!("Holder bound to a non-symbol: {v:?}"),
        })
        .collect();
    assert_eq!(holders.len(), 2, "exactly two caps are currently held");
    assert!(holders.contains(&"alice".to_string()));
    assert!(holders.contains(&"carol".to_string()));
    assert!(!holders.contains(&"bob".to_string()), "bob's revoked cap must be pruned");
}

#[test]
fn the_calm_grade_flags_the_finalized_dependence() {
    // `granted ∧ ¬revoked` is FINALIZED-DEPENDENT: a later revocation retracts a
    // row, so the answer is only "fresh as of" the certified height frontier.
    // The cap-secured store SURFACES this — a consumer knows the row is not
    // unconditionally final, which a hand-rolled SQL view would not tell it.
    let receipts = history();
    let (slice, _root) = whole_log_slice(&receipts);
    let ans = answer_whole_log(slice, caps_currently_held()).unwrap();
    assert_eq!(
        ans.classification.class,
        CoordinationClass::FinalizedDependent,
        "a query with a negated atom must be graded finalized-dependent"
    );
    // The freshness frontier is the max height of the certified slice (height 5,
    // the revocation receipt): the answer is correct AS OF height 5.
    assert_eq!(ans.fresh_as_of, 5, "the answer is fresh as of the revocation height");

    // A purely-positive query (no negation) is MONOTONE — its rows are final.
    let ever_granted = Query::new().atom(
        Pred::Granted,
        vec![Term::Wild, Term::var("Holder"), Term::var("Cap"), Term::Wild],
    );
    let (slice2, _r2) = whole_log_slice(&receipts);
    let mono = answer_whole_log(slice2, ever_granted).unwrap();
    assert_eq!(
        mono.classification.class,
        CoordinationClass::Monotone,
        "a positive conjunctive query is monotone — its rows are final"
    );
}

#[test]
fn a_server_that_omits_a_row_is_caught() {
    // THE NON-OMISSION TEETH. A dishonest server tries to HIDE a granted cap —
    // it drops alice's grant receipt (position 1) from the slice it serves but
    // keeps the certificate's claimed range [0, 4]. The verifier must reject it.
    let receipts = history();
    let (honest_slice, trusted_root) = whole_log_slice(&receipts);

    // The honest answer verifies and includes alice.
    let honest = answer_whole_log(honest_slice, caps_currently_held()).unwrap();
    honest.verify(&Blake3Mmr, &trusted_root).unwrap();
    assert!(honest.rows.iter().any(|r| matches!(
        r.get("Holder"),
        Some(Value::Sym(s)) if s == "alice"
    )));

    // Now the server omits receipt position 1 (alice's grant) but ships the SAME
    // certificate claiming positions [0, 4]. The receipts no longer fill the
    // dense range, so the slice's own certificate verification fails (the opened
    // positions do not match the certified dense range / the count is wrong).
    let mut tampered = receipts.clone();
    tampered.remove(1); // drop alice's grant
    let m = mmr_of(&receipts); // the GENUINE log's MMR (with alice's receipt)
    let (_vals, opening) = m.open_range(0, 4);
    let tampered_slice = AttestedSlice {
        receipts: tampered,
        cert: RangeCertificate { root: trusted_root, lo: 0, hi: 4, opening },
    };
    let bad = answer_whole_log(tampered_slice, caps_currently_held()).unwrap();
    assert!(
        bad.verify(&Blake3Mmr, &trusted_root).is_err(),
        "a server that omits a qualifying receipt must be CAUGHT by the certificate"
    );
}

#[test]
fn the_certificate_survives_the_wire() {
    // The attested answer crosses from the node to the verifying client as JSON
    // (the node-API mirror). It must round-trip and still verify — the
    // certificate is self-contained.
    let receipts = history();
    let (slice, trusted_root) = whole_log_slice(&receipts);
    let ans = answer_whole_log(slice, caps_currently_held()).unwrap();

    let wire = serde_json::to_string(&ans).expect("attested answer serializes");
    let back: AttestedAnswer = serde_json::from_str(&wire).expect("attested answer deserializes");
    back.verify(&Blake3Mmr, &trusted_root)
        .expect("the round-tripped attested read must still verify");
    assert_eq!(back, ans, "serde round-trip is identity");
}
