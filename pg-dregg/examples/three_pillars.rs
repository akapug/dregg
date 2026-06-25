//! pg-dregg — the three pillars, in ONE run, with no postgres and no node.
//!
//! Run it:
//!
//! ```text
//! cargo run --example three_pillars
//! ```
//!
//! This is the "play with it" path. It exercises the three things pg-dregg adds
//! to a database, in plain Rust over the postgres-free cores that `cargo test`
//! proves — so a stranger can SEE them work on this host without installing
//! postgres or cargo-pgrx:
//!
//!   1. CAP-SECURE RLS — a capability predicate compiles to a SQL/JSON `jsonpath`
//!      and filters rows; an unauthorized principal simply cannot see them, and an
//!      attenuated token sees a strict subset (no amplification).
//!   2. THE VERIFIED STORE — a tampered or reordered batch is REFUSED by the
//!      chain tooth the database engine itself runs (`dregg_verify_turn` / the
//!      `dregg.commit_log` gate), without re-running any prover.
//!   3. PROOF-ATTESTED RANGES (Tier-C) — the range-attest seam decodes a
//!      whole-chain proof transport, fails closed by default (attests nothing),
//!      and refuses tampered transports. The real ADMIT polarity (a genuine proof
//!      ACCEPTED) needs the heavyweight circuit verifier; see the closing note.
//!
//! The SAME behaviour runs THROUGH real SQL via the `#[pg_test]`s in `src/lib.rs`
//! (`cargo pgrx test pg18`) and an interactive session (`cargo pgrx run pg18`).
//! This example is those cores told end to end.

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::attest::{
    AttestRequest, SerializedWholeChainProof, WHOLE_CHAIN_DIGEST_LANES, attest_range,
    verify_serialized_proof,
};
use pg_dregg::authz;
use pg_dregg::jsonpath::{pred_to_jsonpath, predicate_attrs};
use pg_dregg::mirror::{ChainRefusal, RootChain};
use pg_dregg::synth::{self, GENESIS_ROOT};

fn hx(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn rule(title: &str) {
    println!(
        "\n\x1b[1m── {title} {}\x1b[0m",
        "─".repeat(64usize.saturating_sub(title.len()))
    );
}

fn main() {
    println!(
        "\x1b[1mpg-dregg — three pillars (cap-RLS · verified store · proof-attested ranges)\x1b[0m"
    );
    println!("running on the postgres-free cores; the same arc runs through SQL on pg18.");

    pillar_1_cap_secure_rls();
    pillar_2_verified_store();
    pillar_3_proof_attested_ranges();

    rule("DONE");
    println!(
        "\x1b[1m✓ a database that filters by capability, refuses a forged history, and \
         (with --features tier-c) proof-attests a range.\x1b[0m"
    );
    println!(
        "  through real SQL:  cargo pgrx run pg18   (then the policies in docs/QUICKSTART-pg-user.md)"
    );
}

// ============================================================================
// PILLAR 1 — CAP-SECURE RLS: a capability predicate filters the rows.
// ============================================================================
fn pillar_1_cap_secure_rls() {
    rule("1. cap-secure RLS — a capability predicate filters the rows");

    // --- 1a. the predicate, compiled to the jsonpath postgres evaluates --------
    // A dregg capability's authority is a tree of `Pred` atoms. pg-dregg compiles
    // that tree ONCE into a SQL/JSON jsonpath, so the database can evaluate it over
    // a row's JSON with `jsonb_path_exists` — a plain, index-eligible SQL predicate.
    let cap_pred = Pred::AllOf(vec![
        Pred::AttrEq {
            key: "action".into(),
            value: "read".into(),
        },
        Pred::AttrPrefix {
            key: "resource".into(),
            prefix: "org/42/public/".into(),
        },
    ]);
    let jsonpath = pred_to_jsonpath(&cap_pred).expect("a first-party Pred compiles to jsonpath");
    println!("  a capability predicate (read + resource prefix org/42/public/) compiles to:");
    println!("    \x1b[36m{jsonpath}\x1b[0m");
    println!(
        "    inspected attrs: {:?}  (the row JSON must bind these)",
        predicate_attrs(&cap_pred)
    );
    println!("  in SQL the read/audit policy is simply:");
    println!("    USING (jsonb_path_exists(row_json, '{jsonpath}'))");

    // --- 1b. the live gate: decide() narrows the visible rows ------------------
    // The WRITE gate stays the Rust `decide` path (it must also consult the issuer
    // key + the revocation set + the signature chain — a jsonpath cannot). This is
    // exactly the per-row decision the RLS policy
    // `USING (dregg_admits('read', row_cap))` makes. We install a trust root and
    // mint two tokens of differing authority over one table.
    let issuer = RootKey::from_seed([42u8; 32]);
    authz::set_issuer_pubkey(issuer.public());
    authz::lru_clear();
    authz::revoked_clear();
    println!(
        "\n  trust root installed (the dregg.issuer_pubkey GUC): {}…",
        &issuer.public().to_hex()[..12]
    );

    // A five-row table across two orgs with a public/private split — the kind of
    // multi-tenant data an app holds. Each row's `row_cap` is the RLS resource id.
    let table: &[(&str, &str)] = &[
        ("org/42/public/readme", "org42 public readme"),
        ("org/42/public/changelog", "org42 public changelog"),
        ("org/42/private/secrets", "org42 PRIVATE secrets"),
        ("org/99/public/readme", "org99 public readme"),
        ("org/99/private/secrets", "org99 PRIVATE secrets"),
    ];
    let now = 1_000i64;
    let visible = |tok: &str| -> Vec<&str> {
        table
            .iter()
            .filter(|(cap, _)| authz::decide(tok, "read", cap, now).allowed())
            .map(|(cap, _)| *cap)
            .collect()
    };

    // The org/42 token: read across all of org/42.
    let org42 = issuer
        .mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            }),
            Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/42/".into(),
            }),
        ])
        .encode();

    // Its holder attenuates it to org/42/public/ only — the holder's own right,
    // offline, no issuer key needed. This is what you hand a less-trusted delegate.
    let public_only = authz::attenuate_token(
        &org42,
        r#"[{"AttrPrefix":{"key":"resource","prefix":"org/42/public/"}}]"#,
    )
    .expect("attenuating a valid token succeeds");

    let parent = visible(&org42);
    let child = visible(&public_only);
    println!(
        "\n  org/42 token        → SELECT sees {} rows: {:?}",
        parent.len(),
        parent
    );
    println!(
        "  attenuated (public) → SELECT sees {} rows: {:?}",
        child.len(),
        child
    );
    assert_eq!(
        parent.len(),
        3,
        "org/42 token reaches the three org/42 rows"
    );
    assert_eq!(
        child.len(),
        2,
        "the attenuated token reaches only the two public rows"
    );
    assert!(child.iter().all(|c| c.contains("/public/")));
    for c in &child {
        assert!(
            parent.contains(c),
            "child saw a row the parent could not — amplification!"
        );
    }
    assert!(parent.len() > child.len(), "narrowing must be strict");
    println!(
        "  → attenuation NARROWED {} → {} rows (strict subset; the private row vanished — no amplification)",
        parent.len(),
        child.len()
    );

    // A token from a DIFFERENT issuer: even claiming org/42, it does not verify
    // against the configured trust root, so it sees NOTHING (fail-closed). An
    // attacker cannot forge visibility.
    let forged = RootKey::from_seed([7u8; 32])
        .mint([
            Caveat::FirstParty(Pred::AttrEq {
                key: "action".into(),
                value: "read".into(),
            }),
            Caveat::FirstParty(Pred::AttrPrefix {
                key: "resource".into(),
                prefix: "org/42/".into(),
            }),
        ])
        .encode();
    assert!(
        visible(&forged).is_empty(),
        "a foreign-issuer token must see nothing"
    );
    assert!(
        visible("dga1_not-a-real-token").is_empty(),
        "garbage must see nothing, not panic"
    );
    println!("  → a foreign-issuer token and a garbage token each see 0 rows (fail-closed)");

    // Instant revocation: revoke the org/42 credential; the very next scan shows
    // zero of its rows (the policy consults the revocation registry per row).
    let id = authz::cap_id(&org42).expect("token decodes to a stable id");
    authz::revoke(&id);
    assert!(
        visible(&org42).is_empty(),
        "a revoked token's rows vanish on the next scan"
    );
    println!(
        "  → revoked the org/42 credential ({}…) — its rows vanish INSTANTLY on the next scan",
        &id[..12]
    );
    authz::unrevoke(&id);
}

// ============================================================================
// PILLAR 2 — THE VERIFIED STORE: a forged history is refused by the engine.
// ============================================================================
fn pillar_2_verified_store() {
    rule("2. the verified store — a forged/reordered history is REFUSED");

    // The mirror replays the node's committed turns. Each turn's post-state root
    // is the next turn's pre-state root, so the turns table is a hash chain. The
    // database engine runs this exact step gate (`dregg_verify_turn`, lifted from
    // `mirror::verify_chain_step`) on every committed batch via the
    // `dregg.commit_log` trigger — so a tampered, reordered, or replayed batch is
    // refused by the DB itself, with NO prover re-run.
    let story = synth::ledger_story();
    let mut chain = RootChain::resume(GENESIS_ROOT, 0);
    for b in &story {
        chain
            .extend(b)
            .unwrap_or_else(|e| panic!("a well-formed batch was refused: {e}"));
    }
    assert_eq!(chain.next_ordinal(), 4, "all four committed turns chain");
    println!(
        "  the node committed {} turns; the mirror accepted them all (head {}…)",
        story.len(),
        &hx(&chain.head().unwrap())[..12]
    );

    // (a) a TAMPERED batch — a substituted pre-state root (a forged ord-2 turn).
    let mut c = RootChain::resume(GENESIS_ROOT, 0);
    c.extend(&story[0]).unwrap();
    c.extend(&story[1]).unwrap();
    let head_before = c.head();
    match c.extend(&synth::tampered_batch_at_2()) {
        Ok(()) => panic!("SECURITY FAILURE: a tampered batch was accepted"),
        Err(ChainRefusal::RootMismatch { .. }) => {
            println!(
                "  (a) a tampered batch (substituted prev_root) → REFUSED (root does not chain)"
            )
        }
        Err(e) => panic!("expected a RootMismatch refusal, got {e}"),
    }
    assert_eq!(
        c.head(),
        head_before,
        "a refused batch must not move the head"
    );

    // (b) a REORDERED batch — offering ord 3 before ord 2 (an ordinal gap/replay).
    let mut c2 = RootChain::resume(GENESIS_ROOT, 0);
    c2.extend(&story[0]).unwrap();
    c2.extend(&story[1]).unwrap();
    match c2.extend(&story[3]) {
        Err(ChainRefusal::OrdinalGap { expected, got }) => println!(
            "  (b) a reordered batch (ord {got} before ord {expected}) → REFUSED (ordinal gap)"
        ),
        other => panic!("expected an OrdinalGap refusal, got {other:?}"),
    }
    assert_eq!(
        c2.next_ordinal(),
        2,
        "the reordered batch did not advance the chain"
    );

    println!("  → forged state cannot enter the store; the head never moves on a refusal");
}

// ============================================================================
// PILLAR 3 — PROOF-ATTESTED RANGES (Tier-C): the range-attest seam.
// ============================================================================
fn pillar_3_proof_attested_ranges() {
    rule("3. proof-attested ranges (Tier-C) — the range-attest seam");

    // A whole-chain IVC proof rides into the database as a versioned, bytea-
    // crossable transport (the S1 artifact). The node (S2) produces it; the SRF
    // `dregg_attest_range` decodes and verifies it (S3). Here we build a
    // well-formed transport with placeholder proof blobs to exercise the boundary.
    let transport = SerializedWholeChainProof::new(
        b"<root-proof-blob>".to_vec(),
        b"<binding-proof-blob>".to_vec(),
        [0x01u8; 32], // genesis_root
        [0x02u8; 32], // final_root
        [[0x03u8; 32]; WHOLE_CHAIN_DIGEST_LANES],
        100, // num_turns the proof claims to cover
    );
    let bytes = transport.to_bytes();
    let anchor = [0xABu8; 32]; // the light client's published VK anchor
    println!(
        "  a whole-chain proof transport encodes to {} bytes (the bytea a node ships)",
        bytes.len()
    );

    // S1 round-trip + fail-closed decode: the transport decodes back, and a
    // corrupted / empty transport is refused at the boundary, never half-read.
    let decoded =
        SerializedWholeChainProof::from_bytes(&bytes).expect("a well-formed transport decodes");
    assert_eq!(decoded, transport, "the transport round-trips");
    assert!(
        SerializedWholeChainProof::from_bytes(b"").is_err(),
        "empty bytes refused"
    );
    // A transport carrying an empty proof component is refused (never a half-proof).
    let half = SerializedWholeChainProof::new(
        vec![],
        b"x".to_vec(),
        [1u8; 32],
        [2u8; 32],
        [[3u8; 32]; WHOLE_CHAIN_DIGEST_LANES],
        1,
    );
    assert!(
        SerializedWholeChainProof::from_bytes(&half.to_bytes()).is_err(),
        "empty root proof refused"
    );
    println!(
        "  → the transport round-trips; empty / half-proof bytes are refused at decode (fail-closed)"
    );

    // The verify seam. In the DEFAULT (circuit-free) build the heavyweight IVC
    // verifier is not linked, so the seam FAILS CLOSED — it attests NOTHING, even
    // on a well-formed transport. This is the only safe default: a proof gate that
    // cannot verify must say "unattested", never "attested".
    match verify_serialized_proof(&bytes, &anchor) {
        Ok(_) => panic!("the default build must NOT attest (no circuit verifier linked)"),
        Err(e) => {
            let first = e.lines().next().unwrap_or(&e);
            println!("  the range-attest seam (default build) → {first}");
        }
    }

    // The full SRF entry, same fail-closed verdict, plus the anti-overclaim tooth.
    let req = AttestRequest {
        proof_bytes: &bytes,
        vk_anchor: anchor,
        lo: 0,
        hi: 9,
    };
    let verdict = attest_range(&req);
    assert!(!verdict.attested(), "default build attests nothing");
    println!(
        "  attest_range([0,9]) → REFUSED (fail-closed): {}",
        verdict.reason()
    );

    // An inverted/empty window is refused up front (a structural tooth that bites
    // in EVERY build, before any proof work).
    let bad_window = attest_range(&AttestRequest {
        proof_bytes: &bytes,
        vk_anchor: anchor,
        lo: 9,
        hi: 0,
    });
    assert!(!bad_window.attested());
    println!(
        "  attest_range([9,0]) → REFUSED (empty/inverted window): {}",
        bad_window.reason()
    );

    println!(
        "\n  the ADMIT polarity — a GENUINE whole-chain proof ACCEPTED, returning the bound\n  \
         window publics, plus tamper-refusal of a relabeled public / wrong VK — is proven by\n  \
         the real recursion fold in tests/tier_c_real_proof.rs. It is SLOW (~minutes) and needs\n  \
         the circuit verifier, so it is gated:\n      \
         \x1b[36mcargo test --features tier-c --test tier_c_real_proof -- --ignored --nocapture\x1b[0m"
    );
}
