//! CAP-SECURED DATA STORE — the runnable first slice (postgres-free CORE).
//!
//! The deos cap-secured store thesis (`docs/deos/DREGG-DATA-STORE.md`): an
//! application table whose Row-Level Security is the SAME kernel capability
//! decision the dregg kernel makes. A row a token cannot cap-reach is INVISIBLE
//! (the RLS `USING` clause filters it out); a wrong or over-broad token is
//! DENIED; an attenuated token sees a STRICT SUBSET.
//!
//! In production this filtering happens inside postgres: an RLS policy
//! `USING (dregg_admits('read', encode(row_cap, 'hex')))` calls the
//! `dregg_admits` extern, which calls `authz::decide(token, action, resource,
//! now)` once per candidate row. THIS test exercises that EXACT decision core
//! (the postgres-free `authz::decide`) over an in-memory table, so the
//! one-kernel-decision RLS semantics are proven without a managed postgres. The
//! pgrx path (`cargo pgrx test pg18`) runs the same `decide` behind the SQL
//! policy; it needs cargo-pgrx + a managed pg18 and is NOT run here (the file
//! header in `Cargo.toml` documents that split).
//!
//! What this proves, concretely:
//!   1. a table of rows each tagged with a `row_cap` (the per-row resource id);
//!   2. RLS = "row visible iff `decide(token, 'read', row_cap, now)` allows" —
//!      the SAME decision the kernel makes, applied per row;
//!   3. an ATTENUATED token sees only its authorized rows (a strict subset);
//!   4. a WRONG-issuer / OVER-BROAD-but-unverifiable token sees NOTHING
//!      (fail-closed);
//!   5. INSTANT revocation: a revoked token's rows vanish on the next scan.

use dregg_auth::credential::{Caveat, Pred, RootKey};
use pg_dregg::authz;
use std::sync::Mutex;

/// The authz decision core is process-GLOBAL (the issuer key, the verified-cred
/// LRU, the revocation set) — exactly as it is in a postgres backend process.
/// The tests in THIS binary share that process, so they serialize on this guard
/// (each test owns the global state for its body). It is a binary-local static:
/// integration tests and the crate's own unit tests run in separate processes,
/// so they never share global state with each other.
static TEST_SERIAL: Mutex<()> = Mutex::new(());

fn lock() -> std::sync::MutexGuard<'static, ()> {
    TEST_SERIAL.lock().unwrap_or_else(|p| p.into_inner())
}

/// One application row: a domain payload plus the `row_cap` the RLS policy gates
/// on. In SQL this is an ordinary table column (`row_cap bytea`); here it is the
/// resource id string `decide` binds as the `resource` attribute.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Row {
    row_cap: &'static str,
    payload: &'static str,
}

/// The application table — five rows across two orgs and a public/private split,
/// exactly the kind of multi-tenant data a deos app (or builders-dev) holds.
fn table() -> Vec<Row> {
    vec![
        Row { row_cap: "org/42/public/readme", payload: "org42 public readme" },
        Row { row_cap: "org/42/public/changelog", payload: "org42 public changelog" },
        Row { row_cap: "org/42/private/secrets", payload: "org42 PRIVATE secrets" },
        Row { row_cap: "org/99/public/readme", payload: "org99 public readme" },
        Row { row_cap: "org/99/private/secrets", payload: "org99 PRIVATE secrets" },
    ]
}

/// THE RLS ROW-FILTER. This is the exact predicate the postgres policy
/// `USING (dregg_admits('read', encode(row_cap,'hex')))` evaluates per row: a
/// row is VISIBLE to `token` iff the kernel capability decision admits `read` on
/// that row's `row_cap` at `now`. One kernel decision, applied to every row.
fn visible_rows(token: &str, now: i64) -> Vec<Row> {
    table()
        .into_iter()
        .filter(|r| authz::decide(token, "read", r.row_cap, now).allowed())
        .collect()
}

/// The issuer/trust root for this test (the database's `dregg.issuer_pubkey`).
fn root() -> RootKey {
    RootKey::from_seed([42u8; 32])
}

/// Install the issuer public key as the process trust root + reset the caches,
/// exactly as the pgrx layer does from the GUC at decision time.
fn install(root: &RootKey) {
    authz::set_issuer_pubkey(root.public());
    authz::lru_clear();
    authz::revoked_clear();
}

/// Mint a read token confined to a resource prefix, naming a subject, expiring
/// at clock 10_000 — the canonical row-cap-bearing token.
fn mint_read(root: &RootKey, subject: &str, prefix: &str) -> String {
    root.mint([
        Caveat::FirstParty(Pred::AttrEq { key: "subject".into(), value: subject.into() }),
        Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
        Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: prefix.into() }),
        Caveat::FirstParty(Pred::NotAfter { at: 10_000 }),
    ])
    .encode()
}

#[test]
fn rls_shows_only_cap_reachable_rows() {
    let _g = lock();
    let root = root();
    install(&root);

    // A token scoped to all of org/42 — it cap-reaches the three org/42 rows and
    // NONE of the org/99 rows. The org/99 rows are simply INVISIBLE (filtered by
    // the RLS USING clause), not errored.
    let org42 = mint_read(&root, "alice", "org/42/");
    let seen = visible_rows(&org42, 1000);
    assert_eq!(seen.len(), 3, "org/42 token must see exactly the three org/42 rows");
    assert!(seen.iter().all(|r| r.row_cap.starts_with("org/42/")));
    assert!(
        !seen.iter().any(|r| r.row_cap.starts_with("org/99/")),
        "an org/99 row a token cannot cap-reach must be INVISIBLE, not visible"
    );
}

#[test]
fn attenuated_token_sees_a_strict_subset() {
    let _g = lock();
    let root = root();
    install(&root);

    // The holder of the org/42 token attenuates it to org/42/public/ only —
    // the holder's own right, no issuer key needed. The narrowed token is what a
    // deos app hands to a less-trusted component / a sub-tenant.
    let org42 = mint_read(&root, "alice", "org/42/");
    let public_only = authz::attenuate_token(
        &org42,
        r#"[{"AttrPrefix":{"key":"resource","prefix":"org/42/public/"}}]"#,
    )
    .expect("attenuation of a valid token must succeed");

    let parent_seen = visible_rows(&org42, 1000);
    let child_seen = visible_rows(&public_only, 1000);

    // The child sees the two public org/42 rows, NOT the private one — a strict
    // subset of the parent's three. This is the no-amplify property observed
    // through the store: attenuation can only HIDE rows, never reveal new ones.
    assert_eq!(child_seen.len(), 2);
    assert!(child_seen.iter().all(|r| r.row_cap.starts_with("org/42/public/")));
    assert!(
        !child_seen.iter().any(|r| r.row_cap.contains("/private/")),
        "the attenuated token must not reach the private row the parent reached"
    );
    // subset: every row the child sees, the parent sees.
    for c in &child_seen {
        assert!(parent_seen.contains(c), "child saw a row the parent did not");
    }
    // strict: the parent sees at least one row (the private secrets) the child does not.
    assert!(
        parent_seen.iter().any(|p| !child_seen.contains(p)),
        "narrowing was not strict — the child saw everything the parent did"
    );
}

#[test]
fn wrong_or_overbroad_token_sees_nothing() {
    let _g = lock();
    let root = root();
    install(&root);

    // A token from a DIFFERENT issuer — even though it claims an org/42 prefix,
    // it does NOT verify against the configured issuer key, so the RLS filter
    // shows it ZERO rows (fail-closed). An attacker cannot forge visibility.
    let other = RootKey::from_seed([7u8; 32]);
    let forged = mint_read(&other, "mallory", "org/42/");
    assert!(
        visible_rows(&forged, 1000).is_empty(),
        "a foreign-issuer token must see nothing — the kernel decision rejects it"
    );

    // A garbage token: no rows, no panic.
    assert!(visible_rows("dga1_not-a-real-token", 1000).is_empty());

    // An EXPIRED genuine token (past NotAfter 10_000): the whole table vanishes
    // — the same kernel temporal caveat the kernel enforces.
    let expired_clock = 99_999;
    let org42 = mint_read(&root, "alice", "org/42/");
    assert!(
        visible_rows(&org42, expired_clock).is_empty(),
        "past the token's NotAfter, no rows are cap-reachable"
    );
}

#[test]
fn instant_revocation_vanishes_rows_on_the_next_scan() {
    let _g = lock();
    let root = root();
    install(&root);

    let org42 = mint_read(&root, "alice", "org/42/");
    assert_eq!(visible_rows(&org42, 1000).len(), 3, "rows visible before revocation");

    // Revoke the exact credential. The next scan — the very next statement in
    // SQL terms — shows ZERO rows, even though the chain-verify is cached hot.
    // Revocation is consulted on every row-check, so it lands instantly.
    let id = authz::cap_id(&org42).expect("token decodes to a stable id");
    authz::revoke(&id);
    assert!(
        visible_rows(&org42, 1000).is_empty(),
        "a revoked token's rows must vanish on the next scan (instant revocation)"
    );

    // Lifting the revocation restores visibility — the credential never changed.
    authz::unrevoke(&id);
    assert_eq!(visible_rows(&org42, 1000).len(), 3);
}

#[test]
fn no_issuer_key_hides_the_whole_table() {
    let _g = lock();
    // No issuer key configured ⇒ EVERY decision denies ⇒ the whole table is
    // invisible. This is the loud fail-closed posture (the silent "all my rows
    // vanished" mode `dregg_issuer_status` exists to make discoverable): a
    // cap-secured store with no trust root shows nothing rather than everything.
    authz::clear_issuer_pubkey();
    authz::lru_clear();
    authz::revoked_clear();
    let root = root();
    let org42 = mint_read(&root, "alice", "org/42/");
    assert!(
        visible_rows(&org42, 1000).is_empty(),
        "with no issuer key, a cap-secured store is empty, never wide-open"
    );
}
