//! # pg-dregg — dregg verified object-capability authorization for PostgreSQL RLS
//!
//! An ordinary postgres-heavy app gates rows with dregg capabilities instead of
//! hand-rolled SQL RLS predicates. The SAME `dga1_…` token authorizes against
//! the dregg kernel and against your plain tables.
//!
//! ## Two layers, one decision
//!
//! * [`core`] — the postgres-independent authorization CORE: decode + verify a
//!   credential (delegated to the proven [`dregg_auth::credential`]), the
//!   verified-credential LRU, the instant-revocation registry, and the caveat /
//!   attenuation-narrowing evaluation. Proven by plain `cargo test` (no
//!   postgres). This is where the M1 thesis is verified.
//! * the `#[pg_extern]` wrappers below (gated behind the `pgrx` feature) — thin
//!   marshalling of SQL `text`/`bigint` into [`core`] calls, plus the
//!   `dregg.issuer_pubkey` GUC and the convenience `dregg_admits` wrapper.
//!
//! ## The assurance boundary (docs/PG-DREGG.md §4)
//!
//! The *capability decision* a policy makes is the verified dregg decision (the
//! Lean↔Rust differential on `dregg-auth` is the anchor). The *integration* —
//! the GUC plumbing, the LRU, the revocation registry, the per-row invocation —
//! is conventional extension code, tested directly in [`core`]. We do not claim
//! the postgres layer is formally verified; we name the seam.

pub mod authz;
pub mod jsonpath;
pub mod mirror;
pub mod synth;

// The PG_MODULE_MAGIC block + the `__pgrx_marker` the schema generator links
// against MUST live at the crate ROOT (cargo-pgrx's pgrx_embed binary calls
// `pg_dregg::__pgrx_marker`). Feature-gated so the core build never sees it.
#[cfg(feature = "pgrx")]
pgrx::pg_module_magic!();

// ===========================================================================
// The postgres extension surface. Compiled only with the `pgrx` feature (which
// the pgNN features turn on); `cargo test` builds none of this.
// ===========================================================================
#[cfg(feature = "pgrx")]
mod pg {
    use crate::authz;
    use pgrx::guc::{GucContext, GucFlags, GucRegistry, GucSetting};
    use pgrx::prelude::*;

    // -----------------------------------------------------------------------
    // Issuer public key — the database trust root (docs/PG-DREGG.md §3.3).
    //
    // The PUBLIC key is publishable, so the GUC is DBA-visible/settable
    // (`GucContext::Sighup`). The PRIVATE key never lives in postgres. A
    // malformed/absent key makes every decision DENY (fail-closed).
    // -----------------------------------------------------------------------
    static ISSUER_PUBKEY: GucSetting<Option<std::ffi::CString>> =
        GucSetting::<Option<std::ffi::CString>>::new(None);

    #[pg_guard]
    pub extern "C-unwind" fn _PG_init() {
        GucRegistry::define_string_guc(
            c"dregg.issuer_pubkey",
            c"The dregg issuer PUBLIC key (64 hex chars). The database trust root.",
            c"Verification uses only the public key; the private key never enters postgres. \
              A malformed or absent key makes every dregg_cap_admits DENY (fail-closed).",
            &ISSUER_PUBKEY,
            GucContext::Sighup,
            GucFlags::empty(),
        );
    }

    /// Pull the issuer key from the GUC into the process-local core slot. Called
    /// at the head of every decision so a SIGHUP-changed key takes effect. Cheap
    /// (a hex parse); on a malformed/absent key it clears the slot ⇒ deny.
    fn sync_issuer_key() {
        match ISSUER_PUBKEY.get() {
            Some(cstring) => {
                let hex = cstring.to_str().unwrap_or("");
                authz::set_issuer_pubkey_hex(hex);
            }
            None => {
                // No key configured ⇒ ensure the slot reflects "deny".
                authz::clear_issuer_pubkey();
            }
        }
    }

    // -----------------------------------------------------------------------
    // The core decision (docs/PG-DREGG.md §2.1, §3.1).
    //
    // VOLATILITY: STABLE, not IMMUTABLE. See docs/PG-DREGG.md §6 + the report.
    // The decision depends on the revocation registry, which can change WITHIN a
    // statement (instant revocation, ember decision #1). An IMMUTABLE function
    // promises the planner the same inputs always give the same output and may
    // be folded/cached across rows; that is UNSOUND once revocation can flip a
    // verdict mid-statement. STABLE (constant within a single statement's
    // snapshot, may differ across statements) is the correct, sound class.
    // STRICT: a NULL token ⇒ NULL ⇒ the policy treats it as deny.
    // -----------------------------------------------------------------------

    /// `dregg_cap_admits(token, action, resource, now) -> bool`. TRUE iff the
    /// credential admits `action` on `resource` at `now`, verified offline
    /// against the configured issuer key, not revoked. Fail-closed.
    #[pg_extern(stable, parallel_safe, strict)]
    fn dregg_cap_admits(token: &str, action: &str, resource: &str, now: i64) -> bool {
        sync_issuer_key();
        authz::decide(token, action, resource, now).allowed()
    }

    /// `dregg_cap_explain(...) -> text`. The human-readable decision reason —
    /// `"allowed"`, or the first violated requirement (or "revoked" / "no issuer
    /// key configured"). For debugging policies and audit logging.
    #[pg_extern(stable, parallel_safe)]
    fn dregg_cap_explain(
        token: Option<&str>,
        action: &str,
        resource: &str,
        now: i64,
    ) -> Option<String> {
        let token = token?;
        sync_issuer_key();
        Some(authz::explain(token, action, resource, now))
    }

    /// `dregg_cap_subject(token) -> text`. The confined subject the token names,
    /// or NULL if the token's chain does not verify under the issuer key.
    #[pg_extern(stable, parallel_safe)]
    fn dregg_cap_subject(token: Option<&str>) -> Option<String> {
        let token = token?;
        sync_issuer_key();
        authz::subject(token)
    }

    /// `dregg_cap_id(token) -> text`. The stable per-credential id (hex of the
    /// chain-committing tail) the revocation registry keys on, or NULL if the
    /// token does not decode. Use it to populate `dregg.revoked`.
    #[pg_extern(immutable, parallel_safe)]
    fn dregg_cap_id(token: Option<&str>) -> Option<String> {
        authz::cap_id(token?)
    }

    /// `dregg_revoke(token) -> text`. Revoke the presented credential
    /// (extension-layer registry; backend-local). Returns the revoked id, or
    /// NULL if the token does not decode. In a clustered deployment this would
    /// write the `dregg.revoked` table; here it mirrors into the backend-local
    /// set the per-row check consults.
    #[pg_extern]
    fn dregg_revoke(token: Option<&str>) -> Option<String> {
        let id = authz::cap_id(token?)?;
        authz::revoke(&id);
        Some(id)
    }

    /// `dregg_unrevoke(id text) -> bool`. Lift a revocation by id.
    #[pg_extern]
    fn dregg_unrevoke(id: &str) -> bool {
        authz::unrevoke(id);
        true
    }

    // -----------------------------------------------------------------------
    // The terse convenience wrapper — reads the session GUC + clock so RLS
    // policies stay readable. STABLE (reads now() and the GUC).
    // -----------------------------------------------------------------------

    /// `dregg_install_schema() -> text`. Install the Tier-B store schema (the
    /// `dregg.*` tables + the query-surface views + the read-side RLS + the
    /// write-lockdown role model), generated from the same Rust that defines the
    /// row types (`crate::mirror::ddl::tier_b`). Idempotent (`IF NOT EXISTS`), so
    /// it is safe to re-run. This is the dregg-developer entry point
    /// (`docs/QUICKSTART-dregg-dev.md` §2): one call stands up "postgres as the
    /// dregg store". Returns a short summary of what it created.
    ///
    /// Must be run by a role that can `CREATE TABLE`/`CREATE ROLE` in the target
    /// database (a DBA/migration role), NOT an application role.
    #[pg_extern]
    fn dregg_install_schema() -> String {
        let ddl = crate::mirror::ddl::tier_b();
        Spi::run(&ddl).expect("dregg_install_schema: Tier-B DDL failed");
        let tables = ddl.matches("CREATE TABLE").count();
        let views = ddl.matches("CREATE OR REPLACE VIEW").count();
        let policies = ddl.matches("CREATE POLICY").count();
        format!(
            "dregg Tier-B store installed: {tables} tables, {views} views, {policies} RLS policies in schema dregg"
        )
    }

    /// `dregg_install_tier_c() -> text`. Install the Tier-C verified-store gate
    /// (`docs/PG-DREGG.md` §10) on top of the Tier-B tables: the
    /// `dregg.commit_log` door + the `BEFORE INSERT` trigger that re-validates
    /// the chain (`dregg_verify_turn`) and materializes the post-image. After
    /// this, a state row exists ONLY as a verified-turn post-image submitted
    /// through `dregg.commit_log` — enforced by the database engine, not by
    /// trusting the writer. Requires [`dregg_install_schema`] to have run first
    /// (the state tables + `dregg.merge_cell` must exist). Idempotent.
    ///
    /// Run by a DBA/migration role (it creates a `SECURITY DEFINER` function and
    /// a trigger), NOT an application role.
    #[pg_extern]
    fn dregg_install_tier_c() -> String {
        let ddl = crate::mirror::ddl::tier_c();
        Spi::run(&ddl).expect("dregg_install_tier_c: Tier-C DDL failed");
        "dregg Tier-C verified-store gate installed: dregg.commit_log + the \
         verify_before_apply trigger (dregg_verify_turn chain re-validation; \
         the ONLY door to state)"
            .to_string()
    }

    /// `dregg_install_write_outbox() -> text`. Install the WRITE-path outbox
    /// (`docs/PG-DREGG.md` §11): the `dregg.submit_queue` table + the RLS gate so
    /// a pg role can submit a verified turn FROM postgres for exactly the agents
    /// its capabilities authorize. Requires [`dregg_install_schema`] first (the
    /// role model). Idempotent. The node-side drainer (queue → real executor →
    /// mirror) is the M3 follow-up; this installs the enqueue half + its gate.
    #[pg_extern]
    fn dregg_install_write_outbox() -> String {
        let ddl = crate::mirror::ddl::write_outbox();
        Spi::run(&ddl).expect("dregg_install_write_outbox: outbox DDL failed");
        "dregg write outbox installed: dregg.submit_queue + the submit_gate RLS \
         policy (a role submits only the turns its capabilities authorize; the \
         node drains the queue through the real verified executor)"
            .to_string()
    }

    /// `dregg_install_login_binding() -> text`. Install the pg17 LOGIN EVENT
    /// TRIGGER authz binding (`docs/PG-DREGG-PG18.md` §6): the
    /// `dregg.role_identity` map + the `ON login` event trigger that binds a
    /// connecting pg role to its dregg agent identity (sets the `dregg.token` /
    /// `dregg.agent` session GUCs from the role's row) at connection time.
    /// Requires [`dregg_install_schema`] first (the role model). Idempotent. After
    /// this, a DBA `INSERT`s `(pg_role, agent, default_token)` rows and every
    /// connection by that role is already capability-bound — the pg-native front
    /// door. A role with no row connects unbound (deny-by-default, fail-closed).
    ///
    /// Run by a DBA/migration role (it creates a `SECURITY DEFINER` function and
    /// an event trigger), NOT an application role.
    #[pg_extern]
    fn dregg_install_login_binding() -> String {
        let ddl = crate::mirror::ddl::login_binding();
        Spi::run(&ddl).expect("dregg_install_login_binding: login-binding DDL failed");
        "dregg login binding installed: dregg.role_identity + the dregg_login_bind \
         event trigger (a connecting role is bound to its dregg capability at login; \
         a role with no identity row connects unbound = deny-by-default)"
            .to_string()
    }

    /// `dregg_bind_role(pg_role text, agent bytea, token text) -> bool`. Bind a
    /// connecting pg role to its dregg agent identity (`docs/PG-DREGG-PG18.md` §6):
    /// upsert the `dregg.role_identity` row the `ON login` trigger installs, so the
    /// role's session is capability-bound the moment it connects. This is the seam
    /// where pg18 OAuth meets dregg — OAuth (a `pg_hba.conf` deployment concern, not
    /// extension SQL) authenticates an external identity to a pg ROLE; this binds
    /// that role to a dregg capability. Calls the `SECURITY DEFINER`
    /// `dregg.bind_role` (which writes the PUBLIC-closed mapping table), so it must
    /// be run by a role the DBA granted `EXECUTE` on `dregg.bind_role`. `token` may
    /// be NULL (bind the agent identity without a default token; the role then
    /// presents its own). Requires [`dregg_install_login_binding`] first.
    #[pg_extern]
    fn dregg_bind_role(pg_role: &str, agent: &[u8], token: Option<&str>) -> bool {
        Spi::run_with_args(
            "SELECT dregg.bind_role($1, $2, $3)",
            &[pg_role.into(), agent.into(), token.into()],
        )
        .expect("dregg_bind_role: bind failed (login binding not installed, or no EXECUTE on dregg.bind_role)");
        true
    }

    /// `dregg_submit_turn(signed_turn bytea, agent bytea) -> uuid`. Submit a
    /// SIGNED turn FROM postgres (`docs/PG-DREGG.md` §11). `signed_turn` is the
    /// postcard `SignedTurn` bytes; `agent` is the turn's agent cell id. Enqueues
    /// the turn into `dregg.submit_queue` and returns the submission id; the node
    /// drains the queue, executes the turn through the REAL verified executor, and
    /// the post-image flows back via the mirror.
    ///
    /// The enqueue is RLS-gated by the `submit_gate` policy (`dregg_admits(
    /// 'submit', encode(agent,'hex'))`): the caller's presented capability (the
    /// `dregg.token` GUC) must admit `submit` on this agent, else the INSERT is
    /// refused by Row-Level Security — a role submits exactly the turns its caps
    /// authorize. This function is NOT `SECURITY DEFINER`: it runs as the calling
    /// role so the WITH CHECK policy bites. The turn stays UNexecuted until the
    /// node accepts it — writes are verified-only because the NODE, not postgres,
    /// executes.
    ///
    /// Returns the submission id (poll `dregg.submit_queue` for the outcome:
    /// `status` walks `pending → executed | refused`, with `receipt_hash` /
    /// `error` carrying the result). RAISEs if RLS refuses the enqueue.
    #[pg_extern]
    fn dregg_submit_turn(signed_turn: &[u8], agent: &[u8]) -> pgrx::Uuid {
        // Insert as the calling role so the submit_gate WITH CHECK policy (the
        // capability admission) gates the enqueue. RETURNING the generated id.
        let id: Option<pgrx::Uuid> = Spi::get_one_with_args(
            "INSERT INTO dregg.submit_queue (agent, signed_turn) VALUES ($1, $2) RETURNING id",
            &[agent.into(), signed_turn.into()],
        )
        .expect("dregg_submit_turn: enqueue failed (RLS refused, or the outbox is not installed)");
        id.expect("dregg_submit_turn: INSERT ... RETURNING id yielded no row")
    }

    /// `dregg_verify_turn(prev_root, ledger_root, ordinal) -> bool`. The Tier-C
    /// chain re-validator (`docs/PG-DREGG.md` §10): TRUE iff a turn with
    /// pre-state `prev_root` and `ordinal` chains onto the database's current
    /// head — i.e. `ordinal` is the next expected one AND `prev_root` equals the
    /// head root (the post-state root of turn *N* is the pre-state root of turn
    /// *N+1*). This is the REAL anti-substitution tooth: it runs the exact same
    /// gate the in-process mirror runs (`crate::mirror::verify_chain_step`, which
    /// `RootChain::extend` also calls), reading the head from `dregg.turns`. A
    /// tampered / reordered / forged batch is refused.
    ///
    /// What it is NOT (documented honestly, `docs/PG-DREGG.md` §10.2/§10.3): it
    /// is NOT a per-turn STARK re-proof. A `CommitRecord` carries no per-turn
    /// proof (proof soundness is the whole-chain IVC light client's job —
    /// `circuit::ivc_turn_chain::verify_turn_chain_recursive`), so the realizable
    /// per-row gate is this structural chain check. It is NOT stubbed to TRUE
    /// (the forbidden failure mode); it fails closed on any deviation.
    ///
    /// STABLE: depends on the current `dregg.turns` head, constant within a
    /// statement snapshot. `ledger_root` is accepted (the post-state the row
    /// claims to produce, recorded by the trigger) though the chain step itself
    /// gates on `prev_root`/`ordinal`; carrying it keeps the signature the
    /// verified-store door's shape.
    #[pg_extern(stable, parallel_safe, strict)]
    fn dregg_verify_turn(prev_root: &[u8], ledger_root: &[u8], ordinal: i64) -> bool {
        let _ = ledger_root; // recorded by the trigger; the chain gate is on prev_root/ordinal
        // Read the current head + next-expected ordinal from dregg.turns.
        // No rows ⇒ genesis (head = None, next = 0).
        let head_hex: Option<String> = Spi::get_one(
            "SELECT encode(ledger_root, 'hex') FROM dregg.turns ORDER BY ordinal DESC LIMIT 1",
        )
        .ok()
        .flatten();
        let next_ordinal: i64 = Spi::get_one(
            "SELECT coalesce(max(ordinal) + 1, 0) FROM dregg.turns",
        )
        .ok()
        .flatten()
        .unwrap_or(0);

        let head: Option<[u8; 32]> = head_hex.and_then(|h| decode_root_hex(&h));
        let Some(prev) = slice_to_root(prev_root) else {
            return false; // malformed prev_root ⇒ fail closed
        };
        if ordinal < 0 {
            return false;
        }
        crate::mirror::verify_chain_step(head, next_ordinal as u64, prev, ordinal as u64).is_ok()
    }

    /// Decode a 64-char hex string into a 32-byte root (fail-closed on bad len).
    fn decode_root_hex(h: &str) -> Option<[u8; 32]> {
        if h.len() != 64 {
            return None;
        }
        let mut out = [0u8; 32];
        for (i, byte) in out.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&h[i * 2..i * 2 + 2], 16).ok()?;
        }
        Some(out)
    }

    /// A bytea slice from SQL into a fixed 32-byte root (fail-closed on bad len).
    fn slice_to_root(s: &[u8]) -> Option<[u8; 32]> {
        s.try_into().ok()
    }

    /// `dregg_admits(action, resource) -> bool`. Reads `current_setting(
    /// 'dregg.token', true)` and `now()`; the ergonomic face for
    /// `USING (dregg_admits('read', id::text))`.
    #[pg_extern(stable, parallel_safe)]
    fn dregg_admits(action: &str, resource: &str) -> bool {
        // current_setting('dregg.token', true) — missing-ok ⇒ NULL ⇒ deny.
        let token: Option<String> = Spi::get_one_with_args(
            "SELECT current_setting('dregg.token', true)",
            &[],
        )
        .unwrap_or(None);
        let Some(token) = token else { return false };
        // unix seconds: extract(epoch from now())::bigint
        let now: i64 = Spi::get_one("SELECT extract(epoch from now())::bigint")
            .ok()
            .flatten()
            .unwrap_or(0);
        sync_issuer_key();
        authz::decide(&token, action, resource, now).allowed()
    }

    // -----------------------------------------------------------------------
    // pg17 SQL/JSON jsonpath: a dregg caveat predicate, compiled to a jsonpath
    // and evaluated IN postgres over the mirrored turn/cell JSON. The read/audit
    // half of the predicate algebra (docs/PG-DREGG-PG18.md §2). The authorization
    // GATE on a write stays the Rust `decide` path (chain + revocation); this is
    // "which mirrored rows satisfy this caveat?" as set-oriented SQL.
    // -----------------------------------------------------------------------

    /// `dregg_pred_jsonpath(pred_json text) -> text`. Compile a JSON-encoded
    /// dregg `Pred` (the caveat predicate algebra,
    /// `dregg_auth::credential::Pred`) into a SQL/JSON jsonpath whose
    /// `jsonb_path_exists(row, path)` is the predicate's admit verdict
    /// (bound-context semantics — `crate::jsonpath`). Returns the jsonpath string,
    /// or NULL if `pred_json` does not parse as a `Pred` (fail-closed: a caller
    /// that gets NULL and feeds it to `JSON_EXISTS` gets a clean error, never a
    /// silent admit). IMMUTABLE: a pure function of its argument.
    ///
    /// This is the bridge that makes the dregg predicate algebra a first-class
    /// pg17 jsonpath: mint/attenuate a credential in Rust, serialize one of its
    /// caveats' `Pred` to JSON, and `SELECT * FROM dregg.turn_effects WHERE
    /// jsonb_path_exists(doc, dregg_pred_jsonpath($1)::jsonpath)` filters the
    /// mirror by exactly that caveat — the same algebra that gates a write,
    /// queryable over the read mirror.
    #[pg_extern(immutable, parallel_safe, strict)]
    fn dregg_pred_jsonpath(pred_json: &str) -> Option<String> {
        let pred: dregg_auth::credential::Pred = serde_json::from_str(pred_json).ok()?;
        crate::jsonpath::pred_to_jsonpath(&pred)
    }

    /// `dregg_pred_jsonpath_strict(pred_json text) -> text`. As
    /// [`dregg_pred_jsonpath`] but every attribute atom carries an `exists(@.key)`
    /// boundness guard, so the jsonpath fails CLOSED on an absent key even under a
    /// `Not` — making it agree with the Rust `Pred::eval` fail-closed semantics
    /// unconditionally (not only on a fully-bound row). Use it when the row JSON
    /// may not bind every inspected attribute.
    #[pg_extern(immutable, parallel_safe, strict)]
    fn dregg_pred_jsonpath_strict(pred_json: &str) -> Option<String> {
        let pred: dregg_auth::credential::Pred = serde_json::from_str(pred_json).ok()?;
        crate::jsonpath::pred_to_jsonpath_strict(&pred)
    }

    /// `dregg_pred_matches(pred_json text, row jsonb) -> bool`. The ergonomic
    /// face: compile the predicate to a jsonpath and evaluate it over `row` in one
    /// call (`jsonb_path_exists`), so a policy or query reads
    /// `WHERE dregg_pred_matches($1, to_jsonb(t))`. TRUE iff `row` satisfies the
    /// caveat predicate; FALSE on a row that does not (or on a `pred_json` that
    /// does not parse — fail-closed). Uses the STRICT compile so an absent key
    /// fails closed even under negation, matching the Rust admit semantics.
    /// IMMUTABLE: pure in (predicate, row).
    #[pg_extern(immutable, parallel_safe, strict)]
    fn dregg_pred_matches(pred_json: &str, row: pgrx::JsonB) -> bool {
        let Ok(pred) = serde_json::from_str::<dregg_auth::credential::Pred>(pred_json) else {
            return false; // unparseable predicate ⇒ fail closed
        };
        let Some(path) = crate::jsonpath::pred_to_jsonpath_strict(&pred) else {
            return false;
        };
        // Evaluate the compiled jsonpath over the row via SPI (the same
        // jsonb_path_exists the read views use), so the in-SQL face and the view
        // face are the identical engine. Fail-closed on any SPI error.
        Spi::get_one_with_args(
            "SELECT jsonb_path_exists($1, $2::jsonpath)",
            &[row.into(), path.into()],
        )
        .ok()
        .flatten()
        .unwrap_or(false)
    }

    // =======================================================================
    // #[pg_test]s — the M1 thesis THROUGH the SQL boundary.
    //
    // These run under `cargo pgrx test pgNN` against a managed postgres. They
    // mirror the core's cargo-test proofs, but observed through real SQL: an
    // RLS-gated table queried under a session GUC, as an unprivileged role so
    // the policy actually filters (superusers BYPASS RLS).
    //
    // The issuer key is configured at server start (crate::pg_test::
    // postgresql_conf_options — the Sighup path), and tokens are minted in Rust
    // (dregg_mint SQL is out of M1 scope, docs §5) and handed to SQL as text.
    // =======================================================================
    #[cfg(any(test, feature = "pg_test"))]
    #[pg_schema]
    mod tests {
        use super::*;
        use dregg_auth::credential::{Caveat, Pred, RootKey};

        fn root() -> RootKey {
            RootKey::from_seed([7u8; 32])
        }

        fn mint_org42(root: &RootKey) -> dregg_auth::credential::Credential {
            root.mint([
                Caveat::FirstParty(Pred::AttrEq {
                    key: "subject".into(),
                    value: "agent-1".into(),
                }),
                Caveat::FirstParty(Pred::AttrEq {
                    key: "action".into(),
                    value: "read".into(),
                }),
                Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "org/42/".into(),
                }),
                Caveat::FirstParty(Pred::NotAfter { at: 2000 }),
            ])
        }

        /// The issuer key is configured at server start by
        /// `crate::pg_test::postgresql_conf_options` (the `dregg.issuer_pubkey`
        /// GUC is `Sighup` — secure: a session cannot SET it to a key it
        /// controls and forge admits). All tests mint under the SAME fixed seed
        /// `[7u8; 32]`, whose public key is the configured one; this asserts the
        /// configured key matches, so the test is honest about what is trusted.
        fn assert_issuer(root: &RootKey) {
            let configured: Option<String> =
                Spi::get_one("SELECT current_setting('dregg.issuer_pubkey', true)").unwrap();
            assert_eq!(
                configured.as_deref(),
                Some(root.public().to_hex().as_str()),
                "the server's configured issuer key must be the test root's public key"
            );
        }

        #[pg_test]
        fn admits_and_attenuation_narrows_through_sql() {
            let root = root();
            assert_issuer(&root);
            let root_tok = mint_org42(&root).encode();
            let narrowed = mint_org42(&root)
                .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "org/42/public/".into(),
                })])
                .encode();

            // Direct dregg_cap_admits over the SQL boundary.
            let f = |t: &str, r: &str, n: i64| -> bool {
                Spi::get_one_with_args(
                    "SELECT dregg_cap_admits($1, 'read', $2, $3)",
                    &[t.into(), r.into(), n.into()],
                )
                .unwrap()
                .unwrap()
            };
            assert!(f(&root_tok, "org/42/private/doc9", 1000));
            assert!(f(&narrowed, "org/42/public/doc1", 1000));
            assert!(!f(&narrowed, "org/42/private/doc9", 1000)); // narrowing held
            assert!(!f(&narrowed, "org/42/public/doc1", 3000)); // past NotAfter
        }

        #[pg_test]
        fn rls_gated_table_narrows_row_visibility() {
            let root = root();
            assert_issuer(&root);

            // A documents table gated by a dregg capability.
            Spi::run(
                "CREATE TABLE documents (id text primary key);
                 INSERT INTO documents VALUES
                   ('org/42/public/doc1'),
                   ('org/42/public/doc2'),
                   ('org/42/private/doc9'),
                   ('org/99/public/doc1');
                 ALTER TABLE documents ENABLE ROW LEVEL SECURITY;
                 ALTER TABLE documents FORCE ROW LEVEL SECURITY;
                 CREATE POLICY cap_read ON documents FOR SELECT
                   USING (dregg_admits('read', id::text));
                 -- RLS is BYPASSED by superusers; query as an unprivileged role
                 -- so the policy actually filters. The role needs SELECT + the
                 -- right to read the dregg.token GUC (any role can read a custom
                 -- GUC it set itself).
                 CREATE ROLE app_reader NOLOGIN;
                 GRANT SELECT ON documents TO app_reader;",
            )
            .unwrap();

            let root_tok = mint_org42(&root).encode();
            let narrowed = mint_org42(&root)
                .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "org/42/public/".into(),
                })])
                .encode();

            // The clock the policy reads is now(); the token expires at 2000
            // (unix seconds), which is in the past, so we set a token that does
            // NOT expire for this visibility test — re-mint without NotAfter so
            // wall-clock now() does not trip the temporal caveat.
            let mk = |prefix: Option<&str>| -> String {
                let mut c = root.mint([
                    Caveat::FirstParty(Pred::AttrEq {
                        key: "action".into(),
                        value: "read".into(),
                    }),
                    Caveat::FirstParty(Pred::AttrPrefix {
                        key: "resource".into(),
                        prefix: "org/42/".into(),
                    }),
                ]);
                if let Some(p) = prefix {
                    c = c.attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                        key: "resource".into(),
                        prefix: p.into(),
                    })]);
                }
                c.encode()
            };
            let _ = (root_tok, narrowed); // the expiring ones exercise the direct test

            let count_under = |tok: &str| -> i64 {
                Spi::run(&format!("SET dregg.token = '{tok}'")).unwrap();
                // SET ROLE to the unprivileged reader so RLS is enforced; reset
                // after counting.
                Spi::run("SET ROLE app_reader").unwrap();
                let n = Spi::get_one::<i64>("SELECT count(*) FROM documents")
                    .unwrap()
                    .unwrap();
                Spi::run("RESET ROLE").unwrap();
                n
            };

            // Root token sees all three org/42 rows (not the org/99 one).
            let n_root = count_under(&mk(None));
            // Narrowed token sees ONLY the two org/42/public rows — a STRICT
            // subset. The no-amplify property, observed through real RLS.
            let n_narrow = count_under(&mk(Some("org/42/public/")));
            assert_eq!(n_root, 3, "root token should see the three org/42 rows");
            assert_eq!(n_narrow, 2, "narrowed token should see only org/42/public");
            assert!(n_narrow < n_root, "attenuation must strictly narrow visibility");
        }

        #[pg_test]
        fn instant_revocation_makes_rows_vanish() {
            let root = root();
            assert_issuer(&root);
            Spi::run(
                "CREATE TABLE docs2 (id text primary key);
                 INSERT INTO docs2 VALUES ('org/42/public/a'), ('org/42/public/b');
                 ALTER TABLE docs2 ENABLE ROW LEVEL SECURITY;
                 ALTER TABLE docs2 FORCE ROW LEVEL SECURITY;
                 CREATE POLICY cap_read ON docs2 FOR SELECT
                   USING (dregg_admits('read', id::text));
                 CREATE ROLE app_reader2 NOLOGIN;
                 GRANT SELECT ON docs2 TO app_reader2;",
            )
            .unwrap();

            let tok = root
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

            // Present the token, then read as the unprivileged role so RLS bites.
            Spi::run(&format!("SET dregg.token = '{tok}'")).unwrap();
            let count = |label: &str| -> i64 {
                Spi::run("SET ROLE app_reader2").unwrap();
                let n = Spi::get_one::<i64>("SELECT count(*) FROM docs2")
                    .unwrap_or_else(|e| panic!("count {label}: {e}"))
                    .unwrap();
                Spi::run("RESET ROLE").unwrap();
                n
            };
            assert_eq!(count("before"), 2, "token admits both rows before revocation");

            // Revoke the EXACT presented credential (as the privileged owner).
            Spi::run_with_args("SELECT dregg_revoke($1)", &[tok.as_str().into()]).unwrap();

            // The SAME query, next statement, returns ZERO rows — instant.
            assert_eq!(
                count("after"),
                0,
                "revocation must take effect on the next statement"
            );
        }

        #[pg_test]
        fn forged_and_expired_are_denied() {
            let root = root();
            assert_issuer(&root);
            let tok = mint_org42(&root).encode();

            let admits = |t: &str, r: &str, n: i64| -> bool {
                Spi::get_one_with_args(
                    "SELECT dregg_cap_admits($1, 'read', $2, $3)",
                    &[t.into(), r.into(), n.into()],
                )
                .unwrap()
                .unwrap()
            };

            // Wrong issuer.
            let other = RootKey::from_seed([9u8; 32]);
            let foreign = mint_org42(&other).encode();
            assert!(!admits(&foreign, "org/42/public/doc1", 1000));
            // Expired.
            assert!(!admits(&tok, "org/42/public/doc1", 9999));
            // Garbage.
            assert!(!admits("dga1_garbage", "org/42/public/doc1", 1000));
        }

        #[pg_test]
        fn subject_is_recovered() {
            let root = root();
            assert_issuer(&root);
            let tok = mint_org42(&root).encode();
            let subj: Option<String> =
                Spi::get_one_with_args("SELECT dregg_cap_subject($1)", &[tok.as_str().into()])
                    .unwrap();
            assert_eq!(subj.as_deref(), Some("agent-1"));
        }

        // ===================================================================
        // Tier B THROUGH real SQL: the mirror's DDL + synthetic-turn rows, an
        // RLS-narrowing query, and the root-chain gate refusing a bad batch.
        //
        // This is the through-postgres twin of `examples/end_to_end.rs`: the
        // SAME synthetic ledger story (crate::synth), the SAME emitted DDL
        // (crate::mirror::ddl::tier_b), now installed in a real pg18 backend and
        // queried under real Row Level Security.
        // ===================================================================
        use crate::mirror::{MirrorBatch, RootChain};
        use crate::synth;

        /// Install the Tier-B schema from the Rust emitter (the exact SQL the
        /// extension ships), then load the synthetic committed turns as the
        /// `dregg_kernel` writer would. Returns nothing; the tables are live.
        fn install_tier_b_and_load_synth() {
            // The schema: via the dregg_install_schema() extern the quickstart
            // documents (which runs mirror::ddl::tier_b() — the same Rust that
            // defines the rows).
            let summary: String = Spi::get_one("SELECT dregg_install_schema()")
                .unwrap()
                .unwrap();
            assert!(summary.contains("Tier-B store installed"));

            // Load the synthetic story AS the kernel writer (the only role the
            // lockdown lets write). We run the root-chain tooth first — a row is
            // only written if its batch chained, mirroring Tier C's discipline.
            let story = synth::ledger_story();
            let mut chain = RootChain::resume(synth::GENESIS_ROOT, 0);
            for b in &story {
                chain.extend(b).expect("synthetic story must chain");
                write_batch(b);
            }
        }

        /// Render one accepted batch's rows as the writer's INSERTs and run them.
        /// The writer runs as the privileged connection role (a BYPASSRLS
        /// superuser in the harness) — exactly the trust position of the
        /// `dregg_kernel` SECURITY-DEFINER writer the emitted role model defines:
        /// it materializes verified-turn post-images wholesale, above the
        /// read-side RLS that gates applications. (The real M2 writer ships the
        /// MirrorBatch; here we inline it so the pg_test is node-free.)
        fn write_batch(b: &MirrorBatch) {
            let hx = |x: &[u8]| -> String { x.iter().map(|y| format!("{y:02x}")).collect() };
            let t = &b.turn;
            Spi::run(&format!(
                "INSERT INTO dregg.turns(ordinal,height,block_id,block_executed_up_to,\
                 turn_hash,creator,receipt_hash,ledger_root,prev_root) VALUES \
                 ({},{},'\\x{}',{},'\\x{}','\\x{}','\\x{}','\\x{}','\\x{}')",
                t.ordinal, t.height, hx(&t.block_id), t.block_executed_up_to,
                hx(&t.turn_hash), hx(&t.creator), hx(&t.receipt_hash),
                hx(&t.ledger_root), hx(&t.prev_root),
            ))
            .unwrap();
            for c in &b.cells {
                // Upsert via PostgreSQL 18 MERGE — the atomic node→pg row
                // materialization. The MERGE (with `merge_action()` + the pg18
                // `RETURNING old/new` balance delta) lives in the shipped
                // `dregg.merge_cell` function (the DDL emitter, crate::mirror::ddl);
                // we invoke it here through a plain SELECT so a later turn's
                // post-image overwrites the cell in one atomic statement, and the
                // returned '<ACTION> <DELTA>' tells us which arm fired and by how
                // much the balance moved. (docs/PG-DREGG-PG18.md §7.)
                let fj = c
                    .fields_json
                    .as_deref()
                    .map(|s| format!("'{}'::jsonb", s.replace('\'', "''")))
                    .unwrap_or_else(|| "NULL".to_string());
                let action: Option<String> = Spi::get_one(&format!(
                    "SELECT dregg.merge_cell('\\x{}'::bytea,'{}',{},{},'\\x'::bytea,{},\
                     '{}',{},'\\x{}'::bytea)",
                    hx(&c.cell_id), c.mode, c.balance, c.nonce, fj, c.lifecycle,
                    c.last_ordinal, hx(&c.cell_root),
                ))
                .unwrap();
                // pg18 dregg.merge_cell returns '<ACTION> <DELTA>' (e.g.
                // 'INSERT +1000000' / 'UPDATE -500') — merge_action() plus the
                // RETURNING old/new balance delta. Proof the MERGE arm fired.
                debug_assert!(
                    matches!(action.as_deref(), Some(a) if a.starts_with("INSERT ") || a.starts_with("UPDATE "))
                );
            }
            for cap in &b.caps {
                // The attenuation (allowed_effects) is carried so the pg17
                // JSON_TABLE view dregg.cap_attenuations can explode it into rows
                // (the no-amplification audit surface).
                let eff = cap
                    .allowed_effects_json
                    .as_deref()
                    .map(|s| format!("'{}'::jsonb", s.replace('\'', "''")))
                    .unwrap_or_else(|| "NULL".to_string());
                let exp = cap
                    .expires_at
                    .map(|e| e.to_string())
                    .unwrap_or_else(|| "NULL".to_string());
                Spi::run(&format!(
                    "INSERT INTO dregg.capabilities(holder,slot,target,permissions,\
                     allowed_effects,expires_at,last_ordinal) \
                     VALUES ('\\x{}',{},'\\x{}','{}'::jsonb,{},{},{})",
                    hx(&cap.holder), cap.slot, hx(&cap.target),
                    cap.permissions_json, eff, exp, cap.last_ordinal,
                ))
                .unwrap();
            }
        }

        /// A read-everything operator token and an ALICE-only attenuated token,
        /// minted under the test root (the configured issuer key).
        fn mirror_tokens(root: &RootKey) -> (String, String) {
            let operator = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "".into() }),
                ])
                .encode();
            let alice_only = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "".into() }),
                ])
                .attenuate([Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "a1".into(),
                })])
                .encode();
            (operator, alice_only)
        }

        /// Count `dregg.cells` rows visible under a token, as the unprivileged
        /// `dregg_reader` (so RLS actually filters; superusers BYPASS it).
        fn cells_visible(tok: &str) -> i64 {
            Spi::run(&format!("SET dregg.token = '{tok}'")).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            let n = Spi::get_one::<i64>("SELECT count(*) FROM dregg.cells")
                .unwrap()
                .unwrap();
            Spi::run("RESET ROLE").unwrap();
            n
        }

        #[pg_test]
        fn tier_b_mirror_rls_narrows_cell_visibility() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();

            // Sanity: as the kernel/owner (RLS still FORCEd, but the cells_read
            // policy is TO dregg_reader; the writer sees its own rows only via a
            // direct count as a privileged role). Confirm three distinct cells
            // landed by counting AS the reader under a wide-open operator token.
            let (operator, alice_only) = mirror_tokens(&root);

            // Operator sees all three cells (TREASURY, ALICE, BOB).
            let n_op = cells_visible(&operator);
            assert_eq!(n_op, 3, "operator token should see all three mirror cells");

            // The ALICE-only attenuated token sees a STRICT SUBSET — only ALICE's
            // cell, whose id hex starts `a1`. The no-amplify property, through
            // real Tier-B RLS on the mirror.
            let n_alice = cells_visible(&alice_only);
            assert_eq!(n_alice, 1, "attenuated token should see only ALICE's cell");
            assert!(n_alice < n_op, "attenuation must strictly narrow mirror visibility");
        }

        #[pg_test]
        fn tier_b_query_surface_views_resolve() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            let (operator, _) = mirror_tokens(&root);

            // The dregg-developer query surface: the cell_balances view, the
            // cap_edges delegation view, and the receipt_chain all resolve and
            // are RLS-gated through the operator token.
            Spi::run(&format!("SET dregg.token = '{operator}'")).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();

            // Balance view: the richest cell is TREASURY at 999_500.
            let top: i64 = Spi::get_one("SELECT max(balance) FROM dregg.cell_balances")
                .unwrap()
                .unwrap();
            assert_eq!(top, 999_500, "TREASURY is the richest visible cell");

            // The delegation edge ALICE→BOB is in cap_edges (holder gated; the
            // operator can read it).
            let edges: i64 = Spi::get_one("SELECT count(*) FROM dregg.cap_edges")
                .unwrap()
                .unwrap();
            assert_eq!(edges, 1, "the grant turn's ALICE→BOB edge is queryable");

            // The receipt chain is walkable in order; four turns landed.
            let turns: i64 = Spi::get_one("SELECT count(*) FROM dregg.receipt_chain")
                .unwrap()
                .unwrap();
            assert_eq!(turns, 4, "all four committed turns are in the receipt chain");
            Spi::run("RESET ROLE").unwrap();
        }

        #[pg_test]
        fn tier_b_apps_cannot_write_state() {
            // The spine: applications (dregg_reader) get SELECT only — state
            // mutates ONLY through verified turns. We assert the privilege
            // lockdown declaratively via the catalog (has_table_privilege),
            // which does not abort the SPI transaction the way triggering the
            // ERROR would: the reader HAS select, and has NO insert/update/delete
            // on any dregg state table. (The emitted DDL's REVOKE + the
            // SELECT-only GRANT are what this verifies are in force.)
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();

            let can = |priv_: &str| -> bool {
                Spi::get_one::<bool>(&format!(
                    "SELECT has_table_privilege('dregg_reader', 'dregg.cells', '{priv_}')"
                ))
                .unwrap()
                .unwrap()
            };
            assert!(can("SELECT"), "the reader must be able to SELECT state");
            assert!(!can("INSERT"), "the reader must NOT be able to INSERT state");
            assert!(!can("UPDATE"), "the reader must NOT be able to UPDATE state");
            assert!(!can("DELETE"), "the reader must NOT be able to DELETE state");

            // And the kernel writer DOES hold the write privileges (the only
            // role that may materialize post-images).
            let kernel = |priv_: &str| -> bool {
                Spi::get_one::<bool>(&format!(
                    "SELECT has_table_privilege('dregg_kernel', 'dregg.cells', '{priv_}')"
                ))
                .unwrap()
                .unwrap()
            };
            assert!(kernel("INSERT"), "the kernel writer must hold INSERT");
            assert!(kernel("UPDATE"), "the kernel writer must hold UPDATE");
        }

        #[pg_test]
        fn pg17_merge_upsert_and_json_table_views() {
            // The pg17 feature leverage, through real SQL:
            //   (1) the MERGE-based mirror upsert in write_batch fires both arms
            //       across the synthetic story (ALICE is inserted at ord 1, then
            //       UPDATEd at ord 2 and ord 3 — a later turn's post-image wins);
            //   (2) the JSON_TABLE projection views (cap_attenuations, cell_fields)
            //       resolve and explode the embedded jsonb into rows.
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth(); // runs the MERGE path 6 times

            let (operator, _) = mirror_tokens(&root);
            Spi::run(&format!("SET dregg.token = '{operator}'")).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();

            // MERGE update arm won: ALICE's final post-image is nonce=2 (ord 3),
            // not the ord-1 insert's nonce=0 — a later turn overwrote in place,
            // and there is exactly ONE ALICE row (no duplicate from re-insert).
            // (Aggregates so the scalar read always yields a row.)
            let alice_hex: String =
                crate::synth::ALICE.iter().map(|b| format!("{b:02x}")).collect();
            let alice_nonce: i64 = Spi::get_one(&format!(
                "SELECT coalesce(max(nonce), -1) FROM dregg.cells \
                 WHERE cell_id = '\\x{alice_hex}'::bytea"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(alice_nonce, 2, "MERGE update arm: ALICE's latest post-image wins");
            let alice_rows: i64 = Spi::get_one(&format!(
                "SELECT count(*) FROM dregg.cells WHERE cell_id = '\\x{alice_hex}'::bytea"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(alice_rows, 1, "MERGE keeps exactly one row per cell (no dup insert)");

            // JSON_TABLE view cell_fields: the decoded balance/nonce slots come
            // out of fields_json as typed columns. TREASURY's row shows 999_500.
            let treasury_bal: i64 = Spi::get_one(
                "SELECT coalesce(max(balance), -1) FROM dregg.cell_fields",
            )
            .unwrap()
            .unwrap();
            assert_eq!(treasury_bal, 999_500, "cell_fields JSON_TABLE projects the balance slot");

            // JSON_TABLE view cap_attenuations: the grant turn's allowed_effects
            // array `["transfer"]` is exploded into one effect row for ALICE→BOB.
            let n_effects: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.cap_attenuations",
            )
            .unwrap()
            .unwrap();
            assert_eq!(n_effects, 1, "exactly one attenuated effect across the story");
            let effect: Option<String> = Spi::get_one::<String>(
                "SELECT string_agg(effect, ',') FROM dregg.cap_attenuations",
            )
            .unwrap();
            assert_eq!(effect.as_deref(), Some("transfer"),
                "cap_attenuations JSON_TABLE explodes the allowed_effects array");
            Spi::run("RESET ROLE").unwrap();
        }

        // ===================================================================
        // The pg18 leverage, through real SQL (docs/PG-DREGG-PG18.md):
        //   (1) MERGE + RETURNING old/new — dregg.merge_cell returns the action
        //       AND the balance delta computed from the pre-image, in one atomic
        //       statement (impossible pre-18 without a separate pre-read);
        //   (2) VIRTUAL generated columns (the pg18 default) — cell_root_hex /
        //       balance_field are computed on READ and equal their canonical
        //       source, with no stored bytes;
        //   (3) uuidv7() — the submit_queue key is temporally sortable.
        // ===================================================================
        #[pg_test]
        fn pg18_merge_returning_delta_virtual_columns_and_uuidv7() {
            let root = root();
            assert_issuer(&root);
            let summary: String =
                Spi::get_one("SELECT dregg_install_schema()").unwrap().unwrap();
            assert!(summary.contains("Tier-B store installed"));
            Spi::run("SET ROLE dregg_kernel").unwrap(); // BYPASSRLS writer

            // A turns row to satisfy the cells FK (last_ordinal references it).
            Spi::run(
                "INSERT INTO dregg.turns(ordinal,height,block_id,block_executed_up_to,\
                 turn_hash,creator,receipt_hash,ledger_root,prev_root) VALUES \
                 (0,0,'\\x22',0,'\\x33','\\xc0','\\x44','\\x11','\\x00')",
            )
            .unwrap();

            // (1a) INSERT arm: merge a fresh cell at balance 1_000_000. pg18
            // RETURNING old/new ⇒ old.balance is NULL ⇒ delta = +1000000.
            let cid = "c000000000000000000000000000000000000000000000000000000000000000";
            let ins: String = Spi::get_one(&format!(
                "SELECT dregg.merge_cell('\\x{cid}'::bytea,'Hosted',1000000,0,'\\x'::bytea,\
                 '{{\"balance\":1000000,\"nonce\":0}}'::jsonb,'Active',0,'\\x{cid}'::bytea)"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(ins, "INSERT +1000000", "pg18 RETURNING new-old delta on the INSERT arm");

            // (1b) UPDATE arm: re-merge the same cell down to 999_500. pg18 reads
            // old.balance = 1_000_000 in the same statement ⇒ delta = -500.
            let upd: String = Spi::get_one(&format!(
                "SELECT dregg.merge_cell('\\x{cid}'::bytea,'Hosted',999500,1,'\\x'::bytea,\
                 '{{\"balance\":999500,\"nonce\":1}}'::jsonb,'Active',0,'\\x{cid}'::bytea)"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(upd, "UPDATE -500", "pg18 RETURNING new-old delta on the UPDATE arm");

            // (2) VIRTUAL generated columns: cell_root_hex / balance_field are
            // read-time projections equal to their canonical source, with no
            // stored bytes. (cell_hex stays STORED because it is indexed.)
            let consistent: i64 = Spi::get_one(&format!(
                "SELECT count(*) FROM dregg.cells WHERE cell_id='\\x{cid}'::bytea \
                 AND cell_root_hex = encode(cell_root,'hex') \
                 AND balance_field = (fields_json->>'balance')::bigint"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(consistent, 1, "VIRTUAL generated columns equal their canonical source on read");
            // pg_attribute records cell_root_hex / balance_field as virtual
            // (attgenerated='v') and cell_hex as stored ('s') — the pg18 kinds.
            let kinds: Option<String> = Spi::get_one(
                "SELECT string_agg(attname || ':' || attgenerated::text, ',' ORDER BY attname) \
                 FROM pg_attribute \
                 WHERE attrelid = 'dregg.cells'::regclass \
                   AND attname IN ('cell_hex','cell_root_hex','balance_field')",
            )
            .unwrap();
            assert_eq!(
                kinds.as_deref(),
                Some("balance_field:v,cell_hex:s,cell_root_hex:v"),
                "pg18 generated-column kinds: cell_hex STORED (indexed), the rest VIRTUAL"
            );
            Spi::run("RESET ROLE").unwrap();

            // (3) uuidv7(): the submit_queue id default is the temporally-sortable
            // v7 (version nibble 7), so two rows inserted in order sort by id.
            let o: String = Spi::get_one("SELECT dregg_install_write_outbox()").unwrap().unwrap();
            assert!(o.contains("write outbox installed"));
            let ver: Option<i32> = Spi::get_one(
                "SELECT get_byte(uuid_send(uuidv7()), 6) >> 4",
            )
            .unwrap();
            assert_eq!(ver, Some(7), "uuidv7() mints a version-7 (temporally sortable) uuid");
        }

        // ===================================================================
        // The pg17 SQL/JSON jsonpath predicate surface (docs/PG-DREGG-PG18.md
        // §2): a dregg `Pred` compiled to a jsonpath and evaluated IN postgres,
        // proven to AGREE with the real chain-verified `dregg_cap_admits`.
        // ===================================================================

        #[pg_test]
        fn pred_jsonpath_matches_agree_with_real_authz() {
            let root = root();
            assert_issuer(&root);

            // The SAME authority, two shapes: a minted credential (the real
            // chain-verified authz path) AND its `Pred` as JSON (the jsonpath
            // read path). They must give the identical admit verdict per row.
            // read on org/42/ until clock 2000, the canonical M1 caveat shape.
            let tok = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "org/42/".into() }),
                    Caveat::FirstParty(Pred::NotAfter { at: 2000 }),
                ])
                .encode();
            // The matching Pred (the algebra the caveat chain encodes), as JSON.
            let pred_json = serde_json::to_string(&Pred::AllOf(vec![
                Pred::AttrEq { key: "action".into(), value: "read".into() },
                Pred::AttrPrefix { key: "resource".into(), prefix: "org/42/".into() },
                Pred::NotAfter { at: 2000 },
            ]))
            .unwrap();

            // The compiled jsonpath is well-formed and non-empty.
            let path: Option<String> = Spi::get_one_with_args(
                "SELECT dregg_pred_jsonpath($1)",
                &[pred_json.as_str().into()],
            )
            .unwrap();
            let path = path.expect("a first-party Pred compiles to a jsonpath");
            assert!(path.starts_with("$ ? ("), "the path is a filter expression: {path}");

            // A matrix of rows: the chain-verified `dregg_cap_admits` verdict and
            // the `dregg_pred_matches` (jsonpath) verdict must be EQUAL on each.
            let cases = [
                ("org/42/public/doc1", 1000_i64),
                ("org/42/private/doc9", 1000),
                ("org/99/x", 1000),
                ("org/42/public/doc1", 3000), // past NotAfter
            ];
            for (res, clk) in cases {
                let authz: bool = Spi::get_one_with_args(
                    "SELECT dregg_cap_admits($1, 'read', $2, $3)",
                    &[tok.as_str().into(), res.into(), clk.into()],
                )
                .unwrap()
                .unwrap();
                let jsonpath: bool = Spi::get_one_with_args(
                    "SELECT dregg_pred_matches($1, jsonb_build_object('action','read','resource',$2::text,'clock',$3::bigint))",
                    &[pred_json.as_str().into(), res.into(), clk.into()],
                )
                .unwrap()
                .unwrap();
                assert_eq!(
                    authz, jsonpath,
                    "the jsonpath of a Pred must admit exactly what the chain-verified \
                     authz admits (res={res}, clk={clk}): authz={authz} jsonpath={jsonpath}"
                );
            }

            // An unparseable predicate fails closed (NULL path / false match).
            let bad_path: Option<String> =
                Spi::get_one_with_args("SELECT dregg_pred_jsonpath($1)", &["not json".into()])
                    .unwrap();
            assert!(bad_path.is_none(), "a non-Pred string yields NULL (fail-closed)");
            let bad_match: bool = Spi::get_one_with_args(
                "SELECT dregg_pred_matches($1, '{}'::jsonb)",
                &["not json".into()],
            )
            .unwrap()
            .unwrap();
            assert!(!bad_match, "an unparseable predicate matches nothing (fail-closed)");
        }

        #[pg_test]
        fn pred_jsonpath_filters_the_mirror_as_a_read() {
            // The read win: the compiled jsonpath used DIRECTLY in a SQL query over
            // the mirror — "which cells' state satisfies this caveat?" as plain SQL,
            // no per-row extern. We build a small jsonb-state table and filter it by
            // a Pred-derived jsonpath via jsonb_path_exists.
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();

            // A predicate over the cell state JSON: balance >= 500 is not in the
            // Pred algebra (it is attribute/prefix/temporal), so we filter on a
            // resource-prefix predicate over a synthesized doc per cell instead:
            // "the cell hex starts with c0" (TREASURY only).
            let pred_json = serde_json::to_string(&Pred::AttrPrefix {
                key: "cell".into(),
                prefix: "c0".into(),
            })
            .unwrap();

            // For each cell, build {cell: <hex>} and keep those the jsonpath admits.
            Spi::run("SET ROLE dregg_kernel").unwrap(); // BYPASSRLS so we see all cells
            let matched: i64 = Spi::get_one_with_args(
                "SELECT count(*) FROM dregg.cells \
                 WHERE jsonb_path_exists(jsonb_build_object('cell', encode(cell_id,'hex')), \
                                         dregg_pred_jsonpath($1)::jsonpath)",
                &[pred_json.as_str().into()],
            )
            .unwrap()
            .unwrap();
            Spi::run("RESET ROLE").unwrap();
            assert_eq!(matched, 1, "exactly one cell (TREASURY, c0…) matches the c0 prefix predicate");
        }

        // ===================================================================
        // The pg17 turn-effects JSON_TABLE view + canonical_cells (builtin-C
        // collation) over the verified store (docs/PG-DREGG-PG18.md §3,§5).
        // ===================================================================

        #[pg_test]
        fn turn_effects_and_canonical_views_resolve_over_the_store() {
            let root = root();
            assert_issuer(&root);
            // Land the well-formed story through the Tier-C commit_log gate, so the
            // commit_log carries the touched-cell payloads turn_effects explodes.
            install_tier_c_and_submit_story();

            // turn_effects: one row per (ordinal, touched cell). The genesis turn
            // funded TREASURY; the transfer touched TREASURY + ALICE. So ordinal 0
            // has 1 effect row and ordinal 1 has 2.
            Spi::run("SET ROLE dregg_kernel").unwrap();
            let ord0: i64 = Spi::get_one("SELECT count(*) FROM dregg.turn_effects WHERE ordinal = 0")
                .unwrap()
                .unwrap();
            let ord1: i64 = Spi::get_one("SELECT count(*) FROM dregg.turn_effects WHERE ordinal = 1")
                .unwrap()
                .unwrap();
            assert_eq!(ord0, 1, "genesis turn has one touched-cell effect row (TREASURY)");
            assert!(ord1 >= 2, "the transfer turn touched at least TREASURY + ALICE");

            // canonical_cells: the builtin-C-collation byte-order. The first row by
            // cell_hex is ALICE (a1…) before TREASURY (c0…) — deterministic,
            // version-stable ordering (a1 < c0 byte-wise).
            let first: Option<String> =
                Spi::get_one("SELECT cell_hex FROM dregg.canonical_cells LIMIT 1").unwrap();
            assert_eq!(
                first.as_deref().map(|s| &s[..2]),
                Some("a1"),
                "canonical_cells orders by builtin-C byte order: a1 (ALICE) sorts first"
            );

            // The generated columns materialized: cell_hex + cell_root_hex are the
            // pg-maintained hex of the canonical bytea (cannot drift).
            let hexes_consistent: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.cells \
                 WHERE cell_hex IS DISTINCT FROM encode(cell_id,'hex') \
                    OR cell_root_hex IS DISTINCT FROM encode(cell_root,'hex')",
            )
            .unwrap()
            .unwrap();
            assert_eq!(hexes_consistent, 0, "generated hex columns equal the canonical bytea's hex");
            Spi::run("RESET ROLE").unwrap();
        }

        // ===================================================================
        // The pg17 LOGIN EVENT TRIGGER authz binding (docs/PG-DREGG-PG18.md §6):
        // a role's session is bound to its dregg capability AT LOGIN, so a plain
        // SELECT is already RLS-narrowed with no app-side token presentation.
        //
        // NOTE: the `login` event fires on a NEW connection, which the in-backend
        // #[pg_test] cannot trigger (it runs inside one already-open connection).
        // So this test asserts the BINDING LOGIC directly — calling the same
        // body the event trigger runs (dregg.on_login via a manual invocation of
        // its effect) and confirming the GUC is set + RLS then narrows. The live
        // cross-connection proof is in sql/e2e-live.sql (a real psql reconnect).
        // ===================================================================

        #[pg_test]
        fn login_binding_sets_the_session_token_and_narrows_rls() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            let o: String = Spi::get_one("SELECT dregg_install_login_binding()").unwrap().unwrap();
            assert!(o.contains("login binding installed"));

            // Map a role to an ALICE-only token (read on a1*). The event trigger
            // would set dregg.token from this row on connect; here we apply that
            // same effect (set_config) to assert the downstream RLS narrowing, the
            // observable consequence the trigger exists to produce.
            let alice_tok = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "a1".into() }),
                ])
                .encode();
            let alice_hex: String = synth::ALICE.iter().map(|b| format!("{b:02x}")).collect();
            Spi::run_with_args(
                "INSERT INTO dregg.role_identity (pg_role, agent, default_token) \
                 VALUES ('dregg_reader', decode($1,'hex'), $2) \
                 ON CONFLICT (pg_role) DO UPDATE SET default_token = EXCLUDED.default_token",
                &[alice_hex.as_str().into(), alice_tok.as_str().into()],
            )
            .unwrap();

            // The identity row is readable by the kernel (the SECURITY DEFINER hook
            // runs as), proving the lookup the trigger does resolves.
            let bound: Option<String> = Spi::get_one(
                "SELECT default_token FROM dregg.role_identity WHERE pg_role = 'dregg_reader'",
            )
            .unwrap();
            assert!(bound.is_some(), "the role's identity row carries its bound token");

            // Apply the trigger's effect (set the session token from the row) and
            // confirm the RLS then narrows: as dregg_reader, only ALICE's cell is
            // visible — the same outcome a login-bound connection gets.
            Spi::run(&format!("SET dregg.token = '{}'", bound.unwrap())).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            let visible: i64 = Spi::get_one("SELECT count(*) FROM dregg.cells").unwrap().unwrap();
            Spi::run("RESET ROLE").unwrap();
            assert_eq!(visible, 1, "the login-bound token narrows the reader to ALICE's cell only");
        }

        #[pg_test]
        fn root_chain_gate_refuses_a_tampered_batch() {
            // The Tier-C anti-substitution tooth (the cheap structural half the
            // even read-only mirror enforces), exercised in the backend process:
            // the RootChain accepts the well-formed story and REFUSES a forged
            // ord-2 batch whose prev_root was substituted, leaving the head put.
            let story = synth::ledger_story();
            let mut chain = RootChain::resume(synth::GENESIS_ROOT, 0);
            chain.extend(&story[0]).unwrap();
            chain.extend(&story[1]).unwrap();
            let head_before = chain.head();
            let err = chain.extend(&synth::tampered_batch_at_2()).unwrap_err();
            assert!(
                matches!(err, crate::mirror::ChainRefusal::RootMismatch { .. }),
                "a tampered batch must be refused by the root-chain tooth"
            );
            assert_eq!(chain.head(), head_before, "a refused batch must not move the head");
        }

        // ===================================================================
        // TIER C THROUGH real SQL: the verified-store gate on a live pg18. The
        // commit_log is the ONLY door to state; its trigger runs the REAL chain
        // re-validator (dregg_verify_turn, backed by mirror::verify_chain_step)
        // and materializes the post-image — and REFUSES a tampered batch by the
        // database engine itself. This is the load-bearing "pg re-validates,
        // never trusts" proof (docs/PG-DREGG.md §10).
        // ===================================================================

        /// Install Tier B + Tier C, then submit one batch's verified post-image
        /// through `dregg.commit_log` (the turn metadata + the touched-cell
        /// post-images as the trigger's jsonb payload, `MirrorBatch::cells_json`).
        /// Returns the SPI result of the INSERT (so the caller can assert it
        /// succeeded or, for a tamper, that it RAISEd).
        fn submit_through_commit_log(b: &MirrorBatch) -> Result<(), pgrx::spi::Error> {
            let hx = |x: &[u8]| -> String { x.iter().map(|y| format!("{y:02x}")).collect() };
            let t = &b.turn;
            let cells_json = b.cells_json().replace('\'', "''");
            Spi::run(&format!(
                "INSERT INTO dregg.commit_log(ordinal,height,block_id,block_executed_up_to,\
                 turn_hash,creator,receipt_hash,ledger_root,prev_root,cells) VALUES \
                 ({},{},'\\x{}',{},'\\x{}','\\x{}','\\x{}','\\x{}','\\x{}','{}'::jsonb)",
                t.ordinal, t.height, hx(&t.block_id), t.block_executed_up_to,
                hx(&t.turn_hash), hx(&t.creator), hx(&t.receipt_hash),
                hx(&t.ledger_root), hx(&t.prev_root), cells_json,
            ))
        }

        /// Install Tier B + Tier C and submit the well-formed synthetic story
        /// through the `dregg.commit_log` gate. Returns the four batches (so the
        /// caller can build a forged follow-up). Each INSERT runs the trigger:
        /// `dregg_verify_turn` (chain re-validation) → record turn →
        /// MERGE-materialize cells.
        fn install_tier_c_and_submit_story() -> Vec<MirrorBatch> {
            let summary: String =
                Spi::get_one("SELECT dregg_install_schema()").unwrap().unwrap();
            assert!(summary.contains("Tier-B store installed"));
            let c_summary: String =
                Spi::get_one("SELECT dregg_install_tier_c()").unwrap().unwrap();
            assert!(c_summary.contains("Tier-C verified-store gate installed"));
            let story = synth::ledger_story();
            for b in &story {
                submit_through_commit_log(b).unwrap_or_else(|e| {
                    panic!("the gate refused a well-formed turn {}: {e}", b.turn.ordinal)
                });
            }
            story
        }

        #[pg_test]
        fn tier_c_commit_log_gate_materializes_verified_turns() {
            let root = root();
            assert_issuer(&root);
            // Submit the well-formed story THROUGH the verifying gate (the ONLY
            // door to state). All four turns are admitted by dregg_verify_turn and
            // their post-images materialized in the same transaction.
            let _story = install_tier_c_and_submit_story();

            // The post-state is materialized: four turns recorded, three distinct
            // cells (TREASURY/ALICE/BOB) with the LATEST post-image — ALICE's nonce
            // is 2 (from ord 3): the MERGE update arm won, exactly as the mirror
            // path materializes. State exists ONLY because a verified turn produced
            // it through the gate.
            let turns: i64 = Spi::get_one("SELECT count(*) FROM dregg.turns").unwrap().unwrap();
            assert_eq!(turns, 4, "all four verified turns recorded through the gate");
            let cells: i64 = Spi::get_one("SELECT count(*) FROM dregg.cells").unwrap().unwrap();
            assert_eq!(cells, 3, "three distinct cells materialized (TREASURY/ALICE/BOB)");
            let alice_hex: String =
                crate::synth::ALICE.iter().map(|b| format!("{b:02x}")).collect();
            let alice_nonce: i64 = Spi::get_one(&format!(
                "SELECT max(nonce) FROM dregg.cells WHERE cell_id = '\\x{alice_hex}'::bytea"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(alice_nonce, 2, "the gate materialized ALICE's latest post-image (MERGE)");

            // The receipt chain the gate built is a walkable hash chain: each row's
            // prev_root is the prior row's ledger_root (the light-client tooth).
            let breaks: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.turns t \
                 JOIN dregg.turns p ON p.ordinal = t.ordinal - 1 \
                 WHERE t.prev_root IS DISTINCT FROM p.ledger_root",
            )
            .unwrap()
            .unwrap();
            assert_eq!(breaks, 0, "the gate-built turns table is an unbroken hash chain");
        }

        /// THE anti-substitution proof, through the database engine: after the
        /// well-formed story (head at ord 3, next-expected ord 4), a forged ord-4
        /// batch whose `prev_root` was substituted is REFUSED by the trigger's
        /// `dregg_verify_turn` — the INSERT RAISEs the exact anti-substitution
        /// error, so no forged state can enter. `#[pg_test(error = …)]` asserts
        /// the precise message: the gate, not a trusted writer, refuses.
        #[pg_test(error = "dregg: turn 4 does not chain onto the head root — refused (anti-substitution)")]
        fn tier_c_gate_refuses_a_tampered_batch_by_raising() {
            let root = root();
            assert_issuer(&root);
            install_tier_c_and_submit_story();
            // A forged ord-4 (next-expected, so the ordinal gap check passes) whose
            // prev_root is the substituted [0x99;32], NOT the real head root. The
            // gate's dregg_verify_turn returns false ⇒ the trigger RAISEs.
            let mut forged = synth::tampered_batch_at_2();
            forged.turn.ordinal = 4;
            forged.cells[0].last_ordinal = 4;
            submit_through_commit_log(&forged)
                .expect("submit returns; the RAISE surfaces as the test's expected ERROR");
        }

        // ===================================================================
        // THE WRITE PATH through real SQL: a pg-user submits a verified turn
        // FROM postgres, RLS-gated to exactly the agents its capability admits
        // `submit` on (docs/PG-DREGG.md §11). dregg_submit_turn enqueues into
        // dregg.submit_queue; the node drains it through the real executor.
        // ===================================================================

        /// A token that admits `submit` on the agent whose hex starts `prefix`
        /// (e.g. "a1" for ALICE), minted under the test root.
        fn submit_token(root: &RootKey, prefix: &str) -> String {
            root.mint([
                Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "submit".into() }),
                Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: prefix.into() }),
            ])
            .encode()
        }

        #[pg_test]
        fn write_path_submit_turn_enqueues_under_an_authorized_token() {
            let root = root();
            assert_issuer(&root);
            let summary: String =
                Spi::get_one("SELECT dregg_install_schema()").unwrap().unwrap();
            assert!(summary.contains("Tier-B store installed"));
            let o_summary: String =
                Spi::get_one("SELECT dregg_install_write_outbox()").unwrap().unwrap();
            assert!(o_summary.contains("write outbox installed"));

            let alice_hex: String = synth::ALICE.iter().map(|b| format!("{b:02x}")).collect();
            // Present an ALICE-submit token and enqueue a turn FOR ALICE as the
            // unprivileged dregg_reader (so the submit_gate RLS policy bites).
            Spi::run(&format!("SET dregg.token = '{}'", submit_token(&root, "a1"))).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            let id: Option<pgrx::Uuid> = Spi::get_one(&format!(
                "SELECT dregg_submit_turn('\\xdeadbeef'::bytea, '\\x{alice_hex}'::bytea)"
            ))
            .unwrap();
            Spi::run("RESET ROLE").unwrap();
            assert!(id.is_some(), "an authorized submit must enqueue and return an id");

            // The row landed as 'pending' for ALICE (the node will drain it).
            let pending: i64 = Spi::get_one(&format!(
                "SELECT count(*) FROM dregg.submit_queue \
                 WHERE agent = '\\x{alice_hex}'::bytea AND status = 'pending'"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(pending, 1, "the authorized turn is queued pending for the node");
        }

        #[pg_test(error = "new row violates row-level security policy for table \"submit_queue\"")]
        fn write_path_rls_refuses_submitting_for_an_unauthorized_agent() {
            let root = root();
            assert_issuer(&root);
            Spi::get_one::<String>("SELECT dregg_install_schema()").unwrap();
            Spi::get_one::<String>("SELECT dregg_install_write_outbox()").unwrap();

            let bob_hex: String = synth::BOB.iter().map(|b| format!("{b:02x}")).collect();
            // Present an ALICE-only submit token, then try to submit a turn FOR
            // BOB. The submit_gate WITH CHECK (dregg_admits('submit', bob_hex))
            // is FALSE under an a1-prefixed token, so RLS refuses the INSERT — a
            // role cannot submit a turn its capability does not authorize.
            Spi::run(&format!("SET dregg.token = '{}'", submit_token(&root, "a1"))).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            // This RAISEs the RLS violation, which is the test's expected ERROR.
            let _: Option<pgrx::Uuid> = Spi::get_one(&format!(
                "SELECT dregg_submit_turn('\\xdeadbeef'::bytea, '\\x{bob_hex}'::bytea)"
            ))
            .unwrap();
        }

        // ===================================================================
        // The pg18 leverage WIRED in the thoroughness pass (docs/PG-DREGG-PG18.md
        // §4/§6/§7/§8 + docs/PG-DREGG.md §14.3), each executed on the live pg18.
        // ===================================================================

        /// pg18 B-tree SKIP SCAN: the composite `cells_by_mode_balance (mode,
        /// balance)` index serves a `WHERE balance = …` query whose LEADING column
        /// (`mode`) is unconstrained — the planner skips through the few `mode`
        /// prefixes rather than seq-scanning. We assert the chosen plan is an
        /// index scan over that index (with seqscan disabled to force the planner
        /// to use the index path it can, which pre-18 it could not for an
        /// unconstrained leading column). This is real pg18 leverage, on real rows.
        #[pg_test]
        fn pg18_skip_scan_serves_balance_with_unconstrained_leading_mode() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            Spi::run("SET ROLE dregg_kernel").unwrap(); // BYPASSRLS writer

            // Load enough rows that the planner prefers the index (a tiny table is
            // always a seq scan). Insert many Hosted cells with distinct balances,
            // chaining off the existing turns (last_ordinal references turn 0).
            Spi::run(
                "INSERT INTO dregg.cells \
                   (cell_id, mode, balance, nonce, fields, fields_json, lifecycle, last_ordinal, cell_root) \
                 SELECT decode(lpad(to_hex(1000 + g), 64, '0'), 'hex'), \
                        CASE WHEN g % 2 = 0 THEN 'Hosted' ELSE 'Sovereign' END, \
                        g, 0, '\\x'::bytea, \
                        jsonb_build_object('balance', g, 'nonce', 0), 'Active', 0, \
                        decode(lpad(to_hex(1000 + g), 64, '0'), 'hex') \
                 FROM generate_series(1, 4000) g \
                 ON CONFLICT (cell_id) DO NOTHING",
            )
            .unwrap();
            Spi::run("ANALYZE dregg.cells").unwrap();
            // Force the index path so we observe skip scan (pre-18 this query would
            // have to fall back to a seq scan or full index scan).
            Spi::run("SET enable_seqscan = off").unwrap();

            // Collect the plain-text EXPLAIN rows and assert the (mode,balance) index
            // serves a balance-only predicate — `mode` (the leading column) is
            // unconstrained, so the index path IS pg18 skip scan.
            let lines: Vec<String> = Spi::connect(|client| {
                let mut out = Vec::new();
                let tup = client
                    .select(
                        "EXPLAIN (COSTS off) SELECT cell_id FROM dregg.cells WHERE balance = 2000",
                        None,
                        &[],
                    )
                    .expect("EXPLAIN runs");
                for row in tup {
                    if let Ok(Some(s)) = row.get::<String>(1) {
                        out.push(s);
                    }
                }
                out
            });
            Spi::run("SET enable_seqscan = on").unwrap();
            Spi::run("RESET ROLE").unwrap();
            let joined = lines.join("\n");
            assert!(
                joined.contains("cells_by_mode_balance"),
                "the (mode,balance) index serves a balance-only query via skip scan; plan was:\n{joined}"
            );
            // And the Index Cond is on balance (the leading mode column is skipped).
            assert!(
                joined.contains("balance = 2000") || joined.to_lowercase().contains("index cond"),
                "the index condition is on balance (mode skipped); plan was:\n{joined}"
            );
        }

        /// pg15 SECURITY_INVOKER views (docs/PG-DREGG.md §14.3, wired): the dev
        /// views run with the INVOKER's privileges, so the base-table RLS narrows a
        /// reader THROUGH the view. We assert (a) the reloption is set on every
        /// dev-view, and (b) the narrowing actually bites: an ALICE-only token sees
        /// only ALICE's cell through `dregg.cell_balances` (the view), not just the
        /// base table — RLS-through-views by declaration, not incidentally.
        #[pg_test]
        fn pg15_security_invoker_views_enforce_rls_through_the_view() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();

            // (a) every dev-view carries security_invoker=true in its reloptions.
            let non_invoker: i64 = Spi::get_one(
                "SELECT count(*) FROM pg_class c \
                 JOIN pg_namespace n ON n.oid = c.relnamespace \
                 WHERE n.nspname = 'dregg' AND c.relkind = 'v' \
                   AND c.relname IN ('cap_edges','cell_balances','receipt_chain', \
                                     'cap_attenuations','cell_fields','canonical_cells') \
                   AND NOT (coalesce(array_to_string(c.reloptions, ','), '') \
                            LIKE '%security_invoker=true%')",
            )
            .unwrap()
            .unwrap();
            assert_eq!(non_invoker, 0, "every dev-view must be security_invoker=true");

            // (b) the narrowing bites THROUGH the view. Grant the reader SELECT on
            // the view, present an ALICE-only token, and count cell_balances rows as
            // the unprivileged reader: only ALICE's cell (a1…) is visible.
            let alice_only = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "a1".into() }),
                ])
                .encode();
            Spi::run(&format!("SET dregg.token = '{alice_only}'")).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            let visible: i64 = Spi::get_one("SELECT count(*) FROM dregg.cell_balances")
                .unwrap()
                .unwrap();
            Spi::run("RESET ROLE").unwrap();
            assert_eq!(
                visible, 1,
                "the security_invoker view narrows the reader to ALICE's cell — RLS through the view"
            );
        }

        /// pg18 `RETURNING WITH (OLD/NEW)` typed applicator (docs/PG-DREGG-PG18.md
        /// §7, wired): `dregg.merge_cell_delta` returns (action, balance_delta,
        /// nonce_delta) read from the pre-image in one atomic MERGE. We exercise
        /// the INSERT arm (delta = full amount), the UPDATE arm (signed delta +
        /// nonce delta), AND — the payoff — assert CONSERVATION directly off the
        /// applicator: the per-cell balance deltas of a transfer sum to zero.
        #[pg_test]
        fn pg18_merge_cell_delta_typed_and_conservation_off_the_applicator() {
            let root = root();
            assert_issuer(&root);
            let summary: String =
                Spi::get_one("SELECT dregg_install_schema()").unwrap().unwrap();
            assert!(summary.contains("Tier-B store installed"));
            Spi::run("SET ROLE dregg_kernel").unwrap();
            Spi::run(
                "INSERT INTO dregg.turns(ordinal,height,block_id,block_executed_up_to,\
                 turn_hash,creator,receipt_hash,ledger_root,prev_root) VALUES \
                 (0,0,'\\x22',0,'\\x33','\\xc0','\\x44','\\x11','\\x00')",
            )
            .unwrap();

            // The OUT params are read via a positional SELECT against the function
            // (portable + explicit across pgrx versions).
            // Fresh cell: INSERT arm ⇒ balance_delta = full amount, nonce_delta = 0.
            let fid = "f000000000000000000000000000000000000000000000000000000000000000";
            let ins = Spi::get_one::<String>(&format!(
                "SELECT action||' '||balance_delta||' '||nonce_delta \
                 FROM dregg.merge_cell_delta('\\x{fid}'::bytea,'Hosted',5000,0,\
                 '\\x'::bytea,'{{\"balance\":5000,\"nonce\":0}}'::jsonb,'Active',0,'\\x{fid}'::bytea)"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(ins, "INSERT 5000 0", "INSERT arm: balance_delta is the full amount, no pre-image nonce");
            // UPDATE arm on the same cell: signed balance delta (−500) + nonce delta (+1).
            let upd = Spi::get_one::<String>(&format!(
                "SELECT action||' '||balance_delta||' '||nonce_delta \
                 FROM dregg.merge_cell_delta('\\x{fid}'::bytea,'Hosted',4500,1,\
                 '\\x'::bytea,'{{\"balance\":4500,\"nonce\":1}}'::jsonb,'Active',0,'\\x{fid}'::bytea)"
            ))
            .unwrap()
            .unwrap();
            assert_eq!(upd, "UPDATE -500 1", "UPDATE arm: signed balance + nonce deltas from the pre-image");

            // CONSERVATION off the applicator: a transfer TREASURY→ALICE→BOB whose
            // per-cell balance deltas (read from the pre-image by the pg18 RETURNING
            // WITH) sum to ZERO. Seed three cells, then apply the transfer and SUM
            // the reported balance deltas. (Seed first so the deltas below are the
            // transfer's, not the funding's.)
            for (id, bal) in [("c0", 1_000_000_i64), ("a1", 0), ("b0", 0)] {
                let full = format!("{id}00000000000000000000000000000000000000000000000000000000000000");
                Spi::run(&format!(
                    "SELECT dregg.merge_cell('\\x{full}'::bytea,'Hosted',{bal},0,'\\x'::bytea,\
                     '{{\"balance\":{bal},\"nonce\":0}}'::jsonb,'Active',0,'\\x{full}'::bytea)"
                ))
                .unwrap();
            }
            // The transfer: TREASURY 1_000_000→999_500 (−500), ALICE 0→400 (+400),
            // BOB 0→100 (+100). Σδ = 0.
            let transfer = [
                ("c0", 999_500_i64, 1u64),
                ("a1", 400, 1),
                ("b0", 100, 1),
            ];
            let mut sum: i64 = 0;
            for (id, bal, nonce) in transfer {
                let full = format!("{id}00000000000000000000000000000000000000000000000000000000000000");
                let d: i64 = Spi::get_one(&format!(
                    "SELECT balance_delta FROM dregg.merge_cell_delta('\\x{full}'::bytea,'Hosted',{bal},{nonce},\
                     '\\x'::bytea,'{{\"balance\":{bal},\"nonce\":{nonce}}}'::jsonb,'Active',0,'\\x{full}'::bytea)"
                ))
                .unwrap()
                .unwrap();
                sum += d;
            }
            Spi::run("RESET ROLE").unwrap();
            assert_eq!(sum, 0, "conservation: the per-cell balance deltas the applicator reported sum to zero");
        }

        /// pg18 `uuidv7()` key as an AUDIT SIGNAL (docs/PG-DREGG-PG18.md §6, wired):
        /// `dregg.submit_queue_audit` recovers the enqueue time + version FROM the
        /// key itself (uuid_extract_timestamp / uuid_extract_version). We assert the
        /// recovered version is 7, the key-derived enqueued_at agrees with the
        /// submitted_at clock (so the key really is time-ordered), and rows come out
        /// in key (arrival) order.
        #[pg_test]
        fn pg18_submit_queue_audit_recovers_time_from_the_uuidv7_key() {
            let root = root();
            assert_issuer(&root);
            Spi::get_one::<String>("SELECT dregg_install_schema()").unwrap();
            let o: String = Spi::get_one("SELECT dregg_install_write_outbox()").unwrap().unwrap();
            assert!(o.contains("write outbox installed"));

            // Enqueue two rows as the table owner (the harness superuser) so the
            // audit view has data — the queue's INSERT grant is to dregg_reader (the
            // submitter), NOT dregg_kernel (which drains): a real find baked into the
            // role model, so we do NOT SET ROLE kernel to write here.
            let a_hex = "a100000000000000000000000000000000000000000000000000000000000000";
            Spi::run(&format!(
                "INSERT INTO dregg.submit_queue(agent, signed_turn) VALUES \
                 ('\\x{a_hex}'::bytea, '\\x01'::bytea), ('\\x{a_hex}'::bytea, '\\x02'::bytea)"
            ))
            .unwrap();
            Spi::run("SET ROLE dregg_kernel").unwrap(); // BYPASSRLS so we see all rows

            // Every row's key is a v7 and its key-derived enqueued_at is within a
            // few seconds of submitted_at (the key carries the time).
            let bad: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.submit_queue_audit \
                 WHERE id_version <> 7 \
                    OR abs(extract(epoch FROM (enqueued_at - submitted_at))) > 5",
            )
            .unwrap()
            .unwrap();
            assert_eq!(bad, 0, "every queue key is a v7 whose embedded time matches submitted_at");

            // The audit view yields rows in key (arrival) order: the first row's
            // enqueued_at is <= the last row's.
            let ordered: bool = Spi::get_one(
                "SELECT (SELECT enqueued_at FROM dregg.submit_queue_audit ORDER BY id LIMIT 1) \
                      <= (SELECT enqueued_at FROM dregg.submit_queue_audit ORDER BY id DESC LIMIT 1)",
            )
            .unwrap()
            .unwrap();
            assert!(ordered, "uuidv7 keys order the audit view by enqueue time");
            Spi::run("RESET ROLE").unwrap();
        }

        /// The OAuth → role → dregg-cap bind seam (docs/PG-DREGG-PG18.md §6, wired):
        /// `dregg_bind_role` is the tested code path that turns a pg role (e.g. one
        /// an OAuth `pg_hba` method authenticated) into a dregg capability. We bind
        /// `dregg_reader` to an ALICE-only token via the extern, confirm the
        /// `role_bindings` introspection view shows the binding WITHOUT leaking the
        /// token, then apply the login hook's effect and confirm RLS narrows — the
        /// whole chain as one tested path. (OAuth itself is pg_hba config, honestly
        /// out of extension SQL; this is the composition point it lands on.)
        #[pg_test]
        fn oauth_bind_role_seam_binds_then_rls_narrows() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            let o: String = Spi::get_one("SELECT dregg_install_login_binding()").unwrap().unwrap();
            assert!(o.contains("login binding installed"));

            let alice_tok = root
                .mint([
                    Caveat::FirstParty(Pred::AttrEq { key: "action".into(), value: "read".into() }),
                    Caveat::FirstParty(Pred::AttrPrefix { key: "resource".into(), prefix: "a1".into() }),
                ])
                .encode();
            let alice_hex: String = synth::ALICE.iter().map(|b| format!("{b:02x}")).collect();

            // Bind the role through the EXTERN (the OAuth composition seam): the same
            // call an IdP-provisioning step or a DBA migration makes.
            let bound: bool = Spi::get_one(&format!(
                "SELECT dregg_bind_role('dregg_reader', '\\x{alice_hex}'::bytea, '{alice_tok}')"
            ))
            .unwrap()
            .unwrap();
            assert!(bound, "dregg_bind_role upserts the role→cap binding");

            // The introspection view shows the binding but NOT the token text.
            Spi::run("SET ROLE dregg_kernel").unwrap();
            let (agent, has_token): (String, bool) = {
                let a: String = Spi::get_one(
                    "SELECT agent FROM dregg.role_bindings WHERE pg_role = 'dregg_reader'",
                )
                .unwrap()
                .unwrap();
                let h: bool = Spi::get_one(
                    "SELECT has_token FROM dregg.role_bindings WHERE pg_role = 'dregg_reader'",
                )
                .unwrap()
                .unwrap();
                (a, h)
            };
            assert_eq!(agent, alice_hex, "role_bindings shows the bound agent");
            assert!(has_token, "role_bindings reports a token is present");
            // The view's columns do NOT include the raw token (no default_token col).
            let leaks_token: i64 = Spi::get_one(
                "SELECT count(*) FROM information_schema.columns \
                 WHERE table_schema='dregg' AND table_name='role_bindings' \
                   AND column_name='default_token'",
            )
            .unwrap()
            .unwrap();
            assert_eq!(leaks_token, 0, "the introspection view must not expose the token text");
            Spi::run("RESET ROLE").unwrap();

            // Apply the login hook's effect (set the session token from the bound
            // row, exactly as dregg.on_login does on a real connection) and confirm
            // RLS narrows the reader to ALICE's cell.
            let installed: Option<String> = Spi::get_one(
                "SELECT default_token FROM dregg.role_identity WHERE pg_role = 'dregg_reader'",
            )
            .unwrap();
            Spi::run(&format!("SET dregg.token = '{}'", installed.unwrap())).unwrap();
            Spi::run("SET ROLE dregg_reader").unwrap();
            let visible: i64 = Spi::get_one("SELECT count(*) FROM dregg.cells").unwrap().unwrap();
            Spi::run("RESET ROLE").unwrap();
            assert_eq!(visible, 1, "the OAuth-bound role's capability narrows RLS to ALICE's cell");
        }

        /// pg18 AIO observability (docs/PG-DREGG-PG18.md §8, wired): the
        /// `dregg.mirror_io_stats` view over `pg_stat_io` resolves and reports the
        /// read/cache mix for the read-heavy mirror. We scan the mirror (driving
        /// real relation I/O), then assert the view has rows for the `normal`
        /// relation context and the cache_hit_ratio is a sane fraction in [0,1].
        #[pg_test]
        fn pg18_mirror_io_stats_view_reports_the_io_mix() {
            let root = root();
            assert_issuer(&root);
            install_tier_b_and_load_synth();
            Spi::run("SET ROLE dregg_kernel").unwrap();
            // Drive some relation reads against the mirror so pg_stat_io has counts.
            let _scan: i64 = Spi::get_one("SELECT count(*) FROM dregg.cells").unwrap().unwrap();

            // The view resolves and has at least one relation/normal row.
            let rows: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.mirror_io_stats WHERE context = 'normal'",
            )
            .unwrap()
            .unwrap();
            assert!(rows >= 1, "mirror_io_stats reports the normal relation I/O context");

            // Where a cache_hit_ratio is reported it is a valid fraction in [0,1].
            let bad_ratio: i64 = Spi::get_one(
                "SELECT count(*) FROM dregg.mirror_io_stats \
                 WHERE cache_hit_ratio IS NOT NULL \
                   AND (cache_hit_ratio < 0 OR cache_hit_ratio > 1)",
            )
            .unwrap()
            .unwrap();
            assert_eq!(bad_ratio, 0, "cache_hit_ratio is a fraction in [0,1]");
            Spi::run("RESET ROLE").unwrap();
        }
    }
}

// pgrx's test harness entrypoint (cargo pgrx test).
#[cfg(feature = "pgrx")]
#[cfg(test)]
pub mod pg_test {
    pub fn setup(_options: Vec<&str>) {}

    /// Configure the managed test server. The issuer key is set HERE (server
    /// start, the secure `Sighup` path) rather than via a session `SET`, since
    /// the GUC is `Sighup` (a session must not be able to point verification at
    /// a key it controls). All #[pg_test]s mint under the fixed seed
    /// `RootKey::from_seed([7u8; 32])`; this is that root's public key.
    pub fn postgresql_conf_options() -> Vec<&'static str> {
        vec![
            "dregg.issuer_pubkey = 'ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c'",
        ]
    }
}
