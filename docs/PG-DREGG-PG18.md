# PG-DREGG-PG18 — being truly PostgreSQL-18-native

`pg-dregg` targets **PostgreSQL 18** (released 2025-09-25) as its primary
backend. This document explains, from first principles, how the extension uses
pg18's own features so that a dregg deployment is not "a key-value blob behind a
postgres connection" but a *real postgres database*: its reads are rich,
set-oriented, index-eligible SQL over typed relations and views; its writes are
verified-only and the database engine itself re-validates them — and the pg18
`MERGE … RETURNING old/new` applicator reports the exact state delta it caused;
and a connecting role is bound to its dregg capability by postgres's own
machinery, including pg18 OAuth.

It is the companion to `docs/PG-DREGG.md`. That document gives the full Tier
A/B/C/D architecture and the spine invariant; this one is the pg18 feature
detail — what each feature *is*, why the dregg mirror wants exactly it, and which
test (run under `cargo pgrx test pg18`) executes it on a live server.

The single sentence the whole design serves:

> **Reads are rich SQL; writes are verified-only; postgres re-validates, it
> never trusts.**

Everything below is one of those three clauses, realized with a pg18 feature.

---

## 1. What "pg-native" means here

A storage layer can speak SQL without *being* a database. If dregg state were a
single `jsonb` column the application picks apart with hand-written operators,
postgres would be a glorified blob store: no typed columns to index, no views to
JOIN, no RLS to gate a row, no engine-enforced write discipline. "pg-native"
means the opposite on every axis:

| clause | pg-native means | the pg18/pg17 feature | §  |
|--------|-----------------|------------------|----|
| **rich reads** | dregg's embedded JSON state is projected into typed, JOINable, index-eligible relations and views | `JSON_TABLE` (17), **virtual generated columns (18)**, builtin-C collation (17) | §2–§5 |
| **verified-only writes** | a state row exists ONLY as the post-image of a verified turn, applied atomically through ONE door — and the applicator reports the delta | **`MERGE … RETURNING old/new` (18)**, a `BEFORE INSERT` re-validating trigger | §7 |
| **postgres re-validates** | the database engine — not a trusted writer — refuses a tampered/reordered/forged batch | the chain re-validator `dregg_verify_turn`, run inside the gate trigger | §7 |
| **pg-native authz** | a connecting role is bound to its dregg capability by postgres, and rows are gated by it | login event trigger (17) + **OAuth (18)** + RLS cap policies; `uuidv7()` (18) queue keys | §6 |

The dregg side stays honest: the *authorization decision* and the *chain
re-validation* are the verified dregg checks (the Lean↔Rust differential on
`dregg-auth`, and the `RootChain` tooth proven by `cargo test` in
`pg-dregg/src/mirror.rs`). pg18 is what lets those checks live *inside the
database* as first-class relations, policies, and triggers rather than beside it
— and pg18's read-time generated columns and `RETURNING old/new` make the mirror
leaner on writes and richer on audit than pg17 allowed.

(`pg13`–`pg17` remain selectable for older deployments; the pg18-only forms
below — virtual generated columns, `RETURNING old/new`, `uuidv7()`, `oauth` —
are the primary-target leverage.)

---

## 2. The caveat algebra as a jsonpath — `Pred → SQL/JSON`

A dregg capability's first-party authority is a tree of predicate atoms
(`dregg_auth::credential::Pred`): equality (`AttrEq`), prefix (`AttrPrefix`), the
temporal gates (`NotBefore`/`NotAfter`/`Within`), and the `AllOf`/`AnyOf`/`Not`
algebra. The authorization *gate* on a write evaluates that tree in Rust, behind
the verified-credential LRU — it must consult the issuer key and the revocation
set, which a jsonpath cannot.

But a great deal of dregg's value as a postgres layer is **reads**: an auditor
asking *"which mirrored cells satisfy this caveat?"*, *"explode a capability's
attenuation and show me the rows."* For those, the predicate is a pure function
of the row's JSON — and postgres has a first-class engine for exactly that:
**SQL/JSON jsonpath** (`jsonb_path_exists` / `JSON_EXISTS`). So `pg-dregg`
compiles a `Pred` ONCE into a jsonpath *filter expression* and lets the database
evaluate it over the mirrored turn/cell JSON as a plain, index-eligible,
set-oriented predicate.

`pg-dregg/src/jsonpath.rs` is the structural compile of `Pred::eval`. The
mapping (the fail-closed corners preserved exactly):

| `Pred` | jsonpath filter fragment |
|--------|--------------------------|
| `True` / `False` | `true` / `false` |
| `AttrEq{key,value}` | `@.key == "value"` |
| `AttrPrefix{key,prefix}` | `@.key starts with "prefix"` |
| `NotBefore{at}` / `NotAfter{at}` | `@.clock >= at` / `@.clock <= at` |
| `Within{nb,na}` | `@.clock >= nb && @.clock <= na` |
| `AllOf([…])` | `(f1 && f2 && …)`, empty ⇒ `true` (`evalAll [] = true`) |
| `AnyOf([…])` | `(f1 \|\| f2 \|\| …)`, empty ⇒ `false` (fail-closed) |
| `Not(p)` | `!(f)` |

The result is wrapped `$ ? (FILTER)`, so `jsonb_path_exists(row, path)` is the
predicate's admit verdict. The extension surface:

- `dregg_pred_jsonpath(pred_json) → text` — the compiled jsonpath string (use it
  directly: `… WHERE jsonb_path_exists(doc, dregg_pred_jsonpath($1)::jsonpath)`).
- `dregg_pred_jsonpath_strict(pred_json) → text` — every atom carries an
  `exists(@.key)` boundness guard, so it fails closed on an absent key even under
  a `Not` (matching `Pred::eval`'s Unbound poisoning unconditionally).
- `dregg_pred_matches(pred_json, row jsonb) → bool` — the ergonomic face,
  compile-and-evaluate in one call.

**The honest scope.** This is the caveat *algebra*, not the credential *chain*: a
jsonpath cannot verify an ed25519 chain, consult revocation, or discharge a
third-party caveat. So jsonpath eval is the read/audit surface over
already-mirrored, already-verified state; the write gate stays the Rust `decide`
path. The compile is faithful: `dregg_pred_jsonpath` agrees with `Pred::eval` on
bound rows (the mirror's projected JSON binds every inspected attribute), and the
strict form agrees unconditionally. `pred_to_jsonpath` returns `None` for any
predicate that is not first-party-expressible (today the total `Pred` algebra is,
so it is always `Some`; the door is closed-by-construction for a future
discharge-bearing variant).

*Proven by* `jsonpath_admit_agrees_with_pred_eval_on_bound_rows` (`cargo test`,
no postgres — a reference evaluator over a matrix of predicates × rows) and, on
live pg18, `pred_jsonpath_matches_agree_with_real_authz` (the compiled jsonpath
admits exactly what the chain-verified `dregg_cap_admits` admits, row by row) and
`pred_jsonpath_filters_the_mirror_as_a_read` (the jsonpath used directly in a
`SELECT … WHERE jsonb_path_exists(…)` over `dregg.cells`).

---

## 3. Deterministic ordering — the builtin C collation (`pg_c_utf8`)

dregg's ledger root is a commitment over **sorted** leaves: cells (and map
entries) are ordered lexicographically *on their canonical bytes*, and the root
folds them in that order. For a pg-side fold over the mirror to see leaves in the
*same* order the kernel committed them, the database's ordering of the leaf keys
must be the identical byte order, with no locale or ICU influence.

postgres ships the builtin **`C.UTF-8` collation `pg_c_utf8`** (pg17): a
provider-stable, version-independent collation whose ordering is byte-wise on the
UTF-8 encoding. Unlike a libc or ICU `C`-like locale, it cannot drift across
OS/ICU upgrades — it is defined by postgres itself. `pg-dregg` types the
canonical hex id column with it and orders the canonical view by it:

```sql
cell_hex text COLLATE pg_c_utf8 GENERATED ALWAYS AS (encode(cell_id,'hex')) STORED,
...
CREATE INDEX cells_by_canonical ON dregg.cells (cell_hex);          -- byte-order index
CREATE VIEW dregg.canonical_cells AS
    SELECT cell_hex, balance, nonce, lifecycle, cell_root_hex, last_ordinal
    FROM dregg.cells ORDER BY cell_hex COLLATE pg_c_utf8;            -- the kernel's leaf order
```

So `dregg.canonical_cells` enumerates cells in the deterministic order the ledger
root uses, and the `cells_by_canonical` index serves range scans in that order
with no ICU dependency. This is the floor a future pg-side root recomputation
stands on: same leaves, same order, no locale drift between database and kernel.
(It is also *why* `cell_hex` must be a STORED generated column — see §4: an index
needs a materialized value, so the indexed canonical key cannot be virtual.)

*Proven by* `turn_effects_and_canonical_views_resolve_over_the_store` (live
pg18): over the verified store, the first row of `dregg.canonical_cells` is ALICE
(`a1…`) before TREASURY (`c0…`) — the byte order `a1 < c0`, deterministically.

---

## 4. Canonical projections that cannot drift — generated columns, pg18 virtual

A query that reads the balance out of `fields_json->>'balance'` by hand, or
re-`encode()`s a bytea to hex in every projection, is re-deriving canonical state
in application code — and can get it wrong, or drift from the column it claims to
mirror. A **generated column** lets the *database* maintain the derived
projection: it is computed from a pinned expression, so it is always exactly the
function of the row it declares.

**pg18 makes `VIRTUAL` the default kind.** A virtual generated column is computed
**on read** (zero stored bytes, no write amplification); a `STORED` column is
computed on write (materialized, indexable). `pg-dregg` chooses the kind per
column by the one thing that distinguishes them — *whether the column must be
indexed* (an index needs a stored value, so a virtual column cannot be indexed):

```sql
-- STORED: backs the cells_by_canonical index (a VIRTUAL column cannot be indexed).
cell_hex       text   COLLATE pg_c_utf8 GENERATED ALWAYS AS (encode(cell_id,'hex'))  STORED,
-- VIRTUAL (the pg18 default, named explicitly): read-side projections, no index.
cell_root_hex  text   COLLATE pg_c_utf8 GENERATED ALWAYS AS (encode(cell_root,'hex')) VIRTUAL,
balance_field  bigint                   GENERATED ALWAYS AS ((fields_json->>'balance')::bigint) VIRTUAL;
```

- `cell_hex` — **STORED.** It is the canonical-order key (§3) and is indexed by
  `cells_by_canonical`. Because postgres recomputes it on every write, a query (or
  the canonical view, or the RLS predicate) reads a hex that *cannot* disagree
  with `encode(cell_id,'hex')`.
- `cell_root_hex` / `balance_field` — **VIRTUAL.** They are read-side projections
  (the canonical view's `cell_root_hex`, the analytics face's typed `bigint`
  balance) that need no index, so paying write-time storage for them is waste.
  pg18 computes them on read, identically and drift-free, with no stored bytes —
  the write path materializes only what is indexed.

The guarantee is "no drift by construction": there is no code path that writes a
generated column independently of its source. A test asserts it directly — over
the store, `cell_root_hex = encode(cell_root,'hex')` and `balance_field =
(fields_json->>'balance')::bigint` for every row — *and* asserts the pg18 kinds
in `pg_attribute` (`attgenerated` is `'s'` for `cell_hex`, `'v'` for the other
two).

> **The pg18 default shift is load-bearing to read carefully.** Pre-18, `GENERATED
> ALWAYS AS (…)` *required* `STORED` (virtual did not exist), so omitting the
> keyword was a syntax error. In pg18, omitting it now means VIRTUAL. `pg-dregg`
> writes the kind **explicitly on every generated column** (`STORED` where indexed,
> `VIRTUAL` otherwise), so the DDL means the same thing regardless of the reader's
> assumptions and a downgrade to a pre-18 ABI surfaces the `VIRTUAL` columns as a
> clear "unsupported" error rather than silently materializing them.

*Proven by* `pg18_merge_returning_delta_virtual_columns_and_uuidv7` (live pg18,
the virtual columns equal their source on read and `pg_attribute` records the
kinds) and `turn_effects_and_canonical_views_resolve_over_the_store`.

---

## 5. A turn's effects as rows — `JSON_TABLE` over the verified store

dregg's state embeds JSON: a cell's decoded field slots (`cells.fields_json`), a
capability's attenuation (`capabilities.allowed_effects`), and — at the
verified-store door — a turn's touched-cell post-images (`commit_log.cells`, a
jsonb array). Querying those with hand-rolled jsonb operators (`->`, `->>`,
`jsonb_array_elements`) is exactly the "blob behind SQL" anti-pattern. SQL/JSON
**`JSON_TABLE`** (pg17) projects a jsonb document into a flat relational surface —
proper rows with typed columns — that a developer JOINs and aggregates as
ordinary SQL.

`pg-dregg` ships three `JSON_TABLE` views:

- `dregg.cell_fields` — `balance`/`nonce` projected out of `fields_json` as typed
  columns.
- `dregg.cap_attenuations` — one row per effect in a capability's
  `allowed_effects` array. This is the **no-amplification audit surface** exploded
  into rows: a child's allowed effects are a subset of its grantor's, queryable
  directly.
- `dregg.turn_effects` — one row per *(ordinal, touched cell)*, exploded from the
  `commit_log` payload the Tier-C gate verified:

```sql
CREATE VIEW dregg.turn_effects AS
    SELECT cl.ordinal, jt.cell_id, jt.balance, jt.nonce, jt.lifecycle, jt.cell_root, cl.submitted_at
    FROM dregg.commit_log cl,
         JSON_TABLE(cl.cells, '$[*]'
             COLUMNS (cell_id text PATH '$.cell_id', balance bigint PATH '$.balance',
                      nonce bigint PATH '$.nonce', lifecycle text PATH '$.lifecycle',
                      cell_root text PATH '$.cell_root')) AS jt;
```

So *"what did turn N do?"* is a plain `SELECT * FROM dregg.turn_effects WHERE
ordinal = N`. This is the realizable per-turn effect surface — a `CommitRecord`
carries no per-turn proof (proof soundness is the whole-chain IVC light client's
job, `docs/PG-DREGG.md` §10.2), but it *does* carry the touched cells the gate
verified, and `turn_effects` is exactly those, as rows.

*Proven by* `turn_effects_and_canonical_views_resolve_over_the_store` (live
pg18) and `pg17_merge_upsert_and_json_table_views` (the `cell_fields` /
`cap_attenuations` projections resolve and explode correctly).

---

## 6. pg-native authz — login trigger, OAuth, and a temporally-sortable queue

The read-side gate is the dregg capability layer expressed as Row-Level Security:
every state table is `FORCE ROW LEVEL SECURITY`, and each carries a policy
`USING (dregg_admits('read', encode(<id>,'hex')))`. `dregg_admits` reads the
session's presented token (`current_setting('dregg.token')`) and `now()`, and
returns the verified dregg decision — so a reader sees only the rows its
capability admits, and attenuating a token strictly narrows what it sees. That is
already pg-native: the *database engine*, under RLS, filters every row by a dregg
capability.

**The login event trigger** (pg17) closes the *presenting-the-token* gap. A
`dregg.role_identity` table maps `pg_role → (agent cell, default token)`, and an
`event_trigger ON login` reads the connecting role's row and `SET`s the
`dregg.token` / `dregg.agent` session GUCs from it. After that, every statement
in the session is already capability-bound, with no application-side token
handling: **the database binds identity → capability the moment you connect.**

```sql
CREATE FUNCTION dregg.on_login() RETURNS event_trigger LANGUAGE plpgsql SECURITY DEFINER AS $$
DECLARE r record;
BEGIN
    BEGIN
        SELECT agent, default_token INTO r FROM dregg.role_identity WHERE pg_role = session_user;
        IF FOUND THEN
            IF r.default_token IS NOT NULL THEN PERFORM set_config('dregg.token', r.default_token, false); END IF;
            PERFORM set_config('dregg.agent', encode(r.agent,'hex'), false);
        END IF;
    EXCEPTION WHEN OTHERS THEN
        RAISE WARNING 'dregg.on_login: identity binding skipped (%):', SQLERRM;   -- anti-lockout
    END;
END $$;
CREATE EVENT TRIGGER dregg_login_bind ON login EXECUTE FUNCTION dregg.on_login();
```

Three properties make this sound: (1) **fail-closed** — a role with no
`role_identity` row gets no token set, so `dregg_admits` reads an absent
`dregg.token` ⇒ deny; (2) **binding never widens authority** — the trigger only
*presents* a token that still has to verify against the issuer key and survive
its caveats and revocation; (3) **a buggy hook cannot lock the database out** —
the body is wrapped so a fault is swallowed and the login proceeds *unbound*
(fail-closed, never fail-shut; recovery is the single-user-mode `ALTER EVENT
TRIGGER … DISABLE`). The function is `SECURITY DEFINER` because it reads
`role_identity`, which the connecting role itself may not.

**pg18 OAuth composes on top — federated identity → role → dregg cap.** pg18 adds
the `oauth` authentication method to `pg_hba.conf` (with `oauth_validator_libraries`
to load a token validator and libpq OAuth connection options). It authenticates a
connection against an external identity provider and maps it to a postgres role.
That is precisely the *who is connecting* question whose answer the login trigger
then turns into a dregg capability: an OAuth-authenticated principal lands as a pg
role, the `ON login` hook reads that role's `dregg.role_identity` row, and the
session is capability-bound — **so an OAuth subject's authority inside the
database is its dregg capability, gated by RLS on every row.** OAuth decides the
role; dregg decides what the role may touch. (The `pg_hba` `oauth` line and the
validator are deployment configuration, not extension SQL; pg-dregg's surface is
the `role_identity` map + the login hook it binds through.)

**The write side has its own cap-RLS policy, keyed by a pg18 `uuidv7()`.** A
pg-user submits a verified turn FROM postgres by enqueuing it into
`dregg.submit_queue`; the `submit_gate` policy gates that INSERT with `WITH CHECK
(dregg_admits('submit', encode(agent,'hex')))`, so a role enqueues exactly the
turns its capability admits `submit` on (§7). The queue's primary key defaults to
pg18 `uuidv7()` — a UUID whose leading bits are a millisecond timestamp, so it is
**temporally sortable**: the node drains the queue in arrival order by `id` alone,
and the index is append-friendly (no random-uuid page churn that `gen_random_uuid()`
/ v4 causes). A drain queue wants exactly a time-ordered key, and pg18 gives one
as a builtin.

*Proven by* `login_binding_sets_the_session_token_and_narrows_rls` (the binding
logic sets the session token and RLS then narrows the reader to ALICE's cell
only; the live cross-connection form is `sql/e2e-live.sql` over a real psql
reconnect), `login_binding_ddl_is_emittable_and_defensive` (the DDL is shaped,
SECURITY DEFINER, anti-lockout), and `pg18_merge_returning_delta_virtual_columns_and_uuidv7`
(the submit_queue default mints a version-7 uuid).

---

## 7. Verified-only writes — `MERGE … RETURNING old/new` behind a re-validating gate

The spine invariant is *state mutates ONLY through verified turns*. pg-dregg
makes the database engine enforce it: a row reaches `dregg.cells` /
`capabilities` / `memory` ONLY through `dregg.commit_log`, whose `BEFORE INSERT`
trigger (`dregg.apply_verified_turn`) (1) re-validates the chain, and only then
(2) records the turn and (3) materializes the post-image — all in one
transaction. The Tier-B privilege lockdown (`REVOKE INSERT,UPDATE,DELETE … FROM
PUBLIC`, `FORCE ROW LEVEL SECURITY`, a `dregg_reader`/`dregg_kernel` split)
forbids every other write path, so this trigger is the ONE door.

**The re-validator is real (the anti-substitution tooth).**
`dregg_verify_turn(prev_root, ledger_root, ordinal)` reads the database's current
head from `dregg.turns` and runs the exact gate the in-process mirror runs
(`pg_dregg::mirror::verify_chain_step`, which `RootChain::extend` also calls): the
turn's `ordinal` must be the next expected one AND its `prev_root` must equal the
head root (the post-state root of turn *N* is the pre-state root of turn *N+1*).
A tampered / reordered / forged batch breaks this and is refused **by the database
engine**, with a `RAISE EXCEPTION` so nothing is written. It is *not* stubbed to
TRUE (the forbidden failure mode); it fails closed on any deviation. What it does
NOT do is re-prove a per-turn STARK — a `CommitRecord` carries no per-turn proof;
that soundness is the whole-chain IVC light client's job. The realizable per-row
gate is this structural chain re-validation, and it is what makes a replicated or
restored mirror self-checking rather than merely copied.

**The applicator is the pg18 `MERGE … RETURNING old/new`.** Materializing a
post-image is an upsert: a first-seen cell INSERTs, a re-touched cell UPDATEs in
place (a later turn's post-image wins). `MERGE` (pg17) is the standard atomic form
and `merge_action()` (pg17) RETURNS which arm fired. **pg18 adds `old.*` / `new.*`
to `RETURNING`** for INSERT/UPDATE/DELETE/MERGE — so the applicator reads the
*pre-image* in the same statement and reports the exact state delta the
materialization caused, an audit signal impossible pre-18 without a separate
pre-read:

```sql
CREATE FUNCTION dregg.merge_cell(p_cell_id bytea, …, p_cell_root bytea) RETURNS text
LANGUAGE plpgsql AS $$
DECLARE v_action text; v_delta bigint;
BEGIN
    MERGE INTO dregg.cells AS t USING (SELECT p_cell_id AS cell_id) AS s ON t.cell_id = s.cell_id
    WHEN MATCHED THEN UPDATE SET balance=p_balance, nonce=p_nonce, fields_json=p_fields_json,
                                 last_ordinal=p_last_ordinal, cell_root=p_cell_root
    WHEN NOT MATCHED THEN INSERT (…) VALUES (…)
    -- pg17 merge_action() = 'INSERT'|'UPDATE'; pg18 old.balance is the pre-image
    -- (NULL on insert) ⇒ the delta is read in the one atomic statement.
    RETURNING merge_action(), new.balance - coalesce(old.balance, 0) INTO v_action, v_delta;
    RETURN v_action || ' ' || (CASE WHEN v_delta >= 0 THEN '+' ELSE '' END) || v_delta::text;
END $$;                                   -- 'INSERT +1000000' | 'UPDATE -500'
```

So the applicator returns *both* which arm fired *and* by how much the balance
moved, in one statement: `'INSERT +1000000'` when TREASURY is first funded,
`'UPDATE -500'` when it pays out. The gate trigger calls `dregg.merge_cell(...)`
for each touched cell, and the *same* function is the live node mirror's writer
(`node/src/pg_mirror.rs`'s `PgSink` issues `SELECT dregg.merge_cell(...)` per
cell), so the verified-store door and the streaming mirror materialize
identically — by construction, not by coincidence.

> **pgrx-0.17 note (a named seam, not a pg18 gap).** A *top-level* `MERGE` issued
> through pgrx's `Spi` panics with *"unrecognized SPI status code: 19"* —
> `SPI_OK_MERGE` (19) is outside the range pgrx-0.17's Spi wrapper maps. Wrapping
> the `MERGE` in the `dregg.merge_cell` SQL function (where the function executor
> consumes the MERGE status) both sidesteps it and is the better design: the
> mirror gets a real `MERGE` *and* a reusable server-side materialization
> function. We do not depend on a future pgrx mapping status 19.

*Proven by* `tier_c_commit_log_gate_materializes_verified_turns` (the well-formed
story lands as real rows through the gate; ALICE's nonce is the latest
post-image's — the MERGE update arm won — and the turns table is an unbroken hash
chain), `tier_c_gate_refuses_a_tampered_batch_by_raising` (a forged batch RAISEs
the exact anti-substitution error: the gate, not a trusted writer, refuses),
`pg18_merge_returning_delta_virtual_columns_and_uuidv7` (the INSERT arm returns
`'INSERT +1000000'` and the UPDATE arm `'UPDATE -500'` — the pg18 old/new delta),
`pg17_merge_upsert_and_json_table_views` (the MERGE arms fire across the story
with exactly one row per cell), and the write-path pair
`write_path_submit_turn_enqueues_under_an_authorized_token` /
`write_path_rls_refuses_submitting_for_an_unauthorized_agent`.

---

## 8. Faster reads — asynchronous I/O (pg18)

The mirror is read-heavy: the explorer/analytics surface scans `dregg.cells`,
walks `dregg.receipt_chain`, and the recursive `cap_edges` delegation tree;
Tier C adds verify-on-write. pg18 introduces an **asynchronous I/O subsystem
(AIO)** that improves sequential scans, bitmap heap scans, and vacuum — the exact
shapes the mirror's large-scan views take — with no SQL change (it is configured
by `io_method` and is transparent to the extension). pg-dregg requires nothing
of it; it is the engine getting faster underneath the read-heavy mirror, and the
reason the "rich reads" clause stays cheap as the ledger grows. (A perf-baseline
of the dev-views under AIO + `pg_stat_io` is the noted observability follow-up,
`docs/PG-DREGG.md` §14.2.)

---

## 9. Running it live

Two reproducible forms exercise everything above against a real `postgresql@18`.

**The `#[pg_test]` suite** — every claim through the SQL boundary, against a
cargo-pgrx-managed pg18:

```
brew install postgresql@18
cargo install cargo-pgrx --version 0.17.0
cargo pgrx init --pg18 "$(brew --prefix postgresql@18)/bin/pg_config"
cd pg-dregg && cargo pgrx test pg18        # the whole suite
```

The postgres-free authorization + mirror core is the always-runnable proof
(`cd pg-dregg && cargo test`, the empty default feature set — no postgres, no
cargo-pgrx).

**The human-runnable e2e** (`pg-dregg/scripts/e2e-live.sh`) drives
`sql/e2e-live.sql` plus the §7 write-path gate on a live database (the cargo-pgrx
pg18 cluster on port 28818) with a freshly minted token. It stands up a clean DB,
sets the issuer key (the `Sighup` GUC), installs Tier B + Tier C from the Rust
DDL emitter, then:

- submits a genesis + transfer through `dregg.commit_log` — the rows LAND
  (TREASURY 999500, ALICE 400) via the MERGE applicator;
- shows the pg18 `MERGE … RETURNING old/new` delta on a demo cell
  (`'INSERT +1000'` then `'UPDATE -300'`) and the VIRTUAL generated columns
  (`cell_root_hex`/`balance_field`, `attgenerated='v'`) equal to their source;
- shows the `dregg.turns` hash chain (each `prev_root` is the prior `ledger_root`);
- submits a TAMPERED ord-2 (substituted `prev_root`) — the trigger RAISEs
  `dregg: turn 2 does not chain onto the head root — refused
  (anti-substitution)`, and a replayed ord-0 is refused too;
- confirms the store is INTACT (still 2 turns, ALICE still 400);
- confirms the privilege lockdown (an app role has zero write on state; only the
  kernel submits);
- mints an ALICE-only `submit` token (`cargo run --example mint`), and shows a
  submit FOR ALICE succeed and a submit FOR BOB refused by RLS.

```
pg-dregg/scripts/e2e-live.sh
```

The live node mirror writer (`node/src/pg_mirror.rs`, the `pg-mirror-live`
feature) carries its own integration test (`pg_sink_writes_through_to_live_pg`,
run with `DREGG_PG_MIRROR_TEST_URL` pointing at a live pg18): a real `PgMirror`
over a real `PgSink` ships a chained sequence through `tokio-postgres`, the rows
land via `dregg.merge_cell`, and the pg side re-validates the chain it received.

---

## 10. Feature inventory

| pg feature | version | clause served | where |
|------------|---------|---------------|-------|
| SQL/JSON jsonpath (`jsonb_path_exists`, `starts with`) | 12 / 17 | rich reads | §2, `src/jsonpath.rs` |
| builtin C collation `pg_c_utf8` | 17 | rich reads (deterministic order) | §3, the `cells_by_canonical` index + `canonical_cells` view |
| **VIRTUAL generated columns** (now the default) | **18** | rich reads (no-drift, no-storage projections) | §4, `dregg.cells` (`cell_root_hex`/`balance_field`) |
| STORED generated columns | 12 | rich reads (indexed canonical key) | §4, `dregg.cells` (`cell_hex`) |
| SQL/JSON `JSON_TABLE` | 17 | rich reads (JSON → rows) | §5, the three projection views |
| login event trigger | 17 | pg-native authz | §6, `dregg.on_login` |
| **`oauth` authentication method** | **18** | pg-native authz (federated identity → role) | §6, composes with `role_identity` + the login hook |
| **`uuidv7()`** (temporally sortable) | **18** | pg-native authz (the drain-queue key) | §6, `dregg.submit_queue` |
| `MERGE` + `merge_action()` | 17 | verified-only writes (atomic upsert) | §7, `dregg.merge_cell` |
| **`RETURNING old.* / new.*`** | **18** | verified-only writes (the applicator's delta audit) | §7, `dregg.merge_cell` |
| **asynchronous I/O (AIO)** | **18** | rich reads (faster large scans) | §8, transparent |
| `BEFORE INSERT` re-validating trigger | core | verified-only writes (the one door) | §7, `dregg.apply_verified_turn` |
| `FORCE ROW LEVEL SECURITY` + cap policies | core | read gate + write gate | §6/§7, the RLS |

For the federation-via-logical-replication path (failover slots,
`pg_createsubscriber`) and the snapshot/backup complement, see
`docs/PG-DREGG.md` §15.
