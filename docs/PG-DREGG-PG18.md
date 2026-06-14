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
| **rich reads** | dregg's embedded JSON state is projected into typed, JOINable, index-eligible relations and views | `JSON_TABLE` (17), **virtual generated columns (18)**, builtin-C collation (17), **B-tree skip scan (18)**, **AIO + `pg_stat_io` + `pg_aios` (18)**, `security_invoker` views (15) | §2–§5, §8 |
| **verified-only writes** | a state row exists ONLY as the post-image of a verified turn, applied atomically through ONE door — and the applicator reports the (typed) delta | **`MERGE … RETURNING WITH (OLD/NEW)` (18)**, a `BEFORE INSERT` re-validating trigger | §7 |
| **postgres re-validates** | the database engine — not a trusted writer — refuses a tampered/reordered/forged batch | the chain re-validator `dregg_verify_turn`, run inside the gate trigger | §7 |
| **integrity floor** | the page integrity every higher guarantee assumes is on by default, and made legible | **data checksums by `initdb` default (18)** surfaced as `dregg.integrity_status` | §11 |
| **federation that re-validates** | a subscriber tails the verified-turn feed and is told when the stream diverged | logical replication + **pg18 `confl_*` conflict counters** as a `conflicts_total` alarm | §10 |
| **pg-native authz** | a connecting role is bound to its dregg capability by postgres, and rows are gated by it | login event trigger (17) + **OAuth (18)** + RLS cap policies; `uuidv7()` (18) queue keys; **`COPY … ON_ERROR` (18)** bulk onboarding | §6, §12 |

The dregg side stays honest: the *authorization decision* and the *chain
re-validation* are the verified dregg checks (the Lean↔Rust differential on
`dregg-auth`, and the `RootChain` tooth proven by `cargo test` in
`pg-dregg/src/mirror.rs`). pg18 is what lets those checks live *inside the
database* as first-class relations, policies, and triggers rather than beside it
— and pg18's read-time generated columns and `RETURNING old/new` make the mirror
leaner on writes and richer on audit than pg17 allowed.

(`pg13`–`pg17` remain selectable for older deployments; the pg18-only forms
below — virtual generated columns, `RETURNING old/new`, `uuidv7()`, `oauth`,
B-tree skip scan, AIO + `pg_aios`, data checksums by default, the
`confl_*` replication-conflict counters, and `COPY … ON_ERROR` — are the
primary-target leverage. §13 records the pg18 features deliberately *not* adopted,
each with its reason.)

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
validator are deployment configuration, not extension SQL.)

The *bind seam* — the point where the OAuth-decided role becomes a dregg
capability — is a tested first-class surface, not just prose. `dregg.bind_role(
pg_role, agent, token)` (the `SECURITY DEFINER` upsert behind the `dregg_bind_role`
extern) is the call an IdP-provisioning step or a DBA migration makes to populate
the `role_identity` row the login hook installs; `dregg.role_bindings` is the
introspection view that shows which role is bound to which agent and *whether* a
token is installed — **without exposing the token text** (it projects
`default_token IS NOT NULL`, never the credential). So the whole chain — OAuth
subject → pg role → `dregg.bind_role` → `role_identity` → `ON login` →
`dregg.token` GUC → RLS on every row — is one tested code path
(`oauth_bind_role_seam_binds_then_rls_narrows`, live pg18).

**The queue key is itself an audit signal.** `dregg.submit_queue_audit` recovers
the enqueue time and version *from the `uuidv7()` key* via pg18's
`uuid_extract_timestamp()` / `uuid_extract_version()` — so `enqueued_at` is read
back from the id (a cross-check that the key really is time-ordered, independent of
the `submitted_at` clock column), `id_version` proves it is a v7, and the view's
`queue_latency` is the node's drain latency measured against the key. It is
`security_invoker`, so the `submit_read` RLS still gates which rows a submitter
sees through it. *Proven by* `pg18_submit_queue_audit_recovers_time_from_the_uuidv7_key`
(live pg18).

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

The example above uses the **explicit `RETURNING WITH (OLD AS o, NEW AS n)`
alias** — the spec-standard pg18 form. It is strictly better than the bare
`old.`/`new.` pseudo-aliases (which only resolve because no column is literally
named `old`/`new`): the explicit alias is unambiguous and future-proof. A twin
applicator `dregg.merge_cell_delta(...)` returns the same MERGE's report as a
*typed tuple* `(action, balance_delta, nonce_delta)` (the pg18 `RETURNING WITH`
reading both the balance and nonce off the pre-image) — the analytics face when a
caller wants the numbers typed rather than the `'<ACTION> <DELTA>'` string. The
payoff: **conservation is assertable directly off the applicator** — the per-cell
balance deltas of a transfer (TREASURY→ALICE→BOB) the applicator reports sum to
zero, no separate read needed. *Proven by*
`pg18_merge_cell_delta_typed_and_conservation_off_the_applicator` (live pg18).

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

## 8. Faster reads — asynchronous I/O (pg18), made observable

The mirror is read-heavy: the explorer/analytics surface scans `dregg.cells`,
walks `dregg.receipt_chain`, and the recursive `cap_edges` delegation tree;
Tier C adds verify-on-write. pg18 introduces an **asynchronous I/O subsystem
(AIO)** that improves sequential scans, bitmap heap scans, and vacuum — the exact
shapes the mirror's large-scan views take — with no SQL change (it is configured
by `io_method` and is transparent to the extension). pg-dregg requires nothing
of it; it is the engine getting faster underneath the read-heavy mirror, and the
reason the "rich reads" clause stays cheap as the ledger grows.

**The AIO observability surface is wired**, not deferred — in two complementary
shapes, the cumulative counters and the live in-flight set. pg18's AIO feeds
`pg_stat_io` (with the new `reads`/`read_bytes`/`write_bytes`/`extend_bytes`
columns and the cache `hits` that never touched the OS); `dregg.mirror_io_stats`
projects the read-path-relevant relation contexts (`normal`, `vacuum`,
`bulkread`, `bulkwrite`) into a compact mirror-facing view that reports, per
(backend type, context), the read/write/extend counts and the `cache_hit_ratio`
the read-heavy mirror watches as the ledger grows. It is a thin SELECT over the
system view (no row data, so no RLS concern). *Proven by*
`pg18_mirror_io_stats_view_reports_the_io_mix` (live pg18: the view resolves,
reports the `normal` relation context, and the hit ratio is a valid fraction).

pg18 *also* ships the brand-new **`pg_aios`** system view — the live set of
asynchronous-I/O handles a backend currently has *outstanding* (the AIO companion
to the cumulative `pg_stat_io`). `dregg.mirror_aio_inflight` surfaces it (a thin
`SELECT * FROM pg_aios`, so it inherits pg_aios's columns verbatim). Where
`mirror_io_stats` answers *"how much I/O has the mirror done and what was the
cache hit rate?"*, `mirror_aio_inflight` answers *"is AIO actually queueing reads
right now, or falling back to synchronous?"* — the in-flight depth under a large
scan is the signal that the async subsystem is engaged. `pg_aios` is a privileged
stats surface (it reads through `pg_get_aios()`, which wants superuser /
`pg_read_all_stats`), so it is an operator/kernel view, not an app-reader one.
*Proven by* `pg18_mirror_aio_inflight_view_resolves_over_pg_aios` (live pg18: the
view resolves and is countable — the pg18 view exists and the mirror surfaces it;
the transient in-flight depth is not pinned).

**B-tree skip scan (pg18) is applied** to the same read paths. The composite
`cells_by_mode_balance (mode, balance)` index serves *both* `WHERE mode = …` *and*
`WHERE balance = …` / `ORDER BY balance` — the latter via skip scan: `mode` (the
leading column) has tiny cardinality (Hosted | Sovereign), so a balance-only
predicate makes the planner skip through the few `mode` prefixes and range-scan
`balance` within each, instead of the pre-18 fallback (a full index scan or seq
scan). One index covers the two hot access paths with no separate `balance` index
to maintain on the write path. *Proven by*
`pg18_skip_scan_serves_balance_with_unconstrained_leading_mode` (live pg18: with
4000 rows the plan uses `cells_by_mode_balance` with an `Index Cond` on `balance`,
the leading `mode` column unconstrained).

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
- shows the pg18 `RETURNING WITH (OLD/NEW)` typed applicator `dregg.merge_cell_delta`
  (the `(action, Δbalance, Δnonce)` tuple), the pg18 **B-tree skip scan** plan over
  `cells_by_mode_balance` (an `Index Cond` on `balance`, the leading `mode` column
  unconstrained), the pg15 `security_invoker` reloption on every dev-view, and the
  pg18 AIO observability view `dregg.mirror_io_stats` (real `cache_hit_ratio`s);
- shows the `dregg.turns` hash chain (each `prev_root` is the prior `ledger_root`);
- submits a TAMPERED ord-2 (substituted `prev_root`) — the trigger RAISEs
  `dregg: turn 2 does not chain onto the head root — refused
  (anti-substitution)`, and a replayed ord-0 is refused too;
- confirms the store is INTACT (still 2 turns, ALICE still 400);
- confirms the privilege lockdown (an app role has zero write on state; only the
  kernel submits);
- mints an ALICE-only `submit` token (`cargo run --example mint`), shows a submit
  FOR ALICE succeed and a submit FOR BOB refused by RLS, the pg18 `uuidv7` queue
  key as an audit signal (`dregg.submit_queue_audit` recovers `id_version=7` + the
  enqueue time from the key), and the OAuth→role→cap bind seam (`dregg_bind_role`
  binds the role; `dregg.role_bindings` shows it without leaking the token).

```
pg-dregg/scripts/e2e-live.sh
```

The live node mirror writer (`node/src/pg_mirror.rs`, the `pg-mirror-live`
feature) carries its own integration test (`pg_sink_writes_through_to_live_pg`,
run with `DREGG_PG_MIRROR_TEST_URL` pointing at a live pg18): a real `PgMirror`
over a real `PgSink` ships a chained sequence through `tokio-postgres`, the rows
land via `dregg.merge_cell`, and the pg side re-validates the chain it received.

---

## 10. Federation hardening — pg18 logical-replication conflict observability

§15 of `docs/PG-DREGG.md` federates dregg via PostgreSQL's own logical
replication: the publisher's `dregg.turns` hash chain *is* the replicated feed,
and a subscriber that tails it re-validates the chain locally
(`dregg_revalidate_replicated_chain`) rather than trusting the stream. The
dregg model is **single-writer fan-out**: the publisher is the only writer;
subscribers are read replicas. That makes an *apply conflict* on a subscriber — a
row it already holds (`confl_insert_exists`), a missing update/delete target
(`confl_update_missing` / `confl_delete_missing`), a divergent origin
(`confl_update_origin_differs`) — a structural **anomaly**: it means the stream is
not the clean verified-turn feed the model assumes.

pg18 newly **counts those conflicts per subscription**, in
`pg_stat_subscription_stats` (the seven `confl_*` columns — `confl_insert_exists`,
`confl_update_origin_differs`, `confl_update_exists`, `confl_update_missing`,
`confl_delete_origin_differs`, `confl_delete_missing`,
`confl_multiple_unique_conflicts`). `dregg.replication_conflicts` surfaces them as
a mirror-facing alarm, joining `pg_subscription` for the subscription name and
summing the seven kinds into a single `conflicts_total` — so a non-zero value is
an immediate *"the replicated feed diverged — investigate"* signal. It
**composes** with the chain-tooth re-validation, on two different layers: the
tooth catches a substituted *root* (turn N's `ledger_root` ≠ turn N+1's
`prev_root`); the conflict counters catch an apply-level divergence postgres
itself detected during replication. The view is empty on a publisher (no
subscriptions) and populated on a subscriber. It is a thin SELECT over the stats
view (no row data). *Proven by*
`pg18_replication_conflicts_view_resolves_with_the_total_alarm` (live pg18: the
view resolves and binds the pg18 `confl_*` columns; the `conflicts_total` alarm
sums them).

(The subscriber bootstrap itself stays a `pg_createsubscriber` runbook —
`dregg_federation_subscriber_runbook` — and the subscription is created `WITH
(failover = true)` so it survives publisher failover, a pg17 failover-slot
feature. pg18 additionally adds `pg_createsubscriber --all` and
`--enable-two-phase`, and `pg_recvlogical --enable-failover`, noted in the runbook
as operator options.)

---

## 11. The integrity floor — pg18 data checksums by default

dregg's thesis is integrity *all the way down*: the kernel commits a sorted-leaf
ledger root, the chain tooth refuses a substituted batch (§7), and the whole-chain
IVC light client attests that every turn executed correctly (`src/attest.rs`).
Every one of those guarantees is *about the bytes the database holds* — and so all
of them quietly **assume page-level integrity**: that the heap/index page postgres
reads back is the page it wrote, not silently-corrupted storage. pg18 makes that
floor the default: **`initdb` now enables data checksums** (every page carries a
checksum the engine verifies on read, so on-disk corruption surfaces as a *loud
error* instead of a wrong byte fed up into the mirror, the root recomputation, or
a verifier). Pre-18 this required an explicit `initdb --data-checksums` (or an
offline `pg_checksums --enable`), and was easy to forget.

`pg-dregg` makes the floor **legible and assertable** rather than merely assumed:
`dregg.integrity_status` projects the read-only `data_checksums` GUC (postgres
sets it from the cluster's control file — `'on'` when checksums are active), the
derived boolean `checksums_enabled`, and the `block_size` the checksum covers. A
setup step (or an operator) reads it to *confirm* the mirror sits on a checksummed
cluster — the page integrity the higher tiers stand on — and a deployment check
can fail loudly if it finds `off`. It is a thin SELECT over GUCs (no row data).
*Proven by* `pg18_data_checksums_are_on_and_integrity_status_reports_it` (live
pg18: the cargo-pgrx cluster, `initdb`'d under the pg18 default, reads
`data_checksums = 'on'` both directly and through the view).

> **The honest scope.** Page checksums catch *storage* corruption (a flipped bit
> on disk, a torn page), not a *malicious authenticated* write — that is the job of
> the chain tooth and the IVC proof, which sit above this floor. The value pg18
> adds is that the floor is now on by default, and `dregg.integrity_status` makes
> the otherwise-invisible "is this cluster checksummed?" a first-class, tested fact
> of the deployment.

---

## 12. Bulk identity onboarding — pg18 `COPY … ON_ERROR ignore`

The OAuth→role→capability bind map (§6) is a DBA-owned table, `dregg.role_identity`,
that a login hook reads to bind each connecting role to its dregg capability.
Provisioning *many* federated identities at once — an IdP export of
`(pg_role, agent_hex, token)` rows — is a real bootstrap path, and a single
malformed line in that export (a bad-hex agent, a truncated row) should not abort
the whole load. pg18 adds **`ON_ERROR ignore`** to `COPY FROM` (with
`REJECT_LIMIT n` to cap how many bad rows are tolerated before it *does* fail, and
the `LOG_VERBOSITY silent` level to suppress per-row notices), so a bulk load
**skips** the malformed rows and lands the good ones, instead of the pre-18
all-or-nothing abort.

`pg-dregg` wires this **without ever loosening the trust seam**. The COPY targets
a *text* staging table, `dregg.role_identity_load` — never `role_identity`
directly — so a malformed row is just a skipped parse error. The DBA then runs
`SELECT * FROM dregg.promote_role_identity_load()`, which validates each staged
row (decodes the hex agent; a bad one is *skipped and counted*, never written) and
upserts the valid ones **through the same audited `dregg.bind_role` seam** the
single-binding path uses. So the bulk path inherits exactly the one-seam
discipline: a binding only ever reaches `role_identity` via `bind_role`, in bulk
or singly; the staging table is a quarantine, not a second door. The COPY command
itself needs a literal path + format, so the recommended form is emitted as a
ready-to-run template — `dregg_load_role_identity_sql(csv_path, reject_limit)`,
like the federation runbook — while the staging table and the validate-and-promote
function are real, shipped DDL. *Proven by*
`pg18_copy_on_error_bulk_loads_bind_map_skipping_bad_rows` (live pg18: a CSV with
a type-bad row is loaded with `ON_ERROR ignore` — the good rows land, the bad one
is skipped — and a bad-hex staged binding is then *skipped* by the promote step
while the valid one reaches `role_identity` through `bind_role`).

> Because `COPY … FROM PROGRAM`/`FROM '<path>'` is itself a privileged operation
> (server-side file/program access), bulk onboarding is a DBA/bootstrap action, not
> an app-role one — which matches who provisions the identity map in the first
> place.

---

## 13. What pg18 offers that pg-dregg deliberately does NOT adopt (yet)

Being pg18-native is a discipline of taking the features that serve a dregg
property and *declining* the ones that do not. Three pg18 capabilities were
evaluated this pass and are **not** adopted, each for a stated reason — recorded
here so the inventory is honest about the boundary.

**Temporal constraints (`WITHOUT OVERLAPS` / `PERIOD`) — DEFERRED, needs a
node-side schema it does not yet have.** pg18 genuinely ships temporal `PRIMARY
KEY`/`UNIQUE` (`WITHOUT OVERLAPS`) *and* temporal `FOREIGN KEY` (`PERIOD`) — both,
in 18 (the FK half, reverted from 17, landed for 18; Paul A. Jungwirth). A
`WITHOUT OVERLAPS` constraint requires its final column to be a **range/multirange
type**, is implemented internally as `EXCLUDE USING GIST (… WITH =, period WITH
&&)`, and needs the `btree_gist` extension when the equality columns are scalars
like `bytea`/`uuid`. The catch for the *current* mirror: it has **no
validity-interval column** — `dregg.cells` and `dregg.capabilities` are keyed by
`(cell_id)` / `(holder, slot)` with **"latest post-image wins"** semantics (the
MERGE upsert in §7 *overwrites in place*). A temporal PK would *forbid* that
overwrite, breaking the materialization model. The genuine fit is a **bitemporal
capability-history** surface — a cap's authority over a *validity range*, so an
auditor can ask *"what could this holder do at time T?"* and a temporal FK can
enforce that a delegation's lifetime is covered by its grantor's — but that is a
**new** relation fed by a **node-side projection** of cap validity intervals
(`pg-dregg` has no `dregg-cell`, so it cannot decode them; that decode lives in
`node/src/pg_mirror.rs`). It is therefore a node-mirror-paired follow-up, not an
in-extension change. *Closure plan:* (1) node projects `(holder, slot, target,
valid_range tstzrange, …)` history rows; (2) a new `dregg.cap_history` table with
`PRIMARY KEY (holder, slot, valid_range WITHOUT OVERLAPS)` (+ `btree_gist`); (3)
optionally a temporal FK from a delegation's range to its grantor's. (Note: the
prior framing of this doc described pg-dregg as already using a "GiST `EXCLUDE`
idiom" — it does **not**; there is no exclusion constraint or range column in the
mirror today, which is exactly why temporal constraints are net-new, not a
swap-in.)

**`COPY … ON_ERROR` into the *state* tables — REJECTED (forbidden by the spine).**
COPY is a bulk *writer*; the spine invariant is that a state row exists ONLY as a
verified-turn post-image applied through the ONE door (the `commit_log` trigger,
§7). A `COPY` into `dregg.cells`/`turns`/`capabilities`/`memory` would be an
unverified write path, which the Tier-B privilege lockdown explicitly forbids. So
`ON_ERROR` is adopted ONLY for the non-state, DBA-owned bootstrap surface (the
identity bind map, §12), never for state.

**Transparent pg18 wins that need no code — noted, not "adopted".** Several pg18
improvements benefit the mirror with *zero* schema or extension change, so there
is nothing to wire (claiming them as "added" would be theatre): the **asynchronous
I/O** engine speeds the mirror's large scans under the existing views (§8);
**parallel `GIN` index builds** speed building `cells_fields_gin` (the
`fields_json` jsonb index) with no DDL change; and `EXPLAIN ANALYZE` now includes
**`BUFFERS` by default**, which the §8 skip-scan plan check benefits from for free.
These are real reasons to be *on* pg18; they are engine behavior, not features the
extension declares.

---

## 14. Feature inventory

| pg feature | version | clause served | where |
|------------|---------|---------------|-------|
| SQL/JSON jsonpath (`jsonb_path_exists`, `starts with`) | 12 / 17 | rich reads | §2, `src/jsonpath.rs` |
| builtin C collation `pg_c_utf8` | 17 | rich reads (deterministic order) | §3, the `cells_by_canonical` index + `canonical_cells` view |
| **VIRTUAL generated columns** (now the default) | **18** | rich reads (no-drift, no-storage projections) | §4, `dregg.cells` (`cell_root_hex`/`balance_field`) |
| STORED generated columns | 12 | rich reads (indexed canonical key) | §4, `dregg.cells` (`cell_hex`) |
| SQL/JSON `JSON_TABLE` | 17 | rich reads (JSON → rows) | §5, the three projection views |
| **B-tree skip scan** | **18** | rich reads (one index, two access paths) | §8, `cells_by_mode_balance` |
| **`security_invoker` views** | 15 | read gate (RLS through every dev-view, declared) | §6/§8, all dev-views `WITH (security_invoker = true)` |
| login event trigger | 17 | pg-native authz | §6, `dregg.on_login` |
| **`oauth` authentication method** | **18** | pg-native authz (federated identity → role) | §6, composes with `role_identity`; the bind seam `dregg.bind_role`/`dregg.role_bindings` |
| **`uuidv7()`** (temporally sortable) | **18** | pg-native authz (the drain-queue key) | §6, `dregg.submit_queue` |
| **`uuid_extract_timestamp` on v7** (v1-only pre-18) / `uuid_extract_version` (17) | **18** / 17 | pg-native authz (the queue key AS an audit signal) | §6, `dregg.submit_queue_audit` |
| `MERGE` + `merge_action()` | 17 | verified-only writes (atomic upsert) | §7, `dregg.merge_cell` |
| **`RETURNING WITH (OLD/NEW)`** | **18** | verified-only writes (the applicator's typed delta audit + conservation) | §7, `dregg.merge_cell` / `dregg.merge_cell_delta` |
| **asynchronous I/O (AIO)** | **18** | rich reads (faster large scans) | §8, transparent + the `dregg.mirror_io_stats` view over `pg_stat_io` |
| **`pg_aios` in-flight view** | **18** | rich reads (AIO engaged-or-not signal) | §8, `dregg.mirror_aio_inflight` |
| **data checksums by `initdb` default** | **18** | integrity floor (page integrity the roots assume) | §11, `dregg.integrity_status` (the `data_checksums` GUC) |
| **logical-replication `confl_*` counters** | **18** | federation hardening (apply-divergence alarm) | §10, `dregg.replication_conflicts` over `pg_stat_subscription_stats` |
| **`COPY … ON_ERROR ignore` / `REJECT_LIMIT` / `LOG_VERBOSITY silent`** | **18** | pg-native authz (bulk identity onboarding, skip-bad-rows) | §12, `dregg.role_identity_load` + `dregg.promote_role_identity_load` + the `dregg_load_role_identity_sql` template |
| `BEFORE INSERT` re-validating trigger | core | verified-only writes (the one door) | §7, `dregg.apply_verified_turn` |
| `FORCE ROW LEVEL SECURITY` + cap policies | core | read gate + write gate | §6/§7, the RLS |
| failover slots (`failover = true`) + `pg_createsubscriber` | 17 (+ pg18 `--all`/`--enable-two-phase`) | federation (survive publisher failover; bootstrap) | §10, the subscriber runbook |
| temporal `WITHOUT OVERLAPS` / `PERIOD` constraints | 18 (ships) | — *DEFERRED* (needs a node-projected cap-validity range; no range column in the mirror today) | §13, the closure plan |
| `COPY … ON_ERROR` into the *state* tables | 18 | — *REJECTED* (a `COPY` bypasses the verified-write spine; §7) | §13 |
| AIO / parallel GIN builds / `EXPLAIN BUFFERS` default | 18 | transparent perf — *no code* (engine behavior) | §13 |

The deferred / rejected rows are spelled out in §13; the version attribution for
every pg18 feature above was confirmed against the official PostgreSQL 18 release
notes (`postgresql.org/docs/18/release-18.html`). For the
federation-via-logical-replication path and the snapshot/backup complement, see
also `docs/PG-DREGG.md` §15.
