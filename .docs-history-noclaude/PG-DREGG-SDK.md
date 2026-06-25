# pg-dregg from the SDKs — Python and TypeScript

pg-dregg makes postgres a native dregg surface (`docs/PG-DREGG.md`). The dregg
SDKs bind that surface directly, so a developer drives a pg-dregg-enabled
postgres idiomatically — no bespoke HTTP, no hand-rolled SQL.

The model the SDK helpers follow is pg-dregg's spine (`docs/PG-DREGG.md` §8):

> **Reads are free SQL; state mutates ONLY through verified turns.**

So the surface is small and shaped by that invariant:

| Helper | What it does | Binds |
|---|---|---|
| connect | open a handle; present a token + assume `dregg_reader` so RLS bites | the `dregg.token` GUC + `SET ROLE` |
| submit a verified turn | enqueue a signed turn for the node's drainer to apply | `dregg_submit_turn(signed_turn, agent)` |
| read state as free SQL | typed projections of cells / turns / caps | `dregg.cell_balances` / `receipt_chain` / `cap_edges` |
| outbox tail | each submission and its drain outcome | `dregg.submit_queue_audit` (base table fallback) |
| federation health | conflict-counter-driven chain re-validation | `dregg_federation_health()` |
| dev-mint / issuer-status | compose a dev token; report the key config | `dregg_dev_mint` / `dregg_issuer_status` |

Presenting an attenuated token narrows the rows you may `SELECT` to a strict
subset — the no-amplification property, enforced by RLS. A superuser BYPASSes
RLS, so the SDKs assume the unprivileged `dregg_reader` role by default.

The write path never executes in postgres: `submit_turn` enqueues an intent the
node's §11.4 drainer runs through the verified executor; only verified
post-state lands. The enqueue is RLS-gated, so a role submits exactly the turns
its capability authorizes.

---

## Python — `dregg.pg`

A thin, typed, `psycopg`-based binding. Pure Python; `psycopg` is imported
lazily, so `import dregg` never requires it.

```bash
pip install 'dregg[pg]'        # pulls psycopg (v3)
```

```python
import dregg.pg as dpg
from datetime import timedelta

# Connect to a pg-dregg-enabled postgres. Presenting a token sets the
# dregg.token GUC and assumes dregg_reader so RLS filters. The DSN defaults to
# $DREGG_PG_DSN / $DATABASE_URL, else the libpq environment.
with dpg.connect("host=/var/run/postgresql dbname=dregg", token="dga1_…") as pg:

    # ── read state as free SQL (typed row projections) ──
    for c in pg.cell_balances(limit=10):        # dregg.cell_balances, richest-first
        print(c.cell, c.balance, c.lifecycle)   # only cells your token admits 'read' on

    head = pg.chain_head()                       # the receipt-chain head (the light client)
    for t in pg.receipt_chain():                 # each prev_root == the prior ledger_root
        ...
    edges = pg.cap_edges()                       # the delegation graph (src → dst)
    total = pg.conservation_total()              # sum(balance) over admitted cells

    # ── submit a verified turn (the node drains it) ──
    # signed_turn is the postcard SignedTurn bytes; agent is its cell id.
    sid = pg.submit_turn(signed_turn_bytes, agent_cell_id)   # returns a uuid
    for s in pg.outbox():                         # status walks pending → executed | refused
        print(s.id, s.status, s.receipt_hash, s.error)

    # ── federation health ──
    print(pg.federation_health())                # 'ok: …' / 'ALARM …' / 'CRITICAL …'
    assert pg.federation_health_ok()

    # ── issuer status + a DEV token (single-tenant on-ramp) ──
    print(pg.issuer_status())                    # discoverable key config; never the privkey
    tok = pg.dev_mint("alice", ["read"], "org/42/", timedelta(hours=1))
    assert pg.cap_admits(tok, "read", "org/42/public/doc1")   # offline-verified, fail-closed
```

`submit_turn` raises `dregg.pg.DreggPgError` (a subclass of `dregg.DreggError`)
when Row-Level Security refuses an enqueue your capability does not authorize —
the message names that it is an authorization refusal, not a bug.

`dev_mint` is DEV ONLY and keeps the issuer-key discipline intact: it routes
through the same mint path as `dregg_mint` and raises if `dregg.issuer_privkey`
is not configured (it never returns a silently-minted token). The production
posture — mint out-of-database, the private key never in postgres — is unchanged.

---

## TypeScript — `@dregg/sdk/pg`

The same shape in TS. No driver is bundled: inject a `pg` (`node-postgres`)
`Client` or `Pool` — any object exposing `query(text, params) → { rows }`
satisfies the `PgQueryable` interface. This mirrors how the SDK treats
`dregg-wasm` (peer, injected).

```bash
npm install pg            # node-postgres (the injected driver)
```

```ts
import { Client } from "pg";
import { Pg } from "@dregg/sdk/pg";

const client = new Client({ host: "/var/run/postgresql", database: "dregg" });
await client.connect();

// Present a token + assume dregg_reader so RLS bites (a superuser BYPASSes RLS).
const pg = await Pg.connect(client, { token: "dga1_…", role: "dregg_reader" });

// ── read state as free SQL ──
for (const c of await pg.cellBalances({ limit: 10 })) {
  console.log(c.cell, c.balance, c.lifecycle); // bigint balances; admitted cells only
}
const head = await pg.chainHead();             // the receipt-chain head
const edges = await pg.capEdges();             // the delegation graph
const total = await pg.conservationTotal();    // sum(balance), as a bigint

// ── submit a verified turn (the node drains it) ──
const sid = await pg.submitTurn(signedTurnBytes, agentCellId); // Uint8Array, Bytes32 → uuid
for (const s of await pg.outbox()) {           // status walks pending → executed | refused
  console.log(s.id, s.status, s.receiptHash, s.error);
}

// ── federation health + dev token ──
console.log(await pg.federationHealth());      // 'ok: …' / 'ALARM …' / 'CRITICAL …'
console.log(await pg.issuerStatus());
const tok = await pg.devMint("alice", ["read"], "org/42/", "1 hour"); // DEV ONLY
console.log(await pg.capAdmits(tok, "read", "org/42/public/doc1"));   // true

await pg.close();
```

`submitTurn` throws `DreggPgError` on an RLS refusal, with the same legible
"your capability does not authorize this" message as the Python binding.

---

## What you bind (the real surface)

Both SDKs bind the shipped pg-dregg surface — the `#[pg_extern]` functions in
`pg-dregg/src/lib.rs` and the `dregg.*` views emitted by `mirror::ddl::tier_b`
(`pg-dregg/sql/schema-tierB.sql`):

- **views** (hex-keyed, `security_invoker` so RLS bites through them):
  `dregg.cell_balances`, `dregg.receipt_chain`, `dregg.cap_edges`,
  `dregg.submit_queue_audit`;
- **write**: `dregg_submit_turn(signed_turn bytea, agent bytea) → uuid` (and the
  raw `INSERT INTO dregg.submit_queue`);
- **functions**: `dregg_federation_health()`, `dregg_dev_mint(subject, actions[],
  resource_prefix, ttl interval)`, `dregg_issuer_status()`,
  `dregg_cap_admits / _explain / _subject / _id`, `dregg_revoke`,
  `dregg_install_schema / _write_outbox`.

The bindings are exercised against these exact SQL shapes (the Python unit tests
assert the column lists; the integration tests run the genuine functions against
a live pg-dregg postgres). See `sdk-py/tests/test_pg.py` and
`sdk-ts/test/pg.test.mjs`.

> The pg18 `dregg.submit_queue_audit` view recovers the enqueue time + version
> from the `uuidv7` key; where it is absent (older / pg17 installs whose
> `uuid_extract_*` functions are unavailable) the outbox helpers fall back to the
> base `dregg.submit_queue` table.
