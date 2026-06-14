// `@dregg/sdk/pg` — the pg-dregg-native binding.
//
// The query construction + serialization the helpers build, asserted against
// the REAL `dregg.*` view/function shapes from `pg-dregg/src/lib.rs` +
// `sql/schema-tierB.sql` — via a recording FAKE `PgQueryable` that captures
// every (sql, params) and replays canned rows. No database (mirrors the
// Python `dregg.pg` unit suite). A column-list drift fails here loudly.

import { test } from "node:test";
import assert from "node:assert/strict";

import { pg as loadPg } from "./helpers.mjs";

// ── a recording fake client (the `PgQueryable` surface) ──

function norm(sql) {
  return String(sql).split(/\s+/).join(" ").trim();
}

class FakeClient {
  constructor() {
    this.calls = []; // { sql, params }
    this.responders = []; // { needle, rows }
    this.ended = false;
  }
  when(needle, rows) {
    this.responders.push({ needle, rows });
    return this;
  }
  async query(text, params = []) {
    const sql = norm(text);
    this.calls.push({ sql, params });
    for (const { needle, rows } of this.responders) {
      if (sql.includes(needle)) return { rows };
    }
    return { rows: [] };
  }
  async end() {
    this.ended = true;
  }
  find(needle) {
    const c = this.calls.find((x) => x.sql.includes(needle));
    if (!c) {
      throw new assert.AssertionError({
        message: `no call containing ${JSON.stringify(needle)}; calls=${JSON.stringify(
          this.calls.map((x) => x.sql),
        )}`,
      });
    }
    return c;
  }
  get last() {
    return this.calls[this.calls.length - 1];
  }
}

const cellId = (n) => Uint8Array.from({ length: 32 }, () => n);
const hexOf = (bytes) => Buffer.from(bytes).toString("hex");

// ── presenting authority (GUC + role) ──

test("connect assumes dregg_reader and presents the token", async () => {
  const { Pg, TOKEN_GUC, READER_ROLE } = await loadPg();
  const fake = new FakeClient();
  const pg = await Pg.connect(fake, { token: "dga1_abc" });
  assert.equal(pg.connection, fake);
  // SET ROLE dregg_reader (via set_config('role', …)).
  const roleCall = fake.find("'role'");
  assert.deepEqual(roleCall.params, [READER_ROLE]);
  // present the token via set_config('dregg.token', …, false).
  const tokCall = fake.find("set_config($1, $2, $3)");
  assert.deepEqual(tokCall.params, [TOKEN_GUC, "dga1_abc", false]);
});

test("connect with role:null stays the connecting role (no SET ROLE)", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient();
  await Pg.connect(fake, { role: null });
  assert.equal(
    fake.calls.some((c) => c.sql.includes("'role'")),
    false,
  );
});

test("presentToken local=true is transaction-scoped", async () => {
  const { Pg, TOKEN_GUC } = await loadPg();
  const fake = new FakeClient();
  const pg = await Pg.connect(fake, { role: null });
  await pg.presentToken("dga1_xyz", true);
  assert.deepEqual(fake.find("set_config($1, $2, $3)").params, [TOKEN_GUC, "dga1_xyz", true]);
});

test("setRole validates the identifier shape", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient();
  const pg = await Pg.connect(fake, { role: null });
  await pg.setRole("dregg_reader"); // ok
  await assert.rejects(() => pg.setRole("evil; DROP"), /invalid role identifier/);
});

test("currentToken reads current_setting missing-ok, empty ⇒ null", async () => {
  const { Pg } = await loadPg();
  const live = new FakeClient().when("current_setting", [{ current_setting: "dga1_live" }]);
  const pgLive = await Pg.connect(live, { role: null });
  assert.equal(await pgLive.currentToken(), "dga1_live");
  const empty = new FakeClient().when("current_setting", [{ current_setting: "" }]);
  const pgEmpty = await Pg.connect(empty, { role: null });
  assert.equal(await pgEmpty.currentToken(), null);
});

// ── free-SQL reads bind the REAL view column lists ──

test("cellBalances binds the real dregg.cell_balances projection", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient().when("dregg.cell_balances", [
    { cell: "c011", balance: 999500, nonce: 1, lifecycle: "Active", last_ordinal: 3 },
  ]);
  const pg = await Pg.connect(fake, { role: null });
  const rows = await pg.cellBalances();
  const sql = fake.last.sql;
  assert.match(sql, /SELECT cell, balance, nonce, lifecycle, last_ordinal/);
  assert.match(sql, /FROM dregg\.cell_balances/);
  assert.match(sql, /ORDER BY balance DESC/);
  assert.equal(rows.length, 1);
  assert.equal(rows[0].balance, 999500n);
  assert.equal(rows[0].nonce, 1n);
  assert.equal(rows[0].lifecycle, "Active");
  assert.equal(rows[0].lastOrdinal, 3n);
});

test("cellBalances limit is parameterized", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient().when("dregg.cell_balances", []);
  const pg = await Pg.connect(fake, { role: null });
  await pg.cellBalances({ limit: 10 });
  const c = fake.find("dregg.cell_balances");
  assert.match(c.sql, /LIMIT \$1/);
  assert.deepEqual(c.params, [10]);
});

test("cellBalance by id filters on the hex key", async () => {
  const { Pg } = await loadPg();
  const id = cellId(0xa1);
  const fake = new FakeClient().when("dregg.cell_balances", [
    { cell: hexOf(id), balance: 400, nonce: 2, lifecycle: "Active", last_ordinal: 2 },
  ]);
  const pg = await Pg.connect(fake, { role: null });
  const row = await pg.cellBalance(id);
  const c = fake.find("dregg.cell_balances");
  assert.match(c.sql, /WHERE cell = \$1/);
  assert.deepEqual(c.params, [hexOf(id)]);
  assert.equal(row.balance, 400n);
});

test("receiptChain binds the real view and the chain links", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient().when("dregg.receipt_chain", [
    { ordinal: 0, height: 0, creator: "c011", prev_root: "00", ledger_root: "3488", committed_at: null },
    { ordinal: 1, height: 1, creator: "c011", prev_root: "3488", ledger_root: "1063", committed_at: null },
  ]);
  const pg = await Pg.connect(fake, { role: null });
  const rows = await pg.receiptChain();
  const sql = fake.last.sql;
  assert.match(sql, /SELECT ordinal, height, creator, prev_root, ledger_root, committed_at/);
  assert.match(sql, /FROM dregg\.receipt_chain ORDER BY ordinal/);
  assert.deepEqual(
    rows.map((r) => r.ordinal),
    [0n, 1n],
  );
  // turn N's ledger_root is turn N+1's prev_root (the RootChain tooth).
  assert.equal(rows[0].ledgerRoot, rows[1].prevRoot);
});

test("chainHead takes the latest ordinal; null on empty", async () => {
  const { Pg } = await loadPg();
  const head = new FakeClient().when("dregg.receipt_chain", [
    { ordinal: 3, height: 3, creator: "a111", prev_root: "5770", ledger_root: "203e", committed_at: null },
  ]);
  const pgHead = await Pg.connect(head, { role: null });
  const h = await pgHead.chainHead();
  assert.match(head.last.sql, /ORDER BY ordinal DESC LIMIT 1/);
  assert.equal(h.ordinal, 3n);
  assert.equal(h.ledgerRoot, "203e");
  const empty = new FakeClient().when("dregg.receipt_chain", []);
  const pgEmpty = await Pg.connect(empty, { role: null });
  assert.equal(await pgEmpty.chainHead(), null);
});

test("capEdges binds the real dregg.cap_edges projection", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient().when("dregg.cap_edges", [
    { src: "a111", dst: "b011", slot: 0, permissions: { transfer: "delegated" }, expires_at: 10000 },
  ]);
  const pg = await Pg.connect(fake, { role: null });
  const edges = await pg.capEdges();
  assert.match(fake.last.sql, /SELECT src, dst, slot, permissions, expires_at/);
  assert.match(fake.last.sql, /FROM dregg\.cap_edges/);
  assert.equal(edges[0].src, "a111");
  assert.equal(edges[0].dst, "b011");
  assert.equal(edges[0].slot, 0);
  assert.deepEqual(edges[0].permissions, { transfer: "delegated" });
  assert.equal(edges[0].expiresAt, 10000n);
});

test("capEdges src filter is hex-parameterized", async () => {
  const { Pg } = await loadPg();
  const src = cellId(0xa1);
  const fake = new FakeClient().when("dregg.cap_edges", []);
  const pg = await Pg.connect(fake, { role: null });
  await pg.capEdges({ src });
  const c = fake.find("dregg.cap_edges");
  assert.match(c.sql, /WHERE src = \$1/);
  assert.deepEqual(c.params, [hexOf(src)]);
});

test("conservationTotal sums balances", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient().when("sum(balance)", [{ coalesce: 1000000 }]);
  const pg = await Pg.connect(fake, { role: null });
  assert.equal(await pg.conservationTotal(), 1000000n);
  assert.match(fake.last.sql, /coalesce\(sum\(balance\), 0\) FROM dregg\.cells/);
});

// ── the write path: submit a verified turn ──

test("submitTurn calls the real extern with bytea params", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient().when("dregg_submit_turn", [
    { dregg_submit_turn: "11111111-1111-1111-1111-111111111111" },
  ]);
  const pg = await Pg.connect(fake, { role: null });
  const agent = cellId(0xa1);
  const id = await pg.submitTurn(new Uint8Array([0xde, 0xad, 0xbe, 0xef]), agent);
  const c = fake.find("dregg_submit_turn");
  assert.match(c.sql, /SELECT dregg_submit_turn\(\$1, \$2\)/);
  // params are bytea (Buffer) for the turn + the agent.
  assert.ok(Buffer.isBuffer(c.params[0]) || c.params[0] instanceof Uint8Array);
  assert.equal(hexOf(c.params[0]), "deadbeef");
  assert.equal(hexOf(c.params[1]), hexOf(agent));
  assert.equal(id, "11111111-1111-1111-1111-111111111111");
});

test("submitTurn accepts a hex agent string", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient().when("dregg_submit_turn", [{ dregg_submit_turn: "id" }]);
  const pg = await Pg.connect(fake, { role: null });
  const agentHex = "a1" + "00".repeat(31);
  await pg.submitTurn(new Uint8Array([1, 2]), agentHex);
  assert.equal(hexOf(fake.find("dregg_submit_turn").params[1]), agentHex);
});

test("submitTurn rejects a non-bytes turn", async () => {
  const { Pg } = await loadPg();
  const pg = await Pg.connect(new FakeClient(), { role: null });
  await assert.rejects(() => pg.submitTurn("nope", "a1" + "00".repeat(31)), /SignedTurn bytes/);
});

test("enqueueTurn uses the raw INSERT path", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient().when("INSERT INTO dregg.submit_queue", [{ id: "raw-id" }]);
  const pg = await Pg.connect(fake, { role: null });
  const id = await pg.enqueueTurn(new Uint8Array([0, 1]), cellId(0xb0));
  const c = fake.find("INSERT INTO dregg.submit_queue");
  assert.match(c.sql, /INSERT INTO dregg\.submit_queue \(agent, signed_turn\) VALUES \(\$1, \$2\) RETURNING id/);
  assert.equal(id, "raw-id");
});

test("an RLS refusal is wrapped legibly", async () => {
  const { Pg, DreggPgError } = await loadPg();
  const fake = new FakeClient();
  fake.query = async (text) => {
    if (norm(text).includes("dregg_submit_turn")) {
      throw new Error('new row violates row-level security policy for table "submit_queue"');
    }
    return { rows: [] };
  };
  const pg = await Pg.connect(fake, { role: null });
  await assert.rejects(
    () => pg.submitTurn(new Uint8Array([1]), cellId(0)),
    (err) => {
      assert.ok(err instanceof DreggPgError);
      assert.match(err.message, /Row-Level Security/);
      assert.match(err.message, /does not authorize/);
      return true;
    },
  );
});

// ── the outbox tail (view preferred, base table fallback) ──

test("outbox prefers the audit view", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient()
    .when("to_regclass('dregg.submit_queue_audit') IS NOT NULL", [{ "?column?": true }])
    .when("FROM dregg.submit_queue_audit", [
      {
        id: "sub-1",
        agent: "a1",
        submitter: "app",
        status: "executed",
        receipt_hash: "ee",
        error: null,
        submitted_at: null,
        resolved_at: null,
      },
    ]);
  const pg = await Pg.connect(fake, { role: null });
  const out = await pg.outbox();
  const c = fake.find("FROM dregg.submit_queue_audit ORDER BY id");
  assert.match(c.sql, /id, agent, submitter, status, receipt_hash, error, submitted_at, resolved_at/);
  assert.equal(out[0].status, "executed");
  assert.equal(out[0].receiptHash, "ee");
});

test("outbox falls back to the base table when the view is absent", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient()
    .when("to_regclass('dregg.submit_queue_audit') IS NOT NULL", [{ "?column?": false }])
    .when("FROM dregg.submit_queue", [
      {
        id: "sub-2",
        agent: "b0",
        submitter: "app",
        status: "pending",
        receipt_hash: null,
        error: null,
        submitted_at: null,
        resolved_at: null,
      },
    ]);
  const pg = await Pg.connect(fake, { role: null });
  const out = await pg.outbox();
  const c = fake.find("FROM dregg.submit_queue ORDER BY id");
  assert.match(c.sql, /encode\(agent,'hex'\) AS agent/);
  assert.match(c.sql, /encode\(receipt_hash,'hex'\) AS receipt_hash/);
  assert.equal(out[0].status, "pending");
});

// ── federation health / issuer status / dev mint bind the real functions ──

test("federationHealth binds the function and classifies the verdict", async () => {
  const { Pg } = await loadPg();
  const ok = new FakeClient().when("dregg_federation_health", [
    { dregg_federation_health: "ok: federation healthy — 1 subscription(s), 0 apply conflicts" },
  ]);
  const pgOk = await Pg.connect(ok, { role: null });
  assert.match(await pgOk.federationHealth(), /^ok:/);
  assert.match(ok.find("dregg_federation_health").sql, /SELECT dregg_federation_health\(\)/);
  assert.equal(await pgOk.federationHealthOk(), true);

  const crit = new FakeClient().when("dregg_federation_health", [
    { dregg_federation_health: "CRITICAL (2 apply conflict(s)) AND chain REFUSED: root does not chain" },
  ]);
  const pgCrit = await Pg.connect(crit, { role: null });
  assert.equal(await pgCrit.federationHealthOk(), false);
});

test("issuerStatus binds the function", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient().when("dregg_issuer_status", [
    { dregg_issuer_status: "verify key CONFIGURED (id ab…)" },
  ]);
  const pg = await Pg.connect(fake, { role: null });
  assert.match(await pg.issuerStatus(), /CONFIGURED/);
});

test("devMint passes a text[] and casts the interval", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient().when("dregg_dev_mint", [{ dregg_dev_mint: "dga1_minted" }]);
  const pg = await Pg.connect(fake, { role: null });
  const tok = await pg.devMint("alice", ["read", "write"], "org/42/", "1 hour");
  const c = fake.find("dregg_dev_mint");
  assert.match(c.sql, /SELECT dregg_dev_mint\(\$1, \$2, \$3, \$4::interval\)/);
  assert.equal(c.params[0], "alice");
  assert.deepEqual(c.params[1], ["read", "write"]);
  assert.equal(c.params[2], "org/42/");
  assert.equal(c.params[3], "1 hour");
  assert.equal(tok, "dga1_minted");
});

test("capAdmits defaults now to the db clock", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient()
    .when("extract(epoch from now())", [{ date_part: 1700000000 }])
    .when("dregg_cap_admits", [{ dregg_cap_admits: true }]);
  const pg = await Pg.connect(fake, { role: null });
  assert.equal(await pg.capAdmits("dga1_x", "read", "org/42/doc"), true);
  assert.deepEqual(fake.find("dregg_cap_admits").params, ["dga1_x", "read", "org/42/doc", 1700000000]);
});

test("capExplain / capSubject / revoke bind their functions", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient()
    .when("extract(epoch from now())", [{ date_part: 1 }])
    .when("dregg_cap_explain", [{ dregg_cap_explain: "allowed" }])
    .when("dregg_cap_subject", [{ dregg_cap_subject: "agent-1" }])
    .when("dregg_revoke", [{ dregg_revoke: "capid123" }]);
  const pg = await Pg.connect(fake, { role: null });
  assert.equal(await pg.capExplain("dga1", "read", "r", 1), "allowed");
  assert.equal(await pg.capSubject("dga1"), "agent-1");
  assert.equal(await pg.revoke("dga1"), "capid123");
});

test("install helpers bind the externs", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient()
    .when("dregg_install_schema", [{ dregg_install_schema: "dregg Tier-B store installed: 4 tables" }])
    .when("dregg_install_write_outbox", [{ dregg_install_write_outbox: "dregg write outbox installed" }]);
  const pg = await Pg.connect(fake, { role: null });
  assert.match(await pg.installSchema(), /Tier-B store installed/);
  assert.match(await pg.installWriteOutbox(), /write outbox installed/);
});

// ── lifecycle ──

test("close releases a client that exposes end()", async () => {
  const { Pg } = await loadPg();
  const fake = new FakeClient();
  const pg = await Pg.connect(fake, { role: null });
  await pg.close();
  assert.equal(fake.ended, true);
});
