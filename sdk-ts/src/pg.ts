/**
 * `@dregg/sdk/pg` — pg-dregg-native ergonomics for the TypeScript SDK.
 *
 * A thin, typed binding of the **real** pg-dregg SQL surface
 * (`pg-dregg/src/lib.rs` + the `dregg.*` schema emitted by
 * `mirror::ddl::tier_b`). It mirrors the highest-value helpers of the Python
 * `dregg.pg` module so a developer drives a pg-dregg-enabled postgres
 * idiomatically from TS. It binds what pg-dregg actually ships — it does not
 * invent a surface.
 *
 * THE MODEL pg-dregg enforces (`.docs-history-noclaude/PG-DREGG.md` §8, the spine):
 *
 * > Reads are free SQL; state mutates ONLY through verified turns.
 *
 * So the helpers fall into exactly that shape:
 *
 * - **connect** — {@link Pg.connect} wraps a `pg`/`node-postgres`-style client.
 *   Presenting a capability token ({@link Pg.presentToken}) sets the
 *   `dregg.token` session GUC and assumes `dregg_reader`, so Row-Level Security
 *   bites (a superuser BYPASSes RLS — `pg-dregg/docs/QUICKSTART-pg-user.md` §2).
 * - **submit a verified turn** — {@link Pg.submitTurn} enqueues a signed turn
 *   via the real `dregg_submit_turn(signed_turn, agent)` extern (RLS-gated by
 *   `dregg_admits('submit', …)`). The node's §11.4 drainer applies it through
 *   the verified executor. **Postgres never executes.**
 * - **read state as free SQL** — typed row projections over the shipped views:
 *   {@link Pg.cellBalances} (`dregg.cell_balances`), {@link Pg.receiptChain}
 *   (`dregg.receipt_chain`), {@link Pg.capEdges} (`dregg.cap_edges`).
 * - **federation health** — {@link Pg.federationHealth} calls the real
 *   `dregg_federation_health()` (`.docs-history-noclaude/PG-DREGG.md` §15).
 * - **dev-mint / issuer-status** — {@link Pg.devMint} (`dregg_dev_mint`, DEV
 *   ONLY) and {@link Pg.issuerStatus} (`dregg_issuer_status`).
 *
 * No driver is bundled. Inject any client exposing a `query(text, params)` that
 * resolves `{ rows }` — `pg`'s `Client`/`Pool` satisfy {@link PgQueryable}
 * directly. This mirrors how the SDK treats `dregg-wasm` (peer, injected),
 * keeping the wire layer driver-agnostic and trivially testable.
 *
 * @packageDocumentation
 */

import { hexDecode, hexEncode } from "./internal/bytes";

/** The session GUC the `dregg_admits` policies read the presented token from. */
export const TOKEN_GUC = "dregg.token";
/** The application role: `SELECT` only, RLS-gated by the M1 caps. */
export const READER_ROLE = "dregg_reader";
/** The verified writer (`BYPASSRLS`); the node drains the outbox as this role. */
export const KERNEL_ROLE = "dregg_kernel";

/** A 32-byte identifier the SQL surface accepts as `bytea`: 64-char hex or 32 raw bytes. */
export type Bytes32 = string | Uint8Array;

/**
 * The minimal client surface this binding needs — exactly what `pg`'s `Client`
 * and `Pool` already expose. Inject one of those, or any object whose `query`
 * resolves `{ rows: T[] }`.
 */
export interface PgQueryable {
  query(text: string, params?: unknown[]): Promise<{ rows: unknown[] }>;
  /** Optional: released by {@link Pg.close} when present (e.g. a `pg.Client`). */
  end?(): Promise<void>;
}

/** A pg-dregg SDK error (a bad query, a missing surface, or an RLS refusal). */
export class DreggPgError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "DreggPgError";
  }
}

// ── typed row projections (each mirrors one shipped view's column shape) ──

/** A row of `dregg.cell_balances` — hex-keyed, balance-first ledger. */
export interface CellBalance {
  cell: string; // encode(cell_id,'hex')
  balance: bigint;
  nonce: bigint;
  lifecycle: string;
  lastOrdinal: bigint;
}

/** A row of `dregg.receipt_chain` — the turn hash chain a light client walks. */
export interface ReceiptRow {
  ordinal: bigint;
  height: bigint;
  creator: string; // encode(creator,'hex')
  prevRoot: string; // encode(prev_root,'hex')
  ledgerRoot: string; // encode(ledger_root,'hex')
  committedAt: Date | null;
}

/** A row of `dregg.cap_edges` — the delegation graph (`src → dst`). */
export interface CapEdge {
  src: string; // encode(holder,'hex')
  dst: string; // encode(target,'hex')
  slot: number;
  permissions: unknown; // jsonb
  expiresAt: bigint | null;
}

/** A row of the submit-queue audit surface — a submission and its drain outcome. */
export interface Submission {
  id: string; // uuid
  agent: string; // encode(agent,'hex')
  submitter: string;
  status: "pending" | "executed" | "refused" | string;
  receiptHash: string | null;
  error: string | null;
  submittedAt: Date | null;
  resolvedAt: Date | null;
}

/** A connection time-to-live for the dev-mint helper (postgres interval literal). */
export type Interval = string; // e.g. "1 hour", "5 min"

function toBytea(value: Bytes32, what = "identifier"): Uint8Array {
  if (value instanceof Uint8Array) return value;
  if (typeof value === "string") {
    const s = value.startsWith("\\x") || value.startsWith("0x") ? value.slice(2) : value;
    try {
      return hexDecode(s);
    } catch {
      throw new DreggPgError(`${what} hex is not valid: ${value}`);
    }
  }
  throw new DreggPgError(`${what} must be 64-char hex or 32 bytes`);
}

/**
 * Bind a `bytea` param the way `node-postgres` expects: a Node `Buffer`. `pg`
 * encodes a `Buffer` as `bytea`; a bare `Uint8Array` is NOT recognized, so we
 * wrap it. (`Buffer.from(view)` copies; the inputs here are small ids/turns.)
 */
function bytea(value: Uint8Array): Uint8Array {
  // `Buffer` is a `Uint8Array` subclass; use it when available (Node), else the
  // raw view (a test fake just records it).
  const B = (globalThis as { Buffer?: { from(v: Uint8Array): Uint8Array } }).Buffer;
  return B ? B.from(value) : value;
}

const ROLE_RE = /^[A-Za-z_][A-Za-z0-9_]{0,62}$/;
function validateIdent(ident: string): string {
  if (!ROLE_RE.test(ident)) throw new DreggPgError(`invalid role identifier: ${ident}`);
  return ident;
}

function asBigInt(v: unknown): bigint {
  if (typeof v === "bigint") return v;
  if (typeof v === "number") return BigInt(v);
  if (typeof v === "string") return BigInt(v);
  throw new DreggPgError(`expected an integer, got ${typeof v}`);
}

function asBigIntOrNull(v: unknown): bigint | null {
  return v === null || v === undefined ? null : asBigInt(v);
}

function asDateOrNull(v: unknown): Date | null {
  if (v === null || v === undefined) return null;
  return v instanceof Date ? v : new Date(String(v));
}

function asStringOrNull(v: unknown): string | null {
  return v === null || v === undefined ? null : String(v);
}

function wrapPgError(err: unknown, what: string): DreggPgError {
  const msg = String((err as { message?: string })?.message ?? err).trim();
  const lower = msg.toLowerCase();
  if (lower.includes("row-level security")) {
    return new DreggPgError(
      `${what}: refused by Row-Level Security — your presented capability does ` +
        `not authorize it (the submit_gate / read policy denied it). Present a ` +
        `token that admits it, and assume the dregg_reader role. [${msg}]`,
    );
  }
  if (lower.includes("does not exist") && (lower.includes("function") || lower.includes("dregg"))) {
    return new DreggPgError(
      `${what}: the pg-dregg surface is not installed in this database ` +
        `(CREATE EXTENSION pg_dregg; SELECT dregg_install_schema();). [${msg}]`,
    );
  }
  return new DreggPgError(`${what}: ${msg}`);
}

/** Options for {@link Pg.connect}. */
export interface PgConnectOptions {
  /** A `dga1_…` capability token to present immediately (sets the `dregg.token` GUC). */
  token?: string;
  /**
   * The role to assume after connecting so RLS bites — defaults to
   * `dregg_reader`. Pass `null` to stay the connecting role (e.g. `dregg_kernel`
   * for the drainer, or a superuser for admin). A superuser BYPASSes RLS.
   */
  role?: string | null;
}

/**
 * A handle on a pg-dregg database. Wraps a {@link PgQueryable} (a `pg.Client`,
 * `pg.Pool`, or any compatible client). The read helpers build parameterized
 * queries over the shipped `dregg.*` views; the write/admin helpers call the
 * real `#[pg_extern]` functions.
 *
 * ```ts
 * import { Client } from "pg";
 * import { Pg } from "@dregg/sdk/pg";
 *
 * const client = new Client({ host: "/var/run/postgresql", database: "dregg" });
 * await client.connect();
 * const pg = await Pg.connect(client, { token, role: "dregg_reader" });
 * for (const c of await pg.cellBalances()) console.log(c.cell, c.balance);
 * ```
 */
export class Pg {
  private constructor(private readonly client: PgQueryable) {}

  /**
   * Wrap an already-connected client and (optionally) present a token + assume a
   * role. Mirrors `dregg.pg.connect`. The client must already be connected (this
   * does not open the socket — inject a `pg.Client`/`pg.Pool` you connected).
   */
  static async connect(client: PgQueryable, opts: PgConnectOptions = {}): Promise<Pg> {
    const pg = new Pg(client);
    const role = opts.role === undefined ? READER_ROLE : opts.role;
    if (role !== null) await pg.setRole(role);
    if (opts.token !== undefined) await pg.presentToken(opts.token);
    return pg;
  }

  /** The underlying client (escape hatch for raw SQL). */
  get connection(): PgQueryable {
    return this.client;
  }

  /** Release the client if it exposes `end()` (a `pg.Client`/`pg.Pool`). */
  async close(): Promise<void> {
    if (typeof this.client.end === "function") await this.client.end();
  }

  // ── small query helpers ──
  private async rows(text: string, params: unknown[] = []): Promise<unknown[]> {
    const res = await this.client.query(text, params);
    return res.rows;
  }

  private async scalar<T = unknown>(text: string, params: unknown[] = []): Promise<T | null> {
    const rows = (await this.rows(text, params)) as Record<string, unknown>[];
    if (rows.length === 0) return null;
    const row = rows[0];
    const keys = Object.keys(row);
    return (keys.length ? row[keys[0]] : null) as T | null;
  }

  // ── presenting authority (the capability the rows are gated by) ──

  /**
   * Present a `dga1_…` capability token for the session by setting the
   * `dregg.token` GUC (`set_config('dregg.token', token, local)`). The
   * `dregg_admits` RLS policies read it. With `local=true` it is
   * transaction-local. A superuser BYPASSes RLS; assume `dregg_reader` (the
   * default in {@link Pg.connect}) so the policy fires.
   */
  async presentToken(token: string, local = false): Promise<void> {
    await this.scalar("SELECT set_config($1, $2, $3)", [TOKEN_GUC, token, local]);
  }

  /** Clear the presented token (present the empty string ⇒ deny-by-default). */
  async clearToken(local = false): Promise<void> {
    await this.scalar("SELECT set_config($1, $2, $3)", [TOKEN_GUC, "", local]);
  }

  /** The token currently presented, or `null` if none. */
  async currentToken(): Promise<string | null> {
    const tok = await this.scalar<string>("SELECT current_setting($1, true)", [TOKEN_GUC]);
    return tok ? tok : null;
  }

  /** `SET ROLE` — assume `role` so RLS is enforced as it (`dregg_reader` for apps). */
  async setRole(role: string): Promise<void> {
    await this.scalar("SELECT set_config('role', $1, false)", [validateIdent(role)]);
  }

  /** `RESET ROLE`. */
  async resetRole(): Promise<void> {
    await this.scalar("RESET ROLE");
  }

  // ── free-SQL reads (typed projections of the shipped views) ──

  /**
   * `dregg.cell_balances` — the ledger, hex-keyed and balance-first. Only the
   * cells the presented token admits `read` on are returned (read-side RLS).
   */
  async cellBalances(opts: { orderByBalance?: boolean; limit?: number } = {}): Promise<CellBalance[]> {
    const orderByBalance = opts.orderByBalance ?? true;
    let sql = "SELECT cell, balance, nonce, lifecycle, last_ordinal FROM dregg.cell_balances";
    if (orderByBalance) sql += " ORDER BY balance DESC";
    const params: unknown[] = [];
    if (opts.limit !== undefined) {
      sql += " LIMIT $1";
      params.push(opts.limit);
    }
    const rows = (await this.rows(sql, params)) as Record<string, unknown>[];
    return rows.map(rowToCellBalance);
  }

  /** One cell's row by id, or `null` if absent / not admitted. */
  async cellBalance(cell: Bytes32): Promise<CellBalance | null> {
    const cellHex = hexEncode(toBytea(cell, "cell id"));
    const rows = (await this.rows(
      "SELECT cell, balance, nonce, lifecycle, last_ordinal FROM dregg.cell_balances WHERE cell = $1",
      [cellHex],
    )) as Record<string, unknown>[];
    return rows.length ? rowToCellBalance(rows[0]) : null;
  }

  /**
   * `dregg.receipt_chain` — the turn hash chain in ordinal order. Walk it to
   * verify non-omission: each row's `prevRoot` is the prior row's `ledgerRoot`.
   */
  async receiptChain(opts: { limit?: number } = {}): Promise<ReceiptRow[]> {
    let sql =
      "SELECT ordinal, height, creator, prev_root, ledger_root, committed_at " +
      "FROM dregg.receipt_chain ORDER BY ordinal";
    const params: unknown[] = [];
    if (opts.limit !== undefined) {
      sql += " LIMIT $1";
      params.push(opts.limit);
    }
    const rows = (await this.rows(sql, params)) as Record<string, unknown>[];
    return rows.map(rowToReceipt);
  }

  /** The latest turn in `dregg.receipt_chain` (the chain head), or `null`. */
  async chainHead(): Promise<ReceiptRow | null> {
    const rows = (await this.rows(
      "SELECT ordinal, height, creator, prev_root, ledger_root, committed_at " +
        "FROM dregg.receipt_chain ORDER BY ordinal DESC LIMIT 1",
    )) as Record<string, unknown>[];
    return rows.length ? rowToReceipt(rows[0]) : null;
  }

  /** `dregg.cap_edges` — the delegation graph; with `src`, only edges out of it. */
  async capEdges(opts: { src?: Bytes32 } = {}): Promise<CapEdge[]> {
    let rows: Record<string, unknown>[];
    if (opts.src !== undefined) {
      const srcHex = hexEncode(toBytea(opts.src, "src cell"));
      rows = (await this.rows(
        "SELECT src, dst, slot, permissions, expires_at FROM dregg.cap_edges WHERE src = $1",
        [srcHex],
      )) as Record<string, unknown>[];
    } else {
      rows = (await this.rows(
        "SELECT src, dst, slot, permissions, expires_at FROM dregg.cap_edges",
      )) as Record<string, unknown>[];
    }
    return rows.map(rowToCapEdge);
  }

  /** `SELECT sum(balance) FROM dregg.cells` — value conserved across the ledger. */
  async conservationTotal(): Promise<bigint> {
    const total = await this.scalar("SELECT coalesce(sum(balance), 0) FROM dregg.cells");
    return asBigInt(total);
  }

  // ── the write path: submit a verified turn (the node drains it) ──

  /**
   * Submit a SIGNED turn FROM postgres via `dregg_submit_turn(signed_turn,
   * agent)` (`.docs-history-noclaude/PG-DREGG.md` §11). `signedTurn` is the postcard `SignedTurn`
   * bytes; `agent` is the turn's agent cell id.
   *
   * Enqueues into `dregg.submit_queue` and returns the submission `uuid`. The
   * enqueue is RLS-gated by `dregg_admits('submit', encode(agent,'hex'))` — a
   * role submits only the turns its capability authorizes; otherwise RLS refuses
   * the INSERT (throws {@link DreggPgError}). **Postgres never executes** — the
   * node's §11.4 drainer applies the turn; poll {@link Pg.outbox} /
   * {@link Pg.submission} for the outcome (`status` walks `pending → executed |
   * refused`). `dregg_submit_turn` is NOT `SECURITY DEFINER` — present a `submit`
   * token and assume `dregg_reader` first.
   */
  async submitTurn(signedTurn: Uint8Array, agent: Bytes32): Promise<string> {
    if (!(signedTurn instanceof Uint8Array)) {
      throw new DreggPgError("signedTurn must be the postcard SignedTurn bytes (Uint8Array)");
    }
    const agentB = toBytea(agent, "agent cell");
    try {
      const id = await this.scalar<string>("SELECT dregg_submit_turn($1, $2)", [
        bytea(signedTurn),
        bytea(agentB),
      ]);
      return String(id);
    } catch (err) {
      throw wrapPgError(err, "dregg_submit_turn (enqueue)");
    }
  }

  /**
   * Enqueue a signed turn by a direct `INSERT INTO dregg.submit_queue` (the
   * explicit form `dregg_submit_turn` wraps). Same RLS gate (`submit_gate`).
   */
  async enqueueTurn(signedTurn: Uint8Array, agent: Bytes32): Promise<string> {
    if (!(signedTurn instanceof Uint8Array)) {
      throw new DreggPgError("signedTurn must be the postcard SignedTurn bytes (Uint8Array)");
    }
    const agentB = toBytea(agent, "agent cell");
    try {
      const id = await this.scalar<string>(
        "INSERT INTO dregg.submit_queue (agent, signed_turn) VALUES ($1, $2) RETURNING id",
        [bytea(agentB), bytea(signedTurn)],
      );
      return String(id);
    } catch (err) {
      throw wrapPgError(err, "submit_queue INSERT");
    }
  }

  // ── the outbox tail (view preferred, base table fallback) ──

  /**
   * Tail the submit-queue audit surface — every submission you may see and its
   * outcome, ordered by `id` (= arrival order on pg18, where the key is a
   * `uuidv7`). RLS-gated by the same `submit` admission. Prefers
   * `dregg.submit_queue_audit` (the pg18 view); falls back to the base
   * `dregg.submit_queue` table where the view is absent (older / pg17 installs).
   */
  async outbox(opts: { limit?: number } = {}): Promise<Submission[]> {
    const { relation, cols } = await this.outboxRelation();
    let sql = `SELECT ${cols} FROM ${relation} ORDER BY id`;
    const params: unknown[] = [];
    if (opts.limit !== undefined) {
      sql += " LIMIT $1";
      params.push(opts.limit);
    }
    const rows = (await this.rows(sql, params)) as Record<string, unknown>[];
    return rows.map(rowToSubmission);
  }

  /** One submission by id from the audit surface (poll after {@link Pg.submitTurn}). */
  async submission(id: string): Promise<Submission | null> {
    const { relation, cols } = await this.outboxRelation();
    const rows = (await this.rows(`SELECT ${cols} FROM ${relation} WHERE id = $1`, [
      id,
    ])) as Record<string, unknown>[];
    return rows.length ? rowToSubmission(rows[0]) : null;
  }

  private outboxRelCache: { relation: string; cols: string } | null = null;
  private async outboxRelation(): Promise<{ relation: string; cols: string }> {
    if (this.outboxRelCache) return this.outboxRelCache;
    const base =
      "id, agent, submitter, status, receipt_hash, error, submitted_at, resolved_at";
    const viewPresent = await this.scalar<boolean>(
      "SELECT to_regclass('dregg.submit_queue_audit') IS NOT NULL",
    );
    let result: { relation: string; cols: string };
    if (viewPresent) {
      // The view renders agent + receipt_hash as hex already.
      result = { relation: "dregg.submit_queue_audit", cols: base };
    } else {
      result = {
        relation: "dregg.submit_queue",
        cols:
          "id, encode(agent,'hex') AS agent, submitter, status, " +
          "encode(receipt_hash,'hex') AS receipt_hash, error, submitted_at, resolved_at",
      };
    }
    this.outboxRelCache = result;
    return result;
  }

  // ── federation health ──

  /**
   * `dregg_federation_health()` — the subscriber-side federation health check
   * (`.docs-history-noclaude/PG-DREGG.md` §15): the pg18 apply-conflict counters DRIVE the chain
   * re-validation. Returns the one-line verdict (`'ok: …'` / `'ALARM …'` /
   * `'CRITICAL …'`).
   */
  async federationHealth(): Promise<string> {
    return String(await this.scalar("SELECT dregg_federation_health()"));
  }

  /** `true` iff {@link Pg.federationHealth} reports the healthy verdict. */
  async federationHealthOk(): Promise<boolean> {
    return (await this.federationHealth()).startsWith("ok:");
  }

  /**
   * `dregg_revalidate_replicated_chain()` — the subscriber re-validation sweep
   * over the replicated `dregg.turns` (the anti-substitution tooth, run locally).
   */
  async revalidateReplicatedChain(): Promise<string> {
    return String(await this.scalar("SELECT dregg_revalidate_replicated_chain()"));
  }

  // ── issuer status + dev mint ──

  /**
   * `dregg_issuer_status()` — the database's dregg key configuration in one line,
   * so the silent fail-closed mode ("no issuer key ⇒ everything denies") is
   * discoverable. Run it first when "all my rows vanished". The private key is
   * never reported.
   */
  async issuerStatus(): Promise<string> {
    return String(await this.scalar("SELECT dregg_issuer_status()"));
  }

  /**
   * `dregg_dev_mint(subject, actions[], resource_prefix, ttl interval)` — **DEV
   * ONLY.** Compose the common capability shape (`action ∈ actions` confined to
   * `resourcePrefix`, expiring `ttl` from now, naming `subject`) and mint a
   * `dga1_…` token, so a newcomer never hand-writes `Pred` JSON. Issuer-key
   * discipline is intact: it routes through the same mint path as `dregg_mint`
   * and RAISES (no silent token) if `dregg.issuer_privkey` is not configured.
   * `ttl` is a postgres interval literal (e.g. `"1 hour"`).
   */
  async devMint(
    subject: string,
    actions: string[],
    resourcePrefix: string,
    ttl: Interval,
  ): Promise<string> {
    try {
      const tok = await this.scalar<string>("SELECT dregg_dev_mint($1, $2, $3, $4::interval)", [
        subject,
        actions,
        resourcePrefix,
        ttl,
      ]);
      return String(tok);
    } catch (err) {
      throw wrapPgError(err, "dregg_dev_mint");
    }
  }

  // ── direct capability decisions (the M1 functions, offline-verified) ──

  /** `dregg_cap_admits(token, action, resource, now)` — TRUE iff admitted (fail-closed). */
  async capAdmits(token: string, action: string, resource: string, now?: number): Promise<boolean> {
    const at = now ?? Number(await this.scalar("SELECT extract(epoch from now())::bigint"));
    const v = await this.scalar<boolean>("SELECT dregg_cap_admits($1, $2, $3, $4)", [
      token,
      action,
      resource,
      at,
    ]);
    return Boolean(v);
  }

  /** `dregg_cap_explain(...)` — the human-readable decision reason. */
  async capExplain(
    token: string,
    action: string,
    resource: string,
    now?: number,
  ): Promise<string | null> {
    const at = now ?? Number(await this.scalar("SELECT extract(epoch from now())::bigint"));
    return asStringOrNull(
      await this.scalar("SELECT dregg_cap_explain($1, $2, $3, $4)", [token, action, resource, at]),
    );
  }

  /** `dregg_cap_subject(token)` — the confined subject the token names, or `null`. */
  async capSubject(token: string): Promise<string | null> {
    return asStringOrNull(await this.scalar("SELECT dregg_cap_subject($1)", [token]));
  }

  /** `dregg_revoke(token)` — revoke the credential; returns the revoked id or `null`. */
  async revoke(token: string): Promise<string | null> {
    try {
      return asStringOrNull(await this.scalar("SELECT dregg_revoke($1)", [token]));
    } catch (err) {
      throw wrapPgError(err, "dregg_revoke");
    }
  }

  // ── one-call schema install (the dregg-developer entry points) ──

  /** `dregg_install_schema()` — install the Tier-B store. Idempotent (DBA role). */
  async installSchema(): Promise<string> {
    try {
      return String(await this.scalar("SELECT dregg_install_schema()"));
    } catch (err) {
      throw wrapPgError(err, "dregg_install_schema");
    }
  }

  /** `dregg_install_write_outbox()` — install the write-path outbox. Idempotent. */
  async installWriteOutbox(): Promise<string> {
    try {
      return String(await this.scalar("SELECT dregg_install_write_outbox()"));
    } catch (err) {
      throw wrapPgError(err, "dregg_install_write_outbox");
    }
  }
}

// ── row mappers (snake_case columns → camelCase typed fields) ──

function rowToCellBalance(r: Record<string, unknown>): CellBalance {
  return {
    cell: String(r.cell),
    balance: asBigInt(r.balance),
    nonce: asBigInt(r.nonce),
    lifecycle: String(r.lifecycle),
    lastOrdinal: asBigInt(r.last_ordinal),
  };
}

function rowToReceipt(r: Record<string, unknown>): ReceiptRow {
  return {
    ordinal: asBigInt(r.ordinal),
    height: asBigInt(r.height),
    creator: String(r.creator),
    prevRoot: String(r.prev_root),
    ledgerRoot: String(r.ledger_root),
    committedAt: asDateOrNull(r.committed_at),
  };
}

function rowToCapEdge(r: Record<string, unknown>): CapEdge {
  return {
    src: String(r.src),
    dst: String(r.dst),
    slot: Number(r.slot),
    permissions: r.permissions ?? null,
    expiresAt: asBigIntOrNull(r.expires_at),
  };
}

function rowToSubmission(r: Record<string, unknown>): Submission {
  return {
    id: String(r.id),
    agent: String(r.agent),
    submitter: String(r.submitter),
    status: String(r.status),
    receiptHash: asStringOrNull(r.receipt_hash),
    error: asStringOrNull(r.error),
    submittedAt: asDateOrNull(r.submitted_at),
    resolvedAt: asDateOrNull(r.resolved_at),
  };
}
