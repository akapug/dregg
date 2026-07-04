"""Tests for ``dregg.pg`` — the pg-dregg-native binding.

Two layers:

* **Unit** (always run): the query construction + serialization the helpers
  build, asserted against the REAL ``dregg.*`` view/function shapes from
  ``pg-dregg/src/lib.rs`` + ``sql/schema-tierB.sql`` — via a recording fake
  ``psycopg`` connection that captures every SQL string + params without a
  database. These pin the binding to the real surface (a column-list drift is a
  loud failure).
* **Integration** (``@pytest.mark.pg_integration``, skip-gated): against a live
  pg-dregg-enabled postgres if one is reachable. Swarm-safe — it creates a
  UNIQUELY-NAMED scratch database, installs the extension + schema there, runs
  the genuine read/write helpers, and DROPs it on teardown. Feature-detecting:
  it exercises only the functions/views the installed extension actually ships
  (the live cluster may carry an older build). Clear skip message if no DB.
"""

from __future__ import annotations

import os
import uuid
from datetime import datetime, timedelta

import pytest

from dregg import pg as dpg


# ════════════════════════════ unit: a recording fake ════════════════════════
# A minimal stand-in for psycopg's Connection/Cursor that records the (sql,
# params) the helpers issue and replays canned rows. No database needed.


class FakeCursor:
    def __init__(self, conn: "FakeConn") -> None:
        self._conn = conn
        self._result: list[tuple] = []

    def execute(self, sql, params=()):
        self._conn.calls.append((_norm(sql), tuple(params) if params else ()))
        self._result = self._conn.next_rows_for(_norm(sql))

    def fetchone(self):
        return self._result[0] if self._result else None

    def fetchall(self):
        return list(self._result)

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False


class FakeInfo:
    dbname = "fake"


class FakeConn:
    def __init__(self) -> None:
        self.calls: list[tuple[str, tuple]] = []
        # ``responder`` maps a substring → rows. First match wins; the scalar
        # helpers read row[0]. Defaults cover the clock + GUC reads.
        self.responder: list[tuple[str, list[tuple]]] = []
        self.closed = False
        self.info = FakeInfo()

    def cursor(self):
        return FakeCursor(self)

    def close(self):
        self.closed = True

    def when(self, needle: str, rows: list[tuple]) -> "FakeConn":
        self.responder.append((needle, rows))
        return self

    def next_rows_for(self, sql: str) -> list[tuple]:
        for needle, rows in self.responder:
            if needle in sql:
                return rows
        return []


def _norm(sql) -> str:
    """Collapse whitespace so assertions are insensitive to formatting."""
    return " ".join(str(sql).split())


def pgh(conn: FakeConn) -> dpg.Pg:
    return dpg.Pg(conn)  # type: ignore[arg-type]


def last_sql(conn: FakeConn) -> str:
    return conn.calls[-1][0]


def find_call(conn: FakeConn, needle: str) -> tuple[str, tuple]:
    for sql, params in conn.calls:
        if needle in sql:
            return sql, params
    raise AssertionError(f"no call containing {needle!r}; calls={[c[0] for c in conn.calls]}")


# ── coercion + identifier validation ──


def test_to_bytea_accepts_hex_and_bytes():
    raw = bytes(range(32))
    assert dpg._to_bytea(raw) == raw
    assert dpg._to_bytea(raw.hex()) == raw
    assert dpg._to_bytea("\\x" + raw.hex()) == raw
    assert dpg._to_bytea("0x" + raw.hex()) == raw


def test_to_bytea_rejects_garbage():
    with pytest.raises(ValueError):
        dpg._to_bytea("nothex!!")
    with pytest.raises(TypeError):
        dpg._to_bytea(12345)  # type: ignore[arg-type]


def test_validate_ident_whitelists_role_shape():
    assert dpg._validate_ident("dregg_reader") == "dregg_reader"
    assert dpg._validate_ident("dregg_kernel") == "dregg_kernel"
    for bad in ["", "1abc", "drop table", "a-b", "x;y", "a" * 64]:
        with pytest.raises(ValueError):
            dpg._validate_ident(bad)


# ── presenting authority (GUC + role) ──


def test_present_token_sets_the_dregg_token_guc():
    conn = FakeConn()
    pgh(conn).present_token("dga1_abc")
    sql, params = find_call(conn, "set_config")
    assert params == ("dregg.token", "dga1_abc", False)
    assert dpg.TOKEN_GUC == "dregg.token"


def test_present_token_local_is_transaction_scoped():
    conn = FakeConn()
    pgh(conn).present_token("dga1_xyz", local=True)
    _, params = find_call(conn, "set_config")
    assert params == ("dregg.token", "dga1_xyz", True)


def test_set_role_validates_and_uses_set_config_role():
    conn = FakeConn()
    pgh(conn).set_role("dregg_reader")
    sql, params = find_call(conn, "'role'")
    assert params == ("dregg_reader",)
    with pytest.raises(ValueError):
        pgh(conn).set_role("evil; DROP")


def test_current_token_reads_current_setting_missing_ok():
    conn = FakeConn().when("current_setting", [("dga1_live",)])
    assert pgh(conn).current_token() == "dga1_live"
    _, params = find_call(conn, "current_setting")
    assert params == ("dregg.token",)
    # empty string ⇒ None
    conn2 = FakeConn().when("current_setting", [("",)])
    assert pgh(conn2).current_token() is None


# ── free-SQL reads bind the REAL view column lists ──


def test_cell_balances_binds_the_real_view():
    conn = FakeConn().when(
        "dregg.cell_balances", [("c011" + "0" * 60, 999500, 1, "Active", 3)]
    )
    out = pgh(conn).cell_balances()
    sql = last_sql(conn)
    # Exactly the dregg.cell_balances projection (sql/schema-tierB.sql).
    assert "FROM dregg.cell_balances" in sql
    assert "SELECT cell, balance, nonce, lifecycle, last_ordinal" in sql
    assert "ORDER BY balance DESC" in sql
    assert len(out) == 1
    row = out[0]
    assert isinstance(row, dpg.CellBalance)
    assert row.balance == 999500 and row.nonce == 1 and row.lifecycle == "Active"
    assert row.last_ordinal == 3


def test_cell_balances_limit_is_parameterized():
    conn = FakeConn().when("dregg.cell_balances", [])
    pgh(conn).cell_balances(limit=10)
    sql, params = find_call(conn, "dregg.cell_balances")
    assert "LIMIT %s" in sql and params == (10,)


def test_cell_balance_by_id_filters_on_hex():
    cell = bytes([0xA1] + [0] * 31)
    conn = FakeConn().when("dregg.cell_balances", [(cell.hex(), 400, 2, "Active", 2)])
    row = pgh(conn).cell_balance(cell)
    sql, params = find_call(conn, "dregg.cell_balances")
    assert "WHERE cell = %s" in sql
    assert params == (cell.hex(),)
    assert row is not None and row.balance == 400


def test_receipt_chain_binds_the_real_view_and_orders_by_ordinal():
    now = datetime(2026, 6, 14, 12, 0, 0)
    conn = FakeConn().when(
        "dregg.receipt_chain",
        [(0, 0, "c011", "00" * 32, "3488", now),
         (1, 1, "c011", "3488", "1063", now)],
    )
    out = pgh(conn).receipt_chain()
    sql = last_sql(conn)
    assert "FROM dregg.receipt_chain" in sql
    assert "SELECT ordinal, height, creator, prev_root, ledger_root, committed_at" in sql
    assert "ORDER BY ordinal" in sql
    assert [r.ordinal for r in out] == [0, 1]
    assert all(isinstance(r, dpg.ReceiptRow) for r in out)
    # The chain links: turn N's ledger_root is turn N+1's prev_root.
    assert out[0].ledger_root == out[1].prev_root


def test_chain_head_takes_the_latest_ordinal():
    conn = FakeConn().when("dregg.receipt_chain", [(3, 3, "a111", "5770", "203e", None)])
    head = pgh(conn).chain_head()
    sql = last_sql(conn)
    assert "ORDER BY ordinal DESC LIMIT 1" in sql
    assert head is not None and head.ordinal == 3 and head.ledger_root == "203e"


def test_chain_head_none_on_empty_ledger():
    conn = FakeConn().when("dregg.receipt_chain", [])
    assert pgh(conn).chain_head() is None


def test_cap_edges_binds_the_real_view():
    conn = FakeConn().when(
        "dregg.cap_edges",
        [("a111", "b011", 0, {"transfer": "delegated"}, 10000)],
    )
    out = pgh(conn).cap_edges()
    sql = last_sql(conn)
    assert "FROM dregg.cap_edges" in sql
    assert "SELECT src, dst, slot, permissions, expires_at" in sql
    e = out[0]
    assert isinstance(e, dpg.CapEdge)
    assert e.src == "a111" and e.dst == "b011" and e.slot == 0
    assert e.permissions == {"transfer": "delegated"} and e.expires_at == 10000


def test_cap_edges_src_filter_is_hex_parameterized():
    src = bytes([0xA1] + [0] * 31)
    conn = FakeConn().when("dregg.cap_edges", [])
    pgh(conn).cap_edges(src=src)
    sql, params = find_call(conn, "dregg.cap_edges")
    assert "WHERE src = %s" in sql and params == (src.hex(),)


def test_conservation_total_sums_balances():
    conn = FakeConn().when("sum(balance)", [(1_000_000,)])
    assert pgh(conn).conservation_total() == 1_000_000
    assert "coalesce(sum(balance), 0) FROM dregg.cells" in last_sql(conn)


# ── the write path: submit a verified turn ──


def test_submit_turn_calls_the_real_extern():
    sid = uuid.uuid4()
    conn = FakeConn().when("dregg_submit_turn", [(sid,)])
    agent = bytes([0xA1] + [0] * 31)
    out = pgh(conn).submit_turn(b"\xde\xad\xbe\xef", agent)
    sql, params = find_call(conn, "dregg_submit_turn")
    assert "SELECT dregg_submit_turn(%s, %s)" in sql
    assert params == (b"\xde\xad\xbe\xef", agent)
    assert out == sid


def test_submit_turn_accepts_hex_agent():
    conn = FakeConn().when("dregg_submit_turn", [(uuid.uuid4(),)])
    agent_hex = "a1" + "00" * 31
    pgh(conn).submit_turn(b"\x01\x02", agent_hex)
    _, params = find_call(conn, "dregg_submit_turn")
    assert params[1] == bytes.fromhex(agent_hex)


def test_submit_turn_rejects_non_bytes_turn():
    conn = FakeConn()
    with pytest.raises(TypeError):
        pgh(conn).submit_turn("not-bytes", "a1" + "00" * 31)  # type: ignore[arg-type]


def test_enqueue_turn_uses_the_raw_insert_path():
    sid = uuid.uuid4()
    conn = FakeConn().when("INSERT INTO dregg.submit_queue", [(sid,)])
    agent = bytes([0xB0] + [0] * 31)
    out = pgh(conn).enqueue_turn(b"\x00\x01", agent)
    sql, params = find_call(conn, "INSERT INTO dregg.submit_queue")
    assert "INSERT INTO dregg.submit_queue (agent, signed_turn) VALUES (%s, %s) RETURNING id" in sql
    assert params == (agent, b"\x00\x01")
    assert out == sid


def test_submit_turn_rls_refusal_is_wrapped_legibly():
    class RLSError(Exception):
        pass

    conn = FakeConn()

    def boom(sql, params=()):
        if "dregg_submit_turn" in _norm(sql):
            raise RLSError(
                'new row violates row-level security policy for table "submit_queue"'
            )
        conn.calls.append((_norm(sql), tuple(params)))

    cur = conn.cursor()
    cur.execute = boom  # type: ignore[method-assign]
    conn.cursor = lambda: cur  # type: ignore[method-assign]

    with pytest.raises(dpg.DreggPgError) as exc:
        pgh(conn).submit_turn(b"\x01", bytes(32))
    msg = str(exc.value)
    assert "Row-Level Security" in msg
    assert "does not authorize" in msg


# ── the outbox tail (view preferred, base table fallback) ──


def test_outbox_prefers_the_audit_view_with_v7_columns():
    sid = uuid.uuid4()
    enq = datetime(2026, 6, 14, 12, 0, 0)
    conn = (
        FakeConn()
        .when("to_regclass('dregg.submit_queue_audit') IS NOT NULL", [(True,)])
        .when("column_name='id_version'", [(1,)])
        .when(
            "FROM dregg.submit_queue_audit",
            [(sid, "a1", "app", "executed", "ee" * 32, None, enq, enq, 7, enq, timedelta(seconds=1))],
        )
    )
    out = pgh(conn).outbox()
    sql, _ = find_call(conn, "FROM dregg.submit_queue_audit ORDER BY id")
    assert "id, agent, submitter, status, receipt_hash, error, submitted_at, resolved_at" in sql
    assert "id_version, enqueued_at, queue_latency" in sql
    s = out[0]
    assert isinstance(s, dpg.Submission)
    assert s.status == "executed" and s.executed and not s.pending
    assert s.id_version == 7 and s.receipt_hash == "ee" * 32


def test_outbox_falls_back_to_base_table_when_view_absent():
    sid = uuid.uuid4()
    conn = (
        FakeConn()
        .when("to_regclass('dregg.submit_queue_audit') IS NOT NULL", [(False,)])
        .when(
            "FROM dregg.submit_queue",
            [(sid, "b0", "app", "pending", None, None, None, None)],
        )
    )
    out = pgh(conn).outbox()
    sql, _ = find_call(conn, "FROM dregg.submit_queue ORDER BY id")
    # The base-table fallback renders agent + receipt_hash as hex.
    assert "encode(agent,'hex') AS agent" in sql
    assert "encode(receipt_hash,'hex') AS receipt_hash" in sql
    s = out[0]
    assert s.status == "pending" and s.pending
    assert s.id_version is None and s.enqueued_at is None


# ── federation health / issuer status / dev mint bind the real functions ──


def test_federation_health_binds_the_function_and_parses_ok():
    conn = FakeConn().when(
        "dregg_federation_health",
        [("ok: federation healthy — 1 subscription(s), 0 apply conflicts",)],
    )
    pg = pgh(conn)
    assert pg.federation_health().startswith("ok:")
    assert "SELECT dregg_federation_health()" in find_call(conn, "dregg_federation_health")[0]
    # federation_health_ok re-reads the function and classifies the verdict.
    assert pg.federation_health_ok() is True

    conn2 = FakeConn().when(
        "dregg_federation_health",
        [("CRITICAL (2 apply conflict(s)) AND chain REFUSED: root does not chain",)],
    )
    assert pgh(conn2).federation_health_ok() is False


def test_issuer_status_binds_the_function():
    conn = FakeConn().when("dregg_issuer_status", [("verify key CONFIGURED (id ab…)",)])
    out = pgh(conn).issuer_status()
    assert "CONFIGURED" in out
    assert "SELECT dregg_issuer_status()" in find_call(conn, "dregg_issuer_status")[0]


def test_dev_mint_with_timedelta_passes_interval_param():
    conn = FakeConn().when("dregg_dev_mint", [("dga1_minted",)])
    out = pgh(conn).dev_mint("alice", ["read", "write"], "org/42/", timedelta(hours=1))
    sql, params = find_call(conn, "dregg_dev_mint")
    assert "SELECT dregg_dev_mint(%s, %s, %s, %s)" in sql
    assert params[0] == "alice"
    assert params[1] == ["read", "write"]  # text[] — psycopg adapts the list
    assert params[2] == "org/42/"
    assert isinstance(params[3], timedelta)
    assert out == "dga1_minted"


def test_dev_mint_with_string_ttl_casts_interval_literal():
    conn = FakeConn().when("dregg_dev_mint", [("dga1_minted2",)])
    pgh(conn).dev_mint("bob", ["submit"], "b0", "5 min")
    sql, params = find_call(conn, "dregg_dev_mint")
    assert "%s::interval" in sql
    assert params == ("bob", ["submit"], "b0", "5 min")


def test_cap_admits_defaults_now_to_db_clock():
    conn = (
        FakeConn()
        .when("extract(epoch from now())", [(1_700_000_000,)])
        .when("dregg_cap_admits", [(True,)])
    )
    assert pgh(conn).cap_admits("dga1_x", "read", "org/42/doc") is True
    _, params = find_call(conn, "dregg_cap_admits")
    assert params == ("dga1_x", "read", "org/42/doc", 1_700_000_000)


def test_cap_explain_and_subject_bind_their_functions():
    conn = (
        FakeConn()
        .when("extract(epoch from now())", [(1,)])
        .when("dregg_cap_explain", [("allowed",)])
        .when("dregg_cap_subject", [("agent-1",)])
    )
    pg = pgh(conn)
    assert pg.cap_explain("dga1", "read", "r", now=1) == "allowed"
    assert pg.cap_subject("dga1") == "agent-1"


def test_revoke_binds_the_function():
    conn = FakeConn().when("dregg_revoke", [("capid123",)])
    assert pgh(conn).revoke("dga1") == "capid123"
    assert "SELECT dregg_revoke(%s)" in find_call(conn, "dregg_revoke")[0]


def test_install_helpers_bind_the_externs():
    conn = (
        FakeConn()
        .when("dregg_install_schema", [("dregg Tier-B store installed: 4 tables",)])
        .when("dregg_install_write_outbox", [("dregg write outbox installed",)])
    )
    pg = pgh(conn)
    assert "Tier-B store installed" in pg.install_schema()
    assert "write outbox installed" in pg.install_write_outbox()


# ── context manager closes the connection ──


def test_context_manager_closes():
    conn = FakeConn()
    with pgh(conn) as pg:
        assert pg.connection is conn
    assert conn.closed is True


def test_missing_psycopg_message_is_actionable(monkeypatch):
    import builtins

    real_import = builtins.__import__

    def no_psycopg(name, *a, **k):
        if name == "psycopg":
            raise ModuleNotFoundError("No module named 'psycopg'")
        return real_import(name, *a, **k)

    monkeypatch.setattr(builtins, "__import__", no_psycopg)
    with pytest.raises(dpg.DreggPgError) as exc:
        dpg._import_psycopg()
    assert "psycopg" in str(exc.value) and "pip install" in str(exc.value)


# ═══════════════════════════ integration (skip-gated) ═══════════════════════
# Against a live pg-dregg-enabled postgres if one is reachable. Swarm-safe:
# creates a uniquely-named scratch DB, installs the surface, runs the genuine
# helpers, DROPs it. Feature-detecting: the live cluster may carry an older
# extension build, so each newer function/view is probed before use.

PGRX_SOCK = os.path.expanduser("~/.pgrx")
# The test issuer root is RootKey::from_seed([7;32]); this is its public key
# (the same one e2e-live.sh configures). dregg_dev_mint needs the PRIVATE seed,
# which we set as the superuser-only GUC in the scratch DB to exercise minting.
ISSUER_PUBKEY = "ea4a6c63e29c520abef5507b132ec5f9954776aebebe7b92421eea691446d22c"
ISSUER_PRIVKEY = "07" * 32  # RootKey::from_seed([7;32]) seed


def _admin_dsn() -> str | None:
    """A libpq DSN to the ``postgres`` maintenance DB on a reachable
    pg-dregg-enabled cluster, or ``None`` if none is found. Honors
    ``$DREGG_PG_ADMIN_DSN`` / ``$DREGG_PG_DSN``; otherwise probes the usual
    cargo-pgrx endpoints — pg18 on TCP ``127.0.0.1:28818`` (pgrx starts pg18
    without a custom socket dir) and pg17 on the pgrx Unix socket :28817 —
    preferring the higher version. Each candidate must have ``pg_dregg``
    available, else it is not the cluster we want."""
    explicit = os.environ.get("DREGG_PG_ADMIN_DSN") or os.environ.get("DREGG_PG_DSN")
    if explicit:
        return explicit
    try:
        import psycopg
    except ModuleNotFoundError:
        return None
    candidates = [
        f"host=127.0.0.1 port=28818 dbname=postgres",   # pgrx pg18 (TCP)
        f"host={PGRX_SOCK} port=28818 dbname=postgres",  # pgrx pg18 (socket, if configured)
        f"host={PGRX_SOCK} port=28817 dbname=postgres",  # pgrx pg17 (socket)
        f"host=127.0.0.1 port=28817 dbname=postgres",    # pgrx pg17 (TCP, if enabled)
    ]
    for dsn in candidates:
        try:
            with psycopg.connect(dsn, connect_timeout=2) as c:
                with c.cursor() as cur:
                    cur.execute(
                        "SELECT count(*) FROM pg_available_extensions WHERE name='pg_dregg'"
                    )
                    if (cur.fetchone() or [0])[0] >= 1:
                        return dsn
        except Exception:
            continue
    return None


@pytest.fixture(scope="module")
def live_db():
    """Create a uniquely-named scratch database with pg_dregg + the Tier-B schema
    installed, yield a DSN to it, and DROP it on teardown. Skips the whole module
    if no pg-dregg cluster is reachable."""
    admin = _admin_dsn()
    if admin is None:
        pytest.skip(
            "no pg-dregg-enabled postgres reachable "
            "(set $DREGG_PG_DSN or start the cargo-pgrx cluster; "
            "looked for the pgrx socket on :28818/:28817 with pg_dregg available)"
        )
    import psycopg

    dbname = f"dregg_sdkpg_{uuid.uuid4().hex[:16]}"
    # CREATE/DROP DATABASE cannot run inside a transaction block.
    with psycopg.connect(admin, autocommit=True) as c:
        c.execute(f'CREATE DATABASE "{dbname}"')
    # Build the scratch DB's DSN by swapping dbname.
    db_dsn = _swap_dbname(admin, dbname)
    try:
        # The issuer VERIFY key (dregg.issuer_pubkey) is a Sighup GUC — it cannot
        # be set per-database (only via ALTER SYSTEM + reload, which is NOT
        # swarm-safe on a shared cluster). We INHERIT it: the dev cluster is
        # already configured cluster-wide (the e2e harness ran ALTER SYSTEM), so
        # the scratch DB sees the test root. The PRIVATE key (Suset) we set
        # per-database so dregg_dev_mint can mint tokens that verify under the
        # inherited public key (RootKey::from_seed([7;32]) — pub/priv pair).
        with psycopg.connect(admin, autocommit=True) as c:
            c.execute(f"ALTER DATABASE \"{dbname}\" SET dregg.issuer_privkey = '{ISSUER_PRIVKEY}'")
        with psycopg.connect(db_dsn, autocommit=True) as c:
            c.execute("CREATE EXTENSION IF NOT EXISTS pg_dregg")
        # Reconnect so the per-db GUC applies, then install the schema + outbox.
        with psycopg.connect(db_dsn, autocommit=True) as c:
            c.execute("SELECT dregg_install_schema()")
            c.execute("SELECT dregg_install_write_outbox()")
        yield db_dsn
    finally:
        with psycopg.connect(admin, autocommit=True) as c:
            # Terminate stragglers, then drop.
            c.execute(
                "SELECT pg_terminate_backend(pid) FROM pg_stat_activity "
                "WHERE datname = %s AND pid <> pg_backend_pid()",
                (dbname,),
            )
            c.execute(f'DROP DATABASE IF EXISTS "{dbname}"')


def _swap_dbname(dsn: str, dbname: str) -> str:
    """Return ``dsn`` with its ``dbname`` replaced (keyword DSNs only; the pgrx
    probe always builds a keyword DSN)."""
    parts = [p for p in dsn.split() if not p.startswith("dbname=")]
    parts.append(f"dbname={dbname}")
    return " ".join(parts)


def _has_function(pg: dpg.Pg, signature: str) -> bool:
    return bool(pg._scalar(f"SELECT to_regprocedure('{signature}') IS NOT NULL"))


def _verify_key_is_test_root(pg: dpg.Pg) -> bool:
    """True iff the cluster's configured ``dregg.issuer_pubkey`` is the test root
    (``RootKey::from_seed([7;32])``) — i.e. tokens minted with our seed verify.
    The verify key is a Sighup GUC inherited cluster-wide; on a clean machine it
    is absent and the crypto-dependent assertions must skip rather than fail."""
    configured = pg._scalar("SELECT current_setting('dregg.issuer_pubkey', true)")
    return configured == ISSUER_PUBKEY


@pytest.mark.pg_integration
def test_live_connect_and_read_empty_views(live_db):
    """The free-SQL read helpers resolve against the real shipped views (empty on
    a fresh store) — the binding's column lists match what pg-dregg ships."""
    with dpg.connect(live_db, role=None) as pg:
        assert pg.cell_balances() == []
        assert pg.receipt_chain() == []
        assert pg.cap_edges() == []
        assert pg.chain_head() is None
        assert pg.conservation_total() == 0


@pytest.mark.pg_integration
def test_live_issuer_status_and_dev_mint_roundtrip(live_db):
    """``dregg_issuer_status`` + ``dregg_dev_mint`` + ``dregg_cap_admits`` form a
    real loop: mint a dev token, and the admit path accepts exactly its shape.
    Each newer function is feature-detected (older installs skip it)."""
    with dpg.connect(live_db, role=None) as pg:
        if not _has_function(pg, "dregg_dev_mint(text, text[], text, interval)"):
            pytest.skip("installed pg_dregg predates dregg_dev_mint")
        if not _verify_key_is_test_root(pg):
            pytest.skip("cluster's dregg.issuer_pubkey is not the test root (set it cluster-wide to run)")
        if _has_function(pg, "dregg_issuer_status()"):
            status = pg.issuer_status()
            assert "CONFIGURED" in status  # the cluster's inherited verify key

        tok = pg.dev_mint("alice", ["read"], "org/42/", timedelta(hours=1))
        assert tok.startswith("dga1_")
        # The minted token admits read under its prefix, denies outside it.
        assert pg.cap_admits(tok, "read", "org/42/public/doc1") is True
        assert pg.cap_admits(tok, "read", "org/99/x") is False
        assert pg.cap_admits(tok, "delete", "org/42/public/doc1") is False
        assert pg.cap_subject(tok) == "alice"
        assert pg.cap_explain(tok, "read", "org/42/public/doc1") == "allowed"


@pytest.mark.pg_integration
def test_live_federation_health_on_a_publisher(live_db):
    """``dregg_federation_health`` on a single node (no subscriptions) reports the
    healthy verdict. Feature-detected (newer externs). The health check reads
    ``dregg.replication_conflicts``, which ``dregg_install_federation()`` creates
    (db-scoped — the publication + its conflict view live in this scratch DB and
    are dropped with it), so we install federation first."""
    import psycopg

    with dpg.connect(live_db, role=None) as pg:
        if not _has_function(pg, "dregg_federation_health()"):
            pytest.skip("installed pg_dregg predates dregg_federation_health")
        if not _has_function(pg, "dregg_install_federation()"):
            pytest.skip("installed pg_dregg predates dregg_install_federation")
        # Install the federation publication + the replication-conflicts view the
        # health check reads (database-scoped; cleaned up by DROP DATABASE).
        with psycopg.connect(live_db, autocommit=True) as c:
            c.execute("SELECT dregg_install_federation()")
        verdict = pg.federation_health()
        # A publisher with no subscriptions is healthy (0 apply conflicts).
        assert verdict.startswith("ok:"), verdict
        assert pg.federation_health_ok() is True


@pytest.mark.pg_integration
def test_live_submit_turn_is_rls_gated(live_db):
    """The write path through real RLS: present a ``submit`` token for ALICE, and
    submitting FOR ALICE enqueues while submitting FOR BOB is refused by
    Row-Level Security (a role submits only what its caps authorize). Read the
    outbox back to see the pending row."""
    import psycopg

    alice = bytes([0xA1] + [0] * 31)
    bob = bytes([0xB0] + [0] * 31)
    with dpg.connect(live_db, role=None) as minter:
        if not _has_function(minter, "dregg_dev_mint(text, text[], text, interval)"):
            pytest.skip("installed pg_dregg predates dregg_dev_mint")
        if not _verify_key_is_test_root(minter):
            pytest.skip("cluster's dregg.issuer_pubkey is not the test root")
        # Mint an ALICE-only submit token (resource prefix = ALICE's hex).
        tok = minter.dev_mint("alice-agent", ["submit"], alice.hex(), timedelta(minutes=5))

    # Present the token and become dregg_reader so submit_gate bites.
    with dpg.connect(live_db, token=tok, role="dregg_reader") as pg:
        sid = pg.submit_turn(b"\xde\xad\xbe\xef", alice)
        assert sid is not None

        # The outbox shows the pending submission for ALICE.
        subs = pg.outbox()
        assert any(s.agent == alice.hex() and s.pending for s in subs)
        one = pg.submission(sid)
        assert one is not None and one.agent == alice.hex()

        # Submitting FOR BOB under the ALICE-only token is RLS-refused.
        with pytest.raises(dpg.DreggPgError) as exc:
            pg.submit_turn(b"\xde\xad\xbe\xef", bob)
        assert "Row-Level Security" in str(exc.value)


@pytest.mark.pg_integration
def test_live_rls_narrows_cell_visibility(live_db):
    """The no-amplification property through real Tier-B RLS: as the kernel writer
    seed one cell + its turn, then a wide-open token sees it and an unrelated-prefix
    token does not. Uses the kernel role to materialize (the only writer)."""
    import psycopg

    cell = bytes([0xA1] + [0] * 31)
    with psycopg.connect(live_db, autocommit=True) as c:
        c.execute("SET ROLE dregg_kernel")
        # A turns row (FK target), then the cell via the shipped MERGE applicator.
        c.execute(
            "INSERT INTO dregg.turns(ordinal,height,block_id,block_executed_up_to,"
            "turn_hash,creator,receipt_hash,ledger_root,prev_root) VALUES "
            "(0,0,%s,0,%s,%s,%s,%s,%s)",
            (b"\x22", b"\x33", cell, b"\x44", b"\x11", b"\x00"),
        )
        c.execute(
            "SELECT dregg.merge_cell(%s,'Hosted',1000,0,%s,%s::jsonb,'Active',0,%s)",
            (cell, b"", '{"balance":1000,"nonce":0}', cell),
        )

    with dpg.connect(live_db, role=None) as minter:
        if not _has_function(minter, "dregg_dev_mint(text, text[], text, interval)"):
            pytest.skip("installed pg_dregg predates dregg_dev_mint")
        if not _verify_key_is_test_root(minter):
            pytest.skip("cluster's dregg.issuer_pubkey is not the test root")
        wide = minter.dev_mint("op", ["read"], "", timedelta(hours=1))      # all resources
        narrow = minter.dev_mint("op", ["read"], "ff", timedelta(hours=1))  # an unrelated prefix

    with dpg.connect(live_db, token=wide, role="dregg_reader") as pg:
        seen = {c.cell for c in pg.cell_balances()}
        assert cell.hex() in seen, "the wide-open token sees the seeded cell"
    with dpg.connect(live_db, token=narrow, role="dregg_reader") as pg:
        seen = {c.cell for c in pg.cell_balances()}
        assert cell.hex() not in seen, "the unrelated-prefix token is narrowed away"
