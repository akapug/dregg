# deos dev environment: a live local node + the cockpit attached to it

This is the working environment for developing on dregg: a real `dregg-node`
running locally with the verified **lean** state producer, and the deos cockpit
(`starbridge-v2`) attached to it so its receipt feed and federation/cell views
reflect that live node alongside the embedded image.

Nothing here is a demo or a mock. The node commits real verified turns; the
cockpit reads the node's real `/status`, `/api/cells`, `/api/receipts`, and the
SSE `/api/events/stream` receipt push.

## 1. Build

```sh
cargo build -p dregg-node
```

The node links the verified Lean kernel (`libdregg_lean.a`). If the metatheory
working tree has an in-progress proof regression (a module that fails its
`#assert_axioms` hygiene gate, so `lake build Dregg2.Exec.FFI` exits non-zero),
the FFI build script (`dregg-lean-ffi/build.rs`) now detects the failed Lean
build, restores the git-tracked consistent seed archive, and links that — instead
of splicing a torn partial set whose cross-module specializations don't resolve.
So the node builds and runs even while a proof lane is mid-flight. To pick up
fresh Lean changes in the kernel, make `lake build Dregg2.Exec.FFI` green in
`metatheory/` first, then rebuild.

## 2. Stand up the node

```sh
# fresh data dir (idempotent: init skips if the dir already exists)
./target/debug/dregg-node init --data-dir /tmp/deos-node

# run with the devnet faucet on port 8771
./target/debug/dregg-node run --data-dir /tmp/deos-node --enable-faucet --port 8771
```

The first `run` against a fresh data dir does a one-time devnet backfill
(materializes the `alice` agent key + a few starbridge factory cells), then binds
the HTTP API. Wait for:

```
INFO dregg_node: HTTP API listening addr=127.0.0.1:8771
```

(~15–20s on a fresh dir; near-instant afterward.) Until that line, `/status`
will refuse the connection — the node is still seeding.

### Confirm the lean producer is live

```sh
curl -s http://127.0.0.1:8771/status | python3 -m json.tool
```

```json
{
    "healthy": false,
    "peer_count": 0,
    "latest_height": 0,
    "consensus_live": true,
    "federation_mode": "solo",
    "state_producer": "lean",
    "lean_producer": true,
    "full_turn_proving": false,
    "producer_covered_effects": 21
}
```

`state_producer: "lean"` + `lean_producer: true` is the verified producer.
`healthy: false` is just `peer_count == 0` (n=1 solo devnet) — expected. Add
`--prove-turns` (or `DREGG_PROVE_TURNS=1`) to flip `full_turn_proving` on (every
committed turn carries a full-turn STARK; off by default since it is on the hot
path).

### Faucet a cell and read it back

The faucet recipient is `CellId::derive_raw(public_key, blake3("default"))`. With
`public_key` set, the node materializes a real hosted cell (not a stub):

```sh
curl -s -X POST http://127.0.0.1:8771/api/faucet \
  -H 'Content-Type: application/json' \
  -d '{"recipient":"<derived-cell-id-hex>","amount":5000,"public_key":"<pubkey-hex>"}'
# -> {"success":true,"turn_hash":"9696a1ad…","amount":5000,…}

curl -s http://127.0.0.1:8771/api/cell/<derived-cell-id-hex> | python3 -m json.tool
# -> {"found":true,"balance":5000,"public_key":"…","state_commitment":"…",…}
```

The faucet commits a real verified turn; its receipt appears in the feed
(`pre_state → post_state`, `has_proof:true`, `executor_signed:true`,
`has_witness:true`):

```sh
curl -s "http://127.0.0.1:8771/api/receipts?limit=5" | python3 -m json.tool
```

The same receipt is pushed over the SSE stream (replay from the start with
`Last-Event-ID: 0`):

```sh
curl -sN -H 'Last-Event-ID: 0' http://127.0.0.1:8771/api/events/stream
# event: receipt
# id: 1
# data: {"chain_index":1,"turn_hash":"…","has_proof":true,…}
```

A fresh SSE connection without `Last-Event-ID` tails from the current head — it
only emits receipts committed *after* you connect, so trigger a turn to see it
push. This is exactly what the cockpit's live pump consumes.

## 3. Boot deos against the node

```sh
cd starbridge-v2
cargo run --features native-full --bin starbridge-v2 -- --node http://localhost:8771
```

(`--node=http://localhost:8771` also works.) deos boots into the login ceremony;
pick an identity and the cockpit comes up over the embedded verified image AND
attached to the live node. The attach (`starbridge-v2/src/main.rs` →
`login::LoginSurface::boot` → `Cockpit::with_node`) does, on connect:

* `LiveNode::sync()` — one blocking snapshot of `/status` + `/api/cells` +
  `/api/receipts`, projected into the cockpit's live reflections (the live-node
  panel / federation view).
* `LiveNode::connect_stream()` — opens the SSE `/api/events/stream`; a background
  reader feeds the pure parser and the cockpit's `pump_live` drains it each frame,
  so the receipt feed advances LIVE on every turn the node commits.

An unreachable node is non-fatal: the embedded image stays fully usable, the live
panels just show no node state.

## One-liner to bring it all up

```sh
cargo build -p dregg-node && \
./target/debug/dregg-node init --data-dir /tmp/deos-node ; \
./target/debug/dregg-node run --data-dir /tmp/deos-node --enable-faucet --port 8771 &
# wait for "HTTP API listening", then:
( cd starbridge-v2 && cargo run --features native-full --bin starbridge-v2 -- --node http://localhost:8771 )
```
