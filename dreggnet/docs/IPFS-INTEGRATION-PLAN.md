# IPFS integration for DreggNet

**Status:** design + working prototype (`dregg-ipfs` crate, green over `MockIpfs`;
the real Kubo client compiles). Running a live daemon / pinning service / public
gateway is reviewed-go (ops).

> "ipfs integration seems natural?" — it is, and the reason is one fact: **IPFS CIDs
> carry a blake3 multihash.** DreggNet already content-addresses everything it stores
> and serves; a dregg blake3 content commitment, re-encoded as a CIDv1, simply *is*
> the content's IPFS address. No bridge hashing, no second identity to keep in sync.

---

## 1. The CID alignment

A CIDv1 is `multibase( varint(version) ‖ varint(codec) ‖ multihash )` where
`multihash = varint(hash-code) ‖ varint(len) ‖ digest`. For a blake3 digest:

```
  dregg blake3 commitment            IPFS CIDv1 (raw codec, blake3 multihash)
  ───────────────────────            ────────────────────────────────────────
  d = blake3(bytes)   (32 B)   ⇄     0x01 0x55 0x1e 0x20 ‖ d
                                      │    │    │    └ digest length = 32
                                      │    │    └ multihash code: blake3 = 0x1e
                                      │    └ multicodec: raw = 0x55
                                      └ CID version = 1
                                      (multibase base32-lower, prefix `b`  →  "bafk…")
```

The digest the CID wraps is *exactly* the dregg blake3 commitment — re-encoding adds
the multiformats framing, it does not re-hash. This is implemented in
[`dregg_ipfs::Cid`](../dregg-ipfs/src/cid.rs):

- `Cid::raw_blake3(bytes)` — a blob's CID = `raw(blake3(blob))`.
- `Cid::from_blake3_digest(codec, digest)` — wrap an **already-computed** dregg
  commitment (e.g. a `dregg-merge` `Delta::id`) with no re-hash.
- `Cid::to_string_cid()` / `Cid::parse()` — the `bafk…` form a gateway URL carries.

### Identical (one raw blob) vs chunked (a DAG)

- **Identical — the clean case the bridge targets.** Pin a whole blob as one **raw**
  block. The CID *equals* `blake3(blob)`, so a fetcher recomputes `blake3(fetched)`
  and compares — content-addressing, intrinsic to IPFS, no dregg machinery needed.
  ([`fetch_verified`](../dregg-ipfs/src/bridge.rs)).
- **Chunked.** Above the chunk threshold IPFS splits a file into a UnixFS/dag-pb DAG;
  the root CID is a `dag-pb` hash *over the chunk links*, **not** `blake3(file)`. The
  flat re-hash no longer applies. The bridge handles this by committing the **DAG root
  CID** the daemon returned directly in the cell, and verifying a fetch by re-pinning
  through the same chunker (deterministic for a fixed chunker config) rather than a
  flat re-hash. `fetch_verified` refuses a non-raw CID
  (`IpfsError::NotVerifiableByFlatHash`) rather than silently trusting it.

**The bridge default keeps blobs whole** (`raw-leaves=true`, one block per object/
asset) so the clean `CID == content_root` identity holds. Chunking is opt-in for
genuinely large objects, and then the committed-DAG-root path is used.

### Two commitments, kept distinct (important)

DreggNet's in-process cell commitment (`hosting::content_root`,
`storage::bucket::content_root`) is an **FNV-1a stand-in** for the dregg node's
Poseidon2 umem heap root — it binds objects into the cell Merkle root for the
trustless `verify_opening` / `verify_site_bundle` read. It is **not** the CID and is
not collision-resistant (documented as such at its definition). The IPFS CID is a
**separate, cryptographic** content address (blake3) over the *raw bytes*. The bridge
does not conflate them; it commits the CID **into** the cell (so the FNV/Poseidon2
heap root binds the CID), giving the two-layer verify in §2. Where a dregg commitment
is *already* blake3 (`dregg-merge` deltas, the kernel receipt hash), the CID and the
commitment are literally the same 32 bytes (§3.3).

---

## 2. Storage / hosting backing — decentralized verify-don't-trust hosting

```
  publish/put (cap-gated, receipted turn)        read (from ANY node, no trust)
  ───────────────────────────────────────        ──────────────────────────────
  bytes ──pin_blob──▶ IPFS  ⇒  CID                CID ──any node/gateway──▶ bytes
   │                                                │
   └ commit CID in the cell  ───────────────┐       ├─(1) content-address: blake3(bytes)==CID
     (bound into content_root + the           │      │        a flipped byte → REFUSED
      owner-signed Publish/Put receipt)        └──────┴─(2) the dregg receipt: the cell
                                                         commits this CID, owner-signed
                                                         a wrong/forged CID → REFUSED
```

`BucketRegistry`/site-publish pins object/asset bytes on IPFS and stores the returned
CID in the cell. The bytes are then served from **any** IPFS node or public gateway,
not only the DreggNet edge. A visitor re-witnesses with **no trust in the node it
fetched from**, by two composing checks:

1. **content-addressing** — the fetched bytes must hash to the CID
   ([`fetch_verified`]); a node that flips a byte moves the hash and is refused. This
   is intrinsic to IPFS.
2. **the dregg receipt** — the cell commits the CID (bound into `content_root` and the
   prev-hash-chained, ed25519-signed `PublishReceipt`/`PutReceipt`), so the reader
   checks the CID it fetched under is the one the **owner** committed, via the existing
   trustless reads (`dreggnet_webapp::verify_site_bundle`,
   `dreggnet_storage::verify_opening`). A wrong or re-signed CID is caught by the
   owner-key pin.

Together: *which* bytes (the CID) **and** *whose/authorized* bytes (the owner-signed
cell). IPFS supplies a decentralized any-node transport; dregg adds the authorized,
receipted, cap-gated commitment.

**Contrast Fleek** (git → IPFS/Filecoin, trust the pin/gateway): Fleek's IPFS verifies
*storage* — that some bytes have a CID — but not the *served operation*. It has no
operation receipt, no cap-gate, no verifiable owner-signed cell. DreggNet keeps the
content-addressing **and** adds the receipt + cap + verifiable cell over the same
decentralized transport. (This is exactly the "verify the operated result, not just
the storage" line in `docs/VISION.md` / the `LIFTOFF-SURPASS-MATRIX.md` Fleek row.)

### The bridge points (named follow-up, surgical)

The prototype proves the fit without mutating the `storage`/`webapp` crates (a
parallel lane owns them). The wiring follow-up is one field + one call each:

- `storage`: add an optional `ipfs_cid: Option<String>` to `Object` (or a per-key CID
  side-map in `BucketCell`); in `BucketRegistry::put`, after the bytes are accepted,
  `pin_blob(client, &bytes)` and record the CID (it is then bound by `recommit()` into
  `content_root` and the `PutReceipt`). `verified_get` already opens the object against
  the root; the CID rides along.
- `webapp::hosting`: same shape on `Asset`/`SiteCell`; `publish` pins each asset and
  the `content_root`/`PublishReceipt` bind the CIDs. The serve path can 302 to a
  gateway by CID, or proxy-and-verify.
- the client is injected at the registry boundary (`SiteRegistry::with_ipfs(client)`),
  the same way `with_bandwidth` / `signed` are attached — keeping the core net-free.

---

## 3. The merge-runtime transport

`dregg-merge` (breadstuffs) is DreggNet's I-confluent offchain write runtime: deltas
are a **content-addressed grow-set** (the rhizomatic Merkle-CRDT shape), each delta's
identity is its 32-byte **blake3** `content_id`, and a retraction pins its target by
content address (a Merkle link). This is the textbook case for IPFS as transport:

- **Distribution.** A grow-set of content-addressed deltas is exactly what IPFS
  distributes well — fetch a delta by its CID from any peer, dedup by CID (a G-Set
  union is idempotent, so re-fetching is free), and a retraction's `target` Merkle
  link is a CID that resolves to the delta it retracts.
- **The cleanest alignment in the system.** A delta's blake3 `content_id` IS its IPFS
  address — `delta_cid(id)` wraps it (default `dag-cbor` codec) with the *same 32
  bytes*. Fetch-by-CID then recompute `Delta::id` re-witnesses the delta with no
  separate hash. ([`dregg_ipfs::delta_cid`](../dregg-ipfs/src/bridge.rs)).
- **Offchain coordination.** Two parties accumulate deltas on their own cell copies
  with no coordination, exchange the delta sets over IPFS (publish your grow-set's
  CIDs; pull the peer's), then merge locally — the `MergeRuntime` confluence gate
  decides free-merge vs settle-at-boundary. IPFS is the gossip/exchange layer; the
  `MergeReceipt` (over the read face's MMR) remains the verifiable trace. No chain op
  per merge, no consensus on the transport.

This needs no change to `dregg-merge`: its ids are already the CIDs. The bridge is the
`delta_cid` adapter plus an `IpfsClient` for put/get of delta payloads.

---

## 4. The IPFS client choice

**Recommendation: an injected transport seam, real client = Kubo HTTP RPC over an
injected HTTP, default deployment = a local/remote `ipfs` (Kubo) daemon.** This
matches how the bridge already injects its `dregg_verify` RPCs and keeps the verified
core net-free.

| option | what it is | verdict |
|---|---|---|
| **Kubo HTTP API** (`/api/v0/*`) | talk to a real `ipfs` daemon over HTTP | **chosen** — ubiquitous, language-agnostic, the daemon owns pinning/GC/peering (ops, not our code); plain HTTP on `127.0.0.1:5001`, no TLS for a local daemon |
| embedded `iroh` / `rust-ipfs` / `beetle` | an in-process IPFS node in the binary | rejected for the core — pulls a large async/libp2p closure into a crate that must stay light + portable; revisit only if a daemon-free single binary is wanted |

So the seam is [`IpfsClient`](../dregg-ipfs/src/client.rs): `put_raw` (pin → CID),
`get` (fetch by CID), `pin`. Three impls cross it:

- `MockIpfs` — in-process content-addressed store; the whole bridge round-trip +
  tamper-refusal runs in `cargo test`, no network.
- `KuboClient<H: HttpPost>` — the **real** client: a pure Kubo-RPC *formatter*
  (`add?cid-version=1&hash=blake3&raw-leaves=true&pin=true`, `block/get`, `pin/add`)
  that delegates the actual HTTP to an **injected** `HttpPost`. It pulls no HTTP/TLS
  crate — the gateway injects a reqwest-backed `HttpPost`, a local tool the bundled
  `StdHttpPost`.
- `StdHttpPost` — a std-only plain-HTTP/1.1 transport for a local daemon (compiles
  everywhere; live use is reviewed-go).

### Code vs ops (honest)

- **Code (done, tested):** the CID↔commitment bridge, the `IpfsClient` seam,
  `MockIpfs` round-trip + tamper-refusal, the Kubo RPC formatting (tested over a
  recording transport). `cargo test -p dregg-ipfs` is green.
- **Reviewed-go (ops, not code):** running a live IPFS daemon and a **pinning policy**
  (what to pin, replication factor, GC, who pays — folds into the existing hosting
  bandwidth/`$DREGG` meter), and a **public gateway** serving (a CID gateway in front
  of the edge, or rely on the public IPFS gateway network). These are deployment
  decisions behind the same injected seam.

---

## 5. What the prototype proves (`dregg-ipfs`)

`cargo test -p dregg-ipfs` (17 unit + 2 integration, green):

- **the CID alignment** — a raw blob's CID embeds exactly `blake3(blob)`; a dregg
  blake3 commitment re-encodes to a CID and back with no re-hash; CID string/binary
  round-trips; `base32([0x01,0x55]) == "afkq"` (a raw CIDv1 begins `bafk…`).
- **`CID == content_root` for a raw blob** — `pin_blob(bytes)` returns
  `blob_cid(bytes) == raw(blake3(bytes))`.
- **storage → IPFS round-trip** (`tests/storage_ipfs_roundtrip.rs`) — a bucket `put`
  (signed `PutReceipt`, re-witnessed via `verify_chain_from`) paired with an IPFS pin;
  the CID committed in the cell as a sibling manifest object (opens against the bucket
  root); fetch-by-CID from the node returns the published bytes.
- **a tampered fetch is REFUSED** — a node that serves different bytes under the
  committed CID is caught by the content-address check (`IpfsError::CidMismatch`).
- **the real Kubo client compiles** and formats `add`/`block-get`/`pin` correctly
  (exercised over a recording `HttpPost`).
