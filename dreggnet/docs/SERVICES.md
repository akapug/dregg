# DreggNet Cloud — the service catalog

DreggNet sells **operated reality** over dregg's free, verifiable substrate
(`ARCHITECTURE.md` → "Revenue"). A cloud is a catalog of services; this document
maps the standard cloud catalog onto the dregg primitives, so every DreggNet
service is the *same shape* rather than a pile of unrelated daemons.

## The one shape every service has

Each service is built from the same five moves, and is judged on the same three
properties. Read this once and every row below is legible.

The five moves (the dregg primitives):

| primitive | what it gives a service |
|---|---|
| **cell** (located state, the 4 substances) | the durable object the service owns — a bucket, a table, a topic, a name. State that lives somewhere and has an owner. |
| **cap-gated turn** (`StorageCap`-style token → receipted write) | the authorization + audit: an operation is exercised by attenuating a capability, and leaves a receipt binding *who did what to which committed state*. |
| **umem** (passable witnessed memory) | the committed content of a cell — a heap whose root anchors the trustless read. |
| **metering** (`Account`/`StandingObligation` → `Payable`) | the bill: every operation charges a funded budget and is refused before it commits if over budget. |
| **the trustless read** (re-witness bytes against the committed root) | the verification: a reader confirms what it was served matches the committed cell, *without trusting the server*. |

The three properties (how a row is graded):

- **Built on** — the dregg primitive the service *is*, not merely uses.
- **Paid** — the operation is metered against a funded budget (the dregg
  `execution-lease` / `Payable` rail the bridge already drives).
- **Verified** — the read (or the receipt) is re-witnessable: the client is not
  asked to trust DreggNet.

The reference implementation of the whole shape is **object storage**
(`storage/`), described below and shipped in this repo. Every other row is the
same template over a different cell.

## The catalog

| # | service | built on (primitive) | shape | paid | verified | status |
|---|---|---|---|---|---|---|
| 1 | **Object storage** | bucket = **cell**; objects = content-addressed umem | `create/put/get/list/delete`, cap-gated; trustless `verified_get` | per-op + per-KiB | object opening re-witnessed vs `content_root` | **shipped** (`storage/`) |
| 2 | **KV / database** | register-file **cell** (the kvstore exemplar) | `put/get/delete` keyed registers; monotone version | per-op | committed register state, replayable receipts | thin wrap of the kvstore cell pattern — **near** |
| 3 | **Pub/sub & messaging** | the **reactor** (on-chain command-cell → reactive) + SSE | `publish` (a cap-gated turn appends to a topic cell) → subscribers stream cell events | per-message / per-delivery | each delivered event carries its receipt; subscriber re-witnesses the topic root | **roadmap** |
| 4 | **Queues / task queue** | the **conditional-batch / cq** (durable, atomic) | `enqueue` (cap-gated turn) → durable workers `lease`+`ack`; exactly-once | per-enqueue + per-lease | the cq is itself a committed cell; dequeue leaves a receipt | **roadmap** |
| 5 | **Scheduled / cron jobs** | the **durable layer** on a timer (`dreggnet-durable`) | register a schedule cell → durable workflow fires per period | per-run (a metered durable workflow) | each run is a durable, crash-resumable, exactly-once-metered workflow | **near** (the durable runtime exists; the timer trigger is the new bit) |
| 6 | **Functions (FaaS)** | the **wasm tier** (`dreggnet-exec` → polyana) | deploy a wasm handler → invoke per request, runs in the sandbox at the lease's cap-tier | per-invocation (metered through the bridge) | the handler runs at the cap-grade the lease authorizes; output rides a receipt | **shipped (compute)** — exposed as the agent-web-app router (`webapp/`); the "deploy a standalone function" front door is the packaging step |
| 7 | **Secrets / KMS** | the **cipherclerk** (caps/secrets) + cap-bounded grants | `store/grant/use` a secret; a grant is an attenuated cap, never the plaintext | per-grant / per-use | a use leaves a receipt; the secret never leaves its cap boundary | **roadmap** (generalizes the existing BYO-keys pattern) |
| 8 | **Naming / DNS** | the **nameservice** (cell-based names) | `register/resolve/transfer` a name cell; ties to `example.com` | per-registration / per-renewal | the name→target binding is a committed cell a resolver re-witnesses | **near** (the nameservice cell exists in breadstuffs; DreggNet exposes resolution — already used by hosting's `<name>.example.com`) |
| 9 | **Identity / auth** | the **credential ZK presentation** (cap attenuation) | `issue/present/verify` — auth-as-a-service over attenuable credentials | per-verification | a presentation is a zero-knowledge proof the verifier checks; no secret disclosed | **roadmap** |
| 10 | **Static web hosting** | site = **cell** (the template `storage` generalizes) | `publish` a minisite cell; serve read-only over `<name>.example.com` | per-publish / per-GB-served | trustless cell projection (`deos-view`) re-witnesses served bytes | **shipped** (`webapp/src/hosting.rs`) |
| 11 | **Agent-served web APIs** | the **wasm tier** + router (`webapp/`) | an agent declares routes → polyana handlers; DreggNet serves them | per-request (`LeasedRouter` → `402` if over budget) | each request runs through a durable, exactly-once-metered workflow | **shipped** (`webapp/`) |
| 12 | **Compute lease (durable execution)** | the **bridge** (`execution-lease` → polyana) | rent a funded durable runtime at a cap-tier | per-period meter tick | exactly-once metering, crash-resume within budget | **shipped** (`bridge/`, `control/`) |
| 13 | **Agent coordination** | branch/stitch over **cells** + the durable layer | agents share a cell-fork they each drive, stitched by the settlement rail | per-turn | each coordination turn is a receipted, settlement-sound merge | **shipped (substrate)** — the orchestration/swarm apps in breadstuffs; DreggNet exposes it as a service |

Rows 10–13 are today's offering (`compute-lease, web-hosting, agent-coordination,
agent-web-APIs`). Rows 1–9 round the catalog out to the standard cloud surface.

## The services, grounded

### 1. Object storage — *shipped* (`storage/`)

**A bucket is a dregg cell.** Its committed state holds the bucket name, its
owner, a content commitment (`content_root`) over content-addressed objects, and
the content itself (object key → `Object` = content-type + bytes). The five
operations — `create_bucket`, `put`, `get`, `list`, `delete` — are each gated by a
`StorageCap` (`storage-bucket/<name>`, bound to holder + bucket name, so a cap for
bucket A cannot touch bucket B); each mutation is metered against a funded
`Account` (per-op + per-KiB) and refused *before any write* if over budget; and
each leaves a receipt (`PutReceipt` / `DeleteReceipt` binding who stored what, at
which content address, charged how much, moving to which committed root).

The read is **trustless**: `verified_get` returns an `ObjectOpening` (the object
bytes + the committed root + the ordered leaf list), and the pure `verify_opening`
re-witnesses, with no trust in the server, that (1) the served bytes reproduce the
leaf the opening claims, and (2) the leaves re-fold to the claimed root. A flipped
byte or a forged root is caught. This is the object-store counterpart of the
hosting module's trustless cell projection.

Honest seam (shared with hosting): in-process the leaf/root are FNV stand-ins for
the cell's committed Poseidon2 umem heap root, and the opening is the full leaf
list rather than a Merkle path; the *bytes-bind-to-root* property the verifier
checks is identical, and the deliberate flip-on step is committing the bucket cell
to a real dregg node so each put/delete is a witnessed `Effect::Write`.

This is the direct generalization of the static-hosting cell
(`webapp/src/hosting.rs`): a site commits a path→asset map served read-only; a
bucket commits a key→object map operated through cap-gated, metered, receipted
turns. It is the reference implementation of the catalog's one shape.

### 2. KV / database

The kvstore cell (the breadstuffs exemplar) is a register-file cell with a
monotone version slot and a capacity tooth: `put`/`delete` desugar to verified
`SetField` turns the executor checks against the cell's program, and `get` is the
named cross-cell-read seam. DreggNet exposes this as a managed verified KV
service: a thin wrap of the same cell, metered per operation. The verified store
underneath (pg-dregg, proof-attested) is the durable backing.

### 3. Pub/sub & messaging

The reactor turns an on-chain command-cell into a reactive stream: a `publish` is
a cap-gated turn that appends to a topic cell; subscribers stream the cell's
events (SSE today, the gateway's existing event surface). Each delivered event
carries its receipt, so a subscriber re-witnesses the topic against its committed
root. The metering is per-message published and/or per-delivery.

### 4. Queues / task queue

The conditional-batch / cq is a durable, atomic queue primitive: `enqueue` is a
cap-gated turn into a queue cell; durable workers `lease` an item and `ack` it,
with exactly-once semantics inherited from the durable layer. The queue is itself
a committed cell, so depth and the work-in-flight are re-witnessable; a dequeue
leaves a receipt. Metered per enqueue plus per lease.

### 5. Scheduled / cron jobs

A schedule is a cell holding a cron expression + the workload to fire; a durable
workflow (`dreggnet-durable`) fires it per period. Because the run is a durable
workflow, it is crash-resumable and exactly-once-metered — the same guarantee the
bridge gives compute leases. The runtime exists; the new bit is the timer trigger
cell and the period-fire loop. Metered per run.

### 6. Functions (FaaS)

The wasm tier (`dreggnet-exec` → polyana) already runs a handler in the sandbox at
the cap-grade the lease authorizes (`webapp/`'s router is this, behind HTTP
routes). The standalone-function front door is the packaging step: deploy a wasm
component as a named function cell, invoke it per request, meter per invocation
through the bridge. The cap-tier is enforced by the bridge's `map_cap_grade`.

### 7. Secrets / KMS

The cipherclerk holds secrets behind cap boundaries. A `store` writes an encrypted
secret cell; a `grant` is an *attenuated capability* to use it (never the
plaintext); a `use` exercises the grant and leaves a receipt. This generalizes the
existing BYO-keys pattern (where an agent brings its own provider keys) into a
managed, cap-bounded secret store. Metered per grant / per use; the secret never
crosses its cap boundary, which is the verification.

### 8. Naming / DNS

The nameservice is cell-based naming: a name is a cell binding `<name> → target`,
registered/resolved/transferred by cap-gated turns. DreggNet already consumes it —
hosting resolves `<name>.example.com` to a site cell — and exposes it as a managed
naming service (the `<name>.store.example.com` endpoint a bucket can address is the
same mechanism). The binding is a committed cell a resolver re-witnesses. Metered
per registration / renewal.

### 9. Identity / auth

The credential ZK presentation is auth-as-a-service: an issuer `issue`s an
attenuable credential; a holder `present`s a zero-knowledge proof of a predicate
over it; a verifier `verify`s without learning the underlying secret. This is the
cap-attenuation machinery turned outward as a login/authorization product.
Metered per verification.

## Roadmap ordering

The order follows *least new substrate first* — each step reuses the most already
built, so the catalog fills out as thin welds rather than new engines.

1. **Object storage** — *done* (`storage/`). The reference shape; nothing new
   underneath, the hosting cell generalized.
2. **KV / database** — thin wrap of the kvstore cell pattern over the pg-dregg
   verified store. No new primitive, only the managed surface + metering.
3. **Naming / DNS** — the nameservice cell already exists and hosting already
   resolves names; expose register/resolve/transfer as a first-class service.
4. **Scheduled / cron jobs** — the durable runtime exists; add the timer-trigger
   cell and the period-fire loop.
5. **Queues** — the cq primitive exists; expose enqueue/lease/ack with metering.
6. **Functions (FaaS)** — the wasm tier + router exist; add the standalone-function
   packaging + per-invocation front door.
7. **Pub/sub & messaging** — the reactor + SSE exist; add the topic cell + the
   subscribe stream + per-message metering.
8. **Secrets / KMS** — generalize the cipherclerk BYO-keys pattern into a managed
   cap-bounded secret store.
9. **Identity / auth** — expose the credential ZK presentation as a verification
   service (the most new product surface, so last).

Throughout, the invariant is the bridge's (`ARCHITECTURE.md`): **no service lets
DreggNet claim more than the dregg rail proves was paid for, and no service serves
a read the client cannot re-witness.**
