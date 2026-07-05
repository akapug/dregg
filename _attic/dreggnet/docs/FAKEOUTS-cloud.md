# FAKEOUTS — the DreggNet cloud / gateway / hosting / economy surface

_Read-only audit, 2026-06-30. Scope: `gateway/`, `webapp/`, `storage/`, `billing/`,
`demo/stripe-receiver/`, and the economy primitives they lean on (`durable/conserve.rs`,
`durable/settle.rs`, `control/hosting_meter.rs`, `control/node_api.rs`, breadstuffs'
`bridge/stripe_mirror.rs`). Every finding is grounded to `file:line`. The taxonomy hunted:
stub-returning-a-constant · mock-as-live · vacuous-check · partial-labeled-complete ·
lie-vs-code · `unimplemented!`/`todo!`/`unreachable!`/panic on a real path · proof/root-from-a-constant._

---

## TL;DR verdict (sober)

**No CRITICAL fakeouts on the cloud surface.** The three things the audit most feared —
the funding/LEASE-1a gate, the Poseidon2 `content_root` + `verify_site_bundle` /
`verify_opening` re-witness, and the Stripe signature verify + Σδ=0 conservation — are
**all genuinely implemented and non-vacuous** (proven true-AND-false by their own tests).
The known prior fakeout, the **FNV content-root, is GONE** — FNV now appears only in
comment/test names asserting its absence. There are **zero** `unimplemented!`/`todo!`/
`unreachable!`/panic on real paths across the whole surface; every non-test `.unwrap()`/
`.expect()` is `Mutex` poison propagation or a documented invariant.

This surface is one of the **honest** ones: nearly every seam wears a name tag with its
flip-on condition. The genuine findings are (a) **one real, exploitable-in-principle
integrity weakness** in `verify_opening` inherited from the shared `dregg-circuit`
byte-packing primitive (HIGH), (b) **one deployment-posture trust assumption** in the
console read plane (HIGH-if-misdeployed), and (c) a handful of honestly-named seams and
stale under-claiming docs. The sin we hunt — a *laundered* fake that looks real but isn't —
was not found on any money/verify path.

**The single worst item (now ✅ RESOLVED — see H1):** the storage `verify_opening` /
`content_address` docstrings claimed "a single changed byte moves it" and that the opening
proves "the served bytes ARE the committed object" (`storage/src/object.rs:9,218`,
`storage/src/bucket.rs:52`), but the underlying `from_bytes_packed` felt encoding was **not
injective** — a same-length adversarial byte substitution in the `+p` alias class produced
the identical commitment and the trustless read still accepted. Fixed 2026-07-01 by routing
the cloud commitment path through an injective 3-byte-per-felt packing (the shared circuit
primitive untouched); the claim is now true at the byte level, with anti-aliasing teeth
proving the same-length substitution is caught. It was a **real overstated integrity claim
over a real collision class**, not a laundered stub.

---

## HIGH

### H1 — `verify_opening` accepts an aliased byte substitution (felt-packing not injective) — ✅ RESOLVED

**RESOLVED (2026-07-01).** The cloud content-commitment path no longer routes bytes
through the shared 4-byte `dregg_circuit::field::from_bytes_packed` (u32 `% p`). Both
commitment sites — `storage/src/object.rs::poseidon2::digest8` and
`webapp/src/hosting.rs::poseidon2::absorb_len_delimited` — now use a local **injective**
`pack_bytes` (3 bytes/felt, u24 `< 2^24 ≤ p`, no modular wraparound); combined with the
existing byte-length prefix the byte→felt map is injective for same-length AND
different-length inputs. The shared circuit primitive is UNCHANGED (the in-circuit / Lean
path keeps `from_bytes_packed`). The real Poseidon2 `hash_many_8` / `wire_commit_8` stay the
hash; only the encoding into the field changed, so `content_root` VALUES re-hash (fine — no
live content). Anti-aliasing teeth added that construct a genuine old-`+p`-alias pair
(witnessed equal under the still-present `from_bytes_packed`) and confirm the new
`content_address`/`content_root` now MOVE and `verify_opening` / `verify_site_bundle`
REJECT the same-length substitution: `storage` `same_length_alias_substitution_is_caught`
+ `same_length_alias_substitution_is_rejected_by_verify_opening`, `webapp`
`same_length_alias_substitution_is_refused`. The docstrings' "a single changed byte moves
it" is now literally true at the byte level. Original finding preserved below.


- **Where:** `storage/src/object.rs:219` (`digest8`) → `dregg_circuit::field::from_bytes_packed`
  (`~/.cargo/git/checkouts/dregg-…/circuit/src/field.rs:194`), reduced by
  `BabyBear::new(v) = v % p`, `p = 2013265921 (≈ 2^30.9)`. Consumed by `object_leaf`
  (`object.rs:57`), `content_address`, and `bucket.rs:252 verify_opening`.
- **Pretends:** the docstrings/tests say "a single changed byte moves it" (`object.rs:9`),
  and `verify_opening` proves "the served bytes ARE the committed object" (`bucket.rs:52`,
  `lib.rs:34`) — a trustless content-integrity read.
- **Actually:** `from_bytes_packed` packs each **4 little-endian bytes → one u32 → `% p`**.
  Since `p < 2^32`, every 4-byte chunk value `v ∈ [p, 2^32)` reduces to `v − p`, i.e. it
  **aliases** the chunk representing `v − p` (~53% of 4-byte values have a `+p` partner).
  The primitive's own comment admits it: "Only uses 31 bits, so at most 3.875 bytes of
  entropy per element" and `encode/decode_hash` are "lossy due to modular reduction"
  (`field.rs:192,222`). So two **distinct, equal-length** byte strings differing by `+p`
  on a chunk produce the **identical** `content_address`/`object_leaf`/`content_root`, and
  since `verify_opening` recomputes through the same lossy packing, the substituted bytes
  **verify as genuine**. A malicious host can serve altered bytes for a content-addressed
  object and pass the reader's trustless check. The length-prefix in `digest8` binds length,
  not per-chunk injectivity.
- **Severity:** HIGH — load-bearing (it is the storage trustless-read security claim), and
  exploitable in principle. Distinct from the well-documented *output* 31-bit→124-bit floor
  (that part is correctly widened via `wire_commit_8`); this is an *input-encoding* gap.
- **Fakeout-or-honest-seam:** **partial lie-vs-code** — the "single changed byte" docstrings
  are overstated (true for the random flips the tests exercise, false for the `+p` alias
  class the tests never try). Inherited from the shared circuit primitive, not a stub this
  crate slipped in.
- **Fix:** pack ≤3 content bytes/felt (24 bits `< p`, injective) for the digest input, or
  bind a byte-exact canonical-bytes+length commitment alongside the felt digest. Cheapest
  local fix: route content bytes through an injective felt encoding rather than the 4-byte
  `from_bytes_packed`. (Upstream fix belongs in `dregg-circuit`.)

### H2 — Console read-scoping trusts an unauthenticated `X-Dregg-Subject` header
- **Where:** `gateway/src/api.rs:20-31, 166-176` — the `/api/*` "cap-scoping teeth"
  (`owner == subject`) key entirely off the `X-Dregg-Subject` request header.
- **Pretends:** per-subject read isolation ("a caller only sees their own sites / servers /
  buckets / spend / balance").
- **Actually:** the gateway trusts the echoed header **blindly** — it is meant to be set by
  Caddy forward-auth. If `:8080` is not firewalled to Caddy-only, a direct
  `curl -H 'X-Dregg-Subject: victim' …:8080/api/sites` reads **any** subject's data. Unlike
  the storage/publish planes (which verify a cryptographic `dga1_` credential), this plane
  has no in-gateway cap check.
- **Severity:** HIGH **if** `:8080` is exposed beyond Caddy; otherwise a latent
  deployment-posture risk.
- **Fakeout-or-honest-seam:** **honest seam** — the code documents the bind/firewall
  requirement. Not laundered, but a real risk worth hardening because the surface *looks*
  authorization-bearing.
- **Fix:** have the gateway verify the cap/credential itself rather than trusting the echoed
  header, or enforce (and assert at startup) that `:8080` is bound loopback/overlay-only.

---

## MEDIUM (all honestly-named seams — noted so we don't over-react, none laundered)

### M1 — Default build funds against a **node-trusted**, not light-client-verified, read
- **Where:** `gateway/src/funding.rs:188-193`, `gateway/src/main.rs:370-372`;
  the verified path is `control/src/node_api.rs:660 read_verified_leases`
  (real: `verified_leases_windowed(&windows, &root)` against a trusted root, TOFU or a
  finalized `CheckpointAnchor`).
- **Pretends / Actually:** the LEASE-1a gate itself is **real and non-vacuous**
  (`funding.rs:74-85 authorize` does an input-dependent `funded && is_active && cap_grade ≥
  floor && budget_units ≥ need`, wired into every write path, fails closed with no source).
  But **without `--features dregg-verify`** the source is `NodeApiLeaseSource` — it *trusts
  the node's cell-API answer* rather than cryptographically verifying it.
- **Severity:** MEDIUM. **Honest seam** — labeled "real, but node-trusted" and
  "build `--features dregg-verify` for the verified read" at every doc surface
  (`funding.rs:25-28`, `main.rs:322-328`). Fix: deploy with `dregg-verify` (make it the
  serving default).

### M2 — Storage writes bypass the LEASE-1a chain-funding rail (in-process budget stand-in)
- **Where:** `gateway/src/storage.rs:290-299` (`account_for`) — a storage PUT is metered
  against an account **auto-funded to `default_budget` on first use** ("the in-process
  stand-in for a funded lease").
- **Actually:** unlike machines-create and site-publish (which gate on real on-chain
  funding), a valid cap-holder gets free metered storage up to a self-granted budget with
  no chain funding check. Writes still require a real `dga1_` credential.
- **Severity:** MEDIUM. **Honest seam** — labeled "stand-in" — but a genuine divergence from
  the "no free resource" rail the module otherwise invokes. Fix: route storage accounting
  through the same `FundingSource` as machines/publish.

### M3 — `impl Handler for StorageHandler` hardwires an empty body
- **Where:** `gateway/src/storage.rs:333-345` — `handle()` calls `dispatch(…, &[], …)`; the
  body is always empty because `dreggnet_http::Request` (`http/src/request.rs:63`) exposes
  no body accessor.
- **Actually:** a PUT routed through the generic `Handler` trait would **silently store a
  zero-byte object**. The functional path is `dispatch`/`respond` called with a body read
  off the socket (what the tests exercise).
- **Severity:** MEDIUM (correctness trap on a naive live mount).
- **Fakeout-or-honest-seam:** **honest seam** — `lib.rs:52` / `storage.rs:37-42` say
  "Neither is wired live here" — but the `impl Handler` *looks* functional. Same shape in
  `gateway/src/webapp.rs:141-146` (publish through the bare trait 400s on empty content;
  the body-bearing path is `dispatch`, `webapp.rs:22-24`). Fix: drop the `Handler` impl (or
  make the body a required parameter) until `Request` carries a body.

### M4 — Console server / billing surfaces return empty in production (not fabricated)
- **Where:** `gateway/src/api.rs:100-116, 246-268` — `/api/servers`,
  `/api/billing/spend`, `/api/billing/balances` return `[]`/`0` because no `ServerSource`/
  `BillingSource` is wired (`main.rs:221-225` uses `ApiHandler::new`, no
  `.with_servers`/`.with_billing`).
- **Severity:** MEDIUM. **Honest seam** — labeled "the honesty law … empty until wired";
  returns empty, never fabricates. Fix: wire the sources (the `billing` crate already
  produces verifiable invoices — see D2).

### M5 — Demo Stripe receiver mints via the `test-utils` RAM applier, not the committed authority
- **Where:** `demo/stripe-receiver/Cargo.toml` links breadstuffs' `dregg-bridge` with
  `features = ["test-utils"]`; the mint fns (`mint_against_webhook`/`mint_against_payment`/
  `draw_mint`) are `#[cfg(any(test, feature = "test-utils"))]` in
  `breadstuffs/bridge/src/stripe_mirror.rs:485,509,546`.
- **Pretends / Actually:** the **signature verify is genuinely real** — `stripe_mirror.rs:279
  verify` does `HMAC-SHA256(secret, "{t}.{body}")` with a constant-time compare (`subtle`),
  replay-window enforcement, and currency/amount/recipient parse; the receiver refuses on
  bad-sig/tamper/wrong-currency/replay and requires a non-empty secret or `exit(2)`
  (`main.rs:59-68`). But the **mint** is the in-process RAM applier, so demo double-mint
  protection is only a **local `seen_payments` set** — a second relayer with a fresh set is
  not stopped. Production is the committed `verify_payment → bridge_mint_against_lock`
  against the global `note_nullifiers` (`stripe_mirror.rs:557-592`, "a per-relayer LOCAL
  fast-reject CACHE, NOT the global double-mint authority").
- **Severity:** MEDIUM. Would be **CRITICAL if** this binary were ever pointed at live money
  — but it is labeled demo/test-mode throughout (`runbooks/STRIPE-SETUP.md:40` "No real
  money moves"; the Cargo.toml calls it "the DreggNet-plane in-process twin").
- **Fakeout-or-honest-seam:** **honest seam.** Fix: never point live Stripe at the
  `test-utils` receiver; keep `bridge_mint_against_lock` the sole money path.

---

## LOW / doc-drift (stale docs that UNDER-claim — worth refreshing, not fakeouts)

### D1 — `webapp/src/lib.rs:49-54` says "in-memory SQLite", code is on-disk
The `LeasedRouter` summary claims "over an **in-memory** SQLite store per request", but the
code uses `run_workflow_on_disk_blocking` under `temp_dir()/dreggnet-webapp/<app>`
(`router.rs:30,140-152,186,305`) — on-disk with cross-process crash-resume. Stale
**under**-claim (docs undersell realness). Fix the lib.rs summary.

### D2 — `docs/CLOUD-PROVIDER-READINESS.md:203` marks INVOICES as "LACK"
The doc still says "no invoice … console has SpendEntry rows only", but the `billing` crate
now provides verifiable invoices + seal + `invoices_for` and a real receipt-trace
(`billing/src/invoice.rs:164-252`, proven to equal the ledger balance in `lib.rs:122-184`).
Stale **under**-claim. Refresh the doc.

### D3 — `bucket.rs:194` `parse_felts8(&leaf).unwrap_or([ZERO;8])` masks a bad leaf
`leaf` is always internally produced (always parses), so the fallback is unreachable today,
but silently substituting an all-zero leaf on a future non-internal caller would corrupt the
fold rather than error. LOW, **not a fakeout**. Fix: `expect` the invariant or propagate.

---

## Honest seams / non-findings (verified REAL — do NOT cry wolf)

- **Funding/LEASE-1a gate — REAL.** `funding.rs:74-85` input-dependent, wired into
  machines-create (`gateway.rs:253-320`) and publish (`sitepublish.rs:227-245`), fails closed
  with no source; the verified read (`node_api.rs:660`) really light-client-verifies against
  a trusted root. Proven non-vacuous in `tests/no_free_compute.rs`.
- **`content_root` / `content_address` — REAL Poseidon2**, not FNV/stub
  (`webapp/src/hosting.rs:1036-1114`, `storage/src/object.rs:57`, `bucket.rs:180`), verified
  against the real `hash_many_8` / `wire_commit_8` / `compute_heap_root_entries` primitives.
- **`verify_site_bundle` — REAL re-witness** (`webapp/src/verify.rs:152-207`): attestation +
  signer pin + `verify_chain` + recompute-and-compare the content root; refuses tamper /
  re-sign / forged-root, proven over real TCP (`tests/verified_read_http.rs`).
- **`verify_opening` — REAL and biting** (`storage/src/bucket.rs:252`): recompute leaf +
  re-fold root, refuses missing/flipped/tampered/doctored (`receipt_chain_verify.rs`). Its
  *only* weakness is H1's inherited encoding aliasing.
- **Meter counts REAL bytes** (`storage/src/registry.rs:320`, `meter.rs:65`;
  `control/hosting_meter.rs`) — charges `object.size()`, atomic, refuses over-budget, never
  negative.
- **Receipt chain — REAL trace** (`storage/src/registry.rs:234`): prev-hash-chained +
  ed25519, forged root → `BadSignature`, spliced link → `BrokenLink`.
- **Conservation Σδ=0 — REAL enforcement** (`durable/src/conserve.rs:87-165`): paired delta,
  refuses debit-below-zero (`InsufficientFunds`), overflow-checked credit; `settle.rs:262-326`
  atomic dedup+move+record, exactly-once. Not a decorative twin.
- **Invoice receipt-trace — REAL** (`billing/src/invoice.rs:164-252`): aggregates real
  usage, `verify_against_receipts` rejects non-tracing / math-mismatch / asset-mismatch
  lines; the test asserts `inv.total_units == ledger.balance(provider)`.
- **Stripe HMAC verify — REAL** (see M5) with a constant-time compare and replay window.
- **In-circuit witness of `Effect::Write` / deployed-root byte-identity = the VK-epoch**
  (`hosting.rs:39-47,1056-1058`, `bucket.rs:42-51`): the off-chain commitment is real every
  build; only the light-client in-circuit witnessing is the deliberate deferred flip.
  Includes the `wire_commit_8` vs `wire_commit_8_chip` non-byte-identity — honestly labeled.
- **`TailscaleMesh::connect`** (`control/src/mesh.rs:468-480`) assumes the host is already on
  the tailnet; dispatch over a plain stub returns `ProviderError::Unimplemented` **carrying
  the exact POST it would issue** (`mesh.rs:581-586`) — an honest named live-overlay step,
  not a silent no-op.
- **`gen_machine_id`/`gen_instance_id`** (`gateway.rs:535-551`) — explicitly "Not
  cryptographic — an opaque handle"; ids are not security-bearing.
- **Rate cards / default assets** (`billing/usage.rs:140-153`, `hosting_meter.rs:88-93`,
  `stripe-receiver main.rs:77 [0xCD;32]`) — a price list / demo constant, cross-checked for
  alignment (`lib.rs:186-203`), not a fake.

---

## The deploy-state caveat (context, not a code fakeout)

`docs/DEPLOY-READINESS.md` (itself an honest audit) records that the **wired** gateway,
provider, console, status, landing, and webauth are **built in the repo but NOT on the live
box** (runtime images are Jun-29, predating the wire-up commit). So the *live* gateway is the
older un-wired one and the *live* auth is basic-auth, not the cap-account webauth default. That
is a deployment-lag fact, honestly documented — not a laundered code fakeout — but it means the
real gates audited above are not yet the ones facing the internet.
