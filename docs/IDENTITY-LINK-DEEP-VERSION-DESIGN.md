# Identity-Link DEEP Version — links as receipt-signed turns on K's identity cell (design, 2026-07-19)

**Status:** partially SHIPPED. The **churn-independent core is built and unit-tested in
`webauth-core`** — brick 1 `account_id_of_root` (the rotation-proof join key,
`link_registry.rs`), brick 2 `link_kel` (the LINK/UNLINK memo convention + the pure
`fold_link_events` / `resolve_root_from_events` resolver), and the `linked_platforms` credential
schema type. The **node/cell-touching parts and the Lean AIR remain design** (§8/§9 below are the
concrete build spec for when the `node` crate un-churns). Progresses the identity PILLAR from the
shipped *shared-TSV registry* to *links are receipt-signed turns on the identity cell*.

**What is verifiable NOW vs later:** the memo format, the signature/verb discipline, the fold, and
the account-id cross-check with the TSV resolver are all provable in `webauth-core`'s own test
suite (`cargo test -p webauth-core`, no node). The `verify_export` extension, the dual-write +
reconcile, and the `FederationId ↔ account-id` adapter are **convergence-gated** (need the `node`
crate). The **D2 enforced-links register is Lean-authored AIR** (§1.3) — the tripwire.

**Substrate note (read first):** everything in stages D1/D2 that is **enforcement of a constraint**
(who may append a link, append-only-ness, unlink-preserves-history as a *cell-program* rule) is
**AIR authored in Lean**, with a refinement theorem over the emitted object; Rust only calls the
emitted artifact. The stages that are Rust are serde/format/ed25519/blake3 plumbing and are
labeled as such. Where a section reaches a real constraint it says so out loud — see **D2**.

---

## 0. Where we are (the shallow version, live)

The shipped layer (`webauth-core`):

- **`account_id.rs`** — `account_id_hex(inception_pubkey)` = hex of
  `CellId::derive_raw(inception_pubkey, blake3("dregg:account-identity:v1"))`. The account id **IS**
  the substrate identity-cell id, byte-for-byte, and is derived from the **inception** key, so it is
  fixed for life across rotation (the KERI AID invariant).
- **`link_claim.rs`** — `verify_link_claim(...)`: root key **K** signs the canonical message
  `"dregg-identity-link-v1:" ‖ platform ‖ 0 ‖ uid ‖ 0 ‖ custodial_hex ‖ 0 ‖ root_hex ‖ 0 ‖ challenge`;
  fresh within the `challenge.rs` window; `verify_strict`. This is the **authorization object** — K
  attests it controls a platform account whose custodial key is `custodial_pubkey`.
- **`link_registry.rs`** — `LinkStore` / `FileLinkStore`: an append-only TSV at
  `$DREGG_LINK_DIR/links.tsv`. `resolve_root(custodial) -> Option<root>` (latest-wins),
  `platforms_for_root(root)`. Binds the **raw pubkeys** (each consumer derives its own cell flavor).
  Every frontend appends; resolution unifies at display.

What the shallow version does **not** have, and the deep version supplies:

| gap in the shallow TSV | deep-version fix |
|---|---|
| the join key is a **raw** root pubkey with **no rotation story** — if K rotates, a new link signs under a new key and the two humans stop unifying | join on the **inception-derived account id** (`account_id_hex`), which survives rotation |
| a link record is a **bare file line** — no receipt, no witness, no non-repudiation, no ordering, no export | a link is an **event on K's identity cell** — chained, receipt-signed, federation-witnessed, exportable via `verify_export` |
| unlink = "just append another line" with no history discipline | unlink = a **revocation event** on the cell; the KEL preserves the full history and the verifier folds it |
| resolution is a **display join** — soft, online, node-local | K can mint a **HandoffCertificate** delegating a scoped capability to the platform key: offline-verifiable, capability-shaped, non-amplifying |
| "same human across platforms" leaks **which** accounts | a **linked-platforms credential** proves it in ZK with selective disclosure / anonymous multi-show |

---

## 1. The link record as an identity-cell TURN

### 1.1 The shape of the cell (and the honest constraint it imposes)

K's identity cell (`starbridge_polis::identity`) is a fixed 16-slot key-state cell:

| slot | register | who writes it |
|---|---|---|
| 0 | `STATE` (UNINIT→ACTIVE→RETIRED) | lifecycle |
| 1 | `NEXT_KEYS_DIGEST` | `KeyRotationGate` |
| 2 | `CURRENT_KEYS_COMMIT` | `KeyRotationGate` (== exhibited preimage) |
| 3 | `LAST_ROTATED_AT` | the gate (cooling anchor) |
| 4 | `COUNCIL_COMMIT` | pinned once |
| 5..7 | reserved | **pinned zero** |

The reserved slots are **pinned to zero** (`RESERVED_SLOTS` → `pinned_zero`). So the current cell
has **no free register to carry a link payload**. That constraint forks the design into two honest
stages: **D1 rides the machinery the cell already has (no new AIR)**, and **D2 gives links an
enforced register (new AIR, authored in Lean)**.

### 1.2 D1 — links as attested `ixn` events (reachable now; NO new constraint)

The KEL export (`node/src/identity_export.rs`) already walks the persisted commit log, keeps every
turn that **touched the identity cell**, and classifies each into KERI kinds: `icp` / `rot` / `ixn`
/ `rtd`. A turn that touches the cell **without moving the key registers** is an **`ixn`
(interaction)** — and `verify_export` already enforces that an `ixn` may **not** move slots 1/2 or
the pinned council commitment. That is exactly the envelope a link needs.

**A link turn is an `ixn` turn touching K's identity cell whose action carries the existing
`link_claim` attestation as a committed memo.** Concretely:

- The turn's effect list makes **no register change** (or only a permitted reserved-consistent
  no-op) — so `classify()` labels it `ixn` and the immutability teeth in `verify_export` pass.
- The turn's **action/journal carries the attestation bytes** `link_claim_message(platform, uid,
  custodial_hex, K_root_hex, challenge) ‖ K_signature` (plus a `LINK` / `UNLINK` verb tag). The
  turn hash commits it (it is part of the signed turn), and the KEL event's `turn_hash` /
  `receipt_hash` are already digested into the chain.
- Because it is a real turn, it inherits — **for free, verbatim** — everything the KEL gives:
  **chaining** (`prior_event_digest`), the **executor signature** on the `TurnReceipt`
  (`canonical_executor_signed_message`), **federation witness artifacts** (DWR1, re-bound by
  `receipt_hash`), and **portable export** (`verify_export`, no node needed to check).

**Unlink** is another `ixn` link turn with the `UNLINK` verb over the same `(platform, uid)`,
signed by K. History is preserved because the KEL never rewrites — the unlink is a later event; the
resolver folds `LINK`/`UNLINK` in sequence (latest-wins per `(platform, uid)`), and the full trail
stays in the log for audit and export.

**`resolve_root` reads the cell's event log** — *in addition to*, then *instead of*, the TSV
(migration §5). The cell-reading resolver:

1. runs `verify_export(log, pinned_K_key)` — all the chain/receipt/witness teeth fire;
2. recomputes `derive_raw(K_inception_pubkey, account_root_token()) == log.cell` — **the cell IS K**
   (this is the `account_id` derivation, reused verbatim; it is what binds the whole log to K);
3. for each `LINK`/`UNLINK` attestation, `verify_strict`s K's signature and folds it into a
   `custodial → account_id` map (unlink removes the binding; latest event wins);
4. returns the **stable account id** as the join key.

**What D1 proves, at the honest resolution:** the link's **authorization** is K's ed25519 signature
(real, node-independent — the same guarantee the shipped `link_claim` already has). What the cell
*adds* over the TSV is **ordering, non-repudiation (executor + witness receipts), unlink-with-
history, and a portable verifier** — all reusing existing, tested machinery. What it does **not** yet
add is *cell-program enforcement* that only K may append a link (in D1 that is enforced by K's
signature in the payload, not by the cell's constraint set) — that is **D2**.

**New in D1 (all Rust — serde / ed25519 / blake3, NOT AIR):**

- a `LINK`/`UNLINK` verb + attestation memo convention on the turn action;
- an **additive KEL format bump** `dregg-kel/2`: an optional `link_attestation` (and `unlink`
  marker) attachment on `IdentityEvent`, digested into the event digest (so tampering breaks the
  chain) or bound via `turn_hash`; readers already `reject-on-unknown` on `format`, so v1 logs stay
  valid;
- `verify_export` extended to check (a) `cell == derive_raw(K_inception, token)`, (b) the
  attestation is signed by a key **in the key set exhibited at that event** (see §4 — this ties
  links to rotation), (c) unlink folding;
- a `resolve_root_from_kel(...)` that returns the same `custodial → account_id` map shape.

**SHIPPED (churn-independent, `webauth-core`, unit-tested):** the memo convention + the pure fold
are built as `webauth-core::link_kel`:

- `LinkMemo` — the canonical on-turn bytes (`LINK_MEMO_DOMAIN ‖ verb ‖ platform ‖ 0 ‖ uid ‖ 0 ‖
  custodial_hex ‖ 0 ‖ challenge ‖ 0 ‖ root_pubkey(32) ‖ signature(64)`), with `to_bytes` /
  `from_bytes` round-trip. It **wraps the existing `link_claim` attestation verbatim** for LINK and
  adds a byte-for-byte sibling `unlink_claim_message` under `dregg-identity-unlink-v1:` for UNLINK,
  so a LINK signature can never be replayed as an UNLINK (distinct domain ⇒ distinct signed bytes).
- `fold_link_events(&[LinkEvent]) -> Result<LinkResolution, LinkFoldError>` — verify each event's K
  signature, enforce one-cell (one signing root) + strictly-increasing KEL order, fold LINK/UNLINK
  latest-wins per custodial, expose the stable account id. `resolve_root_from_events(events,
  custodial)` is the thin `custodial → account_id` seam — the **cell-reading analogue of
  `link_registry::resolve_root_account`**, and a test pins that the two agree byte-for-byte on the
  equivalent link set.

This is exactly step 2–4 of the cell-reading resolver above, testable with **no live node**. What
it deliberately does NOT do (deferred to §8): replay rotation (it pins one signing root), bind each
link signature to the *exhibited key set*, check `cell == derive_raw(K_inception, ..)`, or run the
chain/receipt/witness teeth — those need the KEL and live in `verify_export`.

### 1.3 D2 — an ENFORCED links register (LATER; AIR authored in LEAN)

> **TRIPWIRE — this is constraint/gadget work. It is authored in Lean.** The moment we want the
> *cell program itself* to gate link appends (append-only; only a key exhibited against
> `CURRENT_KEYS_COMMIT` may append; unlink cannot erase history; the links commitment evolves by a
> proven rule), that is a **`StateConstraint` / gadget with a refinement theorem over the emitted
> object**. It does **not** get hand-written as a Rust `StateConstraint`. It is emitted from Lean
> and Rust calls the artifact — exactly like `KeyRotationGate`.

Two Lean-authored shapes are available; pick at D2 time:

- **Option A — a `LINKS_COMMIT` register (repurpose reserved slot 5).** A commitment (sorted-Merkle
  accumulator) over the currently-active link set. A `LINK`/`UNLINK` turn evolves slot 5 from
  `old_root` to `new_root` by an **append/tombstone rule gated in Lean**, signed by a key exhibited
  against slot 2. This keeps links *on* the identity cell but requires proving the new register does
  not disturb the pre-rotation invariants (the cleanest refinement obligation).
- **Option B — a separate K-anchored *link-ledger* cell.** A second cell derived under a distinct
  domain token (e.g. `"dregg:identity-links:v1"`) whose program admits appends only when the turn
  carries a signature chaining to K's identity-cell `CURRENT_KEYS_COMMIT`. The identity cell stays
  *pure key-state* (its proven invariants untouched); the link ledger gets its own simpler
  append-only gate. Preferred if we want zero risk to the pre-rotation proofs.

Until D2 lands, D1's guarantee (K's signature authorizes; the KEL orders/witnesses/exports) is the
honest ceiling — stated as such.

---

## 2. HandoffCertificate-backed DELEGATION (resolution becomes capability-shaped)

Today `resolve_root` is a **display join**: online, node-local, "these two accounts are the same
human." A `captp::HandoffCertificate` turns that into an **offline-verifiable, capability-shaped**
delegation: "K authorized THIS platform key to exercise THESE capabilities on K's behalf."

**The mint.** K (introducer) calls `HandoffCertificate::create(K_signing_key, K_federation_id,
target_federation, target_cell, recipient_pk = platform_custodial_pubkey, permissions, allowed_
effects, expires_at, max_uses, swiss)`. The cert is signed under
`"dregg-handoff-cert-v1"`, travels **out of band** as `dregg-handoff:<base58>` (QR, DM, file, BLE),
and the platform key proves receipt with a `HandoffPresentation` (recipient signs the nonce).

**Why this is stronger than a display join:**

- **Offline / self-contained** — the platform side proves "K delegated to me" from the cert alone,
  no live `resolve_root` lookup against a shared file.
- **Non-amplifying** — `validate_handoff` enforces `granted ⊆ held` and `granted.target ==
  held.target` (the Lean `handoff_non_amplifying` / `handoff_same_target` spec). The platform key
  can act for K only within the exact scope K registered — never wider.
- **Scoped + revocable** — `permissions: AuthRequired` (incl. `Custom { vk_hash }`),
  `allowed_effects: EffectMask`, `expires_at`, `max_uses`, and swiss pre-registration (unregister to
  revoke). A link is no longer "same human forever"; it is "this key may do X for K until Y."
- **Hybrid-PQ** — the introducer's `FederationId` **commits** to the ML-DSA-65 key
  (`IntroducerIdentityCommitmentMismatch` fail-closed), so the delegation survives a quantum
  adversary who forges only the ed25519 half.

**Relationship to §1.** The link `ixn` event says "K claims this platform account is K's" (an
attestation). The HandoffCertificate says "K grants this platform key capability C over resource R"
(an authorization). They compose: the link event is the **public, witnessed record** that the
delegation happened; the cert is the **bearer proof** the platform key carries to *exercise* it.

**Reuse:** `HandoffCertificate` / `HandoffPresentation` / `validate_handoff` verbatim.
**New (Rust, small):** an adapter binding K's cert-introducer `FederationId` to K's inception pubkey
(so "the introducer IS the account" is checkable), and the swiss pre-registration on the target
(needs the node — §6 gap).

---

## 3. A "linked-platforms" CREDENTIAL (selective disclosure)

Goal: **"prove I am the same human across platforms without revealing WHICH Discord account."**
This is exactly `credentials/`'s shape (federation-bound issuer membership + real STARK presentation
+ selective disclosure + predicate proofs + anonymous unlinkable multi-show).

**Schema** (`CredentialSchema`, caller-defined):

```
linked-platforms:
  platforms_count      : Int      # how many platforms are linked to this human
  has_discord          : Int(0/1)
  has_telegram         : Int(0/1)
  has_web              : Int(0/1)
  discord_uid_commit   : Bytes32  # blake3(discord_uid) — never the uid itself
  telegram_uid_commit  : Bytes32
  account_id           : Bytes32  # K's inception-derived account id
```

**Issuance** (`credentials::issue(issuer, schema, holder_id = blake3(K_pk), attributes, issued_at,
not_after)`). The **issuer is a dregg node/federation** that has **verified K's cell KEL** (§1: run
`verify_export`, confirm the `LINK` events, count platforms) and attests the attribute set. The
credential is a real signed macaroon anchored to `federation_root`.

**Presentation.** The holder chooses what leaks:

- **Selective disclosure** — `PresentationOptions::new().disclose("has_discord")` reveals
  `has_discord = 1` but **not** `discord_uid_commit`, never the uid.
- **Predicate proof** — `.predicate(PredicateRequest::new("platforms_count", Predicate::Gte(2)))`
  proves "≥ 2 platforms linked" without revealing the count or the platforms.
- **Anonymous multi-show** — `present_anonymous(...)` uses a fresh blinding factor per show, so the
  verifier learns only "the presenter holds *some* linked-platforms credential from this issuer" —
  not which credential, not which accounts, and two shows are unlinkable.

This is the primitive that answers the goal: `present_anonymous` + `disclose("has_discord")` +
`predicate(platforms_count ≥ 2)` proves *"I am one human who holds a Discord account and at least
two linked platforms, attested by issuer I"* while revealing **no** account identifiers.

**Reuse:** `credentials::{issue, present, present_anonymous, verify, verify_anonymous}` +
`PresentationOptions` + `PredicateRequest` verbatim. **New (Rust):** the `linked-platforms` schema
and the issuer-side flow that reads K's KEL before issuing. **Honest gap:** the credential is only as
sound as (a) the issuer's check that the cell really carries the links, and (b) the STARK floor the
presentation inherits (§6).

---

## 4. Rotation of K via the KERI cell (the id survives; the signing key rotates)

The identity cell **already** does KERI pre-rotation (`KeyRotationGate`, kernel semantics
`metatheory/Dregg2/Apps/PreRotation.lean`), and `account_id` is **inception-derived**, so this
section is mostly "use what exists" — but it fixes a **real shallow-version wound**.

- **Rotate** = a `rot` turn (`sdk::identity::rotate_effects` + `.reveal(preimage)`): exhibit the
  preimage of `NEXT_KEYS_DIGEST`, install it as `CURRENT_KEYS_COMMIT`, re-commit a fresh next digest
  in the same turn, stamp `LAST_ROTATED_AT`, after the cooling window. A thief holding every current
  key still cannot rotate (`rotate_compromise_resistant`).
- **The account id does not move.** `account_id_hex` derives from the **inception** key, so the cell
  id — and therefore the join key every link resolves to — is unchanged by rotation.
- **Links bind to the account, not to a raw signing key.** After a rotation, existing links stay
  valid (they resolve to the stable account id); **new** link `ixn` events are signed by the **new**
  key set. The KEL shows the `rot` event sitting between link `ixn` events, and `verify_export`
  replays the whole key history.
- **This is the concrete correctness win over the TSV.** In the shipped TSV, `resolve_root` returns
  the **raw** `root_pubkey_hex`; a rotation of K would produce links under a **different** pubkey and
  the two humans would **stop unifying** — a latent orphaning bug. Keying on the account id (which is
  what the cell id *is*) makes rotation transparent. Binding link signatures to *the key set
  exhibited at each event* (§1.2) further means a stolen **old** key cannot forge a **new** link.

**Reuse:** the entire rotation machinery + `account_id`, verbatim. **New:** only the §1 rule that a
link attestation is verified against the current key set at its event (Rust, in `verify_export`).

---

## 5. Migration path — TSV → cell (additive; no big-bang)

The invariant that makes this non-disruptive: **`resolve_root` keeps the same signature at every
phase** (`custodial → join-key`), so no consumer in the offerings stack changes. Only the *authority*
behind it moves, and the *join key* widens from raw-pubkey to account-id (which is byte-compatible
because the account id **is** the future cell id).

- **P0 (today).** TSV only. `resolve_root(custodial) -> root_pubkey_hex`.
- **P1 — account-id join key (the smallest step, §7).** Frontends also record
  `account_id_hex(root_pubkey)` and `resolve_root` keys on it. Pure addition to the shipped TSV;
  churn-independent (`webauth-core` only). Immediately makes links rotation-proof and makes the TSV
  key **byte-identical to the cell id** the KEL will later expose.
- **P2 — dual-write.** Every verified link **also** submits a `LINK` `ixn` turn to K's identity cell
  **when the node is reachable** (queue + retry otherwise); the TSV is still written as a fast cache.
  A `reconcile` job rebuilds the TSV cache from the KEL (`verify_export`) so the cache is *provably
  derived* from the authority, not an independent source of truth.
- **P3 — cell-authoritative.** `resolve_root` reads a **verified local cache refreshed from
  `verify_export`**; the TSV is demoted to a pure, rebuildable cache and is never trusted on its own.
  `UNLINK` turns land on the cell and flow into the cache. The TSV can be deleted and rebuilt from
  the KEL at any time.

At no phase is there a flag day: P1 is additive, P2 is a background writer, P3 is a cache-source swap
behind an unchanged resolver signature.

---

## 6. Honest gaps (named at the right resolution)

- **Needs the node/cell live.** D1 requires K to *have* a provisioned identity cell on a running
  node and the frontends to submit turns to it. Today links are recorded offline into a file; the
  cell path needs the node reachable (queue + eventual submission covers transient outages, but the
  cell is per-user aspirational until each K has one). The TSV remains the only store until then.
- **The link's *ordering/finality* inherits the ledger's floor.** The link's **authorization** is
  K's ed25519 signature — real and node-independent. The KEL's chain (blake3), executor signature
  (ed25519), and witness re-binding are **real cryptographic checks**. But "this cell state is the
  consensus-canonical state" inherits the deployed ledger's undischarged FRI/STARK posture (per
  `project-fri-soundness-reality`: the deployed floor is a calculator-bits posture and the ledger
  does not touch the apex). So: authorization = sound; ordering/finality = as sound as the ledger,
  no more. Do **not** describe a link event as "verified on-chain" beyond that.
- **`verify_export`'s own stated limit.** The "this post-state snapshot belongs to THIS turn's
  commit" binding rests on the **exporting node's commit log**, not on per-cell state-commitment
  openings against `ledger_root` (the anchors are present in the event for that upgrade). The receipt
  + witness attestations bind an executor and a federation to the export; a fully trustless export
  wants the state-commitment openings. Carry that limit forward verbatim.
- **Credential issuer trust + STARK floor.** The linked-platforms credential is only as good as the
  issuer's KEL check, and `present`'s soundness inherits the same STARK floor as any bridge
  presentation.
- **Delegation needs node-side swiss registration.** The HandoffCertificate path needs the target
  federation live to register/unregister the swiss entry (mint offline; register online).
- **D2 is unbuilt AIR.** Until the enforced links register (§1.3) is **authored in Lean**, link
  append-only-ness and "only K may append" are enforced by K's signature in the payload, not by the
  cell's constraint set. That is the honest D1 ceiling; D2 is the Lean-substrate lift, not a Rust
  `StateConstraint`.

---

## 7. Reuse vs Build — and the smallest first step

### Reuse (verbatim / as-is)

| component | role in the deep version |
|---|---|
| `webauth-core::account_id` | the stable, inception-derived join key = the cell id (§1, §4, §5) |
| `webauth-core::link_claim` | the authorization object — becomes the turn's attestation memo (§1) |
| `webauth-core::challenge` | freshness on the claim (§1) |
| `webauth-core::link_registry` (TSV) | kept as the fast, rebuildable cache (§5) |
| `node::identity_export` (`extract_identity_log` + `verify_export`) | the KEL: chain + receipts + witnesses + portable verify (§1) |
| `starbridge_polis::identity` + `sdk::identity` (`KeyRotationGate`, `genesis_effects`, `rotate_effects`) | rotation; the cell the links ride on (§1, §4) |
| `captp::HandoffCertificate` / `HandoffPresentation` / `validate_handoff` | scoped, offline, non-amplifying delegation (§2) |
| `credentials::{issue, present, present_anonymous, verify}` + `PresentationOptions` + `PredicateRequest` | the linked-platforms credential (§3) |

### Build (new)

| item | substrate |
|---|---|
| `LINK`/`UNLINK` verb + attestation memo convention on the turn action | Rust (turn-action plumbing) |
| additive KEL format bump `dregg-kel/2` (optional digested `link_attestation` / `unlink` attachment) | Rust (serde) |
| `verify_export` extension: `cell == derive_raw(K_inception, token)`, link sig vs. exhibited key set, unlink folding | Rust (ed25519 + blake3) |
| `resolve_root_from_kel(...)` returning the same `custodial → account_id` shape | Rust |
| dual-write + `reconcile` (submit link turn when node-reachable; rebuild TSV from KEL) | Rust |
| `FederationId ↔ account-id` adapter for the cert introducer | Rust (small) |
| `linked-platforms` schema + issuer-side flow (verify KEL, then `issue`) | Rust (uses `credentials` verbatim) |
| **D2: the ENFORCED links register** (slot-5 `LINKS_COMMIT` append-gate **or** a K-anchored link-ledger cell program) | **LEAN-authored AIR + refinement theorem; Rust calls the emitted artifact** |

### Smallest first step (moves toward the cell, no big-bang, churn-independent)

**Make the TSV join key the inception-derived account id, not the raw root pubkey.** Have the
frontends record `account_id_hex(root_pubkey)` alongside the raw root in `link_registry`, and have
`resolve_root` key on the account id (P1 above). It is a few lines, touches **only `webauth-core`**
(no cross-crate churn), and it is the single seam that lets the cell slot in later with **zero**
consumer changes, because:

1. it makes links **rotation-proof today** (the join key is inception-derived, so a future K
   rotation does not orphan them — closing the latent shallow-version wound in §4);
2. the account id **is** the cell id the KEL will later expose, so when the cell becomes the
   authority (P2/P3) the cache keys already match the cell id **byte-for-byte** — no re-keying, no
   migration of existing records;
3. it requires **no node and no new AIR** — it is the cheapest possible motion in the cell's
   direction.

The next step after that is P2 dual-write of `LINK` `ixn` turns behind a node-reachable check —
still additive, still behind the unchanged `resolve_root` signature.

---

## 8. Node-side build spec (concrete; for when the `node` crate un-churns)

Everything here touches `node/src/*` (co-tenant-churny) and so is **design, not yet code**. It is
written as a precise build order so it can be executed against the real tree without re-deriving the
seams. All of it is **Rust plumbing (serde / ed25519 / blake3)** except where §8.4 flags Lean.

### 8.1 The `verify_export` extension (`node/src/identity_export.rs`)

The shipped verifier signature is
`verify_export(log: &IdentityEventLog, pinned_executor_key: Option<&[u8; 32]>) -> Result<VerifyReport, VerifyError>`.
Add a link-aware pass **without changing** the existing chain/rotation/receipt teeth (they stay the
authority for ordering + key history). Concretely:

1. **Format bump `dregg-kel/2` (additive).** `KEL_FORMAT_VERSION` currently pins `"dregg-kel/1"`
   and `verify_export` rejects any other `format`. Widen the accept set to `{dregg-kel/1,
   dregg-kel/2}`; add to `IdentityEvent` an optional, `#[serde(default, skip_serializing_if …)]`
   `link_attestation: Option<LinkAttestation>` where `LinkAttestation` is the decoded
   `webauth_core::link_kel::LinkMemo` (verb + platform + uid + custodial_hex + root_pubkey +
   challenge + signature). It must be **digested into `event_digest`** (extend `DigestSurface` with
   a tag-prefixed `Option` branch, exactly like `prior`) so tampering breaks the chain — OR bound via
   the already-digested `turn_hash` if the memo rides the turn action. Pick the digest-inclusion
   route; it is self-contained (no dependence on how the turn serialized its action). v1 logs carry
   no attestation and stay valid (reject-on-unknown only fires on an unknown *format*, not a missing
   optional field).

2. **`cell == derive_raw(K_inception, account_root_token())`.** The account binding. `verify_export`
   already decodes `log.cell`. Add a parameter `pinned_inception_key: Option<&[u8; 32]>`; when
   present, check `CellId::derive_raw(pinned_inception_key, &webauth_core::account_id::account_root_token()).0
   == cell` and fail closed (`VerifyError::CellNotAccountId`) otherwise. This is the tooth that says
   *this whole log is K's* — reusing `account_id` verbatim. (Without the pin, the verifier still
   checks everything else; the binding is simply unproven, and the report says so.)

3. **Link signature vs. the *exhibited key set* (rotation-aware).** For each event carrying a
   `link_attestation`, rebuild the attestation message
   (`link_kel::LinkMemo::signed_message()` — reuse verbatim) and `verify_strict` the signature.
   The signing key must be a key **exhibited at or before this event**: the verifier already walks
   `current_keys_commit` per event; require the attestation's `root_pubkey` hash to the key-set
   commitment in force at this `seq` (i.e. `blake3(root_pubkey)`-membership against the installed
   `current_keys_commit`, matching the gate's `HashKind::Blake3` shape). A stolen **old** key thus
   cannot forge a **new** link (§4). New `VerifyError::LinkKeyNotExhibited { seq }`.

4. **Unlink folding = the pure fold, wrapped.** After the per-event teeth pass, hand the ordered
   `link_attestation`s (in `seq` order) to `webauth_core::link_kel::fold_link_events` and surface the
   `LinkResolution` in `VerifyReport` (add `links_active: usize`, and a `resolve_root(custodial)`
   helper on the report). **Do not re-implement the fold node-side** — the churn-independent core is
   the single source of truth; `verify_export` only *feeds* it verified, ordered events. `resolve_root_from_kel(log, pinned_inception_key, custodial)` is then a one-liner:
   `verify_export(..)?.resolve_root(custodial)`.

Adversarial tests to ship with it (mirroring the existing `chain_tamper_refuses` style): a link
attestation whose signature is by a non-exhibited key refuses; a tampered memo (digest mismatch)
refuses; an UNLINK folds the custodial out; `cell != derive_raw(K_inception, ..)` refuses.

### 8.2 Dual-write + reconcile (P2 → P3 of §5)

- **Dual-write.** Where a frontend today calls `FileLinkStore::record` after `verify_link_claim`,
  it *also* (behind a node-reachable check) submits a `LINK` `ixn` turn to K's identity cell whose
  action carries `LinkMemo::to_bytes()`. The submission is a normal turn through the existing
  SDK/exec path — the memo is opaque action bytes; **no new AIR** (the cell program does not yet
  gate it — that is D2). On node-unreachable, queue with retry; the TSV write is the fast cache and
  is never blocked on the node.
- **`reconcile` job.** Periodically `GET /identity/export/{cell}` for each K, run
  `verify_export(.., pinned_inception_key)`, fold, and **rebuild the TSV cache from the fold result**
  so the cache is *provably derived from the authority* (the KEL), not an independent truth. The TSV
  can be deleted and rebuilt at any time. This is the P3 "cache-source swap behind an unchanged
  `resolve_root` signature": consumers keep calling `resolve_root(custodial) -> account_id`; only the
  refresh source moves from "appended by frontends" to "folded from `verify_export`".
- **Reconcile is the honesty gate.** Because the cache is rebuilt from `verify_export`, a divergence
  between "what the TSV says" and "what the KEL proves" is a *detectable, fail-closed* condition (the
  reconcile drops any TSV row the KEL does not carry), not a silent drift.

### 8.3 The `FederationId ↔ account-id` adapter (for §2 delegation)

`FederationId(pub [u8; 32])` (`types/src/lib.rs`). The HandoffCertificate names K as introducer by
`FederationId`; to check "the introducer **is** the account", bind K's `FederationId` to K's
inception pubkey. Build a tiny adapter (Rust, `node`-adjacent):

- `fn account_federation_id(inception_pubkey: &[u8; 32]) -> FederationId` — the canonical map. The
  clean choice is `FederationId(CellId::derive_raw(inception_pubkey, &account_root_token()).0)`, i.e.
  **the FederationId IS the account id / cell id** (byte-identical), so "introducer == account" is a
  literal `==` and no separate registry is needed.
- `fn verify_introducer_is_account(cert_introducer: &FederationId, inception_pubkey: &[u8; 32]) -> bool`
  — `*cert_introducer == account_federation_id(inception_pubkey)`. The cert's hybrid-PQ commitment
  (`IntroducerIdentityCommitmentMismatch`, §2) already binds the `FederationId` to the ML-DSA key;
  this adds the binding to the *account*, closing "K delegated" ⇒ "the account delegated".

If the deployed `FederationId` derivation is *not* free to define this way (it is assigned by node
provisioning), fall back to a one-row attestation cell mapping `FederationId → account_id` signed by
K; but prefer the derivation identity — it needs no extra state.

### 8.4 D2 — the ENFORCED links register  ⚠ **LEAN-AUTHORED AIR (THE TRIPWIRE)**

> **STOP. This section is constraint/gadget work. It is authored in Lean, not Rust.** The moment the
> *cell program itself* gates link appends — append-only; only a key exhibited against
> `CURRENT_KEYS_COMMIT` may append; unlink cannot erase history; a `LINKS_COMMIT` register evolves by
> a proven append/tombstone rule — that is a **`StateConstraint` / gadget with a refinement theorem
> over the emitted object**, emitted from Lean, with Rust calling the artifact (exactly like
> `KeyRotationGate`). Do **not** hand-write it as a Rust `StateConstraint`; extending a Rust AIR to
> "just add the link-append case" IS the drift. Options A (slot-5 `LINKS_COMMIT`) and B (a separate
> K-anchored link-ledger cell) are in §1.3; pick at D2 time **in Lean**. Until then, D1's ceiling —
> K's signature authorizes; the KEL orders/witnesses/exports — is the honest posture, stated as such.

---

## 9. Linked-platforms credential — shipped schema + issuer adapter (design §3 made concrete)

### 9.1 SHIPPED (churn-independent, `webauth-core::linked_platforms`)

The **schema half is built and tested**, with **no dependency on the ZK stack** (`dregg-credentials`
pulls in `dregg-bridge` + `dregg-circuit`, which are churny — so `webauth-core` does not depend on
it):

- `SCHEMA_NAME = "linked-platforms-v1"` and the **ordered** attribute names
  (`schema_attributes()` — order is load-bearing for the credential fold-chain):
  `platforms_count, has_discord, has_telegram, has_web, discord_uid_commit, telegram_uid_commit,
  account_id`.
- `LinkedPlatformsAttributes::from_resolution(&LinkResolution) -> Option<..>` — the **pure**
  builder: it turns the folded cell links (§1.2, `link_kel`) into the attribute set — distinct
  platform count, per-platform presence flags, `blake3(uid)` hiding commitments (never the uid), and
  the 32-byte account id. `to_credential_pairs()` renders them as ordered `(name, LinkedAttrValue)`
  pairs for the issuer.
- `LinkedAttrValue { Int(u64), Bytes32([u8; 32]) }` — a local, churn-independent mirror of
  `credentials::AttrValue` so the schema type need not link the ZK crate.

### 9.2 The issuer-side flow (design; the thin adapter for when `credentials` is reachable)

The issuer is a dregg node/federation that has **verified K's KEL before attesting**:

1. `verify_export(log, pinned_inception_key)` (§8.1) → a `LinkResolution` (fold).
2. `LinkedPlatformsAttributes::from_resolution(&resolution)` → the attribute set (shipped).
3. Map `to_credential_pairs()` into `credentials::CredentialAttributes` and call
   `credentials::issue(issuer, &schema, holder_id = blake3(K_pk), attributes, issued_at, not_after)`
   (verbatim), with `schema = CredentialSchema::new(SCHEMA_NAME, schema_attributes())`.
4. Presentation is `credentials::present` / `present_anonymous` + `PresentationOptions::disclose` +
   `PredicateRequest::new("platforms_count", Predicate::Gte(2))` — all verbatim.

**One concrete integration gap to resolve at build time (honest, named now):** `credentials::AttrValue`
has variants `Integer / Text / Date / Bool` but **no `Bytes32`**. The 32-byte `account_id` /
`*_uid_commit` attributes therefore ride either as (a) `AttrValue::Text(hex(commit))` — whose fact
term is `blake3(hex(commit))`, an extra hash that issuer and verifier must both apply, still a valid
hiding commitment — or (b) a new `AttrValue::Bytes32([u8;32])` variant added to `dregg-credentials`
(preferred; it makes the disclosed bytes the commitment itself). The `Int` attributes
(`platforms_count`, the `has_*` 0/1 flags) map to `AttrValue::Integer` directly and carry the
predicate path (`platforms_count ≥ 2`).

**Honest ceiling (design §6):** the credential is only as sound as (a) the issuer actually running
`verify_export` + the fold before attesting (mitigated by making that step 1), and (b) the STARK
floor `present` inherits (`project-fri-soundness-reality`). Both are named, not papered over.
