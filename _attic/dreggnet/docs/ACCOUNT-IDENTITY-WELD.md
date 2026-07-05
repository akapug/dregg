# Account-Identity Weld — rotation, recovery, revocation for the live cap-account

> The launch-blocker `docs/KEY-RECOVERY-AND-KERI.md` found: the live DreggNet
> `dga1_` cap-account is a **bearer macaroon whose identity is its own tail**, so
> losing the key loses the account forever — no rotation, no recovery, no
> revocation. The fix is *already built, proven, and deployed* in the breadstuffs
> substrate (KERI pre-rotation via `KeyRotationGate`, HINTS social recovery via
> `ThresholdSigVerifier`, `Effect::RevokeCapability`) — but attached to the
> **identity cell**, a different object than the `dga1_` credential the cloud
> authenticates with. This document is the weld: it re-anchors the account to the
> substrate identity cell **by depending on the real substrate**, now that the
> AGPL firewall is dissolved (ember owns the copyright; DreggNet goes AGPL).

The one-sentence shape:

> **The account is a stable, key-derived identity-cell id; the `dga1_`
> credential is a short-lived, revocable *session token* under it; rotation /
> recovery / revocation happen as real turns on the identity cell, and because
> the account subject IS that cell's id, the account and all its resources
> survive every one of them.**

---

## 0. Tiers

| Tier | What | Ships | Depends on |
|---|---|---|---|
| **0** | Compromise response: a **revocation deny-set** + **default short expiry** in `webauth` | now, DreggNet-local | nothing new |
| **1** | The table-stake: **re-anchor** the account subject to a key-derived identity-cell id; **rotate / recover / revoke** as real substrate turns | the weld | the real breadstuffs substrate (`dregg-types`, the executor, `KeyRotationGate`, the membership verifier, `RevokeCapability`) |

---

## 1. Tier 0 — compromise response (shipped, `webauth`-local)

Closes "stolen token, can't kill it" with no substrate dependency.

### 1.1 Default short expiry

`grant::mint_session` stamps a `NotAfter` caveat at `issued_at + ttl_secs`
(default `config::DEFAULT_SESSION_TTL_SECS = 24h`, overridable via
`DREGG_WEBAUTH_SESSION_TTL`). A leaked bearer token **self-expires** within a
day; the offline verifier already enforces `NotAfter` against its clock
(`cred::Pred::NotAfter`, fail-closed when no clock is bound). Re-issued on each
login. *(Proof: `mint_session_self_expires`.)*

### 1.2 Revocation deny-set (the cloud-side `Effect::RevokeCapability`)

`WebAuthConfig.revoked: BTreeSet<String>` is consulted in `decide` **after** the
credential would otherwise admit. An entry refuses a credential whose:

- **tail commitment hex** (`cred::Credential::tail_hex`) matches → kills exactly
  one leaked session token; or
- **account subject** (`subject_of`) matches → kills *every* session for a
  compromised account (the proactive "rotate-out" companion).

Offline-distributable and fail-closed: a signed list the forward-auth service
loads (`DREGG_WEBAUTH_REVOKED` inline, `DREGG_WEBAUTH_REVOKED_FILE` a path; `#`
comments, comma/whitespace/newline separated; lowercased for canonical
tail-hex matching). *(Proofs: `revoked_by_tail_is_refused`,
`revoked_by_subject_kills_every_session`, `revoked_list_parsing_round_trip`.)*

Tier 0 mitigates compromise but does **not** give continuity-preserving
rotation or loss recovery — for those, the account id must stop being the
credential tail. That is Tier 1.

---

## 2. Tier 1 — the re-anchor (the root cause fix)

### 2.1 The account id IS the substrate identity-cell id

The root cause is `subject_of = hash(credential tail)`: the subject is a function
of the *credential*, so a different credential is a different account. The fix
(per `breadstuffs/docs/deos/SESSION-LOGIN.md` §2.2) is a **self-certifying,
key-derived** account id:

```
account_id = CellId::derive_raw(&inception_pubkey, &ACCOUNT_ROOT_TOKEN)
           = blake3::derive_key("dregg-cell-id-v1", inception_pubkey ‖ ACCOUNT_ROOT_TOKEN)
```

We **depend on the real substrate** for this — `dregg_types::CellId::derive_raw`,
the exact function the breadstuffs executor addresses cells with (`webauth`'s
`account_id` module path-deps `breadstuffs/types`, the LIGHT substrate crate:
serde + blake3 + ed25519, no Lean/prover closure). So a DreggNet account and the
rotatable substrate **identity cell** the control plane provisions for it are the
**same principal, byte-for-byte**. `ACCOUNT_ROOT_TOKEN = blake3("dreggnet:account-identity:v1")`
is the published domain separator binding the two; the control plane MUST
provision the identity cell under the same token. *(Proof:
`account_id::tests::account_id_is_the_substrate_cell_id`.)*

### 2.2 The INCEPTION key, not the current key (the KERI invariant)

The id is derived from the account's **inception** public key — the first key it
was created with — and is then *fixed for life*. Key rotation changes the
*current* authoritative key (the one a session is minted under) but NEVER the
inception-derived id, exactly as a KERI AID is its inception id and continuity is
carried by the rotation chain (the KEL), not by re-deriving from the current key.
Deriving from the current key would change the id on every rotation and defeat
the purpose. (This is why the substrate's `rotate_current_keys_irrelevant` /
`rotChain_pinned_by_commitments` are the right backbone: the *commitments*, not
the live keys, pin the identity.)

### 2.3 The credential becomes a session token under the account

`grant::mint_session` mints a `dga1_` carrying, on its root block:

1. an `acct = <account-id-hex>` first-party caveat — an **issuer-vouched
   annotation** (the block is signed by the root chain, so it cannot be
   tampered), NOT an access gate. `decide` binds `acct` into the verification
   context from the credential's own claim, so the caveat is self-consistent and
   `verify` decides on the **cap**, not the subject label;
2. the cap grant (`cap` `AnyOf`, unchanged);
3. the Tier-0 `NotAfter` expiry.

`subject_of` returns `dregg:<account-id-hex>` when the `acct` caveat is present.
So **every re-issue of a session — a fresh login, a key rotation, a guardian
recovery — yields the SAME subject**, and the account survives. *(Proofs:
`reanchored_subject_is_stable_across_reissue`,
`attenuated_session_keeps_account_subject`,
`distinct_accounts_distinct_subjects`.)*

The offline forward-auth verifier stays a **pure session-credential checker** (it
verifies `dga1_` sessions under the configured root pubkey, as today). The
rotation/recovery/revocation logic — which changes *who controls the account* —
runs on the substrate, off the offline verify path.

### 2.4 Backward compatibility & migration

`subject_of` falls back to the **legacy tail-commitment subject**
(`dregg:<hex(tail)[..16]>`) for any credential with no `acct` caveat, so
already-issued credentials keep working unchanged (proof:
`legacy_credential_keeps_tail_subject`). Migration is non-breaking because no
consumer parses the subject — `org`, `dregg-secrets`, `console`, `guard`, and
`billing` all treat it as an **opaque string key** (verified census, 2026-06-30).
But the subject *is* embedded in durable, receipt-chained records (org
memberships, secrets audit, billing invoices), so for an **existing** account the
control plane re-issues the session with `acct` set to the value that keeps
`subject_of` returning the account's *current* subject string — i.e. the legacy
16-hex tail-subject is **grandfathered** as that account's stable id at migration
time (the `acct` caveat can carry any stable string; `subject_of` just prepends
`dregg:`). New accounts get the full 64-hex identity-cell id. Either way the
subject is henceforth *stable across re-issue*, which is the property that was
missing.

---

## 3. Rotate / Recover / Revoke — real turns on the real substrate

These run in the **control plane / a dregg-backed issuer service** that depends on
the real substrate (the executor, the deployed gate, the deployed verifier) — no
porting. The offline forward-auth verifier is untouched. Each is a deployed,
machine-proven mechanism the weld simply *drives* for a DreggNet account:

### 3.1 ROTATE — `KeyRotationGate` (KERI pre-rotation)

The account's authoritative key is the identity cell's key set; rotation is the
deployed `rotate` verb (`AgentRuntime::rotate_identity`, gate
`StateConstraint::KeyRotationGate` in `cell/src/program/eval.rs`, proven in
`metatheory/Dregg2/Apps/PreRotation.lean`): exhibit the pre-committed
next-keys preimage, install it, re-commit forward, wait out cooling. The
identity-cell id is continuous; the old key is dead; a thief holding the *current*
key has gained nothing toward rotating (`rotate_current_keys_irrelevant`). On
rotation the issuer re-mints the `dga1_` session under the new key with the
**same `acct`** — same subject, same account. *(Substrate e2e:
`sdk/tests/identity_prerotation_e2e.rs`, extended for the account scenario in
`sdk/tests/dreggnet_account_identity_e2e.rs`.)*

### 3.2 RECOVER — the HINTS guardian quorum

A lost-key account recovers via an M-of-N guardian quorum that *authorizes a
rotation* to a fresh key the user picks now (`ThresholdSigVerifier` →
`hints::verify_aggregate`, `turn/src/executor/membership_verifier.rs`; non-lock-in
floor `metatheory/Polis/PolisRecoveryFloor.lean`). No custodian, no "reset"
button, no secret reconstruction. The identity cell (the durable principal) is
unchanged, so every cell it owns — every DreggNet resource — is still its own. A
sub-threshold or wrong-committee quorum is **refused** by the executor.
*(Substrate e2e: `sdk/tests/identity_social_recovery_e2e.rs`.)*

### 3.3 REVOKE — `Effect::RevokeCapability` + rotate-out

On compromise: kill the leaked sessions (Tier 0 deny-set, immediate at the edge)
**and** rotate the account key (§3.1) so the thief's key is dead, then revoke any
capabilities the thief was delegated (`Effect::RevokeCapability`,
`turn/src/action.rs`; `KeyLeak.lean` `revoke_kills_leak_immediate` at n=1). The
blast radius is bounded to the attenuation-downward-closure and cannot amplify
or mint value (Σδ=0).

---

## 4. The honest seam

What is a **real depend-on-substrate weld** here, today:

- ✅ The account id is the real `dregg_types::CellId::derive_raw` — `webauth`
  depends on the real substrate crate; byte-identical to the executor's cell
  addressing. Proven.
- ✅ The re-anchored subject (stable across re-issue) + Tier-0 revoke/expiry —
  built and proven in `webauth`.
- ✅ Rotate / recover / revoke are the **deployed** substrate mechanisms, proven
  `#assert_axioms`-clean and exercised end-to-end on the **real executor** in
  `breadstuffs/sdk/tests/` — extended here for the DreggNet account scenario
  (the account anchored to the identity-cell id survives a rotation with its
  owned resources intact; recovers via the guardian quorum; a compromised key is
  revoked).

What remains a **named seam** (not unbuilt cryptography — wiring):

- The control-plane **provisioning + issuer** loop that, per account, (a)
  provisions the identity cell under `ACCOUNT_ROOT_TOKEN` at signup, (b) on a
  rotation/recovery turn committing, re-mints the `dga1_` session under the new
  key with the same `acct`. The mechanism (the SDK calls) is proven and tested;
  the production loop that calls them on the live control plane is the
  integration wire. It belongs in the dregg-backed issuer (which may take the
  AGPL substrate dependency, like the existing `dregg-verify` lane), keeping the
  offline forward-auth verifier a pure session checker.

The launch-blocker is closed by **depending on the real substrate**: the account
is a rotatable identity, recoverable via guardians, with a leaked key revocable —
no new cryptography, the mechanism is the substrate's, proven and deployed.
