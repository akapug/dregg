# Cap-Account Key Recovery & the KERI Work — what's built, what's wired, what's a gap

> The launch-relevant question, stated plainly: DreggNet ships the identity front
> office — **cap-accounts** (`dga1_` subjects), **orgs/teams** (roles = cap
> attenuations), **per-account secrets**, the **console**. For a cloud where "the
> chain is your account," the unaddressed table-stake is: **what happens when a
> customer's cap-account key is LOST or COMPROMISED?** Lose the key → lose the
> cloud, with no recovery. This document answers: does dregg already have the
> answer in its KERI-adjacent work, or is it a gap?

**The one-sentence verdict.** dregg has a *complete, machine-proven, executor-deployed*
key-rotation / social-recovery / compromise-containment system — but it is built on
the **identity-cell** object in the breadstuffs substrate, and it is **NOT wired** to
the **`dga1_` bearer cap-account** the DreggNet cloud actually authenticates with.
Today, for a live customer account, rotation / recovery / compromise-response are a
**GAP**. The good news: the answer is built and proven; the work is a *weld*, not a
research build — but a non-trivial one, because the two systems model identity with
two different objects and DreggNet deliberately firewalls itself from the substrate's
dependency closure.

---

## 1. What the live DreggNet cap-account actually is

A DreggNet cap-account is a **bearer macaroon**, not a key-rotatable identity. It is a
faithful, wire-compatible *port* of the breadstuffs `dregg-auth::credential` scheme
(`webauth/src/cred.rs:1-27`), ported inline rather than depended-on so the workspace
"builds offline + pulls no AGPL dregg git" (`webauth/Cargo.toml:7-13`).

- **The credential** (`dga1_…`) is a nonce + an append-only ed25519 caveat-block
  chain. The root block verifies under the **issuer's** public key; each block names
  the verifying key the next block signs under (`webauth/src/cred.rs:14-26`,
  `CREDENTIAL_PREFIX = "dga1_"` at `:42`). It is the biscuit public-key delegation
  chain (`Dregg2.Authority.BiscuitGraph`).
- **Verification is offline, fail-closed, and against a single configured root
  pubkey** — there is no account database, no session table, no network call
  (`webauth/src/lib.rs:81-125`, `decide`). "login = paste / wallet-sign a `dga1_`
  credential" (`webauth/src/server.rs:9`).
- **The account *subject* is derived from the credential, not from a stable key.**
  The credential carries no explicit subject field, so the subject is a short hash of
  its **tail commitment**: `dregg:<hex(tail)[..16]>` (`webauth/src/lib.rs:127-133`,
  `subject_of`). **This is the load-bearing fact for recovery:** the subject is a
  function of the credential chain, so a *different* credential is a *different*
  subject — i.e. a different account.
- **Authority is narrowed only by attenuation + expiry.** `attenuate_caps` appends a
  confining caveat (can only shrink reach, `webauth/src/cred.rs:364-378`); `mint_caps`
  can stamp a `NotAfter` expiry caveat (`webauth/src/grant.rs:35-45`). There is no
  amplification and no removal API — but also no continuity-preserving *rotation*.

Everything a customer owns is scoped by that subject. The console shows a resource iff
`resource.owner() == authenticated_subject` (`console/src/model.rs`, the `Owned`
trait; `console/src/scope.rs`). Orgs lift this one level — an org-owned resource's
`owner` is the `org:<16hex>` id and members are `dga1_` subjects
(`org/src/resource.rs:3-13`, `org/src/lib.rs:20`). Per-account secrets are sealed
under an account-scoped KEK keyed by the subject (`dregg-secrets/src/kms.rs`,
`dregg-secrets/src/console.rs:11-12`). DEC billing is per-subject
(`billing/src/lib.rs:38-40`). Account standing/qu/suspension is per-account
(`guard/src/`).

### Blast radius — lose/leak the `dga1_` key → lose/expose

| Lost the credential (and its proof key) | Leaked the credential (bearer copy) |
|---|---|
| Permanently locked out of the account | Anyone holding the bytes can act as you |
| All sites, servers, agents, domains, storage buckets (`console` views, owner-scoped) | …until a `NotAfter` caveat (if any) expires — and `decide` checks **no revocation set**, so you cannot proactively kill it |
| All per-account secrets (sealed under the account KEK, `dregg-secrets`) | The thief reads/writes every cap the token grants |
| Full DEC balance + billing identity (`billing`) | They can spend the DEC balance |
| Org memberships + standing (`org`, `guard`) | They act under your org roles |

There is **no rotation, no recovery, no revocation path anywhere in DreggNet**: a
grep for `next_keys_digest`/`KeyRotationGate`/`pre-rotation`/`social.recovery`/
`guardian`/`rotate` over the Rust tree returns nothing (the only `revoke` hit is a pun
in `org/src/cap.rs:173`). DreggNet does **not** depend on the substrate's identity
crates — only `demo/stripe-receiver`, an optional `polyana` feature, and an optional
`durable` pg-backend reach into breadstuffs at all; `webauth` is a self-contained
port (`webauth/Cargo.toml:7-13`). So the substrate's rotation machinery is not merely
unwired — it is firewalled out of the default closure by design.

---

## 2. What dregg *has already built* (the KERI work) — and where it lives

The substrate answer is real, machine-checked, and **deployed in the real executor**.
It operates on the **identity cell**, a different object than the `dga1_` credential.

### 2a. KERI pre-rotation — formalized AND deployed

- **Lean kernel semantics** — `metatheory/Dregg2/Apps/PreRotation.lean`. Every
  key-state event commits the digest of the *next, unexposed* key set
  (`next_keys_digest`); a rotation must *exhibit the preimage* of the committed digest
  (`rotate_exhibits_preimage`, `:144`). The keystones, all `#assert_axioms`-clean
  (only `propext`/`Classical.choice`/`Quot.sound`, `:586-605`):
  - `rotate_current_keys_irrelevant` (`:170`) — admission is `rfl`-independent of the
    *current* keys: a thief who exfiltrates every current signing key has gained
    **literally nothing** toward rotating.
  - `rotate_compromise_resistant` (`:180`) — under the named hash-CR carrier
    `KeySetCR`, any presented key set other than the pre-committed one is refused (an
    admitted forgery would *be* a hash collision).
  - `rotChain_pinned_by_commitments` (`:225`) — the public commitment stream pins the
    *entire* key history; no alternative admitted history exists. This is KERI's
    chained `rot`/KEL, as a theorem.
  - `rotateWriteCooled` (`:449`) — the production shape: preimage gate × a cooling
    time-lock (`TemporalAtom.cooledSince`) × the caveat-gated guarded write, so a
    contested/coerced rotation is **slow and visible** to the council before it lands.
- **Deployed executor enforcement** — `StateConstraint::KeyRotationGate`
  (`cell/src/program/types.rs:1338`, evaluated `cell/src/program/eval.rs:881-974`,
  `hash_preimage32`). The rotate verb is a real guarded write on the live record
  kernel.
- **SDK + end-to-end tests** — `sdk/src/identity.rs` (the `next_keys_digest` /
  `KeyRotationGate` rotate verb, `COUNCIL_COMMIT_SLOT`, `members_commitment`);
  `sdk/tests/identity_prerotation_e2e.rs` (negative tests: the executor rejects
  *well-signed-by-the-current-key* rotations — current keys contribute nothing) and
  `sdk/tests/identity_social_recovery_e2e.rs`.

### 2b. Social recovery — guardian quorum authorizes a rotation (no custodian)

- **Architecture** — `docs/deos/RECOVERY-SYSTEM.md`. "You cannot lose your own OS":
  when every device key is lost, recovery is an **M-of-N guardian quorum that
  authorizes a key *rotation* to a NEW key the user picks now** — never a custodian,
  never a "reset my account" button, never secret reconstruction. It uses **DKG'd
  weighted-threshold BLS (HINTS) + KERI pre-rotation**, *not* Shamir (Shamir
  reconstructs the OLD secret at a single point of compromise; the threshold scheme
  *authorizes a forward-secure rotation*, §1).
- **Deployed verifier** — `ThresholdSigVerifier` →`hints::verify_aggregate`
  (`turn/src/executor/membership_verifier.rs`); a sub-threshold quorum is **refused**
  by the host-pinned floor (`sub_threshold_quorum_refused`), a wrong-committee quorum
  is refused (`wrong_committee_quorum_refused`). WHO (the quorum authorizes
  `set_state`) and HOW (the `KeyRotationGate` mechanics) are orthogonal teeth, both
  must pass. The whole recovery is **one cap-gated, light-client-verifiable witnessed
  turn** (§4).
- **Non-lock-in floor, bound to the deployed verb** —
  `metatheory/Polis/PolisRecoveryFloor.lean`: `recoverableNow` is a *decidable, public*
  predicate — control is recoverable iff some published roster member can be presented
  as an admissible rotation — proven over the *live* `rotateStep`, not a toy.

### 2c. Compromise containment + revocation — already proved

- `docs/deos/ADVERSARY-KEY-LEAK.md` + `metatheory/Metatheory/KeyLeak.lean`: a leaked
  key is the *opaque controller* `polis_safety` was already proven against. The blast
  radius is exactly the attenuation-downward-closure of the principal's own c-list
  (`leak_blast_no_amplify` — no amplification, no new targets); it cannot mint value
  (Σδ=0); and it is **killed by revocation**, bounded in time
  (`Revocation.eventual_bounded_revocation`), *immediate* at n=1
  (`revoke_kills_leak_immediate`). The revoke effect is first-class:
  `Effect::RevokeCapability` (`turn/src/action.rs:970`).
- **The D-side dual** — `metatheory/Metatheory/ResharingChain.lean` +
  `docs/deos/RESHARING-CHAINS.md`: forward-secure *committee* secrets (proactive
  resharing, `federation/src/dkg.rs::reshare_deal`) so the *guardian set itself* can be
  rotated without revealing past secrets. (Relevant once recovery is wired; not on the
  critical path for a single-account rotation.)

### 2d. The login design that already names the weld

`docs/deos/SESSION-LOGIN.md` §2 is, in effect, the spec for binding the two systems:
"login = receiving your root capability; a session = the cap-tree you hold." Its §2.1
**already names two admission modes**: challenge-response (possession of the key) **and
KERI pre-rotation** ("a returning principal proves continuity: the presented current key
hashes to the previously-committed `next_keys_digest` … this survives key rotation
without re-deriving identity — recovery, not just authentication"). Critically §2.2:
`root_cell = CellId::derive_raw(&pubkey, &ROOT_TOKEN)` — **identity is a derivation, not
a credential tail**: "lose the manager's storage and a returning user re-derives to
exactly the same cell." That stable-id property is *precisely* what the DreggNet
`dga1_`/`subject_of(tail)` model lacks.

---

## 3. The KERI ↔ dregg correspondence

dregg independently reinvented most of KERI; KERI's discipline names the one thing the
live cloud account is missing.

| KERI concept | dregg's already-built primitive | Status for the live cloud |
|---|---|---|
| Self-certifying AID (identifier *is* the key) | `CellId::derive_raw(pubkey, token)` (`types/src/lib.rs:701`) — identity is the content-address of the key | **Reinvented**, but the **cloud account uses a different id** (`dregg:<credential-tail>`), which is *not* key-derived → the rotation discipline can't attach |
| Key Event Log (KEL), hash-chained signed events | the `next_keys_digest` register's receipt-chained history (`PreRotation.lean:351-421`); the macaroon block chain on the credential side | **Reinvented** (identity cell). The `dga1_` credential chain is an *attenuation* chain, not a *rotation* KEL |
| Pre-rotation (commit next key's hash; current key can't rotate) | `KeyRotationGate` + `rotate_current_keys_irrelevant` | **Built + proven + deployed** — on the identity cell, **not** the `dga1_` account |
| Witnesses + receipts | every turn emits a `TurnReceipt`; the federation/fed-QA quorum | **Reinvented** |
| Duplicity detection (catch a lying controller) | the Rust↔Lean differential + the lying-operator detection; `EquivocationEvidence` (`federation/src/dkg_ceremony.rs`) | **Reinvented** |
| No-blockchain end-verifiability (verify with the verifier, not a chain) | "running only the verifier" — light-client unfoolability (`RECOVERY-SYSTEM.md §4`) | **Reinvented + stronger** (the recovery itself is a verifiable witnessed turn) |
| **Forward-secure rotation as the recovery primitive** | the social-recovery quorum *authorizes a rotation* (`RECOVERY-SYSTEM.md`) | **What KERI's discipline adds to the cloud:** the live `dga1_` account has *no* rotation event at all, so it has no recovery and no compromise response |

**Where KERI adds something dregg's *cloud* lacks (not the substrate):** the substrate
already has all of KERI. The *cloud account* has only the macaroon attenuation chain —
which is KERI's *delegation* story but **not** its *rotation/pre-rotation* story. The
gap is exactly the part of KERI the substrate built and the cloud didn't wire:
key continuity across rotation, anchored to a self-certifying (key-derived) id.

---

## 4. The gap assessment — rotation / recovery / compromise, for a live account

| Capability | Substrate (identity cell) | Live DreggNet cap-account (`dga1_`) |
|---|---|---|
| **(a) Rotation** — new key, old retired, identity continuous | **BUILT + PROVEN + DEPLOYED** — `KeyRotationGate`, `cell/src/program/eval.rs:888`, `PreRotation.lean`, e2e `sdk/tests/identity_prerotation_e2e.rs` | **GAP.** No rotation. The subject *is* a function of the credential (`subject_of`, tail hash), so a new credential = a new subject = a new account. No continuity. |
| **(b) Loss recovery** — regain account via guardians / pre-committed key | **BUILT + PROVEN + DEPLOYED** — HINTS quorum + `ThresholdSigVerifier`, `RECOVERY-SYSTEM.md`, e2e `sdk/tests/identity_social_recovery_e2e.rs`; non-lock-in floor `PolisRecoveryFloor.lean` | **GAP.** No guardians, no recovery cap, no pre-rotation escrow. The only "recovery" is the issuer re-minting — which is a *trusted custodian* (the anti-pattern the substrate work exists to avoid) and still cannot regain a *stable* subject. |
| **(c) Compromise response** — revoke + rotate before the thief drains it | **BUILT + PROVEN** — `Effect::RevokeCapability` (`turn/src/action.rs:970`), `KeyLeak.lean` `revoke_kills_leak` (n=1 immediate) | **GAP.** `webauth::decide` checks no revocation set; a leaked `dga1_` is valid until any `NotAfter` caveat expires. No proactive kill, no rotate-out. |

**Honest framing.** This is not "dregg can't do this." dregg *does* do this, completely,
in the substrate. It is an **integration gap**: the cloud's authentication object is a
bearer macaroon whose identity is its own tail, and the rotation/recovery machinery is
attached to a *different* object (a key-derived identity cell) that the cloud never
adopted — by a deliberate dependency firewall (`webauth/Cargo.toml:7-13`).

---

## 5. The minimal path — account recovery as a cloud table-stake

Two tiers. Tier 0 is cheap, DreggNet-local, and closes the *compromise* hole this week.
Tier 1 is the real table-stake (rotation + recovery) and is a *weld* of proven parts,
but a non-trivial one because of the object mismatch and the AGPL/offline firewall.

### Tier 0 — compromise response, no substrate dependency (days)

Closes "stolen token, can't kill it" without touching breadstuffs:

1. **Make expiry the default, short.** Mint cap-account credentials with a `NotAfter`
   caveat (`webauth/src/grant.rs:43`) by default and re-issue on login, so a leaked
   token self-expires. (Bounds the window; does not enable proactive kill.)
2. **Add a revocation check to `decide`.** A published deny-set keyed by credential
   tail / subject, consulted in `webauth/src/lib.rs:decide` after verify. Offline-
   distributable (a signed list the forward-auth service loads), fail-closed.
   This is the cloud-side analogue of `Effect::RevokeCapability` and gives the
   operator/customer a "kill this credential now" button.

Tier 0 mitigates compromise but **does not** give continuity-preserving rotation or
loss recovery — for those the account id must stop being the credential tail.

### Tier 1 — rotation + recovery (the table-stake): anchor the account to an identity cell

The root cause is `subject_of` = `hash(credential tail)`. The fix is the
`SESSION-LOGIN.md §2.2` design: **make the account subject a key-derived, rotatable
identity-cell id, and make the `dga1_` credential a *session* re-minted on each
rotation** rather than the identity itself.

1. **Self-certifying account id.** Define the account subject as
   `CellId::derive_raw(account_pubkey, …)` (key-derived, stable) instead of the
   credential tail. Now a rotation that changes the key but preserves the cell id keeps
   the same subject → org memberships, secrets KEK, DEC balance, owned resources all
   survive a rotation. (This is the single highest-leverage change.)
2. **Rotation = the deployed KERI gate.** Bind the account's authoritative key to an
   identity cell's `next_keys_digest` register and rotate via `KeyRotationGate`
   (`cell/src/program/eval.rs:888`, proven in `PreRotation.lean`). On rotation, re-mint
   the `dga1_` session credential under the new key. Pre-rotation gives the
   compromise-resistance for free: a stolen *current* key cannot rotate.
3. **Recovery = the deployed guardian quorum.** Wire the HINTS
   `ThresholdSigVerifier` recovery flow (`turn/src/executor/membership_verifier.rs`,
   `RECOVERY-SYSTEM.md`, e2e-tested) so a lost-key customer recovers via an M-of-N
   guardian quorum authorizing a rotation to a fresh key — no custodian, witnessed,
   light-client-verifiable.

**The honest cost.** Tier 1 needs the identity-cell + federation machinery in the loop,
which collides with `webauth`'s deliberate "offline + AGPL-free default closure"
discipline (`webauth/Cargo.toml:7-13`). The natural resolution: run the
rotation/recovery turns in the **control plane / a dregg-backed issuer service** (which
*may* take the AGPL dregg dependency, like `demo/stripe-receiver` and the optional
`polyana`/`durable` lanes already do), while the offline forward-auth verifier stays a
pure credential checker — it just verifies `dga1_` *sessions* whose issuing key is now
a rotatable identity cell instead of a static root. The proofs, the executor gate, and
the e2e tests already exist; the build is the *binding*, not the mechanism.

---

## 6. Bottom line for launch

- **Do we have customer-account key rotation / recovery / compromise-response today?**
  **No — all three are a GAP for the live `dga1_` cap-account.** No rotation, no
  recovery, no revocation in DreggNet (`webauth`/`org`/`console`/`guard`); a lost key
  loses the whole account, a leaked key is valid until expiry.
- **Does dregg have the answer?** **Yes, fully — but attached to the wrong object.**
  KERI pre-rotation, HINTS social recovery, and revocation containment are
  machine-proven (`#assert_axioms`-clean) *and* deployed in the real executor with
  end-to-end tests (`cell/src/program/eval.rs:888`, `sdk/tests/identity_*_e2e.rs`,
  `turn/src/executor/membership_verifier.rs`) — on the **identity cell**, not the
  **`dga1_` bearer credential** the cloud authenticates with.
- **Minimal path.** Tier 0 (short-expiry + a revocation deny-set in `webauth::decide`)
  closes compromise-response in days, DreggNet-locally. Tier 1 (re-anchor the account
  subject to a key-derived identity-cell id, rotate via the deployed `KeyRotationGate`,
  recover via the deployed guardian quorum, run those turns in the control plane) is
  the real table-stake — a *weld of proven parts*, gated by the object re-anchoring and
  the dependency-firewall decision, not by any unbuilt cryptography.

( ◕‿◕ )  *the chain is your account — so the account must be able to turn the page.*
