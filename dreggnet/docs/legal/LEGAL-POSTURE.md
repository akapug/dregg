# DreggNet Legal & Policy Posture

> **TEMPLATE — NOT LEGAL ADVICE. RATIFY WITH COUNSEL BEFORE RELYING ON ANY OF IT.**
> This document and the four policy templates beside it (`ACCEPTABLE-USE-POLICY.md`,
> `TERMS-OF-SERVICE.md`, `PRIVACY-NOTICE.md`, `DMCA-AND-TAKEDOWN.md`) were drafted
> by an engineering agent, not a lawyer. They are a *pragmatic minimum* — a
> starting posture and a ratify-ready scaffold for ember + a real attorney to
> review, fill, and adopt. Everywhere a real legal judgment is required, this doc
> says so out loud rather than faking certainty. `[[FILL: ...]]` marks every
> placeholder a human must complete (entity, jurisdiction, designated agent,
> contacts) before publishing.

This is the framing for audit risk **E-1** in `docs/CLOUD-PROVIDER-READINESS.md` —
the #1 launch gate. Today the repo contains **no** ToS, AUP, privacy notice, or
DMCA notice, **no** named operating entity, and **no** abuse contact. As a result:

- there is no contractual basis to remove a tenant's content or terminate them;
- there is no DMCA §512 safe harbor, so the operator is directly liable for hosted
  infringement instead of shielded by notice-and-takedown;
- there is no stated NCMEC/CSAM reporting posture — a legal *obligation*, not a
  choice, the moment user content is hosted;
- there is no privacy basis while user bytes and payment data are processed; and
- Stripe, registrars, and upstream hosts (Hetzner et al.) require an AUP + a
  business identity, and can pull the plug without one.

The goal here is **the minimum honest posture that lets the doors open**, not a
maximalist legal treatise.

---

## 1. The operator-liability reality (the honest framing)

Running a KYC-free, wallet-as-account, public host that serves arbitrary static
sites and runs arbitrary code is, by construction, a magnet for phishing, malware
command-and-control, spam, crypto-mining, DDoS-source workloads, and illegal
content. The technical isolation in DreggNet is genuinely strong (see
`docs/RED-TEAM-FINDINGS-2.md` — host RCE, tenant-escape, and host-resource
exhaustion are bounded). **That is not the exposure.** The exposure is being the
*named operator* of the host. Five hard realities a KYC-free posture does **not**
let you escape:

### 1.1 DMCA safe harbor needs a registered designated agent
US copyright law (17 U.S.C. §512) shields a hosting provider from liability for
user-posted infringing material **only if** the provider (a) has registered a
**designated agent** with the U.S. Copyright Office (the online DMCA Designated
Agent Directory, ~$6 per registration, renew every 3 years), (b) publishes that
agent's contact info, (c) operates a notice-and-takedown process, and (d) adopts
and reasonably implements a **repeat-infringer termination** policy. Miss any of
these and the safe harbor is simply unavailable — the operator is exposed to
direct/contributory infringement liability for whatever a tenant hosts. This is a
**form-filling + process** task, not a judgment call: it is squarely in the
minimum. See `DMCA-AND-TAKEDOWN.md`.

### 1.2 CSAM carries a mandatory reporting duty regardless of KYC
Under 18 U.S.C. §2258A, a US "provider" that obtains **actual knowledge** of
apparent child sexual abuse material (CSAM) on its system has a **mandatory legal
duty to report** to the NCMEC CyberTipline, and to preserve the relevant data.
KYC-free changes nothing here: there is no "we didn't know who they were" defense
to a report obligation once you have knowledge. Knowingly hosting it, or failing
to report once you know, is criminal exposure. The posture is non-negotiable:
**we do not provide a discretion knob on CSAM** — confirmed CSAM is removed and
reported. The AUP and DMCA docs both state this; counsel should confirm the
reporting mechanics and any registration/preservation specifics.

### 1.3 Payment-processor and registrar AUPs are contractual gates
Stripe is the live fiat rail (`demo/stripe-receiver/`, `runbooks/STRIPE-SETUP.md`).
Stripe's Services Agreement and Restricted Businesses list **require** the merchant
to maintain an acceptable-use policy and to not knowingly facilitate prohibited
activity; a KYC-free passthrough to anonymous compute is exactly the profile that
gets accounts reviewed and frozen. Domain registrars and upstream hosts (Hetzner,
Cloudflare) carry their own AUPs that obligate *you* to police *your* tenants.
None of these care that the architecture is verifiable; they care that there is a
named responsible party with a policy and an enforcement arm. The AUP + a working
takedown path is what keeps these relationships alive.

### 1.4 Privacy obligations attach the moment you process personal data
Even with a deliberately minimal-data design (see §4), you still process: Stripe
payment metadata, IP addresses and request logs at the gateway, and any contact
an account voluntarily gives. GDPR (EU/UK visitors) and CCPA/CPRA (California)
attach to that processing and create data-subject rights (access, deletion).
**Caveat that genuinely needs counsel:** whether DreggNet needs an EU/UK
representative, a formal DPA with Stripe, and how the no-storage-delete gap
(`docs/CLOUD-PROVIDER-READINESS.md` S-7 — storage has no TTL/erasure path today)
interacts with a deletion request. The privacy notice states the honest minimum;
the deletion-path engineering gap is tracked separately and must close before
inviting EU users at scale.

### 1.5 "Permissionless" is an architecture choice, not a liability shield
The verifiable rail makes the *substrate* trustless. It does **not** make the
*operator* anonymous or immune. Whoever signs the Stripe account, registers the
domain, and pays the Hetzner invoice is the legally responsible operator. The only
real question is *which legal person that is* — see §3.

---

## 2. The minimum-to-open-doors checklist

The smallest set that turns "a verifiable cloud demo" into "a KYC-free cloud that
survives an upstream's abuse desk and a subpoena." Each item is a launch-blocker.

- [ ] **Name an operating entity** and decide personal-vs-entity (§3). `[[FILL: entity]]`
- [ ] **Adopt the AUP** (`ACCEPTABLE-USE-POLICY.md`) — prohibited content/conduct + enforcement + appeal.
- [ ] **Adopt the ToS** (`TERMS-OF-SERVICE.md`) — service description, as-is/no-warranty (it is alpha/devnet), payment terms, liability cap, termination, governing law. `[[FILL: jurisdiction]]`
- [ ] **Publish the Privacy Notice** (`PRIVACY-NOTICE.md`) — minimal-data posture, Stripe, logs, no-KYC, deletion path + contact.
- [ ] **Register a DMCA designated agent** with the U.S. Copyright Office and publish the notice (`DMCA-AND-TAKEDOWN.md`). `[[FILL: designated agent]]`
- [ ] **Stand up `abuse@` and `security.txt`** — a monitored abuse/legal inbox and an RFC 9116 `/.well-known/security.txt`. `[[FILL: abuse contact]]`
- [ ] **State the CSAM/NCMEC posture** publicly (in the AUP + DMCA docs) and have the internal report mechanism ready before launch.
- [ ] **Wire the enforcement arm to the policy** — the `dreggnet-guard` crate (quotas / rate / suspend / takedown) is built; the AUP must point at it and an operator must be able to execute a takedown. (See §5.)
- [ ] **Confirm a data-subject deletion path exists** (or scope the launch to exclude where it cannot be honored) — the storage erasure gap is real today.
- [ ] **Have counsel ratify all five docs** before they go live. This list is the engineering minimum; the legal sign-off is the gate.

---

## 3. Operator-entity options (ember's decision)

Who is "the operator" is the single most consequential legal choice, and it is
**ember's to make** — this section frames the trade-offs honestly so the decision
is informed. None of these is a recommendation; all assume counsel ratifies.

### Option A — Run it personally (sole proprietor, ember as the named operator)
- **Pros:** zero formation cost/time; fastest path to "doors open"; no corporate
  formalities; fine for a devnet/alpha with a tiny user base.
- **Cons:** **unlimited personal liability** — a tenant's hosted infringement,
  an abuse lawsuit, a Stripe chargeback storm, or a regulatory action reaches
  ember's personal assets directly. There is no veil. For a KYC-free public host
  that *invites* abusive traffic by construction, this is the riskiest posture and
  is hard to recommend past a closed alpha.
- **When it's tolerable:** invite-only / closed devnet with known users, no public
  open signups, while the entity is being formed in parallel.

### Option B — A single-member LLC (US, e.g. Delaware or `[[FILL: state]]`)
- **Pros:** a **liability shield** separating company assets from ember's personal
  assets (if formalities are kept — separate bank account, no commingling); cheap
  and fast to form (days, a few hundred dollars + a registered agent); Stripe and
  registrars are comfortable contracting with an LLC; the entity, not the person,
  is the named operator on every policy and invoice.
- **Cons:** the veil is **not absolute** — it can be pierced if formalities lapse,
  and it does not shield against the member's *own* direct wrongdoing or criminal
  exposure (e.g. knowingly hosting CSAM). Modest ongoing compliance (annual
  filings, separate accounting). A single-member LLC is still "ember's company" in
  practice.
- **When it fits:** the default pragmatic choice for actually opening public doors
  — most of the personal-liability downside of Option A is removed at low cost.

### Option C — A foundation / nonprofit (or a non-US foundation, e.g. Swiss/Cayman)
- **Pros:** strong "this is public infrastructure / a protocol, not my business"
  story; mission-locked governance; common in the crypto/protocol world; can be a
  good fit for the `$DREGG`/DEC token story (separates the protocol from a
  profit-seeking operator) and for a credible neutral-operator narrative.
- **Cons:** **slow and expensive** to set up and run (months, real legal/admin
  spend, ongoing governance + reporting); overkill for an alpha; a foundation does
  **not** by itself absorb operator liability for *running the metal* — you often
  still need an operating company underneath it to hold the Stripe account and the
  servers. Premature for "open the doors this quarter."
- **When it fits:** later-stage, if/when DreggNet wants a credible decentralized /
  public-good governance posture; not the launch-gate answer.

### Option D — "Infrastructure provider, not a publisher" (common-carrier-ish posture)
This is a **framing layered on top of A/B/C, not a separate entity.** The claim:
DreggNet transports and executes tenant-chosen bits and does not select, endorse,
or curate content — closer to a conduit/host than a publisher.
- **Pros:** it is the *correct* and honest characterization, and it is exactly what
  the verifiable rail supports (see §5 — takedown is de-route, the host cannot
  alter a tenant's bytes). It strengthens the DMCA §512 "service provider" framing
  and the AUP's "we enforce a policy, we don't editorialize" story.
- **Cons / honest caveat:** **"common carrier" is a specific legal status DreggNet
  does not have** and should not claim — common-carrier protections (and §230's
  separate protections) are not a magic shield, and §512 safe harbor still requires
  the registered agent + notice-and-takedown + repeat-infringer policy regardless
  of how you frame yourself. Use this as a *posture and a design principle*, not as
  a legal conclusion. Counsel must confirm what can be said.

> **The pragmatic default for actually opening doors:** **Option B (single-member
> LLC)** as the named operator, adopting the **Option D framing** (infrastructure
> provider, enforce-a-policy-don't-publish), with **Option C** held in reserve for a
> later decentralization story. **Option A** only for a closed alpha while B forms.
> This is a starting recommendation for counsel to confirm — not legal advice.

---

## 4. What the minimal-data, KYC-free design changes (it's an advantage)

DreggNet's architecture is, unusually, a **privacy and compliance asset** rather
than only a risk — lean into it honestly:

- **The account is a pseudonymous cap, not an identity.** An account is a
  wallet-held `dga1_` ed25519 capability (`webauth/src/cred.rs`,
  `console/src/scope.rs`). DreggNet does not collect government ID, legal name, or
  KYC by default. **Less data collected = less data to breach, less to subpoena,
  less GDPR/CCPA surface.** This is a genuine data-minimization story — say it
  plainly in the privacy notice.
- **No KYC is a deliberate posture, not an oversight.** Frame it as
  data-minimization-by-design, paired with an *enforcement* model that bounds abuse
  by behavior (the guard) rather than by identity. The bound is "an anonymous
  account is admitted, not trusted" (the guard's conservative default tier).

## 5. What the verifiable rail changes for moderation (a feature, not a tension)

The headline pitch — "the host *cannot* tamper with a byte" — is about
**integrity**, not **availability**, and that distinction is what makes moderation
both *possible* and *better* here:

- **Takedown is de-route / suspend, never byte-tamper.** When the operator acts on
  abuse, it **stops serving or running** the resource (`guard::Guard::suspend_resource`
  flips `SuspensionRegistry::is_suspended`, and the serving path refuses with `403`).
  It does **not** alter the tenant's bytes. So "we can't tamper with your content"
  and "we can remove abusive content from our network" are both true and fully
  compatible. The integrity guarantee is about *what we serve being faithful*, not
  *being obligated to serve everything forever*.
- **Every moderation action is a receipted, auditable governance turn.** Each
  flag/suspend/reinstate/report is sealed into a prev-hash-chained, ed25519-signed
  governance log (`guard/src/governance.rs`); a third party holding the operator's
  governance public key can `verify_chain` the entire moderation history and detect
  any reorder, splice, or forgery. This turns the AUP-enforcement story from "trust
  the host's say-so" into "here is a tamper-evident record of every takedown, why,
  by whom, and when." **That is a stronger abuse-desk and due-process posture than a
  normal host can offer** — it is a feature to advertise, not a liability to hide.
- **The owner always sees the reason.** Suspension reasons are owner-readable
  (`suspension_reason`), so takedown is not a silent black box — it supports the
  AUP's appeal path.

---

## 6. What genuinely needs a lawyer before opening doors (don't fake this)

The following are **not** things this template can resolve. They require counsel
sign-off as part of the launch gate:

1. **Entity formation + the personal-vs-entity decision** (§3) and the actual
   formation paperwork.
2. **Governing-law and dispute-resolution choice** in the ToS (`[[FILL: jurisdiction]]`)
   — arbitration vs courts, venue, class-action waiver enforceability.
3. **DMCA designated-agent registration** mechanics and the repeat-infringer
   policy's defensibility.
4. **CSAM/NCMEC reporting + data-preservation mechanics** — the exact obligations,
   the report channel, and preservation duties for the chosen jurisdiction.
5. **GDPR/CCPA applicability** — whether an EU/UK representative is needed, the
   Stripe DPA, lawful basis, and how the storage-erasure gap (no TTL/delete path
   today, `docs/CLOUD-PROVIDER-READINESS.md` S-7) is reconciled with deletion
   rights *before* inviting EU users at scale.
6. **The "infrastructure provider / not a publisher" framing** (§3.D) — what can be
   said truthfully and what claims (common-carrier, §230) must be avoided.
7. **Token / payment characterization** — whether `$DREGG`/DEC and the Stripe
   on-ramp implicate money-transmission, securities, or sanctions/OFAC screening
   obligations. This is a specialist question and is **out of scope** for these
   templates entirely; flag it for counsel.
8. **Sanctions / export** — whether a KYC-free global host needs any OFAC/sanctioned-
   jurisdiction screening at the payment or service layer.

> **Bottom line.** The engineering minimum is: name an entity, adopt the four
> policies, register the DMCA agent, stand up `abuse@`/`security.txt`, state the
> CSAM posture, and point the AUP at the already-built `dreggnet-guard` enforcement
> arm. The legal minimum is: a lawyer ratifies all of it and resolves the eight
> items above. Neither half is optional before the doors open.
</content>
</invoke>
