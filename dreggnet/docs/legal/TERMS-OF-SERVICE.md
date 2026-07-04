# DreggNet Terms of Service

> **TEMPLATE — RATIFY WITH COUNSEL BEFORE PUBLISHING.** Drafted by an engineering
> agent, not a lawyer. This is a *minimum* ToS scaffold for an **alpha / devnet**
> verifiable cloud. `[[FILL: ...]]` marks placeholders. Governing law, liability
> caps, and dispute resolution in particular require legal review.

**Operator:** `[[FILL: legal entity name]]` ("DreggNet", "we", "us", "our")
**Effective date:** `[[FILL: date]]`
**Contact:** `[[FILL: support@dreggnet.example]]`

These Terms govern your access to and use of DreggNet. By creating an account
(capability credential) or using the service, you agree to these Terms, the
[Acceptable Use Policy](./ACCEPTABLE-USE-POLICY.md), the
[Privacy Notice](./PRIVACY-NOTICE.md), and the
[DMCA & Takedown Policy](./DMCA-AND-TAKEDOWN.md), each incorporated by reference.
If you do not agree, do not use DreggNet.

---

## 1. The service

DreggNet is a permissionless, KYC-free verifiable cloud that lets you deploy and
host static sites and web apps, run code and durable agents, store objects, bind
custom domains, and run persistent servers, billed by metered usage. The
underlying [dregg](https://github.com/emberian/dregg) substrate provides a
verifiable record of what was promised, paid, and owed; DreggNet operates the
infrastructure that runs and serves your workloads.

**DreggNet is an infrastructure and execution provider.** We transport, host, and
execute the content and code *you* choose. We do not pre-screen, select, endorse,
or curate tenant content, and the service is not a publisher of your content.

## 2. Accounts and capabilities

- An account is a **capability credential** (a wallet-held `dga1_` ed25519
  caveat-chain), not an identity. We do not require KYC by default.
- **You are solely responsible for safeguarding your credential.** Possession of
  the credential is control of the account; anyone holding it can act as you. We
  cannot recover a lost credential and are not liable for loss arising from a
  leaked, lost, or shared credential.
- Capabilities may be attenuated and delegated. You remain responsible for all
  activity under your account and any capability you delegate.
- You must be legally able to form a contract and not barred from the service.

## 3. Alpha / devnet status — AS-IS, NO WARRANTY

**DreggNet is provided on an alpha / development-network ("devnet") basis.** It is
experimental, may change or break, and is offered **"AS IS" and "AS AVAILABLE"
without warranties of any kind**, whether express, implied, or statutory,
including (without limitation) merchantability, fitness for a particular purpose,
non-infringement, availability, durability, or uninterrupted/error-free operation.

- **No durability or data-loss guarantee.** Portions of the data plane are not yet
  fully durable across restarts; **do not store anything you cannot afford to
  lose.** Keep your own backups.
- **No uptime / SLA** is offered during alpha. Service may be suspended, degraded,
  or discontinued at any time without notice.
- We may add, change, deprecate, or remove features at any time.

To the maximum extent permitted by law, you use DreggNet at your own risk.

## 4. Payment terms ($DREGG / DEC and fiat)

- **Metered, usage-based billing.** Charges accrue per resource (compute,
  bandwidth, storage, uptime) per the published rates `[[FILL: rate card / pricing URL]]`.
  Some early-era usage may be subsidized or free; subsidy may be withdrawn at any
  time on notice.
- **On-substrate payment** settles in `$DREGG` / DEC through the dregg Payable rail
  as a verifiable, conserving transfer; non-payment lapses the relevant lease and
  the resource is reaped (stops serving/running).
- **Fiat on-ramp via Stripe.** Card payments are processed by **Stripe**; your card
  data is handled by Stripe under its terms and privacy policy, not stored by us
  (see [Privacy Notice](./PRIVACY-NOTICE.md)). You authorize charges for usage you
  incur.
- **Prepaid / lease model.** Resources run only while their lease is funded. You are
  responsible for keeping a sufficient balance; we are not liable for a resource
  reaped due to an unfunded or lapsed lease.
- **Taxes.** Stated prices exclude taxes; you are responsible for any applicable
  taxes other than taxes on our net income.
- **Refunds / disputes.** `[[FILL: refund policy — default: usage charges are
  non-refundable except as required by law; disputes to support@ first]]`.
  Chargebacks initiated without first contacting us may result in suspension.

## 5. Your content and conduct

- **You retain ownership** of content and code you provide. You grant us only the
  limited license to host, store, transmit, execute, and serve it as needed to
  operate the service for you, and to comply with law.
- You represent that you have all rights to your content and that your use complies
  with the [Acceptable Use Policy](./ACCEPTABLE-USE-POLICY.md) and applicable law.
- **Integrity, not endorsement.** DreggNet's verifiable rail means we serve your
  bytes faithfully and **cannot alter them**; it does **not** mean we endorse them
  or must serve content that violates the AUP.

## 6. Suspension and termination

- We may **suspend, throttle, de-route, or terminate** any resource or account that
  violates the AUP, threatens the service or others, is required to be removed by
  law, or risks our upstream/payment relationships — graduated where practical
  (flag → throttle → suspend), immediate where necessary (e.g. CSAM, active abuse).
- Enforcement actions are executed through the [`dreggnet-guard`](../../guard/)
  layer and recorded as **receipted, auditable governance turns**; suspension
  reasons are owner-readable. Appeals follow the AUP §5 process.
- **Takedown is de-route / suspend, never byte-tampering** — consistent with the
  integrity guarantee in §5.
- You may stop using the service at any time; you remain responsible for charges
  already incurred. We may discontinue the service (or your access) with or without
  cause; we will give reasonable notice where practical.

## 7. Limitation of liability

To the maximum extent permitted by law: DreggNet and its operator are **not liable
for any indirect, incidental, special, consequential, exemplary, or punitive
damages**, or for lost profits, revenue, data, or goodwill, arising from or related
to the service. **Our total aggregate liability** for any claim is limited to the
**greater of the amounts you paid us for the service in the `[[FILL: 3]]` months
before the claim, or `[[FILL: USD 100]]`.** Some jurisdictions do not allow certain
limitations; in those, the limitations apply to the fullest extent permitted.

## 8. Indemnification

You will indemnify and hold harmless DreggNet and its operator from claims, losses,
and expenses (including reasonable legal fees) arising from your content, your use
of the service, or your breach of these Terms or the AUP, to the extent permitted
by law.

## 9. Disclaimers specific to the verifiable rail

The verifiability guarantees describe **integrity** (faithful execution and serving,
tamper-evident receipts), **not** availability, durability, legality, or fitness of
any tenant workload. A receipt proves what happened; it is not a warranty that a
workload is correct, lawful, or will remain available.

## 10. Governing law and disputes

These Terms are governed by the laws of `[[FILL: governing-law jurisdiction]]`,
without regard to conflict-of-laws rules. `[[FILL: dispute resolution — courts vs
binding arbitration; venue; any class-action waiver — REQUIRES COUNSEL]]`.

## 11. Changes to these Terms

We may update these Terms; material changes will be posted with a new effective
date. Continued use after the effective date is acceptance. If you do not agree,
stop using the service.

## 12. Miscellaneous

- **Entire agreement:** these Terms + the incorporated policies are the entire
  agreement between you and us regarding the service.
- **Severability:** if a provision is unenforceable, the rest remains in effect.
- **No waiver:** our failure to enforce a provision is not a waiver.
- **Assignment:** you may not assign these Terms without our consent; we may assign
  them in connection with a merger, acquisition, or sale of assets.
- **Contact:** `[[FILL: support@dreggnet.example]]`.

> **Counsel must ratify §3 (warranty disclaimer), §4 (payment + Stripe + token
> characterization), §7 (liability cap), §10 (governing law / arbitration), and the
> token/money-transmission question flagged in `LEGAL-POSTURE.md` §6 before this is
> published or relied upon.**
</content>
