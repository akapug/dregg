# DreggNet Privacy Notice

> **TEMPLATE — RATIFY WITH COUNSEL BEFORE PUBLISHING.** Drafted by an engineering
> agent, not a lawyer. Minimum privacy notice for a KYC-free verifiable cloud.
> `[[FILL: ...]]` marks placeholders. GDPR/CCPA applicability and the data-deletion
> mechanics in particular need legal + engineering confirmation (see §7).

**Operator / data controller:** `[[FILL: legal entity name]]` ("DreggNet", "we")
**Effective date:** `[[FILL: date]]`
**Privacy contact:** `[[FILL: privacy@dreggnet.example]]`

This notice explains what we collect, why, and your choices. DreggNet is built on
a **data-minimization-by-design** posture: we are KYC-free, accounts are
pseudonymous capabilities, and we collect as little as possible. Less data
collected means less to breach, less to subpoena, and less to mishandle.

---

## 1. The short version

- **No KYC.** We do not require your government ID, legal name, or identity to use
  DreggNet. An account is a pseudonymous **capability credential**, not a verified
  identity.
- **We collect the minimum** to run, secure, and bill the service: a pseudonymous
  account id, payment metadata (via Stripe — card data never touches us), and
  operational logs/receipts.
- **We don't sell your personal data.**
- **You can ask** what we hold and request deletion (subject to the limits in §7).

## 2. What we collect

| Category | What | Why | Source |
|---|---|---|---|
| **Account identifier** | A pseudonymous subject id derived from your `dga1_` capability credential. **Not** a name or government ID. | Identify your account, attribute resources, enforce quotas. | You (on use) |
| **Payment metadata** | For fiat: a Stripe customer/charge reference and amount. **We do not receive or store full card numbers** — Stripe processes card data under its own terms. For on-substrate: `$DREGG`/DEC transfer records (pseudonymous, on the verifiable rail). | Process payment, prevent fraud, meet our records duties. | Stripe; the dregg substrate |
| **Operational logs** | IP address, timestamps, request metadata, error/security events at the gateway. | Security, abuse prevention, debugging, rate-limiting, legal compliance. | Automatic |
| **Usage metering** | Per-resource compute/bandwidth/storage/uptime counters and verifiable per-charge receipts. | Bill you accurately; provide auditable receipts. | Automatic |
| **Moderation records** | If your account is reported/flagged/suspended, a receipted governance event (subject id, resource, reason, time, actor). | Auditable, tamper-evident enforcement and appeals. | Enforcement |
| **Content you host** | The bytes of your sites, objects, code, and workloads. | To host/serve/run them for you. We serve them faithfully and **cannot alter them**; we do not mine them for advertising. | You |
| **Voluntary contact** | Any email/handle you give us for support, abuse reports, or appeals. | Respond to you. | You |

We do **not** intentionally collect special-category personal data and ask that you
not put such data, or others' personal data, into resources without a lawful basis.

## 3. How we use it

To operate, secure, meter, and bill the service; to prevent and respond to abuse
(per the [AUP](./ACCEPTABLE-USE-POLICY.md)); to comply with law (including DMCA and
mandatory CSAM reporting); and to communicate with you about the service. We do
**not** sell personal data or use your hosted content for advertising.

## 4. Who we share it with

- **Stripe** — payment processing (card data handled by Stripe under its policy).
- **Infrastructure providers** — e.g. our hosting/network upstreams `[[FILL: e.g.
  Hetzner, Cloudflare]]`, who process traffic/IP data to deliver the service.
- **Law enforcement / legal** — when legally required (e.g. a valid subpoena), or
  for the **mandatory NCMEC CyberTipline report** of apparent CSAM (18 U.S.C.
  §2258A), or to protect rights and safety. Our KYC-free posture means we often
  simply **do not hold** identifying data to disclose.
- We do not otherwise sell or rent your personal data.

## 5. Cookies / local storage

`[[FILL: state whether the console/web surfaces use cookies or local storage, and
for what — e.g. session/auth only, no third-party advertising/tracking cookies.]]`

## 6. Retention

We keep operational logs and billing/receipt records `[[FILL: retention period —
e.g. logs 30–90 days; billing records as required by law/tax]]`. Moderation
governance records are **append-only and tamper-evident by design** (the audit
trail); they are retained as part of the verifiable enforcement record. Content you
host is retained while your resources exist and you keep them funded.

## 7. Your rights and data deletion

Depending on where you are (e.g. **GDPR** for EU/UK, **CCPA/CPRA** for California),
you may have rights to access, correct, delete, or port your personal data, and to
object to certain processing. To exercise them, contact
**`[[FILL: privacy@dreggnet.example]]`**.

- **Pseudonymity helps you here:** because we hold little identifying data, there is
  little to disclose or erase in the first place.
- **You can delete most of your content** by destroying your resources (sites,
  buckets, servers) through the CLI/console.
- **Honest limits (counsel + engineering must confirm before EU-scale launch):**
  - Some operational logs and billing/receipt records are retained for security,
    fraud-prevention, and legal/tax reasons even after deletion of content.
  - **Moderation governance records are append-only** by design and are not erased
    (they are the tamper-evident enforcement audit trail).
  - **An object-storage erasure/TTL path is still being built** (`docs/CLOUD-PROVIDER-READINESS.md`
    S-7). Until it ships, a deletion request against stored objects may not be fully
    automatable. This gap is tracked and must be closed before we invite users for
    whom a binding erasure right applies. *This is a known limitation stated honestly,
    not a finished guarantee.*

## 8. Security

We use the technical isolation and integrity controls described in the
[architecture](../../ARCHITECTURE.md) and red-team docs. No system is perfectly
secure; you are responsible for safeguarding your capability credential (whoever
holds it controls the account).

## 9. International transfers

DreggNet's infrastructure may process data in `[[FILL: regions]]`. `[[FILL:
transfer-mechanism note for EU/UK if applicable — REQUIRES COUNSEL]]`.

## 10. Children

DreggNet is not directed to children and is not for use by anyone under `[[FILL:
13/16]]`. We do not knowingly collect their personal data.

## 11. Changes and contact

We may update this notice; material changes will be posted with a new effective
date. Questions or requests: **`[[FILL: privacy@dreggnet.example]]`**.

> **Counsel + engineering must confirm §7 (deletion mechanics vs the storage-erasure
> gap), §2 (Stripe DPA), and GDPR/CCPA applicability before this is published or
> relied upon.**
</content>
