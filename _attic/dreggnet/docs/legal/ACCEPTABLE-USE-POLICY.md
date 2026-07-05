# DreggNet Acceptable Use Policy (AUP)

> **TEMPLATE — RATIFY WITH COUNSEL BEFORE PUBLISHING.** Drafted by an engineering
> agent, not a lawyer. Modeled on the shape of mainstream host AUPs (Hetzner,
> fly.io, Vercel, Cloudflare). `[[FILL: ...]]` marks placeholders a human must
> complete. Effective date and entity must be set before this is binding.

**Operator:** `[[FILL: legal entity name]]` ("DreggNet", "we", "us")
**Effective date:** `[[FILL: date]]`
**Contact for abuse / reports:** `[[FILL: abuse@dreggnet.example]]`

This Acceptable Use Policy governs everything you deploy, host, run, store, or
serve using DreggNet. It is part of, and incorporated into, the
[Terms of Service](./TERMS-OF-SERVICE.md). By using DreggNet you agree to it. We
may update it; material changes will be posted with a new effective date.

DreggNet is a **permissionless, KYC-free** verifiable cloud: accounts are
pseudonymous capability credentials, not verified identities. Because we do not
gate by identity, we **do** gate by conduct. This policy is the conduct bound, and
the [`dreggnet-guard`](../../guard/) enforcement layer is its teeth (see §3).

---

## 1. Prohibited content and uses

You may not use DreggNet — including any site, server, agent, bucket, domain, or
compute you create — to host, store, serve, transmit, generate, or facilitate any
of the following. This list is illustrative, not exhaustive; we may act on conduct
that is abusive in spirit even if not enumerated.

### 1.1 Child sexual abuse material (CSAM) — zero tolerance, mandatory reporting
Any content that sexually exploits or endangers minors is **absolutely
prohibited**. This is not subject to discretion, appeal, or the ordinary review
flow. Upon obtaining actual knowledge of apparent CSAM, we will **remove it,
suspend the account, preserve the relevant data, and report to the NCMEC
CyberTipline** as required by 18 U.S.C. §2258A and cooperate with law enforcement.
KYC-free status does not change this duty in any way.

### 1.2 Malware, phishing, and credential abuse
- Malware, ransomware, spyware, worms, viruses, or their distribution/staging.
- **Malware command-and-control (C2)** infrastructure or botnet coordination.
- **Phishing** — deceptive pages, kits, or campaigns impersonating others to
  harvest credentials, payment data, or personal information.
- Hosting or serving exploit kits, or staging an attack on a third party.

### 1.3 Spam and unsolicited messaging
- Bulk unsolicited email, SMS, or messaging; spam relays or open relays.
- Harvesting addresses for, or supporting, spam operations.
- Any use that lands DreggNet's network on a blocklist (Spamhaus et al.).

### 1.4 Network abuse, DDoS, and unauthorized access
- Originating or participating in **denial-of-service / DDoS** attacks.
- Port scanning, vulnerability scanning, or intrusion attempts against systems
  you do not own or lack explicit authorization to test.
- Unauthorized access to any system, account, network, or data.
- Egress abuse: weaponizing DreggNet's outbound network or IP reputation to attack,
  scrape, or flood third parties.

### 1.5 Cryptocurrency mining without disclosure
- Undisclosed cryptocurrency mining or other covert resource-monetization
  workloads. Mining/compute-heavy workloads are only permissible if **explicitly
  disclosed and run under a paid lease appropriate to the resource draw** — covert
  miners pegging subsidized/free compute are prohibited and will be suspended.

### 1.6 Illegal content and conduct
- Content or activity unlawful in the jurisdiction(s) DreggNet operates in
  (`[[FILL: jurisdiction]]`) or where it is served.
- Distribution of stolen data, fraud schemes, illegal marketplaces, or content
  facilitating serious crime.
- Content that incites or facilitates violence or terrorism.

### 1.7 Intellectual-property infringement
- Hosting, serving, or distributing content that infringes copyright, trademark,
  or other IP rights of others. Copyright complaints are handled under our
  [DMCA & Takedown Policy](./DMCA-AND-TAKEDOWN.md), including a
  **repeat-infringer termination** policy.

### 1.8 Other abuse
- Deceptive impersonation of DreggNet, its operator, or any third party.
- Circumventing quotas, rate limits, suspensions, or account bans (including
  creating sibling accounts to evade enforcement).
- Any use that materially threatens the security, integrity, availability, or
  reputation of DreggNet or its other users.

---

## 2. Your responsibilities

- You are responsible for everything done under your account / capability
  credential, including by your delegates, attenuated sub-capabilities, and agents.
- Keep your credential secret. Because accounts are cap-based and pseudonymous,
  **whoever holds the credential controls the account** — loss or leak is your risk.
- You must have the rights to everything you host or process, and you must comply
  with all laws applicable to your use.

---

## 3. Enforcement — and why it is auditable

DreggNet enforces this policy through the **`dreggnet-guard`** layer
([`guard/`](../../guard/)). Enforcement is graduated, and every standing change is
a **receipted, tamper-evident governance turn** (a prev-hash-chained, ed25519-signed
record anyone holding the operator's governance public key can re-verify). We do
not moderate by silent fiat; we moderate by an auditable record.

| Action | What it does | Mechanism |
|---|---|---|
| **Quota ceiling** | Caps how many sites/servers/agents/buckets/domains you hold and your cumulative compute/bandwidth/storage. Over the ceiling is refused in-band (`402`). | `guard::admit_create`, `charge_metered` |
| **Rate limit** | Caps deploy rate and request rate per account/site. Over the ceiling is refused (`429`). | `guard::admit_request`, `RatePolicy` |
| **Flag** | Moves your account to a **tighter quota tier** while still serving — the "under review" throttle. | `guard::flag` → `AccountStanding::Flagged` |
| **Suspend / takedown** | **De-routes / stops serving** the resource (and, for an account, blocks new creation). Your bytes are never altered — we stop serving, we do not tamper. | `guard::suspend_resource` → `403` |
| **Reinstate** | Restores a resource/account to good standing (e.g. after a successful appeal or counter-notice). | `guard::reinstate` |

**Important integrity note (the verifiable-rail promise is intact):** a takedown is
**de-route / suspend**, never byte-tampering. DreggNet's "the host cannot alter your
bytes" guarantee is about *integrity of what we serve*, not an obligation to serve
prohibited content forever. We can, and will, stop carrying abuse — and the act of
doing so is itself on an auditable record.

We may act **immediately and without prior notice** where required to prevent
imminent harm, comply with law (e.g. CSAM), protect the network, or preserve our
relationships with upstream providers and payment processors. Otherwise we aim to
act proportionately (flag → throttle → suspend) and to state a reason.

---

## 4. Reporting abuse

Report abuse, security issues, or policy violations to **`[[FILL: abuse@dreggnet.example]]`**
or via the abuse-report intake. A report is recorded as an auditable governance
event but **takes no automatic enforcement action** — review (by an operator or an
automated signal) decides whether to act. Include the resource (a `*.example.com`
URL, custom domain, server, or resource id), the nature of the abuse, and any
evidence. Copyright complaints: see [DMCA & Takedown](./DMCA-AND-TAKEDOWN.md).

## 5. Appeals

If your resource or account is suspended, the **owner-readable reason** is shown in
your console (the suspension record exposes its reason). To appeal, contact
**`[[FILL: appeals@dreggnet.example]]`** with the resource id and your response. We
will review; an upheld appeal is executed as a **receipted `reinstate`** governance
turn restoring your standing. Appeals do **not** apply to CSAM removals, which are
final and reported.

## 6. Changes

We may revise this AUP. Continued use after a change's effective date is acceptance.

> **Counsel must ratify §1 (especially 1.1/1.6/1.7), §3's enforcement language, and
> §5's appeal commitments before this is published or relied upon.**
</content>
