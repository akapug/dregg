# DreggNet DMCA & Takedown Policy

> **TEMPLATE — RATIFY WITH COUNSEL BEFORE PUBLISHING.** Drafted by an engineering
> agent, not a lawyer. `[[FILL: ...]]` marks placeholders. The designated-agent
> details are blank until ember **registers the agent with the U.S. Copyright
> Office** — the safe harbor does not apply until that registration exists.

**Operator:** `[[FILL: legal entity name]]` ("DreggNet", "we")
**Effective date:** `[[FILL: date]]`
**Abuse contact:** `[[FILL: abuse@dreggnet.example]]`

DreggNet is an **infrastructure and hosting provider**: we host and serve content
that our users choose. We respect intellectual-property rights and respond to valid
notices. This policy is part of the [Acceptable Use Policy](./ACCEPTABLE-USE-POLICY.md)
and [Terms of Service](./TERMS-OF-SERVICE.md).

---

## 1. DMCA designated agent

To submit a DMCA copyright notice (17 U.S.C. §512), contact our registered
designated agent:

```
Designated Agent:  [[FILL: agent name / role]]
Operator entity:   [[FILL: legal entity name]]
Address:           [[FILL: physical mailing address]]
Email:             [[FILL: dmca@dreggnet.example]]
Phone:             [[FILL: phone]]
```

> **GATING ACTION (ember):** register this designated agent in the **U.S. Copyright
> Office DMCA Designated Agent Directory** (online, ~$6, renew every 3 years).
> **Until that registration exists and these fields are filled, DreggNet does not
> have §512 safe-harbor protection** and the operator is exposed to direct liability
> for hosted infringement. This is the single most important blank in this folder.

## 2. Filing a copyright infringement notice (takedown)

Send a written notice to the designated agent including all of the following (per
§512(c)(3)):

1. Your physical or electronic signature.
2. Identification of the copyrighted work claimed to be infringed.
3. Identification of the infringing material and **enough information to locate it**
   — the `*.example.com` URL, custom domain, server, or resource id.
4. Your contact information (address, phone, email).
5. A statement that you have a **good-faith belief** the use is not authorized by
   the owner, its agent, or the law.
6. A statement, **under penalty of perjury**, that the information is accurate and
   that you are the owner or authorized to act for the owner.

Incomplete notices may not be actionable. **Knowing material misrepresentation in a
notice can subject you to liability** under §512(f).

## 3. What we do with a valid notice

1. The notice is recorded as a **receipted abuse-report governance event** (the
   auditable intake; `guard::file_report`).
2. On review, we **expeditiously disable access** to the identified material by
   **suspending / de-routing** the resource (`guard::suspend_resource` → the serving
   path refuses with `403`).
   - **De-route, not tamper.** Consistent with DreggNet's integrity guarantee, we
     **stop serving** the material; we do **not** alter the user's bytes. The host
     cannot tamper with content — it can stop carrying it.
   - The action is a **receipted, tamper-evident governance turn**: who acted, why,
     and when, re-verifiable by anyone holding the operator's governance public key.
3. We notify the affected user with the **owner-readable reason** (the suspension
   record) so they can file a counter-notice.

## 4. Counter-notice

If you believe your material was removed by mistake or misidentification, send a
counter-notice to the designated agent including (per §512(g)):

1. Your physical or electronic signature.
2. Identification of the removed material and its prior location.
3. A statement **under penalty of perjury** that you have a good-faith belief the
   material was removed by mistake or misidentification.
4. Your name, address, phone, and a statement consenting to the jurisdiction of
   `[[FILL: federal district court]]` (and that you will accept service from the
   complainant).

On a valid counter-notice we may, after the statutory waiting period (generally
10–14 business days, absent notice that the complainant has filed suit), **reinstate
the material** as a receipted `reinstate` governance turn.

## 5. Repeat-infringer policy

Consistent with §512(i), we have adopted and will reasonably implement a policy to
**terminate, in appropriate circumstances, the accounts of repeat infringers.**
Repeated valid notices against an account may move it to `Flagged` and then
`Suspended` standing, up to termination. `[[FILL: counsel to confirm the threshold
and process is defensible.]]`

## 6. Trademark and other IP

For trademark or other (non-copyright) IP complaints, contact
**`[[FILL: abuse@dreggnet.example]]`** with the equivalent identifying detail. We
review and act under the [AUP](./ACCEPTABLE-USE-POLICY.md).

## 7. General abuse reporting

For non-IP abuse (phishing, malware, spam, network abuse, illegal content) report
to **`[[FILL: abuse@dreggnet.example]]`** and see the [AUP](./ACCEPTABLE-USE-POLICY.md)
§4. We also publish an RFC 9116 `/.well-known/security.txt` `[[FILL: confirm
published]]` for security and abuse contact discovery.

## 8. CSAM — mandatory removal and NCMEC reporting

**Child sexual abuse material is handled outside the ordinary notice-and-counter
process.** Upon actual knowledge of apparent CSAM we will **remove it, suspend the
account, preserve the relevant data, and report to the NCMEC CyberTipline** as
required by **18 U.S.C. §2258A**, and cooperate with law enforcement. There is **no
counter-notice, appeal, or reinstatement** for CSAM removals. To report suspected
CSAM, contact **`[[FILL: abuse@dreggnet.example]]`** immediately (or report directly
to the NCMEC CyberTipline at report.cybertip.org). KYC-free status does not alter
this duty. `[[FILL: counsel to confirm reporting + data-preservation mechanics for
the operating jurisdiction.]]`

## 9. Good faith and limits

We act in good faith on valid notices and are not liable for actions taken in
reliance on a notice or counter-notice that later proves inaccurate. This policy is
not legal advice; consult a lawyer about your rights.

> **GATING for counsel/ember before this is live: (1) register the designated agent
> (§1); (2) confirm the counter-notice jurisdiction (§4); (3) confirm the
> repeat-infringer threshold (§5); (4) confirm CSAM reporting + preservation
> mechanics (§8); (5) publish `security.txt` (§7).**
</content>
