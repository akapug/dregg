**Does dregg's deploy-checker actually catch bad or inconsistent contracts? Yes — with an honest scope.**

Short version: it does, for a specific set of problems, and when it refuses something it points at the exact spot that's wrong — before the contract can even deploy. But it's not a magic "detect any scam" button, and I'll be straight about that, because anyone who claims that button exists is selling you something.

Here's what it actually catches today (it reads the contract's real permission map and checks it):

- **Secret mint** — a contract that quietly keeps the power to print more tokens. It's refused unless that power is either thrown away (renounced/burned) or held by a governance holder you've declared. This is the classic "dev can secretly mint and dump."

- **Hidden admin** — someone handing themselves *more* power than they were actually given. Refused, and it names the exact grant. This is the "hidden super-admin" trick.

- **Money that doesn't add up** — value created out of thin air. Every asset's ins and outs have to sum to zero, or it's refused. This is "makes supply from nothing."

- **Drain power** — the ability to move the pooled funds (like the LP) handed to someone who shouldn't have it, or broader than allowed. This is "dev can drain the pool."

When it refuses, it tells you the exact grant that's the problem — e.g. *"grant issuer → operator: this hands out live mint power"* — and it does this **before any gas is spent**. The check *is* the gate.

**The honest limit** (this part matters): it works on contracts written in dregg's own capability format, where it can actually read the permission map. It is not a scanner that reads arbitrary Solidity bytecode — and "catch ANY malicious contract, always" is mathematically impossible. No tool on Earth can do that. So instead we do something honest: we make whole *classes* of rug either impossible or refused-with-a-reason, and we're upfront that we can't magically catch everything. A checker that claims it catches everything is lying to you.

So: real, running, points at the problem, provable for the cases above — and honest about the one line it can't cross.

(And yeah… there's more under the hood than the chat has seen 😄 — but the rule here is to never let that turn into overclaiming.)
