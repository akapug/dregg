# Provable Agent Labor — how dregg-cloud proves the QA *was real*

*The nuanced design ember asked to "talk about more" (it died in a context-roll
between `99f316b8` and `a77a9549`; the code got built, this doc is the design
behind it). This is the canonical answer to: **when a dregg-cloud agent runs
testing / QA / prod-monitoring for a customer, how does the protocol witness and
prove the QA actually happened and was real — not just "the agent said so"?***

*Read this for the SHAPE and the exact honest claim. Companion grounding:
`docs/VISION-NEXT-PRODUCT.md` (the Proof-of-QA wedge), `docs/VISION-AGENT-WORLD.md`
(the agent-in-the-world thesis), `docs/RECEIPT-CONTRACT.md`,
`docs/REPLENISHING-BUDGET.md`. The code lives in the open-source `dregg-agent`
crate — `breadstuffs/dregg-agent/src/{agent,federation_qa,receipt,meter,budget}.rs`
— re-exported and wired to the real owned wasmi compute engine by DreggNet at
`exec/src/agent_toolkit.rs`. Verify any file:line against HEAD before relying on
it; this is a design doc, not a status board.*

---

## 1. The question, precisely

"Prove the QA was real" sounds like one question. It is two, and keeping them
apart is the whole discipline of this doc — because one of them is the most
honest thing dregg can offer, and the other is a thing **no substrate can ever
offer**, and conflating them is exactly how an agent-QA product becomes a lie.

Decompose the customer's anxiety. An autonomous agent reports: *"I ran the
tests, they passed, I deployed, it's healthy."* The customer cannot tell a
genuine green run from a confident hallucination. What, precisely, would relieve
that?

**What CAN be proven — the declared run.** That a *named command* (the test
invocation) ran against a *named body of code* (a content commitment), and
produced a *named result* (exit + an output digest) — and that this triple holds
**operator-independently**: not because the agent said so, not because one
operator's box said so, but because anyone, offline, re-running the bound command
on the bound code reproduces the bound result, and a quorum of mutually-distrusting
operators each did so and agreed. This is the thing *nobody else can offer*. Every
"AI agent in CI" product can run a suite and print a log; none can make the log
**unfakeable, bounded, and re-witnessable by a stranger**. That is the moat.

**What CANNOT be proven — the meaning of the run.** That the declared tests are
*good* — that the suite is non-trivial, that it actually exercises the behavior
the customer cares about, that a green result *means the software works*. An empty
test suite passes. A suite of `assert!(true)` passes. A suite that tests the wrong
module passes. The substrate can prove, to the last bit, that *this* suite ran on
*this* code with *this* result — and that tells you **nothing** about whether the
suite was worth running. Test-meaningfulness is the author's job, permanently, and
**dregg must never claim otherwise.** The moment a Proof-of-QA badge is read as "the
software is correct" rather than "the declared QA provably happened," the product
has overclaimed, and the first empty-suite-that-passed in the wild burns the trust
the whole thing is built to manufacture.

So the precise question is: *prove the QA happened, as declared, operator-independently
— and never imply the QA was sufficient.* The rest of this doc is the ladder that
delivers the first half and the named floor that refuses the second.

---

## 2. The ladder of assurance — L1 → L5

Five layers. The first four are climbing rungs of *real* assurance, each with a
distinct attack it stops and an honest limit it does not close (which the next rung
does). The fifth is not a rung — it is the floor, the thing that is unprovable by
anyone, named so it is never silently claimed.

A verifier climbs the ladder in order: a higher rung is only meaningful once the
lower ones hold (an operator-independent verdict over a forgeable receipt chain is
worthless). Each rung is `#[fail-closed]`: the *absence* of a proof is a rejection,
never a pass.

### L1 — tamper-evidence: the verdict is sealed, not asserted

**What it proves.** Every admitted action — and the QA verdict bound into it — is
sealed into a prev-hash-linked, ed25519-signed receipt chain. The verdict (pass/fail,
the test summary, *and* the `WitnessedRun` binding) is folded into the signed body
hash, so it is part of what the signature commits to, not a side note. A non-witness
re-verifies the whole chain with no trust in the operator.

**The attack it stops.** *Forge a verdict post-hoc.* An operator (or a compromised
agent) edits a recorded "tests failed" into "tests passed" after the fact, or splices
a receipt out of the chain to hide an action. Caught: flipping any bound field moves
the body hash and the ed25519 signature no longer verifies (`ChainError::BadSignature`);
removing a receipt breaks the prev-hash link (`ChainError::BrokenLink`).

**Grounded in.** `dregg-agent/src/agent.rs` — `AgentReceipt::body_hash` binds
`tool_ok`, `tool_summary`, and the full `WitnessedRun` (command · code_root · exit ·
output_digest) into the hash (≈ lines 446–483); `verify_agent_run` (≈ line 622) calls
`receipt::verify_chain` (`dregg-agent/src/receipt.rs:307`). Teeth:
`the_receipt_chain_verifies_and_tampering_is_caught`, `removing_a_receipt_breaks_the_chain`.

**The honest limit.** Tamper-evidence proves the record is *internally consistent
and unedited since signing*. It does **not** prove the recorded verdict reflects a
real execution — a runtime that *originally* signs a fabricated "passed" produces a
perfectly valid chain. L1 catches editing the story; it does not catch a lie told
straight. That is L3.

### L2 — budget / cap-boundedness: the agent couldn't exceed spend or reach

**What it proves.** Two hard bounds, by construction, not by a watchdog:

- **Spend.** Every action draws its cost from a replenishing-budget cell; an
  exhausted budget refuses the next action **in-band** (`MeterError::OverBudget`,
  fail-closed) — the runaway is *contained*, not merely logged after the fact. The
  un-drawn headroom (`budget − consumed`) is a hard ceiling on everything the agent
  *could still have done* — the could-have bound, surfaced in the run report.
- **Reach.** Every action is cap-gated against an attenuable `dga1_` credential
  before it runs; a tool-call / cell-op outside the granted bundle is refused
  (`ActionOutcome::CapRefused`) before any draw or commit. A sub-agent gets a
  genuinely *attenuated* child credential (it can only narrow — the no-amplify
  lattice on both the cap axis and the budget axis).

**The attack it stops.** *The runaway / the overreach.* A stuck or adversarial agent
that loops forever, or reaches for a service / cell / endpoint it was never granted.
Caught: consumption is capped at the ceiling regardless of plan length; an
out-of-bundle action never runs and leaves no receipt (the agent never reached
outside its authority). A forged report claiming more spend than the ceiling permits,
or more than the chain attests, is rejected (`BoundViolated` / `ConsumedMismatch`).

**Grounded in.** `dregg-agent/src/agent.rs` — the cap-gate (`Credential::verify`,
≈ line 1026) and the meter draw (`Meter::draw`, ≈ line 1049) in `run_inner`;
`dregg-agent/src/meter.rs` (the `OverBudget` refusal) and `budget.rs` (the
`ReplenishingBudget` cell). Teeth: `a_runaway_is_contained_by_the_budget_ceiling`,
`an_out_of_bundle_invoke_is_refused_and_not_receipted`,
`a_subagent_attenuates_and_cannot_exceed_the_parent`, `the_budget_proves_the_could_have_bound`.

**Why it belongs in a QA proof.** "The QA happened" is only half a customer's
question; the other half is "and the agent didn't burn my budget or touch things it
shouldn't have *while* doing it." L2 makes the blast radius a property of the cell and
the cap, so a security lead can sign the budget line: the proof of work-done arrives
*with* a proof of bounded-cost and bounded-reach.

**The honest limit.** L2 bounds what the agent *could do*; it says nothing about
whether the QA verdict it *did* produce is real. Orthogonal axis — necessary, not
sufficient.

### L3 — execution-witnessing: the substrate re-ran the declared command on the deployed code

**What it proves.** This is the rung that lifts the claim from "the runtime committed
X and couldn't edit it afterward" (L1) to "the substrate ran *these* tests on *the
deployed* code with *this* result." The QA tool emits a `WitnessedRun` binding three
re-checkable facts: the exact `command`, a `code_root` content-commitment to the code
the run executed against, and the result (`exit` + `output_digest`). A verifier then
checks two things:

1. **The tests ran on the deployed code.** `code_root == deployed content_root` — the
   suite ran on what was actually deployed, not on arbitrary or stale code
   (`WitnessVerifyError::CodeRootMismatch`).
2. **The result matches a re-execution.** Re-running the bound `(command, code_root)`
   reproduces the bound `(exit, output_digest)`. A runtime that recorded a verdict its
   execution does not actually produce is caught here — the binding mismatches on
   re-run (`WitnessVerifyError::ExecutionMismatch`). An un-re-executable binding is
   rejected fail-closed (`NotReWitnessable`) — a verdict nobody can reproduce is *not*
   accepted.

**The attack it stops.** *The straight lie L1 can't catch.* A runtime that signs a
genuine, internally-consistent "tests passed" receipt — but never ran the tests, or
ran them on different code. L1's chain is valid; L3 re-executes the declared command on
the declared code and the fabricated result fails to reproduce.

**Grounded in.** `dregg-agent/src/agent.rs` — `verify_witnessed_qa` (≈ line 764), the
`WitnessedRun` struct (≈ line 287). The re-execution oracle is injected: DreggNet wires
the real owned wasmi sandbox engine as the runner (`exec/src/agent_toolkit.rs` —
`with_run_tests_in` / `rewitness_run_tests` riding `crate::run_workload`), so the bound
ties to a genuine sandboxed execution at the owned `Sandboxed` compute tier. Tooth:
`run_tests_binds_a_real_sandboxed_execution` (the real wat suite runs in the owned
wasmi sandbox, the witness binds, the whole run re-witnesses).

**The honest limit — the one that forces L4.** The re-execution still runs in **the
same compute substrate** that produced the original verdict. So L3 proves "*this
substrate* ran these tests on this code with this result" — it is **operator-dependent**.
A single lying operator whose substrate is rigged to *both* record *and* re-reproduce
a fabricated verdict is not caught by a re-run inside that same rigged substrate. L3 is
the strongest thing one operator can prove about itself, and it is not enough — proving
your own honesty to yourself is the category gap a trusted CI host can never close.

### L4 — federation-attestation: independent operators re-run and quorum-certify

**What it proves.** The verdict is submitted to the live federation; **each independent
operator re-executes the bound `(command, code_root)` on its OWN substrate**, gets its
own `(exit, output_digest)`, and **signs that result**. A quorum (threshold-3 of the
n=4 nodes) agreeing on the *same* result is the **attested verdict** — a `QuorumCert`,
the same multi-sig-over-a-fact shape as the turn-finality quorum certificate. Because
the operators are independent (distinct keys, distinct substrates), no single one can
forge the verdict: a lying operator is **outvoted** by the honest majority *and*
**detected** — its signed-but-divergent attestation is named on the cert as evidence,
not dropped as noise. This is **operator-independent**: no single substrate is trusted.

**The attacks it stops.**
- *A lying operator* (a rigged substrate signing a false pass over a truly-failing
  suite, or a false failure over a green one) → the honest majority still certifies the
  *true* result, and the liar is surfaced in `AttestedVerdict::divergent`.
- *A lying submitter* (the agent/operator submitting a false claim) → if the honest
  quorum's independent re-runs disagree with the submitted claim, `matches_claim` is
  `false` — the submitter's claim is *refuted*, not laundered.
- *A forged or stuffed cert* — an attestation off a different run (`OffTopicAttestation`),
  from a non-federation key (`UnknownOperator`), an operator voting twice
  (`DuplicateOperator`), or a tampered signed result (`ForgedAttestation`) → the whole
  cert is refused.
- *No genuine agreement* — when no single result reaches the threshold (the operators
  truly disagree), the verdict is **not** attested (`NoQuorum`), refused fail-closed.

**A bonus the topology buys for free.** `snoopy-lean` and `snoopy-rust` re-running the
same QA and agreeing carries the **rust↔lean differential** cross-check all the way
down to the QA layer — two independent implementations of the executor agreeing on the
result, not just two copies of one.

**Grounded in.** `dregg-agent/src/federation_qa.rs` — `Federation::attest` (≈ line 262)
fans the run to every `Operator` (each re-executes on its own substrate + signs);
`verify_quorum_cert` (≈ line 400) validates every attestation (this-run · known-signer ·
once · valid-signature) and certifies the largest agreeing block iff it meets the
threshold, naming dissenters. Teeth: `an_honest_quorum_certifies_the_verdict`,
`a_lying_operator_is_outvoted_and_detected`, `a_false_failure_vote_is_outvoted_and_detected`,
`a_lying_submitter_claim_is_refuted_by_the_quorum`, `no_quorum_is_refused`,
`a_forged_attestation_is_rejected`, `an_outsider_attestation_is_rejected`.

**The honest limit — what L4 still assumes.** L4 delivers operator-independence: any
*single* operator is powerless to lie. What it still assumes is that the operators are
*genuinely* independent — distinct keys, distinct substrates, not secretly the same
party — and a verifier still trusts the *federation re-execution itself* (it trusts that
each operator's signed `(exit, output_digest)` came from a faithful re-run, rather than
having a pure light client *witness* that re-run in-circuit). Closing that — a non-operator
light client directly verifying each re-run was faithful — is the residual (§4). L4 is
the off-chain federation-attestation half; it makes any single operator powerless, but
it is operators attesting, not yet a circuit witnessing.

### L5 — test-meaningfulness: the honest floor, UNPROVABLE by anyone

**What it would be.** That the declared tests are *good* — non-vacuous, relevant,
sufficient to justify the trust a green badge invites.

**Why it is unprovable — by dregg or anyone.** Meaningfulness is a property of the
relationship between a test suite and an *intent* that lives only in the author's head.
An empty suite passes. `assert!(true)` passes. A suite that exhaustively tests the
wrong thing passes. No amount of cryptography, re-execution, or quorum can distinguish
a meaningful green from a vacuous green, because the substrate has no access to what the
software was *supposed* to do. This is not a dregg limitation to be closed in a future
epoch; it is a category boundary. (It rhymes with the project's standing discipline —
*don't launder vacuity as honest*: a spec that is true-but-vacuous is still broken. L5
is that lesson at the product surface: a *proof* that a vacuous suite ran is honest
about what it proves and must be honest about what it doesn't.)

**The design consequence.** L5 is named precisely so it is **never silently claimed**.
Test-meaningfulness is, permanently, the author's responsibility. The product surface
must say "the declared QA provably happened" and must *never* drift to "the software is
correct." The badge is a proof-of-process, not a proof-of-quality — and the honesty of
saying so is part of why the proof-of-process is worth anything.

---

## 3. The precise product claim

The exact wording the product may stand behind, and the exact wording it may not.

> **What dregg-cloud proves:** a *tamper-evident* (L1), *budget/cap-bounded* (L2),
> *federation-attested* (L4) proof that **the declared tests ran against the deployed
> code with the declared result** — re-witnessable by anyone, offline, trusting no
> single operator.

> **What it does NOT prove (and must never imply):** that the tests are *good*, that
> the result *means the software works*, or that the QA was *sufficient* (L5). The proof
> is of **process**, not of **quality**. Whether a suite is worth running is the author's
> responsibility, forever.

Honest layering inside that claim, so the wording tracks what is *built* vs the *named
residual*:

- **L1 + L2** are LIVE and proven (the receipt chain, the budget cell, the cap bundle —
  re-witnessed by `verify_agent_run`, teeth in `agent.rs`).
- **L3** is LIVE on the local / single-substrate path (the witness binds a *real*
  sandboxed execution via the owned wasmi engine wiring; `verify_witnessed_qa` re-executes
  it). Its honest limit (operator-dependence) is stated, not hidden.
- **L4** is BUILT and tested as the open-source `federation_qa` core (quorum attest +
  `verify_quorum_cert`, full teeth). Pointing it at the **live n=4 nodes** (`edge` ·
  `persvati` · `snoopy-lean` · `snoopy-rust`) as a wired production path is a
  *reviewed-go* — the mechanism exists; the live wiring is the go-live (§4).
- **L5** is, and always will be, out of scope by category.

**The Proof-of-QA wedge.** The buyer is the engineering team — specifically the
platform/security lead — at any shop putting an AI coding/ops agent into a real
pipeline. The pain is brand-new in 2026 and acute: *you have the agent's word and a log
it wrote itself.* The use is a **CI gate** (the PR check re-runs the proof; green-without-
trusting-anyone or it doesn't merge) and a **compliance artifact** (a sealed, shareable
manifest that the declared QA provably happened under a hard spend cap, re-verifiable by
an auditor who was not there). It converts "trust the agent" into "audit the agent,"
which is the difference between a pilot and production. That is a budget line a security
lead can sign — and the differentiating machinery (L1–L4) already runs at HEAD, which is
why Proof-of-QA, not the marketplace it grows into, is the wedge.

---

## 4. The residual + the path

Three threads, each named with what it closes and what it is waiting on. None is a
parking lot; each is a burn-down.

**(a) The in-circuit witness — close L4's last assumption.** L4 is operators attesting;
the deeper seam is a **pure light client** (not the operators) directly witnessing that
each QA re-execution was faithful — the re-run folded into the EffectVM / recursion tree
so a non-operator verifies it in-circuit, anchored to `verifyBatch accept ⟹ ∃ genuine
kernel transition` (breadstuffs `CircuitSoundness.lean`). This is the **swarm's VK-epoch**,
owned by the circuit-soundness lane (the `MergeRefinesConfluence`-shape seam — the same
"a light client, not a re-executing validator, witnesses it" weld the house capacities
carry, `HOUSE-CAPACITIES-WELD-PLAN.md`). When it lands, the QA proof needs *no* trusted
operator and *no* trusted federation — only the deployed VK. Until then, L4's honest
boundary is stated plainly: a verifier trusts the operators are genuinely independent;
the quorum makes any single one powerless to lie. This is a real rung on a burn-down, not
a wall — and it is a VK-affecting circuit change, so it belongs to that lane and not to a
thin-context kernel poke.

**(b) Live federation-QA wiring — a reviewed-go.** The `federation_qa` core is built and
tested against modeled operators (honest, lying, abstaining, saboteur). Pointing
`Federation` at the **real n=4 nodes** — each operator's `re_execute` oracle riding its
*own* node's `run_workload` tier — is the live wiring. It is staged, reversible, and
waiting on the same one-word go as the rest of the reviewed-go battery
(`MORNING-REVIEW.md`). Empirically validating it (a real QA verdict fanned to four
independent boxes, certified or refuted) is exactly the kind of live N-node run that
*validates whether the thing works* — and is worth doing to learn, not gated on
paper-green.

**(c) The open-source `dregg-agent` story — anyone can run + verify.** The whole assurance
core — the receipt chain, the budget/meter, the cap braid, the witnessed `run_tests`, and
`federation_qa` — lives in the open-source `dregg-agent` crate, depending on nothing but
the substrate and owning no compute engine (its compute tools take an *injected* runner;
`dregg-agent/src/toolkit.rs`). DreggNet is a thin wrapper that injects the real owned wasmi
engine (`exec/src/agent_toolkit.rs`). This matters for the claim: *anyone* can run the
agent, *anyone* can be a federation operator, and *anyone* can `verify_quorum_cert`
against a pinned operator set — the proof is not "trust dregg-cloud," it is "re-witness it
yourself, with your own operators if you like." Operator-independence is only meaningful if
the operator set is open, and it is.

---

## 5. Why provable agent labor is the product's spine

The verifiable-cap-budget-receipt substrate was not built to host static sites or move
tokens — those are exercises of it. It was built so that **agent labor can be trusted
without trusting the agent**. That is the thesis of `VISION-AGENT-WORLD.md` made into a
purchasable thing: *autonomy and safety are one primitive.* The same three objects that
let an agent *act* — a budget cell (its allowance), a capability (its reach), a receipt
chain (its record) — are the same three that *bound and prove* it. You can hand an agent
real-world authority **precisely because** you can bound and audit it cryptographically,
and the leash is the grant.

Provable agent labor is where that thesis cashes out into a sentence a stranger pays for:
*give an autonomous agent a budget and a capability; get back a cryptographic proof of
everything it did and a hard bound on everything it could have done.* The QA verdict is
the sharpest instance — it is the one place the agent's *claim* (the tests passed) is
exactly the thing the customer most wants to *not* take on faith, and it is the place
where L1→L4 turn "trust me" into "verify me, down to *the declared tests ran on the
deployed code with this result, and four independent operators agree.*"

And the spine holds *because* it knows where it ends. The product is honest at L5: it
proves the labor *happened, as declared, operator-independently*, and it never pretends
to prove the labor was *wise*. That boundary is not a weakness in the pitch — it is the
reason the pitch is believable. A system that claimed to prove your tests are good would
be lying, and one lie at the floor would cost every proof above it. Provable agent labor
is the spine precisely because every vertebra is load-bearing and named: four rungs of
real, climbing assurance, and one floor that is honest about being a floor.

---

*Dated 2026-06-30. The design ember asked to "talk about more," written down at last.
Every layer names the file:line it stands on and the attack it stops; the residual names
its burn-down; the floor names what is unprovable so it is never claimed. Verify any
LIVE / reviewed-go / file:line against HEAD before relying on it — L1–L3 are proven on
the local path, L4 is built-and-tested with the live-node wiring a reviewed-go, and the
in-circuit witness is the VK-epoch seam. ( ⌐■_■ )*
