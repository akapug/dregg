# The Deploy Gate: proof-carrying contract deployment

A design note on using dregg as a **deploy-time verification gate** for a chain
(an L2, or any chain with a deployment path) — grounded in what already exists in
this repo, with the honest boundary named rather than hidden.

Origin: a community question (Geeeeeves, 2026-07-11) — could dregg be a scoped
module ("a micro-kernel / egg") on an L2 that validates a contract before it is
allowed to deploy, to keep scams off the chain? The honest answer reframes the
goal, because the naive version is undecidable and dregg already has the better
version.

## The reframe: don't detect scams — refuse rug-classes, and prove the rest

"Detect malicious contracts" is not decidable. By Rice's theorem, any non-trivial
semantic property of an arbitrary program is undecidable; scam detection over
arbitrary bytecode is adversarial and permanently incomplete (this is why every
scanner — GoPlus, Honeypot.is — is a *heuristic oracle you trust*, not a proof).
Promising "we catch all scams" is a claim the first slipped-through rug falsifies.

dregg's move is the opposite, and it is already built for dregg's own
deployments: **make whole rug-classes either structurally impossible or provably
visible before deploy, and make the check itself verifiable — a proof the chain
re-checks, not a verdict it trusts.**

## What already exists (this is not theoretical)

### DreggDL — a checkable deployment spec that gates before gas

`dregg-deploy` (DreggDL) is a CapDL-inspired declarative deployment spec: write
the capability/authority layout once (TOML/JSON), lower it to the exact
`dregg_turn::CallForest` the SDKs instantiate, and run four **static** checks over
the *whole declared authority structure* — before any gas:

- **Conservation (B):** per asset, value moves sum to exactly zero.
- **Non-amplification (A):** a granted capability is an attenuation (⊆ facets,
  narrower-or-equal target/expiry) of a capability the granter itself holds — no
  authority is created along a delegation edge.
- **Well-formedness:** no `Authorization::Unchecked` outside genesis, references
  resolve, no empty actions, deltas present where conservation needs them.
- **Ring balance:** a settlement ring's legs close a cycle that conserves per asset.

The `apply` flow **gates on the static check**: an amplifying or non-conserving
spec is `Refused` *before a single turn is produced* — the check is the gate, not
an afterthought. And the non-amplification leg is grounded in a line-for-line
transcription of seL4's own abstract spec (`metatheory/Dregg2/Firmament/
SeL4Abstract.lean`, `seL4_derive_cap_non_amplifying`), not a black box.

### Dregg2.Verify — the same checks, with an honest boundary drawn as structure

`dregg-userspace-verify` (Dregg2.Verify) is the static, userspace, pre-submission
half: it reads a constructed-but-not-submitted `CallForest` and returns an
assurance verdict, naming the precise offending locus (which root, node, effect,
asset) on failure. Crucially, its `boundary` module draws the decidability line
**as engineered structure, not a caveat**:

- **Statically decidable (from the artifact alone):** per-asset conservation,
  delegation-edge attenuation, well-formedness, ring cycle-closure.
- **Needs the live executor / proof (NOT static):** whether the signer actually
  *held* the capability it grants, whether balances suffice, credential/signature
  validity, caveat discharge against live host context, nullifier freshness, and
  the whole-state commitment. For those, route through the verified executor and
  verify the receipt.

That boundary *is* the Rice's-theorem honesty — dregg states exactly what a static
check can and cannot promise, and hands the rest to the proof.

## The three tiers (name all three; do not blur them)

A deploy gate is only as honest as its tiers:

1. **Deployed *as* a dregg cap-layout (provable).** The authority structure is
   checkable off one file: hidden or amplifying authority is *refused* before
   deploy (non-amplification + attenuation), value-from-nothing is *refused*
   (conservation), and any *disclosed* dangerous authority (e.g. a dev cap that
   can drain LP) is **provably visible** — the gate *policy* ("no un-renounced
   mint", "LP locked ≥ D") refuses it, provably. This is "fair by construction"
   with the thing prior fair-launch attempts lacked: a proof.
2. **Arbitrary foreign bytecode (heuristic, incomplete — say so).** A contract you
   cannot express as a cap-layout falls back to heuristic analysis (bytecode /
   template allow-listing, simulation-based honeypot checks with *named* coverage
   limits). This tier is necessary-not-sufficient and must be labelled as such —
   it is the same incompleteness every scanner has; dregg's only edge here is that
   the checks that *do* run are verifiable.
3. **Exceptions → governed review.** Anything the automated tiers cannot clear
   routes to a human/governance review that issues a proof-carrying "reviewed &
   approved by quorum" attestation. dregg's governance (the vote engines, now with
   non-custodial proof-of-holdings weight) is that mechanism. This acknowledges the
   undecidability instead of pretending it away.

## The shape: a scoped module, not chain control

Geeeeeves's "micro-kernel / egg" framing is exact: the gate performs *one*
function (permit-or-refuse a deployment), it does not control the L2. That is the
same plug-not-socket shape as dregg's interop adapters (the Hyperlane ISM, the
LayerZero DVN): dregg is the **proof-carrying verification backend** that the host
mechanism — here, the deployment path — plugs into. The chain requires a valid
dregg deploy-permit; the permit carries a proof the chain verifies; the chain
never trusts dregg's word.

```
  contract (as a DreggDL spec)                     the L2 / chain
  ─────────────────────────────                    ─────────────────────
  authority layout  ──lower──▶  CallForest             deploy path
                                    │                       ▲
                    Dregg2.Verify::analyze                  │ permit + proof
                                    ▼                       │
                     Assurance (A · B · wf · ring)  ────────┘
                     REFUSED-with-a-reason before gas,
                     or a proof-carrying deploy permit
```

## Why a chain would want it (the honest BD story)

A chain cannot fix human greed, and no gate stops every scam. But a chain that
adopts a *provable* deploy gate earns a **verifiable** "we did our diligence"
claim — the check ran, here is the proof, re-check it yourself. For a chain
courting institutional capital, that verifiable-cleanliness signal is the point:
not "trust us, it's clean," but "here is a proof the deploy rules held." That is a
real, defensible partnership story, and it is the honest one.

## What is real today vs. what is new

- **Real today:** the gate-on-static-check pattern (`dregg-deploy::plan_apply`
  refuses before gas), the four checks, the honest static/dynamic boundary
  (`dregg-userspace-verify::boundary`), non-amplification grounded in transcribed
  seL4, and the governance for tier 3.
- **New for a foreign-chain deploy gate:** the on-chain permit hook on the target
  chain (the same adapter shape as the ISM/DVN), the tier-2 foreign-bytecode
  analysis engine (the hard, permanently-incomplete part — scope it honestly), and
  the policy language for tier-1 gate policies ("no un-renounced mint", etc.).

The strong claim is tier 1 and it is provable. The weak claim is tier 2 and it is
heuristic. Ship both with their labels on.
