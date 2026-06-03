# Effect Fidelity Ledger — dregg1 `apply.rs` vs Lean `execFullA`

Adversarial read-only audit (2026-06-03, 4 Opus skeptics) of the wave-1..4 fidelity work.
The library is GREEN (3497 jobs, 0 sorry) — these verdicts are about FAITHFULNESS, not build.
This ledger gates which effects the L2 demonstrator apps can build real (not hollow) proofs on.

## Verdict legend
- **FAITHFUL** — matches dregg1 including fail-closed cases.
- **PORTALED** — crypto honestly deferred to a §8 carrier; the state machine around it is real.
- **PARTIAL** — real state machine + value/existence gates, but a NAMED authorization gap (says exactly what).
- **SHADOW** — no-op / flag-flip / silent-alias standing in for real semantics. MUST fix before an app leans on it.

## Ledger

### Invocation + obligation
| Effect | Verdict | Note |
|---|---|---|
| `exerciseA` | **PARTIAL** | De-shadow REAL (recurses `inner` against the target, all-or-nothing, proven `execFullA_exerciseA_recurses`). Gate is connectivity-only (`confersEdgeTo`); the cap **facet-mask / `allowed_effects`**, per-inner target-permission cross-check, cap expiry, and revocation-channel (dregg1 apply.rs:2472–2643) are NOT executable. |
| `createObligationA` | **FAITHFUL** | (as documented escrow-alias) full real create gate: `authorizedB`, `0≤stake≤bal`, creator∈accounts, id-uniqueness. Gap: no `deadline_height` field (see CLOCK below). |
| `fulfillObligationA` | **PARTIAL** | Real state machine (returns stake to obligor, marks resolved, double-fulfill fail-closes). **`actor` threaded into NO gate** → anyone can fulfill any obligation, anytime. Missing: obligor-only, before-deadline, proof-verify. |
| `slashObligationA` | **PARTIAL** | Real state machine (stake→beneficiary, marks resolved). **No deadline/caller gate** → anyone can slash before deadline. Slash vs fulfill differ only by which party is credited. |

### Factory + slot-caveats
| Effect | Verdict | Note |
|---|---|---|
| `createCellFromFactoryA` | **PARTIAL** | Registry-existence + privileged-fresh-mint gates real; the keystone `createCellFromFactoryChainA_installs_program` (minted cell's `slotCaveats` = factory's declared caveats) is genuine + non-vacuous. Gap: create-time *envelope* validation (cap-template / field-range / mode / child-VK / budget) unmodeled — only the caveat-install slice. |
| slot-caveat enforcement (`setFieldA`→`stateStepGuarded`) | **FAITHFUL** | For the 6 modeled caveats (Immutable / MonotonicSequence / Monotonic / WriteOnce / BoundedBy / SenderAuthorized) — arm-for-arm vs `program.rs`, fail-closed proven (`stateStepGuarded_caveat_violation_fails`), on the LIVE path. Named gaps: (1) real gate is the post-effect program pass `execute_tree.rs:861` over the WHOLE new state, not per-field — so cross-slot caveats (`SumEqualsAcross`/`FieldDelta`/`AllowedTransitions`/`CapabilityUniqueness`/`RateLimit`, ~9 of ~15 kinds) are NOT representable in the single-field-scalar model; (2) `SenderAuthorized` witness-uniqueness is a §8 portal; (3) genesis `None`-old fail-mode collapsed to default-0. None of the 6 accepted-for-free. |

### Lifecycle + seal
| Effect | Verdict | Note |
|---|---|---|
| `cellSealA` / `cellUnsealA` / `cellDestroyA` | **FAITHFUL** | Real discriminant state machine Live↔Sealed↔Destroyed, proven terminality/seal/not-sealed teeth, DeathCert bound. Minor gap: `cellDestroy` omits dregg1's `CertificateMismatch` cell-id binding check. (dregg1 has no global `accepts_effects` dispatch gate either — Lean matches honestly.) |
| `refreshDelegationA` | **FAITHFUL** | Self-only, fresh parent c-list snapshot, proven `_snapshots_parent`. Minor gap: elides epoch / staleness / clist-commitment metadata. |
| `createSealPairA` / `sealA` / `unsealA` | **FAITHFUL / PORTALED** | Genuinely DE-SHADOWED — capability ACTUALLY moves through the box (`unsealChainA_grants_sealed_cap` is the witness a flag-flip could never satisfy). AEAD = honest §8 portal. Lean is equal-or-STRONGER than dregg1 (held-payload confinement gate; rejects ≥ dregg1) → safe-direction divergences, not soundness holes. |

### Queue + committed-escrow + pipeline
| Effect | Verdict | Note |
|---|---|---|
| `queueAtomicTxA` | **PARTIAL** | Atomicity REAL (commits IFF every sub-op commits, proven `_commits_iff_all`/`_atomic_witness`). Gap: per-sub-op writer/owner ACL collapsed into the single `stateAuthB` abstraction (not dregg1's literal `fields[5]`/`fields[2]` byte-compare). |
| `queuePipelineStepA` | **FAITHFUL** | Real dequeue-then-fanout; source owner gate + each sink ACL+capacity gate, all-or-nothing; `routing_witness` proves the message genuinely moves source→every sink. |
| `createCommittedEscrowA` | **PORTALED** | Now an HONEST §8 portal (`hidingProof : Bool` is the executable shadow of the range-proof verify) — no longer silently == plain escrow on the create side. |
| `releaseCommittedEscrowA` | **SHADOW** | SILENTLY ALIASED to plain escrow release. No `claim_auth` vs `recipient_commitment`, no recipient-matches-claim check (dregg1 apply.rs:2271–2285). Commits on `id` alone. |
| `refundCommittedEscrowA` | **SHADOW** | SILENTLY ALIASED to plain escrow refund AND drops the timeout fail-closed case (dregg1 requires `block_height > timeout_height` + `claim_auth` vs `creator_commitment`, apply.rs:2371–2393). Most adversarial gap: can refund BEFORE deadline without claim auth. |
| `pipelinedSendA` | **PARTIAL** | Divergent fail-mode: Lean neutral-commit at apply (post-resolution model, honest doc); dregg1 is a HARD ERROR at apply (`PreconditionFailed`) because resolution must precede apply. |

## The systematic theme — a missing STATE DIMENSION (time)
Every PARTIAL/SHADOW temporal gap shares one root cause: **`RecChainedState` has no block-height / logical clock, and escrow/obligation records carry no deadline field.** So dregg1's deadline gates (obligation before-deadline, slash post-deadline, committed-refund timeout, bridge timeout) and identity gates (obligor-only fulfill) are carried as Prop hypotheses at the theorem layer instead of being executably checked. This is one foundational model-shape decision, not N per-effect bugs.

Also recurring: **identity gates not threaded** — fulfill/slash take `actor` but never gate on it (independent of the clock; a straightforward fix).

## What the L2 apps can trust today
- **Conservation, capability non-amplification, confinement, no-double-spend, slot-caveat permanence, lifecycle, cap-movement-through-seal** — all real and provable on the executor.
- **NOT yet trustworthy on the temporal/identity axis**: auction reveal-deadlines, bounty deadline-gated fulfillment, bonded-swap slash timing, committed-escrow claim-auth. An app proof touching these would be hollow until the clock dimension + identity threading land.
