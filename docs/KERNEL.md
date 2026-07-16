# The verified kernel

The Lean metatheory under `metatheory/Dregg2/` defines the kernel and proves the
guarantees a light client relies on. The skeptic-facing ledger of exactly what is proved
— and the four honesty labels — is `metatheory/CLAIMS.md`; `metatheory/Dregg2/Claims.lean`
re-pins every keystone with `#assert_axioms`, which fails the build unless the theorem's
entire axiom set is `{propext, Classical.choice, Quot.sound}`. "Proved" below means that:
free of the kernel open-hole axiom, modulo the named §8 interface obligations that are, by
design, the circuit's job and never Lean's.

## Cells and the four substances

A cell holds four substances, each a distinct epistemic mode (`cell/src/state.rs`; the
kernel-reserved system-root slots `DELEG`/`NULLIFIER`/`COMMIT` are indices 4/5/6 of the
`system_root` module, `state.rs:68–90`):

- **value** — per-asset signed (`i64`) balances. An asset *is* its issuer cell, which
  carries −supply, so every asset's units sum to identically 0. Conserved knowledge:
  movable, never creatable.
- **state** — programmable slots plus a nonce (the freshness coordinate). Revisable
  knowledge, governed by the cell's own program.
- **authority** — a capability tree. Productive knowledge: what the cell can construct a
  witness for.
- **evidence** — append-only nullifier / commitment / epoch ledgers. The only *monotone*
  substance: knowledge once constructed is recorded and never un-constructed.

## Conservation (Σδ = 0)

A turn moves, withholds, or erases units but never creates or destroys them. The shared
lemma is `Dregg2.Conserve.sum_conserve_of_deltas_zero` (`Dregg2/Conserve.lean:49`):
deltas summing to zero preserve the measure. The "no free copy" minimality fact —
governing both the operational and categorical views — is
`Dregg2.Core.noClone_of_invariant_tensor` (`Dregg2/Core.lean:206`): under an additive
cancellative monoid, an invariant tensor forces `count A = 0`. Conservation is realized as
a theorem about the running executor, not an assumed primitive:
`Dregg2.Exec.conservation_step_realized` (`Dregg2/Exec/StepComplete.lean:92`) discharges
the abstract `Core.conservation_step` from `Dregg2.Exec.cexec_attests`
(`Dregg2/Exec/StepComplete.lean:75`), which proves the executable machine attests all four
step-invariant conjuncts.

## The verbs and the executor

The six-color linearity coloring of effects is total and exhaustive —
`Dregg2.Spec.Conservation.linearity` over the `Effect` enum
(`Dregg2/Spec/Conservation.lean:164`; the colors are Conservative / Monotonic / Terminal /
Generative / Annihilative / Neutral — transfer = conservative, mint = disclosed generative,
setField = neutral), with `linearity_examples` (`:171`) witnessing it discriminates. The
deployed effect vocabulary (`turn/src/action.rs`, `enum Effect`) is the full catalog
(Transfer, GrantCapability, Introduce, NoteCreate/NoteSpend, SpawnWithDelegation, Mint/Burn,
ShieldedTransfer, the reactive Promise/Notify/React, …), and the Rust `Effect::linearity`
mirrors the Lean coloring with the same six `LinearityClass` colors. The executor is
one gated entry: `execFullAGated` reads `gateOK na s` on the same pre-state it then steps
(within-cell no-TOCTOU is automatic), and the running kernel is reached through the
`@[export]` C-ABI entries in `Dregg2/Exec/DistributedExports.lean` so the Rust runtime
computes its verdict *from* the verified Lean. The unbounded life of a cell is sound by a
guarded bisimulation to a golden oracle: `Dregg2.Exec.livingCell_sound`
(`Dregg2/Exec/Cell.lean:102`).

## Authority = production under non-forgeability

You hold a capability iff you can construct the witness the kernel accepts. The admission
gate is one fail-closed conjunction, `Dregg2.Exec.gateOK` (`Dregg2/Exec/FullForestAuth.lean:486`),
over four legs: `credentialValidG` (the witness verifies — non-forgeability, `:433`),
`capAuthorityG` (kernel cap narrowing, `granted ⊆ held`, `:443`), `caveatsDischarged`
(`:467`), and the revocation gate.

- **Attenuation narrows.** `Dregg2.Spec.Guard.attenuate_narrows`
  (`Dregg2/Spec/Guard.lean:207`) — attenuation only narrows admission (a meet-semilattice,
  not Heyting).
- **Generation traces to a held generator.** `Dregg2.Spec.gen_step_traces`
  (`Dregg2/Spec/Authority.lean:391`) — every new edge of one authorized step traces to an
  authorized generator; the whole-history closure is
  `Dregg2.Spec.only_connectivity_begets_connectivity`
  (`Dregg2/Spec/Authority.lean:456`).
- **Non-amplification.** `Dregg2.Spec.introduce_non_amplifying`
  (`Dregg2/Spec/Authority.lean:294`) — a Granovetter introduction confers no more than the
  introducer holds; the whole gated turn preserves this:
  `Dregg2.Exec.execFullForestG_no_amplify` (`Dregg2/Exec/FullForestAuth.lean:1014`).

Authority is *not* affine descent (a quantity that drains); it is a proof obligation you
re-discharge at every point of use.

## The light client cannot be fooled

The apex is `Dregg2.Circuit.lightclient_unfoolable`
(`Dregg2/Circuit/CircuitSoundness.lean:570`). Its only inputs are what a light client
actually has — the public inputs and the proof; it takes no `pre`/`post` and no
`StateDecode` as hypotheses. From `verifyBatch vk pi π = accept` plus named §8 floors it
derives that there *exists* a genuine kernel transition committing to exactly the published
roots. Over the whole history this is
`Dregg2.Circuit.light_client_verifies_whole_history`
(`Dregg2/Circuit/RecursiveAggregation.lean:200`): checking only the aggregate root yields
that every turn executed correctly and the chain is correctly ordered (no
reorder/drop/insert). Conservation rides the same root with no prover-supplied
state-continuity hypothesis (`Dregg2.Circuit.conserves_from_verification`,
`Dregg2/Circuit/RecursiveAggregation.lean:339`), and the anti-ghost tooth is
`Dregg2.Circuit.tampered_aggregate_cannot_bind`
(`Dregg2/Circuit/RecursiveAggregation.lean:544`): no sound aggregate can attest a reordered
chain.

### The five guarantees

The assurance case (`Dregg2/AssuranceCase.lean`) states the headline guarantees as
theorems:

- `Dregg2.authority_guarantee` (`:166`) — every committed step is authorized.
- `Dregg2.conservation_guarantee` (`:259`) — units conserve (Law 1).
- `Dregg2.integrity_guarantee` (`:412`) — the post-state projection is exactly the fold of
  the blind-emitted memory trace; tampering an un-written address breaks the bind.
- `Dregg2.freshness_guarantee` (`:581`) — the nonce/freshness coordinate advances; replay
  is excluded.
- `Dregg2.unfoolability_guarantee` (`:666`) — the light client, checking only a succinct
  root, cannot be shown a forged history.

## Open (named residuals, not undone)

The kernel keystones above are `#assert_axioms`-clean. The genuinely-open frontier is short
and named (full list and labels in `metatheory/CLAIMS.md` § OPEN):

- **The macaroon ↔ cap arrow, beyond the coherent overlap.** The credential is one
  authority seen four ways (biscuit · macaroon · cap · zk), all refining `granted ⊆ held`.
  The convergence arrow is proved on a coherently-built bridge node:
  `Dregg2.Authority.CaveatCapBridge.chainGateG_implies_capAuthorityG`
  (`Dregg2/Authority/CaveatCapBridge.lean:168`) — on a node whose `.capTpDelivered`
  `granted` IS the macaroon chain's narrowing (`mkBridgeNode`), a verifying-and-admitting
  caveat chain forces the kernel cap gate (`chainGateG na = true → capAuthorityG na = true`),
  non-vacuous in both polarities (`…_devac`, `:357`) and `#assert_axioms`-pinned
  (`:592`, `:606`). What stays open: in `gateOK` the two faces are still AND-ed over
  disjoint state on an *arbitrary* `NodeAuth`; the proven arrow covers the coherent
  construction, not every production node shape. A genuine fail-closed conjunction
  (defense-in-depth, not a hole); the general arrow is the research edge
  (`metatheory/CONSTRUCTIVE-KNOWLEDGE.md` §12).
- **`Proof.Refine` full simulation diagram.** The conservation + intra-vat integrity
  refinements are pinned (`Dregg2.Proof.refine_conservation`,
  `Dregg2/Proof/Refine.lean:65`, et al.); the full abstract forward simulation needs an
  abstract small-step relation absent from `Core`.

Two residuals keep their names but are discharged — documentation, not open work:

- **Settlement soundness rides the deployed predicate.** `settlement_soundness`
  (`metatheory/Metatheory/SettlementSoundness.lean:153`) takes `BindsLiveAuthority` as a
  typed hypothesis, and the deployed settlement predicate is proven to satisfy it:
  `deployedSettle_binds_live_authority` (`:305`), discharged from the deployed tip-time
  revocation gate (non-tautological — unlike the definitional `liveSettlement_binds`,
  `:244`), with the negative pole `branchSettle_NOT_binds` (`:408`) separating faithful
  from unfaithful settlements.
- **The epoch-stamp circuit residuals.** `RevokeDelegationEpochResidual` /
  `SpawnEpochStampResidual` / `RefreshEpochStampResidual` are CLOSED by the per-effect
  descriptor cutover: each deployed descriptor's forced PRODUCT component
  write-gate-forces the epoch stamp, the conjunct is dropped from the bridges, and each
  `def` survives only as documentation of the forced proposition — "CLOSED (NOT an open
  residual) … Nothing reads it" (`Dregg2/Circuit/EffectRefinement.lean:359`, `:819`;
  `Dregg2/Circuit/EffectRefinementBatch2.lean:296`).

Note: `settlement_soundness` lives in `metatheory/Metatheory/` (the constructive-knowledge
*logic* tree), not `metatheory/Dregg2/` (the *verification* of the dregg2 system); the
distinction is `metatheory/CONSTRUCTIVE-KNOWLEDGE.md` §13. The macaroon-arrow bridge
resolves under `metatheory/Dregg2/Authority/`, and every theorem cited above as a kernel
keystone resolves under `metatheory/Dregg2/`.
