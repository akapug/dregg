# forge-as-a-grain — the CI/witness soundness architecture (grounded at HEAD)

*A file:line-grounded record of what the forge-as-a-grain soundness stack IS after the
review → fix → bridge → re-review → heal-forward → weld epoch. Present-tense what-is; every claim
points at code; every trusted step and every unbuilt seam is named. Companion to the vision doc
`docs/deos/DREGG-FORGE.md` (which narrates the design); THIS is the ground truth of the guarantees.*

## The two properties, and how each is check-don't-trust

**(i) "CI actually passed against this PR's code."** Closed by three layers:
- **The check binds the work.** `dregg-doc/src/ci_verdict.rs` — `CiVerdict{input_root, command_id,
  confinement_id, exit_code, output_digest}` is committed *inside* the signed genesis turn of a CI-run
  cell; `CheckRequirement::CiRun::satisfied_by` (`check.rs`) re-derives `planned_ci_run_hash` from the
  presented verdict and refuses unless it equals the receipt's `turn_hash` (`VerdictNotCommitted`), so a
  loose verdict can't forge the binding. `input_root == substrate_commit(pr.merged_graph())`
  (`pull_request.rs::input_root`) binds it to *this PR's* landed code; `exit_code != 0` refuses.
- **The runner runs the real code, confined.** `forge-ci-runner/src/confined.rs::run_check_confined`
  takes a `&History`, *self-materializes* it into a fresh dir (`materialize.rs`), runs the check under
  `spawn_pd_confined_exec` (firmament), and `input_root_of_dir` (`lib.rs`) refuses any tree that isn't the
  faithful materialization (`verify_faithful_materialization`: `document.txt == render(replay(history))`,
  no stray files) — closing serve-X-commit-Y.
- **A lying host is caught by re-execution.** `reexecute_and_verify` (`confined.rs`) re-materializes from
  the auditor's *trusted* `&History` into a fresh dir, re-runs, and returns `HostLied{field}` on any
  divergence — the audit is independent, not circular.

**(ii) "The host can't tamper with what it serves."** `sandstorm-bridge`: `/var` commits via the *real*
`dregg_circuit::heap_root::compute_heap_root` (`cell.rs`), the served root is owner-attested
(`bridge.rs::RootAttestation`), and `verify_served_against_ledger` (`bridge.rs`) checks the card is a leaf
under a root the visitor fetched from the **federation** (`fetch_ledger_root` over `GET /api/cell/{id}`),
published by `grain.rs::publish_grain_root` (owner-signed `UpdateCommitmentRequest`, mirroring
`node/src/api.rs` exactly). A host holding the owner key still can't beat the ledger's committed root.

**Anti-replay.** `ci_verdict.rs::CiNullifierAccumulator` — a committed `commit::MerkleTree` with a
shareable `[u8;32]` root + membership/non-membership proofs; `land_checked` refuses a replayed verdict.

## The assurance lattice (`dregg-doc/src/ci_assurance.rs`) — the tradeoff is legible at the type

`CiAssurance`, weakest→strongest, each with a uniform `Trust / Cost / Latency / Determinism / Catches-a-liar?`
doc block:
- `TrustedSigned{keys}` — one signed work-bound verdict. Catches a liar? No (detect out-of-band).
- `ReExecuted{keys, quorum}` — ≥quorum distinct-active-key, turn-bound, same-work matching attestations;
  a divergence → `Convicted`. Trust: ≥quorum honest re-executors + deterministic build. **Catches a liar: yes.**
- `OptimisticChallenge{keys, window}` — provisional; a challenger's divergent verdict posted to the
  `blocklace` is an equivocation `detect_upheld_challenge` convicts (anti-Sybil: creator ∈ active keys).
- `Proven{vk}` — a real `dregg-circuit` STARK (`StarkCiProofVerifier`, `ci_attestation_program`): the
  verdict is bound as public inputs (`PiBinding`) + a pass-gate (`exit_code==0`) constraint; verification
  trusts only STARK soundness + the vk. **Scope: proves the pass-gate + verdict-binding, NOT the
  execution** (see seams).
- `Staked{bond_ref, inner}` — wraps any inner policy; an inner `Conviction` yields a real conserving,
  one-shot forfeiture (`staked_bond.rs::SlashOutcome`, over the `dregg_cell` balance ledger + `escrow_sealed`
  consumed-flag). `Conviction` is **unforgeable** — private fields + `evaluate`-only minters + a
  `compile_fail` doctest.

Keys are a `GovernedKeySet` (`ci_assurance.rs`) — governed (Operator | GovernedNamespace threshold) +
rotatable/revocable, closing the static-key finding.

## The trusted steps (named, legitimate) and the unbuilt seams (named, typed)

**Legitimate named trust:** `ReExecuted` rests on "≥quorum independent re-executors are honest AND the
build is deterministic," anti-Sybil'd by `KeyGovernance`. `Proven` rests on STARK soundness + the vk.
These are the intended assumptions, not hidden.

**Unbuilt seams (typed interfaces / stubs with a real drop-in point):**
- **The `Proven` execution proof (a bounded, honest scope — NOT the load-bearing thing).** `Proven` today
  proves the pass-gate + verdict-binding, not that `output_digest` is the genuine function of the input.
  The honest way to close it (settled 2026-07-08): DON'T marry dregg's `p3-recursion` *fork* to an extant
  zkVM's Plonky3 (SP1 etc.) — the two forks' `StarkConfig`s (field, hash, FRI params) diverge and drift
  every release, a maintenance sinkhole. Instead bind an external zkVM proof via
  `circuit-prove/src/custom_proof_bind.rs` (verify the zkVM proof out-of-circuit with its own SDK, bind the
  commitment) — fork-agnostic, works for any zkVM. AND: zkVM proving of a general build is ~10⁴–10⁶× native
  (minutes–hours on a GPU), so `Proven` is realistic only for **bounded, high-value, deterministic checks**,
  not arbitrary `cargo test`. **The general-CI soundness is NOT the zkVM** — it is the already-built
  *optimistic* stack (`ReExecuted{quorum}` + `OptimisticChallenge` fraud-proofs + `Staked` slash), the same
  design optimistic rollups use precisely because zk-proving general execution is too slow. `Proven` is a
  premium rung, not a missing floor.
- **Live gossip dissemination** — `detect_upheld_challenge` + the equivocation logic are real (over a real
  `Blocklace::insert`); only the network transport that fills `challenge_lace` across nodes is out-of-test.
- **Federation write TRANSPORT (schemes + signatures are real, only the HTTP call is stubbed).**
  `publish_grain_root` (grain heap-root) AND `publish_nullifier_root` (the accumulator root — cross-node
  anti-replay, `ci_verdict.rs`) both build node-acceptable owner-signed `UpdateCommitmentRequest`s and
  `fetch_*_root` reads them back; only the live `POST /cells/update-commitment` / `GET /api/cell/{id}` is
  out-of-test. Caveat: a stock node's `state_commitment` is whole-cell BLAKE3 *absorbing* the heap-root; a
  deployment surfaces the heap-root as the committed value (schemes + wire already match).
- **Deployment wiring** — host posts the bond at CI-job intake (`post_bond` exists; who-calls-it is
  out-of-crate); a cross-node stake registry (`bond_ref → holding cell`); multi-file repo trees (a PR is
  one document today, so `materialize` is one file; a path→doc repo makes it a fan-out).

## Crates

`dregg-doc` (root-workspace member AND default-member — `Cargo.toml:16`/`:23`; its own `Cargo.toml:28`
notes the fold, with the heavy deps optional behind `cell-heap`/`substrate`/`rope`) — the forge core:
PR/merge/review, CiVerdict/CiRun, CiAssurance, staked_bond, nullifier accumulator. `forge-ci-runner`
(its own excluded workspace root, `Cargo.toml:68`; its `src/materialize.rs` builds against an older
dregg-doc `AtomContent` API — the named seam blocking its fold, `Cargo.toml:57-59`) — the confined
producer + re-executor + the doc→worktree materialization. `sandstorm-bridge` (member) — the witnessed
cloud serving.
