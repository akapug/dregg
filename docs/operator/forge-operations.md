# Operator manual — running a dregg forge (assurance, keys, CI, bonds)

*How to operate the dregg-native code forge (`dregg-doc`, `forge-ci-runner`). Grounded in the real
API; every config knob points at a type. Companion to `docs/OPERATOR-ONBOARDING.md` (node/federation)
and the guarantee ground-truth `docs/reference/forge-as-a-grain.md`. Honest split: the operational
*model* and the in-process surfaces are real today; the cross-node HTTP/gossip transports are named
seams (called out inline), so a single-host / test-federation deployment is fully operable now and a
multi-node one is operable as those transports land.*

## The one decision that matters: which CI assurance

A required check carries a `CiAssurance` policy (`dregg-doc/src/ci_assurance.rs`). This is the
operator's core choice — read the tradeoff off the enum's doc block and pick the point you want:

| rung | you trust… | cost | catches a lying host? | operate it when… |
|---|---|---|---|---|
| `TrustedSigned{keys}` | the signing host | ~free | no (detect out-of-band) | internal repos, low stakes |
| `ReExecuted{keys, quorum}` | ≥quorum honest re-executors + a deterministic build | quorum× compute | **yes, by agreement** | **the default for public CI** |
| `OptimisticChallenge{keys, window}` | nobody, if anyone re-runs during the window | ~free happy-path | yes, if challenged in time | high throughput + a watchful challenger set |
| `Proven{vk}` | only STARK soundness | very high (bounded checks only) | yes, unconditionally | a small, high-value, deterministic check |
| `Staked{bond_ref, inner}` | inner + a bond backs it | inner + escrow | inner + **money on the line** | anything you want economically deterred |

**Recommended default: `Staked{ ReExecuted{quorum: 3}, bond }`** — an independent-re-execution majority
with a slashable bond. This is the optimistic-plus-stake model (like optimistic rollups) and is the
right choice for general CI, because zk-proving a general build is impractical (`Proven` is for bounded
checks — see the reference doc). Build the check with `RequiredCheck::ci_run_assured(id, command_id,
editor_seed, region_seed, assurance)`.

## Set up the trusted-key set (governed, rotatable)

`keys` in every rung is a `GovernedKeySet` (`ci_assurance.rs`), not a bare list. Operate it:
- **Who may add/remove a key** — `KeyGovernance::Operator` (a single operator key) or
  `GovernedNamespace{namespace, threshold}` (a committee threshold swap via `governed-namespace`). Pick
  `GovernedNamespace` for a shared/public forge so no single operator can inject a trusted signer.
- **Add a runner's key** — `admit(key, epoch)`; **retire one** — `revoke(key)` (its verdicts stop
  satisfying immediately, `active_keys()` excludes it); **rotate** — `rotate(old, new)`.
- The host executor signing seed is installed via `agent_platform::AgentPlatform::with_executor_signing_key`
  / the CWM `fire_advance_step_signed(.., seed)`; the *public* key (`dregg_sdk::executor_pubkey_from_seed`)
  is what you `admit` into the set. A revoked/rotated-out host can no longer produce satisfying verdicts.

## Run a CI check (the confined runner)

`forge_ci_runner::run_check_confined(history, command_image, argv, command_id, host_signing_seed,
editor_seed, region_seed)` (macOS Seatbelt today; the firmament tier):
- It **materializes the PR's committed code itself** from the patch `History` into a fresh jail dir —
  do NOT hand it a pre-seeded working tree (that path is refused, `MaterializationMismatch`).
- It runs `command_image argv` confined, captures `{exit_code, output_digest}`, and commits a signed
  `CiVerdict` bound to `input_root == substrate_commit(merged_graph)`.
- **The check command MUST be deterministic** — a flaky build is a false-conviction hazard under
  `ReExecuted`/`OptimisticChallenge` (the operator's responsibility; the jail fixes inputs but the
  command must not embed wall-clock/RNG). Pin toolchains; use `--frozen`/lockfiles.

For `ReExecuted{quorum: N}`, operate **N independent runner hosts** (distinct governed keys), each
running `run_check_confined` over the same PR; collect the N signed verdicts into the
`CiRunWitness.attestations`. A divergent one is a conviction.

## Bonds + slashing (the `Staked` rung)

- **Post a bond at job intake** — `staked_bond::post_bond(host_cell, bond_cell, StakedBond{bond_ref,
  amount, poster, asset, beneficiary_on_slash})`. `beneficiary_on_slash`: `Burn` (default), `Pool(cell)`,
  or `Challenger(cell)` (pay the party who proved the lie). **Seam:** who *calls* `post_bond` at intake
  is deployment wiring — wire it into your CI-job admission.
- **On a conviction** the forge yields a `SlashOutcome` (conserving, one-shot); fire its transfer through
  your executor. A `Conviction` is unforgeable (only a real `evaluate` divergence mints one), so an
  honest host is never slashed absent a real detected lie.
- **On satisfaction** the bond is releasable to the host (`release_bond`).

## Challenges (the `OptimisticChallenge` rung)

A challenger who re-runs a verdict and finds divergence calls `ci_assurance::post_challenge(divergence,
challenger_key)` → a signed `blocklace` block. `detect_upheld_challenge` convicts iff the challenger is
an **active governed key** and the block contradicts the host verdict on the same run. **Operate a
challenger set** (trusted re-executors watching the feed). **Seam:** the live gossip that disseminates
challenge blocks across nodes is not yet wired — a single-host or shared-`Blocklace` deployment works
today.

## Federation publish (witness + cross-node replay)

- **Grain heap-root** — `sandstorm-bridge::publish_grain_root(...)` builds the owner-signed
  `UpdateCommitmentRequest`; a visitor `fetch_ledger_root`s it from `GET /api/cell/{id}` and verifies a
  served card against the *ledger's* root (not the host).
- **Nullifier-accumulator root** — `dregg_doc::publish_nullifier_root(...)` (identical pattern) so
  cross-node anti-replay holds via the ledger.
- **Seam:** both build node-acceptable signed requests; the live `POST /cells/update-commitment` /
  `GET /api/cell/{id}` HTTP calls are the only unwired part — a node operator posts these at each honest
  checkpoint. On a stock node `state_commitment` is the whole-cell BLAKE3 absorbing the heap-root; a
  deployment surfaces the heap-root as the committed value.

## What is operable today vs. the named transport seams

**Operable now (single-host / shared-state / test-federation):** the assurance policy + governed keys,
the confined runner + re-execution audit, the bond post/slash/release, the challenge detection over a
shared `Blocklace`, and the publish/fetch request construction + verification. All are unit-covered.

**Named seams (multi-node live wiring):** the federation HTTP POST/GET, the cross-node challenge gossip,
`post_bond`-at-intake, a cross-node stake registry, and multi-file repo trees. See
`docs/reference/forge-as-a-grain.md` for the full typed-seam list. None is a soundness hole — each is a
transport/wiring step over machinery that already verifies.
