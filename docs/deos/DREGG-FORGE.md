# The dregg-native forge — code collaboration with no git, all the way down

*Design note (2026-07-07). A code forge that is NOT a git host: dregg's own patch theory IS the
version control, a repo IS a cell, a commit IS a receipted turn, and a pull-request review IS the
stitcher. Sibling of `GRAIN-HOMESERVER.md` — the homeserver-grain hosts the community, the
forge-grain hosts its code; both ride the membrane. This is a WELD doc: the substrate already
exists (census below), the frontier is the collaboration surface + the federated hosting.*

## The thesis

Every code forge is a git host with a review UI bolted on. Git is the substrate; the forge is
chrome. Dregg inverts it: the substrate is **patch theory + capabilities + verified turns**, so the
forge is not "a nicer GitHub" — it is *what version control looks like when the history is
cryptographically owned, the merges are provably sound, and every operation is a cap-gated receipted
turn.* No git. Dregg has, as ember puts it, full Pijul.

## The substrate (already built — census, not aspiration)

- **The VCS core IS Pijul, operational.** `dregg-doc/src/depend.rs` header: *"The Pijul theory of
  patches made operational: patch dependencies, unrecord (pull a patch — and only what truly depends
  on it — out), cherry-pick (apply onto another branch), and commute (the independence test)."*
  `patch.rs` (`Patch`/`Op`/`PatchId`, compose), `merge.rs` (the **pushout** merge — Mimram–Di Giusto,
  total/commutative/associative/idempotent), `resolution.rs`/`ConflictRegion` (conflicts are
  first-class objects, never silent overwrites), `blame.rs`, `history.rs`. This is a sound-merge VCS,
  not a diff-and-pray one.
- **History lives IN the cell.** As of 2026-07-07 (`3f754287e`), a document's whole patch/blame chain
  is committed heap state (`doc_heap.rs` `COLL_HISTORY`): reopen reconstructs history, every tampered
  history byte is refused, edit ORDER is committed. A repo's log is not a side-file — it is the cell.
- **A git-face already exists over it.** `deos-zed-full/src/cell_git.rs`: *"each save = a verified turn
  = a commit; the dregg-doc patch theory"* — it serves `status`/`blame`/`show`/`load_commit`/`diff`/
  `branches`/`head_sha`/`revparse`/`search_commits`/`file_history` off the patch chain + `History::
  replay_to`. Editors that speak git talk to dregg without knowing git isn't underneath.
- **Multi-author fork/merge IS branch-and-stitch.** `starbridge-apps/branch-stitch-multiplayer` +
  `distributed_card` + `shared_fork`: two principals fork one artifact, each edits, stitch by pushout,
  a true conflict surfaces as a `ConflictRegion`. That IS a pull request: fork → diverge → review the
  conflict → resolve by a verified patch.
- **I-confluent offline merge.** `dregg-merge` (CvRDT join) for the freely-mergeable ops.

## The mapping (git noun → dregg noun)

| Forge concept | Dregg realization | Status |
|---|---|---|
| repository | a cell (or a path-tree of cells, as `cell_git` maps paths→cells) | substrate built |
| commit | a receipted verified **turn** (a patch applied, cap-gated) | built (`cell_git`) |
| history / log | the patch chain in the cell's heap (`COLL_HISTORY`) | built (2026-07-07) |
| branch | a fork of the repo cell (the membrane fork) | built (branch-and-stitch) |
| merge | the **pushout** (`dregg-doc::merge`) — provably sound | built |
| conflict | a first-class `ConflictRegion` | built |
| pull request | fork → stitch; the diff IS the two forks' divergence | built (mechanism) |
| code review | the **stitcher** over the `ConflictRegion` + `resolution` | built (mechanism) |
| blame | `dregg-doc::blame` over the patch chain | built |
| CI check | a verified turn whose receipt gates the merge (a `ProofCondition`) | primitives exist |
| access control | capabilities — who may push/merge/review is a cap you hold | built (the whole kernel) |
| forge host | a **forge-grain** on the community platform | FRONTIER (this doc) |

## The frontier (what to build)

Everything above is a substrate; the forge is the *product surface* welded onto it:

1. **The repo-as-cell object + a real branch/PR model.** `cell_git` today serves ONE synthetic `main`
   branch (read-mostly). A forge needs first-class branches (repo-cell forks), a `PullRequest` object
   (a proposed fork + its target + the stitch state + review threads), and merge-gated-on-review
   (the target's cap-holder resolves the `ConflictRegion` → a verified merge turn). Branch-and-stitch
   already gives the fork/diverge/stitch; the PR is the named, reviewable, cap-gated wrapper.
2. **CI as receipted turns.** A check is a turn whose `ProofCondition`/receipt is the merge gate: the
   merge cannot land until the check-turns are committed. No trusted CI runner — the proof is the pass.
   (Composes with the confined-brain grain: a CI job is a confined body driving verified turns.)
3. **The federated forge-grain.** A repo lives on a **grain** (like the homeserver-grain): confined,
   cap-metered, R2. A repo hosted on box A is fork-able by box B over the membrane; a PR crosses the
   same `MembraneEnvelope` a co-driven card does. Federation = your repo is reachable from anyone's
   client, push rights are a cap you granted. This is where forge-grain meets homeserver-grain: the
   community platform hosts both the chat rooms and the code.
4. **The surface (a deos-view face).** Repo browser / diff / review / blame as `deos-view` cards, so
   the forge paints in every glass (cockpit, browser, Discord, terminal) — like the other reflective
   cards. `cell_git` already computes the data; the forge card renders it.

## THE FULL COMPOSITION (3-lane census, 2026-07-08) — it is ONE weld, not reinvention

A comprehensive census of the grain economy (mandate/workflow/gateway + hosting/lease/economy/grain +
market/bounty/orchestration) found that the ENTIRE forge-as-a-grain body already exists and composes.
The map:

| Lifecycle leg | Existing crate / entry point |
|---|---|
| List + rent the runner | `grain-commons::GrainRegistry`/`RentQuote` → `agent-platform::AgentPlatform::rent` |
| Fund + meter the lease (prepaid, fused meter⊗draw); lapse/reap | `hosted-lease::HostedLease` · `bill_period` · `reap_if_behind` |
| Settle rent (conserving, exactly-once) | `hosted-durable::{Settlement, LeaseCharge, SettleReceipt}` |
| Confine the runner body (one egress door) | `grain-jail::ConfinedBrain` + firmament `process-pd` / `spawn_pd_confined_exec` |
| The CI pipeline (DAG: fetch→build→test→report, no-skip, exact-+1) | `compartment-workflow-mandate` (CWM) `cwm_cell_program` + `advance_step` |
| Per-step COMPUTE budget tooth (`SPEND_ACCUM ≤ BUDGET`) | CWM `colonist_job` |
| Clearance (which runner role runs which step) | CWM `ClearanceDominates` root-bound lattice |
| Runner cap (rate/deadline/scope, revocable) | `tool-access-delegation` `Grant`/`fire_invoke`/`RevokeDelegation` |
| Runner identity + spend budget + caps body | `edge-mandate` `CapMandate` + `authorized_keys_line` |
| Artifact/log upload (volume-metered) | `storage-gateway-mandate` `fire_put` |
| Drive each step as a metered kernel turn | `agent-platform::drive_serving` → `grain-turn::ToolGatewayMinter` |
| Finalize + cross-node verify | `agent-platform::node::LocalNode` · `verify_landed`/`verify_r2` |
| Renter attestation (R2 ladder) | `grain-verify::GrainAttestation::verify_r2_for_renter` |
| Fork the runner (matrix / fan-out jobs) | `grain-fork::ConfinedSession::fork_two` (egress+budget attenuated) |
| CI-fan-out orchestration (N runners, one budget, audited) | `swarm-orchestration` (+ `agent-orchestration::audit_run`) |
| Pay to trigger / entitlement | `discharge-gateway` `PaymentEvaluator`/`ProofRequiredEvaluator` |
| **PR-as-a-bounty** (post→claim→submit→payout, no-double-pay) | `bounty-board` `BountyTreasury::payout` (conserving) |
| **CI-as-a-market-job** (post/bid/settle, conservation) | `compute-exchange` |
| Branch-protection (who changes the required-check set) | `governed-namespace` threshold-committee swap |
| **Terminal check-receipt the forge gate consumes** | ⚠ **THE ONE GAP — see below** |

## THE ONE WELD: the terminal check turn needs an executor-SIGNED receipt

Every drive path in the grain family (`agent-platform::drive*`, `grain-turn`, `node.land`) mints
`Finality::Final` but **`executor_signature == None`** — because `sdk/src/runtime.rs:78` builds the
`TurnExecutor` with no signing key and NOTHING in the family calls `set_executor_signing_key`. The
forge gate `RequiredCheck::CommittedReceipt` (`dregg-doc/check.rs:211-230`) refuses an unsigned receipt
fail-closed (`CheckRefusal::Unsigned`) and Ed25519-verifies over `canonical_executor_signed_message`.
The ONLY existing producer of a gate-valid receipt is `dregg-doc::ExecutorDrivenDoc` (`executor_drive.rs:182`
sets the key, `:466` Final). So the weld is exactly one signature domain. Two routes:

- **Route (i) — the forge's own executor signs the terminal check turn (RECOMMENDED first slice).** The
  runner drives the CI workflow through the grain path (metered, R2 — intermediate steps need no
  signature), and the TERMINAL "checks passed" turn is committed through the forge-grain's
  `ExecutorDrivenDoc` (signed), producing the receipt `RequiredCheck::satisfied_by` accepts. This is
  EXACTLY what `check.rs:40-43` already envisions ("the check job as a confined grain whose only egress
  is committing the check-turn receipt"). It does NOT change any grain host's security surface — the
  forge-grain's executor key is the trust anchor, pinned in `trusted_executor_keys`.
- **Route (ii) — sign the whole grain drive path (deeper unification, ember-decision).** Teach
  agent-platform/grain-turn to build their `AgentRuntime`/`TurnExecutor` with
  `set_executor_signing_key(grain_seed)` and register that pubkey as a trusted executor key. Then EVERY
  grain turn becomes forge-admissible — but the grain host's executor key becomes a forge trust anchor
  (a real security-surface change). Powerful; needs ember's call.

**The same weld closes the market side:** bind `bounty-board::payout` / `compute-exchange::settle` to
require the runner's terminal SIGNED receipt (the completion witness) — then *PR merges → the runner's
signed terminal receipt satisfies BOTH the forge merge gate AND the bounty payout*. One signature, three
gates lit (CI, bounty, market).

## The weld gaps, prioritized (the ONLY new code)

1. **Signed terminal receipt** (Route i or ii) — the one hard blocker.
2. **The forge↔grain binding** — a thin forge-grain that seeds a CWM charter, drives it, signs the
   terminal turn, and hands its receipt to `PullRequest::present_witness`. (`dregg-doc` has no dep on the
   grain crates today — a new binding crate or a dregg-doc feature.)
3. **`planned_advance_turn_hash`** on CWM/colonist_job (the pre-image so `RequiredCheck::committed_receipt`
   can name the terminal turn before it runs — the analogue of `ExecutorDrivenDoc::planned_turn_hash`).
4. **Completion-witness precondition** on `bounty-board::payout` / `compute-exchange::settle`.
5. **2→N orchestration arity** (both orchestration crates hardwire `enum Worker{A,B}`) + a **forge-event→
   turn settlement reactor** (auto-payout on merge; the `CoordinatorReactor` pattern is the template).

## Forge-as-a-grain (the design, grounded in tonight's confinement machinery)

The forge-grain is the homeserver-grain's sibling — and it reuses the EXACT machinery the
homeserver-as-a-grain proved (`docs/deos/GRAIN-HOMESERVER.md`): the firmament heavy-body `Confinement`
tier + `spawn_pd_confined_exec`, the membrane, the agent-platform lease. Three parts:

**(a) A repo is a cell; the forge SERVICE is receipted turns.** The repo state already lives in a cell
(the doc rides the umem-heap; the patch chain is committed heap state). Hosting = a **repo-grain**: a
cap-metered lease (`agent-platform` rent/host/meter/reap) over the repo cell, whose forge operations
(open PR, comment, approve, land) are the cap-gated receipted turns the forge core (`dregg-doc`
`PullRequest`/`check`/`review`) already produces. No heavy external process — the forge core is native
dregg, so the repo-grain is LIGHTER than the homeserver-grain (it needs no rocksdb/exec door).

**(b) Federated: a PR crosses the membrane between instances.** A pull request from another instance
is a fork carried over the SAME `MembraneEnvelope` a co-driven card rides (`card_carry` + the
branch-and-stitch machinery). Open-PR-from-elsewhere = `seal_fork` → cross → `rehydrate` → the target
holder reviews the `ConflictRegion` and lands a verified merge turn. Your repo is reachable from
anyone's client; push/merge rights are caps you granted and can attenuate/revoke. This is where
forge-grain meets homeserver-grain: the community platform hosts the chat rooms AND the code, over one
membrane.

**(c) CI-as-confined-grains — the part that MOST reuses tonight's work.** A check job is exactly the
heavy-body confined body we just built for the homeserver: `spawn_pd_confined_exec` a build/test runner
under a `Confinement` with {`write_path` = a scratch build dir, `exec_image` = the build tool,
`system_reads` for the toolchain, NO net (or one `net_out` proxy door for deps) — and crucially its
ONLY meaningful output is committing the check-turn receipt the merge gate demands (`check.rs`'s
`CommittedReceipt`). No trusted CI runner: the runner is a cap-bounded body that *physically cannot* do
anything but produce the receipt — the proof IS the pass, and the runner can't forge it, reach the
network, or touch anything but its scratch dir. The homeserver-grain proved a heavy rocksdb+tokio body
runs under the deny-default tier + the named doors; a CI runner is the same shape pointed at a build.

**The convergence.** homeserver-grain (community) + forge-grain (code) + CI-as-grains (verification) are
ONE substrate: the firmament confinement tier + the membrane + the agent-platform lease, pointed at
three services. Every one is confined, cap-metered, federated, and receipted — a town with a square, a
workshop, and a foundry, all built the same way, caps all the way down.

**CI-as-grains, welded to the WorkflowMandate (the census — DON'T reinvent it).** A CI pipeline is a
`compartment-workflow-mandate` (CWM) **charter**: a step DAG (fetch → build → test → report) where each
`advance_step` is a `Signature`-cap-gated, `step_clearance_ok` clearance-checked, `cwm_cell_program`-
enforced turn (teeth: `FieldLteField(STEP_CURSOR ≤ CHARTER_TERMINAL)`, `MonotonicSequence(STEP_CURSOR)`),
and the CWM **reactor** self-drives (one committed step wakes the next — the on-chain officer loop). Three
things weld:
1. **The step's WORK runs confined** — `spawn_pd_confined_exec` (firmament heavy-body tier) runs the
   build/test tool under {`write_path` = scratch, `exec_image` = the tool, no net or one proxy door}. The
   runner physically can't do anything but its build + advance the step.
2. **The terminal step's receipt IS the forge check** — the CI charter's terminal `advance_step` commits
   an executor-signed receipt; a forge `PullRequest`'s `RequiredCheck::CommittedReceipt{turn_hash}`
   (`dregg-doc/check.rs`) is bound to exactly that turn. So "merge requires CI green" = the forge merge
   gate requires the CWM charter to reach its terminal step. No trusted runner: the proof IS the pass,
   and the workflow-mandate + confinement mean the runner can neither forge the receipt nor escape.
3. **Metered** — the run's lease/discharge rides `discharge-gateway` / `agent-platform` (a CI run costs;
   the mandate discharges it), for free.
The weld keystone (first slice): bind a forge `RequiredCheck` to a CWM charter's terminal receipt and
prove a PR gates on the charter completing (incomplete → merge refused; terminal receipt → admitted).
The confined-exec of a real build is the terminal step's work, layered on. All in CLEAN crates
(compartment-workflow-mandate + dregg-doc + firmament).

**First buildable slices (safe zones, hbox-gated):** the repo-grain lease (agent-platform over a repo
cell — `agent-platform` is a root crate, coordinate) · the CI-runner grain (reuse
`spawn_pd_confined_exec` + `check.rs::CommittedReceipt` — firmament excluded ws + dregg-doc excluded ws,
CLEAN of the other terminal) · the membrane PR carry (extend `card_carry` — the pattern is proven). The
CI-runner grain is the highest-leverage next: it's the "no trusted runner" property, and it's a direct
composition of two things we shipped tonight (the confined exec-spawn + the receipt-gated check).

## Follow-ups (post 2026-07-07 adversarial-review + surfaces session)

The forge core is built + hardened + surfaced (card in every glass; `dregg-forge` CLI). Named residues:
- **Live-repo wiring (the primary one):** a `From<PullRequest> for deos_view::ForgeView` (+ diff/conflict/
  check/review sub-shapes) in `dregg-doc`, and the CLI driving a real `DocHeapCell` / `cell_git` on-disk
  tree instead of the in-memory demo. `cell_git` already computes status/diff/blame — this is the last mile.
- **Re-export `author_of_editor` + a `bound_author()` convenience** from the dregg-doc crate root (the CLI
  had to reproduce the editor-identity fold because `review` is a private module).
- **card-carry authenticity (F4c):** fold an originator signature over `fork_root` + verify on open, so the
  tooth is authenticity-not-just-integrity in-layer (today authenticity is the Matrix transport's job — see
  `card_carry_bridge.rs` honest-scope note); + the consistent-forge test.
- **world_bridge (F4b):** confirm the deos-hermes test on hbox (the bind-semantics fix is code-correct; the
  local build kept timing out).
- **THE CI-RUNNER GRAIN (the exciting next build):** `spawn_pd_confined_exec` a check runner under the
  heavy-body `Confinement` whose only output is committing the `check.rs::CommittedReceipt` — the "no trusted
  runner, the proof IS the pass" property, a direct composition of two things shipped 2026-07-07, both in
  CLEAN excluded workspaces (firmament + dregg-doc). See the forge-as-a-grain design above.

## Why this is not "GitHub on dregg"

- **The history is owned + unforgeable.** A commit is a cap-gated receipted turn; a forged history is
  inexpressible (the heap root binds the patch chain). You cannot rewrite someone's blame.
- **The merge is a theorem, not a heuristic.** The pushout is provably the least state containing both
  edits; a conflict is an object you resolve, never a silent stomp.
- **Access is capabilities, not ACL rows.** "Can merge to main" is a cap you hold and can attenuate /
  delegate / revoke — the same lattice as everything else in dregg.
- **It's a member of the community, not a separate silo.** The forge-grain and the homeserver-grain
  are the same architecture; your town has both a square and a workshop.

## The first buildable slice (no kernel, no git)

Build the **`PullRequest` object + the review-as-stitcher weld** over the existing branch-and-stitch +
`dregg-doc` merge, entirely in-process, two poles: a PR whose forks merge cleanly lands a verified
merge turn; a PR with a true conflict surfaces a `ConflictRegion` that the target cap-holder must
resolve before the merge turn is admitted (an unresolved conflict → merge refused; a non-holder's
merge → refused). This is the forge's keystone, and like the homeserver body it needs neither the
localnet nor a kernel change — it welds primitives that already exist.
