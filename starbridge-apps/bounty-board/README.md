# starbridge-bounty-board

**Escrow-backed bounties as a one-way state machine, enforced by the verified executor.**

A poster escrows a reward and opens a bounty; a worker claims it (first-claimer-wins);
the worker submits work; the poster pays out. Every transition is a signed turn the
**verified executor** checks against slot-caveats baked into the bounty cell at birth —
so a bounty cannot be stolen, replayed, re-priced, or paid twice.

This is a dregg-native app built from primitives only — `FactoryDescriptor`,
`Effect::SetField` / `Effect::EmitEvent`, `Authorization::Signature` from
`AppCipherclerk::make_action`, and Lane-G `StateConstraint` slot caveats. There is **no**
domain-specific bounty `Effect`, **no** `Authorization::Unchecked`, **no** `[0u8; 64]`
placeholder signature. It is a greenfield rebuild of the legacy `apps/bounty-board/` HTTP
app on the dregg substrate.

## The lifecycle, enforced by caveats (not asserted)

Each bounty lives in a sovereign cell whose state machine is its installed `CellProgram`:

```
OPEN ──claim──▶ CLAIMED ──submit──▶ SUBMITTED ──payout──▶ PAID
```

| Slot | Constant            | Caveat            | What it guarantees |
|:---:|---------------------|-------------------|--------------------|
| `2` | `TITLE_HASH_SLOT`     | `WriteOnce`       | the title is fixed at posting |
| `3` | `REWARD_SLOT`         | `WriteOnce`       | the escrowed reward cannot be re-priced after a worker commits |
| `4` | `STATE_SLOT`          | `StrictMonotonic` | `OPEN→CLAIMED→SUBMITTED→PAID`, no going back, no re-entering a state (so: no double-claim, no re-open, no double-payout) |
| `5` | `CLAIMANT_HASH_SLOT`  | `WriteOnce`       | **first-claimer-wins** — a claim cannot be overwritten to steal the bounty |
| `6` | `SUBMISSION_HASH_SLOT` | `WriteOnce`      | the submitted artifact hash is fixed at submission |

`StrictMonotonic` on `STATE_SLOT` is doing a lot of work: because a transition must move
to a **strictly greater** code, re-writing the same code is rejected. That single caveat
gives no-double-claim, no-re-open, and no-double-payout for free.

## What this crate exports

```rust
bounty_factory_descriptor() -> FactoryDescriptor   // the constructor-transparency contract
bounty_cell_program()       -> CellProgram         // the installed state machine
factory_descriptors()       -> Vec<FactoryDescriptor>

// turn-builders — each carries a real Ed25519 signature from the cclerk
build_post_action(cclerk,   bounty_cell, title, reward)
build_claim_action(cclerk,  bounty_cell, claimant)
build_submit_action(cclerk, bounty_cell, artifact_uri)
build_payout_action(cclerk, bounty_cell)

register(ctx: &StarbridgeAppContext) -> [u8; 32]   // mount factory + inspector
```

## Running it against a node

The canonical embedded-node path (no external services) — drive the whole lifecycle and
watch the executor refuse the hostile turns:

```rust
use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, CellMode};
use dregg_cell::FactoryCreationParams;
use starbridge_bounty_board::*;

let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x62u8; 32]);
let exec = EmbeddedExecutor::new(&cclerk, "default");
exec.deploy_factory(bounty_factory_descriptor());

// fund the agent, birth a bounty cell from the factory, grant the owner cap …
// then:
exec.submit_action(&cclerk, build_post_action(&cclerk,   bounty, "fix the bug", 500))?;
exec.submit_action(&cclerk, build_claim_action(&cclerk,  bounty, "bob"))?;
exec.submit_action(&cclerk, build_submit_action(&cclerk, bounty, "ipfs://artifact"))?;
exec.submit_action(&cclerk, build_payout_action(&cclerk, bounty))?;
```

`tests/factory_birth.rs` is the runnable, self-contained version of exactly this flow
(birth → full lifecycle → adversarial refusals).

In a federation deployment, `register(ctx)` mounts the factory on a
`StarbridgeAppContext`; the in-browser `DreggRuntime` then resolves
`window.dregg.createFromFactory(BOUNTY_FACTORY_VK, owner_pk, token)` against the host's
descriptor service, and the JS inspector (`inspectors.js`, component `<dregg-bounty>`)
renders the per-cell state machine.

## Tests

| Test | Surface | What it pins |
|---|---|---|
| `src/lib.rs::tests::*` | `CellProgram::evaluate` directly | descriptor shape + every slot caveat in isolation (legal post/claim, double-claim, claimant theft, reward change, state regression) |
| `tests/factory_birth.rs::factory_born_bounty_runs_the_whole_lifecycle` | **the real executor** | birth → `post → claim → submit → payout` all ACCEPTED; post-state reads back exactly |
| `tests/factory_birth.rs::..._refuses_theft_replay_and_reward_tampering` | **the real executor** | claimant theft / re-claim replay / reward chiseling all REFUSED; state survives |
| `tests/factory_birth.rs::..._refuses_state_regression_and_double_payout` | **the real executor** | a PAID bounty refuses re-open and double-payout |

```sh
cargo test -p starbridge-bounty-board
```

## See also

- `../nameservice/README.md` — the anchor starbridge-app and paint-by-numbers exemplar.
- `../tool-access-delegation/` — sibling app; the factory-birth test pattern this crate's
  `tests/factory_birth.rs` follows.
- `../../HORIZONLOG.md` — `APPS-POLISH` follow-ups (escrow-balance binding; userspace-verify
  integration).
