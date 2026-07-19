# starbridge-privacy-voting

**One-vote-per-ballot polling with monotone, tamper-evident tallies — enforced by the verified executor.**

A poll is opened with a question; each voter is issued a **ballot cell** they can spend
**exactly once**; the tally cells only ever count **up**; the poll **closes exactly once**.
Every transition is a signed turn the verified executor checks against slot-caveats baked
into the cell at birth.

This is a dregg-native app built from primitives only — `FactoryDescriptor`,
`Effect::SetField` / `Effect::EmitEvent`, `Authorization::Signature`, and Lane-G
`StateConstraint` slot caveats. There is **no** domain-specific `Effect::CastVote`. It is
a greenfield rebuild of the legacy `apps/privacy-voting/` HTTP app.

## Two cells, two factories

### Poll cell (`POLL_FACTORY_VK`)

| Slot | Constant            | Caveat       | What it guarantees |
|:---:|---------------------|--------------|--------------------|
| `2` | `QUESTION_HASH_SLOT`  | `WriteOnce`  | the question is fixed at poll-open |
| `3` | `TALLY_YES_SLOT`      | `Monotonic`  | the YES tally only ever increases |
| `4` | `TALLY_NO_SLOT`       | `Monotonic`  | the NO tally only ever increases |
| `5` | `TALLY_ABSTAIN_SLOT`  | `Monotonic`  | the ABSTAIN tally only ever increases |
| `6` | `CLOSED_SLOT`         | `WriteOnce`  | a poll **closes exactly once** — no re-open, no re-close |

### Ballot cell (`BALLOT_FACTORY_VK`)

| Slot | Constant        | Caveat      | What it guarantees |
|:---:|-----------------|-------------|--------------------|
| `2` | `POLL_REF_SLOT`   | `WriteOnce` | the ballot is bound to one poll |
| `3` | `VOTE_SLOT`       | `WriteOnce` | **one vote per ballot cell** — a ballot is spent exactly once |

`Monotonic` on the tallies means a tally can never be *lowered* to erase a vote.
`WriteOnce` on `VOTE_SLOT` means a voter cannot change or double-spend a ballot.

> **Note on the threat model.** This app gives *one-vote-per-ballot* and *monotone,
> tamper-evident tallies*. Ballot/voter *unlinkability* (true ballot secrecy) is a
> separate, stronger property; the privacy story here is the structural one (the cell
> model + caveats), not a mixnet. See the HORIZONLOG follow-up.

## What this crate exports

```rust
poll_factory_descriptor()   -> FactoryDescriptor
ballot_factory_descriptor() -> FactoryDescriptor
factory_descriptors()       -> Vec<FactoryDescriptor>

build_open_poll_action(cclerk,   poll_cell, question)
build_cast_vote_action(cclerk,   ballot_cell, poll_cell, choice)   // VOTE_YES|VOTE_NO|VOTE_ABSTAIN
build_record_tally_action(cclerk, poll_cell, choice)
build_close_poll_action(cclerk,  poll_cell)

register(ctx: &StarbridgeAppContext) -> ([u8; 32], [u8; 32])       // (poll_vk, ballot_vk)
```

## Running it against a node

```rust
let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x62u8; 32]);
let exec = EmbeddedExecutor::new(&cclerk, "default");
exec.deploy_factory(poll_factory_descriptor());
exec.deploy_factory(ballot_factory_descriptor());

// birth a poll cell + a ballot cell from their factories, grant caps, then:
exec.submit_action(&cclerk, build_open_poll_action(&cclerk, poll, "ship it?"))?;
exec.submit_action(&cclerk, build_cast_vote_action(&cclerk, ballot, poll, VOTE_YES))?;
// a second vote on the same ballot cell is REFUSED (WriteOnce on VOTE_SLOT)
// lowering a tally is REFUSED (Monotonic); re-closing the poll is REFUSED (WriteOnce)
```

The end-to-end versions of these flows — birth + accept + adversarial refuse, all through
the real `EmbeddedExecutor` — live in `src/lib.rs::tests` (the
`factory_born_*` tests). `register(ctx)` mounts both factories for a federation deployment.

## Tests

```sh
cargo test -p starbridge-privacy-voting
```

The suite covers descriptor shape, every slot caveat in isolation, and the
factory-birth executor path: a ballot spent twice is refused, a tally lowered is refused,
a poll re-closed is refused.

## Private scored-decision proof seam

For four-person/four-option guild votes, party choices, matchmaking, or quest
branches, `dregg-circuit-prove::private_preference` supplies a Lean-authored
winner-only hiding proof over private bounded-score ballots. It deliberately is
not a dependency of this wasm-clean app crate: the host verifies through
`verify_decision_zk`, checks the receipt session/root against its poll source,
then maps `VerifiedDecision.winner` to the poll's canonical option ordering.
The ballot cells here continue to provide eligibility/one-vote lifecycle teeth;
the proof organ provides private exact aggregation. See
`../../docs/deos/PRIVATE-PREFERENCE-N4K4.md` for the exact composition and its
Tier-1-not-Tier-0 boundary.

## See also

- `../nameservice/README.md` — the anchor starbridge-app and exemplar.
- `../../HORIZONLOG.md` — `APPS-POLISH`: ballot unlinkability (mixnet/nullifier-set) is a
  named follow-up, not a claim of this app.
