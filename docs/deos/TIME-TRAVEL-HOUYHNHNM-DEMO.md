# Time-Travel / Undo — Houyhnhnm Pillar #3

The flagship that makes dregg's *temporal* axis tangible: REWIND a live verified
history to a past state, BRANCH at that past point, and replay a DIFFERENT
verified future. The spatial twin (fork a confined world, drive it, stitch it
back) is branch-and-stitch (`starbridge-v2/src/branch_stitch_session.rs`); this
is the same event-structure config-lattice object walked along *time*.

Demo: `demo/tests/time_travel_houyhnhnm.rs` (gpui-free, `cargo test -p
dregg-demo --test time_travel_houyhnhnm`, 4 tests green).

## What it exercises (all on the REAL substrate)

A two-party ledger world (`alice=1000`, `bob=0`) accrues four verified turns
through the real `TurnExecutor`: two transfers, a field-write memo, a reverse
transfer. Then time-travel, mapped 1:1 onto `turn/src/reversible.rs`:

- **REWIND** — `ReversibleHistory::replay_to(k)` (forward-from-genesis) AND
  `ReversibleHistory::undo_to(k)` (backward-from-head via the `Turn::invert`
  un-turn, gated by the executor). The two roads land on the SAME verified past
  value/state (`ledgers_agree_modulo_nonce`), checked against the recorded root
  tooth `roots[k]`.
- **BRANCH** — fork the past with the first-class `ReversibleHistory::fork_at(k)`:
  a new history whose committed prefix `[0,k]` SHARES the parent's config-lattice
  *down-set* (each prefix step is an `Arc`-handle clone — NOT re-executed),
  landing on the original's `roots[k]` byte-identically. The fork's root at `k`
  equals the original's EXACTLY (same verified past), then a divergent turn
  writes a different future (`alice→bob 500` instead of the original tail). This
  is the temporal dual of branch-and-stitch's spatial `World::fork`.
- **GENUINE** — the divergent turn carries a real `TurnReceipt`; conservation /
  authority hold (the real executor rejects otherwise); the branch head root
  differs from both the original head and the original step at the same height;
  the original recorded history is untouched (forking, not rewriting).

## How real the reversibility is

`undo_to` is an **exact inverse on value/state** — `undo(do(s)) == s` on
balances, fields, and capabilities — *modulo the per-turn monotone nonce
ratchet*, the one deliberate island of irreversibility every committed turn
carries (`FIRST-CLASS-REVERSIBILITY.md` §4.2). It is NOT a replay-to-N
approximation: it walks history backward applying genuine inverse turns
(`Turn::invert`, the Clean/Contextual tiers) through the executor, fail-closed at
any settled commit (`Burn`, `NoteSpend`, a nonce bump, a revoke). The demo proves
the boundary: rewinding the clean tail succeeds; rewinding *past* a settled nonce
bump refuses with `IrreversibleStep`.

## fork_at — the shared-down-set temporal fork (built)

`ReversibleHistory::fork_at(k)` is first-class: it SHARES the recorded prefix as
the event-structure config-lattice *down-set* rather than re-executing it. Each
prefix step is an `Arc`-handle clone of the parent's (no executor runs, no payload
is deep-copied), and the fork's `roots[0..=k]` are the parent's recorded teeth
copied byte-identically — so the fork lands on `roots[k]` exactly WITHOUT
replaying the prefix turns. The structural sharing is witnessed by
`Arc::ptr_eq(parent.steps()[i], fork.steps()[i])` for every `i < k`: the fork's
past *is* the parent's, not a fresh re-execution
(`fork_at_shares_the_downset_not_replay`). The fork then records divergent
verified turns from `k` forward (against the working ledger the rewind already
produced), and the parent is untouched — the shared prefix payloads are immutable.
Down-sets compose: `fork_at(k).fork_at(j<=k)` agrees with `fork_at(j)` on every
shared step. This is the temporal dual of branch-and-stitch's spatial `World::fork`,
and the sound optimization the earlier replay-synthesis pointed at (the demo
formerly re-executed the `steps()` prefix through `record_commit` — faithful but an
O(k) recomputation).

**Next reversibility rung:** wire `fork_at` into the meta-debug rewind UI
(`FIRST-CLASS-REVERSIBILITY.md` §3.3) so the live desktop scrubs backward and
*branches* the past in lock-step — the rewind button forks a shared down-set, the
adept drives a divergent verified future, the parent timeline stands untouched.
