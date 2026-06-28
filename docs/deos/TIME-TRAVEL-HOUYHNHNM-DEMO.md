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
- **BRANCH** — fork the past by replaying the recorded `steps()` prefix `0..k`
  into a fresh `ReversibleHistory` (the demo's `fork_at`). The fork's root at `k`
  equals the original's EXACTLY (same verified past), then a divergent turn
  writes a different future (`alice→bob 500` instead of the original tail).
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

## The named gap + the next rung

`ReversibleHistory` has **no first-class `fork_at(k)` API**. The demo synthesizes
branching by replaying the public `steps()` prefix through `record_commit` —
faithful (the replayed prefix lands on the original root tooth at every shared
step, asserted in `the_named_gap_fork_at_is_replay_of_the_prefix`) but
re-executing rather than structurally sharing the prefix.

**Next reversibility rung:** a real `ReversibleHistory::fork_at(k) ->
ReversibleHistory` that shares the prefix as the event-structure config-lattice
*down-set* (no re-execution), the temporal dual of branch-and-stitch's spatial
fork. The faithfulness this demo proves is exactly why that sharing would be a
sound optimization, not a semantics change.
