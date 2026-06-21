## scripts

A **script** (the dregg name for a *macro*) is a reusable, attenuable,
proof-carrying *recorded turn-sequence* — the same idea as a factory, generalized
from "create a cell" to "run a sequence." It is the Tier-1 object `turn/src/script.rs`:
a named, content-addressed wrapper over the proven `Pipeline` carrier
(`turn/src/eventual.rs` — a serializable `{ turns, dependency-DAG, atomic }`).

`Script::record(name, turns)` builds a linear pipeline from a sequence of turns;
`.replay(ledger, executor)` runs them through the **real** verified executor via
`execute_pipeline` (the same machinery the protocol already trusts), returning one
receipt per turn. `.id()` is the script's content-address — `blake3` over the
pipeline — its identity, exactly as a factory is identified by its VK hash.

Crucially there is **no new kernel verb and no new circuit.** A script rides the
existing pipeline + executor; recording and replaying a turn-sequence is something
dregg could already do, given a name. The cockpit's macro record/replay (⏺▶) is a
script recorded off the live session; because navigation state is itself witnessed
cells, a recorded session is literally a sequence of real turns.

## macros-as-custom-vk

The deep move (why a macro does **not** need a general zkVM): a script is *bounded
and fixed-structure* — a known pipeline of N turns with known effect shapes — so it
has a *fixed* circuit, which is its own verification key. You don't *interpret* a
script with a universal machine; you *compile* it, the way a factory derives its
child VK. The script's circuit is the **composition of its turns' per-effect rungs**
along the dependency DAG (+ the hole-binding constraints) — composition of rungs
that already exist (emitted from Lean), not a new prover.

So a script runs via `Authorization::Custom { vk_hash = script_id }` — the
app-defined-verification seam dregg already has — with the script's holes as the
public inputs (the guarded-hole binding is already Lean-proven). **The macro becomes
its own proof system** — dregg's thesis ("the token became the proof system") one
level up: the *macro* became the proof system. A light client verifies a script-run
as an ordinary `Custom`-authorized turn against the script's VK; it never
re-executes and never needs a universal VM.

The only honest constraint is *bounded* (no unbounded loops — a macro is a fixed
recorded sequence; unbounded control flow is exactly where a real zkVM would start,
and is deliberately out of scope). The Tier-1 object above gives the carrier + the
content-address; Tier-2 swaps the content hash for the compiled circuit VK. Full
design: `docs/deos/MACRO-AS-CUSTOM-VK.md`.
