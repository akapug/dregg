# Macros / scripts as Custom-VK objects — verifying a recorded turn-sequence without a general zkVM

A macro (= a reusable, attenuable, proof-carrying *recorded turn-sequence*) seems
to need a general zkVM: to make "this script ran correctly" a verified protocol
fact you'd have to prove arbitrary execution. That's the hard, wrong framing.

**The move (ember): compile each script to its own Custom verification key.** A
script is not interpreted by a universal machine; it is *compiled* into a fixed,
specialized circuit — its own VK — exactly the way a factory's child VK is
derived from its descriptor. The zkVM problem dissolves because a macro is
**bounded and fixed-structure**: a known `Pipeline` of N turns with known effect
shapes and named holes. A fixed structure has a fixed circuit.

## Why every piece already exists

1. **The carrier** — `Pipeline`/`TurnBatch` (`turn/src/eventual.rs:282`): a
   serializable `{ turns, dependency-DAG, atomic }` that already replays through
   the canonical `execute_pipeline` → `TurnExecutor`.
2. **Per-effect circuits** — each effect already has a circuit descriptor/rung
   (the rotated `…VmDescriptor2R24` family, emitted from Lean). A script's circuit
   is the **composition** of its turns' per-effect rungs along the dependency DAG
   — composition of existing rungs, not a new interpreter.
3. **The compile-to-circuit DSL** — `#[dregg_caveat]` / `#[dregg_circuit]` already
   compile predicates to AIR/Datalog/gates + a VK. Extending this to compile a
   *bounded turn-sequence* to a composed circuit is more of the same machinery,
   one level up.
4. **The content-addressed-VK template pattern** — factories
   (`cell/src/factory.rs`): a descriptor is identified by its VK hash, registered,
   instantiated by an effect, validated, replayed. A script *is* this pattern,
   generalized from "create a cell" to "run a sequence."
5. **The verification hook** — `AuthRequired::Custom { vk_hash }` +
   `Authorization::Custom` + the `WitnessedPredicateRegistry` (`cell/src/predicate.rs`):
   the protocol's existing app-defined-verification seam.
6. **Parameterization, already Lean-proven** — guarded holes
   (`held_promise.rs` / `pipeline_continuation.rs`; `holeFill_binds_in_circuit`):
   a hole-fill binds both the value and its guard, in-circuit, fail-closed,
   one-shot. The script's parameters are the public inputs to its Custom VK.

## The shape

```
script  :=  a bounded Pipeline + named guarded holes
compile :=  fold the turns' per-effect rungs along the dependency DAG,
            + the hole-binding constraints, into ONE composed circuit → script_vk
identity:=  script_vk hash (content-addressed, like a factory)
run     :=  a turn (or the Pipeline itself) authorized by
            Authorization::Custom { vk_hash = script_vk };
            its WitnessedPredicate attests the composed execution;
            the holes are the public inputs (bound by holeFill_binds_in_circuit)
attenuate:= the script's Custom predicate is itself caveat-restrictable
            ("adoption is attenuation" — a sub-VK / narrower predicate)
```

So: **a script is its own proof system.** This is dregg's deepest thesis ("the
token became the proof system") taken one level up — the *macro* became the proof
system. A light client verifies a script-run as an ordinary `Custom`-authorized
turn against the script's VK; it never re-executes and never needs a universal VM.

## "Effect or not?" — both are coherent

- **Not an effect (lean):** a macro is just a `Pipeline` whose execution is
  attested by a `Custom` predicate. It rides the existing Custom-auth path with
  *no new kernel verb*. The macro is a cell-held `Script` descriptor + its VK; you
  "run" it by submitting the Pipeline with `Authorization::Custom`.
- **An effect (`RunScript`):** a first-class verb `RunScript { script_vk, params }`
  paralleling `CreateCellFromFactory`, whose in-circuit descriptor *is* the
  composed script circuit. Cleaner ergonomics + a single receipted unit, at the
  cost of a new VK-affecting effect (the factory pattern, formally).

Recommendation: prototype the **lean (non-effect)** form first — a `Script`
descriptor + Custom-predicate attestation over a `Pipeline`, replayed through the
existing executor — because it adds no new kernel verb and rides proven seams. Promote
to a `RunScript` effect only if the ergonomics demand it.

## The honest edges

- **Bounded only.** Scripts are fixed recorded sequences (no unbounded loops). A
  macro *should* be bounded; unbounded control flow is where a real zkVM would be
  needed, and is deliberately out of scope.
- **Circuit composition is real work** (VK-affecting, ember-gated): folding the
  per-effect rungs + the DAG + hole constraints into one VK. But it is composition
  of *existing, emitted-from-Lean* rungs — not a new proving system.
- **The non-effect form's soundness** rests on the Custom predicate genuinely
  attesting the whole composed execution (not a stripped sub-claim) — the same
  anti-strip discipline the `AnyOfBound` caveats already enforce.

## The unification it buys

Factories (cell-creation templates) and scripts (action-sequence templates) become
*one idea*: **content-addressed VK templates compiled from a fixed structure,
instantiated with guarded-hole parameters, attested by their own VK.** A factory
is the degenerate one-creation script; a script is the factory generalized to a
sequence. Both are "a recorded intention, compiled to its own verifier."
