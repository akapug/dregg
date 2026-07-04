# Cells as service objects

A cell already does method-dispatch: an `Action` carries a `method: Symbol` +
`args`, and a `CellProgram::Cases` program scopes a transition to a method via
`TransitionGuard::MethodIs`. **Cells-as-service-objects** gives that interface a
first-class typed shape and a userspace front door, *without* a kernel effect: the
interface lives entirely above the effect-VM, and an invocation desugars to the
ordinary verified effects the method names. The kernel and the light client keep
seeing only the effects they already enforce and witness.

## `InterfaceDescriptor` — a userspace typed interface

`cell/src/interface.rs` holds the types:

- **`Semantics`** — the replayable-vs-service distinction as a typed bit. A
  `Replayable` method is a pure verified-turn template (re-running it against the
  same pre-state reproduces the same post-state). A `Serviced` method is answered
  by the cell ACTING AS A SERVICE OBJECT — it reads other cells, NOT a pure replay;
  its soundness prerequisite is the OFE theorem
  `crossCellRead_refines_observedField` (`metatheory/Dregg2/Exec/UniversalBridge.lean:1019`).
- **`MethodSig`** — one method: its `symbol` (the BLAKE3 method-name hash an
  `Action` targets), `args_schema`, `auth_required`, and `semantics`.
- **`InterfaceDescriptor`** (`cell/src/interface.rs:215`) — a named set of methods,
  content-addressed by `interface_id` (the sorted-Poseidon2 root over the method
  leaves, `compute_interface_id`, `:246` — the same machinery the cap-root uses).
- **`route_method`** (`:361`) — routes a method symbol through the descriptor's
  VERIFIED DFA router (the same `dregg_dfa::Router::classify` a federation
  constitution audits), so an unknown method does not route → refused, fail-closed.
- **`derive_replayable`** (`:294`) — a cell that already dispatches (a
  `CellProgram::Cases` with `MethodIs` guards) gets its `Replayable` interface for
  FREE: each guard lifts to a `MethodSig`. No extra authoring, no commitment.

**The interface is a USERSPACE object, NOT a committed cell field.** There is no
`Cell::interfaces` field and the cell commitment does not bind the descriptor — the
v9→v10 commitment bump that would have committed it was **backed out**. A descriptor
is resolved at the userspace layer either by `derive_replayable` (reads only the
program) or from an app-maintained registry. (The `interface.rs` module header still
carries the earlier "the commitment binds / on-cell `InterfaceRef`" framing from the
Stage-1 design; that framing is superseded by the userspace integration the
`invoke()` / Service Explorer / kvstore modules describe.)

## `invoke()` — the userspace front door

`app-framework/src/invoke.rs` is the dispatch front door. It lives *slightly above*
the effect-VM primitive, **NOT** as a kernel effect — **there is no `Effect::Invoke`**;
the `Effect` enum is unchanged (no new variant, the desktop link stays clean).
`invoke()`:

1. **Resolves the descriptor in userspace** — derived from the cell's `CellProgram`
   or taken from an explicit app-registered descriptor. No commitment dependency.
2. **Routes the method** through the descriptor's verified DFA `route_method` — an
   unknown method is refused, fail-closed.
3. **Gates on semantics** — a `Replayable` method desugars to its underlying
   effects (the function's job); a `Serviced` method is a NAMED SEAM (its answer
   rides the OFE cross-cell-read, not a pure replay), so `invoke` refuses to
   desugar it and points at the seam.
4. **Cap-gates on `auth_required`** — the caller's declared `InvokeAuthority` must
   satisfy the method's `AuthRequired` before any effect is built (the early
   legible refusal; the real cryptographic check runs downstream in the executor).
5. **Desugars to an `Action` + fires** — the underlying existing effects
   (`SetField`, `Transfer`, …) are wrapped in an `Action` targeting the method
   symbol, signed by the framework cipherclerk, and submitted through the normal
   executor. The receipt is the ordinary turn receipt.

## The kvstore exemplar (`0d1a3f8b`)

`starbridge-apps/kvstore/src/lib.rs` is the worked exemplar: a verified key-value
register store exposed as a service cell. It publishes a typed
`InterfaceDescriptor` with three methods —

| method   | semantics    | auth        | desugars to                              |
|----------|--------------|-------------|------------------------------------------|
| `put`    | `Replayable` | `Signature` | bump version + `SetField(reg, value)`    |
| `delete` | `Replayable` | `Signature` | bump version + `SetField(reg, 0)`        |
| `get`    | `Serviced`   | `None`      | — (the named OFE seam: a pure read, no turn) |

The store's `CellProgram` scopes `StateConstraint::Monotonic` on the version slot to
the mutator cases, so a replayed or reordered mutation that would lower the version
is an **executor refusal on the verified commit path** — not a userspace check. The
cap-gate is enforced twice: at the `invoke()` front door and again by the executor
on the desugared turn's real signature. `get` is `Serviced`, so `invoke()` refuses
to desugar it, naming the OFE seam rather than faking a write.

## The Service Explorer

`starbridge-v2/src/service_explorer.rs` is the deos-interior face of `invoke()` — a
Postman-like surface that discovers the methods a cell publishes (its
`InterfaceDescriptor`, derived-from-program or registry-supplied), lets you fill a
method's arguments, and invokes it as a real verified turn. It adds no kernel
effect; membership of the invoked method is decided by the same `route_method` DFA
router. gpui-free and `cargo test`-able: a test discovers methods off a real cell
program, invokes a replayable method, and refuses an unknown / unauthorized /
serviced one in-band.

## Open seam

A `Serviced` method's answer is the named OFE seam — its receipt carrier (the
cross-cell reads it observed + the produced result, so a light client can re-check a
service answer) and the CapTP interface handshake (exchanging an
`InterfaceDescriptor` on `CapHello`) are named in `cell/src/interface.rs:38–49`, not
yet built.
