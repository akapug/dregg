# @dregg/sdk

TypeScript SDK for dregg. Two user-facing nouns and one shape:

```text
Identity → .turn() → typed verb builders → .sign() → .submit() → Receipt
```

An unauthorized act is inexpressible on the public surface: every action
carries a real Ed25519 `Authorization::Signature` over the canonical
federation-bound signing message, and every submission rides a `SignedTurn`
envelope over the canonical `Turn::hash`. The raw vocabulary (including
unauthorized construction) is sealed behind `@dregg/sdk/raw`.

This package mirrors the Rust SDK (`sdk/`) shape-for-shape and
byte-for-byte: key derivation, postcard wire encoding, canonical hashes, and
signing preimages are differentially tested against the repo's own
`dregg-wasm` build, and the identity derivation is pinned by the same golden
vector as the Rust SDK, CLI, and browser extension — if any implementation
drifts, all of them fail together.

## Walkthrough (devnet)

```ts
import { AgentRuntime, Identity, NodeClient, ReceiptFilter, profiles } from "@dregg/sdk";

// 1. A named identity — the same $DREGG_HOME/profiles store as `dregg id`.
const identity = profiles.loadActive() ?? (profiles.create("me"), profiles.load("me"));

// 2. Bind to a node.
const node = new NodeClient("https://devnet.dregg.fg-goose.online", {
  devnetKey: process.env.DREGG_DEVNET_KEY, // the signed-turn ingress is operator-gated
});
const runtime = new AgentRuntime(identity, node);

// 3. Materialize + fund the agent cell (devnet faucet).
await runtime.faucet(2000);

// 4. Observe before acting.
const stream = node.events().subscribe(new ReceiptFilter().cell(identity.cellId()));

// 5. The one public turn shape.
const authorized = await runtime.turn().writeU64(0, 42n).fee(1000).sign();
console.log(authorized.explain()); // the anti-blind-signing reading, [sem]-tagged
const receipt = await authorized.submit();

// 6. The same noun arrives on the nervous system.
for await (const observed of stream) {
  if (observed.turnHash === receipt.turnHash) break;
}

// 7. The STARK attaches lazily (the node's async prove pool).
const proof = await node.turnProof(receipt.turnHash);
if (proof) receipt.attachProof(proof);
```

Runnable version: `node examples/devnet-walkthrough.mjs` (after `npm run build`).

## Surface

| Export | Purpose |
|--------|---------|
| `Identity` | Ed25519 identity; `blake3 derive_key("dregg/0", seed64)` derivation |
| `profiles` | Shared `$DREGG_HOME/profiles` named-identity store (`dregg id …`) |
| `NodeClient` / `AgentRuntime` | A node's HTTP surface / an identity bound to it |
| `TurnBuilder` / `AuthorizedTurn` | Typed verbs → `.sign()` → `.submit()`; empty turns refused |
| `Receipt` / `TurnProof` | Proof-of-execution noun; STARK lazily attached, mis-bound attachments refused |
| `NodeEvents` / `ReceiptFilter` | `subscribe(filter)` → `AsyncIterable<Receipt>` (SSE, Last-Event-ID resume, reconnecting) |
| `explainTurn` / `renderTurn` / `explainAction` / `explainEffect` | The clerk's faithful reading: total, `[sem <digest>]`-tagged (equal text ⇒ equal semantics) |
| `program` | Cell-program atoms (`senderIs` / `senderInSlot` / `balanceGte` / `balanceLte` / `preimageGate`, `anyOf` / `not` / `implies`) + content-addressed factory descriptors |

### Turn verbs

`transfer(to, amount)` · `transferFrom(from, to, amount)` · `write(index, value)` ·
`writeU64(index, n)` · `grant(to, cap)` · `incrementNonce()` · `effect(e)` /
`effects(list)` · modifiers `on(target)` · `method(name)` · `fee(n)`.

Unlike the Rust in-process runtime there is no `.asCell(..)`: the remote
signed ingress pins `turn.agent` to the signer's default cell.

### Sealed: `@dregg/sdk/raw`

The wire vocabulary (postcard encoders, canonical hashes, signing preimages,
`unsignedAction`). Quarantined exactly like the Rust SDK's `sdk/src/raw.rs`:
if you import it in application code you are almost certainly building
something the executor will reject.

### Legacy: `@dregg/sdk/wasm`

The pre-refinement wasm-bound playground client (`DreggClient`,
`DreggRuntime`, proof/Merkle/Datalog toys) — unchanged, for existing
consumers.

## Tests

```bash
npm test   # build + node --test
```

- **Differential**: TS-built signed turns are byte-identical (postcard
  encoding AND canonical `Turn::hash` v3) to the Rust implementation via the
  repo's `dregg-wasm` build; BLAKE3 is differentially tested across chunk
  boundaries.
- **Golden vector**: seed `00..3f` → pubkey `335840a9…8b9a`, the same pin as
  `sdk/src/profiles.rs`, `cli/src/commands/id.rs`, and
  `extension/test/derivation.test.mjs`.
- Profile store, SSE resume/reconnect, explain totality + sem-tag
  discrimination, program content-addressing.

## License

AGPL-3.0-or-later
