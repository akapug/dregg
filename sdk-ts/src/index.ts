/**
 * `@dregg/sdk` — the authorization-first TypeScript SDK for dregg.
 *
 * Two user-facing nouns and one shape:
 *
 * ```text
 * Identity → .turn() → typed verb builders → .sign() → .submit() → Receipt
 * ```
 *
 * - [`Identity`] — who acts (Ed25519, derived `blake3 derive_key("dregg/0")`
 *   from a 64-byte master seed; same golden vector as the Rust SDK / CLI /
 *   extension).
 * - [`profiles`] — the shared `$DREGG_HOME/profiles` named-identity store
 *   (`dregg id create / list / use`).
 * - [`AgentRuntime`] / [`NodeClient`] — an identity bound to a node;
 *   `runtime.turn()` opens the typed verb builder.
 * - [`TurnBuilder`] / [`AuthorizedTurn`] — the one public turn shape. An
 *   unauthorized act is inexpressible on this surface (the raw vocabulary
 *   is sealed behind `@dregg/sdk/raw`).
 * - [`Receipt`] — the proof-of-execution noun, born proofless, with the
 *   composed full-turn STARK lazily attached.
 * - [`NodeEvents`] — `subscribe(filter)` → `AsyncIterable<Receipt>` over
 *   the node's committed-receipt SSE stream (Last-Event-ID resume,
 *   reconnecting).
 * - [`explainTurn`] / [`renderTurn`] — the anti-blind-signing reading: a
 *   total, semantics-faithful description of exactly what a turn does.
 * - [`program`] — the cell-program constraint atoms
 *   (senderIs / senderInSlot / balanceGte / balanceLte / preimageGate and
 *   anyOf / not / implies composition) with content-addressed factory
 *   descriptors.
 *
 * ```ts
 * import { Identity, AgentRuntime, profiles } from "@dregg/sdk";
 *
 * const id = profiles.loadActive() ?? Identity.generate();
 * const runtime = new AgentRuntime(id, "https://devnet.dregg.fg-goose.online");
 * await runtime.faucet(500);
 * const signed = await runtime.turn().writeU64(0, 42n).sign();
 * console.log(signed.explain()); // read before you leap
 * const receipt = await signed.submit();
 * console.log("committed:", receipt.turnHash);
 * ```
 *
 * The legacy wasm-bound playground client lives at `@dregg/sdk/wasm`.
 *
 * @packageDocumentation
 */

// Who acts.
export { Identity, MAIN_IDENTITY_PATH } from "./identity";

// Named local identity profiles (shared store with the Rust SDK + CLI).
export * as profiles from "./profiles";
export { ProfileError, PROFILE_ENV } from "./profiles";
export type { ProfileInfo } from "./profiles";

// The node surface + the acting runtime.
export { AgentRuntime, NodeClient, NodeError } from "./client";
export type {
  CellDetail,
  NodeClientOptions,
  NodeIdentity,
  ReceiptInfo,
  SubmitSignedTurnResponse,
} from "./client";

// The one public turn shape.
export { AuthorizedTurn, EmptyTurnError, TurnBuilder } from "./turns";

// The receipt noun (lazy proof).
export { Receipt, TurnProof, WrongTurnProofError } from "./receipt";
export type { ReceiptFields, TurnReceiptJson } from "./receipt";

// The receipt nervous system.
export { createSseParser, NodeEvents, ReceiptFilter, ReceiptStream } from "./events";
export type { NodeEventsOptions } from "./events";

// The clerk's faithful reading.
export { explainAction, explainEffect, explainTurn, renderTurn } from "./explain";

// The cell-program constraint language.
export * as program from "./program";

// Public wire types reachable from the authorized surface (constructing
// these does not authorize anything; the sealed vocabulary incl.
// unsignedAction lives at @dregg/sdk/raw).
export type {
  Action,
  AuthRequired,
  CapabilityRef,
  CellId,
  Effect,
  Turn,
} from "./internal/wire";
export { fieldFromU64, symbol } from "./internal/wire";
export { hexDecode, hexEncode } from "./internal/bytes";
