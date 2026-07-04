/**
 * Hydrate a page's JSON {@link TurnRequestSpec} into the SDK's typed `Effect`
 * list, routed onto an `AgentRuntime.turn()` builder.
 *
 * Two safety rules live here, at the boundary the page cannot cross:
 *
 *   1. **The page never names a source cell.** Every verb's `from`/acting cell
 *      is the signer's own cell (`runtime.identity.cellId()`), so a page cannot
 *      describe a turn that spends from someone else's cell. (The executor would
 *      reject it anyway — this just keeps the approval reading honest.)
 *   2. **No `Unchecked` path.** Effects only ever flow through the typed builder;
 *      the authorization is stamped by `.sign()`, never by the page.
 *
 * Byte fields arrive as hex strings (the page speaks JSON); we decode to the
 * exact-length `Uint8Array` the wire encoder demands, throwing on any malformed
 * field rather than silently truncating.
 */

import { hexDecode } from "@dregg/sdk/browser";
import type { AuthRequired, CapabilityRef, Effect, TurnBuilder } from "@dregg/sdk/browser";
import type { AuthRequiredSpec, EffectSpec, TurnRequestSpec } from "./protocol";

function hex32(s: string, what: string): Uint8Array {
  const b = hexDecode(s);
  if (b.length !== 32) throw new Error(`${what}: expected 32 bytes, got ${b.length}`);
  return b;
}

function authRequired(a: AuthRequiredSpec): AuthRequired {
  switch (a.kind) {
    case "none":
    case "signature":
    case "proof":
    case "either":
    case "impossible":
      return { kind: a.kind };
    case "custom":
      return { kind: "custom", vkHash: hex32(a.vkHashHex, "vkHash") };
    default: {
      const _never: never = a;
      throw new Error(`unknown AuthRequired: ${JSON.stringify(_never)}`);
    }
  }
}

/**
 * Build a single typed `Effect` from its spec, pinning the signer's cell as the
 * source where a verb implies one.
 */
function hydrateEffect(spec: EffectSpec, signer: Uint8Array): Effect {
  switch (spec.kind) {
    case "transfer":
      return { kind: "transfer", from: signer, to: hex32(spec.toHex, "transfer.to"), amount: BigInt(spec.amount) };
    case "setField":
      return { kind: "setField", cell: signer, index: spec.index, value: hex32(spec.valueHex, "setField.value") };
    case "incrementNonce":
      return { kind: "incrementNonce", cell: signer };
    case "grantCapability": {
      const cap: CapabilityRef = {
        target: hex32(spec.cap.targetHex, "cap.target"),
        slot: spec.cap.slot,
        permissions: authRequired(spec.cap.permissions),
      };
      return { kind: "grantCapability", from: signer, to: hex32(spec.toHex, "grant.to"), cap };
    }
    default: {
      const _never: never = spec;
      throw new Error(`unknown effect kind: ${JSON.stringify(_never)}`);
    }
  }
}

/**
 * Apply a {@link TurnRequestSpec} to a fresh `TurnBuilder` (from
 * `runtime.turn()`), returning the same builder for chaining into `.sign()`.
 * Refuses an empty spec early (the builder also refuses an empty turn at sign
 * time, but failing here gives a clearer message).
 */
export function applySpec(builder: TurnBuilder, spec: TurnRequestSpec, signer: Uint8Array): TurnBuilder {
  if (!spec.effects || spec.effects.length === 0) {
    throw new Error("turn spec has no effects");
  }
  if (spec.method) builder.method(spec.method);
  if (spec.fee !== undefined) builder.fee(spec.fee);
  const effects = spec.effects.map((e) => hydrateEffect(e, signer));
  builder.effects(effects);
  return builder;
}
