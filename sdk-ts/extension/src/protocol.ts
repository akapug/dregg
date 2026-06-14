/**
 * The page <-> extension provider protocol — the ONE narrow message vocabulary
 * that crosses the trusted-path boundary.
 *
 * The shape of the front door (mirrors `@dregg/sdk`'s two-noun door):
 *
 *   page  --request-->  content-script  --port-->  background (the Identity)
 *                                                       |
 *                                                  approval popup
 *                                                  (user reads explain())
 *                                                       |
 *   page  <--receipt--  content-script  <--port--  background (.sign().submit())
 *
 * The KEY never appears in this vocabulary. A page can ASK for an identity hint,
 * ASK to sign+submit a turn it describes (verbs only — no key, no signature),
 * and RECEIVE a receipt. It can never receive, set, or influence key material;
 * the most a page learns is the signer's public cell id and the committed
 * receipt. Authorization stays inescapable: the background only ever builds
 * turns through `@dregg/sdk`'s `AgentRuntime.turn()` (no `Unchecked` path), and
 * a turn is signed ONLY after the user approves the faithful `explain()` reading.
 */

import type { Effect } from "@dregg/sdk/browser";

/** A page's description of ONE turn to sign — verbs only, never a signature. */
export interface TurnRequestSpec {
  /** Optional human label the dapp suggests (advisory; never trusted as the reading). */
  readonly label?: string;
  /** The acting method verb (default `"execute"`). */
  readonly method?: string;
  /** The computron budget (default 10000, Rust parity). */
  readonly fee?: number;
  /**
   * The effects to stage, as the SDK's wire `Effect` projections with hex
   * strings for byte fields (the page speaks JSON; the background re-hydrates to
   * `Uint8Array` and routes them through `AgentRuntime.turn().effects(...)`).
   * The background re-derives `from` cells to the signer where a verb implies it,
   * so a page cannot smuggle a foreign source cell past the executor's gates.
   */
  readonly effects: readonly EffectSpec[];
}

/** JSON-friendly `Effect` (hex strings for the 32-byte fields). */
export type EffectSpec =
  | { kind: "setField"; index: number; valueHex: string }
  | { kind: "transfer"; toHex: string; amount: string | number }
  | { kind: "incrementNonce" }
  | {
      kind: "grantCapability";
      toHex: string;
      cap: { targetHex: string; slot: number; permissions: AuthRequiredSpec };
    };

/** JSON-friendly `AuthRequired` (the c-list permission a grant installs). */
export type AuthRequiredSpec =
  | { kind: "none" }
  | { kind: "signature" }
  | { kind: "proof" }
  | { kind: "either" }
  | { kind: "impossible" }
  | { kind: "custom"; vkHashHex: string };

/** Methods a page can invoke through `window.dregg` (the narrow surface). */
export type ProviderMethod =
  | "dregg:identity" // unrestricted: the signer's public cell id (no key)
  | "dregg:isConnected" // unrestricted: is the extension present + unlocked
  | "dregg:turn"; // restricted: sign+submit a described turn (approval-gated)

/** Methods any origin may call without an approval prompt (read-only, no key). */
export const UNRESTRICTED_METHODS: ReadonlySet<ProviderMethod> = new Set<ProviderMethod>([
  "dregg:identity",
  "dregg:isConnected",
]);

/** Methods that ALWAYS require explicit user approval of the explain() reading. */
export const RESTRICTED_METHODS: ReadonlySet<ProviderMethod> = new Set<ProviderMethod>([
  "dregg:turn",
]);

/** A request crossing page -> content-script -> background. */
export interface ProviderRequest {
  readonly type: ProviderMethod;
  /** Page-generated correlation id. */
  readonly id: string;
  /** Present only for `dregg:turn`. */
  readonly spec?: TurnRequestSpec;
}

/** The identity hint a page may read (NO key material — public cell id only). */
export interface IdentityView {
  readonly cellIdHex: string;
  readonly publicKeyHex: string;
  readonly label?: string;
}

/** The committed-turn result handed back to the page (the `Receipt` noun, JSON). */
export interface ReceiptView {
  readonly turnHash: string;
  readonly receiptHash?: string;
  readonly agent?: string;
  readonly postStateHash?: string;
  readonly computronsUsed?: number;
  readonly actionCount?: number;
  readonly finality?: string;
}

/** A response crossing background -> content-script -> page. */
export type ProviderResponse =
  | { id: string; ok: true; result: IdentityView | ReceiptView | { connected: boolean } }
  | { id: string; ok: false; error: string };

/** The reading the popup shows the user before they approve (anti-blind-signing). */
export interface ApprovalView {
  /** The faithful, total `@dregg/sdk` `explain()` reading of EXACTLY what is signed. */
  readonly explain: string;
  /** Per-line plain-language rendering of each effect (derived from the same term). */
  readonly lines: readonly string[];
  /** The requesting page origin (shown so the user knows who is asking). */
  readonly origin: string;
  /** The signer's public cell id (who would sign). */
  readonly signerCellIdHex: string;
  /** Any effect the SDK could not read maps to a do-not-sign-blind warning. */
  readonly hasUnknown: boolean;
  /** Advisory label the page suggested (clearly marked as page-supplied). */
  readonly pageLabel?: string;
}
