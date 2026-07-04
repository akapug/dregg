/**
 * Plain-language rendering of EXACTLY what a turn does — the popup's
 * anti-blind-signing reading.
 *
 * This never invents a description: every line is derived from the same typed
 * `Effect` term the `AuthorizedTurn` will sign and submit. The friendly summary
 * sits ALONGSIDE the SDK's faithful `explainEffect` reading (which carries the
 * canonical `[sem <digest>]` tag bound to `Effect::hash`), so the screen and the
 * signed bytes cannot drift. An effect kind the SDK cannot read becomes an
 * explicit `UNKNOWN — do not approve` line (never a silent blank), turning a
 * blind signature into a refusal.
 */

import { explainAction, explainEffect, hexEncode } from "@dregg/sdk/browser";
import type { Action, Effect } from "@dregg/sdk/browser";
import type { ApprovalView } from "./protocol";

const short = (b: Uint8Array): string => {
  const h = hexEncode(b);
  return `${h.slice(0, 8)}…${h.slice(-4)}`;
};

/**
 * The friendly one-liner for an effect. Kept deliberately small and total: any
 * kind not enumerated here returns `undefined`, which the caller renders as an
 * UNKNOWN do-not-sign-blind warning — exactly the SDK's discipline.
 */
function friendly(effect: Effect): string | undefined {
  switch (effect.kind) {
    case "transfer":
      return `Send ${effect.amount} computrons to ${short(effect.to)}`;
    case "setField":
      return `Write state slot #${effect.index} of ${short(effect.cell)}`;
    case "incrementNonce":
      return `Advance the nonce of ${short(effect.cell)} (no value change)`;
    case "grantCapability":
      return `Grant a capability on ${short(effect.cap.target)} (slot ${effect.cap.slot}) to ${short(effect.to)}`;
    case "revokeCapability":
      return `Revoke the capability in slot ${effect.slot} of ${short(effect.cell)}`;
    case "emitEvent":
      return `Emit an event (${effect.data.length} field(s)) from ${short(effect.cell)}`;
    case "createCell":
      return `Create a new cell with balance ${effect.balance}`;
    default:
      return undefined;
  }
}

/**
 * One plain line per effect: the friendly summary when readable, else the
 * explicit UNKNOWN warning. Both forms append the SDK's faithful sem-tagged
 * reading so an inspecting user can verify the bytes.
 */
export function plainLines(effects: readonly Effect[]): string[] {
  return effects.map((e, i) => {
    const f = friendly(e);
    const faithful = explainEffect(e); // carries [sem <digest>]
    if (f === undefined) {
      return `${i + 1}. UNKNOWN EFFECT — do not approve unless you trust this page. (${faithful})`;
    }
    return `${i + 1}. ${f}   ${faithful}`;
  });
}

/** True iff some effect could not be read (a blind-signing risk). */
export function anyUnknown(effects: readonly Effect[]): boolean {
  return effects.some((e) => friendly(e) === undefined);
}

/**
 * Build the full {@link ApprovalView} the popup renders before the user
 * approves. `explain` is the SDK's faithful total reading of the signed action;
 * `lines` is the per-effect plain language; `hasUnknown` flips the blind-signing
 * guard. The reading is computed from the SAME `Action` the `AuthorizedTurn`
 * holds — there is no second description that could drift.
 */
export function buildApprovalView(args: {
  action: Action;
  origin: string;
  signerCellIdHex: string;
  pageLabel?: string;
}): ApprovalView {
  const effects = args.action.effects;
  return {
    explain: explainAction(args.action),
    lines: plainLines(effects),
    origin: args.origin,
    signerCellIdHex: args.signerCellIdHex,
    hasUnknown: anyUnknown(effects),
    pageLabel: args.pageLabel,
  };
}
