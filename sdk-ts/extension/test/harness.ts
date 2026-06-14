/**
 * The headless test harness entry — ONE bundle re-exporting everything the
 * trusted-path test drives, so the mediator and the test share a single copy of
 * the SDK classes (no cross-bundle class-identity mismatch). esbuild inlines the
 * SDK + @noble into this file (see build.mjs `--tests`).
 */

export { TrustedPathMediator, TurnDeclinedError, receiptView } from "../src/mediator";
export { buildApprovalView, plainLines, anyUnknown } from "../src/explain-plain";
export { applySpec } from "../src/spec";

// The SDK surface the test constructs the runtime + a native-signature oracle
// from — the SAME classes the mediator closes over.
export {
  Identity,
  AgentRuntime,
  NodeClient,
  hexEncode,
  hexDecode,
} from "@dregg/sdk/browser";
export type { Turn, Action, Effect } from "@dregg/sdk/browser";
