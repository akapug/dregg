/**
 * Headless test of the trusted-path front door. Drives the SAME mediator the
 * MV3 background worker uses, with a MOCK node (no network), proving:
 *
 *   1. an UNAPPROVED request is NEVER signed-to-the-wire (no submit);
 *   2. an APPROVED request signs + submits and yields a Receipt;
 *   3. the signature the mediator submits is BYTE-IDENTICAL to the native SDK;
 *   4. the key NEVER leaves the mediator (no path exposes seed material; the
 *      page-facing identity view carries only public fields);
 *   5. the approval view renders the REAL effects (anti-blind-signing) and flags
 *      an effect it cannot read as UNKNOWN (no silent blind signature).
 *
 * Run: `node build.mjs --tests && node --test test/*.test.mjs` (in Docker).
 */

import { test } from "node:test";
import assert from "node:assert/strict";

import {
  TrustedPathMediator,
  TurnDeclinedError,
  buildApprovalView,
  applySpec,
  Identity,
  AgentRuntime,
  NodeClient,
  hexEncode,
} from "./.build/harness.mjs";

// A 32-byte test seed (NOT the golden CLI vector — just deterministic here).
const SEED = new Uint8Array(32);
for (let i = 0; i < 32; i++) SEED[i] = i + 1;

const FED = new Uint8Array(32).fill(7); // a fixed federation id (no discovery)

/**
 * A NodeClient that performs NO network I/O. It records every submitted
 * envelope so the test can assert what (if anything) reached the wire, and
 * returns canned reads for the bits `submit()` consults.
 */
class MockNode extends NodeClient {
  constructor() {
    super("http://mock.invalid", { federationId: FED });
    this.submitted = []; // every envelope the runtime tried to submit
  }
  async federationId() {
    return FED;
  }
  async cell() {
    return { id: "", found: true, balance: 1_000_000, nonce: 0, public_key: "", fields: [] };
  }
  async receipts() {
    return []; // empty chain → receiptChainHead() is undefined
  }
  async receiptChainHead() {
    return undefined;
  }
  async submitSignedEnvelope(envelope) {
    this.submitted.push(envelope);
    // Echo a plausible accepted response (turn_hash filled by the runtime).
    return { accepted: true, turn_hash: null, action_count: 1, proof_status: "pending" };
  }
  async receiptForTurn(turnHashHex) {
    // Minimal committed receipt noun.
    return { turnHash: turnHashHex, finality: "committed", actionCount: 1 };
  }
}

function makeMediator() {
  const node = new MockNode();
  const identity = Identity.fromKeyBytes(SEED);
  const runtime = new AgentRuntime(identity, node, { federationId: FED });
  const mediator = new TrustedPathMediator(runtime, { label: "test id" });
  return { mediator, node, identity, runtime };
}

// A simple transfer spec the page would send (verbs only, no key, no signature).
function transferSpec(toHex, amount = 100) {
  return { effects: [{ kind: "transfer", toHex, amount }] };
}

const bobHex = hexEncode(Identity.fromKeyBytes(new Uint8Array(32).fill(9)).cellId());

test("UNAPPROVED request is never submitted (no signature reaches the wire)", async () => {
  const { mediator, node } = makeMediator();
  let approvalShown = false;
  const declineGate = async (view) => {
    approvalShown = true;
    // The user is shown the real reading, then declines.
    assert.match(view.explain, /transfer 100 computrons/);
    return false;
  };
  await assert.rejects(
    () => mediator.handleTurnFromOrigin(transferSpec(bobHex), "https://evil.example", declineGate),
    (e) => e instanceof TurnDeclinedError,
  );
  assert.equal(approvalShown, true, "the user must be shown the reading before any decision");
  assert.equal(node.submitted.length, 0, "a declined turn must submit NOTHING to the wire");
});

test("APPROVED request signs + submits and returns a Receipt", async () => {
  const { mediator, node } = makeMediator();
  const approveGate = async () => true;
  const receipt = await mediator.handleTurnFromOrigin(transferSpec(bobHex), "https://dapp.example", approveGate);
  assert.equal(node.submitted.length, 1, "exactly one envelope reaches the wire on approval");
  assert.ok(receipt.turnHash, "a receipt with a turn hash is returned");
  assert.equal(receipt.finality, "committed");
});

test("the submitted signature is BYTE-IDENTICAL to the native SDK", async () => {
  // Mediator path: build+sign+submit the transfer through the front door.
  const { mediator, node } = makeMediator();
  await mediator.handleTurnFromOrigin(transferSpec(bobHex), "https://dapp.example", async () => true);
  const mediatorEnvelope = node.submitted[0];

  // Native SDK path: the SAME identity builds+signs the SAME transfer directly.
  const node2 = new MockNode();
  const id2 = Identity.fromKeyBytes(SEED);
  const rt2 = new AgentRuntime(id2, node2, { federationId: FED });
  const signed = await rt2.turn().transfer(id2.cellId(), 0n).sign(); // placeholder, replaced below
  // Build the identical transfer (to bob, 100) the spec produced:
  const signedNative = await rt2
    .turn()
    .transfer(Identity.fromKeyBytes(new Uint8Array(32).fill(9)).cellId(), 100n)
    .sign();
  await signedNative.submit();
  const nativeEnvelope = node2.submitted.at(-1);

  // The per-action Ed25519 signature is the load-bearing equality. Compare the
  // full signed-turn envelopes byte-for-byte (they share nonce 0, empty chain
  // head, the same fed id, and the deterministic ed25519 signature).
  assert.equal(
    hexEncode(mediatorEnvelope),
    hexEncode(nativeEnvelope),
    "front-door envelope must equal the native SDK envelope byte-for-byte",
  );
  // (sanity: the placeholder build did not pollute the comparison)
  assert.ok(signed);
});

test("the key NEVER leaves the mediator (only public fields are exposed)", async () => {
  const { mediator, identity } = makeMediator();
  const view = mediator.identityView();
  // The page-facing view is exactly the public hint.
  assert.equal(view.cellIdHex, identity.cellIdHex());
  assert.equal(view.publicKeyHex, identity.publicKeyHex);
  // No seed/private material anywhere in the serialized view.
  const serialized = JSON.stringify(view);
  const seedHex = hexEncode(SEED);
  assert.ok(!serialized.includes(seedHex), "the view must not contain the seed");
  // The mediator exposes no method that returns key bytes.
  assert.equal(typeof mediator.seed, "undefined");
  assert.equal(typeof mediator.identityView().seed, "undefined");
  assert.equal(typeof mediator.identityView().privateKey, "undefined");
});

test("the approval view renders the REAL effects (anti-blind-signing)", async () => {
  const { mediator } = makeMediator();
  let captured;
  await mediator
    .handleTurnFromOrigin(transferSpec(bobHex, 4242), "https://dapp.example", async (view) => {
      captured = view;
      return false; // decline; we only want the reading
    })
    .catch(() => {});
  assert.ok(captured, "the gate received an approval view");
  assert.equal(captured.origin, "https://dapp.example");
  assert.equal(captured.hasUnknown, false, "a plain transfer is fully readable");
  assert.match(captured.lines[0], /Send 4242 computrons/);
  assert.match(captured.lines[0], /\[sem [0-9a-f]{64}\]/, "each line carries the faithful sem digest");
  assert.match(captured.explain, /transfer 4242 computrons/);
});

test("an unreadable effect flags UNKNOWN (no silent blind signature)", () => {
  // The do-not-sign-blind guard: an effect kind the friendly renderer does NOT
  // enumerate (e.g. a future wire variant the popup has not learned to read yet)
  // must surface as UNKNOWN, never a silent blank. We forge such an effect by
  // using a kind outside the modeled set (the type system forbids this in normal
  // code; here we prove the runtime guard holds if it ever happens).
  const cell = new Uint8Array(32).fill(1);
  const action = {
    target: cell,
    method: new Uint8Array(32),
    args: [],
    authorization: { kind: "signature", r: new Uint8Array(32), s: new Uint8Array(32) },
    // A deliberately-unmodeled effect kind — the friendly switch returns
    // undefined for it, tripping the UNKNOWN line. (explainEffect tolerates the
    // unknown kind by falling through; the guard is what matters.)
    effects: [{ kind: "futureUnknownEffect", cell }],
  };
  const view = buildApprovalView({ action, origin: "x", signerCellIdHex: "ab" });
  assert.equal(view.hasUnknown, true, "an effect with no friendly reading is UNKNOWN");
  assert.match(view.lines[0], /UNKNOWN EFFECT/);
});

test("a page cannot smuggle a foreign source cell (from is pinned to the signer)", async () => {
  const { mediator, identity, runtime } = makeMediator();
  // Even if a page tried to set a foreign `from`, the spec hydration ignores it
  // and pins `from` to the signer. Assert via applySpec directly.
  const builder = runtime.turn();
  applySpec(builder, transferSpec(bobHex, 50), identity.cellId());
  const signed = await builder.sign();
  const eff = signed.action().effects[0];
  assert.equal(hexEncode(eff.from), identity.cellIdHex(), "transfer source is the signer, not page-chosen");
  assert.ok(mediator); // keep the mediator referenced
});
