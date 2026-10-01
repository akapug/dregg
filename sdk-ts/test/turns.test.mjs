// The authorized turn builder against a mock node: verb staging, the
// empty-turn refusal, federation-id discovery, and a full
// sign() → explain() → submit() → Receipt round trip whose mock pins the
// canonical hybrid framing and enrolled identity carriers. The cross-language
// Rust harness owns the actual signature-verification gate.

import { test } from "node:test";
import assert from "node:assert/strict";
import { createServer } from "node:http";

import { SIGNED_TURN_SUFFIX_LEN, decodeTurnCoordinates, hex, raw, sdk } from "./helpers.mjs";

async function mockNode({ onEnvelope }) {
  const rawMod = await raw();
  const nodePubkey = Uint8Array.from({ length: 32 }, () => 5);
  const receipts = [];
  const server = createServer((req, res) => {
    const send = (code, body) => {
      res.writeHead(code, { "content-type": "application/json" });
      res.end(JSON.stringify(body));
    };
    if (req.url === "/api/node/identity") {
      return send(200, {
        public_key: hex(nodePubkey),
        agent_cell: "00".repeat(32),
        unlocked: true,
        agent_balance: 0,
        agent_nonce: 0,
      });
    }
    if (req.url === "/api/federations") {
      // Unconfigured solo node: a placeholder entry with no real committee.
      return send(200, [
        { id: "00".repeat(32), federation_id: "00".repeat(32), committee_epoch: 0, member_count: 0, is_local: true },
      ]);
    }
    if (req.url?.startsWith("/api/cell/")) {
      return send(200, {
        id: req.url.slice("/api/cell/".length),
        found: true,
        balance: 500,
        nonce: 7,
        public_key: "",
        fields: [],
        last_receipt_hash: null, // this agent has committed nothing yet
      });
    }
    if (req.url === "/api/receipts") {
      return send(200, receipts);
    }
    if (req.url === "/status") {
      // `submit()` counts the turn's deadline (a block height) from this.
      return send(200, { latest_height: receipts.length });
    }
    if (req.url === "/api/turns/submit-signed" && req.method === "POST") {
      const chunks = [];
      req.on("data", (c) => chunks.push(c));
      req.on("end", () => {
        const body = new Uint8Array(Buffer.concat(chunks));
        const result = onEnvelope(body, receipts);
        send(200, result);
      });
      return;
    }
    send(404, { error: "nope" });
  });
  await new Promise((r) => server.listen(0, r));
  return {
    server,
    nodePubkey,
    url: `http://127.0.0.1:${server.address().port}`,
  };
}

test("sign() refuses an empty turn", async () => {
  const { AgentRuntime, Identity, EmptyTurnError } = await sdk();
  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => i));
  const runtime = new AgentRuntime(identity, "http://127.0.0.1:1"); // never contacted
  await assert.rejects(() => runtime.turn().sign(), EmptyTurnError);
});

test("full round trip: verbs -> sign -> explain -> submit -> Receipt", async () => {
  const rawMod = await raw();
  const { AgentRuntime, Identity } = await sdk();

  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => 0x20 + i));
  const agentHex = identity.cellIdHex();

  let verified = null;
  const { server, url, nodePubkey } = await mockNode({
    onEnvelope: (body, receipts) => {
      // Canonical hybrid frame: turn ++ Ed signature/key ++ ML-DSA signature/key.
      const turnBytes = body.subarray(0, body.length - (1 + 64 + 1 + 32 + 2 + 3309 + 2 + 1952));
      assert.equal(body[turnBytes.length], 0x40);
      assert.equal(body[turnBytes.length + 65], 0x20);
      const sig = body.subarray(turnBytes.length + 1, turnBytes.length + 65);
      const signer = body.subarray(turnBytes.length + 66, turnBytes.length + 98);
      const pqSigPrefix = turnBytes.length + 98;
      assert.deepEqual(Array.from(body.subarray(pqSigPrefix, pqSigPrefix + 2)), [0xed, 0x19]);
      const pqSignerPrefix = pqSigPrefix + 2 + 3309;
      assert.deepEqual(Array.from(body.subarray(pqSignerPrefix, pqSignerPrefix + 2)), [0xa0, 0x0f]);
      const pqSigner = body.subarray(pqSignerPrefix + 2);
      assert.equal(hex(pqSigner), hex(identity.mlDsaPublicKey()), "the envelope carries the enrolled PQ identity");
      // signature over the canonical Turn::hash — recompute it from the TS
      // wire vocabulary (the differential test ties this to Rust).
      // We can't re-decode postcard here; instead require the client to have
      // signed SOMETHING this signer verifies, and pin the agent binding.
      assert.equal(hex(signer), identity.publicKeyHex, "signer must be the submitting identity");
      const expectedAgent = rawMod.deriveCellId(signer);
      assert.equal(hex(expectedAgent), agentHex, "turn agent must be derive_raw(signer, blake3('default'))");
      // The turn bytes BEGIN with the agent cell id (postcard field order).
      assert.equal(hex(turnBytes.subarray(0, 32)), agentHex);
      verified = { sig, turnBytes };
      const turnHashHex = "cd".repeat(32); // the mock's name for it
      receipts.push({
        chain_index: 0,
        chain_head: true,
        receipt_hash: "ef".repeat(32),
        turn_hash: turnHashHex,
        agent: agentHex,
        pre_state: "11".repeat(32),
        post_state: "22".repeat(32),
        timestamp: 1765432100,
        computrons_used: 100,
        action_count: 1,
        previous_receipt_hash: null,
        finality: "tentative",
        was_encrypted: false,
        was_burn: false,
        has_proof: false,
      });
      return { accepted: true, turn_hash: turnHashHex, action_count: 1 };
    },
  });

  try {
    const runtime = new AgentRuntime(identity, url);

    const to = Uint8Array.from({ length: 32 }, () => 9);
    const builder = runtime.turn().transfer(to, 25n).writeU64(1, 42n).incrementNonce().fee(2000);
    const authorized = await builder.sign();

    // The anti-blind-signing reading: faithful, total, sem-tagged. The default
    // signer is HYBRID post-quantum, and the reading says so — a citizen is
    // told which perimeter they are authorizing under, not just "a signature".
    const explanation = authorized.explain();
    assert.ok(
      explanation.includes("authorized by a HYBRID signature (Ed25519 + ML-DSA-65 post-quantum"),
      `explain() must name the hybrid PQ perimeter, got: ${explanation}`,
    );
    assert.ok(explanation.includes("transfer 25 computrons"));
    assert.ok(explanation.includes("set state field #1"));
    assert.ok(explanation.includes("increment the nonce"));
    assert.ok(explanation.includes("[sem "));

    // The signed action verifies against the discovered federation id
    // (unconfigured solo node → blake3(node operator pubkey)).
    const fedId = rawMod.blake3(nodePubkey);
    const action = authorized.action();
    // The DEFAULT front-door signer is HYBRID post-quantum.
    assert.equal(action.authorization.kind, "hybridSignature");
    // The mock's `/api/cell/` serves nonce 7, so that is the live replay
    // counter `sign()` read and the value `sig-v3` binds into the signature.
    // (Signing over any other nonce verifies nowhere — see the wrong-nonce
    // falsifier in `hybrid-verify.test.mjs`.)
    const msg = rawMod.actionSigningMessage(action, fedId, 7n);
    assert.ok(
      rawMod.ed25519Verify(identity.publicKey, msg, action.authorization.ed25519),
      "the ed25519 half must verify over the canonical federation+nonce-bound message",
    );
    // BOTH halves cover that same message — the PQ half is real, not decorative.
    assert.ok(
      rawMod.mlDsaVerify(action.authorization.mlDsaPk, msg, action.authorization.mlDsa),
      "the ML-DSA-65 half must verify over the SAME message under the turn ctx",
    );
    assert.equal(
      hex(action.authorization.mlDsaPk),
      hex(identity.mlDsaPublicKey()),
      "the carried PQ public key is the one derived from this identity's seed",
    );

    const receipt = await authorized.submit();
    assert.ok(verified, "the mock saw and verified the envelope");
    assert.equal(receipt.turnHash, "cd".repeat(32));
    assert.equal(receipt.receiptHash, "ef".repeat(32));
    assert.equal(receipt.agent, agentHex);
    assert.equal(receipt.hasProof(), false, "receipts are born proofless");

    // One-shot submit (consume-on-submit parity).
    await assert.rejects(() => authorized.submit(), /already submitted/);
  } finally {
    server.close();
  }
});

test("on(target) retargets the action while the agent still signs and pays", async () => {
  const rawMod = await raw();
  const { AgentRuntime, Identity } = await sdk();
  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => 0x40 + i));
  const target = Uint8Array.from({ length: 32 }, () => 0x77);

  const { server, url } = await mockNode({
    onEnvelope: () => ({ accepted: true, turn_hash: "aa".repeat(32) }),
  });
  try {
    const runtime = new AgentRuntime(identity, url);
    const authorized = await runtime.turn().on(target).writeU64(0, 1n).sign();
    const action = authorized.action();
    assert.equal(hex(action.target), hex(target), ".on(target) must aim the ACTION at the target");
    // The write verb defaulted its cell to the acting (target) cell.
    assert.equal(hex(action.effects[0].cell), hex(target));
  } finally {
    server.close();
  }
});

// ─── the per-agent receipt head ─────────────────────────────────────────────
//
// The node admits a signed turn only when `previous_receipt_hash` equals the
// AGENT's own head (`agent_receipt_head_hash(turn.agent)`), served on
// `GET /api/cell/{agent}` as `last_receipt_hash`. Until 2026-09-30 `submit()`
// threaded the NODE-WIDE tip of `GET /api/receipts`, so any turn was refused
// whenever another agent had committed since this agent's last receipt, and its
// one retry read the same wrong tip. This mock enforces the node's rule.

const AGENT_SUBMIT_REFUSAL = "receipt chain mismatch";

/** A mock node that keeps per-agent heads and nonces and refuses exactly as the node does. */
async function chainMockNode({ afterAgentCellRead } = {}) {
  const nodePubkey = Uint8Array.from({ length: 32 }, () => 5);
  const agents = new Map(); // agentHex -> { nonce: bigint, head: string | null }
  const receipts = []; // node-wide, newest last
  const submits = []; // every envelope the node saw: { agent, nonce, previousReceiptHash, accepted }
  let minted = 0;
  const commit = (agentHex) => {
    const a = agents.get(agentHex) ?? { nonce: 0n, head: null };
    minted += 1;
    // Heads never end in 0x00 (see `decodeTurnCoordinates`).
    const receiptHash = minted.toString(16).padStart(2, "0").repeat(32);
    const turnHash = (0x80 + minted).toString(16).repeat(32);
    for (const r of receipts) r.chain_head = false;
    receipts.push({
      chain_index: receipts.length,
      chain_head: true,
      receipt_hash: receiptHash,
      turn_hash: turnHash,
      agent: agentHex,
      pre_state: "11".repeat(32),
      post_state: "22".repeat(32),
      timestamp: 1,
      computrons_used: 10,
      action_count: 1,
      previous_receipt_hash: a.head,
      finality: "tentative",
      was_encrypted: false,
      was_burn: false,
      has_proof: false,
    });
    agents.set(agentHex, { nonce: a.nonce + 1n, head: receiptHash });
    return { receiptHash, turnHash };
  };
  const server = createServer((req, res) => {
    const send = (code, body) => {
      res.writeHead(code, { "content-type": "application/json" });
      res.end(JSON.stringify(body));
    };
    if (req.url === "/api/node/identity") {
      return send(200, { public_key: hex(nodePubkey), agent_cell: "00".repeat(32), unlocked: true, agent_balance: 0, agent_nonce: 0 });
    }
    if (req.url === "/api/federations") {
      return send(200, [{ id: "00".repeat(32), federation_id: "00".repeat(32), committee_epoch: 0, member_count: 0, is_local: true }]);
    }
    if (req.url?.startsWith("/api/cell/")) {
      const id = req.url.slice("/api/cell/".length);
      const a = agents.get(id) ?? { nonce: 0n, head: null };
      send(200, { id, found: true, balance: 500, nonce: Number(a.nonce), public_key: "", fields: [], last_receipt_hash: a.head });
      afterAgentCellRead?.(id, { commit, agents, receipts });
      return;
    }
    if (req.url === "/api/receipts") return send(200, receipts);
    if (req.url === "/status") return send(200, { latest_height: receipts.length });
    if (req.url === "/api/turns/submit-signed" && req.method === "POST") {
      const chunks = [];
      req.on("data", (c) => chunks.push(c));
      req.on("end", () => {
        const body = new Uint8Array(Buffer.concat(chunks));
        const turnBytes = body.subarray(0, body.length - SIGNED_TURN_SUFFIX_LEN);
        const agent = hex(turnBytes.subarray(0, 32));
        const coords = decodeTurnCoordinates(turnBytes);
        const live = agents.get(agent) ?? { nonce: 0n, head: null };
        const seen = { agent, nonce: coords.nonce, previousReceiptHash: coords.previousReceiptHash ?? null };
        submits.push(seen);
        if (seen.previousReceiptHash !== live.head) {
          seen.accepted = false;
          return send(200, { accepted: false, turn_hash: null, error: AGENT_SUBMIT_REFUSAL });
        }
        if (coords.nonce !== live.nonce) {
          seen.accepted = false;
          return send(200, { accepted: false, turn_hash: null, error: `nonce mismatch: expected ${live.nonce}` });
        }
        seen.accepted = true;
        const { turnHash } = commit(agent);
        send(200, { accepted: true, turn_hash: turnHash, action_count: 1 });
      });
      return;
    }
    send(404, { error: "nope" });
  });
  await new Promise((r) => server.listen(0, r));
  return { server, commit, agents, receipts, submits, url: `http://127.0.0.1:${server.address().port}` };
}

test("submit() threads the AGENT's own head: another agent committing between the read and the submit does not refuse it", async () => {
  const { AgentRuntime, Identity } = await sdk();
  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => 0x61 + i));
  const me = identity.cellIdHex();
  const other = "b0".repeat(32);

  let submitPhase = false;
  const node = await chainMockNode({
    // Another agent commits right AFTER this agent's coordinates are read —
    // the node-wide tip moves between the read and the submit.
    afterAgentCellRead: (id, { commit }) => {
      if (submitPhase && id === me) commit(other);
    },
  });
  try {
    // History: I committed once, then the other agent committed after me, so
    // the node-wide tip is NOT my head even before the race.
    const mine = node.commit(me);
    node.commit(other);

    const runtime = new AgentRuntime(identity, node.url);
    const authorized = await runtime.turn().incrementNonce().sign();
    submitPhase = true;
    const receipt = await authorized.submit();

    const nodeWideTip = node.receipts.find((r) => r.chain_head).receipt_hash;
    assert.notEqual(nodeWideTip, mine.receiptHash, "precondition: the node-wide tip is another agent's receipt");
    assert.equal(node.submits.length, 1, "lands on the FIRST attempt — nothing to retry");
    assert.equal(node.submits[0].previousReceiptHash, mine.receiptHash, "the turn carried MY head, not the node-wide tip");
    assert.equal(node.submits[0].nonce, 1n);
    assert.equal(receipt.agent, me);
    assert.equal(receipt.previousReceiptHash, mine.receiptHash);
  } finally {
    node.server.close();
  }
});

test("a turn carrying the NODE-WIDE tip is refused by this mock (the head test can fail)", async () => {
  // The falsifier for the test above: the mock really enforces the agent's own
  // head, so an SDK threading `/api/receipts`' tip would be refused here.
  const rawMod = await raw();
  const { Identity } = await sdk();
  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => 0x62 + i));
  const node = await chainMockNode();
  try {
    node.commit(identity.cellIdHex());
    const tip = node.commit("b1".repeat(32)).receiptHash;
    const agent = identity.cellId();
    const fed = new Uint8Array(32);
    const action = identity.signAction(rawMod.unsignedActionNamed(agent, "execute", [{ kind: "incrementNonce", cell: agent }]), fed, 1n);
    const turn = { agent, nonce: 1n, roots: [{ action, children: [] }], fee: 0n, validUntil: 1800n, previousReceiptHash: Uint8Array.from(Buffer.from(tip, "hex")) };
    const res = await fetch(`${node.url}/api/turns/submit-signed`, { method: "POST", body: identity.signTurnEnvelope(turn) });
    const json = await res.json();
    assert.equal(json.accepted, false);
    assert.equal(json.error, AGENT_SUBMIT_REFUSAL);
  } finally {
    node.server.close();
  }
});

test("submit() retries once over a RE-READ head when this agent's own head moved under it", async () => {
  const rawMod = await raw();
  const { AgentRuntime, Identity } = await sdk();
  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => 0x63 + i));
  const me = identity.cellIdHex();

  let submitReads = 0;
  let raced = null;
  const node = await chainMockNode({
    // On the FIRST submit-phase read only, a concurrent turn of MINE commits
    // after my coordinates were read: my head and nonce both move.
    afterAgentCellRead: (id, { commit }) => {
      if (id !== me) return;
      submitReads += 1;
      if (submitReads === 2) raced = commit(me); // read #1 is sign()'s, #2 is submit()'s first
    },
  });
  try {
    const first = node.commit(me);
    const runtime = new AgentRuntime(identity, node.url);
    const authorized = await runtime.turn().incrementNonce().sign();
    const receipt = await authorized.submit();

    assert.ok(raced, "the race happened");
    assert.equal(node.submits.length, 2, "refused once, then retried once");
    assert.deepEqual(
      node.submits.map((s) => [s.previousReceiptHash, s.nonce, s.accepted]),
      [
        [first.receiptHash, 1n, false],
        [raced.receiptHash, 2n, true],
      ],
      "the retry re-read BOTH coordinates and carried the moved head and nonce",
    );
    assert.equal(receipt.previousReceiptHash, raced.receiptHash);
    // sig-v3 binds the nonce, so the retry re-signed the ACTION over the new one.
    const fed = rawMod.blake3(Uint8Array.from({ length: 32 }, () => 5));
    const action = authorized.action();
    assert.ok(rawMod.ed25519Verify(identity.publicKey, rawMod.actionSigningMessage(action, fed, 2n), action.authorization.ed25519));
  } finally {
    node.server.close();
  }
});
