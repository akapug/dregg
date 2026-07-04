// Events: SSE parser unit coverage + a live subscribe() against a local
// mock node — including a mid-stream connection drop, to prove the
// Last-Event-ID resume + reconnect path actually resumes.

import { test } from "node:test";
import assert from "node:assert/strict";
import { createServer } from "node:http";

import { sdk } from "./helpers.mjs";

function wireReceipt(i) {
  const word = (n) => Array.from({ length: 32 }, () => n);
  return {
    chain_index: i,
    receipt_hash: `${i}`.padStart(64, "a"),
    turn_hash: `${i}`.padStart(64, "b"),
    cells: [],
    kinds: ["transfer"],
    height: i,
    has_proof: false,
    finality: "tentative",
    timestamp: 1765432100 + i,
    receipt: {
      turn_hash: word(i),
      forest_hash: word(0),
      pre_state_hash: word(1),
      post_state_hash: word(2),
      timestamp: 1765432100 + i,
      effects_hash: word(3),
      computrons_used: 100,
      action_count: 1,
      previous_receipt_hash: null,
      agent: word(9),
      finality: "Tentative",
      was_encrypted: false,
      was_burn: false,
    },
  };
}

test("SSE parser: chunk boundaries, comments, multi-line data, CRLF", async () => {
  const { createSseParser } = await import("../dist/index.mjs");
  const p = createSseParser();
  let events = [];
  // Heartbeat comment alone produces nothing.
  events = events.concat(p.feed(": hb\n\n"));
  assert.equal(events.length, 0);
  // An event split across arbitrary chunk boundaries still parses.
  events = events.concat(p.feed("id: 4\neve"));
  events = events.concat(p.feed("nt: receipt\ndata: {\"a\""));
  events = events.concat(p.feed(": 1}\n\n"));
  assert.equal(events.length, 1);
  assert.equal(events[0].id, "4");
  assert.equal(events[0].event, "receipt");
  assert.equal(events[0].data, '{"a": 1}');
  // CRLF + multi-line data join with \n.
  const more = p.feed("data: line1\r\ndata: line2\r\n\r\n");
  assert.equal(more.length, 1);
  assert.equal(more[0].data, "line1\nline2");
});

test("subscribe() yields Receipt nouns; reconnect resumes from Last-Event-ID", async () => {
  const requests = [];
  const server = createServer((req, res) => {
    requests.push({ url: req.url, lastEventId: req.headers["last-event-id"] ?? null });
    res.writeHead(200, {
      "content-type": "text/event-stream",
      "cache-control": "no-cache",
    });
    const resume = req.headers["last-event-id"];
    const start = resume !== undefined ? Number(resume) + 1 : 0;
    if (start === 0) {
      // First connection: two receipts, then drop the connection mid-stream
      // to force the reconnect path.
      res.write(": hb\n\n");
      res.write(`event: receipt\nid: 0\ndata: ${JSON.stringify(wireReceipt(0))}\n\n`);
      res.write(`event: receipt\nid: 1\ndata: ${JSON.stringify(wireReceipt(1))}\n\n`);
      setTimeout(() => res.destroy(), 20);
    } else {
      // Resumed connection: serve from the cursor.
      res.write(`event: receipt\nid: ${start}\ndata: ${JSON.stringify(wireReceipt(start))}\n\n`);
      // Keep open; the client closes.
    }
  });
  await new Promise((r) => server.listen(0, r));
  const port = server.address().port;

  const { NodeEvents, ReceiptFilter } = await sdk();
  const events = new NodeEvents(`http://127.0.0.1:${port}`, { initialBackoffMs: 10 });
  const stream = events.subscribe(new ReceiptFilter().kind("transfer"));

  const got = [];
  for await (const receipt of stream) {
    got.push(receipt);
    if (got.length === 3) break;
  }
  server.close();

  assert.equal(got.length, 3);
  assert.equal(got[0].chainIndex, 0);
  assert.equal(got[1].chainIndex, 1);
  assert.equal(got[2].chainIndex, 2, "the third receipt must come from the RESUMED connection");
  // The receipts are the full noun, built from the canonical wire receipt.
  assert.equal(got[0].agent, "09".repeat(32));
  assert.equal(got[0].finality, "tentative");
  assert.equal(got[0].hasProof(), false);
  // The reconnect carried Last-Event-ID = 1.
  assert.ok(requests.length >= 2, "expected a reconnect");
  assert.equal(requests[1].lastEventId, "1");
  // The filter rode the query string.
  assert.match(requests[0].url, /kind=transfer/);
});

test("a wrong-turn proof attachment is refused; first writer wins", async () => {
  const { Receipt, TurnProof, WrongTurnProofError } = await sdk();
  const receipt = new Receipt({ turnHash: "ab".repeat(32) });
  assert.equal(receipt.hasProof(), false);

  const wrong = new TurnProof(Uint8Array.from({ length: 32 }, () => 0xcd), new Uint8Array(4));
  assert.throws(() => receipt.attachProof(wrong), WrongTurnProofError);
  assert.equal(receipt.hasProof(), false, "a mis-bound attachment is refused, not stored");

  const right = new TurnProof(Uint8Array.from({ length: 32 }, () => 0xab), new Uint8Array(4));
  assert.equal(receipt.attachProof(right), true);
  assert.equal(receipt.hasProof(), true);
  const second = new TurnProof(Uint8Array.from({ length: 32 }, () => 0xab), new Uint8Array(8));
  assert.equal(receipt.attachProof(second), false, "a receipt never silently swaps attestations");
  assert.equal(receipt.proof().bytes.length, 4);
});
