// THE DRIVEN PASSKEY RUN — an EXTENSION-LESS passkey voter really participates.
//
// Loads the same Commons demo in a real (headless) Chromium, attaches a CDP WebAuthn
// VIRTUAL AUTHENTICATOR (PRF, mirroring extension/tests/passkey-sign), then:
//   1. enrolls a WebAuthn passkey on the page — no extension (PRF-wraps a dregg key);
//   2. casts the "you" ballot through the REAL StoryEngine over the REAL wasm
//      StoryWorld / CollectiveChoiceEngine, under the passkey's STABLE public id, with
//      the ballot's consent routed through a genuine biometric (PRF) assertion;
//   3. ASSERTS the ballot COUNTED under that stable id (the tally grew by one, the
//      engine recorded the passkey's public key as the voter, and a SECOND ballot from
//      the same id is refused — a stable ballot identity, one voter one vote).
//
//   node demo/run-passkey.mjs
//
// Fail-honest: if this Chromium cannot virtualize the WebAuthn PRF extension, enroll
// fails with a PRF error and the run reports that exact coupling rather than faking it.

import assert from "node:assert/strict";
import { mkdir, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";
import path from "node:path";
import { makeServer } from "./serve.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");

const pwRequire = createRequire(path.join(REPO, "extension", "tests", "package.json"));
const { chromium } = pwRequire("playwright");

const OUT = path.join(__dirname, "run");

/** A CDP WebAuthn virtual authenticator with PRF (hmac-secret) — the same setup the
 *  committed passkey tests use. Falls back to a non-PRF authenticator so we can report
 *  the coupling honestly (enroll then fails closed on the missing PRF extension). */
async function addAuthenticator(client) {
  await client.send("WebAuthn.enable", { enableUI: false });
  const base = {
    protocol: "ctap2",
    ctap2Version: "ctap2_1",
    transport: "internal",
    hasResidentKey: true,
    hasUserVerification: true,
    automaticPresenceSimulation: true,
    isUserVerified: true,
  };
  try {
    const { authenticatorId } = await client.send("WebAuthn.addVirtualAuthenticator", {
      options: { ...base, hasPrf: true },
    });
    return { authenticatorId, prf: true };
  } catch {
    const { authenticatorId } = await client.send("WebAuthn.addVirtualAuthenticator", {
      options: base,
    });
    return { authenticatorId, prf: false };
  }
}

async function main() {
  await mkdir(OUT, { recursive: true });
  const { server, base } = await makeServer(0);
  const browser = await chromium.launch({ headless: true });
  const pageErrors = [];
  try {
    const page = await browser.newPage({ viewport: { width: 900, height: 1400 }, deviceScaleFactor: 2 });
    page.on("pageerror", (e) => pageErrors.push(String(e)));
    page.on("console", (m) => { if (m.type() === "error") pageErrors.push(`console: ${m.text()}`); });

    const client = await page.context().newCDPSession(page);
    const { authenticatorId } = await addAuthenticator(client);

    // WebAuthn rejects a bare IP as the relying-party id ("invalid domain"), and the
    // demo derives its rpId from `location.hostname` — so drive it over `localhost`
    // (which Chromium resolves to the 127.0.0.1 server) to give a valid RP id.
    const origin = base.replace("127.0.0.1", "localhost");
    await page.goto(`${origin}/`, { waitUntil: "load" });

    // Boot: the element settles verified (or the page fail-closes).
    await page.waitForFunction(
      () => {
        const el = document.getElementById("commons");
        return (el && (el.hasAttribute("verified") || el.hasAttribute("error"))) || !!window.__DEMO_ERROR;
      },
      null,
      { timeout: 40000 },
    );
    const bootErr = await page.evaluate(() => window.__DEMO_ERROR || null);
    if (bootErr) throw new Error(`the demo failed to boot (fail-closed):\n    ${bootErr}`);
    const verifiedAtBoot = await page.evaluate(() => document.getElementById("commons").hasAttribute("verified"));
    assert.equal(verifiedAtBoot, true, "the story resolves + replay-verifies at load");

    const passkeyReady = await page.evaluate(() => window.__PASSKEY_READY === true);
    assert.equal(passkeyReady, true, "the page-side passkey custody constructed (extension-less WebAuthn+WebCrypto)");
    // The stable ballot identity is declared eligible up front (before enroll).
    const declaredId = await page.evaluate(() => window.__PASSKEY_DECLARED_ID || null);

    // ── ENROLL a WebAuthn passkey — no extension ──
    const enroll = await page.evaluate(() => window.__demoEnrollPasskey());
    if (!enroll.ok && /PRF/i.test(String(enroll.error))) {
      throw new Error(
        "REAL SEAM (not faked): this Chromium could not virtualize the WebAuthn PRF extension, so the " +
          `passkey could not wrap the dregg key page-side. Coupling: ${enroll.error}`,
      );
    }
    assert.equal(enroll.ok, true, `passkey enroll succeeded (extension-less): ${enroll.error || ""}`);
    assert.ok(/^[0-9a-f]{64}$/.test(enroll.id), `the passkey minted a 32-byte ed25519 ballot identity (${enroll.id})`);

    // ── CAST the "you" ballot through the passkey, on the real engine ──
    const vote = await page.evaluate(() => window.__demoPasskeyVote());
    assert.equal(vote.ok, true, `the passkey ballot ran: ${vote.error || ""}`);

    // ── ASSERT: an extension-less passkey ballot COUNTED under a stable id ──
    assert.equal(vote.refused, false, `the passkey ballot was accepted (not refused): ${vote.reason || ""}`);
    assert.equal(vote.counted, 1, `the tally grew by exactly one passkey ballot (before ${vote.before} → after ${vote.after})`);
    assert.equal(vote.voter, enroll.id, "the engine recorded the ballot under the passkey's stable public id");
    assert.equal(vote.enrolledPublicKey, enroll.id, "publicKey() == the enrolled dregg key (stable identity)");
    assert.equal(vote.electorateHasId, true, "the passkey's stable id is an eligible ballot identity on the real engine");
    assert.equal(vote.doubleRefused, true, `a SECOND ballot from the same passkey id is refused (one voter, one vote): ${vote.doubleReason || ""}`);
    assert.ok(vote.lastSig && vote.lastSig.signer === enroll.id,
      `the biometric gate produced a genuine hybrid SignedTurn signed by the passkey key (signer ${vote.lastSig && vote.lastSig.signer})`);
    if (declaredId) assert.equal(declaredId, enroll.id, "the up-front declared eligible id == the enrolled passkey id");

    // ── CAPTURE ──
    await page.waitForTimeout(200);
    const shot = path.join(OUT, "passkey-vote.png");
    await page.screenshot({ path: shot, fullPage: true }).catch(() => {});

    const report = renderReport({ base, declaredId, enroll, vote });
    const txt = path.join(OUT, "passkey-vote.txt");
    await writeFile(txt, report, "utf8");

    if (pageErrors.length) console.warn("page console/errors:\n  " + pageErrors.join("\n  "));

    console.log(report);
    console.log(`\n  screenshot → ${shot}`);
    console.log(`  capture    → ${txt}\n`);
    console.log("  ✓ EXTENSION-LESS PASSKEY VOTER: enrolled a WebAuthn passkey, cast a biometric-gated ballot, counted under a stable id.\n");
  } finally {
    await browser.close();
    server.close();
  }
}

function renderReport({ base, declaredId, enroll, vote }) {
  const L = [];
  L.push("THE COMMONS — the extension-less passkey voter");
  L.push("driven run · CDP WebAuthn virtual authenticator (PRF) · real wasm StoryWorld");
  L.push("served at " + base);
  L.push("=".repeat(66));
  L.push("");
  L.push("ENROLL (no extension)");
  L.push(`  WebAuthn passkey enrolled : ${enroll.ok ? "yes" : "NO — " + enroll.error}`);
  L.push(`  stable ballot identity    : ${enroll.id}  (${short(enroll.id)})`);
  L.push(`  declared eligible up front: ${declaredId || "(n/a)"}`);
  L.push("");
  L.push("CAST the \"you\" ballot (biometric-gated, extension-less)");
  L.push(`  option                    : #${vote.option} "${vote.optionLabel}"`);
  L.push(`  recorded voter            : ${vote.voter}`);
  L.push(`  hybrid SignedTurn signer  : ${vote.lastSig ? vote.lastSig.signer : "(none)"}  (ed25519 + ML-DSA-65)`);
  L.push(`  tally                     : ${vote.before} → ${vote.after}   (counted ${vote.counted})`);
  L.push(`  eligible on the engine    : ${vote.electorateHasId ? "yes (in the electorate)" : "NO"}`);
  L.push(`  second ballot, same id    : ${vote.doubleRefused ? "REFUSED (one voter, one vote): " + (vote.doubleReason || "") : "NOT refused (!)"}`);
  L.push("");
  L.push("-".repeat(66));
  L.push("An extension-less person enrolled a WebAuthn passkey, and its ballot counted");
  L.push("on the real CollectiveChoiceEngine under a stable, biometric-gated identity.");
  L.push("Sovereignty without lock-in.");
  L.push("");
  return L.join("\n");
}

function short(idHex) {
  return idHex ? `${idHex.slice(0, 4)}…${idHex.slice(-4)}` : "—";
}

main().catch((e) => {
  console.error("\n  ✗ PASSKEY RUN FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});
