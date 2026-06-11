// Profile store: the same $DREGG_HOME/profiles layout and semantics as
// sdk/src/profiles.rs (create/list/use/load, env override, 0600, validation).

import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, rmSync, statSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

import { sdk } from "./helpers.mjs";

async function withTempStore(f) {
  const dir = mkdtempSync(join(tmpdir(), "dregg-profile-test-"));
  const oldHome = process.env.DREGG_HOME;
  const oldProfile = process.env.DREGG_PROFILE;
  process.env.DREGG_HOME = dir;
  delete process.env.DREGG_PROFILE;
  try {
    return await f(dir);
  } finally {
    if (oldHome === undefined) delete process.env.DREGG_HOME;
    else process.env.DREGG_HOME = oldHome;
    if (oldProfile === undefined) delete process.env.DREGG_PROFILE;
    else process.env.DREGG_PROFILE = oldProfile;
    rmSync(dir, { recursive: true, force: true });
  }
}

test("create / list / use / load roundtrip", async () => {
  const { profiles } = await sdk();
  await withTempStore(async () => {
    assert.deepEqual(profiles.list(), []);
    const info = profiles.create("ember");
    assert.equal(info.name, "ember");
    assert.equal(info.active, false, "no active profile yet");

    // Duplicate name refused.
    assert.throws(() => profiles.create("ember"), (e) => e.code === "already_exists");

    profiles.create("walnut");
    profiles.setActive("walnut");
    const listing = profiles.list();
    assert.equal(listing.length, 2);
    assert.ok(listing.some((p) => p.name === "walnut" && p.active));
    assert.ok(listing.some((p) => p.name === "ember" && !p.active));

    // The loaded identity's key matches the recorded public key.
    const identity = profiles.load("walnut");
    const rec = listing.find((p) => p.name === "walnut");
    assert.equal(identity.publicKeyHex, rec.publicKeyHex);

    // loadActive resolves the persistent default…
    const active = profiles.loadActive();
    assert.equal(active.publicKeyHex, identity.publicKeyHex);

    // …and DREGG_PROFILE overrides it.
    process.env.DREGG_PROFILE = "ember";
    const overridden = profiles.loadActive();
    assert.equal(overridden.publicKeyHex, profiles.load("ember").publicKeyHex);
    delete process.env.DREGG_PROFILE;
  });
});

test("the on-disk record is the shared version-1 JSON shape", async () => {
  const { profiles } = await sdk();
  await withTempStore(async (dir) => {
    profiles.create("shape");
    const record = JSON.parse(readFileSync(join(dir, "profiles", "shape.json"), "utf8"));
    assert.equal(record.version, 1);
    assert.equal(record.name, "shape");
    assert.match(record.seed_hex, /^[0-9a-f]{128}$/);
    assert.match(record.public_key_hex, /^[0-9a-f]{64}$/);
    assert.equal(typeof record.created_at, "number");
  });
});

test("names are validated and loads are deterministic", async () => {
  const { profiles } = await sdk();
  await withTempStore(async () => {
    assert.throws(() => profiles.create(""), (e) => e.code === "invalid_name");
    assert.throws(() => profiles.create("No Caps"), (e) => e.code === "invalid_name");
    assert.throws(() => profiles.create("../evil"), (e) => e.code === "invalid_name");
    assert.throws(() => profiles.setActive("ghost"), (e) => e.code === "not_found");

    profiles.create("stable");
    const a = profiles.load("stable").publicKeyHex;
    const b = profiles.load("stable").publicKeyHex;
    assert.equal(a, b, "profile load is deterministic (same seed, same key)");
  });
});

test("profile key material is mode 0600", async () => {
  const { profiles } = await sdk();
  await withTempStore(async (dir) => {
    profiles.create("secretive");
    const mode = statSync(join(dir, "profiles", "secretive.json")).mode & 0o777;
    assert.equal(mode, 0o600, "profile key material must be 0600");
  });
});
