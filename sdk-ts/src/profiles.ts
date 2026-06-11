/**
 * Named local identity profiles — the SAME store as the Rust SDK and CLI
 * (`dregg id create / list / use`; sdk/src/profiles.rs).
 *
 * ## Store layout (shared across implementations)
 *
 * ```text
 * $DREGG_HOME/profiles/<name>.json   (else ~/.dregg/profiles/) — mode 0600
 * $DREGG_HOME/profiles/ACTIVE        — the persistent default (a name)
 * ```
 *
 * Profile file (version 1):
 * `{ "version": 1, "name", "seed_hex" (128 hex), "public_key_hex", "created_at" }`
 *
 * `seed_hex` is the 64-byte master seed; the identity is
 * `blake3::derive_key("dregg/0", seed)` → Ed25519 — pinned by the shared
 * golden vector (seed 00..3f → pub 335840a9…8b9a) in this package's tests,
 * in sdk/src/profiles.rs, cli/src/commands/id.rs, and the extension.
 *
 * Resolution order: `DREGG_PROFILE` env override → `ACTIVE` file → none.
 *
 * Node-only (filesystem + process env).
 */

import { chmodSync, existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { randomBytes } from "node:crypto";
import { join } from "node:path";

import { Identity } from "./identity";
import { hexDecodeExact, hexEncode } from "./internal/bytes";

/** Environment variable that overrides the persistent active profile. */
export const PROFILE_ENV = "DREGG_PROFILE";

/** A profile's public face (no key material). */
export interface ProfileInfo {
  name: string;
  publicKeyHex: string;
  createdAt: number;
  active: boolean;
}

/** Profile-store errors (mirrors `sdk::profiles::ProfileError`). */
export class ProfileError extends Error {
  readonly code:
    | "invalid_name"
    | "already_exists"
    | "not_found"
    | "io"
    | "malformed";

  constructor(code: ProfileError["code"], message: string) {
    super(message);
    this.name = "ProfileError";
    this.code = code;
  }
}

interface ProfileFile {
  version: number;
  name: string;
  seed_hex: string;
  public_key_hex: string;
  created_at: number;
}

/** `$DREGG_HOME/profiles` if set, else `~/.dregg/profiles`. */
export function profilesDir(): string {
  const home = process.env.DREGG_HOME;
  if (home) return join(home, "profiles");
  const base = process.env.HOME ?? ".";
  return join(base, ".dregg", "profiles");
}

function validName(name: string): boolean {
  return /^[a-z0-9_-]{1,64}$/.test(name);
}

function profilePath(name: string): string {
  return join(profilesDir(), `${name}.json`);
}

function activePath(): string {
  return join(profilesDir(), "ACTIVE");
}

function writePrivate(path: string, contents: string | Uint8Array): void {
  mkdirSync(profilesDir(), { recursive: true });
  writeFileSync(path, contents, { mode: 0o600 });
  // writeFileSync's mode only applies on create; pin it for overwrites too.
  chmodSync(path, 0o600);
}

function readProfile(name: string): ProfileFile {
  const path = profilePath(name);
  if (!existsSync(path)) {
    throw new ProfileError("not_found", `profile ${JSON.stringify(name)} not found`);
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(readFileSync(path, "utf8"));
  } catch (e) {
    throw new ProfileError("malformed", `profile file for ${JSON.stringify(name)} is malformed: ${(e as Error).message}`);
  }
  const p = parsed as Partial<ProfileFile>;
  if (
    typeof p !== "object" || p === null ||
    p.version !== 1 ||
    typeof p.name !== "string" ||
    typeof p.seed_hex !== "string" ||
    typeof p.public_key_hex !== "string"
  ) {
    throw new ProfileError("malformed", `profile file for ${JSON.stringify(name)} is malformed: missing/invalid fields`);
  }
  return {
    version: 1,
    name: p.name,
    seed_hex: p.seed_hex,
    public_key_hex: p.public_key_hex,
    created_at: typeof p.created_at === "number" ? p.created_at : 0,
  };
}

/**
 * Create a named profile with a fresh random 64-byte seed. Fails if the name
 * is taken. Does NOT change the active profile (call [`setActive`]).
 */
export function create(name: string): ProfileInfo {
  if (!validName(name)) {
    throw new ProfileError("invalid_name", `invalid profile name ${JSON.stringify(name)}: use 1-64 chars of [a-z0-9-_]`);
  }
  const path = profilePath(name);
  if (existsSync(path)) {
    throw new ProfileError("already_exists", `profile ${JSON.stringify(name)} already exists`);
  }
  const seed = new Uint8Array(randomBytes(64));
  const identity = Identity.fromSeed(seed);
  const createdAt = Math.floor(Date.now() / 1000);
  const record: ProfileFile = {
    version: 1,
    name,
    seed_hex: hexEncode(seed),
    public_key_hex: identity.publicKeyHex,
    created_at: createdAt,
  };
  writePrivate(path, JSON.stringify(record, null, 2));
  return {
    name,
    publicKeyHex: identity.publicKeyHex,
    createdAt,
    active: activeName() === name,
  };
}

/** List all profiles (sorted by name), marking the active one. */
export function list(): ProfileInfo[] {
  const dir = profilesDir();
  const active = activeName();
  let entries: string[];
  try {
    entries = readdirSync(dir);
  } catch (e) {
    if ((e as NodeJS.ErrnoException).code === "ENOENT") return [];
    throw new ProfileError("io", `profile store io error: ${(e as Error).message}`);
  }
  const out: ProfileInfo[] = [];
  for (const entry of entries) {
    if (!entry.endsWith(".json")) continue;
    const name = entry.slice(0, -".json".length);
    try {
      const p = readProfile(name);
      out.push({
        name: p.name,
        publicKeyHex: p.public_key_hex,
        createdAt: p.created_at,
        active: active === name,
      });
    } catch (e) {
      if (e instanceof ProfileError && e.code === "malformed") {
        // List a malformed file by name so the user can see and fix it —
        // silently hiding a broken profile would be worse.
        out.push({ name, publicKeyHex: `<malformed: ${e.message}>`, createdAt: 0, active: false });
        continue;
      }
      throw e;
    }
  }
  out.sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
  return out;
}

/** Set the persistent default profile (`dregg id use <name>`). Must exist. */
export function setActive(name: string): void {
  if (!validName(name)) {
    throw new ProfileError("invalid_name", `invalid profile name ${JSON.stringify(name)}: use 1-64 chars of [a-z0-9-_]`);
  }
  if (!existsSync(profilePath(name))) {
    throw new ProfileError("not_found", `profile ${JSON.stringify(name)} not found`);
  }
  writePrivate(activePath(), name);
}

/** The active profile name: `DREGG_PROFILE` override → `ACTIVE` file. */
export function activeName(): string | undefined {
  const env = process.env[PROFILE_ENV]?.trim();
  if (env) return env;
  try {
    const contents = readFileSync(activePath(), "utf8").trim();
    return contents.length > 0 ? contents : undefined;
  } catch {
    return undefined;
  }
}

/** Load a named profile's identity. */
export function load(name: string): Identity {
  const record = readProfile(name);
  let seed: Uint8Array;
  try {
    seed = hexDecodeExact(record.seed_hex, 64);
  } catch (e) {
    throw new ProfileError("malformed", `profile file for ${JSON.stringify(name)} is malformed: seed_hex: ${(e as Error).message}`);
  }
  return Identity.fromSeed(seed);
}

/**
 * Load the active profile's identity, if any is configured — the automatic
 * pickup point (`DREGG_PROFILE` override → `ACTIVE` file → undefined).
 */
export function loadActive(): Identity | undefined {
  const name = activeName();
  return name === undefined ? undefined : load(name);
}
