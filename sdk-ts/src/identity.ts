/**
 * `Identity` — the cipherclerk: who is acting.
 *
 * The first half of the SDK's authorization-first shape:
 *
 * ```text
 * Identity → .turn() → typed verb builders → .sign() → .submit() → Receipt
 * ```
 *
 * Key derivation is the SAME as the Rust SDK / CLI / extension:
 * `blake3::derive_key("dregg/0", seed64)` → 32-byte Ed25519 seed → keypair
 * (sdk/src/mnemonic.rs `derive_keypair`). All implementations pin the same
 * golden vector (seed `00..3f` → pubkey `335840a9…8b9a`), so any drift fails
 * everywhere at once.
 */

import { blake3DeriveKey } from "./internal/blake3";
import { ed25519PublicKey, ed25519Sign } from "./internal/ed25519";
import { exactBytes, hexEncode } from "./internal/bytes";
import type { Action, CellId, Turn } from "./internal/wire";
import { actionSigningMessage, deriveCellId, encodeSignedTurn, turnHash } from "./internal/wire";

/** The main-agent derivation path. Sub-agents use `dregg/1`, `dregg/2`, … */
export const MAIN_IDENTITY_PATH = "dregg/0";

/**
 * A local signing identity (Ed25519). Construct from a 64-byte master seed
 * (profile store shape), a raw 32-byte Ed25519 seed, or a named profile
 * (see `profiles.ts`).
 */
export class Identity {
  /** The 32-byte Ed25519 seed (key material — never logged). */
  private readonly seed: Uint8Array;
  /** The 32-byte Ed25519 public key. */
  readonly publicKey: Uint8Array;

  private constructor(seed32: Uint8Array) {
    this.seed = exactBytes(seed32, 32, "ed25519 seed");
    this.publicKey = ed25519PublicKey(this.seed);
  }

  /**
   * Derive the main identity from a 64-byte master seed at path `dregg/0`
   * (the profile-store derivation — mirrors `AgentCipherclerk::from_seed`).
   */
  static fromSeed(seed64: Uint8Array, path: string = MAIN_IDENTITY_PATH): Identity {
    exactBytes(seed64, 64, "master seed");
    return new Identity(blake3DeriveKey(path, seed64));
  }

  /** Wrap a raw 32-byte Ed25519 seed directly (no path derivation). */
  static fromKeyBytes(seed32: Uint8Array): Identity {
    return new Identity(seed32);
  }

  /** A fresh random identity (OS randomness). */
  static generate(): Identity {
    const seed = new Uint8Array(64);
    globalThis.crypto.getRandomValues(seed);
    return Identity.fromSeed(seed);
  }

  /** Hex Ed25519 public key (the profile store's `public_key_hex`). */
  get publicKeyHex(): string {
    return hexEncode(this.publicKey);
  }

  /**
   * This identity's default agent cell:
   * `CellId::derive_raw(publicKey, blake3("default"))` — the cell the node
   * requires as `turn.agent` for envelope-signed submissions.
   */
  cellId(): CellId {
    return deriveCellId(this.publicKey);
  }

  /** Hex form of [`cellId`]. */
  cellIdHex(): string {
    return hexEncode(this.cellId());
  }

  /** Sign arbitrary bytes (Ed25519, deterministic). */
  signBytes(message: Uint8Array): Uint8Array {
    return ed25519Sign(this.seed, message);
  }

  /**
   * Sign an action over the canonical federation-bound signing message
   * (`dregg-action-sig-v2`), replacing its authorization with a real
   * `Signature` — the ONLY way an action leaves the authorized flow.
   */
  signAction(action: Action, federationId: Uint8Array): Action {
    const message = actionSigningMessage(action, federationId);
    const sig = this.signBytes(message);
    return {
      ...action,
      authorization: { kind: "signature", r: sig.slice(0, 32), s: sig.slice(32, 64) },
    };
  }

  /**
   * Sign a turn's canonical `Turn::hash` (v3) and wrap it in the postcard
   * `SignedTurn` envelope the node's `/api/turns/submit-signed` ingress
   * verifies (signature over the hash; `turn.agent` must be this identity's
   * default cell).
   */
  signTurnEnvelope(turn: Turn): Uint8Array {
    const hash = turnHash(turn);
    const sig = this.signBytes(hash);
    return encodeSignedTurn(turn, sig, this.publicKey);
  }
}
