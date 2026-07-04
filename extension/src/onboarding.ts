/**
 * Pure onboarding/recovery safety predicates (no chrome / wasm dependencies so
 * they are unit-testable). These enforce the MF-1 guarantee: a wallet is only
 * ever created once the user has chosen a real passphrase AND confirmed the
 * recovery phrase they backed up — there is no path to a key protected solely
 * by an ephemeral session key.
 */

/** Minimum length for a wallet-encryption passphrase. */
export const MIN_WALLET_PASSPHRASE_LEN = 8;

/** Canonical form of a mnemonic for comparison (case/whitespace-insensitive). */
export function normalizeMnemonic(s: string): string {
  return s.trim().toLowerCase().split(/\s+/).filter(Boolean).join(" ");
}

/**
 * True iff the user's re-typed confirmation matches the generated candidate
 * phrase. Used to prove the user actually backed up the recovery phrase before
 * the wallet is created.
 */
export function mnemonicConfirmed(candidate: string, confirm: string): boolean {
  const c = normalizeMnemonic(candidate);
  // Never accept an empty candidate as "confirmed".
  return c.length > 0 && c === normalizeMnemonic(confirm);
}

/**
 * Validate a wallet-encryption passphrase. A passphrase is mandatory — an empty
 * or too-short one would force the orphan-prone internal-key fallback.
 */
export function walletPassphraseOk(p: string): { ok: boolean; error?: string } {
  if (!p || p.length < MIN_WALLET_PASSPHRASE_LEN) {
    return { ok: false, error: `Choose a passphrase of at least ${MIN_WALLET_PASSPHRASE_LEN} characters.` };
  }
  return { ok: true };
}
