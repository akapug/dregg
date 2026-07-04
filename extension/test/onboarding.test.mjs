// MF-1: the onboarding/recovery safety gate. These enforce that a wallet is
// only created once the user has confirmed the recovery-phrase backup AND set a
// real passphrase — there is no path to a key protected only by an ephemeral
// session key.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  normalizeMnemonic,
  mnemonicConfirmed,
  walletPassphraseOk,
  MIN_WALLET_PASSPHRASE_LEN,
} from './.build/onboarding.mjs';

const PHRASE =
  'abandon ability able about above absent absorb abstract absurd abuse access accident ' +
  'account accuse achieve acid acoustic acquire across act action actor actress actual';

test('normalizeMnemonic is case/whitespace-insensitive', () => {
  assert.equal(normalizeMnemonic('  Foo   BAR\tbaz \n'), 'foo bar baz');
});

test('confirmation must match the candidate exactly (modulo case/space)', () => {
  assert.equal(mnemonicConfirmed(PHRASE, PHRASE), true);
  assert.equal(mnemonicConfirmed(PHRASE, '  ' + PHRASE.toUpperCase() + '  '), true);
});

test('a wrong or partial confirmation is rejected (forces real backup)', () => {
  assert.equal(mnemonicConfirmed(PHRASE, PHRASE.replace('abandon', 'zebra')), false);
  assert.equal(mnemonicConfirmed(PHRASE, 'abandon ability able'), false);
  assert.equal(mnemonicConfirmed(PHRASE, ''), false);
});

test('an empty candidate is never "confirmed"', () => {
  assert.equal(mnemonicConfirmed('', ''), false);
  assert.equal(mnemonicConfirmed('   ', 'anything'), false);
});

test('wallet passphrase is mandatory and length-gated (no orphan-key path)', () => {
  assert.equal(walletPassphraseOk('').ok, false);
  assert.equal(walletPassphraseOk('short').ok, false);
  assert.equal(walletPassphraseOk('x'.repeat(MIN_WALLET_PASSPHRASE_LEN - 1)).ok, false);
  assert.equal(walletPassphraseOk('x'.repeat(MIN_WALLET_PASSPHRASE_LEN)).ok, true);
  assert.equal(walletPassphraseOk('a-strong-passphrase').ok, true);
});
