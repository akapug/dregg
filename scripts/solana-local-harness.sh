#!/usr/bin/env bash
# solana-local-harness.sh — boot a FREE local solana-test-validator, mint a
# stand-in $DREGG SPL token, lock an amount into a vault, and harvest the real
# artifacts the validator produces into a manifest the `solana_local_e2e` test
# (bridge/tests/solana_local_e2e.rs, gated on SOLANA_LOCAL=1) feeds through the
# trustless bridge verify + mint.
#
# Usage:
#   scripts/solana-local-harness.sh            # boot, harvest, leave manifest, stop validator
#   scripts/solana-local-harness.sh --run-test # also run the gated e2e test
#
# Output: $ARTIFACTS_DIR/manifest.json (default /tmp/dregg-solana-local) + the
# raw account-data side-car files it references.
#
# This is the "are we ready to test, locally, for free?" answer: yes. It needs
# only the Agave/Solana toolchain (solana-test-validator + spl-token + solana
# CLI). If they are not installed it prints the install command and exits 2.
set -euo pipefail

ARTIFACTS_DIR="${ARTIFACTS_DIR:-/tmp/dregg-solana-local}"
LEDGER_DIR="${LEDGER_DIR:-$ARTIFACTS_DIR/ledger}"
MANIFEST="$ARTIFACTS_DIR/manifest.json"
RPC_URL="http://127.0.0.1:8899"
LOCK_AMOUNT="${LOCK_AMOUNT:-250}"        # integer token units (token has 0 decimals)
MINT_AMOUNT="${MINT_AMOUNT:-1000}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Make a locally-installed Agave toolchain visible.
export PATH="$HOME/.local/share/solana/install/active_release/bin:$PATH"

note() { printf '\033[36m[harness]\033[0m %s\n' "$*" >&2; }
fail() { printf '\033[31m[harness] %s\033[0m\n' "$*" >&2; exit 1; }

# ---- 0. tool check ---------------------------------------------------------
missing=()
for t in solana solana-test-validator solana-keygen spl-token jq; do
  command -v "$t" >/dev/null 2>&1 || missing+=("$t")
done
if [ "${#missing[@]}" -ne 0 ]; then
  cat >&2 <<EOF
[harness] missing tools: ${missing[*]}

Install the free Agave/Solana toolchain (test-validator + spl-token + CLI):

  sh -c "\$(curl -sSfL https://release.anza.xyz/stable/install)"
  export PATH="\$HOME/.local/share/solana/install/active_release/bin:\$PATH"

(and \`brew install jq\` if jq is missing). Then re-run this script.
EOF
  exit 2
fi

mkdir -p "$ARTIFACTS_DIR"
rm -rf "$LEDGER_DIR"

# ---- 1. boot the local validator -------------------------------------------
note "booting solana-test-validator (free, private, resettable) ..."
solana-test-validator --reset --quiet --ledger "$LEDGER_DIR" \
  --rpc-port 8899 >"$ARTIFACTS_DIR/validator.log" 2>&1 &
VALIDATOR_PID=$!

cleanup() {
  if kill -0 "$VALIDATOR_PID" 2>/dev/null; then
    note "stopping validator (pid $VALIDATOR_PID)"
    kill "$VALIDATOR_PID" 2>/dev/null || true
    wait "$VALIDATOR_PID" 2>/dev/null || true
  fi
}
trap cleanup EXIT

solana config set --url "$RPC_URL" >/dev/null

note "waiting for the validator to become healthy ..."
ok=0
for _ in $(seq 1 60); do
  if solana cluster-version >/dev/null 2>&1 && \
     [ "$(solana epoch-info --output json 2>/dev/null | jq -r '.absoluteSlot // 0')" != "0" ]; then
    ok=1; break
  fi
  sleep 1
done
[ "$ok" = "1" ] || fail "validator did not become healthy in time (see $ARTIFACTS_DIR/validator.log)"

# ---- 2. fund + mint a stand-in $DREGG SPL token ----------------------------
PAYER="$ARTIFACTS_DIR/payer.json"
[ -f "$PAYER" ] || solana-keygen new --no-bip39-passphrase --force --silent --outfile "$PAYER" >/dev/null
PAYER_PK="$(solana-keygen pubkey "$PAYER")"
solana config set --keypair "$PAYER" >/dev/null
solana airdrop 100 "$PAYER_PK" >/dev/null 2>&1 || solana airdrop 100 "$PAYER_PK" >/dev/null

# `spl-token address` derives the (deterministic) associated token account for an
# owner+mint; create-account only returns a signature.
ata() { spl-token address --verbose --token "$1" --owner "$2" --output json | jq -r '.associatedTokenAddress'; }

note "creating the stand-in \$DREGG SPL token (0 decimals) ..."
MINT=$(spl-token create-token --decimals 0 --fee-payer "$PAYER" --mint-authority "$PAYER_PK" \
        --output json 2>/dev/null | jq -r '.commandOutput.address')
[ -n "$MINT" ] && [ "$MINT" != "null" ] || fail "token mint creation failed"

spl-token create-account "$MINT" --fee-payer "$PAYER" --owner "$PAYER_PK" >/dev/null
SRC_ATA="$(ata "$MINT" "$PAYER_PK")"
spl-token mint "$MINT" "$MINT_AMOUNT" "$SRC_ATA" --fee-payer "$PAYER" --mint-authority "$PAYER" >/dev/null

# ---- 3. lock an amount into a vault account --------------------------------
VAULT_OWNER="$ARTIFACTS_DIR/vault-owner.json"
[ -f "$VAULT_OWNER" ] || solana-keygen new --no-bip39-passphrase --force --silent --outfile "$VAULT_OWNER" >/dev/null
VAULT_OWNER_PK="$(solana-keygen pubkey "$VAULT_OWNER")"
spl-token create-account "$MINT" --owner "$VAULT_OWNER_PK" --fee-payer "$PAYER" >/dev/null
VAULT="$(ata "$MINT" "$VAULT_OWNER_PK")"
note "locking $LOCK_AMOUNT \$DREGG into vault $VAULT ..."
spl-token transfer "$MINT" "$LOCK_AMOUNT" "$VAULT" --fee-payer "$PAYER" --owner "$PAYER" >/dev/null

# ---- 4. locate the bank-state accounts ------------------------------------
VOTE_ACCT=$(solana-keygen pubkey "$LEDGER_DIR/vote-account-keypair.json")
IDENTITY_KP="$LEDGER_DIR/validator-keypair.json"
STAKE_KP="$LEDGER_DIR/stake-account-keypair.json"
[ -f "$STAKE_KP" ] || fail "no bootstrap stake-account-keypair.json in the ledger ($LEDGER_DIR)"
STAKE_ACCT=$(solana-keygen pubkey "$STAKE_KP")
STAKE_HISTORY="SysvarStakeHistory1111111111111111111111111"

EPOCH=$(solana epoch-info --output json | jq -r '.epoch')
SLOT=$(solana epoch-info --output json | jq -r '.absoluteSlot')

# ---- 5. harvest the real artifacts ----------------------------------------
# A helper: dump <pubkey> account data to <file>.bin and emit a JSON object with
# its real header fields + a pointer to the data file.
harvest() {
  local pubkey="$1" label="$2"
  local bin="$ARTIFACTS_DIR/$label.bin"
  solana account "$pubkey" --output-file "$bin" >/dev/null
  local info; info=$(solana account "$pubkey" --output json)
  # The CLI nests the fields under .account.
  jq -n \
    --arg pubkey "$pubkey" \
    --arg data_file "$bin" \
    --argjson lamports "$(jq -r '.account.lamports' <<<"$info")" \
    --arg owner "$(jq -r '.account.owner' <<<"$info")" \
    --argjson executable "$(jq -r '.account.executable' <<<"$info")" \
    --argjson rent_epoch "$(jq -r '.account.rentEpoch | if . > 9223372036854775807 then 0 else . end' <<<"$info")" \
    '{pubkey:$pubkey, lamports:$lamports, owner:$owner, executable:$executable, rent_epoch:$rent_epoch, data_file:$data_file}'
}

note "harvesting real bank-state artifacts ..."
VOTE_JSON=$(harvest "$VOTE_ACCT" vote_account)
STAKE_JSON=$(harvest "$STAKE_ACCT" stake_account)
SH_JSON=$(harvest "$STAKE_HISTORY" stake_history)

VAULT_INFO=$(solana account "$VAULT" --output json)
VAULT_LAMPORTS=$(jq -r '.account.lamports' <<<"$VAULT_INFO")
VAULT_OWNER_PK=$(jq -r '.account.owner' <<<"$VAULT_INFO")

# The bootstrap vote account's on-chain authorized voter is the vote-account
# keypair itself (test-validator default: Vote Authority == vote account). Record
# it so the test signs each vote with the real on-chain authority.
AUTH_KP="$LEDGER_DIR/vote-account-keypair.json"
: "$IDENTITY_KP" # (validator identity; recorded for reference, not the voter)

jq -n \
  --argjson slot "$SLOT" \
  --argjson epoch "$EPOCH" \
  --arg spl_mint "$MINT" \
  --arg vault_account "$VAULT" \
  --argjson locked_amount "$LOCK_AMOUNT" \
  --argjson vault_account_lamports "$VAULT_LAMPORTS" \
  --arg vault_account_owner "$VAULT_OWNER_PK" \
  --argjson vote_account "$VOTE_JSON" \
  --argjson stake_account "$STAKE_JSON" \
  --argjson stake_history "$SH_JSON" \
  --arg authority_keypair_file "$AUTH_KP" \
  --argjson new_rate_activation_epoch null \
  '{slot:$slot, epoch:$epoch, spl_mint:$spl_mint, vault_account:$vault_account,
    locked_amount:$locked_amount, vault_account_lamports:$vault_account_lamports,
    vault_account_owner:$vault_account_owner, vote_account:$vote_account,
    stake_account:$stake_account, stake_history:$stake_history,
    authority_keypair_file:$authority_keypair_file,
    new_rate_activation_epoch:$new_rate_activation_epoch}' > "$MANIFEST"

note "manifest written: $MANIFEST"
note "  slot=$SLOT epoch=$EPOCH mint=$MINT vault=$VAULT locked=$LOCK_AMOUNT"

# ---- 6. optionally run the gated e2e test ----------------------------------
if [ "${1:-}" = "--run-test" ]; then
  note "running the gated e2e test against the harvested artifacts ..."
  ( cd "$REPO_ROOT" && \
    SOLANA_LOCAL=1 DREGG_SOLANA_ARTIFACTS="$MANIFEST" \
    cargo test -p dregg-bridge --test solana_local_e2e -- --nocapture )
else
  cat >&2 <<EOF
[harness] to run the e2e test against these artifacts:

  SOLANA_LOCAL=1 DREGG_SOLANA_ARTIFACTS="$MANIFEST" \\
    cargo test -p dregg-bridge --test solana_local_e2e -- --nocapture
EOF
fi
