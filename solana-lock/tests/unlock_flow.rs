//! End-to-end test of the M-of-N threshold Unlock path over `solana-program-test`
//! (native BanksClient, no SBF). It exercises the REAL trust boundary:
//!
//!   * the on-chain program reconstructs the canonical unlock message hash and
//!     verifies `>= M` ed25519 signatures from DISTINCT configured oracle keys,
//!     carried in ed25519 native-program (precompile) instructions and read back
//!     through the instructions sysvar;
//!   * every fail-closed case (empty sigs / M-1 / duplicate signer / stranger
//!     signer / tampered payload / replay) is refused AND the vault does not pay out.
//!
//! These tests run by DEFAULT on `cargo test` — no feature gate hides them.

use dregg_solana_lock::attestation::unlock_message_hash;
use dregg_solana_lock::instruction::LockInstruction;
use dregg_solana_lock::state::VaultConfig;
use dregg_solana_lock::{
    process_instruction, SEED_CONFIG, SEED_LOCK, SEED_REDEEM, SEED_VAULT, SEED_VAULT_AUTHORITY,
};

use solana_program_test::{processor, BanksClient, ProgramTest};
use solana_sdk::{
    account::Account,
    instruction::{AccountMeta, Instruction, InstructionError},
    program_pack::Pack,
    pubkey::Pubkey,
    signature::{Keypair, Signer},
    system_program,
    transaction::{Transaction, TransactionError},
};

fn program_id() -> Pubkey {
    Pubkey::new_from_array([9u8; 32])
}

fn instructions_sysvar_id() -> Pubkey {
    solana_program::sysvar::instructions::id()
}

/// Build a self-contained ed25519 native-program instruction asserting `kp` signed
/// the 32-byte `message`. The runtime precompile verifies it before our program runs.
fn ed25519_ix(kp: &Keypair, message: &[u8; 32]) -> Instruction {
    let sig = kp.sign_message(message);
    let sig_bytes: [u8; 64] = sig.as_ref().try_into().expect("64-byte signature");
    let pk: [u8; 32] = kp.pubkey().to_bytes();
    solana_ed25519_program::new_ed25519_instruction_with_signature(message, &sig_bytes, &pk)
}

/// State handed back from `setup`: a vault with `locked` $DREGG and a 2-of-3 oracle
/// set, plus a fresh recipient token account.
struct Env {
    banks: BanksClient,
    payer: Keypair,
    program_id: Pubkey,
    config_pda: Pubkey,
    vault_pda: Pubkey,
    vault_auth_pda: Pubkey,
    mint: Pubkey,
    recipient_token: Pubkey,
    oracles: Vec<Keypair>, // the 3 configured oracle keypairs
    threshold: u8,         // M = 2
}

async fn setup(locked: u64) -> Env {
    let program_id = program_id();
    let mut pt = ProgramTest::new(
        "dregg_solana_lock",
        program_id,
        processor!(process_instruction),
    );

    let mint = Keypair::new();
    let mint_authority = Keypair::new();
    let user = Keypair::new();
    let user_token = Keypair::new();
    let recipient_owner = Keypair::new();
    let recipient_token = Keypair::new();

    // 2-of-3 oracle set.
    let oracles: Vec<Keypair> = (0..3).map(|_| Keypair::new()).collect();
    let threshold: u8 = 2;

    let rent = solana_sdk::rent::Rent::default();

    // mint account
    {
        let mut mint_data = vec![0u8; spl_token::state::Mint::LEN];
        let mint_state = spl_token::state::Mint {
            mint_authority: solana_program::program_option::COption::Some(mint_authority.pubkey()),
            supply: 1_000_000,
            decimals: 6,
            is_initialized: true,
            freeze_authority: solana_program::program_option::COption::None,
        };
        spl_token::state::Mint::pack(mint_state, &mut mint_data).unwrap();
        pt.add_account(
            mint.pubkey(),
            Account {
                lamports: rent.minimum_balance(mint_data.len()),
                data: mint_data,
                owner: spl_token::id(),
                executable: false,
                rent_epoch: 0,
            },
        );
    }
    // user token account holding balance to lock
    {
        let mut acct_data = vec![0u8; spl_token::state::Account::LEN];
        let acct_state = spl_token::state::Account {
            mint: mint.pubkey(),
            owner: user.pubkey(),
            amount: 1_000_000,
            delegate: solana_program::program_option::COption::None,
            state: spl_token::state::AccountState::Initialized,
            is_native: solana_program::program_option::COption::None,
            delegated_amount: 0,
            close_authority: solana_program::program_option::COption::None,
        };
        spl_token::state::Account::pack(acct_state, &mut acct_data).unwrap();
        pt.add_account(
            user_token.pubkey(),
            Account {
                lamports: rent.minimum_balance(acct_data.len()),
                data: acct_data,
                owner: spl_token::id(),
                executable: false,
                rent_epoch: 0,
            },
        );
    }
    // recipient token account (dest of the unlock), initialized, empty.
    {
        let mut acct_data = vec![0u8; spl_token::state::Account::LEN];
        let acct_state = spl_token::state::Account {
            mint: mint.pubkey(),
            owner: recipient_owner.pubkey(),
            amount: 0,
            delegate: solana_program::program_option::COption::None,
            state: spl_token::state::AccountState::Initialized,
            is_native: solana_program::program_option::COption::None,
            delegated_amount: 0,
            close_authority: solana_program::program_option::COption::None,
        };
        spl_token::state::Account::pack(acct_state, &mut acct_data).unwrap();
        pt.add_account(
            recipient_token.pubkey(),
            Account {
                lamports: rent.minimum_balance(acct_data.len()),
                data: acct_data,
                owner: spl_token::id(),
                executable: false,
                rent_epoch: 0,
            },
        );
    }

    let (mut banks, payer, recent_blockhash) = pt.start().await;

    let (config_pda, _) = Pubkey::find_program_address(&[SEED_CONFIG], &program_id);
    let (vault_pda, _) =
        Pubkey::find_program_address(&[SEED_VAULT, config_pda.as_ref()], &program_id);
    let (vault_auth_pda, _) =
        Pubkey::find_program_address(&[SEED_VAULT_AUTHORITY, config_pda.as_ref()], &program_id);

    // --- InitVault with the 2-of-3 oracle set ---
    let oracle_keys: Vec<[u8; 32]> = oracles.iter().map(|k| k.pubkey().to_bytes()).collect();
    let init_ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(payer.pubkey(), true),
            AccountMeta::new(config_pda, false),
            AccountMeta::new_readonly(mint.pubkey(), false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(vault_auth_pda, false),
            AccountMeta::new_readonly(spl_token::id(), false),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: LockInstruction::InitVault {
            oracle_threshold: threshold,
            oracle_keys,
        }
        .pack(),
    };
    let mut tx = Transaction::new_with_payer(&[init_ix], Some(&payer.pubkey()));
    tx.sign(&[&payer], recent_blockhash);
    banks.process_transaction(tx).await.expect("InitVault");

    // --- Lock `locked` into the vault so there is something to release ---
    let nonce = 0u64;
    let (record_pda, _) = Pubkey::find_program_address(
        &[SEED_LOCK, config_pda.as_ref(), &nonce.to_le_bytes()],
        &program_id,
    );
    let recent_blockhash = banks.get_latest_blockhash().await.unwrap();
    let lock_ix = Instruction {
        program_id,
        accounts: vec![
            AccountMeta::new(payer.pubkey(), true),
            AccountMeta::new(config_pda, false),
            AccountMeta::new(user_token.pubkey(), false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(user.pubkey(), true),
            AccountMeta::new(record_pda, false),
            AccountMeta::new_readonly(spl_token::id(), false),
            AccountMeta::new_readonly(system_program::id(), false),
        ],
        data: LockInstruction::Lock {
            amount: locked,
            dregg_recipient: [0xEEu8; 32],
        }
        .pack(),
    };
    let mut tx = Transaction::new_with_payer(&[lock_ix], Some(&payer.pubkey()));
    tx.sign(&[&payer, &user], recent_blockhash);
    banks.process_transaction(tx).await.expect("Lock");

    Env {
        banks,
        payer,
        program_id,
        config_pda,
        vault_pda,
        vault_auth_pda,
        mint: mint.pubkey(),
        recipient_token: recipient_token.pubkey(),
        oracles,
        threshold,
    }
}

impl Env {
    fn receipt_pda(&self, redeem_id: &[u8; 32]) -> Pubkey {
        Pubkey::find_program_address(
            &[SEED_REDEEM, self.config_pda.as_ref(), redeem_id],
            &self.program_id,
        )
        .0
    }

    /// The canonical hash the oracle signs for `(amount, recipient=this vault's
    /// recipient token account, redeem_id)`.
    fn hash_for(&self, amount: u64, redeem_id: &[u8; 32]) -> [u8; 32] {
        unlock_message_hash(
            &self.mint.to_bytes(),
            amount,
            &self.recipient_token.to_bytes(),
            redeem_id,
        )
    }

    fn unlock_ix(&self, amount: u64, redeem_id: [u8; 32]) -> Instruction {
        Instruction {
            program_id: self.program_id,
            accounts: vec![
                AccountMeta::new_readonly(self.config_pda, false),
                AccountMeta::new(self.vault_pda, false),
                AccountMeta::new_readonly(self.vault_auth_pda, false),
                AccountMeta::new(self.recipient_token, false),
                AccountMeta::new(self.receipt_pda(&redeem_id), false),
                AccountMeta::new(self.payer.pubkey(), true),
                AccountMeta::new_readonly(spl_token::id(), false),
                AccountMeta::new_readonly(system_program::id(), false),
                AccountMeta::new_readonly(instructions_sysvar_id(), false),
            ],
            data: LockInstruction::Unlock { amount, redeem_id }.pack(),
        }
    }

    /// Assemble `ed_ixs` followed by the unlock instruction, sign with the payer,
    /// and submit. Returns the BanksClient result.
    async fn try_unlock(
        &mut self,
        ed_ixs: Vec<Instruction>,
        amount: u64,
        redeem_id: [u8; 32],
    ) -> Result<(), solana_program_test::BanksClientError> {
        let mut ixs = ed_ixs;
        ixs.push(self.unlock_ix(amount, redeem_id));
        let bh = self.banks.get_latest_blockhash().await.unwrap();
        let mut tx = Transaction::new_with_payer(&ixs, Some(&self.payer.pubkey()));
        tx.sign(&[&self.payer], bh);
        self.banks.process_transaction(tx).await
    }

    async fn vault_amount(&mut self) -> u64 {
        let acct = self
            .banks
            .get_account(self.vault_pda)
            .await
            .unwrap()
            .unwrap();
        spl_token::state::Account::unpack(&acct.data)
            .unwrap()
            .amount
    }

    async fn recipient_amount(&mut self) -> u64 {
        let acct = self
            .banks
            .get_account(self.recipient_token)
            .await
            .unwrap()
            .unwrap();
        spl_token::state::Account::unpack(&acct.data)
            .unwrap()
            .amount
    }
}

/// The custom error code the on-chain program returned, if any (bottom-most
/// instruction error in the transaction).
fn custom_code(err: &solana_program_test::BanksClientError) -> Option<u32> {
    match err {
        solana_program_test::BanksClientError::TransactionError(
            TransactionError::InstructionError(_, InstructionError::Custom(c)),
        ) => Some(*c),
        _ => None,
    }
}

// LockError discriminants (mirrors src/error.rs).
const ERR_ALREADY_REDEEMED: u32 = 7;
const ERR_THRESHOLD_NOT_MET: u32 = 11;

/// The vault config was written as a 2-of-3 oracle set (sanity: the new layout
/// round-trips on chain and NO single `unlock_authority` remains).
#[tokio::test]
async fn init_writes_oracle_set() {
    let mut env = setup(250_000).await;
    let cfg_acct = env
        .banks
        .get_account(env.config_pda)
        .await
        .unwrap()
        .unwrap();
    assert_eq!(cfg_acct.owner, env.program_id);
    let cfg = VaultConfig::unpack(&cfg_acct.data).unwrap();
    assert_eq!(cfg.oracle_threshold, 2);
    assert_eq!(cfg.oracle_count, 3);
    for o in &env.oracles {
        assert!(cfg.contains_oracle(&o.pubkey().to_bytes()));
    }
    assert_eq!(env.vault_amount().await, 250_000);
}

/// A valid 2-of-3 attestation releases the funds.
#[tokio::test]
async fn valid_threshold_unlocks() {
    let mut env = setup(250_000).await;
    let amount = 100_000u64;
    let redeem_id = [0x01u8; 32];
    let hash = env.hash_for(amount, &redeem_id);

    let ed = vec![
        ed25519_ix(&env.oracles[0], &hash),
        ed25519_ix(&env.oracles[2], &hash),
    ];
    env.try_unlock(ed, amount, redeem_id)
        .await
        .expect("2-of-3 valid attestation unlocks");

    assert_eq!(env.vault_amount().await, 150_000, "vault paid out `amount`");
    assert_eq!(
        env.recipient_amount().await,
        100_000,
        "recipient received it"
    );
    // the receipt PDA now exists (consumed).
    let receipt = env
        .banks
        .get_account(env.receipt_pda(&redeem_id))
        .await
        .unwrap();
    assert!(receipt.is_some(), "redeem receipt was created");
}

/// NOMAD-LAW: an unlock carrying ZERO oracle signatures never authorizes a payout.
#[tokio::test]
async fn empty_signature_set_refused() {
    let mut env = setup(250_000).await;
    let amount = 100_000u64;
    let redeem_id = [0x02u8; 32];

    let err = env
        .try_unlock(vec![], amount, redeem_id)
        .await
        .expect_err("zero signatures must be refused");
    assert_eq!(custom_code(&err), Some(ERR_THRESHOLD_NOT_MET));
    assert_eq!(env.vault_amount().await, 250_000, "vault did not pay out");
    assert_eq!(env.recipient_amount().await, 0);
}

/// M-1 signatures (one, threshold is two) is refused.
#[tokio::test]
async fn m_minus_one_refused() {
    let mut env = setup(250_000).await;
    let amount = 100_000u64;
    let redeem_id = [0x03u8; 32];
    let hash = env.hash_for(amount, &redeem_id);

    let ed = vec![ed25519_ix(&env.oracles[1], &hash)];
    let err = env
        .try_unlock(ed, amount, redeem_id)
        .await
        .expect_err("1-of-3 (< M) refused");
    assert_eq!(custom_code(&err), Some(ERR_THRESHOLD_NOT_MET));
    assert_eq!(env.vault_amount().await, 250_000);
}

/// The SAME oracle signing twice counts once — a duplicate signer cannot reach M.
#[tokio::test]
async fn duplicate_signer_refused() {
    let mut env = setup(250_000).await;
    let amount = 100_000u64;
    let redeem_id = [0x04u8; 32];
    let hash = env.hash_for(amount, &redeem_id);

    let ed = vec![
        ed25519_ix(&env.oracles[0], &hash),
        ed25519_ix(&env.oracles[0], &hash), // same key again
    ];
    let err = env
        .try_unlock(ed, amount, redeem_id)
        .await
        .expect_err("duplicate signer must not reach threshold");
    assert_eq!(custom_code(&err), Some(ERR_THRESHOLD_NOT_MET));
    assert_eq!(env.vault_amount().await, 250_000);
}

/// A signature from a non-configured (stranger) key does not count toward M.
#[tokio::test]
async fn stranger_signer_refused() {
    let mut env = setup(250_000).await;
    let amount = 100_000u64;
    let redeem_id = [0x05u8; 32];
    let hash = env.hash_for(amount, &redeem_id);

    let stranger = Keypair::new(); // NOT in the oracle set
    let ed = vec![
        ed25519_ix(&env.oracles[0], &hash), // 1 real oracle
        ed25519_ix(&stranger, &hash),       // + 1 stranger => only 1 distinct oracle
    ];
    let err = env
        .try_unlock(ed, amount, redeem_id)
        .await
        .expect_err("a stranger signature does not count");
    assert_eq!(custom_code(&err), Some(ERR_THRESHOLD_NOT_MET));
    assert_eq!(env.vault_amount().await, 250_000);
}

/// A valid-but-for-the-WRONG-payload attestation is refused: two real oracles sign
/// the hash for a different amount than the unlock requests, so the reconstructed
/// hash does not match and neither signature counts.
#[tokio::test]
async fn tampered_payload_refused() {
    let mut env = setup(250_000).await;
    let requested = 100_000u64;
    let signed_amount = 999_999u64; // oracles signed a DIFFERENT amount
    let redeem_id = [0x06u8; 32];
    let wrong_hash = env.hash_for(signed_amount, &redeem_id);

    let ed = vec![
        ed25519_ix(&env.oracles[0], &wrong_hash),
        ed25519_ix(&env.oracles[1], &wrong_hash),
    ];
    let err = env
        .try_unlock(ed, requested, redeem_id)
        .await
        .expect_err("sigs over a different payload must not authorize this unlock");
    assert_eq!(custom_code(&err), Some(ERR_THRESHOLD_NOT_MET));
    assert_eq!(env.vault_amount().await, 250_000, "vault did not pay out");
    assert_eq!(env.recipient_amount().await, 0);
}

/// Replay: after a successful unlock, re-submitting the same `redeem_id` (even with
/// fresh valid signatures) is refused by the redeem-receipt PDA, and the vault does
/// not pay twice.
#[tokio::test]
async fn replay_refused() {
    let mut env = setup(250_000).await;
    let amount = 100_000u64;
    let redeem_id = [0x07u8; 32];
    let hash = env.hash_for(amount, &redeem_id);

    // first: succeeds.
    let ed = vec![
        ed25519_ix(&env.oracles[0], &hash),
        ed25519_ix(&env.oracles[1], &hash),
    ];
    env.try_unlock(ed, amount, redeem_id)
        .await
        .expect("first unlock");
    assert_eq!(env.vault_amount().await, 150_000);

    // second: same redeem_id, freshly valid signatures — refused as already redeemed.
    let ed2 = vec![
        ed25519_ix(&env.oracles[0], &hash),
        ed25519_ix(&env.oracles[2], &hash),
    ];
    let err = env
        .try_unlock(ed2, amount, redeem_id)
        .await
        .expect_err("replay must be refused");
    assert_eq!(custom_code(&err), Some(ERR_ALREADY_REDEEMED));
    assert_eq!(env.vault_amount().await, 150_000, "vault did not pay twice");
    assert_eq!(env.recipient_amount().await, 100_000);
}
