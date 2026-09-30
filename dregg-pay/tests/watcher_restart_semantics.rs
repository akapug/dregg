//! **RESTART SEMANTICS for the payment watcher** (`docs/reference/RESTART-SEMANTICS.md`).
//!
//! A process restart is not an edge case — it is the state the watcher is in every
//! single time it starts, and an adversary gets to choose it by waiting for a deploy.
//! This file drives the ONE decision that matters on the money path:
//!
//! > after the watcher process is replaced, does the SAME on-chain payment credit twice?
//!
//! The restart is modelled honestly: the watcher is **dropped** and a brand-new one is
//! constructed from the same config over the same chain state. Nothing in RAM survives;
//! everything on the chain does. The assertion is on the **`CreditLedger` balance** — the
//! decision the guard makes — not on what the watcher returned.
//!
//! # What this file caught
//!
//! Against the pre-fix `SolanaWatcher` (balance total + the RPC's *current* slot as the
//! reference) this test failed with `balance after the restart poll was 10` on a single
//! 500-unit payment worth 5 runs. The reference `sol:{addr}:{slot}:{amount}` was fresh
//! on every poll because the slot advances every ~400ms, so the durable `pay_processed`
//! table could never recognise a repeat, and the in-RAM `last_seen` map that was the
//! only real guard is empty at boot. **Every restart re-credited every standing
//! balance.** The repair was the KEY, not the store: a key the chain owns.
//!
//! The key is `soltx:{signature}:{address}:{mint}`, not `soltx:{signature}`: one
//! transaction can pay several deposit accounts, and keyed on the signature alone the
//! second account's credit was refused as already processed and lost
//! (`one_transaction_paying_two_deposit_addresses_credits_both`).

use std::sync::{Arc, Mutex};

use dregg_pay::{
    CreditLedger, CreditOutcome, DepositAddress, InMemoryStore, ObservedTransfer, PayConfig,
    PaymentRef, SPL_TOKEN_PROGRAM_ID, SignatureWatcher, TransferFetcher, UserId, WatchError,
    Watcher, signature_payment_ref,
};

/// Atomic units per run credit — 500 units is exactly 5 runs.
const PRICE_PER_RUN: u64 = 100;
const MINT: [u8; 32] = [9u8; 32];
const WALLET: [u8; 32] = [1u8; 32];

fn config() -> PayConfig {
    PayConfig::devnet_mock(
        *b"seedseedseedseedseedseedseedseed",
        MINT,
        DepositAddress([2u8; 32]),
        PRICE_PER_RUN,
    )
}

/// The CHAIN — the thing that survives the process. It holds the transfer history and
/// a slot clock that, like a real cluster, ADVANCES on every read. The advancing clock
/// is deliberate: it is precisely what made the old balance-total reference fresh on
/// every poll, so a fix that quietly reintroduced a slot into the key would be caught
/// here rather than in production.
struct Chain {
    transfers: Mutex<Vec<(String, u64)>>,
    slot: Mutex<u64>,
}

impl Chain {
    fn with_transfer(signature: &str, amount: u64) -> Arc<Self> {
        Arc::new(Chain {
            transfers: Mutex::new(vec![(signature.to_string(), amount)]),
            slot: Mutex::new(100),
        })
    }

    /// A new deposit lands on-chain.
    fn land(&self, signature: &str, amount: u64) {
        self.transfers
            .lock()
            .unwrap()
            .push((signature.to_string(), amount));
    }
}

/// A signature-history transport over the shared chain. Constructing a second one is
/// what "the new process reconnects to the same RPC" means.
struct ChainTransfers {
    chain: Arc<Chain>,
}

impl TransferFetcher for ChainTransfers {
    fn fetch_transfers(
        &self,
        _owner: &DepositAddress,
        _mint: &[u8; 32],
        _token_program: &[u8; 32],
        limit: usize,
    ) -> Result<Vec<ObservedTransfer>, WatchError> {
        // A real RPC reports its CURRENT slot, which advances ~every 400ms.
        let mut slot = self.chain.slot.lock().unwrap();
        *slot += 1;
        let now = *slot;
        Ok(self
            .chain
            .transfers
            .lock()
            .unwrap()
            .iter()
            .rev()
            .take(limit)
            .map(|(signature, amount)| ObservedTransfer {
                signature: signature.clone(),
                slot: now,
                amount: *amount,
                mint: MINT,
                token_owner: WALLET,
                token_program: SPL_TOKEN_PROGRAM_ID,
            })
            .collect())
    }
}

/// Build the watcher a fresh process would build: same config, same RPC, nothing
/// carried over. Calling this twice IS the restart.
fn boot(cfg: &PayConfig, chain: &Arc<Chain>) -> SignatureWatcher<ChainTransfers> {
    SignatureWatcher::new(
        cfg,
        ChainTransfers {
            chain: Arc::clone(chain),
        },
    )
    .unwrap()
}

/// **THE RESTART TEST.** One 500-unit payment sits on the chain. A watcher observes it
/// and the ledger credits 5 runs. The watcher is then DROPPED and rebuilt from the same
/// config over the same chain — a restart — and polls the same unchanged chain state.
///
/// The balance must still be 5. Anything else is the same money paid for twice.
#[test]
fn restart_does_not_double_credit_the_same_payment() {
    let chain = Chain::with_transfer("PaymentSignatureOne", 500);
    let cfg = config();
    let ledger = CreditLedger::new(InMemoryStore::new(), PRICE_PER_RUN);
    let alice = UserId::from("alice");
    let deposit = DepositAddress(WALLET);

    // ── process 1 ────────────────────────────────────────────────────────────
    {
        let watcher = boot(&cfg, &chain);
        for payment in watcher.poll(&alice, &deposit).unwrap() {
            ledger.credit(&payment);
        }
    } // ← the watcher is dropped. THIS IS THE RESTART.
    assert_eq!(
        ledger.balance(&alice),
        5,
        "the 500-unit payment credits 5 runs once"
    );

    // ── process 2: same config, same chain, nothing new landed ───────────────
    let watcher = boot(&cfg, &chain);
    let outcomes: Vec<CreditOutcome> = watcher
        .poll(&alice, &deposit)
        .unwrap()
        .iter()
        .map(|p| ledger.credit(p))
        .collect();

    assert_eq!(
        ledger.balance(&alice),
        5,
        "a RESTART must not re-credit a payment the ledger already processed; \
         balance after the restart poll was {} (outcomes: {outcomes:?})",
        ledger.balance(&alice)
    );
    assert!(
        outcomes
            .iter()
            .all(|o| matches!(o, CreditOutcome::AlreadyCredited)),
        "the durable ledger — not the watcher — is what recognises the repeat: {outcomes:?}"
    );
}

/// **The restart must not become a deaf watcher either.** A REFUSE-shaped fix (never
/// re-report anything after a restart) would pass the test above and silently drop real
/// money. So: restart, and then land a genuinely new payment. It must credit.
#[test]
fn restart_still_credits_a_genuinely_new_payment() {
    let chain = Chain::with_transfer("PaymentSignatureOne", 500);
    let cfg = config();
    let ledger = CreditLedger::new(InMemoryStore::new(), PRICE_PER_RUN);
    let alice = UserId::from("alice");
    let deposit = DepositAddress(WALLET);

    {
        let watcher = boot(&cfg, &chain);
        for payment in watcher.poll(&alice, &deposit).unwrap() {
            ledger.credit(&payment);
        }
    }
    assert_eq!(ledger.balance(&alice), 5);

    // A second, genuinely different payment lands while the process is down.
    chain.land("PaymentSignatureTwo", 300);

    let watcher = boot(&cfg, &chain);
    for payment in watcher.poll(&alice, &deposit).unwrap() {
        ledger.credit(&payment);
    }
    assert_eq!(
        ledger.balance(&alice),
        8,
        "5 already-credited runs + 3 new ones — a restart forgets nothing and \
         re-credits nothing"
    );
}

/// **THE SWEEP TRAP.** This is the bug that persisting `last_seen` would have made
/// permanent, and it is why the key had to change rather than the store.
///
/// Balance 500 is credited; an operator sweep empties the account; a new 500-unit
/// deposit lands. Under a balance-total key that second deposit is invisible
/// (`amount == prev`) and the credit is LOST — today a restart is the only thing that
/// heals it, which is why persisting the cursor would have kept the disease and removed
/// the accidental cure. Under a transaction-signature key the second deposit is simply
/// a different transaction, so it credits, and re-polling still does not double-credit
/// the first.
#[test]
fn a_post_sweep_redeposit_at_the_same_total_still_credits() {
    let chain = Chain::with_transfer("DepositBeforeSweep", 500);
    let cfg = config();
    let ledger = CreditLedger::new(InMemoryStore::new(), PRICE_PER_RUN);
    let alice = UserId::from("alice");
    let deposit = DepositAddress(WALLET);

    let watcher = boot(&cfg, &chain);
    for payment in watcher.poll(&alice, &deposit).unwrap() {
        ledger.credit(&payment);
    }
    assert_eq!(ledger.balance(&alice), 5);

    // …the sweeper moves the whole balance to the treasury, and the user deposits
    // exactly the same amount again. The account total is 500 both before and after.
    chain.land("DepositAfterSweep", 500);

    let watcher = boot(&cfg, &chain);
    let outcomes: Vec<CreditOutcome> = watcher
        .poll(&alice, &deposit)
        .unwrap()
        .iter()
        .map(|p| ledger.credit(p))
        .collect();
    assert_eq!(
        ledger.balance(&alice),
        10,
        "a re-deposit at the old total is NEW money and must credit: {outcomes:?}"
    );
    assert_eq!(
        outcomes
            .iter()
            .filter(|o| matches!(o, CreditOutcome::Credited { .. }))
            .count(),
        1,
        "exactly one of the two observed transfers was new: {outcomes:?}"
    );
}

/// The reference the ledger stores is the CHAIN's key, verbatim — signature, credited
/// deposit address, mint; no slot, no counter, no total. Pinned as a literal shape
/// because this string is the durable primary key in `pay_processed`: changing its shape
/// re-opens every already credited payment for a second credit (a rebuild, with the
/// store re-genesised — never a silent in-place change).
#[test]
fn the_stored_reference_is_the_transaction_signature() {
    let chain = Chain::with_transfer("PaymentSignatureOne", 500);
    let cfg = config();
    let watcher = boot(&cfg, &chain);
    let payments = watcher
        .poll(&UserId::from("alice"), &DepositAddress(WALLET))
        .unwrap();
    assert_eq!(
        payments[0].reference,
        PaymentRef(format!(
            "soltx:PaymentSignatureOne:{}:{}",
            bs58::encode(WALLET).into_string(),
            bs58::encode(MINT).into_string()
        ))
    );
}

/// ONE transaction, post − pre deltas on TWO watched deposit accounts (alice's and
/// bob's) — the transaction anyone can build: 1 unit to a victim, 1 unit to themselves.
/// A transport that reports the transfers of exactly the polled owner.
struct OneTxTwoAccounts;

impl TransferFetcher for OneTxTwoAccounts {
    fn fetch_transfers(
        &self,
        owner: &DepositAddress,
        mint: &[u8; 32],
        token_program: &[u8; 32],
        _limit: usize,
    ) -> Result<Vec<ObservedTransfer>, WatchError> {
        let delta = match owner.to_bytes() {
            ALICE_WALLET => 500,
            BOB_WALLET => 300,
            _ => return Ok(Vec::new()),
        };
        Ok(vec![ObservedTransfer {
            signature: "OneTxPaysTwoUsers".to_string(),
            slot: 7,
            amount: delta,
            mint: *mint,
            token_owner: owner.to_bytes(),
            token_program: *token_program,
        }])
    }
}

const ALICE_WALLET: [u8; 32] = [0xA1u8; 32];
const BOB_WALLET: [u8; 32] = [0xB0u8; 32];

/// **Two credits from one transaction.** Keyed on the signature alone, alice's credit
/// marked `soltx:OneTxPaysTwoUsers` processed and bob's credit for the same transaction
/// came back `AlreadyCredited` — bob's 300 units lost, by anyone who pays two addresses
/// in one transaction. Each credited account gets its own key, both credit, and a
/// re-poll of either still credits nothing twice.
#[test]
fn one_transaction_paying_two_deposit_addresses_credits_both() {
    let cfg = config();
    let ledger = CreditLedger::new(InMemoryStore::new(), PRICE_PER_RUN);
    let watcher = SignatureWatcher::new(&cfg, OneTxTwoAccounts).unwrap();
    let (alice, bob) = (UserId::from("alice"), UserId::from("bob"));
    let (alice_addr, bob_addr) = (DepositAddress(ALICE_WALLET), DepositAddress(BOB_WALLET));

    let alice_pays = watcher.poll(&alice, &alice_addr).unwrap();
    let bob_pays = watcher.poll(&bob, &bob_addr).unwrap();
    let alice_outcome = ledger.credit(&alice_pays[0]);
    let bob_outcome = ledger.credit(&bob_pays[0]);
    assert!(matches!(alice_outcome, CreditOutcome::Credited { .. }));
    assert!(
        matches!(bob_outcome, CreditOutcome::Credited { .. }),
        "bob's credit from the shared transaction was refused as processed: {bob_outcome:?}"
    );
    assert_ne!(
        alice_pays[0].reference, bob_pays[0].reference,
        "one transaction paying two accounts is two payments with two keys"
    );
    assert_eq!(ledger.balance(&alice), 5);
    assert_eq!(ledger.balance(&bob), 3);

    // Re-polling both (a restart, a second tick) credits nothing more.
    for (user, addr) in [(&alice, &alice_addr), (&bob, &bob_addr)] {
        for p in watcher.poll(user, addr).unwrap() {
            assert!(matches!(ledger.credit(&p), CreditOutcome::AlreadyCredited));
        }
    }
    assert_eq!((ledger.balance(&alice), ledger.balance(&bob)), (5, 3));
}

/// The same collision across ASSETS: one transaction paying one deposit address in both
/// `$DREGG` and USDC is two credits. The key carries the mint, so they are distinct.
#[test]
fn one_transaction_paying_both_assets_to_one_address_has_two_keys() {
    let cfg = config();
    let addr = DepositAddress(ALICE_WALLET);
    assert_ne!(
        signature_payment_ref("OneTxTwoAssets", &addr, &cfg.mint),
        signature_payment_ref("OneTxTwoAssets", &addr, &cfg.usdc_mint)
    );
}
