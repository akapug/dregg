//! [`CreditLedger`] — per-user RUN credits, minted from observed `$DREGG` payments
//! at a configured price, spent one-per-run, idempotent per payment reference.
//!
//! # Relationship to the kernel value layer
//!
//! This is an OFF-CHAIN service ledger (the bot persists it in sqlite), not the
//! kernel's conserving value layer. It is modelled on the same shape as
//! `dregg_payable::Payable` (`balance` / value-out) and the SDK tool-gateway's
//! `Charge` (per-call value metering): a credit is "one run's worth of budget",
//! [`CreditLedger::debit`] is the metered spend. The endgame is to back these
//! credits with a dregg-protocol-native `Effect::Transfer` so the run budget is a
//! conserved on-chain balance; today they are a custodial service ledger over
//! observed Solana payments.

use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use crate::config::UserId;
use crate::watcher::{PaymentReceived, PaymentRef};

/// The pluggable credit store. In tests / small deployments use
/// [`InMemoryStore`]; the discord bot supplies a sqlite-backed impl. All methods
/// take `&self` (interior mutability) so a `CreditLedger` can be shared.
///
/// Stores can override [`CreditStore::credit_once`] with a database transaction.
/// The ledger also serializes operations on one store handle, and the in-memory
/// implementation performs deduplication + balance mutation under one mutex.
pub trait CreditStore {
    /// The user's current run-credit balance.
    fn balance(&self, user: &UserId) -> u64;
    /// Set the user's current balance (compatibility primitive for persistent stores).
    fn set_balance(&self, user: &UserId, credits: u64);
    /// Whether `reference` has already been processed.
    fn is_processed(&self, reference: &PaymentRef) -> bool;
    /// Mark `reference` processed.
    fn mark_processed(&self, reference: &PaymentRef);
    /// Atomically deduplicate `reference` and add `credits`. Implementations backed
    /// by a database must perform both changes in one transaction.
    fn credit_once(
        &self,
        user: &UserId,
        reference: &PaymentRef,
        credits: u64,
    ) -> StoreCreditOutcome {
        if self.is_processed(reference) {
            return StoreCreditOutcome::AlreadyProcessed;
        }
        let Some(new_balance) = self.balance(user).checked_add(credits) else {
            return StoreCreditOutcome::BalanceOverflow;
        };
        self.set_balance(user, new_balance);
        self.mark_processed(reference);
        StoreCreditOutcome::Credited { new_balance }
    }
    /// Atomically spend one credit, returning the remaining balance.
    fn debit_one(&self, user: &UserId) -> Option<u64> {
        let remaining = self.balance(user).checked_sub(1)?;
        self.set_balance(user, remaining);
        Some(remaining)
    }
}

/// The atomic store result behind [`CreditLedger::credit`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StoreCreditOutcome {
    Credited { new_balance: u64 },
    AlreadyProcessed,
    BalanceOverflow,
}

/// A simple, thread-safe in-memory [`CreditStore`] for tests and single-process
/// deployments.
#[derive(Default)]
pub struct InMemoryStore {
    state: Mutex<InMemoryState>,
}

#[derive(Default)]
struct InMemoryState {
    balances: HashMap<UserId, u64>,
    processed: HashSet<PaymentRef>,
}

impl InMemoryStore {
    /// A fresh empty store.
    pub fn new() -> Self {
        Self::default()
    }
}

impl CreditStore for InMemoryStore {
    fn balance(&self, user: &UserId) -> u64 {
        *self.state.lock().unwrap().balances.get(user).unwrap_or(&0)
    }
    fn set_balance(&self, user: &UserId, credits: u64) {
        self.state
            .lock()
            .unwrap()
            .balances
            .insert(user.clone(), credits);
    }
    fn is_processed(&self, reference: &PaymentRef) -> bool {
        self.state.lock().unwrap().processed.contains(reference)
    }
    fn mark_processed(&self, reference: &PaymentRef) {
        self.state
            .lock()
            .unwrap()
            .processed
            .insert(reference.clone());
    }
    fn credit_once(
        &self,
        user: &UserId,
        reference: &PaymentRef,
        credits: u64,
    ) -> StoreCreditOutcome {
        let mut state = self.state.lock().unwrap();
        if state.processed.contains(reference) {
            return StoreCreditOutcome::AlreadyProcessed;
        }
        let current = *state.balances.get(user).unwrap_or(&0);
        let Some(new_balance) = current.checked_add(credits) else {
            return StoreCreditOutcome::BalanceOverflow;
        };
        state.balances.insert(user.clone(), new_balance);
        state.processed.insert(reference.clone());
        StoreCreditOutcome::Credited { new_balance }
    }
    fn debit_one(&self, user: &UserId) -> Option<u64> {
        let mut state = self.state.lock().unwrap();
        let current = *state.balances.get(user).unwrap_or(&0);
        let remaining = current.checked_sub(1)?;
        state.balances.insert(user.clone(), remaining);
        Some(remaining)
    }
}

/// What a [`CreditLedger::credit`] did — surfaced so callers (and tests) can prove
/// idempotency.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CreditOutcome {
    /// The payment was newly credited: `runs` run-credits added from `amount`
    /// atomic `$DREGG` units (`amount / price_per_run`, floored). `remainder`
    /// atomic units were below the price of one run and are NOT credited (the
    /// operator may choose to carry them; this ledger discards sub-run dust).
    Credited {
        /// Run-credits added.
        runs: u64,
        /// Atomic `$DREGG` units consumed to mint `runs`.
        amount: u64,
        /// Atomic `$DREGG` units left over below one run's price (dust).
        remainder: u64,
        /// The user's balance after crediting.
        new_balance: u64,
    },
    /// This payment reference was already credited — no double-credit (idempotent).
    AlreadyCredited,
    /// The payment was for a positive amount but below the price of a single run,
    /// so it minted zero credits. Not an error; nothing was added.
    BelowOneRun {
        /// The amount that was too small.
        amount: u64,
    },
    /// Crediting would overflow the user's counter. The reference is deliberately
    /// left unprocessed so an operator can resolve the balance and retry.
    BalanceOverflow,
}

/// Why a [`CreditLedger::debit`] failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DebitError {
    /// The user has no run-credits to spend.
    InsufficientCredits {
        /// The user whose balance was empty.
        user: UserId,
    },
}

impl std::fmt::Display for DebitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DebitError::InsufficientCredits { user } => {
                write!(f, "user {user} has no run-credits to spend")
            }
        }
    }
}

impl std::error::Error for DebitError {}

/// The per-user run-credit ledger over a pluggable [`CreditStore`].
pub struct CreditLedger<S: CreditStore> {
    store: S,
    price_per_run: u64,
    operations: Mutex<()>,
}

impl<S: CreditStore> CreditLedger<S> {
    /// New ledger. `price_per_run` = atomic `$DREGG` units per one run credit
    /// (must be ≥ 1).
    pub fn new(store: S, price_per_run: u64) -> Self {
        assert!(price_per_run >= 1, "price_per_run must be >= 1");
        CreditLedger {
            store,
            price_per_run,
            operations: Mutex::new(()),
        }
    }

    /// The configured price (atomic `$DREGG` per run).
    pub fn price_per_run(&self) -> u64 {
        self.price_per_run
    }

    /// Borrow the underlying store.
    pub fn store(&self) -> &S {
        &self.store
    }

    /// Credit run-credits from an observed [`PaymentReceived`] — **idempotent by
    /// [`PaymentReceived::reference`]**. Re-observing the same payment returns
    /// [`CreditOutcome::AlreadyCredited`] and changes nothing. This is the primary
    /// entry the watcher feeds.
    pub fn credit(&self, payment: &PaymentReceived) -> CreditOutcome {
        let _operation = self.operations.lock().unwrap();
        let runs = payment.amount / self.price_per_run;
        let consumed = runs * self.price_per_run;
        let remainder = payment.amount - consumed;
        match self
            .store
            .credit_once(&payment.user, &payment.reference, runs)
        {
            StoreCreditOutcome::AlreadyProcessed => CreditOutcome::AlreadyCredited,
            StoreCreditOutcome::BalanceOverflow => CreditOutcome::BalanceOverflow,
            StoreCreditOutcome::Credited { .. } if runs == 0 => CreditOutcome::BelowOneRun {
                amount: payment.amount,
            },
            StoreCreditOutcome::Credited { new_balance } => CreditOutcome::Credited {
                runs,
                amount: consumed,
                remainder,
                new_balance,
            },
        }
    }

    /// Credit a PRE-COMPUTED number of runs from an observed payment — **idempotent
    /// by [`PaymentReceived::reference`]**. This is the DUAL-ASSET entry: the caller
    /// prices the payment with
    /// [`runs_for_payment`](crate::pricing::runs_for_payment) (USDC flat, `$DREGG` at
    /// the discounted oracle rate) and hands the resulting `runs` here, so a run
    /// credited from either asset is uniform at the ledger. `runs == 0` (a sub-run
    /// payment) marks the reference processed and returns
    /// [`CreditOutcome::BelowOneRun`] — no double-processing on a later re-observe.
    pub fn credit_runs(&self, payment: &PaymentReceived, runs: u64) -> CreditOutcome {
        let _operation = self.operations.lock().unwrap();
        match self
            .store
            .credit_once(&payment.user, &payment.reference, runs)
        {
            StoreCreditOutcome::AlreadyProcessed => CreditOutcome::AlreadyCredited,
            StoreCreditOutcome::BalanceOverflow => CreditOutcome::BalanceOverflow,
            StoreCreditOutcome::Credited { .. } if runs == 0 => CreditOutcome::BelowOneRun {
                amount: payment.amount,
            },
            StoreCreditOutcome::Credited { new_balance } => CreditOutcome::Credited {
                runs,
                // In the price-fed path the whole payment is consumed into `runs`.
                amount: payment.amount,
                remainder: 0,
                new_balance,
            },
        }
    }

    /// Spend one run-credit. Fails with [`DebitError::InsufficientCredits`] if the
    /// user has none. Returns the balance remaining after the spend.
    pub fn debit(&self, user: &UserId) -> Result<u64, DebitError> {
        let _operation = self.operations.lock().unwrap();
        self.store
            .debit_one(user)
            .ok_or_else(|| DebitError::InsufficientCredits { user: user.clone() })
    }

    /// The user's run-credit balance.
    pub fn balance(&self, user: &UserId) -> u64 {
        self.store.balance(user)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::DepositAddress;

    fn payment(user: &str, amount: u64, reference: &str) -> PaymentReceived {
        PaymentReceived {
            user: UserId::from(user),
            deposit_address: DepositAddress([0u8; 32]),
            asset: crate::config::Asset::Dregg,
            amount,
            reference: PaymentRef(reference.to_string()),
        }
    }

    #[test]
    fn credit_runs_is_idempotent_and_uniform() {
        let ledger = CreditLedger::new(InMemoryStore::new(), 1);
        let carol = UserId::from("carol");
        // A USDC-priced payment worth 7 runs (computed upstream).
        let out = ledger.credit_runs(&payment("carol", 700_000, "usdc-tx1"), 7);
        assert!(matches!(
            out,
            CreditOutcome::Credited {
                runs: 7,
                new_balance: 7,
                ..
            }
        ));
        assert_eq!(ledger.balance(&carol), 7);
        // Re-observe the same reference ⇒ no double-credit.
        assert_eq!(
            ledger.credit_runs(&payment("carol", 700_000, "usdc-tx1"), 7),
            CreditOutcome::AlreadyCredited
        );
        assert_eq!(ledger.balance(&carol), 7);
        // A sub-run payment marks processed and credits nothing.
        assert_eq!(
            ledger.credit_runs(&payment("carol", 1, "dust"), 0),
            CreditOutcome::BelowOneRun { amount: 1 }
        );
        assert_eq!(ledger.balance(&carol), 7);
    }

    #[test]
    fn credit_debit_and_idempotency() {
        let ledger = CreditLedger::new(InMemoryStore::new(), 100);
        let alice = UserId::from("alice");

        // 250 units @ 100/run = 2 runs, 50 dust.
        let out = ledger.credit(&payment("alice", 250, "tx1"));
        assert_eq!(
            out,
            CreditOutcome::Credited {
                runs: 2,
                amount: 200,
                remainder: 50,
                new_balance: 2
            }
        );
        assert_eq!(ledger.balance(&alice), 2);

        // Re-observe the SAME reference ⇒ no double-credit.
        assert_eq!(
            ledger.credit(&payment("alice", 250, "tx1")),
            CreditOutcome::AlreadyCredited
        );
        assert_eq!(ledger.balance(&alice), 2);

        // A different payment credits again.
        ledger.credit(&payment("alice", 100, "tx2"));
        assert_eq!(ledger.balance(&alice), 3);

        // Debit spends one at a time.
        assert_eq!(ledger.debit(&alice), Ok(2));
        assert_eq!(ledger.debit(&alice), Ok(1));
        assert_eq!(ledger.debit(&alice), Ok(0));
        // Empty balance ⇒ debit fails.
        assert_eq!(
            ledger.debit(&alice),
            Err(DebitError::InsufficientCredits {
                user: alice.clone()
            })
        );
    }

    #[test]
    fn below_one_run_credits_nothing() {
        let ledger = CreditLedger::new(InMemoryStore::new(), 100);
        assert_eq!(
            ledger.credit(&payment("bob", 50, "small")),
            CreditOutcome::BelowOneRun { amount: 50 }
        );
        assert_eq!(ledger.balance(&UserId::from("bob")), 0);
    }

    #[test]
    fn concurrent_duplicate_credit_is_one_atomic_store_transaction() {
        use std::sync::{Arc, Barrier};
        use std::thread;

        let ledger = Arc::new(CreditLedger::new(InMemoryStore::new(), 100));
        let payment = Arc::new(payment("alice", 100, "same-chain-payment"));
        let start = Arc::new(Barrier::new(9));
        let mut threads = Vec::new();
        for _ in 0..8 {
            let ledger = Arc::clone(&ledger);
            let payment = Arc::clone(&payment);
            let start = Arc::clone(&start);
            threads.push(thread::spawn(move || {
                start.wait();
                ledger.credit(&payment)
            }));
        }
        start.wait();
        let outcomes: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();
        assert_eq!(
            outcomes
                .iter()
                .filter(|o| matches!(o, CreditOutcome::Credited { .. }))
                .count(),
            1
        );
        assert_eq!(ledger.balance(&UserId::from("alice")), 1);
    }
}
