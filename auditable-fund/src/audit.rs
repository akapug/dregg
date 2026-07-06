//! The **audit** — what a third party runs to check the fund followed its mandate and did not
//! lie about a single fill, trusting NO operator.
//!
//! [`audit_fund`] takes the exported [`TrackRecord`] plus the two public notary anchors (the
//! fund's decision notary and the oracle's price notary) and:
//!
//!  1. **light-client verifies the ledger** — `node.verify()` (`dregg-turn::verify_receipt_chain`):
//!     the finalized receipt chain is a genuine, unbroken, single-agent, state-continuous
//!     sequence. An inserted / reordered / dropped / backdated turn breaks it.
//!  2. **matches records to the chain** — one on-ledger turn per record, each record's
//!     `turn_hash` a member of the finalized log.
//!  3. **re-verifies every decision + price attestation** — each decision is an authentic ∧
//!     well-formed ∧ injection-free turn; each fill is at a zkOracle-attested price whose
//!     notarized body proves the claimed amount.
//!  4. **re-derives the book and checks the mandate held** — independently replays each fill,
//!     confirms position/budget caps held and the record's stated post-state matches.
//!  5. **recomputes the trade-commitment chain** and confirms it equals the value witnessed on
//!     the finalized ledger's `ATTESTATION_SLOT` — the forge/backdate teeth: any altered,
//!     dropped, reordered, or fabricated record diverges from the on-ledger witness.
//!  6. **produces the P&L** from the verifiable receipts.

use deos_hermes::{AnthropicConfig, attestation_commitment, verify_zkoracle};

use crate::brain::Side;
use crate::fund::{TrackRecord, fold_commitment};
use crate::oracle::{EndpointConfig, verify_attested_price};

/// The result of a passing audit — the fund's provable track record.
#[derive(Clone, Debug)]
pub struct AuditReport {
    /// The number of on-ledger turns (== decisions).
    pub turns: usize,
    /// The number of buy/sell fills.
    pub trades: usize,
    /// The number of holds.
    pub holds: usize,
    /// Realized P&L: final cash minus the mandate budget.
    pub realized_pnl: i64,
    /// Open positions at the end (asset → units).
    pub open_positions: std::collections::BTreeMap<String, i64>,
    /// Mark-to-market of open positions at their last attested price.
    pub mark_to_market: i64,
    /// Equity: final cash + mark-to-market.
    pub equity: i64,
    /// Total P&L: equity minus the mandate budget.
    pub total_pnl: i64,
    /// Final cash.
    pub final_cash: i64,
}

/// Why an audit REFUSED the track record — every variant is a way the fund would have had to
/// lie, each independently detectable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuditError {
    /// The finalized ledger's receipt chain does not verify (forged / reordered / broken).
    ChainInvalid(String),
    /// The record count and the finalized turn count disagree (hidden or fabricated turns).
    TurnCountMismatch {
        /// Records claimed.
        records: usize,
        /// Turns on the finalized log.
        chain: usize,
    },
    /// Record `usize`'s turn hash is not on the finalized log.
    TurnNotOnChain(usize),
    /// Record `usize`'s decision is not a valid attested turn.
    DecisionNotAttested(usize),
    /// Record `usize` is a fill with no / an invalid price attestation.
    PriceNotAttested(usize),
    /// Record `usize`'s stated fill price is not the attested amount.
    FillPriceMismatch(usize),
    /// Record `usize` breached the mandate (asset / position / budget / post-state).
    MandateBreached {
        /// The record index.
        at: usize,
        /// What broke.
        why: String,
    },
    /// The recomputed trade-commitment chain does not match the on-ledger witness — a forged,
    /// altered, dropped, reordered, or backdated record.
    LedgerCommitmentMismatch,
    /// The finalized ledger carries no trade-commitment witness (an unbound / unattested run).
    MissingOnLedgerCommitment,
}

impl core::fmt::Display for AuditError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for AuditError {}

/// **Run the third-party audit.** See the module docs for the six checks. Returns the provable
/// [`AuditReport`] (track record + P&L) or the first [`AuditError`] that bites.
pub fn audit_fund(
    track: &TrackRecord,
    decision_config: &AnthropicConfig,
    oracle_config: &EndpointConfig,
) -> Result<AuditReport, AuditError> {
    // (1) LIGHT-CLIENT: the finalized receipt chain verifies (no operator trust).
    track
        .node
        .verify()
        .map_err(|e| AuditError::ChainInvalid(format!("{e:?}")))?;

    // (2) One on-ledger turn per claimed record — no hidden or fabricated turns.
    let chain_len = track.node.finalized_len();
    if chain_len != track.records.len() {
        return Err(AuditError::TurnCountMismatch {
            records: track.records.len(),
            chain: chain_len,
        });
    }

    let mut acc = [0u8; 32];
    let mut cash = track.mandate.budget;
    let mut positions: std::collections::BTreeMap<String, i64> = std::collections::BTreeMap::new();
    let mut last_price: std::collections::BTreeMap<String, i64> = std::collections::BTreeMap::new();
    let mut trades = 0usize;
    let mut holds = 0usize;

    for (i, r) in track.records.iter().enumerate() {
        // Membership: the record names a genuine on-chain turn.
        if !track.node.contains(&r.turn_hash) {
            return Err(AuditError::TurnNotOnChain(i));
        }

        // (3a) The decision is a valid attested turn.
        verify_zkoracle(&r.decision_att, decision_config)
            .map_err(|_| AuditError::DecisionNotAttested(i))?;

        match r.side {
            Side::Hold => {
                holds += 1;
                // A hold changes nothing; its stated post-state must reflect that.
                let cur = *positions.get(&r.asset).unwrap_or(&0);
                if r.cash_after != cash || r.position_after != cur {
                    return Err(AuditError::MandateBreached {
                        at: i,
                        why: "hold altered the book".to_string(),
                    });
                }
            }
            Side::Buy | Side::Sell => {
                trades += 1;
                // MANDATE: asset allowed.
                if !track.mandate.allows(&r.asset) {
                    return Err(AuditError::MandateBreached {
                        at: i,
                        why: format!("asset `{}` outside the mandate", r.asset),
                    });
                }
                // (3b) The fill is at a provably attested price for the claimed amount.
                let ap = r
                    .price_att
                    .as_ref()
                    .ok_or(AuditError::PriceNotAttested(i))?;
                // Re-verify the attestation and re-derive the notarized amount in cents; the
                // record's stated fill price must be exactly that attested amount.
                let cents = verify_attested_price(ap, oracle_config)
                    .map_err(|_| AuditError::PriceNotAttested(i))?;
                if cents != r.price {
                    return Err(AuditError::FillPriceMismatch(i));
                }

                // (4) Independently re-derive the fill against the running book.
                let cur = *positions.get(&r.asset).unwrap_or(&0);
                let (new_cash, new_pos) = match r.side {
                    Side::Buy => {
                        let cost =
                            r.qty
                                .checked_mul(r.price)
                                .ok_or(AuditError::MandateBreached {
                                    at: i,
                                    why: "fill overflow".to_string(),
                                })?;
                        (cash - cost, cur + r.qty)
                    }
                    Side::Sell => {
                        if r.qty > cur {
                            return Err(AuditError::MandateBreached {
                                at: i,
                                why: "oversell (short) — no position".to_string(),
                            });
                        }
                        let proceeds =
                            r.qty
                                .checked_mul(r.price)
                                .ok_or(AuditError::MandateBreached {
                                    at: i,
                                    why: "fill overflow".to_string(),
                                })?;
                        (cash + proceeds, cur - r.qty)
                    }
                    Side::Hold => unreachable!(),
                };
                // MANDATE: position bound + solvency.
                if new_pos.abs() > track.mandate.max_position {
                    return Err(AuditError::MandateBreached {
                        at: i,
                        why: format!("position {new_pos} past max {}", track.mandate.max_position),
                    });
                }
                if new_cash < 0 {
                    return Err(AuditError::MandateBreached {
                        at: i,
                        why: "over budget".to_string(),
                    });
                }
                // The record's stated post-state must match the independent re-derivation.
                if r.cash_after != new_cash || r.position_after != new_pos {
                    return Err(AuditError::MandateBreached {
                        at: i,
                        why: "record post-state inconsistent with the re-derived book".to_string(),
                    });
                }
                cash = new_cash;
                positions.insert(r.asset.clone(), new_pos);
                last_price.insert(r.asset.clone(), r.price);
            }
        }

        // (5) Recompute the trade-commitment chain over the published records.
        let decision_commit = attestation_commitment(&r.decision_att);
        let price_commit = r
            .price_att
            .as_ref()
            .map(|ap| attestation_commitment(&ap.attestation));
        acc = fold_commitment(
            acc,
            decision_commit,
            price_commit,
            r.side,
            &r.asset,
            r.qty,
            r.price,
            r.cash_after,
            r.position_after,
        );
        // The record's own stored accumulator must match (self-consistency of the record set).
        if r.commit_after != acc {
            return Err(AuditError::LedgerCommitmentMismatch);
        }
    }

    // (5b) THE ON-LEDGER BIND — the recomputed final accumulator must equal the value the
    //      finalized ledger witnesses at ATTESTATION_SLOT. A forged / altered / dropped /
    //      reordered / backdated record set diverges here.
    match track.on_ledger_commitment {
        Some(c) if c == acc => {}
        Some(_) => return Err(AuditError::LedgerCommitmentMismatch),
        None => return Err(AuditError::MissingOnLedgerCommitment),
    }

    // (6) P&L from the verifiable receipts.
    let realized_pnl = cash - track.mandate.budget;
    let open_positions: std::collections::BTreeMap<String, i64> = positions
        .iter()
        .filter(|(_, p)| **p != 0)
        .map(|(a, p)| (a.clone(), *p))
        .collect();
    let mark_to_market: i64 = open_positions
        .iter()
        .map(|(a, &p)| p * last_price.get(a).copied().unwrap_or(0))
        .sum();
    let equity = cash + mark_to_market;
    let total_pnl = equity - track.mandate.budget;

    Ok(AuditReport {
        turns: chain_len,
        trades,
        holds,
        realized_pnl,
        open_positions,
        mark_to_market,
        equity,
        total_pnl,
        final_cash: cash,
    })
}
