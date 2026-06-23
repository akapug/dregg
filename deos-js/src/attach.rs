//! ATTACH — run JS over a PROVIDED live World, not deos-js's own embedded engine.
//!
//! [`Applet`](crate::Applet) mints its OWN [`DreggEngine`](dregg_sdk::embed::DreggEngine):
//! a fresh, single-cell world. That proves the agent-runs-JS-bound-to-its-cap shape
//! end-to-end, but the JS only ever crawls + drives ITS OWN private image.
//!
//! THE ATTACH PATH binds the runtime to a **provided** World — the live cockpit's
//! real ledger (the operator's actual cells), or a fork of it (safe experimentation)
//! — through a thin [`WorldSink`] the host implements. The JS then:
//!
//!   * `deos.world.cells()` / `deos.cell(id).reflect()` crawl the ATTACHED World's
//!     REAL cells (via [`crate::reflect_binding`] over [`WorldSink::ledger`]); and
//!   * `app.fire("name", n)` commits a real cap-gated verified turn ON THAT World
//!     (via [`WorldSink::commit_turn`]) — a receipt that lands on the live ledger.
//!
//! ## The red-team invariant is KEPT
//!
//! The cap tooth ([`dregg_cell::is_attenuation`]) lives HERE, in deos-js, exactly as
//! in [`Applet::fire`]: a fire is admitted iff the AGENT'S `held` authority satisfies
//! the affordance's `required`. The runtime is mounted under that attenuated `held`,
//! never the World's root. An over-reach (a `required` the agent does not hold) is
//! refused IN-BAND — no turn, no receipt — and a fire is bound to the agent's OWN
//! cell, so it cannot cross to another vessel. (`docs/deos/AGENT-CONFINEMENT-REDTEAM.md`.)
//!
//! deos-js does NOT depend on starbridge-v2 (the dependency runs the other way), so
//! the live `World` is reached through this trait, not a direct type — the host
//! crate (or deos-hermes) supplies the `impl WorldSink`.

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Ledger};
use dregg_turn::action::Effect;
use dregg_types::CellId;

use crate::applet::{CellModel, FireError, Slot};

/// The host's live World, reduced to exactly what an attached applet needs: a
/// witnessed read surface (the crawl) and a commit primitive (the fire).
///
/// starbridge-v2's `World` implements this (its `ledger()` + a `commit_turn`-backed
/// adapter); a `World::fork()` implements it identically (the safe sandbox variant).
/// The implementor owns the verified executor — every [`fire_effects`](Self::fire_effects)
/// runs the SAME conservation / ocap / authority gate the live world would.
pub trait WorldSink {
    /// Read the live ledger the reflective crawl walks (the SAME ledger a fire commits
    /// onto) by running `f` over a borrow of it. Closure-passing (rather than handing
    /// back a `&Ledger`) so a host holding the World behind an `Rc<RefCell<World>>`
    /// can borrow it for exactly the read's duration — the crawl is synchronous, so
    /// `f` produces its JSON (or whatever) and the borrow ends.
    fn with_ledger(&self, f: &mut dyn FnMut(&Ledger));

    /// Commit ONE verified turn on `agent`'s cell carrying `effects`, named `method`,
    /// against the live verified executor. The host builds the turn with its OWN
    /// `World::turn` shape (so the live turn is byte-shaped exactly like every other
    /// cockpit turn: the agent's nonce, the chain head threaded, the World's fee
    /// stamped) and commits it through `World::commit_turn`. Returns the real receipt
    /// hash on commit, or the executor's rejection reason.
    ///
    /// The cap tooth has ALREADY run in deos-js before this is called (the over-reach
    /// is refused in-band, never reaching here) — this is the authorized commit only.
    fn fire_effects(
        &mut self,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String>;
}

/// An applet whose substance is a PROVIDED live World (the attach path), in contrast
/// to [`Applet`](crate::Applet) which owns a fresh embedded engine.
///
/// It carries the agent's identity (`agent` cell), its `held` authority (the cap the
/// runtime is mounted under), and the named affordance surface (`required` per name —
/// the cap tooth a fire is checked against). A fire builds the SAME counter-bump turn
/// shape [`Applet::fire`] builds, but commits it through the [`WorldSink`] onto the
/// LIVE ledger.
pub struct AttachedApplet {
    sink: Box<dyn WorldSink>,
    /// The agent's cell — the agent of every committed turn (its OWN vessel: a fire
    /// binds this cell, so it cannot cross to another).
    agent: CellId,
    /// The held authority the runtime is mounted under (the red-team invariant: the
    /// caller's ATTENUATED cap, never the World's root).
    held: AuthRequired,
    /// The agent's affordance surface — `(name, required)`. A fire of `name` is gated
    /// on `required`; an unheld `required` is the over-reach the cap tooth refuses.
    affordances: Vec<(String, AuthRequired)>,
    /// The slot a fire's counter-bump writes (the spike's mutating shape).
    counter_slot: Slot,
    /// The committed receipt hashes, in order (the audit tape the JS left on the live
    /// World).
    receipts: Vec<[u8; 32]>,
    /// Ephemeral view-state — never a turn (the load-bearing distinction).
    view: std::collections::BTreeMap<String, String>,
}

impl AttachedApplet {
    /// Attach an applet to a provided live World (`sink`), driving the agent cell
    /// `agent` under `held`, with the named `affordances` surface. `counter_slot` is
    /// the state slot a fire bumps (the counter shape; reuse the same slot the host's
    /// affordance writes).
    pub fn attach(
        sink: Box<dyn WorldSink>,
        agent: CellId,
        held: AuthRequired,
        affordances: Vec<(String, AuthRequired)>,
        counter_slot: Slot,
    ) -> Self {
        AttachedApplet {
            sink,
            agent,
            held,
            affordances,
            counter_slot,
            receipts: Vec::new(),
            view: std::collections::BTreeMap::new(),
        }
    }

    /// The agent cell (the applet's sovereignty boundary on the attached World).
    pub fn cell(&self) -> CellId {
        self.agent
    }

    /// The held authority the runtime is mounted under.
    pub fn held(&self) -> &AuthRequired {
        &self.held
    }

    /// Read the attached World's live ledger (the crawl surface) by running `f` over
    /// it. The SAME ledger a fire commits onto — the reflective read is of the REAL
    /// cells.
    pub fn with_ledger(&self, f: &mut dyn FnMut(&Ledger)) {
        self.sink.with_ledger(f);
    }

    /// The registered affordance specs (name + required authority) — the cap-gated
    /// message surface the reflective `affordances(viewer)` projects.
    pub fn affordance_specs(&self) -> Vec<(String, AuthRequired)> {
        let mut specs = self.affordances.clone();
        specs.sort_by(|a, b| a.0.cmp(&b.0));
        specs
    }

    /// The committed receipt tape (what the JS left on the live World).
    pub fn receipts(&self) -> &[[u8; 32]] {
        &self.receipts
    }

    /// The number of verified turns committed onto the attached World.
    pub fn receipt_count(&self) -> usize {
        self.receipts.len()
    }

    /// The most recent committed receipt hash, if any.
    pub fn last_receipt(&self) -> Option<[u8; 32]> {
        self.receipts.last().copied()
    }

    /// A witnessed read of the agent cell's live model off the attached ledger.
    pub fn model(&self) -> CellModel {
        let mut model = CellModel::from_ledger_empty();
        let agent = self.agent;
        self.sink
            .with_ledger(&mut |l| model = CellModel::from_ledger(l, &agent));
        model
    }

    /// Witnessed read of one model field as a u64 (the scalar shape).
    pub fn get_u64(&self, slot: Slot) -> u64 {
        self.model().field_u64(slot)
    }

    /// **Fire an affordance** — commit ONE cap-gated verified turn ON THE LIVE WORLD.
    ///
    /// 1. resolve the affordance (an unknown name = no turn);
    /// 2. CAP TOOTH, in-band: `held` must satisfy the affordance's `required`
    ///    ([`dregg_cell::is_attenuation`]) — an over-reach commits NOTHING;
    /// 3. build the counter-bump turn (agent = the agent's OWN cell, the chain head
    ///    threaded from the live World, the fee stamped) and commit it through the
    ///    [`WorldSink`] — landing the receipt on the live ledger.
    pub fn fire(&mut self, affordance: &str, arg: i64) -> Result<[u8; 32], FireError> {
        let required = self
            .affordances
            .iter()
            .find(|(n, _)| n == affordance)
            .map(|(_, r)| r.clone())
            .ok_or_else(|| FireError::UnknownAffordance(affordance.to_string()))?;

        // (2) CAP TOOTH — the REAL is_attenuation, in-band. Refused ⇒ nothing committed,
        // and (crucially on a LIVE world) nothing reaches the executor at all.
        if !dregg_cell::is_attenuation(&self.held, &required) {
            return Err(FireError::Unauthorized {
                affordance: affordance.to_string(),
            });
        }

        // (3) writes = the counter-bump (pure function of the live model), exactly as
        //     the embedded `Applet::fire`. The effects bump the counter slot AND the
        //     nonce (so the turn chains + the model witnesses the fire). They act on
        //     the agent's OWN cell — a fire cannot reach another vessel.
        let model = self.model();
        let cur = model.field_u64(self.counter_slot) as i64;
        let next = (cur + arg).max(0) as u64;
        let value: FieldElement = crate::applet::pack_u64(next);
        let effects = vec![
            Effect::SetField {
                cell: self.agent,
                index: self.counter_slot,
                value,
            },
            Effect::IncrementNonce { cell: self.agent },
        ];

        // (4) commit through the host's World (its own turn shape — the chain head,
        //     nonce + fee threaded host-side). The receipt lands on the live ledger.
        let rh = self
            .sink
            .fire_effects(self.agent, affordance, effects)
            .map_err(FireError::Executor)?;
        self.receipts.push(rh);
        Ok(rh)
    }

    /// Set ephemeral view-state — a plain in-memory change (NO turn, NO receipt).
    pub fn set_view(&mut self, key: &str, value: &str) {
        self.view.insert(key.to_string(), value.to_string());
    }

    /// Read ephemeral view-state.
    pub fn get_view(&self, key: &str) -> Option<&str> {
        self.view.get(key).map(|s| s.as_str())
    }
}
