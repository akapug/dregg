//! The action verbs: demo turns, the SIMULATE composer, cipherclerk, buffer, terminal, swarm + the killer-demo driver.

use super::*;

impl Cockpit {
    pub(crate) fn run_demo_transfer(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::transfer(treasury, user, 1_000)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    pub(crate) fn run_demo_grant(&mut self, cx: &mut Context<Self>) {
        let [_treasury, service, user] = self.anchors;
        // Re-grant the service's user-cap to a fresh slot (legitimate).
        let outcome = {
            let mut w = self.world.borrow_mut();
            let slot = w
                .ledger()
                .get(&service)
                .map(|c| c.capabilities.len() as u32)
                .unwrap_or(0);
            let turn = w.turn(
                service,
                vec![world::grant_capability(service, service, user, slot)],
            );
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    pub(crate) fn run_demo_create(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, _user] = self.anchors;
        let seed = (self.world.borrow().cell_count() as u8).wrapping_add(0x40);
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::create_cell(seed)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// **LAUNCH a confined app at RUNTIME** — the powerbox's missing first half.
    ///
    /// The boot-seeded `powerbox_app` is one demo app; this spawns an ARBITRARY
    /// confined app on demand. It calls the real [`AppLauncher::launch`]: births a
    /// fresh app-cell into the live world holding NO ambient authority (an empty
    /// c-list — a genuine confined app-as-cell), records it, and makes IT the app
    /// whose [`CapabilityRequest`] the powerbox panel now mediates (`powerbox_app`
    /// points at the freshly launched cell). The request then routes through the
    /// EXISTING [`Powerbox::present`] the panel already renders — the launcher
    /// supplies the confined requester; the powerbox supplies the grant. Re-runnable:
    /// each press births a distinct app and switches the panel to it.
    pub(crate) fn run_launch_confined_app(&mut self, cx: &mut Context<Self>) {
        use starbridge_v2::powerbox::AppLauncher;
        let n = self.launched_apps.len() + 1;
        let launched = {
            let mut w = self.world.borrow_mut();
            AppLauncher::launch(
                &mut w,
                format!("launched-app-{n}"),
                "this app launched at runtime and needs to reach one peer/resource — designate exactly one",
                dregg_cell::AuthRequired::None,
            )
        };
        // The freshly launched confined app is now the powerbox's current requester:
        // its standing request is routed through the existing Powerbox::present the
        // panel renders. Switch to the POWERBOX tab so the designation flow is in view.
        self.powerbox_app = Some(launched.app_cell);
        self.powerbox_outcome = Some(format!(
            "launched: {} — a fresh CONFINED app (no ambient authority); it can only ASK. Designate a held target below.",
            launched.label()
        ));
        self.launched_apps.push(launched);
        self.tab = Tab::Powerbox;
        self.refresh_cells();
        cx.notify();
    }

    pub(crate) fn run_over_grant(&mut self, cx: &mut Context<Self>) {
        // Demonstrate the ocap guarantee FIRING: an illegitimate grant.
        let [treasury, _service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            // treasury holds no cap to user → no-amplification rejects this.
            let turn = w.turn(
                treasury,
                vec![world::grant_capability(treasury, treasury, user, 0)],
            );
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// Birth a fresh cell and SEAL it in one demo flow — shows the lifecycle
    /// verb running through the real executor (seal must target the acting cell;
    /// we genesis the cell, then seal it). Re-runnable: each press seals a new
    /// fresh cell so the lifecycle column grows.
    pub(crate) fn run_seal(&mut self, cx: &mut Context<Self>) {
        let outcome = {
            let mut w = self.world.borrow_mut();
            let seed = (w.cell_count() as u8).wrapping_add(0x70);
            let id = w.genesis_cell(seed, 0);
            let turn = w.turn(id, vec![world::seal(id, "operator seal demo")]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// Burn value from the treasury — supply provably reduced, no credit. The
    /// receipt's `was_burn` flag is bound into its hash (the cockpit's proof
    /// view surfaces it).
    pub(crate) fn run_burn(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, _user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::burn(treasury, 1_000)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// Compose a MULTI-ACTION turn — treasury pays BOTH service and user in one
    /// atomic verified turn (two sibling actions, one receipt). Demonstrates the
    /// call-forest composer driving the real executor.
    pub(crate) fn run_compose_multi(&mut self, cx: &mut Context<Self>) {
        let [treasury, service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.forest_turn(
                treasury,
                vec![
                    (treasury, vec![world::transfer(treasury, service, 500)]),
                    (treasury, vec![world::transfer(treasury, user, 750)]),
                ],
            );
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    // --- the WHAT-IF / SIMULATE composer verbs ------------------------------
    //
    // These build an `IntentDraft` (compose any intent over any cell), run it
    // through a FORKED throwaway world to PREDICT the outcome (the real executor,
    // live world untouched), then — on commit — fire the SAME turn for real.

    /// Cycle the SIMULATE composer's AGENT through the live cells (the cell that
    /// authorizes + submits the composed turn). A fresh draft is started on the new
    /// agent (the prior forest is cleared, since its actions referenced the old
    /// agent's intent); the prediction is invalidated.
    pub(crate) fn sim_cycle_agent(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        if cells.is_empty() {
            return;
        }
        let cur = cells
            .iter()
            .position(|c| *c == self.sim_draft.agent)
            .unwrap_or(0);
        let next = cells[(cur + 1) % cells.len()];
        self.sim_draft = starbridge_v2::simulate::IntentDraft::new(next);
        self.sim_outcome = None;
        self.sim_commit_banner = None;
        cx.notify();
    }

    /// Cycle the TARGET cell the next added effect will act on (the action's
    /// acting cell). Wraps over the live cells.
    pub(crate) fn sim_cycle_target(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        if cells.is_empty() {
            return;
        }
        self.sim_target_idx = (self.sim_target_idx + 1) % cells.len();
        cx.notify();
    }

    /// Cycle the EFFECT KIND the next "+ add" will append, over the full palette
    /// (the studio-parity coverage — every single-custody-simulable effect).
    pub(crate) fn sim_cycle_effect(&mut self, cx: &mut Context<Self>) {
        self.sim_effect_idx = (self.sim_effect_idx + 1) % self.sim_effect_palette().len();
        cx.notify();
    }

    /// The effect palette, with the CURRENT target/peer cells filled in (so the
    /// templates reference real live cells). The "+ add" verb appends the entry at
    /// `sim_effect_idx`. Order is the coverage display order.
    pub(crate) fn sim_effect_palette(&self) -> Vec<starbridge_v2::simulate::EffectKind> {
        use starbridge_v2::simulate::EffectKind as E;
        let cells = &self.cells;
        let target = cells
            .get(self.sim_target_idx)
            .copied()
            .unwrap_or(self.sim_draft.agent);
        // A "peer" distinct from the target where possible (for transfer/grant dests).
        let peer = cells
            .iter()
            .find(|c| **c != target)
            .copied()
            .unwrap_or(target);
        vec![
            E::Transfer {
                to: peer,
                amount: 250,
            },
            E::GrantCapability {
                to: peer,
                target,
                slot: 0,
            },
            E::RevokeCapability { slot: 0 },
            E::EmitEvent {
                topic: "what-if".into(),
            },
            E::IncrementNonce,
            E::CreateCell { seed: 0x9A },
            E::SetField {
                index: 0,
                value: [7u8; 32],
            },
            E::SetPermissionsOpen,
            E::MakeSovereign,
            E::Seal {
                reason: "what-if seal".into(),
            },
            E::Unseal,
            E::Destroy,
            E::Burn { amount: 1_000 },
        ]
    }

    /// Append the currently-picked effect (on the currently-picked target) to the
    /// draft as a new action root. Invalidates the prior prediction.
    pub(crate) fn sim_add_effect(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        let Some(target) = cells.get(self.sim_target_idx).copied() else {
            return;
        };
        let palette = self.sim_effect_palette();
        let Some(effect) = palette.get(self.sim_effect_idx).cloned() else {
            return;
        };
        let ai = self.sim_draft.add_action(target);
        self.sim_draft.add_effect(ai, effect);
        self.sim_outcome = None;
        self.sim_commit_banner = None;
        cx.notify();
    }

    /// Drop the most-recently-added action from the draft (the panel's undo).
    pub(crate) fn sim_pop_action(&mut self, cx: &mut Context<Self>) {
        let n = self.sim_draft.actions.len();
        if n > 0 {
            self.sim_draft.remove_action(n - 1);
        }
        self.sim_outcome = None;
        self.sim_commit_banner = None;
        cx.notify();
    }

    /// Clear the draft to an empty forest on the same agent.
    pub(crate) fn sim_clear(&mut self, cx: &mut Context<Self>) {
        self.sim_draft = starbridge_v2::simulate::IntentDraft::new(self.sim_draft.agent);
        self.sim_outcome = None;
        self.sim_commit_banner = None;
        cx.notify();
    }

    /// **SIMULATE the draft** — predict its consequences in a forked throwaway
    /// world (the real executor, live world UNTOUCHED). Stores the [`SimOutcome`]
    /// the panel renders (the predicted post-state + receipt, or the refusal).
    pub(crate) fn sim_run(&mut self, cx: &mut Context<Self>) {
        let outcome = {
            let w = self.world.borrow();
            starbridge_v2::simulate::simulate(&w, &self.sim_draft)
        };
        self.sim_outcome = Some(outcome);
        self.sim_commit_banner = None;
        cx.notify();
    }

    /// **COMMIT the draft for real** — run the IDENTICAL turn on the LIVE world.
    /// Only meaningful after a SIMULATE that predicted a commit; the button is
    /// disabled otherwise. Surfaces the real executor's verdict (which matches the
    /// prediction) + refreshes the image.
    pub(crate) fn sim_commit(&mut self, cx: &mut Context<Self>) {
        // Only commit a draft the prediction said would commit (the panel disables
        // the button otherwise; this guards the keyboard/palette path too).
        let predicted_ok = matches!(
            self.sim_outcome,
            Some(starbridge_v2::simulate::SimOutcome::Predicted { .. })
        );
        if !predicted_ok {
            self.sim_commit_banner =
                Some("SIMULATE first — commit is enabled only after a predicted-commit".into());
            cx.notify();
            return;
        }
        let outcome = {
            let mut w = self.world.borrow_mut();
            starbridge_v2::simulate::commit(&mut w, &self.sim_draft)
        };
        self.sim_commit_banner = Some(match &outcome {
            CommitOutcome::Committed { receipt, events } => format!(
                "COMMITTED for real — {} action(s), {} computrons, {} dynamics event(s). \
                 The prediction held.",
                receipt.action_count,
                receipt.computrons_used,
                events.len()
            ),
            CommitOutcome::Rejected { reason, at_action } => {
                format!("REJECTED by the live executor: {reason} @ {at_action:?}")
            }
            // The world is suspended (meta-debug Suspend gate): the turn was staged,
            // not run, so the prediction is neither confirmed nor refused — it waits
            // on resume. Surface the halt honestly rather than claim an outcome.
            CommitOutcome::Queued { agent } => {
                format!(
                    "QUEUED — world suspended; the staged turn from {} commits on resume",
                    world::short(agent)
                )
            }
        });
        // The committed turn changed the image; also drop the stale prediction (the
        // pre-state it predicted against is now spent).
        self.sim_outcome = None;
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    // --- the CIPHERCLERK action loop (real macaroons) -----------------------
    //
    // These drive the REAL `AgentCipherclerk` via the `cipherclerk` action
    // layer (mint → attenuate → delegate → discharge). The demo acts on the two
    // seeded identities (alice mints/attenuates/delegates; bob receives) and the
    // "dns" service, so the operator can watch the wallet + delegation vault
    // grow and see the discharge verdict.

    pub(crate) fn run_clerk_mint(&mut self, cx: &mut Context<Self>) {
        let out = self.clerk.mint("alice", "dns");
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    pub(crate) fn run_clerk_attenuate(&mut self, cx: &mut Context<Self>) {
        // Confine alice's dns root to read-only with a far-future expiry.
        let out = self
            .clerk
            .attenuate_latest("alice", "dns", "r", Some(4_000_000_000));
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    pub(crate) fn run_clerk_delegate(&mut self, cx: &mut Context<Self>) {
        // Hand a dns/read capability to bob as a real signed envelope.
        let out = self.clerk.delegate_to("alice", "bob", "dns", "r");
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    pub(crate) fn run_clerk_discharge(&mut self, cx: &mut Context<Self>) {
        // Discharge alice's dns token against an atomic 'r' (read) request now.
        // (The macaroon action vocabulary is the atomic letters r/w/c/d/C.)
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        let out = self.clerk.discharge("alice", "dns", "r", now);
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    // --- the A1 EDITOR/BUFFER surface ops (cap-gated edits) ------------------
    //
    // Editing the buffer's text is free (an in-memory doc edit); LANDING it is a
    // cap-gated verified turn — the cockpit presents the WRITE cap and the
    // backing cell's digest advances (a real receipt). A read-only buffer would
    // refuse — the no-amplification rule at the editor.

    /// Type a line into the editor buffer (free, in-memory) — the operator can
    /// watch the doc become DIRTY (its digest now differs from the committed one).
    pub(crate) fn buffer_type_demo(&mut self, cx: &mut Context<Self>) {
        let stamp = self.world.borrow().height();
        self.editor_buffer
            .doc_mut()
            .insert(&format!("edit @ h{stamp}\n"));
        self.last_outcome = Some(
            "buffer: typed a line (in-memory — the doc is now DIRTY until a cap-gated commit)"
                .to_string(),
        );
        self.tab = Tab::Buffer;
        cx.notify();
    }

    /// COMMIT the editor buffer — write its digest into the backing cell through
    /// a REAL verified turn (cap-gated; the cockpit presents the WRITE cap).
    pub(crate) fn buffer_commit(&mut self, cx: &mut Context<Self>) {
        let cap = self.editor_buffer_cap.clone();
        let result = {
            let mut w = self.world.borrow_mut();
            self.editor_buffer.commit(&mut w, &cap)
        };
        self.last_outcome = Some(match result {
            Ok(rev) => format!(
                "buffer: COMMITTED — digest written to the backing cell as a verified turn (revision {rev})"
            ),
            Err(e) => format!("buffer: commit REFUSED — {}", e.explain()),
        });
        self.refresh_cells();
        self.tab = Tab::Buffer;
        cx.notify();
    }

    /// Attempt to COMMIT through a READ-ONLY mirror — the no-amplification rule
    /// firing at the editor. The cockpit narrows its write cap to a read-only
    /// (Signature) mirror via a REAL GrantCapability share, then tries to commit
    /// through it: the buffer-cap gate REFUSES (a read-only buffer cannot write).
    pub(crate) fn buffer_readonly_write_demo(&mut self, cx: &mut Context<Self>) {
        let cap = self.editor_buffer_cap.clone();
        // Narrow to a read-only mirror through the real executor (None → Signature).
        let mirror = match self.shell.share(
            &cap,
            /*peer app*/ 0x4E0,
            dregg_cell::AuthRequired::Signature,
        ) {
            Ok(m) => m,
            Err(e) => {
                self.last_outcome = Some(format!(
                    "buffer: could not make a read-only mirror — {}",
                    shell_err(&e)
                ));
                cx.notify();
                return;
            }
        };
        self.surface_caps.insert(mirror.surface(), mirror.clone());
        // A read-only buffer rendered into the mirror's surface.
        let ro_buffer = BufferCell::new(
            mirror.surface(),
            self.editor_buffer.backing(),
            "scratch.txt (read-only mirror)",
            self.editor_buffer.doc().text(),
        );
        let result = {
            let mut w = self.world.borrow_mut();
            ro_buffer.commit(&mut w, &mirror)
        };
        self.last_outcome = Some(match result {
            Ok(_) => {
                "buffer: read-only write UNEXPECTEDLY committed (should have refused!)".to_string()
            }
            Err(e) => format!(
                "buffer: ⚠ read-only write REFUSED — {} (no-amplification at the editor)",
                e.explain()
            ),
        });
        self.tab = Tab::Buffer;
        cx.notify();
    }

    // --- the A1 TERMINAL surface ops (the ADOS tool-call seam) ---------------
    //
    // A command is cap-gated on the terminal-cell's c-list: an in-mandate target
    // COMMITS (its receipt is the output); an out-of-mandate one REFUSES. This is
    // the agent's Bash confined to its mandate, made a surface.

    /// Run an IN-MANDATE command — the service terminal-cell holds a cap reaching
    /// the user cell, so a transfer to the user COMMITS (its receipt is the output).
    pub(crate) fn terminal_run_in_mandate(&mut self, cx: &mut Context<Self>) {
        let [_treasury, _service, user] = self.anchors;
        let line = {
            let mut w = self.world.borrow_mut();
            self.terminal.run(
                &mut w,
                Command::Transfer {
                    target: user,
                    amount: 100,
                },
            )
        };
        self.last_outcome = Some(match line {
            Ok(l) => format!(
                "terminal: command COMMITTED — {} (receipt is the output)",
                l.result
            ),
            Err(e) => format!("terminal: command REFUSED — {}", e.explain()),
        });
        self.refresh_cells();
        self.tab = Tab::Terminal;
        cx.notify();
    }

    /// Run an OUT-OF-MANDATE command — target a cell the terminal-cell holds NO
    /// cap for; the command cap-gate REFUSES it (the agent's Bash confined). Uses
    /// the treasury (the service holds no cap reaching it).
    pub(crate) fn terminal_run_out_of_mandate(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, _user] = self.anchors;
        let line = {
            let mut w = self.world.borrow_mut();
            self.terminal.run(
                &mut w,
                Command::Transfer {
                    target: treasury,
                    amount: 1,
                },
            )
        };
        self.last_outcome = Some(match line {
            Ok(_) => {
                "terminal: out-of-mandate command UNEXPECTEDLY committed (should have refused!)"
                    .to_string()
            }
            Err(e) => format!(
                "terminal: ⚠ command REFUSED — {} (cap-gate, BEFORE any turn)",
                e.explain()
            ),
        });
        self.tab = Tab::Terminal;
        cx.notify();
    }

    // --- the A2 SWARM surface ops (notify-edge-routed cap-coordination) ------

    /// Swarm action: coordinator EMITS a notify event targeting worker-a.
    /// This is the grounded seam: the emit is a cap-gated turn; the
    /// `NotifyEdge` lands in worker-a's inbox (async, NOT a joint turn).
    /// Swarm layout: service = coordinator (cap to user), user = worker-a.
    pub(crate) fn swarm_coordinator_emit_a(&mut self, cx: &mut Context<Self>) {
        let [_treasury, coord, worker_a] = self.anchors; // service=coord, user=worker-a
        let outcome = {
            let mut w = self.world.borrow_mut();
            self.swarm.run(
                &mut w,
                coord,
                vec![world::emit_event(worker_a, "task/go", vec![])],
            )
        };
        self.last_outcome = Some(match &outcome {
            Ok(ao) => format!(
                "swarm: coordinator emitted task/go → worker-a (receipt {}) — {} notify edge(s) deposited",
                ao.receipt_hash.map(|h| reflect::short_hex(&h)).unwrap_or_default(),
                ao.notify_edges.len(),
            ),
            Err(e) => format!("swarm: REFUSED — {}", e.label()),
        });
        self.refresh_cells();
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// Swarm action: worker-a DRAINS its pending notification (its own async ack turn).
    /// This is a wholly independent turn from the coordinator's emit — different
    /// receipt, different height, different provenance. The async model at work.
    pub(crate) fn swarm_worker_a_drain(&mut self, cx: &mut Context<Self>) {
        let [_treasury, _coord, worker_a] = self.anchors; // user=worker-a
        let outcome = {
            let mut w = self.world.borrow_mut();
            self.swarm.drain_notify(&mut w, worker_a)
        };
        self.last_outcome = Some(match outcome {
            Ok(receipt) => format!(
                "swarm: worker-a DRAINED its notify inbox (ack receipt {}) — async, separate from sender's turn",
                reflect::short_hex(&receipt),
            ),
            Err(e) => format!("swarm: drain REFUSED — {}", e.label()),
        });
        self.refresh_cells();
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// Swarm action: coordinator (service) sends value to worker-a (user) AND emits
    /// a wake to worker-a, in ONE multi-effect turn. One seam, two effects, real receipt.
    /// (worker-b = treasury = unreachable from service; transfer to treasury would REFUSE.)
    pub(crate) fn swarm_coordinator_transfer_and_wake(&mut self, cx: &mut Context<Self>) {
        let [_treasury, coord, worker_a] = self.anchors; // service=coord, user=worker-a
        let outcome = {
            let mut w = self.world.borrow_mut();
            self.swarm.run(
                &mut w,
                coord,
                vec![
                    world::transfer(coord, worker_a, 500),
                    world::emit_event(worker_a, "task/done", vec![]),
                ],
            )
        };
        self.last_outcome = Some(match &outcome {
            Ok(ao) => format!(
                "swarm: coordinator transferred 500 + woke worker-a (receipt {}) — {} notify edge(s)",
                ao.receipt_hash.map(|h| reflect::short_hex(&h)).unwrap_or_default(),
                ao.notify_edges.len(),
            ),
            Err(e) => format!("swarm: REFUSED — {}", e.label()),
        });
        self.refresh_cells();
        self.tab = Tab::Swarm;
        cx.notify();
    }

    // --- the four-surface KILLER DEMO (N5) live driver ----------------------

    /// **Advance the killer demo by ONE frame** — the SWARM-tab "next frame" button.
    /// Each press runs the next step of the headline script (mint → agent turn →
    /// notify → drain → over-grant REFUSAL → over-spend REFUSAL) through the demo's
    /// OWN embedded verified world, appending the frame's render line to the strip.
    /// When the script is complete, the button reports it (and the operator can
    /// reset to replay).
    /// The killer demo, BOOTED ON FIRST ACCESS. Building it constructs a metered
    /// verified world + deploys the mint factory; that (and its slow proof-bearing
    /// turns) is exactly what we keep off the first-paint path — so the demo is
    /// `None` until the operator first reaches the SWARM tab or a killer-demo verb,
    /// at which point this materializes it. Every later access reuses the same one.
    pub(crate) fn killer_demo(&mut self) -> &mut HeadlineDemo {
        self.killer_demo.get_or_insert_with(HeadlineDemo::boot)
    }

    pub(crate) fn killer_demo_advance(&mut self, cx: &mut Context<Self>) {
        if self.killer_demo().is_complete() {
            self.last_outcome =
                Some("killer demo: the script is complete — reset to replay it.".to_string());
        } else if let Some(line) = self.killer_demo().advance() {
            self.killer_demo_lines.push(line.clone());
            // The trimmed first line of the frame, for the outcome banner.
            let banner = line.lines().next().unwrap_or(&line).trim().to_string();
            self.last_outcome = Some(format!("killer demo: {banner}"));
        }
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// **Run the WHOLE killer demo at once** — the SWARM-tab "run all" button. Drives
    /// the full four-frame + dual-refusal script and reports the verdict (the
    /// `--headless` self-check, in the cockpit). Captures every frame line into the
    /// strip so the operator can read the four frames + both refusals.
    pub(crate) fn killer_demo_run_all(&mut self, cx: &mut Context<Self>) {
        // Reset to a fresh world so "run all" is a clean replay from frame 0.
        self.killer_demo().reset();
        self.killer_demo_lines.clear();
        while let Some(line) = self.killer_demo().advance() {
            self.killer_demo_lines.push(line);
            if self.killer_demo().is_complete() {
                break;
            }
        }
        self.last_outcome = Some(if self.killer_demo().contract_holds() {
            "killer demo ✓ — four frames committed, two distinct handoff receipts, \
             BOTH refusals fired fail-closed. (pg step 5 deferred.)"
                .to_string()
        } else {
            "killer demo ✗ — the headline contract did NOT hold (a regression).".to_string()
        });
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// **The pixel-layer OVER-SHARE refusal** — the SWARM-tab "⚠ over-share at the
    /// glass" button: the THIRD register of the same no-amplification law. Opens the
    /// demo's minted budget cell as a cap-confined surface (in the cockpit's live
    /// shell), shares it READ-ONLY, then tries to promote it to WRITABLE — the real
    /// executor REJECTS the widening (`DelegationDenied`), surfaced as `⚠ over-share`
    /// at the PIXEL layer. Requires the demo to have MINTED its token cell (frame 1).
    pub(crate) fn killer_demo_over_share(&mut self, cx: &mut Context<Self>) {
        // Ensure the demo is booted, then drive it. We can't go through the
        // `killer_demo()` accessor here (it would hold a &mut borrow of `self`
        // across the `&mut self.shell` arg); boot it, then reach the now-`Some`
        // field directly so `shell` is a disjoint borrow.
        let _ = self.killer_demo();
        let demo = self.killer_demo.as_mut().expect("just booted");
        let result = demo.refuse_over_share(&mut self.shell);
        let line = match result {
            Ok(reason) => format!("killer demo: {reason}"),
            Err(why) => format!("killer demo: over-share path — {why}"),
        };
        self.killer_demo_lines.push(line.clone());
        self.last_outcome = Some(line);
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// **Reset the killer demo** to a fresh world at frame 0 (the SWARM-tab "reset"
    /// button) so the operator can replay the script from the start.
    pub(crate) fn killer_demo_reset(&mut self, cx: &mut Context<Self>) {
        self.killer_demo().reset();
        self.killer_demo_lines.clear();
        self.last_outcome = Some("killer demo: reset to frame 0 — ready to replay.".to_string());
        self.tab = Tab::Swarm;
        cx.notify();
    }
}
