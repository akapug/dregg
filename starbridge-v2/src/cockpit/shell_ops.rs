//! Replay scrubber + debugger retarget + the cap-first SHELL window ops (open/focus/close/share/present/overpaint/input-steal).

use super::*;

impl Cockpit {
    // --- replay scrubber + debugger retarget (palette-drivable) -------------

    pub(crate) fn replay_step_back(&mut self, cx: &mut Context<Self>) {
        self.replay_cursor = self.replay_cursor.saturating_sub(1);
        cx.notify();
    }

    pub(crate) fn replay_step_forward(&mut self, cx: &mut Context<Self>) {
        let len = self.world.borrow().recorded_turns().len();
        self.replay_cursor = (self.replay_cursor + 1).min(len);
        cx.notify();
    }

    pub(crate) fn replay_to_genesis(&mut self, cx: &mut Context<Self>) {
        self.replay_cursor = 0;
        cx.notify();
    }

    pub(crate) fn replay_to_head(&mut self, cx: &mut Context<Self>) {
        self.replay_cursor = self.world.borrow().recorded_turns().len();
        cx.notify();
    }

    /// Pin a what-if FORK at the current scrubber cursor: re-run the cursor's
    /// real turn as the "alternate" (a no-op divergence baseline) so the panel
    /// shows the fork machinery live. (A richer alt-turn editor is a follow-on;
    /// this proves the verified-fork path through the palette.)
    pub(crate) fn replay_fork_here(&mut self, cx: &mut Context<Self>) {
        let w = self.world.borrow();
        let history = w.recorded_turns();
        let k = self.replay_cursor.min(history.len());
        // Use the treasury anchor for a representative alternate transfer.
        let [treasury, _service, user] = self.anchors;
        // A small alternate transfer the branch point can apply.
        let alt = world::bare_turn(
            treasury,
            history
                .replay_to(k)
                .ok()
                .and_then(|l| l.get(&treasury).map(|c| c.state.nonce()))
                .unwrap_or(0),
            vec![world::transfer(treasury, user, 1)],
        );
        match history.fork_at(k, alt) {
            Ok(fork) => {
                drop(w);
                self.replay_fork = Some(fork);
            }
            Err(_) => {
                drop(w);
                self.replay_fork = None;
            }
        }
        cx.notify();
    }

    pub(crate) fn replay_clear_fork(&mut self, cx: &mut Context<Self>) {
        self.replay_fork = None;
        cx.notify();
    }

    /// Retarget the debugger to a transfer FROM the currently-selected cell (so
    /// the operator can step any cell's outgoing turn, not just the seeded one).
    pub(crate) fn debug_retarget_selected(&mut self, cx: &mut Context<Self>) {
        if let Selection::Cell(id) = self.selection {
            let [_t, _s, user] = self.anchors;
            // Target = the selected cell; pay a token amount to `user` so there
            // is an effect to step (the debugger re-executes faithfully).
            let to = if user == id { self.anchors[0] } else { user };
            self.debug_turn = self.world.borrow().turn(id, vec![world::transfer(id, to, 100)]);
            self.tab = Tab::Debugger;
            cx.notify();
        } else {
            self.last_outcome = Some("debugger retarget: select a cell first".to_string());
            cx.notify();
        }
    }

    // --- the cap-first SHELL ops (each routes through the CAP-GATED shell) ---
    //
    // The cockpit IS the operator: it holds every surface's cap in `surface_caps`.
    // But it can ONLY drive a surface by presenting that cap to the shell's
    // gated API — so the window manager's ocap discipline is demonstrated, not
    // bypassed. (A window op with no held cap simply has nothing to present and
    // is refused — exactly the no-ambient-authority property.)

    /// Open the currently-selected cell as a new cap-confined SURFACE. The shell
    /// mints the surface's cap; the cockpit files it in its vault. (Opening a
    /// cell that isn't selected falls back to the service anchor so the verb is
    /// always live.)
    pub(crate) fn shell_open_selected(&mut self, cx: &mut Context<Self>) {
        let cell = match self.selection {
            Selection::Cell(id) => id,
            _ => self.anchors[1], // service, as a sensible default
        };
        let short = reflect::short_hex(cell.as_bytes());
        let cap = self.shell.open_cell_view(cell, format!("cell {short}"));
        self.surface_caps.insert(cap.surface(), cap);
        self.last_outcome = Some(format!("shell: opened surface for cell {short} (cap minted)"));
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Focus + raise the front-most NON-console surface (a cap-gated op). The
    /// cockpit presents the held cap; the shell authenticates it before raising.
    pub(crate) fn shell_focus_front(&mut self, cx: &mut Context<Self>) {
        // Find the current front non-console surface in the live scene.
        let front = {
            let w = self.world.borrow();
            let scene = self.shell.compose(&w);
            scene
                .items
                .iter()
                .rev()
                .find(|it| !it.surface.is_console())
                .map(|it| it.surface.id())
        };
        if let Some(id) = front {
            self.with_cap(id, |shell, cap| shell.focus(cap), cx, "focus");
        } else {
            self.last_outcome = Some("shell: no cell surface to focus".to_string());
            cx.notify();
        }
    }

    /// Close the focused surface (cap-gated; the console is protected, so closing
    /// it is refused — a refusal the operator can watch). The cap is dropped when
    /// the surface closes.
    pub(crate) fn shell_close_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to close".to_string());
            cx.notify();
            return;
        };
        let outcome = match self.surface_caps.get(&id) {
            Some(cap) => self.shell.close(cap),
            None => Err(starbridge_v2::shell::ShellError::Unauthorized),
        };
        match outcome {
            Ok(()) => {
                self.surface_caps.remove(&id);
                self.last_outcome = Some("shell: closed the focused surface (cap retired)".to_string());
            }
            Err(e) => {
                self.last_outcome = Some(format!("shell: close REFUSED — {}", shell_err(&e)));
            }
        }
        cx.notify();
    }

    /// Minimize the focused surface (cap-gated).
    pub(crate) fn shell_minimize_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to minimize".to_string());
            cx.notify();
            return;
        };
        self.with_cap(id, |shell, cap| shell.set_minimized(cap, true), cx, "minimize");
    }

    /// SHARE the focused window with another app — an ATTENUATING (read-only
    /// mirror) hand-off through a REAL `Effect::GrantCapability` turn on the
    /// firmament executor. Commits; the recipient's narrowed window cap is filed
    /// in the vault (so its shared window is drivable), demonstrating "a window =
    /// a firmament cap" delegated through the real executor — granted ⊆ held.
    pub(crate) fn shell_share_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to share".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        // Hand a READ-ONLY mirror (Signature ⊆ the held rights) to a peer app.
        match self.shell.share(&cap, /*peer app*/ 0x5EED, dregg_cell::AuthRequired::Signature) {
            Ok(shared) => {
                self.surface_caps.insert(shared.surface(), shared);
                self.last_outcome = Some(
                    "shell: shared a read-only window mirror (real GrantCapability turn committed)"
                        .to_string(),
                );
            }
            Err(e) => {
                self.last_outcome = Some(format!("shell: share REFUSED — {}", shell_err(&e)));
            }
        }
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// ⚠ Attempt to OVER-SHARE the focused window — the no-amplification
    /// guarantee firing at the desktop. We first share a read-only mirror to a
    /// peer (commits), then have THAT peer try to re-share its window with WIDER
    /// authority than it holds; the REAL executor REJECTS the widening
    /// (`DelegationDenied`). This is the window-manager analogue of the composer's
    /// ⚠ over-grant verb — a refusal the operator can watch.
    pub(crate) fn shell_overshare_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to over-share".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        // Step 1: legitimately hand a peer a read-only mirror (commits).
        let mirror = match self.shell.share(&cap, /*peer*/ 0xA11CE, dregg_cell::AuthRequired::Signature) {
            Ok(m) => m,
            Err(e) => {
                self.last_outcome = Some(format!("shell: setup share failed — {}", shell_err(&e)));
                cx.notify();
                return;
            }
        };
        self.surface_caps.insert(mirror.surface(), mirror.clone());
        // Step 2: that read-only-mirror peer tries to OVER-SHARE (Signature →
        // Either is WIDER). The real executor REJECTS it — watch it fire.
        match self.shell.share(&mirror, /*victim*/ 0xBAD, dregg_cell::AuthRequired::Either) {
            Ok(_) => {
                self.last_outcome =
                    Some("shell: over-share UNEXPECTEDLY committed (should have rejected!)".to_string());
            }
            Err(e) => {
                self.last_outcome = Some(format!(
                    "shell: ⚠ over-share REJECTED by the real executor — {} (no-amplification on glass)",
                    shell_err(&e)
                ));
            }
        }
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Cycle the compositor layout (float → tile → stack). A shell-global op (it
    /// rearranges the whole scene), so it is not surface-cap-scoped.
    pub(crate) fn shell_cycle_layout(&mut self, cx: &mut Context<Self>) {
        self.shell.cycle_layout();
        self.last_outcome = Some(format!("shell: layout → {}", self.shell.layout().label()));
        self.tab = Tab::Shell;
        cx.notify();
    }

    // --- THE VERIFIED-SCENE teaching moments (T1/T2/T3 at the pixel layer) ---
    //
    // These exercise the compositor's `present()` path so the operator can WATCH
    // the scene-authority teeth bite — exactly the over-share teaching moment,
    // one hop out (the no-amplification guarantee firing at the GLASS).

    /// PRESENT honestly from the FOCUSED surface: paint its own region, claim
    /// focus (it IS the focus holder), advance the frame. COMMITS — the scene
    /// the operator sees is the genuine projection (the commit polarity).
    pub(crate) fn shell_present_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to present".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        let region = id.region();
        let digest = self.next_frame_digest();
        let w = self.world.borrow();
        match self.shell.present(&cap, &w, vec![region], /*claims_focus*/ true, digest) {
            Ok(commit) => {
                self.last_outcome = Some(format!(
                    "shell: present COMMITTED — frame {} on the focused surface (genuine projection)",
                    commit.digest
                ));
            }
            Err(e) => {
                self.last_outcome = Some(format!("shell: present REFUSED — {}", shell_err(&e)));
            }
        }
        drop(w);
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Attempt an OVERPAINT: the focused surface tries to paint the FRONT OTHER
    /// surface's region — the T1 non-overlap tooth REFUSES it (a cell cannot
    /// paint a region another cell owns). The pixel-layer over-grant.
    pub(crate) fn shell_overpaint_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to present".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        // Compute the frame digest BEFORE borrowing the world (the digest
        // counter is `&mut self`; the present below holds an immutable borrow).
        let digest = self.next_frame_digest();
        // Find ANOTHER surface's region to overpaint (a genuinely-distinct attack
        // — a real second surface's region, not a malformed one).
        let w = self.world.borrow();
        let victim_region = self
            .shell
            .compose_scene(&w)
            .surfaces
            .iter()
            .find(|s| Some(s.owner) != self.shell.focused_cell())
            .and_then(|s| s.regions.first().copied());
        let Some(victim_region) = victim_region else {
            drop(w);
            self.last_outcome =
                Some("shell: need a second surface to demo an overpaint".to_string());
            cx.notify();
            return;
        };
        match self.shell.present(&cap, &w, vec![victim_region], true, digest) {
            Ok(_) => {
                self.last_outcome = Some(
                    "shell: overpaint UNEXPECTEDLY committed (should have rejected!)".to_string(),
                );
            }
            Err(e) => {
                self.last_outcome = Some(format!(
                    "shell: ⚠ overpaint REFUSED by the verified scene — {} (T1 no-amplification on glass)",
                    shell_err(&e)
                ));
            }
        }
        drop(w);
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Attempt an INPUT-STEAL: a NON-focused surface presents its own region but
    /// asserts input focus to steal the keystroke — the T3 input-routing tooth
    /// REFUSES it (input routes only to the focus holder).
    pub(crate) fn shell_input_steal(&mut self, cx: &mut Context<Self>) {
        // Compute the frame digest BEFORE borrowing the world (the digest counter
        // is `&mut self`; the present below holds an immutable borrow of it).
        let digest = self.next_frame_digest();
        // Find a non-focused, non-console surface to play the thief.
        let w = self.world.borrow();
        let thief = self
            .shell
            .surfaces_in_z_order()
            .into_iter()
            .find(|s| !s.is_console() && Some(s.id()) != self.shell.focused())
            .map(|s| s.id());
        let Some(thief) = thief else {
            drop(w);
            self.last_outcome =
                Some("shell: need a second surface to demo an input-steal".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&thief).cloned() else {
            drop(w);
            self.last_outcome = Some("shell: no held cap for the thief surface".to_string());
            cx.notify();
            return;
        };
        let region = thief.region();
        match self.shell.present(&cap, &w, vec![region], /*claims_focus*/ true, digest) {
            Ok(_) => {
                self.last_outcome = Some(
                    "shell: input-steal UNEXPECTEDLY committed (should have rejected!)".to_string(),
                );
            }
            Err(e) => {
                self.last_outcome = Some(format!(
                    "shell: ⚠ input-steal REFUSED by the verified scene — {} (T3 only the focus holder gets input)",
                    shell_err(&e)
                ));
            }
        }
        drop(w);
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// A monotonic frame digest for the present teaching moments (so every
    /// present genuinely advances the frame — the Lean `new ≠ old` leg).
    pub(crate) fn next_frame_digest(&mut self) -> u64 {
        self.frame_seq = self.frame_seq.wrapping_add(1);
        0xF00D_0000 + self.frame_seq
    }

    /// Focus a surface by id when the operator clicks it in the scene. The click
    /// is only a HINT — the cockpit then presents the held cap, and the shell's
    /// cap-gated `focus` is the actual authority (no held cap ⇒ no focus).
    pub(crate) fn shell_click_surface(&mut self, id: SurfaceId, cx: &mut Context<Self>) {
        self.with_cap(id, |shell, cap| shell.focus(cap), cx, "focus");
    }

    /// Drive a cap-gated shell op for surface `id`: look up the held cap, present
    /// it to the shell, and surface the verdict. Centralizes the "present the
    /// cap or it's refused" discipline so every op goes through it.
    pub(crate) fn with_cap<F>(&mut self, id: SurfaceId, op: F, cx: &mut Context<Self>, what: &str)
    where
        F: FnOnce(&mut Shell, &SurfaceCapability) -> Result<(), starbridge_v2::shell::ShellError>,
    {
        let result = match self.surface_caps.get(&id) {
            Some(cap) => op(&mut self.shell, cap),
            // No held cap for this surface → nothing to present → refused. This
            // IS the no-ambient-authority property (you can't act without a cap).
            None => Err(starbridge_v2::shell::ShellError::Unauthorized),
        };
        if let Err(e) = result {
            self.last_outcome = Some(format!("shell: {what} REFUSED — {}", shell_err(&e)));
        }
        cx.notify();
    }

}
