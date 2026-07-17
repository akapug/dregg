//! THE CAP-GATED MULTI-SURFACE COMPOSITOR — the verified-scene discipline, on glass.
//!
//! This is the Rust realization of the Lean `Dregg2.Apps.Compositor` `AppSpec`
//! (`metatheory/Dregg2/Apps/Compositor.lean`) — the same `Scene` / `Surface`
//! tuple and the SAME three scene-authority teeth, enforced at the pixel layer
//! the shell composites. `.docs-history-noclaude/DREGG-DESKTOP-OS.md` §5 ("the verified scene")
//! casts output-integrity as *unfoolability applied to the display path*: a
//! light client that checks `verify root = true` cannot be fooled by the pale
//! ghost lying about protocol state, and the compositor asks the SAME question
//! one hop out — **can the human at the glass be fooled?** The pale ghost on the
//! display is a UI that paints another cell's region, labels a window as a cell
//! it is not, or steals the keystroke meant for the focused cell. The three
//! teeth refuse each:
//!
//!   * **T1 NON-OVERLAP** — a surface composites ONLY its own cap-authorized
//!     region-set; an overpaint of another surface's region is REFUSED. This is
//!     `granted ⊆ held` with `Rights = region-set`, on the SAME `is_attenuation`
//!     direction the firmament uses for window caps — the no-amplification
//!     guarantee firing at the PIXEL layer (cf. the cockpit's over-grant /
//!     over-share teaching moments). [`Compositor::t1_non_overlap`].
//!   * **T2 LABEL-BINDING** — every surface's trusted-path identity label is a
//!     FUNCTION of `(owner, source_state_root)`, read by the SHELL from the live
//!     world ledger / the owning cell's authority lineage, NEVER the surface's
//!     self-description (the §5 T2 discipline). A present declaring a label that
//!     is not the genuine owner-binding is REFUSED. [`Compositor::t2_label_bound`].
//!   * **T3 FOCUS-EXCLUSIVITY** — at-most-one focused surface; input routes ONLY
//!     to the focused one; the shell enforces it. A double-focus scene, or a
//!     present that delivers input to a non-focused surface, is REFUSED.
//!     [`Compositor::t3_focus_exclusive`] / [`Compositor::t3_input_routed`].
//!
//! `present()` folds the WHOLE scene authority into a single admission decision
//! (exactly the Lean `sceneAdmit` conjunction) BEFORE it touches the frame: a
//! present that any tooth forbids returns [`PresentError`] and changes NOTHING
//! (fail-closed), mirroring the Lean executor returning `none`. A committed
//! present advances the frame digest and is recorded in the compositor's frame
//! log (the analogue of the on-ledger commit + the `state_root` tooth).
//!
//! This module is gpui-FREE and `cargo test`-able. The scene it composites is a
//! pure description (ordered surfaces, each owner/regions/z-layer/focus); the
//! cockpit maps it onto gpui in z-order and routes input through the focus gate.
//! The shell ([`crate::shell`]) owns the firmament cap-fabric the *window-ops*
//! authenticate against; the compositor enforces the *scene authority* on top —
//! two distinct gates, faithful to §5 ("the scene authority is a SEPARATE gate
//! the executor enforces on top" of the surface cap).

use dregg_cell::CellId;

/// An opaque region (rectangle / tile) identity. The compositor's regions
/// partition the glass; a surface owns a SET of regions; two surfaces' region
/// sets must be disjoint (T1 non-overlap). Mirrors the Lean `RegionId := Nat`.
pub type RegionId = u64;

/// The genuine surface label the compositor renders for a surface owned by
/// `owner` projecting state-root `root` — a pure function of the authority
/// lineage (the T2 binding). The owning APP never supplies this; the SHELL
/// computes it from cell state, so a window cannot label itself as a cell it is
/// not. Mirrors the Lean `labelOf owner root := owner * 1000003 + root`, here a
/// 128-bit mix over the cell id's leading bytes + the state-root so distinct
/// `(owner, root)` pairs give distinct labels (the binding is renderer-agnostic;
/// the real compositor uses Poseidon2 over the structured provenance lattice —
/// the DISCIPLINE is what T2 enforces, not this particular function).
pub fn label_of(owner: &CellId, source_state_root: u64) -> u128 {
    let b = owner.as_bytes();
    // Fold the 32-byte owner id down to a u64 (a deterministic digest), then mix
    // with the source root — an injective-enough binding for the executable
    // model (a different owner OR a different root ⇒ a different label).
    let mut owner_acc: u64 = 0xcbf2_9ce4_8422_2325; // FNV-1a offset basis
    for &byte in b {
        owner_acc ^= byte as u64;
        owner_acc = owner_acc.wrapping_mul(0x0000_0100_0000_01B3); // FNV prime
    }
    (owner_acc as u128) * 1_000_003 + source_state_root as u128
}

/// One surface in the compositor's scene graph — the Lean `Surface` tuple
/// `(owningCellId, regionRect, contentDigest, sourceStateRoot, zLayer,
/// focusFlag)`, made concrete. The compositor reads these (it does NOT trust the
/// app to supply the label or the owner — those come from the shell's view of
/// the live world).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompositedSurface {
    /// The cell that owns this surface — the authority lineage the compositor
    /// reads from cell state (NOT app-supplied). The T2 label binds to this.
    pub owner: CellId,
    /// The set of regions (tiles) this surface occupies. Non-overlap (T1) means
    /// these are pairwise-disjoint across surfaces, and a present by `owner` may
    /// target ONLY regions in this set (`granted ⊆ held`).
    pub regions: Vec<RegionId>,
    /// The content digest currently shown in this surface (the projection of
    /// `source_state_root`). Advanced by a committed `present()`.
    pub content_digest: u64,
    /// The cell state-root this content is a genuine projection of (the
    /// light-client-checkable bind — a present declares the root it projects,
    /// and T2 binds the label to it).
    pub source_state_root: u64,
    /// The z-layer (stacking order); the compositor paints back-to-front. The
    /// trusted-path overlay (§5 SAK) lives at a z-layer no cell holds a cap to.
    pub z_layer: i64,
    /// Whether this surface currently holds input focus (T3: at-most-one across
    /// the whole scene; input routes only here).
    pub focus_flag: bool,
}

impl CompositedSurface {
    /// Whether this surface owns `region` (the T1 region-set membership).
    pub fn owns_region(&self, region: RegionId) -> bool {
        self.regions.contains(&region)
    }
}

/// The compositor's scene — the ordered list of surfaces. THIS is the verified
/// dregg cell's state (Lean §5: "Its state IS the scene graph — an ordered list
/// of surfaces"). The compositor decides every admission from the scene it reads.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CompositorScene {
    /// Surfaces in paint order (back-to-front; the front-most is last).
    pub surfaces: Vec<CompositedSurface>,
}

/// What a `present()` call presents — the Lean `Present` tuple. The
/// `content_digest` transition `old → new` is the scalar frame advance; the rest
/// is the scene authority the compositor folds in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Present {
    /// The region-set this present writes (T1: must be `⊆` the presenter's owned
    /// regions AND disjoint from every foreign surface's regions).
    pub target: Vec<RegionId>,
    /// The state-root the presented content is a projection of (T2: binds the
    /// label; also the root a light client can check the content against).
    pub source_state_root: u64,
    /// The label the present declares (T2: must equal `label_of(presenter,
    /// source_state_root)` — the genuine owner-binding the SHELL computes).
    pub declared_label: u128,
    /// Whether this present asserts input focus (T3: only the scene's unique
    /// focus holder may — delivering input elsewhere is keystroke theft).
    pub claims_focus: bool,
    /// The new content digest this present commits for its region (the frame
    /// advance; must differ from the current digest — a present changes the frame).
    pub new_digest: u64,
}

/// Why a `present()` was REFUSED by the compositor's scene authority. Each
/// variant is a tooth of the Lean `*_rejected` theorems (`present_overpaint_
/// rejected` / `present_label_spoof_rejected` / `present_double_focus_rejected`
/// / `present_input_misroute_rejected`). A refusal changes NOTHING (fail-closed,
/// the analogue of the Lean executor returning `none`); the cockpit surfaces it
/// as a teaching moment, exactly like the composer's ⚠ over-grant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PresentError {
    /// **T1** — the present overpaints: its target region-set is NOT `⊆` the
    /// presenter's owned regions, OR it overlaps a region another surface owns.
    /// A cell cannot paint a region another cell holds (no-amplification at the
    /// pixel layer). Carries the offending region(s) for the operator log.
    Overpaint { offending: Vec<RegionId> },
    /// **T2** — the present's declared label is NOT the genuine owner-binding
    /// (`declared_label ≠ label_of(presenter, source_state_root)`). The pale
    /// ghost cannot paint a window labelled as a cell it is not.
    LabelSpoof { declared: u128, genuine: u128 },
    /// **T3 (input)** — the present asserts input focus but the presenter is NOT
    /// the scene's unique focus holder. Input routes only to the focused
    /// surface; a cell cannot steal the keystroke meant for another.
    InputMisroute { focus_holder: Option<CellId> },
    /// **T3 (scene)** — the scene already has TWO+ focus flags (ambiguous input);
    /// no present can commit into a scene that routes input ambiguously.
    DoubleFocus { focus_count: usize },
    /// The presenter does not own a surface in the scene at all (it cannot
    /// present against a scene it has no surface in).
    NoSurface,
    /// The present does not advance the frame (`new_digest == current`); a
    /// present must genuinely change the frame (the Lean `new ≠ old` leg).
    NoFrameAdvance,
}

impl PresentError {
    /// A short operator-legible label (the tooth that bit).
    pub fn tooth(&self) -> &'static str {
        match self {
            PresentError::Overpaint { .. } => "T1 overpaint",
            PresentError::LabelSpoof { .. } => "T2 label-spoof",
            PresentError::InputMisroute { .. } => "T3 input-misroute",
            PresentError::DoubleFocus { .. } => "T3 double-focus",
            PresentError::NoSurface => "no surface",
            PresentError::NoFrameAdvance => "no frame advance",
        }
    }

    /// A one-line human explanation (the cockpit shows this as the refusal
    /// reason — the anti-ghost tooth, surfaced).
    pub fn explain(&self) -> String {
        match self {
            PresentError::Overpaint { offending } => format!(
                "overpaint REFUSED — region(s) {offending:?} are not in the presenter's \
                 cap-authorized set (granted ⊆ held fails at the pixel layer)"
            ),
            PresentError::LabelSpoof { declared, genuine } => format!(
                "label-spoof REFUSED — declared label {declared} ≠ the genuine owner-binding \
                 {genuine} (the label is the SHELL's, not the app's)"
            ),
            PresentError::InputMisroute { focus_holder } => format!(
                "input-misroute REFUSED — the presenter is not the focus holder ({}); input \
                 routes only to the focused surface",
                focus_holder
                    .as_ref()
                    .map(|c| crate::reflect::short_hex(c.as_bytes()))
                    .unwrap_or_else(|| "none".to_string())
            ),
            PresentError::DoubleFocus { focus_count } => format!(
                "double-focus REFUSED — the scene has {focus_count} focus flags (ambiguous \
                 input); at-most-one is load-bearing"
            ),
            PresentError::NoSurface => {
                "REFUSED — the presenter owns no surface in the scene".to_string()
            }
            PresentError::NoFrameAdvance => {
                "REFUSED — the present does not advance the frame digest".to_string()
            }
        }
    }
}

/// One committed present in the compositor's frame log — the analogue of an
/// on-ledger receipt (Lean §10 "the present recorded on-ledger"). The log is the
/// provenance of the scene: every genuine frame advance is recorded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrameCommit {
    /// The presenter that advanced the frame.
    pub presenter: CellId,
    /// The region-set it painted (all `⊆` its owned set, disjoint from foreign).
    pub regions: Vec<RegionId>,
    /// The content digest it committed (the new frame).
    pub digest: u64,
    /// The state-root the content projects (the light-client bind).
    pub source_state_root: u64,
    /// The genuine owner-label bound to this frame (T2).
    pub label: u128,
}

/// THE CAP-GATED MULTI-SURFACE COMPOSITOR. Holds the scene (ordered surfaces
/// with their region ownership + focus) and the frame log, and enforces the
/// three scene-authority teeth on every `present()`. gpui-free; the cockpit
/// composites the scene in z-order and routes input through the focus gate.
///
/// The compositor mediates AUTHORITY over the scene — it never moves value and
/// never mints a capability (the Lean `present_conserves` / `present_no_amplify`
/// keystones). It is a SEPARATE gate from the shell's window-cap fabric: the
/// shell decides who may *drive a window*; the compositor decides what a surface
/// may *paint / where input goes*.
#[derive(Clone, Debug, Default)]
pub struct Compositor {
    scene: CompositorScene,
    /// The append-only frame log (committed presents, in order) — the scene's
    /// provenance. A refused present never appears here (fail-closed).
    frames: Vec<FrameCommit>,
}

impl Compositor {
    /// A fresh compositor with an empty scene and no committed frames.
    pub fn new() -> Self {
        Compositor {
            scene: CompositorScene::default(),
            frames: Vec::new(),
        }
    }

    /// Replace the whole scene (the shell composes it each frame from its owned
    /// surfaces + the live world). The compositor then enforces the teeth
    /// against THIS scene. The scene is the closed-over authority of §4 — the
    /// region→owner map, the focus holder, every surface's region-set.
    pub fn set_scene(&mut self, scene: CompositorScene) {
        self.scene = scene;
    }

    /// The current scene (read-only — the cockpit paints this in z-order).
    pub fn scene(&self) -> &CompositorScene {
        &self.scene
    }

    /// The surfaces in paint order (back-to-front), already z-sorted. The
    /// cockpit composites these in this order; the front-most paints last.
    pub fn surfaces_in_z_order(&self) -> Vec<&CompositedSurface> {
        let mut v: Vec<&CompositedSurface> = self.scene.surfaces.iter().collect();
        v.sort_by_key(|s| s.z_layer);
        v
    }

    /// The committed frame log (the scene's provenance — every genuine present).
    pub fn frames(&self) -> &[FrameCommit] {
        &self.frames
    }

    // --- the three scene-authority teeth (decidable, fail-closed) ------------
    //
    // These mirror the Lean `t1NonOverlap` / `t2LabelBound` / `t3FocusExclusive`
    // / `t3InputRouted` predicates EXACTLY — same shape, same fail-closed sense.

    /// **T1 NON-OVERLAP.** Is a present by `presenter` targeting `target`
    /// T1-admissible? Iff (a) `presenter` owns a surface AND `target` ⊆ its
    /// owned region-set (`granted ⊆ held`), AND (b) `target` is disjoint from
    /// EVERY foreign surface's regions (no overpaint of a region another cell
    /// owns). Mirrors the Lean `t1NonOverlap sc presenter target`.
    pub fn t1_non_overlap(&self, presenter: &CellId, target: &[RegionId]) -> bool {
        // (a) the presenter owns a surface whose region-set covers `target`:
        let owns_all = self
            .scene
            .surfaces
            .iter()
            .any(|s| &s.owner == presenter && target.iter().all(|r| s.owns_region(*r)));
        if !owns_all {
            return false;
        }
        // (b) `target` is disjoint from every FOREIGN surface's regions:
        self.scene
            .surfaces
            .iter()
            .all(|s| &s.owner == presenter || target.iter().all(|r| !s.owns_region(*r)))
    }

    /// The specific regions of a present that would overpaint (for the refusal
    /// reason): the target regions the presenter does not own, plus any that
    /// collide with a foreign surface. Empty iff T1 holds.
    fn overpaint_regions(&self, presenter: &CellId, target: &[RegionId]) -> Vec<RegionId> {
        let owned: Vec<RegionId> = self
            .scene
            .surfaces
            .iter()
            .filter(|s| &s.owner == presenter)
            .flat_map(|s| s.regions.iter().copied())
            .collect();
        let foreign: Vec<RegionId> = self
            .scene
            .surfaces
            .iter()
            .filter(|s| &s.owner != presenter)
            .flat_map(|s| s.regions.iter().copied())
            .collect();
        target
            .iter()
            .copied()
            .filter(|r| !owned.contains(r) || foreign.contains(r))
            .collect()
    }

    /// **T2 LABEL-BINDING.** Is a present declaring `declared_label` while
    /// projecting `source_state_root`, by `presenter`, T2-admissible? Iff
    /// `declared_label == label_of(presenter, source_state_root)` — the label is
    /// the genuine owner-binding the SHELL computes, not an app-chosen one.
    /// Mirrors the Lean `t2LabelBound presenter sourceStateRoot declaredLabel`.
    pub fn t2_label_bound(
        &self,
        presenter: &CellId,
        source_state_root: u64,
        declared_label: u128,
    ) -> bool {
        declared_label == label_of(presenter, source_state_root)
    }

    /// **T3 FOCUS-EXCLUSIVITY (scene).** Is the scene T3-admissible? Iff
    /// AT-MOST-ONE surface holds `focus_flag` (`focus_count ≤ 1`). Mirrors the
    /// Lean `t3FocusExclusive sc` / `countFocus sc ≤ 1`.
    pub fn t3_focus_exclusive(&self) -> bool {
        self.focus_count() <= 1
    }

    /// The number of focused surfaces (Lean `countFocus`). At-most-one is the
    /// T3 invariant; two is an ambiguous-input scene.
    pub fn focus_count(&self) -> usize {
        self.scene.surfaces.iter().filter(|s| s.focus_flag).count()
    }

    /// The unique focus holder (the owner of the focused surface), if any. Input
    /// routes ONLY here. Mirrors the Lean `focusHolder sc`.
    pub fn focus_holder(&self) -> Option<CellId> {
        self.scene
            .surfaces
            .iter()
            .find(|s| s.focus_flag)
            .map(|s| s.owner)
    }

    /// **T3 INPUT-ROUTING.** Is a present that may assert focus
    /// (`claims_focus`) input-route-admissible? When it asserts focus, the
    /// presenter MUST be the scene's unique focus holder; a non-input present
    /// (`claims_focus == false`) is vacuously routed. Mirrors the Lean
    /// `t3InputRouted sc presenter claimsFocus`.
    pub fn t3_input_routed(&self, presenter: &CellId, claims_focus: bool) -> bool {
        !claims_focus || self.focus_holder().as_ref() == Some(presenter)
    }

    /// **THE FOLDED SCENE ADMISSION** — does the scene authority admit this
    /// present? The conjunction T1 ∧ T2 ∧ T3 (non-overlap ∧ label-bound ∧
    /// focus-exclusive ∧ input-routed) AND a genuine frame advance, computed
    /// from the closed-over scene. Returns `Ok(())` if admitted, else the
    /// specific tooth that bit. Mirrors the Lean `sceneAdmit sc presenter p old
    /// new` (the whole scene authority folded to the scalar boundary).
    pub fn scene_admit(&self, presenter: &CellId, p: &Present) -> Result<(), PresentError> {
        // The current frame digest the presenter's surface shows (the `old`).
        let current = self
            .scene
            .surfaces
            .iter()
            .find(|s| &s.owner == presenter)
            .map(|s| s.content_digest);
        let Some(current) = current else {
            return Err(PresentError::NoSurface);
        };
        // T3 scene: at-most-one focus flag (checked first — an ambiguous scene
        // rejects every present, mirroring the Lean double-focus tooth).
        if !self.t3_focus_exclusive() {
            return Err(PresentError::DoubleFocus {
                focus_count: self.focus_count(),
            });
        }
        // T1: non-overlap / granted ⊆ held.
        if !self.t1_non_overlap(presenter, &p.target) {
            return Err(PresentError::Overpaint {
                offending: self.overpaint_regions(presenter, &p.target),
            });
        }
        // T2: label = genuine owner-binding.
        if !self.t2_label_bound(presenter, p.source_state_root, p.declared_label) {
            return Err(PresentError::LabelSpoof {
                declared: p.declared_label,
                genuine: label_of(presenter, p.source_state_root),
            });
        }
        // T3 input: input routes only to the focus holder.
        if !self.t3_input_routed(presenter, p.claims_focus) {
            return Err(PresentError::InputMisroute {
                focus_holder: self.focus_holder(),
            });
        }
        // A present genuinely advances the frame (the Lean `new ≠ old` leg).
        if p.new_digest == current {
            return Err(PresentError::NoFrameAdvance);
        }
        Ok(())
    }

    /// **PRESENT — the cap-gated frame advance.** A surface submits a present
    /// against the compositor: the scene authority is folded in
    /// ([`Self::scene_admit`]) and, IFF every tooth admits it, the frame digest
    /// advances and the present is recorded in the frame log. A present any
    /// tooth forbids is REFUSED and changes NOTHING (fail-closed — the Rust
    /// analogue of the Lean executor returning `none`; the post-state the light
    /// client verifies can only ever reflect a T1∧T2∧T3-respecting scene).
    ///
    /// Returns the recorded [`FrameCommit`] on success, or the tooth that bit.
    pub fn present(&mut self, presenter: &CellId, p: Present) -> Result<FrameCommit, PresentError> {
        self.scene_admit(presenter, &p)?;
        // Admitted: advance the presenter's surface frame digest + record it.
        if let Some(s) = self
            .scene
            .surfaces
            .iter_mut()
            .find(|s| &s.owner == presenter)
        {
            s.content_digest = p.new_digest;
            s.source_state_root = p.source_state_root;
        }
        let commit = FrameCommit {
            presenter: *presenter,
            regions: p.target.clone(),
            digest: p.new_digest,
            source_state_root: p.source_state_root,
            label: p.declared_label,
        };
        self.frames.push(commit.clone());
        Ok(commit)
    }

    /// Route an input event to the focused surface, returning its owner — or
    /// refuse if the `claimed` cell is not the focus holder. THE T3 INPUT GATE
    /// the shell enforces: input is delivered ONLY to the cell the user
    /// demonstrably chose (the focus holder); a misroute is refused. (The
    /// `claimed` cell is the one some component believes should receive the
    /// event; the gate confirms it against the unique focus holder.)
    pub fn route_input(&self, claimed: &CellId) -> Result<CellId, PresentError> {
        match self.focus_holder() {
            Some(holder) if &holder == claimed => Ok(holder),
            holder => Err(PresentError::InputMisroute {
                focus_holder: holder,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    /// The honest two-surface scene from the Lean `demoScene`, transposed to
    /// real `CellId`s: a wallet (regions {10,11}, root 500, FOCUSED), a browser
    /// (regions {20,21}, root 600, not focused), and a trusted chrome (region
    /// {99}, top z, not focused).
    fn demo() -> (Compositor, CellId, CellId, CellId) {
        let wallet = cid(1);
        let browser = cid(2);
        let chrome = cid(9);
        let mut c = Compositor::new();
        c.set_scene(CompositorScene {
            surfaces: vec![
                CompositedSurface {
                    owner: wallet,
                    regions: vec![10, 11],
                    content_digest: 1234,
                    source_state_root: 500,
                    z_layer: 0,
                    focus_flag: true,
                },
                CompositedSurface {
                    owner: browser,
                    regions: vec![20, 21],
                    content_digest: 5678,
                    source_state_root: 600,
                    z_layer: 0,
                    focus_flag: false,
                },
                CompositedSurface {
                    owner: chrome,
                    regions: vec![99],
                    content_digest: 9999,
                    source_state_root: 700,
                    z_layer: 100,
                    focus_flag: false,
                },
            ],
        });
        (c, wallet, browser, chrome)
    }

    #[test]
    fn label_of_binds_owner_and_root_injectively() {
        // T2's binding: a different owner OR a different root ⇒ a different
        // label (the pale ghost can't reuse another cell's label).
        let a = cid(1);
        let b = cid(2);
        assert_ne!(
            label_of(&a, 500),
            label_of(&b, 500),
            "owner changes the label"
        );
        assert_ne!(
            label_of(&a, 500),
            label_of(&a, 600),
            "root changes the label"
        );
        assert_eq!(
            label_of(&a, 500),
            label_of(&a, 500),
            "the binding is a function"
        );
    }

    #[test]
    fn t1_the_owner_paints_its_own_region_but_a_foreigner_cannot() {
        // THE T1 TOOTH: the wallet owns region 10; the browser does NOT.
        let (c, wallet, browser, _chrome) = demo();
        assert!(c.t1_non_overlap(&wallet, &[10]), "wallet owns region 10");
        assert!(
            c.t1_non_overlap(&wallet, &[10, 11]),
            "wallet owns both its regions"
        );
        assert!(
            !c.t1_non_overlap(&browser, &[10]),
            "the browser overpainting the wallet's region 10 is refused (T1)"
        );
        assert!(
            !c.t1_non_overlap(&wallet, &[10, 20]),
            "the wallet reaching into the browser's region 20 is refused (T1)"
        );
    }

    #[test]
    fn t2_the_genuine_label_binds_and_a_spoof_is_refused() {
        // THE T2 TOOTH: the wallet's genuine label binds; the browser declaring
        // the wallet's label fails.
        let (c, wallet, browser, _chrome) = demo();
        let wallet_label = label_of(&wallet, 500);
        assert!(
            c.t2_label_bound(&wallet, 500, wallet_label),
            "wallet's genuine label binds"
        );
        assert!(
            !c.t2_label_bound(&browser, 600, wallet_label),
            "the browser declaring the wallet's label is refused (T2)"
        );
    }

    #[test]
    fn t3_at_most_one_focus_and_input_routes_only_there() {
        // THE T3 TEETH: exactly one focus holder; input routes only to it.
        let (c, wallet, browser, _chrome) = demo();
        assert!(
            c.t3_focus_exclusive(),
            "the honest scene has at-most-one focus"
        );
        assert_eq!(c.focus_count(), 1, "exactly one focus holder");
        assert_eq!(c.focus_holder(), Some(wallet), "the wallet holds focus");
        assert!(
            c.t3_input_routed(&wallet, true),
            "the wallet (focus holder) may assert focus"
        );
        assert!(
            !c.t3_input_routed(&browser, true),
            "the non-focused browser asserting focus mis-routes (T3)"
        );
        // A non-input present is vacuously routed (no focus claim).
        assert!(
            c.t3_input_routed(&browser, false),
            "a non-input present is fine"
        );
    }

    #[test]
    fn double_focus_scene_is_refused_for_every_present() {
        // THE T3 (double-focus) TOOTH: a scene with two focus flags is
        // ambiguous; no present commits into it.
        let wallet = cid(1);
        let browser = cid(2);
        let mut c = Compositor::new();
        c.set_scene(CompositorScene {
            surfaces: vec![
                CompositedSurface {
                    owner: wallet,
                    regions: vec![10],
                    content_digest: 1,
                    source_state_root: 500,
                    z_layer: 0,
                    focus_flag: true,
                },
                CompositedSurface {
                    owner: browser,
                    regions: vec![20],
                    content_digest: 2,
                    source_state_root: 600,
                    z_layer: 0,
                    focus_flag: true, // ← TWO focus flags
                },
            ],
        });
        assert!(!c.t3_focus_exclusive(), "two focus flags ⇒ not exclusive");
        assert_eq!(c.focus_count(), 2);
        let honest = Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: false,
            new_digest: 7,
        };
        assert!(
            matches!(
                c.scene_admit(&wallet, &honest),
                Err(PresentError::DoubleFocus { .. })
            ),
            "an ambiguous-input scene rejects every present (T3)"
        );
    }

    #[test]
    fn honest_present_commits_and_advances_the_frame() {
        // THE COMMIT POLARITY: the focused wallet painting its own region with
        // its genuine label COMMITS, advancing the frame digest + logging it.
        let (mut c, wallet, _browser, _chrome) = demo();
        let p = Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: true,
            new_digest: 4242,
        };
        let commit = c.present(&wallet, p).expect("the honest present commits");
        assert_eq!(commit.presenter, wallet);
        assert_eq!(commit.digest, 4242);
        // The frame advanced on the wallet's surface.
        let s = c
            .scene()
            .surfaces
            .iter()
            .find(|s| s.owner == wallet)
            .unwrap();
        assert_eq!(s.content_digest, 4242, "the frame digest advanced");
        // The present is recorded in the frame log (provenance).
        assert_eq!(c.frames().len(), 1);
        assert_eq!(c.frames()[0].label, label_of(&wallet, 500));
    }

    #[test]
    fn overpaint_present_is_refused_and_changes_nothing() {
        // THE T1 TOOTH on present(): the browser overpainting the wallet's
        // region 10 is REFUSED, and the wallet's frame is untouched.
        let (mut c, wallet, browser, _chrome) = demo();
        let before = c
            .scene()
            .surfaces
            .iter()
            .find(|s| s.owner == wallet)
            .unwrap()
            .content_digest;
        let attack = Present {
            target: vec![10], // region 10 is the WALLET's
            source_state_root: 600,
            declared_label: label_of(&browser, 600),
            claims_focus: false,
            new_digest: 999,
        };
        let r = c.present(&browser, attack);
        assert!(
            matches!(r, Err(PresentError::Overpaint { .. })),
            "overpaint refused, got {r:?}"
        );
        // Fail-closed: nothing changed (no frame logged, the wallet untouched).
        assert_eq!(c.frames().len(), 0, "a refused present logs no frame");
        let after = c
            .scene()
            .surfaces
            .iter()
            .find(|s| s.owner == wallet)
            .unwrap()
            .content_digest;
        assert_eq!(
            before, after,
            "the wallet's frame is untouched by the refused overpaint"
        );
    }

    #[test]
    fn label_spoof_present_is_refused() {
        // THE T2 TOOTH on present(): the browser painting its OWN region but
        // DECLARING the wallet's label is REFUSED (the pale ghost).
        let (mut c, wallet, browser, _chrome) = demo();
        let spoof = Present {
            target: vec![20], // the browser's OWN region (T1 ok)
            source_state_root: 600,
            declared_label: label_of(&wallet, 500), // ← the WALLET's label
            claims_focus: false,
            new_digest: 321,
        };
        let r = c.present(&browser, spoof);
        assert!(
            matches!(r, Err(PresentError::LabelSpoof { .. })),
            "label-spoof refused, got {r:?}"
        );
        assert_eq!(c.frames().len(), 0);
    }

    #[test]
    fn input_steal_present_is_refused() {
        // THE T3 TOOTH on present(): the non-focused browser painting its own
        // region with its own label but ASSERTING focus (to steal the keystroke)
        // is REFUSED.
        let (mut c, _wallet, browser, _chrome) = demo();
        let steal = Present {
            target: vec![20],
            source_state_root: 600,
            declared_label: label_of(&browser, 600),
            claims_focus: true, // ← the browser is NOT the focus holder
            new_digest: 555,
        };
        let r = c.present(&browser, steal);
        assert!(
            matches!(r, Err(PresentError::InputMisroute { .. })),
            "input-steal refused, got {r:?}"
        );
        assert_eq!(c.frames().len(), 0);
    }

    #[test]
    fn route_input_delivers_only_to_the_focus_holder() {
        // THE T3 INPUT GATE: input is delivered only to the focus holder; a
        // misroute to a non-focused cell is refused.
        let (c, wallet, browser, _chrome) = demo();
        assert_eq!(
            c.route_input(&wallet),
            Ok(wallet),
            "input routes to the focus holder"
        );
        assert!(
            matches!(
                c.route_input(&browser),
                Err(PresentError::InputMisroute { .. })
            ),
            "input to a non-focused cell is refused"
        );
    }

    #[test]
    fn the_present_with_no_frame_advance_is_refused() {
        // A present that does not change the frame digest is a no-op, refused
        // (the Lean `new ≠ old` leg).
        let (mut c, wallet, _browser, _chrome) = demo();
        let same = Present {
            target: vec![10],
            source_state_root: 500,
            declared_label: label_of(&wallet, 500),
            claims_focus: true,
            new_digest: 1234, // == the wallet's current digest
        };
        assert!(matches!(
            c.present(&wallet, same),
            Err(PresentError::NoFrameAdvance)
        ));
    }

    #[test]
    fn a_present_by_a_cell_with_no_surface_is_refused() {
        let (mut c, _wallet, _browser, _chrome) = demo();
        let stranger = cid(0x55);
        let p = Present {
            target: vec![10],
            source_state_root: 0,
            declared_label: label_of(&stranger, 0),
            claims_focus: false,
            new_digest: 1,
        };
        assert!(matches!(
            c.present(&stranger, p),
            Err(PresentError::NoSurface)
        ));
    }
}
