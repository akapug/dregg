//! The 📄 DOCS editor surface: each edit/resolve a real cap-gated turn; conflicts as first-class states.

use super::*;

// ══════════════════════════════════════════════════════════════════════════
// THE 📄 DOCS EDITOR — the dreggverse document language as a cockpit surface.
// Each edit/resolve is a real cap-gated TURN through the genuine executor
// (riding `dregg_doc::ExecutorDrivenDoc`); a CONFLICT is a first-class STATE
// (both alternatives rendered, each tagged with who wrote it); transclusion +
// backlinks reuse the built Nelson pieces. See `starbridge_v2::doc_editor`.
// (A SEPARATE impl block at EOF so it never clobbers a peer's mid-file edits.)
// ══════════════════════════════════════════════════════════════════════════
impl Cockpit {
    // ── the edit verbs (each an edit = a real cap-gated turn) ─────────────────

    /// Append text to the document as ALICE — a real cap-gated turn leaving a
    /// receipt. The banner shows the executor verdict.
    pub(crate) fn doc_append_alice(&mut self, _cx: &mut Context<Cockpit>) {
        let out = self.doc_editor.append(
            "And every edit is a witnessed turn. ",
            starbridge_v2::doc_editor::DocAuthor::ALICE,
        );
        self.doc_outcome = Some(out.banner());
    }

    /// Attempt the same append on the UNAUTHORIZED editor (no region cap) — the
    /// executor's cross-cell cap gate REFUSES it IN-BAND (`CapabilityNotHeld`); the
    /// document is untouched. The refusal is the feature (the anti-ghost tooth).
    pub(crate) fn doc_attempt_unauthorized(&mut self, _cx: &mut Context<Cockpit>) {
        let out = self.doc_editor.attempt_unauthorized(
            "a forbidden region edit ",
            starbridge_v2::doc_editor::DocAuthor::BOB,
        );
        self.doc_outcome = Some(out.banner());
    }

    /// Sow a first-class PROSE conflict: two co-authors append a different
    /// continuation after the same tail atom (both real turns). The document now
    /// LIVES IN a conflict state.
    pub(crate) fn doc_sow_prose_conflict(&mut self, _cx: &mut Context<Cockpit>) {
        let (a, b) = self
            .doc_editor
            .sow_prose_conflict("Cats are the best. ", "Dogs are the best. ");
        self.doc_outcome = Some(format!(
            "sowed a prose conflict · alice: {} · bob: {}",
            if a.committed() { "✓" } else { "✗" },
            if b.committed() { "✓" } else { "✗" },
        ));
    }

    /// Sow a first-class FIELD conflict (the conservation/authority regime): two
    /// co-authors set a different `title` — both survive as a clash a resolution
    /// must CHOOSE (it may need consensus).
    pub(crate) fn doc_sow_field_conflict(&mut self, _cx: &mut Context<Cockpit>) {
        let (a, b) = self
            .doc_editor
            .sow_field_conflict("title", "On Cats", "On Dogs");
        self.doc_outcome = Some(format!(
            "sowed a field conflict (title) · alice: {} · bob: {}",
            if a.committed() { "✓" } else { "✗" },
            if b.committed() { "✓" } else { "✗" },
        ));
    }

    /// RESOLVE the first prose conflict by KEEPING its first alternative (drop the
    /// rest) — a real cap-gated resolving turn that collapses the antichain.
    pub(crate) fn doc_resolve_prose_keep(&mut self, _cx: &mut Context<Cockpit>) {
        let prose: Vec<_> = self
            .doc_editor
            .conflicts()
            .into_iter()
            .filter(|c| c.regime == dregg_doc::Regime::Prose)
            .collect();
        if let Some(c) = prose.first() {
            let heads: Vec<dregg_doc::AtomId> = c.alternatives.iter().map(|a| a.head).collect();
            if let Some((keep, drop)) = heads.split_first() {
                let out = self.doc_editor.resolve_prose_keep(
                    *keep,
                    drop,
                    starbridge_v2::doc_editor::DocAuthor::ALICE,
                );
                self.doc_outcome = Some(format!("resolve (keep alice's): {}", out.banner()));
            }
        } else {
            self.doc_outcome = Some("no prose conflict to resolve".into());
        }
    }

    /// RESOLVE the first prose conflict by ORDERING its alternatives (both kept) —
    /// a real cap-gated resolving `Connect` turn.
    pub(crate) fn doc_resolve_prose_order(&mut self, _cx: &mut Context<Cockpit>) {
        let prose: Vec<_> = self
            .doc_editor
            .conflicts()
            .into_iter()
            .filter(|c| c.regime == dregg_doc::Regime::Prose)
            .collect();
        if let Some(c) = prose.first() {
            let heads: Vec<dregg_doc::AtomId> = c.alternatives.iter().map(|a| a.head).collect();
            let out = self
                .doc_editor
                .resolve_prose_order(&heads, starbridge_v2::doc_editor::DocAuthor::ALICE);
            self.doc_outcome = Some(format!("resolve (order both): {}", out.banner()));
        } else {
            self.doc_outcome = Some("no prose conflict to resolve".into());
        }
    }

    /// RESOLVE the title FIELD conflict by CHOOSING alice's value — a real
    /// superseding `SetField` turn (the settling authority recorded).
    pub(crate) fn doc_resolve_field(&mut self, _cx: &mut Context<Cockpit>) {
        let out = self.doc_editor.resolve_field_choose(
            "title",
            "On Cats",
            starbridge_v2::doc_editor::DocAuthor::ALICE,
        );
        self.doc_outcome = Some(format!("settle title = 'On Cats': {}", out.banner()));
    }

    /// THE 📄 DOCS PANEL — the document editor surface: the linearized content,
    /// conflicts-as-states inline (both alternatives + provenance), one-click
    /// resolve, and the transclusion/backlinks hypermedia faces.
    pub(crate) fn docs_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let rendered = self.doc_editor.rendered();
        let conflicts = self.doc_editor.conflicts();
        let region = self.doc_editor.region_id();
        let editor = self.doc_editor.editor_id();
        let commitment = self.doc_editor.commitment();
        let seam_ok = self.doc_editor.commitment_matches();

        // The hypermedia faces, reusing the built `web_cells`/`links_here` pieces.
        let viewer = self.anchors[2]; // the cockpit `user` principal
        let (transclusion, backlinks) = {
            let w = self.world.borrow();
            let t = self
                .doc_editor
                .transclusion(&w, viewer, dregg_cell::AuthRequired::None);
            let b = self
                .doc_editor
                .backlinks(&w, region, dregg_cell::AuthRequired::None, 1);
            (t, b)
        };

        let mut col = div()
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_hidden();
        col = col.child(
            section_title("📄 DOCS · the dreggverse document language · a patch IS a turn").mb_1(),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "A document is a CELL; an edit is a PATCH is a cap-gated TURN (a real receipt). A \
             CONFLICT is a first-class STATE you live in — two live alternatives, each tagged \
             with who wrote it — resolved by a later patch, never an error. Transclusion is a \
             verified cross-cell quote; backlinks are the witness-graph read backward.",
        ));

        // ── THE SUBSTRATE HEADER — the document IS a real cell ───────────────
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .mt_1()
                .child(pill(
                    format!("doc cell {}", reflect::short_hex(&region.0)),
                    theme::accent(),
                ))
                .child(pill(
                    format!("editor {}", reflect::short_hex(&editor.0)),
                    theme::accent(),
                ))
                .child(pill(
                    format!("commit {}", reflect::short_hex(&commitment)),
                    theme::muted(),
                ))
                .child(pill(
                    if seam_ok {
                        "seam: commitment == projection"
                    } else {
                        "seam DRIFT"
                    },
                    if seam_ok { theme::good() } else { theme::bad() },
                ))
                .child(pill(
                    if rendered.has_conflict() {
                        "conflicted"
                    } else {
                        "clean"
                    },
                    if rendered.has_conflict() {
                        theme::warn()
                    } else {
                        theme::good()
                    },
                )),
        );

        // ── THE MOLDABLE INSPECTION — the document AS an inspectable object ──
        // The doc lens (rendered · patch-history · conflict-as-state · commitment)
        // reachable straight from the editor: the same generic body widget every
        // lens uses, off the live document's folded graph. Closes the doc-lens
        // reachability gap (the editor surface now BOTH authors AND inspects).
        {
            use starbridge_v2::doc_lens::DocumentInspection;
            use starbridge_v2::presentable::{PresentCtx, Presentable};
            let w = self.world.borrow();
            let ctx = PresentCtx::new(&w, viewer);
            let inspection =
                DocumentInspection::from_graph("the live document", self.doc_editor.graph());
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::accent())
                    .mt_1()
                    .child("◆ moldable inspection — the document as an inspectable object"),
            );
            for p in inspection.present(&ctx) {
                col = col.child(
                    div()
                        .flex()
                        .flex_col()
                        .gap_1()
                        .p_2()
                        .mt_1()
                        .rounded_md()
                        .border_1()
                        .border_color(theme::border())
                        .bg(theme::panel())
                        .child(div().text_xs().text_color(theme::muted()).child(format!(
                            "{} · {}",
                            p.kind.slug(),
                            p.label
                        )))
                        .child(Self::render_presentation_body(&p.body)),
                );
            }
        }

        // ── THE EDIT VERBS (each an edit = a real cap-gated turn) ────────────
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .mt_1()
                .child(small_button(
                    cx,
                    "docs-append",
                    "✎ edit (commit a turn)",
                    theme::good(),
                    Cockpit::doc_append_alice,
                ))
                .child(small_button(
                    cx,
                    "docs-unauthorized",
                    "⛔ try unauthorized edit",
                    theme::bad(),
                    Cockpit::doc_attempt_unauthorized,
                ))
                .child(small_button(
                    cx,
                    "docs-sow-prose",
                    "⑂ sow prose conflict",
                    theme::warn(),
                    Cockpit::doc_sow_prose_conflict,
                ))
                .child(small_button(
                    cx,
                    "docs-sow-field",
                    "⑂ sow field conflict (title)",
                    theme::warn(),
                    Cockpit::doc_sow_field_conflict,
                )),
        );

        // ── THE OUTCOME BANNER (the real executor verdict) ───────────────────
        if let Some(banner) = &self.doc_outcome {
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .border_1()
                    .border_color(theme::border())
                    .text_xs()
                    .font_family("Menlo")
                    .text_color(theme::text())
                    .child(banner.clone()),
            );
        }

        // ── THE RENDERED DOCUMENT (clean runs + inline conflict markers) ─────
        col = col.child(
            section_title("THE DOCUMENT (linearized content)")
                .mt_2()
                .mb_1(),
        );
        let mut doc_box = div()
            .flex()
            .flex_col()
            .gap_1()
            .p_2()
            .rounded_md()
            .bg(theme::panel())
            .border_1()
            .border_color(theme::border());
        for seg in &rendered.segments {
            match seg {
                dregg_doc::Segment::Clean(t) => {
                    doc_box =
                        doc_box.child(div().text_sm().text_color(theme::text()).child(t.clone()));
                }
                dregg_doc::Segment::Conflict(_) => {
                    doc_box = doc_box.child(
                        div()
                            .text_xs()
                            .text_color(theme::warn())
                            .child("⑂ — a conflict region lives here (see below) —"),
                    );
                }
            }
        }
        col = col.child(doc_box);

        // ── CONFLICTS-AS-STATES: both alternatives, each with PROVENANCE ─────
        if !conflicts.is_empty() {
            col = col.child(
                section_title(
                    "CONFLICTS — a STATE you live in (both alternatives + who wrote each)",
                )
                .mt_2()
                .mb_1(),
            );
            for c in conflicts.iter() {
                let regime_color = if c.needs_consensus {
                    theme::bad()
                } else {
                    theme::warn()
                };
                let mut cbox = div()
                    .flex()
                    .flex_col()
                    .gap_1()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .border_1()
                    .border_color(regime_color);
                cbox = cbox.child(
                    div()
                        .flex()
                        .flex_wrap()
                        .items_center()
                        .gap_1()
                        .child(pill(format!("{} regime", c.regime.label()), regime_color))
                        .when(c.field.is_some(), |d| {
                            d.child(pill(
                                format!("field: {}", c.field.clone().unwrap_or_default()),
                                theme::accent(),
                            ))
                        })
                        .child(pill(
                            if c.needs_consensus {
                                "may need consensus"
                            } else {
                                "unilaterally resolvable"
                            },
                            theme::muted(),
                        )),
                );
                for alt in &c.alternatives {
                    let prov = match alt.receipt_hash {
                        Some(h) => format!("receipt {}", reflect::short_hex(&h)),
                        None => "(witness-only)".to_string(),
                    };
                    cbox = cbox.child(
                        div()
                            .flex()
                            .flex_col()
                            .gap_0p5()
                            .px_2()
                            .py_1()
                            .rounded_md()
                            .bg(theme::panel())
                            .border_1()
                            .border_color(theme::border())
                            .child(
                                div()
                                    .flex()
                                    .items_center()
                                    .gap_1()
                                    .child(pill(format!("@{}", alt.author_name), theme::accent()))
                                    .child(pill(prov, theme::muted())),
                            )
                            .child(div().text_sm().text_color(theme::text()).child(
                                if alt.text.is_empty() {
                                    "(empty)".to_string()
                                } else {
                                    alt.text.clone()
                                },
                            )),
                    );
                }
                let resolve_row = if c.regime == dregg_doc::Regime::Field {
                    div().flex().flex_wrap().gap_1().mt_1().child(small_button(
                        cx,
                        "docs-resolve-field",
                        "✓ settle title = alice's",
                        theme::good(),
                        Cockpit::doc_resolve_field,
                    ))
                } else {
                    div()
                        .flex()
                        .flex_wrap()
                        .gap_1()
                        .mt_1()
                        .child(small_button(
                            cx,
                            "docs-resolve-keep",
                            "✓ resolve: keep alice's",
                            theme::good(),
                            Cockpit::doc_resolve_prose_keep,
                        ))
                        .child(small_button(
                            cx,
                            "docs-resolve-order",
                            "✓ resolve: order both",
                            theme::good(),
                            Cockpit::doc_resolve_prose_order,
                        ))
                };
                cbox = cbox.child(resolve_row);
                col = col.child(cbox);
            }
        }

        // ── THE HYPERMEDIA FACES (the built Nelson pieces, reused) ───────────
        col = col.child(
            section_title("HYPERMEDIA · transclusion + backlinks (Nelson, verified)")
                .mt_2()
                .mb_1(),
        );
        if let Some(t) = &transclusion {
            col = col.child(
                div()
                    .flex()
                    .flex_col()
                    .gap_0p5()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(theme::panel())
                    .border_1()
                    .border_color(theme::border())
                    .child(div().text_xs().text_color(theme::muted()).child(
                        "TRANSCLUSION — a verified cross-cell quote (content-addressed + receipt; \
                         the quote IS the source's committed value, never a copy):",
                    ))
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::text())
                            .font_family("Menlo")
                            .child(format!(
                                "{} quotes {} · field {} · receipt {} · {}",
                                reflect::short_hex(&t.host.0),
                                reflect::short_hex(&t.source.0),
                                t.transcluded_field,
                                t.provenance_receipt,
                                if t.source_finalized {
                                    "FINALIZED"
                                } else {
                                    "tentative"
                                },
                            )),
                    ),
            );
        } else {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("(too few cells to compose a transclusion yet)"),
            );
        }
        col = col.child(
            div().text_xs().text_color(theme::muted()).mt_1().child(format!(
                "WHAT-LINKS-HERE (who transcludes this document) · {} backlink(s) · viewer holds {} \
                 — a backlink the viewer's caps cannot admit is fogged",
                backlinks.backlinks.len(),
                backlinks.viewer_tier,
            )),
        );
        for bl in backlinks.backlinks.iter().take(6) {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::text())
                    .font_family("Menlo")
                    .child(format!("← {}", bl.observer_uri)),
            );
        }

        col.into_any_element()
    }
}
