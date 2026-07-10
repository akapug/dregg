//! **Richer Document Explorer faces** over the `dregg_doc` patch core — the
//! patch-diff, the three-way / merge-base view, and the visual node-graph.
//!
//! The desktop's Document Explorer already carries History / Graph / Blame faces
//! (in `mod.rs`: `render_docx_history` / `render_docx_graph` / `render_docx_blame`).
//! Those show revision rows, a flat atom list, and per-line authorship. This
//! module adds the faces that make the patch theory's *content* and *shape*
//! visible:
//!
//!   * [`render_patch_diff`] — what each patch in the history actually CHANGED:
//!     the `Op`s it carries, one legible line per op (the add/delete/connect/
//!     set-field grammar of `dregg_doc::patch`).
//!   * [`render_three_way_view`] — the diff3 / merge-base column: each conflict
//!     region shown against the common ancestor (`merge_base`) both sides forked
//!     from, every diverging side attributed to its author.
//!   * [`render_docgraph_nodes`] — the `DocGraph` as a vertical chain of bevel
//!     "node" boxes (vs the flat list), with explicit fork markers where an atom
//!     has more than one live successor — the Pijul graph made visible.
//!
//! Each face is a PURE render free-function over an immutable `dregg_doc` value
//! (no `Context<DeosDesktop>`, no interactivity): the Document Explorer wires
//! them in as read-only tabs. They draw from the shared NT chrome kit so they
//! match the rest of the desktop.

use gpui::prelude::FluentBuilder;
use gpui::{div, px, AnyElement, FontWeight, IntoElement, ParentElement, Styled};

use dregg_doc::{merge, merge_base, render_three_way, walk_atoms, AtomId, Doc, DocGraph, Op};

use crate::deos_desktop::chrome::{
    bevel_raised, bevel_sunken, face_row, face_section, NT_DIM, NT_FACE_DARK, NT_SELECT, NT_TEXT,
};

/// A short legible atom id (the low 16 bits, hex) — matches the `a%04x` style the
/// existing `render_docx_graph` uses so the faces read consistently.
fn atom_short(id: AtomId) -> String {
    if id == AtomId::ROOT {
        "ROOT".to_string()
    } else {
        format!("a{:04x}", (id.0 as u64) & 0xffff)
    }
}

/// A 1-line, length-bounded, newline-flattened content preview. Empty/whitespace
/// renders as the middot placeholder the desktop uses for "no content".
fn preview(s: &str, max: usize) -> String {
    let p: String = s.chars().take(max).collect();
    if p.trim().is_empty() {
        "·".to_string()
    } else {
        // Flatten newlines to a font-safe return marker (the geometric ⏎ is tofu in
        // the bake font — a bracketed ASCII reads cleanly everywhere).
        p.replace('\n', "[nl]")
    }
}

/// Describe one [`Op`] as a single legible line — the human reading of the patch
/// grammar (`dregg_doc::patch::Op`). The marker glyphs are kept inside the bake
/// font's coverage (the same restraint `chrome` documents for its glyphs).
fn describe_op(op: &Op) -> String {
    match op {
        Op::Add { id, content, after } => format!(
            "+ add {} '{}' after {}",
            atom_short(*id),
            preview(&content.render_text(), 40),
            atom_short(*after)
        ),
        Op::Delete { id } => format!("× delete {}", atom_short(*id)),
        Op::Connect { from, to } => {
            format!("+ connect {} → {}", atom_short(*from), atom_short(*to))
        }
        Op::SetField {
            name,
            value,
            superseding,
        } => {
            let verb = if *superseding {
                "field (supersede)"
            } else {
                "field"
            };
            format!("• {} {} := '{}'", verb, name, preview(value, 40))
        }
        Op::Resurrect { id } => format!("+ resurrect {}", atom_short(*id)),
        Op::Disconnect { from, to } => {
            format!("× disconnect {} → {}", atom_short(*from), atom_short(*to))
        }
        Op::RetractField { name } => format!("× retract field {}", name),
    }
}

/// **The PATCH-DIFF face** — for every patch in the history, WHAT IT CHANGED.
///
/// Each patch is a group header (`patch N · @author · K ops`) followed by one row
/// per [`Op`] it carries, described legibly by [`describe_op`]. This exposes the
/// *content* of the patch history that the History face leaves implicit (it shows
/// replayed text + revision rows, not the ops each revision applied).
pub fn render_patch_diff(doc: &Doc) -> AnyElement {
    let patches = doc.history().patches();
    let total_ops: usize = patches.iter().map(|p| p.ops.len()).sum();
    let mut col = div().flex().flex_col().gap_1().child(face_section(&format!(
        "Patch diff — {} patch(es), {total_ops} op(s)",
        patches.len()
    )));

    if patches.is_empty() {
        col = col.child(face_row(
            "(empty)",
            "type into the document to record a patch",
        ));
        return col.into_any_element();
    }

    for (i, patch) in patches.iter().enumerate() {
        let author = patch.author.0 & 0xffff;
        let n = patch.ops.len();
        // The patch group header: index · author · op count · short patch id.
        col = col.child(
            div()
                .flex()
                .flex_row()
                .gap_1()
                .mt_1()
                .text_size(px(10.0))
                .font_weight(FontWeight::BOLD)
                .text_color(gpui::rgb(NT_SELECT))
                .child(format!(
                    "patch {i} · @{author} · {n} op{} · #{:04x}",
                    if n == 1 { "" } else { "s" },
                    (patch.id().0 as u64) & 0xffff
                )),
        );
        if n == 0 {
            col = col.child(
                div()
                    .px_2()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_DIM))
                    .child("(no ops — identity patch)"),
            );
            continue;
        }
        for op in &patch.ops {
            col = col.child(
                div()
                    .px_2()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_TEXT))
                    .child(describe_op(op)),
            );
        }
    }
    col.into_any_element()
}

/// **The THREE-WAY / merge-base face** — each conflict region in the merged
/// document shown against the common ancestor both sides forked from.
///
/// `merged` is the document that may carry first-class conflict states (the
/// stitch of two branches); `base` is any document on the shared history. The
/// common ancestor is recovered as the [`merge_base`] of the two histories, then
/// `dregg_doc`'s [`render_three_way`] reads, per conflict region, the BASE column
/// and every diverging side. A clean merge yields no regions.
///
/// Note the underlying `dregg_doc::render_three_way` takes two `&DocGraph`; this
/// wrapper computes both from the two `&Doc`s — the ancestor graph from
/// `merge_base(...).replay()` and the merged graph from `merge(...)` of the two
/// replays — so the Document Explorer can call it with the two open documents.
pub fn render_three_way_view(merged: &Doc, base: &Doc) -> AnyElement {
    // The common ancestor of the two histories, replayed into the BASE graph.
    let ancestor = merge_base(merged.history(), base.history()).replay();
    // The merged graph: the pushout/union of the two folds (the same object the
    // stitch produces). Built here so conflict regions are read off the real
    // union rather than assuming `merged` already carries both sides.
    let merged_graph = merge(&merged.history().replay(), &base.history().replay());

    let conflicts = render_three_way(&merged_graph, &ancestor);

    let mut col = div().flex().flex_col().gap_1().child(face_section(&format!(
        "Three-way — {} conflict region(s)",
        conflicts.len()
    )));

    if conflicts.is_empty() {
        col = col.child(face_row(
            "(clean)",
            "no conflict regions — the merge linearizes",
        ));
        return col.into_any_element();
    }

    for (i, c) in conflicts.iter().enumerate() {
        col = col.child(
            div()
                .mt_1()
                .text_size(px(10.0))
                .font_weight(FontWeight::BOLD)
                .text_color(gpui::rgb(NT_SELECT))
                .child(format!("region {i} · {} side(s)", c.sides.len())),
        );
        // The BASE column: what the common ancestor carried at the fork point.
        let base_text = if c.base_text.trim().is_empty() {
            "(insert — ancestor had nothing here)".to_string()
        } else {
            preview(&c.base_text, 60)
        };
        col = col.child(face_row("base", &base_text));
        // Each diverging side, attributed to its author + patch.
        for side in &c.sides {
            col = col.child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .px_1()
                    .text_size(px(10.0))
                    .child(
                        div()
                            .w(px(96.0))
                            .text_color(gpui::rgb(0x4040a0))
                            .child(format!(
                                "@{} #{:04x}",
                                side.author.0 & 0xffff,
                                (side.patch.0 as u64) & 0xffff
                            )),
                    )
                    .child(div().flex_1().child(preview(&side.text, 60))),
            );
        }
    }
    col.into_any_element()
}

/// Live successors of `id` (alive atoms only), in id order — the edges that the
/// node-graph draws as forward arrows. Tombstoned successors are excluded from
/// the fork count (a dead branch is not a live antichain) but still shown as
/// dimmed nodes in their own right when the walk reaches them via `atoms()`.
fn live_successors(g: &DocGraph, id: AtomId) -> Vec<AtomId> {
    g.successors(id)
        .filter(|s| g.atom(*s).map(|a| a.is_alive()).unwrap_or(false))
        .collect()
}

/// **The NODE-GRAPH face** — the `DocGraph` as a vertical chain of bevel node
/// boxes with explicit fork markers, rather than the flat list of the existing
/// Graph face.
///
/// The ALIVE linear spine ([`walk_atoms`]) is drawn first, top-to-bottom, each
/// atom a small raised node box (short id + a 1-line content preview) joined by a
/// "↓" connector. Where an atom has more than one live successor — a genuine
/// antichain, a Pijul conflict fork — a "⑂ fork" marker is shown in place of the
/// plain connector. Below the spine, any atoms NOT on the spine (tombstones and
/// the off-spine fork branches) are listed dimmed, so the full graph (incl. the
/// content the walk stops short of) stays visible.
pub fn render_docgraph_nodes(doc: &Doc) -> AnyElement {
    let g = doc.history().replay();
    let spine = walk_atoms(&g);
    let spine_ids: std::collections::BTreeSet<AtomId> = spine.iter().map(|(id, _)| *id).collect();

    let total = g.atoms().count();
    let alive = g.atoms().filter(|a| a.is_alive()).count();

    let mut col = div().flex().flex_col().gap_1().child(face_section(&format!(
        "DocGraph nodes — {} atom(s), {alive} alive, {} on spine",
        total,
        spine.len()
    )));

    // The ROOT anchor opens the chain.
    col = col.child(node_box("ROOT", "(anchor)", false, true));
    col = col.child(connector(&g, AtomId::ROOT));

    // The alive linear spine, node by node.
    for (idx, (id, text)) in spine.iter().enumerate() {
        let author = g
            .atom(*id)
            .map(|a| a.provenance.author.0 & 0xffff)
            .unwrap_or(0);
        col = col.child(node_box(
            &atom_short(*id),
            &format!("@{author} · {}", preview(text, 44)),
            false,
            false,
        ));
        // A connector after every node except where this is the final spine atom
        // AND it has no live successor (the chain simply ends).
        let is_last = idx + 1 == spine.len();
        if !is_last || !live_successors(&g, *id).is_empty() {
            col = col.child(connector(&g, *id));
        }
    }

    // Off-spine atoms: tombstones + the branches the walk stopped short of (the
    // far side of a fork). Listed dimmed so the whole graph stays legible.
    let mut off: Vec<_> = g
        .atoms()
        .filter(|a| a.id != AtomId::ROOT && !spine_ids.contains(&a.id))
        .collect();
    off.sort_by_key(|a| a.id.0);
    if !off.is_empty() {
        col = col.child(face_section(&format!("Off-spine — {} atom(s)", off.len())));
        for a in &off {
            let status = if a.is_alive() {
                "fork branch"
            } else {
                "tombstone"
            };
            col = col.child(node_box(
                &atom_short(a.id),
                &format!("{status} · {}", preview(&a.content.render_text(), 40)),
                true,
                false,
            ));
        }
    }

    col.into_any_element()
}

/// One node box in the graph chain — a small NT raised bevel carrying a short id
/// and a 1-line label. `dim` renders an off-spine / dead node greyed; `anchor`
/// marks the ROOT sentinel.
fn node_box(id: &str, label: &str, dim: bool, anchor: bool) -> impl IntoElement {
    let id_color = if anchor || dim { NT_DIM } else { NT_SELECT };
    // Off-spine / dead nodes read SUNKEN-grey (recessed into the graph); live spine
    // nodes read RAISED (the same two-tone bevel as every other NT face).
    let base = div()
        .flex()
        .flex_row()
        .gap_1()
        .px_2()
        .py_1()
        .max_w(px(360.0))
        .text_size(px(10.0));
    let base = if dim {
        bevel_sunken(base.bg(gpui::rgb(NT_FACE_DARK))).text_color(gpui::rgb(NT_DIM))
    } else {
        bevel_raised(base)
    };
    base.child(
        div()
            .w(px(70.0))
            .font_weight(FontWeight::BOLD)
            .text_color(gpui::rgb(id_color))
            .child(id.to_string()),
    )
    .child(div().flex_1().child(label.to_string()))
}

/// The connector under a node: a plain "↓" when the atom continues to a single
/// live successor, or a "⑂ fork (N ways)" marker when it has a live antichain
/// (more than one live successor with no order between them — a Pijul conflict).
fn connector(g: &DocGraph, id: AtomId) -> impl IntoElement {
    let succ = live_successors(g, id);
    // The fork glyph (⑂) is tofu in the bake font; a bracketed ASCII marker reads as
    // the antichain everywhere. The plain "↓" connector is a basic arrow the font
    // carries.
    let (glyph, color, fork) = if succ.len() > 1 {
        (format!("├< fork ({} ways)", succ.len()), 0xa04040u32, true)
    } else {
        ("↓".to_string(), NT_DIM, false)
    };
    div()
        .px_2()
        .text_size(px(10.0))
        .when(fork, |d| d.font_weight(FontWeight::BOLD))
        .text_color(gpui::rgb(color))
        .child(glyph)
}
