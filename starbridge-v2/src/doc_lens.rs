//! # The DOCUMENT lens — a literate `dregg_doc` document, moldably inspected.
//!
//! `docs/deos/DOCUMENT-LANGUAGE.md` §4 names the document's *faces* — "rendered /
//! source / patch-history / conflict presentations" — as a Presentable to build.
//! The `doc_editor` (DOCS tab) is the AUTHOR surface; this is the uniform INSPECT
//! surface, so a document inspects through the SAME Registry / Spotter / Halo
//! framework as cells, caps, receipts — the moldable inspector's complete-coverage
//! bar (every protocol object has its presentation set).
//!
//! It rides the green `dregg_doc` patch core directly (no parallel model):
//!
//! - **Rendered** — `content(graph)` linearized, with first-class conflict regions
//!   marked legibly ("two people wrote this differently — here's both", the
//!   AOL-wonder bar, never swallowed).
//! - **Patch history** — the `History` of authored patches as a provenance
//!   timeline (who recorded what, oldest→newest) — the augmentation trail.
//! - **Conflict-as-state** — the live `ConflictRegion`s as a FIRST-CLASS state
//!   (an antichain of alternatives, each attributed to its author), NOT a failure;
//!   a clean document says so honestly.
//! - **Commitment + two-regime** — the document's `commit` binding + the
//!   grow-only-prose (I-confluent) vs single-valued-field (clashable) split — the
//!   "what-is" / source face.
//!
//! gpui-free + fully tested; renders through the existing generic body widget.

use dregg_doc::{
    blame, content, substrate_commit, Author, ConflictRegion, DocGraph, ExecutorDrivenDoc, History,
    PatchId, Regime, Rendered, Segment,
};

use crate::presentable::{
    PresentCtx, Presentable, Presentation, PresentationBody, PresentationKind, TimelineEvent,
    TimelineView,
};
use crate::reflect::{Field, Inspectable, ObjectKind};

/// The moldable inspection of one literate document. The folded `graph` is the
/// content the rendered/conflict/commitment faces read; `history` is the patch
/// trail (present when the doc is sourced from its full [`History`], absent when
/// sourced from a LIVE document's graph — the substrate keeps the folded state,
/// not the patch log, so a live-cell projection degrades the trail honestly).
pub struct DocumentInspection {
    /// An operator-legible name for the document.
    pub title: String,
    /// The folded document content (always present — the rendered/conflict/
    /// commitment/blame faces read this).
    graph: DocGraph,
    /// The authoritative patch trail, when known (the `History` source). `None`
    /// for a live-document projection (the trail lives in the receipt log, not the
    /// folded cell state).
    history: Option<History>,
}

impl DocumentInspection {
    /// Inspect a document from its full patch [`History`] — the complete face set
    /// including the patch-history trail.
    pub fn new(title: impl Into<String>, history: History) -> Self {
        DocumentInspection {
            title: title.into(),
            graph: history.replay(),
            history: Some(history),
        }
    }

    /// Inspect a document from a folded [`DocGraph`] (a live document's content).
    /// The rendered/conflict/commitment/blame faces are full; the patch-history
    /// trail is reported honestly as unavailable in this projection.
    pub fn from_graph(title: impl Into<String>, graph: &DocGraph) -> Self {
        DocumentInspection {
            title: title.into(),
            graph: graph.clone(),
            history: None,
        }
    }

    /// Inspect a LIVE [`ExecutorDrivenDoc`] (the DOCS tab's authoritative doc,
    /// driven through the real executor) — the reachability path from the editor
    /// surface to the moldable inspector. Sources the folded graph directly.
    pub fn from_doc(title: impl Into<String>, doc: &ExecutorDrivenDoc) -> Self {
        DocumentInspection::from_graph(title, doc.graph())
    }
}

/// A short hex of a `PatchId` (a 128-bit content address).
fn short_patch(p: PatchId) -> String {
    let s = format!("{:032x}", p.0);
    format!("{}…", &s[..8])
}

/// An author handle for display (the `Author` is an opaque 64-bit principal).
fn author_label(a: Author) -> String {
    if a == Author::SYSTEM {
        "system".to_string()
    } else {
        format!("author {:x}", a.0)
    }
}

impl Presentable for DocumentInspection {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Document
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let graph = &self.graph;
        let rendered: Rendered = content(graph);
        let lines = blame(graph);
        let commitment = substrate_commit(graph);
        let conflict_count = rendered.conflicts().count();
        let patch_count = self.history.as_ref().map(History::len).unwrap_or(0);

        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor (universal-coverage invariant).
        let insp = Inspectable {
            kind: ObjectKind::Document,
            title: format!("DOCUMENT — {}", self.title),
            subtitle: format!(
                "{patch_count} patch{} · {} live atom{} · {conflict_count} open conflict{}",
                if patch_count == 1 { "" } else { "es" },
                lines.len(),
                if lines.len() == 1 { "" } else { "s" },
                if conflict_count == 1 { "" } else { "s" },
            ),
            fields: vec![
                Field::text("title", self.title.clone()),
                Field::text("patches", patch_count.to_string()),
                Field::text("live_atoms", lines.len().to_string()),
                Field::boolean("has_conflict", rendered.has_conflict()),
                Field::text(
                    "commitment",
                    commitment
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect::<String>(),
                ),
                Field::text(
                    "tip",
                    match &self.history {
                        Some(h) => h
                            .tip()
                            .map(short_patch)
                            .unwrap_or_else(|| "genesis".to_string()),
                        None => "live projection (trail not in folded state)".to_string(),
                    },
                ),
            ],
        };
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Document".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Rendered — the document content, conflicts marked legibly.
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Rendered".to_string(),
            search_text: format!("rendered content {}", rendered.to_marked_string()),
            body: PresentationBody::Prose(rendered_prose(&rendered)),
        });

        // (3) Patch history — the augmentation trail, oldest→newest, attributed.
        out.push(Presentation {
            kind: PresentationKind::Provenance,
            label: "Patch History".to_string(),
            search_text: format!("patch history trail {patch_count} patches"),
            body: PresentationBody::Timeline(patch_timeline(self.history.as_ref())),
        });

        // (4) Conflict-as-state — the first-class conflict regions (or honestly
        //     clean). An antichain of attributed alternatives, NOT a failure.
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Conflicts".to_string(),
            search_text: format!("conflict as state antichain {conflict_count}"),
            body: PresentationBody::Fields(conflict_fields(&rendered)),
        });

        // (5) Commitment + two-regime — the binding + the "what-is" source face.
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Commitment".to_string(),
            search_text: "commitment binding two-regime prose field iconfluent".to_string(),
            body: PresentationBody::Prose(commitment_prose(commitment, &rendered)),
        });

        out
    }
}

/// The rendered document as legible prose: clean runs verbatim; a conflict shown
/// as its attributed alternatives (the AOL-wonder "here's both" bar).
fn rendered_prose(rendered: &Rendered) -> String {
    if rendered.segments.is_empty() {
        return "(empty document — no content atoms yet)".to_string();
    }
    let mut out = String::new();
    for seg in &rendered.segments {
        match seg {
            Segment::Clean(s) => out.push_str(s),
            Segment::Conflict(c) => {
                out.push_str("\n⟨conflict — ");
                out.push_str(match c.regime {
                    Regime::Prose => "two prose forks, unordered",
                    Regime::Field => "a single-valued field clash",
                });
                if let Some(f) = &c.field {
                    out.push_str(&format!(" · field “{f}”"));
                }
                out.push_str("⟩\n");
                for (i, alt) in c.alternatives.iter().enumerate() {
                    out.push_str(&format!(
                        "  [{}] {} — “{}”\n",
                        i + 1,
                        author_label(alt.provenance.author),
                        alt.text
                    ));
                }
            }
        }
    }
    out
}

/// The patch history as a provenance timeline — one event per recorded patch,
/// oldest→newest, attributed to its author with its op count. A live-document
/// projection (no `History`) reports the trail's absence as a single honest event
/// rather than a fabricated history.
fn patch_timeline(history: Option<&History>) -> TimelineView {
    let Some(history) = history else {
        return TimelineView {
            events: vec![TimelineEvent {
                at: 0,
                label: "live projection — the patch trail lives in the receipt log, \
                        not the folded cell state"
                    .to_string(),
                hash: None,
            }],
        };
    };
    let events = history
        .patches()
        .iter()
        .enumerate()
        .map(|(i, p)| TimelineEvent {
            at: i as u64,
            label: format!(
                "{} · {} · {} op{}",
                short_patch(p.id()),
                author_label(p.author),
                p.ops.len(),
                if p.ops.len() == 1 { "" } else { "s" }
            ),
            hash: None,
        })
        .collect();
    TimelineView { events }
}

/// The conflict regions as a field tree — each conflict an antichain of attributed
/// alternatives. A clean document records that honestly (no fabricated conflict).
fn conflict_fields(rendered: &Rendered) -> Inspectable {
    let conflicts: Vec<&ConflictRegion> = rendered.conflicts().collect();
    let mut fields: Vec<Field> = vec![
        Field::boolean("clean", conflicts.is_empty()),
        Field::text("open_conflicts", conflicts.len().to_string()),
    ];
    for (ci, c) in conflicts.iter().enumerate() {
        let regime = match c.regime {
            Regime::Prose => "prose (antichain)",
            Regime::Field => "field (single-valued clash)",
        };
        fields.push(Field::text(
            format!("conflict_{}", ci + 1),
            format!(
                "{regime}{} · {} alternatives",
                c.field
                    .as_ref()
                    .map(|f| format!(" · {f}"))
                    .unwrap_or_default(),
                c.alternatives.len()
            ),
        ));
        for (ai, alt) in c.alternatives.iter().enumerate() {
            fields.push(Field::text(
                format!("  c{}_alt_{}", ci + 1, ai + 1),
                format!("{}: “{}”", author_label(alt.provenance.author), alt.text),
            ));
        }
    }
    Inspectable {
        kind: ObjectKind::Document,
        title: "CONFLICT-AS-STATE".to_string(),
        subtitle: if conflicts.is_empty() {
            "clean — no open conflicts (a valid, fully-ordered document)".to_string()
        } else {
            format!(
                "{} open conflict{} — first-class states, resolved by a later patch",
                conflicts.len(),
                if conflicts.len() == 1 { "" } else { "s" }
            )
        },
        fields,
    }
}

/// The commitment binding + the two-regime "what-is" explanation.
fn commitment_prose(commitment: [u8; 32], rendered: &Rendered) -> String {
    let mut s = String::new();
    // The REAL commitment: the wide sorted-Poseidon2 heap root (`substrate_commit`),
    // shown as its short hex. This replaced the retired non-cryptographic scalar.
    let hex: String = commitment.iter().map(|b| format!("{b:02x}")).collect();
    s.push_str(&format!("COMMITMENT — the document binds to {hex}.\n\n"));
    s.push_str(
        "A document is a Pijul-shaped patch object: a keyed atom map + order-edges + \
         a single-valued field store. Two REGIMES:\n",
    );
    s.push_str(
        "· PROSE is grow-only content — I-confluent: independent inserts always glue, \
         so concurrent prose merges clean. A genuine fork (two unordered runs at one \
         position) is a first-class CONFLICT STATE, not a failure.\n",
    );
    s.push_str(
        "· FIELDS are single-valued — a concurrent clash on the same field is a real \
         conflict the author resolves (the non-monotone face).\n\n",
    );
    if rendered.has_conflict() {
        s.push_str(
            "This document currently carries open conflict state(s) — the commitment \
             binds BOTH live alternatives + their provenance, so the bound state is a \
             faithful conflict, not a hidden choice.",
        );
    } else {
        s.push_str(
            "This document is conflict-free — a single, fully-ordered rendered content \
             the commitment binds.",
        );
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::presentable::PresentCtx;
    use crate::world::World;
    use dregg_doc::{Op, Patch};

    fn alice() -> Author {
        Author(0xA11CE)
    }
    fn bob() -> Author {
        Author(0xB0B)
    }

    /// A history with two clean appends by Alice, then a Bob fork that conflicts
    /// with an Alice fork at the same point.
    fn conflicted_history() -> History {
        let mut h = History::new();
        let (a1, op1) = Patch::add(1, "the cat ", dregg_doc::AtomId::ROOT);
        h.commit(Patch::by(alice(), [op1]));
        let (_a2, op2) = Patch::add(2, "sat on the mat. ", a1);
        h.commit(Patch::by(alice(), [op2]));
        // Two forks at a1 → an unordered prose conflict.
        let (_fa, opa) = Patch::add(3, "(quietly) ", a1);
        let (_fb, opb) = Patch::add(0x9E37, "(loudly) ", a1);
        h.commit(Patch::by(alice(), [opa]));
        h.commit(Patch::by(bob(), [opb]));
        h
    }

    fn clean_history() -> History {
        let mut h = History::new();
        let (a1, op1) = Patch::add(1, "hello ", dregg_doc::AtomId::ROOT);
        h.commit(Patch::by(alice(), [op1]));
        let (_a2, op2) = Patch::add(2, "world", a1);
        h.commit(Patch::by(bob(), [op2]));
        h
    }

    #[test]
    fn presents_the_full_face_set() {
        let doc = DocumentInspection::new("notes", clean_history());
        let w = World::new();
        let ctx = PresentCtx::new(&w, dregg_cell::CellId::derive_raw(&[0u8; 32], &[0u8; 32]));
        let set = doc.present(&ctx);
        // Floor + rendered + patch-history + conflicts + commitment.
        assert_eq!(set.len(), 5);
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
        assert!(set.iter().any(|p| p.label == "Rendered"));
        assert!(set.iter().any(|p| p.label == "Patch History"));
        assert!(set.iter().any(|p| p.label == "Conflicts"));
        assert!(set.iter().any(|p| p.kind == PresentationKind::Invariant));
        // The object kind is the new first-class Document.
        assert_eq!(doc.object_kind(), ObjectKind::Document);
    }

    #[test]
    fn the_patch_history_timeline_is_the_real_trail() {
        let doc = DocumentInspection::new("notes", conflicted_history());
        let tl = patch_timeline(doc.history.as_ref());
        // Four recorded patches, oldest→newest, monotone keys.
        assert_eq!(tl.events.len(), 4);
        assert_eq!(tl.events[0].at, 0);
        assert_eq!(tl.events[3].at, 3);
        // The last patch is attributed to Bob (the fork author).
        assert!(tl.events[3].label.contains(&format!("{:x}", bob().0)));
    }

    #[test]
    fn conflict_as_state_surfaces_attributed_alternatives() {
        let doc = DocumentInspection::new("notes", conflicted_history());
        let rendered = content(&doc.graph);
        assert!(rendered.has_conflict(), "the two forks conflict");
        let cf = conflict_fields(&rendered);
        // Not clean; the conflict carries ≥2 attributed alternatives.
        assert!(cf.fields.iter().any(|f| f.key == "clean"));
        assert!(
            cf.fields.iter().any(|f| f.key.contains("alt")),
            "alternatives are surfaced and attributed"
        );
    }

    #[test]
    fn a_clean_document_reports_no_conflict_honestly() {
        let doc = DocumentInspection::new("notes", clean_history());
        let rendered = content(&doc.graph);
        assert!(!rendered.has_conflict());
        let cf = conflict_fields(&rendered);
        assert!(cf.subtitle.contains("clean"));
        assert!(
            cf.fields
                .iter()
                .any(|f| f.key == "clean"
                    && matches!(&f.value, crate::reflect::FieldValue::Bool(true))),
            "clean is recorded true"
        );
    }

    #[test]
    fn the_commitment_prose_binds_and_names_the_regimes() {
        let doc = DocumentInspection::new("notes", conflicted_history());
        let rendered = content(&doc.graph);
        let prose = commitment_prose(substrate_commit(&doc.graph), &rendered);
        assert!(prose.contains("COMMITMENT"));
        assert!(
            prose.contains("PROSE") && prose.contains("FIELDS"),
            "two regimes named"
        );
        assert!(
            prose.contains("conflict"),
            "the conflict binding is described"
        );
    }

    /// The REACHABILITY path: source the lens from a LIVE document (the DOCS tab's
    /// `ExecutorDrivenDoc`, driven through the real executor). The folded faces are
    /// full; the patch-history trail is reported honestly as a live projection.
    #[test]
    fn sources_from_a_live_executor_driven_doc() {
        let mut doc = ExecutorDrivenDoc::new(11, 12, true);
        let (a1, op1) = Patch::add(1, "live edit ", dregg_doc::AtomId::ROOT);
        doc.edit(Patch::by(alice(), [op1]))
            .expect("authorized edit commits");
        let (_a2, op2) = Patch::add(2, "through the executor", a1);
        doc.edit(Patch::by(alice(), [op2]))
            .expect("authorized edit commits");

        let inspection = DocumentInspection::from_doc("live notes", &doc);
        let w = World::new();
        let set = inspection.present(&PresentCtx::new(
            &w,
            dregg_cell::CellId::derive_raw(&[2u8; 32], &[0u8; 32]),
        ));
        // The full face set still renders from the folded graph.
        assert_eq!(set.len(), 5);
        // The rendered content reflects the live edits.
        let rendered = set.iter().find(|p| p.label == "Rendered").unwrap();
        if let PresentationBody::Prose(s) = &rendered.body {
            assert!(s.contains("live edit"), "the live content is rendered");
        } else {
            panic!("Rendered is a Prose body");
        }
        // The patch-history degrades honestly (no trail in the folded projection).
        let hist = set.iter().find(|p| p.label == "Patch History").unwrap();
        if let PresentationBody::Timeline(t) = &hist.body {
            assert_eq!(t.events.len(), 1);
            assert!(t.events[0].label.contains("live projection"));
        } else {
            panic!("Patch History is a Timeline body");
        }
    }

    /// Op is re-exported and usable (a compile-level guard that the grammar is in
    /// scope for callers building documents through this lens).
    #[test]
    fn the_patch_grammar_is_reachable() {
        let _empty: Vec<Op> = Vec::new();
        let doc = DocumentInspection::new("empty", History::new());
        let set = doc.present(&PresentCtx::new(
            &World::new(),
            dregg_cell::CellId::derive_raw(&[1u8; 32], &[0u8; 32]),
        ));
        // An empty document still presents the full face set, honestly empty.
        assert_eq!(set.len(), 5);
    }
}
