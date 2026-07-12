//! **The deos-`ViewNode` → WeChat message text renderer.** An offering's [`Surface`] is a deos
//! affordance view-tree; a WeChat Official Account text message is one plain-text blob (WeChat OA
//! forbids arbitrary per-message buttons — see the crate doc). This walks the tree into the *prose*
//! half (room text, party state, verified-turn count, section titles); the *affordance* half (the
//! [`deos_view::ViewNode::Menu`] rows / the passed [`Action`]s) is appended by
//! [`crate::api::build_present_request`] as a NUMBERED REPLY LIST, NOT a keyboard — the WeChat-native
//! way to offer dynamic choices (the user replies with the number). Same surface, a WeChat renderer.

use deos_view::ViewNode;
use dreggnet_offerings::Surface;

/// Render a [`Surface`] into WeChat message text (the *non-affordance* half of the surface).
/// [`ViewNode::Menu`]/[`ViewNode::Button`] are OMITTED here — they are rendered as the numbered
/// reply list in [`crate::api::build_present_request`], not inline in the prose. Section titles
/// head their blocks; text nodes are lines.
pub fn render_surface_text(surface: &Surface) -> String {
    let mut out = String::new();
    walk(surface.view(), 0, &mut out);
    out.trim_end().to_string()
}

fn walk(node: &ViewNode, depth: usize, out: &mut String) {
    match node {
        ViewNode::Text(t) => {
            if !t.trim().is_empty() {
                push_line(out, t.trim());
            }
        }
        ViewNode::Section {
            title, children, ..
        } => {
            if !title.trim().is_empty() {
                let heading = if depth == 0 {
                    title.trim().to_string()
                } else {
                    format!("— {}", title.trim())
                };
                push_line(out, &heading);
            }
            for c in children {
                walk(c, depth + 1, out);
            }
        }
        ViewNode::VStack(children) | ViewNode::Row(children) | ViewNode::List(children) => {
            for c in children {
                walk(c, depth, out);
            }
        }
        // The affordance half — rendered as the numbered reply list, not inline prose.
        ViewNode::Menu { .. } | ViewNode::Button { .. } => {}
        // Any other leaf/container: best-effort, so a richer offering surface still degrades to
        // readable text rather than dropping content silently.
        other => {
            if let Some(children) = child_slice(other) {
                for c in children {
                    walk(c, depth, out);
                }
            }
        }
    }
}

/// Children of the container variants we do not special-case (so future richer surfaces still
/// render their contents). `None` for leaves.
fn child_slice(node: &ViewNode) -> Option<&[ViewNode]> {
    match node {
        ViewNode::Table(children) => Some(children),
        _ => None,
    }
}

fn push_line(out: &mut String, line: &str) {
    if !out.is_empty() {
        out.push('\n');
    }
    out.push_str(line);
}
