//! **The Telegram text backend** — walk a [`ViewNode`] IR into Telegram message text.
//!
//! A Telegram message is plain text plus an inline keyboard. This is the *text* half: room prose,
//! party state, section titles. The affordance half (a [`ViewNode::Menu`]/[`ViewNode::Button`])
//! becomes the inline keyboard the frontend builds from the passed actions, NOT text — so those
//! nodes are omitted here.
//!
//! This is the moved-in `dreggnet-telegram::render::walk` (formerly a subset walker in the
//! frontend crate); here it covers the container variants an affordance can nest inside, so a
//! nested section/text is rendered rather than dropped.

use crate::affordance::AffordanceTransport;
use crate::backend::SurfaceBackend;
use crate::tree::ViewNode;

/// **Render a [`ViewNode`] surface into Telegram message text** (the *non-affordance* half).
/// [`ViewNode::Menu`]/[`ViewNode::Button`] are OMITTED (rendered as the inline keyboard, not text);
/// section titles head their blocks; text nodes are lines. Trailing whitespace is trimmed.
pub fn render_text(tree: &ViewNode) -> String {
    let mut out = String::new();
    walk(tree, 0, &mut out);
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
                // A bold-ish heading (kept plain-text; a live bot could set MarkdownV2).
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
        // The affordance half — rendered as the inline keyboard, not as text.
        ViewNode::Menu { .. } | ViewNode::Button { .. } => {}
        // Full node coverage: the remaining containers recurse (an affordance/section nested in a
        // Table/Grid/Tabs/Host/Adept still contributes its text) rather than dropping silently.
        ViewNode::Table(children) | ViewNode::Grid { children, .. } => {
            for c in children {
                walk(c, depth, out);
            }
        }
        ViewNode::Tabs { panels, .. } => {
            for p in panels {
                walk(p, depth, out);
            }
        }
        ViewNode::Host { view: Some(v), .. } => walk(v, depth, out),
        ViewNode::Adept(inner) => walk(inner, depth, out),
        // The bound/indicator leaves have no plain-text projection here.
        _ => {}
    }
}

fn push_line(out: &mut String, line: &str) {
    if !out.is_empty() {
        out.push('\n');
    }
    out.push_str(line);
}

/// **The Telegram [`SurfaceBackend`]** — the [`ViewNode`] IR → message text ([`render_text`]).
/// Binds are unused (Telegram text has no in-place live re-read); [`decode`](SurfaceBackend::decode)
/// uses the Telegram affordance codec (`<turn>:<arg>` `callback_data`).
pub struct TelegramBackend;

impl SurfaceBackend for TelegramBackend {
    type Rendered = String;

    fn transport(&self) -> AffordanceTransport {
        AffordanceTransport::Telegram
    }

    fn render(&self, tree: &ViewNode, _binds: &[u64]) -> String {
        render_text(tree)
    }
}
