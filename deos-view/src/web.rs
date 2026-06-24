//! The **web renderer** — walk the SAME deos-js view-tree into an HTML/DOM string.
//!
//! This is the *web projection* of the reflective cockpit. The native renderer
//! ([`crate::render`], gpui-gated) turns a [`ViewNode`] into gpui-component widgets;
//! THIS renderer turns the IDENTICAL [`ViewNode`] into HTML. Same data, two renderers
//! — the card is renderer-INDEPENDENT. It paints in a browser, not just the native
//! cockpit.
//!
//! It is gpui-FREE and deos-js-FREE: it depends on nothing but [`crate::tree`] (which
//! is `serde` only). So `cargo build -p deos-view --no-default-features --features web`
//! compiles a tiny graph — no GPU, no SpiderMonkey — and the `web_render_card` example
//! bakes a browser-loadable `.html`.
//!
//! ## The vocabulary mirrors the gpui renderer one-for-one
//!
//! | view-tree node      | gpui ([`crate::render`])    | web (here)                              |
//! |---------------------|------------------------------|-----------------------------------------|
//! | `vstack(...kids)`   | `v_flex().gap_2().p_3()`     | `<div class="deos-vstack">`             |
//! | `row(...kids)`      | `h_flex().gap_2()`           | `<div class="deos-row">`                |
//! | `text(s)`           | `Label`                      | `<span class="deos-text">`              |
//! | `bind{slot,label}`  | bold `Label`, live re-read   | `<span class="deos-bind" data-slot>`    |
//! | `button{label,...}` | `Button`, onClick fires turn | `<button data-turn data-arg>`           |
//! | `input{bindView}`   | bordered draft field         | `<span class="deos-input">`             |
//! | `list` / `table`    | `v_flex` of children         | `<div class="deos-list/table">`         |
//!
//! ## What is real vs. the seam
//!
//! - **Real here:** the SAME serializable [`ViewNode`] the SpiderMonkey engine produced
//!   (parsed by [`crate::parse_view_tree`]) walks into HTML; a `bind` carries its live
//!   value (read off the applet ledger and passed in) AND the `data-slot` it re-reads; a
//!   `button` carries its affordance `{turn, arg}` as `data-turn`/`data-arg` — the exact
//!   payload a click must fire. The produced document is a real, browser-loadable file.
//! - **The seam (named, not papered):** wiring a browser button-click back to a REAL
//!   cap-gated verified turn needs the executor reachable from the browser. That is the
//!   wasm bridge (`wasm/` `bindings*.rs` already exposes the verifier/turn surface to
//!   JS): a click POSTs `{turn, arg}` to a node, or drives an in-browser wasm executor,
//!   and the receipt re-reads the bound slots. The bake here renders the view + carries
//!   every affordance payload; the live-turn wire is the documented follow-on, exactly
//!   as the native path's live turn is `Applet::fire`.

use crate::tree::ViewNode;

/// The live values of the `bind` nodes, in tree-walk (pre-order) appearance — the SAME
/// order the native renderer's `bind_plan` mints `BindingId`s in. Element `n` is the value the
/// `n`th `bind` node shows. A caller that has a live applet reads these off the ledger
/// (`applet.get_u64(slot)`, the witnessed read); a static bake passes the snapshot it
/// wants to paint. `None`/short → the renderer falls back to `0` (an un-driven bind).
pub type BindValues = [u64];

/// Render a view-tree to an HTML fragment string (no `<html>`/`<head>` — just the card's
/// markup). `bind_values[n]` is the live value of the `n`th `bind` node (tree-walk order);
/// a missing index paints `0`. Use [`render_card_document`] for a full browser-loadable page.
pub fn render_html(tree: &ViewNode, bind_values: &BindValues) -> String {
    let mut out = String::new();
    let mut bind_cursor = 0usize;
    node(tree, bind_values, &mut bind_cursor, &mut out);
    out
}

/// The recursive walker — mirrors [`crate::render::AppletView::node`] node-for-node.
fn node(n: &ViewNode, binds: &BindValues, cursor: &mut usize, out: &mut String) {
    match n {
        ViewNode::VStack(children) => {
            out.push_str("<div class=\"deos-vstack\">");
            for c in children {
                node(c, binds, cursor, out);
            }
            out.push_str("</div>");
        }
        ViewNode::Row(children) => {
            out.push_str("<div class=\"deos-row\">");
            for c in children {
                node(c, binds, cursor, out);
            }
            out.push_str("</div>");
        }
        ViewNode::Text(s) => {
            out.push_str("<span class=\"deos-text\">");
            out.push_str(&escape(s));
            out.push_str("</span>");
        }
        ViewNode::Bind { slot, label } => {
            // THE SIGNAL BINDING — paint the live value (the same witnessed read the JS
            // closure / gpui `bind` made), and carry `data-slot` so a browser re-read
            // after a turn knows which slot to refresh (the fine-grained signal source).
            let value = binds.get(*cursor).copied().unwrap_or(0);
            *cursor += 1;
            let text = if label.is_empty() {
                value.to_string()
            } else {
                format!("{label}{value}")
            };
            out.push_str(&format!(
                "<span class=\"deos-bind\" data-slot=\"{slot}\">{}</span>",
                escape(&text)
            ));
        }
        ViewNode::Button { label, turn, arg } => {
            // THE AFFORDANCE — carry `{turn, arg}` as data-attributes: the exact payload
            // a click must fire as a REAL cap-gated verified turn through the executor
            // (the wasm/node bridge — the named seam). The button is rendered + wired with
            // its payload; the live turn is the documented follow-on (see module docs).
            out.push_str(&format!(
                "<button class=\"deos-button\" data-turn=\"{}\" data-arg=\"{}\">{}</button>",
                escape(turn),
                arg,
                escape(label)
            ));
        }
        ViewNode::Input { bind_view } => {
            out.push_str(&format!(
                "<span class=\"deos-input\" data-bind-view=\"{}\">&lsaquo;{}&rsaquo;</span>",
                escape(bind_view),
                escape(bind_view)
            ));
        }
        ViewNode::List(items) => {
            out.push_str("<div class=\"deos-list\">");
            for it in items {
                node(it, binds, cursor, out);
            }
            out.push_str("</div>");
        }
        ViewNode::Table(rows) => {
            out.push_str("<div class=\"deos-table\">");
            for r in rows {
                node(r, binds, cursor, out);
            }
            out.push_str("</div>");
        }
    }
}

/// A full, standalone, browser-loadable HTML document for a card. `title` heads the page;
/// `bind_values` are the live `bind` values to paint (tree-walk order). Styling mirrors
/// the cockpit's dark theme (the same dark-mode the gpui `headless` bake forces) so the
/// browser projection LOOKS like the native one. Open the written file in any browser.
pub fn render_card_document(title: &str, tree: &ViewNode, bind_values: &BindValues) -> String {
    let body = render_html(tree, bind_values);
    format!(
        "<!doctype html>\n\
<html lang=\"en\">\n\
<head>\n\
<meta charset=\"utf-8\">\n\
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
<title>{title}</title>\n\
<style>{CSS}</style>\n\
</head>\n\
<body>\n\
<main class=\"deos-card\">{body}</main>\n\
<script>{JS}</script>\n\
</body>\n\
</html>\n",
        title = escape(title),
        CSS = CSS,
        JS = JS,
    )
}

/// HTML-escape text content / attribute values (the view-tree carries author/cell data).
fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

/// The card styling — mirrors the cockpit dark theme so the browser projection matches
/// the gpui `headless` dark-mode bake. `deos-vstack`/`deos-row` are flex; the button is
/// the cockpit's primary accent.
const CSS: &str = "
:root{--bg:#121317;--fg:#e6e7eb;--muted:#9aa0aa;--accent:#5b8cff;--border:#2a2c33;}
*{box-sizing:border-box;}
body{margin:0;background:var(--bg);color:var(--fg);font-family:'IBM Plex Sans',system-ui,sans-serif;display:flex;justify-content:center;padding:2rem;}
.deos-card{background:#181a20;border:1px solid var(--border);border-radius:10px;padding:.5rem;min-width:240px;}
.deos-vstack{display:flex;flex-direction:column;gap:.5rem;padding:.75rem;}
.deos-row{display:flex;flex-direction:row;gap:.5rem;align-items:center;}
.deos-text{color:var(--fg);}
.deos-bind{font-weight:700;color:var(--fg);}
.deos-input{padding:.25rem .5rem;border:1px solid var(--border);border-radius:4px;color:var(--muted);}
.deos-button{background:var(--accent);color:#fff;border:none;border-radius:6px;padding:.4rem .8rem;font:inherit;cursor:pointer;}
.deos-button:hover{filter:brightness(1.1);}
.deos-list,.deos-table{display:flex;flex-direction:column;gap:.25rem;}
.deos-table{border:1px solid var(--border);border-radius:6px;padding:.25rem;}
";

/// The browser-side affordance wire — a button click reads its `data-turn`/`data-arg`
/// and dispatches a `deos-affordance` CustomEvent carrying that payload. The LIVE turn
/// (POST to a node / an in-browser wasm executor, then re-read the bound slots) is the
/// named seam an embedding fills; this proves the affordance payload survives the web
/// projection intact (the click carries exactly the `{turn, arg}` the native `Button`
/// fires through `Applet::fire`).
const JS: &str = "
document.querySelectorAll('.deos-button').forEach(function(b){
  b.addEventListener('click', function(){
    var turn = b.getAttribute('data-turn');
    var arg = parseInt(b.getAttribute('data-arg') || '0', 10);
    // SEAM: dispatch the affordance payload. An embedding listens for this and fires a
    // REAL cap-gated verified turn (node POST or in-browser wasm executor), then re-reads
    // the bound slots. Here we surface it (so the wire is demonstrable, not papered).
    document.dispatchEvent(new CustomEvent('deos-affordance', {detail:{turn:turn, arg:arg}}));
    console.log('deos affordance:', turn, arg);
  });
});
";
