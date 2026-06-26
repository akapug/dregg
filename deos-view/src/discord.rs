//! The **Discord renderer** — walk the SAME deos-js view-tree into a Discord embed
//! (+ message components).
//!
//! This is the *Discord projection* of the reflective cockpit, the FOURTH backend over
//! the one [`ViewNode`] IR. The native renderer ([`crate::render`], gpui-gated) turns a
//! [`ViewNode`] into gpui-component widgets; the web renderer ([`crate::web`]) turns the
//! IDENTICAL tree into an HTML string; the seL4 path bakes it to a framebuffer; and THIS
//! renderer turns the IDENTICAL tree into a serenity [`CreateEmbed`] + a `Vec` of
//! [`CreateActionRow`] button rows. Same data, four renderers — the card is
//! renderer-INDEPENDENT. The discord-bot's surfaces ARE these cards.
//!
//! It is gpui-FREE and deos-js-FREE: it depends on nothing but [`crate::tree`] (serde)
//! and serenity's builder/model types. So `cargo build -p deos-view --no-default-features
//! --features discord` compiles a small graph — no GPU, no SpiderMonkey — and a bot that
//! holds a [`ViewNode`] gets the SAME card the desktop renders, as a Discord message.
//!
//! ## The vocabulary mirrors the gpui/web renderers
//!
//! Discord's embed model is flatter than the DOM, so the mapping projects the tree onto
//! an embed's `title` / `description` / `fields[]` plus a button-component grid:
//!
//! | view-tree node      | web ([`crate::web`])         | discord (here)                          |
//! |---------------------|------------------------------|-----------------------------------------|
//! | `vstack`/`list`     | `<div>` container            | a block container (children flow on)    |
//! | `row`               | `<div class="deos-row">`     | ONE embed FIELD (name = first part,      |
//! |                     |                              | value = the rest; its buttons → grid)   |
//! | `table`             | `<div class="deos-table">`   | one embed FIELD per row                  |
//! | `text(s)`           | `<span class="deos-text">`   | a line of the embed description          |
//! | `bind{slot,label}`  | `data-slot` span, live value | the live value, in the description/field |
//! | `button{turn,arg}`  | `<button data-turn data-arg>`| a button component, the affordance in    |
//! |                     |                              | its `custom_id` (`deosturn:<turn>:<arg>`)|
//! | `input{bindView}`   | `<span class="deos-input">`  | a `‹bindView›` placeholder in the text   |
//!
//! ## The affordance round-trip (the `data-turn` of Discord)
//!
//! The web renderer carries a button's `{turn, arg}` as `data-turn`/`data-arg`; Discord's
//! equivalent is the component **custom-id**. A [`ViewNode::Button`] becomes a
//! [`CreateButton`] whose custom-id is [`affordance_custom_id`] (`deosturn:<turn>:<arg>`);
//! a bot's component handler decodes it with [`parse_affordance_id`] and fires it as a
//! REAL cap-gated verified turn — the exact payload the native `Button` fires through
//! `Applet::fire`. The button is the affordance, renderer-independent.

use crate::tree::ViewNode;
use serenity::all::{ButtonStyle, CreateActionRow, CreateButton, CreateEmbed};

/// The custom-id prefix carrying a [`ViewNode::Button`]'s affordance through Discord's
/// component-id channel — the Discord analogue of the web renderer's `data-turn`.
pub const TURN_PREFIX: &str = "deosturn";

/// A rendered card, ready to post: the [`CreateEmbed`] (title/description/fields) plus the
/// button [`CreateActionRow`]s (the affordances). A bot may further chain `.color()`,
/// `.footer()`, etc. onto the embed before sending (the renderer sets only the structural
/// shape from the tree — color/footer are presentation the surface owns).
pub struct DiscordCard {
    /// The embed mirroring the tree's text/bind/row/table structure.
    pub embed: CreateEmbed,
    /// The button rows (≤5 rows × ≤5 buttons), one button per [`ViewNode::Button`].
    pub components: Vec<CreateActionRow>,
}

/// The custom-id a [`ViewNode::Button`] firing `turn` with `arg` carries
/// (`deosturn:<turn>:<arg>`) — the affordance payload, routed back on press.
pub fn affordance_custom_id(turn: &str, arg: i64) -> String {
    format!("{TURN_PREFIX}:{turn}:{arg}")
}

/// Decode a button-component custom-id minted by [`affordance_custom_id`] back into its
/// `(turn, arg)` affordance — what a bot's component handler fires as a verified turn. A
/// custom-id that is not one of ours returns `None` (the handler ignores it).
pub fn parse_affordance_id(custom_id: &str) -> Option<(String, i64)> {
    let mut it = custom_id.splitn(3, ':');
    if it.next()? != TURN_PREFIX {
        return None;
    }
    let turn = it.next()?.to_string();
    let arg = it.next()?.parse().ok()?;
    Some((turn, arg))
}

/// The accumulator the tree-walk fills: an embed description, its fields, and the button
/// affordances (in tree-walk order — the SAME order the web renderer's `data-slot` binds /
/// the native `BindingId`s appear).
#[derive(Default)]
struct Accum {
    description: String,
    fields: Vec<(String, String, bool)>,
    buttons: Vec<(String, String)>,
}

/// Render a view-tree to a Discord [`DiscordCard`]. `title` heads the embed; `bind_values[n]`
/// is the live value of the `n`th `bind` node (tree-walk/pre-order, like the web renderer);
/// a missing index paints `0` (an un-driven bind). The structural shape (description, fields,
/// buttons) comes from the tree; the caller adds color/footer as it likes.
pub fn render_card(title: &str, tree: &ViewNode, bind_values: &[u64]) -> DiscordCard {
    let mut acc = Accum::default();
    let mut cursor = 0usize;
    block(tree, bind_values, &mut cursor, &mut acc);

    let mut embed = CreateEmbed::new().title(title);
    let desc = acc.description.trim_end();
    if !desc.is_empty() {
        embed = embed.description(desc.to_string());
    }
    // Discord caps an embed at 25 fields; a field's name AND value must be non-empty.
    for (name, value, inline) in acc.fields.into_iter().take(25) {
        embed = embed.field(or_blank(name, "·"), or_blank(value, "\u{200b}"), inline);
    }

    DiscordCard {
        embed,
        components: button_rows(acc.buttons),
    }
}

/// The block-level walker — mirrors [`crate::web::render_html`]'s pre-order walk so the bind
/// cursor advances in the SAME order. A `row`/`table` becomes embed FIELD(s); everything
/// else flows into the description (or, for a `button`, the component grid).
fn block(n: &ViewNode, binds: &[u64], cursor: &mut usize, acc: &mut Accum) {
    match n {
        ViewNode::VStack(children) | ViewNode::List(children) => {
            for c in children {
                block(c, binds, cursor, acc);
            }
        }
        ViewNode::Table(rows) => {
            for r in rows {
                row_field(r, binds, cursor, acc);
            }
        }
        ViewNode::Row(_) => row_field(n, binds, cursor, acc),
        ViewNode::Text(s) => push_line(&mut acc.description, s),
        ViewNode::Bind { label, .. } => {
            let value = binds.get(*cursor).copied().unwrap_or(0);
            *cursor += 1;
            push_line(&mut acc.description, &format!("{label}{value}"));
        }
        ViewNode::Button { label, turn, arg } => {
            acc.buttons
                .push((label.clone(), affordance_custom_id(turn, *arg)));
        }
        ViewNode::Input { bind_view } => {
            push_line(
                &mut acc.description,
                &format!("\u{2039}{bind_view}\u{203a}"),
            );
        }
    }
}

/// Render one `row` (or `table` row) as a single embed field: the first inline part is the
/// field NAME, the rest its VALUE; any buttons in the row join the component grid (so the
/// tally row `[text(name), bind(value), button(+1), button(−1)]` becomes a `name → value`
/// field plus its two buttons).
fn row_field(n: &ViewNode, binds: &[u64], cursor: &mut usize, acc: &mut Accum) {
    let mut parts: Vec<String> = Vec::new();
    inline(n, binds, cursor, &mut parts, &mut acc.buttons);
    let name = if parts.is_empty() {
        String::new()
    } else {
        parts.remove(0)
    };
    let value = parts.join(" ");
    acc.fields.push((name, value, true));
}

/// Collect a row's inline parts (text / bind values) and its buttons, recursing through any
/// nested layout. Advances the bind cursor in pre-order (consistent with [`block`]).
fn inline(
    n: &ViewNode,
    binds: &[u64],
    cursor: &mut usize,
    parts: &mut Vec<String>,
    buttons: &mut Vec<(String, String)>,
) {
    match n {
        ViewNode::Row(children) | ViewNode::VStack(children) | ViewNode::List(children) => {
            for c in children {
                inline(c, binds, cursor, parts, buttons);
            }
        }
        ViewNode::Table(rows) => {
            for r in rows {
                inline(r, binds, cursor, parts, buttons);
            }
        }
        ViewNode::Text(s) => {
            if !s.is_empty() {
                parts.push(s.clone());
            }
        }
        ViewNode::Bind { label, .. } => {
            let value = binds.get(*cursor).copied().unwrap_or(0);
            *cursor += 1;
            parts.push(format!("{label}{value}"));
        }
        ViewNode::Button { label, turn, arg } => {
            buttons.push((label.clone(), affordance_custom_id(turn, *arg)));
        }
        ViewNode::Input { bind_view } => parts.push(format!("\u{2039}{bind_view}\u{203a}")),
    }
}

/// Chunk the collected affordances into Discord button rows (≤5 buttons/row, ≤5 rows). Each
/// button carries its affordance in the custom-id ([`affordance_custom_id`]) — the press
/// payload a bot decodes with [`parse_affordance_id`].
fn button_rows(buttons: Vec<(String, String)>) -> Vec<CreateActionRow> {
    buttons
        .chunks(5)
        .take(5)
        .map(|chunk| {
            CreateActionRow::Buttons(
                chunk
                    .iter()
                    .map(|(label, id)| CreateButton::new(id).label(label).style(style_for(label)))
                    .collect(),
            )
        })
        .collect()
}

/// A cosmetic button style by label (the gate is the cap gate, not the color): a `+`-ish
/// label is constructive (green), a `−`/`del`/`burn`-ish one destructive (red), else primary.
fn style_for(label: &str) -> ButtonStyle {
    let l = label.to_lowercase();
    if label.starts_with('+') || l.contains("approve") || l.contains("add") {
        ButtonStyle::Success
    } else if label.starts_with('-')
        || label.starts_with('\u{2212}')
        || l.contains("del")
        || l.contains("burn")
        || l.contains("remove")
    {
        ButtonStyle::Danger
    } else {
        ButtonStyle::Primary
    }
}

/// Append `s` as a line of the description (newline-separated, no leading blank line).
fn push_line(desc: &mut String, s: &str) {
    if !desc.is_empty() {
        desc.push('\n');
    }
    desc.push_str(s);
}

/// A Discord field name/value must be non-empty; substitute `fallback` for an empty string.
fn or_blank(s: String, fallback: &str) -> String {
    if s.is_empty() {
        fallback.to_string()
    } else {
        s
    }
}
