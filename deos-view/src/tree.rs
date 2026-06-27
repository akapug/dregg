//! The **view-tree model** — the Rust shape of the deos-js `deos.ui.*` element-tree.
//!
//! `deos-js` builds a *serializable* element-tree (data, NOT gpui) in real
//! SpiderMonkey: `deos.ui.{vstack,row,text,bind,button,input,list,table}`. A button's
//! `onClick` is `{turn, arg}`; a `bind(()=>expr)` is a fine-grained signal binding.
//! That JS object is `JSON.stringify`-ed by the engine and read back into Rust (see
//! [`crate::bridge`]); this module is the Rust mirror it parses into. The renderer
//! ([`crate::render`]) walks this tree into real gpui-component widgets.
//!
//! NOTE on `bind`: `JSON.stringify` drops the closure (`node.read` is a function), so
//! a serialized `bind` node carries only `kind:"bind"`. The renderer re-reads the
//! bound value off the live applet ledger directly (the binding IS `app.get(slot)`),
//! which is the same witnessed read the JS closure made — see [`ViewNode::Bind`].

use serde::Deserialize;

/// A node of the view-tree, mirroring the JS `deos.ui.*` shape exactly.
///
/// The JS shape is `{ kind, props, children? , read? }`. We deserialize via the raw
/// [`RawNode`] (a faithful JSON mirror) and lift it into this typed enum so the
/// renderer matches on real variants.
#[derive(Debug, Clone)]
pub enum ViewNode {
    /// `vstack(...children)` → a vertical column (`v_flex`).
    VStack(Vec<ViewNode>),
    /// `row(...children)` → a horizontal row (`h_flex`).
    Row(Vec<ViewNode>),
    /// `text(s)` → a `Label`.
    Text(String),
    /// `bind(() => expr)` → a signal binding. The closure does not survive
    /// serialization; the renderer re-reads the bound value off the live ledger
    /// (the model slot the JS closure read). `slot` is the model slot to re-read
    /// (the counter shape binds slot 0); `label` is an optional prefix.
    Bind { slot: usize, label: String },
    /// `button(label, aff, arg)` → a `Button` whose onClick fires affordance `turn`
    /// with `arg` (a REAL cap-gated verified turn through the applet).
    Button {
        label: String,
        turn: String,
        arg: i64,
    },
    /// `input(viewKey)` → a text input bound to ephemeral view-state `bind_view`.
    Input { bind_view: String },
    /// `list(items)` → a vertical list of child nodes.
    List(Vec<ViewNode>),
    /// `table(rows)` → a table; each row is itself a node (a `row` of cells).
    Table(Vec<ViewNode>),

    // ── The RICHNESS EXPANSION (docs/deos/DEOS-VIEW-RICHNESS-EXPANSION.md) — growing the
    //    vocabulary toward native-cockpit parity so liberating a surface into a card is
    //    LOSSLESS. Batch 1: a container, an actuation+selection node, a bound visual, a leaf.
    /// `section(title, ...children)` → a titled, bordered container (the uniform "styled
    /// section"). `tag` selects a styling accent (the existing `props.tag` convention —
    /// `genuine`/`refusal`/…). Unlocks Organs, the Trust/Devtools blocks, every panel's
    /// `section_title` + bordered-box idiom.
    Section {
        title: String,
        tag: String,
        children: Vec<ViewNode>,
    },
    /// `tabs({tabs, selectedSlot, selectTurn}, ...panels)` → a tab-strip whose visible panel
    /// is bound to model slot `selected_slot`. A tab click fires `select_turn` with `arg =
    /// the tab index` (a REAL verified turn that writes the slot). Unlocks Lanes, Devtools,
    /// Moldable. The renderer walks ALL panels (keeping the bind cursor aligned) and displays
    /// only the selected one.
    Tabs {
        /// The tab labels, one per panel (in `panels` order).
        tabs: Vec<String>,
        /// The model slot holding the active tab index (read live each paint).
        selected_slot: usize,
        /// The affordance a tab click fires (`arg` is the clicked tab's index).
        select_turn: String,
        /// The tab bodies — one per label; only the selected one is displayed.
        panels: Vec<ViewNode>,
    },
    /// `gauge({slot, max, label})` → a bound progress / balance bar. The fill is
    /// `get_u64(slot) / max`, clamped to `[0,1]`. Reads its slot IMMEDIATE-MODE (it does not
    /// consume the tree-walk bind cursor — it is not a `Bind`). Unlocks `face_gauge`, the
    /// Time liveness bar, any "glow = activity" indicator.
    Gauge {
        slot: usize,
        max: u64,
        label: String,
    },
    /// `divider()` → a thin full-width horizontal rule (a groove / separator). A pure leaf.
    Divider,
}

/// The raw JSON mirror of a `deos.ui.*` node (`{ kind, props, children }`). The
/// engine's `JSON.stringify(tree)` produces exactly this; we then [`RawNode::lift`]
/// it into the typed [`ViewNode`].
#[derive(Debug, Clone, Deserialize)]
pub struct RawNode {
    pub kind: String,
    #[serde(default)]
    pub props: RawProps,
    #[serde(default)]
    pub children: Vec<RawNode>,
}

/// The raw `props` bag — every field optional (a node uses only the ones for its kind).
#[derive(Debug, Clone, Default, Deserialize)]
pub struct RawProps {
    #[serde(default)]
    pub text: Option<String>,
    #[serde(default)]
    pub label: Option<String>,
    // The JS prelude (`deos.ui.button`) emits the camelCase key `onClick`; deserialize it
    // by that name (with the snake_case alias kept) so the affordance `{turn, arg}` the
    // engine produced survives the parse into BOTH renderers — the native `Button`'s
    // on_click AND the web `<button data-turn data-arg>`. Without the rename the engine's
    // `onClick` silently dropped to a `{turn:"", arg:0}` default.
    #[serde(default, rename = "onClick", alias = "on_click")]
    pub on_click: Option<RawOnClick>,
    #[serde(default, rename = "bindView", alias = "bind_view")]
    pub bind_view: Option<String>,
    /// For a `bind` node the renderer needs to know WHICH model slot to re-read.
    /// The JS closure isn't serializable, so the applet author tags the bind node's
    /// props with `slot` (the counter shape uses slot 0). Absent → slot 0. Also the
    /// model slot a `gauge` reads its fill ratio from.
    #[serde(default)]
    pub slot: Option<usize>,

    // ── The richness-expansion props (batch 1: section / tabs / gauge). Every field
    //    optional; a node reads only the ones for its kind (the raw `props` bag idiom). ──
    /// A `section`'s header title.
    #[serde(default)]
    pub title: Option<String>,
    /// A styling accent / disclosure tag (`section`, `pill`, …): the existing `props.tag`
    /// convention (`genuine`/`refusal`/…), reused by the disclosure filter.
    #[serde(default)]
    pub tag: Option<String>,
    /// A `gauge`'s denominator (the fill is `slot_value / max`, clamped to `[0,1]`).
    #[serde(default)]
    pub max: Option<u64>,
    /// A `tabs` node's tab labels, one per panel (camelCase `tabs`, snake alias).
    #[serde(default, alias = "tab_labels")]
    pub tabs: Option<Vec<String>>,
    /// A `tabs` node's model slot holding the active tab index (camelCase `selectedSlot`).
    #[serde(default, rename = "selectedSlot", alias = "selected_slot")]
    pub selected_slot: Option<usize>,
    /// A `tabs` node's select affordance (`arg` is the clicked tab index; camelCase).
    #[serde(default, rename = "selectTurn", alias = "select_turn")]
    pub select_turn: Option<String>,
}

/// `onClick = { turn, arg }` — the affordance a button fires.
#[derive(Debug, Clone, Deserialize)]
pub struct RawOnClick {
    pub turn: String,
    #[serde(default)]
    pub arg: i64,
}

impl RawNode {
    /// Lift a raw JSON node into the typed [`ViewNode`]. An unknown kind renders as a
    /// labelled placeholder text (honest: the renderer shows what it could not map).
    pub fn lift(&self) -> ViewNode {
        let kids = || self.children.iter().map(|c| c.lift()).collect::<Vec<_>>();
        match self.kind.as_str() {
            "vstack" => ViewNode::VStack(kids()),
            "row" => ViewNode::Row(kids()),
            "text" => ViewNode::Text(self.props.text.clone().unwrap_or_default()),
            "bind" => ViewNode::Bind {
                slot: self.props.slot.unwrap_or(0),
                label: self.props.label.clone().unwrap_or_default(),
            },
            "button" => {
                let oc = self.props.on_click.clone().unwrap_or(RawOnClick {
                    turn: String::new(),
                    arg: 0,
                });
                ViewNode::Button {
                    label: self.props.label.clone().unwrap_or_default(),
                    turn: oc.turn,
                    arg: oc.arg,
                }
            }
            "input" => ViewNode::Input {
                bind_view: self.props.bind_view.clone().unwrap_or_default(),
            },
            "list" => ViewNode::List(kids()),
            "table" => ViewNode::Table(kids()),
            "section" => ViewNode::Section {
                title: self.props.title.clone().unwrap_or_default(),
                tag: self.props.tag.clone().unwrap_or_default(),
                children: kids(),
            },
            "tabs" => ViewNode::Tabs {
                tabs: self.props.tabs.clone().unwrap_or_default(),
                selected_slot: self.props.selected_slot.unwrap_or(0),
                select_turn: self.props.select_turn.clone().unwrap_or_default(),
                panels: kids(),
            },
            "gauge" => ViewNode::Gauge {
                slot: self.props.slot.unwrap_or(0),
                max: self.props.max.unwrap_or(0),
                label: self.props.label.clone().unwrap_or_default(),
            },
            "divider" => ViewNode::Divider,
            other => ViewNode::Text(format!("‹unmapped node: {other}›")),
        }
    }
}

/// Parse the engine's `JSON.stringify(viewTree)` string into a typed [`ViewNode`].
pub fn parse_view_tree(json: &str) -> Result<ViewNode, String> {
    let raw: RawNode = serde_json::from_str(json).map_err(|e| format!("view-tree JSON: {e}"))?;
    Ok(raw.lift())
}
