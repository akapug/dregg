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

    // ── The COMPOSITION KEYSTONE (docs/deos/CELL-HOSTED-VIEWTREE.md) — a cell is a
    //    first-class hostable COMPONENT whose committed heap stores its own evolving
    //    view-tree; `host` MOUNTS that whole tree here as a subtree. This is distinct from
    //    `bind` (reads ONE scalar value off `(cell, slot)`) and from value-transclusion (a
    //    value snapshot from another cell): `host` mounts an ENTIRE view-tree sourced from the
    //    hosted cell's committed heap. Hosted trees contain `host` nodes for OTHER cells →
    //    fractal recursion (cells-host-cells-host-view-trees, to arbitrary depth). ──
    /// `host(cellId)` → mount the hosted cell's WHOLE view-tree here, as a subtree.
    ///
    /// `cell` is the hosted cell's id (hex). `view` is the RESOLVED hosted view-tree:
    /// - `None` — an UNRESOLVED mount (a bare reference). The renderer paints an honest
    ///   `‹mount cell …: unresolved›` placeholder until [`resolve_mounts`] fills it from the
    ///   cell's committed heap (the cell-heap-as-view-source — see [`crate::mount`]).
    /// - `Some(tree)` — the resolved/provided subtree, mounted whole. A resolver emits this;
    ///   an author may also carry a pre-baked subtree inline (the first-cut provided source).
    ///
    /// `host` stays PURE DATA (a cell-id string + an optional resolved subtree, NO live
    /// `Applet`/`Ledger` handle) so the gpui-free + deos-js-free `web`/`discord` renderers
    /// walk the IDENTICAL resolved tree — the heap read happens OUTSIDE the IR, at the
    /// boundary, and the result is spliced back in. The hosted subtree participates in the
    /// SAME pre-order bind cursor (every renderer recurses `view` at the host's position).
    Host {
        cell: String,
        view: Option<Box<ViewNode>>,
    },
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
    /// A `host` node's hosted cell id (hex) — the mount reference. The hosted cell's WHOLE
    /// view-tree is read from its committed heap and mounted here (see [`ViewNode::Host`]).
    #[serde(default, alias = "cellId")]
    pub cell: Option<String>,
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
            // `host(cellId)` — a child (if present) is the provided/pre-baked hosted subtree;
            // no child = an UNRESOLVED mount (filled later from the cell heap by
            // [`resolve_mounts`]). At most one hosted subtree (a host mounts ONE cell's tree).
            "host" => ViewNode::Host {
                cell: self.props.cell.clone().unwrap_or_default(),
                view: self.children.first().map(|c| Box::new(c.lift())),
            },
            other => ViewNode::Text(format!("‹unmapped node: {other}›")),
        }
    }
}

/// A source of cells' hosted view-trees — the cell-heap-as-view-source seen abstractly. A
/// [`resolve_mounts`] walk asks it for the hosted view-tree of each [`ViewNode::Host`]'s
/// cell. The native [`crate::mount`] impl reads the tree out of the cell's committed heap;
/// tests / provided sources use an in-memory [`MapMountSource`]. Any
/// `Fn(&str) -> Option<ViewNode>` is a `MountSource` (the blanket impl below).
pub trait MountSource {
    /// The hosted view-tree of `cell` (hex id), or `None` if the cell hosts no tree (the
    /// host then stays an unresolved placeholder — honest, never a crash).
    fn hosted_tree(&self, cell: &str) -> Option<ViewNode>;
}

impl<F: Fn(&str) -> Option<ViewNode>> MountSource for F {
    fn hosted_tree(&self, cell: &str) -> Option<ViewNode> {
        self(cell)
    }
}

/// An in-memory `cell-id → hosted view-tree` source (a provided source / the test source).
#[derive(Debug, Default, Clone)]
pub struct MapMountSource(pub std::collections::BTreeMap<String, ViewNode>);

impl MapMountSource {
    /// Insert a cell's hosted view-tree (builder-style).
    pub fn with(mut self, cell: impl Into<String>, tree: ViewNode) -> Self {
        self.0.insert(cell.into(), tree);
        self
    }
}

impl MountSource for MapMountSource {
    fn hosted_tree(&self, cell: &str) -> Option<ViewNode> {
        self.0.get(cell).cloned()
    }
}

/// The maximum mount DEPTH (`host` nesting) the resolver unfolds before fail-safing. Bounds
/// a huge-but-acyclic mount tree so it can never blow the stack (cycles are caught separately
/// by the visited-path check). 16 levels of cells-host-cells is far past any real surface.
pub const MAX_MOUNT_DEPTH: usize = 16;

/// **Resolve every `host` mount against a [`MountSource`]** — the cell-hosted-view-tree
/// composition keystone. Walks `tree`, and for each [`ViewNode::Host`] fills its `view` from
/// the source's hosted tree for that cell (recursing into it so nested `host`s — fractal
/// cells-host-cells — resolve too). Returns a fully-resolved tree every renderer walks
/// identically.
///
/// FAIL-SAFE BY CONSTRUCTION (the recursion contract):
/// - **cycle** — a `host{cell}` naming a cell already on the mount path (self-host, or an
///   a→b→a cycle) resolves to a `‹mount cycle: …›` body inside the host frame (the cell is
///   still shown; only the self-reference is cut). Never an infinite unfold.
/// - **depth** — at [`MAX_MOUNT_DEPTH`] the resolver stops with a `‹mount depth exceeded›`
///   body (a huge acyclic tree can't blow the stack).
/// - **source miss** — a cell the source can't supply stays `view: None` (the unresolved
///   placeholder). A `host` already carrying a `view` (provided/pre-baked) is recursed for
///   nested hosts but otherwise kept.
pub fn resolve_mounts(tree: &ViewNode, source: &dyn MountSource) -> ViewNode {
    let mut path: Vec<String> = Vec::new();
    resolve_rec(tree, source, &mut path, 0)
}

fn resolve_rec(
    node: &ViewNode,
    source: &dyn MountSource,
    path: &mut Vec<String>,
    depth: usize,
) -> ViewNode {
    let recur = |children: &[ViewNode], path: &mut Vec<String>| -> Vec<ViewNode> {
        children
            .iter()
            .map(|c| resolve_rec(c, source, path, depth))
            .collect()
    };
    match node {
        ViewNode::Host { cell, view } => {
            // Cycle: this cell is already being mounted on the current path.
            if path.iter().any(|c| c == cell) {
                return ViewNode::Host {
                    cell: cell.clone(),
                    view: Some(Box::new(ViewNode::Text(format!("‹mount cycle: {cell}›")))),
                };
            }
            // Depth: a huge (acyclic) mount chain fail-safes rather than blowing the stack.
            if depth >= MAX_MOUNT_DEPTH {
                return ViewNode::Host {
                    cell: cell.clone(),
                    view: Some(Box::new(ViewNode::Text("‹mount depth exceeded›".into()))),
                };
            }
            // The hosted subtree: the provided/pre-baked `view`, else the source's tree for
            // this cell. A miss leaves it unresolved (the honest placeholder).
            let hosted = match view {
                Some(v) => Some((**v).clone()),
                None => source.hosted_tree(cell),
            };
            let resolved = hosted.map(|h| {
                path.push(cell.clone());
                let r = resolve_rec(&h, source, path, depth + 1);
                path.pop();
                Box::new(r)
            });
            ViewNode::Host {
                cell: cell.clone(),
                view: resolved,
            }
        }
        ViewNode::VStack(cs) => ViewNode::VStack(recur(cs, path)),
        ViewNode::Row(cs) => ViewNode::Row(recur(cs, path)),
        ViewNode::List(cs) => ViewNode::List(recur(cs, path)),
        ViewNode::Table(cs) => ViewNode::Table(recur(cs, path)),
        ViewNode::Section {
            title,
            tag,
            children,
        } => ViewNode::Section {
            title: title.clone(),
            tag: tag.clone(),
            children: recur(children, path),
        },
        ViewNode::Tabs {
            tabs,
            selected_slot,
            select_turn,
            panels,
        } => ViewNode::Tabs {
            tabs: tabs.clone(),
            selected_slot: *selected_slot,
            select_turn: select_turn.clone(),
            panels: recur(panels, path),
        },
        // Leaves carry no mounts — cloned through unchanged.
        ViewNode::Text(_)
        | ViewNode::Bind { .. }
        | ViewNode::Button { .. }
        | ViewNode::Input { .. }
        | ViewNode::Gauge { .. }
        | ViewNode::Divider => node.clone(),
    }
}

/// Parse the engine's `JSON.stringify(viewTree)` string into a typed [`ViewNode`].
pub fn parse_view_tree(json: &str) -> Result<ViewNode, String> {
    let raw: RawNode = serde_json::from_str(json).map_err(|e| format!("view-tree JSON: {e}"))?;
    Ok(raw.lift())
}

#[cfg(test)]
mod mount_tests {
    use super::*;

    /// A `host(cell)` with no child lifts to an UNRESOLVED mount (`view: None`).
    #[test]
    fn host_lifts_unresolved_from_bare_reference() {
        let tree =
            parse_view_tree(r#"{ "kind":"host", "props":{ "cell":"abcd" } }"#).expect("parse host");
        match tree {
            ViewNode::Host { cell, view } => {
                assert_eq!(cell, "abcd", "the host carries the cell ref");
                assert!(view.is_none(), "a bare host reference is unresolved");
            }
            _ => panic!("root is a host node"),
        }
    }

    /// `resolve_mounts` fills a host's `view` from the source — and recurses, so a FRACTAL
    /// 2-level nest (parent hosts child, child hosts grandchild) resolves end-to-end.
    #[test]
    fn resolve_mounts_unfolds_a_fractal_two_level_nest() {
        let grandchild = ViewNode::Section {
            title: "G".into(),
            tag: String::new(),
            children: vec![ViewNode::Text("grandchild leaf".into())],
        };
        // The child hosts the grandchild (a host node inside the child's own tree).
        let child = ViewNode::Section {
            title: "C".into(),
            tag: String::new(),
            children: vec![
                ViewNode::Text("child body".into()),
                ViewNode::Host {
                    cell: "gc".into(),
                    view: None,
                },
            ],
        };
        let source = MapMountSource::default()
            .with("child", child)
            .with("gc", grandchild);
        let parent = ViewNode::VStack(vec![
            ViewNode::Text("parent".into()),
            ViewNode::Host {
                cell: "child".into(),
                view: None,
            },
        ]);

        let resolved = resolve_mounts(&parent, &source);
        // Walk down: parent → host(child) → child Section → host(gc) → grandchild Section.
        let ViewNode::VStack(top) = &resolved else {
            panic!("root vstack")
        };
        let ViewNode::Host {
            view: Some(child_v),
            ..
        } = &top[1]
        else {
            panic!("host(child) resolved")
        };
        let ViewNode::Section {
            children: child_kids,
            ..
        } = &**child_v
        else {
            panic!("child is a section")
        };
        let ViewNode::Host {
            view: Some(gc_v), ..
        } = &child_kids[1]
        else {
            panic!("host(gc) resolved INSIDE the child — the fractal nest")
        };
        let ViewNode::Section {
            title: gc_title, ..
        } = &**gc_v
        else {
            panic!("grandchild is a section")
        };
        assert_eq!(gc_title, "G", "the grandchild tree mounted two levels deep");
    }

    /// A cell hosting ITSELF is caught — the resolver fail-safes to a cycle placeholder
    /// rather than unfolding forever.
    #[test]
    fn resolve_mounts_breaks_a_self_cycle() {
        // `loop` hosts a tree that hosts `loop` again.
        let looping = ViewNode::Host {
            cell: "loop".into(),
            view: None,
        };
        let source = MapMountSource::default().with("loop", looping.clone());
        let resolved = resolve_mounts(&looping, &source);
        let ViewNode::Host { view: Some(v), .. } = &resolved else {
            panic!("the outer host resolved once")
        };
        // Its body is the inner host(loop), which is a CYCLE — its body is the placeholder.
        let ViewNode::Host {
            view: Some(inner), ..
        } = &**v
        else {
            panic!("inner host present")
        };
        match &**inner {
            ViewNode::Text(t) => assert!(t.contains("mount cycle"), "self-cycle is cut: {t}"),
            _ => panic!("the self-cycle resolves to the cycle placeholder"),
        }
    }

    /// A mutual a→b→a cycle is caught the same way (the visited PATH, not just self).
    #[test]
    fn resolve_mounts_breaks_a_mutual_cycle() {
        let a = ViewNode::Host {
            cell: "b".into(),
            view: None,
        };
        let b = ViewNode::Host {
            cell: "a".into(),
            view: None,
        };
        let source = MapMountSource::default().with("a", a).with("b", b);
        let root = ViewNode::Host {
            cell: "a".into(),
            view: None,
        };
        // Just terminating (no stack overflow / hang) + producing a tree is the property.
        let resolved = resolve_mounts(&root, &source);
        let rendered = format!("{resolved:?}");
        assert!(
            rendered.contains("mount cycle"),
            "the mutual cycle is cut with a placeholder"
        );
    }

    /// A pre-baked (provided) `view` is kept AND recursed for nested hosts.
    #[test]
    fn resolve_mounts_keeps_and_recurses_a_provided_subtree() {
        let provided = ViewNode::Host {
            cell: "outer".into(),
            view: Some(Box::new(ViewNode::Host {
                cell: "inner".into(),
                view: None,
            })),
        };
        let source =
            MapMountSource::default().with("inner", ViewNode::Text("inner resolved".into()));
        let resolved = resolve_mounts(&provided, &source);
        let ViewNode::Host { view: Some(v), .. } = &resolved else {
            panic!("outer kept its provided view")
        };
        let ViewNode::Host {
            view: Some(inner), ..
        } = &**v
        else {
            panic!("the nested host inside the provided subtree was visited")
        };
        assert!(
            matches!(&**inner, ViewNode::Text(t) if t == "inner resolved"),
            "the nested host inside a provided subtree resolved from the source"
        );
    }
}
