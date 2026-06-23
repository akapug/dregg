"""THE COMPONENTS PILLAR emitter — census the gpui-component widget set (the VISUAL
building blocks the deos cockpit is built from) and cross-link each widget to where
the cockpit actually uses it.

Two sources, joined:
  1. The widget CATALOG — name · what-it-is · variants — read off the gpui-component
     crate (`~/dev/gpui-component/crates/ui/src/`). The catalog is carried here as a
     curated table (the crate is not MCP-crawlable); each entry names the module so a
     reader can open the source.
  2. The cockpit USAGE — a live grep over `starbridge-v2/src/cockpit/` for each
     widget, so the "used in deos / by which surface" edges are never stale: re-run
     this and a newly-used widget lights up.

Emits `data/components.json`:
  { "meta": {...}, "components": [ {id, name, module, kind, what, variants,
      used_in_deos, used_files, used_surfaces, source} ], "edges": [...] }

Stable ids (`component:<slug>`) + typed edges (component→cockpit-file, component→
surface) make it hypermedia-ready: the site can cross-link a surface to the widgets
it is built from and back.
"""
import json
import os
import re
import subprocess

ROOT = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(ROOT, "data")
os.makedirs(DATA, exist_ok=True)

# The cockpit tree we grep for usage. (Absolute so we don't depend on cwd.)
COCKPIT = os.path.expanduser("~/dev/breadstuffs/starbridge-v2/src/cockpit")
GPUI_UI = os.path.expanduser("~/dev/gpui-component/crates/ui/src")

# Which cockpit panel file maps to which atlas surface ids (for the usage→surface
# edge). A widget grepped in a file is attributed to that file's surfaces.
FILE_SURFACES = {
    "panels_main.rs": ["home", "shell", "agent", "objects", "proofs", "debugger",
                       "replay", "cipherclerk", "composer", "simulate"],
    "panels_moldable.rs": ["inspector", "inspect-act", "workspace", "lanes"],
    "panels_web.rs": ["web-of-cells", "links-here", "powerbox", "graph"],
    "panels_webshell.rs": ["webshell"],
    "panels_workspace.rs": ["dock-workspace", "buffer", "terminal"],
    "panels_devtools.rs": ["devtools"],
    "helpers.rs": [],   # shared button-variant helper — touches everything
    "time.rs": ["time"],
    "docs.rs": ["docs"],
    "nav.rs": [], "actions.rs": [], "dispatch.rs": [], "render.rs": [],
    "construct.rs": [], "mod.rs": [], "live.rs": [], "shell_ops.rs": [],
}

# ---------------------------------------------------------------------------
# 1. THE CATALOG — the gpui-component widgets, grouped, with what-it-is + variants.
#    Each: (name, module, kind, what, [variants], [grep_symbols]). `grep_symbols`
#    are the type names we grep the cockpit for to detect usage (the primary
#    struct + its state/event siblings).
# ---------------------------------------------------------------------------
CATALOG = [
    # --- input + action -------------------------------------------------
    ("Button", "button", "action",
     "A clickable action element — the workhorse verb control.",
     ["Primary", "Secondary", "Danger", "Warning", "Success", "Info", "Ghost",
      "Link", "Text", "Outline", "compact", "sizes (xs/sm/md/lg)", "icon", "loading"],
     ["Button", "ButtonVariants"]),
    ("ButtonGroup", "button", "action",
     "A connected group of related buttons with single/multiple selection.",
     ["horizontal/vertical", "single/multiple select"], ["ButtonGroup"]),
    ("Toggle", "button", "action",
     "A button that toggles between pressed and unpressed states.",
     ["Ghost", "Outline", "sizes"], ["Toggle"]),
    ("DropdownButton", "button", "action",
     "A button carrying a dropdown menu.", ["custom menu", "anchor"], ["DropdownButton"]),
    ("Input", "input", "input",
     "A text input field — single-line, password, or multiline, with prefix/suffix.",
     ["password", "multiline", "prefix/suffix", "cleanable", "mask toggle"],
     ["Input", "InputState", "InputEvent", "TextInput"]),
    ("Checkbox", "checkbox", "input",
     "A binary input for selecting/deselecting an option.",
     ["label", "sizes", "disabled", "tooltip"], ["Checkbox"]),
    ("Radio", "radio", "input",
     "A single-choice control for mutually-exclusive options (usually grouped).",
     ["label", "disabled", "sizes"], ["Radio", "RadioGroup"]),
    ("Switch", "switch", "input",
     "A toggle for switching between two states.",
     ["label placement", "color", "sizes", "disabled"], ["Switch"]),
    ("Slider", "slider", "input",
     "Select a value or range along an axis.",
     ["single/range", "min/max", "step", "continuous/release"], ["Slider", "SliderState"]),
    ("Select", "select", "input",
     "A searchable dropdown selecting from a list (SearchableList-backed).",
     ["cleanable", "placeholder", "icons"], ["Select"]),
    ("Combobox", "combobox", "input",
     "A searchable, filterable dropdown of options.",
     ["cleanable", "placeholder"], ["Combobox"]),
    ("ColorPicker", "color_picker", "input",
     "Pick a color via HSL sliders + palettes.", ["presets", "HSLA"], ["ColorPicker"]),
    ("Rating", "rating", "input",
     "A star-based rating control (display or collect).",
     ["max stars", "color", "disabled"], ["Rating"]),

    # --- text + display -------------------------------------------------
    ("Label", "label", "display",
     "A text label with optional secondary text, masking, and match highlighting.",
     ["secondary", "masked", "highlight"], ["Label"]),
    ("Link", "link", "display",
     "A hyperlink element (HTML <a> analogue).", ["href", "disabled"], ["Link"]),
    ("Text / TextView", "text", "display",
     "Rich text rendering — markdown / HTML / styled text, selectable + scrollable.",
     ["Markdown", "HTML", "selectable", "code-block actions"], ["TextView", "TextViewState"]),
    ("Highlighter", "highlighter", "display",
     "Code syntax highlighting (tree-sitter; WASM stub).", ["language detect"], ["Highlighter"]),
    ("Kbd", "kbd", "display",
     "Render a keybinding in platform-specific format.", ["outline", "action-bound"], ["Kbd"]),
    ("Badge", "badge", "display",
     "A small count / dot / icon indicator on another element.",
     ["number (max)", "dot", "icon"], ["Badge"]),
    ("Tag", "tag", "display",
     "A small categorizing label.",
     ["Primary", "Secondary", "Danger", "Success", "Warning", "Info", "outline"], ["Tag"]),
    ("Avatar / AvatarGroup", "avatar", "display",
     "A user avatar (image or initials); the group is a compact stack.",
     ["image", "initials", "group limit", "sizes"], ["Avatar", "AvatarGroup"]),
    ("Icon", "icon", "display",
     "An icon element (the shared icon set).", ["sized", "colored"], ["Icon"]),
    ("DescriptionList", "description_list", "display",
     "Label-value pairs for metadata display.",
     ["vertical/horizontal", "bordered", "columns"], ["DescriptionList"]),
    ("Separator", "separator", "display",
     "A horizontal / vertical divider line.", ["Solid", "Dashed", "labeled"], ["Separator"]),
    ("Skeleton", "skeleton", "feedback",
     "An animated loading placeholder.", ["primary/secondary"], ["Skeleton"]),
    ("Spinner", "spinner", "feedback",
     "A rotating loading indicator.", ["icon", "color", "speed", "sizes"], ["Spinner"]),
    ("Progress / ProgressCircle", "progress", "feedback",
     "A linear or circular progress indicator.",
     ["indeterminate", "color", "0-100"], ["Progress", "ProgressCircle"]),
    ("Alert", "alert", "feedback",
     "A message box for important information.",
     ["Info", "Success", "Warning", "Error", "banner"], ["Alert"]),
    ("Notification", "notification", "feedback",
     "A temporary message in a notification area.",
     ["Info", "Success", "Warning", "Error", "auto-hide", "actions"], ["Notification"]),

    # --- layout + container ---------------------------------------------
    ("Accordion", "accordion", "container",
     "Expandable / collapsible sections.", ["multiple", "bordered", "sizes"], ["Accordion"]),
    ("Collapsible", "collapsible", "container",
     "An interactive expand/collapse element.", ["open/closed"], ["Collapsible"]),
    ("GroupBox", "group_box", "container",
     "A styled container with an optional title.", ["Normal", "Fill", "Outline"], ["GroupBox"]),
    ("Card", "card", "container",
     "A bordered content card.", ["padded", "bordered"], ["Card"]),
    ("Form / Field", "form", "container",
     "A container organizing form fields.",
     ["horizontal/vertical", "label width", "multi-column"], ["Form", "Field"]),
    ("Settings", "setting", "container",
     "A settings panel with sidebar navigation.", ["multi-page", "groups"], ["Settings", "SettingPage"]),
    ("Sidebar", "sidebar", "navigation",
     "A collapsible sidebar navigation.",
     ["Icon", "Offcanvas", "groups", "header/footer"], ["Sidebar", "SidebarMenu"]),
    ("Dock", "dock", "container",
     "A fixed edge-anchored panel container (left/right/bottom/center), resizable + "
     "tabbed — the dock the cockpit's paned workspace is modeled on.",
     ["Left", "Right", "Bottom", "Center", "resizable", "collapsible"], ["Dock", "DockArea"]),
    ("ResizablePanelGroup", "resizable", "container",
     "Panels separated by draggable handles.",
     ["horizontal/vertical", "initial sizes"], ["ResizablePanel", "ResizablePanelGroup", "ResizableState"]),
    ("StatusBar", "status_bar", "container",
     "A bottom bar with left/center/right regions.", ["3 regions"], ["StatusBar"]),
    ("TitleBar", "title_bar", "container",
     "The window title bar.", ["custom controls"], ["TitleBar"]),

    # --- navigation -----------------------------------------------------
    ("TabBar / Tab", "tab", "navigation",
     "A tabbed interface for switching content sections.",
     ["Tab", "Outline", "Pill", "Segmented", "Underline", "scroll"], ["TabBar", "Tab "]),
    ("Breadcrumb", "breadcrumb", "navigation",
     "Hierarchy location trail.", ["disabled items", "click handlers"], ["Breadcrumb"]),
    ("Pagination", "pagination", "navigation",
     "Page-number navigation for paginated content.", ["compact", "prev/next"], ["Pagination"]),
    ("Stepper", "stepper", "navigation",
     "A step-by-step progress indicator.",
     ["horizontal/vertical", "clickable steps"], ["Stepper"]),
    ("Menu / PopupMenu / ContextMenu", "menu", "navigation",
     "A popup menu of contextual actions.",
     ["separator", "submenu", "checkable", "icons", "AppMenuBar"], ["PopupMenu", "ContextMenu", "AppMenuBar"]),
    ("NativeMenu", "native_menu", "navigation",
     "An OS-native popup menu rendered outside window bounds.", ["actions", "checked"], ["NativeMenu"]),
    ("Tree", "tree", "navigation",
     "A hierarchical list of tree-structured data.",
     ["expand/collapse", "nested", "depth"], ["Tree", "TreeState", "TreeItem"]),

    # --- overlay --------------------------------------------------------
    ("Dialog / AlertDialog", "dialog", "overlay",
     "A modal dialog overlay for focused interaction.",
     ["title/content/footer", "overlay-closable", "AlertDialog"], ["Dialog", "AlertDialog"]),
    ("Sheet", "sheet", "overlay",
     "A panel sliding in from a window edge.",
     ["Left", "Right", "Bottom", "Center", "resizable"], ["Sheet"]),
    ("Popover", "popover", "overlay",
     "A floating panel triggered by a click.", ["anchor", "overlay-closable"], ["Popover"]),
    ("HoverCard", "hover_card", "overlay",
     "A popover shown on hover with a delay.", ["anchor", "delays"], ["HoverCard"]),
    ("Tooltip", "tooltip", "overlay",
     "Helper text on hover, with optional keybinding.", ["text/custom", "action"], ["Tooltip"]),
    ("Clipboard", "clipboard", "overlay",
     "A copy-to-clipboard utility control.", ["static/dynamic", "callback"], ["Clipboard"]),

    # --- data + viz -----------------------------------------------------
    ("List", "list", "data",
     "A virtual-scrolling, searchable, selectable list.",
     ["searchable", "selectable", "scrollbar"], ["List", "ListState", "ListItem", "ListDelegate"]),
    ("Table / DataTable", "table", "data",
     "A table for tabular data — stateless Table or virtual-scrolling DataTable.",
     ["sizes", "cell align", "columns", "virtual"], ["Table", "DataTable", "TableHeader"]),
    ("VirtualList", "virtual_list", "data",
     "A performant renderer for large datasets via virtual scrolling.",
     ["horizontal/vertical"], ["VirtualList", "VirtualListScrollHandle"]),
    ("Scrollbar / Scrollable", "scroll", "data",
     "A custom scrollbar + a wrapper adding scrollbars to elements.",
     ["Scrolling", "Hover", "Always", "h/v axis"], ["Scrollbar", "Scrollable"]),
    ("Charts", "chart", "data",
     "Bar / Line / Area / Pie / Candlestick chart visualizations.",
     ["Bar", "Line", "Area", "Pie/donut", "Candlestick"],
     ["BarChart", "LineChart", "AreaChart", "PieChart", "CandlestickChart"]),
    ("Plot", "plot", "data",
     "The base framework (axis/grid/scale/shape) for building custom charts.",
     ["axis", "grid", "scale", "shape"], ["Plot"]),
]


def _gpui_symbols(text):
    """The set of bare type names this file pulls from `gpui_component` — anything
    in a `use gpui_component::…{A, B}` import or referenced via a `gpui_component::`
    path. This is the honest 'is it really a gpui-component widget here' signal:
    the cockpit re-uses many of the same NAMES locally (`Tab`, `Switch`, `Field`),
    so a bare token match would over-count. We attribute usage ONLY to symbols this
    file actually sources from the crate."""
    syms = set()
    # path references: gpui_component::input::InputState, gpui_component::Sizable
    for m in re.finditer(r"gpui_component::([A-Za-z0-9_:]+)", text):
        for part in m.group(1).split("::"):
            if part and part[0].isupper():
                syms.add(part)
    # use-imports: `use gpui_component::button::{Button, ButtonVariants};`
    for m in re.finditer(r"use\s+gpui_component::[^;]*;", text):
        for part in re.findall(r"[A-Za-z0-9_]+", m.group(0)):
            if part and part[0].isupper():
                syms.add(part)
    return syms


def grep_usage(symbols):
    """Return {file_basename: hit_count} where `hit_count` is how many times any of
    `symbols` (the widget's primary struct + siblings) is referenced in a cockpit
    file — but ONLY in files that actually source that symbol from `gpui_component`
    (so the cockpit's own homonyms — its `Tab` enum, a `Field` regime — don't count
    as widget usage)."""
    files = {}
    if not os.path.isdir(COCKPIT):
        return files
    wanted = {s.rstrip() for s in symbols}
    pats = {s: re.compile(r"(?<![A-Za-z0-9_])" + re.escape(s) + r"(?![A-Za-z0-9_])") for s in wanted}
    for fn in os.listdir(COCKPIT):
        if not fn.endswith(".rs"):
            continue
        try:
            text = open(os.path.join(COCKPIT, fn), encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        sourced = _gpui_symbols(text) & wanted
        if not sourced:
            continue
        n = sum(len(pats[s].findall(text)) for s in sourced)
        if n:
            files[fn] = n
    return files


def slug(name):
    return re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")


def build():
    comps, edges = [], []
    used_count = 0
    for (name, module, kind, what, variants, symbols) in CATALOG:
        cid = "component:" + slug(name)
        usage = grep_usage(symbols)
        used = bool(usage)
        if used:
            used_count += 1
        surfaces = sorted({s for fn in usage for s in FILE_SURFACES.get(fn, [])})
        comps.append({
            "id": cid,
            "name": name,
            "module": module,
            "kind": kind,
            "group": kind,                 # app.js detail card reads `.group`
            "what": what,
            "summary": what,               # app.js detail card reads `.summary`
            "variants": variants,
            "used_in_deos": used,
            "used_files": sorted(usage.keys()),
            "use_counts": usage,
            "used_surfaces": surfaces,
            "surfaces": surfaces,          # app.js cross-links via `.surfaces`
            "verbs": [],                   # widgets don't map to protocol verbs
            "source": f"~/dev/gpui-component/crates/ui/src/{module}",
        })
        for fn in usage:
            edges.append({"from": cid, "to": "file:" + fn, "type": "used_in_file", "count": usage[fn]})
        for sid in surfaces:
            edges.append({"from": cid, "to": "surface:" + sid, "type": "renders_on_surface"})
    # The cockpit's OWN dock (starbridge-v2/src/dock/: Pane, PaneGroup,
    # ActivePaneDecorator) is modeled on gpui-component's Dock — the self-hosting
    # paned workspace. Record it as a typed cross-link so the site can show the
    # lineage even though the cockpit forks rather than imports the widget.
    edges.append({
        "from": "component:dock", "to": "surface:dock-workspace",
        "type": "modeled_by_local_dock",
        "note": "starbridge-v2/src/dock/{pane,pane_group}.rs forks gpui-component's Dock "
                "into the cockpit's resizable editor/terminal/chat/agent workspace.",
    })
    # group counts by kind
    kinds = {}
    for c in comps:
        kinds.setdefault(c["kind"], 0)
        kinds[c["kind"]] += 1
    data = {
        "meta": {
            "catalog_count": len(comps),
            "used_in_deos": used_count,
            "kinds": kinds,
            "source_crate": "~/dev/gpui-component/crates/ui/src",
            "cockpit_tree": "starbridge-v2/src/cockpit",
            "note": "catalog = the gpui-component widget set (the visual building blocks); "
                    "used_in_deos is a LIVE grep of the cockpit — re-run to refresh. The "
                    "cockpit drives a focused set directly (Button · Input) over its own "
                    "dock (Pane/PaneGroup, modeled on gpui-component's Dock); the rest of "
                    "the palette is available + documented here.",
        },
        "components": comps,
        "edges": edges,
    }
    out = os.path.join(DATA, "components.json")
    json.dump(data, open(out, "w"), indent=2)
    print(f"components: {len(comps)} cataloged · {used_count} used live in the cockpit → {out}")
    return data


if __name__ == "__main__":
    build()
