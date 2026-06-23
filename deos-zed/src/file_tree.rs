//! The file-tree / open-file affordance — browse a directory and open a file
//! into the [`Editor`](crate::editor::Editor).
//!
//! Like everything in deos-zed, directory listing goes through the [`Fs`] seam,
//! NOT `std::fs` directly. So a `FirmamentFs`-backed tree browses
//! `DirectoryCell`s (capability-scoped discovery), and the same tree UI works
//! unchanged.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use gpui::{
    px, App, AppContext as _, Context, Entity, IntoElement, ParentElement as _, SharedString,
    Styled as _, Window,
};
use gpui_component::list::ListItem;
use gpui_component::tree::{tree, TreeItem, TreeState};
use gpui_component::{h_flex, ActiveTheme as _, IconName};

use crate::fs::Fs;

/// Recursively build tree items for a directory through the [`Fs`] seam.
///
/// Depth-limited so a huge tree doesn't stall the first paint; deeper levels
/// are still reachable because each folder re-reads on expand in a richer
/// build, but for the demo a bounded eager walk is plenty and keeps the seam
/// the only I/O path. Hidden entries (dotfiles, `target/`) are skipped.
fn build_items(fs: &Arc<dyn Fs>, dir: &Path, depth_left: usize) -> Vec<TreeItem> {
    let mut items = Vec::new();
    let Ok(entries) = fs.read_dir(dir) else {
        return items;
    };
    for entry in entries {
        let name = entry.file_name();
        if name.starts_with('.') || name == "target" || name == "node_modules" {
            continue;
        }
        let id: SharedString = entry.path.to_string_lossy().to_string().into();
        if entry.is_dir {
            let children = if depth_left > 0 {
                build_items(fs, &entry.path, depth_left - 1)
            } else {
                Vec::new()
            };
            items.push(TreeItem::new(id, name).children(children));
        } else {
            items.push(TreeItem::new(id, name));
        }
    }
    // Folders first, then alphabetical.
    items.sort_by(|a, b| {
        b.is_folder()
            .cmp(&a.is_folder())
            .then(a.label.cmp(&b.label))
    });
    items
}

/// A directory browser bound to the [`Fs`] seam. Renders a tree; clicking a
/// file invokes the host-supplied `on_open` with the file's path.
pub struct FileTree {
    state: Entity<TreeState>,
    fs: Arc<dyn Fs>,
    root: PathBuf,
}

impl FileTree {
    /// Build a file tree rooted at `root`, listing through `fs`.
    pub fn new(fs: Arc<dyn Fs>, root: PathBuf, cx: &mut App) -> Self {
        let state = cx.new(|cx| TreeState::new(cx));
        let items = build_items(&fs, &root, 4);
        state.update(cx, |s, cx| s.set_items(items, cx));
        Self { state, fs, root }
    }

    /// Re-scan the root through the [`Fs`] seam (e.g. after a save created a file).
    pub fn refresh(&self, cx: &mut App) {
        let items = build_items(&self.fs, &self.root, 4);
        self.state.update(cx, |s, cx| s.set_items(items, cx));
    }

    /// Render the tree. `on_open` is invoked (in a `cx` where `V` is the host
    /// view) with the clicked file's path; the host opens it into its editor.
    pub fn render<V: 'static>(
        &self,
        host: Entity<V>,
        on_open: impl Fn(&mut V, PathBuf, &mut Window, &mut Context<V>) + 'static + Clone,
        cx: &mut App,
    ) -> impl IntoElement {
        let host = host.clone();
        tree(&self.state, move |ix, entry, _selected, _window, _cx| {
            let item = entry.item();
            let icon = if !entry.is_folder() {
                IconName::File
            } else if entry.is_expanded() {
                IconName::FolderOpen
            } else {
                IconName::Folder
            };
            let label = item.label.clone();
            let id = item.id.clone();
            let is_folder = item.is_folder();
            let host = host.clone();
            let on_open = on_open.clone();

            ListItem::new(ix)
                .w_full()
                .py_0p5()
                .px_2()
                .pl(px(16.) * entry.depth() + px(8.))
                .child(h_flex().gap_2().child(icon).child(label))
                .on_click(move |_, window, cx| {
                    if is_folder {
                        return;
                    }
                    let path = PathBuf::from(id.to_string());
                    let on_open = on_open.clone();
                    host.update(cx, |v, cx| {
                        on_open(v, path, window, cx);
                    });
                })
        })
        .text_sm()
        .p_1()
        .bg(cx.theme().sidebar)
        .text_color(cx.theme().sidebar_foreground)
        .h_full()
    }
}
