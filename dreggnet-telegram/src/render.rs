//! **The deos-`ViewNode` → Telegram message text renderer.** An offering's [`Surface`] is a
//! deos affordance view-tree; a Telegram message is plain text plus an inline keyboard. This walks
//! the tree into the *text* half (room prose, party state, verified-turn count, section titles);
//! the *affordance* half (the [`deos_view::ViewNode::Menu`] rows / the passed [`Action`]s) becomes
//! the inline keyboard in [`crate::api::build_present_request`], NOT text — so the same surface
//! that paints Discord buttons paints a Telegram keyboard, no reinvention.

use deos_view::{SurfaceBackend, TelegramBackend};
use dreggnet_offerings::Surface;

/// Render a [`Surface`] into Telegram message text (the *non-affordance* half of the surface).
/// [`deos_view::ViewNode::Menu`]/`Button` are OMITTED — they are rendered as the inline keyboard,
/// not as text. Section titles head their blocks; text nodes are lines.
///
/// Renders through the deos-view [`TelegramBackend`] (the moved-in walker — full node coverage);
/// this crate no longer maintains its own subset walker.
pub fn render_surface_text(surface: &Surface) -> String {
    TelegramBackend.render(surface.view(), &[])
}
