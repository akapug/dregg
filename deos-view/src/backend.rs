//! **The `SurfaceBackend` trait** — the one seat every renderer of the [`ViewNode`] IR shares.
//!
//! A backend takes the SAME (mount-resolved, disclosed) view-tree + its live bind values and
//! projects it onto its channel's output ([`render`](SurfaceBackend::render) → an HTML string, a
//! Discord card, Telegram text, …), and it [`decode`](SurfaceBackend::decode)s an actuation id
//! that channel carried back into the `{turn, arg}` affordance to fire. Decoding is the ONE
//! [`crate::affordance`] codec, selected by the backend's [`transport`](SurfaceBackend::transport)
//! — so every backend round-trips its own encoded affordances by construction.
//!
//! This is the extraction of the previously ad-hoc render functions (`web::render_html`,
//! `discord::render_card`, the moved-in web-form + Telegram-text walkers) behind one trait; the
//! frontend crates (`dreggnet-web`, `dreggnet-telegram`) render through the deos-view backends
//! instead of maintaining their own subset walkers.

use crate::affordance::{parse_affordance_id, AffordanceTransport};
use crate::tree::ViewNode;

/// A projection of the one [`ViewNode`] IR onto a concrete surface channel (web / Discord /
/// Telegram / …). One `render` from the tree + binds; one `decode` back from an actuation id via
/// the shared affordance codec.
pub trait SurfaceBackend {
    /// The rendered output of this channel — an HTML `String`, a `DiscordCard`, Telegram text, …
    type Rendered;

    /// The channel this backend carries affordances on — selects the [`crate::affordance`] codec
    /// used by the default [`decode`](Self::decode).
    fn transport(&self) -> AffordanceTransport;

    /// Render `tree` (already mount-resolved + disclosed) with its live `binds` (tree-walk order;
    /// a channel with no live binds, e.g. Telegram text, ignores them) into this channel's output.
    fn render(&self, tree: &ViewNode, binds: &[u64]) -> Self::Rendered;

    /// Decode an actuation id this channel carried back into the `{turn, arg}` affordance to fire.
    /// The default routes through the ONE [`crate::affordance`] codec for this backend's
    /// [`transport`](Self::transport); `None` for an id this transport never minted.
    fn decode(&self, id: &str) -> Option<(String, i64)> {
        parse_affordance_id(id, self.transport())
    }
}
