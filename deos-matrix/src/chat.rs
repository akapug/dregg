//! The **deos-chat** gpui UI: a room-list sidebar, a timeline, and a real
//! composer, driven off a [`ChatSource`](crate::source::ChatSource).
//!
//! This is the social/multiplayer layer over the dregg world. The view is pure
//! presentation over the [`ChatSource`] seam — it does NOT know whether the
//! backend is the live `matrix-rust-sdk` worker or the offline [`MockSource`], so
//! the same UI renders against a recorded sync with no homeserver.
//!
//! ## Patterns adopted from nheko (the "solves problems correctly" reference)
//!
//!   * **Composer keymap is the de-facto standard**: Enter = send, Shift-Enter =
//!     newline. Wired via `gpui_component::input::InputEvent::PressEnter { shift }`
//!     — send only when `!shift`. (nheko's exact contract; users have muscle
//!     memory for it.)
//!   * **Timeline is a presentation pass over the event stream**: sender-grouping
//!     and day separators are *computed* from the message list each frame, not
//!     stored state. Edits/redactions would be states of an event, not deletions.
//!   * **Room list is keyboard-navigable + unread-badged**, sorted for display by
//!     the source. Encryption state is a per-row, visible indicator (legible trust
//!     — nheko's correctness principle).
//!   * **Own-vs-other alignment + sender color** so a glance reads the conversation.
//!
//! The membrane affordance (a message can carry a rehydratable cap-bounded fork of
//! the deos world — see [`crate::membrane`]) is surfaced as a composer action; the
//! actual mint/rehydrate lives in the confined comms-PD (`MembraneHost`).

use std::sync::Arc;

use gpui::{
    div, px, rgb, App, AppContext as _, Context, Entity, FocusHandle, Focusable, Hsla,
    InteractiveElement as _, IntoElement, MouseButton, ParentElement as _, Render, SharedString,
    StatefulInteractiveElement as _, Styled as _, Subscription, Window,
};
use gpui::prelude::FluentBuilder as _;
use gpui_component::{
    input::{Input, InputEvent, InputState},
    h_flex, v_flex, ActiveTheme as _,
};

use crate::client::{RoomSummary, TimelineMessage};
use crate::source::ChatSource;

/// How many recent messages to pull per room.
const TIMELINE_LIMIT: u16 = 80;

/// The root chat view: sidebar + timeline + composer, over a [`ChatSource`].
pub struct ChatView {
    source: Arc<dyn ChatSource>,
    me: Option<String>,
    rooms: Vec<RoomSummary>,
    /// Index into `rooms` of the selected room, if any.
    selected: Option<usize>,
    /// The selected room's timeline (oldest-first).
    timeline: Vec<TimelineMessage>,
    /// The composer's rope-backed input (a real `gpui-component` `Input`).
    composer: Entity<InputState>,
    status: SharedString,
    focus: FocusHandle,
    _subs: Vec<Subscription>,
}

impl ChatView {
    /// Build the view over a data source. Loads the room list immediately and
    /// selects the first room so the demo opens onto a populated timeline.
    pub fn new(source: Arc<dyn ChatSource>, window: &mut Window, cx: &mut Context<Self>) -> Self {
        let composer = cx.new(|cx| {
            InputState::new(window, cx)
                .multi_line(true)
                .placeholder("Message — Enter to send, Shift-Enter for newline")
        });

        // The load-bearing seam: Enter (without shift) submits; Shift-Enter is a
        // newline (handled by the input itself). This is nheko's composer contract.
        let subs = vec![cx.subscribe_in(
            &composer,
            window,
            |this, _input, event: &InputEvent, window, cx| {
                if let InputEvent::PressEnter { shift, .. } = event {
                    if !shift {
                        this.submit(window, cx);
                    }
                }
            },
        )];

        let me = source.whoami();
        let label = source.backend_label();
        let mut me_view = Self {
            source,
            me,
            rooms: Vec::new(),
            selected: None,
            timeline: Vec::new(),
            composer,
            status: SharedString::from(format!("connected — {label}")),
            focus: cx.focus_handle(),
            _subs: subs,
        };
        me_view.refresh_rooms(cx);
        if !me_view.rooms.is_empty() {
            me_view.select_room(0, cx);
        }
        me_view
    }

    /// Pull the room list from the source.
    fn refresh_rooms(&mut self, cx: &mut Context<Self>) {
        match self.source.rooms() {
            Ok(rooms) => self.rooms = rooms,
            Err(e) => self.status = SharedString::from(format!("room list error: {e}")),
        }
        cx.notify();
    }

    /// Select a room by index and load its timeline.
    fn select_room(&mut self, idx: usize, cx: &mut Context<Self>) {
        if idx >= self.rooms.len() {
            return;
        }
        self.selected = Some(idx);
        self.refresh_timeline(cx);
    }

    /// Reload the selected room's timeline from the source.
    fn refresh_timeline(&mut self, cx: &mut Context<Self>) {
        let Some(idx) = self.selected else { return };
        let room_id = self.rooms[idx].room_id.to_string();
        match self.source.timeline(&room_id, TIMELINE_LIMIT) {
            Ok(tl) => self.timeline = tl,
            Err(e) => self.status = SharedString::from(format!("timeline error: {e}")),
        }
        cx.notify();
    }

    /// Send the composer's contents to the selected room, then clear + refresh.
    fn submit(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        let Some(idx) = self.selected else { return };
        let body = self.composer.read(cx).value().to_string();
        let body = body.trim();
        if body.is_empty() {
            return;
        }
        let room_id = self.rooms[idx].room_id.to_string();
        match self.source.send(&room_id, body) {
            Ok(_id) => {
                self.composer.update(cx, |state, cx| {
                    state.set_value("", window, cx);
                });
                self.status = SharedString::from("sent");
                self.refresh_timeline(cx);
            }
            Err(e) => {
                self.status = SharedString::from(format!("send failed: {e}"));
                cx.notify();
            }
        }
    }

    // --- rendering --------------------------------------------------------

    fn render_sidebar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = self.selected;
        let rows = self.rooms.iter().enumerate().map(|(i, room)| {
            let is_sel = selected == Some(i);
            let name = room.display_name.clone();
            let unread = room.unread_notifications;
            let enc = room.is_encrypted;
            v_flex()
                .id(("room", i))
                .px_3()
                .py_2()
                .gap_1()
                .cursor_pointer()
                .when(is_sel, |d| d.bg(cx.theme().accent))
                .hover(|d| d.bg(cx.theme().muted))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev, _win, cx| {
                        this.select_room(i, cx);
                    }),
                )
                .child(
                    h_flex()
                        .gap_2()
                        .items_center()
                        .child(
                            // Encryption indicator — a legible, per-row trust badge
                            // (nheko's correctness principle).
                            div()
                                .text_xs()
                                .child(if enc { "🔒" } else { "  " }),
                        )
                        .child(div().flex_1().font_weight(gpui::FontWeight::MEDIUM).child(name))
                        .when(unread > 0, |d| {
                            d.child(
                                div()
                                    .px_1p5()
                                    .rounded_full()
                                    .bg(rgb(0xE0457B))
                                    .text_color(rgb(0xFFFFFF))
                                    .text_xs()
                                    .child(format!("{unread}")),
                            )
                        }),
                )
                .when_some(room.topic.clone(), |d, topic| {
                    d.child(
                        div()
                            .text_xs()
                            .text_color(cx.theme().muted_foreground)
                            .truncate()
                            .child(topic),
                    )
                })
        });

        v_flex()
            .w(px(248.))
            .h_full()
            .border_r_1()
            .border_color(cx.theme().border)
            .child(
                div()
                    .px_3()
                    .py_2()
                    .border_b_1()
                    .border_color(cx.theme().border)
                    .font_weight(gpui::FontWeight::BOLD)
                    .child("rooms"),
            )
            .child(
                v_flex()
                    .id("room-list")
                    .flex_1()
                    .min_h(px(0.))
                    .overflow_y_scroll()
                    .children(rows),
            )
    }

    fn render_timeline(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let me = self.me.clone();
        let theme = cx.theme();
        let muted = theme.muted_foreground;

        // Presentation pass: group consecutive messages by the same sender and
        // insert day separators (computed, not stored). nheko's timeline shape.
        let mut prev_sender: Option<String> = None;
        let mut prev_day: Option<i64> = None;
        let rows = self.timeline.iter().enumerate().map(move |(i, m)| {
            let same_sender = prev_sender.as_deref() == Some(m.sender.as_str());
            prev_sender = Some(m.sender.clone());

            let day = (m.timestamp_ms / 86_400_000) as i64;
            let day_sep = if prev_day != Some(day) {
                prev_day = Some(day);
                Some(day_label(m.timestamp_ms))
            } else {
                None
            };

            let is_me = me.as_deref() == Some(m.sender.as_str());
            let sender_short = short_sender(&m.sender);
            let time = time_label(m.timestamp_ms);
            let color = sender_color(&m.sender);

            let mut block = v_flex().id(("msg", i)).px_3();
            if let Some(label) = day_sep {
                block = block.child(
                    div()
                        .my_2()
                        .text_center()
                        .text_xs()
                        .text_color(muted)
                        .child(label),
                );
            }
            // Sender header only on the first message of a run (grouping).
            if !same_sender {
                block = block.child(
                    h_flex()
                        .mt_2()
                        .gap_2()
                        .items_baseline()
                        .child(
                            div()
                                .font_weight(gpui::FontWeight::BOLD)
                                // own messages in a steady blue; others by stable
                                // per-sender hue. Both `Hsla` so the branches unify.
                                .text_color(if is_me {
                                    gpui::hsla(217.0 / 360.0, 1.0, 0.65, 1.0)
                                } else {
                                    color
                                })
                                .child(sender_short),
                        )
                        .child(div().text_xs().text_color(muted).child(time)),
                );
            }
            block.child(
                div()
                    .pl(px(if same_sender { 0. } else { 0. }))
                    .text_color(theme.foreground)
                    .child(m.body.clone()),
            )
        });

        v_flex()
            .id("timeline")
            .flex_1()
            .min_h(px(0.))
            .overflow_y_scroll()
            .py_2()
            .children(rows)
    }

    fn render_composer(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let disabled = self.selected.is_none();
        v_flex()
            .border_t_1()
            .border_color(cx.theme().border)
            .p_2()
            .gap_1()
            .child(
                div()
                    .h(px(64.))
                    .child(Input::new(&self.composer).h_full()),
            )
            .child(
                h_flex()
                    .justify_between()
                    .items_center()
                    .child(
                        div()
                            .text_xs()
                            .text_color(cx.theme().muted_foreground)
                            .child(if disabled {
                                SharedString::from("select a room to send")
                            } else {
                                self.status.clone()
                            }),
                    )
                    .child(
                        // The membrane affordance: attach a rehydratable cap-bounded
                        // fork of the deos world (minted by the comms-PD's
                        // MembraneHost). Inert in the pure-mock demo; live in deos.
                        div()
                            .id("attach-membrane")
                            .px_2()
                            .py_1()
                            .rounded_md()
                            .bg(cx.theme().secondary)
                            .cursor_pointer()
                            .text_xs()
                            .child("⬡ attach membrane")
                            .on_mouse_down(
                                MouseButton::Left,
                                cx.listener(|this, _ev, _win, cx| {
                                    this.status = SharedString::from(
                                        "membrane: mint via comms-PD MembraneHost (see docs/deos/MEMBRANE-MERGE-SEAM.md)",
                                    );
                                    cx.notify();
                                }),
                            ),
                    ),
            )
    }
}

impl Focusable for ChatView {
    fn focus_handle(&self, _: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for ChatView {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let header = self
            .selected
            .and_then(|i| self.rooms.get(i))
            .map(|r| r.display_name.clone())
            .unwrap_or_else(|| "deos-chat".to_string());
        let topic = self
            .selected
            .and_then(|i| self.rooms.get(i))
            .and_then(|r| r.topic.clone());

        let sidebar = self.render_sidebar(cx);
        let timeline = self.render_timeline(cx);
        let composer = self.render_composer(cx);

        h_flex()
            .size_full()
            .track_focus(&self.focus)
            .key_context("ChatView")
            .bg(cx.theme().background)
            .text_color(cx.theme().foreground)
            .child(sidebar)
            .child(
                v_flex()
                    .flex_1()
                    .min_w(px(0.))
                    .h_full()
                    .child(
                        v_flex()
                            .px_3()
                            .py_2()
                            .border_b_1()
                            .border_color(cx.theme().border)
                            .child(div().font_weight(gpui::FontWeight::BOLD).child(header))
                            .when_some(topic, |d, t| {
                                d.child(
                                    div()
                                        .text_xs()
                                        .text_color(cx.theme().muted_foreground)
                                        .child(t),
                                )
                            }),
                    )
                    .child(timeline)
                    .child(composer),
            )
    }
}

// --- presentation helpers (the computed timeline pass) ----------------------

/// `@ember:deos.local` → `ember`.
fn short_sender(s: &str) -> String {
    s.trim_start_matches('@')
        .split(':')
        .next()
        .unwrap_or(s)
        .to_string()
}

/// A stable per-sender color (hash → hue) so a glance reads who-said-what.
fn sender_color(s: &str) -> Hsla {
    let mut h: u32 = 2166136261;
    for b in s.bytes() {
        h = (h ^ b as u32).wrapping_mul(16777619);
    }
    let hue = (h % 360) as f32 / 360.0;
    gpui::hsla(hue, 0.55, 0.62, 1.0)
}

fn time_label(ms: u64) -> String {
    let secs = (ms / 1000) % 86_400;
    let h = secs / 3600;
    let m = (secs % 3600) / 60;
    format!("{h:02}:{m:02}")
}

fn day_label(ms: u64) -> String {
    // A coarse, dependency-free day stamp (days since epoch). Good enough for the
    // separator; a real client would localize. Kept tiny on purpose.
    let day = ms / 86_400_000;
    format!("· day {day} ·")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_sender_strips_sigil_and_server() {
        assert_eq!(short_sender("@ember:deos.local"), "ember");
        assert_eq!(short_sender("plain"), "plain");
    }

    #[test]
    fn sender_color_is_stable() {
        assert_eq!(sender_color("@a:b"), sender_color("@a:b"));
    }

    #[test]
    fn time_label_formats_hh_mm() {
        // 1h 1m past midnight = 3660s = 3_660_000 ms.
        assert_eq!(time_label(3_660_000), "01:01");
    }
}
