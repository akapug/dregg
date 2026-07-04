//! THE SERVICE DIRECTORY panel (📇 DIRECTORY) — the whole-image discover/announce
//! surface, the sibling of the per-cell [`super::panels_moldable`] service explorer.
//!
//! It renders the live [`ServiceDirectory`] (every service-publishing cell in the
//! cockpit's embedded image, each interface derived live) and lets the operator
//! ANNOUNCE a selected service as a REAL verified turn through the embedded executor
//! — a witnessed `Effect::EmitEvent` the next discover reads back, closing the
//! publish loop over the real ledger.

use super::*;

use starbridge_v2::service_directory::{
    AnnounceOutcome, DiscoveredService, ServiceDirectory, ServiceFilter, ServiceKind,
};

impl Cockpit {
    /// THE SERVICE DIRECTORY — browse every service-publishing cell in the live
    /// image and announce one as a real verified turn.
    pub(crate) fn service_directory_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let w = self.world.borrow();
        let dir = ServiceDirectory::discover(
            &w,
            &ServiceFilter {
                include_non_services: self.service_directory_include_caps,
                ..Default::default()
            },
        );

        let mut col = div()
            .id("cockpit-scroll-body-directory")
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_y_scroll();

        col = col.child(section_title(
            "📇 DIRECTORY · discover every service in the image → announce one",
        ));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The WHOLE-IMAGE sibling of the per-cell service explorer: it scans the live ledger \
             for every cell that publishes a service interface (each interface derived live, no \
             ledger wiring), listing its interface-id, method count, and kind. Selecting a \
             service and pressing ANNOUNCE publishes its interface as a REAL verified turn (an \
             Effect::EmitEvent carrying the canonical announce topic, committed through the \
             embedded executor) — a witnessed receipt the next discover reads back, so a service \
             is marked ANNOUNCED exactly when a genuine announce turn for it has committed.",
        ));

        // The live tally + the include-capabilities toggle.
        let include_caps = self.service_directory_include_caps;
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_2()
                .child(div().text_xs().text_color(theme::text()).child(format!(
                    "{} service(s) · {} announced",
                    dir.services.len(),
                    dir.announced_count
                )))
                .child(cycle_chip(
                    cx,
                    "dir-include-caps",
                    if include_caps {
                        "⊖ services only".to_string()
                    } else {
                        "⊕ include opaque capabilities".to_string()
                    },
                    if include_caps {
                        theme::accent()
                    } else {
                        theme::good()
                    },
                    Cockpit::service_directory_toggle_caps,
                )),
        );

        col = col.child(section_title("discovered services"));
        if dir.services.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "(no service-publishing cells in this image — a cell publishes an interface when \
                 its program dispatches on a method symbol. Toggle ⊕ to also list opaque \
                 capability cells.)",
            ));
        }
        for s in &dir.services {
            col = col.child(self.service_directory_row(s, cx));
        }

        // The ANNOUNCE section — publish the selected service's interface.
        col = col.child(section_title("announce"));
        let selected = self.service_directory_selected;
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_1()
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(match selected {
                            Some(c) => {
                                format!("selected service {}", reflect::short_hex(c.as_bytes()))
                            }
                            None => "(pick a service above)".to_string(),
                        }),
                )
                .when(selected.is_some(), |d| {
                    d.child(
                        Button::new(SharedString::from("dir-announce"))
                            .label("announce → publish interface (real turn)")
                            .primary()
                            .xsmall()
                            .on_click(cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                                this.service_directory_announce(cx);
                            })),
                    )
                }),
        );

        if let Some(b) = &self.service_directory_outcome {
            let color = if b.contains("REFUSED") {
                theme::bad()
            } else {
                theme::good()
            };
            col = col.child(
                div()
                    .mt_1()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel())
                    .text_xs()
                    .text_color(color)
                    .child(b.clone()),
            );
        }

        col.into_any_element()
    }

    /// One discovered-service row — its handle, kind, interface-id, method count,
    /// the announced badge, and a select button.
    fn service_directory_row(
        &self,
        s: &DiscoveredService,
        cx: &mut Context<Self>,
    ) -> gpui::AnyElement {
        let selected = self.service_directory_selected == Some(s.cell);
        let (kind_label, kind_color) = match s.kind {
            ServiceKind::Service => ("service", theme::good()),
            ServiceKind::Capability => ("capability", theme::muted()),
        };
        let cell = s.cell;
        let pick_id = SharedString::from(format!(
            "dir-pick-{}",
            reflect::short_hex(s.cell.as_bytes())
        ));
        let invokable = s.kind == ServiceKind::Service;
        div()
            .flex()
            .justify_between()
            .items_center()
            .px_2()
            .py_0p5()
            .rounded_md()
            .bg(if selected {
                theme::panel_hi()
            } else {
                theme::panel()
            })
            .child(
                div()
                    .flex()
                    .flex_col()
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::text())
                            .child(format!("⬡ {}", s.label)),
                    )
                    .child(div().text_xs().text_color(theme::muted()).child(format!(
                        "interface {} · {} method(s)",
                        reflect::short_hex(&s.interface_id),
                        s.method_count,
                    ))),
            )
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_1()
                    .child(pill(kind_label, kind_color))
                    .when(s.announced, |d| d.child(pill("ANNOUNCED", theme::good())))
                    .when(invokable, |d| {
                        d.child(
                            Button::new(pick_id)
                                .label(if selected { "selected" } else { "select" })
                                .xsmall()
                                .outline()
                                .on_click(cx.listener(move |this, _ev: &ClickEvent, _w, cx| {
                                    this.service_directory_select(cell, cx);
                                })),
                        )
                    }),
            )
            .into_any_element()
    }

    /// Select a discovered service to announce.
    pub(crate) fn service_directory_select(&mut self, cell: CellId, cx: &mut Context<Self>) {
        self.service_directory_selected = Some(cell);
        self.service_directory_outcome = None;
        cx.notify();
    }

    /// Toggle whether the listing includes opaque (no-interface) capability cells.
    pub(crate) fn service_directory_toggle_caps(&mut self, cx: &mut Context<Self>) {
        self.service_directory_include_caps = !self.service_directory_include_caps;
        cx.notify();
    }

    /// **ANNOUNCE the selected service — a real verified turn.** Publishes the
    /// selected service cell's interface to the directory: builds the announcer's
    /// (the cockpit `user` principal) [`Effect::EmitEvent`] carrying the announce
    /// topic + the interface-id, and commits it through the embedded executor. A
    /// refusal (nothing to announce / the executor gated the announcer) is surfaced
    /// in-band. After a commit the discovered listing re-reads the announcement back
    /// (the loop closes over the real ledger).
    pub(crate) fn service_directory_announce(&mut self, cx: &mut Context<Self>) {
        let Some(service) = self.service_directory_selected else {
            self.service_directory_outcome =
                Some("REFUSED: pick a service to announce first".to_string());
            cx.notify();
            return;
        };
        // The announcer is the cockpit `user` principal (the operator's own hand).
        let announcer = self.anchors[2];
        let outcome = {
            let mut w = self.world.borrow_mut();
            ServiceDirectory::announce(&mut w, announcer, service)
        };
        self.service_directory_outcome = Some(match outcome {
            AnnounceOutcome::Announced {
                receipt,
                interface_id,
                method_count,
            } => format!(
                "announced interface {} ({} method(s)) · receipt {}",
                reflect::short_hex(&interface_id),
                method_count,
                reflect::short_hex(&receipt.receipt_hash()),
            ),
            AnnounceOutcome::Refused {
                reason,
                by_executor,
            } => format!(
                "REFUSED announce ({}): {reason}",
                if by_executor {
                    "executor"
                } else {
                    "front-door"
                }
            ),
        });
        self.refresh_cells();
        cx.notify();
    }
}
