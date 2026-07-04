# Third-party notice — gpui-component

`starbridge-v2` depends on **gpui-component** (the `crates/ui` member), the
shadcn-style widget library for gpui that gives the cockpit its real widgets —
above all a text `Input`, plus `Button`, dock, popovers, pickers, and the rest.

- Upstream: <https://github.com/longbridge/gpui-component>
- License: **Apache-2.0** (`LICENSE-APACHE` in the gpui-component checkout).
  Apache-2.0 is permissive and compatible with this repository's
  AGPL-3.0-or-later: the combined work is distributed under the AGPL, and the
  Apache-2.0 terms (including its NOTICE-retention requirement) are preserved for
  the gpui-component sources.
- Copyright: Longbridge <https://longbridge.com> (2024–2025).

## Vendored fork + provenance

The dependency is consumed from the dregg fork
**`emberian/gpui-component@dregg-repoint`** (a sibling checkout at
`../../gpui-component`, like the `emberian/zed` gpui fork). The fork carries ONE
change to upstream: it re-points every zed-derived dependency
(`gpui`, `gpui_platform`, `gpui_web`, `gpui_macros`, `reqwest_client`) from
`zed-industries/zed@1d217ee` to our fork
`emberian/zed@407a6ffd977d82b828e392f92db5cb34edea9549` — the SAME rev
`starbridge-v2` already pins.

This is a clean re-point, not a port: `gpui/src` at `1d217ee` is byte-identical
to our fork's `gpui/src` (our fork only patches `gpui_linux`/`gpui_platform`/
`gpui_wgpu` — the offscreen/headless renderer — never the gpui API). The result
is ONE resolved `gpui` instance across the cockpit + widget graph. The fork also
replicates the `[patch.crates-io]` the zed monorepo requires of consumers
(`async-process`, `async-task`, vendored `pathfinder_simd`) so it builds green
standalone.

No upstream gpui-component source files were modified; only the workspace
`Cargo.toml` dependency table.
