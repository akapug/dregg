# gpui offscreen render — the real cockpit, no GPU (proven)

The seL4 `qemu_virt_aarch64` machine has no GPU, so starbridge-v2's gpui (wgpu → Vulkan)
cockpit cannot present to a window there. This is the proven path to render it anyway —
**gpui → software Vulkan (lavapipe) → an offscreen texture → RGBA readback → the seL4
compositor framebuffer** — so the real cockpit can be a Mode/tab inside the VM, beside the
live image viewer.

## Proven (not theorized)

`docs/desktop-os-research/patches/gpui-offscreen-proof.png` (1024×640 RGBA8) is a real gpui
scene — a cockpit-shaped layout with crisp anti-aliased text, rounded bordered panels, the
world/shell/reflect columns — rendered **with no GPU and no window** on persvati via lavapipe
(`llvmpipe (LLVM 20.1.8), backend=Vulkan, type=Cpu`), through the *actual* `WgpuRenderer`
the real cockpit uses. Scene = 18 quads + 258 monochrome glyph sprites; BGRA→RGBA + premultiplied
alpha + 256-byte row alignment all correct.

## The patch — `patches/gpui-offscreen.patch`

A ~615-line diff against zed's `gpui_wgpu` (the renderer leaf the whole gpui stack already depends
on). `cargo check` + `cargo clippy -p gpui_wgpu` clean; the windowed path is intact (the surface
became `Option`, all 5 sites guarded). Exactly the three functions the feasibility lane scoped,
modelled on the Metal `render_scene_to_image` (`gpui_macos/src/metal_renderer.rs:628`):
- `wgpu_context.rs`: `offscreen_instance()` (`display: None`) + `new_offscreen()` +
  `select_offscreen_adapter_and_device()` (`ZED_OFFSCREEN_PREFER_CPU=1` floats lavapipe to the top).
- `wgpu_renderer.rs`: **(a)** `draw_scene_to_view(scene, &TextureView, w, h)` — the extracted
  shared drawing core (globals + encoder/pass/overflow-grow/submit, minus `present()`); `draw()`
  now = acquire frame → `draw_scene_to_view` → present. **(b)** `render_scene_to_image(scene,
  Size<DevicePixels>) -> (Vec<u8> rgba, u32, u32)` — owned `Bgra8Unorm` texture
  (`RENDER_ATTACHMENT|COPY_SRC`) → `draw_scene_to_view` → `copy_texture_to_buffer` → `map_async`
  + `poll(Wait)` → BGRA→RGBA swizzle (returns raw RGBA, adds no dep). **(c)** `new_offscreen()`
  surfaceless ctor.

Reproduce: patched fork on persvati `~/src/zed`; harness `/tmp/gpui-offscreen-poc/`; run with
`VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json ZED_OFFSCREEN_PREFER_CPU=1`.

## Vendor-into-dregg plan (the next lane)

The chain is `starbridge-v2 --features gpui-ui → gpui + gpui_platform → gpui_linux (gpui_wgpu)`,
so the patch lands exactly where the stack already depends.

1. **Land the patch on starbridge-v2's pinned rev.** starbridge-v2 pins zed
   `rev = fca2ccd403e8d13c8f4b968cda2f2c322f420f5a` (the PoC fork is at `cccc7b2`). Re-apply the
   diff onto `fca2ccd`'s `gpui_wgpu` (the `draw`/`new_internal` anchors are stable — expect
   line-offset fuzz only). **Preferred:** push a dregg-owned fork branch (`breadstuffs/zed@offscreen-fork`
   off `fca2ccd`) and repoint the `gpui` + `gpui_platform` git deps at it (clean, reviewable,
   survives rebuilds). Alt: a `[patch]` overlay in starbridge-v2's manifest (lighter, but git-source
   `[patch]` is finicky workspace-wide).
2. **Wire it to the seL4 framebuffer.** Implement `PlatformHeadlessRenderer` for a wgpu renderer
   (using `new_offscreen` + `render_scene_to_image` — ~1 thin impl, the heavy lifting is done), add
   a headless cockpit-render entry beside `run_window` (`main.rs:124`): build the `Cockpit` element
   tree in a headless `App` (text_system = `CosmicTextSystem`), drive a frame, `render_scene_to_image`,
   then blit the RGBA into the VM framebuffer (same byte format the live image-viewer Mode already
   writes). For first bring-up, push a hand-built Scene (as the PoC does) to prove the seL4 plumbing,
   then swap in the real cockpit element tree.

The honest frontier beyond this: the cockpit's `shell::Scene` is a window-manager model, not a gpui
`Scene` — the real cockpit element tree needs a live headless `App`/`Window` (step 2's harness), which
this PoC stands in for with a hand-authored cockpit-shaped Scene through the identical renderer path.
