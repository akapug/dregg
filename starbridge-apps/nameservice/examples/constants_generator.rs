//! Generator for `pages/constants.generated.js`.
//!
//! Run with `cargo run -p starbridge-nameservice --example constants_generator`
//! to (re)write the canonical JS constants module from the Rust source of
//! truth (`starbridge_nameservice::web_constants`). The `constants_js_is_in_sync`
//! test fails if the committed file drifts from this output, so regenerate here
//! whenever a slot index, factory-vk, or event topic changes in `src/lib.rs`.

use std::path::Path;

fn main() {
    let module = starbridge_nameservice::web_constants();
    let js = module.render_js();

    // The pages/ dir is resolved relative to this crate's manifest so the
    // generator works from any cwd.
    let out = Path::new(env!("CARGO_MANIFEST_DIR")).join("pages/constants.generated.js");
    std::fs::write(&out, &js).expect("write constants.generated.js");
    eprintln!("wrote {} ({} bytes)", out.display(), js.len());
}
