//! cargo-pgrx schema-generation entrypoint (the `pgrx_embed_<crate>` binary).
//! Written by the `cargo pgrx new` template; you should not need to touch it.
//! Built only under the `pgrx` feature (see Cargo.toml `required-features`).
::pgrx::pgrx_embed!();
