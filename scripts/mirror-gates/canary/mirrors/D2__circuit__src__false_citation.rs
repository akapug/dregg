//! CANARY (D2) — M11's citation shape. This file asserts `descriptor_by_name` is module-private and
//! leans on that to justify its own copy. `canary-circuit`'s `lib.rs` makes it `pub`, so the
//! justification is false — the mirror is unjustified, and nothing but a citation checker sees it.

/// Kept here because `descriptor_by_name` is module-private.
pub fn shadow_lookup() -> &'static str {
    "{}"
}
