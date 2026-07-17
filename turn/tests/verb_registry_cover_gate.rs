//! # The verb-registry cover gate — the anti-drift ratchet.
//!
//! FAILS when any `Effect` variant in `turn/src/action.rs` lacks a reified
//! `EffectTag` in the Lean registry
//! `metatheory/Dregg2/Substrate/VerbRegistry.lean` (or vice versa), so the
//! four-substance classification cover cannot drift silently again. It exists
//! because it DID drift: post verb-lockstep the registry pinned 27 tags while
//! the wire enum grew to 34 (`SetProgram`, `Promise`, `Notify`, `React`,
//! `Mint`, `ShieldedTransfer`, `Custom` landed unclassified).
//!
//! ## Mechanism, and why this shape
//!
//! Source-to-source pin: this test `include_str!`s BOTH sources and
//! mechanically extracts (a) the Rust `pub enum Effect` variant names and
//! (b) the Lean `inductive EffectTag` constructor names, then requires them
//! to be IDENTICAL AS ORDERED SEQUENCES. Rationale over the alternatives:
//!
//!  * an *emitted roster file* (Lean writes, Rust pins) adds a generated
//!    intermediate that goes stale exactly when nobody regenerates it — the
//!    failure mode we are closing. `include_str!` of the two PRIMARY sources
//!    has no intermediate: editing either source re-runs the comparison at
//!    the next `cargo test`, with no regeneration step to forget;
//!  * a *reified-tag count check* (27 == 27) would pass under compensating
//!    drift (one added + one removed). Name-by-name, order-sensitive
//!    equality cannot.
//!
//! Order matters twice: the durable postcard codec is discriminant-index-
//! sensitive (a new `Effect` variant MUST append, never insert — see the
//! `Mint` doc comment in `action.rs`), and the registry documents "the order
//! mirrors `action.rs`". So the gate pins the full ordered roster, which
//! also catches an insertion that would silently shift wire discriminants.
//!
//! ## The other half of the tooth (Lean side)
//!
//! Name-parity alone does not prove every tag is *classified*. That half is
//! the Lean compiler: `VerbRegistry.classify : EffectTag → Classification`
//! is an exhaustive match (an uncovered constructor is a COMPILE ERROR), and
//! `mem_allEffectTags : ∀ t, t ∈ allEffectTags` proves the roster list
//! covers every constructor. Chain: Rust variant ⇒ (this test) Lean
//! `EffectTag` constructor ⇒ (Lean exhaustiveness) classified under the
//! four-substance discipline. A wire variant added without a classification
//! now fails EITHER this test (no tag) or the Lean build (tag unclassified).
//!
//! ## Anti-vacuity
//!
//! A broken extractor must FAIL, never pass on two empty lists: the test
//! asserts a floor of 27 variants on each side and pins the first anchor
//! (`SetField`) explicitly.

/// The Rust wire enum — the ground truth the registry must cover.
const ACTION_RS: &str = include_str!("../src/action.rs");

/// The Lean registry — the classification cover under the four-substance
/// discipline (value linear / authority non-forgeable / evidence monotone /
/// state guarded-mutable).
const VERB_REGISTRY_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Substrate/VerbRegistry.lean");

/// Strip `//`-to-EOL line comments (covers `///` doc comments) and
/// `/* ... */` block comments. The `Effect` enum body contains no string
/// literals outside comments, so no string-state tracking is needed; if one
/// is ever added the anchors/floor below fail loudly rather than silently.
fn strip_comments(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
        } else if bytes[i] == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
            i += 2;
            while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                i += 1;
            }
            i += 2;
        } else {
            out.push(bytes[i] as char);
            i += 1;
        }
    }
    out
}

/// Extract the ordered variant names of `pub enum Effect { ... }` from
/// `action.rs` source: walk the enum body tracking brace depth; a variant
/// name is the identifier appearing at depth 1 in "expecting" position
/// (start of body, after a `,`, or after a variant's `{...}` field block
/// closes). Attributes (`#[...]`) at variant position are skipped.
fn rust_effect_variants(src: &str) -> Vec<String> {
    let clean = strip_comments(src);
    let start = clean
        .find("pub enum Effect {")
        .expect("gate: `pub enum Effect {` not found in action.rs");
    let body = &clean[start..];
    let bytes = body.as_bytes();
    let mut variants = Vec::new();
    let mut depth: i32 = 0;
    let mut expecting = false;
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        match c {
            b'{' => {
                depth += 1;
                if depth == 1 {
                    expecting = true;
                }
                i += 1;
            }
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    break; // end of the enum body
                }
                if depth == 1 {
                    // a variant's field block closed; next (after `,`) is a name
                    expecting = true;
                }
                i += 1;
            }
            b',' if depth == 1 => {
                expecting = true;
                i += 1;
            }
            b'#' if depth == 1 => {
                // skip an attribute: `#[ ... ]` (bracket-balanced)
                let mut bd = 0i32;
                while i < bytes.len() {
                    match bytes[i] {
                        b'[' => bd += 1,
                        b']' => {
                            bd -= 1;
                            if bd == 0 {
                                i += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    i += 1;
                }
            }
            _ if depth == 1 && expecting && (c as char).is_ascii_uppercase() => {
                let mut j = i;
                while j < bytes.len()
                    && ((bytes[j] as char).is_ascii_alphanumeric() || bytes[j] == b'_')
                {
                    j += 1;
                }
                variants.push(body[i..j].to_string());
                expecting = false;
                i = j;
            }
            _ => {
                i += 1;
            }
        }
    }
    variants
}

/// Extract the ordered constructor names of `inductive EffectTag` from the
/// Lean registry source: take the text from the `inductive EffectTag` header
/// to its `deriving` clause; every `|`-introduced identifier is a
/// constructor.
fn lean_effect_tags(src: &str) -> Vec<String> {
    // Lean line comments are `--`; strip them so a commented-out tag can
    // never satisfy the gate.
    let clean: String = src
        .lines()
        .map(|l| l.split("--").next().unwrap_or(""))
        .collect::<Vec<_>>()
        .join("\n");
    let start = clean
        .find("inductive EffectTag")
        .expect("gate: `inductive EffectTag` not found in VerbRegistry.lean");
    let body = &clean[start..];
    let end = body
        .find("deriving")
        .expect("gate: `deriving` clause of EffectTag not found");
    let body = &body[..end];
    let mut tags = Vec::new();
    for piece in body.split('|').skip(1) {
        let name: String = piece
            .trim_start()
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if !name.is_empty() {
            tags.push(name);
        }
    }
    tags
}

#[test]
fn every_effect_variant_is_classified_in_the_lean_registry() {
    let rust = rust_effect_variants(ACTION_RS);
    let lean = lean_effect_tags(VERB_REGISTRY_LEAN);

    // Anti-vacuity: a silently-broken extractor must fail here, not pass on
    // two empty (hence equal) lists.
    assert!(
        rust.len() >= 27,
        "gate extractor floor: only {} Rust variants parsed — extractor broken?",
        rust.len()
    );
    assert!(
        lean.len() >= 27,
        "gate extractor floor: only {} Lean tags parsed — extractor broken?",
        lean.len()
    );
    assert_eq!(
        rust.first().map(String::as_str),
        Some("SetField"),
        "gate anchor: first Effect variant should be SetField"
    );

    let unclassified: Vec<&String> = rust.iter().filter(|v| !lean.contains(v)).collect();
    let stale: Vec<&String> = lean.iter().filter(|t| !rust.contains(t)).collect();

    assert!(
        unclassified.is_empty() && stale.is_empty(),
        "verb-registry cover DRIFT.\n\
         Effect variants with NO EffectTag (unclassified — add the tag to\n\
         metatheory/Dregg2/Substrate/VerbRegistry.lean and classify it under\n\
         the four-substance discipline): {:?}\n\
         EffectTags with NO Effect variant (stale — the wire variant was\n\
         removed or renamed; retire the tag): {:?}\n\
         rust roster ({}): {:?}\n\
         lean roster ({}): {:?}",
        unclassified,
        stale,
        rust.len(),
        rust,
        lean.len(),
        lean
    );

    // Ordered equality: postcard wire discriminants are index-sensitive and
    // the registry mirrors action.rs order — an INSERTION (silent
    // discriminant shift) must fail even when both name-sets match.
    assert_eq!(
        rust, lean,
        "verb-registry roster ORDER drift: same names, different order.\n\
         New Effect variants must APPEND (postcard discriminants are\n\
         index-sensitive) and the registry mirrors action.rs order."
    );
}
