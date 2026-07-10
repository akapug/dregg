//! **A collectively-authorable, verifiable CYOA in the tab** — the wasm realization of
//! `spween-dregg`'s single-player [`Driver`](spween_dregg::Driver), the narrative sibling
//! of [`DocCollabWorld`](crate::bindings_doc::DocCollabWorld).
//!
//! A spween story is a graph of passages; a *choice* is a cap-bounded **turn** the real
//! executor admits IFF the choice's gate passes; a *playthrough* is an **un-retconnable
//! receipt chain** a stranger can replay (`spween-dregg/src/verify.rs`). [`StoryWorld`]
//! holds a `spween-dregg` [`WorldCell`](spween_dregg::WorldCell) +
//! [`Driver`](spween_dregg::Driver) at [`NodeTarget::Local`](dregg_node_target::NodeTarget)
//! — in-process, NO networking — and exposes exactly the contract the `<dregg-story>`
//! element consumes: render the current passage, list condition-gated choices, `advance`
//! one verified turn, and `verify` the whole chain by replay.
//!
//! ## ⚠ PLATFORM NOTE — this rides the NATIVE executor, not (yet) wasm32
//!
//! [`StoryWorld`] wraps `spween-dregg`'s real [`Driver`], whose turns are admitted by
//! [`dregg_app_framework::EmbeddedExecutor`]. That executor lives in `dregg-app-framework`,
//! whose dependency set is UNCONDITIONALLY non-wasm32 (`axum 0.8` + `tokio` `full` +
//! `reqwest` + `tower-http`) — the SAME crate the wasm `Cargo.toml` already documents it
//! must not pull. So this module and its `spween-dregg` dependency are gated
//! `cfg(not(target_arch = "wasm32"))`: the binding, its `#[wasm_bindgen]` surface, and its
//! host-target test are real and exercised, but the story path is NOT in the shipped wasm
//! bundle until `spween-dregg` grows a wasm-safe executor route that does not ride
//! `dregg-app-framework` (a change to `spween-dregg`, out of this lane's scope). The
//! `#[wasm_bindgen]` attributes are kept so that flip is one gate away — mirroring the
//! project's "one flip from live" manifest philosophy.

use wasm_bindgen::prelude::*;

use spween_dregg::{Driver, Playthrough, Scene, WorldCell, parse, verify};

/// The deterministic deploy seed. `spween-dregg` derives the world-cell identity from the
/// scene id + seed, so a fixed seed makes a playthrough re-verify against a freshly
/// re-deployed, identically-seeded world (the `verify` path's requirement).
const STORY_SEED: u8 = 7;

/// The synthetic filename a browser-supplied `.scene` source is parsed under (only feeds
/// the scene id / error spans — the source string is authoritative).
const STORY_FILENAME: &str = "story.scene";

/// **A spween story running as verifiable turns, in the tab.** Owns a `spween-dregg`
/// [`WorldCell`] + [`Driver`] at `NodeTarget::Local` (the default — in-process, no
/// networking). Each [`Self::advance`] runs the stock `spween::Runtime`'s gate-checked
/// `select_choice` and flushes the resulting cell writes as ONE cap-gated verified turn,
/// appending its receipt to the chain; [`Self::verify`] replays that chain against a fresh
/// world — the "stranger checks the story" tooth.
#[wasm_bindgen]
pub struct StoryWorld {
    /// The compiled scene. LEAKED to `'static`: a `Driver<'s>` borrows the `Scene` for its
    /// runtime, and a `#[wasm_bindgen]` struct cannot be self-referential. A `StoryWorld`
    /// lives for the page's lifetime, so one small per-story leak is the honest cost of
    /// the borrow (the alternative — an `ouroboros`/`Pin` self-reference — buys nothing
    /// here). The same `&'static Scene` re-deploys the fresh world `verify` replays.
    scene: &'static Scene,
    /// The stock-runtime driver over the world-cell; each `advance` is a verified turn.
    driver: Driver<'static>,
}

#[wasm_bindgen]
impl StoryWorld {
    /// **Compile a spween `.scene` source into a verifiable world and start the
    /// playthrough.** FAIL-CLOSED: a source that does not parse to a scene is a `JsError`
    /// (no half-deployed world). The intro passage's entry effects commit as the genesis
    /// turn, so the story's first receipt exists before any choice is taken.
    #[wasm_bindgen(constructor)]
    pub fn new(scene_source: String) -> Result<StoryWorld, JsError> {
        Self::try_new(&scene_source).map_err(|e| JsError::new(&e))
    }

    /// The fallible core — `String` errors, wasm-bindgen-free, so the fail-closed path is
    /// testable NATIVELY (constructing a `JsError` panics off-wasm). `new` wraps this in
    /// `JsError`. Fail-closed: an unparseable scene / failed deploy mints no world.
    fn try_new(scene_source: &str) -> Result<StoryWorld, String> {
        let scene = parse(scene_source, STORY_FILENAME).map_err(|e| e.to_string())?;
        // Leak the scene to `'static` so the borrowing `Driver` can be owned by this struct.
        let scene: &'static Scene = Box::leak(Box::new(scene));

        let world = WorldCell::deploy(scene, STORY_SEED).map_err(|e| e.to_string())?;
        let driver = Driver::start(world, scene).map_err(|e| e.to_string())?;

        Ok(StoryWorld { scene, driver })
    }

    /// The current passage name (empty once the scene has ended).
    #[wasm_bindgen(js_name = currentPassage)]
    pub fn current_passage(&self) -> String {
        self.driver.current_passage().unwrap_or_default()
    }

    /// The current passage's narrative prose — the text to render. Reads spween's own
    /// per-passage prose (`Runtime::current_prose`); empty once the scene has ended.
    #[wasm_bindgen(js_name = passageProse)]
    pub fn passage_prose(&self) -> String {
        self.driver.prose().unwrap_or_default()
    }

    /// The choices at the current passage as JSON: `[{index, text, available}]`.
    /// `available` is the condition-gated availability the stock runtime already computes
    /// against the cell-backed state (`spween-dregg`'s [`ChoiceView`](spween_dregg::ChoiceView)).
    /// The `<dregg-story>` element renders an unavailable choice as disabled; a call to
    /// [`Self::advance`] on it is refused in-band regardless (fail-closed at the turn).
    #[wasm_bindgen(js_name = choicesJson)]
    pub fn choices_json(&self) -> String {
        use serde_json::json;
        let rows: Vec<serde_json::Value> = self
            .driver
            .choices()
            .into_iter()
            .map(|c| {
                json!({
                    "index": c.index,
                    "text": c.text,
                    "available": c.available,
                })
            })
            .collect();
        json!(rows).to_string()
    }

    /// **Advance the story by taking choice `index` — as ONE verified turn.** Runs the
    /// stock `select_choice` (which checks the gate, runs the effects, navigates) and
    /// flushes the buffered cell writes as a single cap-gated turn, appending its receipt.
    ///
    /// Returns JSON `{ ok, passage, receiptCount, commitmentHex, error? }`. FAIL-CLOSED: a
    /// gated (condition-not-met) or out-of-range choice — or a choice on an already-ended
    /// scene — returns `{ ok: false, error }` and NOTHING commits (`receiptCount` and
    /// `commitmentHex` still describe the last good state). This is the story advancing
    /// only ever along an eligible edge.
    pub fn advance(&mut self, index: usize) -> String {
        use serde_json::json;
        match self.driver.advance(index) {
            Ok(_step) => json!({
                "ok": true,
                "passage": self.current_passage(),
                "receiptCount": self.receipt_count(),
                "commitmentHex": self.commitment_hex(),
            })
            .to_string(),
            Err(e) => json!({
                "ok": false,
                "passage": self.current_passage(),
                "receiptCount": self.receipt_count(),
                "commitmentHex": self.commitment_hex(),
                "error": e.to_string(),
            })
            .to_string(),
        }
    }

    /// **Verify the whole playthrough by replay** — the un-retconnable "stranger checks the
    /// story" check. Re-drives a FRESH, identically-seeded world through the recorded choice
    /// sequence and confirms it reproduces the exact committed state at every step, AND that
    /// the receipt chain links cleanly (`spween-dregg/src/verify.rs` — both teeth). A forged
    /// (ineligible) choice is refused by the executor on replay; a tampered receipt breaks
    /// the chain. Returns `true` iff the playthrough is authentic.
    pub fn verify(&self) -> bool {
        let Ok(fresh) = WorldCell::deploy(self.scene, STORY_SEED) else {
            return false;
        };
        verify(fresh, self.scene, &self.driver.playthrough()).is_ok()
    }

    /// The world-cell's current committed state commitment (hex) — the `post_state_hash` of
    /// the last committed turn (genesis if no choice has been taken yet). This is the
    /// stranger's check surface: it MOVES on every advance and pins exactly one committed
    /// history.
    #[wasm_bindgen(js_name = commitmentHex)]
    pub fn commitment_hex(&self) -> String {
        let last = self
            .driver
            .steps()
            .last()
            .map(|s| &s.receipt)
            .or_else(|| self.driver.genesis());
        match last {
            Some(r) => crate::bindings::hex_encode(&r.post_state_hash),
            None => String::new(),
        }
    }

    /// The committed-receipt count — the audit-tape length (the genesis turn plus one per
    /// advanced choice). Proves each advance was a real verified turn, not a local poke.
    #[wasm_bindgen(js_name = receiptCount)]
    pub fn receipt_count(&self) -> usize {
        // genesis (1, once started) + one per committed choice-step.
        let genesis = usize::from(self.driver.genesis().is_some());
        genesis + self.driver.steps().len()
    }

    /// Whether the scene has ended (no further choices).
    #[wasm_bindgen(js_name = isEnded)]
    pub fn is_ended(&self) -> bool {
        self.driver.is_ended()
    }
}

// ── PHASE 2 (stub — do NOT build here) ────────────────────────────────────────────────
//
// The COLLECTIVE mode: the crowd co-authors the story. `spween-dregg`'s `run_collective`
// drives a `CollectiveRound` over the real cap-bounded `VoteEngine` — the audience polls
// each branch, the winning branch fires as a turn. A later lane wires this to `<dregg-poll>`:
//
//   pub fn open_branch_poll(&mut self) -> String   // JSON of the branch options to poll
//   pub fn close_branch_poll(&mut self) -> String  // tally the ballots, advance the winner
//
// over `spween_dregg::{run_collective, CollectiveRound, Ballot, PollContext}`. Left as a
// comment: this lane ships single-player verifiable CYOA only.

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    /// A 3-passage tavern story with a numeric gate (`perception >= 10`, unset ⇒ refused),
    /// plain-choice navigation, and an end. The `<dregg-story>` contract exercised here is
    /// exactly what the browser element calls.
    const TAVERN: &str = r#"---
id: tavern_encounter
title: The Mysterious Stranger
weight: 10
---

=== intro

A hooded figure sits alone in the corner of the tavern.
They gesture for you to approach.

* [Approach cautiously] { perception >= 10 }
  ~ perception_used = true
  -> cautious

* [Approach boldly]
  -> bold

=== bold

You stride over confidently. The stranger seems amused
by your directness.

* [Sit down]
  ~ stranger_trust += 1
  -> conversation

=== cautious

You notice a glint of steel beneath their cloak.

* [Sit down]
  ~ stranger_trust += 2
  -> conversation

=== conversation

The stranger leans close and whispers of an artifact.

* [Thank them and leave]
  -> END
"#;

    /// THE STORY LOOP: compile a real `.scene`, advance through choices as verified turns
    /// (the passage changes + the receipt count grows), a GATED choice is refused
    /// (fail-closed, nothing commits), and the honest playthrough replays true.
    #[test]
    fn story_advances_as_verified_turns_and_reverifies() {
        let mut story = StoryWorld::new(TAVERN.to_string()).expect("the tavern scene compiles");

        // Genesis is committed before any choice: one receipt, we are at `intro`.
        assert_eq!(story.current_passage(), "intro");
        assert_eq!(story.receipt_count(), 1, "the genesis turn is committed");
        assert!(!story.passage_prose().is_empty(), "the intro renders prose");
        assert!(!story.commitment_hex().is_empty());

        // The choices: index 0 "Approach cautiously" is GATED (perception unset ⇒ < 10 ⇒
        // unavailable); index 1 "Approach boldly" is open.
        let choices: serde_json::Value =
            serde_json::from_str(&story.choices_json()).expect("choices are JSON");
        let choices = choices.as_array().expect("a choice array");
        assert_eq!(choices.len(), 2);
        assert_eq!(choices[0]["available"], serde_json::json!(false));
        assert_eq!(choices[1]["available"], serde_json::json!(true));

        // FAIL-CLOSED: advancing the GATED choice is refused; NOTHING commits.
        let refused: serde_json::Value =
            serde_json::from_str(&story.advance(0)).expect("advance returns JSON");
        assert_eq!(
            refused["ok"],
            serde_json::json!(false),
            "gated choice refused"
        );
        assert!(refused.get("error").is_some(), "the refusal carries a why");
        assert_eq!(
            story.current_passage(),
            "intro",
            "still at intro; nothing moved"
        );
        assert_eq!(
            story.receipt_count(),
            1,
            "no turn committed on a refused choice"
        );

        // Advance the OPEN choice (index 1): a real verified turn → `bold`, receipts grow.
        let ok: serde_json::Value =
            serde_json::from_str(&story.advance(1)).expect("advance returns JSON");
        assert_eq!(ok["ok"], serde_json::json!(true));
        assert_eq!(ok["passage"], serde_json::json!("bold"));
        assert_eq!(story.current_passage(), "bold");
        assert_eq!(story.receipt_count(), 2, "one advance = one new receipt");

        // Advance again: bold → conversation (its only choice, index 0).
        let ok2: serde_json::Value =
            serde_json::from_str(&story.advance(0)).expect("advance returns JSON");
        assert_eq!(ok2["ok"], serde_json::json!(true));
        assert_eq!(story.current_passage(), "conversation");
        assert_eq!(story.receipt_count(), 3);

        // And into the ending.
        let done: serde_json::Value =
            serde_json::from_str(&story.advance(0)).expect("advance returns JSON");
        assert_eq!(done["ok"], serde_json::json!(true));
        assert!(story.is_ended(), "the scene ended");
        assert_eq!(story.receipt_count(), 4, "genesis + 3 committed choices");

        // THE STRANGER CHECK: the honest playthrough replays true.
        assert!(story.verify(), "the honest playthrough re-verifies");
    }

    /// A bad scene FAILS CLOSED — no `StoryWorld` is minted from unparseable source.
    #[test]
    fn bad_scene_is_fail_closed() {
        let broken = StoryWorld::try_new("this is not a spween scene {{{");
        assert!(broken.is_err(), "an unparseable scene mints no world");
    }

    /// TAMPER a receipt in the recorded playthrough → `verify` (both teeth) rejects it.
    /// The `StoryWorld` API itself never exposes a mutate-the-tape door; this reaches into
    /// `spween-dregg`'s public `Playthrough` to corrupt a `post_state_hash`, breaking the
    /// hash-chain linkage the un-retconnable check rests on.
    #[test]
    fn tampered_receipt_fails_verification() {
        let mut story = StoryWorld::new(TAVERN.to_string()).expect("compile");
        let _ = story.advance(1); // intro -> bold
        let _ = story.advance(0); // bold  -> conversation

        // The honest chain verifies.
        assert!(story.verify(), "honest chain verifies before tamper");

        // Corrupt the genesis receipt's post_state_hash → the next receipt's pre_state_hash
        // no longer links (LinkageBroken / a diverged replay state).
        let mut tampered: Playthrough = story.driver.playthrough();
        tampered.genesis.post_state_hash = [0xAB; 32];
        let fresh = WorldCell::deploy(story.scene, STORY_SEED).expect("fresh world");
        assert!(
            verify(fresh, story.scene, &tampered).is_err(),
            "a tampered receipt chain is refused"
        );
    }
}
