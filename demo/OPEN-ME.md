# The Commons — a crowd authors a verifiable story

A self-contained web page you open in the morning and **watch a crowd collectively
author a verifiable story**: the real story loads and renders, a simulated assembly
casts custody-signed ballots on the real quorum engine, the winning branch advances as
one verified turn, on to an ending, and a stranger's replay proves the receipt chain.

No extension. No server logic. The page runs the **real** shipping pieces in-tab:

- the wasm `StoryWorld` (a spween CYOA compiled from `stories/the-commons.scene`);
- the shipping `<dregg-story collective>` element + `StoryEngine`, wired in-page via
  `setStoryPortFactory` (the page-SDK path — the element speaks a story port that
  routes to an in-page engine instead of an extension);
- the real federation-grade `CollectiveChoiceEngine` (write-once ballots, monotone
  tallies, an `AffineLe` quorum gate) deciding every branch.

## Open it — one command

```
node demo/serve.mjs
```

Then open **http://127.0.0.1:8787** in Chrome or Firefox.

(A tiny static server is needed because the page loads an ES module + a wasm binary,
and wasm-bindgen instantiates it via `instantiateStreaming`, which requires a real
HTTP origin and the `application/wasm` MIME — a bare `file://` open won't do it.
`node demo/serve.mjs 9000` picks a different port.)

### What you'll see

1. The story loads at the river's bend and **replay-verifies** (the free, trustless tier).
2. The assembly of seven villagers votes each branch — each ballot flashes a visible
   **"✍ signing turn…"** beat (the custody write, made legible) and lands on the live
   tally. You watch the tally grow, the quorum resolve, and the winner advance.
3. It plays through to an ending, then runs `verify()` and shows
   **"✓ receipt chain verified — nothing was rewritten."**
4. **Vote yourself:** click **⏸ pause (vote yourself)**, then click an option inside
   the story to cast your own ballot as `you` (an eligible voter in the roster).

## The driven run (it worked, shown)

```
node demo/run.mjs
```

Loads the demo in headless Chromium, waits for the crowd to reach the ending, **asserts**
the story advanced through ≥2 crowd-voted branches (the passage changed and the receipt
tape grew each round) and that `verify()` replayed true, then writes:

- `demo/run/screenshot.png` — the played-out story;
- `demo/run/transcript.txt` — each round: passage, options, tally, winner, receipt count.

A most-recent run reached `intro → river → reckoning → ending_open` across **3** branches,
receipt tape `1 → 4`, `verify() == true`.
