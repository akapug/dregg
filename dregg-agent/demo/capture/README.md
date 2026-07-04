# demo/capture — the browser-surface capture harness

Records the **web half** of the dregg demo film: the DreggNet surfaces driven in
a real (headless) chromium via Playwright, composited with the terminal agent
film into `../film-browser.mp4` and `../film-full.mp4`.

Full shot-list, honesty labels, and prereqs live in [`../FILM.md`](../FILM.md)
(§ *The browser surfaces*). Quick start:

```sh
(cd ~/dev/DreggNet && cargo build -p dreggnet-attach -p dreggnet-console \
     -p dreggnet-status -p dreggnet-landing)   # server binaries
(cd ../../../extension && node build.mjs)        # rebuild the extension dist/ (gitignored)
npm install                                     # capture deps (reuses cached chromium)
./run-capture.sh                                # drive every surface -> out/*.webm
./stitch.sh                                     # composite -> ../film-{browser,full}.mp4
```

| file | role |
|------|------|
| `run-capture.sh`        | launches the real DreggNet binaries + a stub node/webauth, runs the three capture scripts |
| `stitch.sh`             | normalizes clips + cards and concats the two films (ffmpeg + ImageMagick) |
| `capture-cockpit.mjs`   | the STAR: `dreggnet-attach` — goal → stream → verify → tamper → tiny-budget bite |
| `capture-extension.mjs` | the cipherclerk MV3 extension — onboard → login (challenge/sign) → powerbox grant |
| `capture-panes.mjs`     | `dreggnet-console` / `-status` / `-landing` |
| `mock-node.mjs`         | hermetic stub of the node + the cap-auth webauth (REAL Ed25519 verify of the login signature) |
| `lib.mjs`               | the caption bar + paced helpers (pure overlay; no surface behaviour faked) |

**Honesty:** every frame is badged **RECORDED LOCALLY**. The cockpit receipt-chain
**verify + tamper** and the extension **login signature** are real; the cockpit
tool-verdicts are demo-labelled (canned), the login runs against a local
stub-webauth, and console/status/landing render over local fixtures — no
live-cloud claim. Media + `node_modules/` are gitignored.
