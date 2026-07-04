#!/usr/bin/env bash
# Stitch the portal.dregg.studio stills into a captioned clip (static holds +
# crossfades + lower-third captions). Sources are REAL screenshots of the served
# portal, captured by capture.mjs (see demo/surfaces/SURFACES.md).
#
# HONESTY: the in-tab recursive-STARK verifier is real wasm; its proof-GENERATION
# step exceeds this sandbox's headless-chromium wasm limit, so the shots show the
# portal's trust-first UI + the verifier engaging, not a green "Verified" end-
# state. It completes in a full desktop browser. Output: demo/surfaces/out/portal.mp4
set -euo pipefail
cd "$(dirname "$0")/../.."
S=demo/surfaces/out/shots
OUT=demo/surfaces/out
FONT=/System/Library/Fonts/Menlo.ttc
W=1920; H=1200; FPS=30
FFMPEG="${FFMPEG:-$(for f in /opt/homebrew/opt/ffmpeg@6/bin/ffmpeg ffmpeg; do "$f" -hide_banner -filters 2>/dev/null | grep -q drawtext && { echo "$f"; break; }; done)}"
[ -n "$FFMPEG" ] || { echo "need an ffmpeg with drawtext (brew install ffmpeg@6)"; exit 1; }
echo "using ffmpeg: $FFMPEG"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT

prep() { magick "$1" -resize ${W}x${H}^ -gravity center -extent ${W}x${H} "$2"; }
seg() {
  local src="$1" secs="$2" out="$3" title="$4" sub="$5"
  "$FFMPEG" -y -loglevel error -loop 1 -t "$secs" -i "$src" -filter_complex "\
    [0:v]drawbox=x=0:y=ih-150:w=iw:h=150:color=black@0.62:t=fill[bar];\
    [bar]drawtext=fontfile=${FONT}:text='${title}':fontcolor=white:fontsize=36:x=60:y=h-116,\
         drawtext=fontfile=${FONT}:text='${sub}':fontcolor=0x8fe3b0:fontsize=23:x=60:y=h-62[v]" \
    -map "[v]" -r ${FPS} -c:v libx264 -pix_fmt yuv420p -crf 20 "$out"
}

echo "prescale…"
prep "$S/01-hero.png"      "$tmp/1.png"
prep "$S/02-network.png"   "$tmp/2.png"
prep "$S/03-cell-fold.png" "$tmp/3.png"

echo "segments…"
seg "$tmp/1.png" 6 "$tmp/1.mp4" \
  "portal.dregg.studio - verify it yourself" \
  "a recursive-STARK light client, in this browser tab - trust no server"
seg "$tmp/2.png" 6 "$tmp/2.mp4" \
  "the living network - sovereign cells, read live from the edge" \
  "each cell carries a proof of its WHOLE committed history"
seg "$tmp/3.png" 7 "$tmp/3.mp4" \
  "open a cell -> its whole history folds to ONE root" \
  "the field table is the SERVER-CLAIMED state; the light client binds it (real wasm)"

echo "concat with crossfades…"
XF=0.6
"$FFMPEG" -y -loglevel error \
  -i "$tmp/1.mp4" -i "$tmp/2.mp4" -i "$tmp/3.mp4" \
  -filter_complex "\
    [0:v][1:v]xfade=transition=fade:duration=${XF}:offset=$(echo "6-${XF}"|bc)[a];\
    [a][2:v]xfade=transition=fade:duration=${XF}:offset=$(echo "6+6-2*${XF}"|bc)[v]" \
  -map "[v]" -r ${FPS} -c:v libx264 -preset slow -crf 24 -pix_fmt yuv420p -movflags +faststart "$OUT/portal.mp4"

echo "wrote $OUT/portal.mp4"
ffprobe -v error -show_entries format=duration -show_entries stream=width,height -of default=noprint_wrappers=1 "$OUT/portal.mp4"
