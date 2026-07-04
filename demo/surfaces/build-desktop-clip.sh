#!/usr/bin/env bash
# Stitch the deos-desktop bakes into a captioned clip (static holds + crossfades +
# lower-third captions). Sources are LIVE gpui offscreen renders produced by:
#   ./target/debug/starbridge-v2 --render-showcase demo/surfaces/out/desktop/showcase
#   ./target/debug/starbridge-v2 --render-desktop  demo/surfaces/out/desktop/desktop
# (see demo/surfaces/SURFACES.md). Output: demo/surfaces/out/desktop.mp4
set -euo pipefail
cd "$(dirname "$0")/../.."
D=demo/surfaces/out/desktop
OUT=demo/surfaces/out
FONT=/System/Library/Fonts/Menlo.ttc
W=1920; H=1200; FPS=30
# This ffmpeg build needs `drawtext` (the default brew ffmpeg omits it).
FFMPEG="${FFMPEG:-$(for f in /opt/homebrew/opt/ffmpeg@6/bin/ffmpeg ffmpeg; do "$f" -hide_banner -filters 2>/dev/null | grep -q drawtext && { echo "$f"; break; }; done)}"
[ -n "$FFMPEG" ] || { echo "need an ffmpeg with drawtext (brew install ffmpeg@6)"; exit 1; }
echo "using ffmpeg: $FFMPEG"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT

# Pre-scale a still to WxH (crop-fill) once — fast, avoids per-frame zoompan cost.
prep() { magick "$1" -resize ${W}x${H}^ -gravity center -extent ${W}x${H} "$2"; }

# One captioned static segment. seg <scaled.png> <seconds> <out> <title> <subtitle>
seg() {
  local src="$1" secs="$2" out="$3" title="$4" sub="$5"
  "$FFMPEG" -y -loglevel error -loop 1 -t "$secs" -i "$src" -filter_complex "\
    [0:v]drawbox=x=0:y=ih-150:w=iw:h=150:color=black@0.62:t=fill[bar];\
    [bar]drawtext=fontfile=${FONT}:text='${title}':fontcolor=white:fontsize=36:x=60:y=h-116,\
         drawtext=fontfile=${FONT}:text='${sub}':fontcolor=0x8fe3b0:fontsize=23:x=60:y=h-62[v]" \
    -map "[v]" -r ${FPS} -c:v libx264 -pix_fmt yuv420p -crf 20 "$out"
}

echo "prescale…"
prep "$D/showcase.png" "$tmp/s1.png"
prep "$D/desktop.png"  "$tmp/s2.png"
prep "$D/desktop.world-board-before.png" "$tmp/s3a.png"
prep "$D/desktop.world-board-after.png"  "$tmp/s3b.png"

echo "segments…"
seg "$tmp/s1.png" 6 "$tmp/1.mp4" \
  "deos - the verified ocap desktop" \
  "one live image of REAL sovereign cells   ·   LIVE gpui render (offscreen, this machine)"
seg "$tmp/s2.png" 8 "$tmp/2.mp4" \
  "moldable inspectors · spotter · world-explorer · Pharo halo" \
  "click a cell -> its state, caps, receipts   ·   malleable from within, over real cells"
seg "$tmp/s3a.png" 5 "$tmp/3a.mp4" \
  "a verified turn re-paints the world" \
  "the confined agent composes a live World Board from scratch"
seg "$tmp/s3b.png" 5 "$tmp/3b.mp4" \
  "Sigma balance = 5000 · conserved every turn" \
  "height 5 -> 8   ·   the executor proved it, invariant under transfers"

echo "concat with crossfades…"
# xfade chain: 1 -> 2 -> 3a -> 3b
XF=0.6
"$FFMPEG" -y -loglevel error \
  -i "$tmp/1.mp4" -i "$tmp/2.mp4" -i "$tmp/3a.mp4" -i "$tmp/3b.mp4" \
  -filter_complex "\
    [0:v][1:v]xfade=transition=fade:duration=${XF}:offset=$(echo "6-${XF}"|bc)[a];\
    [a][2:v]xfade=transition=fade:duration=${XF}:offset=$(echo "6+8-2*${XF}"|bc)[b];\
    [b][3:v]xfade=transition=fade:duration=${XF}:offset=$(echo "6+8+5-3*${XF}"|bc)[v]" \
  -map "[v]" -r ${FPS} -c:v libx264 -preset slow -crf 24 -pix_fmt yuv420p -movflags +faststart "$OUT/desktop.mp4"

echo "wrote $OUT/desktop.mp4"
ffprobe -v error -show_entries format=duration -show_entries stream=width,height -of default=noprint_wrappers=1 "$OUT/desktop.mp4"
