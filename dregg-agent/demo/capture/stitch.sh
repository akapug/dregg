#!/usr/bin/env bash
# Composite the captured browser clips (out/*.webm from ./run-capture.sh) into:
#   ../film-browser.mp4  — the companion browser film (~1:05): cockpit verify+tamper
#                          -> extension login+powerbox -> console/status/landing.
#   ../film-full.mp4      — the single richer ~2:00 cut: the terminal agent film
#                          (2x recap) THEN the full browser arc.
# Both are gitignored; regenerate any time. Nothing is a live-cloud claim.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT="$HERE/out"; SEG="$OUT/seg"; DEMO="$(cd "$HERE/.." && pwd)"
mkdir -p "$SEG"
FONT="/System/Library/Fonts/Supplemental/Arial.ttf"
[ -f "$FONT" ] || FONT="/System/Library/Fonts/Helvetica.ttc"
BG=0x0e0e1a; W=1280; H=800; FPS=30
X264=(-c:v libx264 -preset veryfast -crf 20 -pix_fmt yuv420p -video_track_timescale 30000)

norm() { # src dst  — scale-to-fit + pad to WxH, uniform codec params
  ffmpeg -y -loglevel error -i "$1" -vf \
    "scale=$W:$H:force_original_aspect_ratio=decrease,pad=$W:$H:(ow-iw)/2:(oh-ih)/2:color=$BG,setsar=1,fps=$FPS,format=yuv420p" \
    -an "${X264[@]}" "$2"
}
speed() { # src dst factor — speed up (for the terminal recap) + normalize
  ffmpeg -y -loglevel error -i "$1" -vf \
    "setpts=PTS/$3,scale=$W:$H:force_original_aspect_ratio=decrease,pad=$W:$H:(ow-iw)/2:(oh-ih)/2:color=$BG,setsar=1,fps=$FPS,format=yuv420p" \
    -an "${X264[@]}" "$2"
}
card() { # title subtitle seconds dst  (ImageMagick renders the still; ffmpeg loops it)
  local png="${4%.mp4}.png"
  magick -size ${W}x${H} "xc:#0e0e1a" -gravity center -font "$FONT" \
    -pointsize 48 -fill white   -annotate +0-64 "$1" \
    -pointsize 25 -fill "#9a9ac0" -annotate +0+16 "$2" \
    -gravity south -pointsize 16 -fill "#ffcf6b" -annotate +0+42 "RECORDED LOCALLY" \
    "$png"
  ffmpeg -y -loglevel error -loop 1 -t "$3" -i "$png" -vf \
    "scale=$W:$H,setsar=1,fps=$FPS,format=yuv420p" -an "${X264[@]}" "$4"
}
concat() { # dst seg...   (identical params -> stream copy)
  local dst="$1"; shift
  : > "$SEG/list.txt"
  for f in "$@"; do echo "file '$f'" >> "$SEG/list.txt"; done
  ffmpeg -y -loglevel error -f concat -safe 0 -i "$SEG/list.txt" -c copy "$dst"
}

echo "── normalizing clips ───────────────────────────────────────────────────"
for c in cockpit extension console status landing; do
  [ -f "$OUT/$c.webm" ] || { echo "missing $OUT/$c.webm — run ./run-capture.sh first"; exit 1; }
  norm "$OUT/$c.webm" "$SEG/$c.mp4"
done

echo "── cards ───────────────────────────────────────────────────────────────"
card "The web side of the product"      "DreggNet in the browser  -  cockpit, extension, panes"      3 "$SEG/title.mp4"
card "The BROWSER surfaces"             "the same verify-dont-trust, now visceral in the browser"    2 "$SEG/divider.mp4"
card "verify-dont-trust, all the way down" "Hermes  -  NVIDIA  -  Stripe  -  DreggNet"               4 "$SEG/close.mp4"

echo "── film-browser.mp4 (companion) ────────────────────────────────────────"
concat "$DEMO/film-browser.mp4" \
  "$SEG/title.mp4" "$SEG/cockpit.mp4" "$SEG/extension.mp4" \
  "$SEG/console.mp4" "$SEG/status.mp4" "$SEG/landing.mp4" "$SEG/close.mp4"

echo "── film-full.mp4 (terminal recap 2x + browser) ─────────────────────────"
if [ -f "$DEMO/film.mp4" ]; then
  speed "$DEMO/film.mp4" "$SEG/terminal2x.mp4" 2.0
  concat "$DEMO/film-full.mp4" \
    "$SEG/terminal2x.mp4" "$SEG/divider.mp4" "$SEG/cockpit.mp4" "$SEG/extension.mp4" \
    "$SEG/console.mp4" "$SEG/status.mp4" "$SEG/landing.mp4" "$SEG/close.mp4"
else
  echo "  (no ../film.mp4 terminal film present — skipping film-full; render it via demo/film.sh)"
fi

echo "── done ────────────────────────────────────────────────────────────────"
for f in film-browser film-full; do
  [ -f "$DEMO/$f.mp4" ] && printf "%-18s %s  %ss\n" "$f.mp4" \
    "$(du -h "$DEMO/$f.mp4" | cut -f1)" \
    "$(ffprobe -v error -show_entries format=duration -of default=nk=1:nw=1 "$DEMO/$f.mp4" | cut -d. -f1)"
done
