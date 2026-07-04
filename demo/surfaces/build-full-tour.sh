#!/usr/bin/env bash
# Stitch the FULL-TOUR companion film: the browser lane's main cut (terminal
# agent + cockpit verify/tamper) followed by the two WONDER surfaces this lane
# owns (portal.dregg.studio + the deos-desktop). Normalizes everything to
# 1280x800 (the browser-lane resolution) and concatenates with short crossfades.
#
# Reads the browser lane's committed media READ-ONLY (never writes it); writes
# only demo/surfaces/out/full-tour.mp4. If a browser film is absent (it is
# gitignored — regenerate via dregg-agent/demo/film.sh + demo/capture), the tour
# degrades to a portal+desktop "surfaces reel" and says so.
set -euo pipefail
cd "$(dirname "$0")/../.."
OUT=demo/surfaces/out
FFMPEG="${FFMPEG:-$(for f in /opt/homebrew/opt/ffmpeg@6/bin/ffmpeg ffmpeg; do "$f" -hide_banner -version >/dev/null 2>&1 && { echo "$f"; break; }; done)}"
W=1280; H=800; FPS=30
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT

# Candidate segments, in tour order. The browser main cut first (if present).
CANDIDATES=(
  "dregg-agent/demo/film-full.mp4"     # terminal agent + cockpit + tamper (browser lane)
  "$OUT/portal.mp4"                    # portal.dregg.studio (this lane)
  "$OUT/desktop.mp4"                   # the deos-desktop (this lane)
)
segs=()
for c in "${CANDIDATES[@]}"; do
  if [ -f "$c" ]; then echo "  + $c"; segs+=("$c"); else echo "  - (absent) $c"; fi
done
[ "${#segs[@]}" -ge 1 ] || { echo "no segments found — build portal.mp4/desktop.mp4 first"; exit 1; }

# Normalize each to WxH/FPS, SAR 1, yuv420p, silent (video-only tour).
i=0; norm=()
for s in "${segs[@]}"; do
  o="$tmp/n$i.mp4"
  "$FFMPEG" -y -loglevel error -i "$s" -an \
    -vf "scale=${W}:${H}:force_original_aspect_ratio=decrease,pad=${W}:${H}:(ow-iw)/2:(oh-ih)/2:color=black,setsar=1,fps=${FPS}" \
    -c:v libx264 -preset medium -crf 22 -pix_fmt yuv420p "$o"
  norm+=("$o"); i=$((i+1))
done

if [ "${#norm[@]}" -eq 1 ]; then
  cp "${norm[0]}" "$OUT/full-tour.mp4"
else
  printf "file '%s'\n" "${norm[@]}" > "$tmp/list.txt"
  # Plain concat (fast, robust). Crossfades across many inputs get fiddly; a hard
  # cut between distinct surfaces reads fine as a "tour".
  "$FFMPEG" -y -loglevel error -f concat -safe 0 -i "$tmp/list.txt" \
    -c:v libx264 -preset medium -crf 22 -pix_fmt yuv420p -movflags +faststart "$OUT/full-tour.mp4"
fi

echo "wrote $OUT/full-tour.mp4"
ffprobe -v error -show_entries format=duration -show_entries stream=width,height -of default=noprint_wrappers=1 "$OUT/full-tour.mp4"
