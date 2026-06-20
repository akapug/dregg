#!/usr/bin/env bash
# win-guest-sync.sh — push Mac-side repo edits into the Parallels Windows guest.
#
# The deos Windows port is built INSIDE a Parallels Windows 11 (ARM64) guest, but
# all editing happens on the Mac. Parallels Tools' shared-folder FS is unreliable
# on this guest (prl_fs not running), so the repo lives at a LOCAL guest path
# (C:\deos) seeded from a `git archive` and refreshed by this script over a tiny
# range-capable HTTP server on the host's Parallels subnet IP.
#
# Usage:
#   scripts/win-guest-sync.sh                 # sync the whole tracked tree (HEAD + working edits)
#   scripts/win-guest-sync.sh path/to/file …  # sync specific files (fast; for iterative edits)
#
# Env:
#   VM_UUID   Parallels VM uuid           (default: the deos guest)
#   HOST_IP   host IP on the guest subnet (default: 10.211.55.2)
#   PORT      host HTTP port              (default: 8731)
#   GUEST_DIR guest repo root             (default: C:\deos)
set -euo pipefail

VM_UUID="${VM_UUID:-{6fe33fde-550b-45a5-bddf-1fab30ccf2d1}}"
HOST_IP="${HOST_IP:-10.211.55.2}"
PORT="${PORT:-8731}"
GUEST_DIR="${GUEST_DIR:-C:\\deos}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SERVE_DIR="$(mktemp -d)"
trap 'rm -rf "$SERVE_DIR"' EXIT

q() { prlctl exec "$VM_UUID" cmd /c "$1"; }

# Range-capable, thread-safe single-file HTTP server (Python http.server truncates
# long transfers through the prlctl exec channel; a 206-honouring server lets curl
# -C - resume to completion).
start_server() {
  python3 - "$SERVE_DIR" "$PORT" >/tmp/win-guest-sync-http.log 2>&1 &
  echo $!
} <<'PY'
import http.server, socketserver, os, re, sys, urllib.parse
ROOT, PORT = sys.argv[1], int(sys.argv[2])
class H(http.server.BaseHTTPRequestHandler):
    def do_HEAD(self): self._s(True)
    def do_GET(self):  self._s(False)
    def _s(self, head):
        p = os.path.join(ROOT, os.path.basename(urllib.parse.unquote(self.path.lstrip('/'))))
        if not os.path.isfile(p):
            self.send_response(404); self.end_headers(); return
        sz = os.path.getsize(p); rng = self.headers.get('Range'); a, b = 0, sz-1
        if rng:
            m = re.match(r'bytes=(\d+)-(\d*)', rng)
            if m:
                a = int(m.group(1))
                if m.group(2): b = int(m.group(2))
        n = b-a+1
        self.send_response(206 if rng else 200)
        self.send_header('Accept-Ranges', 'bytes')
        self.send_header('Content-Length', str(n))
        if rng: self.send_header('Content-Range', f'bytes {a}-{b}/{sz}')
        self.end_headers()
        if head: return
        with open(p, 'rb') as f:
            f.seek(a); rem = n
            while rem > 0:
                c = f.read(min(65536, rem))
                if not c: break
                try: self.wfile.write(c)
                except BrokenPipeError: return
                rem -= len(c)
    def log_message(self, *a): pass
class S(socketserver.ThreadingTCPServer):
    allow_reuse_address = True; daemon_threads = True
S(('0.0.0.0', PORT), H).serve_forever()
PY

# Fetch a host file into the guest, resuming until the byte count matches.
pull() { # $1 = archive basename, $2 = expected size
  q "del ${GUEST_DIR}\\$1 2>nul& for /L %i in (1,1,20) do @(curl.exe -s -C - -o ${GUEST_DIR}\\$1 http://${HOST_IP}:${PORT}/$1 & for %A in (${GUEST_DIR}\\$1) do @if %~zA GEQ $2 exit /b 0)"
}

cd "$REPO_ROOT"
q "if not exist ${GUEST_DIR} mkdir ${GUEST_DIR}" >/dev/null 2>&1 || true

SRV=$(start_server); sleep 1
trap 'kill "$SRV" 2>/dev/null; rm -rf "$SERVE_DIR"' EXIT

if [ "$#" -eq 0 ]; then
  echo "[win-sync] full tree → ${GUEST_DIR}"
  # tracked files + working-tree edits (ls-files honours .gitignore; -m/-o adds edits/new)
  tar -czf "$SERVE_DIR/deos-sync.tar.gz" $(git ls-files; git ls-files -o --exclude-standard) 2>/dev/null
  SZ=$(stat -f%z "$SERVE_DIR/deos-sync.tar.gz")
  pull deos-sync.tar.gz "$SZ"
  q "tar -xzf ${GUEST_DIR}\\deos-sync.tar.gz -C ${GUEST_DIR}"
  echo "[win-sync] done ($SZ bytes)"
else
  for f in "$@"; do
    base="$(echo "$f" | tr '/' '_')"
    cp "$f" "$SERVE_DIR/$base"
    SZ=$(stat -f%z "$SERVE_DIR/$base")
    pull "$base" "$SZ"
    # place it at the right guest path
    gp="${GUEST_DIR}\\$(echo "$f" | tr '/' '\\')"
    gd="$(dirname "$gp")"
    q "if not exist \"$gd\" mkdir \"$gd\" & copy /Y ${GUEST_DIR}\\$base \"$gp\" >nul"
    echo "[win-sync] $f → $gp ($SZ bytes)"
  done
fi
