#!/usr/bin/env python3
"""node thermal exporter — a tiny, dependency-free Prometheus sidecar.

Runs ON the compute node and serves `/metrics` over the headscale overlay so the edge
Prometheus can scrape the box's thermal/power state (it has no node-exporter).
The Compute dashboard's thermal panels read these series.

Source of truth, in order of preference per metric:
  1. LIVE sysfs / procfs reads (the freshest, deterministic source — this runs on
     the box, so the kernel surfaces are right here).
  2. The last row of /var/log/node-thermal.csv (the sampler the HARDWARE-
     NODE runbook documents) — a fallback when a live surface is absent.

Exposes (Prometheus exposition, text/plain):
  node_a_cpu_temp_celsius   — package/CPU temperature (°C)
  node_a_cpu_freq_mhz       — mean current core frequency (MHz)
  node_a_fan_level          — thinkpad_acpi EC fan level (0..7; 7≈"full")
  node_a_load1              — 1-minute load average
  node_a_thermal_up         — 1 if at least temp OR load was read this scrape

No third-party deps (stdlib only) so it runs under the system python3 with a
plain systemd unit. Bind: 0.0.0.0:8022 (the overlay address 100.64.0.2:8022).
"""

import glob
import os
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

CSV_PATH = os.environ.get("NODE_THERMAL_CSV", "/var/log/node-thermal.csv")
BIND_HOST = os.environ.get("NODE_THERMAL_HOST", "0.0.0.0")
BIND_PORT = int(os.environ.get("NODE_THERMAL_PORT", "8022"))

FAN_LEVEL_NAMED = {"auto": 4, "full-speed": 7, "disengaged": 7}


def _read_text(path):
    try:
        with open(path, "r") as f:
            return f.read().strip()
    except OSError:
        return None


def read_cpu_temp_celsius():
    """Package/CPU temp from hwmon. Prefer a coretemp/k10temp 'Package'/'Tctl'
    label; else the max of any *_input under a CPU-ish hwmon. Returns °C float."""
    best = None
    for hwmon in glob.glob("/sys/class/hwmon/hwmon*"):
        name = (_read_text(os.path.join(hwmon, "name")) or "").lower()
        if name not in ("coretemp", "k10temp", "zenpower", "cpu_thermal"):
            continue
        for temp_input in glob.glob(os.path.join(hwmon, "temp*_input")):
            raw = _read_text(temp_input)
            if raw is None:
                continue
            try:
                celsius = int(raw) / 1000.0
            except ValueError:
                continue
            label_path = temp_input.replace("_input", "_label")
            label = (_read_text(label_path) or "").lower()
            if "package" in label or "tctl" in label or "tdie" in label:
                return celsius
            best = celsius if best is None else max(best, celsius)
    # Last resort: the generic thermal zone.
    if best is None:
        raw = _read_text("/sys/class/thermal/thermal_zone0/temp")
        if raw is not None:
            try:
                best = int(raw) / 1000.0
            except ValueError:
                pass
    return best


def read_cpu_freq_mhz():
    """Mean of per-core scaling_cur_freq (kHz) → MHz."""
    vals = []
    for path in glob.glob("/sys/devices/system/cpu/cpu[0-9]*/cpufreq/scaling_cur_freq"):
        raw = _read_text(path)
        if raw is None:
            continue
        try:
            vals.append(int(raw) / 1000.0)  # kHz → MHz
        except ValueError:
            continue
    if not vals:
        return None
    return sum(vals) / len(vals)


def read_fan_level():
    """thinkpad_acpi fan level from /proc/acpi/ibm/fan (the 'level: N' line)."""
    text = _read_text("/proc/acpi/ibm/fan")
    if text is None:
        return None
    for line in text.splitlines():
        if line.lower().startswith("level:"):
            val = line.split(":", 1)[1].strip().lower()
            if val.isdigit():
                return float(val)
            return float(FAN_LEVEL_NAMED.get(val, "nan")) if val in FAN_LEVEL_NAMED else None
    return None


def read_load1():
    text = _read_text("/proc/loadavg")
    if text is None:
        return None
    try:
        return float(text.split()[0])
    except (ValueError, IndexError):
        return None


def read_csv_fallback():
    """Map the last CSV data row to {temp,freq,fan,load} by header name.

    The sampler's exact columns are box-side; we match tolerantly so a format
    tweak doesn't break the exporter. Returns a dict of whatever it could map.
    """
    out = {}
    try:
        with open(CSV_PATH, "r") as f:
            lines = [ln for ln in f.read().splitlines() if ln.strip()]
    except OSError:
        return out
    if len(lines) < 2:
        return out
    header = [h.strip().lower() for h in lines[0].split(",")]
    last = [c.strip() for c in lines[-1].split(",")]
    for col, raw in zip(header, last):
        try:
            num = float(raw)
        except ValueError:
            continue
        if "temp" in col and "temp" not in out:
            out["temp"] = num
        elif "freq" in col and "freq" not in out:
            out["freq"] = num
        elif "fan" in col and "fan" not in out:
            out["fan"] = num
        elif "load" in col and "load" not in out:
            out["load"] = num
    return out


def collect():
    temp = read_cpu_temp_celsius()
    freq = read_cpu_freq_mhz()
    fan = read_fan_level()
    load1 = read_load1()

    csv = read_csv_fallback()
    if temp is None:
        temp = csv.get("temp")
    if freq is None:
        freq = csv.get("freq")
    if fan is None:
        fan = csv.get("fan")
    if load1 is None:
        load1 = csv.get("load")
    return temp, freq, fan, load1


def render():
    temp, freq, fan, load1 = collect()
    lines = []

    def emit(name, help_text, mtype, value):
        lines.append(f"# HELP {name} {help_text}")
        lines.append(f"# TYPE {name} {mtype}")
        if value is not None:
            lines.append(f"{name} {value}")

    emit("node_a_cpu_temp_celsius", "the compute node package/CPU temperature (Celsius).", "gauge", temp)
    emit("node_a_cpu_freq_mhz", "the compute node mean current core frequency (MHz).", "gauge", freq)
    emit("node_a_fan_level", "the compute node thinkpad_acpi EC fan level (0..7).", "gauge", fan)
    emit("node_a_load1", "the compute node 1-minute load average.", "gauge", load1)
    up = 1 if (temp is not None or load1 is not None) else 0
    emit("node_a_thermal_up", "1 if the exporter read at least temp or load.", "gauge", up)
    return "\n".join(lines) + "\n"


class Handler(BaseHTTPRequestHandler):
    def do_GET(self):  # noqa: N802
        if self.path.rstrip("/") in ("/metrics", ""):
            body = render().encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/plain; version=0.0.4")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif self.path.rstrip("/") == "/health":
            self.send_response(200)
            self.end_headers()
            self.wfile.write(b"ok\n")
        else:
            self.send_response(404)
            self.end_headers()

    def log_message(self, *_args):  # quiet — journald gets stderr only
        pass


def main():
    server = ThreadingHTTPServer((BIND_HOST, BIND_PORT), Handler)
    print(f"node-thermal-exporter listening on {BIND_HOST}:{BIND_PORT} (csv={CSV_PATH})", file=sys.stderr)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        server.shutdown()


if __name__ == "__main__":
    main()
