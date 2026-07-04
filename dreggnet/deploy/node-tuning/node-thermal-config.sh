#!/usr/bin/env bash
# node-a steady-state thermal/CPU config. Idempotent; logs each setting.
# Applied at boot by node-thermal-config.service.
set -u

FAN_LEVEL=3
MAX_FREQ=3300000
GOVERNOR=powersave
EPP=balance_power

log() { echo "node-thermal-config: $*"; }

# --- Fan: quiet fixed level (requires thinkpad_acpi fan_control=1) ---
if [ -w /proc/acpi/ibm/fan ]; then
    if echo "level ${FAN_LEVEL}" > /proc/acpi/ibm/fan 2>/dev/null; then
        log "fan -> level ${FAN_LEVEL}"
    else
        log "WARN: failed to set fan level ${FAN_LEVEL} (fan_control not enabled?)"
    fi
else
    log "WARN: /proc/acpi/ibm/fan not writable (thinkpad_acpi loaded with fan_control=1?)"
fi

# --- CPU boost ON (dynamic, but capped via scaling_max_freq) ---
if [ -w /sys/devices/system/cpu/cpufreq/boost ]; then
    echo 1 > /sys/devices/system/cpu/cpufreq/boost && log "boost -> 1"
else
    log "WARN: cpufreq/boost not writable"
fi

# --- Per-core: max freq cap + governor + EPP ---
applied=0
for d in /sys/devices/system/cpu/cpu[0-9]*/cpufreq; do
    [ -d "$d" ] || continue
    [ -w "$d/scaling_max_freq" ] && echo "$MAX_FREQ" > "$d/scaling_max_freq"
    [ -w "$d/scaling_governor" ] && echo "$GOVERNOR" > "$d/scaling_governor"
    [ -w "$d/energy_performance_preference" ] && echo "$EPP" > "$d/energy_performance_preference"
    applied=$((applied+1))
done
log "applied max=${MAX_FREQ} governor=${GOVERNOR} epp=${EPP} to ${applied} cores"

exit 0
