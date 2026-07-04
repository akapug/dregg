# HARDWARE-NODE — the build/compute box's thermal + power config

node-a is the engine room: the reference build box (it has the Lean toolchain
and builds the node + bot images natively) and the compute backend
(`:8021/fulfill` + STARK proving). This runbook is the **hardware** layer — the
fan, the CPU power config, the OOM-killer, and the thermal logger — the stuff that
keeps heavy builds from cooking the laptop, all of which we set up by hand and
**none of which survives a reboot yet** (the standing TODO).

The box is a multi-core AMD laptop running Ubuntu.

> **Doc-drift note (reconcile when next on the box):** the compute-backend docs
> (`deploy/COMPUTE-BACKEND.md`, `deploy/ARCHITECTURE-COMPUTE-BACKEND.md`) cite
> node-a as a multi-core box. The fan/pstate/earlyoom facts below assume a
> laptop-class chassis; adapt for other hardware.

## The fan (run it hard during builds)

The laptop's EC fan is driven through `thinkpad_acpi`. Manual control is **off
by default** and must be enabled:

```sh
# enable manual fan control (default is firmware-managed):
sudo modprobe thinkpad_acpi fan_control=1
# or, if already loaded:  echo 1 | sudo tee /sys/module/thinkpad_acpi/parameters/fan_control  (read-only post-load — reload the module)

# the control + status file (levels 0-7, plus "auto"/"full-speed"):
cat /proc/acpi/ibm/fan                       # status / current level / RPM
echo 'level 5' | sudo tee /proc/acpi/ibm/fan # we run LEVEL 5 during heavy builds
echo 'level auto' | sudo tee /proc/acpi/ibm/fan
```

We run **level 5** for sustained build/prove load — high airflow without
full-speed scream. **Keep the intake clean** — a hair/dust-clogged intake on this
chassis costs real thermal headroom (clean it when temps creep at a given level).

## The CPU (amd-pstate-epp — boost on, capped, powersave)

The Ryzen runs the **amd-pstate-epp** driver. The config we run trades a little
peak clock for a much flatter thermal curve under sustained load:

```sh
# confirm the driver:
cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_driver      # amd-pstate-epp

# boost ON (turbo allowed, but bounded by the freq cap below):
cat /sys/devices/system/cpu/cpufreq/boost                     # 1
echo 1 | sudo tee /sys/devices/system/cpu/cpufreq/boost

# cap the max frequency (~3.3 GHz) so sustained builds don't thermal-spike:
for c in /sys/devices/system/cpu/cpu*/cpufreq/scaling_max_freq; do
  echo 3300000 | sudo tee "$c"               # kHz
done

# governor: powersave (with epp the "powersave" governor is the normal dynamic
# one — it scales on demand; it is NOT a fixed-low-clock mode):
for c in /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor; do
  echo powersave | sudo tee "$c"
done
```

The intent: **dynamic, not full-boost** — let cores ramp on demand but ceiling
them so a `cargo`/mathlib spike doesn't run the package straight into the thermal
limit. This is what makes the `taskset -c 0-5 -j6` bounded build (NODE-OPS.md) sit
in a stable band instead of thrashing.

## earlyoom (why heavy builds die)

`earlyoom` runs and is configured to **prefer killing the build toolchain** when
memory gets tight:

```
earlyoom --prefer '(^|/)(cargo|cc|cc1|cc1plus|ld|rustc|lake)$'
```

So an unbounded `cargo build -j$(nproc)` on the Lean/mathlib closure spikes memory
and earlyoom **reaps the compiler mid-build** — that is the expected behavior, not
a bug. The consequence to remember: if earlyoom kills a build that is rebuilding a
running **node**, the SIGKILL can be the one that triggers the STORE-INTEGRITY
recovery event (NODE-OPS.md). **Mitigation: always bound heavy builds** —
`taskset -c 0-5 cargo build -j6 …` keeps peak memory under the ceiling.

```sh
systemctl status earlyoom            # confirm it's running + the --prefer regex
journalctl -u earlyoom | tail        # what it has reaped
```

## The thermal logger

A small sampler records temps so we can see what a build does to the chassis over
time:

- **Script:** `/usr/local/bin/node-thermal-log.sh` — samples package/core
  temps (and fan level) on an interval and appends a CSV row.
- **Unit:** `node-thermal.service` — runs the sampler.
- **Output:** `/var/log/node-thermal.csv`.

```sh
systemctl status node-thermal.service
tail -f /var/log/node-thermal.csv
sensors                              # the raw read the sampler wraps
```

## ✅ This now persists a reboot (the mechanism)

The settings above used to be runtime-only sysfs writes that reverted on every
reboot — the box silently de-tuned (fan to firmware-auto, no freq cap, governor
reset, `thinkpad_acpi` without `fan_control=1`). That is now **fixed and durable
on the box**, and the artifacts are **version-controlled in
`deploy/node-tuning/`** so a re-provision keeps the tuning:

1. **`/etc/modprobe.d/thinkpad_acpi.conf`** (= `deploy/node-tuning/thinkpad_acpi.conf`)
   — `options thinkpad_acpi fan_control=1`, so the module loads with manual fan
   control enabled on every boot (the *level* is then set in step 2).
2. **`node-thermal-config.service`** (= `deploy/node-tuning/node-thermal-config.service`)
   — a `Type=oneshot`, `RemainAfterExit=yes`, `WantedBy=multi-user.target` unit
   that runs `/usr/local/sbin/node-thermal-config.sh`
   (= `deploy/node-tuning/node-thermal-config.sh`) on boot. The script is
   **idempotent** and applies: fan **level 3**, **boost 1**, **`scaling_max_freq`
   3300000 kHz**, **governor `powersave`**, **EPP `balance_power`** across all
   cores, logging each setting to the journal.

> Fan **level 3** is the persisted *steady-state* (quiet, safe-airflow). Bump to
> **level 5** by hand for sustained heavy build/prove load (it reverts to 3 on the
> next boot/oneshot run).

**Install on a fresh box (from the repo):**

```sh
sudo install -m644 deploy/node-tuning/thinkpad_acpi.conf /etc/modprobe.d/thinkpad_acpi.conf
sudo install -m755 deploy/node-tuning/node-thermal-config.sh /usr/local/sbin/node-thermal-config.sh
sudo install -m644 deploy/node-tuning/node-thermal-config.service /etc/systemd/system/node-thermal-config.service
sudo systemctl daemon-reload && sudo systemctl enable --now node-thermal-config.service
```

**Verify the persistence (without rebooting):**

```sh
systemctl is-enabled node-thermal-config.service       # enabled → fires on boot
systemctl status  node-thermal-config.service          # active (exited), status=0
cat /sys/module/thinkpad_acpi/parameters/fan_control       # Y
awk '/level:/{print $2}' /proc/acpi/ibm/fan                # 3
cat /sys/devices/system/cpu/cpufreq/boost                  # 1
cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor  # powersave
cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_max_freq  # 3300000
sudo /usr/local/sbin/node-thermal-config.sh            # idempotent re-apply, exit 0
```

The unit is enabled (symlinked into `multi-user.target.wants`) and has run
cleanly on a real boot, so the tuning survives a reboot. The thermal-logger
`.service` survives independently (it always did); what changed is that the
*settings it observes* now also survive.

## See also

- NODE-OPS.md — the bounded build, the warm-worktree, why a reaped build can
  break a node.
- `deploy/COMPUTE-BACKEND.md` — the compute backend + the systemd agent.
</content>
