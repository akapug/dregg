# node thermal exporter

A tiny dependency-free Prometheus sidecar that runs ON the compute node (node-a) and serves the
box's thermal/power state over the headscale overlay, so the edge Prometheus can
scrape it (node-a has no node-exporter). The **Compute** dashboard's thermal
panels read these series.

## Series

| metric | meaning |
| --- | --- |
| `node_a_cpu_temp_celsius` | package/CPU temperature (°C) |
| `node_a_cpu_freq_mhz` | mean current core frequency (MHz) |
| `node_a_fan_level` | thinkpad_acpi EC fan level (0..7) |
| `node_a_load1` | 1-minute load average |
| `node_a_thermal_up` | 1 if temp or load read this scrape |

Values come from LIVE sysfs/procfs first (`/sys/class/hwmon`,
`/sys/devices/system/cpu/*/cpufreq`, `/proc/acpi/ibm/fan`, `/proc/loadavg`); the
last row of `/var/log/node-thermal.csv` (the sampler in
`runbooks/HARDWARE-NODE.md`) is a per-metric fallback.

## Deploy (on the compute node (node-a))

```sh
# from a checkout at /opt/dreggnet
sudo cp deploy/observability/node-thermal-exporter/node-thermal-exporter.service \
        /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable --now node-thermal-exporter.service
# verify locally:
curl -s localhost:8022/metrics | grep node_
```

Binds `0.0.0.0:8022`; reachable from the edge as `100.64.0.2:8022` over the
overlay. The Prometheus `node-a-thermal` scrape job targets that address.

## Verify the scrape (from the edge)

```sh
# from the edge box, over the overlay:
curl -s http://100.64.0.2:8022/metrics | grep node_a_cpu_temp_celsius
# in Prometheus: target `node-a-thermal` should be UP and
# node_a_cpu_temp_celsius should have a fresh sample.
```
