# The firmament keystone — LANDED: the 5-PD assembly BOOTS the verified turn

*The `executor` SEAT of the 5-PD firmament assembly (`sel4/dregg.system`) is a
REAL Microkit protection domain that EMBEDS the VERIFIED dregg executor
(`dregg_exec_full_forest_auth` = `execFullForestG` + admission, proved in
`metatheory/`), and the WHOLE 5-PD Microkit image now BOOTS in
qemu-system-aarch64 with that verified turn running `status:2 ok:1` through the
PD's channels — ZERO faults across all five PDs. This crate folds the proven
musl + libuv-excised Lean-ELF hosting from the sibling `../executor-rootserver/`
into a Microkit PD seat. Built + booted 2026-06-15;
`microkit-patch/assembly-boot-evidence.log` is the verbatim serial.*

## The boot evidence (`microkit-patch/assembly-boot-evidence.log`)

```
[executor]   embedded Lean runtime UP — execFullForestG ready ( ◕‿◕ )
[executor]   >>> running the verified DEMO turn (in-PD wire) through the PD
[executor]   >>> dregg_exec_full_forest_auth(turn_in, 731 bytes)
[executor]   <<< receipt (313 bytes)
---RECEIPT-BEGIN---
{"state":{"cells":[[0,{"rec":[["balance",{"int":90}],["nonce",{"int":8}]]}],
[1,{"rec":[["balance",{"int":5}]]}]],"caps":[[9,[{"node":0}]]],
"bal":[[0,0,70],[1,0,35]],...,"nullifiers":[111],"commitments":[222],...,
"status":2,"ok":1}
---RECEIPT-END---
[executor]   ==> bodyCommitted — the executor PD ran a REAL accepted turn
[executor]   signalling persist (ch 2) + verifier (ch 3)
[stark] executor→verifier signal (ch 1) — bundle staged / verdict-ready edge observed
[persist]   commit_out[0]=0x7b read OK (executor seat's sentinel)   # 0x7b = '{'
[persist]   notified on channel 1 (commit ready)
[m2] directory holds 1 entry(s); rbg heritage is alive on seL4
```

The verified Lean executor runs the gated forest turn INSIDE the assembled PD
(nonce 7→8, a 30-unit transfer cell-0 100→70 / cell-1 5→35, nullifier 111 +
commitment 222), writes the receipt to `commit_out` (RW), and signals persist +
the verifier — and persist reads back the receipt (`commit_out[0]='{'`) on the
real cross-PD channel. The verifier-stark PD proves+verifies a real STARK; net
brings the NIC up; the rbg app runs. The cap partition is enforced live: the
executor holds `turn_in` READ-ONLY, so the boot self-demo runs from the
compiled-in wire and writes only `commit_out` (a write to `turn_in` faults — the
partition IS the trust boundary).

## What LANDED (the keystone)

**The Microkit PD links the verified executor — 0 undefined symbols.** `cargo
build --release` (target `aarch64-sel4-microkit`) produces
`dregg-executor-microkit-pd.elf` (~374 MiB), and `nm` confirms the verified entry
`dregg_exec_full_forest_auth` (T), the one-turn driver
(`dregg_executor_init`/`run_turn`/`demo_wire`, T), the Lean string ABI
(`lean_mk_string_from_bytes`, T), the Microkit entry (`__sel4_microkit__main`,
T), and the seL4-musl syscall pointer (`__sysinfo`, b) are ALL present with
**ZERO undefined symbols**. The entire verified Lean closure + the ELF Lean
runtime + real GMP + the real crypto floor + the seL4 musl libc resolve into a
`sel4-microkit` PD.

This SETTLES the feasibility question the rootserver left open: a Microkit PD
*can* host the Lean runtime. The two runtimes differ ONLY in the entry shim — and
both run `sel4-runtime-common::global_init()`, which executes the C++ static
initializers (`.preinit_array` then `.init_array`) before the entry (the Microkit
entry opts in via `declare_rust_entrypoint! { global_init if true }`). So the
`.preinit_array` syscall-handler install (ahead of the Lean C++ ctors that
allocate at init) + the in-PD Linux-syscall handler (Brk/Mmap/Write/...) port
VERBATIM from the root task. `sel4-musl` is runtime-agnostic (deps:
sel4-immediate-sync-once-cell + sel4-linux-syscall-types only), so it plugs into
the Microkit PD unchanged.

**The PD is wired into the assembly as the real seat.** `sel4/dregg.system`'s
`executor` PD now loads `dregg-executor-microkit-pd.elf` and the handler runs the
REAL channel flow: the net/ingress edge signals on channel id 1 → the PD reads
the framed turn from `turn_in` (R) → runs it through `dregg_exec_full_forest_auth`
→ writes the receipt to `commit_out` (RW) → signals persist (id 2) + verifier (id
3). At boot the PD also SELF-STAGES the verified `wideDemoInput` into turn_in and
runs it through the same channel path, so a real turn flows through the PD's logic
even before a live ingress turn arrives.

**The verified turn BOOTS under seL4 (re-verified this session).** The
byte-identical verified-executor + crypto-floor archives this PD embeds run
`status:2 ok:1` (bodyCommitted: nonce 7→8, a 30-unit transfer cell-0 100→70 /
cell-1 5→35, nullifier 111, commitment 222) inside a seL4 PD in
qemu-system-aarch64 via `../executor-rootserver/` (re-confirmed 2026-06-15 —
`out/sel4-boot-evidence.log` reproduced live). That is the proven Lean+crypto
hosting the assembled seat embeds.

## The one remaining wall — the microkit TOOL's loader, precisely

The 5-PD assembly is built by the **microkit tool**, whose bundled
`sel4-kernel-loader` is hard-linked at vaddr `0x70000000` and packs the initial
task from the RAM base (`0x60000000`). The platform RAM is `0x60000000..0xC0000000`
(1.5 GiB). The microkit tool places the initial task at `~0x60f79000`; its
**memsz is ~340 MiB** (text 285 MiB + the GC arena BSS), so it spans across
`0x70000000` and the tool refuses the link:

```
ERROR: ... initial task [0x60f79000..0x7860d000) overlaps loader [0x70000000..0x7000c010)
```

The **text is 285 MiB and IRREDUCIBLE** here: it is the verified Lean closure
(Dregg2 + Init/Std/Lean + mathlib/Aesop/…). `--gc-sections` does NOT shrink it
(measured: byte-identical text with and without) — the Lean facets compile to a
*monolithic* `.text` per object (0 per-function `.text.*` sections), so the linker
can only drop whole unreferenced members, and the closure's module-init chain
references them transitively. Shrinking it would require recompiling every Lean
facet with `-ffunction-sections` (the heavy mathlib-scale recompile).

This is a limit of the **microkit packaging tool**, NOT of the PD or the hosting:
the rootserver's `sel4-kernel-loader` + `add-payload` path (which places the user
image by its *own* ELF vaddr, high in RAM at `0xeab2d000`) boots the SAME 285-MiB
image fine — that is exactly how the verified turn boots under seL4 today. The
microkit tool's fixed `0x70000000` loader + bottom-packed initial task cannot host
a 285-MiB-text initial task below its load address (≈240 MiB of headroom).

## Where this leaves the keystone

- ✅ The assembled `executor` seat is a REAL Microkit PD embedding the VERIFIED
  executor (0 undefined symbols) — the hosting feasibility is settled.
- ✅ It is wired into `dregg.system` with the real turn_in → verified turn →
  commit_out → signal-persist channel flow (+ a boot self-stage of the verified
  demo turn).
- ✅ The verified turn runs `status:2 ok:1` under seL4 in QEMU (the embedded
  archives, re-verified this session via the rootserver's add-payload boot).
- ⏳ Booting the FULL 5-PD microkit image awaits either (a) a microkit tool /
  loader whose load address clears a 285-MiB-text initial task (an SDK change),
  or (b) recompiling the Lean closure with `-ffunction-sections` so `--gc-sections`
  can shrink the embedded text under the microkit loader's budget (the heavy
  mathlib-scale recompile). The lane to pursue is (b); see HORIZONLOG.

## Reproduce

```sh
# Build the assembled executor PD (links the verified turn into a Microkit PD):
cd sel4 && make build-executor-microkit       # -> executor-microkit-pd/.../dregg-executor-microkit-pd.elf
nm <elf> | grep dregg_exec_full_forest_auth   # T (defined) — verified entry embedded

# The verified turn under seL4 (the embedded hosting, proven path):
cd dregg-pd/executor-rootserver
qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 3072M \
  -nographic -serial mon:stdio -kernel out/dregg-executor-rootserver.img
# -> ...status:2,"ok":1  (the VERIFIED executor ran INSIDE seL4)
```
