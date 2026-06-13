/* driver.c — the minimal embedded-Lean executor harness.
 *
 * Drives ONE real turn through the VERIFIED executor entry
 * `dregg_exec_full_forest_auth(String) -> String` (Dregg2/Exec/FFI.lean), using
 * the standard embedded-Lean init sequence for COMPILED Lean (NOT lean_initialize,
 * which would pull the elaborator/kernel — see WALL.md). This same sequence is
 * what the seL4 executor-PD's `init` runs; here it is a standalone musl binary so
 * the turn can be validated under qemu-aarch64 before the PD integration.
 *
 * Init contract (Lean FFI): lean_initialize_runtime_module() then the module init
 * initialize_<Module>(builtin=1, io_world) for the executor's top module, then
 * lean_io_mark_end_initialization(). The module init runs the transitive
 * import-init chain (Init + the reachable mathlib/Lean + Dregg2_Exec_*).
 */
#include <lean/lean.h>
#include <stdio.h>
#include <string.h>

/* The verified production entry (C ABI: lean_object* in/out, a Lean String). */
extern "C" lean_object *dregg_exec_full_forest_auth(lean_object *input);

/* The executor's top module init (emitted by the closure). v4.30.0 ABI: single
 * uint8_t arg, returns an IO result. */
extern "C" lean_object *initialize_Dregg2_Dregg2_Exec_FFI(uint8_t builtin);

/* lean_initialize_runtime_module lives in runtime/init_module.h, not the shipped
 * lean.h; forward-declare it (it is in libleanrt_elf.a). */
extern "C" void lean_initialize_runtime_module(void);

int main(int argc, char **argv) {
    (void)argc; (void)argv;
    fputs("[exec] lean_initialize_runtime_module()\n", stderr);
    lean_initialize_runtime_module();

    fputs("[exec] initialize_Dregg2_Dregg2_Exec_FFI(builtin=1)\n", stderr);
    lean_object *res = initialize_Dregg2_Dregg2_Exec_FFI(1);
    if (lean_io_result_is_error(res)) {
        fputs("[exec] FATAL: module init returned IO error\n", stderr);
        lean_io_result_show_error(res);
        return 2;
    }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();

    /* Build the input wire string. An empty/garbage wire makes parseWWire return
     * `none`, which the entry handles by emitting a `rejected` status — a VALID
     * turn result (the fail-closed path), proving the whole decode->step->encode
     * pipeline runs end to end. A real OFFER wire can be supplied on argv[1]. */
    const char *wire = (argc > 1) ? argv[1] : "";
    lean_object *in = lean_mk_string(wire);

    fputs("[exec] >>> dregg_exec_full_forest_auth(wire)\n", stderr);
    lean_object *out = dregg_exec_full_forest_auth(in);
    const char *outc = lean_string_cstr(out);
    fprintf(stderr, "[exec] <<< receipt (%zu bytes):\n", strlen(outc));
    fputs("---RECEIPT-BEGIN---\n", stdout);
    fputs(outc, stdout);
    fputs("\n---RECEIPT-END---\n", stdout);
    lean_dec_ref(out);
    fputs("[exec] turn complete — the VERIFIED executor ran.\n", stderr);
    return 0;
}
