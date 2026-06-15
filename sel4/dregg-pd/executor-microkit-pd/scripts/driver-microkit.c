/* driver-microkit.c — the one-turn harness for the ASSEMBLED executor PD.
 *
 * Exposes three C entries the Rust Microkit PD (src/main.rs) calls:
 *
 *   dregg_executor_init()        — run the embedded-Lean runtime init ONCE (at PD
 *                                  boot, after the sel4-musl syscall handler is
 *                                  installed). Returns 0 on success.
 *   dregg_executor_run_turn(in_ptr, in_len, out_ptr, out_cap)
 *                                — run ONE real turn through the VERIFIED executor
 *                                  entry `dregg_exec_full_forest_auth(String)
 *                                  -> String` (Dregg2/Exec/FFI.lean). The turn
 *                                  wire is read from `in_ptr[0..in_len]` (the
 *                                  `turn_in` shared region the net/ingress edge
 *                                  staged), and the receipt is copied into
 *                                  `out_ptr[0..out_cap]` (the `commit_out` region
 *                                  handed to persist). Returns the receipt byte
 *                                  length (>=0), or -1 if it would overflow
 *                                  out_cap.
 *   dregg_executor_demo_wire(len)— the verified `wideDemoInput` wire (the same
 *                                  OFFER the host-musl + rootserver runs banked →
 *                                  status:2 ok:1), so the PD can self-stage a real
 *                                  turn when the net edge hasn't written one. The
 *                                  wire is compiled in via out/demo-wire.o.
 *
 * This is the SAME init contract + turn as ../executor-rootserver/scripts/
 * driver-sel4.c, but the turn input/output flow through the shared `turn_in` /
 * `commit_out` regions (the assembly's real channels) rather than a compiled-in
 * wire and stdout. Init for COMPILED Lean (NOT lean_initialize, which would pull
 * the elaborator/kernel — see ../../executor-pd/WALL.md).
 *
 * Diagnostic prints go to stderr via the libc, whose write()/writev() the
 * sel4-musl handler in main.rs routes to the seL4 debug serial.
 */
#include <lean/lean.h>
#include <stdio.h>
#include <string.h>

/* The verified production entry (C ABI: lean_object* in/out, a Lean String). */
extern lean_object *dregg_exec_full_forest_auth(lean_object *input);

/* The executor's top module init (emitted by the closure). v4.30.0 ABI: single
 * uint8_t arg, returns an IO result. */
extern lean_object *initialize_Dregg2_Dregg2_Exec_FFI(uint8_t builtin);

/* In runtime/init_module.h, not the shipped lean.h; it is in libleanrt_elf.a. */
extern void lean_initialize_runtime_module(void);

/* The verified demo wire (the same `wideDemoInput` the host-musl + rootserver
 * runs banked → status:2 ok:1). Provided as a generated C string constant
 * (out/demo-wire.c, emitted from out/demo-wire.txt). A weak "" fallback keeps the
 * driver linkable on its own (the entry handles "" as a fail-closed `rejected` —
 * still a full decode→step→encode round trip). */
extern const char dregg_demo_wire[];
__attribute__((weak)) const char dregg_demo_wire[] = "";

const char *dregg_executor_demo_wire(unsigned long *len) {
    if (len) *len = (unsigned long)strlen(dregg_demo_wire);
    return dregg_demo_wire;
}

int dregg_executor_init(void) {
    fputs("[executor]   lean_initialize_runtime_module()\n", stderr);
    lean_initialize_runtime_module();

    fputs("[executor]   initialize_Dregg2_Dregg2_Exec_FFI(builtin=1)\n", stderr);
    lean_object *res = initialize_Dregg2_Dregg2_Exec_FFI(1);
    if (lean_io_result_is_error(res)) {
        fputs("[executor]   FATAL: module init returned IO error\n", stderr);
        lean_io_result_show_error(res);
        return 2;
    }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();
    fputs("[executor]   embedded Lean runtime initialized — executor ready\n", stderr);
    return 0;
}

/* Run ONE verified turn. `in_ptr[0..in_len]` is the turn wire (from turn_in);
 * the receipt is copied to `out_ptr[0..out_cap]` (commit_out). Returns the
 * receipt length, or -1 on overflow. */
long dregg_executor_run_turn(const char *in_ptr, unsigned long in_len,
                             char *out_ptr, unsigned long out_cap) {
    /* lean_mk_string wants a NUL-terminated C string; the wire in turn_in is raw
     * bytes of length in_len. Build a Lean String from the explicit length so we
     * neither over-read past in_len nor require the region to be NUL-terminated. */
    lean_object *in = lean_mk_string_from_bytes(in_ptr, (size_t)in_len);

    fprintf(stderr, "[executor]   >>> dregg_exec_full_forest_auth(turn_in, %lu bytes)\n", in_len);
    lean_object *out = dregg_exec_full_forest_auth(in);
    const char *outc = lean_string_cstr(out);
    size_t outn = strlen(outc);
    fprintf(stderr, "[executor]   <<< receipt (%zu bytes)\n", outn);

    long rc;
    if (outn + 1 <= out_cap) {
        memcpy(out_ptr, outc, outn);
        out_ptr[outn] = 0; /* NUL so persist can treat it as a C string too */
        rc = (long)outn;
    } else {
        fprintf(stderr, "[executor]   receipt (%zu) exceeds commit_out capacity (%lu)\n",
                outn, out_cap);
        rc = -1;
    }
    lean_dec_ref(out);
    return rc;
}
