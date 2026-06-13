/* init-stubs.c — break the metaprogramming init-chain for the embedded executor.
 *
 * The verified executor closure imports `Dregg2.Tactics` (a proof/metaprogramming
 * module) from nearly every data module. At module-init time, the REAL
 * initialize_Dregg2_Dregg2_Tactics calls initialize_Lean + the mathlib Tactic
 * framework — which drags the entire Lean elaborator/kernel (lean_expr_*,
 * lean_kernel_*, lean_add_decl, ...) into the link. Those C++ kernel primitives
 * live in libleancpp/src/kernel (not the compiled .c facets) and are NEVER called
 * by `dregg_exec_full_forest_auth` (verified: the executor's reachable compute
 * objects reference ZERO elaborator/kernel symbols — they enter ONLY via this
 * init-chain).
 *
 * So we provide NO-OP versions of the metaprogramming initializers. Linked before
 * the closure archive, the linker resolves these symbols here and never pulls the
 * real (elaborator-dragging) members. The executor's DATA modules keep their own
 * inits (which pull only the data mathlib already in libmathlib_elf.a).
 *
 * Init ABI (v4.30.0): lean_object* initialize_X(uint8_t builtin); returns
 * lean_io_result_mk_ok(lean_box(0)). Idempotent via a local guard.
 */
#include <lean/lean.h>

#define NOOP_INIT(name)                                                   \
  static uint8_t name##_done = 0;                                         \
  extern "C" lean_object *name(uint8_t builtin) {                         \
    (void)builtin;                                                        \
    if (name##_done) return lean_io_result_mk_ok(lean_box(0));            \
    name##_done = 1;                                                      \
    return lean_io_result_mk_ok(lean_box(0));                            \
  }

/* The elaborator gateways reachable from the executor (verified set). We stub the
 * BIG gateway `initialize_Lean` (the whole Lean elaborator/kernel init) and the
 * Dregg2/aesop metaprogramming roots; that cuts the bulk of the elaborator. We do
 * NOT stub the individual mathlib `Tactic_*` inits: those objects get pulled from
 * the mathlib archive for the DATA symbols they also define, so stubbing them here
 * causes multiple-definition. Any elaborator C++ primitive their dead tactic code
 * references is caught by the kernel-stub (kernel-stub-syms.txt) instead. */
NOOP_INIT(initialize_Dregg2_Dregg2_Tactics)
NOOP_INIT(initialize_Lean)
NOOP_INIT(initialize_aesop_Aesop)
