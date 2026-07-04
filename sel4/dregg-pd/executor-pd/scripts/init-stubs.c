/* init-stubs.c — the executor closure's import-boundary initializers.
 *
 * THE PRINCIPLED ELABORATOR TRIM (EMBEDDABLE-LEAN-RUNTIME.md §4 #2). The verified
 * executor closure imports `Dregg2.Tactics` (a pure metaprogramming module —
 * `#assert_axioms`/`#assert_clean` command elabs + the `dregg_auto`/`option_inj`/…
 * proof-automation macros) from 22 of its 77 reachable modules. That facet
 * (`Tactics.c`) `LEAN_EXPORT`s ZERO `l_Dregg2_*` runtime functions — only its
 * module initializer `initialize_Dregg2_Dregg2_Tactics`, which the toolchain emits
 * to chain into `initialize_Lean` + the mathlib `Tactic.Tauto`/`Ring` inits, which
 * drag the ENTIRE Lean elaborator/kernel (lean_expr_*, lean_kernel_*,
 * lean_add_decl, …) into the link. The executor's compute path calls ZERO of
 * those (verified): they enter ONLY via this init-chain.
 *
 * So `cross-compile-closure.sh` EXCLUDES `Tactics.c` from the closure archive
 * (`RUNTIME_DEAD_TRIM`) — the elaborator is severed at the SHAPE of the closure,
 * because `Tactics.c` is the only facet in the whole closure that calls
 * `initialize_Lean`. With the facet absent, `initialize_Dregg2_Dregg2_Tactics`
 * (still CALLED by the 22 importing facets' init-chains) is a genuine
 * import-boundary symbol — resolved by the no-op HERE. This is now a true closure
 * boundary, not a link-order shadow of a linked-but-dead member.
 *
 * `initialize_Lean` / `initialize_aesop_Aesop` no-ops stay (defensively):
 *   - initialize_aesop_Aesop is genuinely still called from the closure
 *     (`Dregg2.Catalog`'s init-chain); its no-op cuts the aesop metaprogramming
 *     init the same way (Catalog uses aesop only at proof time).
 *   - initialize_Lean is no longer referenced by any CLOSURE facet (Tactics.c was
 *     its sole caller), but the linked Lean runtime archives (libLean_elf.a) define
 *     and may chain it; the no-op keeps the elaborator-init severed there too.
 * Linked before the archives, the linker resolves these here.
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
