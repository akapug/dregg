/* aux-defs.c — faithfully recover the ONE auto-derived DecidableLt auxiliary that
 * (a) the executor reaches at init and (b) standalone `lean -c` fails to re-emit.
 *
 * THE GAP (precisely characterized): the released `lean -c`, reading the prebuilt
 * v4.30.0 `.olean`s, is internally inconsistent for `l_String_instDecidableLtRaw___aux__1`:
 * `Init.Data.String.Basic`'s fresh emission CALLS it (Basic.c:1672,5795), but
 * `Init.Data.String.PosRaw` (its canonical owner, where the toolchain's bootstrap
 * `libInit.a` defines it) does NOT re-emit it. So no re-emitted module supplies the
 * body. (3 sibling auxiliaries — BitVec/Duration — share the gap but are unreachable
 * on the executor turn and stay abort-guarded in dead-stub.c.)
 *
 * THE RECOVERY is exact, not hand-rolled: the SELF-CONTAINED wrapper that IS emitted
 * (PosRaw.c: `l_String_instDecidableLtRaw`) is verbatim
 *     uint8_t l_String_instDecidableLtRaw(p1,p2){ return lean_nat_dec_lt(p1,p2); }
 * because `String.Pos.Raw` wraps a `Nat` byteIdx and its `<` is `Nat.decLt`. The
 * `___aux__1` worker is the same instance's equation-compiler form, i.e. the SAME
 * comparison. So the faithful body is `lean_nat_dec_lt(p1, p2)`. (Borrowing ABI: the
 * call sites pass owned args and do not expect the callee to consume them — matching
 * `lean_nat_dec_lt`, which borrows.)
 */
#include <lean/lean.h>
extern "C" uint8_t l_String_instDecidableLtRaw___aux__1(lean_object *p1, lean_object *p2) {
    return lean_nat_dec_lt(p1, p2);
}
