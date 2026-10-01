/-
# SeedDraw — the uniformity EVALUATION, out of the crypto archive's build

`SeedDraw.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its uniformity pin ran a `native_decide` at elaboration — so a
game-fixture regression was a hard failure of every Rust proving target in the workspace
(the compilation-unit coupling the stale-fixture outage measured).  The STATEMENT remains
in `SeedDraw.lean` as an evaluation-free `check_* : Bool` definition; THIS module is where
it is RUN.  It is rooted in the `PathOfAngelsGuards` library and reachable from
`Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates the pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

The theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified name is unchanged.
-/
import Dregg2.Games.PathOfAngels.SeedDraw

namespace Dregg2.Games.PathOfAngels.SeedDraw

set_option autoImplicit false

/-! ## The laboratory, moved out of the runtime module (#86)

These definitions were compiled into the `Dregg2.FFI` closure, and Lean computes every compiled
no-argument `def` when its module initializes: each `check_*` and fixture here ran on every node
boot. They live beside the pins that evaluate them now; nothing linked into the node reaches them. -/

/-- Uniformity over the WHOLE domain a byte stream can serve.  For every bound
in `1..256`, every residue below it has exactly `256 / bound` accepted preimages,
so no residue is favoured — this is the complete finite domain of `drawBelow?`,
not a sample of it. -/
def drawUniformB : Bool :=
  (List.range 257).all fun bound =>
    bound == 0 || (fibreSizes bound).all (fun n => n == 256 / bound)

/-- Uniformity over the WHOLE domain a byte stream can serve: for every bound in
`1..256`, every residue below it has exactly `256 / bound` accepted preimages.
(Pinned `= true` in `SeedDrawFixtures`.) -/
def check_draw_is_uniform_on_every_bound : Bool := drawUniformB

theorem draw_is_uniform_on_every_bound :
    check_draw_is_uniform_on_every_bound = true := by native_decide

#assert_compiled draw_is_uniform_on_every_bound

end Dregg2.Games.PathOfAngels.SeedDraw
