/- `lake env lean --run EmitFhIRClearingPlan.lean` emits the Rust-consumed plan artifact. -/
import Market.FhIRClearingPlan

open Market.FhIRClearingPlan

def main : IO Unit :=
  match emitCanonical rebalanceV1 with
  | some wire => IO.print wire
  | none => throw <| IO.userError "rebalance-v1 is not admitted; refusing to emit"
