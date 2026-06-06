import Dregg2.Circuit.TurnEmit
namespace S3
open Dregg2.Circuit Dregg2.Circuit.TurnEmit
open Dregg2.Circuit.SetFieldCommit (emittedSetField setFieldAirName setFieldCircuit)
open Dregg2.Circuit.EffectInstances (setFieldE)
open Dregg2.Circuit.EffectCommit (effectCircuit emittedEffect)

-- structurally equal as lists? try decide on the constraint lists
example : (effectCircuit setFieldE).length = setFieldCircuit.length := by native_decide
end S3
