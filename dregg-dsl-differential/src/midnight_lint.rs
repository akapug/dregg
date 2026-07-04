//! Lint the JSON emitted by `gen_midnight` for structural well-formedness.
//!
//! Midnight ZKIR v3 is verified by an off-chain proof server we don't
//! bundle. To still get *some* value out of the gen_midnight backend in
//! this crate, we statically lint the emitted program: it must parse as
//! JSON, declare each dregg caveat parameter as an input wire, and
//! terminate with an `output` instruction.

use serde_json::Value;

/// The `op` strings that are real ZKIR v3 `Instruction` variants
/// (snake_case, mirroring `~/midnight/midnight-ledger/zkir-v3/src/ir.rs`).
/// Any emitted instruction whose `op` is outside this set is a placeholder
/// that the Midnight proof server cannot consume — the lint rejects it.
const REAL_ZKIR_OPS: &[&str] = &[
    "encode",
    "decode",
    "assert",
    "cond_select",
    "constrain_bits",
    "constrain_eq",
    "constrain_to_boolean",
    "copy",
    "impact",
    "ec_mul",
    "ec_mul_generator",
    "hash_to_curve",
    "div_mod_power_of_two",
    "reconstitute_field",
    "transient_hash",
    "persistent_hash",
    "keccak256",
    "test_eq",
    "add",
    "mul",
    "neg",
    "not",
    "less_than",
    "public_input",
    "private_input",
    "output",
];

/// Check the structure of the emitted ZKIR program. Returns `Ok(())` if
/// the JSON is valid and contains the expected instruction skeleton.
pub fn lint(zkir_json: &str, param_names: &[&str]) -> Result<(), String> {
    let v: Value =
        serde_json::from_str(zkir_json).map_err(|e| format!("ZKIR JSON does not parse: {e}"))?;

    let obj = v
        .as_object()
        .ok_or_else(|| "ZKIR root is not a JSON object".to_string())?;

    // version — `IrSource::version` is an `IrMinorVersion` (a serde_repr u8),
    // so the faithful serialized form is a non-negative integer, not an object.
    let version = obj
        .get("version")
        .ok_or_else(|| "ZKIR missing `version`".to_string())?;
    let is_minor_version = version.as_u64().is_some();
    if !is_minor_version {
        return Err(format!(
            "ZKIR `version` must be the numeric IrMinorVersion repr (got {version})"
        ));
    }

    // inputs — every param name must appear
    let inputs = obj
        .get("inputs")
        .and_then(Value::as_array)
        .ok_or_else(|| "ZKIR missing `inputs` array".to_string())?;
    for &param in param_names {
        let expected_wire = format!("%{param}");
        let found = inputs.iter().any(|input| {
            input
                .as_object()
                .and_then(|o| o.get("name"))
                .and_then(Value::as_str)
                .map(|n| n == expected_wire || n.starts_with(&expected_wire))
                .unwrap_or(false)
        });
        if !found {
            return Err(format!(
                "ZKIR `inputs` missing wire for param `{param}` (expected `{expected_wire}`)"
            ));
        }
    }

    // instructions — must have at least one, last one should be `output`
    let instructions = obj
        .get("instructions")
        .and_then(Value::as_array)
        .ok_or_else(|| "ZKIR missing `instructions` array".to_string())?;
    if instructions.is_empty() {
        return Err("ZKIR `instructions` is empty".into());
    }
    // every instruction must name a real ZKIR v3 op (no placeholders)
    for instr in instructions {
        let op = instr
            .as_object()
            .and_then(|o| o.get("op"))
            .and_then(Value::as_str)
            .ok_or_else(|| "ZKIR instruction missing string `op`".to_string())?;
        if !REAL_ZKIR_OPS.contains(&op) {
            return Err(format!(
                "ZKIR instruction `op: {op}` is not a real ZKIR v3 instruction"
            ));
        }
    }
    let last_op = instructions
        .last()
        .and_then(Value::as_object)
        .and_then(|o| o.get("op"))
        .and_then(Value::as_str);
    if last_op != Some("output") {
        return Err(format!(
            "ZKIR final instruction is not `output` (got {:?})",
            last_op
        ));
    }

    Ok(())
}
