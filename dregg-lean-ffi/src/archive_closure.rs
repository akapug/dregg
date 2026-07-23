use std::collections::HashSet;

const INITIALIZER_PREFIXES: [&str; 3] = ["initialize_", "runtime_initialize_", "meta_initialize_"];

pub(crate) fn initializer_module(symbol: &str) -> Option<&str> {
    let symbol = symbol.trim_start_matches('_');
    INITIALIZER_PREFIXES
        .iter()
        .find_map(|prefix| symbol.strip_prefix(prefix))
}

fn is_toolchain_module(module: &str) -> bool {
    ["Init", "Std", "Lean", "Lake"]
        .iter()
        .any(|lib| module == *lib || module.starts_with(&format!("{lib}_")))
}

pub(crate) fn undefined_initializers_from_nm(text: &str) -> Result<Vec<String>, String> {
    let mut defined = HashSet::new();
    let mut referenced = HashSet::new();
    let mut initializer_records = 0usize;
    for line in text.lines() {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        let (kind, symbol) = match tokens.as_slice() {
            [kind, symbol] if kind.len() == 1 => (*kind, *symbol),
            [_address, kind, symbol] if kind.len() == 1 => (*kind, *symbol),
            _ => continue,
        };
        let name = symbol.trim_start_matches('_');
        let Some(module) = initializer_module(name) else {
            continue;
        };
        if is_toolchain_module(module) {
            continue;
        }
        initializer_records += 1;
        if kind == "U" {
            referenced.insert(name.to_string());
        } else {
            defined.insert(name.to_string());
        }
    }
    if initializer_records == 0 {
        return Err(
            "nm output contained no recognizable non-toolchain Lean initializer records"
                .to_string(),
        );
    }
    let mut missing: Vec<String> = referenced.difference(&defined).cloned().collect();
    missing.sort();
    Ok(missing)
}

pub(crate) fn describe_unresolved(symbols: &[String]) -> String {
    let shown = symbols
        .iter()
        .take(8)
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join(", ");
    let suffix = if symbols.len() > 8 { ", …" } else { "" };
    format!(
        "{} unresolved initializer(s): {shown}{suffix}",
        symbols.len()
    )
}

/// Repeatedly extract dependency objects until the archive has no missing module initializer.
/// There is deliberately no pass bound: the archive grows monotonically, and a repeated unresolved
/// set is the actual fixed point that proves extraction cannot make further progress.
pub(crate) fn converge<M, A>(mut missing: M, mut add: A) -> Result<usize, String>
where
    M: FnMut() -> Result<Vec<String>, String>,
    A: FnMut(usize, &[String]) -> Result<usize, String>,
{
    let mut seen = HashSet::new();
    for pass in 0usize.. {
        let mut unresolved = missing()?;
        unresolved.sort();
        unresolved.dedup();
        if unresolved.is_empty() {
            return Ok(pass);
        }
        if !seen.insert(unresolved.clone()) {
            return Err(format!(
                "initializer closure reached a non-empty fixed point; {}",
                describe_unresolved(&unresolved)
            ));
        }
        let added = add(pass, &unresolved)?;
        if added == 0 {
            return Err(format!(
                "initializer closure made no progress; {}",
                describe_unresolved(&unresolved)
            ));
        }
    }
    unreachable!("the unbounded pass index can only end by convergence or error")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn closure_converges_past_the_old_sixteen_pass_bound() {
        let remaining = Cell::new(25usize);
        let passes = converge(
            || {
                let n = remaining.get();
                Ok(if n == 0 {
                    Vec::new()
                } else {
                    vec![format!("initialize_mathlib_Dependency_{n}")]
                })
            },
            |_pass, unresolved| {
                assert_eq!(unresolved.len(), 1);
                remaining.set(remaining.get() - 1);
                Ok(1)
            },
        )
        .expect("a finite dependency chain must converge");

        assert_eq!(passes, 25);
    }

    #[test]
    fn closure_rejects_a_non_empty_fixed_point() {
        let error = converge(
            || Ok(vec!["initialize_mathlib_Missing".to_string()]),
            |_pass, _unresolved| Ok(1),
        )
        .expect_err("a repeated unresolved set must fail loudly");

        assert!(error.contains("non-empty fixed point"));
        assert!(error.contains("initialize_mathlib_Missing"));
    }

    #[test]
    fn final_validation_covers_all_lean_initializer_variants() {
        let missing = undefined_initializers_from_nm(
            "                 U initialize_mathlib_Mathlib_A\n\
             0000000000000000 T meta_initialize_mathlib_Mathlib_A\n\
                              U runtime_initialize_mathlib_Mathlib_A\n\
                              U meta_initialize_mathlib_Mathlib_A\n\
                              U initialize_Lean_Elab\n\
                              U runtime_initialize_Std_Data\n",
        )
        .expect("the fixture contains recognizable project initializers");

        assert_eq!(
            missing,
            vec![
                "initialize_mathlib_Mathlib_A".to_string(),
                "runtime_initialize_mathlib_Mathlib_A".to_string(),
            ]
        );
    }

    #[test]
    fn malformed_nm_output_cannot_masquerade_as_a_closed_archive() {
        let error = undefined_initializers_from_nm("archive.a(member.o): unexpected format")
            .expect_err("a matched-nothing scan must fail loudly");

        assert!(error.contains("no recognizable"));
    }
}
