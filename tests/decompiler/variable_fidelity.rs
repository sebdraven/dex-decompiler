//! Variable naming / typing fidelity on hand-built bytecode (register reuse).
//! Cases the minimal DEX cannot express (parameters, `<init>`, typed calls) are in
//! `tests/decompiler/variable_fidelity_cases.md`.

use super::helpers::minimal_dex_with_method_code;
use dex_decompiler::{parse_dex, Decompiler};
use regex::Regex;

pub(super) fn decompile(bytecode: &[u8]) -> String {
    let dex_bytes = minimal_dex_with_method_code(bytecode);
    let dex = parse_dex(&dex_bytes).unwrap();
    Decompiler::new(&dex).decompile().unwrap()
}

/// Every method body of this module (determinism replays them).
pub(super) const CASES: [&[u8]; 4] =
    [D1_LITERAL_JOIN, D1_MOVE_RESULT_IF, D6_FOLDED_CONST, CMPL_DOUBLE_IF_LTZ];

const D1_LITERAL_JOIN: &[u8] = &[
    0x12, 0x01, // 00: const/4 v1, 0
    0x22, 0x00, 0x00, 0x00, // 02: new-instance v0, java.lang.Object
    0x38, 0x01, 0x04, 0x00, // 06: if-eqz v1, +4 -> 0e
    0x1a, 0x00, 0x03, 0x00, // 0a: const-string v0, "foo"
    0x6e, 0x10, 0x00, 0x00, 0x00, 0x00, // 0e: invoke-virtual {v0}, Simple.foo()
    0x0e, 0x00, // 14: return-void
];

const D1_MOVE_RESULT_IF: &[u8] = &[
    0x12, 0x00, // 00: const/4 v0, 0
    0x22, 0x01, 0x00, 0x00, // 02: new-instance v1, java.lang.Object
    0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 06: invoke-virtual {v1}, Simple.foo()
    0x0a, 0x00, // 0c: move-result v0
    0x38, 0x00, 0x05, 0x00, // 0e: if-eqz v0, +5 -> 18
    0x6e, 0x10, 0x00, 0x00, 0x01, 0x00, // 12: invoke-virtual {v1}, Simple.foo()
    0x0e, 0x00, // 18: return-void
];

const D6_FOLDED_CONST: &[u8] = &[
    0x12, 0x50, // 00: const/4 v0, 5
    0x38, 0x00, 0x03, 0x00, // 02: if-eqz v0, +3 -> 08
    0x0e, 0x00, // 06: return-void
    0xd8, 0x01, 0x00, 0x01, // 08: add-int/lit8 v1, v0, 1
    0x38, 0x01, 0x03, 0x00, // 0c: if-eqz v1, +3 -> 12
    0x0e, 0x00, // 10: return-void
    0x0e, 0x00, // 12: return-void
];

const CMPL_DOUBLE_IF_LTZ: &[u8] = &[
    0x16, 0x00, 0x01, 0x00, // 00: const-wide/16 v0, 1
    0x2f, 0x00, 0x00, 0x00, // 04: cmpl-double v0, v0, v0
    0x3a, 0x00, 0x05, 0x00, // 08: if-ltz v0, +5 -> 12
    0x16, 0x00, 0x02, 0x00, // 0c: const-wide/16 v0, 2
    0x0e, 0x00, // 10: return-void
    0x0e, 0x00, // 12: return-void
];

/// Synthetic locals read somewhere without a `Type name =` declaration.
fn undeclared_locals(java: &str) -> Vec<String> {
    let token = Regex::new(r"\b(?:i|z|l|s|f|d|c|obj|local|v)\d+(?:_r\d+)?\b").unwrap();
    let mut missing: Vec<String> = Vec::new();
    for m in token.find_iter(java) {
        let name = m.as_str();
        let decl = Regex::new(&format!(r"[\w.$\[\]<>]+\s+{}\s*=", regex::escape(name))).unwrap();
        if !decl.is_match(java) && !missing.iter().any(|n| n == name) {
            missing.push(name.to_string());
        }
    }
    missing
}

/// D1: v0 is `new Object()` or `"foo"` at the call (φ). The literal must not become
/// the receiver (`"wsClient".f()` in 001173).
#[test]
fn d1_literal_from_one_branch_is_not_the_receiver_after_the_join() {
    let java = decompile(D1_LITERAL_JOIN);
    assert!(java.contains(".foo()"), "{java}");
    assert!(!java.contains("\"foo\".foo()"), "{java}");
}

/// D1: `move-result v0` redefines v0 between `const/4 v0, 0` and `if-eqz v0`; the
/// constant must not be folded into the condition (`if ("RAT_DEBUG" == null)` in 001155).
#[test]
fn d1_constant_overwritten_by_move_result_is_not_folded_into_if() {
    let java = decompile(D1_MOVE_RESULT_IF);
    assert!(java.contains("if ("), "{java}");
    assert!(!java.contains("0 == 0"), "{java}");
    assert!(!java.contains("0 != 0"), "{java}");
}

/// D6: `const/4 v0, 5` feeds both the first `if` and `add-int/lit8`. Folding it into the
/// condition must not drop the definition the addition still reads.
#[test]
fn d6_constant_folded_into_if_stays_defined_for_its_other_use() {
    let java = decompile(D6_FOLDED_CONST);
    let missing = undeclared_locals(&java);
    assert!(missing.is_empty(), "undeclared {missing:?} in:\n{java}");
}

/// A cmpl-double result is `int`, although its register holds a double before and after
/// (`float f2 = (d5 < 0.9) ? -1 : …`, `byte[] l0 = …`).
#[test]
fn cmp_result_is_declared_int() {
    let java = decompile(CMPL_DOUBLE_IF_LTZ);
    let decl = Regex::new(r"(?m)^\s*([\w.$\[\]<>]+)\s+\w+\s*=\s*\(.*\)\s*\?\s*-1\s*:").unwrap();
    let ty = decl.captures(&java).map(|c| c[1].to_string());
    assert_eq!(ty.as_deref(), Some("int"), "{java}");
}
