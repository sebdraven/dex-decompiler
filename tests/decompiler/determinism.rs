//! Same input, same Java, to the byte. Every `HashMap` / `HashSet` instance gets its own
//! hash keys, even within one process: a pass whose result follows table iteration order
//! makes two runs differ, so each input is decompiled several times by fresh decompilers.

use super::fixture_harness::{decompile_fixtures_apk, decompile_fixtures_dex};
use super::variable_fidelity;
use dex_decompiler::{load_dexes_from_path, Decompiler};
use std::path::PathBuf;

const RUNS: usize = 20;

/// Runs `decompile` `RUNS` times; every output must equal the first one.
fn assert_stable(what: &str, decompile: impl Fn() -> String) {
    let first = decompile();
    for run in 1..RUNS {
        let next = decompile();
        if next == first {
            continue;
        }
        let at = first
            .lines()
            .zip(next.lines())
            .position(|(a, b)| a != b)
            .unwrap_or_else(|| first.lines().count().min(next.lines().count()));
        panic!(
            "{what}: run {run} differs from run 0 at line {}\n  run 0: {:?}\n  run {run}: {:?}",
            at + 1,
            first.lines().nth(at),
            next.lines().nth(at),
        );
    }
}

#[test]
fn fixtures_dex_decompiles_identically() {
    assert_stable("decompiler_fixtures/classes.dex", decompile_fixtures_dex);
}

#[test]
fn fixtures_apk_decompiles_identically() {
    assert_stable("decompiler_fixtures.apk", decompile_fixtures_apk);
}

#[test]
fn variable_fidelity_cases_decompile_identically() {
    for (i, bytecode) in variable_fidelity::CASES.iter().enumerate() {
        assert_stable(&format!("variable_fidelity case {i}"), || {
            variable_fidelity::decompile(bytecode)
        });
    }
}

/// The `TestDefault` methods of `type_fidelity` (loops, try/catch, typed locals).
#[test]
fn type_fidelity_methods_decompile_identically() {
    const CLASS: &str = "androguard.test.TestDefault";
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("testdata/classes4.dex");
    let dexes =
        load_dexes_from_path(&path).unwrap_or_else(|e| panic!("load {}: {e}", path.display()));
    for method in ["testDouble", "pouet2", "foo4", "foobis", "main", "foo2", "test_base"] {
        assert_stable(&format!("{CLASS}#{method}"), || {
            for dex in &dexes {
                let dc = Decompiler::new(dex);
                if let Some(encoded) = dc.find_method(CLASS, method) {
                    return dc
                        .decompile_method(&encoded, Some("TestDefault"), Some(CLASS))
                        .unwrap_or_else(|e| panic!("decompile {CLASS}#{method}: {e}"));
                }
            }
            panic!("method not found: {CLASS}#{method}");
        });
    }
}
