//! Same input, same Java, to the byte. Every `HashMap` / `HashSet` instance gets its own
//! hash keys, even within one process: a pass whose result follows table iteration order
//! makes two runs differ, so each input is decompiled several times by fresh decompilers.

use super::fixture_harness::{decompile_fixtures_apk, decompile_fixtures_dex};
use super::variable_fidelity;
use dex_decompiler::{load_dexes_from_path, parse_dex, Decompiler};
use std::path::{Path, PathBuf};

const RUNS: usize = 20;
const CLASS_RUNS: usize = 10;

/// First differing line (1-based) and its text in `a` and `b`.
fn first_difference<'a>(a: &'a str, b: &'a str) -> (usize, Option<&'a str>, Option<&'a str>) {
    let at = a
        .lines()
        .zip(b.lines())
        .position(|(x, y)| x != y)
        .unwrap_or_else(|| a.lines().count().min(b.lines().count()));
    (at + 1, a.lines().nth(at), b.lines().nth(at))
}

/// Runs `decompile` `RUNS` times; every output must equal the first one.
fn assert_stable(what: &str, decompile: impl Fn() -> String) {
    let first = decompile();
    for run in 1..RUNS {
        let next = decompile();
        if next == first {
            continue;
        }
        let (line, a, b) = first_difference(&first, &next);
        panic!("{what}: run {run} differs from run 0 at line {line}\n  run 0: {a:?}\n  run {run}: {b:?}");
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

/// Every `.dex` under `dir`, recursively, in path order.
fn dex_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    paths.sort();
    for path in paths {
        if path.is_dir() {
            dex_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "dex") {
            out.push(path);
        }
    }
}

/// Each class of each `.dex` of `testdata/`, decompiled `CLASS_RUNS` times, each run by a
/// fresh `Decompiler`. Long on the large DEXes: run it in release.
#[test]
fn every_testdata_class_decompiles_identically() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("testdata");
    let mut paths = Vec::new();
    dex_files(&root, &mut paths);
    assert!(!paths.is_empty(), "no .dex under {}", root.display());
    for path in &paths {
        let data = std::fs::read(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let dex = parse_dex(&data).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
        let decompile_classes = || -> Vec<(String, String)> {
            let dc = Decompiler::new(&dex);
            dc.collect_included_classes()
                .unwrap_or_else(|e| panic!("classes of {}: {e}", path.display()))
                .into_iter()
                .map(|(class_def, class)| {
                    let java = dc
                        .decompile_class(&class_def)
                        .unwrap_or_else(|e| format!("<error: {e}>"));
                    (class, java)
                })
                .collect()
        };
        let first = decompile_classes();
        for run in 1..CLASS_RUNS {
            let next = decompile_classes();
            for ((class, a), (_, b)) in first.iter().zip(&next) {
                if a != b {
                    let (line, ra, rb) = first_difference(a, b);
                    panic!(
                        "{} {class}: run {run} differs from run 0 at line {line}\n  \
                         run 0: {ra:?}\n  run {run}: {rb:?}",
                        path.display()
                    );
                }
            }
        }
    }
}
