//! 手法の汎用性のテスト: 問題集（データベース）にない、同じ類の方程式でも手法が効くことを確かめる。
//! 問題集の文法では書けない係数や符号（2y, x − f(y) など）を使った方程式を選んでいる。
//! 各テストは、報告された解の族を新しい検証核でも確かめる（健全性の二重確認）。
//! 手法と方程式の類の対応は docs/TACTICS.md を参照。

use fe_kernel::{AddKind, Kernel, Poly};
use fe_solver::parse::parse_general;
use fe_solver::solve::{solve, SolveOutput};
use std::time::Duration;

fn run(eq: &str, secs: u64) -> (Poly, Poly, SolveOutput) {
    let (l, r) = parse_general(eq).unwrap();
    let out = solve(l.clone(), r.clone(), Duration::from_secs(secs)).unwrap();
    (l, r, out)
}

/// 報告した族がすべて新しい検証核でも解であること
fn check_families(eq: &str, l: &Poly, r: &Poly, out: &SolveOutput) {
    let fresh = Kernel::new(l.clone(), r.clone()).unwrap();
    for f in out.families.iter().chain(out.found.iter()) {
        assert!(fresh.verify_solution(f.g()).is_ok(), "{}: 解でない族 {:?}", eq, f.g());
    }
    for f in out.add_families.iter().chain(out.add_found.iter()) {
        assert!(fresh.verify_additive_kind(f.g(), f.kind()).is_ok(), "{}: 解でない加法的な族", eq);
    }
}

/// 加法的関数の族（特殊解決）: f(線形結合) = 線形結合の f の型（コーシー型）
#[test]
fn tactic_additive_family_cauchy_type() {
    for eq in ["f(x + 2*y) = f(x) + 2*f(y)", "f(2*x + 3*y) = 2*f(x) + 3*f(y)", "f(3*x + 3*y) = 3*f(x) + 3*f(y)"] {
        let (l, r, out) = run(eq, 10);
        assert_eq!(out.status, "special", "{}", eq);
        assert!(out.add_families.iter().any(|f| f.kind() == AddKind::Free), "{}: 条件のない加法的な族がない", eq);
        check_families(eq, &l, &r, &out);
    }
}

/// 対合の加法的関数の族（特殊解決）: f(x + k·f(y)) = f(x) + k·y の型
#[test]
fn tactic_involution_family() {
    for eq in ["f(x + 2*f(y)) = f(x) + 2*y", "f(x - f(y)) = f(x) - y", "f(x + f(2*y)) = f(x) + 2*y"] {
        let (l, r, out) = run(eq, 10);
        assert_eq!(out.status, "special", "{}", eq);
        assert!(out.add_families.iter().any(|f| f.kind() == AddKind::Involution), "{}: 対合の族がない", eq);
        check_families(eq, &l, &r, &out);
    }
}

/// 分数の代入: f(x² + c·xy) = f(x)² + f(c·xy) の型（y := y/x で f(x² + y) = f(x)² + f(y) に帰着）
#[test]
fn tactic_fraction_substitution() {
    let eq = "f(x^2 + 2*x*y) = f(x)^2 + f(2*x*y)";
    let (l, r, out) = run(eq, 60);
    assert_eq!(out.status, "complete", "{}", eq);
    let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    got.sort();
    assert_eq!(got, vec!["0".to_string(), "x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// 入れ替えの差と f の値で決まる量の補題: 右辺が x, y について対称な f(A(x, y)) = R(x, y) の型。
/// P(x, y) − P(y, x) で f(A(x, y)) = f(A(y, x))、P(1, x) 型の事実 f(g(f(x))) = S(x) から単射性を導いて A(x, y) = A(y, x)
#[test]
fn tactic_swap_difference_and_value_injectivity() {
    for (eq, want) in [
        ("f(x*f(y) + 2*f(x*y)) = x*y + 2*f(x*y)", vec!["-1/3*x", "x"]),
        ("f(2*x*f(y) + f(x*y)) = 2*x*y + f(x*y)", vec!["-2/3*x", "x"]),
    ] {
        let (l, r, out) = run(eq, 30);
        assert_eq!(out.status, "complete", "{}", eq);
        let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
        got.sort();
        assert_eq!(got, want, "{}: 解の集合 {:?}", eq, got);
        check_families(eq, &l, &r, &out);
    }
}
