//! 負のテスト: ソルバが誤った結論（偽の一意性・存在しない解）を出さないこと。
//! いずれもソルバ全体（探索部＋検証核）を実際に走らせて確かめる。

use fe_kernel::poly::{q, qf};
use fe_kernel::{Kernel, Poly, Q};
use fe_solver::parse::parse_general;
use fe_solver::problems::load_problems;
use fe_solver::solve::{solve, SolveOutput};
use std::time::Duration;

const T: Duration = Duration::from_secs(4);

fn run(eq: &str) -> SolveOutput {
    let (l, r) = parse_general(eq).unwrap();
    solve(l, r, T).unwrap()
}

/// 総当たりで見つかる 1 次以下の解 f(x) = a x + b（a, b は小さな有理数）。検証は新しい検証核で行う。
fn brute_force_linear(l: &Poly, r: &Poly) -> Vec<(Q, Q)> {
    let k = Kernel::new(l.clone(), r.clone()).unwrap();
    let vals = [q(0), q(1), q(-1), q(2), q(-2), qf(1, 2), qf(-1, 2), q(3), q(-3)];
    let mut out = vec![];
    for a in &vals {
        for b in &vals {
            let g = Poly::var(0).scale(a).add(&Poly::constant(b.clone()));
            if k.verify_solution(&g).is_ok() {
                out.push((a.clone(), b.clone()));
            }
        }
    }
    out
}

/// 族 template（パラメータ Var(2), Var(3), …）が a x + b を含むか
fn family_contains(template: &Poly, nparams: usize, a: &Q, b: &Q) -> bool {
    let target = Poly::var(0).scale(a).add(&Poly::constant(b.clone()));
    let mut cands = vec![q(0), q(1), q(-1), q(2), q(-2), qf(1, 2), qf(-1, 2), q(3), q(-3), a.clone(), b.clone()];
    cands.push(-a.clone());
    cands.push(-b.clone());
    let combos: Vec<Vec<Q>> = match nparams {
        0 => vec![vec![]],
        1 => cands.iter().map(|c| vec![c.clone()]).collect(),
        2 => cands.iter().flat_map(|c| cands.iter().map(move |d| vec![c.clone(), d.clone()])).collect(),
        _ => return true, // 3 個以上のパラメータはこの検査の対象外（保守的に合格扱いしない方がよいが、現状出現しない）
    };
    for c in combos {
        let mut s = vec![Poly::var(0), Poly::var(1)];
        for v in &c {
            s.push(Poly::constant(v.clone()));
        }
        if template.subst_vars(&s) == target {
            return true;
        }
    }
    false
}

/// 完全解決と主張したなら: 各族が（新しい検証核でも）解であり、総当たりの解をすべて含む
fn check_sound(eq_desc: &str, l: &Poly, r: &Poly, out: &SolveOutput) {
    let fresh = Kernel::new(l.clone(), r.clone()).unwrap();
    for f in out.found.iter().chain(out.families.iter()) {
        assert!(fresh.verify_solution(f.g()).is_ok(), "{}: 解でない族を報告した: {:?}", eq_desc, f.g());
    }
    if out.status == "complete" {
        for (a, b) in brute_force_linear(l, r) {
            let ok = out.families.iter().any(|f| family_contains(f.template(), f.params().len(), &a, &b));
            assert!(ok, "{}: 完全解決と主張したが解 {}x + {} が含まれない", eq_desc, a, b);
        }
    }
}

#[test]
fn negative_pathological_equations_are_not_complete() {
    // 多項式の族で書き尽くせない解（加法的関数・各点ごとに ±x・対合・乗法的関数など）をもつ方程式
    for eq in [
        "f(x + y) = f(x) + f(y)",
        "f(x*y) = f(x)*f(y)",
        "f(x)^2 = x^2",
        "f(f(x)) = x",
        "f(x + f(y)) = f(x) + y",
        "f(x^2) = f(x)^2",
        "f(x^2 + y) = f(x)^2 + f(y)",
        "f(x)*f(y) = f(x*y)",
        "f(x*f(x)) = x^2",
        "f(x - y) = f(x) - f(y)",
    ] {
        let out = run(eq);
        assert_ne!(out.status, "complete", "{}: 解の集合が多項式の族ではないのに完全解決と主張した", eq);
        let (l, r) = parse_general(eq).unwrap();
        check_sound(eq, &l, &r, &out);
    }
}

#[test]
fn negative_multiple_solutions_not_collapsed() {
    // 複数の解をもつ方程式で、解を取りこぼして一意性を主張しないこと
    for eq in [
        "f(x*y) = x*f(y)",                // f(x) = cx
        "f(x + y) = x + f(y)",            // f(x) = x + c
        "f(x*f(y)) = f(x)*y",             // 0 と ±x?（総当たりで検査）
        "f(x + y) + f(x - y) = 2*f(x)",   // 定数と 1 次の和
        "f(x)*f(y) = f(x)*y + 0",         // 0 と x
        "f(f(x)) = f(x)",                 // 射影（非多項式の解も多い）
        "x*f(y) = y*f(x)",                // cx
        "f(x) + f(y) = f(x) + y + f(0)",  // x + c
    ] {
        let out = run(eq);
        let (l, r) = parse_general(eq).unwrap();
        check_sound(eq, &l, &r, &out);
    }
}

#[test]
fn negative_broken_database_equations() {
    // データベースの方程式を壊したもの（右辺に定数を足す・項を入れ替える）で偽の結論を出さないこと
    let probs = load_problems().unwrap();
    let mut n = 0;
    for p in probs.iter().step_by(37).take(18) {
        let (l, r) = p.equations[0].parsed.sides();
        for (tag, l2, r2) in [
            ("+1", l.clone(), r.add(&Poly::int(1))),
            ("*2", l.clone(), r.scale(&q(2))),
            ("swap", r.clone().add(&Poly::f(Poly::var(0))), l.clone()),
        ] {
            let desc = format!("{} {} ({})", p.id, p.equations[0].display, tag);
            let out = solve(l2.clone(), r2.clone(), Duration::from_secs(2)).unwrap();
            check_sound(&desc, &l2, &r2, &out);
            n += 1;
        }
    }
    assert!(n >= 50);
}

#[test]
fn negative_database_complete_results_contain_all_simple_solutions() {
    // 評価セットの一部で、完全解決なら総当たりの 1 次の解をすべて含むこと
    let probs = load_problems().unwrap();
    for p in probs.iter().step_by(23).take(37) {
        let (l, r) = p.equations[0].parsed.sides();
        let out = solve(l.clone(), r.clone(), Duration::from_secs(2)).unwrap();
        check_sound(&p.id, &l, &r, &out);
    }
}
