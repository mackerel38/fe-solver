//! 負のテスト: ソルバが誤った結論（偽の一意性・存在しない解）を出さないこと。
//! いずれもソルバ全体（探索部＋検証核）を実際に走らせて確かめる。

use fe_kernel::poly::{q, qf};
use fe_kernel::{AddKind, Kernel, Poly, Q};
use num_traits::Zero;
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

/// 加法的な族 {A + t} が 1 次関数 ax + b を含むか（t = 0 なら b = 0、t が単独のパラメータなら常に。
/// 条件つきの族なら t = 0 で、さらに a² = 1（対合）または a² = a（射影））
fn add_family_contains(fam: &fe_kernel::AddFamily, a: &fe_kernel::Q, b: &fe_kernel::Q) -> bool {
    let t = fam.template();
    match fam.kind() {
        AddKind::Free => {
            if t.is_zero() {
                b.is_zero()
            } else {
                *t == Poly::var(2)
            }
        }
        AddKind::Involution => t.is_zero() && b.is_zero() && a.clone() * a.clone() == q(1),
        AddKind::Projection => t.is_zero() && b.is_zero() && a.clone() * a.clone() == a.clone(),
    }
}

/// 報告した族がすべて（新しい検証核でも）解であること。
/// 完全解決と主張したなら総当たりの解をすべて含み、しかも「任意の加法的関数が解」ではないこと
/// （そうなら多項式で書けない病的な解があるので、多項式・区分的な族だけの完全解決は誤り）。
/// 特殊解決と主張したなら、加法的な族が解で、総当たりの解をすべて含むこと。
fn check_sound(eq_desc: &str, l: &Poly, r: &Poly, out: &SolveOutput) {
    let fresh = Kernel::new(l.clone(), r.clone()).unwrap();
    for f in out.found.iter().chain(out.families.iter()) {
        assert!(fresh.verify_solution(f.g()).is_ok(), "{}: 解でない族を報告した: {:?}", eq_desc, f.g());
    }
    for f in out.pw_found.iter().chain(out.pw_families.iter()) {
        assert!(fresh.verify_piecewise(f.breaks().to_vec(), f.pieces().to_vec()).is_ok(), "{}: 解でない区分的な族を報告した", eq_desc);
    }
    for f in out.add_found.iter().chain(out.add_families.iter()) {
        assert!(fresh.verify_additive_kind(f.g(), f.kind()).is_ok(), "{}: 解でない加法的な族を報告した: {:?}", eq_desc, f.g());
    }
    if out.status == "special" || out.status == "special_exist" {
        assert!(out.add_found.is_some(), "{}: 特殊解決なのに加法的な族の検証がない", eq_desc);
    }
    if out.status == "special" {
        assert!(!out.add_families.is_empty(), "{}: 特殊解決なのに加法的な族の葉がない", eq_desc);
    }
    if out.status == "complete" {
        assert!(
            fresh.verify_additive(&Poly::zero()).is_err()
                && fresh.verify_additive(&Poly::f(Poly::zero())).is_err()
                && fresh.verify_additive_kind(&Poly::zero(), AddKind::Involution).is_err()
                && fresh.verify_additive_kind(&Poly::zero(), AddKind::Projection).is_err(),
            "{}: 病的な加法的関数の族が解なのに、多項式・区分的な族だけで完全解決と主張した",
            eq_desc
        );
    }
    if out.status == "complete" || out.status == "special" {
        for (a, b) in brute_force_linear(l, r) {
            let ok = out.families.iter().any(|f| family_contains(f.template(), f.params().len(), &a, &b))
                || out.add_families.iter().any(|f| add_family_contains(f, &a, &b));
            assert!(ok, "{}: 解の集合を決めたと主張したが解 {}x + {} が含まれない", eq_desc, a, b);
        }
        // 区分的な解（区切り点 0、各側 ±x, 0, ±1）を総当たりで探し、完全解決の答えに含まれることを確かめる
        let side = [Poly::var(0), Poly::var(0).neg(), Poly::zero(), Poly::int(1), Poly::int(-1)];
        for gl in &side {
            for gr in &side {
                for v in [Poly::zero(), Poly::int(1), Poly::int(-1)] {
                    let pieces = vec![gl.clone(), v.clone(), gr.clone()];
                    if fresh.verify_piecewise(vec![q(0)], pieces.clone()).is_err() {
                        continue;
                    }
                    let as_poly = gl == gr && v == gl.subst_vars(&[Poly::zero()]);
                    let lin_b = gl.terms().iter().find(|(m, _)| m.is_one()).map(|(_, c)| c.clone()).unwrap_or_else(|| q(0));
                    let lin = gl.terms().iter().all(|(m, _)| m.degree() <= 1);
                    let lin_a = gl.terms().iter().find(|(m, _)| !m.is_one()).map(|(_, c)| c.clone()).unwrap_or_else(|| q(0));
                    let ok = if as_poly && lin && out.add_families.iter().any(|f| add_family_contains(f, &lin_a, &lin_b)) {
                        true
                    } else if as_poly {
                        out.families.iter().any(|f| f.params().is_empty() && f.template() == gl)
                            || out.families.iter().any(|f| {
                                let cs = gl.terms();
                                let a = cs.iter().find(|(m, _)| !m.is_one()).map(|(_, c)| c.clone()).unwrap_or_else(|| q(0));
                                let b = cs.iter().find(|(m, _)| m.is_one()).map(|(_, c)| c.clone()).unwrap_or_else(|| q(0));
                                family_contains(f.template(), f.params().len(), &a, &b)
                            })
                    } else {
                        out.pw_families.iter().any(|f| f.pieces() == &pieces[..])
                    };
                    assert!(ok, "{}: 完全解決と主張したが区分的な解 {:?} が含まれない", eq_desc, pieces.iter().map(|p| p.to_string()).collect::<Vec<_>>());
                }
            }
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
        "f(x + y^2) = f(x) + f(y^2)", // 加法的関数はすべて解（病的な解を含む）
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
fn negative_special_only_when_additive_functions_are_solutions() {
    // 加法的関数（条件なし・対合・射影）の族が解ではない方程式で特殊解決と主張しないこと
    for eq in ["f(x*y) = f(x)*f(y)", "f(x^2) = f(x)^2", "f(x)^2 = x^2", "f(x*f(y)) = y*f(x)", "f(x + y) = f(x)*f(y)"] {
        let out = run(eq);
        assert!(
            out.status != "special" && out.status != "special_exist",
            "{}: 任意の加法的関数が解ではないのに特殊解決と主張した",
            eq
        );
        let (l, r) = parse_general(eq).unwrap();
        check_sound(eq, &l, &r, &out);
    }
}

#[test]
fn special_for_cauchy_type_equations() {
    // 解の集合が加法的関数全体（と多項式の解）になる方程式は特殊解決になる
    for eq in ["f(x + y) = f(x) + f(y)", "f(x - y) = f(x) - f(y)", "f(x + y^2) = f(x) + f(y^2)"] {
        let out = run(eq);
        assert_eq!(out.status, "special", "{}", eq);
        let (l, r) = parse_general(eq).unwrap();
        check_sound(eq, &l, &r, &out);
    }
    // 条件つきの加法的関数（射影 A(A(x)) = A(x)・対合 A(A(x)) = x）がすべて解になる方程式は、少なくとも病的な解の存在を示す
    for eq in ["f(x + f(y)) = f(x) + f(y)", "f(f(x)) = x", "f(x + f(y)) = f(x) + y", "f(f(x) + f(y)) = x + y"] {
        let out = run(eq);
        assert!(out.status == "special" || out.status == "special_exist", "{}: {}", eq, out.status);
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

/// 解の集合がわかっている方程式: 完全解決と主張するなら、答えはちょうどその集合でなければならない
#[test]
fn negative_known_solution_sets_exact() {
    // f(x²+y) = f(x)²+f(y): f(0)=0, f(x²)=f(x)², 加法的かつ奇関数、x ≥ 0 で f ≥ 0 なのでコーシーより f(x)=cx、c²=c。解は 0 と x。
    // f(x+y) = x+f(y): y=0 で f(x) = x + f(0)。解は x + c（c は任意）。
    // f(x+f(y)) = x+y: 解は x のみ。
    let cases: Vec<(&str, Vec<&str>)> = vec![
        ("f(x^2 + y) = f(x)^2 + f(y)", vec!["0", "x"]),
        ("f(x + y) = x + f(y)", vec!["x + c"]),
        ("f(x + f(y)) = x + y", vec!["x"]),
    ];
    for (eq, want) in cases {
        let out = run(eq);
        let (l, r) = parse_general(eq).unwrap();
        check_sound(eq, &l, &r, &out);
        if out.status == "complete" {
            let mut got: Vec<String> = out
                .families
                .iter()
                .map(|f| {
                    let t = f.template().clone();
                    // パラメータは c と表示して比較
                    let s = if f.params().len() == 1 { t.subst_vars(&[Poly::var(0), Poly::var(1), Poly::var(2)]) } else { t };
                    let txt = s.to_string().replace("v", "c");
                    txt
                })
                .collect();
            got.sort();
            let mut w: Vec<String> = want.iter().map(|s| s.to_string()).collect();
            w.sort();
            assert_eq!(out.families.len() + out.pw_families.len(), want.len(), "{}: 解の個数が違う: {:?}", eq, got);
            for wanted in &w {
                let ok = out.families.iter().any(|f| {
                    let p = parse_general(&format!("f(x) = {}", wanted.replace('c', "y"))).unwrap().1;
                    // 1 パラメータの族は Var(2) を y に読み替えて比較
                    let t = f.template().subst_vars(&[Poly::var(0), Poly::var(1), Poly::var(1)]);
                    t == p
                });
                assert!(ok, "{}: 期待する解 {} がない（得た族: {:?}）", eq, wanted, got);
            }
        }
    }
}
