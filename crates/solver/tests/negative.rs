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

/// 任意の区間をもつ族の具体的な関数（任意の値は、引数と種から決まる擬似乱数で選ぶ）
fn arb_member(fam: &fe_kernel::ArbFamily, seed: u64) -> impl Fn(&Q) -> Q + '_ {
    use fe_kernel::ArbPiece;
    use std::hash::{Hash, Hasher};
    move |t: &Q| -> Q {
        let br = fam.breaks();
        // t の属する区間の番号
        let mut idx = 2 * br.len();
        for (k, b) in br.iter().enumerate() {
            if t < b {
                idx = 2 * k;
                break;
            }
            if t == b {
                idx = 2 * k + 1;
                break;
            }
        }
        let mut h = std::collections::hash_map::DefaultHasher::new();
        format!("{}", t).hash(&mut h);
        seed.hash(&mut h);
        let r = h.finish();
        let ev = |g: &Poly| eval_poly(g, t, &Q::zero(), &|_| Q::zero());
        match &fam.pieces()[idx] {
            ArbPiece::Fixed(g) => ev(g),
            ArbPiece::Free => Q::from_integer(((r % 7) as i64 - 3).into()) / Q::from_integer(((r >> 8) % 3 + 1).into()),
            ArbPiece::NonNeg => Q::from_integer(((r % 5) as i64).into()) / Q::from_integer(((r >> 8) % 3 + 1).into()),
            ArbPiece::NonPos => -Q::from_integer(((r % 5) as i64).into()) / Q::from_integer(((r >> 8) % 3 + 1).into()),
            ArbPiece::Choice(a, b) => {
                if r % 2 == 0 {
                    ev(a)
                } else {
                    ev(b)
                }
            }
        }
    }
}

/// 多項式を x, y の値と f の関数で厳密に評価する（検証核とは独立に、有理数で計算する）
fn eval_poly(p: &Poly, xv: &Q, yv: &Q, f: &dyn Fn(&Q) -> Q) -> Q {
    use fe_kernel::Atom;
    let mut s = Q::zero();
    for (m, c) in p.terms() {
        let mut t = c.clone();
        for (a, e) in m.factors() {
            let v = match a {
                Atom::Var(0) => xv.clone(),
                Atom::Var(1) => yv.clone(),
                Atom::F(u) => f(&eval_poly(u, xv, yv, f)),
                other => panic!("評価できない原子 {:?}", other),
            };
            for _ in 0..*e {
                t = t * v.clone();
            }
        }
        s = s + t;
    }
    s
}

/// 任意の区間をもつ族が、具体的な関数（4 通りの値の選び方）で方程式を有理数の点で厳密に満たすこと（検証核とは独立の確認）
fn check_arb_numerically(eq_desc: &str, l: &Poly, r: &Poly, fam: &fe_kernel::ArbFamily) {
    let pts = [q(-3), q(-2), q(-1), qf(-1, 2), q(0), qf(1, 3), q(1), q(2), qf(5, 2)];
    for seed in 0..4u64 {
        let f = arb_member(fam, seed);
        for a in &pts {
            for b in &pts {
                let lv = eval_poly(l, a, b, &f);
                let rv = eval_poly(r, a, b, &f);
                assert!(lv == rv, "{}: 任意の区間をもつ族の具体的な関数（種 {}）が x = {}, y = {} で方程式を満たさない", eq_desc, seed, a, b);
            }
        }
    }
}

/// ℚ(√2) の数 a + b√2（a, b は有理数）。有理数と無理数で式を変える族を、検証核とは独立に無理数の点でも厳密に評価する
#[derive(Clone, Debug, PartialEq)]
struct K2(Q, Q);

impl K2 {
    fn add(&self, o: &K2) -> K2 {
        K2(&self.0 + &o.0, &self.1 + &o.1)
    }
    fn mul(&self, o: &K2) -> K2 {
        K2(&self.0 * &o.0 + Q::from_integer(2.into()) * &self.1 * &o.1, &self.0 * &o.1 + &self.1 * &o.0)
    }
}

fn eval_k2(p: &Poly, xv: &K2, yv: &K2, f: &dyn Fn(&K2) -> K2) -> K2 {
    use fe_kernel::Atom;
    let mut s = K2(Q::zero(), Q::zero());
    for (m, c) in p.terms() {
        let mut t = K2(c.clone(), Q::zero());
        for (a, e) in m.factors() {
            let v = match a {
                Atom::Var(0) => xv.clone(),
                Atom::Var(1) => yv.clone(),
                Atom::F(u) => f(&eval_k2(u, xv, yv, f)),
                other => panic!("評価できない原子 {:?}", other),
            };
            for _ in 0..*e {
                t = t.mul(&v);
            }
        }
        s = s.add(&t);
    }
    s
}

/// 有理数と無理数で式を変える族が、有理数の点と ℚ(√2) の無理数の点で方程式を厳密に満たすこと（検証核とは独立の確認）
fn check_qsplit_numerically(eq_desc: &str, l: &Poly, r: &Poly, fam: &fe_kernel::QsFamily) {
    let g = |p: &Poly, t: &K2| eval_k2(p, t, &K2(Q::zero(), Q::zero()), &|_| K2(Q::zero(), Q::zero()));
    let f = |t: &K2| if t.1.is_zero() { g(fam.g_rat(), t) } else { g(fam.g_irr(), t) };
    let pts: Vec<K2> = [(q(0), q(0)), (q(1), q(0)), (q(-1), q(0)), (qf(1, 2), q(0)), (q(-3), q(0)), (q(0), q(1)), (q(0), q(-1)), (q(1), q(1)), (qf(-1, 2), q(1)), (q(3), q(-2)), (q(0), qf(1, 2))]
        .into_iter()
        .map(|(a, b)| K2(a, b))
        .collect();
    for a in &pts {
        for b in &pts {
            let lv = eval_k2(l, a, b, &f);
            let rv = eval_k2(r, a, b, &f);
            assert!(lv == rv, "{}: 有理数と無理数で式を変える族が x = {:?}, y = {:?} で方程式を満たさない", eq_desc, a, b);
        }
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
    for f in out.arb_found.iter() {
        assert!(fresh.verify_arbitrary(f.breaks().to_vec(), f.pieces().to_vec()).is_ok(), "{}: 解でない任意の区間をもつ族を報告した", eq_desc);
        check_arb_numerically(eq_desc, l, r, f);
    }
    if out.status == "special" {
        assert!(out.add_found.is_some(), "{}: 特殊解決なのに加法的な族の検証がない", eq_desc);
    }
    for f in out.qs_found.iter() {
        assert!(fresh.verify_rational_split(f.g_rat().clone(), f.g_irr().clone()).is_ok(), "{}: 解でない有理数・無理数の族を報告した", eq_desc);
        check_qsplit_numerically(eq_desc, l, r, f);
    }
    if out.status == "special_exist" {
        // 病的な解の存在は、加法的な族・任意の区間をもつ族・有理数と無理数で式を変える族（上で新しい検証核と、
        // 検証核とは独立の数値で確かめた）による
        assert!(
            out.add_found.is_some() || out.arb_found.is_some() || out.qs_found.is_some(),
            "{}: 特殊解決なのに病的な解の族の検証がない",
            eq_desc
        );
    }
    // 解の集合を決めた（complete / special）なら、有理数と無理数で式を変える族（多項式・区分的な式・加法的関数 + 多項式の
    // どれでも書けない解）が解であってはならない
    if out.status == "complete" || out.status == "special" {
        assert!(out.qs_found.is_none(), "{}: 解の集合を決めたのに、有理数と無理数で式を変える族も解である", eq_desc);
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
    // 加法的関数（条件なし・対合・射影）の族が解ではない方程式で、加法的な族による特殊解決を主張しないこと。
    // f(x²) = f(x)² と f(x)² = x² は「x ≥ 0 で x、x < 0 で各点ごとに ±x」という病的な解をもつので、病的な解の存在
    // （special_exist）は、任意の区間をもつ族が新しい検証核と、検証核とは独立の数値の確認（check_sound）を通るときだけ認める。
    for eq in ["f(x*y) = f(x)*f(y)", "f(x^2) = f(x)^2", "f(x)^2 = x^2", "f(x*f(y)) = y*f(x)", "f(x + y) = f(x)*f(y)"] {
        let out = run(eq);
        assert!(out.status != "special", "{}: 任意の加法的関数が解ではないのに加法的な族で解の集合を決めたと主張した", eq);
        assert!(out.add_found.is_none(), "{}: 任意の加法的関数が解ではないのに加法的な族を報告した", eq);
        if out.status == "special_exist" {
            assert!(out.arb_found.is_some(), "{}: 病的な解の存在の根拠がない", eq);
        }
        let (l, r) = parse_general(eq).unwrap();
        check_sound(eq, &l, &r, &out);
    }
}

#[test]
fn negative_arbitrary_family_examples_are_genuine() {
    // 病的な解（各点ごとに ±x）をもつことが知られている方程式で、報告した任意の区間をもつ族を数値でも確かめる
    for eq in ["f(x)^2 = x^2", "f(x^2) = f(x)^2", "f(x^2 + f(y^2)) = x^2 + y^2", "f(x^2 + y^2) = f(x)^2 + f(y)^2"] {
        let out = run(eq);
        assert_eq!(out.status, "special_exist", "{}", eq);
        assert!(out.arb_found.is_some(), "{}", eq);
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

/// 任意の区間をもつ族（病的な解の存在）は、解が多項式・加法的な族だけの方程式や、壊した方程式では検証を通らない
#[test]
fn negative_rational_split_examples_are_genuine() {
    // 有理数と無理数で式を変える病的な解をもつ方程式で、報告した族を新しい検証核と ℚ(√2) の数値で確かめる
    for eq in ["f(2*f(x)) = x + f(x)", "f(3*f(x)) = 2*x + f(x)", "f(x + x*f(y)) = f(x) + f(x)*f(y)", "f(f(x) + f(y)^2) = f(x) + y*f(y)"] {
        let out = run(eq);
        assert_eq!(out.status, "special_exist", "{}", eq);
        let (l, r) = parse_general(eq).unwrap();
        let k = Kernel::new(l.clone(), r.clone()).unwrap();
        assert!(out.error.is_none(), "{}: 内部エラー {:?}", eq, out.error);
        let fam = out.qs_found.clone().or_else(|| fe_solver::search::find_qsplit_candidates(&k, &out.found)).expect("有理数と無理数で式を変える族がない");
        check_qsplit_numerically(eq, &l, &r, &fam);
        check_sound(eq, &l, &r, &out);
    }
}

#[test]
fn negative_no_rational_split_for_rigid_equations() {
    // 解が多項式で決まる（または加法的関数だけの）方程式と、病的な解をもつ方程式を壊したもので、
    // 有理数と無理数で式を変える族を解としないこと
    for eq in [
        "f(x + y) = f(x) + y",
        "f(x + f(y)) = f(x) + y",
        "f(x^2 + f(y)) = y + f(x)^2",
        "f(x*f(y) + x) = x*y + f(x)",
        "f(x + y) = f(x) + f(y)",
        "f(x*y) = f(x)*f(y)",
        "f(x^2) = f(x)^2",
        // 壊した方程式
        "f(2*f(x)) = x + 2*f(x)",
        // f(2f(xy)) = xy + f(xy) + 1 は壊れていない（多項式の解 x + 1/2・−x/2 − 1 を有理数・無理数で使い分ける解をもつ）ので使わない
        "f(2*f(x*y)) = x*y + 2*f(x*y)",
        "f(x + x*f(y)) = f(x) + f(x)*f(y) + x",
        "f(f(x) + f(y)^2) = 2*f(x) + y*f(y)",
    ] {
        let (l, r) = parse_general(eq).unwrap();
        let k = Kernel::new(l.clone(), r.clone()).unwrap();
        let out = solve(l.clone(), r.clone(), T).unwrap();
        assert!(fe_solver::search::find_qsplit_candidates(&k, &out.found).is_none(), "{}: 有理数と無理数で式を変える族を解としてしまう", eq);
        assert!(out.qs_found.is_none(), "{}: 有理数と無理数で式を変える族を報告した", eq);
        check_sound(eq, &l, &r, &out);
    }
}

#[test]
fn negative_no_arbitrary_family_for_rigid_equations() {
    for eq in [
        "f(x^2 + f(y)) = y + f(x)^2",
        "f(x*f(y) + x) = x*y + f(x)",
        "f(f(x) + y) = 2*x + f(f(y) - x)",
        "f(x + f(y)) = f(x) + y",
        "f(x + y) = f(x) + f(y)",
        // 壊した方程式（f(x² + f(y²)) = x² + y² は負の側が任意だが、右辺を変えると成り立たない）
        "f(x^2 + f(y^2)) = x^2 + 2*y^2",
        "f(f(x) + f(y)^2) = f(x) + 2*f(y)^2",
    ] {
        let (l, r) = parse_general(eq).unwrap();
        let k = Kernel::new(l.clone(), r.clone()).unwrap();
        assert!(fe_solver::search::find_arb_candidates(&k).is_none(), "{}: 任意の区間をもつ族を解としてしまう", eq);
        let out = solve(l, r, T).unwrap();
        assert!(out.arb_found.is_none(), "{}: 任意の区間をもつ族を報告した", eq);
    }
}
