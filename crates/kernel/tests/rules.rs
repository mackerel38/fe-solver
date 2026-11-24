//! 検証核の推論規則ごとのテスト。各規則について、正しい使い方で期待どおりの節が出ること、
//! 誤った使い方（前提の形が違う・スコープ外の定数・別の枝の事実など）が拒否されることを確かめる。

use fe_kernel::poly::{q, qf};
use fe_kernel::{Clause, Kernel, Lit, Poly, Rel, ROOT};

fn x() -> Poly {
    Poly::var(0)
}
fn y() -> Poly {
    Poly::var(1)
}
fn f(p: Poly) -> Poly {
    Poly::f(p)
}
fn c(n: i64) -> Poly {
    Poly::int(n)
}
fn cl(nvars: u32, lits: Vec<Lit>) -> Clause {
    Clause::new(nvars, lits).unwrap()
}

/// f(x + f(y)) = x + y
fn k_fxfy() -> Kernel {
    Kernel::new(f(x().add(&f(y()))), x().add(&y())).unwrap()
}
/// f(x + y) = x + y
fn k_simple() -> Kernel {
    Kernel::new(f(x().add(&y())), x().add(&y())).unwrap()
}

#[test]
fn axiom_is_the_equation() {
    let k = k_fxfy();
    let a = k.axiom();
    assert_eq!(*k.clause(a), cl(2, vec![Lit::eq(f(x().add(&f(y()))).sub(&x()).sub(&y()))]));
}

#[test]
fn kernel_rejects_equation_with_constants_or_extra_vars() {
    assert!(Kernel::new(f(Poly::var(2)), x()).is_err());
    assert!(Kernel::new(f(Poly::cnst(0)), x()).is_err());
    assert!(Kernel::new(Poly::inv(x()), x()).is_err());
}

#[test]
fn instantiate_ok_and_errors() {
    let mut k = k_fxfy();
    let a = k.axiom();
    // P(0, y): f(f(y)) = y   （新しい節の変数は y を Var(0) として 1 個）
    let p = k.instantiate(ROOT, a, vec![c(0), x()], 1).unwrap();
    assert_eq!(*k.clause(p), cl(1, vec![Lit::eq(f(f(x())).sub(&x()))]));
    // 代入の個数が違う
    assert!(k.instantiate(ROOT, a, vec![c(0)], 1).is_err());
    // 範囲外の変数
    assert!(k.instantiate(ROOT, a, vec![c(0), y()], 1).is_err());
    // 存在しない定数
    assert!(k.instantiate(ROOT, a, vec![Poly::cnst(0), x()], 1).is_err());
    // f を含む式を代入してよい: P(x - f(y), y): f(x) = x - f(y) + y
    let p2 = k.instantiate(ROOT, a, vec![x().sub(&f(y())), y()], 2).unwrap();
    assert_eq!(*k.clause(p2), cl(2, vec![Lit::eq(f(x()).sub(&x()).add(&f(y())).sub(&y()))]));
}

#[test]
fn lincomb_ok_and_errors() {
    let mut k = k_fxfy();
    let a = k.axiom();
    let p1 = k.instantiate(ROOT, a, vec![x().sub(&f(y())), y()], 2).unwrap(); // f(x) - x + f(y) - y = 0
    let p2 = k.instantiate(ROOT, p1, vec![x(), c(0)], 1).unwrap(); // f(x) - x + f(0) = 0
    // p1(x,y) - p2(x) = f(y) - y - f(0)
    let r = k.lincomb(ROOT, 2, vec![(c(1), p1, 0), (c(-1), p2, 0)]).unwrap();
    assert_eq!(*k.clause(r), cl(2, vec![Lit::eq(f(y()).sub(&y()).sub(&f(c(0))))]));
    // 多項式係数
    let r2 = k.lincomb(ROOT, 1, vec![(x(), p2, 0)]).unwrap();
    assert_eq!(*k.clause(r2), cl(1, vec![Lit::eq(x().mul(&f(x())).sub(&x().pow(2)).add(&x().mul(&f(c(0)))))]));
    // 前提の変数が多すぎる
    assert!(k.lincomb(ROOT, 1, vec![(c(1), p1, 0)]).is_err());
    // 不等式リテラルには使えない
    let sq = k.pos_comb(ROOT, 1, vec![], vec![], vec![(q(1), x())], q(0), false).unwrap();
    assert!(k.lincomb(ROOT, 1, vec![(c(1), sq, 0)]).is_err());
    // 側リテラルが引き継がれる
    let t = k.trichotomy(ROOT, 1, x()).unwrap(); // x>0 | x=0 | -x>0
    let eq_idx = k.clause(t).lits().iter().position(|l| l.rel() == Rel::Eq).unwrap();
    let r3 = k.lincomb(ROOT, 1, vec![(c(2), t, eq_idx)]).unwrap();
    assert_eq!(k.clause(r3).lits().len(), 3);
}

#[test]
fn congruence_ok_and_errors() {
    let mut k = k_fxfy();
    let a = k.axiom();
    let ffy = k.instantiate(ROOT, a, vec![c(0), x()], 1).unwrap(); // f(f(x)) - x = 0
    // f(u + 1·(f(f(x)) - x)) = f(u) で u = x: f(f(f(x))) = f(x)
    let r = k.congruence(ROOT, 1, x(), vec![(c(1), ffy, 0)]).unwrap();
    assert_eq!(*k.clause(r), cl(1, vec![Lit::eq(f(f(f(x()))).sub(&f(x())))]));
    // 乗数つき・複数前提: f(y + 2(f(f(y)) - y)) と f(y) が等しい
    let ffy2 = k.instantiate(ROOT, a, vec![c(0), y()], 2).unwrap();
    let r2 = k.congruence(ROOT, 2, y(), vec![(c(2), ffy2, 0), (c(1), ffy, 0)]).unwrap();
    let arg = y().add(&f(f(y())).sub(&y()).scale(&q(2))).add(&f(f(x())).sub(&x()));
    assert_eq!(*k.clause(r2), cl(2, vec![Lit::eq(f(arg).sub(&f(y())))]));
    let sq = k.pos_comb(ROOT, 1, vec![], vec![], vec![(q(1), x())], q(0), false).unwrap();
    assert!(k.congruence(ROOT, 1, x(), vec![(c(1), sq, 0)]).is_err());
    // 範囲外の変数を base に使えない
    assert!(k.congruence(ROOT, 1, y(), vec![(c(1), ffy, 0)]).is_err());
    // 前提の変数が多すぎる
    assert!(k.congruence(ROOT, 1, x(), vec![(c(1), ffy2, 0)]).is_err());
    assert!(k.congruence(ROOT, 1, x(), vec![]).is_err());
}

#[test]
fn eq_or_ne_rule() {
    let mut k = k_simple();
    let e = k.eq_or_ne(ROOT, 1, x().sub(&c(2))).unwrap();
    assert_eq!(*k.clause(e), cl(1, vec![Lit::eq(x().sub(&c(2))), Lit::ne(x().sub(&c(2)))]));
    assert!(k.eq_or_ne(ROOT, 1, y()).is_err());
    // 条件付き代入の例: x = 0 ∨ f(x) = x と f(0) = 0 から f(x) = x
    let k2 = Kernel::new(f(x().mul(&y())), x().mul(&f(y()))).unwrap();
    let mut k2 = k2;
    let a = k2.axiom();
    let p1 = k2.instantiate(ROOT, a, vec![x(), c(1)], 1).unwrap(); // f(x) = x f(1)
    let p0 = k2.instantiate(ROOT, a, vec![c(0), c(0)], 0).unwrap(); // f(0) = 0
    let em = k2.eq_or_ne(ROOT, 1, x()).unwrap(); // x = 0 ∨ x ≠ 0
    let ei = k2.clause(em).lits().iter().position(|l| l.rel() == Rel::Eq).unwrap();
    // x = 0 なら f(x) = f(0): congruence(base 0, 1·x)
    let cg = k2.congruence(ROOT, 1, c(0), vec![(c(1), em, ei)]).unwrap(); // f(x) - f(0) = 0 ∨ x ≠ 0
    let ci = k2.clause(cg).lits().iter().position(|l| l.rel() == Rel::Eq).unwrap();
    let lc = k2.lincomb(ROOT, 1, vec![(c(1), cg, ci), (c(1), p0, 0)]).unwrap(); // f(x) = 0 ∨ x ≠ 0
    assert_eq!(*k2.clause(lc), cl(1, vec![Lit::eq(f(x())), Lit::ne(x())]));
    let _ = p1;
}

#[test]
fn zero_product_and_nonzero_factor() {
    let mut k = k_simple();
    let a = k.axiom();
    let p = k.instantiate(ROOT, a, vec![x(), c(0)], 1).unwrap(); // f(x) - x = 0
    let m = k.lincomb(ROOT, 1, vec![(x(), p, 0)]).unwrap(); // x f(x) - x^2 = 0
    let z = k.zero_product(ROOT, m, 0, vec![x(), f(x()).sub(&x())]).unwrap();
    assert_eq!(*k.clause(z), cl(1, vec![Lit::eq(x()), Lit::eq(f(x()).sub(&x()))]));
    // 定数倍のずれは許す
    assert!(k.zero_product(ROOT, m, 0, vec![x().scale(&q(2)), f(x()).sub(&x())]).is_ok());
    // 積が一致しない
    assert!(k.zero_product(ROOT, m, 0, vec![x(), f(x())]).is_err());
    // ≠ には使えない / NonzeroFactor は ≠ のみ
    let t = k.trichotomy(ROOT, 1, x().mul(&y().add(&c(1)))).unwrap_err();
    assert!(t.contains("範囲外"));
    let (_, _, c1, hs, _) = k.split_em(ROOT, cl(1, vec![Lit::eq(x().mul(&f(x())))])).unwrap();
    // 子1: a·f(a) ≠ 0
    let h = hs[0];
    let a0 = Poly::cnst(0);
    let nf = k.nonzero_factor(c1, h, 0, vec![a0.clone(), f(a0.clone())], 1).unwrap();
    assert_eq!(*k.clause(nf), cl(0, vec![Lit::ne(f(a0.clone()))]));
    assert!(k.nonzero_factor(c1, h, 0, vec![a0.clone(), a0.clone()], 1).is_err());
    assert!(k.zero_product(c1, h, 0, vec![a0.clone(), f(a0)]).is_err());
}

#[test]
fn resolve_ok_and_errors() {
    let mut k = k_simple();
    let t = k.trichotomy(ROOT, 1, x()).unwrap(); // x > 0 | x = 0 | -x > 0
    let sq = k.pos_comb(ROOT, 1, vec![], vec![], vec![(q(1), x())], q(0), false).unwrap(); // x^2 >= 0
    // -x > 0 と x >= 0 は否定どうし。x >= 0 はまだないので、x^2 では消せない
    let gt_neg = k.clause(t).lits().iter().position(|l| *l == Lit::gt(x().neg())).unwrap();
    assert!(k.resolve(ROOT, t, gt_neg, sq, 0).is_err());
    // x ≥ 0 を作って解消
    let (c0, h0, _c1, _hs, _) = k.split_em(ROOT, cl(1, vec![Lit::ge(f(x()))])).unwrap();
    let _ = h0;
    let ge = k.pos_comb(c0, 1, vec![(q(1), h0, 0)], vec![], vec![], q(0), false).unwrap(); // f(x) >= 0
    let t2 = k.trichotomy(c0, 1, f(x())).unwrap();
    let li = k.clause(t2).lits().iter().position(|l| *l == Lit::gt(f(x()).neg())).unwrap();
    let r = k.resolve(c0, t2, li, ge, 0).unwrap();
    assert_eq!(*k.clause(r), cl(1, vec![Lit::gt(f(x())), Lit::eq(f(x()))]));
}

#[test]
fn trichotomy_and_strict_ne() {
    let mut k = k_simple();
    let t = k.trichotomy(ROOT, 1, x().sub(&c(1))).unwrap();
    assert_eq!(k.clause(t).lits().len(), 3);
    let gt = k.pos_comb(ROOT, 1, vec![], vec![], vec![(q(1), x())], q(1), true).unwrap(); // x^2 + 1 > 0
    let ne = k.strict_ne(ROOT, gt, 0).unwrap();
    assert_eq!(*k.clause(ne), cl(1, vec![Lit::ne(x().pow(2).add(&c(1)))]));
    let ge = k.pos_comb(ROOT, 1, vec![], vec![], vec![(q(1), x())], q(0), false).unwrap();
    assert!(k.strict_ne(ROOT, ge, 0).is_err());
}

#[test]
fn pos_comb_rules() {
    let mut k = k_simple();
    // 平方の和: (x - 1)^2 + 2 > 0
    let r = k.pos_comb(ROOT, 1, vec![], vec![], vec![(q(1), x().sub(&c(1)))], q(2), true).unwrap();
    assert_eq!(*k.clause(r), cl(1, vec![Lit::gt(x().pow(2).sub(&x().scale(&q(2))).add(&c(3)))]));
    // 負の係数は不可
    assert!(k.pos_comb(ROOT, 1, vec![], vec![], vec![(q(-1), x())], q(0), false).is_err());
    assert!(k.pos_comb(ROOT, 1, vec![], vec![], vec![], q(-1), false).is_err());
    // 根拠のない strict は不可
    assert!(k.pos_comb(ROOT, 1, vec![], vec![], vec![(q(1), x())], q(0), true).is_err());
    // 矛盾の検出: -1 ≥ 0 は偽のリテラルなので空節になる（等式で打ち消して定数にする）
    let a = k.axiom();
    let p = k.instantiate(ROOT, a, vec![x(), c(0)], 1).unwrap(); // f(x) - x = 0
    let r2 = k.pos_comb(ROOT, 1, vec![], vec![(c(1), p, 0)], vec![], q(0), false).unwrap();
    assert!(k.clause(r2).lits()[0].rel() == Rel::Ge);
    // 根の枝はまだ閉じていない
    assert!(!k.is_closed(ROOT));
}

#[test]
fn contradiction_closes_branch() {
    let mut k = k_simple();
    let a = k.axiom();
    // 子1: f(0) ≠ 0 を仮定。P(0,0): f(0) = 0 と合わせて矛盾。
    let (c0, _h0, c1, hs, _) = k.split_em(ROOT, cl(0, vec![Lit::eq(f(c(0)))])).unwrap();
    let p00 = k.instantiate(c1, a, vec![c(0), c(0)], 0).unwrap(); // f(0) = 0
    let r = k.resolve(c1, p00, 0, hs[0], 0).unwrap();
    assert!(k.clause(r).is_false());
    assert!(k.is_closed(c1));
    assert!(!k.is_closed(c0));
    assert!(!k.is_closed(ROOT));
}

#[test]
fn mul_ineq_rule() {
    let mut k = k_simple();
    let s1 = k.pos_comb(ROOT, 2, vec![], vec![], vec![(q(1), x())], q(1), true).unwrap(); // x^2+1 > 0
    let s2 = k.pos_comb(ROOT, 2, vec![], vec![], vec![(q(1), y())], q(0), false).unwrap(); // y^2 >= 0
    let m = k.mul_ineq(ROOT, s1, 0, s2, 0).unwrap();
    assert_eq!(*k.clause(m), cl(2, vec![Lit::ge(x().pow(2).add(&c(1)).mul(&y().pow(2)))]));
    let s3 = k.pos_comb(ROOT, 2, vec![], vec![], vec![(q(1), y())], q(1), true).unwrap();
    let m2 = k.mul_ineq(ROOT, s1, 0, s3, 0).unwrap();
    assert_eq!(k.clause(m2).lits()[0].rel(), Rel::Gt);
    let a = k.axiom();
    assert!(k.mul_ineq(ROOT, a, 0, s1, 0).is_err());
}

#[test]
fn square_range_rule() {
    // f(x^2 + y) = x^2 + f(y)
    let mut k = Kernel::new(f(x().pow(2).add(&y())), x().pow(2).add(&f(y()))).unwrap();
    let a = k.axiom();
    let p = k.instantiate(ROOT, a, vec![x(), c(0)], 1).unwrap(); // f(x^2) - x^2 - f(0) = 0
    let pre = cl(1, vec![Lit::eq(f(x()).sub(&x()).sub(&f(c(0))))]);
    let r = k.square_range(ROOT, p, 0, pre).unwrap();
    assert_eq!(
        *k.clause(r),
        cl(1, vec![Lit::eq(f(x()).sub(&x()).sub(&f(c(0)))), Lit::gt(x().neg())])
    );
    // 形が合わない（x が x^2 以外の形でも現れる）
    let q2 = k.instantiate(ROOT, a, vec![x(), x()], 1).unwrap(); // f(x^2 + x) - x^2 - f(x)
    let bad = cl(1, vec![Lit::eq(f(x().add(&x())).sub(&x()).sub(&f(x())))]);
    assert!(k.square_range(ROOT, q2, 0, bad).is_err());
    // 偽の前提形（符号違い）も不可
    let bad2 = cl(1, vec![Lit::eq(f(x()).add(&x()).sub(&f(c(0))))]);
    assert!(k.square_range(ROOT, p, 0, bad2).is_err());
}

#[test]
fn inv_axiom_and_weaken() {
    let mut k = k_simple();
    let i = k.inv_axiom(ROOT, 1, x()).unwrap();
    assert_eq!(*k.clause(i), cl(1, vec![Lit::eq(x()), Lit::eq(x().mul(&Poly::inv(x())).sub(&c(1)))]));
    let a = k.axiom();
    let w = k.weaken(ROOT, a, vec![Lit::eq(x().sub(&c(3)))], 2).unwrap();
    assert_eq!(k.clause(w).lits().len(), 2);
    assert!(k.weaken(ROOT, a, vec![], 1).is_err());
}

#[test]
fn split_components_rejects_pointwise_disjunction() {
    // f(x^2) = f(x)^2 型の各点ごとの選言「f(x) = 0 ∨ f(x) = x」を全体の場合分けに使えないこと
    let mut k = Kernel::new(f(x().mul(&y())), f(x()).mul(&f(y()))).unwrap();
    let (c0, h0, _c1, _hs, _) = k
        .split_em(ROOT, cl(1, vec![Lit::eq(f(x())), Lit::eq(f(x()).sub(&x()))]))
        .unwrap();
    assert!(k.split_components(c0, h0).is_err(), "同じ変数を共有する選言は分けられない");
    // 変数を共有しない選言は分けられる: ∀x,y. f(x) = 0 ∨ f(y) = y
    let mut k2 = Kernel::new(f(x().mul(&y())), f(x()).mul(&f(y()))).unwrap();
    let (d0, g0, _d1, _gs, _) = k2.split_em(ROOT, cl(2, vec![Lit::eq(f(x())), Lit::eq(f(y()).sub(&y()))])).unwrap();
    let ch = k2.split_components(d0, g0).unwrap();
    assert_eq!(ch.len(), 2);
    let hyps: Vec<Clause> = ch.iter().map(|(_, h)| k2.clause(*h).clone()).collect();
    assert!(hyps.contains(&cl(2, vec![Lit::eq(f(x()))])));
    assert!(hyps.contains(&cl(2, vec![Lit::eq(f(y()).sub(&y()))])));
    // 同じ枝は二度分けられない
    assert!(k2.split_components(d0, g0).is_err());
}

#[test]
fn constants_are_scoped_to_their_branch() {
    let mut k = k_simple();
    let a = k.axiom();
    let (c0, _h0, c1, _hs, consts) = k.split_em(ROOT, cl(1, vec![Lit::eq(f(x()).sub(&x()))])).unwrap();
    assert_eq!(consts.len(), 1);
    let ac = Poly::cnst(consts[0]);
    // 子1 では使える
    assert!(k.instantiate(c1, a, vec![ac.clone(), c(0)], 0).is_ok());
    // 兄弟の子0 や親では使えない
    assert!(k.instantiate(c0, a, vec![ac.clone(), c(0)], 0).is_err());
    assert!(k.instantiate(ROOT, a, vec![ac.clone(), c(0)], 0).is_err());
    // 子1 の事実を子0 で使えない
    let p = k.instantiate(c1, a, vec![x(), c(0)], 1).unwrap();
    assert!(k.lincomb(c0, 1, vec![(c(1), p, 0)]).is_err());
}

#[test]
fn merge_rules() {
    let mut k = k_simple();
    let a = k.axiom();
    let (c0, _h0, c1, _hs, consts) = k.split_em(ROOT, cl(0, vec![Lit::eq(f(c(1)).sub(&c(1)))])).unwrap();
    assert!(consts.is_empty());
    let p0 = k.instantiate(c0, a, vec![x(), c(0)], 1).unwrap();
    let p1 = k.instantiate(c1, a, vec![x(), c(0)], 1).unwrap();
    let p1b = k.instantiate(c1, a, vec![c(0), x()], 1).unwrap(); // 同じ内容（x+0 と 0+x）
    let m = k.merge(ROOT, vec![Some(p0), Some(p1b)]).unwrap();
    assert_eq!(k.fact(m).branch(), ROOT);
    let _ = p1;
    // 内容が違うと不可
    let q1 = k.instantiate(c1, a, vec![x(), x()], 1).unwrap();
    assert!(k.merge(ROOT, vec![Some(p0), Some(q1)]).is_err());
    // 閉じていない子を None にできない
    assert!(k.merge(ROOT, vec![Some(p0), None]).is_err());
    // 子の定数を含む事実は親に持ち上げられない
    let mut k2 = k_simple();
    let a2 = k2.axiom();
    let (e0, _g0, e1, _gs, cs) = k2.split_em(ROOT, cl(1, vec![Lit::eq(f(x()).sub(&x()))])).unwrap();
    let ac = Poly::cnst(cs[0]);
    let r1 = k2.instantiate(e1, a2, vec![ac.clone(), c(0)], 0).unwrap();
    let r0 = k2.weaken(e0, a2, vec![], 2);
    assert!(r0.is_ok());
    let _ = r1;
    // 子0 では ac は使えないので、同じ節を子0 で作れない → merge 不可
    assert!(k2.instantiate(e0, a2, vec![ac, c(0)], 0).is_err());
}

#[test]
fn merge_with_closed_child() {
    let mut k = k_simple();
    let a = k.axiom();
    let (c0, _h0, c1, hs, _) = k.split_em(ROOT, cl(0, vec![Lit::eq(f(c(0)))])).unwrap();
    let p00 = k.instantiate(c1, a, vec![c(0), c(0)], 0).unwrap();
    let r = k.resolve(c1, p00, 0, hs[0], 0).unwrap();
    assert!(k.clause(r).is_false());
    let p = k.instantiate(c0, a, vec![x(), c(0)], 1).unwrap();
    let m = k.merge(ROOT, vec![Some(p), None]).unwrap();
    assert_eq!(k.fact(m).branch(), ROOT);
}

#[test]
fn verify_solution_rule() {
    let k = k_simple();
    assert!(k.verify_solution(&x()).is_ok());
    assert!(k.verify_solution(&c(0)).is_err());
    assert!(k.verify_solution(&x().neg()).is_err());
    // f(x+y) = x + f(y) の解は x + c（c は任意）
    let k2 = Kernel::new(f(x().add(&y())), x().add(&f(y()))).unwrap();
    let fam = k2.verify_solution(&x().add(&f(c(0)))).unwrap();
    assert_eq!(fam.params().len(), 1);
    // パラメータは独立な記号として扱う: x + f(0)^2 も解（c^2 も任意の非負数だが、記号的に恒等式）
    assert!(k2.verify_solution(&x().add(&f(c(0)).pow(2))).is_ok());
    // f(x+y) = f(x) + f(y) では x + c は c = 0 のときだけ解なので、パラメータ付きでは不可
    let k3 = Kernel::new(f(x().add(&y())), f(x()).add(&f(y()))).unwrap();
    assert!(k3.verify_solution(&x().add(&f(c(0)))).is_err());
    assert!(k3.verify_solution(&x().mul(&f(c(1)))).is_ok());
    // x を含む f の原子は不可
    assert!(k.verify_solution(&f(x())).is_err());
    assert!(k.verify_solution(&y()).is_err());
}

#[test]
fn complete_proof_for_simple_equation() {
    let mut k = k_simple();
    let a = k.axiom();
    let p = k.instantiate(ROOT, a, vec![x(), c(0)], 1).unwrap(); // f(x) = x
    let fam = k.verify_solution(&x()).unwrap();
    let concl = k.conclude();
    assert!(!concl.complete);
    // 形が違う事実では確定できない
    let fam0 = k.verify_solution(&x()).unwrap();
    let bad = k.instantiate(ROOT, a, vec![x(), x()], 1).unwrap();
    assert!(k.mark_solution(ROOT, bad, fam0).is_err());
    k.mark_solution(ROOT, p, fam).unwrap();
    let concl = k.conclude();
    assert!(concl.complete);
    assert_eq!(concl.families.len(), 1);
}

#[test]
fn facts_from_another_kernel_are_rejected() {
    let mut k1 = k_simple();
    let mut k2 = k_simple();
    let a1 = k1.axiom();
    let _ = k2.axiom();
    assert!(k2.instantiate(ROOT, a1, vec![x(), c(0)], 1).is_err());
    let fam = k1.verify_solution(&x()).unwrap();
    let p2 = {
        let a2 = k2.axiom();
        k2.instantiate(ROOT, a2, vec![x(), c(0)], 1).unwrap()
    };
    assert!(k2.mark_solution(ROOT, p2, fam).is_err());
    let _ = k1.instantiate(ROOT, a1, vec![x(), c(0)], 1).unwrap();
}

#[test]
fn literal_normalization_is_sound() {
    // 定数倍はリテラルの意味を変えない範囲でだけ正規化される
    assert_eq!(Lit::eq(x().scale(&q(-3))), Lit::eq(x()));
    assert_eq!(Lit::ge(x().scale(&q(3))), Lit::ge(x()));
    assert_ne!(Lit::ge(x().scale(&q(-3))), Lit::ge(x()));
    assert_ne!(Lit::gt(x().neg()), Lit::gt(x()));
    assert_eq!(Lit::gt(x().scale(&qf(1, 2))), Lit::gt(x()));
    // 定数リテラル
    assert_eq!(Lit::eq(c(1)).truth(), Some(false));
    assert_eq!(Lit::ge(c(0)).truth(), Some(true));
    assert_eq!(Lit::gt(c(0)).truth(), Some(false));
    assert_eq!(Lit::ne(c(0)).truth(), Some(false));
    // 否定
    assert_eq!(Lit::gt(x()).negate(), Lit::ge(x().neg()));
    assert_eq!(Lit::ge(x()).negate(), Lit::gt(x().neg()));
    assert_eq!(Lit::eq(x()).negate(), Lit::ne(x()));
}

#[test]
fn abandon_split_rule() {
    let mut k = k_simple();
    let a = k.axiom();
    let (c0, _h0, c1, hs, consts) = k.split_em(ROOT, cl(1, vec![Lit::eq(f(x()).sub(&x()))])).unwrap();
    let ac = Poly::cnst(consts[0]);
    let p1 = k.instantiate(c1, a, vec![ac.clone(), c(0)], 0).unwrap();
    let _ = hs;
    let p0 = k.instantiate(c0, a, vec![x(), c(0)], 1).unwrap();
    k.abandon_split(ROOT).unwrap();
    // 子孫の枝・事実・定数はもう使えない
    assert!(k.instantiate(c1, a, vec![x(), c(0)], 1).is_err());
    assert!(k.lincomb(ROOT, 1, vec![(c(1), p0, 0)]).is_err());
    assert!(k.lincomb(ROOT, 0, vec![(c(1), p1, 0)]).is_err());
    assert!(k.instantiate(ROOT, a, vec![ac, c(0)], 0).is_err());
    // 根は再び葉で、別の場合分けができる
    assert!(k.branch(ROOT).children().is_empty());
    let (d0, _, d1, _, _) = k.split_em(ROOT, cl(0, vec![Lit::eq(f(c(0)))])).unwrap();
    assert!(k.lincomb(d0, 1, vec![(c(1), p0, 0)]).is_err(), "取り消した枝の事実は新しい子でも使えない");
    let _ = d1;
    // 取り消した枝の解の確定は結論に影響しない
    let concl = k.conclude();
    assert!(!concl.complete);
    // 二度目の取り消しは可能、場合分けのない枝の取り消しは不可
    k.abandon_split(ROOT).unwrap();
    assert!(k.abandon_split(ROOT).is_err());
}

#[test]
fn abandon_split_refused_after_merge() {
    let mut k = k_simple();
    let a = k.axiom();
    let (c0, _h0, c1, _hs, _) = k.split_em(ROOT, cl(0, vec![Lit::eq(f(c(1)).sub(&c(1)))])).unwrap();
    let p0 = k.instantiate(c0, a, vec![x(), c(0)], 1).unwrap();
    let p1 = k.instantiate(c1, a, vec![x(), c(0)], 1).unwrap();
    let m = k.merge(ROOT, vec![Some(p0), Some(p1)]).unwrap();
    assert!(k.abandon_split(ROOT).is_err());
    assert!(k.lincomb(ROOT, 1, vec![(c(1), m, 0)]).is_ok());
}

// ---------------------------------------------------------------------------
// 区分的な解

fn abs_pieces() -> (Vec<fe_kernel::Q>, Vec<Poly>) {
    (vec![q(0)], vec![x().neg(), c(0), x()])
}

#[test]
fn piecewise_verification() {
    // f(xy) = f(x)f(y) は |x| を解にもつ
    let k = Kernel::new(f(x().mul(&y())), f(x()).mul(&f(y()))).unwrap();
    let (b, p) = abs_pieces();
    assert!(k.verify_piecewise(b.clone(), p.clone()).is_ok());
    // f(x + y) = f(x) + f(y) は |x| を解にもたない
    let k2 = Kernel::new(f(x().add(&y())), f(x()).add(&f(y()))).unwrap();
    assert!(k2.verify_piecewise(b.clone(), p.clone()).is_err());
    // f(x+y) = x + y では x（区分なし相当）は解、|x| は解でない
    let k3 = k_simple();
    assert!(k3.verify_piecewise(vec![q(0)], vec![x(), c(0), x()]).is_ok());
    assert!(k3.verify_piecewise(b.clone(), p.clone()).is_err());
    // 点の値だけ違うものは解でない
    assert!(k3.verify_piecewise(vec![q(0)], vec![x(), c(1), x()]).is_err());
    // 形式の誤り
    assert!(k.verify_piecewise(vec![q(1), q(0)], vec![x(), c(0), x(), c(0), x()]).is_err());
    assert!(k.verify_piecewise(vec![q(0)], vec![x(), x()]).is_err());
    assert!(k.verify_piecewise(vec![q(0)], vec![f(x()), c(0), x()]).is_err());
}

#[test]
fn piecewise_marking() {
    let mut k = Kernel::new(f(x().mul(&y())), f(x()).mul(&f(y()))).unwrap();
    // 仮定として A: x < 0 ∨ f(x) = x,  B: x > 0 ∨ f(x) = −x,  C: f(0) = 0 を置く
    let (a0, ha, _, _, _) = k.split_em(ROOT, cl(1, vec![Lit::gt(x().neg()), Lit::eq(f(x()).sub(&x()))])).unwrap();
    let (b0, hb, _, _, _) = k.split_em(a0, cl(1, vec![Lit::gt(x()), Lit::eq(f(x()).add(&x()))])).unwrap();
    let (c0, hc, _, _, _) = k.split_em(b0, cl(0, vec![Lit::eq(f(c(0)))])).unwrap();
    let (b, p) = abs_pieces();
    let fam = k.verify_piecewise(b.clone(), p.clone()).unwrap();
    // 区間の順序は (−∞,0), {0}, (0,∞)
    assert!(k.mark_piecewise(c0, vec![ha, hc, hb], fam.clone()).is_err(), "区間と事実の対応が違う");
    k.mark_piecewise(c0, vec![hb, hc, ha], fam).unwrap();
    let concl = k.conclude();
    assert_eq!(concl.pw_families.len(), 1);
    assert!(!concl.complete, "他の枝が開いている");
}

#[test]
fn piecewise_marking_rejects_insufficient_conditions() {
    let mut k = Kernel::new(f(x().mul(&y())), f(x()).mul(&f(y()))).unwrap();
    // x > 1 ∨ f(x) = x は (0, ∞) 全体では f(x) = x を与えない
    let (a0, ha, _, _, _) = k.split_em(ROOT, cl(1, vec![Lit::gt(x().sub(&c(1))), Lit::eq(f(x()).sub(&x()))])).unwrap();
    let (b0, hb, _, _, _) = k.split_em(a0, cl(1, vec![Lit::gt(x()), Lit::eq(f(x()).add(&x()))])).unwrap();
    let (c0, hc, _, _, _) = k.split_em(b0, cl(0, vec![Lit::eq(f(c(0)))])).unwrap();
    let (b, p) = abs_pieces();
    let fam = k.verify_piecewise(b, p).unwrap();
    assert!(k.mark_piecewise(c0, vec![hb, hc, ha], fam).is_err());
}

#[test]
fn piecewise_literal_falsity() {
    use fe_kernel::piecewise::PwFamily;
    let _ = std::mem::size_of::<PwFamily>();
    let k = Kernel::new(f(x().mul(&y())), f(x()).mul(&f(y()))).unwrap();
    let fam = k.verify_piecewise(vec![q(0)], vec![x().neg(), c(0), x()]).unwrap();
    assert_eq!(fam.interval(0), (None, Some(q(0))));
    assert_eq!(fam.interval(1), (Some(q(0)), Some(q(0))));
    assert_eq!(fam.interval(2), (Some(q(0)), None));
}

#[test]
fn cauchy_bounded_rule() {
    // f(x + y) = f(x) + f(y) を例に、A と B を仮定として置く
    let mut k = Kernel::new(f(x().add(&y())), f(x()).add(&f(y()))).unwrap();
    let f0 = f(c(0));
    let a_cl = cl(2, vec![Lit::eq(f(x().add(&y())).sub(&f(x())).sub(&f(y())).add(&f0))]);
    let (a0, ha, _, _, _) = k.split_em(ROOT, a_cl).unwrap();
    let b_cl = cl(1, vec![Lit::gt(x().neg()), Lit::ge(f(x()).sub(&c(3)))]);
    let (b0, hb, _, _, _) = k.split_em(a0, b_cl).unwrap();
    let r = k.cauchy_bounded(b0, ha, hb).unwrap();
    let g = f(c(1)).sub(&f0).mul(&x()).add(&f0);
    assert_eq!(*k.clause(r), cl(1, vec![Lit::eq(f(x()).sub(&g))]));
    // 上に有界でもよい
    let (c0, hc, _, _, _) = k.split_em(b0, cl(1, vec![Lit::gt(x().neg()), Lit::ge(f(x()).neg().add(&f(c(2))))])).unwrap();
    assert!(k.cauchy_bounded(c0, ha, hc).is_ok());
    // 形の誤り: 加法性でない・条件が x > 0・x を含む境界・逆順
    let (d0, hd, _, _, _) = k.split_em(c0, cl(1, vec![Lit::gt(x()), Lit::ge(f(x()))])).unwrap();
    assert!(k.cauchy_bounded(d0, ha, hd).is_err());
    let (e0, he, _, _, _) = k.split_em(d0, cl(1, vec![Lit::gt(x().neg()), Lit::ge(f(x()).sub(&x()))])).unwrap();
    assert!(k.cauchy_bounded(e0, ha, he).is_err());
    assert!(k.cauchy_bounded(e0, hb, ha).is_err());
    let (g0, hg, _, _, _) = k.split_em(e0, cl(2, vec![Lit::eq(f(x().add(&y())).sub(&f(x())).sub(&f(y())))])).unwrap();
    assert!(k.cauchy_bounded(g0, hg, hb).is_err(), "f(0) の項がない形は受け付けない");
}
