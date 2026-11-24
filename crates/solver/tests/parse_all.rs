//! 全問題が About ページの文法で厳密にパースできることの保証。

use fe_kernel::{Kernel, Poly};
use fe_solver::parse::{parse_general, parse_strict, term_poly, TERMS};
use fe_solver::problems::{load_problems, Set};

#[test]
fn all_problems_parse_strictly() {
    let probs = load_problems().expect("データの読み込み");
    assert_eq!(probs.len(), 847, "About ページの問題数は 847");
    let n_eq: usize = probs.iter().map(|p| p.equations.len()).sum();
    assert_eq!(n_eq, 1625, "x<->y で同一視する前の方程式は 1625 個");
    assert_eq!(probs.iter().filter(|p| p.status == "solved").count(), 552);
    assert_eq!(probs.iter().filter(|p| p.set == Set::Unseen).count(), 110);
    assert_eq!(probs.iter().filter(|p| p.set == Set::Challenge).count(), 295);
    for p in &probs {
        assert!(p.equations.len() == 1 || p.equations.len() == 2, "{}", p.id);
        for e in &p.equations {
            // display の解析結果がデータの left/right と一致する
            assert_eq!(vec![e.parsed.a.clone(), e.parsed.b.clone()], e.left, "{}", p.id);
            assert_eq!(vec![e.parsed.c.clone(), e.parsed.d.clone()], e.right, "{}", p.id);
            // 一般パーサとも一致する
            let (l, r) = e.parsed.sides();
            let (gl, gr) = parse_general(&e.display).expect("一般パーサ");
            assert_eq!((l.clone(), r.clone()), (gl, gr), "{}", p.id);
            // f(x) = x が解である（About ページの制約）ことを検証核で確認
            let k = Kernel::new(l, r).expect("kernel");
            k.verify_solution(&Poly::var(0)).unwrap_or_else(|m| panic!("{}: f(x)=x が解でない: {}", p.id, m));
        }
        // 2 本ある場合は x<->y の入れ替えで互いに移る
        if p.equations.len() == 2 {
            let swap = |q: &Poly| q.subst_vars(&[Poly::var(1), Poly::var(0)]);
            let (l0, r0) = p.equations[0].parsed.sides();
            let (l1, r1) = p.equations[1].parsed.sides();
            assert_eq!((swap(&l0), swap(&r0)), (l1, r1), "{}", p.id);
        }
    }
}

#[test]
fn strict_parser_rejects_malformed() {
    for bad in [
        "f(x + y) = x + y + x",
        "f(x+y) = x + y",
        "f(x + y) = x - y",
        "f(x + z) = x + y",
        "f(x + y) == x + y",
        "g(x + y) = x + y",
        "f(x + y) = x^3 + y",
        "f(x + y = x + y)",
        "f(x + y) = 2x + y",
        "f(x + y) = x + y = y",
    ] {
        assert!(parse_strict(bad).is_err(), "受理してはいけない: {}", bad);
    }
    assert!(parse_strict("f(x + f(y)) = x + y").is_ok());
}

#[test]
fn terms_are_17_distinct_polys() {
    let mut ps: Vec<Poly> = TERMS.iter().map(|t| term_poly(t).unwrap()).collect();
    ps.sort();
    ps.dedup();
    assert_eq!(ps.len(), 17);
}
