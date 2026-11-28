//! 書き換え規則の左辺（パターン）と項の照合。
//! 照合結果は候補にすぎず、実際の書き換えは検証核の Instantiate で行われる（照合の誤りは健全性に影響しない）。

use fe_kernel::{Atom, Mono, Poly, Q};
use num_traits::{One, Signed, Zero};

/// パターン変数は Var(PAT + i) に移して、対象の変数と区別する
pub const PAT: u32 = 1_000_000;

pub fn shift_vars(p: &Poly, by: u32, n: u32) -> Poly {
    let s: Vec<Poly> = (0..n).map(|i| Poly::var(i + by)).collect();
    p.subst_vars(&s)
}

fn pat_vars(p: &Poly) -> Vec<u32> {
    p.vars().into_iter().filter(|&v| v >= PAT).collect()
}

fn apply(p: &Poly, s: &[Option<Poly>]) -> Poly {
    let max = PAT + s.len() as u32;
    // 値の決まったパターン変数を（入れ子の中も含めて）含まなければ、作り直さずにそのまま返す（結果は同じ）
    let mut any = false;
    p.visit_atoms(&mut |a| {
        if !any {
            if let Atom::Var(i) = a {
                if *i >= PAT && *i < max && s[(*i - PAT) as usize].is_some() {
                    any = true;
                }
            }
        }
    });
    if !any {
        return p.clone();
    }
    // PAT 以上の変数だけを置き換える
    p.transform(&mut |a| match a {
        Atom::Var(i) if i >= PAT && i < max => match &s[(i - PAT) as usize] {
            Some(t) => t.clone(),
            None => Poly::var(i),
        },
        other => Poly::from_atom(other),
    })
}

/// 単項式が「パターン変数を含む原子」を含むか
fn mono_has_pat_atom(m: &Mono) -> bool {
    m.factors().iter().any(|(a, _)| match a {
        Atom::F(p) | Atom::Inv(p) => !pat_vars(p).is_empty(),
        _ => false,
    })
}

pub fn is_perfect_square_mono(t: &Poly) -> Option<Poly> {
    if t.terms().len() != 1 {
        return None;
    }
    let (m, c) = &t.terms()[0];
    if c.is_negative() {
        return None;
    }
    let n = c.numer();
    let d = c.denom();
    let sn = n.sqrt();
    let sd = d.sqrt();
    if &(&sn * &sn) != n || &(&sd * &sd) != d {
        return None;
    }
    let mut out = Poly::constant(Q::new(sn, sd));
    for (a, e) in m.factors() {
        if e % 2 != 0 {
            return None;
        }
        out = out.mul(&Poly::from_atom(a.clone()).pow(e / 2));
    }
    Some(out)
}

fn match_rec(p: &Poly, t: &Poly, s: &mut Vec<Option<Poly>>, depth: u32) -> bool {
    if depth > 12 {
        return false;
    }
    let p2 = apply(p, s);
    let pv = pat_vars(&p2);
    if pv.is_empty() {
        return p2 == *t;
    }
    // 1. 原子の中にパターン変数を含む項を、対象の同じ係数の原子の項と対応させる
    if let Some((m, c)) = p2.terms().iter().find(|(m, _)| mono_has_pat_atom(m)) {
        if m.factors().len() == 1 && m.factors()[0].1 == 1 {
            let (pa, _) = &m.factors()[0];
            for (tm, tc) in t.terms() {
                if tc != c || tm.factors().len() != 1 || tm.factors()[0].1 != 1 {
                    continue;
                }
                let (ta, _) = &tm.factors()[0];
                let ok_head = matches!((pa, ta), (Atom::F(_), Atom::F(_)) | (Atom::Inv(_), Atom::Inv(_)));
                if !ok_head {
                    continue;
                }
                let (pi, ti) = match (pa, ta) {
                    (Atom::F(a), Atom::F(b)) | (Atom::Inv(a), Atom::Inv(b)) => (a, b),
                    _ => unreachable!(),
                };
                let mut s2 = s.clone();
                if !match_rec(pi, ti, &mut s2, depth + 1) {
                    continue;
                }
                let rest_p = p2.sub(&Poly::mono(m.clone(), c.clone()));
                let rest_t = t.sub(&Poly::mono(tm.clone(), tc.clone()));
                let mut s3 = s2.clone();
                if match_rec(&rest_p, &rest_t, &mut s3, depth + 1) {
                    *s = s3;
                    return true;
                }
            }
            return false;
        }
        // パターン変数を含む原子に他の因子が掛かった単項式（x·f(x), x·f(y), f(x)·f(y), f(x)² など）:
        // その原子を、対象の単項式の因子に現れる同じ種類の原子と順に対応させて引数を照合し、
        // 原子が閉じた式になったパターン全体の照合を続ける（代入すると原子は各項の因子として残るため、
        // 対象の因子の原子だけを候補にすればよい。積が 0 に消える代入は見つけない）
        let Some((pa, _)) = m.factors().iter().find(|(a, _)| match a {
            Atom::F(q) | Atom::Inv(q) => !pat_vars(q).is_empty(),
            _ => false,
        }) else {
            return false;
        };
        let mut cands: Vec<&Atom> = Vec::new();
        for (tm, _) in t.terms() {
            for (ta, _) in tm.factors() {
                let same_head = matches!((pa, ta), (Atom::F(_), Atom::F(_)) | (Atom::Inv(_), Atom::Inv(_)));
                if same_head && !cands.contains(&ta) {
                    cands.push(ta);
                }
            }
        }
        for ta in cands.into_iter().take(16) {
            let (pi, ti) = match (pa, ta) {
                (Atom::F(a), Atom::F(b)) | (Atom::Inv(a), Atom::Inv(b)) => (a, b),
                _ => unreachable!(),
            };
            let mut s2 = s.clone();
            if !match_rec(pi, ti, &mut s2, depth + 1) {
                continue;
            }
            if match_rec(p, t, &mut s2, depth + 1) {
                *s = s2;
                return true;
            }
        }
        return false;
    }
    // 2. パターン変数が原子の外にだけ現れる場合
    //    a) c·v + (定数部) の形: v = (t − 定数部)/c
    //    b) c·v² + (定数部) の形: (t − 定数部)/c が完全平方の単項式
    if pv.len() == 1 {
        let v = pv[0];
        let mut lin: Option<Q> = None;
        let mut sq: Option<Q> = None;
        let mut rest = Poly::zero();
        let mut ok = true;
        // v の係数が閉じた式（パターン変数を含まない原子の積。例: a·v）の項
        let mut lin_closed = Poly::zero();
        for (m, c) in p2.terms() {
            let has = m.factors().iter().any(|(a, _)| *a == Atom::Var(v));
            if !has {
                rest = rest.add(&Poly::mono(m.clone(), c.clone()));
            } else if m.factors().len() == 1 && m.factors()[0].1 == 1 {
                lin = Some(c.clone());
            } else if m.factors().len() == 1 && m.factors()[0].1 == 2 {
                sq = Some(c.clone());
            } else if m.factors().iter().all(|(a, e)| (*a == Atom::Var(v) && *e == 1) || (*a != Atom::Var(v) && pat_vars(&Poly::from_atom(a.clone())).is_empty())) {
                let mut coef = Poly::constant(c.clone());
                for (a, e) in m.factors() {
                    if *a != Atom::Var(v) {
                        coef = coef.mul(&Poly::from_atom(a.clone()).pow(*e));
                    }
                }
                lin_closed = lin_closed.add(&coef);
            } else {
                ok = false;
            }
        }
        if !ok {
            return false;
        }
        let idx = (v - PAT) as usize;
        // 係数が閉じた式の 1 次: v = (t − 残り)/C（割り切れるときだけ）
        if !lin_closed.is_zero() && sq.is_none() {
            let cc = match &lin {
                Some(q) => lin_closed.add(&Poly::constant(q.clone())),
                None => lin_closed.clone(),
            };
            let val = match crate::polyutil::exact_div(&t.sub(&rest), &cc) {
                Some(q) => q,
                None => return false,
            };
            if !pat_vars(&val).is_empty() {
                return false;
            }
            s[idx] = Some(val);
            return apply(p, s) == *t;
        }
        match (lin, sq) {
            (Some(c), None) => {
                let val = t.sub(&rest).scale(&(Q::one() / c));
                if !pat_vars(&val).is_empty() {
                    return false;
                }
                s[idx] = Some(val);
                return apply(p, s) == *t;
            }
            (None, Some(c)) => {
                let val = t.sub(&rest).scale(&(Q::one() / c));
                if let Some(r) = is_perfect_square_mono(&val) {
                    s[idx] = Some(r);
                    return apply(p, s) == *t;
                }
                if val.is_zero() {
                    s[idx] = Some(Poly::zero());
                    return apply(p, s) == *t;
                }
                return false;
            }
            _ => return false,
        }
    }
    false
}

/// パターン（変数 Var(0..n)）を対象の多項式に照合し、代入を返す（使われない変数は 0）
pub fn match_poly(pattern: &Poly, n: u32, target: &Poly) -> Option<Vec<Poly>> {
    match_shifted(&shift_vars(pattern, PAT, n), n, target)
}

/// 変数を Var(PAT + i) に移したパターンを照合する（規則ごとに移したものを持っておき、照合のたびに移さない）
pub fn match_shifted(p: &Poly, n: u32, target: &Poly) -> Option<Vec<Poly>> {
    let mut s: Vec<Option<Poly>> = vec![None; n as usize];
    if !match_rec(p, target, &mut s, 0) {
        return None;
    }
    let out: Vec<Poly> = s.into_iter().map(|o| o.unwrap_or_else(Poly::zero)).collect();
    // パターンに代入を入れて対象と一致するか（元のパターンの subst_vars と同じ）
    let filled: Vec<Option<Poly>> = out.iter().cloned().map(Some).collect();
    if apply(p, &filled) != *target {
        return None;
    }
    Some(out)
}

/// 原子のパターンの変数を Var(PAT + i) に移す（match_atom_shifted に渡す形）
pub fn shift_atom(a: &Atom, n: u32) -> Atom {
    match a {
        Atom::F(p) => Atom::F(std::rc::Rc::new(shift_vars(p, PAT, n))),
        Atom::Inv(p) => Atom::Inv(std::rc::Rc::new(shift_vars(p, PAT, n))),
        other => other.clone(),
    }
}

pub fn match_atom(pattern: &Atom, n: u32, target: &Atom) -> Option<Vec<Poly>> {
    match_atom_shifted(&shift_atom(pattern, n), n, target)
}

/// shift_atom で変数を移したパターンの照合
pub fn match_atom_shifted(pattern: &Atom, n: u32, target: &Atom) -> Option<Vec<Poly>> {
    match (pattern, target) {
        (Atom::F(p), Atom::F(t)) | (Atom::Inv(p), Atom::Inv(t)) => match_shifted(p, n, t),
        (Atom::Const(i), Atom::Const(j)) if i == j => Some(vec![Poly::zero(); n as usize]),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn x() -> Poly {
        Poly::var(0)
    }
    fn y() -> Poly {
        Poly::var(1)
    }
    #[test]
    fn basic() {
        // f(x) にはなんでも合う
        let s = match_poly(&x(), 1, &Poly::f(y()).add(&Poly::int(2))).unwrap();
        assert_eq!(s[0], Poly::f(y()).add(&Poly::int(2)));
        // -x
        let s = match_poly(&x().neg(), 1, &y()).unwrap();
        assert_eq!(s[0], y().neg());
        // x + f(y) と 3 + f(x^2)
        let pat = x().add(&Poly::f(y()));
        let t = Poly::int(3).add(&Poly::f(x().pow(2)));
        let s = match_poly(&pat, 2, &t).unwrap();
        assert_eq!(s, vec![Poly::int(3), x().pow(2)]);
        // f(x) の入れ子
        let pat = Poly::f(x());
        assert!(match_poly(&pat, 1, &Poly::f(Poly::f(y()))).is_some());
        assert!(match_poly(&pat, 1, &y()).is_none());
        // x^2 と 4y^2
        let s = match_poly(&x().pow(2), 1, &y().pow(2).scale(&fe_kernel::poly::q(4))).unwrap();
        assert_eq!(s[0], y().scale(&fe_kernel::poly::q(2)));
        assert!(match_poly(&x().pow(2), 1, &y()).is_none());
        // 定数
        assert!(match_poly(&Poly::zero(), 0, &Poly::zero()).is_some());
        assert!(match_poly(&Poly::zero(), 0, &x()).is_none());
        // 係数が閉じた式の 1 次: a·x + 1 と a·(y + 2) + 1（a は定数の記号）なら x = y + 2。割り切れなければ照合しない
        let a = Poly::cnst(0);
        let pat = a.mul(&x()).add(&Poly::one());
        let t = a.mul(&y().add(&Poly::int(2))).add(&Poly::one());
        let s = match_poly(&pat, 1, &t).unwrap();
        assert_eq!(s[0], y().add(&Poly::int(2)));
        assert!(match_poly(&pat, 1, &y().add(&Poly::one())).is_none());
    }
    #[test]
    fn product_with_pattern_atom() {
        let f = Poly::f;
        // x·f(x) と y·f(y)、(y+1)·f(y+1)（展開された形）
        let pat = x().mul(&f(x()));
        assert_eq!(match_poly(&pat, 1, &y().mul(&f(y()))).unwrap(), vec![y()]);
        let y1 = y().add(&Poly::one());
        assert_eq!(match_poly(&pat, 1, &y1.mul(&f(y1.clone()))).unwrap(), vec![y1.clone()]);
        // 引数が食い違うものには合わない: y·f(y + 1)
        assert!(match_poly(&pat, 1, &y().mul(&f(y1.clone()))).is_none());
        // x·f(y) と 2·f(x²)、f(3)·f(x)·x（変数の値は原子の照合と 1 次の係数から決まる）
        let pat = x().mul(&f(y()));
        assert_eq!(match_poly(&pat, 2, &f(x().pow(2)).scale(&fe_kernel::poly::q(2))).unwrap(), vec![Poly::int(2), x().pow(2)]);
        let s = match_poly(&pat, 2, &f(Poly::int(3)).mul(&f(x())).mul(&x())).unwrap();
        assert_eq!(Poly::var(0).mul(&f(Poly::var(1))).subst_vars(&s), f(Poly::int(3)).mul(&f(x())).mul(&x()));
        // f(x)² + x と f(y + 1)² + y + 1
        let pat = f(x()).pow(2).add(&x());
        assert_eq!(match_poly(&pat, 1, &f(y1.clone()).pow(2).add(&y1)).unwrap(), vec![y1.clone()]);
        assert!(match_poly(&pat, 1, &f(y1.clone()).pow(2).add(&y())).is_none());
        // x·f(x) + 2x·f(y) と 1 + ... のように合わないもの
        let pat = x().mul(&f(x())).add(&x().mul(&f(y())).scale(&fe_kernel::poly::q(2)));
        assert!(match_poly(&pat, 2, &Poly::one()).is_none());
    }
}
