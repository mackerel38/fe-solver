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
        for (m, c) in p2.terms() {
            let has = m.factors().iter().any(|(a, _)| *a == Atom::Var(v));
            if !has {
                rest = rest.add(&Poly::mono(m.clone(), c.clone()));
            } else if m.factors().len() == 1 && m.factors()[0].1 == 1 {
                lin = Some(c.clone());
            } else if m.factors().len() == 1 && m.factors()[0].1 == 2 {
                sq = Some(c.clone());
            } else {
                ok = false;
            }
        }
        if !ok {
            return false;
        }
        let idx = (v - PAT) as usize;
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
    let p = shift_vars(pattern, PAT, n);
    let mut s: Vec<Option<Poly>> = vec![None; n as usize];
    if !match_rec(&p, target, &mut s, 0) {
        return None;
    }
    let out: Vec<Poly> = s.into_iter().map(|o| o.unwrap_or_else(Poly::zero)).collect();
    if pattern.subst_vars(&out) != *target {
        return None;
    }
    Some(out)
}

pub fn match_atom(pattern: &Atom, n: u32, target: &Atom) -> Option<Vec<Poly>> {
    match (pattern, target) {
        (Atom::F(p), Atom::F(t)) | (Atom::Inv(p), Atom::Inv(t)) => match_poly(p, n, t),
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
    }
}
