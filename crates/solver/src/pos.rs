//! 非負性の証明書探し（平方和への分解）と、平方の値域に関する補助。
//! ここで作るのは候補（分解）だけで、事実は検証核の PosComb / SquareRange が作る。

use crate::polyutil::coeffs_in;
use fe_kernel::{Atom, Mono, Poly, Q};
use num_traits::{One, Signed, Zero};

/// p = Σ d_k s_k² + κ（d_k > 0, κ ≥ 0）と分解できれば (平方の一覧, κ) を返す。
/// 原子（変数・f の値など）はすべて実数の変数とみなす。
pub fn sos(p: &Poly) -> Option<(Vec<(Q, Poly)>, Q)> {
    sos_rec(p, 0)
}

fn sos_rec(p: &Poly, depth: u32) -> Option<(Vec<(Q, Poly)>, Q)> {
    if depth > 8 {
        return None;
    }
    if let Some(c) = p.as_const() {
        return if c.is_negative() { None } else { Some((vec![], c)) };
    }
    // 1. すべての項が「正の係数 × 平方の単項式」（定数項は非負）
    let mut squares = Vec::new();
    let mut kappa = Q::zero();
    let mut ok = true;
    for (m, c) in p.terms() {
        if m.is_one() {
            if c.is_negative() {
                ok = false;
                break;
            }
            kappa = c.clone();
            continue;
        }
        if c.is_negative() || m.factors().iter().any(|(_, e)| e % 2 != 0) {
            ok = false;
            break;
        }
        let mut r = Mono::one();
        for (a, e) in m.factors() {
            for _ in 0..(e / 2) {
                r = r.mul(&Mono::atom(a.clone()));
            }
        }
        squares.push((c.clone(), Poly::mono(r, Q::one())));
    }
    if ok {
        return Some((squares, kappa));
    }
    // 2. ある原子 z について 2 次（主係数は正の定数）なら平方完成して残りを再帰
    let atoms: Vec<Atom> = p.top_atoms().into_iter().collect();
    for z in atoms.iter().rev() {
        let cs = coeffs_in(p, z);
        if cs.keys().max() != Some(&2) {
            continue;
        }
        let a = match cs.get(&2).and_then(|c| c.as_const()) {
            Some(a) if a.is_positive() => a,
            _ => continue,
        };
        let b = cs.get(&1).cloned().unwrap_or_else(Poly::zero);
        let c = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
        if b.top_atoms().contains(z) || c.top_atoms().contains(z) {
            continue;
        }
        let two_a = &a * Q::from_integer(2.into());
        let h = b.scale(&(Q::one() / &two_a));
        let s = Poly::from_atom(z.clone()).add(&h);
        let rest = c.sub(&b.mul(&b).scale(&(Q::one() / (&a * Q::from_integer(4.into())))));
        if let Some((mut sq, k)) = sos_rec(&rest, depth + 1) {
            sq.push((a, s));
            return Some((sq, k));
        }
    }
    None
}

/// p の中で変数 v が v² の形でだけ現れる（f の引数の中も含む）なら、v² を v に置き換えた式を返す
pub fn unsquare(p: &Poly, v: u32) -> Option<Poly> {
    let mut out = Poly::zero();
    let mut found = false;
    for (m, c) in p.terms() {
        let mut t = Poly::constant(c.clone());
        for (a, e) in m.factors() {
            let piece = match a {
                Atom::Var(w) if *w == v => {
                    if e % 2 != 0 {
                        return None;
                    }
                    found = true;
                    Poly::var(v).pow(e / 2)
                }
                Atom::F(arg) | Atom::Inv(arg) if arg.vars().contains(&v) => {
                    let inner = unsquare(arg, v)?;
                    found = true;
                    let at = match a {
                        Atom::F(_) => Poly::f(inner),
                        _ => Poly::inv(inner),
                    };
                    at.pow(*e)
                }
                other => Poly::from_atom(other.clone()).pow(*e),
            };
            t = t.mul(&piece);
        }
        out = out.add(&t);
    }
    if found {
        Some(out)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fe_kernel::poly::{q, qf};
    #[test]
    fn sos_basic() {
        let x = Poly::var(0);
        let y = Poly::var(1);
        assert!(sos(&x.pow(2).add(&Poly::constant(qf(1, 4)))).is_some());
        assert!(sos(&x.pow(2).sub(&x).add(&Poly::constant(qf(1, 4)))).is_some()); // (x − 1/2)²
        assert!(sos(&x.pow(2).sub(&x)).is_none());
        assert!(sos(&x.pow(2).add(&x.mul(&y).scale(&q(2))).add(&y.pow(2).scale(&q(2)))).is_some());
        assert!(sos(&x).is_none());
        let (sq, k) = sos(&x.pow(2).add(&Poly::int(1))).unwrap();
        assert_eq!(k, q(1));
        assert_eq!(sq.len(), 1);
    }
    #[test]
    fn unsquare_basic() {
        let x = Poly::var(0);
        let y = Poly::var(1);
        let p = Poly::f(x.add(&y.pow(2))).sub(&y.pow(2));
        let u = unsquare(&p, 1).unwrap();
        assert_eq!(u, Poly::f(x.add(&y)).sub(&y));
        assert!(unsquare(&Poly::f(y.clone()).sub(&y.pow(2)), 1).is_none());
        assert!(unsquare(&x, 1).is_none());
    }
}
