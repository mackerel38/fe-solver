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
    // 3. 定数でない項がすべてある単項式 M（原子 2 つ以上の積）のべきなら、M を 1 つの原子 z とみなして分解し、z を M に戻す
    //    （例: (1 + y²f(y)²)² + y f(y) は w = y f(y) の 4 次式）
    if let Some(base) = common_base(p) {
        let z = Atom::Const(u32::MAX - 7);
        let mut pz = Poly::zero();
        for (m, c) in p.terms() {
            let k = if m.is_one() { 0 } else { power_of(m, &base)? };
            pz = pz.add(&Poly::from_atom(z.clone()).pow(k).scale(c));
        }
        if let Some((sq, k)) = sos_rec(&pz, depth + 1) {
            let mp = Poly::mono(base, Q::one());
            let back = sq
                .into_iter()
                .map(|(d, t)| (d, t.transform(&mut |a| if a == z { mp.clone() } else { Poly::from_atom(a) })))
                .collect();
            return Some((back, k));
        }
    }
    // 4. 次数最大の項が「正の係数 × 平方の単項式」なら、その項を平方として外し、残りを分解する（例: w⁴ + 2w² + w + 1）
    let maxd = p.terms().iter().map(|(m, _)| m.degree()).max()?;
    if let Some((m, c)) = p.terms().iter().find(|(m, c)| m.degree() == maxd && c.is_positive() && m.factors().iter().all(|(_, e)| e % 2 == 0)) {
        let rest = p.sub(&Poly::mono(m.clone(), c.clone()));
        if let Some((mut sq, k)) = sos_rec(&rest, depth + 1) {
            let mut r = Mono::one();
            for (a, e) in m.factors() {
                for _ in 0..(e / 2) {
                    r = r.mul(&Mono::atom(a.clone()));
                }
            }
            sq.push((c.clone(), Poly::mono(r, Q::one())));
            return Some((sq, k));
        }
    }
    None
}

/// 定数でない項の単項式がすべて M のべきになる単項式 M（原子 2 つ以上の積で、次数が最小の単項式の指数を最大公約数で割ったもの）
fn common_base(p: &Poly) -> Option<Mono> {
    let m0 = p.terms().iter().map(|(m, _)| m).filter(|m| !m.is_one()).min_by_key(|m| m.degree())?;
    if m0.factors().len() < 2 {
        return None;
    }
    let g = m0.factors().iter().fold(0u32, |g, (_, e)| gcd(g, *e));
    let mut base = Mono::one();
    for (a, e) in m0.factors() {
        for _ in 0..(e / g) {
            base = base.mul(&Mono::atom(a.clone()));
        }
    }
    if p.terms().iter().all(|(m, _)| m.is_one() || power_of(m, &base).is_some()) {
        Some(base)
    } else {
        None
    }
}

/// m = base^k なら k
fn power_of(m: &Mono, base: &Mono) -> Option<u32> {
    if m.factors().len() != base.factors().len() {
        return None;
    }
    let mut k: Option<u32> = None;
    for ((a, e), (b, d)) in m.factors().iter().zip(base.factors()) {
        if a != b || e % d != 0 {
            return None;
        }
        match k {
            None => k = Some(e / d),
            Some(k0) if k0 == e / d => {}
            _ => return None,
        }
    }
    k
}

fn gcd(a: u32, b: u32) -> u32 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
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
    fn sos_monomial_base_and_top_square() {
        // (1 + y²f(y)²)² + y f(y): w = y f(y) の 4 次式 w⁴ + 2w² + w + 1。分解が恒等式になること
        let y = Poly::var(1);
        let w = y.mul(&Poly::f(y.clone()));
        let p = Poly::one().add(&w.pow(2)).pow(2).add(&w);
        let (sq, k) = sos(&p).expect("分解できない");
        let mut back = Poly::constant(k.clone());
        for (d, s) in &sq {
            assert!(d.is_positive());
            back = back.add(&s.pow(2).scale(d));
        }
        assert_eq!(back, p);
        assert!(k.is_positive());
        // w⁴ − w は負になりうる（w = 1/2）ので分解しない
        assert!(sos(&w.pow(4).sub(&w)).is_none());
        // x⁴ + x² + x + 1（1 変数。最高次の x⁴ を外すと x² + x + 1 が平方完成できる）
        let x = Poly::var(0);
        assert!(sos(&x.pow(4).add(&x.pow(2)).add(&x).add(&Poly::one())).is_some());
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
