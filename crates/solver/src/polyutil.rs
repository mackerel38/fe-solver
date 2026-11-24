//! 探索部用の多項式ユーティリティ（候補探し用。正しさは検証核が確かめる）。

use fe_kernel::{Atom, Mono, Poly, Q};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::BTreeMap;

/// p を原子 a の多項式とみなした係数 (次数 → 係数多項式)
pub fn coeffs_in(p: &Poly, a: &Atom) -> BTreeMap<u32, Poly> {
    let mut out: BTreeMap<u32, Poly> = BTreeMap::new();
    for (m, c) in p.terms() {
        let mut e = 0;
        let mut rest = Poly::constant(c.clone());
        for (b, eb) in m.factors() {
            if b == a {
                e = *eb;
            } else {
                rest = rest.mul(&Poly::from_atom(b.clone()).pow(*eb));
            }
        }
        let entry = out.entry(e).or_insert_with(Poly::zero);
        *entry = entry.add(&rest);
    }
    out.retain(|_, v| !v.is_zero());
    out
}

pub fn from_coeffs(cs: &BTreeMap<u32, Poly>, a: &Atom) -> Poly {
    let ap = Poly::from_atom(a.clone());
    let mut out = Poly::zero();
    for (e, c) in cs {
        out = out.add(&c.mul(&ap.pow(*e)));
    }
    out
}

/// 有理数係数の 1 変数多項式（係数ベクトル, 低次から）の有理根
pub fn rational_roots(cs: &[Q]) -> Vec<Q> {
    // 整数係数に直す
    let mut l = BigInt::one();
    for c in cs {
        l = l.lcm(c.denom());
    }
    let ints: Vec<BigInt> = cs.iter().map(|c| (c * Q::from_integer(l.clone())).to_integer()).collect();
    let mut ints = ints;
    // 0 根
    let mut roots = Vec::new();
    let mut k = 0;
    while k < ints.len() && ints[k].is_zero() {
        k += 1;
    }
    if k > 0 {
        roots.push(Q::zero());
    }
    ints.drain(0..k);
    if ints.len() <= 1 {
        return roots;
    }
    let a0 = ints[0].abs();
    let an = ints[ints.len() - 1].abs();
    let small = |n: &BigInt| n.to_u64().map_or(false, |v| v <= 1_000_000);
    if !small(&a0) || !small(&an) {
        return roots;
    }
    let divs = |n: u64| -> Vec<u64> { (1..=n).filter(|d| n % d == 0).collect() };
    let ps = divs(a0.to_u64().unwrap());
    let qs = divs(an.to_u64().unwrap());
    let mut cand: Vec<Q> = Vec::new();
    for p in &ps {
        for q in &qs {
            for s in [1i64, -1] {
                let r = Q::new(BigInt::from(*p as i64 * s), BigInt::from(*q as i64));
                if !cand.contains(&r) {
                    cand.push(r);
                }
            }
        }
    }
    for r in cand {
        let mut v = Q::zero();
        let mut pw = Q::one();
        for c in &ints {
            v += Q::from_integer(c.clone()) * &pw;
            pw *= &r;
        }
        if v.is_zero() && !roots.contains(&r) {
            roots.push(r);
        }
    }
    roots
}

/// 1 変数多項式 (原子 a) を有理根で因数分解: 因子のリスト（1 次因子 a − r と残り）
pub fn factor_univariate(p: &Poly, a: &Atom) -> Option<Vec<Poly>> {
    let cs = coeffs_in(p, a);
    if cs.values().any(|c| c.as_const().is_none()) {
        return None;
    }
    let deg = *cs.keys().next_back()?;
    if deg < 2 {
        return None;
    }
    let mut vec: Vec<Q> = (0..=deg).map(|e| cs.get(&e).and_then(|c| c.as_const()).unwrap_or_else(Q::zero)).collect();
    let roots = rational_roots(&vec);
    if roots.is_empty() {
        return None;
    }
    let mut factors = Vec::new();
    let ap = Poly::from_atom(a.clone());
    for r in roots {
        // 重複度ぶん割る
        loop {
            let (q, rem) = synth_div(&vec, &r);
            if !rem.is_zero() {
                break;
            }
            factors.push(ap.sub(&Poly::constant(r.clone())));
            vec = q;
            if vec.len() <= 1 {
                break;
            }
        }
    }
    let mut rest = Poly::zero();
    for (e, c) in vec.iter().enumerate() {
        rest = rest.add(&ap.pow(e as u32).scale(c));
    }
    if rest.as_const().is_none() {
        factors.push(rest);
    } else if factors.is_empty() {
        return None;
    } else {
        // 定数倍は最初の因子に掛ける
        let c = rest.as_const().unwrap();
        factors[0] = factors[0].scale(&c);
    }
    Some(factors)
}

/// 低次からの係数ベクトルを (x − r) で割る: (商, 余り)
pub fn synth_div(cs: &[Q], r: &Q) -> (Vec<Q>, Q) {
    let n = cs.len();
    if n == 0 {
        return (vec![], Q::zero());
    }
    let mut q = vec![Q::zero(); n.saturating_sub(1)];
    let mut acc = Q::zero();
    for i in (0..n).rev() {
        acc = &acc * r + &cs[i];
        if i > 0 {
            q[i - 1] = acc.clone();
        }
    }
    (q, acc)
}

/// 変数 Var(v) の多項式とみなして (Var(v) − r) で割る（余りが 0 のときだけ商を返す）
pub fn div_linear(p: &Poly, v: u32, r: &Poly) -> Option<Poly> {
    let a = Atom::Var(v);
    let cs = coeffs_in(p, &a);
    let deg = cs.keys().next_back().copied().unwrap_or(0);
    // 係数は多項式。ホーナー法で (x − r) で割る
    let mut q: Vec<Poly> = vec![Poly::zero(); deg as usize];
    let mut acc = Poly::zero();
    for i in (0..=deg).rev() {
        acc = acc.mul(r).add(cs.get(&i).unwrap_or(&Poly::zero()));
        if i > 0 {
            q[(i - 1) as usize] = acc.clone();
        }
    }
    if !acc.is_zero() {
        return None;
    }
    let ap = Poly::var(v);
    let mut out = Poly::zero();
    for (e, c) in q.iter().enumerate() {
        out = out.add(&c.mul(&ap.pow(e as u32)));
    }
    Some(out)
}

/// 単項式の共通因子（原子の最小指数）
pub fn monomial_content(p: &Poly) -> Mono {
    let mut it = p.terms().iter();
    let first = match it.next() {
        Some((m, _)) => m.clone(),
        None => return Mono::one(),
    };
    let mut common: Vec<(Atom, u32)> = first.factors().to_vec();
    for (m, _) in it {
        common = common
            .into_iter()
            .filter_map(|(a, e)| m.factors().iter().find(|(b, _)| *b == a).map(|(_, e2)| (a, e.min(*e2))))
            .collect();
    }
    let mut out = Mono::one();
    for (a, e) in common {
        for _ in 0..e {
            out = out.mul(&Mono::atom(a.clone()));
        }
    }
    out
}

pub fn div_mono(p: &Poly, m: &Mono) -> Poly {
    Poly::from_terms(p.terms().iter().map(|(m2, c)| (m2.div(m).expect("割り切れる"), c.clone())).collect())
}

/// x, y の多項式として係数を取り出す（係数は x, y を含まない）
pub fn coeffs_xy(p: &Poly) -> BTreeMap<(u32, u32), Poly> {
    let mut out: BTreeMap<(u32, u32), Poly> = BTreeMap::new();
    for (m, c) in p.terms() {
        let mut ex = 0;
        let mut ey = 0;
        let mut rest = Poly::constant(c.clone());
        for (a, e) in m.factors() {
            match a {
                Atom::Var(0) => ex = *e,
                Atom::Var(1) => ey = *e,
                other => rest = rest.mul(&Poly::from_atom(other.clone()).pow(*e)),
            }
        }
        let entry = out.entry((ex, ey)).or_insert_with(Poly::zero);
        *entry = entry.add(&rest);
    }
    out.retain(|_, v| !v.is_zero());
    out
}

/// 有理数の正方行列の逆行列（ガウスの消去法）
pub fn invert(m: &[Vec<Q>]) -> Option<Vec<Vec<Q>>> {
    let n = m.len();
    let mut a: Vec<Vec<Q>> = m.iter().cloned().collect();
    let mut inv: Vec<Vec<Q>> = (0..n).map(|i| (0..n).map(|j| if i == j { Q::one() } else { Q::zero() }).collect()).collect();
    for col in 0..n {
        let piv = (col..n).find(|&r| !a[r][col].is_zero())?;
        a.swap(col, piv);
        inv.swap(col, piv);
        let p = a[col][col].clone();
        for j in 0..n {
            a[col][j] = &a[col][j] / &p;
            inv[col][j] = &inv[col][j] / &p;
        }
        for r in 0..n {
            if r != col && !a[r][col].is_zero() {
                let f = a[r][col].clone();
                for j in 0..n {
                    let t = &a[col][j] * &f;
                    a[r][j] -= t;
                    let t2 = &inv[col][j] * &f;
                    inv[r][j] -= t2;
                }
            }
        }
    }
    Some(inv)
}

/// 単項式の辞書式順序（大きい原子の指数から比べる）。積と両立する単項式順序。
pub fn lex_cmp(a: &Mono, b: &Mono) -> std::cmp::Ordering {
    let mut fa: Vec<&(Atom, u32)> = a.factors().iter().collect();
    let mut fb: Vec<&(Atom, u32)> = b.factors().iter().collect();
    fa.reverse();
    fb.reverse();
    let (mut i, mut j) = (0, 0);
    loop {
        match (fa.get(i), fb.get(j)) {
            (None, None) => return std::cmp::Ordering::Equal,
            (Some(_), None) => return std::cmp::Ordering::Greater,
            (None, Some(_)) => return std::cmp::Ordering::Less,
            (Some((x, ex)), Some((y, ey))) => {
                if x == y {
                    if ex != ey {
                        return ex.cmp(ey);
                    }
                    i += 1;
                    j += 1;
                } else if x > y {
                    return std::cmp::Ordering::Greater;
                } else {
                    return std::cmp::Ordering::Less;
                }
            }
        }
    }
}

fn lead(p: &Poly) -> Option<(Mono, Q)> {
    p.terms().iter().max_by(|a, b| lex_cmp(&a.0, &b.0)).cloned()
}

/// 多項式の平方根（あれば）。辞書式順序の主項から順に決める。
pub fn poly_sqrt(p: &Poly) -> Option<Poly> {
    if p.is_zero() {
        return Some(Poly::zero());
    }
    let (lm, lc) = lead(p)?;
    if lc.is_negative() {
        return None;
    }
    let first = crate::matching::is_perfect_square_mono(&Poly::mono(lm, lc))?;
    let mut root = first.clone();
    let mut rem = p.sub(&first.mul(&first));
    let two = Q::from_integer(BigInt::from(2));
    let (lm2, lc2) = (first.terms()[0].0.clone(), &first.terms()[0].1 * &two);
    for _ in 0..30 {
        if rem.is_zero() {
            return Some(root);
        }
        let (m, c) = lead(&rem)?;
        let qm = m.div(&lm2)?;
        let t = Poly::mono(qm, &c / &lc2);
        rem = rem.sub(&root.scale(&two).mul(&t)).sub(&t.mul(&t));
        root = root.add(&t);
    }
    None
}

/// p を u で割り切れるなら商（u の主項による多項式の割り算。主項は辞書式順序）
pub fn exact_div(p: &Poly, u: &Poly) -> Option<Poly> {
    if u.is_zero() {
        return None;
    }
    let lead = |q: &Poly| q.terms().iter().max_by(|a, b| lex_cmp(&a.0, &b.0)).cloned();
    let (um, uc) = lead(u)?;
    let mut rem = p.clone();
    let mut quo = Poly::zero();
    for _ in 0..200 {
        if rem.is_zero() {
            return Some(quo);
        }
        let (rm, rc) = lead(&rem)?;
        let qm = rm.div(&um)?;
        let t = Poly::mono(qm, &rc / &uc);
        quo = quo.add(&t);
        rem = rem.sub(&t.mul(u));
    }
    None
}
