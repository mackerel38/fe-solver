//! 探索部の共通の補助関数
#![allow(unused_imports)]

use crate::engine::{coeff_of_atom, replace_atom, Added, BState, Engine, Res, RwRule, TIMEOUT};
use crate::order::{atom_cmp, poly_size};
use crate::polyutil::*;
use fe_kernel::{AddFamily, AddKind, Atom, BranchId, Fact, Family, Kernel, Lit, Mono, Poly, Rel, Q};
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};


pub(crate) fn x() -> Poly {
    Poly::var(0)
}
pub(crate) fn y() -> Poly {
    Poly::var(1)
}

/// 単項式の分類（1 変数の事実で f(x) = g(x) を得るための消去順）
pub(crate) fn mclass(m: &Mono) -> u8 {
    let fx = Atom::F(std::rc::Rc::new(x()));
    let mut cls = 0u8;
    for (a, e) in m.factors() {
        if !a.has_var() {
            continue;
        }
        match a {
            Atom::Var(_) => {}
            _ if *a == fx => cls = cls.max(if *e >= 2 { 2 } else { 1 }),
            _ => return 3,
        }
    }
    cls
}

pub(crate) fn mono_prio(m: &Mono) -> (u8, Option<Atom>, u32) {
    let mut best: Option<Atom> = None;
    for (a, _) in m.factors() {
        if best.as_ref().map_or(true, |b| atom_cmp(a, b) == std::cmp::Ordering::Greater) {
            best = Some(a.clone());
        }
    }
    (mclass(m), best, m.degree())
}

pub(crate) fn prio_cmp(a: &Mono, b: &Mono) -> std::cmp::Ordering {
    let (ca, aa, da) = mono_prio(a);
    let (cb, ab, db) = mono_prio(b);
    ca.cmp(&cb)
        .then_with(|| match (&aa, &ab) {
            (Some(x), Some(y)) => atom_cmp(x, y),
            (Some(_), None) => std::cmp::Ordering::Greater,
            (None, Some(_)) => std::cmp::Ordering::Less,
            (None, None) => std::cmp::Ordering::Equal,
        })
        .then_with(|| da.cmp(&db))
        .then_with(|| a.cmp(b))
}

/// u が変数 v について「定数係数の 1 次」で、v が原子の中に現れないなら (係数, 残り) を返す
pub(crate) fn linear_in(u: &Poly, v: u32) -> Option<(Q, Poly)> {
    let a = Atom::Var(v);
    let mut coef: Option<Q> = None;
    let mut rest = Poly::zero();
    for (m, c) in u.terms() {
        let e = m.factors().iter().find(|(b, _)| *b == a).map(|(_, e)| *e).unwrap_or(0);
        let inside = m.factors().iter().any(|(b, _)| *b != a && Poly::from_atom(b.clone()).vars().contains(&v));
        if inside {
            return None;
        }
        if e == 0 {
            rest = rest.add(&Poly::mono(m.clone(), c.clone()));
        } else if e == 1 && m.factors().len() == 1 {
            coef = Some(c.clone());
        } else {
            return None;
        }
    }
    coef.map(|c| (c, rest))
}

/// d が変数 v について「v·(a·v + b)」の形（a は 0 でない有理数、v は原子の中に現れない）なら、
/// v で割った残り a·v + b = 0 の根 −b/a を返す（v = 0 は自明な解なので除く）
pub(crate) fn root_after_factor(d: &Poly, v: u32) -> Option<Poly> {
    let av = Atom::Var(v);
    for (m, _) in d.terms() {
        if m.factors().iter().any(|(b, _)| *b != av && Poly::from_atom(b.clone()).vars().contains(&v)) {
            return None;
        }
    }
    let cs = coeffs_in(d, &av);
    if cs.keys().copied().collect::<Vec<_>>() != vec![1, 2] {
        return None;
    }
    let a = cs[&2].as_const()?;
    if a.is_zero() {
        return None;
    }
    Some(cs[&1].neg().scale(&(Q::one() / a)))
}

/// 単項式の中の w·inv(w) を 1 に約す（f・inv の引数の中も再帰的に）。式の変形の候補を作るだけで、正しさは検証核で示す
pub(crate) fn cancel_inv(p: &Poly, w: u32) -> Poly {
    let wa = Atom::Var(w);
    let iwa = Atom::Inv(std::rc::Rc::new(Poly::var(w)));
    let mut out = Poly::zero();
    for (m, c) in p.terms() {
        let mut t = Poly::constant(c.clone());
        let (mut ew, mut ei) = (0u32, 0u32);
        for (a, e) in m.factors() {
            let a2 = match a {
                Atom::F(u) => Atom::F(std::rc::Rc::new(cancel_inv(u, w))),
                Atom::Inv(u) => Atom::Inv(std::rc::Rc::new(cancel_inv(u, w))),
                o => o.clone(),
            };
            if a2 == wa {
                ew += e;
            } else if a2 == iwa {
                ei += e;
            } else {
                t = t.mul(&Poly::from_atom(a2).pow(*e));
            }
        }
        let k = ew.min(ei);
        if ew > k {
            t = t.mul(&Poly::var(w).pow(ew - k));
        }
        if ei > k {
            t = t.mul(&Poly::inv(Poly::var(w)).pow(ei - k));
        }
        out = out.add(&t);
    }
    out
}

/// stored = k·target となる有理数 k（定数倍でなければ None）
pub(crate) fn scale_ratio(stored: &Poly, target: &Poly) -> Option<Q> {
    let (m, c) = target.terms().first()?;
    let c2 = stored.terms().iter().find(|(m2, _)| m2 == m)?.1.clone();
    let k = c2 / c;
    if target.scale(&k) == *stored {
        Some(k)
    } else {
        None
    }
}

/// 節の中で、target の定数倍になっている等式リテラルの位置と倍率
pub(crate) fn find_lit(c: &fe_kernel::Clause, target: &Poly) -> Option<(usize, Q)> {
    for (i, l) in c.lits().iter().enumerate() {
        if l.rel() == Rel::Eq {
            if let Some(k) = scale_ratio(l.poly(), target) {
                return Some((i, k));
            }
        }
    }
    None
}

/// 多項式に現れる f の原子（入れ子も含む）で変数を含むもの
pub(crate) fn f_atoms_with_vars(p: &Poly) -> Vec<Poly> {
    let mut out: Vec<Poly> = Vec::new();
    p.visit_atoms(&mut |a| {
        if let Atom::F(u) = a {
            if u.has_var() && !out.contains(u) {
                out.push((**u).clone());
            }
        }
    });
    out
}



/// x − r の形なら r
pub(crate) fn is_point_cond(p: &Poly) -> Option<Q> {
    if p.has_f() {
        return None;
    }
    let cs = coeffs_in(p, &Atom::Var(0));
    if cs.keys().max() != Some(&1) || cs.len() > 2 {
        return None;
    }
    let c1 = cs.get(&1)?.as_const()?;
    let c0 = cs.get(&0).map(|c| c.as_const()).unwrap_or(Some(Q::zero()))?;
    if p.vars().len() != 1 {
        return None;
    }
    Some(-c0 / c1)
}

// ---------------------------------------------------------------------------
// 候補解の探索（部分結果用）。数値は使わず、係数の連立方程式を有理数で解く。


pub fn n_components(c: &fe_kernel::Clause) -> usize {
    fe_kernel::kernel::components(c).len()
}


/// 単項式を x だけの部分と y だけの部分に分ける（x と y を両方含む原子があれば None）。閉じた原子は x 側に入れる。
pub(crate) fn split_mono_xy(m: &Mono) -> Option<(Mono, Mono)> {
    let mut mx = Mono::one();
    let mut my = Mono::one();
    for (a, e) in m.factors() {
        let vs = Poly::from_atom(a.clone()).vars();
        let piece = {
            let mut t = Mono::one();
            for _ in 0..*e {
                t = t.mul(&Mono::atom(a.clone()));
            }
            t
        };
        if vs.contains(&0) && vs.contains(&1) {
            return None;
        } else if vs.contains(&1) {
            my = my.mul(&piece);
        } else {
            mx = mx.mul(&piece);
        }
    }
    Some((mx, my))
}


/// p(x, y) = A(x)·B(y) と分解できれば (A, B)（どちらも定数でない）
pub fn rank1_split(p: &Poly) -> Option<(Poly, Poly)> {
    let mut m: BTreeMap<Mono, BTreeMap<Mono, Q>> = BTreeMap::new();
    for (mono, c) in p.terms() {
        let (mx, my) = split_mono_xy(mono)?;
        m.entry(mx).or_default().insert(my, c.clone());
    }
    let (x0, row0) = m.iter().next()?;
    let (y0, c00) = row0.iter().next()?;
    let _ = x0;
    // A(x) = Σ_i M[i][y0] x_i, B(y) = Σ_j M[x0][j]/M[x0][y0] y_j
    let mut a = Poly::zero();
    for (mx, row) in &m {
        let c = row.get(y0).cloned().unwrap_or_else(Q::zero);
        a = a.add(&Poly::mono(mx.clone(), c));
    }
    let mut b = Poly::zero();
    for (my, c) in row0 {
        b = b.add(&Poly::mono(my.clone(), c / c00));
    }
    if a.mul(&b) != *p {
        return None;
    }
    if !a.vars().contains(&0) || !b.vars().contains(&1) {
        return None;
    }
    Some((a, b))
}


/// u が変数 v について「閉じた係数 c（定数でない）の 1 次」なら (c, 残り)
pub(crate) fn linear_in_closed(u: &Poly, v: u32) -> Option<(Poly, Poly)> {
    let a = Atom::Var(v);
    let cs = coeffs_in(u, &a);
    if cs.keys().max() != Some(&1) {
        return None;
    }
    let c = cs.get(&1)?.clone();
    if c.has_var() || c.as_const().is_some() {
        return None;
    }
    let w = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
    if w.vars().contains(&v) {
        return None;
    }
    // v が原子の中に現れないこと
    for (m, _) in u.terms() {
        for (b, _) in m.factors() {
            if *b != a && Poly::from_atom(b.clone()).vars().contains(&v) {
                return None;
            }
        }
    }
    Some((c, w))
}


pub(crate) fn hash_clause(c: &fe_kernel::Clause) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    c.hash(&mut h);
    h.finish()
}


pub(crate) fn hash_poly(p: &Poly) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    p.hash(&mut h);
    h.finish()
}


/// 1 変数の式の f(a·x + b) で a の逆数 inv(a) がわかっていれば、x := (x − b)·inv(a)
pub(crate) fn affine_inv_substs(p: &Poly, invs: &[(Poly, Poly)]) -> Vec<Poly> {
    let mut out = Vec::new();
    for arg in f_atoms_with_vars(p) {
        let cs = coeffs_in(&arg, &Atom::Var(0));
        if cs.keys().max() != Some(&1) {
            continue;
        }
        let a = match cs.get(&1) {
            Some(a) => a.clone(),
            None => continue,
        };
        let b = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
        if b.has_var() {
            continue;
        }
        for (u, iu) in invs {
            if *u == a || u.monic() == a.monic() {
                // a = λu なら inv(a) = inv(u)/λ
                let lam = a.leading_coeff().unwrap() / u.leading_coeff().unwrap();
                let s = x().sub(&b).mul(iu).scale(&(Q::one() / lam));
                if !out.contains(&s) {
                    out.push(s);
                }
            }
        }
    }
    out
}
