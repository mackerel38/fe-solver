//! 項の大きさと順序（書き換えの向きを決める。停止性はさらに手数の上限で保証する）。

use fe_kernel::{Atom, Poly};
use num_traits::One;
use num_traits::Signed;
use std::cmp::Ordering;

pub fn atom_depth(a: &Atom) -> u32 {
    match a {
        Atom::Var(_) | Atom::Const(_) => 0,
        Atom::F(p) | Atom::Inv(p) => 1 + poly_depth(p),
    }
}

pub fn poly_depth(p: &Poly) -> u32 {
    p.terms().iter().flat_map(|(m, _)| m.factors().iter().map(|(a, _)| atom_depth(a))).max().unwrap_or(0)
}

pub fn atom_weight(a: &Atom) -> u32 {
    match a {
        Atom::Var(_) => 2,
        Atom::Const(_) => 2,
        Atom::F(p) => poly_weight(p).saturating_add(3),
        Atom::Inv(p) => poly_weight(p).saturating_add(4),
    }
}

/// 係数の重さ: |分子| + 分母 − 2（±1 なら 0）。定数の絶対値が小さいほど軽い（整礎）
pub fn coef_weight(c: &fe_kernel::Q) -> u32 {
    use num_traits::ToPrimitive;
    let n = c.numer().abs().to_u64().unwrap_or(u64::MAX / 4);
    let d = c.denom().to_u64().unwrap_or(u64::MAX / 4);
    let neg = if c.numer() < &num_bigint::BigInt::from(0) { 1 } else { 0 };
    (n.saturating_add(d).saturating_sub(2)).min(1 << 20) as u32 + neg
}

pub fn poly_weight(p: &Poly) -> u32 {
    let mut w: u32 = 0;
    for (m, c) in p.terms() {
        w = w.saturating_add(1);
        if !c.is_one() {
            w = w.saturating_add(coef_weight(c));
        }
        for (a, e) in m.factors() {
            w = w.saturating_add(atom_weight(a).saturating_mul(*e));
        }
    }
    w
}

/// 原子の全順序: (f の深さ, 重さ, 正規形の順序)
pub fn atom_cmp(a: &Atom, b: &Atom) -> Ordering {
    (atom_depth(a), atom_weight(a)).cmp(&(atom_depth(b), atom_weight(b))).then_with(|| a.cmp(b))
}

/// p に現れる最上位の原子がすべて a より小さいか
pub fn all_atoms_less(p: &Poly, a: &Atom) -> bool {
    p.terms().iter().all(|(m, _)| m.factors().iter().all(|(b, _)| atom_cmp(b, a) == Ordering::Less))
}

pub fn max_atom(p: &Poly) -> Option<Atom> {
    let mut best: Option<Atom> = None;
    for (m, _) in p.terms() {
        for (a, _) in m.factors() {
            if best.as_ref().map_or(true, |b| atom_cmp(a, b) == Ordering::Greater) {
                best = Some(a.clone());
            }
        }
    }
    best
}

/// 多項式の「複雑さ」（事実の優先順位づけに使う）
pub fn poly_size(p: &Poly) -> u32 {
    poly_weight(p) + 4 * poly_depth(p)
}
