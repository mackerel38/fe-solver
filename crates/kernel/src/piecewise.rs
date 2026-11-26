//! 区分的な解の族（検証核の一部）: x の範囲によって式が変わる解（f(x) = |x| など）。
//!
//! 表現: 有理数の区切り点 b_1 < … < b_m と、2m+1 個の「区間」
//!   (−∞, b_1), {b_1}, (b_1, b_2), {b_2}, …, {b_m}, (b_m, ∞)
//! のそれぞれでの多項式 g_i(x)（有理数係数、x だけの式）。区間は実数全体を重なりなく覆う。
//!
//! 解であることの検証（verify_piecewise）は次の場合分けによる厳密な確認:
//!   1. x, y それぞれの符号（負・0・正）の 9 通りに分ける（三分律）。0 の変数は 0 を代入する。
//!   2. 方程式の f の適用を内側から評価する。引数 v の各区間への所属（v − b の符号）を、
//!      「各単項式の符号が x, y の符号から決まり、すべて同符号」なら確定し、確定しなければ区間ごとに分ける
//!      （分けたときは「v がその区間にある」を条件として記録する）。値は g_i(v)。
//!   3. 各場合で、左辺 − 右辺が恒等的に 0 になるか、記録した条件が両立しない（同じ v が異なる区間に属する）
//!      ことを確認する。点の区間 {b} の条件 v = b は、v が変数について定数係数の 1 次なら代入して使う。
//!   どの場合も示せなければ検証は失敗する（健全だが不完全）。
//!
//! 点の区間 {b} の式には、パラメータ（Var(2), Var(3), …。任意の実数を表す）を使ってよい（x ≠ 0 で 0、x = 0 で任意の c など）。
//! パラメータを含む式の符号はわからないものとして扱う（引数の区間への所属は場合分けされる）ので、検証はパラメータの
//! すべての値について成り立つことを示す。条件 v = b は、v がパラメータについて定数係数の 1 次でも代入して使う。

use crate::poly::{Atom, Poly, Q};
use num_traits::{One, Signed, Zero};

/// 区分的な解の族（検証済み）。フィールドは非公開で、検証核の verify_piecewise だけが作れる。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PwFamily {
    pub(crate) kernel: u64,
    pub(crate) breaks: Vec<Q>,
    pub(crate) pieces: Vec<Poly>,
}

impl PwFamily {
    /// 式に現れるパラメータ（Var(2) 以降の番号）
    pub fn params(&self) -> Vec<u32> {
        let mut out: Vec<u32> = self.pieces.iter().flat_map(|g| g.vars()).filter(|&v| v >= 2).collect();
        out.sort();
        out.dedup();
        out
    }
    pub fn breaks(&self) -> &[Q] {
        &self.breaks
    }
    /// 区間 i の多項式（i が偶数なら開区間、奇数なら区切り点）
    pub fn pieces(&self) -> &[Poly] {
        &self.pieces
    }
    /// 区間 i の端点 (下端, 上端)。None は無限。点の区間では両方 Some(b)。
    pub fn interval(&self, i: usize) -> (Option<Q>, Option<Q>) {
        interval(&self.breaks, i)
    }
}

pub(crate) fn interval(breaks: &[Q], i: usize) -> (Option<Q>, Option<Q>) {
    if i % 2 == 1 {
        let b = breaks[(i - 1) / 2].clone();
        return (Some(b.clone()), Some(b));
    }
    let k = i / 2;
    let lo = if k == 0 { None } else { Some(breaks[k - 1].clone()) };
    let hi = if k == breaks.len() { None } else { Some(breaks[k].clone()) };
    (lo, hi)
}

/// 多項式の符号（x, y の符号が sx, sy のとき）。各単項式の符号がそろえば確定。
/// 戻り値: Some(1) 正, Some(-1) 負, Some(0) 恒等的に 0, None 不明。
pub(crate) fn sign_of(p: &Poly, sx: i32, sy: i32) -> Option<i32> {
    if p.is_zero() {
        return Some(0);
    }
    let mut s: Option<i32> = None;
    for (m, c) in p.terms() {
        let mut t = if c.is_positive() { 1 } else { -1 };
        for (a, e) in m.factors() {
            let v = match a {
                Atom::Var(0) => sx,
                Atom::Var(1) => sy,
                _ => return None,
            };
            if e % 2 == 1 {
                t *= v;
            }
        }
        match s {
            None => s = Some(t),
            Some(s0) if s0 == t => {}
            _ => return None,
        }
    }
    s
}

/// 1 つの場合: 値の多項式と、記録した条件（引数 v が区間 i にある）
#[derive(Clone)]
struct Case {
    value: Poly,
    conds: Vec<(Poly, usize)>,
}

/// v が区間 i にあるかの判定: Some(true)/Some(false)/None（不明）
fn member(breaks: &[Q], i: usize, v: &Poly, sx: i32, sy: i32) -> Option<bool> {
    let (lo, hi) = interval(breaks, i);
    if i % 2 == 1 {
        let b = lo.unwrap();
        return match sign_of(&v.sub(&Poly::constant(b)), sx, sy)? {
            0 => Some(true),
            _ => Some(false),
        };
    }
    let mut res = Some(true);
    if let Some(l) = lo {
        match sign_of(&v.sub(&Poly::constant(l)), sx, sy) {
            Some(1) => {}
            Some(_) => return Some(false),
            None => res = None,
        }
    }
    if let Some(h) = hi {
        match sign_of(&v.sub(&Poly::constant(h)), sx, sy) {
            Some(-1) => {}
            Some(_) => return Some(false),
            None => res = None,
        }
    }
    res
}

/// 多項式 p の f を区分的な族で展開した場合の一覧
fn expand(p: &Poly, breaks: &[Q], pieces: &[Poly], sx: i32, sy: i32, budget: &mut usize) -> Option<Vec<Case>> {
    let mut acc: Vec<Case> = vec![Case { value: Poly::zero(), conds: vec![] }];
    for (m, c) in p.terms() {
        // 単項式ごとに、各原子の場合を掛け合わせる
        let mut mcases: Vec<Case> = vec![Case { value: Poly::constant(c.clone()), conds: vec![] }];
        for (a, e) in m.factors() {
            let acases: Vec<Case> = match a {
                Atom::Var(_) => vec![Case { value: Poly::from_atom(a.clone()), conds: vec![] }],
                Atom::F(arg) => {
                    let mut out = Vec::new();
                    for ac in expand(arg, breaks, pieces, sx, sy, budget)? {
                        for (i, g) in pieces.iter().enumerate() {
                            match member(breaks, i, &ac.value, sx, sy) {
                                Some(false) => continue,
                                Some(true) => out.push(Case { value: g.subst_vars(&[ac.value.clone()]), conds: ac.conds.clone() }),
                                None => {
                                    let mut conds = ac.conds.clone();
                                    conds.push((ac.value.clone(), i));
                                    out.push(Case { value: g.subst_vars(&[ac.value.clone()]), conds });
                                }
                            }
                        }
                    }
                    out
                }
                _ => return None,
            };
            let mut next = Vec::new();
            for mc in &mcases {
                for ac in &acases {
                    if *budget == 0 {
                        return None;
                    }
                    *budget -= 1;
                    let mut conds = mc.conds.clone();
                    conds.extend(ac.conds.iter().cloned());
                    next.push(Case { value: mc.value.mul(&ac.value.pow(*e)), conds });
                }
            }
            mcases = next;
        }
        let mut next = Vec::new();
        for a0 in &acc {
            for mc in &mcases {
                if *budget == 0 {
                    return None;
                }
                *budget -= 1;
                let mut conds = a0.conds.clone();
                conds.extend(mc.conds.iter().cloned());
                next.push(Case { value: a0.value.add(&mc.value), conds });
            }
        }
        acc = next;
    }
    Some(acc)
}

/// 条件のもとで値が 0 か（または条件が両立しないか）を確かめる
fn case_ok(case: &Case, breaks: &[Q]) -> bool {
    let mut value = case.value.clone();
    let mut conds = case.conds.clone();
    // 同じ引数が異なる区間に属する条件は両立しない
    for i in 0..conds.len() {
        for j in (i + 1)..conds.len() {
            if conds[i].0 == conds[j].0 && conds[i].1 != conds[j].1 {
                return true;
            }
        }
    }
    // 点の区間の条件 v = b で、v が変数について定数係数の 1 次なら代入
    for _ in 0..4 {
        if value.is_zero() {
            return true;
        }
        let mut applied = false;
        for k in 0..conds.len() {
            let (v, i) = conds[k].clone();
            if i % 2 == 0 {
                continue;
            }
            let b = breaks[(i - 1) / 2].clone();
            let d = v.sub(&Poly::constant(b));
            let mut vars: Vec<u32> = d.vars().into_iter().collect();
            vars.sort();
            for var in vars {
                let a = Atom::Var(var);
                let mut coef: Option<Q> = None;
                let mut rest = Poly::zero();
                let mut ok = true;
                for (m, c) in d.terms() {
                    let e = m.factors().iter().find(|(x, _)| *x == a).map(|(_, e)| *e).unwrap_or(0);
                    if e == 0 {
                        rest = rest.add(&Poly::mono(m.clone(), c.clone()));
                    } else if e == 1 && m.factors().len() == 1 {
                        coef = Some(c.clone());
                    } else {
                        ok = false;
                    }
                }
                if !ok || coef.is_none() || rest.vars().contains(&var) {
                    continue;
                }
                let val = rest.neg().scale(&(Q::one() / coef.unwrap()));
                let n = (var as usize + 1).max(2);
                let mut s: Vec<Poly> = (0..n as u32).map(Poly::var).collect();
                s[var as usize] = val;
                value = value.subst_vars(&s);
                conds = conds.iter().map(|(p, j)| (p.subst_vars(&s), *j)).collect();
                conds.remove(k);
                applied = true;
                break;
            }
            if applied {
                break;
            }
        }
        if !applied {
            break;
        }
    }
    if value.is_zero() {
        return true;
    }
    // 代入後に定数になった条件が偽なら両立しない
    for (v, i) in &conds {
        if let Some(c) = v.as_const() {
            let (lo, hi) = interval(breaks, *i);
            let inside = if i % 2 == 1 {
                c == lo.unwrap()
            } else {
                lo.map_or(true, |l| c > l) && hi.map_or(true, |h| c < h)
            };
            if !inside {
                return true;
            }
        }
    }
    false
}

/// 区分的な族が方程式 lhs = rhs の解であることを確かめる
pub(crate) fn verify(lhs: &Poly, rhs: &Poly, breaks: &[Q], pieces: &[Poly]) -> Result<(), String> {
    for w in breaks.windows(2) {
        if w[0] >= w[1] {
            return Err("区切り点が増加列でない".into());
        }
    }
    if pieces.len() != 2 * breaks.len() + 1 {
        return Err("区間の数が合わない".into());
    }
    for (i, g) in pieces.iter().enumerate() {
        for (m, _) in g.terms() {
            for (a, _) in m.factors() {
                let ok = match a {
                    Atom::Var(0) => true,
                    // パラメータは点の区間の式にだけ使える
                    Atom::Var(k) if *k >= 2 => i % 2 == 1,
                    _ => false,
                };
                if !ok {
                    return Err("各区間の式は x の有理数係数の多項式（点の区間ではパラメータも可）でなければならない".into());
                }
            }
        }
    }
    let d = lhs.sub(rhs);
    for sx in [-1, 0, 1] {
        for sy in [-1, 0, 1] {
            let mut s = vec![Poly::var(0), Poly::var(1)];
            if sx == 0 {
                s[0] = Poly::zero();
            }
            if sy == 0 {
                s[1] = Poly::zero();
            }
            let dd = d.subst_vars(&s);
            let mut budget = 20000usize;
            let cases = expand(&dd, breaks, pieces, sx, sy, &mut budget).ok_or("場合が多すぎる")?;
            for c in &cases {
                if !case_ok(c, breaks) {
                    return Err(format!("符号 ({}, {}) の場合に方程式を満たすことを示せない", sx, sy));
                }
            }
        }
    }
    Ok(())
}

/// 1 次式リテラル a·x + c ⋈ 0 が区間全体で偽か
pub fn literal_false_on(p: &Poly, rel: crate::clause::Rel, lo: &Option<Q>, hi: &Option<Q>, point: bool) -> bool {
    use crate::clause::Rel;
    if p.vars().iter().any(|&v| v != 0) || p.has_f() || p.has_inv() || !p.consts().is_empty() {
        return false;
    }
    let mut a = Q::zero();
    let mut c = Q::zero();
    for (m, k) in p.terms() {
        if m.is_one() {
            c = k.clone();
        } else if m.factors().len() == 1 && m.factors()[0] == (Atom::Var(0), 1) {
            a = k.clone();
        } else {
            return false;
        }
    }
    let at = |x: &Q| &a * x + &c;
    if point {
        let v = at(lo.as_ref().unwrap());
        return match rel {
            Rel::Gt => !v.is_positive(),
            Rel::Ge => v.is_negative(),
            Rel::Eq => !v.is_zero(),
            Rel::Ne => v.is_zero(),
        };
    }
    if a.is_zero() {
        return match rel {
            Rel::Gt => !c.is_positive(),
            Rel::Ge => c.is_negative(),
            Rel::Eq => !c.is_zero(),
            Rel::Ne => c.is_zero(),
        };
    }
    // 開区間上の値域 (pmin, pmax)。None は無限。
    let (pmin, pmax) = if a.is_positive() {
        (lo.as_ref().map(at), hi.as_ref().map(at))
    } else {
        (hi.as_ref().map(at), lo.as_ref().map(at))
    };
    match rel {
        Rel::Gt | Rel::Ge => matches!(pmax, Some(m) if !m.is_positive()),
        Rel::Eq => matches!(&pmin, Some(m) if !m.is_negative()) || matches!(&pmax, Some(m) if !m.is_positive()),
        Rel::Ne => false,
    }
}
