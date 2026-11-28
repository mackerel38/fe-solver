//! 有理数と無理数で式を変える解の族（検証核の一部。病的な解の存在の証明に使う）。
//!
//! 表現: f(v) = g₁(v)（v が有理数のとき）、g₂(v)（v が無理数のとき）。g₁, g₂ は x の有理数係数の多項式で g₁ ≠ g₂。
//!
//! 病的であること: g₁ − g₂ は 0 でない多項式なので根は有限個。それ以外の点 a では、a に収束する有理数の列と
//! 無理数の列（どちらも稠密なのでとれる）で f の値の極限が g₁(a) と g₂(a) に分かれるので、f は a で不連続。
//! よって f は有限個の点を除いて至るところ不連続で、多項式や（有限個の区間ごとに多項式の）区分的な式では書けない。
//!
//! 解であることの検証（verify）は次の場合分けによる厳密な確認:
//!   1. 方程式の各変数が有理数か無理数かで分ける（排中律）。
//!   2. f の適用を内側から評価する。引数 v（変数の有理数係数の多項式）が有理数かを次で判定する:
//!      (a) v に現れる変数がすべて有理数: v は有理数（有理数は和・差・積で閉じ、係数も有理数）。
//!      (b) 無理数の変数がちょうど 1 つ u で、v = r·u + s（r, s は有理数の変数だけの多項式）: r ≠ 0 なら v は無理数
//!          （v が有理数なら u = (v − s)/r も有理数になり矛盾）、r = 0 なら v = s は有理数。r が 0 でない定数なら
//!          無理数と確定し、そうでなければ「r = 0（有理数）」と「r ≠ 0（無理数）」の 2 通りに分け、r = 0 を条件として記録する。
//!      (d) 内側で判定済みの引数 w について v = c·w + s（c は 0 でない有理数、s は有理数の変数だけの多項式）:
//!          v と w は同時に有理数か同時に無理数（v = c·w + s と w = (v − s)/c で、有理数は四則で閉じる）なので w と同じ。
//!      (c) それ以外: 有理数・無理数の 2 通りに分ける。
//!      判定は (引数, 有理数か) として記録する。値は g₁(v) または g₂(v)。判定は (a), (d), (b), (c) の順に試す。
//!   3. 各場合で次のどれかを確かめる: 左辺 − 右辺が恒等的に 0。記録した 2 つの判定 (v, 有理数), (w, 無理数) で
//!      v = c·w + s（(d) と同じ関係。v = w を含む）が成り立つ（両立しない）。
//!      記録した条件 r = 0 のうち、ある変数について定数係数の 1 次で残りがその変数を含まないものを順に代入すると、
//!      左辺 − 右辺が恒等的に 0 になるか、ある条件が 0 でない定数になる（両立しない）。
//!   場合分けはどれも全体を覆い（各点はどれかの場合に入り、その場合の評価はその点での f の値に一致する）、
//!   代入は条件を満たす点での値を変えないので、すべての場合で確かめられれば方程式はすべての実数で成り立つ。
//!   どれかで示せなければ検証は失敗する（健全だが不完全）。

use crate::poly::{Atom, Poly, Q};
use num_traits::{One, Zero};

/// 有理数と無理数で式を変える解の族（検証済み）。フィールドは非公開で、検証核の verify_rational_split だけが作れる。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QsFamily {
    pub(crate) kernel: u64,
    pub(crate) g_rat: Poly,
    pub(crate) g_irr: Poly,
}

impl QsFamily {
    /// 有理数での式 g₁(x)
    pub fn g_rat(&self) -> &Poly {
        &self.g_rat
    }
    /// 無理数での式 g₂(x)
    pub fn g_irr(&self) -> &Poly {
        &self.g_irr
    }
}

/// 1 つの場合: 値、判定の記録 (引数, 有理数か)、条件 r = 0 の r
#[derive(Clone)]
struct Case {
    value: Poly,
    marks: Vec<(Poly, bool)>,
    zeros: Vec<Poly>,
}

impl Case {
    fn join(&self, o: &Case, value: Poly) -> Case {
        let mut marks = self.marks.clone();
        marks.extend(o.marks.iter().cloned());
        let mut zeros = self.zeros.clone();
        zeros.extend(o.zeros.iter().cloned());
        Case { value, marks, zeros }
    }
}

/// 多項式の変数がすべて有理数か（rat[i] は変数 i が有理数か）
fn all_rat(p: &Poly, rat: &[bool]) -> bool {
    p.vars().iter().all(|&i| rat.get(i as usize).copied().unwrap_or(false))
}

/// v = c·w + s（c は 0 でない有理数、s は有理数の変数だけの多項式）か。そうなら v と w は同時に有理数か同時に無理数
fn related(v: &Poly, w: &Poly, rat: &[bool]) -> bool {
    // w の項のうち無理数の変数を含むものの係数の比で c を決める（なければ w は有理数で、この関係は使わない）
    let Some((m, cw)) = w.terms().iter().find(|(m, _)| {
        m.factors().iter().any(|(a, _)| matches!(a, Atom::Var(i) if !rat.get(*i as usize).copied().unwrap_or(false)))
    }) else {
        return false;
    };
    let Some(cv) = v.terms().iter().find(|(mm, _)| mm == m).map(|(_, c)| c.clone()) else {
        return false;
    };
    let c = cv / cw;
    !c.is_zero() && all_rat(&v.sub(&w.scale(&c)), rat)
}

/// 引数 v が有理数かの判定（2 の (a)(d)(b)(c)）。返り値は (有理数か, 条件 r) の可能性の一覧。
/// rat[i] は変数 i が有理数か、known は内側で判定済みの引数。v は変数だけの多項式でなければならない。
fn classify(v: &Poly, rat: &[bool], known: &[(Poly, bool)]) -> Option<Vec<(bool, Option<Poly>)>> {
    let mut irr: Vec<u32> = Vec::new();
    for (m, _) in v.terms() {
        for (a, _) in m.factors() {
            match a {
                Atom::Var(i) => {
                    if !*rat.get(*i as usize)? && !irr.contains(i) {
                        irr.push(*i);
                    }
                }
                _ => return None,
            }
        }
    }
    // (a)
    if irr.is_empty() {
        return Some(vec![(true, None)]);
    }
    // (d)
    if let Some((_, r)) = known.iter().find(|(w, _)| related(v, w, rat)) {
        return Some(vec![(*r, None)]);
    }
    // (b): v = r·u + s
    if irr.len() == 1 {
        let u = Atom::Var(irr[0]);
        let mut r = Poly::zero();
        let mut affine = true;
        for (m, c) in v.terms() {
            match m.factors().iter().find(|(a, _)| *a == u).map(|(_, e)| *e) {
                None => {}
                Some(1) => {
                    let rest: Vec<(Atom, u32)> = m.factors().iter().filter(|(a, _)| *a != u).cloned().collect();
                    let mut t = Poly::constant(c.clone());
                    for (a, e) in rest {
                        t = t.mul(&Poly::from_atom(a).pow(e));
                    }
                    r = r.add(&t);
                }
                Some(_) => affine = false,
            }
        }
        if affine {
            return Some(match r.as_const() {
                Some(c) if !c.is_zero() => vec![(false, None)],
                _ => vec![(true, Some(r)), (false, None)],
            });
        }
    }
    // (c)
    Some(vec![(true, None), (false, None)])
}

/// 多項式 p の f を族で展開した場合の一覧
fn expand(p: &Poly, rat: &[bool], g1: &Poly, g2: &Poly, budget: &mut usize) -> Option<Vec<Case>> {
    let mut acc = vec![Case { value: Poly::zero(), marks: vec![], zeros: vec![] }];
    for (m, c) in p.terms() {
        let mut mcases = vec![Case { value: Poly::constant(c.clone()), marks: vec![], zeros: vec![] }];
        for (a, e) in m.factors() {
            let acases: Vec<Case> = match a {
                Atom::Var(_) => vec![Case { value: Poly::from_atom(a.clone()), marks: vec![], zeros: vec![] }],
                Atom::F(arg) => {
                    let mut out = Vec::new();
                    for ac in expand(arg, rat, g1, g2, budget)? {
                        for (is_rat, zero) in classify(&ac.value, rat, &ac.marks)? {
                            let g = if is_rat { g1 } else { g2 };
                            let mut c2 = ac.clone();
                            c2.marks.push((ac.value.clone(), is_rat));
                            c2.zeros.extend(zero);
                            c2.value = g.subst_vars(&[ac.value.clone()]);
                            out.push(c2);
                        }
                    }
                    out
                }
                _ => return None,
            };
            let mut next = Vec::new();
            for mc in &mcases {
                for ac in &acases {
                    *budget = budget.checked_sub(1)?;
                    next.push(mc.join(ac, mc.value.mul(&ac.value.pow(*e))));
                }
            }
            mcases = next;
        }
        let mut next = Vec::new();
        for a0 in &acc {
            for mc in &mcases {
                *budget = budget.checked_sub(1)?;
                next.push(a0.join(mc, a0.value.add(&mc.value)));
            }
        }
        acc = next;
    }
    Some(acc)
}

/// 3 の確認
fn case_ok(case: &Case, rat: &[bool]) -> bool {
    for (v, rv) in &case.marks {
        for (w, rw) in &case.marks {
            if rv != rw && (v == w || related(v, w, rat)) {
                return true;
            }
        }
    }
    let mut value = case.value.clone();
    let mut zeros = case.zeros.clone();
    loop {
        if value.is_zero() {
            return true;
        }
        if zeros.iter().any(|z| matches!(z.as_const(), Some(c) if !c.is_zero())) {
            return true;
        }
        // 定数係数の 1 次で解ける条件を 1 つ選んで代入する
        let mut pick: Option<(usize, u32, Poly)> = None;
        'outer: for (k, z) in zeros.iter().enumerate() {
            for var in z.vars() {
                let mut coef: Option<Q> = None;
                let mut rest = Poly::zero();
                let mut ok = true;
                for (m, c) in z.terms() {
                    match m.factors().iter().find(|(a, _)| *a == Atom::Var(var)).map(|(_, e)| *e) {
                        None => rest = rest.add(&Poly::mono(m.clone(), c.clone())),
                        Some(1) if m.factors().len() == 1 => coef = Some(c.clone()),
                        _ => ok = false,
                    }
                }
                if let (true, Some(cf)) = (ok, coef) {
                    if !rest.vars().contains(&var) {
                        pick = Some((k, var, rest.neg().scale(&(Q::one() / cf))));
                        break 'outer;
                    }
                }
            }
        }
        let Some((k, var, val)) = pick else {
            return false;
        };
        let mut s: Vec<Poly> = (0..=var).map(Poly::var).collect();
        s[var as usize] = val;
        value = value.subst_vars(&s);
        zeros.remove(k);
        zeros = zeros.iter().map(|z| z.subst_vars(&s)).collect();
    }
}

fn is_x_poly(g: &Poly) -> bool {
    g.terms().iter().all(|(m, _)| m.factors().iter().all(|(a, _)| *a == Atom::Var(0)))
}

/// 族が方程式 lhs = rhs の解であることを確かめる
pub(crate) fn verify(lhs: &Poly, rhs: &Poly, g1: &Poly, g2: &Poly) -> Result<(), String> {
    if !is_x_poly(g1) || !is_x_poly(g2) {
        return Err("有理数・無理数での式は x の有理数係数の多項式でなければならない".into());
    }
    if g1 == g2 {
        return Err("有理数と無理数で式が同じ（多項式の解として確かめる）".into());
    }
    let d = lhs.sub(rhs);
    let mut has_other = false;
    d.visit_atoms(&mut |a| {
        if !matches!(a, Atom::Var(_) | Atom::F(_)) {
            has_other = true;
        }
    });
    if has_other {
        return Err("方程式に変数と f 以外の原子がある".into());
    }
    let n = d.vars().into_iter().max().map_or(0, |m| m + 1) as usize;
    if n > 3 {
        return Err("変数が多すぎる".into());
    }
    for bits in 0..(1u32 << n) {
        let rat: Vec<bool> = (0..n).map(|i| bits & (1 << i) != 0).collect();
        let mut budget = 20000usize;
        let cases = expand(&d, &rat, g1, g2, &mut budget).ok_or("場合が多すぎる")?;
        for c in &cases {
            if !case_ok(c, &rat) {
                let desc: Vec<&str> = rat.iter().map(|&r| if r { "有理数" } else { "無理数" }).collect();
                return Err(format!("変数が ({}) の場合に方程式を満たすことを示せない", desc.join(", ")));
            }
        }
    }
    Ok(())
}
