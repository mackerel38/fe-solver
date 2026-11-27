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
//! 任意の区間をもつ族（ArbFamily、病的な解の存在の証明に使う）: 開区間の一部を「任意の値」にできる。
//!   - Free: その区間で f は任意の関数。NonNeg / NonPos: 値が 0 以上 / 0 以下の任意の関数。
//!   - Choice(g₁, g₂): 各点ごとに g₁(x) か g₂(x) のどちらかを任意に選ぶ（g₁ ≠ g₂）。
//!   検証: 任意の区間に入る引数 v での値 f(v) を、引数ごとに独立な記号 h_v（同じ引数なら同じ記号）として扱い、
//!   Choice は引数ごとに 2 通りに分ける（同じ引数で異なる選択をした場合は両立しないとして除く）。h_v の符号は
//!   NonNeg / NonPos なら既知として、後の引数の区間の判定に使う。各場合で左辺 − 右辺が x, y, h の多項式として
//!   恒等的に 0 なら、どの関数を選んでも方程式が成り立つ（独立な記号で恒等的に成り立つ式は、記号に同じ値や
//!   制約を満たす任意の値を入れても成り立つ）。根拠: 区間への所属・符号の判定は固定の区間の場合と同じ厳密な判定。
//!   病的な解の存在: 任意の区間は無限集合（開区間）なので、そこでの値の選び方は連続体濃度より多く、
//!   区分的な式で書けない解（各点の選択がルベーグ可測でないものなど）を必ず含む。

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
/// 記号（Const 原子）の符号の一覧を加えたもの。記号（Const 原子）の符号の一覧を加えたもの。符号の値は 1（> 0）、−1（< 0）、
/// 2（≥ 0、0 もありうる）、−2（≤ 0）。すべての単項式の符号がそろい、少なくとも 1 つが（弱い記号を含まず）
/// 厳密に符号が決まるときだけ、厳密な符号を返す（弱い項だけの和は 0 になりうるので None）。
pub(crate) fn sign_of_with(p: &Poly, sx: i32, sy: i32, csign: &[(u32, i32)]) -> Option<i32> {
    if p.is_zero() {
        return Some(0);
    }
    let mut s: Option<i32> = None;
    let mut strict = false;
    for (m, c) in p.terms() {
        let mut t = if c.is_positive() { 1 } else { -1 };
        let mut weak = false;
        for (a, e) in m.factors() {
            let v = match a {
                Atom::Var(0) => sx,
                Atom::Var(1) => sy,
                Atom::Const(i) => {
                    let sg = csign.iter().find(|(j, _)| j == i).map(|(_, sg)| *sg)?;
                    if sg.abs() == 2 {
                        weak = true;
                    }
                    sg.signum()
                }
                _ => return None,
            };
            if e % 2 == 1 {
                t *= v;
            }
        }
        if !weak {
            strict = true;
        }
        match s {
            None => s = Some(t),
            Some(s0) if s0 == t => {}
            _ => return None,
        }
    }
    if strict {
        s
    } else {
        None
    }
}

/// 弱い符号の判定: すべての単項式が 0 以上（以下）とわかれば Some(1)（Some(-1)）。不明なら None。
pub(crate) fn weak_sign_of(p: &Poly, sx: i32, sy: i32, csign: &[(u32, i32)]) -> Option<i32> {
    if p.is_zero() {
        return None;
    }
    let mut s: Option<i32> = None;
    for (m, c) in p.terms() {
        let mut t = if c.is_positive() { 1 } else { -1 };
        for (a, e) in m.factors() {
            let v = match a {
                Atom::Var(0) => sx,
                Atom::Var(1) => sy,
                Atom::Const(i) => csign.iter().find(|(j, _)| j == i).map(|(_, sg)| sg.signum())?,
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

/// 区間の種類（任意の区間をもつ族）。Fixed は固定の多項式、他は任意に選べる値。
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArbPiece {
    /// x の有理数係数の多項式
    Fixed(Poly),
    /// 任意の値
    Free,
    /// 0 以上の任意の値
    NonNeg,
    /// 0 以下の任意の値
    NonPos,
    /// 各点ごとに g₁(x) か g₂(x)（g₁ ≠ g₂）
    Choice(Poly, Poly),
}

/// 任意の区間をもつ解の族（検証済み）。フィールドは非公開で、検証核の verify_arbitrary だけが作れる。
/// 少なくとも 1 つの開区間が任意の値なので、病的な解（区分的な式で書けない解）を含む。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArbFamily {
    pub(crate) kernel: u64,
    pub(crate) breaks: Vec<Q>,
    pub(crate) pieces: Vec<ArbPiece>,
}

impl ArbFamily {
    pub fn breaks(&self) -> &[Q] {
        &self.breaks
    }
    pub fn pieces(&self) -> &[ArbPiece] {
        &self.pieces
    }
    pub fn interval(&self, i: usize) -> (Option<Q>, Option<Q>) {
        interval(&self.breaks, i)
    }
}

/// 任意の値の記号に使う Const 原子の番号の始まり（方程式の定数と重ならないように大きくする）
const SYM_BASE: u32 = 1 << 30;

/// 1 つの場合: 値の多項式と、記録した条件（引数 v が区間 i にある）と、各点の選択（引数 v、区間 i、選んだ番号）
#[derive(Clone)]
struct Case {
    value: Poly,
    conds: Vec<(Poly, usize)>,
    choices: Vec<(Poly, usize, u8)>,
}

/// 任意の値の記号の表: (引数, 区間) ごとに 1 つの記号。符号の既知のものは csign に入れる。
struct Syms {
    table: Vec<(Poly, usize)>,
    csign: Vec<(u32, i32)>,
}

impl Syms {
    fn get(&mut self, v: &Poly, i: usize, sign: Option<i32>) -> Poly {
        let k = match self.table.iter().position(|(w, j)| w == v && *j == i) {
            Some(k) => k,
            None => {
                self.table.push((v.clone(), i));
                if let Some(sg) = sign {
                    self.csign.push((SYM_BASE + (self.table.len() - 1) as u32, sg));
                }
                self.table.len() - 1
            }
        };
        Poly::cnst(SYM_BASE + k as u32)
    }
}

/// v が区間 i にあるかの判定: Some(true)/Some(false)/None（不明）
fn member(breaks: &[Q], i: usize, v: &Poly, sx: i32, sy: i32, csign: &[(u32, i32)]) -> Option<bool> {
    let (lo, hi) = interval(breaks, i);
    if i % 2 == 1 {
        let b = lo.unwrap();
        return match sign_of_with(&v.sub(&Poly::constant(b)), sx, sy, csign)? {
            0 => Some(true),
            _ => Some(false),
        };
    }
    let mut res = Some(true);
    if let Some(l) = lo {
        let d = v.sub(&Poly::constant(l));
        match sign_of_with(&d, sx, sy, csign) {
            Some(1) => {}
            Some(_) => return Some(false),
            None => {
                // v − l ≤ 0 とわかれば (l, …) にない
                if weak_sign_of(&d, sx, sy, csign) == Some(-1) {
                    return Some(false);
                }
                res = None
            }
        }
    }
    if let Some(h) = hi {
        let d = v.sub(&Poly::constant(h));
        match sign_of_with(&d, sx, sy, csign) {
            Some(-1) => {}
            Some(_) => return Some(false),
            None => {
                if weak_sign_of(&d, sx, sy, csign) == Some(1) {
                    return Some(false);
                }
                res = None
            }
        }
    }
    res
}

/// 多項式 p の f を族で展開した場合の一覧
fn expand(p: &Poly, breaks: &[Q], pieces: &[ArbPiece], sx: i32, sy: i32, budget: &mut usize, syms: &mut Syms) -> Option<Vec<Case>> {
    let mut acc: Vec<Case> = vec![Case { value: Poly::zero(), conds: vec![], choices: vec![] }];
    for (m, c) in p.terms() {
        // 単項式ごとに、各原子の場合を掛け合わせる
        let mut mcases: Vec<Case> = vec![Case { value: Poly::constant(c.clone()), conds: vec![], choices: vec![] }];
        for (a, e) in m.factors() {
            let acases: Vec<Case> = match a {
                Atom::Var(_) => vec![Case { value: Poly::from_atom(a.clone()), conds: vec![], choices: vec![] }],
                Atom::F(arg) => {
                    let mut out = Vec::new();
                    for ac in expand(arg, breaks, pieces, sx, sy, budget, syms)? {
                        for (i, pc) in pieces.iter().enumerate() {
                            let mem = member(breaks, i, &ac.value, sx, sy, &syms.csign);
                            if mem == Some(false) {
                                continue;
                            }
                            let mut conds = ac.conds.clone();
                            if mem.is_none() {
                                conds.push((ac.value.clone(), i));
                            }
                            let v = &ac.value;
                            let mut push = |value: Poly, ch: Option<u8>| {
                                let mut choices = ac.choices.clone();
                                if let Some(k) = ch {
                                    choices.push((v.clone(), i, k));
                                }
                                out.push(Case { value, conds: conds.clone(), choices });
                            };
                            match pc {
                                ArbPiece::Fixed(g) => push(g.subst_vars(&[v.clone()]), None),
                                ArbPiece::Free => push(syms.get(v, i, None), None),
                                ArbPiece::NonNeg => push(syms.get(v, i, Some(2)), None),
                                ArbPiece::NonPos => push(syms.get(v, i, Some(-2)), None),
                                ArbPiece::Choice(g1, g2) => {
                                    push(g1.subst_vars(&[v.clone()]), Some(0));
                                    push(g2.subst_vars(&[v.clone()]), Some(1));
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
                    let mut choices = mc.choices.clone();
                    choices.extend(ac.choices.iter().cloned());
                    next.push(Case { value: mc.value.mul(&ac.value.pow(*e)), conds, choices });
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
                let mut choices = a0.choices.clone();
                choices.extend(mc.choices.iter().cloned());
                next.push(Case { value: a0.value.add(&mc.value), conds, choices });
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
    // 同じ引数・同じ区間で異なる選択をした場合は両立しない（同じ点の値は 1 つ）
    for i in 0..case.choices.len() {
        for j in (i + 1)..case.choices.len() {
            let (a, b) = (&case.choices[i], &case.choices[j]);
            if a.0 == b.0 && a.1 == b.1 && a.2 != b.2 {
                return true;
            }
        }
    }
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
            // 解く原子: 変数 x, y と、任意の値の記号（Const 原子）
            let mut cands: Vec<Atom> = vec![Atom::Var(0), Atom::Var(1)];
            for c in d.consts() {
                if c >= SYM_BASE {
                    cands.push(Atom::Const(c));
                }
            }
            // c·a^e = 0（単項式が 1 つの原子のべき）なら a = 0
            if let [(m, _)] = d.terms() {
                if let [(a, _)] = m.factors() {
                    if cands.contains(a) {
                        let a = a.clone();
                        let sub = |p: &Poly| p.transform(&mut |t| if t == a { Poly::zero() } else { Poly::from_atom(t) });
                        value = sub(&value);
                        conds = conds.iter().map(|(p, j)| (sub(p), *j)).collect();
                        conds.remove(k);
                        applied = true;
                        break;
                    }
                }
            }
            for a in cands {
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
                let in_rest = match &a {
                    Atom::Var(var) => rest.vars().contains(var),
                    Atom::Const(cc) => rest.consts().contains(cc),
                    _ => true,
                };
                if !ok || coef.is_none() || in_rest {
                    continue;
                }
                let val = rest.neg().scale(&(Q::one() / coef.unwrap()));
                let sub = |p: &Poly| p.transform(&mut |t| if t == a { val.clone() } else { Poly::from_atom(t) });
                value = sub(&value);
                conds = conds.iter().map(|(p, j)| (sub(p), *j)).collect();
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
    // 値が点の区間の条件 v − b（= 0）の定数倍なら、その条件のもとで 0
    for (v, i) in &conds {
        if i % 2 == 1 {
            let d = v.sub(&Poly::constant(breaks[(i - 1) / 2].clone()));
            if let (Some((m0, c0)), Some((_, d0))) = (value.terms().first(), d.terms().iter().find(|(m, _)| m == &value.terms()[0].0)) {
                let _ = m0;
                let r = c0 / d0;
                if value.sub(&d.scale(&r)).is_zero() {
                    return true;
                }
            }
        }
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

/// x の有理数係数の多項式か
fn is_x_poly(g: &Poly) -> bool {
    g.terms().iter().all(|(m, _)| m.factors().iter().all(|(a, _)| *a == Atom::Var(0)))
}

/// 族が方程式 lhs = rhs の解であることを確かめる（共通部分）
fn verify_general(lhs: &Poly, rhs: &Poly, breaks: &[Q], pieces: &[ArbPiece]) -> Result<(), String> {
    for w in breaks.windows(2) {
        if w[0] >= w[1] {
            return Err("区切り点が増加列でない".into());
        }
    }
    if pieces.len() != 2 * breaks.len() + 1 {
        return Err("区間の数が合わない".into());
    }
    for (i, pc) in pieces.iter().enumerate() {
        match pc {
            ArbPiece::Fixed(g) => {
                if !is_x_poly(g) {
                    return Err("各区間の式は x の有理数係数の多項式でなければならない".into());
                }
            }
            ArbPiece::Choice(g1, g2) => {
                if !is_x_poly(g1) || !is_x_poly(g2) || g1 == g2 {
                    return Err("各点の選択は異なる 2 つの x の多項式".into());
                }
                if i % 2 == 1 {
                    return Err("任意の値は開区間にだけ置ける".into());
                }
            }
            _ => {
                if i % 2 == 1 {
                    return Err("任意の値は開区間にだけ置ける".into());
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
            let mut syms = Syms { table: vec![], csign: vec![] };
            let cases = expand(&dd, breaks, pieces, sx, sy, &mut budget, &mut syms).ok_or("場合が多すぎる")?;
            for c in &cases {
                if !case_ok(c, breaks) {
                    return Err(format!("符号 ({}, {}) の場合に方程式を満たすことを示せない", sx, sy));
                }
            }
        }
    }
    Ok(())
}

/// 区分的な族が方程式 lhs = rhs の解であることを確かめる
pub(crate) fn verify(lhs: &Poly, rhs: &Poly, breaks: &[Q], pieces: &[Poly]) -> Result<(), String> {
    let ps: Vec<ArbPiece> = pieces.iter().map(|g| ArbPiece::Fixed(g.clone())).collect();
    verify_general(lhs, rhs, breaks, &ps)
}

/// 任意の区間をもつ族が方程式 lhs = rhs の解であることを確かめる（開区間の少なくとも 1 つが任意の値であること）
pub(crate) fn verify_arbitrary(lhs: &Poly, rhs: &Poly, breaks: &[Q], pieces: &[ArbPiece]) -> Result<(), String> {
    if !pieces.iter().enumerate().any(|(i, p)| i % 2 == 0 && !matches!(p, ArbPiece::Fixed(_))) {
        return Err("任意の値の区間がない（区分的な族として確かめる）".into());
    }
    verify_general(lhs, rhs, breaks, pieces)
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
