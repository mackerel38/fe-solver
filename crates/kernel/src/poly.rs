//! 有理数係数の多項式（検証核の一部）。
//!
//! 原子 (Atom) は次の4種類:
//!   - `Var(i)`   : 事実（節）ごとに全称量化される変数
//!   - `Const(i)` : 証明中に検証核が導入した定数（スコーレム定数）
//!   - `F(p)`     : 未知関数 f を多項式 p に適用したもの
//!   - `Inv(p)`   : 逆数関数 inv を p に適用したもの（inv(p)·p = 1 は p ≠ 0 のときだけ公理で使える）
//!
//! 正規形: 単項式は「原子の昇順に並んだ (原子, 指数≥1) の列」、多項式は「単項式の昇順に並んだ
//! (単項式, 係数≠0) の列」。f や inv の引数も正規形で持つ。正規形は一意なので、
//! 2つの式が実数上で恒等的に等しい（可換環の公理と f, inv が関数であることだけから従う）かどうかは
//! 構造的な等しさ (==) で厳密に判定できる。浮動小数点や乱数は一切使わない。

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeSet;
use std::fmt;
use std::rc::Rc;

pub type Q = BigRational;

pub fn q(n: i64) -> Q {
    Q::from_integer(BigInt::from(n))
}

pub fn qf(n: i64, d: i64) -> Q {
    Q::new(BigInt::from(n), BigInt::from(d))
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Atom {
    Var(u32),
    Const(u32),
    F(Rc<Poly>),
    Inv(Rc<Poly>),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
pub struct Mono(Vec<(Atom, u32)>);

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
pub struct Poly(Vec<(Mono, Q)>);

impl Atom {
    /// 原子が（引数の中も含めて）変数を含むか
    pub fn has_var(&self) -> bool {
        match self {
            Atom::Var(_) => true,
            Atom::Const(_) => false,
            Atom::F(p) | Atom::Inv(p) => p.has_var(),
        }
    }
    pub fn has_f(&self) -> bool {
        match self {
            Atom::Var(_) | Atom::Const(_) => false,
            Atom::F(_) => true,
            Atom::Inv(p) => p.has_f(),
        }
    }
}

impl Mono {
    pub fn one() -> Mono {
        Mono(Vec::new())
    }
    pub fn atom(a: Atom) -> Mono {
        Mono(vec![(a, 1)])
    }
    pub fn factors(&self) -> &[(Atom, u32)] {
        &self.0
    }
    pub fn is_one(&self) -> bool {
        self.0.is_empty()
    }
    pub fn degree(&self) -> u32 {
        self.0.iter().map(|(_, e)| *e).sum()
    }
    pub fn mul(&self, other: &Mono) -> Mono {
        let (a, b) = (&self.0, &other.0);
        let mut out = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0, 0);
        while i < a.len() && j < b.len() {
            match a[i].0.cmp(&b[j].0) {
                std::cmp::Ordering::Less => {
                    out.push(a[i].clone());
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    out.push(b[j].clone());
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    out.push((a[i].0.clone(), a[i].1 + b[j].1));
                    i += 1;
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&a[i..]);
        out.extend_from_slice(&b[j..]);
        Mono(out)
    }
    /// self が other で割り切れるなら商を返す
    pub fn div(&self, other: &Mono) -> Option<Mono> {
        let mut out = Vec::new();
        let mut j = 0;
        let b = &other.0;
        for (a, e) in &self.0 {
            if j < b.len() && b[j].0 == *a {
                if b[j].1 > *e {
                    return None;
                }
                if *e > b[j].1 {
                    out.push((a.clone(), e - b[j].1));
                }
                j += 1;
            } else {
                if j < b.len() && b[j].0 < *a {
                    return None;
                }
                out.push((a.clone(), *e));
            }
        }
        if j < b.len() {
            return None;
        }
        Some(Mono(out))
    }
}

impl Poly {
    pub fn zero() -> Poly {
        Poly(Vec::new())
    }
    pub fn one() -> Poly {
        Poly::constant(Q::one())
    }
    pub fn constant(c: Q) -> Poly {
        if c.is_zero() {
            Poly::zero()
        } else {
            Poly(vec![(Mono::one(), c)])
        }
    }
    pub fn int(n: i64) -> Poly {
        Poly::constant(q(n))
    }
    pub fn from_atom(a: Atom) -> Poly {
        Poly(vec![(Mono::atom(a), Q::one())])
    }
    pub fn var(i: u32) -> Poly {
        Poly::from_atom(Atom::Var(i))
    }
    pub fn cnst(i: u32) -> Poly {
        Poly::from_atom(Atom::Const(i))
    }
    pub fn f(arg: Poly) -> Poly {
        Poly::from_atom(Atom::F(Rc::new(arg)))
    }
    pub fn inv(arg: Poly) -> Poly {
        Poly::from_atom(Atom::Inv(Rc::new(arg)))
    }
    pub fn mono(m: Mono, c: Q) -> Poly {
        if c.is_zero() {
            Poly::zero()
        } else {
            Poly(vec![(m, c)])
        }
    }
    /// 任意の (単項式, 係数) の列から正規形を作る
    pub fn from_terms(mut terms: Vec<(Mono, Q)>) -> Poly {
        terms.sort_by(|a, b| a.0.cmp(&b.0));
        let mut out: Vec<(Mono, Q)> = Vec::with_capacity(terms.len());
        for (m, c) in terms {
            if let Some(last) = out.last_mut() {
                if last.0 == m {
                    last.1 += c;
                    continue;
                }
            }
            out.push((m, c));
        }
        out.retain(|(_, c)| !c.is_zero());
        Poly(out)
    }
    pub fn terms(&self) -> &[(Mono, Q)] {
        &self.0
    }
    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
    pub fn as_const(&self) -> Option<Q> {
        match self.0.len() {
            0 => Some(Q::zero()),
            1 if self.0[0].0.is_one() => Some(self.0[0].1.clone()),
            _ => None,
        }
    }
    /// 正規形で最大の単項式の係数（零多項式なら None）
    pub fn leading_coeff(&self) -> Option<&Q> {
        self.0.last().map(|(_, c)| c)
    }
    pub fn add(&self, other: &Poly) -> Poly {
        let (a, b) = (&self.0, &other.0);
        let mut out = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0, 0);
        while i < a.len() && j < b.len() {
            match a[i].0.cmp(&b[j].0) {
                std::cmp::Ordering::Less => {
                    out.push(a[i].clone());
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    out.push(b[j].clone());
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    let c = &a[i].1 + &b[j].1;
                    if !c.is_zero() {
                        out.push((a[i].0.clone(), c));
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&a[i..]);
        out.extend_from_slice(&b[j..]);
        Poly(out)
    }
    pub fn neg(&self) -> Poly {
        Poly(self.0.iter().map(|(m, c)| (m.clone(), -c)).collect())
    }
    pub fn sub(&self, other: &Poly) -> Poly {
        self.add(&other.neg())
    }
    pub fn scale(&self, k: &Q) -> Poly {
        if k.is_zero() {
            return Poly::zero();
        }
        Poly(self.0.iter().map(|(m, c)| (m.clone(), c * k)).collect())
    }
    pub fn mul(&self, other: &Poly) -> Poly {
        if self.is_zero() || other.is_zero() {
            return Poly::zero();
        }
        if let Some(c) = other.as_const() {
            return self.scale(&c);
        }
        if let Some(c) = self.as_const() {
            return other.scale(&c);
        }
        let mut terms = Vec::with_capacity(self.0.len() * other.0.len());
        for (m1, c1) in &self.0 {
            for (m2, c2) in &other.0 {
                terms.push((m1.mul(m2), c1 * c2));
            }
        }
        Poly::from_terms(terms)
    }
    pub fn mul_mono(&self, m: &Mono, c: &Q) -> Poly {
        if c.is_zero() {
            return Poly::zero();
        }
        Poly::from_terms(self.0.iter().map(|(m1, c1)| (m1.mul(m), c1 * c)).collect())
    }
    pub fn pow(&self, e: u32) -> Poly {
        let mut r = Poly::one();
        for _ in 0..e {
            r = r.mul(self);
        }
        r
    }

    /// ボトムアップの原子置換: f や inv の引数を先に変換して原子を作り直し、
    /// その原子を `g` が返す多項式で置き換える。
    pub fn transform(&self, g: &mut dyn FnMut(Atom) -> Poly) -> Poly {
        let mut acc: Vec<(Mono, Q)> = Vec::new();
        let mut result = Poly::zero();
        let mut simple = true;
        for (m, c) in &self.0 {
            let mut prod = Poly::constant(c.clone());
            for (a, e) in &m.0 {
                let a2 = match a {
                    Atom::F(p) => Atom::F(Rc::new(p.transform(g))),
                    Atom::Inv(p) => Atom::Inv(Rc::new(p.transform(g))),
                    other => other.clone(),
                };
                let r = g(a2);
                prod = prod.mul(&r.pow(*e));
            }
            if simple && prod.0.len() <= 1 {
                acc.extend(prod.0);
            } else {
                simple = false;
                result = result.add(&prod);
            }
        }
        Poly::from_terms(acc).add(&result)
    }

    /// 変数の同時代入: Var(i) を s[i] に置き換える（s の範囲外の変数はそのまま）
    pub fn subst_vars(&self, s: &[Poly]) -> Poly {
        self.transform(&mut |a| match a {
            Atom::Var(i) if (i as usize) < s.len() => s[i as usize].clone(),
            other => Poly::from_atom(other),
        })
    }

    /// 現れる原子（f/inv の引数の中も含む）をすべて訪問する
    pub fn visit_atoms(&self, v: &mut dyn FnMut(&Atom)) {
        for (m, _) in &self.0 {
            for (a, _) in &m.0 {
                v(a);
                match a {
                    Atom::F(p) | Atom::Inv(p) => p.visit_atoms(v),
                    _ => {}
                }
            }
        }
    }
    pub fn vars(&self) -> BTreeSet<u32> {
        let mut s = BTreeSet::new();
        self.visit_atoms(&mut |a| {
            if let Atom::Var(i) = a {
                s.insert(*i);
            }
        });
        s
    }
    pub fn consts(&self) -> BTreeSet<u32> {
        let mut s = BTreeSet::new();
        self.visit_atoms(&mut |a| {
            if let Atom::Const(i) = a {
                s.insert(*i);
            }
        });
        s
    }
    pub fn has_var(&self) -> bool {
        self.0.iter().any(|(m, _)| m.0.iter().any(|(a, _)| a.has_var()))
    }
    pub fn has_f(&self) -> bool {
        self.0.iter().any(|(m, _)| m.0.iter().any(|(a, _)| a.has_f()))
    }
    pub fn has_inv(&self) -> bool {
        let mut found = false;
        self.visit_atoms(&mut |a| {
            if let Atom::Inv(_) = a {
                found = true;
            }
        });
        found
    }
    /// 最上位レベル（f の外）に現れる原子の集合
    pub fn top_atoms(&self) -> BTreeSet<Atom> {
        let mut s = BTreeSet::new();
        for (m, _) in &self.0 {
            for (a, _) in &m.0 {
                s.insert(a.clone());
            }
        }
        s
    }
    pub fn total_degree(&self) -> u32 {
        self.0.iter().map(|(m, _)| m.degree()).max().unwrap_or(0)
    }
    /// 定数倍で正規化: 最大の単項式の係数を 1 にする（零なら零）
    pub fn monic(&self) -> Poly {
        match self.leading_coeff() {
            None => Poly::zero(),
            Some(c) => {
                let inv = Q::one() / c;
                self.scale(&inv)
            }
        }
    }
    /// 正の定数倍で正規化: 最大の単項式の係数を ±1 にする
    pub fn sign_normal(&self) -> Poly {
        match self.leading_coeff() {
            None => Poly::zero(),
            Some(c) => {
                let inv = Q::one() / c.abs();
                self.scale(&inv)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// 表示（デバッグ・エラーメッセージ用の素朴な ASCII 表記。証明文の整形は fe_render が行う）

pub fn var_name(i: u32) -> String {
    const N: [&str; 6] = ["x", "y", "z", "w", "u", "v"];
    if (i as usize) < N.len() {
        N[i as usize].to_string()
    } else {
        format!("x{}", i)
    }
}

pub fn const_name(i: u32) -> String {
    const N: [&str; 12] = ["a", "b", "c", "d", "e", "g", "h", "k", "m", "n", "p", "q"];
    if (i as usize) < N.len() {
        N[i as usize].to_string()
    } else {
        format!("a{}", i)
    }
}

fn fmt_q(c: &Q) -> String {
    if c.is_integer() {
        format!("{}", c.numer())
    } else {
        format!("{}/{}", c.numer(), c.denom())
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Var(i) => write!(f, "{}", var_name(*i)),
            Atom::Const(i) => write!(f, "{}", const_name(*i)),
            Atom::F(p) => write!(f, "f({})", p),
            Atom::Inv(p) => write!(f, "inv({})", p),
        }
    }
}

impl fmt::Display for Mono {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for (a, e) in &self.0 {
            if !first {
                write!(f, "*")?;
            }
            first = false;
            if *e == 1 {
                write!(f, "{}", a)?;
            } else {
                write!(f, "{}^{}", a, e)?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for Poly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return write!(f, "0");
        }
        let mut first = true;
        for (m, c) in self.0.iter().rev() {
            let neg = c.is_negative();
            let a = c.abs();
            if first {
                if neg {
                    write!(f, "-")?;
                }
            } else {
                write!(f, " {} ", if neg { "-" } else { "+" })?;
            }
            first = false;
            if m.is_one() {
                write!(f, "{}", fmt_q(&a))?;
            } else if a.is_one() {
                write!(f, "{}", m)?;
            } else {
                write!(f, "{}*{}", fmt_q(&a), m)?;
            }
        }
        Ok(())
    }
}
