//! リテラルと節（検証核の一部）。
//!
//! リテラル `Lit { poly: p, rel }` は次のいずれかを表す:
//!   Eq: p = 0,   Ne: p ≠ 0,   Gt: p > 0,   Ge: p ≥ 0
//! 節 `Clause { nvars: n, lits }` は「任意の実数 v0, …, v(n-1) について lits のどれかが成り立つ」を表す。
//! リテラルが空の節は矛盾（偽）を表す。
//!
//! 正規化（意味を変えない変形だけ）:
//!   - Eq/Ne は 0 でない定数倍で、Gt/Ge は正の定数倍で、最大単項式の係数を 1（Gt/Ge は ±1）にそろえる。
//!   - 定数多項式のリテラルは真偽が決まる。偽のリテラルは選言から取り除いてよい。
//!   - 選言の順序と重複は意味に影響しないので、整列して重複を除く。

use crate::poly::{Poly, Q};
use num_traits::{Signed, Zero};
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Rel {
    Eq,
    Ne,
    Gt,
    Ge,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Lit {
    poly: Poly,
    rel: Rel,
}

impl Lit {
    /// 正規化してリテラルを作る（意味は p rel 0 のまま）
    pub fn new(poly: Poly, rel: Rel) -> Lit {
        let poly = match rel {
            Rel::Eq | Rel::Ne => poly.monic(),
            Rel::Gt | Rel::Ge => poly.sign_normal(),
        };
        Lit { poly, rel }
    }
    pub fn eq(p: Poly) -> Lit {
        Lit::new(p, Rel::Eq)
    }
    pub fn ne(p: Poly) -> Lit {
        Lit::new(p, Rel::Ne)
    }
    pub fn gt(p: Poly) -> Lit {
        Lit::new(p, Rel::Gt)
    }
    pub fn ge(p: Poly) -> Lit {
        Lit::new(p, Rel::Ge)
    }
    pub fn poly(&self) -> &Poly {
        &self.poly
    }
    pub fn rel(&self) -> Rel {
        self.rel
    }
    /// 否定: ¬(p=0) ⇔ p≠0,  ¬(p>0) ⇔ -p≥0,  ¬(p≥0) ⇔ -p>0
    pub fn negate(&self) -> Lit {
        match self.rel {
            Rel::Eq => Lit::new(self.poly.clone(), Rel::Ne),
            Rel::Ne => Lit::new(self.poly.clone(), Rel::Eq),
            Rel::Gt => Lit::new(self.poly.neg(), Rel::Ge),
            Rel::Ge => Lit::new(self.poly.neg(), Rel::Gt),
        }
    }
    /// 定数リテラルなら真偽を返す
    pub fn truth(&self) -> Option<bool> {
        let c: Q = self.poly.as_const()?;
        Some(match self.rel {
            Rel::Eq => c.is_zero(),
            Rel::Ne => !c.is_zero(),
            Rel::Gt => c.is_positive(),
            Rel::Ge => !c.is_negative(),
        })
    }
    pub fn subst_vars(&self, s: &[Poly]) -> Lit {
        Lit::new(self.poly.subst_vars(s), self.rel)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Clause {
    nvars: u32,
    lits: Vec<Lit>,
}

impl Clause {
    /// 正規化して節を作る。変数番号が nvars 以上なら誤り。
    pub fn new(nvars: u32, lits: Vec<Lit>) -> Result<Clause, String> {
        for l in &lits {
            if let Some(&m) = l.poly.vars().iter().next_back() {
                if m >= nvars {
                    return Err(format!("変数 v{} が節の変数の個数 {} を超えている", m, nvars));
                }
            }
        }
        let mut lits: Vec<Lit> = lits
            .into_iter()
            .map(|l| Lit::new(l.poly, l.rel))
            .filter(|l| l.truth() != Some(false))
            .collect();
        lits.sort();
        lits.dedup();
        Ok(Clause { nvars, lits })
    }
    pub fn nvars(&self) -> u32 {
        self.nvars
    }
    pub fn lits(&self) -> &[Lit] {
        &self.lits
    }
    /// 矛盾（空の選言）
    pub fn is_false(&self) -> bool {
        self.lits.is_empty()
    }
    /// 常に真のリテラルを含む
    pub fn is_tautology(&self) -> bool {
        self.lits.iter().any(|l| l.truth() == Some(true))
    }
    pub fn is_unit(&self) -> bool {
        self.lits.len() == 1
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let r = match self.rel {
            Rel::Eq => "=",
            Rel::Ne => "!=",
            Rel::Gt => ">",
            Rel::Ge => ">=",
        };
        write!(f, "{} {} 0", self.poly, r)
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.nvars > 0 {
            write!(f, "forall")?;
            for i in 0..self.nvars {
                write!(f, " {}", crate::poly::var_name(i))?;
            }
            write!(f, ". ")?;
        }
        if self.lits.is_empty() {
            return write!(f, "FALSE");
        }
        for (i, l) in self.lits.iter().enumerate() {
            if i > 0 {
                write!(f, " | ")?;
            }
            write!(f, "{}", l)?;
        }
        Ok(())
    }
}
