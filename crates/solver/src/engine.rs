//! 探索エンジン: 検証核への推論規則の呼び出しを組み立てる。
//! ここで作られる事実はすべて `Kernel` のメソッドの戻り値であり、探索部が事実を直接作ることはない。

use crate::matching::match_atom;
use crate::order::{all_atoms_less, atom_cmp};
use fe_kernel::{Atom, BranchId, Clause, Fact, Kernel, Lit, Poly, Rel, Q};
use num_traits::{One, Zero};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::time::Instant;

pub type Res<T> = Result<T, String>;

pub const TIMEOUT: &str = "時間切れ";

/// 書き換え規則: ∀v̄. lhs(v̄) → rhs(v̄)（事実 fact の等式から作る）
#[derive(Clone, Debug)]
pub struct RwRule {
    pub fact: Fact,
    pub nvars: u32,
    pub lhs: Atom,
    pub rhs: Poly,
}

/// 枝ごとの知識
#[derive(Clone)]
pub struct BState {
    pub b: BranchId,
    pub rules: Vec<RwRule>,
    /// 閉じた原子のべきの規則 a^k → rhs（rhs は a の次数 < k）
    pub pow_rules: Vec<(Fact, Atom, u32, Poly)>,
    /// 単位等式（正規化・簡約済み）
    pub units: Vec<Fact>,
    /// その他の節（選言・不等式など）
    pub others: Vec<Fact>,
    pub keys: HashSet<Clause>,
    pub cache: HashMap<Atom, Option<(Poly, Fact)>>,
    /// 枝で既に試した代入の記録
    pub tried: HashSet<String>,
}

impl BState {
    pub fn new(b: BranchId) -> BState {
        BState {
            b,
            rules: vec![],
            pow_rules: vec![],
            units: vec![],
            others: vec![],
            keys: HashSet::new(),
            cache: HashMap::new(),
            tried: HashSet::new(),
        }
    }
    /// 子の枝用の複製（キャッシュは引き継がない）
    pub fn child(&self, b: BranchId) -> BState {
        let mut s = self.clone();
        s.b = b;
        s.cache.clear();
        s
    }
}

pub struct Engine {
    pub k: Kernel,
    pub deadline: Instant,
    pub rewrite_budget: usize,
}

pub enum Added {
    New(Fact),
    Known,
    Contradiction(Fact),
    Trivial,
}

/// x ↔ y の入れ替え
pub fn swap_xy(p: &Poly) -> Poly {
    p.subst_vars(&[Poly::var(1), Poly::var(0)])
}

impl Engine {
    pub fn new(k: Kernel, deadline: Instant) -> Engine {
        Engine { k, deadline, rewrite_budget: 400 }
    }

    pub fn check_time(&self) -> Res<()> {
        if Instant::now() > self.deadline {
            Err(TIMEOUT.into())
        } else {
            Ok(())
        }
    }

    pub fn clause(&self, f: Fact) -> &Clause {
        self.k.clause(f)
    }
    pub fn lit0(&self, f: Fact) -> &Lit {
        &self.k.clause(f).lits()[0]
    }
    pub fn poly0(&self, f: Fact) -> Poly {
        self.k.clause(f).lits()[0].poly().clone()
    }
    pub fn nvars(&self, f: Fact) -> u32 {
        self.k.clause(f).nvars()
    }
    pub fn is_unit_eq(&self, f: Fact) -> bool {
        let c = self.k.clause(f);
        c.lits().len() == 1 && c.lits()[0].rel() == Rel::Eq
    }

    // ------------------------------------------------------------------
    // 書き換え

    /// 原子 a の正規形 r と、事実「a − r = 0」（保存形は λ(a − r)）を返す。変化しなければ None。
    pub fn norm_atom(&mut self, st: &mut BState, a: &Atom) -> Res<Option<(Poly, Fact)>> {
        if let Some(c) = st.cache.get(a) {
            return Ok(c.clone());
        }
        let r = self.norm_atom_uncached(st, a)?;
        st.cache.insert(a.clone(), r.clone());
        Ok(r)
    }

    fn atom_nvars(a: &Atom) -> u32 {
        Poly::from_atom(a.clone()).vars().iter().next_back().map_or(0, |m| m + 1)
    }

    fn norm_atom_uncached(&mut self, st: &mut BState, a: &Atom) -> Res<Option<(Poly, Fact)>> {
        let n = Self::atom_nvars(a);
        let b = st.b;
        // 証明の項目: a − cur = Σ coef · (保存形)
        let mut items: Vec<(Poly, Fact, usize)> = Vec::new();
        let mut cur_atom = a.clone();
        if let Atom::F(u) = a {
            let (u2, its) = self.rw_poly(st, u, n)?;
            if u2 != **u {
                let g = self.k.congruence(b, n, u2.clone(), its)?;
                let mu = coeff_of_atom(&self.poly0(g), a).ok_or("合同性の結果に原子がない")?;
                items.push((Poly::constant(Q::one() / mu), g, 0));
                cur_atom = Atom::F(std::rc::Rc::new(u2));
            }
        }
        if self.rewrite_budget == 0 {
            return Ok(None);
        }
        let mut cur = Poly::from_atom(cur_atom.clone());
        // 最上位の規則
        let mut applied = None;
        for (ri, r) in st.rules.iter().enumerate() {
            if let Some(s) = match_atom(&r.lhs, r.nvars, &cur_atom) {
                let rhs = r.rhs.subst_vars(&s);
                if all_atoms_less(&rhs, &cur_atom) {
                    applied = Some((ri, s, rhs));
                    break;
                }
            }
        }
        if let Some((ri, s, rhs)) = applied {
            self.rewrite_budget -= 1;
            let rf = st.rules[ri].fact;
            let inst = if st.rules[ri].nvars == 0 { rf } else { self.k.instantiate(b, rf, s, n)? };
            let lam = coeff_of_atom(&self.poly0(inst), &cur_atom).ok_or("例化の結果に原子がない")?;
            items.push((Poly::constant(Q::one() / lam), inst, 0));
            let (r2, its2) = self.rw_poly(st, &rhs, n)?;
            items.extend(its2);
            cur = r2;
        }
        if items.is_empty() {
            return Ok(None);
        }
        let fa = Poly::from_atom(a.clone());
        if cur == fa {
            return Ok(None);
        }
        // 項目が 1 つで、その事実がすでに a − cur の定数倍なら、それをそのまま使う
        if items.len() == 1 {
            let p = self.poly0(items[0].1);
            if p.monic() == fa.sub(&cur).monic() && self.nvars(items[0].1) <= n {
                return Ok(Some((cur, items[0].1)));
            }
        }
        let f = self.k.lincomb(b, n, items)?;
        // 確認: 保存形は a − cur の定数倍
        let p = self.poly0(f);
        let want = fa.sub(&cur);
        if p.monic() != want.monic() {
            return Err(format!("書き換えの結果が想定と違う: {} vs {}", p, want));
        }
        Ok(Some((cur, f)))
    }

    /// 多項式 p を正規化する。戻り値 (p', items) は p − p' = Σ coef · (保存形) を満たす。
    pub fn rw_poly(&mut self, st: &mut BState, p: &Poly, _n: u32) -> Res<(Poly, Vec<(Poly, Fact, usize)>)> {
        self.check_time()?;
        let mut items = Vec::new();
        let mut cur = p.clone();
        let atoms: Vec<Atom> = p.top_atoms().into_iter().collect();
        for a in atoms {
            if matches!(a, Atom::Var(_)) {
                continue;
            }
            if let Some((r, f)) = self.norm_atom(st, &a)? {
                let (cur2, q) = replace_atom(&cur, &a, &r);
                let lam = coeff_of_atom(&self.poly0(f), &a).ok_or("正規形の事実に原子がない")?;
                items.push((q.scale(&(Q::one() / lam)), f, 0));
                cur = cur2;
            }
        }
        // べきの規則 a^k → rhs
        for _ in 0..8 {
            let mut changed = false;
            for (pf, pa, k, rhs) in st.pow_rules.clone() {
                let (cur2, q) = reduce_power(&cur, &pa, k, &rhs);
                if q.is_zero() {
                    continue;
                }
                // 保存形 = λ (a^k − rhs)
                let stored = self.poly0(pf);
                let target = Poly::from_atom(pa.clone()).pow(k).sub(&rhs);
                let lam = lead_ratio(&stored, &target).ok_or("べき規則の保存形")?;
                items.push((q.scale(&(Q::one() / lam)), pf, 0));
                cur = cur2;
                changed = true;
            }
            if !changed {
                break;
            }
        }
        Ok((cur, items))
    }

    /// 節のすべてのリテラルを書き換える
    pub fn rewrite_clause(&mut self, st: &mut BState, f: Fact) -> Res<Fact> {
        self.rewrite_budget = 400;
        let mut cur = f;
        let n = self.nvars(f);
        let b = st.b;
        let mut i = 0;
        loop {
            let c = self.clause(cur).clone();
            if i >= c.lits().len() {
                break;
            }
            let l = c.lits()[i].clone();
            let (p2, items) = self.rw_poly(st, l.poly(), n)?;
            if items.is_empty() || p2 == *l.poly() {
                i += 1;
                continue;
            }
            let neg_items: Vec<(Poly, Fact, usize)> = items.iter().map(|(q, g, li)| (q.neg(), *g, *li)).collect();
            let newf = match l.rel() {
                Rel::Eq => {
                    let mut its = vec![(Poly::one(), cur, i)];
                    its.extend(neg_items);
                    self.k.lincomb(b, n, its)?
                }
                Rel::Gt | Rel::Ge => {
                    self.k.pos_comb(b, n, vec![(Q::one(), cur, i)], neg_items, vec![], Q::zero(), l.rel() == Rel::Gt)?
                }
                Rel::Ne => {
                    // p' = 0 ∨ p' ≠ 0 から p = 0 ∨ p' ≠ 0 を作り、p ≠ 0 ∨ S と導出
                    let em = self.k.eq_or_ne(b, n, p2.clone())?;
                    let ei = self.clause(em).lits().iter().position(|x| x.rel() == Rel::Eq).ok_or("EqOrNe")?;
                    let mut its = vec![(Poly::one(), em, ei)];
                    its.extend(items.iter().cloned());
                    let lc = self.k.lincomb(b, n, its)?;
                    let want = Lit::eq(l.poly().clone());
                    let li = self.clause(lc).lits().iter().position(|x| *x == want);
                    match li {
                        Some(li) => self.k.resolve(b, lc, li, cur, i)?,
                        None => {
                            i += 1;
                            continue;
                        }
                    }
                }
            };
            if self.clause(newf).lits().len() < c.lits().len() || self.clause(newf).is_false() {
                // リテラルが消えた（偽になった）: 最初からやり直す
                cur = newf;
                i = 0;
                continue;
            }
            cur = newf;
            i += 1;
            if i > 16 {
                break;
            }
        }
        Ok(cur)
    }

    /// 使われている変数を 0..k に詰める
    pub fn canon_vars(&mut self, st: &BState, f: Fact) -> Res<Fact> {
        let c = self.clause(f).clone();
        let used: Vec<u32> = c.lits().iter().flat_map(|l| l.poly().vars()).collect::<std::collections::BTreeSet<u32>>().into_iter().collect();
        let k = used.len() as u32;
        if used.iter().enumerate().all(|(i, &v)| v == i as u32) && c.nvars() == k {
            return Ok(f);
        }
        let mut s = vec![Poly::zero(); c.nvars() as usize];
        for (j, &v) in used.iter().enumerate() {
            s[v as usize] = Poly::var(j as u32);
        }
        self.k.instantiate(st.b, f, s, k)
    }

    // ------------------------------------------------------------------
    // 事実の追加と規則の抽出

    fn clause_key(c: &Clause) -> Clause {
        if c.nvars() == 2 {
            let sw: Vec<Lit> = c.lits().iter().map(|l| Lit::new(swap_xy(l.poly()), l.rel())).collect();
            let c2 = Clause::new(2, sw).unwrap();
            let a = format!("{:?}", c);
            let b = format!("{:?}", c2);
            if b < a {
                return c2;
            }
        }
        c.clone()
    }

    /// 事実を簡約して知識に加える
    pub fn add_fact(&mut self, st: &mut BState, f: Fact) -> Res<Added> {
        self.check_time()?;
        let f = self.canon_vars(st, f)?;
        let f = self.rewrite_clause(st, f)?;
        let f = self.canon_vars(st, f)?;
        let c = self.clause(f).clone();
        if c.is_false() {
            return Ok(Added::Contradiction(f));
        }
        if c.is_tautology() {
            return Ok(Added::Trivial);
        }
        let key = Self::clause_key(&c);
        if st.keys.contains(&key) {
            return Ok(Added::Known);
        }
        st.keys.insert(key);
        if c.lits().len() == 1 && c.lits()[0].rel() == Rel::Eq {
            st.units.push(f);
            if let Some(r) = self.extract_rule(f) {
                self.install_rule(st, r)?;
            } else if let Some((a, k, rhs)) = extract_power_rule(self.clause(f)) {
                st.pow_rules.push((f, a, k, rhs));
                st.cache.clear();
                self.reduce_all(st)?;
            }
        } else {
            st.others.push(f);
        }
        Ok(Added::New(f))
    }

    /// 単位等式から書き換え規則を作る（左辺は単独で現れる最大の原子）
    pub fn extract_rule(&self, f: Fact) -> Option<RwRule> {
        let c = self.clause(f);
        if c.lits().len() != 1 || c.lits()[0].rel() != Rel::Eq || c.nvars() > 1 {
            return None;
        }
        let p = c.lits()[0].poly();
        let mut best: Option<(Atom, Q)> = None;
        for (m, coef) in p.terms() {
            if m.factors().len() != 1 || m.factors()[0].1 != 1 {
                continue;
            }
            let a = &m.factors()[0].0;
            if matches!(a, Atom::Var(_)) {
                continue;
            }
            // a が他の単項式に現れないこと
            let elsewhere = p.terms().iter().any(|(m2, _)| m2 != m && m2.factors().iter().any(|(b, _)| b == a));
            if elsewhere {
                continue;
            }
            let rest = p.sub(&Poly::mono(m.clone(), coef.clone()));
            if !all_atoms_less(&rest, a) {
                continue;
            }
            let av = Poly::from_atom(a.clone()).vars();
            if !rest.vars().is_subset(&av) {
                continue;
            }
            if best.as_ref().map_or(true, |(b, _)| atom_cmp(a, b) == Ordering::Greater) {
                best = Some((a.clone(), coef.clone()));
            }
        }
        let (a, coef) = best?;
        let rest = p.sub(&Poly::from_atom(a.clone()).scale(&coef));
        let rhs = rest.scale(&(-Q::one() / coef));
        Some(RwRule { fact: f, nvars: c.nvars(), lhs: a, rhs })
    }

    /// 規則を加え、既存の単位等式・規則を相互簡約する
    pub fn install_rule(&mut self, st: &mut BState, r: RwRule) -> Res<()> {
        st.rules.push(r);
        st.cache.clear();
        // 相互簡約
        let mut changed = true;
        let mut rounds = 0;
        while changed && rounds < 6 {
            changed = false;
            rounds += 1;
            let units = st.units.clone();
            for u in units {
                self.check_time()?;
                // 自分自身の規則で自分を書き換えないよう、u の規則を一時的に外す
                let saved: Vec<RwRule> = st.rules.clone();
                st.rules.retain(|x| x.fact != u);
                st.cache.clear();
                let u2 = self.rewrite_clause(st, u);
                st.rules = saved;
                st.cache.clear();
                let u2 = u2?;
                if u2 == u {
                    continue;
                }
                let u2 = self.canon_vars(st, u2)?;
                // u を u2 で置き換える
                st.units.retain(|x| *x != u);
                st.rules.retain(|x| x.fact != u);
                changed = true;
                let c = self.clause(u2).clone();
                if c.is_false() {
                    st.others.push(u2);
                    continue;
                }
                if c.is_tautology() {
                    continue;
                }
                let key = Self::clause_key(&c);
                if st.keys.contains(&key) && st.units.iter().any(|x| Self::clause_key(self.clause(*x)) == key) {
                    continue;
                }
                st.keys.insert(key);
                if c.lits().len() == 1 && c.lits()[0].rel() == Rel::Eq {
                    st.units.push(u2);
                    if let Some(r2) = self.extract_rule(u2) {
                        st.rules.push(r2);
                    }
                } else {
                    st.others.push(u2);
                }
                st.cache.clear();
            }
        }
        Ok(())
    }

    /// すべての単位等式を現在の規則で簡約し直す
    pub fn reduce_all(&mut self, st: &mut BState) -> Res<()> {
        let units = st.units.clone();
        for u in units {
            self.check_time()?;
            if st.pow_rules.iter().any(|p| p.0 == u) {
                continue;
            }
            let saved = st.rules.clone();
            st.rules.retain(|x| x.fact != u);
            st.cache.clear();
            let u2 = self.rewrite_clause(st, u);
            st.rules = saved;
            st.cache.clear();
            let u2 = u2?;
            if u2 == u {
                continue;
            }
            st.units.retain(|x| *x != u);
            st.rules.retain(|x| x.fact != u);
            let c = self.clause(u2).clone();
            if c.is_tautology() {
                continue;
            }
            if c.is_false() {
                st.others.push(u2);
                continue;
            }
            st.keys.insert(Self::clause_key(&c));
            if c.lits().len() == 1 && c.lits()[0].rel() == Rel::Eq {
                st.units.push(u2);
                if let Some(r2) = self.extract_rule(u2) {
                    st.rules.push(r2);
                }
            } else {
                st.others.push(u2);
            }
        }
        st.cache.clear();
        Ok(())
    }

    /// 枝に矛盾があれば返す
    pub fn find_contradiction(&self, st: &BState) -> Option<Fact> {
        st.others.iter().chain(st.units.iter()).copied().find(|f| self.clause(*f).is_false())
    }
}

/// p の最上位で原子 a を r に置き換えた p' と、p − p' = q·(a − r) を満たす q を返す
pub fn replace_atom(p: &Poly, a: &Atom, r: &Poly) -> (Poly, Poly) {
    let mut out = Poly::zero();
    let mut q = Poly::zero();
    let ap = Poly::from_atom(a.clone());
    for (m, c) in p.terms() {
        let e = m.factors().iter().find(|(b, _)| b == a).map(|(_, e)| *e).unwrap_or(0);
        if e == 0 {
            out = out.add(&Poly::mono(m.clone(), c.clone()));
            continue;
        }
        let mut rest_p = Poly::constant(c.clone());
        for (b, eb) in m.factors() {
            if b != a {
                rest_p = rest_p.mul(&Poly::from_atom(b.clone()).pow(*eb));
            }
        }
        out = out.add(&rest_p.mul(&r.pow(e)));
        // a^e − r^e = (a − r) Σ a^{e−1−i} r^i
        let mut s = Poly::zero();
        for i in 0..e {
            s = s.add(&ap.pow(e - 1 - i).mul(&r.pow(i)));
        }
        q = q.add(&rest_p.mul(&s));
    }
    (out, q)
}

/// 多項式の中で、単独の単項式 a（指数 1）の係数
pub fn coeff_of_atom(p: &Poly, a: &Atom) -> Option<Q> {
    for (m, c) in p.terms() {
        if m.factors().len() == 1 && m.factors()[0].0 == *a && m.factors()[0].1 == 1 {
            return Some(c.clone());
        }
    }
    None
}

/// 閉じた単位等式 c·a^k + (a の次数 < k の項) = 0 から a^k → rhs を作る（k ≥ 2, a は最大の原子）
pub fn extract_power_rule(c: &Clause) -> Option<(Atom, u32, Poly)> {
    if c.nvars() != 0 || c.lits().len() != 1 || c.lits()[0].rel() != Rel::Eq {
        return None;
    }
    let p = c.lits()[0].poly();
    let a = crate::order::max_atom(p)?;
    let cs = crate::polyutil::coeffs_in(p, &a);
    let k = *cs.keys().next_back()?;
    if k < 2 {
        return None;
    }
    let lc = cs.get(&k)?.as_const()?;
    let rest = p.sub(&Poly::from_atom(a.clone()).pow(k).scale(&lc));
    let rhs = rest.scale(&(-Q::one() / lc));
    Some((a, k, rhs))
}

/// p の中の a^e (e ≥ k) を a^(e−k)·rhs に置き換える。p − p' = q·(a^k − rhs)
pub fn reduce_power(p: &Poly, a: &Atom, k: u32, rhs: &Poly) -> (Poly, Poly) {
    let mut cur = p.clone();
    let mut q = Poly::zero();
    let ap = Poly::from_atom(a.clone());
    let ak = ap.pow(k);
    for _ in 0..32 {
        // a の次数が k 以上の項を 1 段下げる
        let mut hi = Poly::zero();
        for (m, c) in cur.terms() {
            let e = m.factors().iter().find(|(b, _)| b == a).map(|(_, e)| *e).unwrap_or(0);
            if e >= k {
                hi = hi.add(&Poly::mono(m.clone(), c.clone()));
            }
        }
        if hi.is_zero() {
            break;
        }
        // hi = s·a^k
        let s = crate::polyutil::div_mono(&hi, &Poly::from_atom(a.clone()).pow(k).terms()[0].0);
        cur = cur.sub(&s.mul(&ak.sub(rhs)));
        q = q.add(&s);
    }
    (cur, q)
}

/// stored = λ·target なら λ
pub fn lead_ratio(stored: &Poly, target: &Poly) -> Option<Q> {
    let (m, c) = target.terms().last()?;
    let c2 = stored.terms().iter().find(|(m2, _)| m2 == m)?.1.clone();
    let lam = c2 / c;
    if target.scale(&lam) == *stored {
        Some(lam)
    } else {
        None
    }
}
