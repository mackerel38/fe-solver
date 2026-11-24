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
    /// 閉じた単項式の規則 m → rhs（a^k → a の次数 < k の式、f(j)·inv(f(j)) → 1 など）
    pub pow_rules: Vec<(Fact, fe_kernel::Mono, Poly)>,
    /// 閉じた ≠ 0 の事実
    pub nes: Vec<Fact>,
    /// 逆数のわかっている閉じた式 (u, inv(u))
    pub invs: Vec<(Poly, Poly)>,
    /// 単射性の仮定「∀x,y. f(x) − f(y) ≠ 0 ∨ x − y = 0」
    pub inj: Option<Fact>,
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
            nes: vec![],
            invs: vec![],
            inj: None,
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
    pub timing: std::collections::BTreeMap<&'static str, u128>,
    add_depth: u32,
    pub size_cap: u32,
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
        Engine { k, deadline, rewrite_budget: 400, timing: Default::default(), add_depth: 0, size_cap: 80 }
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
            // 解の形の規則 f(x) → g(x; f(c)…) は、自分のパラメータ f(c) を書き換えない
            if !cur_atom.has_var() && r.nvars == 1 && matches!(&r.lhs, Atom::F(p) if **p == Poly::var(0)) {
                let mut is_param = false;
                r.rhs.visit_atoms(&mut |b| {
                    if *b == cur_atom {
                        is_param = true;
                    }
                });
                if is_param {
                    continue;
                }
            }
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
            for (pf, pm, rhs) in st.pow_rules.clone() {
                let (cur2, q) = reduce_mono(&cur, &pm, &rhs);
                if q.is_zero() {
                    continue;
                }
                // 保存形 = λ (m − rhs)
                let stored = self.poly0(pf);
                let target = Poly::mono(pm.clone(), Q::one()).sub(&rhs);
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
        let t0 = Instant::now();
        let r = self.rewrite_clause_inner(st, f);
        *self.timing.entry("rewrite_clause").or_insert(0) += t0.elapsed().as_micros();
        r
    }
    fn rewrite_clause_inner(&mut self, st: &mut BState, f: Fact) -> Res<Fact> {
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
        if self.add_depth > 8 {
            return Ok(Added::Trivial);
        }
        self.add_depth += 1;
        let r = self.add_fact_inner(st, f);
        self.add_depth -= 1;
        r
    }

    fn add_fact_inner(&mut self, st: &mut BState, f: Fact) -> Res<Added> {
        let f = self.canon_vars(st, f)?;
        let f = self.rewrite_clause(st, f)?;
        let f = self.canon_vars(st, f)?;
        let f = self.resolve_nes(st, f)?;
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
        // 大きすぎる事実は捨てる（探索の効率のため。捨てても健全性には影響しない）
        if c.nvars() > 0 && c.lits().iter().map(|l| crate::order::poly_size(l.poly())).sum::<u32>() > self.size_cap {
            return Ok(Added::Trivial);
        }
        st.keys.insert(key.clone());
        if c.lits().len() == 1 && c.lits()[0].rel() == Rel::Eq {
            // 左辺が f(a·x + b)（b は閉じた式, (a,b) ≠ (1,0)）の規則は x → (x − b)/a で f(x) の形に直す
            if let Some(r) = self.extract_rule(f) {
                if let Some(sub) = affine_lhs_normalizer(&r) {
                    let g = self.k.instantiate(st.b, f, vec![sub], 1)?;
                    st.keys.remove(&key);
                    return self.add_fact(st, g);
                }
            }
            st.units.push(f);
            if std::env::var("FE_DEBUG").is_ok() && c.nvars() == 0 {
                eprintln!("add closed unit b{}: {}  rule={:?}", st.b.0, c, self.extract_rule(f).map(|r| r.lhs.to_string()));
            }
            if let Some(r) = self.extract_rule(f) {
                self.install_rule(st, r)?;
            } else if let Some((m, rhs)) = extract_power_rule(self.clause(f)) {
                st.pow_rules.push((f, m, rhs));
                st.cache.clear();
                self.reduce_all(st)?;
            }
        } else {
            if c.nvars() == 0 && c.lits().len() == 1 && c.lits()[0].rel() == Rel::Ne {
                st.nes.push(f);
                self.make_inverse(st, f)?;
            }
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
        // 複雑すぎる左辺の規則は作らない（ほとんど適用されず、相互簡約の費用だけがかかる）
        if crate::order::atom_weight(&a) > 24 || crate::order::atom_depth(&a) > 3 {
            return None;
        }
        let rest = p.sub(&Poly::from_atom(a.clone()).scale(&coef));
        let rhs = rest.scale(&(-Q::one() / coef));
        Some(RwRule { fact: f, nvars: c.nvars(), lhs: a, rhs })
    }

    /// 規則を加え、既存の単位等式・規則を相互簡約する
    pub fn install_rule(&mut self, st: &mut BState, r: RwRule) -> Res<()> {
        let t0 = Instant::now();
        let res = self.install_rule_inner(st, r);
        *self.timing.entry("install_rule").or_insert(0) += t0.elapsed().as_micros();
        res
    }
    fn install_rule_inner(&mut self, st: &mut BState, r: RwRule) -> Res<()> {
        st.rules.push(r.clone());
        self.invalidate_cache(st, &r);
        // 新しい規則で簡約できる単位等式だけを書き換え直す（連鎖的に生じた規則も同様）
        let mut queue = vec![r];
        let mut steps = 0;
        while let Some(newr) = queue.pop() {
            steps += 1;
            if steps > 64 {
                break;
            }
            let units = st.units.clone();
            for u in units {
                self.check_time()?;
                if u == newr.fact || !st.units.contains(&u) {
                    continue;
                }
                if !self.reducible_by(u, &newr) {
                    continue;
                }
                if let Some(r2) = self.resimplify_unit(st, u)? {
                    queue.push(r2);
                }
            }
        }
        Ok(())
    }

    /// 既知の閉じた ≠ 0 の事実で、選言中の等式リテラル u = 0 を取り除く
    pub fn resolve_nes(&mut self, st: &mut BState, f: Fact) -> Res<Fact> {
        let mut cur = f;
        loop {
            let c = self.clause(cur).clone();
            if c.lits().is_empty() {
                return Ok(cur);
            }
            let mut hit = None;
            'outer: for (i, l) in c.lits().iter().enumerate() {
                if l.rel() != Rel::Eq || l.poly().has_var() {
                    continue;
                }
                for &ne in &st.nes {
                    if self.clause(ne).lits()[0] == l.negate() {
                        hit = Some((i, ne));
                        break 'outer;
                    }
                }
            }
            match hit {
                Some((i, ne)) => cur = self.k.resolve(st.b, cur, i, ne, 0)?,
                None => break,
            }
        }
        // 単位等式 u·Q = 0 で u ≠ 0 が既知なら Q = 0
        for _ in 0..4 {
            let c = self.clause(cur).clone();
            if c.lits().len() != 1 || c.lits()[0].rel() != Rel::Eq {
                return Ok(cur);
            }
            let p = c.lits()[0].poly().clone();
            let mut done = true;
            for &ne in &st.nes.clone() {
                let u = self.poly0(ne);
                if u.as_const().is_some() {
                    continue;
                }
                if let Some(q) = crate::polyutil::exact_div(&p, &u) {
                    if q.as_const().is_some() {
                        continue;
                    }
                    let z = self.k.zero_product(st.b, cur, 0, vec![u.clone(), q])?;
                    let zc = self.clause(z).clone();
                    if let Some(i) = zc.lits().iter().position(|l| *l == Lit::eq(u.clone())) {
                        cur = self.k.resolve(st.b, z, i, ne, 0)?;
                        done = false;
                        break;
                    }
                }
            }
            if done {
                break;
            }
        }
        Ok(cur)
    }

    /// 閉じた u ≠ 0 から u·inv(u) = 1 を作り、単項式の規則として登録する（u が単一の原子のとき）
    fn make_inverse(&mut self, st: &mut BState, ne: Fact) -> Res<()> {
        let u = self.poly0(ne);
        if u.terms().len() != 1 || !u.terms()[0].1.is_one() || u.terms()[0].0.factors().len() != 1 || u.terms()[0].0.factors()[0].1 != 1 {
            return Ok(());
        }
        if st.invs.iter().any(|(v, _)| *v == u) {
            return Ok(());
        }
        let ax = self.k.inv_axiom(st.b, 0, u.clone())?;
        let i = self.clause(ax).lits().iter().position(|l| *l == Lit::eq(u.clone())).ok_or("inv")?;
        let r = self.k.resolve(st.b, ax, i, ne, 0)?;
        let m = u.mul(&Poly::inv(u.clone()));
        if m.terms().len() != 1 {
            return Ok(());
        }
        st.pow_rules.push((r, m.terms()[0].0.clone(), Poly::one()));
        st.invs.push((u.clone(), Poly::inv(u)));
        Ok(())
    }

    /// 新しい規則で簡約できる原子を含むキャッシュ項目だけを消す
    pub fn invalidate_cache(&self, st: &mut BState, r: &RwRule) {
        let ld = crate::order::atom_depth(&r.lhs);
        let hit = |p: &Poly| -> bool {
            let mut found = false;
            p.visit_atoms(&mut |a| {
                if found || !matches!(a, Atom::F(_)) || crate::order::atom_depth(a) < ld {
                    return;
                }
                if let Some(s) = match_atom(&r.lhs, r.nvars, a) {
                    if all_atoms_less(&r.rhs.subst_vars(&s), a) {
                        found = true;
                    }
                }
            });
            found
        };
        st.cache.retain(|k, v| {
            if hit(&Poly::from_atom(k.clone())) {
                return false;
            }
            match v {
                Some((r2, _)) => !hit(r2),
                None => true,
            }
        });
    }

    /// 事実 u のどこか（入れ子も含む）に規則 r が適用できるか
    fn reducible_by(&self, u: Fact, r: &RwRule) -> bool {
        let mut found = false;
        let ld = crate::order::atom_depth(&r.lhs);
        for l in self.clause(u).lits() {
            l.poly().visit_atoms(&mut |a| {
                if found || !matches!(a, Atom::F(_)) || crate::order::atom_depth(a) < ld {
                    return;
                }
                if let Some(s) = match_atom(&r.lhs, r.nvars, a) {
                    if all_atoms_less(&r.rhs.subst_vars(&s), a) {
                        found = true;
                    }
                }
            });
        }
        found
    }

    /// 単位等式 u を、u 自身の規則を除いた規則で書き換え直して置き換える。新しい規則ができれば返す。
    fn resimplify_unit(&mut self, st: &mut BState, u: Fact) -> Res<Option<RwRule>> {
        let saved_cache = std::mem::take(&mut st.cache);
        let saved_rules = st.rules.clone();
        st.rules.retain(|x| x.fact != u);
        let u2 = self.rewrite_clause(st, u);
        st.rules = saved_rules;
        st.cache = saved_cache;
        let u2 = u2?;
        if u2 == u {
            return Ok(None);
        }
        let u2 = self.canon_vars(st, u2)?;
        st.units.retain(|x| *x != u);
        st.rules.retain(|x| x.fact != u);
        let c = self.clause(u2).clone();
        if c.is_false() {
            st.others.push(u2);
            return Ok(None);
        }
        if c.is_tautology() {
            return Ok(None);
        }
        let key = Self::clause_key(&c);
        if st.units.iter().any(|x| Self::clause_key(self.clause(*x)) == key) {
            return Ok(None);
        }
        st.keys.insert(key);
        if c.lits().len() == 1 && c.lits()[0].rel() == Rel::Eq {
            st.units.push(u2);
            if let Some(r2) = self.extract_rule(u2) {
                st.rules.push(r2.clone());
                self.invalidate_cache(st, &r2);
                return Ok(Some(r2));
            }
        } else {
            st.others.push(u2);
        }
        Ok(None)
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
pub fn extract_power_rule(c: &Clause) -> Option<(fe_kernel::Mono, Poly)> {
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
    let m = Poly::from_atom(a).pow(k).terms()[0].0.clone();
    Some((m, rhs))
}

/// p の中で単項式 m で割り切れる項を m → rhs で置き換える。p − p' = q·(m − rhs)
pub fn reduce_mono(p: &Poly, m: &fe_kernel::Mono, rhs: &Poly) -> (Poly, Poly) {
    let mut cur = p.clone();
    let mut q = Poly::zero();
    let mp = Poly::mono(m.clone(), Q::one());
    for _ in 0..32 {
        let mut s = Poly::zero();
        for (tm, c) in cur.terms() {
            if let Some(rest) = tm.div(m) {
                s = s.add(&Poly::mono(rest, c.clone()));
            }
        }
        if s.is_zero() {
            break;
        }
        cur = cur.sub(&s.mul(&mp.sub(rhs)));
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

/// 規則の左辺が f(a·x + b)（1 変数, b は閉じた式）で f(x) でないなら、x に代入すべき (x − b)/a を返す
pub fn affine_lhs_normalizer(r: &RwRule) -> Option<Poly> {
    if r.nvars != 1 {
        return None;
    }
    let arg = match &r.lhs {
        Atom::F(p) => (**p).clone(),
        _ => return None,
    };
    if arg == Poly::var(0) {
        return None;
    }
    // 右辺が x の f を含まない（正規化すると解の形 f(x) = g(x) になる）場合だけ
    let mut bad = false;
    r.rhs.visit_atoms(&mut |a| {
        if matches!(a, Atom::F(_) | Atom::Inv(_)) && a.has_var() {
            bad = true;
        }
    });
    if bad {
        return None;
    }
    let cs = crate::polyutil::coeffs_in(&arg, &Atom::Var(0));
    if cs.keys().max() != Some(&1) {
        return None;
    }
    let a = cs.get(&1)?.as_const()?;
    let b = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
    if b.has_var() {
        return None;
    }
    Some(Poly::var(0).sub(&b).scale(&(Q::one() / a)))
}
