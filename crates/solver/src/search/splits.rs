//! 場合分け: f ≡ 0、恒等関数、閉じた係数、各点の選言、変数を共有しない選言、閉じた因数分解（docs/TACTICS.md）
#![allow(unused_imports)]

use crate::engine::{coeff_of_atom, replace_atom, Added, BState, Engine, Res, RwRule, TIMEOUT};
use crate::order::{atom_cmp, poly_size};
use crate::polyutil::*;
use fe_kernel::{AddFamily, AddKind, Atom, BranchId, Fact, Family, Kernel, Lit, Mono, Poly, Rel, Q};
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use super::util::*;
use super::{Fin, Searcher};

impl Searcher {
    /// f ≡ 0 が解なら「∀x. f(x) = 0」か「ある j で f(j) ≠ 0」かで場合を分ける（排中律）
    pub(crate) fn zero_split(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        if st.tried.contains("zero_split") {
            return Ok(false);
        }
        st.tried.insert("zero_split".into());
        if self.e.k.verify_solution(&Poly::zero()).is_err() {
            return Ok(false);
        }
        let c = fe_kernel::Clause::new(1, vec![Lit::eq(Poly::f(x()))]).map_err(|e| e.to_string())?;
        self.bump("zero_split");
        let (c0, h0, c1, hs, _consts) = self.e.k.split_em(st.b, c)?;
        let children = vec![(c0, h0), (c1, hs[0])];
        self.run_children(st, children, depth)?;
        Ok(true)
    }

    /// 恒等関数の候補による場合分け: 「∀x. f(x) = x」か「ある a で f(a) ≠ a」か（排中律）。
    /// 後者では点 a と f(a) − a ≠ 0（逆数）を代入・約分に使う。
    pub(crate) fn identity_split(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        if st.tried.contains("id_split") || self.solution_rule(st).is_some() {
            return Ok(false);
        }
        st.tried.insert("id_split".into());
        let c = fe_kernel::Clause::new(1, vec![Lit::eq(Poly::f(x()).sub(&x()))]).map_err(|e| e.to_string())?;
        let (c0, h0, c1, hs, _consts) = self.e.k.split_em(st.b, c)?;
        self.bump("id_split");
        let children = vec![(c0, h0), (c1, hs[0])];
        // 子 0 は f(x) = x なのですぐ終わる。子 1 に残り時間のほとんどが回る
        let mut ch = children.into_iter();
        let (b0, h0) = ch.next().unwrap();
        let mut s0 = st.child(b0);
        s0.tried.insert("id_split".into());
        match self.e.add_fact(&mut s0, h0) {
            Ok(_) => self.solve_branch(s0, depth + 1)?,
            Err(m) if m == TIMEOUT => self.open.push((b0, TIMEOUT.into())),
            Err(m) => return Err(m),
        }
        let (b1, h1) = ch.next().unwrap();
        let mut s1 = st.child(b1);
        s1.tried.insert("id_split".into());
        match self.e.add_fact(&mut s1, h1) {
            Ok(_) => self.solve_branch(s1, depth + 1)?,
            Err(m) if m == TIMEOUT => self.open.push((b1, TIMEOUT.into())),
            Err(m) => return Err(m),
        }
        Ok(true)
    }

    /// 閉じた係数 a（f(a·x + b) の a や a·f(x) の a）について「a = 0」と「a ≠ 0」に分ける（a ≠ 0 側では逆数を使える）
    pub(crate) fn coef_split(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        let fx = Atom::F(std::rc::Rc::new(x()));
        let mut cands: Vec<Poly> = Vec::new();
        for &u in &st.units {
            if self.e.nvars(u) != 1 {
                continue;
            }
            let p = self.e.poly0(u);
            let fatoms = f_atoms_with_vars(&p);
            if fatoms.len() != 1 {
                continue;
            }
            let arg = &fatoms[0];
            let cs = coeffs_in(arg, &Atom::Var(0));
            if cs.keys().max() == Some(&1) {
                if let Some(a) = cs.get(&1) {
                    if a.as_const().is_none() && !a.has_var() && !cands.contains(a) {
                        cands.push(a.clone());
                    }
                }
            }
            if *arg == x() {
                let c2 = coeffs_in(&p, &fx);
                if c2.keys().max() == Some(&1) {
                    if let Some(c) = c2.get(&1) {
                        if c.as_const().is_none() && !c.has_var() && !cands.contains(c) {
                            cands.push(c.clone());
                        }
                    }
                }
            }
        }
        for a in cands {
            let an = a.monic();
            let key = format!("coef|{:x}", hash_poly(&an));
            if !st.tried.insert(key) {
                continue;
            }
            if st.invs.iter().any(|(u, _)| u.monic() == an) {
                continue;
            }
            // 既に 0 とわかっているなら分けない
            let (a2, _) = self.e.rw_poly(st, &a, 0)?;
            if a2.is_zero() || a2.as_const().is_some() {
                continue;
            }
            let c = fe_kernel::Clause::new(0, vec![Lit::eq(a2)]).map_err(|e| e.to_string())?;
            let (c0, h0, c1, hs, _) = self.e.k.split_em(st.b, c)?;
            self.bump("coef_split");
            let children = vec![(c0, h0), (c1, hs[0])];
            self.run_children(st, children, depth)?;
            return Ok(true);
        }
        Ok(false)
    }

    /// 各点ごとの選言 ∀x. f(x) = g₁(x) ∨ … ∨ f(x) = g_k(x)（g_i は x の f を含まない）を探す
    pub(crate) fn pointwise_clauses(&self, st: &BState) -> Vec<(Fact, Vec<Poly>)> {
        let fx = Atom::F(std::rc::Rc::new(x()));
        let mut out = Vec::new();
        for &f in &st.others {
            let c = self.e.clause(f);
            if c.nvars() != 1 || c.lits().len() < 2 || c.lits().iter().any(|l| l.rel() != Rel::Eq) {
                continue;
            }
            let fmx = Atom::F(std::rc::Rc::new(x().neg()));
            let mut gs = Vec::new();
            for l in c.lits() {
                let p = l.poly();
                // f(x) − g(x) の形、または f(−x) − h(x) の形（このとき候補は g(t) = h(−t)）
                let (atom, reflect) = if coeff_of_atom(p, &fx).is_some() && !p.top_atoms().contains(&fmx) {
                    (fx.clone(), false)
                } else if coeff_of_atom(p, &fmx).is_some() && !p.top_atoms().contains(&fx) {
                    (fmx.clone(), true)
                } else {
                    break;
                };
                let cf = coeff_of_atom(p, &atom).unwrap();
                let h = Poly::from_atom(atom.clone()).sub(&p.scale(&(Q::one() / cf)));
                if !f_atoms_with_vars(&h).is_empty() || h.top_atoms().contains(&atom) {
                    break;
                }
                let g = if reflect { h.subst_vars(&[x().neg()]) } else { h };
                if !gs.contains(&g) {
                    gs.push(g);
                }
            }
            if gs.len() < 1 {
                continue;
            }
            let ok = c.lits().iter().all(|l| {
                let p = l.poly();
                coeff_of_atom(p, &fx).is_some() || coeff_of_atom(p, &fmx).is_some()
            });
            if ok && gs.len() >= 1 && c.lits().len() >= 2 {
                out.push((f, gs));
            }
        }
        out
    }

    /// 各点ごとの選言を、候補ごとの排中律で全体の場合に分ける（各点→全体の推論を正しく行う）
    pub(crate) fn pointwise_split(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        let pcs = self.pointwise_clauses(st);
        for (cf, gs) in pcs {
            let remaining: Vec<Poly> = gs.iter().filter(|g| !st.tried.contains(&format!("pwx|{:x}", hash_poly(g)))).cloned().collect();
            if remaining.is_empty() {
                continue;
            }
            let g = remaining[0].clone();
            let key = format!("pws|{:x}", hash_poly(&g));
            if !st.tried.insert(key) {
                continue;
            }
            let c = fe_kernel::Clause::new(1, vec![Lit::eq(Poly::f(x()).sub(&g))]).map_err(|e| e.to_string())?;
            let (c0, h0, c1, hs, consts) = self.e.k.split_em(st.b, c)?;
            self.bump("pointwise_split");
            let saved = self.e.deadline;
            let now = Instant::now();
            let remain = saved.saturating_duration_since(now);
            // 子 0（f = g）
            self.e.deadline = now + remain / 3;
            let mut s0 = st.child(c0);
            match self.e.add_fact(&mut s0, h0) {
                Ok(_) => self.solve_branch(s0, depth + 1)?,
                Err(m) if m == TIMEOUT => self.open.push((c0, TIMEOUT.into())),
                Err(m) => return Err(m),
            }
            // 子 1（ある a で f(a) ≠ g(a)）
            self.e.deadline = saved;
            let mut s1 = st.child(c1);
            s1.tried.insert(format!("pwx|{:x}", hash_poly(&g)));
            let r = (|| -> Res<()> {
                for h in &hs {
                    self.e.add_fact(&mut s1, *h)?;
                }
                let a = Poly::cnst(consts[0]);
                let inst = self.e.k.instantiate(c1, cf, vec![a.clone()], 0)?;
                self.e.add_fact(&mut s1, inst)?;
                let inst2 = self.e.k.instantiate(c1, cf, vec![a.neg()], 0)?;
                self.e.add_fact(&mut s1, inst2)?;
                Ok(())
            })();
            match r {
                Ok(()) => self.solve_branch(s1, depth + 1)?,
                Err(m) if m == TIMEOUT => self.open.push((c1, TIMEOUT.into())),
                Err(m) => return Err(m),
            }
            return Ok(true);
        }
        Ok(false)
    }

    /// 各点ごとの選言を、事実に現れる閉じた点 K（定数を含む f の引数）で例化する（閉じた選言 → 場合分け）
    pub(crate) fn pointwise_instances(&mut self, st: &mut BState) -> Res<()> {
        let pcs = self.pointwise_clauses(st);
        if pcs.is_empty() {
            return Ok(());
        }
        let mut points: Vec<Poly> = Vec::new();
        for &u in &st.units {
            let p = self.e.poly0(u);
            p.visit_atoms(&mut |a| {
                if let Atom::F(k) = a {
                    if !k.has_var() && !k.consts().is_empty() && !k.has_f() && !points.contains(k) {
                        points.push((**k).clone());
                    }
                }
            });
        }
        points.sort_by_key(|k| poly_size(k));
        points.truncate(self.scaled(16));
        let mut made = 0;
        for (cf, _) in pcs {
            for k in &points {
                if made >= self.scaled(10) || self.closed(st) {
                    return Ok(());
                }
                let key = format!("pwi|{:?}|{:x}", cf, hash_poly(k));
                if !st.tried.insert(key) {
                    continue;
                }
                let inst = self.e.k.instantiate(st.b, cf, vec![k.clone()], 0)?;
                self.bump("pointwise_inst");
                self.e.add_fact(st, inst)?;
                made += 1;
                let inst2 = self.e.k.instantiate(st.b, cf, vec![k.neg()], 0)?;
                self.e.add_fact(st, inst2)?;
            }
        }
        Ok(())
    }

    /// 2 変数の単位等式が A(x)·B(y) = 0 と分解できれば、変数を共有しない選言として全体の場合分けをする
    pub(crate) fn split_disjoint(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        let twos: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 2).collect();
        for f in twos {
            let key = format!("dsplit|{:x}", hash_clause(self.e.clause(f)));
            if st.tried.contains(&key) {
                continue;
            }
            st.tried.insert(key);
            let p = self.e.poly0(f);
            let (a, b) = match rank1_split(&p) {
                Some(ab) => ab,
                None => continue,
            };
            let zp = match self.e.k.zero_product(st.b, f, 0, vec![a, b]) {
                Ok(z) => z,
                Err(_) => continue,
            };
            if crate::search::n_components(self.e.clause(zp)) < 2 {
                continue;
            }
            // f を含まない成分（∀y. y = 0 など）は、その変数に値を代入すれば偽になるので消す
            let zp = self.drop_ffree_components(st, zp)?;
            if crate::search::n_components(self.e.clause(zp)) < 2 {
                self.e.add_fact(st, zp)?;
                continue;
            }
            self.bump("split_disjoint");
            let children = self.e.k.split_components(st.b, zp)?;
            self.run_children(st, children, depth)?;
            return Ok(true);
        }
        Ok(false)
    }

    /// 閉じた（変数のない）事実の因数分解による場合分け。分けたら true。
    pub(crate) fn try_split(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        // 閉じた選言（変数のない節）はそのまま場合分けする
        let closed_disj: Vec<Fact> = st.others.iter().copied().filter(|f| {
            let c = self.e.clause(*f);
            c.nvars() == 0 && c.lits().len() >= 2
        }).collect();
        for f in closed_disj {
            let key = format!("csplit|{:?}", f);
            if !st.tried.insert(key) {
                continue;
            }
            let f2 = self.drop_rootless(st, f)?;
            let n = self.e.clause(f2).lits().len();
            if n == 0 {
                return Ok(true);
            }
            if n == 1 {
                self.e.add_fact(st, f2)?;
                continue;
            }
            self.bump("split");
            let children = self.e.k.split_components(st.b, f2)?;
            self.run_children(st, children, depth)?;
            return Ok(true);
        }
        let closed: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 0).collect();
        for f in closed {
            let key = format!("split|{:x}", hash_clause(self.e.clause(f)));
            if st.tried.contains(&key) {
                continue;
            }
            st.tried.insert(key);
            let p = self.e.poly0(f);
            let factors = match self.closed_factors(&p) {
                Some(fs) => fs,
                None => continue,
            };
            if factors.len() < 2 {
                continue;
            }
            let zp = match self.e.k.zero_product(st.b, f, 0, factors) {
                Ok(z) => z,
                Err(_) => continue,
            };
            if self.e.clause(zp).lits().len() < 2 {
                // 因子がまとまって 1 つになった
                self.e.add_fact(st, zp)?;
                continue;
            }
            // 無理な因子（実数解なし）を先に消す
            let zp = self.drop_rootless(st, zp)?;
            let n = self.e.clause(zp).lits().len();
            if n == 0 {
                return Ok(true);
            }
            if n == 1 {
                self.e.add_fact(st, zp)?;
                continue;
            }
            self.bump("split");
            let children = self.e.k.split_components(st.b, zp)?;
            self.run_children(st, children, depth)?;
            return Ok(true);
        }
        Ok(false)
    }

}
