//! 単射性・零点の補題（排中律で分け、否定側を閉じられなければ取り消す）とその適用（docs/TACTICS.md）
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
    /// 単射性の補題を試す: 排中律で「∀x,y. f(x) = f(y) ⇒ x = y」とその否定（ある a ≠ b で f(a) = f(b)）に分け、
    /// 否定側を時間予算内に矛盾で閉じられれば肯定側で続ける。閉じられなければ場合分けを取り消す。
    pub(crate) fn try_injectivity(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        if st.tried.contains("inj") || st.inj.is_some() {
            return Ok(false);
        }
        st.tried.insert("inj".into());
        let fx = Poly::f(x());
        let fy = Poly::f(y());
        let c = fe_kernel::Clause::new(2, vec![Lit::ne(fx.sub(&fy)), Lit::eq(x().sub(&y()))]).map_err(|e| e.to_string())?;
        let (c0, h0, c1, hs, _consts) = self.e.k.split_em(st.b, c)?;
        self.bump("inj_try");
        let saved = self.e.deadline;
        let now = Instant::now();
        let remain = saved.saturating_duration_since(now);
        self.e.deadline = now + (remain / 4).min(Duration::from_secs(4));
        let open_before = self.open.len();
        let mut cst = st.child(c1);
        cst.tried.insert("inj".into());
        cst.in_trial = true;
        let r = (|| -> Res<()> {
            for h in &hs {
                self.e.add_fact(&mut cst, *h)?;
            }
            Ok(())
        })();
        match r {
            Ok(()) => self.solve_branch(cst, depth + 1)?,
            Err(m) if m == TIMEOUT => {}
            Err(m) => {
                self.e.deadline = saved;
                return Err(m);
            }
        }
        self.e.deadline = saved;
        self.open.truncate(open_before);
        if !self.e.k.is_closed(c1) {
            self.e.k.abandon_split(st.b)?;
            return Ok(false);
        }
        self.bump("inj_proved");
        let mut c0st = st.child(c0);
        c0st.inj = Some(h0);
        c0st.tried.insert("inj".into());
        let r = self.e.add_fact(&mut c0st, h0);
        match r {
            Ok(_) => self.solve_branch(c0st, depth + 1)?,
            Err(m) if m == TIMEOUT => self.open.push((c0, TIMEOUT.into())),
            Err(m) => return Err(m),
        }
        Ok(true)
    }

    /// 零点の補題を試す: 排中律で「∀x. f(x) = 0 ⇒ x = 0」とその否定（ある k ≠ 0 で f(k) = 0）に分け、
    /// 否定側を時間予算内に閉じられれば肯定側で続ける。閉じられなければ場合分けを取り消す。
    pub(crate) fn try_zero_injectivity(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        if st.tried.contains("zinj") || st.zinj.is_some() {
            return Ok(false);
        }
        // f ≡ 0 が解なら（この枝で f(j) ≠ 0 がわかっていない限り）成り立たないので試さない。
        // このときは「試した」と記録しない（f(j) ≠ 0 を仮定した子の枝で試せるように）
        if self.e.k.verify_solution(&Poly::zero()).is_ok() && st.nes.is_empty() {
            return Ok(false);
        }
        st.tried.insert("zinj".into());
        let c = fe_kernel::Clause::new(1, vec![Lit::ne(Poly::f(x())), Lit::eq(x())]).map_err(|e| e.to_string())?;
        let (c0, h0, c1, hs, _consts) = self.e.k.split_em(st.b, c)?;
        self.bump("zinj_try");
        let saved = self.e.deadline;
        let now = Instant::now();
        let remain = saved.saturating_duration_since(now);
        // 否定側の枝の持ち時間: 残り時間の 1/div、最大 secs 秒（既定 div = 5, secs = 4。実験用に FE_ZINJ_DIV・FE_ZINJ_SECS で変えられる）
        let div: u32 = std::env::var("FE_ZINJ_DIV").ok().and_then(|v| v.parse().ok()).unwrap_or(5).max(1);
        let secs: f64 = std::env::var("FE_ZINJ_SECS").ok().and_then(|v| v.parse().ok()).unwrap_or(4.0);
        self.e.deadline = now + (remain / div).min(Duration::from_secs_f64(secs));
        let open_before = self.open.len();
        let retry_before = self.retry.len();
        let mut cst = st.child(c1);
        cst.tried.insert("zinj".into());
        cst.tried.insert("inj".into());
        cst.in_trial = true;
        let r = (|| -> Res<()> {
            for h in &hs {
                self.e.add_fact(&mut cst, *h)?;
            }
            Ok(())
        })();
        match r {
            Ok(()) => self.solve_branch(cst, depth + 1)?,
            Err(m) if m == TIMEOUT => {}
            Err(m) => {
                self.e.deadline = saved;
                return Err(m);
            }
        }
        self.e.deadline = saved;
        self.open.truncate(open_before);
        self.retry.truncate(retry_before);
        if !self.e.k.is_closed(c1) {
            self.e.k.abandon_split(st.b)?;
            return Ok(false);
        }
        self.bump("zinj_proved");
        let mut c0st = st.child(c0);
        c0st.zinj = Some(h0);
        c0st.tried.insert("zinj".into());
        let r = self.e.add_fact(&mut c0st, h0);
        match r {
            Ok(_) => self.solve_branch(c0st, depth + 1)?,
            Err(m) if m == TIMEOUT => self.open.push((c0, TIMEOUT.into())),
            Err(m) => return Err(m),
        }
        Ok(true)
    }

    /// f が変数を含む式 T の値で 0 になることを述べる事実（単位等式 c·f(T) = 0、または選言のリテラル f(T) = 0、
    /// T は x と異なる変数を含む式）があるか。零点の補題（f(t) = 0 ⇒ t = 0）を場合分けより先に試す目安。
    pub(crate) fn has_zero_image(&self, st: &BState) -> bool {
        let is_zero_image = |p: &Poly| -> bool {
            p.terms().len() == 1
                && p.terms()[0].0.factors().len() == 1
                && matches!(&p.terms()[0].0.factors()[0].0, Atom::F(s) if s.has_var() && **s != x())
        };
        st.units.iter().chain(st.others.iter()).any(|&u| {
            let c = self.e.clause(u);
            c.nvars() >= 1 && c.lits().iter().any(|l| l.rel() == Rel::Eq && is_zero_image(l.poly()))
        })
    }

    /// 零点の補題から: 単位等式 c·f(s) = 0 があれば s = 0
    pub(crate) fn apply_zero_injectivity(&mut self, st: &mut BState) -> Res<()> {
        let z = match st.zinj {
            Some(h) => h,
            None => return Ok(()),
        };
        let units = st.units.clone();
        for u in units {
            let p = self.e.poly0(u);
            if p.terms().len() != 1 || p.terms()[0].0.factors().len() != 1 || p.terms()[0].0.factors()[0].1 != 1 {
                continue;
            }
            let s1 = match &p.terms()[0].0.factors()[0].0 {
                Atom::F(s1) => (**s1).clone(),
                _ => continue,
            };
            if s1.is_zero() {
                continue;
            }
            let key = format!("zinj|{:?}", u);
            if !st.tried.insert(key) {
                continue;
            }
            let nv = self.e.nvars(u);
            let inst = self.e.k.instantiate(st.b, z, vec![s1.clone()], nv)?;
            let ic = self.e.clause(inst).clone();
            let want = Lit::ne(Poly::f(s1));
            let li = match ic.lits().iter().position(|l| *l == want) {
                Some(i) => i,
                None => continue,
            };
            let r = self.e.k.resolve(st.b, inst, li, u, 0)?;
            self.bump("zinj_apply");
            self.e.add_fact(st, r)?;
            if self.closed(st) {
                return Ok(());
            }
        }
        // 選言のリテラル f(s) = 0 も s = 0 に置き換える（零点の補題の例「f(s) ≠ 0 ∨ s = 0」との導出原理を繰り返す）
        let others: Vec<Fact> = st.others.iter().copied().filter(|&f| {
            let c = self.e.clause(f);
            c.nvars() >= 1 && c.lits().len() >= 2 && c.lits().len() <= 3
        }).collect();
        for o in others.into_iter().take(self.scaled(12)) {
            let key = format!("zinjd|{:?}", o);
            if !st.tried.insert(key) {
                continue;
            }
            let mut cur = o;
            for _ in 0..3 {
                let c = self.e.clause(cur).clone();
                let pos = c.lits().iter().position(|l| {
                    l.rel() == Rel::Eq
                        && l.poly().terms().len() == 1
                        && l.poly().terms()[0].0.factors().len() == 1
                        && l.poly().terms()[0].0.factors()[0].1 == 1
                        && matches!(&l.poly().terms()[0].0.factors()[0].0, Atom::F(s1) if !s1.is_zero())
                });
                let li = match pos {
                    Some(i) => i,
                    None => break,
                };
                let s1 = match &c.lits()[li].poly().terms()[0].0.factors()[0].0 {
                    Atom::F(s1) => (**s1).clone(),
                    _ => break,
                };
                let inst = self.e.k.instantiate(st.b, z, vec![s1.clone()], c.nvars())?;
                let want = Lit::ne(Poly::f(s1));
                let zi = match self.e.clause(inst).lits().iter().position(|l| *l == want) {
                    Some(i) => i,
                    None => break,
                };
                cur = self.e.k.resolve(st.b, cur, li, inst, zi)?;
            }
            if cur != o {
                self.bump("zinj_apply_disj");
                self.e.add_fact(st, cur)?;
                if self.closed(st) {
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    /// 単射性から: 単位等式 c(f(s) − f(t)) = 0 があれば s − t = 0
    pub(crate) fn apply_injectivity(&mut self, st: &mut BState) -> Res<()> {
        let inj = match st.inj {
            Some(h) => h,
            None => return Ok(()),
        };
        // 単射性から零点の補題: y := 0 を代入し、f(0) が 0 に書き換わって「f(x) ≠ 0 ∨ x = 0」になれば登録する
        if st.zinj.is_none() && st.tried.insert("inj_to_zinj".into()) {
            let inst = self.e.k.instantiate(st.b, inj, vec![x(), Poly::zero()], 1)?;
            if let Added::New(nf) = self.e.add_fact(st, inst)? {
                let want = fe_kernel::Clause::new(1, vec![Lit::ne(Poly::f(x())), Lit::eq(x())]).map_err(|e| e.to_string())?;
                if *self.e.clause(nf) == want {
                    st.zinj = Some(nf);
                    self.bump("zinj_from_inj");
                }
            }
            if self.closed(st) {
                return Ok(());
            }
        }
        let units = st.units.clone();
        for u in units {
            let p = self.e.poly0(u);
            if p.terms().len() != 2 {
                continue;
            }
            let (m1, c1) = &p.terms()[0];
            let (m2, c2) = &p.terms()[1];
            if *c1 != -c2.clone() || m1.factors().len() != 1 || m2.factors().len() != 1 || m1.factors()[0].1 != 1 || m2.factors()[0].1 != 1 {
                continue;
            }
            let (a1, a2) = (&m1.factors()[0].0, &m2.factors()[0].0);
            let (s1, s2) = match (a1, a2) {
                (Atom::F(s1), Atom::F(s2)) => ((**s1).clone(), (**s2).clone()),
                _ => continue,
            };
            let key = format!("inj|{:?}", u);
            if !st.tried.insert(key) {
                continue;
            }
            let nv = self.e.nvars(u);
            let inst = self.e.k.instantiate(st.b, inj, vec![s1.clone(), s2.clone()], nv)?;
            let ic = self.e.clause(inst).clone();
            let want = Lit::ne(Poly::f(s1).sub(&Poly::f(s2)));
            let li = match ic.lits().iter().position(|l| *l == want) {
                Some(i) => i,
                None => continue,
            };
            let r = self.e.k.resolve(st.b, inst, li, u, 0)?;
            self.bump("inj_apply");
            self.e.add_fact(st, r)?;
            if self.closed(st) {
                return Ok(());
            }
        }
        // 選言のリテラル c(f(s) − f(t)) = 0 も s − t = 0 に置き換える（単射性の例「s − t = 0 ∨ f(s) − f(t) ≠ 0」との導出原理）。
        // 変数のない選言（場合分けの候補）も対象にする
        let others: Vec<Fact> = st.others.iter().copied().filter(|&f| {
            let c = self.e.clause(f);
            c.lits().len() >= 2 && c.lits().len() <= 3
        }).collect();
        for o in others.into_iter().take(self.scaled(12)) {
            let key = format!("injd|{:?}", o);
            if !st.tried.insert(key) {
                continue;
            }
            let cur = self.reduce_by_injectivity(st, inj, o)?;
            if cur != o {
                self.bump("inj_apply_disj");
                self.e.add_fact(st, cur)?;
                if self.closed(st) {
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    /// 単射性 inj（「y − x = 0 ∨ f(y) − f(x) ≠ 0」）で、節のリテラル c(f(s) − f(t)) = 0 を s − t = 0 に置き換える（導出原理、最大 3 個）
    pub(crate) fn reduce_by_injectivity(&mut self, st: &mut BState, inj: Fact, o: Fact) -> Res<Fact> {
        let mut cur = o;
        for _ in 0..3 {
            let c = self.e.clause(cur).clone();
            let mut found: Option<(usize, Poly, Poly)> = None;
            for (i, l) in c.lits().iter().enumerate() {
                if l.rel() != Rel::Eq || l.poly().terms().len() != 2 {
                    continue;
                }
                let (m1, c1) = &l.poly().terms()[0];
                let (m2, c2) = &l.poly().terms()[1];
                if *c1 != -c2.clone() || m1.factors().len() != 1 || m2.factors().len() != 1 || m1.factors()[0].1 != 1 || m2.factors()[0].1 != 1 {
                    continue;
                }
                if let (Atom::F(s1), Atom::F(s2)) = (&m1.factors()[0].0, &m2.factors()[0].0) {
                    found = Some((i, (**s1).clone(), (**s2).clone()));
                    break;
                }
            }
            let (li, s1, s2) = match found {
                Some(t) => t,
                None => break,
            };
            let inst = self.e.k.instantiate(st.b, inj, vec![s1.clone(), s2.clone()], c.nvars())?;
            let want = Lit::ne(Poly::f(s1).sub(&Poly::f(s2)));
            let zi = match self.e.clause(inst).lits().iter().position(|l| *l == want) {
                Some(i) => i,
                None => break,
            };
            cur = self.e.k.resolve(st.b, cur, li, inst, zi)?;
        }
        Ok(cur)
    }

    /// 補題の試行（一般形）: 節 c を排中律で分け、否定側（反例の定数つき）を限られた時間で閉じられれば、
    /// c を仮定した側で探索を続ける（c は証明済みの補題になる）。閉じられなければ場合分けを取り消す（AbandonSplit）。
    /// 戻り値: 補題として使って探索を続けたら true。
    pub(crate) fn try_lemma(&mut self, st: &mut BState, depth: u32, round: usize, c: fe_kernel::Clause, name: &str) -> Res<bool> {
        let (c0, h0, c1, hs, _consts) = self.e.k.split_em(st.b, c)?;
        self.bump(&format!("spec_try_{}", name));
        let saved = self.e.deadline;
        let now = Instant::now();
        let remain = saved.saturating_duration_since(now);
        self.e.deadline = now + (remain / 8).min(Duration::from_secs(2));
        let open_before = self.open.len();
        let retry_before = self.retry.len();
        let mut cst = st.child(c1);
        cst.tried.insert(format!("spec|{}", name));
        cst.in_trial = true;
        let r = (|| -> Res<()> {
            for h in &hs {
                self.e.add_fact(&mut cst, *h)?;
            }
            Ok(())
        })();
        match r {
            Ok(()) => self.solve_branch(cst, depth + 1)?,
            Err(m) if m == TIMEOUT => {}
            Err(m) => {
                self.e.deadline = saved;
                return Err(m);
            }
        }
        self.e.deadline = saved;
        self.open.truncate(open_before);
        self.retry.truncate(retry_before);
        if !self.e.k.is_closed(c1) {
            self.e.k.abandon_split(st.b)?;
            return Ok(false);
        }
        self.bump(&format!("spec_proved_{}", name));
        let mut c0st = st.child(c0);
        c0st.tried.insert(format!("spec|{}", name));
        c0st.start_round = round;
        let r = self.e.add_fact(&mut c0st, h0);
        // 補題を仮定した側は実質的な場合分けではないので、深さを増やさずに続ける
        match r {
            Ok(_) => self.solve_branch(c0st, depth)?,
            Err(m) if m == TIMEOUT => self.open.push((c0, TIMEOUT.into())),
            Err(m) => return Err(m),
        }
        Ok(true)
    }

    /// f を解の候補 g で置き換えた式（入れ子の f も内側から置き換える）
    fn apply_sol(p: &Poly, g: &Poly) -> Poly {
        p.transform(&mut |a| match a {
            Atom::F(u) => g.subst_vars(&[Self::apply_sol(&u, g)]),
            other => Poly::from_atom(other),
        })
    }

    /// 解の候補のうち、この枝の事実と明らかには矛盾しないもの（候補の選び方にだけ使う。証明には使わない）
    fn consistent_sols(&self, st: &BState) -> Vec<Poly> {
        self.sols
            .iter()
            .filter(|g| {
                for &u in &st.units {
                    let p = Self::apply_sol(&self.e.poly0(u), g);
                    // 定数（パラメータや枝の定数を含まない）になって 0 でなければ矛盾
                    if p.as_const().map_or(false, |c| !c.is_zero()) {
                        return false;
                    }
                }
                for &n in &st.nes {
                    if Self::apply_sol(&self.e.poly0(n), g).is_zero() {
                        return false;
                    }
                }
                true
            })
            .cloned()
            .collect()
    }

    /// 見つけた解に導かれる補題の推測: 性質の一覧（f(0) = 0、奇関数、偶関数、f(f(x)) = x、f(f(x)) = f(x)、
    /// f(x)² = x²、f(x²) = x·f(x)、f(1) = c、f(x + 1) = f(x) + c）のうち、この枝と矛盾しない解の候補すべてが満たすものを、否定を閉じて補題にする。
    /// 健全性は検証核による（候補の選び方は推測でよい）。
    pub(crate) fn speculate_lemmas(&mut self, st: &mut BState, depth: u32, round: usize) -> Res<bool> {
        if st.in_trial {
            return Ok(false);
        }
        let sols = self.consistent_sols(st);
        // 定数の解しか残っていなければ（どの性質も満たしてしまうので）推測しない
        if sols.is_empty() || sols.iter().all(|g| !g.vars().contains(&0)) {
            return Ok(false);
        }
        let one = Poly::one();
        let mut menu: Vec<(&str, u32, Poly)> = vec![
            ("f0", 0, Poly::f(Poly::zero())),
            ("odd", 1, Poly::f(x().neg()).add(&Poly::f(x()))),
            ("invol", 1, Poly::f(Poly::f(x())).sub(&x())),
        ];
        let tail: Vec<(&str, u32, Poly)> = vec![
            ("even", 1, Poly::f(x().neg()).sub(&Poly::f(x()))),
            ("idem", 1, Poly::f(Poly::f(x())).sub(&Poly::f(x()))),
            // 解の候補が x と −x（や |x|）のとき: 各点で ±x
            ("sq", 1, Poly::f(x()).pow(2).sub(&x().pow(2))),
            // 解の候補がすべて c·x の形のとき: f(x²) = x·f(x)
            ("sqarg", 1, Poly::f(x().pow(2)).sub(&x().mul(&Poly::f(x())))),
        ];
        // f(1) の値・f(x + 1) − f(x) が解の候補で共通の有理数なら、それも候補にする
        let v1: Vec<Poly> = sols.iter().map(|g| g.subst_vars(&[one.clone()])).collect();
        if v1.iter().all(|v| v.as_const().is_some() && *v == v1[0]) {
            menu.push(("f1", 0, Poly::f(one.clone()).sub(&v1[0])));
        }
        let dv: Vec<Poly> = sols.iter().map(|g| g.subst_vars(&[x().add(&one)]).sub(g)).collect();
        if dv.iter().all(|v| v.as_const().is_some() && *v == dv[0]) && !dv[0].is_zero() {
            menu.push(("shift1", 1, Poly::f(x().add(&one)).sub(&Poly::f(x())).sub(&dv[0])));
        }
        menu.extend(tail);
        let mut tried_n = 0;
        for (name, nv, p) in menu {
            if tried_n >= 2 || self.closed(st) {
                break;
            }
            let key = format!("spec|{}", name);
            if st.tried.contains(&key) {
                continue;
            }
            // すべての候補が満たすか
            if !sols.iter().all(|g| Self::apply_sol(&p, g).is_zero()) {
                continue;
            }
            // すでに事実として知っているなら試さない（書き換えで 0 になる）
            let (d, _) = self.e.rw_poly(st, &p, nv)?;
            st.tried.insert(key);
            if d.is_zero() {
                continue;
            }
            tried_n += 1;
            let c = fe_kernel::Clause::new(nv, vec![Lit::eq(p)]).map_err(|e| e.to_string())?;
            if self.try_lemma(st, depth, round, c, name)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

}
