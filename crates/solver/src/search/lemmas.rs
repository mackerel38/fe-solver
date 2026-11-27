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
        self.e.deadline = now + (remain / 5).min(Duration::from_secs(4));
        let open_before = self.open.len();
        let retry_before = self.retry.len();
        let mut cst = st.child(c1);
        cst.tried.insert("zinj".into());
        cst.tried.insert("inj".into());
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
        Ok(())
    }

}
