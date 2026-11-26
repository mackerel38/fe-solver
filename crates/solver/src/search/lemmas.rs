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
        st.tried.insert("zinj".into());
        // f ≡ 0 が解なら（この枝で f(j) ≠ 0 がわかっていない限り）成り立たないので試さない
        if self.e.k.verify_solution(&Poly::zero()).is_ok() && st.nes.is_empty() {
            return Ok(false);
        }
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
