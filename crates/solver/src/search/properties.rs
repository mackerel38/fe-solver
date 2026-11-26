//! 性質と既知の型: 符号の併合、加法的な族による特殊解決、コーシーの方程式への帰着、平方の値域（docs/TACTICS.md）
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
    /// 符号の条件つきの 1 変数の節を扱う:
    ///  (a) 「x < 0 ∨ Q(x)」の x → −x 版「x > 0 ∨ Q(−x)」を作る
    ///  (b) 「p > 0 ∨ Q」と「−p ⋈ 0 ∨ Q」（同じ Q）から Q を導く（非負結合で 0 > 0 となり条件が両立しない）
    pub(crate) fn sign_merge(&mut self, st: &mut BState) -> Res<()> {
        let cls: Vec<Fact> = st.others.iter().copied().filter(|f| {
            let c = self.e.clause(*f);
            c.nvars() == 1 && c.lits().len() == 2
        }).collect();
        // (a)
        for f in &cls {
            let c = self.e.clause(*f).clone();
            let has_cond = c.lits().iter().any(|l| matches!(l.rel(), Rel::Gt | Rel::Ge) && !l.poly().has_f() && l.poly().has_var());
            let has_eq = c.lits().iter().any(|l| l.rel() == Rel::Eq && l.poly().has_f());
            if !(has_cond && has_eq) {
                continue;
            }
            let key = format!("neg|{:?}", f);
            if !st.tried.insert(key) {
                continue;
            }
            let g = self.e.k.instantiate(st.b, *f, vec![x().neg()], 1)?;
            self.e.add_fact(st, g)?;
            if self.closed(st) {
                return Ok(());
            }
        }
        // (b)
        let cls: Vec<Fact> = st.others.iter().copied().filter(|f| {
            let c = self.e.clause(*f);
            c.nvars() <= 2 && c.lits().len() == 2
        }).collect();
        for i in 0..cls.len() {
            for j in (i + 1)..cls.len() {
                let (a, b) = (cls[i], cls[j]);
                let (ca, cb) = (self.e.clause(a).clone(), self.e.clause(b).clone());
                for ia in 0..2 {
                    for ib in 0..2 {
                        let (la, lb) = (&ca.lits()[ia], &cb.lits()[ib]);
                        let (qa, qb) = (&ca.lits()[1 - ia], &cb.lits()[1 - ib]);
                        if qa != qb || !matches!(la.rel(), Rel::Gt | Rel::Ge) || !matches!(lb.rel(), Rel::Gt | Rel::Ge) {
                            continue;
                        }
                        if la.rel() == Rel::Ge && lb.rel() == Rel::Ge {
                            continue;
                        }
                        // la.poly · α + lb.poly · β = 0 となる正の α, β
                        let pa = la.poly();
                        let pb = lb.poly();
                        let (ma, ca0) = match pa.terms().last() {
                            Some(t) => t.clone(),
                            None => continue,
                        };
                        let cb0 = match pb.terms().iter().find(|(m, _)| *m == ma) {
                            Some((_, c)) => c.clone(),
                            None => continue,
                        };
                        let ratio = -(&ca0 / &cb0);
                        if ratio <= Q::zero() || !pa.add(&pb.scale(&ratio)).is_zero() {
                            continue;
                        }
                        let key = format!("smerge|{:?}|{:?}", a, b);
                        if !st.tried.insert(key) {
                            continue;
                        }
                        let nv = ca.nvars().max(cb.nvars());
                        let r = self.e.k.pos_comb(st.b, nv, vec![(Q::one(), a, ia), (ratio, b, ib)], vec![], vec![], Q::zero(), true)?;
                        self.bump("sign_merge");
                        self.e.add_fact(st, r)?;
                        if self.closed(st) {
                            return Ok(());
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// 任意の加法的関数 A について A + f(0)（f(0) は独立なパラメータ）か A が解かを検証核で確かめる（結果は保存）
    pub fn additive_family(&mut self) -> Option<AddFamily> {
        if self.add_fam.is_none() {
            let k = &self.e.k;
            let r = k
                .verify_additive(&Poly::f(Poly::zero()))
                .or_else(|_| k.verify_additive(&Poly::zero()))
                .or_else(|_| k.verify_additive_kind(&Poly::zero(), AddKind::Involution))
                .or_else(|_| k.verify_additive_kind(&Poly::zero(), AddKind::Projection))
                .ok();
            self.add_fam = Some(r);
        }
        self.add_fam.clone().unwrap()
    }

    /// この枝で加法性（f(x+y) = f(x) + f(y) − f(0)）が示されていて、加法的な族が解なら、葉を加法的な族で確定する。
    /// 族が A（定数なし）のときは、f(0) = 0 を書き換え規則で示して f(x+y) = f(x) + f(y) の形にする。
    pub(crate) fn try_mark_additive(&mut self, st: &mut BState) -> Res<bool> {
        let a = match st.additive {
            Some(a) => a,
            None => return Ok(false),
        };
        if !st.tried.insert("mark_additive".into()) {
            return Ok(false);
        }
        let fam = match self.additive_family() {
            Some(f) => f,
            None => return Ok(false),
        };
        let b = st.b;
        let fact = if fam.g().is_zero() {
            let p = self.e.poly0(a);
            let fxy = Atom::F(std::rc::Rc::new(x().add(&y())));
            let lam = match coeff_of_atom(&p, &fxy) {
                Some(l) => l,
                None => return Ok(false),
            };
            let pn = p.scale(&(Q::one() / &lam));
            let target = Poly::f(x().add(&y())).sub(&Poly::f(x())).sub(&Poly::f(y()));
            let d = target.sub(&pn);
            let (d2, items) = self.e.rw_poly(st, &d, 0)?;
            if !d2.is_zero() {
                return Ok(false);
            }
            let mut its = vec![(Poly::constant(Q::one() / &lam), a, 0)];
            its.extend(items);
            self.e.k.lincomb(b, 2, its)?
        } else {
            a
        };
        let r = if fam.kind() == AddKind::Free {
            self.e.k.mark_additive(b, fact, fam)
        } else {
            // 条件 f(f(x)) = x（または f(x)）を書き換え規則で示す
            let ffx = Poly::f(Poly::f(x()));
            let d = if fam.kind() == AddKind::Involution { ffx.sub(&x()) } else { ffx.sub(&Poly::f(x())) };
            let (d2, items) = self.e.rw_poly(st, &d, 0)?;
            if !d2.is_zero() || items.is_empty() {
                return Ok(false);
            }
            let c = self.e.k.lincomb(b, 1, items)?;
            self.e.k.mark_additive_constrained(b, fact, c, fam)
        };
        match r {
            Ok(()) => {
                self.bump("additive_leaf");
                Ok(true)
            }
            Err(_) => Ok(false),
        }
    }

    /// コーシーの方程式への帰着:
    ///  (1) 2 変数の条件つき節「±v ⋈ 0 ∨ Q(x, y)」を (x + v, −v) で例化して反対側の符号の版を作る（符号の併合で全体へ）
    ///  (2) f(x+y) − f(x) − f(y) − k = 0（k は閉じた式）から正準形 f(x+y) = f(x) + f(y) − f(0) を作る
    ///  (3) f(x²) の式が「平方和 + 定数」なら f は x ≥ 0 で下に有界（または上に有界）
    ///  (4) (2) と (3) から CauchyBounded で f(x) = (f(1) − f(0))x + f(0)
    pub(crate) fn cauchy_step(&mut self, st: &mut BState) -> Res<()> {
        let b = st.b;
        // (1)
        let cls: Vec<Fact> = st.others.iter().copied().filter(|f| self.e.clause(*f).nvars() == 2).collect();
        for f in cls {
            let c = self.e.clause(f).clone();
            if c.lits().len() != 2 {
                continue;
            }
            let cond = c.lits().iter().find(|l| matches!(l.rel(), Rel::Gt | Rel::Ge) && !l.poly().has_f());
            let cond = match cond {
                Some(l) => l.clone(),
                None => continue,
            };
            let vs = cond.poly().vars();
            if vs.len() != 1 {
                continue;
            }
            let v = *vs.iter().next().unwrap();
            let key = format!("cflip|{:?}", f);
            if !st.tried.insert(key) {
                continue;
            }
            let o = 1 - v;
            let mut sub = vec![x(), y()];
            sub[o as usize] = Poly::var(o).add(&Poly::var(v));
            sub[v as usize] = Poly::var(v).neg();
            let g = self.e.k.instantiate(b, f, sub, 2)?;
            self.e.add_fact(st, g)?;
            if self.closed(st) {
                return Ok(());
            }
        }
        // (2)
        if st.additive.is_none() {
            let fxy = Atom::F(std::rc::Rc::new(x().add(&y())));
            let units: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 2).collect();
            for u in units {
                let p = self.e.poly0(u);
                let lam = match coeff_of_atom(&p, &fxy) {
                    Some(l) => l,
                    None => continue,
                };
                let pn = p.scale(&(Q::one() / &lam));
                let core = Poly::f(x().add(&y())).sub(&Poly::f(x())).sub(&Poly::f(y()));
                let k = pn.sub(&core); // = −k_orig（閉じた式であること）
                if k.has_var() {
                    continue;
                }
                let target = core.add(&Poly::f(Poly::zero()));
                // target − pn = f(0) − k を規則で 0 と示す
                let d = target.sub(&pn);
                let (d2, items) = self.e.rw_poly(st, &d, 0)?;
                if !d2.is_zero() {
                    continue;
                }
                let mut its = vec![(Poly::constant(Q::one() / &lam), u, 0)];
                // target = pn + d,  d = Σ items（d − 0 = Σ items）
                its.extend(items);
                let canon = self.e.k.lincomb(b, 2, its)?;
                let want = fe_kernel::Clause::new(2, vec![Lit::eq(target.clone())]).map_err(|e| e.to_string())?;
                if *self.e.clause(canon) == want {
                    st.additive = Some(canon);
                    self.bump("additive_found");
                    break;
                }
            }
        }
        // (3)
        if st.bound.is_none() {
            let fx2 = Atom::F(std::rc::Rc::new(x().pow(2)));
            let units: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 1).collect();
            'outer: for u in units {
                let p = self.e.poly0(u);
                let lam = match coeff_of_atom(&p, &fx2) {
                    Some(l) => l,
                    None => continue,
                };
                let r = Poly::from_atom(fx2.clone()).sub(&p.scale(&(Q::one() / &lam)));
                if r.top_atoms().contains(&fx2) {
                    continue;
                }
                let k = Poly::from_terms(r.terms().iter().filter(|(m, _)| m.factors().iter().all(|(a, _)| !a.has_var())).cloned().collect());
                let var_part = r.sub(&k);
                for sign in [1i64, -1] {
                    let sp = var_part.scale(&Q::from_integer(sign.into()));
                    if let Some((sq, kappa)) = crate::pos::sos(&sp) {
                        // sign·(f(x²) − k) = sign·p/λ + sign·(r − k) ≥ 0
                        let pf = self.e.k.pos_comb(b, 1, vec![], vec![(Poly::constant(Q::from_integer(sign.into()) / &lam), u, 0)], sq, kappa, false)?;
                        let pre_poly = Poly::from_atom(Atom::F(std::rc::Rc::new(x()))).sub(&k).scale(&Q::from_integer(sign.into()));
                        let pc = fe_kernel::Clause::new(1, vec![Lit::ge(pre_poly)]).map_err(|e| e.to_string())?;
                        if let Ok(bf) = self.e.k.square_range(b, pf, 0, pc) {
                            st.bound = Some(bf);
                            self.bump("bound_found");
                            break 'outer;
                        }
                    }
                }
            }
        }
        // (4)
        if let (Some(a), Some(bd)) = (st.additive, st.bound) {
            if st.tried.insert("cauchy".into()) {
                let r = self.e.k.cauchy_bounded(b, a, bd)?;
                self.bump("cauchy");
                self.e.add_fact(st, r)?;
            }
        }
        Ok(())
    }

    /// ある変数が 2 乗の形でだけ現れる単位等式から、平方の値域（t ≥ 0）での事実を作る
    pub(crate) fn square_ranges(&mut self, st: &mut BState) -> Res<()> {
        let units: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) >= 1).collect();
        for u in units {
            let key = format!("sqr|{:?}", u);
            if !st.tried.insert(key) {
                continue;
            }
            let p0 = self.e.poly0(u);
            let nv = self.e.nvars(u);
            // f(x²) − f(x)² − k = 0（k は閉じた式）型の 1 変数の事実（f(v)² を f(v²) − k に戻すのに使う）
            let fx = Atom::F(std::rc::Rc::new(x()));
            let fx2 = Atom::F(std::rc::Rc::new(x().pow(2)));
            let sqfact: Option<(Fact, Q)> = st.units.iter().copied().filter(|g| self.e.nvars(*g) == 1).find_map(|g| {
                let q = self.e.poly0(g);
                let lam = coeff_of_atom(&q, &fx2)?;
                let r = q.scale(&(Q::one() / &lam)).sub(&Poly::from_atom(fx2.clone())).add(&Poly::from_atom(fx.clone()).pow(2));
                if r.has_var() { None } else { Some((g, lam)) }
            });
            for v in 0..nv {
                let mut u_use = u;
                let mut p = p0.clone();
                if crate::pos::unsquare(&p, v).is_none() {
                    // f(v)² を f(v²) − k に置き換えて再挑戦
                    let (g, lam) = match &sqfact {
                        Some(t) => t.clone(),
                        None => continue,
                    };
                    let fv = Atom::F(std::rc::Rc::new(Poly::var(v)));
                    let cs = coeffs_in(&p, &fv);
                    if cs.keys().any(|e| *e != 0 && *e != 2) || !cs.contains_key(&2) {
                        continue;
                    }
                    let qco = cs[&2].clone();
                    // g(v) の保存形 = λ(f(v²) − f(v)² − k)。p + (qco/λ)·g(v) で f(v)² が消える
                    let mut sub: Vec<Poly> = vec![Poly::var(v)];
                    let gi = self.e.k.instantiate(st.b, g, std::mem::take(&mut sub), nv)?;
                    let np = p.add(&self.e.poly0(gi).scale(&(Q::one() / &lam)).mul(&qco));
                    if crate::pos::unsquare(&np, v).is_none() {
                        continue;
                    }
                    let lc = self.e.k.lincomb(st.b, nv, vec![(Poly::one(), u, 0), (qco.scale(&(Q::one() / &lam)), gi, 0)])?;
                    u_use = lc;
                    p = self.e.poly0(lc);
                }
                let u = u_use;
                let pre = match crate::pos::unsquare(&p, v) {
                    Some(q) => q,
                    None => continue,
                };
                let pc = match fe_kernel::Clause::new(nv, vec![Lit::eq(pre)]) {
                    Ok(c) => c,
                    Err(_) => continue,
                };
                if let Ok(r) = self.e.k.square_range(st.b, u, v, pc) {
                    self.bump("square_range");
                    self.e.add_fact(st, r)?;
                    if self.closed(st) {
                        return Ok(());
                    }
                }
            }
        }
        Ok(())
    }

}
