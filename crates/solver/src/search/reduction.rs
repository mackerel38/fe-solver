//! 帰着: 導いた 2 変数の等式を別の問題として解き、補題として取り込む（docs/TACTICS.md）
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
    /// 帰着: 導いた 2 変数の等式を新しい方程式として別に解き、完全解決すれば ImportLemma で取り込む
    pub(crate) fn try_reduction(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        let ax = self.e.k.axiom();
        let ax_size = poly_size(&self.e.poly0(ax));
        let ax_clause = self.e.clause(ax).clone();
        let mut cands: Vec<Fact> = st
            .units
            .iter()
            .copied()
            .filter(|u| {
                let c = self.e.clause(*u);
                let p = c.lits()[0].poly();
                c.nvars() == 2 && p.vars().len() == 2 && p.has_f() && poly_size(p) <= ax_size && *c != ax_clause
            })
            .collect();
        cands.sort_by_key(|u| poly_size(&self.e.poly0(*u)));
        let mut attempts = 0;
        for u in cands {
            if attempts >= 1 {
                break;
            }
            let p = self.e.poly0(u);
            let key = format!("reduce|{:x}", hash_poly(&p));
            if !st.tried.insert(key) {
                continue;
            }
            // x↔y 入れ替えで同じものも試さない
            st.tried.insert(format!("reduce|{:x}", hash_poly(&crate::engine::swap_xy(&p).monic())));
            attempts += 1;
            let now = Instant::now();
            let remain = self.e.deadline.saturating_duration_since(now);
            let budget = (remain / 6).min(Duration::from_secs(3));
            if budget < Duration::from_millis(200) {
                return Ok(false);
            }
            let lk = match Kernel::new(p.clone(), Poly::zero()) {
                Ok(k) => k,
                Err(_) => continue,
            };
            let mut sub = Searcher::new(Engine::new(lk, now + budget));
            sub.reduce_depth = self.reduce_depth + 1;
            sub.width = self.width;
            {
                let ax2 = sub.e.k.axiom();
                let sz = poly_size(sub.e.k.clause(ax2).lits()[0].poly());
                sub.e.size_cap = (2 * sz).max(60);
            }
            let ok = sub.solve_root().is_ok() && sub.retry_timeouts(now + budget).is_ok();
            self.bump("reduce_try");
            if !ok {
                continue;
            }
            let concl = sub.e.k.conclude();
            if !concl.complete || !concl.pw_families.is_empty() || !concl.add_families.is_empty() {
                continue;
            }
            let lemma = std::rc::Rc::new(sub.e.k);
            let r = match self.e.k.import_lemma(st.b, u, lemma) {
                Ok(r) => r,
                Err(_) => continue,
            };
            self.bump("reduce_import");
            if self.e.clause(r).lits().len() >= 2 {
                let children = self.e.k.split_components(st.b, r)?;
                self.run_children(st, children, depth)?;
                return Ok(true);
            }
            self.e.add_fact(st, r)?;
            return Ok(false);
        }
        Ok(false)
    }


    /// 既知の型の当てはめ: 2 変数の単位等式が f(a·xy + g(x)) = a·x·f(y) + h(x) の型なら、検証核の規則 AffineXY で
    /// f が 1 次（f(x) = (f(1) − f(0))x + f(0)）であることを得る。形が合わなければ検証核が拒否するだけ（安い）。
    pub(crate) fn apply_known_types(&mut self, st: &mut BState) -> Res<()> {
        // 単位等式と、「x = 0 ∨ …」のような 2 リテラルの事実（x ≠ 0 でだけ成り立つ形）
        let mut units: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 2).collect();
        units.extend(st.others.iter().copied().filter(|&f| self.e.nvars(f) == 2 && self.e.clause(f).lits().len() == 2));
        for u in units {
            if self.closed(st) {
                return Ok(());
            }
            let key = format!("affxy|{:?}", u);
            if !st.tried.insert(key) {
                continue;
            }
            if let Ok(r) = self.e.k.affine_xy(st.b, u) {
                self.bump("affine_xy");
                self.e.add_fact(st, r)?;
                return Ok(());
            }
            if let Ok(r) = self.e.k.affine_ff(st.b, u) {
                self.bump("affine_ff");
                self.e.add_fact(st, r)?;
                return Ok(());
            }
        }
        self.apply_additive_square(st)?;
        Ok(())
    }

    /// 既知の型「0 以上で加法的で f(x²) = x·f(x) なら 1 次」（検証核の規則 AdditiveSquare）の当てはめ:
    /// 1 変数の単位等式 f(x²) − x·f(x) = 0（P2）があるとき、2 変数の単位等式 U を (x, y), (x², y²), (x, y²), (x², y) と
    /// x, y を入れ替えたもので例化し、P2(x)・P2(y) の定数倍を差し引くと f(x² + y²) − f(x²) − f(y²) になれば、それを前提にする。
    /// 効く類: f(x + y) = f(x) + f(y)、f(x² + y) = x·f(x) + f(y)、f(x² + y²) = x·f(x) + y·f(y) などと f(x²) = x·f(x)。
    pub(crate) fn apply_additive_square(&mut self, st: &mut BState) -> Res<()> {
        let xv = x();
        let yv = y();
        let fx = Poly::f(xv.clone());
        let p2_want = Poly::f(xv.mul(&xv)).sub(&xv.mul(&fx));
        let p2 = match st.units.iter().copied().find(|&f| self.e.nvars(f) == 1 && self.e.poly0(f).monic() == p2_want.monic()) {
            Some(f) => f,
            None => return Ok(()),
        };
        let x2 = xv.mul(&xv);
        let y2 = yv.mul(&yv);
        let target = Poly::f(x2.add(&y2)).sub(&Poly::f(x2.clone())).sub(&Poly::f(y2.clone()));
        let fx2 = Atom::F(std::rc::Rc::new(x2.clone()));
        let fy2 = Atom::F(std::rc::Rc::new(y2.clone()));
        let fs = Atom::F(std::rc::Rc::new(x2.add(&y2)));
        let units: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 2).collect();
        let substs: Vec<Vec<Poly>> = vec![
            vec![xv.clone(), yv.clone()],
            vec![x2.clone(), y2.clone()],
            vec![xv.clone(), y2.clone()],
            vec![x2.clone(), yv.clone()],
            vec![yv.clone(), xv.clone()],
            vec![y2.clone(), x2.clone()],
            vec![yv.clone(), x2.clone()],
            vec![y2.clone(), xv.clone()],
        ];
        for u in units {
            if self.closed(st) {
                return Ok(());
            }
            let key = format!("addsq|{:?}|{:?}", u, p2);
            if !st.tried.insert(key) {
                continue;
            }
            let p = self.e.poly0(u);
            for s in &substs {
                let ps = p.subst_vars(s);
                let lam = match coeff_of_atom(&ps, &fs) {
                    Some(l) => l,
                    None => continue,
                };
                // D = ps/λ − target = α·P2(x) + β·P2(y) か
                let d = ps.scale(&(Q::one() / &lam)).sub(&target);
                let alpha = coeff_of_atom(&d, &fx2).unwrap_or_else(Q::zero);
                let beta = coeff_of_atom(&d, &fy2).unwrap_or_else(Q::zero);
                let p2x = p2_want.clone();
                let p2y = p2_want.subst_vars(&[yv.clone()]);
                if d != p2x.scale(&alpha).add(&p2y.scale(&beta)) {
                    continue;
                }
                let b = st.b;
                let inst = if *s == vec![xv.clone(), yv.clone()] { u } else { self.e.k.instantiate(b, u, s.clone(), 2)? };
                let ix = self.e.k.instantiate(b, p2, vec![xv.clone()], 2)?;
                let iy = self.e.k.instantiate(b, p2, vec![yv.clone()], 2)?;
                let lam_i = match scale_ratio(&self.e.poly0(inst), &ps) {
                    Some(k) => k,
                    None => continue,
                };
                // 例化した事実は保存のときに正規化されるので、倍率はそれぞれ求める
                let (mux, muy) = match (scale_ratio(&self.e.poly0(ix), &p2x), scale_ratio(&self.e.poly0(iy), &p2y)) {
                    (Some(a), Some(b)) => (a, b),
                    _ => continue,
                };
                let items = vec![
                    (Poly::constant(Q::one() / (&lam_i * &lam)), inst, 0),
                    (Poly::constant(-(&alpha) / &mux), ix, 0),
                    (Poly::constant(-(&beta) / &muy), iy, 0),
                ];
                let add = self.e.k.lincomb(b, 2, items)?;
                match self.e.k.additive_square(b, add, p2) {
                    Ok(r) => {
                        self.bump("additive_square");
                        self.e.add_fact(st, r)?;
                        return Ok(());
                    }
                    Err(_) => continue,
                }
            }
        }
        Ok(())
    }

}
