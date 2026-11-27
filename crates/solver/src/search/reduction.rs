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
        }
        Ok(())
    }

}
