//! 代入（事実の例化）: 基本の代入、2 変数の代入、特別な点、打ち消し・引数を等しくする代入、分数の代入、全射性の証人（docs/TACTICS.md）
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
    /// 代入候補にする特別な点: 枝の定数（スコーレム定数）と、f の値が定数とわかっている閉じた点
    pub(crate) fn special_points(&mut self, st: &mut BState) -> Res<Vec<Poly>> {
        let mut out: Vec<Poly> = Vec::new();
        for (i, c) in self.e.k.consts().iter().enumerate() {
            if self.e.k.is_ancestor(c.branch(), st.b) {
                out.push(Poly::cnst(i as u32));
            }
        }
        // 規則の左辺 f(p(x)) に小さな有理数を代入した点 K のうち、f(K) の正規形が定数のもの
        let mut cands: Vec<Poly> = Vec::new();
        for r in &st.rules {
            if let Atom::F(p) = &r.lhs {
                if r.nvars == 0 {
                    cands.push((**p).clone());
                } else if r.nvars == 1 {
                    for c in [0i64, 1, -1] {
                        cands.push(p.subst_vars(&[Poly::int(c)]));
                    }
                }
            }
        }
        for k in cands {
            if out.len() >= 4 {
                break;
            }
            if k.as_const().is_some() || out.contains(&k) || crate::order::poly_size(&k) > 30 || !k.has_f() {
                continue;
            }
            let a = Atom::F(std::rc::Rc::new(k.clone()));
            if let Some((r, _)) = self.e.norm_atom(st, &a)? {
                if r.as_const().is_some() {
                    out.push(k);
                }
            }
        }
        Ok(out)
    }

    // ------------------------------------------------------------------
    // 代入による事実の生成

    pub(crate) fn try_instance(&mut self, st: &mut BState, f: Fact, s: Vec<Poly>, nv: u32) -> Res<bool> {
        if self.solution_rule(st).is_some() || self.round_budget == 0 {
            return Ok(false);
        }
        let key = {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            f.hash(&mut h);
            s.hash(&mut h);
            format!("i{:x}", h.finish())
        };
        if !st.tried.insert(key) {
            return Ok(false);
        }
        // 証明を作らない事前計算で無駄とわかる代入例は省く
        if self.e.clause(f).lits().len() == 1 {
            let ps = self.e.poly0(f).subst_vars(&s);
            if self.e.predict_useless(st, &ps) {
                self.bump("inst_skipped");
                return Ok(false);
            }
        }
        self.bump("instances");
        self.round_budget -= 1;
        let _ = nv;
        let nv = s.iter().flat_map(|t| t.vars()).max().map_or(0, |m| m + 1);
        let inst = self.e.k.instantiate(st.b, f, s, nv)?;
        match self.e.add_fact(st, inst)? {
            Added::New(_) => {
                self.bump("inst_new");
                Ok(true)
            }
            Added::Contradiction(_) => Ok(true),
            Added::Known => {
                self.bump("inst_known");
                Ok(false)
            }
            Added::Trivial => {
                self.bump("inst_trivial");
                Ok(false)
            }
        }
    }

    pub(crate) fn instances(&mut self, st: &mut BState, round: usize) -> Res<()> {
        self.round_budget = self.scaled(80 + 40 * round);
        // 生成元: 2 変数の単位等式（小さい順）
        let mut gens: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 2).collect();
        gens.sort_by_key(|f| poly_size(&self.e.poly0(*f)));
        gens.truncate(self.scaled(if round == 0 { 2 } else { 4 + round }));
        let t1: Vec<Poly> = vec![Poly::zero(), Poly::one(), Poly::int(-1), x(), x().neg()];
        let fx = Poly::f(x());
        let half = Poly::constant(fe_kernel::poly::qf(1, 2));
        let t2: Vec<Poly> =
            vec![fx.clone(), fx.neg(), Poly::f(Poly::zero()), x().scale(&fe_kernel::poly::q(2)), Poly::int(2), half.clone(), half.neg()];
        let specials = self.special_points(st)?;
        if std::env::var("FE_DEBUG").is_ok() {
            eprintln!("b{} round {} specials: {:?}", st.b.0, round, specials.iter().map(|p| p.to_string()).collect::<Vec<_>>());
            for r in &st.rules {
                if r.nvars == 0 {
                    eprintln!("  rule0: {} -> {}", r.lhs, r.rhs);
                }
            }
        }
        for g in gens.clone() {
            if self.closed(st) {
                return Ok(());
            }
            // 特別な点での代入
            for (i1, sp) in specials.iter().enumerate() {
                let mut pairs = vec![(x(), sp.clone()), (sp.clone(), x()), (sp.clone(), sp.clone()), (Poly::zero(), sp.clone()), (sp.clone(), Poly::zero())];
                for (i2, sp2) in specials.iter().enumerate() {
                    if i1 != i2 {
                        pairs.push((sp.clone(), sp2.clone()));
                    }
                }
                for (a, bb) in pairs {
                    if self.closed(st) || !st.units.contains(&g) {
                        break;
                    }
                    self.try_instance(st, g, vec![a, bb], 1)?;
                }
            }
            // 1 変数・0 変数の代入
            let mut pool = t1.clone();
            if round >= 1 {
                pool.extend(t2.iter().cloned());
            }
            for s in &pool {
                for t in &pool {
                    if !st.units.contains(&g) {
                        break;
                    }
                    self.try_instance(st, g, vec![s.clone(), t.clone()], 1)?;
                    if self.closed(st) {
                        return Ok(());
                    }
                }
            }
            if !st.units.contains(&g) {
                continue;
            }
            // 2 変数のままの代入（P(f(x), y) など）
            if round >= 1 {
                let fy = Poly::f(y());
                let mut two: Vec<Vec<Poly>> = vec![
                    vec![fx.clone(), y()],
                    vec![x(), fy.clone()],
                    vec![x().neg(), y()],
                    vec![x(), y().neg()],
                    vec![y(), x()],
                    vec![fx.clone(), fy.clone()],
                ];
                // ずらし・倍の代入（P(x, y + 1), P(x + 1, y), P(x, 2y) など）
                if round >= 2 {
                    let one = Poly::one();
                    two.push(vec![x(), y().add(&one)]);
                    two.push(vec![x(), y().sub(&one)]);
                    two.push(vec![x().add(&one), y()]);
                    two.push(vec![x(), y().scale(&fe_kernel::poly::q(2))]);
                    two.push(vec![x().scale(&fe_kernel::poly::q(2)), y()]);
                }
                // f(0) だけのずらし、x − 1、x + y と −y（P(x, y + c) で c = f(0) とする解答が多い）
                if round >= 3 {
                    let f0 = Poly::f(Poly::zero());
                    two.push(vec![x().sub(&Poly::one()), y()]);
                    two.push(vec![x(), y().add(&f0)]);
                    two.push(vec![x(), y().sub(&f0)]);
                    two.push(vec![x().add(&y()), y().neg()]);
                }
                // 和・差の代入と f(0) だけのずらし（第 4 ラウンド以降）
                if round >= 4 {
                    let f0 = Poly::f(Poly::zero());
                    two.push(vec![x().add(&y()), y()]);
                    two.push(vec![x().sub(&y()), y()]);
                    two.push(vec![x(), y().sub(&x())]);
                    two.push(vec![x().add(&f0), y()]);
                    two.push(vec![x().sub(&f0), y()]);
                }
                for s in two {
                    if self.closed(st) || !st.units.contains(&g) {
                        break;
                    }
                    self.try_instance(st, g, s, 2)?;
                }
            }
            // 全射性の証人: f(S(x)) = a·x + b なら v := S((v − b)/a) で f(v) を v にできる
            if round >= 1 {
                for w in self.witnesses(st) {
                    for v in 0..2usize {
                        if self.closed(st) || !st.units.contains(&g) {
                            break;
                        }
                        let mut sb = vec![x(), y()];
                        sb[v] = w.subst_vars(&[Poly::var(v as u32)]);
                        self.try_instance(st, g, sb, 2)?;
                    }
                }
            }
            // 打ち消しの代入
            let p = self.e.poly0(g);
            let invs = st.invs.clone();
            for s in self.cancel_substs(&p, round, &invs) {
                if self.closed(st) {
                    return Ok(());
                }
                if !st.units.contains(&g) {
                    break;
                }
                self.try_instance(st, g, s, 2)?;
            }
            // 分数の代入（v := (v − r)/(c·w) など）
            if round >= 1 {
                for (v, sv) in self.inverse_substs(&p) {
                    if self.closed(st) || !st.units.contains(&g) {
                        break;
                    }
                    self.inverse_instance(st, g, v, sv)?;
                }
            }
        }
        // 1 変数の事実の自己代入
        if round >= 1 {
            let mut ones: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 1).collect();
            ones.sort_by_key(|f| poly_size(&self.e.poly0(*f)));
            ones.truncate(self.scaled(12));
            let mut pool = vec![x().neg(), Poly::zero(), Poly::one()];
            if round >= 2 {
                pool.push(Poly::f(x()));
                pool.push(x().pow(2));
                pool.push(x().pow(2).neg());
                pool.push(Poly::int(-1));
                pool.push(x().add(&Poly::one()));
                pool.push(x().sub(&Poly::one()));
            }
            let all_ones: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 1).collect();
            for f in all_ones {
                let p = self.e.poly0(f);
                for sb in affine_inv_substs(&p, &st.invs) {
                    if self.closed(st) {
                        return Ok(());
                    }
                    if !st.units.contains(&f) {
                        break;
                    }
                    self.try_instance(st, f, vec![sb], 1)?;
                }
            }
            for f in ones {
                for s in &pool {
                    if self.closed(st) {
                        return Ok(());
                    }
                    if !st.units.contains(&f) {
                        break;
                    }
                    self.try_instance(st, f, vec![s.clone()], 1)?;
                }
            }
        }
        Ok(())
    }

    /// 全射性の証人 S（f(S(t)) = t）。1 変数の単位等式 f(u(x)) = a·x + b（a ≠ 0 の有理数, b は閉じた式）から S(t) = u((t − b)/a)
    pub(crate) fn witnesses(&self, st: &BState) -> Vec<Poly> {
        let mut out: Vec<Poly> = Vec::new();
        for &f in &st.units {
            if self.e.nvars(f) != 1 {
                continue;
            }
            let p = self.e.poly0(f);
            for (m, lam) in p.terms() {
                if m.factors().len() != 1 || m.factors()[0].1 != 1 {
                    continue;
                }
                let u = match &m.factors()[0].0 {
                    Atom::F(u) if u.has_var() && **u != x() => (**u).clone(),
                    _ => continue,
                };
                let r = Poly::mono(m.clone(), lam.clone()).sub(&p).scale(&(Q::one() / lam));
                let cs = coeffs_in(&r, &Atom::Var(0));
                if cs.keys().max() != Some(&1) || r.has_f() && f_atoms_with_vars(&r).len() > 0 {
                    continue;
                }
                let a = match cs.get(&1).and_then(|c| c.as_const()) {
                    Some(a) if !a.is_zero() => a,
                    _ => continue,
                };
                let bb = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
                if bb.has_var() {
                    continue;
                }
                let arg = x().sub(&bb).scale(&(Q::one() / a));
                let w = u.subst_vars(&[arg]);
                if poly_size(&w) <= 24 && !out.contains(&w) {
                    out.push(w);
                }
            }
            if out.len() >= 3 {
                break;
            }
        }
        out
    }

    /// 分数の代入の候補: f の引数 u が変数 v について 1 次で係数が c·w（w は他方の変数、c は 0 でない有理数）なら、
    /// v := (v − r)/(c·w)（u を v にする）と v := −r/(c·w)（u を 0 にする）。2 つの引数の差についても同様（引数を等しくする）。
    pub(crate) fn inverse_substs(&self, p: &Poly) -> Vec<(u32, Poly)> {
        let mut atoms: Vec<Poly> = Vec::new();
        for a in p.top_atoms() {
            if let Atom::F(u) = &a {
                if u.has_var() {
                    atoms.push((**u).clone());
                }
            }
        }
        let mut diffs: Vec<(Poly, bool)> = atoms.iter().map(|u| (u.clone(), true)).collect();
        for i in 0..atoms.len() {
            for j in (i + 1)..atoms.len() {
                diffs.push((atoms[i].sub(&atoms[j]), false));
            }
        }
        let mut out: Vec<(u32, Poly)> = Vec::new();
        for (u, single) in diffs {
            for v in 0..2u32 {
                let w = 1 - v;
                let av = Atom::Var(v);
                if u.terms().iter().any(|(m, _)| m.factors().iter().any(|(b, _)| *b != av && Poly::from_atom(b.clone()).vars().contains(&v))) {
                    continue;
                }
                let cs = coeffs_in(&u, &av);
                if cs.keys().max() != Some(&1) {
                    continue;
                }
                let a = &cs[&1];
                // 係数が c·w の形
                let c = match a.terms() {
                    [(m, c)] if m.factors() == [(Atom::Var(w), 1)] => c.clone(),
                    _ => continue,
                };
                let r = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
                let iw = Poly::inv(Poly::var(w)).scale(&(Q::one() / &c));
                if single {
                    let s1 = Poly::var(v).sub(&r).mul(&iw);
                    if !out.contains(&(v, s1.clone())) {
                        out.push((v, s1));
                    }
                }
                if !r.is_zero() {
                    let s0 = r.neg().mul(&iw);
                    if !out.contains(&(v, s0.clone())) {
                        out.push((v, s0));
                    }
                }
            }
        }
        out.truncate(self.scaled(6));
        out
    }

    /// t − t(w := 0) を、「w ≠ 0 ∨ …」の形の事実の一次結合で表す項目（Σ 係数·保存形 = t − t(w := 0)）。
    /// f(s) で s が w を含むなら、内側から再帰的に「f(s) − f(s₀) = 0 ∨ w ≠ 0」を合同性で作り、
    /// 残りの多項式の部分は w で割り切れることを使って排中律のリテラル w = 0 に掛ける。扱えなければ None。
    pub(crate) fn zero_case_items(
        &mut self,
        b: BranchId,
        t: &Poly,
        w: u32,
        eo: Fact,
        ie: usize,
        ke: &Q,
        depth: u32,
    ) -> Res<Option<Vec<(Poly, Fact, usize)>>> {
        if depth > 4 {
            return Ok(None);
        }
        let mut z = vec![x(), y()];
        z[w as usize] = Poly::zero();
        let mut items: Vec<(Poly, Fact, usize)> = Vec::new();
        let mut cur = t.clone();
        for a in t.top_atoms() {
            match &a {
                Atom::F(s0) if s0.vars().contains(&w) => {
                    let sz = s0.subst_vars(&z);
                    let inner = match self.zero_case_items(b, s0, w, eo, ie, ke, depth + 1)? {
                        Some(v) => v,
                        None => return Ok(None),
                    };
                    if inner.is_empty() {
                        continue;
                    }
                    let cg = self.e.k.congruence(b, 2, sz.clone(), inner)?;
                    let target = Poly::from_atom(a.clone()).sub(&Poly::f(sz.clone()));
                    let (ic, kc) = match find_lit(self.e.clause(cg), &target) {
                        Some(t) => t,
                        None => return Ok(None),
                    };
                    let (cur2, q) = replace_atom(&cur, &a, &Poly::f(sz));
                    items.push((q.scale(&(Q::one() / &kc)), cg, ic));
                    cur = cur2;
                }
                Atom::Inv(s0) if s0.vars().contains(&w) => return Ok(None),
                _ => {}
            }
        }
        let rest = cur.sub(&t.subst_vars(&z));
        if !rest.is_zero() {
            match crate::polyutil::exact_div(&rest, &Poly::var(w)) {
                Some(r) => items.push((r.scale(&(Q::one() / ke)), eo, ie)),
                None => return Ok(None),
            }
        }
        Ok(Some(items))
    }

    /// 分数の代入: 2 変数の単位等式 g に v := sv（inv(w) を含む）を代入し、w·inv(w) を 1 に約した式 E' について
    ///  (A) 逆数の公理「w = 0 ∨ w·inv(w) = 1」と合同性・一次結合で「w = 0 ∨ E' = 0」
    ///  (B) 排中律「w = 0 ∨ w ≠ 0」の w = 0 を代入した形と、E'(w = 0) の書き換えで「w ≠ 0 ∨ E' = 0」
    /// を作り、導出原理で「∀x,y. E' = 0」を得る。途中の形が扱えなければ何もしない（すべて検証核の規則で示す）。
    pub(crate) fn inverse_instance(&mut self, st: &mut BState, g: Fact, v: u32, sv: Poly) -> Res<bool> {
        let key = format!("invsub|{:?}|{}|{}", g, v, sv);
        if !st.tried.insert(key) {
            return Ok(false);
        }
        let w = 1 - v;
        let b = st.b;
        let wv = Poly::var(w);
        let one_minus = wv.mul(&Poly::inv(wv.clone())).sub(&Poly::one());
        let mut sb = vec![x(), y()];
        sb[v as usize] = sv;
        let p = self.e.poly0(g).subst_vars(&sb);
        let p1 = cancel_inv(&p, w);
        if p1.has_inv() || p1 == p || p1.is_zero() || poly_size(&p1) > self.e.size_cap {
            return Ok(false);
        }
        let mut z = vec![x(), y()];
        z[w as usize] = Poly::zero();
        let p0 = p1.subst_vars(&z);
        self.bump("invsub_try");
        let inst = self.e.k.instantiate(b, g, sb, 2)?;
        let pi = self.e.poly0(inst);
        let k0 = match scale_ratio(&pi, &p) {
            Some(k) => k,
            None => return Ok(false),
        };
        // (A)
        let ax = self.e.k.inv_axiom(b, 2, wv.clone())?;
        let (ia, ka) = match find_lit(self.e.clause(ax), &one_minus) {
            Some(t) => t,
            None => return Ok(false),
        };
        let mut items: Vec<(Poly, Fact, usize)> = vec![(Poly::constant(Q::one() / &k0), inst, 0)];
        let mut cur = p.clone();
        for a in p.top_atoms() {
            if let Atom::F(u) = &a {
                let u1 = cancel_inv(u, w);
                if u1 == **u {
                    continue;
                }
                let m = match crate::polyutil::exact_div(&(**u).sub(&u1), &one_minus) {
                    Some(m) => m,
                    None => return Ok(false),
                };
                let cg = self.e.k.congruence(b, 2, u1.clone(), vec![(m.scale(&(Q::one() / &ka)), ax, ia)])?;
                let target = Poly::from_atom(a.clone()).sub(&Poly::f(u1.clone()));
                let (ic, kc) = match find_lit(self.e.clause(cg), &target) {
                    Some(t) => t,
                    None => return Ok(false),
                };
                let (cur2, q) = replace_atom(&cur, &a, &Poly::f(u1));
                items.push((q.scale(&(-Q::one() / &kc)), cg, ic));
                cur = cur2;
            }
        }
        let rest = cur.sub(&p1);
        if !rest.is_zero() {
            match crate::polyutil::exact_div(&rest, &one_minus) {
                Some(r) => items.push((r.scale(&(-Q::one() / &ka)), ax, ia)),
                None => return Ok(false),
            }
        }
        let ca = self.e.k.lincomb(b, 2, items)?;
        // (B)
        let eo = self.e.k.eq_or_ne(b, 2, wv.clone())?;
        let (ie, ke) = match find_lit(self.e.clause(eo), &wv) {
            Some(t) => t,
            None => return Ok(false),
        };
        let mut items2 = match self.zero_case_items(b, &p1, w, eo, ie, &ke, 0)? {
            Some(v) => v,
            None => return Ok(false),
        };
        let (d2, its0) = self.e.rw_poly(st, &p0, 2)?;
        if !d2.is_zero() {
            // w = 0 の場合を示せないときは条件つきの事実「w = 0 ∨ E' = 0」だけを加える
            self.e.add_fact(st, ca)?;
            return Ok(true);
        }
        items2.extend(its0);
        if items2.is_empty() {
            return Ok(false);
        }
        let cb = self.e.k.lincomb(b, 2, items2)?;
        // 導出原理: (A) の w = 0 と (B) の w ≠ 0
        let la = match self.e.clause(ca).lits().iter().position(|l| *l == Lit::eq(wv.clone())) {
            Some(i) => i,
            None => return Ok(false),
        };
        let lb = match self.e.clause(cb).lits().iter().position(|l| *l == Lit::ne(wv.clone())) {
            Some(i) => i,
            None => return Ok(false),
        };
        let r = self.e.k.resolve(b, ca, la, cb, lb)?;
        self.bump("invsub_ok");
        self.e.add_fact(st, r)?;
        Ok(true)
    }

    /// f の引数を打ち消す・単純にする代入（2 変数のまま）
    pub(crate) fn cancel_substs(&self, p: &Poly, round: usize, invs: &[(Poly, Poly)]) -> Vec<Vec<Poly>> {
        let atoms = f_atoms_with_vars(p);
        let mut out: Vec<Vec<Poly>> = Vec::new();
        let mut push = |s: Vec<Poly>| {
            if !out.contains(&s) {
                out.push(s)
            }
        };
        for u in &atoms {
            for v in 0..2u32 {
                // u = v·(a·v + b) なら v := −b/a で u = 0
                if let Some(r) = root_after_factor(u, v) {
                    let mut s = vec![x(), y()];
                    s[v as usize] = r;
                    push(s);
                }
                if let Some((a, w)) = linear_in(u, v) {
                    let inv = Q::one() / a;
                    // u を変数 v そのものにする: v := (v − w)/a
                    let mut s = vec![x(), y()];
                    s[v as usize] = Poly::var(v).sub(&w).scale(&inv);
                    push(s);
                    // u = 0 にする: v := −w/a
                    let mut s0 = vec![x(), y()];
                    s0[v as usize] = w.neg().scale(&inv);
                    push(s0);
                }
            }
        }
        // 正定値化: f の引数が c·Y² + a·X + b（c > 0, a ≠ 0）なら Y := X − a/(2c) で c·X² + (b + a²/(4c)) にする
        for u in &atoms {
            for (sq, li) in [(1u32, 0u32), (0, 1)] {
                let ys = coeffs_in(u, &Atom::Var(sq));
                if ys.keys().max() != Some(&2) || ys.contains_key(&1) {
                    continue;
                }
                let c = match ys.get(&2).and_then(|c| c.as_const()) {
                    Some(c) if c > Q::zero() => c,
                    _ => continue,
                };
                let rest = ys.get(&0).cloned().unwrap_or_else(Poly::zero);
                let xs = coeffs_in(&rest, &Atom::Var(li));
                if xs.keys().max() != Some(&1) {
                    continue;
                }
                let a = match xs.get(&1).and_then(|c| c.as_const()) {
                    Some(a) => a,
                    None => continue,
                };
                let b0 = xs.get(&0).cloned().unwrap_or_else(Poly::zero);
                let bq = match b0.as_const() {
                    Some(b) => b,
                    None => continue,
                };
                let four = Q::from_integer(4.into());
                if bq.clone() + &a * &a / (&four * &c) <= Q::zero() {
                    continue;
                }
                let k = -(&a / (Q::from_integer(2.into()) * &c));
                let mut s = vec![x(), y()];
                s[sq as usize] = Poly::var(li).add(&Poly::constant(k));
                push(s);
            }
        }
        // 正定値化（一般形）: f の引数が c·X² + L（c > 0、L は X を含まない定数でない式）なら
        // X := L − 1/(2c) で c·L² + 1/(4c) にする（「X を十分大きくとる」議論の代わり）
        for u in &atoms {
            for sq in [0u32, 1] {
                let xs = coeffs_in(u, &Atom::Var(sq));
                if xs.keys().max() != Some(&2) || xs.contains_key(&1) {
                    continue;
                }
                let c = match xs.get(&2).and_then(|c| c.as_const()) {
                    Some(c) if c > Q::zero() => c,
                    _ => continue,
                };
                let l = xs.get(&0).cloned().unwrap_or_else(Poly::zero);
                if l.as_const().is_some() || l.vars().contains(&sq) {
                    continue;
                }
                // X が原子の中にも現れないこと
                if u.terms().iter().any(|(m, _)| m.factors().iter().any(|(b, _)| *b != Atom::Var(sq) && Poly::from_atom(b.clone()).vars().contains(&sq))) {
                    continue;
                }
                let h = Q::one() / (Q::from_integer(2.into()) * &c);
                let mut s = vec![x(), y()];
                s[sq as usize] = l.sub(&Poly::constant(h));
                push(s);
            }
        }
        // 係数が閉じた可逆な式（f(j) など）の場合: v := (v − w)·inv(c)
        for u in &atoms {
            for v in 0..2u32 {
                if let Some((c, w)) = linear_in_closed(u, v) {
                    if let Some((_, ic)) = invs.iter().find(|(a, _)| *a == c) {
                        let mut s = vec![x(), y()];
                        s[v as usize] = Poly::var(v).sub(&w).mul(ic);
                        push(s);
                        let mut s0 = vec![x(), y()];
                        s0[v as usize] = w.neg().mul(ic);
                        push(s0);
                    }
                }
            }
        }
        if round >= 1 {
            for i in 0..atoms.len() {
                for j in (i + 1)..atoms.len() {
                    let d = atoms[i].sub(&atoms[j]);
                    for v in 0..2u32 {
                        if let Some((a, w)) = linear_in(&d, v) {
                            let mut s = vec![x(), y()];
                            s[v as usize] = w.neg().scale(&(Q::one() / a));
                            push(s);
                        } else if let Some(r) = root_after_factor(&d, v) {
                            // 2 つの引数の差が v·(a·v + b): v := −b/a で引数が一致する
                            let mut s = vec![x(), y()];
                            s[v as usize] = r;
                            push(s);
                        }
                        // 係数が閉じた可逆な式なら、その逆数で解く
                        if let Some((c, w)) = linear_in_closed(&d, v) {
                            if let Some((_, ic)) = invs.iter().find(|(a, _)| *a == c) {
                                let mut s = vec![x(), y()];
                                s[v as usize] = w.neg().mul(ic);
                                push(s);
                            }
                        }
                    }
                }
            }
        }
        out
    }

    // ------------------------------------------------------------------
    // 消去法（1 変数・0 変数の単位等式の一次結合）

}
