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
            // 規則に導かれる代入: 1 変数の規則 f(T(x)) → … があれば、f(v) を含む事実で v := T(v) とし、f(T(v)) を書き換える
            // （例: f(f(y) + c) = y + d があれば y := f(y) + c。f(x f(y) + g(x)) = xy + h(x) を f(xy + …) = x f(y) + … にする）
            if round >= 1 {
                let mut ts: Vec<Poly> = Vec::new();
                for r in &st.rules {
                    if r.nvars != 1 {
                        continue;
                    }
                    if let Atom::F(t) = &r.lhs {
                        let t = (**t).clone();
                        if t.has_var() && t != x() && t.has_f() && poly_size(&t) <= 16 && !ts.contains(&t) {
                            ts.push(t);
                        }
                    }
                }
                ts.truncate(self.scaled(3));
                let pg = self.e.poly0(g);
                for t in ts {
                    for v in 0..2u32 {
                        if self.closed(st) || !st.units.contains(&g) {
                            break;
                        }
                        // f(v) が（入れ子の中も含めて）現れるときだけ
                        if !f_atoms_with_vars(&pg).iter().any(|u| *u == Poly::var(v)) {
                            continue;
                        }
                        let mut sb = vec![x(), y()];
                        sb[v as usize] = t.subst_vars(&[Poly::var(v)]);
                        if self.try_instance(st, g, sb, 2)? {
                            self.bump("rule_subst");
                        }
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
            // 分数の代入（v := (v − r)/(c·w) など）。分母が一般の式のもの（条件つきの事実を 1 つ作るだけ）は第 0 ラウンドから
            let mut ks: Vec<Poly> = vec![Poly::one(), Poly::int(-1)];
            for &u in &st.units {
                if self.e.nvars(u) == 0 {
                    for a in self.e.poly0(u).top_atoms() {
                        if let Atom::F(k) = &a {
                            if k.terms().len() == 1 && k.as_const().is_none() && !k.has_f() && !ks.contains(k) && ks.len() < 4 {
                                ks.push((**k).clone());
                            }
                        }
                    }
                }
            }
            for (v, sv, den) in self.inverse_substs(&p, &ks) {
                if self.closed(st) || !st.units.contains(&g) {
                    break;
                }
                if round == 0 && den == Poly::var(1 - v) {
                    continue;
                }
                self.inverse_instance(st, g, v, sv, den)?;
            }
        }
        // 全射性の証人を、x が f(x) を通してだけ現れる 1 変数の事実に代入する（f(x) を変数に置き換える）
        if round >= 1 {
            let ws = self.witnesses(st);
            if !ws.is_empty() {
                let fxa = Atom::F(std::rc::Rc::new(x()));
                let ones: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 1).collect();
                for f in ones {
                    let p = self.e.poly0(f);
                    let (pw, _) = replace_atom(&p, &fxa, &Poly::var(5));
                    if pw.vars().contains(&0) || !pw.vars().contains(&5) {
                        continue;
                    }
                    for w in &ws {
                        if self.closed(st) {
                            return Ok(());
                        }
                        if !st.units.contains(&f) {
                            break;
                        }
                        self.try_instance(st, f, vec![w.clone()], 1)?;
                    }
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
            // 右辺を 0 にする代入: 1 変数の事実から、x を引数に含む最大の f の項を除いた残りを単項式の因子で割り、
            // x について 1 次 x·a + c（a は有理数、c は閉じた式）なら x := −c/a（例: f(x f(x)) = f(x)(x + f(0)) で x := −f(0)）
            for f in all_ones.iter().copied().take(self.scaled(12)) {
                let p = self.e.poly0(f);
                let big = p
                    .top_atoms()
                    .into_iter()
                    .filter(|a| matches!(a, Atom::F(u) if u.vars().contains(&0) && **u != x()))
                    .max_by_key(|a| poly_size(&Poly::from_atom(a.clone())));
                let big = match big {
                    Some(b) => b,
                    None => continue,
                };
                let (rest, _) = replace_atom(&p, &big, &Poly::zero());
                if rest.is_zero() {
                    continue;
                }
                let content = monomial_content(&rest);
                let r = div_mono(&rest, &content);
                let cs = coeffs_in(&r, &Atom::Var(0));
                if cs.keys().max() != Some(&1) || r.terms().iter().any(|(m, _)| m.factors().iter().any(|(a, _)| *a != Atom::Var(0) && Poly::from_atom(a.clone()).vars().contains(&0))) {
                    continue;
                }
                let a1 = match cs.get(&1).and_then(|c| c.as_const()) {
                    Some(a) if !a.is_zero() => a,
                    _ => continue,
                };
                let c0 = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
                if c0.is_zero() || c0.has_var() {
                    continue;
                }
                let root = c0.neg().scale(&(Q::one() / a1));
                if self.closed(st) {
                    return Ok(());
                }
                if self.try_instance(st, f, vec![root], 0)? {
                    self.bump("root_subst");
                }
            }
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
            // 規則の自己合成（f(f(x) + c) = x + d から平行移動 f(x + c + d) = f(x) + c + d）
            self.self_compose_rules(st)?;
            if self.closed(st) {
                return Ok(());
            }
            // 規則に導かれる代入（1 変数）: 1 変数の規則 f(T(x)) → …（T は x と f を含む）があれば、f(x) を含む 1 変数の事実で
            // x := T(x) とし、f(T(x)) を書き換える（例: f(f(x) + c) = x + d に x := f(x) + c で f(x + c + d) = f(x) + c + d）
            let mut ts: Vec<Poly> = Vec::new();
            for r in &st.rules {
                if r.nvars != 1 {
                    continue;
                }
                if let Atom::F(t) = &r.lhs {
                    let t = (**t).clone();
                    if t.has_var() && t != x() && t.has_f() && poly_size(&t) <= 20 && !ts.contains(&t) {
                        ts.push(t);
                    }
                }
            }
            ts.truncate(self.scaled(3));
            if !ts.is_empty() {
                let fx = x();
                let mut cands: Vec<Fact> = ones.iter().copied().filter(|&f| f_atoms_with_vars(&self.e.poly0(f)).iter().any(|u| *u == fx)).collect();
                cands.truncate(self.scaled(6));
                for f in cands {
                    for t in &ts {
                        if self.closed(st) {
                            return Ok(());
                        }
                        if !st.units.contains(&f) {
                            break;
                        }
                        if self.try_instance(st, f, vec![t.clone()], 1)? {
                            self.bump("rule_subst1");
                        }
                    }
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
        // 結果は枝・単位等式の一覧・逆数の一覧だけで決まる（事実の式は変わらない）ので、これらが同じなら前回の結果を使う
        let key = {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            st.b.hash(&mut h);
            st.units.hash(&mut h);
            st.invs.hash(&mut h);
            h.finish()
        };
        if let Some((k, w)) = self.wit_cache.borrow().as_ref() {
            if *k == key {
                return w.clone();
            }
        }
        let out = self.witnesses_uncached(st);
        *self.wit_cache.borrow_mut() = Some((key, out.clone()));
        out
    }

    fn witnesses_uncached(&self, st: &BState) -> Vec<Poly> {
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
                // 係数は 0 でない有理数か、逆数のわかっている閉じた式（f(a) ≠ 0 の f(a) など）
                let inv_a: Poly = match cs.get(&1) {
                    Some(c) => match c.as_const() {
                        Some(a) if !a.is_zero() => Poly::constant(Q::one() / a),
                        Some(_) => continue,
                        None => match st.invs.iter().find(|(u, _)| u == c) {
                            Some((_, iu)) => iu.clone(),
                            None => continue,
                        },
                    },
                    None => continue,
                };
                let bb = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
                if bb.has_var() {
                    continue;
                }
                let arg = x().sub(&bb).mul(&inv_a);
                let w = u.subst_vars(&[arg]);
                // 大きさの上限 40（f(x − f(0)²) + f(0)² が 30。以前の 24 ではこの証人が使われなかった）
                if poly_size(&w) <= 40 && !out.contains(&w) {
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
    /// 係数が他方の変数の一般の式 a(w)（f(x) − x など）の場合も、a(w) ≠ 0 の点についての代入 v := (v − r)/a(w)、
    /// v := −r/a(w) を候補にする（分母 a(w) を返す。結論は「a(w) = 0 ∨ …」の形になる）。
    /// f の引数（入れ子の中も含む）が c·x·y のときは、v := K/(c·w)（K は 1, −1 と、この枝で f の値がわかる閉じた点）で
    /// 引数を定数 K にする候補も作る（P(x, 1/x)、f(s) = 0 の s で P(x, s/x) など）。
    pub(crate) fn inverse_substs(&self, p: &Poly, ks: &[Poly]) -> Vec<(u32, Poly, Poly)> {
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
        let mut out: Vec<(u32, Poly, Poly)> = Vec::new();
        let mut gen: Vec<(u32, Poly, Poly)> = Vec::new();
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
                let r = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
                if r.has_inv() {
                    continue;
                }
                // 係数が c·w の形（分母は変数 w）か、w の一般の式（分母はその式）
                let (iw, den, list) = match a.terms() {
                    [(m, c)] if m.factors() == [(Atom::Var(w), 1)] => (Poly::inv(Poly::var(w)).scale(&(Q::one() / c)), Poly::var(w), &mut out),
                    _ if a.as_const().is_none() && a.vars() == [w].into_iter().collect() && !a.has_inv() && poly_size(a) <= 20 => {
                        (Poly::inv(a.clone()), a.clone(), &mut gen)
                    }
                    _ => continue,
                };
                if single {
                    let s1 = Poly::var(v).sub(&r).mul(&iw);
                    if !list.iter().any(|(v2, s2, _)| *v2 == v && *s2 == s1) {
                        list.push((v, s1, den.clone()));
                    }
                }
                if !r.is_zero() {
                    let s0 = r.neg().mul(&iw);
                    if !list.iter().any(|(v2, s2, _)| *v2 == v && *s2 == s0) {
                        list.push((v, s0, den.clone()));
                    }
                }
            }
        }
        let mut inn: Vec<(u32, Poly, Poly)> = Vec::new();
        for u in f_atoms_with_vars(p) {
            let c = match u.terms() {
                [(m, c)] if m.factors().len() == 2 && m.factors().iter().all(|(a, e)| *e == 1 && matches!(a, Atom::Var(_))) => c.clone(),
                _ => continue,
            };
            for v in 0..2u32 {
                let w = 1 - v;
                let iw = Poly::inv(Poly::var(w)).scale(&(Q::one() / &c));
                for k in ks {
                    let sv = k.mul(&iw);
                    if !out.iter().chain(inn.iter()).any(|(v2, s2, _)| *v2 == v && *s2 == sv) {
                        inn.push((v, sv, Poly::var(w)));
                    }
                }
            }
        }
        out.truncate(self.scaled(6));
        gen.truncate(self.scaled(4));
        inn.truncate(self.scaled(4));
        out.extend(gen);
        out.extend(inn);
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
    ///
    /// 分母 den が変数 w でない一般の式 D（f(x) − x など）のときは (A) だけを作り、条件つきの事実「D = 0 ∨ E' = 0」を加える。
    pub(crate) fn inverse_instance(&mut self, st: &mut BState, g: Fact, v: u32, sv: Poly, den: Poly) -> Res<bool> {
        let key = format!("invsub|{:?}|{}|{}", g, v, sv);
        if !st.tried.insert(key) {
            return Ok(false);
        }
        let w = 1 - v;
        let b = st.b;
        let general = den != Poly::var(w);
        let wv = den;
        let one_minus = wv.mul(&Poly::inv(wv.clone())).sub(&Poly::one());
        let red = |q: &Poly| -> Option<Poly> {
            if general {
                reduce_inv(q, &wv)
            } else {
                Some(cancel_inv(q, w))
            }
        };
        let mut sb = vec![x(), y()];
        sb[v as usize] = sv;
        let p = self.e.poly0(g).subst_vars(&sb);
        let p1 = match red(&p) {
            Some(q) => q,
            None => return Ok(false),
        };
        // inv(w) が f の引数の外にだけ残るなら、両辺に w^k を掛けて消す（w ≠ 0 の場合の式なので同値。分母が変数のときだけ）
        let iwa = Atom::Inv(std::rc::Rc::new(Poly::var(w)));
        let mut wk: Option<Poly> = None;
        let mut p2 = p1.clone();
        if p1.has_inv() && !general {
            let inner_inv = f_atoms_with_vars(&p1).iter().any(|u| u.has_inv());
            let k = p1.terms().iter().map(|(m, _)| m.factors().iter().filter(|(a, _)| *a == iwa).map(|(_, e)| *e).sum::<u32>()).max().unwrap_or(0);
            if !inner_inv && k >= 1 && k <= 2 {
                let m = Poly::var(w).pow(k);
                let e2 = cancel_inv(&p1.mul(&m), w);
                if !e2.has_inv() {
                    p2 = e2;
                    wk = Some(m);
                }
            }
        }
        let p1_raw = p1;
        let p1 = p2;
        // 逆数が f の引数の中にだけ残る場合は、条件つきの事実「w = 0 ∨ E' = 0」（E' は f の引数に 1/w を含む）として持つ
        // ただし逆数の代入（reciprocal_instances）で消せる形、つまり逆数を含む f の引数がちょうど K/x（K は変数を含まない）のときだけ
        let inner_only = p1.has_inv()
            && p1.terms().iter().all(|(m, _)| m.factors().iter().all(|(a, _)| !matches!(a, Atom::Inv(_))))
            && f_atoms_with_vars(&p1).iter().filter(|u| u.has_inv()).all(|u| {
                u.terms().len() == 1 && {
                    let (m, _) = &u.terms()[0];
                    let invs: Vec<_> = m.factors().iter().filter(|(a, _)| matches!(a, Atom::Inv(_))).collect();
                    invs.len() == 1
                        && invs[0].1 == 1
                        && matches!(&invs[0].0, Atom::Inv(q) if q.terms().len() == 1 && matches!(q.terms()[0].0.factors(), [(Atom::Var(_), 1)]))
                        && m.factors().iter().all(|(a, _)| matches!(a, Atom::Inv(_)) || !Poly::from_atom(a.clone()).has_var())
                }
            });
        if (p1.has_inv() && !inner_only) || p1 == p || p1.is_zero() || poly_size(&p1) > self.e.size_cap {
            return Ok(false);
        }
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
        // p − E を「w = 0 ∨ …」の事実の一次結合で表す（入れ子の f の中も内側から合同性で）
        let diff = match self.inv_items(b, &p, general, w, &wv, &one_minus, ax, ia, &ka, 0)? {
            Some(v) => v,
            None => return Ok(false),
        };
        items.extend(diff.into_iter().map(|(c, f, i)| (c.neg(), f, i)));
        // w^k を掛けた場合: 各項目の係数に w^k を掛け、w^k·E − E'（(w·inv(w) − 1) の倍数）を逆数の公理で引く
        if let Some(m) = &wk {
            items = items.into_iter().map(|(c, f, i)| (c.mul(m), f, i)).collect();
            let rest2 = p1_raw.mul(m).sub(&p1);
            if !rest2.is_zero() {
                match crate::polyutil::exact_div(&rest2, &one_minus) {
                    Some(r) => items.push((r.scale(&(-Q::one() / &ka)), ax, ia)),
                    None => return Ok(false),
                }
            }
            self.bump("invsub_mul");
        }
        let ca = self.e.k.lincomb(b, 2, items)?;
        if inner_only {
            self.bump("invsub_inner");
            let ca = self.tidy_clause(st, ca)?;
            self.e.add_fact(st, ca)?;
            return Ok(true);
        }
        if general {
            self.bump("invsub_gen");
            let ca = self.tidy_clause(st, ca)?;
            self.e.add_fact(st, ca)?;
            return Ok(true);
        }
        let mut z = vec![x(), y()];
        z[w as usize] = Poly::zero();
        let p0 = p1.subst_vars(&z);
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

    /// 逆数のわかる閉じた係数での 1 次の代入: 1 変数の事実の f の引数が c·x + d（c は逆数のわかる閉じた式）なら x := (x − d)/c。
    /// 安くて決定的なこと（f(e·x) = 0 と e ≠ 0 から f ≡ 0 など）が多いので、場合分けより先に毎ラウンド行う。
    pub(crate) fn affine_inverse_ones(&mut self, st: &mut BState) -> Res<()> {
        if st.invs.is_empty() {
            return Ok(());
        }
        let ones: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 1).collect();
        for f in ones {
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
        Ok(())
    }

    /// t − red(t)（red は w·inv(w) = 1 での簡約）を、逆数の公理「w = 0 ∨ w·inv(w) − 1 = 0」と、そこから合同性で作る
    /// 「w = 0 ∨ f(u) − f(red(u)) = 0」の一次結合で表す項目（Σ 係数·保存形 = t − red(t)）。入れ子の f は内側から作る。
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn inv_items(
        &mut self,
        b: BranchId,
        t: &Poly,
        general: bool,
        w: u32,
        wv: &Poly,
        one_minus: &Poly,
        ax: Fact,
        ia: usize,
        ka: &Q,
        depth: u32,
    ) -> Res<Option<Vec<(Poly, Fact, usize)>>> {
        if depth > 4 {
            return Ok(None);
        }
        let red = |q: &Poly| -> Option<Poly> {
            if general {
                reduce_inv(q, wv)
            } else {
                Some(cancel_inv(q, w))
            }
        };
        let t1 = match red(t) {
            Some(q) => q,
            None => return Ok(None),
        };
        let mut items: Vec<(Poly, Fact, usize)> = Vec::new();
        let mut cur = t.clone();
        for a in t.top_atoms() {
            if let Atom::F(u) = &a {
                let u1 = match red(u) {
                    Some(q) => q,
                    None => return Ok(None),
                };
                if u1 == **u {
                    continue;
                }
                let inner = match self.inv_items(b, u, general, w, wv, one_minus, ax, ia, ka, depth + 1)? {
                    Some(v) => v,
                    None => return Ok(None),
                };
                let cg = self.e.k.congruence(b, 2, u1.clone(), inner)?;
                let target = Poly::from_atom(a.clone()).sub(&Poly::f(u1.clone()));
                let (ic, kc) = match find_lit(self.e.clause(cg), &target) {
                    Some(t) => t,
                    None => return Ok(None),
                };
                let (cur2, q) = replace_atom(&cur, &a, &Poly::f(u1));
                items.push((q.scale(&(Q::one() / &kc)), cg, ic));
                cur = cur2;
            }
        }
        let rest = cur.sub(&t1);
        if !rest.is_zero() {
            match crate::polyutil::exact_div(&rest, one_minus) {
                Some(r) => items.push((r.scale(&(Q::one() / ka)), ax, ia)),
                None => return Ok(None),
            }
        }
        Ok(Some(items))
    }

    /// t − t'（t' は t の原子 a を値 val に置き換えたもの。f の引数の中も）を、節 eqf のリテラル ei（λ(a − val) = 0 の形、
    /// 係数 lam）と、そこから合同性で作る事実の一次結合で表す項目（Σ 係数·保存形 = t − t'）。扱えなければ None。
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn atom_replace_items(
        &mut self,
        b: BranchId,
        nv: u32,
        t: &Poly,
        a: &Atom,
        val: &Poly,
        eqf: Fact,
        ei: usize,
        lam: &Q,
        depth: u32,
    ) -> Res<Option<Vec<(Poly, Fact, usize)>>> {
        if depth > 4 {
            return Ok(None);
        }
        let red = |q: &Poly| q.transform(&mut |x| if x == *a { val.clone() } else { Poly::from_atom(x) });
        let diff_lit = Poly::from_atom(a.clone()).sub(val);
        let t1 = red(t);
        let mut items: Vec<(Poly, Fact, usize)> = Vec::new();
        let mut cur = t.clone();
        for at in t.top_atoms() {
            if let Atom::F(u) = &at {
                let u1 = red(u);
                if u1 == **u {
                    continue;
                }
                let inner = match self.atom_replace_items(b, nv, u, a, val, eqf, ei, lam, depth + 1)? {
                    Some(v) => v,
                    None => return Ok(None),
                };
                let cg = self.e.k.congruence(b, nv, u1.clone(), inner)?;
                let target = Poly::from_atom(at.clone()).sub(&Poly::f(u1.clone()));
                let (ic, kc) = match find_lit(self.e.clause(cg), &target) {
                    Some(t) => t,
                    None => return Ok(None),
                };
                let (cur2, q) = replace_atom(&cur, &at, &Poly::f(u1));
                items.push((q.scale(&(Q::one() / &kc)), cg, ic));
                cur = cur2;
            }
        }
        let rest = cur.sub(&t1);
        if !rest.is_zero() {
            match crate::polyutil::exact_div(&rest, &diff_lit) {
                Some(r) => items.push((r.scale(&(Q::one() / lam)), eqf, ei)),
                None => return Ok(None),
            }
        }
        Ok(Some(items))
    }

    /// 規則の自己合成: 1 変数の規則 f(T(x)) = R(x)（T は f(x) を含む）に x := T(x) を代入し、内側の f(T(x)) だけを R(x) に
    /// 書き換える（外側から書き換えると 0 = 0 になるので、合同性で内側を明示的に置き換える）。
    /// 例: f(f(x) + c) = x + d から f(x + c + d) = f(x) + c + d（平行移動）。導出: 例化・合同性・一次結合。
    pub(crate) fn self_compose_rules(&mut self, st: &mut BState) -> Res<()> {
        let rules: Vec<RwRule> = st
            .rules
            .iter()
            .filter(|r| {
                r.nvars == 1
                    && matches!(&r.lhs, Atom::F(t) if **t != x() && poly_size(t) <= 20 && f_atoms_with_vars(t).iter().any(|u| *u == x()))
            })
            .cloned()
            .collect();
        for r in rules.into_iter().take(self.scaled(3)) {
            if self.closed(st) {
                return Ok(());
            }
            if !st.tried.insert(format!("selfc|{:?}", r.fact)) {
                continue;
            }
            let t = match &r.lhs {
                Atom::F(t) => (**t).clone(),
                _ => continue,
            };
            let b = st.b;
            let base = Poly::from_atom(r.lhs.clone()).sub(&r.rhs);
            let (ei, lam) = match find_lit(self.e.clause(r.fact), &base) {
                Some(v) => v,
                None => continue,
            };
            let inst = self.e.k.instantiate(b, r.fact, vec![t.clone()], 1)?;
            let pm = base.subst_vars(&[t.clone()]);
            let (mi, mk) = match find_lit(self.e.clause(inst), &pm) {
                Some(v) => v,
                None => continue,
            };
            let items = match self.atom_replace_items(b, 1, &pm, &r.lhs, &r.rhs, r.fact, ei, &lam, 0)? {
                Some(v) => v,
                None => continue,
            };
            let mut its = vec![(Poly::constant(Q::one() / &mk), inst, mi)];
            its.extend(items.into_iter().map(|(cf, fct, li)| (cf.neg(), fct, li)));
            let cur = self.e.k.lincomb(b, 1, its)?;
            if self.e.clause(cur).lits().iter().all(|l| l.poly().is_zero()) {
                continue;
            }
            self.bump("self_compose");
            self.e.add_fact(st, cur)?;
        }
        Ok(())
    }

    /// 逆数の代入 x := K/x（K は 0 でない有理数か、逆数のわかる閉じた式）: 1 変数の節（条件「x = 0」があってもよい）で
    /// f の引数に 1/x（K/x の形）が現れるとき、x := K/x として K·(K/x)⁻¹ を x に約し、f の外に残る 1/x は x を掛けて消す。
    /// 結果は「x = 0 ∨ …」（x ≠ 0 でだけ成り立つ）。導出: 逆数の公理（K/x と x）・排中律・一次結合・合同性・導出原理。
    /// 例: x ≠ 0 で x·f(1/x) = f(1) から、x ≠ 0 で f(x) = f(1)·x。
    pub(crate) fn reciprocal_instances(&mut self, st: &mut BState) -> Res<()> {
        let x0 = x();
        let ix = Atom::Inv(std::rc::Rc::new(x0.clone()));
        let cands: Vec<Fact> = st
            .units
            .iter()
            .chain(st.others.iter())
            .copied()
            .filter(|&f| {
                let c = self.e.clause(f);
                c.nvars() == 1
                    && c.lits().len() <= 2
                    && c.lits().iter().all(|l| l.rel() == Rel::Eq)
                    && c.lits().iter().any(|l| f_atoms_with_vars(l.poly()).iter().any(|u| u.has_inv()))
            })
            .collect();
        for f in cands.into_iter().take(self.scaled(6)) {
            if self.closed(st) {
                return Ok(());
            }
            let key = format!("recip|{:?}", f);
            if !st.tried.insert(key) {
                continue;
            }
            let c = self.e.clause(f).clone();
            // 条件のリテラルは「x = 0」だけ許す
            let side: Vec<usize> = (0..c.lits().len()).filter(|&i| c.lits()[i] == Lit::eq(x0.clone())).collect();
            let main: Vec<usize> = (0..c.lits().len()).filter(|i| !side.contains(i)).collect();
            if main.len() != 1 {
                continue;
            }
            let p = c.lits()[main[0]].poly().clone();
            // K: f の引数の中の K·inv(x) の係数（有理数か閉じた式）
            let mut k: Option<Poly> = None;
            for u in f_atoms_with_vars(&p) {
                let cs = coeffs_in(&u, &ix);
                if let Some(kk) = cs.get(&1) {
                    if !kk.has_var() && !kk.has_inv() && !kk.is_zero() {
                        k = Some(kk.clone());
                        break;
                    }
                }
            }
            let k = match k {
                Some(k) => k,
                None => continue,
            };
            // K の逆数: 有理数ならそのまま、閉じた式なら st.invs から
            let kinv = match k.as_const() {
                Some(q) => Poly::constant(Q::one() / q),
                None => match st.invs.iter().find(|(u, _)| *u == k) {
                    Some((_, iu)) => iu.clone(),
                    None => continue,
                },
            };
            let b = st.b;
            let u = k.mul(&Poly::inv(x0.clone())); // K/x
            let iu = Atom::Inv(std::rc::Rc::new(u.clone()));
            // ax_u: u = 0 ∨ u·inv(u) − 1 = 0、ax_x: x = 0 ∨ x·inv(x) − 1 = 0
            let ax_u = self.e.k.inv_axiom(b, 1, u.clone())?;
            let ax_x = self.e.k.inv_axiom(b, 1, x0.clone())?;
            let one_u = u.mul(&Poly::from_atom(iu.clone())).sub(&Poly::one());
            let one_x = x0.mul(&Poly::from_atom(ix.clone())).sub(&Poly::one());
            let (iau, kau) = match find_lit(self.e.clause(ax_u), &one_u) {
                Some(t) => t,
                None => continue,
            };
            let (iax, kax) = match find_lit(self.e.clause(ax_x), &one_x) {
                Some(t) => t,
                None => continue,
            };
            // x·(u inv(u) − 1) − K inv(u)·(x inv(x) − 1) = K inv(u) − x
            let r0 = self.e.k.lincomb(
                b,
                1,
                vec![
                    (x0.scale(&(Q::one() / &kau)), ax_u, iau),
                    (k.mul(&Poly::from_atom(iu.clone())).neg().scale(&(Q::one() / &kax)), ax_x, iax),
                ],
            )?;
            // nz: x = 0 ∨ u ≠ 0（u = 0 なら x·u = K だが K ≠ 0）
            let eo = self.e.k.eq_or_ne(b, 1, u.clone())?;
            let (ieo, keo) = match find_lit(self.e.clause(eo), &u) {
                Some(t) => t,
                None => continue,
            };
            // x·u − K·(x inv x − 1) = K（u = K inv x なので x·u = K·x·inv(x)）
            let nz0 = self.e.k.lincomb(b, 1, vec![(x0.scale(&(Q::one() / &keo)), eo, ieo), (k.neg().scale(&(Q::one() / &kax)), ax_x, iax)])?;
            // nz0 は「K = 0 ∨ u ≠ 0 ∨ x = 0」。K = 0 は K が 0 でない有理数なら消えている。閉じた式なら K ≠ 0 で外す
            let mut nz = nz0;
            if let Some(i) = self.e.clause(nz).lits().iter().position(|l| *l == Lit::eq(k.clone())) {
                match st.nes.iter().copied().find(|&n| self.e.poly0(n) == k || self.e.poly0(n) == k.neg()) {
                    Some(n) => nz = self.e.k.resolve(b, nz, i, n, 0)?,
                    None => continue,
                }
            }
            // r0 の u = 0 を nz で外す → R: x = 0 ∨ K inv(u) − x = 0
            let iu0 = match self.e.clause(r0).lits().iter().position(|l| *l == Lit::eq(u.clone())) {
                Some(i) => i,
                None => continue,
            };
            let iun = match self.e.clause(nz).lits().iter().position(|l| *l == Lit::ne(u.clone())) {
                Some(i) => i,
                None => continue,
            };
            let rr = self.e.k.resolve(b, r0, iu0, nz, iun)?;
            // R のリテラル: inv(u) − x·inv(K) の定数倍
            let val = x0.mul(&kinv);
            let target = Poly::from_atom(iu.clone()).sub(&val);
            let (ri, rk) = match find_lit(self.e.clause(rr), &target) {
                Some(t) => t,
                None => continue,
            };
            // 例化 x := K/x
            let inst = self.e.k.instantiate(b, f, vec![u.clone()], 1)?;
            let ci = self.e.clause(inst).clone();
            let pm = p.subst_vars(&[u.clone()]);
            let (mi, mk) = match find_lit(&ci, &pm) {
                Some(t) => t,
                None => continue,
            };
            // inv(u) を x/K に置き換える
            let items = match self.atom_replace_items(b, 1, &pm, &iu, &val, rr, ri, &rk, 0)? {
                Some(v) => v,
                None => continue,
            };
            let pm1 = pm.transform(&mut |a| if a == iu { val.clone() } else { Poly::from_atom(a) });
            let mut its = vec![(Poly::constant(Q::one() / &mk), inst, mi)];
            its.extend(items.into_iter().map(|(cf, fct, li)| (cf.neg(), fct, li)));
            let mut cur = self.e.k.lincomb(b, 1, its)?;
            // 例化でできた条件「K/x = 0」を nz で x = 0 にする
            if let Some(i) = self.e.clause(cur).lits().iter().position(|l| *l == Lit::eq(u.clone())) {
                cur = self.e.k.resolve(b, cur, i, nz, iun)?;
            }
            // 残る 1/x（f の外）は x^k を掛けて消す
            let lits = self.e.clause(cur).lits().to_vec();
            let li = match lits.iter().position(|l| l.poly().has_inv() || !l.poly().vars().is_empty() && *l != Lit::eq(x0.clone())) {
                Some(i) => i,
                None => continue,
            };
            let q = lits[li].poly().clone();
            let kx = q.terms().iter().map(|(m, _)| m.factors().iter().filter(|(a, _)| *a == ix).map(|(_, e)| *e).sum::<u32>()).max().unwrap_or(0);
            if kx > 0 {
                if kx > 2 || f_atoms_with_vars(&q).iter().any(|uu| uu.has_inv()) {
                    continue;
                }
                let m = x0.pow(kx);
                let q2 = cancel_inv(&q.mul(&m), 0);
                if q2.has_inv() {
                    continue;
                }
                // m·q − q2 は (x inv x − 1) の倍数
                let rest = q.mul(&m).sub(&q2);
                let rr2 = match crate::polyutil::exact_div(&rest, &one_x) {
                    Some(r) => r,
                    None => continue,
                };
                cur = self.e.k.lincomb(b, 1, vec![(m, cur, li), (rr2.neg().scale(&(Q::one() / &kax)), ax_x, iax)])?;
            }
            if pm1.has_inv() && kx == 0 && self.e.clause(cur).lits().iter().any(|l| l.poly().has_inv()) {
                continue;
            }
            self.bump("recip_subst");
            let cur = self.tidy_clause(st, cur)?;
            self.e.add_fact(st, cur)?;
        }
        Ok(())
    }

    /// 条件の外せる点での例化: 2 つ以上のリテラルをもつ事実で、1 つの変数 w だけを含む等式リテラル p(w) = 0 について、
    /// この枝の閉じた ≠ の事実 u ≠ 0 に現れる定数 K で p(K) が u の定数倍になるなら、w := K と例化する
    /// （追加時に既知の ≠ の事実でそのリテラルが外れる）。例: 「f(x) = 0 ∨ f(y) = y + f(x) − x」と f(a) ≠ 0 から f(y) = y + f(a) − a。
    pub(crate) fn discharge_conditions(&mut self, st: &mut BState) -> Res<()> {
        if st.nes.is_empty() {
            return Ok(());
        }
        let nes: Vec<Poly> = st.nes.iter().map(|&n| self.e.poly0(n)).collect();
        let mut ks: BTreeSet<u32> = BTreeSet::new();
        for u in &nes {
            ks.extend(u.consts());
        }
        let cands: Vec<Fact> = st
            .others
            .iter()
            .copied()
            .filter(|&f| {
                let c = self.e.clause(f);
                c.nvars() >= 1 && c.lits().len() >= 2
            })
            .collect();
        let mut made = 0;
        for f in cands {
            if made >= self.scaled(12) || self.closed(st) {
                return Ok(());
            }
            if !st.others.contains(&f) {
                continue;
            }
            let c = self.e.clause(f).clone();
            for l in c.lits() {
                if l.rel() != Rel::Eq {
                    continue;
                }
                let vs = l.poly().vars();
                if vs.len() != 1 {
                    continue;
                }
                let w = *vs.iter().next().unwrap();
                for &k in ks.iter().take(4) {
                    let mut sub: Vec<Poly> = Vec::new();
                    let mut nxt = 0u32;
                    for i in 0..c.nvars() {
                        if i == w {
                            sub.push(Poly::cnst(k));
                        } else {
                            sub.push(Poly::var(nxt));
                            nxt += 1;
                        }
                    }
                    let pk = l.poly().subst_vars(&sub);
                    if !nes.iter().any(|u| scale_ratio(u, &pk).is_some()) {
                        continue;
                    }
                    let key = format!("dc|{:?}|{}|{}", f, w, k);
                    if !st.tried.insert(key) {
                        continue;
                    }
                    let inst = self.e.k.instantiate(st.b, f, sub, nxt)?;
                    self.bump("discharge_cond");
                    self.e.add_fact(st, inst)?;
                    made += 1;
                    if self.closed(st) {
                        return Ok(());
                    }
                }
            }
        }
        Ok(())
    }

    /// 条件つきの事実を整える: 1 つの変数しか使わない 2 変数の節は 1 変数にし（Instantiate）、
    /// 等式リテラルの単項式の因子を零積の規則で分ける（f(x)² = 0 → f(x) = 0、x·f(x) = 0 → x = 0 ∨ f(x) = 0）。
    pub(crate) fn tidy_clause(&mut self, st: &mut BState, f: Fact) -> Res<Fact> {
        let b = st.b;
        let mut cur = f;
        let c = self.e.clause(cur).clone();
        if c.nvars() == 2 {
            let vs: BTreeSet<u32> = c.lits().iter().flat_map(|l| l.poly().vars()).collect();
            if !vs.contains(&1) {
                cur = self.e.k.instantiate(b, cur, vec![x(), Poly::zero()], 1)?;
            } else if !vs.contains(&0) {
                cur = self.e.k.instantiate(b, cur, vec![Poly::zero(), x()], 1)?;
            }
        }
        for _ in 0..4 {
            let c = self.e.clause(cur).clone();
            let mut changed = false;
            for (i, l) in c.lits().iter().enumerate() {
                if l.rel() != Rel::Eq {
                    continue;
                }
                let content = monomial_content(l.poly());
                if content.is_one() {
                    continue;
                }
                // 1 つの原子の定数倍（例: x = 0）は分解しても同じ節なので分解しない
                let deg: u32 = content.factors().iter().map(|(_, e)| *e).sum();
                if l.poly().terms().len() == 1 && deg == 1 {
                    continue;
                }
                let mut fs: Vec<Poly> = Vec::new();
                for (a, e) in content.factors() {
                    for _ in 0..*e {
                        fs.push(Poly::from_atom(a.clone()));
                    }
                }
                fs.push(div_mono(l.poly(), &content));
                if let Ok(z) = self.e.k.zero_product(b, cur, i, fs) {
                    cur = z;
                    changed = true;
                    break;
                }
            }
            if !changed {
                break;
            }
        }
        Ok(cur)
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
        // f の外の部分を 0 にする代入: v を引数に含む f の原子を除いた項を v の多項式 c₁·v + c₀ とみて、
        // c₀ が c₁ で割り切れるなら v := −c₀/c₁（例: f(x)² + y·f(x) = f(x)(y + f(x)) で y := −f(x)）
        for v in 0..2u32 {
            let av = Atom::Var(v);
            let mut rest = Poly::zero();
            for (m, c) in p.terms() {
                if m.factors().iter().any(|(b, _)| *b != av && Poly::from_atom(b.clone()).vars().contains(&v)) {
                    continue;
                }
                rest = rest.add(&Poly::mono(m.clone(), c.clone()));
            }
            let cs = coeffs_in(&rest, &av);
            if cs.keys().max() != Some(&1) {
                continue;
            }
            let c1 = cs[&1].clone();
            let c0 = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
            if c0.is_zero() || c1.as_const().is_some() {
                continue; // 係数が定数の場合は既存の打ち消しの代入で扱う
            }
            if let Some(r) = crate::polyutil::exact_div(&c0, &c1) {
                if !r.vars().contains(&v) {
                    let mut s = vec![x(), y()];
                    s[v as usize] = r.neg();
                    push(s);
                }
            }
        }
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
