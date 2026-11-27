//! 解の形の確定: f(x) = g(x) の規則、パラメータの決定、区分的な葉、解の候補の列挙（docs/TACTICS.md）
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
    /// 規則 f(x) → g(x)（g は x の f を含まない）
    pub(crate) fn solution_rule(&self, st: &BState) -> Option<RwRule> {
        let fx = Atom::F(std::rc::Rc::new(x()));
        let mut best: Option<(usize, usize, RwRule)> = None;
        for (idx, r) in st.rules.iter().enumerate() {
            if r.nvars != 1 || r.lhs != fx {
                continue;
            }
            let mut bad = false;
            let mut params = 0;
            r.rhs.visit_atoms(&mut |a| {
                if matches!(a, Atom::F(_) | Atom::Inv(_)) {
                    if a.has_var() {
                        bad = true;
                    } else {
                        params += 1;
                    }
                }
            });
            if bad {
                continue;
            }
            // パラメータが少ないものを優先、同数なら新しいもの
            if best.as_ref().map_or(true, |(p, i, _)| params < *p || (params == *p && idx > *i)) {
                best = Some((params, idx, r.clone()));
            }
        }
        best.map(|(_, _, r)| r)
    }

    pub(crate) fn finalize(&mut self, st: &mut BState, rule: RwRule, depth: u32) -> Res<Fin> {
        self.bump("finalize");
        for _iter in 0..6 {
            self.e.check_time()?;
            if self.closed(st) {
                return Ok(Fin::Done);
            }
            let rule = match self.solution_rule(st) {
                Some(r) => r,
                None => return Ok(Fin::Continue),
            };
            // 解の形の規則を、他の規則で書き換え直す（パラメータ f(0) → 0 などを反映）
            {
                let rf = rule.fact;
                let saved_rules = st.rules.clone();
                let saved_cache = std::mem::take(&mut st.cache);
                st.rules.retain(|r| r.fact != rf);
                let rf2 = self.e.rewrite_clause(st, rf);
                st.rules = saved_rules;
                st.cache = saved_cache;
                let rf2 = rf2?;
                if rf2 != rf && self.e.clause(rf2) != self.e.clause(rf) {
                    st.units.retain(|u| *u != rf);
                    st.rules.retain(|r| r.fact != rf);
                    st.cache.clear();
                    self.e.add_fact(st, rf2)?;
                    if self.closed(st) {
                        return Ok(Fin::Done);
                    }
                    continue;
                }
            }
            // パラメータ f(c) の点で規則を例化した f(c) = g(c) を加える（パラメータの自己整合条件）
            let mut params: Vec<Poly> = Vec::new();
            for (m, _) in rule.rhs.terms() {
                for (a, _) in m.factors() {
                    if let Atom::F(c) = a {
                        if !c.has_var() && !params.contains(c) {
                            params.push((**c).clone());
                        }
                    }
                }
            }
            for c in params {
                let key = format!("selfc|{:?}|{:?}", rule.fact, c);
                if !st.tried.insert(key) {
                    continue;
                }
                let f0 = self.e.k.instantiate(st.b, rule.fact, vec![c], 0)?;
                self.e.add_fact(st, f0)?;
                if self.closed(st) {
                    return Ok(Fin::Done);
                }
            }
            let rule = match self.solution_rule(st) {
                Some(r) => r,
                None => return Ok(Fin::Continue),
            };
            // 公理を書き換えて x, y の恒等式にする
            let ax = self.e.k.axiom();
            let inst = self.e.k.instantiate(st.b, ax, vec![x(), y()], 2)?;
            let ef = self.e.rewrite_clause(st, inst)?;
            let c = self.e.clause(ef).clone();
            if std::env::var("FE_DEBUG").is_ok() {
                eprintln!("finalize b{}: rule {} -> {} ; E = {}", st.b.0, rule.lhs, rule.rhs, c);
                for r in &st.rules {
                    if r.nvars <= 1 { eprintln!("    rule {} -> {}", r.lhs, r.rhs); }
                }
                for (_, m, r) in &st.pow_rules {
                    eprintln!("    mono {} -> {}", m, r);
                }
                for u in &st.units {
                    if self.e.nvars(*u) == 0 { eprintln!("    closed {}", self.e.clause(*u)); }
                }
            }
            if c.is_false() {
                return Ok(Fin::Done);
            }
            if c.is_tautology() || c.lits().is_empty() || c.lits()[0].poly().is_zero() {
                // 解の形が方程式を満たす: 検証して確定
                let g = rule.rhs.clone();
                match self.e.k.verify_solution(&g) {
                    Ok(fam) => {
                        self.e.k.mark_solution(st.b, rule.fact, fam)?;
                        self.bump("solved_leaf");
                        return Ok(Fin::Done);
                    }
                    Err(_) => return Ok(Fin::Continue),
                }
            }
            if c.lits().len() != 1 || c.lits()[0].rel() != Rel::Eq {
                return Ok(Fin::Continue);
            }
            let e = c.lits()[0].poly().clone();
            if !f_atoms_with_vars(&e).is_empty() {
                return Ok(Fin::Continue);
            }
            // 係数を取り出す
            let ef = self.e.canon_vars(st, ef)?;
            let nv = self.e.nvars(ef);
            let e = self.e.poly0(ef);
            let coeffs = coeffs_xy(&e);
            let dx = coeffs.keys().map(|k| k.0).max().unwrap_or(0);
            let dy = coeffs.keys().map(|k| k.1).max().unwrap_or(0);
            let vx = vander(dx);
            let vy = vander(dy);
            let ix = invert(&vx).ok_or("vandermonde")?;
            let iy = invert(&vy).ok_or("vandermonde")?;
            // 格子点での例
            let mut insts: BTreeMap<(u32, u32), (Fact, Q)> = BTreeMap::new();
            for i in 0..=dx {
                for j in 0..=dy {
                    let mut s = vec![Poly::int(i as i64)];
                    if nv == 2 {
                        s.push(Poly::int(j as i64));
                    }
                    if s.len() != nv as usize {
                        s.truncate(nv as usize);
                    }
                    let val = e.subst_vars(&s);
                    if val.is_zero() {
                        continue;
                    }
                    let f = self.e.k.instantiate(st.b, ef, s, 0)?;
                    if self.e.clause(f).is_false() {
                        // この点で矛盾（0 でない定数 = 0）: 枝は閉じた
                        return Ok(Fin::Done);
                    }
                    let lc = val.leading_coeff().unwrap().clone();
                    insts.insert((i, j), (f, lc));
                }
            }
            let mut newfacts = Vec::new();
            for ((a, b), cp) in &coeffs {
                if cp.as_const().map_or(false, |q| q.is_zero()) {
                    continue;
                }
                let mut items: Vec<(Poly, Fact, usize)> = Vec::new();
                for ((i, j), (f, lc)) in &insts {
                    let w = &ix[*a as usize][*i as usize] * &iy[*b as usize][*j as usize];
                    if w.is_zero() {
                        continue;
                    }
                    items.push((Poly::constant(w * lc), *f, 0));
                }
                if items.is_empty() {
                    continue;
                }
                let cf = self.e.k.lincomb(st.b, 0, items)?;
                debug_assert!(self.e.poly0(cf).monic() == cp.monic() || self.e.clause(cf).is_false());
                newfacts.push(cf);
            }
            let mut progress = false;
            for f in newfacts {
                match self.e.add_fact(st, f)? {
                    Added::New(_) | Added::Contradiction(_) => progress = true,
                    _ => {}
                }
                if self.closed(st) {
                    return Ok(Fin::Done);
                }
            }
            if depth < self.max_depth && self.try_split(st, depth)? {
                return Ok(Fin::Done);
            }
            if !progress {
                return Ok(Fin::Continue);
            }
        }
        Ok(Fin::Continue)
    }

    // ------------------------------------------------------------------
    // 場合分け

    /// 正の側・0・負の側のそれぞれで f の式を与える事実がそろっていれば、区分的な解として葉を確定する
    pub(crate) fn try_piecewise_leaf(&mut self, st: &mut BState) -> Res<bool> {
        let fx = Atom::F(std::rc::Rc::new(x()));
        let zero = Q::zero();
        // 区間 (lo, hi) または点で f(x) = h(x) を与える事実と h を探す
        let mut find = |this: &Self, lo: Option<Q>, hi: Option<Q>, point: bool| -> Option<(Fact, Poly)> {
            let mut cands: Vec<Fact> = st.units.iter().chain(st.others.iter()).copied().collect();
            cands.sort();
            for f in cands {
                let c = this.e.clause(f);
                if c.nvars() > 1 {
                    continue;
                }
                let mut h: Option<Poly> = None;
                let mut ok = true;
                for l in c.lits() {
                    if l.poly().has_f() {
                        if h.is_some() || l.rel() != Rel::Eq {
                            ok = false;
                            break;
                        }
                        let t = if c.nvars() == 1 { x() } else if point { Poly::constant(lo.clone().unwrap()) } else { ok = false; break; };
                        let ta = Atom::F(std::rc::Rc::new(t.clone()));
                        let lam = match coeff_of_atom(l.poly(), &ta) {
                            Some(v) => v,
                            None => {
                                ok = false;
                                break;
                            }
                        };
                        let hh = Poly::from_atom(ta).sub(&l.poly().scale(&(Q::one() / lam)));
                        if hh.has_f() || hh.has_inv() || !hh.consts().is_empty() || hh.vars().iter().any(|&v| v != 0) {
                            ok = false;
                            break;
                        }
                        h = Some(hh);
                    } else if !fe_kernel::piecewise::literal_false_on(l.poly(), l.rel(), &lo, &hi, point) {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    if let Some(hh) = h {
                        return Some((f, hh));
                    }
                }
            }
            None
        };
        let _ = &fx;
        let neg = find(self, None, Some(zero.clone()), false);
        let pt = find(self, Some(zero.clone()), Some(zero.clone()), true);
        let pos = find(self, Some(zero.clone()), None, false);
        let (neg, pt, pos) = match (neg, pt, pos) {
            (Some(a), Some(b), Some(c)) => (a, b, c),
            _ => return Ok(false),
        };
        let pv = pt.1.subst_vars(&[Poly::zero()]);
        if neg.1 == pos.1 && pv == pos.1.subst_vars(&[Poly::zero()]) {
            return Ok(false); // 多項式の解（通常の仕上げで扱う）
        }
        let fam = match self.e.k.verify_piecewise(vec![zero], vec![neg.1.clone(), pv, pos.1.clone()]) {
            Ok(f) => f,
            Err(_) => return Ok(false),
        };
        self.e.k.mark_piecewise(st.b, vec![neg.0, pt.0, pos.0], fam)?;
        self.bump("piecewise_leaf");
        Ok(true)
    }

}

pub fn find_candidates(k: &Kernel) -> Vec<Family> {
    let mut out: Vec<Family> = Vec::new();
    // f(t) = a t^2 + b t + c（a, b, c は記号）を代入
    let (va, vb, vc) = (Poly::var(10), Poly::var(11), Poly::var(12));
    let (l, r) = k.equation();
    let tmpl = |t: &Poly| va.mul(&t.pow(2)).add(&vb.mul(t)).add(&vc);
    let apply = |p: &Poly| {
        p.transform(&mut |a| match a {
            Atom::F(arg) => tmpl(&arg),
            other => Poly::from_atom(other),
        })
    };
    let e = apply(l).sub(&apply(r));
    let eqs: Vec<Poly> = coeffs_xy(&e).into_values().collect();
    let mut sols: Vec<BTreeMap<u32, Q>> = Vec::new();
    solve_system(&eqs, &[10, 11, 12], BTreeMap::new(), &mut sols, 0);
    let params = [Atom::Const(1000), Atom::Const(1001), Atom::Const(1002)];
    for s in sols {
        // 自由な未知数はパラメータ
        let mut g = Poly::zero();
        for (i, (v, pw)) in [(10u32, 2u32), (11, 1), (12, 0)].iter().enumerate() {
            let coef = match s.get(v) {
                Some(q) => Poly::constant(q.clone()),
                None => Poly::from_atom(params[i].clone()),
            };
            g = g.add(&coef.mul(&x().pow(*pw)));
        }
        if let Ok(fam) = k.verify_solution(&g) {
            if !out.iter().any(|f| f.template() == fam.template()) {
                out.push(fam);
            }
        }
    }
    out
}


/// 区分的な候補（区切り点 0）: 各側の式と点の値を小さな集合から選び、検証核で検証する
pub fn find_pw_candidates(k: &Kernel) -> Vec<fe_kernel::PwFamily> {
    use fe_kernel::poly::{q, qf};
    let side: Vec<Poly> = vec![x(), x().neg(), Poly::zero(), Poly::one(), Poly::int(-1), x().scale(&q(2)), x().scale(&qf(1, 2)), x().scale(&q(-2))];
    let mut out: Vec<fe_kernel::PwFamily> = Vec::new();
    for gl in &side {
        for gr in &side {
            let mut points: Vec<Poly> = vec![gl.subst_vars(&[Poly::zero()]), gr.subst_vars(&[Poly::zero()]), Poly::zero(), Poly::one()];
            points.dedup();
            for v in points {
                // 区分なし（多項式）と同じものは除く
                if gl == gr && v == gl.subst_vars(&[Poly::zero()]) {
                    continue;
                }
                if let Ok(fam) = k.verify_piecewise(vec![Q::zero()], vec![gl.clone(), v.clone(), gr.clone()]) {
                    if !out.iter().any(|f| f.pieces() == fam.pieces()) {
                        out.push(fam);
                    }
                }
            }
        }
    }
    out
}


/// 任意の区間をもつ族の候補（病的な解の存在）: 0 を区切りに、片側を固定の式 g ∈ {x, −x, 0}、反対側を
/// 任意の値（制約なし・0 以上・0 以下・各点で 2 つの式の一方）とした族を検証核で確かめ、最初に通ったものを返す。
/// 効く類: 方程式の f の引数がいつも 0 以上（以下）になる型（f(x² + f(y²)) = x² + y²、f(f(x) + f(y)²) = f(x) + f(y)² など）、
/// f の値が 2 乗や t·f(t) でだけ現れる型（各点で ±x を選べる）。
pub fn find_arb_candidates(k: &Kernel) -> Option<fe_kernel::ArbFamily> {
    use fe_kernel::ArbPiece::{Choice, Fixed, Free, NonNeg, NonPos};
    let fixed: Vec<Poly> = vec![x(), x().neg(), Poly::zero()];
    let arb = |g: &Poly| -> Vec<fe_kernel::ArbPiece> {
        let mut v = vec![Free, NonNeg, NonPos];
        for (a, b) in [(x(), x().neg()), (Poly::zero(), x()), (Poly::zero(), x().neg())] {
            v.push(Choice(a, b));
        }
        let _ = g;
        v
    };
    for g in &fixed {
        for side in 0..2 {
            for pc in arb(g) {
                let pieces = if side == 0 {
                    vec![pc, Fixed(Poly::zero()), Fixed(g.clone())]
                } else {
                    vec![Fixed(g.clone()), Fixed(Poly::zero()), pc]
                };
                if let Ok(fam) = k.verify_arbitrary(vec![Q::zero()], pieces) {
                    return Some(fam);
                }
            }
        }
    }
    None
}

pub(crate) fn vander(d: u32) -> Vec<Vec<Q>> {
    (0..=d).map(|i| (0..=d).map(|a| Q::from_integer((i as i64).pow(a).into())).collect()).collect::<Vec<_>>()
}


/// 有理数解を、1 変数になった方程式の有理根で分岐しながら探す
pub(crate) fn solve_system(eqs: &[Poly], vars: &[u32], asg: BTreeMap<u32, Q>, out: &mut Vec<BTreeMap<u32, Q>>, depth: u32) {
    if depth > 8 || out.len() > 16 {
        return;
    }
    let sub: Vec<Poly> = (0..13).map(|i| match asg.get(&i) {
        Some(q) => Poly::constant(q.clone()),
        None => Poly::var(i),
    }).collect();
    let cur: Vec<Poly> = eqs.iter().map(|e| e.subst_vars(&sub)).filter(|e| !e.is_zero()).collect();
    if cur.iter().any(|e| e.as_const().map_or(false, |c| !c.is_zero())) {
        return;
    }
    if cur.is_empty() {
        out.push(asg);
        return;
    }
    // 1 変数の方程式を探す
    let mut best: Option<(u32, Poly)> = None;
    for e in &cur {
        let vs = e.vars();
        if vs.len() == 1 {
            let v = *vs.iter().next().unwrap();
            if best.as_ref().map_or(true, |(_, b)| e.total_degree() < b.total_degree()) {
                best = Some((v, e.clone()));
            }
        }
    }
    if let Some((v, e)) = best {
        let cs = coeffs_in(&e, &Atom::Var(v));
        let deg = *cs.keys().max().unwrap();
        let vec: Vec<Q> = (0..=deg).map(|d| cs.get(&d).and_then(|c| c.as_const()).unwrap_or_else(Q::zero)).collect();
        for root in rational_roots(&vec) {
            let mut a2 = asg.clone();
            a2.insert(v, root);
            solve_system(eqs, vars, a2, out, depth + 1);
        }
        return;
    }
    // 1 変数の式がない: 積の形 v·(…) = 0 などを 0 で分岐
    for &v in vars {
        if asg.contains_key(&v) {
            continue;
        }
        if cur.iter().any(|e| e.vars().contains(&v)) {
            let mut a2 = asg.clone();
            a2.insert(v, Q::zero());
            solve_system(eqs, vars, a2.clone(), out, depth + 1);
            for c in [Q::one(), -Q::one()] {
                let mut a3 = asg.clone();
                a3.insert(v, c);
                solve_system(eqs, vars, a3, out, depth + 1);
            }
            return;
        }
    }
}
