//! 消去と因数分解: 1 変数・2 変数の消去、右辺が同じ事実の比較、因数分解、点の条件の除去（docs/TACTICS.md）
#![allow(unused_imports)]

use crate::engine::{coeff_of_atom, replace_atom, Added, BState, Engine, Res, RwRule, TIMEOUT};
use crate::order::{atom_cmp, poly_size};
use crate::polyutil::*;
use fe_kernel::{AddFamily, AddKind, Atom, BranchId, Fact, Family, Kernel, Lit, Mono, Poly, Rel, Q};
use num_traits::{One, Signed, Zero};
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use super::util::*;
use super::{Fin, Searcher};

impl Searcher {
    pub(crate) fn eliminate(&mut self, st: &mut BState) -> Res<()> {
        let rows_in: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) <= 1).collect();
        if rows_in.len() < 2 {
            return Ok(());
        }
        type Row = (BTreeMap<Mono, Q>, Vec<(Q, Fact)>);
        let mut basis: Vec<(Mono, Row)> = Vec::new();
        let lead = |r: &BTreeMap<Mono, Q>| -> Option<Mono> { r.keys().max_by(|a, b| prio_cmp(a, b)).cloned() };
        let sub = |r: &mut Row, other: &Row, k: &Q| {
            for (m, c) in &other.0 {
                let e = r.0.entry(m.clone()).or_insert_with(Q::zero);
                *e -= c * k;
            }
            r.0.retain(|_, c| !c.is_zero());
            for (c, f) in &other.1 {
                r.1.push((-(c * k), *f));
            }
        };
        for f in &rows_in {
            let p = self.e.poly0(*f);
            let mut row: Row = (p.terms().iter().cloned().collect(), vec![(Q::one(), *f)]);
            // 既存の軸で簡約
            loop {
                let mut changed = false;
                for (pm, prow) in &basis {
                    if let Some(c) = row.0.get(pm).cloned() {
                        sub(&mut row, prow, &c);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            if row.0.is_empty() {
                continue;
            }
            let pm = lead(&row.0).unwrap();
            let c = row.0[&pm].clone();
            let inv = Q::one() / &c;
            for v in row.0.values_mut() {
                *v *= &inv;
            }
            for t in row.1.iter_mut() {
                t.0 *= &inv;
            }
            // 既存の行からこの軸を消す
            for (_, prow) in basis.iter_mut() {
                if let Some(c2) = prow.0.get(&pm).cloned() {
                    sub(prow, &row, &c2);
                }
            }
            basis.push((pm, row));
        }
        let known: BTreeSet<Poly> = rows_in.iter().map(|f| self.e.poly0(*f)).collect();
        let mut made = 0;
        let mut cands: Vec<(Mono, Row)> = basis.into_iter().filter(|(pm, _)| mclass(pm) <= 1).collect();
        cands.sort_by(|a, b| prio_cmp(&a.0, &b.0));
        for (_, (row, combo)) in cands {
            if made >= 12 {
                break;
            }
            let p = Poly::from_terms(row.into_iter().collect());
            if p.is_zero() || known.contains(&p.monic()) || combo.len() < 2 {
                continue;
            }
            // 係数の合計を項目にまとめる
            let mut agg: BTreeMap<Fact, Q> = BTreeMap::new();
            for (c, f) in combo {
                *agg.entry(f).or_insert_with(Q::zero) += c;
            }
            let items: Vec<(Poly, Fact, usize)> =
                agg.into_iter().filter(|(_, c)| !c.is_zero()).map(|(f, c)| (Poly::constant(c), f, 0)).collect();
            if items.is_empty() {
                continue;
            }
            self.bump("elim");
            let nf = self.e.k.lincomb(st.b, 1, items)?;
            if let Added::New(_) = self.e.add_fact(st, nf)? {
                made += 1;
            }
            if self.closed(st) {
                return Ok(());
            }
        }
        Ok(())
    }

    /// 右辺が同じ事実の比較: c·f(A₁) = R と c'·f(A₂) = R'（R/c = R'/c'）から f(A₁) − f(A₂) = 0 を作る
    pub(crate) fn same_rhs(&mut self, st: &mut BState) -> Res<()> {
        let mut by_rhs: BTreeMap<(u32, Poly), Vec<(Fact, Q, Atom)>> = BTreeMap::new();
        for &u in &st.units {
            let nv = self.e.nvars(u);
            if nv == 0 {
                continue;
            }
            let p = self.e.poly0(u);
            // 変数を含む f の原子がちょうど 1 つ、単独の項として現れる
            let mut lhs: Option<(Atom, Q)> = None;
            let mut count = 0;
            for (m, c) in p.terms() {
                if m.factors().iter().any(|(a, _)| matches!(a, Atom::F(_)) && a.has_var()) {
                    count += 1;
                    if m.factors().len() == 1 && m.factors()[0].1 == 1 {
                        lhs = Some((m.factors()[0].0.clone(), c.clone()));
                    }
                }
            }
            let (a, c) = match (lhs, count) {
                (Some(t), 1) => t,
                _ => continue,
            };
            let r = Poly::from_atom(a.clone()).sub(&p.scale(&(Q::one() / &c)));
            if r.is_zero() {
                continue;
            }
            by_rhs.entry((nv, r)).or_default().push((u, c, a));
        }
        let mut made = 0;
        for ((nv, _), group) in by_rhs {
            if group.len() < 2 {
                continue;
            }
            let (u1, c1, a1) = &group[0];
            for (u2, c2, a2) in &group[1..] {
                if a1 == a2 || made >= 4 {
                    continue;
                }
                let key = format!("srhs|{:?}|{:?}", u1, u2);
                if !st.tried.insert(key) {
                    continue;
                }
                let items = vec![(Poly::constant(Q::one() / c1), *u1, 0), (Poly::constant(-(Q::one() / c2)), *u2, 0)];
                let nf = self.e.k.lincomb(st.b, nv, items)?;
                self.bump("same_rhs");
                if let Added::New(_) = self.e.add_fact(st, nf)? {
                    made += 1;
                }
                if self.closed(st) {
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    /// 2 変数の単位等式どうしの消去: 大きな原子を共有する事実の差から、より小さな事実を作る
    pub(crate) fn eliminate2(&mut self, st: &mut BState) -> Res<()> {
        let rows_in: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 2).collect();
        if rows_in.len() < 2 {
            return Ok(());
        }
        type Row = (BTreeMap<Mono, Q>, Vec<(Q, Fact)>);
        // 消去の優先順位: 最大の原子が大きい単項式ほど先に消す
        let key = |m: &Mono| -> (u32, Option<Atom>, u32) {
            let mut best: Option<Atom> = None;
            let mut fcount = 0;
            for (a, e) in m.factors() {
                if matches!(a, Atom::F(_)) {
                    fcount += e;
                }
                if best.as_ref().map_or(true, |b| atom_cmp(a, b) == std::cmp::Ordering::Greater) {
                    best = Some(a.clone());
                }
            }
            (fcount, best, m.degree())
        };
        let cmpm = |a: &Mono, b: &Mono| -> std::cmp::Ordering {
            let (fa, aa, da) = key(a);
            let (fb, ab, db) = key(b);
            let c = match (&aa, &ab) {
                (Some(x), Some(y)) => atom_cmp(x, y),
                (Some(_), None) => std::cmp::Ordering::Greater,
                (None, Some(_)) => std::cmp::Ordering::Less,
                (None, None) => std::cmp::Ordering::Equal,
            };
            c.then_with(|| fa.cmp(&fb)).then_with(|| da.cmp(&db)).then_with(|| a.cmp(b))
        };
        let mut basis: Vec<(Mono, Row)> = Vec::new();
        let sub = |r: &mut Row, other: &Row, k: &Q| {
            for (m, c) in &other.0 {
                let e = r.0.entry(m.clone()).or_insert_with(Q::zero);
                *e -= c * k;
            }
            r.0.retain(|_, c| !c.is_zero());
            for (c, f) in &other.1 {
                r.1.push((-(c * k), *f));
            }
        };
        let mut outputs: Vec<Row> = Vec::new();
        for f in &rows_in {
            let p = self.e.poly0(*f);
            let mut row: Row = (p.terms().iter().cloned().collect(), vec![(Q::one(), *f)]);
            loop {
                let mut changed = false;
                for (pm, prow) in &basis {
                    if let Some(c) = row.0.get(pm).cloned() {
                        sub(&mut row, prow, &c);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }
            if row.0.is_empty() {
                continue;
            }
            if row.1.len() >= 2 {
                outputs.push(row.clone());
            }
            let pm = row.0.keys().max_by(|a, b| cmpm(a, b)).cloned().unwrap();
            let c = row.0[&pm].clone();
            let inv = Q::one() / &c;
            for v in row.0.values_mut() {
                *v *= &inv;
            }
            for t in row.1.iter_mut() {
                t.0 *= &inv;
            }
            basis.push((pm, row));
        }
        let mut made = 0;
        for (row, combo) in outputs {
            if made >= 8 || self.closed(st) {
                break;
            }
            let mut agg: BTreeMap<Fact, Q> = BTreeMap::new();
            for (c, f) in combo {
                *agg.entry(f).or_insert_with(Q::zero) += c;
            }
            let items: Vec<(Poly, Fact, usize)> =
                agg.into_iter().filter(|(_, c)| !c.is_zero()).map(|(f, c)| (Poly::constant(c), f, 0)).collect();
            if items.len() < 2 {
                continue;
            }
            let p = Poly::from_terms(row.into_iter().collect());
            if poly_size(&p) > 60 {
                continue;
            }
            self.bump("elim2");
            let nf = self.e.k.lincomb(st.b, 2, items)?;
            if let Added::New(_) = self.e.add_fact(st, nf)? {
                made += 1;
            }
        }
        Ok(())
    }

    /// 1 変数の事実の因数分解: x^k·Q(x) = 0 や f(x) の 2 次式
    pub(crate) fn zero_products(&mut self, st: &mut BState) -> Res<()> {
        let ones: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 1).collect();
        for f in ones {
            if self.closed(st) {
                return Ok(());
            }
            let p = self.e.poly0(f);
            let key = format!("zp|{:?}", f);
            if st.tried.contains(&key) {
                continue;
            }
            st.tried.insert(key);
            let content = monomial_content(&p);
            let mut factors: Option<Vec<Poly>> = None;
            if !content.is_one() {
                let rest = div_mono(&p, &content);
                let mut fs: Vec<Poly> = Vec::new();
                for (a, e) in content.factors() {
                    for _ in 0..*e {
                        fs.push(Poly::from_atom(a.clone()));
                    }
                }
                fs.push(rest);
                factors = Some(fs);
            } else {
                let fx = Atom::F(std::rc::Rc::new(x()));
                let cs = coeffs_in(&p, &fx);
                if cs.keys().max() == Some(&2) && cs.values().all(|c| f_atoms_with_vars(c).is_empty()) {
                    if let Some(c2) = cs.get(&2).and_then(|c| c.as_const()) {
                        let c1 = cs.get(&1).cloned().unwrap_or_else(Poly::zero);
                        let c0 = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
                        let disc = c1.mul(&c1).sub(&c0.scale(&(Q::from_integer(4.into()) * &c2)));
                        if let Some(r) = poly_sqrt(&disc) {
                            let two = Q::from_integer(2.into()) * &c2;
                            let ap = Poly::from_atom(fx);
                            let r1 = c1.neg().add(&r).scale(&(Q::one() / &two));
                            let r2 = c1.neg().sub(&r).scale(&(Q::one() / &two));
                            factors = Some(vec![ap.sub(&r1).scale(&c2), ap.sub(&r2)]);
                        }
                    }
                }
            }
            if let Some(fs) = factors {
                if let Ok(z) = self.e.k.zero_product(st.b, f, 0, fs) {
                    self.bump("zero_product");
                    self.e.add_fact(st, z)?;
                }
            }
        }
        Ok(())
    }

    /// 2 次以上の因子で実数解をもたないもの（平方完成で正）を、矛盾として節から取り除く
    pub(crate) fn drop_rootless(&mut self, st: &mut BState, f: Fact) -> Res<Fact> {
        let mut cur = f;
        loop {
            let c = self.e.clause(cur).clone();
            let mut done = true;
            for (i, l) in c.lits().iter().enumerate() {
                if l.rel() != Rel::Eq {
                    continue;
                }
                if let Some(pos) = self.prove_positive(st, l.poly())? {
                    // pos: q > 0 （q は l の多項式の正の定数倍） → q ≠ 0 と導出
                    let ne = self.e.k.strict_ne(st.b, pos, 0)?;
                    cur = self.e.k.resolve(st.b, cur, i, ne, 0)?;
                    done = false;
                    break;
                }
            }
            if done {
                return Ok(cur);
            }
        }
    }

    /// 閉じた u ≠ 0 の事実から「u² > 0」を作る（三分律 u > 0 ∨ u = 0 ∨ −u > 0、導出原理、不等式の積 2 回）。作ったものは枝で使い回す
    pub(crate) fn square_positive(&mut self, st: &mut BState, u: &Poly) -> Res<Option<Fact>> {
        if let Some((_, f)) = st.pos_sq.iter().find(|(v, _)| v == u) {
            return Ok(Some(*f));
        }
        let ne = match st.nes.iter().copied().find(|&n| self.e.poly0(n) == *u || self.e.poly0(n) == u.neg()) {
            Some(n) => n,
            None => return Ok(None),
        };
        let b = st.b;
        let tri = self.e.k.trichotomy(b, 0, u.clone())?;
        let ieq = match self.e.clause(tri).lits().iter().position(|l| *l == Lit::eq(u.clone())) {
            Some(i) => i,
            None => return Ok(None),
        };
        let c1 = self.e.k.resolve(b, tri, ieq, ne, 0)?;
        let lits = self.e.clause(c1).lits().to_vec();
        if lits.len() != 2 {
            return Ok(None);
        }
        let c2 = self.e.k.mul_ineq(b, c1, 0, c1, 0)?;
        // c2 は「u² > 0 ∨ （もう一方）」。もう一方のリテラルどうしを掛けて u² > 0 だけにする
        let other = lits[1].clone();
        let io = match self.e.clause(c2).lits().iter().position(|l| *l == other) {
            Some(i) => i,
            None => return Ok(None),
        };
        let c3 = self.e.k.mul_ineq(b, c2, io, c2, io)?;
        let cl = self.e.clause(c3).clone();
        if cl.lits().len() != 1 || cl.lits()[0].rel() != Rel::Gt || scale_ratio(cl.lits()[0].poly(), &u.mul(u)).is_none() {
            return Ok(None);
        }
        self.bump("square_positive");
        st.pos_sq.push((u.clone(), c3));
        Ok(Some(c3))
    }

    /// 平方和の判定: q（変数を含んでよい）が「正の係数 × 平方」の和で、厳密に正の項（正の定数、または u ≠ 0 のわかる閉じた u の
    /// u²）を少なくとも 1 つ含むなら「q > 0」を作る（PosComb）。−q がそうなら「−q > 0」。
    pub(crate) fn prove_positive_sos(&mut self, st: &mut BState, q: &Poly) -> Res<Option<Fact>> {
        for sgn in [Q::one(), -Q::one()] {
            let qs = q.scale(&sgn);
            let mut ineqs: Vec<(Q, Fact, usize)> = Vec::new();
            let mut squares: Vec<(Q, Poly)> = Vec::new();
            let mut eqs: Vec<(Poly, Fact, usize)> = Vec::new();
            let mut constant = Q::zero();
            let mut ok = true;
            let qnv = qs.vars().iter().max().map_or(0, |m| m + 1);
            let is_square = |m: &fe_kernel::Mono| m.factors().iter().all(|(_, e)| e % 2 == 0);
            for (m, c) in qs.terms() {
                if !c.is_positive() || !is_square(m) {
                    // 2 項の単位等式 α·m + β·s = 0（s は平方の単項式、−cβ/α > 0）で c·m を平方に置き換える
                    let mut replaced = false;
                    for &u in &st.units {
                        if self.e.nvars(u) > qnv {
                            continue;
                        }
                        let pu = self.e.poly0(u);
                        if pu.terms().len() != 2 {
                            continue;
                        }
                        let (alpha, (sm, beta)) = match (pu.terms().iter().find(|(mm, _)| mm == m), pu.terms().iter().find(|(mm, _)| mm != m)) {
                            (Some((_, a)), Some((sm, b))) => (a.clone(), (sm.clone(), b.clone())),
                            _ => continue,
                        };
                        if !is_square(&sm) || sm.is_one() {
                            continue;
                        }
                        let d = -(c * &beta) / &alpha;
                        if !d.is_positive() {
                            continue;
                        }
                        let mut base = Poly::one();
                        for (a, e) in sm.factors() {
                            base = base.mul(&Poly::from_atom(a.clone()).pow(e / 2));
                        }
                        eqs.push((Poly::constant(c / &alpha), u, 0));
                        squares.push((d, base));
                        replaced = true;
                        break;
                    }
                    if replaced {
                        continue;
                    }
                    ok = false;
                    break;
                }
                if m.is_one() {
                    constant = c.clone();
                    continue;
                }
                let mut base = Poly::one();
                for (a, e) in m.factors() {
                    base = base.mul(&Poly::from_atom(a.clone()).pow(e / 2));
                }
                if !base.has_var() {
                    if let Some(f) = self.square_positive(st, &base)? {
                        let lp = self.e.clause(f).lits()[0].poly().clone();
                        if let Some(k) = scale_ratio(&lp, &base.mul(&base)) {
                            // lp = k·base²（k > 0）なので、係数 c/k を掛ける
                            ineqs.push((c / &k, f, 0));
                            continue;
                        }
                    }
                }
                squares.push((c.clone(), base));
            }
            if !ok || (ineqs.is_empty() && !constant.is_positive()) {
                continue;
            }
            let f = self.e.k.pos_comb(st.b, qnv, ineqs, eqs, squares, constant, true)?;
            self.bump("sos_positive");
            return Ok(Some(f));
        }
        Ok(None)
    }

    /// 1 変数（閉じた原子 1 つ）の 2 次式 q が常に正（または負）なら、事実「±q > 0」を作る
    pub(crate) fn prove_positive(&mut self, st: &mut BState, q: &Poly) -> Res<Option<Fact>> {
        if let Some(f) = self.prove_positive_sos(st, q)? {
            return Ok(Some(f));
        }
        let atoms = q.top_atoms();
        if atoms.len() != 1 || q.has_var() {
            return Ok(None);
        }
        let a = atoms.into_iter().next().unwrap();
        let cs = coeffs_in(q, &a);
        if cs.keys().max() != Some(&2) || cs.values().any(|c| c.as_const().is_none()) {
            return Ok(None);
        }
        let get = |e: u32| cs.get(&e).and_then(|c| c.as_const()).unwrap_or_else(Q::zero);
        let (a2, a1, a0) = (get(2), get(1), get(0));
        let disc = &a1 * &a1 - Q::from_integer(4.into()) * &a2 * &a0;
        if disc >= Q::zero() {
            return Ok(None);
        }
        // s·q = |a2|(t + a1/(2a2))² + (正の定数)
        let s = if a2 > Q::zero() { Q::one() } else { -Q::one() };
        let aa = &a2 * &s;
        let h = &a1 / (Q::from_integer(2.into()) * &a2);
        let k = (&a0 * &s) - &aa * &h * &h;
        let ap = Poly::from_atom(a);
        let fact = self.e.k.pos_comb(st.b, 0, vec![], vec![], vec![(aa, ap.add(&Poly::constant(h)))], k, true)?;
        Ok(Some(fact))
    }

    pub(crate) fn closed_factors(&self, p: &Poly) -> Option<Vec<Poly>> {
        // 単項式の共通因子
        let content = monomial_content(p);
        if !content.is_one() {
            let rest = div_mono(p, &content);
            let mut fs: Vec<Poly> = Vec::new();
            for (a, e) in content.factors() {
                for _ in 0..*e {
                    fs.push(Poly::from_atom(a.clone()));
                }
            }
            if rest.as_const().is_none() {
                fs.push(rest);
            } else {
                let c = rest.as_const().unwrap();
                fs[0] = fs[0].scale(&c);
            }
            return Some(fs);
        }
        let atoms = p.top_atoms();
        if atoms.len() == 1 {
            let a = atoms.into_iter().next().unwrap();
            return factor_univariate(p, &a);
        }
        // 最大の原子について 2 次で、判別式が平方
        let a = atoms.into_iter().max_by(|a, b| atom_cmp(a, b))?;
        let cs = coeffs_in(p, &a);
        if cs.keys().max() == Some(&2) {
            let c2 = cs.get(&2)?.as_const()?;
            let c1 = cs.get(&1).cloned().unwrap_or_else(Poly::zero);
            let c0 = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
            let disc = c1.mul(&c1).sub(&c0.scale(&(Q::from_integer(4.into()) * &c2)));
            let r = poly_sqrt(&disc)?;
            let two = Q::from_integer(2.into()) * &c2;
            let ap = Poly::from_atom(a);
            let r1 = c1.neg().add(&r).scale(&(Q::one() / &two));
            let r2 = c1.neg().sub(&r).scale(&(Q::one() / &two));
            return Some(vec![ap.sub(&r1).scale(&c2), ap.sub(&r2)]);
        }
        None
    }

    /// 「x − r = 0 ∨ Q(x) = 0」で Q(r) = 0 が示せるとき、∀x. Q(x) = 0 を導く
    pub(crate) fn remove_point_conditions(&mut self, st: &mut BState) -> Res<()> {
        let others: Vec<Fact> = st.others.clone();
        for f in others {
            if self.closed(st) {
                return Ok(());
            }
            let c = self.e.clause(f).clone();
            if c.nvars() != 1 || c.lits().len() != 2 {
                continue;
            }
            if c.lits().iter().any(|l| l.rel() != Rel::Eq) {
                continue;
            }
            // 条件リテラル x − r
            let (ci, qi) = if is_point_cond(c.lits()[0].poly()).is_some() {
                (0, 1)
            } else if is_point_cond(c.lits()[1].poly()).is_some() {
                (1, 0)
            } else {
                continue;
            };
            let r = is_point_cond(c.lits()[ci].poly()).unwrap();
            let qpoly = c.lits()[qi].poly().clone();
            let key = format!("pc|{:?}", f);
            if st.tried.contains(&key) {
                continue;
            }
            st.tried.insert(key);
            if let Some(nf) = self.lift_point_condition(st, f, ci, qi, &r, &qpoly)? {
                self.bump("point_condition");
                st.others.retain(|g| *g != f);
                self.e.add_fact(st, nf)?;
            }
        }
        Ok(())
    }

    pub(crate) fn lift_point_condition(&mut self, st: &mut BState, f: Fact, ci: usize, _qi: usize, r: &Q, qp: &Poly) -> Res<Option<Fact>> {
        let b = st.b;
        let rp = Poly::constant(r.clone());
        // Q(r) を正規化して 0 になるか
        let qr = qp.subst_vars(&[rp.clone()]);
        let (qr2, items_r) = self.e.rw_poly(st, &qr, 0)?;
        if !qr2.is_zero() {
            return Ok(None);
        }
        // Q の f(t(x)) の原子は t が f を含まないものに限る
        let mut atoms: Vec<Atom> = qp.top_atoms().into_iter().filter(|a| matches!(a, Atom::F(_)) && a.has_var()).collect();
        atoms.sort_by(|a, b| atom_cmp(b, a));
        for a in &atoms {
            if let Atom::F(t) = a {
                if t.has_f() {
                    return Ok(None);
                }
            }
        }
        let cond = Poly::var(0).sub(&rp);
        let em = self.e.k.eq_or_ne(b, 1, cond.clone())?;
        let ei = self.e.clause(em).lits().iter().position(|l| l.rel() == Rel::Eq).unwrap();
        // em の等式リテラルの保存形 = λ (x − r)
        let lam_em = self.e.clause(em).lits()[ei].poly().terms().iter().find(|(m, _)| !m.is_one()).map(|(_, c)| c.clone()).unwrap();
        let mut items: Vec<(Poly, Fact, usize)> = Vec::new();
        // Q(r) = Σ items_r
        items.extend(items_r);
        let mut cur = qp.clone();
        for a in &atoms {
            if let Atom::F(t) = a {
                let tr = t.subst_vars(&[rp.clone()]);
                let m = div_linear(&t.sub(&tr), 0, &rp).ok_or("割り切れない")?;
                // f(tr + m·(x − r)) − f(tr) = 0 ∨ x − r ≠ 0
                let g = self.e.k.congruence(b, 1, tr.clone(), vec![(m.scale(&(Q::one() / &lam_em)), em, ei)])?;
                let gi = self.e.clause(g).lits().iter().position(|l| l.rel() == Rel::Eq).unwrap();
                let mu = coeff_of_atom(self.e.clause(g).lits()[gi].poly(), a).ok_or("原子がない")?;
                let fr = Poly::f(tr);
                let (cur2, qq) = replace_atom(&cur, a, &fr);
                items.push((qq.scale(&(Q::one() / mu)), g, gi));
                cur = cur2;
            }
        }
        // cur(x) − cur(r) = B·(x − r)
        let cr = cur.subst_vars(&[rp.clone()]);
        let bq = div_linear(&cur.sub(&cr), 0, &rp).ok_or("割り切れない")?;
        if !bq.is_zero() {
            items.push((bq.scale(&(Q::one() / &lam_em)), em, ei));
        }
        // Σ = Q(r) + (Q(x) − Q(r)) = Q(x)。ただし Q(r) の項目は正規化の差分なので、cr = Q(r) に注意
        let h = self.e.k.lincomb(b, 1, items)?;
        // h: Q(x) = 0 ∨ x − r ≠ 0
        let hc = self.e.clause(h).clone();
        let want_ne = Lit::ne(cond);
        let hi = match hc.lits().iter().position(|l| *l == want_ne) {
            Some(i) => i,
            None => return Ok(None),
        };
        let res = self.e.k.resolve(b, f, ci, h, hi)?;
        Ok(Some(res))
    }
    pub(crate) fn drop_ffree_components(&mut self, st: &mut BState, f: Fact) -> Res<Fact> {
        self.e.drop_ffree_components(st, f)
    }

    // ------------------------------------------------------------------
    // 解の形が決まったときの仕上げ

}
