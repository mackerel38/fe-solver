//! 探索戦略。すべての事実は Engine 経由で検証核の推論規則から得る。

use crate::engine::{coeff_of_atom, replace_atom, Added, BState, Engine, Res, RwRule, TIMEOUT};
use crate::order::{atom_cmp, poly_size};
use crate::polyutil::*;
use fe_kernel::{AddFamily, AddKind, Atom, BranchId, Fact, Family, Kernel, Lit, Mono, Poly, Rel, Q};
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

pub struct Searcher {
    pub e: Engine,
    /// 帰着（補題として別に解く）の入れ子の深さ
    pub reduce_depth: u32,
    /// 探索幅（1.0 が標準）。代入数・生成元の数などをこの倍率で増減する
    pub width: f64,
    pub round_budget: usize,
    pub retry: Vec<(BState, u32)>,
    pub open: Vec<(BranchId, String)>,
    pub max_depth: u32,
    pub stats: BTreeMap<String, u64>,
    /// 検証済みの加法的な族（任意の加法的関数 A について A + f(0) または A が解）。None = 未計算
    add_fam: Option<Option<AddFamily>>,
}

fn x() -> Poly {
    Poly::var(0)
}
fn y() -> Poly {
    Poly::var(1)
}

/// 単項式の分類（1 変数の事実で f(x) = g(x) を得るための消去順）
fn mclass(m: &Mono) -> u8 {
    let fx = Atom::F(std::rc::Rc::new(x()));
    let mut cls = 0u8;
    for (a, e) in m.factors() {
        if !a.has_var() {
            continue;
        }
        match a {
            Atom::Var(_) => {}
            _ if *a == fx => cls = cls.max(if *e >= 2 { 2 } else { 1 }),
            _ => return 3,
        }
    }
    cls
}

fn mono_prio(m: &Mono) -> (u8, Option<Atom>, u32) {
    let mut best: Option<Atom> = None;
    for (a, _) in m.factors() {
        if best.as_ref().map_or(true, |b| atom_cmp(a, b) == std::cmp::Ordering::Greater) {
            best = Some(a.clone());
        }
    }
    (mclass(m), best, m.degree())
}

fn prio_cmp(a: &Mono, b: &Mono) -> std::cmp::Ordering {
    let (ca, aa, da) = mono_prio(a);
    let (cb, ab, db) = mono_prio(b);
    ca.cmp(&cb)
        .then_with(|| match (&aa, &ab) {
            (Some(x), Some(y)) => atom_cmp(x, y),
            (Some(_), None) => std::cmp::Ordering::Greater,
            (None, Some(_)) => std::cmp::Ordering::Less,
            (None, None) => std::cmp::Ordering::Equal,
        })
        .then_with(|| da.cmp(&db))
        .then_with(|| a.cmp(b))
}

/// u が変数 v について「定数係数の 1 次」で、v が原子の中に現れないなら (係数, 残り) を返す
fn linear_in(u: &Poly, v: u32) -> Option<(Q, Poly)> {
    let a = Atom::Var(v);
    let mut coef: Option<Q> = None;
    let mut rest = Poly::zero();
    for (m, c) in u.terms() {
        let e = m.factors().iter().find(|(b, _)| *b == a).map(|(_, e)| *e).unwrap_or(0);
        let inside = m.factors().iter().any(|(b, _)| *b != a && Poly::from_atom(b.clone()).vars().contains(&v));
        if inside {
            return None;
        }
        if e == 0 {
            rest = rest.add(&Poly::mono(m.clone(), c.clone()));
        } else if e == 1 && m.factors().len() == 1 {
            coef = Some(c.clone());
        } else {
            return None;
        }
    }
    coef.map(|c| (c, rest))
}

/// d が変数 v について「v·(a·v + b)」の形（a は 0 でない有理数、v は原子の中に現れない）なら、
/// v で割った残り a·v + b = 0 の根 −b/a を返す（v = 0 は自明な解なので除く）
fn root_after_factor(d: &Poly, v: u32) -> Option<Poly> {
    let av = Atom::Var(v);
    for (m, _) in d.terms() {
        if m.factors().iter().any(|(b, _)| *b != av && Poly::from_atom(b.clone()).vars().contains(&v)) {
            return None;
        }
    }
    let cs = coeffs_in(d, &av);
    if cs.keys().copied().collect::<Vec<_>>() != vec![1, 2] {
        return None;
    }
    let a = cs[&2].as_const()?;
    if a.is_zero() {
        return None;
    }
    Some(cs[&1].neg().scale(&(Q::one() / a)))
}

/// 単項式の中の w·inv(w) を 1 に約す（f・inv の引数の中も再帰的に）。式の変形の候補を作るだけで、正しさは検証核で示す
fn cancel_inv(p: &Poly, w: u32) -> Poly {
    let wa = Atom::Var(w);
    let iwa = Atom::Inv(std::rc::Rc::new(Poly::var(w)));
    let mut out = Poly::zero();
    for (m, c) in p.terms() {
        let mut t = Poly::constant(c.clone());
        let (mut ew, mut ei) = (0u32, 0u32);
        for (a, e) in m.factors() {
            let a2 = match a {
                Atom::F(u) => Atom::F(std::rc::Rc::new(cancel_inv(u, w))),
                Atom::Inv(u) => Atom::Inv(std::rc::Rc::new(cancel_inv(u, w))),
                o => o.clone(),
            };
            if a2 == wa {
                ew += e;
            } else if a2 == iwa {
                ei += e;
            } else {
                t = t.mul(&Poly::from_atom(a2).pow(*e));
            }
        }
        let k = ew.min(ei);
        if ew > k {
            t = t.mul(&Poly::var(w).pow(ew - k));
        }
        if ei > k {
            t = t.mul(&Poly::inv(Poly::var(w)).pow(ei - k));
        }
        out = out.add(&t);
    }
    out
}

/// stored = k·target となる有理数 k（定数倍でなければ None）
fn scale_ratio(stored: &Poly, target: &Poly) -> Option<Q> {
    let (m, c) = target.terms().first()?;
    let c2 = stored.terms().iter().find(|(m2, _)| m2 == m)?.1.clone();
    let k = c2 / c;
    if target.scale(&k) == *stored {
        Some(k)
    } else {
        None
    }
}

/// 節の中で、target の定数倍になっている等式リテラルの位置と倍率
fn find_lit(c: &fe_kernel::Clause, target: &Poly) -> Option<(usize, Q)> {
    for (i, l) in c.lits().iter().enumerate() {
        if l.rel() == Rel::Eq {
            if let Some(k) = scale_ratio(l.poly(), target) {
                return Some((i, k));
            }
        }
    }
    None
}

/// 多項式に現れる f の原子（入れ子も含む）で変数を含むもの
fn f_atoms_with_vars(p: &Poly) -> Vec<Poly> {
    let mut out: Vec<Poly> = Vec::new();
    p.visit_atoms(&mut |a| {
        if let Atom::F(u) = a {
            if u.has_var() && !out.contains(u) {
                out.push((**u).clone());
            }
        }
    });
    out
}

pub enum Fin {
    Done,
    Continue,
}

impl Searcher {
    pub fn new(e: Engine) -> Searcher {
        Searcher { e, reduce_depth: 0, width: 1.0, round_budget: 0, retry: vec![], open: vec![], max_depth: 10, stats: BTreeMap::new(), add_fam: None }
    }

    fn add_time(&mut self, k: &str, t0: Instant) {
        *self.stats.entry(k.to_string()).or_insert(0) += t0.elapsed().as_millis() as u64;
    }

    /// 幅で拡大縮小した個数（1 以上）
    fn scaled(&self, n: usize) -> usize {
        ((n as f64) * self.width).round().max(1.0) as usize
    }

    fn bump(&mut self, k: &str) {
        *self.stats.entry(k.to_string()).or_insert(0) += 1;
    }

    pub fn solve_root(&mut self) -> Res<()> {
        let mut st = BState::new(fe_kernel::ROOT);
        let ax = self.e.k.axiom();
        match self.e.add_fact(&mut st, ax) {
            Ok(_) => {}
            Err(m) if m == TIMEOUT => {
                self.open.push((st.b, TIMEOUT.into()));
                return Ok(());
            }
            Err(m) => return Err(m),
        }
        self.solve_branch(st, 0)
    }

    /// 1 つの枝を解く。閉じる・解が確定する・子に分かれる・未解決のいずれかで戻る。
    pub fn solve_branch(&mut self, mut st: BState, depth: u32) -> Res<()> {
        let r = self.solve_branch_inner(&mut st, depth);
        match r {
            Ok(()) => Ok(()),
            Err(m) if m == TIMEOUT => {
                if !self.e.k.is_closed(st.b) && !self.e.k.branch(st.b).is_settled() && self.e.k.branch(st.b).children().is_empty() {
                    self.open.push((st.b, TIMEOUT.into()));
                    // 部分的な期限で止まった葉は、あとで残り時間があれば再開する
                    if self.retry.len() < 64 {
                        self.retry.push((st, depth));
                    }
                }
                Ok(())
            }
            Err(m) => Err(m),
        }
    }

    /// 全体の探索のあとで、時間切れで止まった葉の探索を残り時間で再開する
    pub fn retry_timeouts(&mut self, final_deadline: Instant) -> Res<()> {
        let mut pass = 0;
        while !self.retry.is_empty() && pass < 3 {
            pass += 1;
            let items = std::mem::take(&mut self.retry);
            let k = items.len();
            for (i, (st, depth)) in items.into_iter().enumerate() {
                let now = Instant::now();
                if now >= final_deadline {
                    return Ok(());
                }
                let b = st.b;
                if self.e.k.branch(b).is_dead() || self.e.k.is_dead(b) || !self.e.k.branch(b).children().is_empty() || self.e.k.branch(b).is_settled() {
                    continue;
                }
                let share = final_deadline.saturating_duration_since(now) / ((k - i) as u32);
                self.e.deadline = now + share;
                self.open.retain(|(ob, _)| *ob != b);
                self.bump("retry");
                self.solve_branch(st, depth)?;
            }
        }
        self.e.deadline = final_deadline;
        Ok(())
    }

    fn closed(&self, st: &BState) -> bool {
        self.e.k.is_dead(st.b) || self.e.find_contradiction(st).is_some()
    }

    fn solve_branch_inner(&mut self, st: &mut BState, depth: u32) -> Res<()> {
        let mut stale = 0;
        for round in 0..12 {
            self.e.check_time()?;
            if self.closed(st) {
                return Ok(());
            }
            if let Some(rule) = self.solution_rule(st) {
                if let Fin::Done = self.finalize(st, rule, depth)? {
                    return Ok(());
                }
                if self.closed(st) {
                    return Ok(());
                }
            }
            self.remove_point_conditions(st)?;
            if self.closed(st) {
                return Ok(());
            }
            if depth < self.max_depth {
                if self.try_split(st, depth)? {
                    return Ok(());
                }
            }
            if round == 1 && depth < self.max_depth && self.zero_split(st, depth)? {
                return Ok(());
            }
            if round == 2 && depth <= 4 && self.identity_split(st, depth)? {
                return Ok(());
            }
            if round == 2 && depth <= 4 && std::env::var("FE_NO_INJ").is_err() && self.try_injectivity(st, depth)? {
                return Ok(());
            }
            if depth < self.max_depth && self.solution_rule(st).is_none() && self.pointwise_split(st, depth)? {
                return Ok(());
            }
            if depth < 5 && self.solution_rule(st).is_none() && self.coef_split(st, depth)? {
                return Ok(());
            }
            self.pointwise_instances(st)?;
            if self.closed(st) {
                return Ok(());
            }
            if st.inj.is_some() {
                self.apply_injectivity(st)?;
                if self.closed(st) {
                    return Ok(());
                }
            }
            if round == 2 && depth <= 5 && st.inj.is_none() && self.try_zero_injectivity(st, depth)? {
                return Ok(());
            }
            if round >= 4 && depth <= 3 && self.reduce_depth == 0 && self.solution_rule(st).is_none() && self.try_reduction(st, depth)? {
                return Ok(());
            }
            if st.zinj.is_some() {
                self.apply_zero_injectivity(st)?;
                if self.closed(st) {
                    return Ok(());
                }
            }
            let before = st.units.len() + st.others.len();
            let t0 = Instant::now();
            let r = self.instances(st, round);
            self.add_time("t_instances", t0);
            r?;
            if self.closed(st) {
                return Ok(());
            }
            let t0 = Instant::now();
            let r = self.eliminate(st);
            self.add_time("t_elim", t0);
            r?;
            let t0 = Instant::now();
            let r = self.zero_products(st);
            self.add_time("t_zp", t0);
            r?;
            if self.closed(st) {
                return Ok(());
            }
            let r = self.square_ranges(st);
            r?;
            if self.closed(st) {
                return Ok(());
            }
            self.sign_merge(st)?;
            if self.closed(st) {
                return Ok(());
            }
            self.cauchy_step(st)?;
            if self.closed(st) {
                return Ok(());
            }
            if self.try_mark_additive(st)? {
                return Ok(());
            }
            self.same_rhs(st)?;
            if self.closed(st) {
                return Ok(());
            }
            let t0 = Instant::now();
            let r = self.eliminate2(st);
            self.add_time("t_elim2", t0);
            r?;
            if depth < self.max_depth && self.split_disjoint(st, depth)? {
                return Ok(());
            }
            let after = st.units.len() + st.others.len();
            if after == before {
                stale += 1;
                if stale >= 2 && round >= 3 {
                    break;
                }
            } else {
                stale = 0;
            }
        }
        if self.closed(st) {
            return Ok(());
        }
        if let Some(rule) = self.solution_rule(st) {
            if let Fin::Done = self.finalize(st, rule, depth)? {
                return Ok(());
            }
        }
        if self.try_piecewise_leaf(st)? {
            return Ok(());
        }
        let reason = if self.solution_rule(st).is_some() {
            "解の形 f(x)=g(x) は得たが、パラメータを決めきれない".to_string()
        } else {
            "f(x) = g(x) の形を導けない".to_string()
        };
        self.open.push((st.b, reason));
        Ok(())
    }

    /// f ≡ 0 が解なら「∀x. f(x) = 0」か「ある j で f(j) ≠ 0」かで場合を分ける（排中律）
    fn zero_split(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        if st.tried.contains("zero_split") {
            return Ok(false);
        }
        st.tried.insert("zero_split".into());
        if self.e.k.verify_solution(&Poly::zero()).is_err() {
            return Ok(false);
        }
        let c = fe_kernel::Clause::new(1, vec![Lit::eq(Poly::f(x()))]).map_err(|e| e.to_string())?;
        self.bump("zero_split");
        let (c0, h0, c1, hs, _consts) = self.e.k.split_em(st.b, c)?;
        let children = vec![(c0, h0), (c1, hs[0])];
        self.run_children(st, children, depth)?;
        Ok(true)
    }

    /// 単射性の補題を試す: 排中律で「∀x,y. f(x) = f(y) ⇒ x = y」とその否定（ある a ≠ b で f(a) = f(b)）に分け、
    /// 否定側を時間予算内に矛盾で閉じられれば肯定側で続ける。閉じられなければ場合分けを取り消す。
    fn try_injectivity(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
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

    /// 帰着: 導いた 2 変数の等式を新しい方程式として別に解き、完全解決すれば ImportLemma で取り込む
    fn try_reduction(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
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

    /// 零点の補題を試す: 排中律で「∀x. f(x) = 0 ⇒ x = 0」とその否定（ある k ≠ 0 で f(k) = 0）に分け、
    /// 否定側を時間予算内に閉じられれば肯定側で続ける。閉じられなければ場合分けを取り消す。
    fn try_zero_injectivity(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
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
    fn apply_zero_injectivity(&mut self, st: &mut BState) -> Res<()> {
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
    fn apply_injectivity(&mut self, st: &mut BState) -> Res<()> {
        let inj = match st.inj {
            Some(h) => h,
            None => return Ok(()),
        };
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

    /// 恒等関数の候補による場合分け: 「∀x. f(x) = x」か「ある a で f(a) ≠ a」か（排中律）。
    /// 後者では点 a と f(a) − a ≠ 0（逆数）を代入・約分に使う。
    fn identity_split(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        if st.tried.contains("id_split") || self.solution_rule(st).is_some() {
            return Ok(false);
        }
        st.tried.insert("id_split".into());
        let c = fe_kernel::Clause::new(1, vec![Lit::eq(Poly::f(x()).sub(&x()))]).map_err(|e| e.to_string())?;
        let (c0, h0, c1, hs, _consts) = self.e.k.split_em(st.b, c)?;
        self.bump("id_split");
        let children = vec![(c0, h0), (c1, hs[0])];
        // 子 0 は f(x) = x なのですぐ終わる。子 1 に残り時間のほとんどが回る
        let mut ch = children.into_iter();
        let (b0, h0) = ch.next().unwrap();
        let mut s0 = st.child(b0);
        s0.tried.insert("id_split".into());
        match self.e.add_fact(&mut s0, h0) {
            Ok(_) => self.solve_branch(s0, depth + 1)?,
            Err(m) if m == TIMEOUT => self.open.push((b0, TIMEOUT.into())),
            Err(m) => return Err(m),
        }
        let (b1, h1) = ch.next().unwrap();
        let mut s1 = st.child(b1);
        s1.tried.insert("id_split".into());
        match self.e.add_fact(&mut s1, h1) {
            Ok(_) => self.solve_branch(s1, depth + 1)?,
            Err(m) if m == TIMEOUT => self.open.push((b1, TIMEOUT.into())),
            Err(m) => return Err(m),
        }
        Ok(true)
    }

    /// 代入候補にする特別な点: 枝の定数（スコーレム定数）と、f の値が定数とわかっている閉じた点
    fn special_points(&mut self, st: &mut BState) -> Res<Vec<Poly>> {
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

    fn try_instance(&mut self, st: &mut BState, f: Fact, s: Vec<Poly>, nv: u32) -> Res<bool> {
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

    fn instances(&mut self, st: &mut BState, round: usize) -> Res<()> {
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

    /// 閉じた係数 a（f(a·x + b) の a や a·f(x) の a）について「a = 0」と「a ≠ 0」に分ける（a ≠ 0 側では逆数を使える）
    fn coef_split(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        let fx = Atom::F(std::rc::Rc::new(x()));
        let mut cands: Vec<Poly> = Vec::new();
        for &u in &st.units {
            if self.e.nvars(u) != 1 {
                continue;
            }
            let p = self.e.poly0(u);
            let fatoms = f_atoms_with_vars(&p);
            if fatoms.len() != 1 {
                continue;
            }
            let arg = &fatoms[0];
            let cs = coeffs_in(arg, &Atom::Var(0));
            if cs.keys().max() == Some(&1) {
                if let Some(a) = cs.get(&1) {
                    if a.as_const().is_none() && !a.has_var() && !cands.contains(a) {
                        cands.push(a.clone());
                    }
                }
            }
            if *arg == x() {
                let c2 = coeffs_in(&p, &fx);
                if c2.keys().max() == Some(&1) {
                    if let Some(c) = c2.get(&1) {
                        if c.as_const().is_none() && !c.has_var() && !cands.contains(c) {
                            cands.push(c.clone());
                        }
                    }
                }
            }
        }
        for a in cands {
            let an = a.monic();
            let key = format!("coef|{:x}", hash_poly(&an));
            if !st.tried.insert(key) {
                continue;
            }
            if st.invs.iter().any(|(u, _)| u.monic() == an) {
                continue;
            }
            // 既に 0 とわかっているなら分けない
            let (a2, _) = self.e.rw_poly(st, &a, 0)?;
            if a2.is_zero() || a2.as_const().is_some() {
                continue;
            }
            let c = fe_kernel::Clause::new(0, vec![Lit::eq(a2)]).map_err(|e| e.to_string())?;
            let (c0, h0, c1, hs, _) = self.e.k.split_em(st.b, c)?;
            self.bump("coef_split");
            let children = vec![(c0, h0), (c1, hs[0])];
            self.run_children(st, children, depth)?;
            return Ok(true);
        }
        Ok(false)
    }

    /// 全射性の証人 S（f(S(t)) = t）。1 変数の単位等式 f(u(x)) = a·x + b（a ≠ 0 の有理数, b は閉じた式）から S(t) = u((t − b)/a)
    fn witnesses(&self, st: &BState) -> Vec<Poly> {
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
    fn inverse_substs(&self, p: &Poly) -> Vec<(u32, Poly)> {
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
    fn zero_case_items(
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
    fn inverse_instance(&mut self, st: &mut BState, g: Fact, v: u32, sv: Poly) -> Res<bool> {
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
    fn cancel_substs(&self, p: &Poly, round: usize, invs: &[(Poly, Poly)]) -> Vec<Vec<Poly>> {
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

    fn eliminate(&mut self, st: &mut BState) -> Res<()> {
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

    /// 正の側・0・負の側のそれぞれで f の式を与える事実がそろっていれば、区分的な解として葉を確定する
    fn try_piecewise_leaf(&mut self, st: &mut BState) -> Res<bool> {
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
        let (neg, pos) = match (neg, pos) {
            (Some(a), Some(c)) => (a, c),
            _ => return Ok(false),
        };
        // 0 での値が事実で決まらなければ、パラメータ c（任意の実数）とする
        let (pv, pfact) = match &pt {
            Some((f, h)) => (h.subst_vars(&[Poly::zero()]), Some(*f)),
            None => (Poly::var(2), None),
        };
        if pfact.is_some() && neg.1 == pos.1 && pv == pos.1.subst_vars(&[Poly::zero()]) {
            return Ok(false); // 多項式の解（通常の仕上げで扱う）
        }
        let fam = match self.e.k.verify_piecewise(vec![zero], vec![neg.1.clone(), pv, pos.1.clone()]) {
            Ok(f) => f,
            Err(_) => return Ok(false),
        };
        self.e.k.mark_piecewise(st.b, vec![Some(neg.0), pfact, Some(pos.0)], fam)?;
        self.bump("piecewise_leaf");
        Ok(true)
    }

    /// 各点ごとの選言 ∀x. f(x) = g₁(x) ∨ … ∨ f(x) = g_k(x)（g_i は x の f を含まない）を探す
    fn pointwise_clauses(&self, st: &BState) -> Vec<(Fact, Vec<Poly>)> {
        let fx = Atom::F(std::rc::Rc::new(x()));
        let mut out = Vec::new();
        for &f in &st.others {
            let c = self.e.clause(f);
            if c.nvars() != 1 || c.lits().len() < 2 || c.lits().iter().any(|l| l.rel() != Rel::Eq) {
                continue;
            }
            let fmx = Atom::F(std::rc::Rc::new(x().neg()));
            let mut gs = Vec::new();
            for l in c.lits() {
                let p = l.poly();
                // f(x) − g(x) の形、または f(−x) − h(x) の形（このとき候補は g(t) = h(−t)）
                let (atom, reflect) = if coeff_of_atom(p, &fx).is_some() && !p.top_atoms().contains(&fmx) {
                    (fx.clone(), false)
                } else if coeff_of_atom(p, &fmx).is_some() && !p.top_atoms().contains(&fx) {
                    (fmx.clone(), true)
                } else {
                    break;
                };
                let cf = coeff_of_atom(p, &atom).unwrap();
                let h = Poly::from_atom(atom.clone()).sub(&p.scale(&(Q::one() / cf)));
                if !f_atoms_with_vars(&h).is_empty() || h.top_atoms().contains(&atom) {
                    break;
                }
                let g = if reflect { h.subst_vars(&[x().neg()]) } else { h };
                if !gs.contains(&g) {
                    gs.push(g);
                }
            }
            if gs.len() < 1 {
                continue;
            }
            let ok = c.lits().iter().all(|l| {
                let p = l.poly();
                coeff_of_atom(p, &fx).is_some() || coeff_of_atom(p, &fmx).is_some()
            });
            if ok && gs.len() >= 1 && c.lits().len() >= 2 {
                out.push((f, gs));
            }
        }
        out
    }

    /// 各点ごとの選言を、候補ごとの排中律で全体の場合に分ける（各点→全体の推論を正しく行う）
    fn pointwise_split(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        let pcs = self.pointwise_clauses(st);
        for (cf, gs) in pcs {
            let remaining: Vec<Poly> = gs.iter().filter(|g| !st.tried.contains(&format!("pwx|{:x}", hash_poly(g)))).cloned().collect();
            if remaining.is_empty() {
                continue;
            }
            let g = remaining[0].clone();
            let key = format!("pws|{:x}", hash_poly(&g));
            if !st.tried.insert(key) {
                continue;
            }
            let c = fe_kernel::Clause::new(1, vec![Lit::eq(Poly::f(x()).sub(&g))]).map_err(|e| e.to_string())?;
            let (c0, h0, c1, hs, consts) = self.e.k.split_em(st.b, c)?;
            self.bump("pointwise_split");
            let saved = self.e.deadline;
            let now = Instant::now();
            let remain = saved.saturating_duration_since(now);
            // 子 0（f = g）
            self.e.deadline = now + remain / 3;
            let mut s0 = st.child(c0);
            match self.e.add_fact(&mut s0, h0) {
                Ok(_) => self.solve_branch(s0, depth + 1)?,
                Err(m) if m == TIMEOUT => self.open.push((c0, TIMEOUT.into())),
                Err(m) => return Err(m),
            }
            // 子 1（ある a で f(a) ≠ g(a)）
            self.e.deadline = saved;
            let mut s1 = st.child(c1);
            s1.tried.insert(format!("pwx|{:x}", hash_poly(&g)));
            let r = (|| -> Res<()> {
                for h in &hs {
                    self.e.add_fact(&mut s1, *h)?;
                }
                let a = Poly::cnst(consts[0]);
                let inst = self.e.k.instantiate(c1, cf, vec![a.clone()], 0)?;
                self.e.add_fact(&mut s1, inst)?;
                let inst2 = self.e.k.instantiate(c1, cf, vec![a.neg()], 0)?;
                self.e.add_fact(&mut s1, inst2)?;
                Ok(())
            })();
            match r {
                Ok(()) => self.solve_branch(s1, depth + 1)?,
                Err(m) if m == TIMEOUT => self.open.push((c1, TIMEOUT.into())),
                Err(m) => return Err(m),
            }
            return Ok(true);
        }
        Ok(false)
    }

    /// 各点ごとの選言を、事実に現れる閉じた点 K（定数を含む f の引数）で例化する（閉じた選言 → 場合分け）
    fn pointwise_instances(&mut self, st: &mut BState) -> Res<()> {
        let pcs = self.pointwise_clauses(st);
        if pcs.is_empty() {
            return Ok(());
        }
        let mut points: Vec<Poly> = Vec::new();
        for &u in &st.units {
            let p = self.e.poly0(u);
            p.visit_atoms(&mut |a| {
                if let Atom::F(k) = a {
                    if !k.has_var() && !k.consts().is_empty() && !k.has_f() && !points.contains(k) {
                        points.push((**k).clone());
                    }
                }
            });
        }
        points.sort_by_key(|k| poly_size(k));
        points.truncate(self.scaled(16));
        let mut made = 0;
        for (cf, _) in pcs {
            for k in &points {
                if made >= self.scaled(10) || self.closed(st) {
                    return Ok(());
                }
                let key = format!("pwi|{:?}|{:x}", cf, hash_poly(k));
                if !st.tried.insert(key) {
                    continue;
                }
                let inst = self.e.k.instantiate(st.b, cf, vec![k.clone()], 0)?;
                self.bump("pointwise_inst");
                self.e.add_fact(st, inst)?;
                made += 1;
                let inst2 = self.e.k.instantiate(st.b, cf, vec![k.neg()], 0)?;
                self.e.add_fact(st, inst2)?;
            }
        }
        Ok(())
    }

    /// 符号の条件つきの 1 変数の節を扱う:
    ///  (a) 「x < 0 ∨ Q(x)」の x → −x 版「x > 0 ∨ Q(−x)」を作る
    ///  (b) 「p > 0 ∨ Q」と「−p ⋈ 0 ∨ Q」（同じ Q）から Q を導く（非負結合で 0 > 0 となり条件が両立しない）
    fn sign_merge(&mut self, st: &mut BState) -> Res<()> {
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
    fn try_mark_additive(&mut self, st: &mut BState) -> Res<bool> {
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
    fn cauchy_step(&mut self, st: &mut BState) -> Res<()> {
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
    fn square_ranges(&mut self, st: &mut BState) -> Res<()> {
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

    /// 右辺が同じ事実の比較: c·f(A₁) = R と c'·f(A₂) = R'（R/c = R'/c'）から f(A₁) − f(A₂) = 0 を作る
    fn same_rhs(&mut self, st: &mut BState) -> Res<()> {
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
    fn eliminate2(&mut self, st: &mut BState) -> Res<()> {
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

    /// 2 変数の単位等式が A(x)·B(y) = 0 と分解できれば、変数を共有しない選言として全体の場合分けをする
    fn split_disjoint(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        let twos: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 2).collect();
        for f in twos {
            let key = format!("dsplit|{:x}", hash_clause(self.e.clause(f)));
            if st.tried.contains(&key) {
                continue;
            }
            st.tried.insert(key);
            let p = self.e.poly0(f);
            let (a, b) = match rank1_split(&p) {
                Some(ab) => ab,
                None => continue,
            };
            let zp = match self.e.k.zero_product(st.b, f, 0, vec![a, b]) {
                Ok(z) => z,
                Err(_) => continue,
            };
            if crate::search::n_components(self.e.clause(zp)) < 2 {
                continue;
            }
            // f を含まない成分（∀y. y = 0 など）は、その変数に値を代入すれば偽になるので消す
            let zp = self.drop_ffree_components(st, zp)?;
            if crate::search::n_components(self.e.clause(zp)) < 2 {
                self.e.add_fact(st, zp)?;
                continue;
            }
            self.bump("split_disjoint");
            let children = self.e.k.split_components(st.b, zp)?;
            self.run_children(st, children, depth)?;
            return Ok(true);
        }
        Ok(false)
    }

    fn drop_ffree_components(&mut self, st: &mut BState, f: Fact) -> Res<Fact> {
        self.e.drop_ffree_components(st, f)
    }

    // ------------------------------------------------------------------
    // 解の形が決まったときの仕上げ

    /// 規則 f(x) → g(x)（g は x の f を含まない）
    fn solution_rule(&self, st: &BState) -> Option<RwRule> {
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

    fn finalize(&mut self, st: &mut BState, rule: RwRule, depth: u32) -> Res<Fin> {
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

    /// 閉じた（変数のない）事実の因数分解による場合分け。分けたら true。
    fn try_split(&mut self, st: &mut BState, depth: u32) -> Res<bool> {
        // 閉じた選言（変数のない節）はそのまま場合分けする
        let closed_disj: Vec<Fact> = st.others.iter().copied().filter(|f| {
            let c = self.e.clause(*f);
            c.nvars() == 0 && c.lits().len() >= 2
        }).collect();
        for f in closed_disj {
            let key = format!("csplit|{:?}", f);
            if !st.tried.insert(key) {
                continue;
            }
            let f2 = self.drop_rootless(st, f)?;
            let n = self.e.clause(f2).lits().len();
            if n == 0 {
                return Ok(true);
            }
            if n == 1 {
                self.e.add_fact(st, f2)?;
                continue;
            }
            self.bump("split");
            let children = self.e.k.split_components(st.b, f2)?;
            self.run_children(st, children, depth)?;
            return Ok(true);
        }
        let closed: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 0).collect();
        for f in closed {
            let key = format!("split|{:x}", hash_clause(self.e.clause(f)));
            if st.tried.contains(&key) {
                continue;
            }
            st.tried.insert(key);
            let p = self.e.poly0(f);
            let factors = match self.closed_factors(&p) {
                Some(fs) => fs,
                None => continue,
            };
            if factors.len() < 2 {
                continue;
            }
            let zp = match self.e.k.zero_product(st.b, f, 0, factors) {
                Ok(z) => z,
                Err(_) => continue,
            };
            if self.e.clause(zp).lits().len() < 2 {
                // 因子がまとまって 1 つになった
                self.e.add_fact(st, zp)?;
                continue;
            }
            // 無理な因子（実数解なし）を先に消す
            let zp = self.drop_rootless(st, zp)?;
            let n = self.e.clause(zp).lits().len();
            if n == 0 {
                return Ok(true);
            }
            if n == 1 {
                self.e.add_fact(st, zp)?;
                continue;
            }
            self.bump("split");
            let children = self.e.k.split_components(st.b, zp)?;
            self.run_children(st, children, depth)?;
            return Ok(true);
        }
        Ok(false)
    }

    fn run_children(&mut self, st: &BState, children: Vec<(BranchId, Fact)>, depth: u32) -> Res<()> {
        let saved = self.e.deadline;
        let k = children.len();
        for (i, (cb, h)) in children.into_iter().enumerate() {
            let now = Instant::now();
            let remain = saved.saturating_duration_since(now);
            let share = remain / ((k - i) as u32);
            self.e.deadline = now + share.max(Duration::from_millis(10));
            let mut cst = st.child(cb);
            let r = (|| -> Res<()> {
                match self.e.add_fact(&mut cst, h)? {
                    _ => {}
                }
                Ok(())
            })();
            match r {
                Ok(()) => self.solve_branch(cst, depth + 1)?,
                Err(m) if m == TIMEOUT => self.open.push((cb, TIMEOUT.into())),
                Err(m) => {
                    self.e.deadline = saved;
                    return Err(m);
                }
            }
            self.e.deadline = saved;
        }
        Ok(())
    }

    /// 2 次以上の因子で実数解をもたないもの（平方完成で正）を、矛盾として節から取り除く
    fn drop_rootless(&mut self, st: &mut BState, f: Fact) -> Res<Fact> {
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

    /// 1 変数（閉じた原子 1 つ）の 2 次式 q が常に正（または負）なら、事実「±q > 0」を作る
    fn prove_positive(&mut self, st: &mut BState, q: &Poly) -> Res<Option<Fact>> {
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

    fn closed_factors(&self, p: &Poly) -> Option<Vec<Poly>> {
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

    /// 1 変数の事実の因数分解: x^k·Q(x) = 0 や f(x) の 2 次式
    fn zero_products(&mut self, st: &mut BState) -> Res<()> {
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

    /// 「x − r = 0 ∨ Q(x) = 0」で Q(r) = 0 が示せるとき、∀x. Q(x) = 0 を導く
    fn remove_point_conditions(&mut self, st: &mut BState) -> Res<()> {
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

    fn lift_point_condition(&mut self, st: &mut BState, f: Fact, ci: usize, _qi: usize, r: &Q, qp: &Poly) -> Res<Option<Fact>> {
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
}

fn vander(d: u32) -> Vec<Vec<Q>> {
    (0..=d).map(|i| (0..=d).map(|a| Q::from_integer((i as i64).pow(a).into())).collect()).collect::<Vec<_>>()
}

/// x − r の形なら r
fn is_point_cond(p: &Poly) -> Option<Q> {
    if p.has_f() {
        return None;
    }
    let cs = coeffs_in(p, &Atom::Var(0));
    if cs.keys().max() != Some(&1) || cs.len() > 2 {
        return None;
    }
    let c1 = cs.get(&1)?.as_const()?;
    let c0 = cs.get(&0).map(|c| c.as_const()).unwrap_or(Some(Q::zero()))?;
    if p.vars().len() != 1 {
        return None;
    }
    Some(-c0 / c1)
}

// ---------------------------------------------------------------------------
// 候補解の探索（部分結果用）。数値は使わず、係数の連立方程式を有理数で解く。

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

/// 有理数解を、1 変数になった方程式の有理根で分岐しながら探す
fn solve_system(eqs: &[Poly], vars: &[u32], asg: BTreeMap<u32, Q>, out: &mut Vec<BTreeMap<u32, Q>>, depth: u32) {
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

pub fn n_components(c: &fe_kernel::Clause) -> usize {
    fe_kernel::kernel::components(c).len()
}

/// 単項式を x だけの部分と y だけの部分に分ける（x と y を両方含む原子があれば None）。閉じた原子は x 側に入れる。
fn split_mono_xy(m: &Mono) -> Option<(Mono, Mono)> {
    let mut mx = Mono::one();
    let mut my = Mono::one();
    for (a, e) in m.factors() {
        let vs = Poly::from_atom(a.clone()).vars();
        let piece = {
            let mut t = Mono::one();
            for _ in 0..*e {
                t = t.mul(&Mono::atom(a.clone()));
            }
            t
        };
        if vs.contains(&0) && vs.contains(&1) {
            return None;
        } else if vs.contains(&1) {
            my = my.mul(&piece);
        } else {
            mx = mx.mul(&piece);
        }
    }
    Some((mx, my))
}

/// p(x, y) = A(x)·B(y) と分解できれば (A, B)（どちらも定数でない）
pub fn rank1_split(p: &Poly) -> Option<(Poly, Poly)> {
    let mut m: BTreeMap<Mono, BTreeMap<Mono, Q>> = BTreeMap::new();
    for (mono, c) in p.terms() {
        let (mx, my) = split_mono_xy(mono)?;
        m.entry(mx).or_default().insert(my, c.clone());
    }
    let (x0, row0) = m.iter().next()?;
    let (y0, c00) = row0.iter().next()?;
    let _ = x0;
    // A(x) = Σ_i M[i][y0] x_i, B(y) = Σ_j M[x0][j]/M[x0][y0] y_j
    let mut a = Poly::zero();
    for (mx, row) in &m {
        let c = row.get(y0).cloned().unwrap_or_else(Q::zero);
        a = a.add(&Poly::mono(mx.clone(), c));
    }
    let mut b = Poly::zero();
    for (my, c) in row0 {
        b = b.add(&Poly::mono(my.clone(), c / c00));
    }
    if a.mul(&b) != *p {
        return None;
    }
    if !a.vars().contains(&0) || !b.vars().contains(&1) {
        return None;
    }
    Some((a, b))
}

/// u が変数 v について「閉じた係数 c（定数でない）の 1 次」なら (c, 残り)
fn linear_in_closed(u: &Poly, v: u32) -> Option<(Poly, Poly)> {
    let a = Atom::Var(v);
    let cs = coeffs_in(u, &a);
    if cs.keys().max() != Some(&1) {
        return None;
    }
    let c = cs.get(&1)?.clone();
    if c.has_var() || c.as_const().is_some() {
        return None;
    }
    let w = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
    if w.vars().contains(&v) {
        return None;
    }
    // v が原子の中に現れないこと
    for (m, _) in u.terms() {
        for (b, _) in m.factors() {
            if *b != a && Poly::from_atom(b.clone()).vars().contains(&v) {
                return None;
            }
        }
    }
    Some((c, w))
}

fn hash_clause(c: &fe_kernel::Clause) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    c.hash(&mut h);
    h.finish()
}

fn hash_poly(p: &Poly) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    p.hash(&mut h);
    h.finish()
}

/// 1 変数の式の f(a·x + b) で a の逆数 inv(a) がわかっていれば、x := (x − b)·inv(a)
fn affine_inv_substs(p: &Poly, invs: &[(Poly, Poly)]) -> Vec<Poly> {
    let mut out = Vec::new();
    for arg in f_atoms_with_vars(p) {
        let cs = coeffs_in(&arg, &Atom::Var(0));
        if cs.keys().max() != Some(&1) {
            continue;
        }
        let a = match cs.get(&1) {
            Some(a) => a.clone(),
            None => continue,
        };
        let b = cs.get(&0).cloned().unwrap_or_else(Poly::zero);
        if b.has_var() {
            continue;
        }
        for (u, iu) in invs {
            if *u == a || u.monic() == a.monic() {
                // a = λu なら inv(a) = inv(u)/λ
                let lam = a.leading_coeff().unwrap() / u.leading_coeff().unwrap();
                let s = x().sub(&b).mul(iu).scale(&(Q::one() / lam));
                if !out.contains(&s) {
                    out.push(s);
                }
            }
        }
    }
    out
}
