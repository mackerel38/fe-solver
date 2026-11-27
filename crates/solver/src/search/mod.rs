//! 探索戦略。すべての事実は Engine 経由で検証核の推論規則から得る。
//! 手法ごとにファイルを分けている（docs/TACTICS.md の節に対応）。
#![allow(unused_imports)]

mod elimination;
mod finalize;
mod lemmas;
mod properties;
mod reduction;
mod shift;
mod splits;
mod substitution;
pub(crate) mod util;

use crate::engine::{coeff_of_atom, replace_atom, Added, BState, Engine, Res, RwRule, TIMEOUT};
use crate::order::{atom_cmp, poly_size};
use crate::polyutil::*;
use fe_kernel::{AddFamily, AddKind, Atom, BranchId, Fact, Family, Kernel, Lit, Mono, Poly, Rel, Q};
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use util::*;
pub use finalize::{find_arb_candidates, find_candidates, find_pw_candidates};
pub use util::{n_components, rank1_split};

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
    pub(crate) add_fam: Option<Option<AddFamily>>,
    /// 検証核で確かめた多項式の解の候補（補題の推測に使う。パラメータは Const(1000…) の記号）
    pub(crate) sols: Vec<Poly>,
}

pub enum Fin {
    Done,
    Continue,
}

impl Searcher {
    pub fn new(e: Engine) -> Searcher {
        let sols: Vec<Poly> = finalize::find_candidates(&e.k).iter().map(|f| f.g().clone()).collect();
        Searcher { e, reduce_depth: 0, width: 1.0, round_budget: 0, retry: vec![], open: vec![], max_depth: 10, stats: BTreeMap::new(), add_fam: None, sols }
    }

    pub(crate) fn add_time(&mut self, k: &str, t0: Instant) {
        *self.stats.entry(k.to_string()).or_insert(0) += t0.elapsed().as_millis() as u64;
    }

    /// 幅で拡大縮小した個数（1 以上）
    pub(crate) fn scaled(&self, n: usize) -> usize {
        ((n as f64) * self.width).round().max(1.0) as usize
    }

    pub(crate) fn bump(&mut self, k: &str) {
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

    pub(crate) fn closed(&self, st: &BState) -> bool {
        self.e.k.is_dead(st.b) || self.e.find_contradiction(st).is_some()
    }

    pub(crate) fn solve_branch_inner(&mut self, st: &mut BState, depth: u32) -> Res<()> {
        let mut stale = 0;
        for round in st.start_round.min(11)..12 {
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
            // 条件つきの事実を、条件が偽とわかっている点で例化する（安いので場合分けより先に）
            self.discharge_conditions(st)?;
            if self.closed(st) {
                return Ok(());
            }
            self.affine_inverse_ones(st)?;
            if self.closed(st) {
                return Ok(());
            }
            // 逆数の代入 x := K/x（f の引数の 1/x を消す）
            self.reciprocal_instances(st)?;
            if self.closed(st) {
                return Ok(());
            }
            // 既知の型（f(xy + g(x)) = x f(y) + h(x) なら f は 1 次）
            self.apply_known_types(st)?;
            if self.closed(st) {
                return Ok(());
            }
            // 単射性がわかっていれば、場合分けより先に当てはめる（選言の中も。安い）
            if st.inj.is_some() {
                self.apply_injectivity(st)?;
                if self.closed(st) {
                    return Ok(());
                }
            }
            // 零点の補題がわかっていれば、場合分けより先に当てはめる（安い）
            if st.zinj.is_some() {
                self.apply_zero_injectivity(st)?;
                if self.closed(st) {
                    return Ok(());
                }
            }
            // f が式 T の値で 0 になる事実があれば、零点の補題（f(t) = 0 ⇒ t = 0 か、f(k) = 0 となる k ≠ 0 があるか）を
            // 閉じた選言の場合分けより先に試す（否定側は f(k·x) = 0 から x := x/k で閉じることが多い）
            if depth <= 5 && st.inj.is_none() && st.zinj.is_none() && !st.tried.contains("zinj") && self.has_zero_image(st) {
                if self.try_zero_injectivity(st, depth)? {
                    return Ok(());
                }
                if self.closed(st) {
                    return Ok(());
                }
            }
            // 見つけた解に導かれる補題の推測（すべての解が満たす性質を、否定を閉じられれば補題にする）
            // 探索の予定の最後の段階（幅 2 以上。前の段階で解けなかった問題）だけで行う
            if round == 2 && depth <= 2 && self.width >= 2.0 && std::env::var("FE_NO_SPEC").is_err() {
                if self.speculate_lemmas(st, depth, round)? {
                    return Ok(());
                }
                if self.closed(st) {
                    return Ok(());
                }
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
            // 各点の選言を閉じた点で例化する（閉じた選言は次のラウンドで場合分けされるので、先に代入を 1 回行う）
            self.pointwise_instances(st)?;
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
            // f の値で決まる量の補題（単射性を含む）は第 0 ラウンドから（最初の場合分けの前に単射性を知るため）
            if round == 0 {
                self.value_lemmas(st)?;
                if self.closed(st) {
                    return Ok(());
                }
            }
            if round >= 1 {
                self.swap_differences(st)?;
                if self.closed(st) {
                    return Ok(());
                }
                self.shift_differences(st)?;
                if self.closed(st) {
                    return Ok(());
                }
                self.value_lemmas(st)?;
                if self.closed(st) {
                    return Ok(());
                }
                self.apply_cond_injectivity(st)?;
                if self.closed(st) {
                    return Ok(());
                }
                self.shift_lemmas(st)?;
                if self.closed(st) {
                    return Ok(());
                }
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

    pub(crate) fn run_children(&mut self, st: &BState, children: Vec<(BranchId, Fact)>, depth: u32) -> Res<()> {
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

}
