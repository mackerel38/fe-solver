//! 1 問を解く入口。結果は検証核の結論から作る。

use crate::engine::Engine;
use crate::search::{find_arb_candidates, find_candidates, find_pw_candidates, Searcher};
use fe_kernel::{AddFamily, ArbFamily, Fact, Family, Kernel, Poly, PwFamily, Rel, ROOT};
use std::time::{Duration, Instant};

pub struct SolveOutput {
    pub kernel: Kernel,
    /// complete: 解の集合を決定（多項式・区分的な族）
    /// special: 解の集合を決定（加法的関数を含む族があり、病的な解をもつ）
    /// special_exist: 任意の加法的関数を含む族、または任意の区間をもつ族が解であることを示した（病的な解が存在する）が、
    /// 解の集合は未確定
    /// partial: 解を見つけたが未確定 / unresolved: 解も見つからない
    pub status: &'static str,
    pub families: Vec<Family>,
    pub found: Vec<Family>,
    pub pw_families: Vec<PwFamily>,
    pub pw_found: Vec<PwFamily>,
    /// 解の集合に含まれる加法的な族（special のとき）
    pub add_families: Vec<AddFamily>,
    /// 検証核で確かめた「任意の加法的関数を含む解の族」（根の方程式についての検証。special / special_exist）
    pub add_found: Option<AddFamily>,
    /// 検証核で確かめた「任意の区間をもつ解の族」（ある開区間でどの値を選んでも解。special_exist）
    pub arb_found: Option<ArbFamily>,
    pub reasons: Vec<String>,
    pub error: Option<String>,
    pub elapsed: Duration,
    pub stats: Vec<(String, u64)>,
    /// 根で証明済みの主な事実（部分結果・未解決の報告用）
    pub root_facts: Vec<Fact>,
}

/// 探索の予定: (幅, 時間の割合) の列。各試行は新しい検証核で独立に行い、完全解決した時点で終える。
pub fn default_schedule() -> Vec<(f64, f64)> {
    match std::env::var("FE_SCHEDULE").ok().filter(|s| !s.trim().is_empty()).ok_or(()) {
        Ok(s) => s
            .split(',')
            .filter_map(|t| {
                let (w, f) = t.split_once(':')?;
                Some((w.parse().ok()?, f.parse().ok()?))
            })
            .collect(),
        // 既定: 幅 0.5 で時間の 25%、幅 1 で 35%、幅 2 で残り（20 秒/問の比較で 253 → 256）
        Err(_) => vec![(0.5, 0.25), (1.0, 0.35), (2.0, 1.0)],
    }
}

pub fn solve(lhs: Poly, rhs: Poly, timeout: Duration) -> Result<SolveOutput, String> {
    solve_with(lhs, rhs, timeout, &default_schedule())
}

/// 予定に従って幅を変えながら解く（反復拡幅）。最後の試行は残り時間をすべて使う。
pub fn solve_with(lhs: Poly, rhs: Poly, timeout: Duration, schedule: &[(f64, f64)]) -> Result<SolveOutput, String> {
    let start = Instant::now();
    let sched: Vec<(f64, f64)> = if schedule.is_empty() { vec![(1.0, 1.0)] } else { schedule.to_vec() };
    let mut last: Option<SolveOutput> = None;
    let mut w_last = 1.0;
    for (i, (w, frac)) in sched.iter().enumerate() {
        let remain = (start + timeout).saturating_duration_since(Instant::now());
        if remain.is_zero() && last.is_some() {
            break;
        }
        let t = if i + 1 == sched.len() { remain } else { timeout.mul_f64(*frac).min(remain) };
        let mut out = solve_once(lhs.clone(), rhs.clone(), t, *w)?;
        out.elapsed = start.elapsed();
        out.stats.push(("width_tried".into(), (*w * 100.0) as u64));
        if out.is_settled() {
            return Ok(out);
        }
        w_last = *w;
        last = Some(out);
    }
    // 予定を終えても時間が残っていれば（探索が手詰まりで早く終わった場合）、幅を倍にして残り時間で続ける
    // 幅の上限は既定 16（環境変数 FE_MAX_WIDTH で変更できる）
    let max_w: f64 = std::env::var("FE_MAX_WIDTH").ok().and_then(|v| v.parse().ok()).unwrap_or(16.0);
    let mut w = w_last;
    loop {
        let remain = (start + timeout).saturating_duration_since(Instant::now());
        if remain < Duration::from_secs(2) || remain < timeout / 10 || w >= max_w {
            break;
        }
        w *= 2.0;
        let mut out = solve_once(lhs.clone(), rhs.clone(), remain, w)?;
        out.elapsed = start.elapsed();
        out.stats.push(("width_tried".into(), (w * 100.0) as u64));
        if out.is_settled() {
            return Ok(out);
        }
        last = Some(out);
    }
    Ok(last.unwrap())
}

fn solve_once(lhs: Poly, rhs: Poly, timeout: Duration, width: f64) -> Result<SolveOutput, String> {
    let start = Instant::now();
    let k = Kernel::new(lhs, rhs)?;
    let mut engine = Engine::new(k, start + timeout);
    {
        let ax = engine.k.axiom();
        let sz = crate::order::poly_size(engine.k.clause(ax).lits()[0].poly());
        engine.size_cap = (2 * sz).max(60);
    }
    let mut s = Searcher::new(engine);
    s.width = width;
    let mut error = None;
    if let Err(m) = s.solve_root() {
        error = Some(m);
    }
    if error.is_none() {
        if let Err(m) = s.retry_timeouts(start + timeout) {
            error = Some(m);
        }
    }
    let concl = s.e.k.conclude();
    let mut found = find_candidates(&s.e.k);
    for fam in &concl.families {
        if !found.iter().any(|f| f.template() == fam.template()) {
            found.push(fam.clone());
        }
    }
    let mut pw_found = find_pw_candidates(&s.e.k);
    for fam in &concl.pw_families {
        if !pw_found.iter().any(|f| f.pieces() == fam.pieces() && f.breaks() == fam.breaks()) {
            pw_found.push(fam.clone());
        }
    }
    let add_found = s.additive_family();
    let arb_found = find_arb_candidates(&s.e.k);
    // 健全性の確認: 解の集合を決めた（complete / special）のに、任意の区間をもつ族（無数の、区分的な式で書けない解を含む）が
    // 解なら矛盾。そのときは内部エラーとして報告する（起きてはならない）
    if concl.complete && error.is_none() && arb_found.is_some() {
        error = Some("健全性の警告: 解の集合を決めたが、任意の区間をもつ族も解である".into());
    }
    let status = if concl.complete && error.is_none() {
        if concl.add_families.is_empty() {
            "complete"
        } else {
            "special"
        }
    } else if add_found.is_some() || arb_found.is_some() {
        "special_exist"
    } else if !found.is_empty() || !pw_found.is_empty() {
        "partial"
    } else {
        "unresolved"
    };
    let mut reasons: Vec<String> = s.open.iter().map(|(b, r)| format!("枝{}: {}", b.0, r)).collect();
    if let Some(e) = &error {
        reasons.push(format!("内部エラー: {}", e));
    }
    if !concl.complete && reasons.is_empty() {
        reasons.push("未解決の枝がある".into());
    }
    // 根の単位等式で小さいもの
    let mut root_facts: Vec<Fact> = Vec::new();
    for i in 0..s.e.k.num_facts() {
        let f = s.e.k.fact_at(i).unwrap();
        let rec = s.e.k.fact(f);
        if rec.branch() != ROOT {
            continue;
        }
        let c = rec.clause();
        if c.lits().len() == 1 && c.lits()[0].rel() == Rel::Eq && !c.is_tautology() {
            root_facts.push(f);
        }
    }
    root_facts.sort_by_key(|f| crate::order::poly_size(s.e.k.clause(*f).lits()[0].poly()));
    let mut seen = std::collections::HashSet::new();
    root_facts.retain(|f| seen.insert(s.e.k.clause(*f).clone()));
    root_facts.truncate(12);
    root_facts.sort();
    Ok(SolveOutput {
        status,
        families: concl.families.clone(),
        found,
        pw_families: concl.pw_families.clone(),
        pw_found,
        add_families: concl.add_families.clone(),
        add_found,
        arb_found,
        reasons,
        error,
        elapsed: start.elapsed(),
        stats: s.stats.clone().into_iter().chain(s.e.timing.iter().map(|(k, v)| (format!("us_{}", k), *v as u64))).collect(),
        root_facts,
        kernel: s.e.k,
    })
}

impl SolveOutput {
    /// 解の集合を決定したか（complete か special）
    pub fn is_settled(&self) -> bool {
        self.status == "complete" || self.status == "special"
    }
}

/// 人間向けの報告（証明文は fe_render が検証核の記録から生成する）
pub fn report(out: &SolveOutput) -> String {
    let k = &out.kernel;
    let concl = k.conclude();
    let mut s = String::new();
    match out.status {
        "complete" => {
            s.push_str("状態: 完全解決\n");
            s.push_str(&fe_render::render(k, &concl));
        }
        "special" => {
            s.push_str("状態: 特殊解決\n");
            s.push_str(&fe_render::render(k, &concl));
        }
        _ => {
            s.push_str(match out.status {
                "special_exist" => "状態: 特殊解決\n",
                "partial" => "状態: 部分結果\n",
                _ => "状態: 未解決\n",
            });
            s.push_str(&format!("方程式: {}\n", fe_render::fmt_equation(k)));
            if let Some(fam) = &out.add_found {
                s.push_str(&fe_render::render_additive_exist(k, fam));
            } else if let Some(fam) = &out.arb_found {
                s.push_str(&fe_render::render_arb_exist(k, fam));
            }
            if !out.found.is_empty() || !out.pw_found.is_empty() {
                s.push_str("見つけた解:\n");
                for f in fe_render::display_families(&out.found) {
                    // 加法的関数の族（上の【病的な解の存在】）に含まれるものは省く
                    if out.add_found.iter().any(|a| fe_render::subsumed_by_additive(f, a)) {
                        continue;
                    }
                    s.push_str(&format!("  {}\n", fe_render::fmt_family(f)));
                }
                for f in &out.pw_found {
                    s.push_str(&format!("  {}\n", fe_render::fmt_pw(f)));
                }
            }
            // 止まった理由（内部の枝番号は外し、同じ理由はまとめる）
            s.push_str("止まった理由:\n");
            let mut why: Vec<(String, usize)> = Vec::new();
            for r in &out.reasons {
                let t = match r.split_once(": ") {
                    Some((head, rest)) if head.starts_with('枝') => rest.to_string(),
                    _ => r.clone(),
                };
                match why.iter_mut().find(|(w, _)| *w == t) {
                    Some((_, n)) => *n += 1,
                    None => why.push((t, 1)),
                }
            }
            for (w, n) in why {
                if n > 1 {
                    s.push_str(&format!("  {}（{} つの場合）\n", w, n));
                } else {
                    s.push_str(&format!("  {}\n", w));
                }
            }
            s.push_str("証明済みの事実:\n");
            s.push_str(&fe_render::render_facts(k, &out.root_facts));
        }
    }
    s
}
