//! fe_render: 検証核が記録した導出から、日本語の証明文を機械的に生成する。
//!
//! 入力は `fe_kernel::Kernel`（読み取り専用）だけで、探索部からの文章は一切受け取らない。
//! 証明に必要な事実は、結論（各葉の矛盾・解の確定・場合分けに使った事実）から前提をたどって集める。
#![forbid(unsafe_code)]

use fe_kernel::kernel::{Conclusion, Split};
use fe_kernel::poly::Q;
use fe_kernel::{Atom, BranchId, Clause, Fact, Kernel, Lit, Mono, Poly, Rel, Rule, ROOT};
use num_traits::{One, Signed, Zero};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

// ---------------------------------------------------------------------------
// 式の表示

/// 変数名（節ごとに x, y, z, …）
pub fn var_name(i: u32) -> String {
    const N: [&str; 6] = ["x", "y", "z", "w", "u", "v"];
    if (i as usize) < N.len() {
        N[i as usize].to_string()
    } else {
        format!("x{}", i)
    }
}

/// 検証核が導入した定数の名前（c はパラメータ用に空けておく）
pub fn const_name(i: u32) -> String {
    const N: [&str; 12] = ["a", "b", "d", "e", "g", "h", "k", "m", "n", "p", "q", "r"];
    if (i as usize) < N.len() {
        N[i as usize].to_string()
    } else {
        format!("a{}", i)
    }
}

fn fmt_q(c: &Q) -> String {
    if c.is_integer() {
        format!("{}", c.numer())
    } else {
        format!("{}/{}", c.numer(), c.denom())
    }
}

/// f の入れ子の深さ（表示順と左辺の選択に使う）
fn atom_depth(a: &Atom) -> u32 {
    match a {
        Atom::Var(_) | Atom::Const(_) => 0,
        Atom::F(p) | Atom::Inv(p) => 1 + poly_depth(p),
    }
}
fn poly_depth(p: &Poly) -> u32 {
    p.terms().iter().flat_map(|(m, _)| m.factors().iter().map(|(a, _)| atom_depth(a))).max().unwrap_or(0)
}
fn atom_size(a: &Atom) -> u32 {
    match a {
        Atom::Var(_) | Atom::Const(_) => 1,
        Atom::F(p) | Atom::Inv(p) => 1 + p.terms().iter().map(|(m, _)| 1 + m.factors().iter().map(|(b, e)| atom_size(b) * e).sum::<u32>()).sum::<u32>(),
    }
}
fn mono_key(m: &Mono) -> (u32, u32, u32, u32) {
    let fcount = m.factors().iter().filter(|(a, _)| matches!(a, Atom::F(_))).map(|(_, e)| *e).sum();
    let depth = m.factors().iter().map(|(a, _)| atom_depth(a)).max().unwrap_or(0);
    let size = m.factors().iter().map(|(a, e)| atom_size(a) * e).sum();
    (depth, fcount, size, m.degree())
}

pub struct Names<'a> {
    pub param: Option<&'a dyn Fn(&Atom) -> Option<String>>,
}

impl<'a> Names<'a> {
    pub fn plain() -> Names<'static> {
        Names { param: None }
    }
}

fn fmt_atom(a: &Atom, n: &Names) -> String {
    if let Some(pf) = n.param {
        if let Some(s) = pf(a) {
            return s;
        }
    }
    match a {
        Atom::Var(i) => var_name(*i),
        Atom::Const(i) => const_name(*i),
        Atom::F(p) => format!("f({})", fmt_poly(p, n)),
        Atom::Inv(p) => {
            let s = fmt_poly(p, n);
            // 中身が変数・定数 1 つのときだけ括弧を省く（1/xy・1/1/x のような紛らわしい表示を避ける）
            let simple = p.terms().len() == 1
                && p.terms()[0].1.is_one()
                && matches!(p.terms()[0].0.factors(), [(Atom::Var(_) | Atom::Const(_), 1)]);
            if simple {
                format!("1/{}", s)
            } else {
                format!("1/({})", s)
            }
        }
    }
}

fn fmt_mono(m: &Mono, n: &Names) -> String {
    // 変数・定数を先に、f(...) を後に（xf(y) のような慣習的な表記）
    let mut parts: Vec<(i32, String)> = Vec::new();
    for (a, e) in m.factors() {
        let is_param = n.param.map_or(false, |pf| pf(a).is_some());
        let s = fmt_atom(a, n);
        let s = if *e == 1 { s } else { format!("{}^{}", s, e) };
        let key = match a {
            _ if is_param => -1,
            Atom::Var(_) => 0,
            Atom::Const(_) => 1,
            Atom::Inv(_) => 2,
            Atom::F(_) => 3,
        };
        parts.push((key, s));
    }
    parts.sort_by(|a, b| a.0.cmp(&b.0));
    let mut out = String::new();
    let mut prev_alpha = false;
    let mut prev_inv = false;
    for (_, s) in parts {
        // 1文字の名前どうしが続くとき（x y → xy）以外で曖昧になりそうなら · を入れる（1/x の後ろも）
        let starts_digit = s.chars().next().map_or(false, |c| c.is_ascii_digit());
        if !out.is_empty() && (starts_digit || prev_inv || (prev_alpha && s.starts_with("1/"))) {
            out.push('·');
        }
        prev_alpha = true;
        prev_inv = s.starts_with("1/");
        out.push_str(&s);
    }
    out
}

/// 項を複雑さの降順に並べて表示する
pub fn fmt_poly(p: &Poly, n: &Names) -> String {
    if p.is_zero() {
        return "0".into();
    }
    let mut terms: Vec<&(Mono, Q)> = p.terms().iter().collect();
    terms.sort_by(|a, b| mono_key(&b.0).cmp(&mono_key(&a.0)).then_with(|| a.0.cmp(&b.0)));
    let mut out = String::new();
    for (i, (m, c)) in terms.iter().enumerate() {
        let neg = c.is_negative();
        let a = c.abs();
        if i == 0 {
            if neg {
                out.push('-');
            }
        } else {
            out.push_str(if neg { " - " } else { " + " });
        }
        if m.is_one() {
            out.push_str(&fmt_q(&a));
        } else if a.is_one() {
            out.push_str(&fmt_mono(m, n));
        } else if a.is_integer() {
            out.push_str(&format!("{}{}", fmt_q(&a), fmt_mono(m, n)));
        } else {
            out.push_str(&format!("({}){}", fmt_q(&a), fmt_mono(m, n)));
        }
    }
    out
}

fn wrap(s: String, p: &Poly) -> String {
    if p.terms().len() > 1 {
        format!("({})", s)
    } else {
        s
    }
}

/// リテラルを「左辺 関係 右辺」の形で表示する。f を含む項を左辺に集める。
pub fn fmt_lit(l: &Lit, n: &Names) -> String {
    let p = l.poly();
    let has_f = |m: &Mono| m.factors().iter().any(|(a, _)| matches!(a, Atom::F(_)));
    let mut left: Vec<(Mono, Q)> = Vec::new();
    let mut right: Vec<(Mono, Q)> = Vec::new();
    let any_f = p.terms().iter().any(|(m, _)| has_f(m));
    if any_f {
        for (m, c) in p.terms() {
            if has_f(m) {
                left.push((m.clone(), c.clone()))
            } else {
                right.push((m.clone(), -c.clone()))
            }
        }
    } else {
        // f を含まない: 最も次数の高い項を左辺に
        let mut ts: Vec<(Mono, Q)> = p.terms().to_vec();
        ts.sort_by(|a, b| mono_key(&b.0).cmp(&mono_key(&a.0)).then_with(|| a.0.cmp(&b.0)));
        let mut it = ts.into_iter();
        if let Some(t) = it.next() {
            left.push(t);
        }
        for (m, c) in it {
            right.push((m, -c));
        }
    }
    let mut lp = Poly::from_terms(left);
    let mut rp = Poly::from_terms(right);
    let rel = l.rel();
    // 左辺の主項の係数が負なら両辺に −1 を掛ける（不等号は向きが変わる）
    let lead_neg = {
        let mut ts: Vec<&(Mono, Q)> = lp.terms().iter().collect();
        ts.sort_by(|a, b| mono_key(&b.0).cmp(&mono_key(&a.0)).then_with(|| a.0.cmp(&b.0)));
        ts.first().map_or(false, |(_, c)| c.is_negative())
    };
    let mut flipped = false;
    if lead_neg {
        lp = lp.neg();
        rp = rp.neg();
        flipped = true;
    }
    let rs = match (rel, flipped) {
        (Rel::Eq, _) => "=",
        (Rel::Ne, _) => "≠",
        (Rel::Gt, false) => ">",
        (Rel::Gt, true) => "<",
        (Rel::Ge, false) => "≥",
        (Rel::Ge, true) => "≤",
    };
    format!("{} {} {}", fmt_poly(&lp, n), rs, fmt_poly(&rp, n))
}

fn lit_has_f(l: &Lit) -> bool {
    l.poly().has_f()
}

/// 節を日本語で表示する
pub fn fmt_clause(c: &Clause, n: &Names) -> String {
    if c.is_false() {
        return "矛盾".into();
    }
    let used: BTreeSet<u32> = c.lits().iter().flat_map(|l| l.poly().vars()).collect();
    let quant = if used.is_empty() {
        String::new()
    } else {
        let vs: Vec<String> = used.iter().map(|&i| var_name(i)).collect();
        format!("任意の実数 {} について ", vs.join(", "))
    };
    let conds: Vec<&Lit> = c.lits().iter().filter(|l| !lit_has_f(l) && l.poly().has_var()).collect();
    let mains: Vec<&Lit> = c.lits().iter().filter(|l| lit_has_f(l) || !l.poly().has_var()).collect();
    let body = if !conds.is_empty() && !mains.is_empty() {
        let cs: Vec<String> = conds.iter().map(|l| fmt_lit(&l.negate(), n)).collect();
        let ms: Vec<String> = mains.iter().map(|l| fmt_lit(l, n)).collect();
        format!("{} ならば {}", cs.join(" かつ "), ms.join(" または "))
    } else {
        let ls: Vec<String> = c.lits().iter().map(|l| fmt_lit(l, n)).collect();
        ls.join(" または ")
    };
    format!("{}{}", quant, body)
}

// ---------------------------------------------------------------------------
// 依存関係

fn premises(r: &Rule) -> Vec<Fact> {
    match r {
        Rule::Axiom | Rule::Hypothesis { .. } | Rule::Trichotomy { .. } | Rule::InvAxiom { .. } | Rule::EqOrNe { .. } => {
            vec![]
        }
        Rule::Congruence { items, .. } => items.iter().map(|(_, f, _)| *f).collect(),
        Rule::Instantiate { premise, .. }
        | Rule::ZeroProduct { premise, .. }
        | Rule::NonzeroFactor { premise, .. }
        | Rule::StrictNe { premise, .. }
        | Rule::SquareRange { premise, .. }
        | Rule::Weaken { premise, .. } => vec![*premise],
        Rule::LinComb { items } => items.iter().map(|(_, f, _)| *f).collect(),
        Rule::Resolve { a, b, .. } | Rule::MulIneq { a, b, .. } => vec![*a, *b],
        Rule::PosComb { ineqs, eqs, .. } => {
            ineqs.iter().map(|(_, f, _)| *f).chain(eqs.iter().map(|(_, f, _)| *f)).collect()
        }
        Rule::Merge { facts, .. } => facts.iter().flatten().copied().collect(),
        Rule::CauchyBounded { additive, bound } => vec![*additive, *bound],
        Rule::AffineXY { premise } | Rule::AffineFF { premise } => vec![*premise],
        Rule::AdditiveSquare { add, sq } => vec![*add, *sq],
        Rule::ImportLemma { premise, .. } => vec![*premise],
    }
}

/// 結論に必要な事実をすべて集める
fn needed_facts(k: &Kernel, roots: &[Fact]) -> BTreeSet<Fact> {
    let mut seen = BTreeSet::new();
    let mut stack: Vec<Fact> = roots.to_vec();
    while let Some(f) = stack.pop() {
        if !seen.insert(f) {
            continue;
        }
        for p in premises(k.fact(f).rule()) {
            stack.push(p);
        }
    }
    seen
}

/// 証明木で「意味のある」枝（閉じた葉・解の葉・その祖先）から、根となる事実を集める
fn proof_roots(k: &Kernel, b: BranchId, out: &mut Vec<Fact>) {
    let r = k.branch(b);
    if let Some(f) = r.contradiction() {
        out.push(f);
        return;
    }
    if let Some((f, _)) = r.solution() {
        out.push(*f);
    }
    if let Some((fs, _)) = r.pw_solution() {
        out.extend(fs.iter().copied());
    }
    if let Some((fs, _)) = r.add_solution() {
        out.extend(fs.iter().copied());
    }
    if let Some(Split::Components { fact }) = r.split() {
        out.push(*fact);
    }
    for &c in r.children() {
        proof_roots(k, c, out);
    }
}

// ---------------------------------------------------------------------------
// 規則ごとの文

struct Ctx<'a> {
    k: &'a Kernel,
    label: BTreeMap<Fact, usize>,
    next: usize,
    out: String,
}

impl<'a> Ctx<'a> {
    fn lbl(&self, f: Fact) -> String {
        match self.label.get(&f) {
            Some(i) => format!("({})", i),
            None => format!("(#{})", f.index()),
        }
    }
    fn subst_str(&self, prem: &Clause, subst: &[Poly], is_axiom: bool) -> String {
        let n = Names::plain();
        if is_axiom {
            let args: Vec<String> = subst.iter().map(|t| fmt_poly(t, &n)).collect();
            return format!("P({})", args.join(", "));
        }
        let used: BTreeSet<u32> = prem.lits().iter().flat_map(|l| l.poly().vars()).collect();
        let mut parts = Vec::new();
        for (i, t) in subst.iter().enumerate() {
            if i as u32 >= prem.nvars() {
                break;
            }
            if *t == Poly::var(i as u32) || !used.contains(&(i as u32)) {
                continue;
            }
            parts.push(format!("{} → {}", var_name(i as u32), fmt_poly(t, &n)));
        }
        if parts.is_empty() {
            "変数名をそのまま".into()
        } else {
            parts.join(", ")
        }
    }
    fn coef_str(&self, c: &Poly, first: bool) -> (bool, String) {
        let n = Names::plain();
        if let Some(q) = c.as_const() {
            let neg = q.is_negative();
            let a = q.abs();
            let s = if a.is_one() { String::new() } else { format!("{}·", fmt_q(&a)) };
            let _ = first;
            return (neg, s);
        }
        // 多項式係数: 主項の符号で向きを決める
        let lead_neg = c.leading_coeff().map_or(false, |q| q.is_negative());
        let cc = if lead_neg { c.neg() } else { c.clone() };
        (lead_neg, format!("{}·", wrap(fmt_poly(&cc, &n), &cc)))
    }
    fn reason(&self, f: Fact) -> String {
        let k = self.k;
        let rec = k.fact(f);
        let n = Names::plain();
        match rec.rule() {
            Rule::Axiom => "与えられた方程式".into(),
            Rule::Hypothesis { .. } => "この場合の仮定".into(),
            Rule::Instantiate { premise, subst } => {
                let is_ax = *premise == k.axiom();
                if is_ax {
                    format!("{} より", self.subst_str(k.clause(*premise), subst, true))
                } else {
                    format!("{} で {} として", self.lbl(*premise), self.subst_str(k.clause(*premise), subst, false))
                }
            }
            Rule::LinComb { items } => {
                if items.len() == 1 {
                    let (c, p, _) = &items[0];
                    if c.as_const().map_or(false, |q| q.is_one()) {
                        return format!("{} を整理して", self.lbl(*p));
                    }
                }
                let mut s = String::new();
                for (i, (c, p, _)) in items.iter().enumerate() {
                    let (neg, cs) = self.coef_str(c, i == 0);
                    if i == 0 {
                        if neg {
                            s.push('−');
                        }
                    } else {
                        s.push_str(if neg { " − " } else { " + " });
                    }
                    s.push_str(&cs);
                    s.push_str(&self.lbl(*p));
                }
                format!("{} を計算して", s)
            }
            Rule::Congruence { base, items } => {
                let mut arg = base.clone();
                for (m, f, li) in items {
                    arg = arg.add(&m.mul(k.clause(*f).lits()[*li].poly()));
                }
                let fs: Vec<String> = items.iter().map(|(_, f, _)| self.lbl(*f)).collect();
                format!(
                    "{} より {} = {} なので、f の値も等しく",
                    fs.join(", "),
                    fmt_poly(&arg, &n),
                    fmt_poly(base, &n)
                )
            }
            Rule::EqOrNe { poly } => format!("{} は 0 か 0 でないかのどちらかなので", fmt_poly(poly, &n)),
            Rule::ZeroProduct { premise, factors, .. } => {
                let fs: Vec<String> = factors.iter().map(|q| format!("({})", fmt_poly(q, &n))).collect();
                format!("{} を {} = 0 と因数分解して", self.lbl(*premise), fs.join(""))
            }
            Rule::NonzeroFactor { premise, factors, .. } => {
                let fs: Vec<String> = factors.iter().map(|q| format!("({})", fmt_poly(q, &n))).collect();
                format!("{} より {} ≠ 0 なので", self.lbl(*premise), fs.join(""))
            }
            Rule::Resolve { a, la, b, .. } => {
                let l = &k.clause(*a).lits()[*la];
                { let _ = l; format!("{} と {} より", self.lbl(*a), self.lbl(*b)) }
            }
            Rule::Trichotomy { .. } => "実数の三分律より".into(),
            Rule::StrictNe { premise, .. } => format!("{} より", self.lbl(*premise)),
            Rule::PosComb { ineqs, eqs, squares, constant } => {
                let mut parts: Vec<String> = Vec::new();
                for (c, f, _) in ineqs {
                    parts.push(if c.is_one() { self.lbl(*f) } else { format!("{}·{}", fmt_q(c), self.lbl(*f)) });
                }
                for (c, f, _) in eqs {
                    let (neg, cs) = self.coef_str(c, false);
                    parts.push(format!("{}{}{}", if neg { "−" } else { "" }, cs, self.lbl(*f)));
                }
                for (c, s) in squares {
                    let sq = format!("({})^2", fmt_poly(s, &n));
                    parts.push(if c.is_one() { sq } else { format!("{}·{}", fmt_q(c), sq) });
                }
                if !constant.is_zero() {
                    parts.push(fmt_q(constant));
                }
                let base = "";
                format!("{} の和をとって{}", parts.join(" + "), base)
            }
            Rule::MulIneq { a, b, .. } => format!("{} と {} を掛け合わせて", self.lbl(*a), self.lbl(*b)),
            Rule::SquareRange { premise, var } => format!(
                "{} は {} を {}^2 の形でだけ含み、0 以上の任意の実数は平方数なので",
                self.lbl(*premise),
                var_name(*var),
                var_name(*var)
            ),
            Rule::InvAxiom { poly } => format!("{} ≠ 0 ならば逆数 {} が存在するので", fmt_poly(poly, &n), fmt_atom(&Atom::Inv(std::rc::Rc::new(poly.clone())), &n)),
            Rule::Weaken { premise, .. } => format!("{} より特に", self.lbl(*premise)),
            Rule::CauchyBounded { additive, bound } => format!(
                "{} より g(x) = f(x) − f(0) は加法的、{} より g は x ≥ 0 で片側に有界なので",
                self.lbl(*additive),
                self.lbl(*bound)
            ),
            Rule::AffineXY { premise } => format!(
                "{} は f(xy + g(x)) = x f(y) + h(x) の型（g, h は x だけの式）であり、この型の解は 1 次関数に限るので",
                self.lbl(*premise)
            ),
            Rule::AdditiveSquare { add, sq } => format!(
                "{} より 0 以上の数どうしで f は加法的、{} より f(x²) = x·f(x)。このとき f は奇関数で、すべての実数で加法的になり、f(x + 1) の場合と比べると f は 1 次関数に限るので",
                self.lbl(*add),
                self.lbl(*sq)
            ),
            Rule::AffineFF { premise } => format!(
                "{} は f(f(x)f(y) + g(x)) = y f(x) + h(x) の型（g, h は x だけの式）であり、この型の解は 1 次関数に限るので（f は全単射になり、逆関数で変数を取り替えると f(xy + g(x)) = x f(y) + h(x) の型に帰着する）",
                self.lbl(*premise)
            ),
            Rule::ImportLemma { premise, lemma } => format!(
                "{} は方程式 {} であり、下の【補題】より、解は次に限るので",
                self.lbl(*premise),
                fmt_equation(lemma)
            ),
            Rule::Merge { facts, .. } => {
                let fs: Vec<String> = facts.iter().flatten().map(|f| self.lbl(*f)).collect();
                format!("{} より、どの場合でも成り立つので", fs.join(", "))
            }
        }
    }

    /// 変数名の付け替えだけの例化や、係数 1 つの自明な一次結合なら、その前提を返す（証明文では省略）
    fn alias_of(&self, f: Fact) -> Option<Fact> {
        let k = self.k;
        let rec = k.fact(f);
        match rec.rule() {
            Rule::Instantiate { premise, subst } if *premise != k.axiom() => {
                let pc = k.clause(*premise);
                let used: BTreeSet<u32> = pc.lits().iter().flat_map(|l| l.poly().vars()).collect();
                let mut targets = BTreeSet::new();
                for &i in &used {
                    let t = subst.get(i as usize)?;
                    // 変数名が変わらない（恒等的な）代入だけを省略する。名前が変わると前提の文と食い違うため
                    if *t != Poly::var(i) {
                        return None;
                    }
                    targets.insert(i);
                }
                if rec.clause().lits().len() == pc.lits().len() {
                    Some(*premise)
                } else {
                    None
                }
            }
            Rule::LinComb { items } if items.len() == 1 => {
                let (c, p, _) = &items[0];
                if c.as_const().map_or(false, |q| !q.is_zero()) && k.clause(*p).lits() == rec.clause().lits() {
                    Some(*p)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn emit(&mut self, f: Fact, indent: &str) {
        if self.label.contains_key(&f) {
            return;
        }
        if let Some(p) = self.alias_of(f) {
            self.emit(p, indent);
            let l = self.label[&p];
            self.label.insert(f, l);
            return;
        }
        let i = self.next;
        self.next += 1;
        self.label.insert(f, i);
        let reason = self.reason(f);
        let stmt = fmt_clause(self.k.clause(f), &Names::plain());
        let _ = writeln!(self.out, "{}({}) {}: {}", indent, i, reason, stmt);
    }
}

/// 解の族の表示（パラメータは c, c1, c2, …）
pub fn fmt_family(fam: &fe_kernel::Family) -> String {
    let np = fam.params().len();
    let name = move |i: usize| if np == 1 { "c".to_string() } else { format!("c{}", i + 1) };
    let pf = move |a: &Atom| match a {
        Atom::Var(i) if *i >= 2 => Some(name((*i - 2) as usize)),
        _ => None,
    };
    let n = Names { param: Some(&pf) };
    let mut s = format!("f(x) = {}", fmt_poly(fam.template(), &n));
    if np > 0 {
        let ps: Vec<String> = (0..np).map(name).collect();
        s.push_str(&format!("（{} は任意の実数）", ps.join(", ")));
    }
    s
}

/// 加法的な族の表示: f(x) = A(x) + g(x)（A は任意の加法的関数、パラメータは c, c1, …）
pub fn fmt_add_family(fam: &fe_kernel::AddFamily) -> String {
    let np = fam.params().len();
    let name = move |i: usize| if np == 1 { "c".to_string() } else { format!("c{}", i + 1) };
    let pf = move |a: &Atom| match a {
        Atom::Var(i) if *i >= 2 => Some(name((*i - 2) as usize)),
        _ => None,
    };
    let n = Names { param: Some(&pf) };
    let t = fam.template();
    let mut s = if t.is_zero() {
        "f(x) = A(x)".to_string()
    } else {
        let g = fmt_poly(t, &n);
        if g.starts_with('-') {
            format!("f(x) = A(x) - {}", &g[1..].trim_start())
        } else {
            format!("f(x) = A(x) + {}", g)
        }
    };
    let mut notes = vec![match fam.kind() {
        fe_kernel::AddKind::Free => "A は任意の加法的関数".to_string(),
        fe_kernel::AddKind::Involution => "A は A(A(x)) = x を満たす任意の加法的関数".to_string(),
        fe_kernel::AddKind::Projection => "A は A(A(x)) = A(x) を満たす任意の加法的関数".to_string(),
    }];
    if np > 0 {
        let ps: Vec<String> = (0..np).map(name).collect();
        notes.push(format!("{} は任意の実数", ps.join(", ")));
    }
    s.push_str(&format!("（{}）", notes.join("、")));
    s
}

/// 多項式の族 b のすべての関数が多項式の族 a に含まれるか（表示で重複を省くため。証明には使わない）。
/// a の各パラメータが x のある 1 つのべきの係数としてだけ 1 次で現れる（c、cx、x + c、c₁x + c₂ など）とき、
/// b − a(パラメータ = 0) の x の各べきの係数を、そのべきのパラメータに割り当てられれば含まれる。
pub fn family_subsumes(a: &fe_kernel::Family, b: &fe_kernel::Family) -> bool {
    if a.template() == b.template() && a.params().len() == b.params().len() {
        return true;
    }
    let na = a.params().len() as u32;
    if na == 0 {
        return false;
    }
    let xdeg = |m: &fe_kernel::Mono| m.factors().iter().filter(|(t, _)| *t == Atom::Var(0)).map(|(_, e)| *e).sum::<u32>();
    // a のパラメータ j → (x の指数, 係数)
    let mut pos: Vec<Option<(u32, Q)>> = vec![None; na as usize];
    for (m, c) in a.template().terms() {
        let ps: Vec<&(Atom, u32)> = m.factors().iter().filter(|(t, _)| matches!(t, Atom::Var(i) if *i >= 2)).collect();
        if ps.is_empty() {
            continue;
        }
        if ps.len() != 1 || ps[0].1 != 1 || m.factors().iter().any(|(t, _)| !matches!(t, Atom::Var(_))) {
            return false;
        }
        let j = match ps[0].0 {
            Atom::Var(i) => (i - 2) as usize,
            _ => return false,
        };
        if pos[j].is_some() {
            return false;
        }
        pos[j] = Some((xdeg(m), c.clone()));
    }
    // b のパラメータは別の番号にずらす
    let mut sb = vec![Poly::var(0), Poly::var(1)];
    for k in 0..b.params().len() as u32 {
        sb.push(Poly::var(100 + k));
    }
    let b2 = b.template().subst_vars(&sb);
    let mut z = vec![Poly::var(0), Poly::var(1)];
    for _ in 0..na {
        z.push(Poly::zero());
    }
    let d = b2.sub(&a.template().subst_vars(&z));
    let mut exps: Vec<u32> = d.terms().iter().map(|(m, _)| xdeg(m)).collect();
    exps.sort();
    exps.dedup();
    let mut used = vec![false; na as usize];
    for e in exps {
        match (0..na as usize).find(|&j| !used[j] && matches!(&pos[j], Some((pe, _)) if *pe == e)) {
            Some(j) => used[j] = true,
            None => return false,
        }
    }
    true
}

/// 表示用: 他の族に含まれる多項式の族を省いた一覧（同じ族どうしは先のものを残す）
pub fn display_families(fams: &[fe_kernel::Family]) -> Vec<&fe_kernel::Family> {
    let mut out = Vec::new();
    for (i, f) in fams.iter().enumerate() {
        let dominated = fams.iter().enumerate().any(|(j, g)| j != i && family_subsumes(g, f) && !(family_subsumes(f, g) && j > i));
        if !dominated {
            out.push(f);
        }
    }
    out
}

/// 多項式の族 g'(x; p̄) のすべての関数が加法的な族 {A + t} に含まれるか（表示で重複を省くため）。
/// t = 0 なら g' が x について斉次 1 次（ax の形）、t が単独のパラメータ c なら g' が x の 1 次以下なら含まれる。
/// 区間 (lo, hi) 上の値の関数（x の多項式、次数 1 以下）が任意の区間の制約を満たすか（判定できなければ false）
fn piece_within(g: &Poly, pc: &fe_kernel::ArbPiece, lo: &Option<Q>, hi: &Option<Q>) -> bool {
    use fe_kernel::ArbPiece;
    use num_traits::{Signed, Zero};
    match pc {
        ArbPiece::Fixed(h) => h == g,
        ArbPiece::Free => true,
        ArbPiece::Choice(a, b) => a == g || b == g,
        ArbPiece::NonNeg | ArbPiece::NonPos => {
            // g = a·x + c（パラメータなし）だけを扱う
            let mut a = Q::zero();
            let mut c = Q::zero();
            for (m, k) in g.terms() {
                if m.is_one() {
                    c = k.clone();
                } else if m.factors() == [(Atom::Var(0), 1)] {
                    a = k.clone();
                } else {
                    return false;
                }
            }
            let sgn = if matches!(pc, ArbPiece::NonNeg) { Q::one() } else { -Q::one() };
            // 区間の両端（無限なら傾きの符号）で s·g ≥ 0 なら区間全体で s·g ≥ 0（1 次式なので）
            let ok_end = |e: &Option<Q>, toward_minus: bool| -> bool {
                match e {
                    Some(t) => !((&a * t + &c) * &sgn).is_negative(),
                    None => {
                        let slope = if toward_minus { -a.clone() } else { a.clone() } * &sgn;
                        slope.is_positive() || (slope.is_zero() && !(&c * &sgn).is_negative())
                    }
                }
            };
            ok_end(lo, true) && ok_end(hi, false)
        }
    }
}

/// 多項式の族（パラメータなし）が任意の区間をもつ族に含まれるか（表示で省くため）
pub fn family_in_arb(fam: &fe_kernel::Family, arb: &fe_kernel::ArbFamily) -> bool {
    if !fam.params().is_empty() {
        return false;
    }
    let g = fam.template();
    arb.pieces().iter().enumerate().all(|(i, pc)| {
        let (lo, hi) = arb.interval(i);
        if i % 2 == 1 {
            let b = Poly::constant(lo.clone().unwrap());
            match pc {
                fe_kernel::ArbPiece::Fixed(h) => h.subst_vars(&[b.clone()]) == g.subst_vars(&[b]),
                _ => false,
            }
        } else {
            piece_within(g, pc, &lo, &hi)
        }
    })
}

/// 区分的な族が任意の区間をもつ族に含まれるか（区切り点が同じときだけ判定する）
pub fn pw_in_arb(pw: &fe_kernel::PwFamily, arb: &fe_kernel::ArbFamily) -> bool {
    if pw.breaks() != arb.breaks() {
        return false;
    }
    arb.pieces().iter().enumerate().all(|(i, pc)| {
        let (lo, hi) = arb.interval(i);
        let g = &pw.pieces()[i];
        if i % 2 == 1 {
            let b = Poly::constant(lo.clone().unwrap());
            match pc {
                fe_kernel::ArbPiece::Fixed(h) => h.subst_vars(&[b.clone()]) == g.subst_vars(&[b]),
                _ => false,
            }
        } else {
            piece_within(g, pc, &lo, &hi)
        }
    })
}

pub fn subsumed_by_additive(fam: &fe_kernel::Family, add: &fe_kernel::AddFamily) -> bool {
    let xdeg = |m: &fe_kernel::Mono| m.factors().iter().filter(|(a, _)| *a == Atom::Var(0)).map(|(_, e)| *e).sum::<u32>();
    let terms = fam.template().terms();
    let t = add.template();
    if add.kind() != fe_kernel::AddKind::Free {
        // 条件つき: パラメータのない ax で、a² = 1（対合）または a² = a（射影）
        if !fam.params().is_empty() || !terms.iter().all(|(m, _)| xdeg(m) == 1 && m.factors().len() == 1) {
            return false;
        }
        let a = terms.first().map(|(_, c)| c.clone()).unwrap_or_else(|| Q::from_integer(0.into()));
        return match add.kind() {
            fe_kernel::AddKind::Involution => a.clone() * a.clone() == Q::from_integer(1.into()),
            _ => a.clone() * a.clone() == a,
        };
    }
    if t.is_zero() {
        terms.iter().all(|(m, _)| xdeg(m) == 1)
    } else if *t == Poly::var(2) {
        terms.iter().all(|(m, _)| xdeg(m) <= 1)
    } else {
        false
    }
}

/// 加法的な族を代入した両辺（A を有理数係数の和について展開したもの。A(m) を "A(m)" と表示する）
fn additive_sides(k: &Kernel, fam: &fe_kernel::AddFamily) -> (String, String) {
    let (l, r) = k.equation();
    let t = fam.template().clone();
    let np = fam.params().len() as u32;
    let apply = |p: &Poly| {
        p.transform(&mut |a| match a {
            Atom::F(arg) => {
                let mut out = Poly::zero();
                for (m, c) in arg.terms() {
                    let inner = match m.factors() {
                        [(Atom::F(u), 1)] => Some((**u).clone()),
                        _ => None,
                    };
                    let term = match (fam.kind(), inner) {
                        (fe_kernel::AddKind::Involution, Some(u)) => u,
                        (fe_kernel::AddKind::Projection, Some(u)) => Poly::f(u),
                        _ => Poly::f(Poly::mono(m.clone(), Q::from_integer(1.into()))),
                    };
                    out = out.add(&term.scale(c));
                }
                let mut s = vec![(*arg).clone(), Poly::var(1)];
                for i in 0..np {
                    s.push(Poly::var(2 + i));
                }
                out.add(&t.subst_vars(&s))
            }
            other => Poly::from_atom(other),
        })
    };
    let params = fam.params().len();
    let pn = move |i: u32| if params == 1 { "c".to_string() } else { format!("c{}", i + 1) };
    let pf = move |a: &Atom| match a {
        Atom::Var(i) if *i >= 2 => Some(pn(i - 2)),
        _ => None,
    };
    let n = Names { param: Some(&pf) };
    // 展開後の f はすべて A を表す
    let show = |p: &Poly| fmt_poly(p, &n).replace("f(", "A(");
    (show(&apply(l)), show(&apply(r)))
}

/// 加法的な族が解であることの確認文（検算・病的な解の存在の説明に使う。正しさは検証核が確認済み）
fn additive_check(k: &Kernel, fam: &fe_kernel::AddFamily) -> String {
    let (l, r) = additive_sides(k, fam);
    let (rule, example) = match fam.kind() {
        fe_kernel::AddKind::Free => ("", "ハメル基底を使う"),
        fe_kernel::AddKind::Involution => ("、A(A(t)) = t", "ハメル基底を 2 つに分け、一方で t ↦ t、他方で t ↦ −t とする"),
        fe_kernel::AddKind::Projection => ("、A(A(t)) = A(t)", "ハメル基底を 2 つに分け、一方で t ↦ t、他方で t ↦ 0 とする"),
    };
    format!(
        "{} を代入し、A(有理数係数の和) = 有理数係数の A の和{} で展開すると 左辺 = {}、右辺 = {} で一致する。\n\
         {}と ax の形でない A も作れるので、これらには病的な解が含まれる。",
        fmt_add_family(fam),
        rule,
        l,
        r,
        example
    )
}

/// 解の集合は未確定だが、任意の加法的関数を含む族が解であること（病的な解の存在）の報告
pub fn render_additive_exist(k: &Kernel, fam: &fe_kernel::AddFamily) -> String {
    format!("【病的な解の存在】\n{}\nほかに解があるかどうかは示せていない。\n", additive_check(k, fam))
}

/// 任意の区間をもつ族の表示（例: 「f(x) = x（x ≥ 0）、x < 0 では 0 以上の任意の値」）
pub fn fmt_arb(fam: &fe_kernel::ArbFamily) -> String {
    use fe_kernel::ArbPiece;
    let n = Names::plain();
    let br = fam.breaks();
    let pcs = fam.pieces();
    let desc = |p: &ArbPiece| -> (bool, String) {
        match p {
            ArbPiece::Fixed(g) => (true, fmt_poly(g, &n)),
            ArbPiece::Free => (false, "任意の値".into()),
            ArbPiece::NonNeg => (false, "0 以上の任意の値".into()),
            ArbPiece::NonPos => (false, "0 以下の任意の値".into()),
            ArbPiece::Choice(a, b) => (false, format!("各点で {} か {} のどちらか（点ごとに任意に選ぶ）", fmt_poly(a, &n), fmt_poly(b, &n))),
        }
    };
    let mut fixed: Vec<String> = Vec::new();
    let mut free: Vec<String> = Vec::new();
    // 区切り点の値が隣の固定の区間の式と一致するなら、その区間に含めて「x ≥ b」「x ≤ b」と書く
    let mut merged: Vec<bool> = vec![false; pcs.len()];
    let mut closed_side: Vec<Option<&str>> = vec![None; pcs.len()];
    for k in 0..br.len() {
        let pi = 2 * k + 1;
        if let ArbPiece::Fixed(pv) = &pcs[pi] {
            let bp = Poly::constant(br[k].clone());
            let v = pv.subst_vars(&[bp.clone()]);
            if let ArbPiece::Fixed(g) = &pcs[pi + 1] {
                if g.subst_vars(&[bp.clone()]) == v && closed_side[pi + 1].is_none() {
                    merged[pi] = true;
                    closed_side[pi + 1] = Some("left");
                    continue;
                }
            }
            if let ArbPiece::Fixed(g) = &pcs[pi - 1] {
                if g.subst_vars(&[bp]) == v && closed_side[pi - 1].is_none() {
                    merged[pi] = true;
                    closed_side[pi - 1] = Some("right");
                }
            }
        }
    }
    for (i, p) in pcs.iter().enumerate() {
        if merged[i] {
            continue;
        }
        let (lo, hi) = fam.interval(i);
        let (lt, gt) = match closed_side[i] {
            Some("left") => ("≤", "≥"),
            Some("right") => ("≤", "≥"),
            _ => ("<", ">"),
        };
        let (lop, hop) = match closed_side[i] {
            Some("left") => (gt, "<"),
            Some("right") => (">", lt),
            _ => (gt, lt),
        };
        let cond = match (&lo, &hi) {
            (Some(a), Some(b)) if a == b => format!("x = {}", fmt_q(a)),
            (None, Some(b)) => format!("x {} {}", hop, fmt_q(b)),
            (Some(a), None) => format!("x {} {}", lop, fmt_q(a)),
            (Some(a), Some(b)) => format!("{} {} x {} {}", fmt_q(a), if lop == "≥" { "≤" } else { "<" }, hop, fmt_q(b)),
            (None, None) => "すべての x".into(),
        };
        let (is_fixed, d) = desc(p);
        if is_fixed {
            fixed.push(format!("{}（{}）", d, cond));
        } else {
            let sp = if d.chars().next().map_or(false, |c| c.is_ascii_alphanumeric()) { " " } else { "" };
            free.push(format!("{} では{}{}", cond, sp, d));
        }
    }
    let _ = br;
    format!("f(x) = {}、{}", fixed.join("、"), free.join("、"))
}

/// 任意の区間をもつ族による病的な解の存在の説明（検証核の検証 verify_arbitrary の内容）
pub fn render_arb_exist(_k: &Kernel, fam: &fe_kernel::ArbFamily) -> String {
    format!(
        "【病的な解の存在】\n{} は、任意に選べる区間での値をどのように選んでも解である。\n\
         x, y の符号（負・0・正）で場合を分け、f の各引数が属する区間を符号から決めて（決まらなければ区間ごとに分けて）f を展開し、\
         任意に選べる区間での値 f(t) は引数 t ごとに独立な記号（0 以上・0 以下などの制約つき、各点の選択は 2 通りに分ける）として、\
         どの場合も左辺と右辺が恒等的に一致することを確かめた。\n\
         任意に選べる点は無数にあるので、この族は区分的な式で書けない解（各点の選び方がルベーグ可測でないものなど）を含む。\n\
         ほかに解があるかどうかは示せていない。\n",
        fmt_arb(fam)
    )
}

/// 有理数と無理数で式を変える族の表示
pub fn fmt_qsplit(fam: &fe_kernel::QsFamily) -> String {
    let n = Names::plain();
    format!("f(x) = {}（x が有理数）, {}（x が無理数）", fmt_poly(fam.g_rat(), &n), fmt_poly(fam.g_irr(), &n))
}

/// 有理数と無理数で式を変える族による病的な解の存在の説明（検証核の検証 verify_rational_split の内容）
pub fn render_qsplit_exist(_k: &Kernel, fam: &fe_kernel::QsFamily) -> String {
    format!(
        "【病的な解の存在】\n{} は解である。\n\
         各変数が有理数か無理数かで場合を分け、f の各引数が有理数か無理数かを内側から決めて f を展開すると、\
         どの場合も左辺と右辺が一致する。\n\
         有理数と無理数で式が異なるので、この関数は多項式や区分的な式では書けない。\n\
         ほかに解があるかどうかは示せていない。\n",
        fmt_qsplit(fam)
    )
}

/// 区分的な族の表示（区切り点の値が隣の区間の式と一致すればまとめる）
pub fn fmt_pw(fam: &fe_kernel::PwFamily) -> String {
    let n = Names::plain();
    let br = fam.breaks();
    let pcs = fam.pieces();
    let mut parts: Vec<String> = Vec::new();
    let qs = |q: &Q| fmt_q(q);
    for (k, b) in br.iter().enumerate() {
        let left = &pcs[2 * k];
        let pt = &pcs[2 * k + 1];
        let right = &pcs[2 * k + 2];
        let bp = Poly::constant(b.clone());
        let pv = pt.subst_vars(&[bp.clone()]);
        let lo = if k == 0 { None } else { Some(br[k - 1].clone()) };
        // 左の区間
        let lcond = match &lo {
            None => format!("x < {}", qs(b)),
            Some(l) => format!("{} < x < {}", qs(l), qs(b)),
        };
        if k == 0 || true {
            let left_closed = left.subst_vars(&[bp.clone()]) == pv;
            let right_closed = right.subst_vars(&[bp.clone()]) == pv;
            if k == 0 {
                if left_closed && !right_closed {
                    parts.push(format!("{}（x ≤ {}）", fmt_poly(left, &n), qs(b)));
                } else {
                    parts.push(format!("{}（{}）", fmt_poly(left, &n), lcond));
                }
            }
            if !left_closed && !right_closed {
                parts.push(format!("{}（x = {}）", fmt_poly(&pv, &n), qs(b)));
            }
            let hi = br.get(k + 1);
            let rcond = match (hi, right_closed && !(left_closed && !right_closed) && !(left_closed && right_closed && false)) {
                (None, true) => format!("x ≥ {}", qs(b)),
                (None, false) => format!("x > {}", qs(b)),
                (Some(h), true) => format!("{} ≤ x < {}", qs(b), qs(h)),
                (Some(h), false) => format!("{} < x < {}", qs(b), qs(h)),
            };
            let rc = if left_closed && !right_closed { rcond.replace('≥', ">").replace("≤ x", "< x") } else { rcond };
            parts.push(format!("{}（{}）", fmt_poly(right, &n), rc));
        }
    }
    format!("f(x) = {}", parts.join(", "))
}

/// 方程式の表示
pub fn fmt_equation(k: &Kernel) -> String {
    let (l, r) = k.equation();
    let n = Names::plain();
    format!("{} = {}", fmt_poly(l, &n), fmt_poly(r, &n))
}

/// 族を方程式に代入した両辺（検算の表示用。正しさは検証核が確認済み）
fn substituted_sides(k: &Kernel, fam: &fe_kernel::Family) -> (Poly, Poly) {
    let (l, r) = k.equation();
    let t = fam.template().clone();
    let np = fam.params().len() as u32;
    let apply = |p: &Poly| {
        p.transform(&mut |a| match a {
            Atom::F(arg) => {
                let mut s = vec![(*arg).clone(), Poly::var(1)];
                for i in 0..np {
                    s.push(Poly::var(2 + i));
                }
                t.subst_vars(&s)
            }
            other => Poly::from_atom(other),
        })
    };
    (apply(l), apply(r))
}

fn render_branch(ctx: &mut Ctx, b: BranchId, need: &BTreeSet<Fact>, depth: usize, path: &str) {
    let k = ctx.k;
    let indent = "  ".repeat(depth);
    let r = k.branch(b);
    // この枝の必要な事実（作られた順）
    let mine: Vec<Fact> = need.iter().copied().filter(|f| k.fact(*f).branch() == b).collect();
    for f in &mine {
        if matches!(k.fact(*f).rule(), Rule::Hypothesis { .. }) {
            continue;
        }
        // 前提が先に出ていることを保証（祖先の枝で未出力のものがあれば先に出す）
        ctx.emit(*f, &indent);
    }
    if let Some(f) = r.contradiction() {
        let _ = writeln!(ctx.out, "{}{} は矛盾なので、この場合は起こらない。", indent, ctx.lbl(f));
        return;
    }
    if let Some((f, fam)) = r.solution() {
        let _ = writeln!(ctx.out, "{}{} より、この場合は {} である。", indent, ctx.lbl(*f), fmt_family(fam));
        return;
    }
    if let Some((fs, fam)) = r.pw_solution() {
        let ls: Vec<String> = fs.iter().map(|f| ctx.lbl(*f)).collect();
        let _ = writeln!(ctx.out, "{}{} より、この場合は {} である。", indent, ls.join(", "), fmt_pw(fam));
        return;
    }
    if let Some((fs, fam)) = r.add_solution() {
        let what = if fam.g().is_zero() {
            "f は加法的".to_string()
        } else {
            format!("f(x) - ({}) は加法的", fmt_poly(fam.g(), &Names::plain()))
        };
        let mut reason = format!("{} より {}", ctx.lbl(fs[0]), what);
        if let Some(c) = fs.get(1) {
            reason.push_str(&format!("、{} より {}", ctx.lbl(*c), fmt_clause(k.clause(*c), &Names::plain())));
        }
        let _ = writeln!(ctx.out, "{}{}なので、この場合は {} である。", indent, reason, fmt_add_family(fam));
        return;
    }
    let children = r.children().to_vec();
    if children.is_empty() {
        let _ = writeln!(ctx.out, "{}この場合は未解決。", indent);
        return;
    }
    let n = Names::plain();
    match r.split() {
        Some(Split::Components { fact }) => {
            let _ = writeln!(ctx.out, "{}{} より、次の {} つの場合に分ける。", indent, ctx.lbl(*fact), children.len());
        }
        Some(Split::ExcludedMiddle { clause, .. }) => {
            let _ = writeln!(ctx.out, "{}「{}」が成り立つかどうかで場合を分ける。", indent, fmt_clause(clause, &n));
        }
        None => {}
    }
    for (i, &c) in children.iter().enumerate() {
        let cp = if path.is_empty() { format!("{}", i + 1) } else { format!("{}-{}", path, i + 1) };
        let hyps: Vec<Fact> = k.branch(c).hyps().to_vec();
        let mut hs = Vec::new();
        for h in &hyps {
            let j = ctx.next;
            ctx.next += 1;
            ctx.label.insert(*h, j);
            hs.push(format!("({}) {}", j, fmt_clause(k.clause(*h), &n)));
        }
        let extra = match r.split() {
            Some(Split::ExcludedMiddle { consts, .. }) if i == 1 && !consts.is_empty() => {
                let cs: Vec<String> = consts.iter().map(|&c| const_name(c)).collect();
                format!("そうでない場合。ある実数 {} について", cs.join(", "))
            }
            Some(Split::ExcludedMiddle { .. }) if i == 1 => "そうでない場合。".to_string(),
            _ => String::new(),
        };
        let _ = writeln!(ctx.out, "{}【場合 {}】{}{}", indent, cp, extra, hs.join("、"));
        if k.is_closed(c) && k.branch(c).contradiction().is_none() && k.branch(c).children().is_empty() {
            let _ = writeln!(ctx.out, "{}  この場合は起こらない。", indent);
        }
        render_branch(ctx, c, need, depth + 1, &cp);
    }
    // 子から合流した事実など、まだ出していない必要な事実
    for f in &mine {
        ctx.emit(*f, &indent);
    }
}

/// 完全な証明文（または部分結果の報告）を生成する
pub fn render(k: &Kernel, concl: &Conclusion) -> String {
    let mut roots = Vec::new();
    proof_roots(k, ROOT, &mut roots);
    let need = needed_facts(k, &roots);
    let mut ctx = Ctx { k, label: BTreeMap::new(), next: 1, out: String::new() };
    let _ = writeln!(ctx.out, "方程式: {}（任意の実数 x, y について）", fmt_equation(k));
    let _ = writeln!(ctx.out, "この主張を P(x, y) と書く。");
    ctx.label.insert(k.axiom(), 0);
    ctx.label.remove(&k.axiom());
    ctx.emit(k.axiom(), "");
    if concl.complete {
        let mut fams: Vec<String> = display_families(&concl.families)
            .into_iter()
            .filter(|f| !concl.add_families.iter().any(|a| subsumed_by_additive(f, a)))
            .map(fmt_family)
            .collect();
        fams.extend(concl.pw_families.iter().map(fmt_pw));
        fams.extend(concl.add_families.iter().map(fmt_add_family));
        if fams.is_empty() {
            let _ = writeln!(ctx.out, "\n【結論】解は存在しない。");
        } else {
            let _ = writeln!(ctx.out, "\n【結論】解は次のものに限る: {}", fams.join("、 "));
        }
    }
    let _ = writeln!(ctx.out, "\n【証明】");
    render_branch(&mut ctx, ROOT, &need, 0, "");
    if !concl.families.is_empty() || !concl.pw_families.is_empty() || !concl.add_families.is_empty() {
        let _ = writeln!(ctx.out, "\n【検算】");
        for fam in &concl.add_families {
            let _ = writeln!(ctx.out, "{}", additive_check(k, fam));
        }
        for fam in &concl.pw_families {
            let _ = writeln!(
                ctx.out,
                "{} は、x, y の符号と各 f の引数の範囲で場合を分けて代入すると、どの場合も両辺が一致する。",
                fmt_pw(fam)
            );
        }
        let n = Names::plain();
        for fam in display_families(&concl.families).into_iter().filter(|f| !concl.add_families.iter().any(|a| subsumed_by_additive(f, a))) {
            let (l, r) = substituted_sides(k, fam);
            let params = fam.params().len();
            let pn = |i: u32| if params == 1 { "c".to_string() } else { format!("c{}", i + 1) };
            let pf = |a: &Atom| match a {
                Atom::Var(i) if *i >= 2 => Some(pn(i - 2)),
                _ => None,
            };
            let np = Names { param: Some(&pf) };
            let _ = n;
            let _ = writeln!(
                ctx.out,
                "{} を代入すると 左辺 = {}、右辺 = {} で一致する。",
                fmt_family(fam),
                fmt_poly(&l, &np),
                fmt_poly(&r, &np)
            );
        }
    }
    // 使った補題の証明
    let mut lemmas: Vec<std::rc::Rc<Kernel>> = Vec::new();
    for f in &need {
        if let Rule::ImportLemma { lemma, .. } = k.fact(*f).rule() {
            if !lemmas.iter().any(|l| std::rc::Rc::ptr_eq(l, lemma)) {
                lemmas.push(lemma.clone());
            }
        }
    }
    for (i, l) in lemmas.iter().enumerate() {
        let _ = writeln!(ctx.out, "\n【補題 {}】", i + 1);
        let c = l.conclude();
        ctx.out.push_str(&render(l, &c));
    }
    ctx.out
}

/// 根で証明済みの事実（とその導出）を列挙する（部分結果・未解決の報告用）
pub fn render_facts(k: &Kernel, facts: &[Fact]) -> String {
    let need = needed_facts(k, facts);
    let mut ctx = Ctx { k, label: BTreeMap::new(), next: 1, out: String::new() };
    let _ = writeln!(ctx.out, "方程式: {}（任意の実数 x, y について）。この主張を P(x, y) と書く。", fmt_equation(k));
    for f in need {
        if k.fact(f).branch() == ROOT {
            ctx.emit(f, "");
        }
    }
    ctx.out
}
