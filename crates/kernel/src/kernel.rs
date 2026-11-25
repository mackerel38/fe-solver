//! 検証核の本体: 証明済みの事実 (`Fact`) はこのモジュールの推論規則だけが作れる。
//!
//! # 強制の仕組み
//! - `Fact` のフィールドは非公開で、公開コンストラクタはない。クレート外（探索部）からは
//!   `Kernel` の推論規則メソッドの戻り値としてしか `Fact` を得られない（Rust のモジュール可視性で強制）。
//! - 事実の内容（節）は `Kernel` の非公開フィールドに保存され、外部へは `&` 参照（読み取り専用）でしか渡さない。
//! - 各 `Fact` は作った `Kernel` の id を持ち、別の `Kernel` の事実を混ぜると拒否する。
//! - このクレートは `#![forbid(unsafe_code)]`。探索部のクレートも同様に unsafe を禁止している。
//!
//! # 論理
//! 未知関数 f: R → R が「与えられた方程式（公理）」を満たすとする。証明は場合分けの木で、
//! 各ノード（枝, branch）は仮定（場合分けで加わった節）と、その枝で導入された定数を持つ。
//! 枝 b の事実は「公理と、根から b までのすべての仮定のもとで成り立つ節」である。
//! 祖先の枝の事実は子孫の枝でも使える。場合分けは常に網羅的なので、
//! 「すべての葉が矛盾で閉じるか、解の形が決まっている」なら、解はそれらの形に限られる。
//!
//! 定数 (`Const`) は場合分け（排中律）で導入され、導入した枝とその子孫でのみ使える（スコープ検査）。

use crate::clause::{Clause, Lit, Rel};
use crate::piecewise::PwFamily;
use crate::poly::{Atom, Poly, Q};
use num_traits::{One, Signed, Zero};
use std::collections::BTreeSet;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_KERNEL_ID: AtomicU64 = AtomicU64::new(1);

/// 証明済みの事実への不透明なハンドル。検証核の推論規則だけが作れる。
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Fact {
    kernel: u64,
    idx: u32,
}

impl Fact {
    /// 導出の順番（表示用）
    pub fn index(&self) -> usize {
        self.idx as usize
    }
}

/// 場合分けの木の枝。番号は検証核が割り当てる（偽造しても範囲検査と祖先検査で弾かれる）。
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct BranchId(pub u32);

pub const ROOT: BranchId = BranchId(0);

/// 導出規則の記録（証明文の生成に使う。内容は検証核が書き込み、外部からは読むだけ）
#[derive(Clone, Debug)]
pub enum Rule {
    Axiom,
    Hypothesis { parent: BranchId, child_index: usize },
    Instantiate { premise: Fact, subst: Vec<Poly> },
    LinComb { items: Vec<(Poly, Fact, usize)> },
    Congruence { base: Poly, items: Vec<(Poly, Fact, usize)> },
    EqOrNe { poly: Poly },
    ZeroProduct { premise: Fact, lit: usize, factors: Vec<Poly> },
    NonzeroFactor { premise: Fact, lit: usize, factors: Vec<Poly>, index: usize },
    Resolve { a: Fact, la: usize, b: Fact, lb: usize },
    Trichotomy { poly: Poly },
    StrictNe { premise: Fact, lit: usize },
    PosComb { ineqs: Vec<(Q, Fact, usize)>, eqs: Vec<(Poly, Fact, usize)>, squares: Vec<(Q, Poly)>, constant: Q },
    MulIneq { a: Fact, la: usize, b: Fact, lb: usize },
    SquareRange { premise: Fact, var: u32 },
    InvAxiom { poly: Poly },
    Weaken { premise: Fact, extra: Vec<Lit> },
    Merge { parent: BranchId, facts: Vec<Option<Fact>> },
    CauchyBounded { additive: Fact, bound: Fact },
    ImportLemma { premise: Fact, lemma: std::rc::Rc<Kernel> },
}

#[derive(Clone, Debug)]
pub struct FactRec {
    clause: Clause,
    branch: BranchId,
    rule: Rule,
}

impl FactRec {
    pub fn clause(&self) -> &Clause {
        &self.clause
    }
    pub fn branch(&self) -> BranchId {
        self.branch
    }
    pub fn rule(&self) -> &Rule {
        &self.rule
    }
}

/// 枝の分け方
#[derive(Clone, Debug)]
pub enum Split {
    /// 変数を共有しないリテラルの組への分割: ∀x̄.(A(x̄₁) ∨ B(x̄₂)) ⇔ (∀x̄₁.A) ∨ (∀x̄₂.B)
    Components { fact: Fact },
    /// 排中律: (∀x̄. C(x̄)) ∨ (∃ā. ¬C(ā))。後者では新しい定数 ā を導入する
    ExcludedMiddle { clause: Clause, consts: Vec<u32> },
}

#[derive(Clone, Debug)]
pub struct BranchRec {
    parent: Option<BranchId>,
    depth: u32,
    children: Vec<BranchId>,
    split: Option<Split>,
    hyps: Vec<Fact>,
    contradiction: Option<Fact>,
    solution: Option<(Fact, Family)>,
    /// 区分的な解の確定（区間ごとの事実と族）
    pw_solution: Option<(Vec<Fact>, PwFamily)>,
    /// 取り消された場合分けの子孫（以後どこでも使えない）
    dead: bool,
    /// この枝の場合分けから Merge で事実を持ち上げたか（取り消し不可になる）
    merged: bool,
}

impl BranchRec {
    pub fn is_dead(&self) -> bool {
        self.dead
    }
    pub fn parent(&self) -> Option<BranchId> {
        self.parent
    }
    pub fn depth(&self) -> u32 {
        self.depth
    }
    pub fn children(&self) -> &[BranchId] {
        &self.children
    }
    pub fn split(&self) -> Option<&Split> {
        self.split.as_ref()
    }
    pub fn hyps(&self) -> &[Fact] {
        &self.hyps
    }
    pub fn contradiction(&self) -> Option<Fact> {
        self.contradiction
    }
    pub fn solution(&self) -> Option<&(Fact, Family)> {
        self.solution.as_ref()
    }
    pub fn pw_solution(&self) -> Option<&(Vec<Fact>, PwFamily)> {
        self.pw_solution.as_ref()
    }
}

#[derive(Clone, Debug)]
pub struct ConstRec {
    branch: BranchId,
}

impl ConstRec {
    pub fn branch(&self) -> BranchId {
        self.branch
    }
}

/// 解であることが検証された関数の族 x ↦ g(x; p̄)。
/// g は Var(0) と「変数を含まない原子」(f(0) などのパラメータ) の多項式。
/// 検証核は、各パラメータを独立な記号とみなして、すべての値で方程式が恒等的に成り立つことを確認済み。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Family {
    kernel: u64,
    g: Poly,
    template: Poly,
    params: Vec<Atom>,
}

impl Family {
    /// 元の形（パラメータは f(0) などの原子のまま）
    pub fn g(&self) -> &Poly {
        &self.g
    }
    /// パラメータを Var(2), Var(3), … に置き換えた形（引数は Var(0)）
    pub fn template(&self) -> &Poly {
        &self.template
    }
    pub fn params(&self) -> &[Atom] {
        &self.params
    }
}

/// 結論: すべての葉が閉じているか解の形が決まっていれば complete。
#[derive(Clone, Debug)]
pub struct Conclusion {
    pub complete: bool,
    pub families: Vec<Family>,
    pub pw_families: Vec<PwFamily>,
    pub open_leaves: Vec<BranchId>,
}

#[derive(Debug)]
pub struct Kernel {
    id: u64,
    lhs: Poly,
    rhs: Poly,
    facts: Vec<FactRec>,
    branches: Vec<BranchRec>,
    consts: Vec<ConstRec>,
    axiom: Fact,
}

type R<T> = Result<T, String>;

impl Kernel {
    /// 方程式 ∀x,y: lhs = rhs を公理として検証核を作る。x = Var(0), y = Var(1)。
    pub fn new(lhs: Poly, rhs: Poly) -> R<Kernel> {
        for p in [&lhs, &rhs] {
            if p.vars().iter().any(|&v| v > 1) || !p.consts().is_empty() || p.has_inv() {
                return Err("方程式は変数 x, y と f だけで書かれていなければならない".into());
            }
        }
        let id = NEXT_KERNEL_ID.fetch_add(1, Ordering::Relaxed);
        let mut k = Kernel {
            id,
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            facts: Vec::new(),
            branches: vec![BranchRec {
                parent: None,
                depth: 0,
                children: vec![],
                split: None,
                hyps: vec![],
                contradiction: None,
                solution: None,
                pw_solution: None,
                dead: false,
                merged: false,
            }],
            consts: Vec::new(),
            axiom: Fact { kernel: id, idx: 0 },
        };
        // 規則 Axiom: 与えられた方程式そのもの。f は方程式を満たすと仮定しているので成り立つ。
        let c = Clause::new(2, vec![Lit::eq(lhs.sub(&rhs))])?;
        k.axiom = k.push(c, ROOT, Rule::Axiom);
        Ok(k)
    }

    // ------------------------------------------------------------------
    // 読み取り用

    pub fn axiom(&self) -> Fact {
        self.axiom
    }
    pub fn equation(&self) -> (&Poly, &Poly) {
        (&self.lhs, &self.rhs)
    }
    pub fn fact(&self, f: Fact) -> &FactRec {
        assert_eq!(f.kernel, self.id, "別の検証核の事実");
        &self.facts[f.idx as usize]
    }
    pub fn clause(&self, f: Fact) -> &Clause {
        &self.fact(f).clause
    }
    pub fn num_facts(&self) -> usize {
        self.facts.len()
    }
    /// i 番目の事実（表示・走査用）
    pub fn fact_at(&self, i: usize) -> Option<Fact> {
        if i < self.facts.len() {
            Some(Fact { kernel: self.id, idx: i as u32 })
        } else {
            None
        }
    }
    pub fn branch(&self, b: BranchId) -> &BranchRec {
        &self.branches[b.0 as usize]
    }
    pub fn num_branches(&self) -> usize {
        self.branches.len()
    }
    pub fn consts(&self) -> &[ConstRec] {
        &self.consts
    }

    /// a が b の祖先または b 自身か
    pub fn is_ancestor(&self, a: BranchId, b: BranchId) -> bool {
        let mut cur = Some(b);
        while let Some(c) = cur {
            if c == a {
                return true;
            }
            cur = self.branches[c.0 as usize].parent;
        }
        false
    }

    /// 枝が閉じている（矛盾が導かれた、またはすべての子が閉じている）
    pub fn is_closed(&self, b: BranchId) -> bool {
        let r = &self.branches[b.0 as usize];
        if r.contradiction.is_some() {
            return true;
        }
        !r.children.is_empty() && r.children.iter().all(|&c| self.is_closed(c))
    }
    /// 祖先を含めて閉じているか
    pub fn is_dead(&self, b: BranchId) -> bool {
        let mut cur = Some(b);
        while let Some(c) = cur {
            if self.branches[c.0 as usize].contradiction.is_some() {
                return true;
            }
            cur = self.branches[c.0 as usize].parent;
        }
        self.is_closed(b)
    }

    // ------------------------------------------------------------------
    // 内部検査

    fn check_fact(&self, f: Fact) -> R<&FactRec> {
        if f.kernel != self.id || (f.idx as usize) >= self.facts.len() {
            return Err("この検証核の事実ではない".into());
        }
        Ok(&self.facts[f.idx as usize])
    }
    fn check_branch(&self, b: BranchId) -> R<()> {
        if (b.0 as usize) >= self.branches.len() {
            return Err("存在しない枝".into());
        }
        if self.branches[b.0 as usize].dead {
            return Err("取り消された枝".into());
        }
        Ok(())
    }
    /// 事実 f が枝 target で使える（f の枝が target の祖先または自身）ことを確かめて節を返す
    fn premise(&self, f: Fact, target: BranchId) -> R<&Clause> {
        let rec = self.check_fact(f)?;
        if !self.is_ancestor(rec.branch, target) {
            return Err("前提の事実がこの枝では使えない（祖先の枝の事実ではない）".into());
        }
        Ok(&rec.clause)
    }
    /// 探索部が与えた式の検査: 変数番号 < nvars、定数は target で有効（スコープ内）
    fn check_term(&self, p: &Poly, nvars: u32, target: BranchId) -> R<()> {
        if let Some(&m) = p.vars().iter().next_back() {
            if m >= nvars {
                return Err(format!("式の変数番号 {} が範囲外", m));
            }
        }
        for c in p.consts() {
            let cr = self.consts.get(c as usize).ok_or("存在しない定数")?;
            if !self.is_ancestor(cr.branch, target) {
                return Err("定数がこの枝のスコープ外".into());
            }
        }
        Ok(())
    }
    fn check_clause_terms(&self, c: &Clause, target: BranchId) -> R<()> {
        for l in c.lits() {
            self.check_term(l.poly(), c.nvars(), target)?;
        }
        Ok(())
    }
    fn lit_of<'a>(c: &'a Clause, i: usize) -> R<&'a Lit> {
        c.lits().get(i).ok_or_else(|| "リテラル番号が範囲外".to_string())
    }
    fn side_lits(c: &Clause, i: usize) -> Vec<Lit> {
        c.lits().iter().enumerate().filter(|(j, _)| *j != i).map(|(_, l)| l.clone()).collect()
    }

    fn push(&mut self, clause: Clause, branch: BranchId, rule: Rule) -> Fact {
        let f = Fact { kernel: self.id, idx: self.facts.len() as u32 };
        let is_false = clause.is_false();
        self.facts.push(FactRec { clause, branch, rule });
        if is_false {
            let br = &mut self.branches[branch.0 as usize];
            if br.contradiction.is_none() {
                br.contradiction = Some(f);
            }
        }
        f
    }

    // ------------------------------------------------------------------
    // 推論規則

    /// 規則 Instantiate（全称例化）:
    /// ∀v̄. C(v̄) が成り立つなら、任意の式 t̄（f を含んでもよい。f の値も実数なので）を代入した
    /// ∀w̄. C(t̄(w̄)) も成り立つ。式中の定数は target の枝で有効でなければならない。
    pub fn instantiate(&mut self, target: BranchId, premise: Fact, subst: Vec<Poly>, nvars: u32) -> R<Fact> {
        self.check_branch(target)?;
        let c = self.premise(premise, target)?.clone();
        if subst.len() != c.nvars() as usize {
            return Err("代入の個数が変数の個数と一致しない".into());
        }
        for t in &subst {
            self.check_term(t, nvars, target)?;
        }
        let lits = c.lits().iter().map(|l| l.subst_vars(&subst)).collect();
        let out = Clause::new(nvars, lits)?;
        Ok(self.push(out, target, Rule::Instantiate { premise, subst }))
    }

    /// 規則 LinComb（多項式係数の一次結合）:
    /// 各前提 i の選ばれたリテラルが p_i = 0（残りを S_i とする）で、変数は番号で共有する
    /// （各前提は全称なので、同じ値を代入した例と見なせる）。任意の多項式 c_i について
    /// 「Σ c_i p_i = 0 ∨ S_1 ∨ … ∨ S_k」が成り立つ。
    /// 根拠: どの S_i も偽になる点では各 p_i = 0 なので、Σ c_i p_i = 0。
    pub fn lincomb(&mut self, target: BranchId, nvars: u32, items: Vec<(Poly, Fact, usize)>) -> R<Fact> {
        self.check_branch(target)?;
        if items.is_empty() {
            return Err("一次結合の項がない".into());
        }
        let mut sum = Poly::zero();
        let mut side = Vec::new();
        for (coef, f, li) in &items {
            let c = self.premise(*f, target)?;
            if c.nvars() > nvars {
                return Err("前提の変数が多すぎる".into());
            }
            let l = Self::lit_of(c, *li)?;
            if l.rel() != Rel::Eq {
                return Err("一次結合は等式リテラルにだけ使える".into());
            }
            self.check_term(coef, nvars, target)?;
            sum = sum.add(&coef.mul(l.poly()));
            side.extend(Self::side_lits(c, *li));
        }
        let mut lits = vec![Lit::eq(sum)];
        lits.extend(side);
        let out = Clause::new(nvars, lits)?;
        Ok(self.push(out, target, Rule::LinComb { items }))
    }

    /// 規則 Congruence（関数の合同性）:
    /// 各前提 i の選ばれたリテラルが p_i = 0（残り S_i）で、変数は番号で共有する。任意の式 u と多項式 m_i について
    /// 「f(u + Σ m_i p_i) − f(u) = 0 ∨ S_1 ∨ … ∨ S_k」。
    /// 根拠: どの S_i も偽になる点では各 p_i = 0 なので u + Σ m_i p_i = u となり、f の値も等しい。
    pub fn congruence(&mut self, target: BranchId, nvars: u32, base: Poly, items: Vec<(Poly, Fact, usize)>) -> R<Fact> {
        self.check_branch(target)?;
        if items.is_empty() {
            return Err("合同性の前提がない".into());
        }
        self.check_term(&base, nvars, target)?;
        let mut arg = base.clone();
        let mut side = Vec::new();
        for (m, f, li) in &items {
            let c = self.premise(*f, target)?;
            if c.nvars() > nvars {
                return Err("前提の変数が多すぎる".into());
            }
            let l = Self::lit_of(c, *li)?;
            if l.rel() != Rel::Eq {
                return Err("合同性は等式リテラルにだけ使える".into());
            }
            self.check_term(m, nvars, target)?;
            arg = arg.add(&m.mul(l.poly()));
            side.extend(Self::side_lits(c, *li));
        }
        let p = Poly::f(arg).sub(&Poly::f(base.clone()));
        let mut lits = vec![Lit::eq(p)];
        lits.extend(side);
        let out = Clause::new(nvars, lits)?;
        Ok(self.push(out, target, Rule::Congruence { base, items }))
    }

    /// 規則 EqOrNe（排中律, リテラル版）: 任意の式 p について「p = 0 ∨ p ≠ 0」。
    pub fn eq_or_ne(&mut self, target: BranchId, nvars: u32, poly: Poly) -> R<Fact> {
        self.check_branch(target)?;
        self.check_term(&poly, nvars, target)?;
        let out = Clause::new(nvars, vec![Lit::eq(poly.clone()), Lit::ne(poly.clone())])?;
        Ok(self.push(out, target, Rule::EqOrNe { poly }))
    }

    /// 規則 ZeroProduct（積が 0 なら因子のどれかが 0）:
    /// 選ばれたリテラルが p = 0 で、探索部が示した因子の積 Π q_j が p の 0 でない定数倍に
    /// 厳密に一致するなら「q_1 = 0 ∨ … ∨ q_m = 0 ∨ S」。根拠: 実数は整域。
    pub fn zero_product(&mut self, target: BranchId, premise: Fact, lit: usize, factors: Vec<Poly>) -> R<Fact> {
        self.check_branch(target)?;
        let c = self.premise(premise, target)?.clone();
        let l = Self::lit_of(&c, lit)?;
        if l.rel() != Rel::Eq {
            return Err("ZeroProduct は等式リテラルにだけ使える".into());
        }
        Self::check_product(l.poly(), &factors)?;
        for q in &factors {
            self.check_term(q, c.nvars(), target)?;
        }
        let mut lits: Vec<Lit> = factors.iter().map(|q| Lit::eq(q.clone())).collect();
        lits.extend(Self::side_lits(&c, lit));
        let out = Clause::new(c.nvars(), lits)?;
        Ok(self.push(out, target, Rule::ZeroProduct { premise, lit, factors }))
    }

    /// 規則 NonzeroFactor（積が 0 でなければ各因子も 0 でない）:
    /// 選ばれたリテラルが p ≠ 0 で Π q_j が p の 0 でない定数倍なら「q_index ≠ 0 ∨ S」。
    pub fn nonzero_factor(&mut self, target: BranchId, premise: Fact, lit: usize, factors: Vec<Poly>, index: usize) -> R<Fact> {
        self.check_branch(target)?;
        let c = self.premise(premise, target)?.clone();
        let l = Self::lit_of(&c, lit)?;
        if l.rel() != Rel::Ne {
            return Err("NonzeroFactor は ≠ リテラルにだけ使える".into());
        }
        Self::check_product(l.poly(), &factors)?;
        let q = factors.get(index).ok_or("因子番号が範囲外")?.clone();
        self.check_term(&q, c.nvars(), target)?;
        let mut lits = vec![Lit::ne(q)];
        lits.extend(Self::side_lits(&c, lit));
        let out = Clause::new(c.nvars(), lits)?;
        Ok(self.push(out, target, Rule::NonzeroFactor { premise, lit, factors, index }))
    }

    fn check_product(p: &Poly, factors: &[Poly]) -> R<()> {
        if factors.is_empty() {
            return Err("因子がない".into());
        }
        let mut prod = Poly::one();
        for q in factors {
            prod = prod.mul(q);
        }
        if p.is_zero() || prod.is_zero() || prod.monic() != p.monic() {
            return Err("因子の積が元の多項式の定数倍に一致しない".into());
        }
        Ok(())
    }

    /// 規則 Resolve（導出原理）:
    /// 「L ∨ A」と「¬L ∨ B」から「A ∨ B」。変数は番号で共有する。
    /// ¬(p=0) は p≠0、¬(p>0) は −p≥0、¬(p≥0) は −p>0（正規化後に厳密一致を要求）。
    pub fn resolve(&mut self, target: BranchId, a: Fact, la: usize, b: Fact, lb: usize) -> R<Fact> {
        self.check_branch(target)?;
        let ca = self.premise(a, target)?.clone();
        let cb = self.premise(b, target)?.clone();
        let l1 = Self::lit_of(&ca, la)?;
        let l2 = Self::lit_of(&cb, lb)?;
        if l1.negate() != *l2 {
            return Err("リテラルが互いの否定になっていない".into());
        }
        let nvars = ca.nvars().max(cb.nvars());
        let mut lits = Self::side_lits(&ca, la);
        lits.extend(Self::side_lits(&cb, lb));
        let out = Clause::new(nvars, lits)?;
        Ok(self.push(out, target, Rule::Resolve { a, la, b, lb }))
    }

    /// 規則 Trichotomy（三分律）: 任意の式 p について「p > 0 ∨ p = 0 ∨ −p > 0」。
    pub fn trichotomy(&mut self, target: BranchId, nvars: u32, poly: Poly) -> R<Fact> {
        self.check_branch(target)?;
        self.check_term(&poly, nvars, target)?;
        let lits = vec![Lit::gt(poly.clone()), Lit::eq(poly.clone()), Lit::gt(poly.neg())];
        let out = Clause::new(nvars, lits)?;
        Ok(self.push(out, target, Rule::Trichotomy { poly }))
    }

    /// 規則 StrictNe: 「p > 0 ∨ S」から「p ≠ 0 ∨ S」。
    pub fn strict_ne(&mut self, target: BranchId, premise: Fact, lit: usize) -> R<Fact> {
        self.check_branch(target)?;
        let c = self.premise(premise, target)?.clone();
        let l = Self::lit_of(&c, lit)?;
        if l.rel() != Rel::Gt {
            return Err("StrictNe は > リテラルにだけ使える".into());
        }
        let mut lits = vec![Lit::ne(l.poly().clone())];
        lits.extend(Self::side_lits(&c, lit));
        let out = Clause::new(c.nvars(), lits)?;
        Ok(self.push(out, target, Rule::StrictNe { premise, lit }))
    }

    /// 規則 PosComb（非負結合）:
    /// 不等式リテラル p_i ≥ 0 または p_i > 0 に非負の有理数 a_i を、等式リテラル e_j = 0 に任意の多項式 c_j を、
    /// 任意の式 s_k の平方に非負の有理数 d_k を掛け、非負の定数 κ を加えた
    /// q = Σ a_i p_i + Σ c_j e_j + Σ d_k s_k² + κ について「q ≥ 0 ∨ 各前提の残り」。
    /// strict を求めた場合は、a_i > 0 の厳密不等式 (>) の前提があるか κ > 0 のときに限り「q > 0」。
    /// 根拠: 非負の数の非負結合は非負、平方は非負。正の数を加えれば正。
    pub fn pos_comb(
        &mut self,
        target: BranchId,
        nvars: u32,
        ineqs: Vec<(Q, Fact, usize)>,
        eqs: Vec<(Poly, Fact, usize)>,
        squares: Vec<(Q, Poly)>,
        constant: Q,
        strict: bool,
    ) -> R<Fact> {
        self.check_branch(target)?;
        if constant.is_negative() {
            return Err("定数は非負でなければならない".into());
        }
        let mut sum = Poly::constant(constant.clone());
        let mut side = Vec::new();
        let mut strict_ok = constant.is_positive();
        for (a, f, li) in &ineqs {
            if a.is_negative() {
                return Err("不等式の係数は非負でなければならない".into());
            }
            let c = self.premise(*f, target)?;
            if c.nvars() > nvars {
                return Err("前提の変数が多すぎる".into());
            }
            let l = Self::lit_of(c, *li)?;
            match l.rel() {
                Rel::Gt => {
                    if a.is_positive() {
                        strict_ok = true
                    }
                }
                Rel::Ge => {}
                _ => return Err("不等式リテラルではない".into()),
            }
            sum = sum.add(&l.poly().scale(a));
            side.extend(Self::side_lits(c, *li));
        }
        for (cf, f, li) in &eqs {
            let c = self.premise(*f, target)?;
            if c.nvars() > nvars {
                return Err("前提の変数が多すぎる".into());
            }
            let l = Self::lit_of(c, *li)?;
            if l.rel() != Rel::Eq {
                return Err("等式リテラルではない".into());
            }
            self.check_term(cf, nvars, target)?;
            sum = sum.add(&cf.mul(l.poly()));
            side.extend(Self::side_lits(c, *li));
        }
        for (d, s) in &squares {
            if d.is_negative() {
                return Err("平方の係数は非負でなければならない".into());
            }
            self.check_term(s, nvars, target)?;
            sum = sum.add(&s.mul(s).scale(d));
        }
        if strict && !strict_ok {
            return Err("厳密不等式を導く根拠がない".into());
        }
        let mut lits = vec![if strict { Lit::gt(sum) } else { Lit::ge(sum) }];
        lits.extend(side);
        let out = Clause::new(nvars, lits)?;
        Ok(self.push(out, target, Rule::PosComb { ineqs, eqs, squares, constant }))
    }

    /// 規則 MulIneq（不等式の積）: 「p ⋈ 0 ∨ A」「q ⋈ 0 ∨ B」（⋈ は ≥ か >）から「pq ⋈' 0 ∨ A ∨ B」。
    /// ⋈' は両方 > のとき >、それ以外は ≥。根拠: 非負同士の積は非負、正同士の積は正。
    pub fn mul_ineq(&mut self, target: BranchId, a: Fact, la: usize, b: Fact, lb: usize) -> R<Fact> {
        self.check_branch(target)?;
        let ca = self.premise(a, target)?.clone();
        let cb = self.premise(b, target)?.clone();
        let l1 = Self::lit_of(&ca, la)?;
        let l2 = Self::lit_of(&cb, lb)?;
        let ok = |r: Rel| r == Rel::Gt || r == Rel::Ge;
        if !ok(l1.rel()) || !ok(l2.rel()) {
            return Err("不等式リテラルではない".into());
        }
        let p = l1.poly().mul(l2.poly());
        let lit = if l1.rel() == Rel::Gt && l2.rel() == Rel::Gt { Lit::gt(p) } else { Lit::ge(p) };
        let nvars = ca.nvars().max(cb.nvars());
        let mut lits = vec![lit];
        lits.extend(Self::side_lits(&ca, la));
        lits.extend(Self::side_lits(&cb, lb));
        let out = Clause::new(nvars, lits)?;
        Ok(self.push(out, target, Rule::MulIneq { a, la, b, lb }))
    }

    /// 規則 SquareRange（平方の値域）:
    /// 前提の節 C が、ある節 C'(t) の変数 v を v² に置き換えたもの C'(v²) と（正規化後に）厳密に一致するなら
    /// 「∀t. t < 0 ∨ C'(t)」（C' の変数 v を t と読む）。根拠: t ≥ 0 なら t = (√t)² なので C'(t) = C(√t)。
    pub fn square_range(&mut self, target: BranchId, premise: Fact, var: u32, pre: Clause) -> R<Fact> {
        self.check_branch(target)?;
        let c = self.premise(premise, target)?.clone();
        if pre.nvars() != c.nvars() || var >= c.nvars() {
            return Err("変数の個数が合わない".into());
        }
        self.check_clause_terms(&pre, target)?;
        let mut s: Vec<Poly> = (0..c.nvars()).map(Poly::var).collect();
        s[var as usize] = Poly::var(var).pow(2);
        let back = Clause::new(c.nvars(), pre.lits().iter().map(|l| l.subst_vars(&s)).collect())?;
        if back != c {
            return Err("前提が C'(v²) の形になっていない".into());
        }
        let mut lits = pre.lits().to_vec();
        lits.push(Lit::gt(Poly::var(var).neg()));
        let out = Clause::new(c.nvars(), lits)?;
        Ok(self.push(out, target, Rule::SquareRange { premise, var }))
    }

    /// 規則 InvAxiom（逆数）: 任意の式 u について「u = 0 ∨ u·inv(u) − 1 = 0」。
    /// inv は u ≠ 0 で 1/u、u = 0 で 0 と定めた全域関数なので常に成り立つ。
    pub fn inv_axiom(&mut self, target: BranchId, nvars: u32, poly: Poly) -> R<Fact> {
        self.check_branch(target)?;
        self.check_term(&poly, nvars, target)?;
        let lits = vec![Lit::eq(poly.clone()), Lit::eq(poly.mul(&Poly::inv(poly.clone())).sub(&Poly::one()))];
        let out = Clause::new(nvars, lits)?;
        Ok(self.push(out, target, Rule::InvAxiom { poly }))
    }

    /// 規則 Weaken（弱化）: 「A」から「A ∨ B」。
    pub fn weaken(&mut self, target: BranchId, premise: Fact, extra: Vec<Lit>, nvars: u32) -> R<Fact> {
        self.check_branch(target)?;
        let c = self.premise(premise, target)?.clone();
        if nvars < c.nvars() {
            return Err("変数の個数が足りない".into());
        }
        for l in &extra {
            self.check_term(l.poly(), nvars, target)?;
        }
        let mut lits = c.lits().to_vec();
        lits.extend(extra.iter().cloned());
        let out = Clause::new(nvars, lits)?;
        Ok(self.push(out, target, Rule::Weaken { premise, extra }))
    }

    /// 規則 CauchyBounded（コーシーの方程式の有界な解）:
    /// 前提 A「∀x,y. f(x+y) − f(x) − f(y) + f(0) = 0」と、前提 B「∀x. x < 0 ∨ s·(f(x) − k) ≥ 0」
    /// （s = ±1、k は変数を含まない式）から「∀x. f(x) − (f(1) − f(0))·x − f(0) = 0」。
    /// 根拠: g(x) = f(x) − f(0) とおくと A より g は加法的（g(x+y) = g(x) + g(y)）。B より g は [0, ∞) で
    /// 下に（s = −1 なら上に）有界。加法的関数は有理数倍を保ち（g(qx) = q·g(x)）、区間上で片側に有界なら
    /// g(x) = g(1)·x（ダルブーの定理: 有界性から g(1)x − g(x) が有理数倍で任意に大きくなりえないことを使う）。
    /// よって f(x) = (f(1) − f(0))x + f(0)。
    pub fn cauchy_bounded(&mut self, target: BranchId, additive: Fact, bound: Fact) -> R<Fact> {
        self.check_branch(target)?;
        let ca = self.premise(additive, target)?.clone();
        let cb = self.premise(bound, target)?.clone();
        let x = Poly::var(0);
        let y = Poly::var(1);
        let f0 = Poly::f(Poly::zero());
        let want_a = Clause::new(2, vec![Lit::eq(Poly::f(x.add(&y)).sub(&Poly::f(x.clone())).sub(&Poly::f(y.clone())).add(&f0))])?;
        if ca != want_a {
            return Err("前提 A が f(x+y) = f(x) + f(y) − f(0) の形ではない".into());
        }
        if cb.nvars() != 1 || cb.lits().len() != 2 {
            return Err("前提 B の形が違う".into());
        }
        let cond = Lit::gt(x.neg());
        let other = match (cb.lits()[0] == cond, cb.lits()[1] == cond) {
            (true, false) => &cb.lits()[1],
            (false, true) => &cb.lits()[0],
            _ => return Err("前提 B に条件 x < 0 がない".into()),
        };
        if other.rel() != Rel::Ge {
            return Err("前提 B が不等式 ≥ ではない".into());
        }
        // other.poly() = α·f(x) + (変数を含まない式)、α ≠ 0
        let fx = Atom::F(std::rc::Rc::new(x.clone()));
        let mut alpha: Option<Q> = None;
        for (m, c) in other.poly().terms() {
            if m.factors().len() == 1 && m.factors()[0] == (fx.clone(), 1) {
                alpha = Some(c.clone());
            } else if m.factors().iter().any(|(a, _)| a.has_var()) {
                return Err("前提 B の式が f(x) の 1 次式（他は定数）ではない".into());
            }
        }
        if alpha.map_or(true, |a| a.is_zero()) {
            return Err("前提 B に f(x) がない".into());
        }
        let g = Poly::f(Poly::one()).sub(&f0).mul(&x).add(&f0);
        let out = Clause::new(1, vec![Lit::eq(Poly::f(x).sub(&g))])?;
        Ok(self.push(out, target, Rule::CauchyBounded { additive, bound }))
    }

    /// 規則 ImportLemma（補題として解いた方程式への帰着）:
    /// 別の検証核 L が方程式 E' を公理として完全解決しており（すべての葉が閉じるか解の形が確定）、
    /// この枝の事実 premise の節が E' の公理の節と厳密に一致するなら、L の各葉の解の形 f(x) = g_i(x) を
    /// 変数を分けて並べた選言「∀x₁,…,x_k. f(x₁) = g₁(x₁) ∨ … ∨ f(x_k) = g_k(x_k)」が成り立つ。
    /// g_i は f の値などの閉じた原子を含んでよいが、L で導入された定数を含んではならない。区分的な解の葉は扱わない。
    /// 根拠: L の場合分けは網羅的なので、E' を満たす任意の f はある葉の仮定を満たし（定数は適当に選べる）、
    /// その葉の事実 ∀x. f(x) = g_i(x) が成り立つ。g_i は L の定数を含まないので f だけについての主張である。
    /// premise により f はこの枝で E' を満たす。
    pub fn import_lemma(&mut self, target: BranchId, premise: Fact, lemma: std::rc::Rc<Kernel>) -> R<Fact> {
        self.check_branch(target)?;
        if lemma.id == self.id {
            return Err("自分自身を補題にはできない".into());
        }
        let c = self.premise(premise, target)?.clone();
        let lax = lemma.clause(lemma.axiom).clone();
        if c != lax {
            return Err("事実が補題の方程式と一致しない".into());
        }
        let concl = lemma.conclude();
        if !concl.complete {
            return Err("補題が完全解決していない".into());
        }
        if !concl.pw_families.is_empty() {
            return Err("区分的な解をもつ補題は扱わない".into());
        }
        // 閉じていない葉の解の事実を集める
        let mut gs: Vec<Poly> = Vec::new();
        let mut stack = vec![ROOT];
        while let Some(b) = stack.pop() {
            if lemma.is_closed(b) {
                continue;
            }
            let r = lemma.branch(b);
            if r.children.is_empty() {
                let (f, _) = r.solution.as_ref().ok_or("解の確定していない葉がある")?;
                let lc = lemma.clause(*f);
                // ∀x. f(x) − g = 0（保存形は正規化済み）から g を取り出す
                if lc.nvars() != 1 || lc.lits().len() != 1 || lc.lits()[0].rel() != Rel::Eq {
                    return Err("葉の事実の形が違う".into());
                }
                let fx = Poly::f(Poly::var(0));
                let fxa = Atom::F(std::rc::Rc::new(Poly::var(0)));
                let p = lc.lits()[0].poly();
                let lam = p
                    .terms()
                    .iter()
                    .find(|(m, _)| m.factors().len() == 1 && m.factors()[0] == (fxa.clone(), 1))
                    .map(|(_, c)| c.clone())
                    .ok_or("葉の事実に f(x) がない")?;
                let g = fx.sub(&p.scale(&(Q::one() / lam)));
                if g.top_atoms().contains(&fxa) {
                    return Err("葉の事実の形が違う".into());
                }
                if !g.consts().is_empty() {
                    return Err("葉の解の式が補題の定数を含む".into());
                }
                if !gs.contains(&g) {
                    gs.push(g);
                }
            } else {
                stack.extend(r.children.iter().copied());
            }
        }
        let k = gs.len() as u32;
        let mut lits = Vec::new();
        for (i, g) in gs.iter().enumerate() {
            let mut s = vec![Poly::zero(); k.max(1) as usize];
            s[0] = Poly::var(i as u32);
            let gi = g.subst_vars(&s);
            lits.push(Lit::eq(Poly::f(Poly::var(i as u32)).sub(&gi)));
        }
        let out = Clause::new(k, lits)?;
        Ok(self.push(out, target, Rule::ImportLemma { premise, lemma }))
    }

    // ------------------------------------------------------------------
    // 場合分け

    fn new_child(&mut self, parent: BranchId) -> BranchId {
        let id = BranchId(self.branches.len() as u32);
        let depth = self.branches[parent.0 as usize].depth + 1;
        self.branches.push(BranchRec {
            parent: Some(parent),
            depth,
            children: vec![],
            split: None,
            hyps: vec![],
            contradiction: None,
            solution: None,
            pw_solution: None,
            dead: false,
            merged: false,
        });
        self.branches[parent.0 as usize].children.push(id);
        id
    }

    fn check_splittable(&self, b: BranchId) -> R<()> {
        self.check_branch(b)?;
        let r = &self.branches[b.0 as usize];
        if !r.children.is_empty() {
            return Err("この枝は既に場合分けされている".into());
        }
        if r.solution.is_some() || r.pw_solution.is_some() {
            return Err("この枝は既に解が確定している".into());
        }
        Ok(())
    }

    /// 規則 SplitComponents（変数を共有しない選言による場合分け）:
    /// 節のリテラルを「変数を共有するもの同士」でまとめた成分を C_1, …, C_k（k ≥ 2）とすると、
    /// ∀v̄.(C_1 ∨ … ∨ C_k) ⇔ (∀.C_1) ∨ … ∨ (∀.C_k)（成分は変数を共有しないので量化子を分配できる）。
    /// よって枝を k 個の子に分け、子 i では C_i を仮定する。各点ごとの選言（同じ変数を共有する
    /// 「f(x)=x ∨ f(x)=0」など）はひとつの成分になるので、この規則では分けられない。
    pub fn split_components(&mut self, b: BranchId, fact: Fact) -> R<Vec<(BranchId, Fact)>> {
        self.check_splittable(b)?;
        let c = self.premise(fact, b)?.clone();
        let comps = components(&c);
        if comps.len() < 2 {
            return Err("変数を共有しない成分が2つ以上ない".into());
        }
        self.branches[b.0 as usize].split = Some(Split::Components { fact });
        let mut out = Vec::new();
        for (i, comp) in comps.into_iter().enumerate() {
            let child = self.new_child(b);
            let cl = Clause::new(c.nvars(), comp)?;
            let h = self.push(cl, child, Rule::Hypothesis { parent: b, child_index: i });
            self.branches[child.0 as usize].hyps.push(h);
            out.push((child, h));
        }
        Ok(out)
    }

    /// 規則 SplitExcludedMiddle（排中律による場合分け）:
    /// 任意の節 C について (∀v̄. C(v̄)) ∨ (∃ā. ¬C(ā))。
    /// 子0 では C を仮定し、子1 では新しい定数 ā（変数ごとに1つ。検証核が番号を割り当て、
    /// 子1とその子孫でのみ有効）を導入して、C の各リテラル L について ¬L(ā) を仮定する。
    pub fn split_em(&mut self, b: BranchId, clause: Clause) -> R<(BranchId, Fact, BranchId, Vec<Fact>, Vec<u32>)> {
        self.check_splittable(b)?;
        self.check_clause_terms(&clause, b)?;
        if clause.is_false() || clause.is_tautology() {
            return Err("自明な節では場合分けしない".into());
        }
        let c0 = self.new_child(b);
        let c1 = self.new_child(b);
        let mut consts = Vec::new();
        let mut s = Vec::new();
        for _ in 0..clause.nvars() {
            let id = self.consts.len() as u32;
            self.consts.push(ConstRec { branch: c1 });
            consts.push(id);
            s.push(Poly::cnst(id));
        }
        self.branches[b.0 as usize].split = Some(Split::ExcludedMiddle { clause: clause.clone(), consts: consts.clone() });
        let h0 = self.push(clause.clone(), c0, Rule::Hypothesis { parent: b, child_index: 0 });
        self.branches[c0.0 as usize].hyps.push(h0);
        let mut hs = Vec::new();
        for l in clause.lits() {
            let nl = l.negate().subst_vars(&s);
            let cl = Clause::new(0, vec![nl])?;
            let h = self.push(cl, c1, Rule::Hypothesis { parent: b, child_index: 1 });
            self.branches[c1.0 as usize].hyps.push(h);
            hs.push(h);
        }
        Ok((c0, h0, c1, hs, consts))
    }

    /// 規則 Merge（場合の合流）:
    /// 枝 b の各子 c_i について、c_i が閉じている（矛盾）か、c_i で成り立つ事実の節がすべて同じ C なら、
    /// C は b で成り立つ。C は b で有効な定数だけを含まなければならない（子で導入した定数は不可）。
    /// 根拠: 場合分けは網羅的なので、b の任意の状況でどれかの子の仮定が成り立つ。
    pub fn merge(&mut self, b: BranchId, facts: Vec<Option<Fact>>) -> R<Fact> {
        self.check_branch(b)?;
        let children = self.branches[b.0 as usize].children.clone();
        if children.is_empty() || children.len() != facts.len() {
            return Err("子の数と事実の数が一致しない".into());
        }
        let mut clause: Option<Clause> = None;
        for (c, f) in children.iter().zip(&facts) {
            match f {
                None => {
                    if !self.is_closed(*c) {
                        return Err("事実のない子が閉じていない".into());
                    }
                }
                Some(f) => {
                    let cl = self.premise(*f, *c)?.clone();
                    match &clause {
                        None => clause = Some(cl),
                        Some(prev) => {
                            if *prev != cl {
                                return Err("子ごとの事実が一致しない".into());
                            }
                        }
                    }
                }
            }
        }
        let clause = clause.ok_or("すべての子が閉じている（矛盾は自動的に親へ伝わる）")?;
        self.check_clause_terms(&clause, b)?;
        self.branches[b.0 as usize].merged = true;
        Ok(self.push(clause, b, Rule::Merge { parent: b, facts }))
    }

    /// 操作 AbandonSplit（場合分けの取り消し）:
    /// 枝 b の場合分けをなかったことにし、b を再び葉に戻す。子孫の枝はすべて無効になり、
    /// その事実・定数は以後どこでも使えない（無効な枝を対象にした規則の呼び出しはすべて拒否される）。
    /// 根拠: 子孫の枝の事実はもともと子孫の枝でしか使えない（前提の祖先検査・定数のスコープ検査）ので、
    /// それらを捨てても b とその祖先で成り立つ事実には影響しない。ただし Merge で子から b へ持ち上げた
    /// 事実がある場合は、その根拠を残すため取り消せない。
    pub fn abandon_split(&mut self, b: BranchId) -> R<()> {
        self.check_branch(b)?;
        if self.branches[b.0 as usize].merged {
            return Err("Merge で事実を持ち上げた場合分けは取り消せない".into());
        }
        let children = std::mem::take(&mut self.branches[b.0 as usize].children);
        if children.is_empty() {
            return Err("場合分けされていない".into());
        }
        let mut stack = children;
        while let Some(c) = stack.pop() {
            let r = &mut self.branches[c.0 as usize];
            r.dead = true;
            stack.extend(r.children.iter().copied());
        }
        self.branches[b.0 as usize].split = None;
        Ok(())
    }

    // ------------------------------------------------------------------
    // 解の検証と結論

    /// 関数族 x ↦ g(x; p̄) が方程式の解であることを厳密な記号計算で確かめる。
    /// g は Var(0) と、変数を含まない原子（パラメータ）だけを最上位に含む多項式でなければならない。
    /// 各パラメータを独立な記号に置き換え、f(t) := g(t) を方程式の両辺に（内側から）代入して、
    /// 差が x, y, パラメータの多項式として恒等的に 0 になることを確認する。
    pub fn verify_solution(&self, g: &Poly) -> R<Family> {
        let mut params: Vec<Atom> = Vec::new();
        for (m, _) in g.terms() {
            for (a, _) in m.factors() {
                match a {
                    Atom::Var(0) => {}
                    Atom::Var(_) => return Err("解の式に x 以外の変数がある".into()),
                    other => {
                        if other.has_var() {
                            return Err("解の式の原子が x を含む（f(x) などは不可）".into());
                        }
                        if !params.contains(other) {
                            params.push(other.clone());
                        }
                    }
                }
            }
        }
        params.sort();
        let template = map_top_atoms(g, &mut |a| match a {
            Atom::Var(0) => Poly::var(0),
            other => {
                let k = params.iter().position(|p| p == other).unwrap() as u32;
                Poly::var(2 + k)
            }
        });
        let np = params.len() as u32;
        let apply = |t: &Poly| -> Poly {
            t.transform(&mut |a| match a {
                Atom::F(arg) => {
                    let mut s = vec![(*arg).clone(), Poly::var(1)];
                    for k in 0..np {
                        s.push(Poly::var(2 + k));
                    }
                    template.subst_vars(&s)
                }
                other => Poly::from_atom(other),
            })
        };
        let lhs = apply(&self.lhs);
        let rhs = apply(&self.rhs);
        if !lhs.sub(&rhs).is_zero() {
            return Err("方程式を恒等的には満たさない".into());
        }
        Ok(Family { kernel: self.id, g: g.clone(), template, params })
    }

    /// 葉 b で「∀x. f(x) = g(x)」が成り立ち、g が検証済みの解の族なら、その葉を「解が確定」とする。
    pub fn mark_solution(&mut self, b: BranchId, fact: Fact, fam: Family) -> R<()> {
        self.check_branch(b)?;
        if fam.kernel != self.id {
            return Err("別の検証核で検証された族".into());
        }
        let r = &self.branches[b.0 as usize];
        if !r.children.is_empty() || r.solution.is_some() || r.pw_solution.is_some() {
            return Err("葉ではないか既に解が確定している".into());
        }
        let c = self.premise(fact, b)?;
        let want = Clause::new(1, vec![Lit::eq(Poly::f(Poly::var(0)).sub(&fam.g))])?;
        if *c != want {
            return Err("事実が ∀x. f(x) = g(x) の形ではない".into());
        }
        self.branches[b.0 as usize].solution = Some((fact, fam));
        Ok(())
    }

    /// 証明木全体の結論。すべての葉が閉じているか解の形が確定していれば complete。
    pub fn conclude(&self) -> Conclusion {
        let mut families: Vec<Family> = Vec::new();
        let mut pw: Vec<PwFamily> = Vec::new();
        let mut open = Vec::new();
        self.collect(ROOT, &mut families, &mut pw, &mut open);
        Conclusion { complete: open.is_empty(), families, pw_families: pw, open_leaves: open }
    }

    fn collect(&self, b: BranchId, fams: &mut Vec<Family>, pw: &mut Vec<PwFamily>, open: &mut Vec<BranchId>) {
        if self.is_closed(b) {
            return;
        }
        let r = &self.branches[b.0 as usize];
        if r.children.is_empty() {
            if let Some((_, fam)) = &r.solution {
                if !fams.iter().any(|f| f.template == fam.template) {
                    fams.push(fam.clone());
                }
            } else if let Some((_, fam)) = &r.pw_solution {
                if !pw.iter().any(|f| f.breaks == fam.breaks && f.pieces == fam.pieces) {
                    pw.push(fam.clone());
                }
            } else {
                open.push(b);
            }
            return;
        }
        for &c in &r.children {
            self.collect(c, fams, pw, open);
        }
    }

    /// 区分的な族が解であることを確かめる（詳細は piecewise モジュール）
    pub fn verify_piecewise(&self, breaks: Vec<Q>, pieces: Vec<Poly>) -> R<PwFamily> {
        crate::piecewise::verify(&self.lhs, &self.rhs, &breaks, &pieces)?;
        Ok(PwFamily { kernel: self.id, breaks, pieces })
    }

    /// 葉 b で、区分的な族の各区間 i について事実 facts[i] が「その区間では f(x) = g_i(x)」を与えるなら、
    /// 葉を「解が確定」とする。facts[i] の節は、f を含む等式リテラル λ(f(t) − h) = 0（t = x、または点の区間では
    /// t = 区切り点）がちょうど 1 つで、他のリテラルは x の 1 次式でその区間全体で偽、h は区間上で g_i と一致すること。
    /// 根拠: 区間上では他のリテラルが偽なので f(x) = h(x) = g_i(x)。区間は実数全体を覆う。
    pub fn mark_piecewise(&mut self, b: BranchId, facts: Vec<Fact>, fam: PwFamily) -> R<()> {
        self.check_branch(b)?;
        if fam.kernel != self.id {
            return Err("別の検証核で検証された族".into());
        }
        let r = &self.branches[b.0 as usize];
        if !r.children.is_empty() || r.solution.is_some() || r.pw_solution.is_some() {
            return Err("葉ではないか既に解が確定している".into());
        }
        if facts.len() != fam.pieces.len() {
            return Err("区間の数と事実の数が合わない".into());
        }
        for (i, f) in facts.iter().enumerate() {
            let c = self.premise(*f, b)?.clone();
            let (lo, hi) = fam.interval(i);
            let point = i % 2 == 1;
            if c.nvars() > 1 {
                return Err("事実の変数が多すぎる".into());
            }
            let mut found = false;
            for l in c.lits() {
                if l.poly().has_f() {
                    if found || l.rel() != Rel::Eq {
                        return Err("f を含むリテラルは等式 1 つだけ".into());
                    }
                    found = true;
                    // λ(f(t) − h) の形
                    let t = if c.nvars() == 1 {
                        Poly::var(0)
                    } else if point {
                        Poly::constant(lo.clone().unwrap())
                    } else {
                        return Err("閉じた事実は点の区間にだけ使える".into());
                    };
                    let fa = Atom::F(std::rc::Rc::new(t.clone()));
                    let p = l.poly();
                    let lam = p
                        .terms()
                        .iter()
                        .find(|(m, _)| m.factors().len() == 1 && m.factors()[0] == (fa.clone(), 1))
                        .map(|(_, c)| c.clone())
                        .ok_or("f(x) の項がない")?;
                    let h = Poly::from_atom(fa).sub(&p.scale(&(Q::one() / lam)));
                    if h.has_f() || h.has_inv() || !h.consts().is_empty() || h.vars().iter().any(|&v| v != 0) {
                        return Err("h が x の多項式ではない".into());
                    }
                    let g = &fam.pieces[i];
                    let agree = if point {
                        let bp = Poly::constant(lo.clone().unwrap());
                        h.subst_vars(&[bp.clone()]) == g.subst_vars(&[bp])
                    } else {
                        h == *g
                    };
                    if !agree {
                        return Err("区間上で式が一致しない".into());
                    }
                } else if !crate::piecewise::literal_false_on(l.poly(), l.rel(), &lo, &hi, point) {
                    return Err("条件リテラルが区間全体で偽になっていない".into());
                }
            }
            if !found {
                return Err("f(x) = h(x) のリテラルがない".into());
            }
        }
        self.branches[b.0 as usize].pw_solution = Some((facts, fam));
        Ok(())
    }
}

/// 最上位の原子だけを置き換える（引数の中には入らない）
fn map_top_atoms(p: &Poly, g: &mut dyn FnMut(&Atom) -> Poly) -> Poly {
    let mut out = Poly::zero();
    for (m, c) in p.terms() {
        let mut prod = Poly::constant(c.clone());
        for (a, e) in m.factors() {
            prod = prod.mul(&g(a).pow(*e));
        }
        out = out.add(&prod);
    }
    out
}

/// 節のリテラルを、変数を共有するもの同士で連結成分に分ける（変数を含まないリテラルはそれぞれ単独の成分）
pub fn components(c: &Clause) -> Vec<Vec<Lit>> {
    let lits = c.lits();
    let n = lits.len();
    let vars: Vec<BTreeSet<u32>> = lits.iter().map(|l| l.poly().vars()).collect();
    let mut comp: Vec<usize> = (0..n).collect();
    fn find(c: &mut Vec<usize>, i: usize) -> usize {
        let mut i = i;
        while c[i] != i {
            c[i] = c[c[i]];
            i = c[i];
        }
        i
    }
    for i in 0..n {
        for j in (i + 1)..n {
            if !vars[i].is_disjoint(&vars[j]) {
                let (a, b) = (find(&mut comp, i), find(&mut comp, j));
                comp[a] = b;
            }
        }
    }
    let mut groups: Vec<(usize, Vec<Lit>)> = Vec::new();
    for i in 0..n {
        let r = find(&mut comp, i);
        match groups.iter_mut().find(|(k, _)| *k == r) {
            Some((_, v)) => v.push(lits[i].clone()),
            None => groups.push((r, vec![lits[i].clone()])),
        }
    }
    groups.into_iter().map(|(_, v)| v).collect()
}
