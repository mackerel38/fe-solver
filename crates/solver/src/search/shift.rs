//! 平行移動型の推論（f(x + T(y)) = f(x) + S(y) の型など）と、f の値で決まる量・条件つき単射性（docs/TACTICS.md）
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
    /// ずらしの差: 2 変数の単位等式 p(x, y) と、ずらした例 p(x, y ± 1)、p(x ± 1, y)（追加時に f(t + 1) = f(t) + c などの規則で
    /// 書き換わる）の差をとり、項が減るなら加える（Instantiate, LinComb）。例: f(xf(x) + xy) = x² + f(x)f(y) と
    /// f(t + 1) = f(t) + 1 から f(xf(x) + xy + x) = f(xf(x) + xy) + f(x)（左辺の引数は y について 1 次なので、分数の代入で加法性へ）。
    pub(crate) fn shift_differences(&mut self, st: &mut BState) -> Res<()> {
        let mut units: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 2).collect();
        units.sort_by_key(|f| poly_size(&self.e.poly0(*f)));
        units.truncate(self.scaled(3));
        let one = Poly::one();
        let mut shifts: Vec<Vec<Poly>> = vec![
            vec![x(), y().add(&one)],
            vec![x().add(&one), y()],
            vec![x(), y().sub(&one)],
            vec![x().sub(&one), y()],
        ];
        // 平行移動の事実 f(x + K) = a·f(x) + b（K は閉じた式）があれば、K だけのずらしも使う
        for &f1 in &st.units {
            if self.e.nvars(f1) != 1 {
                continue;
            }
            for a in self.e.poly0(f1).top_atoms() {
                if let Atom::F(u) = &a {
                    let k = u.sub(&x());
                    if !k.is_zero() && !k.has_var() && k.as_const().is_none() && poly_size(&k) <= 12 {
                        for sb in [vec![x(), y().add(&k)], vec![x().add(&k), y()]] {
                            if !shifts.contains(&sb) && shifts.len() < 8 {
                                shifts.push(sb);
                            }
                        }
                    }
                }
            }
        }
        for u in units {
            for sb in &shifts {
                if self.closed(st) || !st.units.contains(&u) {
                    return Ok(());
                }
                let key = format!("shiftdiff|{:?}|{:?}", u, sb);
                if !st.tried.insert(key) {
                    continue;
                }
                let inst = self.e.k.instantiate(st.b, u, sb.clone(), 2)?;
                let nf = match self.e.add_fact(st, inst)? {
                    Added::New(nf) => nf,
                    _ => continue,
                };
                if self.e.clause(nf).lits().len() != 1 || self.e.nvars(nf) != 2 {
                    continue;
                }
                let pn = self.e.poly0(nf);
                let pu = self.e.poly0(u);
                // 共通の単項式（閉じた因子の違いは許す）の係数をそろえて引き、項が減るものを探す。
                // 掛ける係数 k は有理数か閉じた式（f(1) など）
                let mut best: Option<Poly> = None;
                for (m, cu) in pu.terms() {
                    let mut k = Poly::zero();
                    for (m2, cn) in pn.terms() {
                        if let Some(qm) = m2.div(m) {
                            let qp = Poly::mono(qm, Q::one());
                            if !qp.has_var() {
                                k = k.add(&qp.scale(&(cn / cu)));
                            }
                        }
                    }
                    if k.is_zero() {
                        continue;
                    }
                    let d = pn.sub(&pu.mul(&k));
                    // f(x), f(y) のように変数そのものに f を適用した原子の数
                    let bare = |p: &Poly| p.top_atoms().iter().filter(|a| matches!(a, Atom::F(u) if u.terms().len() == 1 && u.terms()[0].0.factors().len() == 1 && matches!(u.terms()[0].0.factors()[0], (Atom::Var(_), 1)) && *u.terms()[0].1.numer() == 1.into() && *u.terms()[0].1.denom() == 1.into())).count();
                    if d.has_f() && (d.terms().len() < pn.terms().len() || bare(&d) < bare(&pn)) {
                        best = Some(k);
                        break;
                    }
                }
                let k = match best {
                    Some(k) => k,
                    None => continue,
                };
                let r = self.e.k.lincomb(st.b, 2, vec![(Poly::one(), nf, 0), (k.neg(), u, 0)])?;
                self.bump("shift_diff");
                self.e.add_fact(st, r)?;
            }
        }
        Ok(())
    }

    /// 入れ替えの差: 2 変数の単位等式 p(x, y) = 0 から、x と y を入れ替えた例 p(y, x) = 0 との差
    /// p(x, y) − p(y, x) = 0 を作る（一次結合）。右辺が対称なら f(A(x, y)) − f(A(y, x)) = 0 のような事実になる。
    /// 入れ替えた例そのものは既知として加えないため、差は別に作る必要がある。項が減る（2 つの f の差など）ときだけ加える。
    pub(crate) fn swap_differences(&mut self, st: &mut BState) -> Res<()> {
        let units: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 2).collect();
        let mut n = 0;
        for u in units {
            if n >= self.scaled(8) || self.closed(st) {
                return Ok(());
            }
            let key = format!("swapdiff|{:?}", u);
            if !st.tried.insert(key) {
                continue;
            }
            let p = self.e.poly0(u);
            let ps = crate::engine::swap_xy(&p);
            let d = p.sub(&ps);
            if d.is_zero() || d.terms().len() >= p.terms().len() || !d.has_f() {
                continue;
            }
            n += 1;
            let b = st.b;
            let us = self.e.k.instantiate(b, u, vec![y(), x()], 2)?;
            let k = match scale_ratio(&self.e.poly0(us), &ps) {
                Some(k) => k,
                None => continue,
            };
            let r = self.e.k.lincomb(b, 2, vec![(Poly::one(), u, 0), (Poly::constant(-Q::one() / &k), us, 0)])?;
            self.bump("swap_diff");
            self.e.add_fact(st, r)?;
        }
        Ok(())
    }

    /// この枝で加法性（f(x+y) = f(x) + f(y) − f(0)）が示されていて、加法的な族が解なら、葉を加法的な族で確定する。
    /// 族が A（定数なし）のときは、f(0) = 0 を書き換え規則で示して f(x+y) = f(x) + f(y) の形にする。
    /// 平行移動の事実「∀x,y. f(x + A(y)) − f(x) − B(y) = 0」（A, B は x を含まない）から、
    /// 「ずらし幅が同じなら増分も同じ」: ∀y,z. A(y) − A(z) ≠ 0 ∨ B(y) − B(z) = 0 と、その z = 0 の場合を作る。
    /// 作り方（すべて検証核の規則）: 排中律 A(y) − A(z) = 0 ∨ ≠ 0、合同性 f(x + A(z) + (A(y) − A(z))) = f(x + A(z)) ∨ ≠、
    /// 一次結合で f(x + A(y)) − f(x + A(z)) と元の事実 2 つから x を消す。
    pub(crate) fn shift_lemmas(&mut self, st: &mut BState) -> Res<()> {
        let units: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 2).collect();
        for u in units {
            if self.closed(st) {
                return Ok(());
            }
            let p = self.e.poly0(u);
            for xv in 0..2u32 {
                let yv = 1 - xv;
                let xa = Atom::F(std::rc::Rc::new(Poly::var(xv)));
                // f(x) の係数が −1 になるよう正規化
                let c = match coeff_of_atom(&p, &xa) {
                    Some(c) => c,
                    None => continue,
                };
                let pn = p.scale(&(-Q::one() / &c));
                // x を含む原子は f(x) と f(x + A) の 2 つだけで、f(x + A) の係数は 1
                let mut shift: Option<Poly> = None;
                let mut ok = true;
                for a in pn.top_atoms() {
                    if a == xa || !Poly::from_atom(a.clone()).vars().contains(&xv) {
                        continue;
                    }
                    match &a {
                        Atom::F(arg) if shift.is_none() => {
                            let d = (**arg).sub(&Poly::var(xv));
                            if d.vars().contains(&xv) || coeff_of_atom(&pn, &a) != Some(Q::one()) {
                                ok = false;
                                break;
                            }
                            shift = Some(d);
                        }
                        _ => {
                            ok = false;
                            break;
                        }
                    }
                }
                let a_y = match (ok, shift) {
                    (true, Some(d)) if d.vars().contains(&yv) => d,
                    _ => continue,
                };
                // B(y) = f(x + A) − f(x) − pn の残り（x を含まないこと）
                let fa = Poly::f(Poly::var(xv).add(&a_y));
                let b_y = fa.sub(&Poly::f(Poly::var(xv))).sub(&pn);
                if b_y.vars().contains(&xv) {
                    continue;
                }
                let key = format!("shiftlem|{:?}|{}", u, xv);
                if !st.tried.insert(key) {
                    continue;
                }
                self.bump("shift_lemma");
                // 変数: x = xv, y = yv, z = Var(2)
                let zv = Poly::var(2);
                let mut sz = vec![Poly::var(0), Poly::var(1)];
                sz[yv as usize] = zv.clone();
                let a_z = a_y.subst_vars(&{
                    let mut t = vec![Poly::var(0), Poly::var(1), Poly::var(2)];
                    t[yv as usize] = zv.clone();
                    t
                });
                let b = st.b;
                let uz = self.e.k.instantiate(b, u, sz.clone(), 3)?;
                let diff = a_y.sub(&a_z);
                let eo = self.e.k.eq_or_ne(b, 3, diff.clone())?;
                let (ie, ke) = match find_lit(self.e.clause(eo), &diff) {
                    Some(t) => t,
                    None => continue,
                };
                let base = Poly::var(xv).add(&a_z);
                let cg = self.e.k.congruence(b, 3, base.clone(), vec![(Poly::constant(Q::one() / &ke), eo, ie)])?;
                let target = fa.sub(&Poly::f(base));
                let (ic, kc) = match find_lit(self.e.clause(cg), &target) {
                    Some(t) => t,
                    None => continue,
                };
                // u の保存形 = λ·pn、uz の保存形 = λ·pn(y → z)
                let lam_u = match scale_ratio(&self.e.poly0(u), &pn) {
                    Some(k) => k,
                    None => continue,
                };
                let pnz = {
                    let mut t = vec![Poly::var(0), Poly::var(1), Poly::var(2)];
                    t[yv as usize] = zv.clone();
                    pn.subst_vars(&t)
                };
                let lam_z = match scale_ratio(&self.e.poly0(uz), &pnz) {
                    Some(k) => k,
                    None => continue,
                };
                // pn − pnz − (f(x + A(y)) − f(x + A(z))) = −B(y) + B(z)
                let items = vec![
                    (Poly::constant(Q::one() / &lam_u), u, 0),
                    (Poly::constant(-Q::one() / &lam_z), uz, 0),
                    (Poly::constant(-Q::one() / &kc), cg, ic),
                ];
                let lem = self.e.k.lincomb(b, 3, items)?;
                let lem = self.e.canon_vars(st, lem)?;
                self.e.add_fact(st, lem)?;
                // 周期の補題: x := x − A(−y) で y と −y の例を引くと
                //   f(x + A(y) − A(−y)) − f(x) − (B(y) − B(−y)) = 0（B が偶なら A(y) − A(−y) は周期）
                {
                    let mut neg = vec![Poly::var(0), Poly::var(1)];
                    neg[yv as usize] = Poly::var(yv).neg();
                    let a_neg = a_y.subst_vars(&neg);
                    let b_neg = b_y.subst_vars(&neg);
                    let mut s1 = vec![Poly::var(0), Poly::var(1)];
                    s1[xv as usize] = Poly::var(xv).sub(&a_neg);
                    let mut s2 = s1.clone();
                    s2[yv as usize] = Poly::var(yv).neg();
                    let i1 = self.e.k.instantiate(b, u, s1.clone(), 2)?;
                    let i2 = self.e.k.instantiate(b, u, s2.clone(), 2)?;
                    let e1 = pn.subst_vars(&s1);
                    let e2 = pn.subst_vars(&s2);
                    if let (Some(k1), Some(k2)) = (scale_ratio(&self.e.poly0(i1), &e1), scale_ratio(&self.e.poly0(i2), &e2)) {
                        let per = self.e.k.lincomb(
                            b,
                            2,
                            vec![(Poly::constant(Q::one() / &k1), i1, 0), (Poly::constant(-Q::one() / &k2), i2, 0)],
                        )?;
                        let _ = b_neg;
                        self.bump("shift_period");
                        self.e.add_fact(st, per)?;
                        if self.closed(st) {
                            return Ok(());
                        }
                    }
                }
                // z = 0 の場合
                let mut s0: Vec<Poly> = vec![Poly::var(0), Poly::var(1)];
                let lc = self.e.clause(lem).clone();
                if lc.nvars() == 2 {
                    s0[1] = Poly::zero();
                    let l0 = self.e.k.instantiate(b, lem, s0, 1)?;
                    self.e.add_fact(st, l0)?;
                }
                if self.closed(st) {
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    /// f の値で決まる量の補題: 1 変数の事実 c·f(u) + R(y) = 0 で、u が y を f(y) を通してだけ含むなら
    /// （u = g(f(y))）、f(y) = f(z) のとき u(y) = u(z) なので R(y) = R(z)。
    /// 作り方（すべて検証核の規則）: 排中律 f(y) − f(z) = 0 ∨ ≠ 0、合同性で f(u(y)) = f(u(z)) ∨ ≠、
    /// 一次結合で「R(y) − R(z) = 0 ∨ f(y) − f(z) ≠ 0」、さらに R(z) の f(z) を f(y) に置き換える。
    pub(crate) fn value_lemmas(&mut self, st: &mut BState) -> Res<()> {
        let units: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) == 1).collect();
        let fy = Poly::f(x());
        let fya = Atom::F(std::rc::Rc::new(x()));
        let mut done = 0;
        for u in units {
            if done >= self.scaled(6) || self.closed(st) {
                return Ok(());
            }
            let p = self.e.poly0(u);
            // u = g(f(y)) の形の f の原子（y は f(y) を通してだけ現れる）
            let mut cand: Option<(Atom, Poly)> = None;
            for a in p.top_atoms() {
                if let Atom::F(arg) = &a {
                    if **arg == x() || !arg.vars().contains(&0) {
                        continue;
                    }
                    // arg の中で f(y) を記号 w（Var(5)）に置き換えて、y が残らないこと
                    let (w_arg, _) = replace_atom(arg, &fya, &Poly::var(5));
                    if w_arg.vars().contains(&0) || !w_arg.vars().contains(&5) {
                        continue;
                    }
                    if cand.is_none() {
                        cand = Some((a.clone(), (**arg).clone()));
                    }
                }
            }
            let (atom, arg) = match cand {
                Some(c) => c,
                None => continue,
            };
            let key = format!("valuelem|{:?}", u);
            if !st.tried.insert(key) {
                continue;
            }
            let c = match coeff_of_atom(&p, &atom) {
                Some(c) => c,
                None => continue,
            };
            done += 1;
            self.bump("value_lemma");
            let b = st.b;
            let z = y();
            // u(z): y → z
            let uz = self.e.k.instantiate(b, u, vec![z.clone()], 2)?;
            let fz = Poly::f(z.clone());
            let diff = fy.sub(&fz);
            let eo = self.e.k.eq_or_ne(b, 2, diff.clone())?;
            let (ie, ke) = match find_lit(self.e.clause(eo), &diff) {
                Some(t) => t,
                None => continue,
            };
            // arg(y) − arg(z) = m·(f(y) − f(z))
            let arg_z = arg.subst_vars(&[z.clone()]);
            let m = match crate::polyutil::exact_div(&arg.sub(&arg_z), &diff) {
                Some(m) => m,
                None => continue,
            };
            let cg = self.e.k.congruence(b, 2, arg_z.clone(), vec![(m.scale(&(Q::one() / &ke)), eo, ie)])?;
            let target = Poly::from_atom(atom.clone()).sub(&Poly::f(arg_z.clone()));
            let (ic, kc) = match find_lit(self.e.clause(cg), &target) {
                Some(t) => t,
                None => continue,
            };
            let pz = p.subst_vars(&[z.clone()]);
            let lam_z = match scale_ratio(&self.e.poly0(uz), &pz) {
                Some(k) => k,
                None => continue,
            };
            // p(y) − p(z) − c·(f(arg(y)) − f(arg(z))) = R(y) − R(z)
            let mut items = vec![
                (Poly::one(), u, 0),
                (Poly::constant(-Q::one() / &lam_z), uz, 0),
                (Poly::constant(-(c.clone()) / &kc), cg, ic),
            ];
            // R(z) の f(z) を f(y) に: R(y) − R(z) − (R(y) − R(z)[f(z)→f(y)]) = q·(f(y) − f(z)) の分を排中律のリテラルで足す
            let rdiff = p.sub(&pz).sub(&target.scale(&c));
            let fza = Atom::F(std::rc::Rc::new(z.clone()));
            let (r2, q) = replace_atom(&rdiff, &fza, &fy);
            // rdiff − r2 = q·(f(z) − f(y)) = −q·diff
            items.push((q.scale(&(Q::one() / &ke)), eo, ie));
            let _ = r2;
            let lem = self.e.k.lincomb(b, 2, items)?;
            if let Added::New(nf) = self.e.add_fact(st, lem)? {
                // 「… ∨ f(y) − f(x) ≠ 0」の形なら条件つきの単射性として覚える
                let want = Lit::ne(Poly::f(y()).sub(&Poly::f(x())));
                let c = self.e.clause(nf).clone();
                if c.nvars() == 2 && c.lits().contains(&want) {
                    // ちょうど「y − x = 0 ∨ f(y) − f(x) ≠ 0」なら単射性そのもの（既存の単射性の適用に使う）
                    let injl = Lit::eq(y().sub(&x()));
                    if st.inj.is_none() && c.lits().len() == 2 && c.lits().contains(&injl) {
                        st.inj = Some(nf);
                        self.bump("inj_from_value");
                    } else if st.cinj.len() < 8 {
                        st.cinj.push(nf);
                    }
                }
            }
        }
        Ok(())
    }

    /// 条件つきの単射性「Q(x, y) ∨ f(y) − f(x) ≠ 0」を、単位等式 f(s₁) − f(s₂) = 0 に当てはめて Q を得る（導出原理）
    pub(crate) fn apply_cond_injectivity(&mut self, st: &mut BState) -> Res<()> {
        if st.cinj.is_empty() {
            return Ok(());
        }
        // 当てはめる相手は変数のない事実と小さい 1 変数の事実に限る。1 変数の事実を先に（変数のない事実が多いと予算を使い切って
        // f(x f(x)) = f(x²) のような事実に届かないので）、予算は別々に（1 変数 scaled(8) 回、変数なし scaled(32) 回。合計は以前と同じ。1 変数の予算を大きくすると当てはめが増えすぎる）
        let mut units: Vec<Fact> = st.units.iter().copied().filter(|f| self.e.nvars(*f) <= 1).collect();
        units.sort_by_key(|f| (1 - self.e.nvars(*f), poly_size(&self.e.poly0(*f))));
        let mut budget1 = self.scaled(8);
        let mut budget0 = self.scaled(32);
        for u in units {
            let one = self.e.nvars(u) == 1;
            if (one && budget1 == 0) || (!one && budget0 == 0) {
                continue;
            }
            let p = self.e.poly0(u);
            // 大きさの上限 48（f(x²) − f(x·f(x)) が 31。以前の 30 ではこの事実に当てはめられなかった）
            if p.terms().len() != 2 || poly_size(&p) > 48 {
                continue;
            }
            let (m1, c1) = &p.terms()[0];
            let (m2, c2) = &p.terms()[1];
            if *c1 != -c2.clone() || m1.factors().len() != 1 || m2.factors().len() != 1 || m1.factors()[0].1 != 1 || m2.factors()[0].1 != 1 {
                continue;
            }
            let (s1, s2) = match (&m1.factors()[0].0, &m2.factors()[0].0) {
                (Atom::F(s1), Atom::F(s2)) => ((**s1).clone(), (**s2).clone()),
                _ => continue,
            };
            let nv = self.e.nvars(u);
            if one {
                budget1 -= 1;
            } else {
                budget0 -= 1;
            }
            if self.cinj_on_pair(st, u, &s1, &s2, nv)? {
                return Ok(());
            }
        }
        // 右辺が同じ 2 つの書き換え規則 f(A₁) → R、f(A₂) → R の組: 差 f(A₁) − f(A₂) = 0 を一次結合で作り（正規化すると 0 = 0 に
        // 消えるので事実としては加えず、前提としてだけ使う）、同じように当てはめる（例: f(f(x)²) = x f(x) と f(x²) = x f(x)）
        let rules: Vec<RwRule> = st
            .rules
            .iter()
            .filter(|r| r.nvars <= 1 && matches!(&r.lhs, Atom::F(a) if poly_size(a) <= 24) && poly_size(&r.rhs) <= 24)
            .cloned()
            .collect();
        // 規則の根での例: 1 変数の規則 f(A(x)) → f(B(x)) + p(x)（p は f を含まない x の多項式）で、p の有理根 x₀ では
        // f(A(x₀)) = f(B(x₀))。この例は規則に吸収されて事実としては残らない（加えると 0 = 0 に消える）ので、例化した事実を
        // 前提としてだけ使い、同じように当てはめる（例: f(f(x)²) → f(0) + x² の x₀ = 0 で f(f(0)²) = f(0)。FE-0355 型）
        let mut pts = 0;
        for r in rules.iter().filter(|r| r.nvars == 1) {
            if pts >= self.scaled(8) || st.cinj_pairs >= self.scaled(16) || self.closed(st) {
                break;
            }
            let Atom::F(a) = &r.lhs else { continue };
            let mut fb: Option<Poly> = None;
            let mut rest = Poly::zero();
            let mut ok = true;
            for (m, c) in r.rhs.terms() {
                if !m.factors().iter().any(|(at, _)| matches!(at, Atom::F(_))) {
                    if m.factors().iter().any(|(at, _)| *at != Atom::Var(0)) {
                        ok = false;
                    }
                    rest = rest.add(&Poly::mono(m.clone(), c.clone()));
                } else if fb.is_none() && c.is_one() && m.factors().len() == 1 && m.factors()[0].1 == 1 {
                    if let Atom::F(bp) = &m.factors()[0].0 {
                        fb = Some((**bp).clone());
                    }
                } else {
                    ok = false;
                }
            }
            let (Some(bp), true) = (fb, ok) else { continue };
            if rest.is_zero() {
                continue;
            }
            let cmap = crate::polyutil::coeffs_in(&rest, &Atom::Var(0));
            let deg = cmap.keys().copied().max().unwrap_or(0) as usize;
            let mut cs: Vec<Q> = vec![Q::zero(); deg + 1];
            let mut num = true;
            for (e, c) in &cmap {
                match c.as_const() {
                    Some(q) => cs[*e as usize] = q,
                    None => num = false,
                }
            }
            if !num {
                continue;
            }
            for x0 in crate::polyutil::rational_roots(&cs).into_iter().take(2) {
                let key = format!("cinjpt|{:?}|{}", r.fact, x0);
                if !st.tried.insert(key) {
                    continue;
                }
                let pt = [Poly::constant(x0.clone())];
                let (s1, s2) = (a.subst_vars(&pt), bp.subst_vars(&pt));
                if s1 == s2 {
                    continue;
                }
                let inst = self.e.k.instantiate(st.b, r.fact, pt.to_vec(), 0)?;
                // 例が f(s₁) − f(s₂) の定数倍であること
                let p = self.e.poly0(inst);
                let fa = |t: &Poly| Mono::atom(Atom::F(std::rc::Rc::new(t.clone())));
                let ok2 = p.terms().len() == 2
                    && p.terms().iter().any(|(m, _)| *m == fa(&s1))
                    && p.terms().iter().any(|(m, _)| *m == fa(&s2))
                    && p.terms()[0].1 == -p.terms()[1].1.clone();
                if !ok2 {
                    continue;
                }
                pts += 1;
                st.cinj_pairs += 1;
                self.bump("cinj_rule_point");
                if self.cinj_on_pair(st, inst, &s1, &s2, 0)? {
                    return Ok(());
                }
            }
        }
        // 右辺が同じ組を、左辺と右辺の大きさの和が小さい順に試す（役に立つ組は小さいことが多い）
        let mut cand: Vec<(u32, usize, usize)> = Vec::new();
        for i in 0..rules.len() {
            for j in (i + 1)..rules.len() {
                let (r1, r2) = (&rules[i], &rules[j]);
                if r1.nvars != r2.nvars || r1.rhs != r2.rhs || r1.lhs == r2.lhs {
                    continue;
                }
                let sz = poly_size(&Poly::from_atom(r1.lhs.clone())) + poly_size(&Poly::from_atom(r2.lhs.clone())) + poly_size(&r1.rhs);
                cand.push((sz, i, j));
            }
        }
        cand.sort();
        let mut pairs = 0;
        for (_, i, j) in cand {
            {
                if pairs >= self.scaled(8) || st.cinj_pairs >= self.scaled(16) || self.closed(st) {
                    return Ok(());
                }
                let (r1, r2) = (&rules[i], &rules[j]);
                let key = format!("cinjrule|{:?}|{:?}", r1.fact, r2.fact);
                if !st.tried.insert(key) {
                    continue;
                }
                let (s1, s2) = match (&r1.lhs, &r2.lhs) {
                    (Atom::F(a), Atom::F(b)) => ((**a).clone(), (**b).clone()),
                    _ => continue,
                };
                let t1 = Poly::from_atom(r1.lhs.clone()).sub(&r1.rhs);
                let t2 = Poly::from_atom(r2.lhs.clone()).sub(&r2.rhs);
                let (k1, k2) = match (scale_ratio(&self.e.poly0(r1.fact), &t1), scale_ratio(&self.e.poly0(r2.fact), &t2)) {
                    (Some(a), Some(b)) => (a, b),
                    _ => continue,
                };
                let nv = r1.nvars;
                let d = self.e.k.lincomb(st.b, nv, vec![(Poly::constant(Q::one() / k1), r1.fact, 0), (Poly::constant(-(Q::one() / k2)), r2.fact, 0)])?;
                pairs += 1;
                st.cinj_pairs += 1;
                self.bump("cinj_rule_pair");
                if self.cinj_on_pair(st, d, &s1, &s2, nv)? {
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    /// 単位等式 u（f(s₁) − f(s₂) の定数倍 = 0）に、条件つきの単射性「Q ∨ f(y) − f(x) ≠ 0」を当てはめて Q を加える。閉じたら true
    fn cinj_on_pair(&mut self, st: &mut BState, u: Fact, s1: &Poly, s2: &Poly, nv: u32) -> Res<bool> {
        for ci in st.cinj.clone() {
            for (a, bb) in [(s2.clone(), s1.clone()), (s1.clone(), s2.clone())] {
                let key = format!("cinj|{:?}|{:?}|{}", u, ci, a);
                if !st.tried.insert(key) {
                    continue;
                }
                let inst = self.e.k.instantiate(st.b, ci, vec![a.clone(), bb.clone()], nv)?;
                let want = Lit::ne(Poly::f(bb.clone()).sub(&Poly::f(a.clone())));
                let li = match self.e.clause(inst).lits().iter().position(|l| *l == want) {
                    Some(i) => i,
                    None => continue,
                };
                let r = self.e.k.resolve(st.b, inst, li, u, 0)?;
                self.bump("cinj_apply");
                self.e.add_fact(st, r)?;
                if self.closed(st) {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }
}
