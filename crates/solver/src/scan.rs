//! 計測用の調査（証明には使わない）: 各点で 2 つの候補 g1, g2 を自由に選んだ関数がすべて方程式を満たすか
//! （満たすなら、選び方を非可測な集合で決めた病的な解が存在する）を、データベースの方程式について数える。
use fe_kernel::{Atom, Poly};

fn f_args(p: &Poly) -> Vec<Poly> {
    let mut out: Vec<Poly> = Vec::new();
    p.visit_atoms(&mut |a| {
        if let Atom::F(u) = a {
            if !out.contains(u) {
                out.push((**u).clone());
            }
        }
    });
    out
}

fn eval(p: &Poly, args: &[Poly], choice: &[usize], gs: &[Poly]) -> Poly {
    let mut out = Poly::zero();
    for (m, c) in p.terms() {
        let mut prod = Poly::constant(c.clone());
        for (a, e) in m.factors() {
            let v = match a {
                Atom::F(u) => {
                    let i = args.iter().position(|q| q == &**u).unwrap();
                    let inner = eval(u, args, choice, gs);
                    gs[choice[i]].subst_vars(&[inner])
                }
                other => Poly::from_atom(other.clone()),
            };
            prod = prod.mul(&v.pow(*e));
        }
        out = out.add(&prod);
    }
    out
}

/// 各点で g1, g2 のどちらを選んでも（f の引数ごとに独立に）恒等式になるか
pub fn pointwise_choice_ok(l: &Poly, r: &Poly, g1: &Poly, g2: &Poly) -> bool {
    let d = l.sub(r);
    let args = f_args(&d);
    if args.len() > 12 {
        return false;
    }
    let gs = [g1.clone(), g2.clone()];
    for bits in 0u32..(1u32 << args.len()) {
        let choice: Vec<usize> = (0..args.len()).map(|i| ((bits >> i) & 1) as usize).collect();
        if !eval(&d, &args, &choice, &gs).is_zero() {
            return false;
        }
    }
    true
}

pub fn library() -> Vec<(String, Poly)> {
    let x = Poly::var(0);
    let mut v = vec![
        ("0", Poly::zero()),
        ("1", Poly::int(1)),
        ("-1", Poly::int(-1)),
        ("2", Poly::int(2)),
        ("x", x.clone()),
        ("-x", x.neg()),
        ("2x", x.scale(&fe_kernel::poly::q(2))),
        ("x^2", x.pow(2)),
        ("-x^2", x.pow(2).neg()),
        ("x+1", x.add(&Poly::int(1))),
        ("x-1", x.sub(&Poly::int(1))),
        ("1-x", Poly::int(1).sub(&x)),
        ("-x-1", x.neg().sub(&Poly::int(1))),
    ];
    v.drain(..).map(|(a, b)| (a.to_string(), b)).collect()
}

/// 加法的な A についての展開（計測用。kind: 0 = 制約なし, 1 = A(A(t)) = t, 2 = A(A(t)) = A(t)）で、
/// f(t) := A(t) + g(t) が恒等式になるか
pub fn additive_ok(l: &Poly, r: &Poly, g: &Poly, kind: u8) -> bool {
    let fa = |m: &fe_kernel::Mono| -> Option<Poly> {
        if m.factors().len() == 1 && m.factors()[0].1 == 1 {
            if let Atom::F(u) = &m.factors()[0].0 {
                return Some((**u).clone());
            }
        }
        None
    };
    let apply = |t: &Poly| -> Poly {
        t.transform(&mut |a| match a {
            Atom::F(arg) => {
                let mut out = Poly::zero();
                for (m, c) in arg.terms() {
                    let term = match (kind, fa(m)) {
                        (1, Some(inner)) => inner,
                        (2, Some(inner)) => Poly::f(inner),
                        _ => Poly::f(Poly::mono(m.clone(), fe_kernel::poly::q(1))),
                    };
                    out = out.add(&term.scale(c));
                }
                out.add(&g.subst_vars(&[(*arg).clone()]))
            }
            other => Poly::from_atom(other),
        })
    };
    apply(l).sub(&apply(r)).is_zero()
}
