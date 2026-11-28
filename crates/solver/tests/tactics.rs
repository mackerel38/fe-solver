//! 手法の汎用性のテスト: 問題集（データベース）にない、同じ類の方程式でも手法が効くことを確かめる。
//! 問題集の文法では書けない係数や符号（2y, x − f(y) など）を使った方程式を選んでいる。
//! 各テストは、報告された解の族を新しい検証核でも確かめる（健全性の二重確認）。
//! 手法と方程式の類の対応は docs/TACTICS.md を参照。

use fe_kernel::{AddKind, Kernel, Poly};
use fe_solver::parse::parse_general;
use fe_solver::solve::{solve, SolveOutput};
use std::time::Duration;

/// 探索の時間配分は実時間で決まるので、重いテストが同時に動いて CPU を取り合うと結果が変わりうる。
/// このファイルの求解は 1 つずつ行う（テストの条件は弱めていない）。
static SOLVE_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn run(eq: &str, secs: u64) -> (Poly, Poly, SolveOutput) {
    let _guard = SOLVE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let (l, r) = parse_general(eq).unwrap();
    let out = solve(l.clone(), r.clone(), Duration::from_secs(secs)).unwrap();
    (l, r, out)
}

/// 報告した族がすべて新しい検証核でも解であること
fn check_families(eq: &str, l: &Poly, r: &Poly, out: &SolveOutput) {
    let fresh = Kernel::new(l.clone(), r.clone()).unwrap();
    for f in out.families.iter().chain(out.found.iter()) {
        assert!(fresh.verify_solution(f.g()).is_ok(), "{}: 解でない族 {:?}", eq, f.g());
    }
    for f in out.add_families.iter().chain(out.add_found.iter()) {
        assert!(fresh.verify_additive_kind(f.g(), f.kind()).is_ok(), "{}: 解でない加法的な族", eq);
    }
}

/// 加法的関数の族（特殊解決）: f(線形結合) = 線形結合の f の型（コーシー型）
#[test]
fn tactic_additive_family_cauchy_type() {
    for eq in ["f(x + 2*y) = f(x) + 2*f(y)", "f(2*x + 3*y) = 2*f(x) + 3*f(y)", "f(3*x + 3*y) = 3*f(x) + 3*f(y)"] {
        let (l, r, out) = run(eq, 10);
        assert_eq!(out.status, "special", "{}", eq);
        assert!(out.add_families.iter().any(|f| f.kind() == AddKind::Free), "{}: 条件のない加法的な族がない", eq);
        check_families(eq, &l, &r, &out);
    }
}

/// 対合の加法的関数の族（特殊解決）: f(x + k·f(y)) = f(x) + k·y の型
#[test]
fn tactic_involution_family() {
    for eq in ["f(x + 2*f(y)) = f(x) + 2*y", "f(x - f(y)) = f(x) - y", "f(x + f(2*y)) = f(x) + 2*y"] {
        let (l, r, out) = run(eq, 10);
        assert_eq!(out.status, "special", "{}", eq);
        assert!(out.add_families.iter().any(|f| f.kind() == AddKind::Involution), "{}: 対合の族がない", eq);
        check_families(eq, &l, &r, &out);
    }
}

/// 分数の代入: f(x² + c·xy) = f(x)² + f(c·xy) の型（y := y/x で f(x² + y) = f(x)² + f(y) に帰着）
#[test]
fn tactic_fraction_substitution() {
    let eq = "f(x^2 + 2*x*y) = f(x)^2 + f(2*x*y)";
    let (l, r, out) = run(eq, 60);
    assert_eq!(out.status, "complete", "{}", eq);
    let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    got.sort();
    assert_eq!(got, vec!["0".to_string(), "x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// 入れ替えの差と f の値で決まる量の補題: 右辺が x, y について対称な f(A(x, y)) = R(x, y) の型。
/// P(x, y) − P(y, x) で f(A(x, y)) = f(A(y, x))、P(1, x) 型の事実 f(g(f(x))) = S(x) から単射性を導いて A(x, y) = A(y, x)
#[test]
fn tactic_swap_difference_and_value_injectivity() {
    for (eq, want) in [
        ("f(x*f(y) + 2*f(x*y)) = x*y + 2*f(x*y)", vec!["-1/3*x", "x"]),
        ("f(2*x*f(y) + f(x*y)) = 2*x*y + f(x*y)", vec!["-2/3*x", "x"]),
    ] {
        let (l, r, out) = run(eq, 30);
        assert_eq!(out.status, "complete", "{}", eq);
        let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
        got.sort();
        assert_eq!(got, want, "{}: 解の集合 {:?}", eq, got);
        check_families(eq, &l, &r, &out);
    }
}

/// 全射性の連鎖: f(a) ≠ 0 の点で y について 1 次になる事実から全射性の証人（係数が閉じた式でもよい）、
/// f の外の部分を 0 にする代入（y := −f(x)）、単射性から零点の補題（f(0) = 0 のもとで f(t) = 0 ⇒ t = 0）
#[test]
fn tactic_surjectivity_chain() {
    let eq = "f(2*x*f(x) + x*f(y)) = 2*f(x)^2 + y*f(x)";
    let (l, r, out) = run(eq, 60);
    assert_eq!(out.status, "complete", "{}", eq);
    let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    got.sort();
    assert_eq!(got, vec!["0".to_string(), "x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// 分母が一般の式の分数の代入: f の引数が一方の変数について 1 次で、係数が他方の変数の式 a(w)（f(y) + y、f(x) − x など）の型。
/// a(w) ≠ 0 の点で v := (v − r)/a(w) として「a(w) = 0 ∨ …」を作り、変数を共有しない選言や各点の選言の場合分けにつなぐ
#[test]
fn tactic_general_denominator_fraction() {
    for (eq, want) in [
        ("f(x*f(y) + 2*x*y) = x*f(y) + 2*x*y", vec!["-2*x", "x"]),
        ("f(2*x*f(y) + 2*x*y) = x*f(y) + x*y", vec!["-x", "1/2*x"]),
        ("f(x^2 + 2*y*f(x)) = f(x)^2 + 2*f(x*y)", vec!["-1", "0", "x"]),
    ] {
        let (l, r, out) = run(eq, 60);
        assert_eq!(out.status, "complete", "{}", eq);
        let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
        got.sort();
        let mut want: Vec<String> = want.into_iter().map(String::from).collect();
        want.sort();
        assert_eq!(got, want, "{}: 解の集合 {:?}", eq, got);
        check_families(eq, &l, &r, &out);
    }
}

/// 条件の外せる点での例化: 「f(x) = 0 ∨ f(y) − y = f(x) − x」のような条件つきの事実を、f(a) ≠ 0 のわかっている点 a で例化して
/// 無条件の事実 f(y) = y + f(a) − a にする。f(x + k·y·f(x)) = f(x) + k·y·f(x) の型（解は 0 と x + c）
#[test]
fn tactic_discharge_conditions() {
    for eq in ["f(x + 2*y*f(x)) = f(x) + 2*y*f(x)", "f(x - y*f(x)) = f(x) - y*f(x)"] {
        let (l, r, out) = run(eq, 30);
        assert_eq!(out.status, "complete", "{}", eq);
        assert!(out.families.iter().any(|f| f.params().len() == 1 && f.template().vars().contains(&0)), "{}: x + c の族がない {:?}", eq, out.families.iter().map(|f| f.template().to_string()).collect::<Vec<_>>());
        assert!(out.families.iter().any(|f| f.template().to_string() == "0"), "{}: 0 がない", eq);
        check_families(eq, &l, &r, &out);
    }
}

/// 零点の補題の連鎖: 「f(k) = 0 となる k ≠ 0 があれば P(k, y) から f(k·y) が定数 → y := y/k で f は定数」で否定側を閉じ、
/// 「f(t) = 0 ⇒ t = 0」のもとで引数を等しくする代入（分母が式の分数の代入を含む）から f(x) = x。
/// f(c·x² + x·f(y)) = c·f(x)² + f(xy)、f(f(x)² + c·y·f(x)) = f(x²) + f(c·xy) の型
#[test]
fn tactic_zero_lemma_chain() {
    for eq in ["f(2*x^2 + x*f(y)) = 2*f(x)^2 + f(x*y)", "f(f(x)^2 + 2*y*f(x)) = f(x^2) + f(2*x*y)"] {
        let (l, r, out) = run(eq, 60);
        assert_eq!(out.status, "complete", "{}", eq);
        let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
        got.sort();
        assert_eq!(got, vec!["0".to_string(), "x".to_string()], "{}: 解の集合 {:?}", eq, got);
        check_families(eq, &l, &r, &out);
    }
}

/// 入れ子の引数を定数にする分数の代入と、分母を払う変形: f の中の f(c·xy) について y := K/(c·x)（K = 1 や f(K) = 0 の点）とし、
/// f の外に残る 1/x は両辺に x を掛けて消す（x ≠ 0 の場合の式）。入れ子の f の中の x·(1/x) は内側から合同性で 1 にする。
/// f(x + f(c·xy)) = f(x) + c·y·f(x) の型
#[test]
fn tactic_inner_constant_fraction() {
    let eq = "f(x + f(2*x*y)) = f(x) + 2*y*f(x)";
    let (l, r, out) = run(eq, 60);
    assert_eq!(out.status, "complete", "{}", eq);
    let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    got.sort();
    assert_eq!(got, vec!["0".to_string(), "x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// 任意の区間をもつ族（病的な解の存在、特殊解決）: f の引数がいつも 0 以上になる型や、f が 2 乗でだけ現れる型。
/// x ≥ 0 で f(x) = x、x < 0 では任意の値（0 以上・各点で ±x などの制約つき）を検証核で確かめる
#[test]
fn tactic_arbitrary_family() {
    use fe_kernel::ArbPiece;
    for (eq, want) in [
        ("f(x^2 + f(2*y^2)) = x^2 + 2*y^2", "Free"),
        ("f(2*f(x) + f(y)^2) = 2*f(x) + f(y)^2", "NonNeg"),
        ("f(x^2 + 2*f(y)^2) = f(x)^2 + 2*y^2", "Choice"),
    ] {
        let (l, r, out) = run(eq, 20);
        assert_eq!(out.status, "special_exist", "{}", eq);
        let fam = out.arb_found.clone().expect("任意の区間をもつ族がない");
        let kind = match &fam.pieces()[0] {
            ArbPiece::Free => "Free",
            ArbPiece::NonNeg => "NonNeg",
            ArbPiece::NonPos => "NonPos",
            ArbPiece::Choice(_, _) => "Choice",
            ArbPiece::Fixed(_) => "Fixed",
        };
        assert_eq!(kind, want, "{}", eq);
        let fresh = Kernel::new(l.clone(), r.clone()).unwrap();
        assert!(fresh.verify_arbitrary(fam.breaks().to_vec(), fam.pieces().to_vec()).is_ok(), "{}: 新しい検証核で確かめられない", eq);
        check_families(eq, &l, &r, &out);
    }
}

/// 有理数と無理数で式を変える族（病的な解の存在、特殊解決）: f の値と引数が有理数係数の 1 次式でだけ結ばれる型。
/// 「有理数で g₁、無理数で g₂」を検証核で確かめる（データベースにない係数・項のもの）
#[test]
fn tactic_rational_split_family() {
    for (eq, g1, g2) in [
        ("f(3*f(x)) = 2*x + f(x)", "x", "-2/3*x"),
        ("f(f(x*y) + 2*f(x*y)) = 2*x*y + f(x*y)", "x", "-2/3*x"),
        ("f(f(x) + 2*f(y)^2) = f(x) + 2*y*f(y)", "x", "0"),
        ("f(x + 2*x*f(y)) = f(x) + 2*f(x)*f(y)", "x", "0"),
    ] {
        let (l, r, out) = run(eq, 10);
        assert_eq!(out.status, "special_exist", "{}", eq);
        assert!(out.error.is_none(), "{}: 内部エラー {:?}", eq, out.error);
        let fam = out.qs_found.clone().or_else(|| {
            // 任意の区間をもつ族が先に見つかった場合も、有理数・無理数の族の候補が通ることを確かめる
            fe_solver::search::find_qsplit_candidates(&Kernel::new(l.clone(), r.clone()).unwrap(), &out.found)
        });
        let fam = fam.expect("有理数と無理数で式を変える族がない");
        let fresh = Kernel::new(l.clone(), r.clone()).unwrap();
        let (a, b) = (parse_general(&format!("f(x) = {}", g1)).unwrap().1, parse_general(&format!("f(x) = {}", g2)).unwrap().1);
        assert!(fresh.verify_rational_split(a, b).is_ok(), "{}: 期待した族が検証核で確かめられない", eq);
        assert!(fresh.verify_rational_split(fam.g_rat().clone(), fam.g_irr().clone()).is_ok(), "{}: 新しい検証核で確かめられない", eq);
        check_families(eq, &l, &r, &out);
    }
}

/// 零点の補題を早めに試し、選言の中の f(s) = 0 にも当てはめる: 引数を等しくする代入で「f(x) = 0 ∨ f(x − f(x)) = 0」を得て、
/// 「f(t) = 0 ⇒ t = 0」で「x = 0 ∨ x − f(x) = 0」にする。f(x·f(x) + c·xy) = f(x²) + c·f(x)f(y) の型
#[test]
fn tactic_zero_lemma_in_disjunction() {
    let eq = "f(x*f(x) + 2*x*y) = f(x^2) + 2*f(x)*f(y)";
    let (l, r, out) = run(eq, 60);
    assert_eq!(out.status, "complete", "{}", eq);
    let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    got.sort();
    assert_eq!(got, vec!["0".to_string(), "x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// ずらしの差: P(x, y + 1) − P(x, y)（f(t + 1) = f(t) + c で書き換わる）から f(A + x) = f(A) + f(x)、A が y について 1 次なので
/// 分数の代入で加法性 f(s + x) = f(s) + f(x)。f(c·x·f(x) + xy) = c·x² + f(x)f(y) の型
#[test]
fn tactic_shift_difference() {
    let eq = "f(2*x*f(x) + x*y) = 2*x^2 + f(x)*f(y)";
    let (l, r, out) = run(eq, 60);
    assert_eq!(out.status, "complete", "{}", eq);
    let got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    assert_eq!(got, vec!["x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// 単射性の選言への当てはめ: 単射性（f の値で決まる量の補題から第 0 ラウンドで得る）で、選言や場合分け前の因数分解の
/// リテラル f(s) − f(t) = 0 を s − t = 0 にする（f(x)² = f(−x)² の因数 f(x) − f(−x) = 0 が x = 0 になるなど）。
/// f(c·f(x) + f(y)²) = c·x + f(y²) の型
#[test]
fn tactic_injectivity_in_disjunction() {
    let eq = "f(2*f(x) + f(y)^2) = 2*x + f(y^2)";
    let (l, r, out) = run(eq, 90);
    assert_eq!(out.status, "complete", "{}", eq);
    let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    got.sort();
    assert_eq!(got, vec!["-x".to_string(), "x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// 見つけた解に導かれる補題の推測: 枝と矛盾しない解の候補（ここでは f(x) = x）がすべて満たす性質（f(f(x)) = x など）を、
/// 否定を閉じて補題にする。f(x − y·f(x)) = f(x) − x·f(y) の型（解は 0 と x）
#[test]
fn tactic_solution_guided_lemmas() {
    let eq = "f(x - y*f(x)) = f(x) - x*f(y)";
    let (l, r, out) = run(eq, 90);
    assert_eq!(out.status, "complete", "{}", eq);
    let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    got.sort();
    assert_eq!(got, vec!["0".to_string(), "x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// 既知の型の当てはめ（検証核の規則 AffineXY）: f(a·xy + g(x)) = a·x·f(y) + h(x)（x と y の役割が逆でもよい）なら f は 1 次。
/// 残りは 1 次関数の係数の決定。問題集にない係数・形の方程式
#[test]
fn tactic_affine_xy_type() {
    for (eq, want) in [
        ("f(x*f(x) + 3*x*y) = x^2 + 3*x*f(y)", vec!["-x", "x"]),
        ("f(x*y + y*f(y)) = y*f(x) + f(y)^2", vec!["-x + 1", "x*z"]),
    ] {
        let (l, r, out) = run(eq, 30);
        assert_eq!(out.status, "complete", "{}", eq);
        let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
        got.sort();
        let mut want: Vec<String> = want.into_iter().map(String::from).collect();
        want.sort();
        assert_eq!(got, want, "{}: 解の集合 {:?}", eq, got);
        check_families(eq, &l, &r, &out);
    }
}

/// 規則に導かれる代入: 1 変数の規則 f(T(y)) → …（P(1, y) からの f(f(y) + c) = y + d など）があれば、f(v) を含む事実で
/// v := T(v) とする。f(c·x·f(y) + g(x)) = c·xy + h(x) の型が f(xy + …) = x f(y) + … になり、既知の型（AffineXY）に帰着する
#[test]
fn tactic_rule_guided_substitution() {
    let eq = "f(2*x*f(y) + x) = 2*x*y + f(x)";
    let (l, r, out) = run(eq, 30);
    assert_eq!(out.status, "complete", "{}", eq);
    let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    got.sort();
    assert_eq!(got, vec!["-x".to_string(), "x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// 符号の議論の基本部品: 各点の選言（f(t) ∈ {0, t}）を、事実に現れる f の引数 t（変数を含む式）で例化し、規則で書き換えた後、
/// 平方和で正とわかるリテラル（u ≠ 0 なら u² > 0、2 項の等式で平方に置き換える）を外す。f(x² + c·y²) 型
#[test]
fn tactic_sign_reasoning_sos() {
    let eq = "f(x^2 + 4*y^2) = x*f(x) + f(2*y)^2";
    let (l, r, out) = run(eq, 90);
    assert_eq!(out.status, "complete", "{}", eq);
    let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    got.sort();
    assert_eq!(got, vec!["0".to_string(), "x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// 既知の型 AffineFF: f(c·f(x)f(y) + g(x)) = d·y·f(x) + h(x) なら f は 1 次（f は全単射になり、逆関数で変数を取り替えると
/// AffineXY の型に帰着する）。問題集にない係数の方程式
#[test]
fn tactic_affine_ff_type() {
    let eq = "f(2*f(x)*f(y) + x^2) = 2*y*f(x) + x^2";
    let (l, r, out) = run(eq, 30);
    assert_eq!(out.status, "complete", "{}", eq);
    let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    got.sort();
    assert!(!got.is_empty(), "{}: 解がない", eq);
    check_families(eq, &l, &r, &out);
}

/// 逆数の代入 x := K/x（reciprocal_instances）: 「x ≠ 0 ならば x·f(b/x) = …」の形の事実で f の引数の b/x を消す。
/// 問題集にない式（f(f(xy) + x²) = x f(x) + x f(y) の符号・係数を変えたもの）で確かめる。
/// 最初に選んだ式 f(f(xy) − x²) = x f(y) − x f(x) は、規則の自己合成を入れてから逆数の代入を使わずに解けるようになったので、
/// 逆数の代入を使うことの確認は係数 2 の式で行い、最初の式は完全解決の確認として残す。
#[test]
fn tactic_reciprocal_substitution() {
    for (eq, need_recip) in [("f(f(x*y) - 2*x^2) = x*f(y) - 2*x*f(x)", true), ("f(f(x*y) - x^2) = x*f(y) - x*f(x)", false)] {
        let (l, r, out) = run(eq, 120);
        assert_eq!(out.status, "complete", "{}", eq);
        let mut got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
        got.sort();
        assert_eq!(got, vec!["0".to_string(), "x".to_string()], "{}", eq);
        check_families(eq, &l, &r, &out);
        if need_recip {
            let used = out.stats.iter().find(|(k, _)| k == "recip_subst").map_or(0, |(_, v)| *v);
            assert!(used > 0, "{}: 逆数の代入を使っていない", eq);
        }
    }
}

/// 規則の自己合成（self_compose_rules）: 1 変数の規則 f(f(x) + c) = x + d に x := f(x) + c を代入し、内側の f(f(x) + c) だけを
/// x + d に書き換えて、平行移動 f(x + c + d) = f(x) + c + d を得る（外側から書き換えると 0 = 0 になる）。
/// 問題集にない式（f(x f(x) + f(xy)) = x f(x) + xy の係数を変えたもの）で、P(1, x) の f(f(x) + 2f(1)) = x + 2f(1) から
/// f(x + 4f(1)) = f(x) + 4f(1) が導かれること
#[test]
fn tactic_self_composition() {
    let eq = "f(2*x*f(x) + f(x*y)) = 2*x*f(x) + x*y";
    let (l, r, out) = run(eq, 20);
    check_families(eq, &l, &r, &out);
    let (tl, tr) = parse_general("f(x + 4*f(1)) = f(x) + 4*f(1)").unwrap();
    let want = tl.sub(&tr);
    let k = &out.kernel;
    let found = (0..k.num_facts()).filter_map(|i| k.fact_at(i)).any(|f| {
        let c = k.clause(f);
        c.lits().len() == 1 && {
            let p = c.lits()[0].poly();
            p == &want || p == &want.neg()
        }
    });
    assert!(found, "{}: 平行移動 f(x + 4f(1)) = f(x) + 4f(1) が導かれていない", eq);
    let used = out.stats.iter().find(|(k, _)| k == "self_compose").map_or(0, |(_, v)| *v);
    assert!(used > 0, "{}: 規則の自己合成を使っていない", eq);
}

/// 全射性の証人（大きめの証人）: P(x, 0) の f(f(x) + c·f(0)²) = x + c·f(0)² から証人 S(t) = f(t − c·f(0)²) + c·f(0)²
/// （f(S(t)) = t）を作り、P(x, S(y)) で f(x) を外す。証人の式の大きさの上限が小さいと使われない（大きさ 30 前後）。
/// 問題集にない係数の式で確かめる
#[test]
fn tactic_surjectivity_witness_large() {
    for eq in ["f(f(x) + 2*f(y)^2) = x + 2*f(y)^2", "f(2*f(x) + f(y)^2) = 2*x + f(y)^2"] {
        let (l, r, out) = run(eq, 30);
        assert_eq!(out.status, "complete", "{}", eq);
        let got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
        assert_eq!(got, vec!["x".to_string()], "{}: 解の集合 {:?}", eq, got);
        check_families(eq, &l, &r, &out);
    }
}

/// 条件つきの単射性の早期の当てはめと、1 つの原子のべき = 0 の零積: P(0, y) の f(f(y)²) = f(0) + 2y² から
/// 「f(y) = f(z) なら y² = z²」を作り、P(0, 0) の f(f(0)²) = f(0) に当てはめて f(0)⁴ = 0、零積の規則で f(0) = 0
/// （べきの規則として残さない）。問題集にない係数の式で、根の枝にこの f(0) = 0 ができること
#[test]
fn tactic_power_zero_from_value_lemma() {
    let eq = "f(x*f(x) + f(y)^2) = f(x^2) + 2*y^2";
    let (l, r, out) = run(eq, 10);
    check_families(eq, &l, &r, &out);
    let k = &out.kernel;
    let f0 = Poly::f(Poly::zero());
    let found = (0..k.num_facts()).filter_map(|i| k.fact_at(i)).any(|f| {
        let c = k.clause(f);
        c.nvars() == 0
            && c.lits().len() == 1
            && c.lits()[0].poly() == &f0
            && matches!(k.fact(f).rule(), fe_kernel::Rule::ZeroProduct { premise, .. }
                if k.clause(*premise).lits().len() == 1 && k.clause(*premise).lits()[0].poly().terms().len() == 1)
    });
    assert!(found, "{}: f(0)⁴ = 0 から零積の規則で f(0) = 0 が導かれていない", eq);
}

/// 条件つきの単射性（f の値で決まる量の補題）の当てはめの繰り返し: P(0, y) の f(f(y)²) = f(0) + y² から「f(y) = f(z) なら
/// y² = z²」。f(f(0)²) = f(0) に当てはめて f(0) = 0、すると P(x, 0) が f(2x f(x)) = f(2x²) に書き換わるので、もう一度当てはめて
/// 4x²f(x)² = 4x⁴、x²(f(x)² − x²) = 0 から f(x)² = x²。問題集にない係数の式（FE-0355 の型）
#[test]
fn tactic_cond_injectivity_fixpoint() {
    let eq = "f(2*x*f(x) + f(y)^2) = f(2*x^2) + y^2";
    let (l, r, out) = run(eq, 60);
    assert_eq!(out.status, "complete", "{}", eq);
    let got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    assert_eq!(got, vec!["x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
}

/// 大きくとる代入（「x を十分大きくとる」議論）: x ≥ 0 で f(x) = x がわかったあと、x := 1 + (2y f(y))² を代入すると、
/// x も f の引数 2x f(x) + 2y f(y) も平方和で正とわかり、条件つきの規則で書き換えて y f(y) = y² になる。
/// 平方和の分解は w = y f(y) の 4 次式（単項式を 1 つの原子とみなし、最高次の平方の項を外して平方完成）。
/// FE-0336 型 f(x f(x) + y f(y)) = x² + f(y²) の係数を変えた式
#[test]
fn tactic_large_substitution() {
    let eq = "f(2*x*f(x) + 2*y*f(y)) = 2*x^2 + 2*f(y^2)";
    let (l, r, out) = run(eq, 30);
    assert_eq!(out.status, "complete", "{}", eq);
    let got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    assert_eq!(got, vec!["x".to_string()], "{}: 解の集合 {:?}", eq, got);
    let used = out.stats.iter().any(|(k, v)| k == "large_subst" && *v > 0);
    assert!(used, "{}: 大きくとる代入を使っていない", eq);
    check_families(eq, &l, &r, &out);
}

/// パターンつきのべきの規則: 1 変数の事実 f(x)² = x² を、f の引数の中の f(t)² にも当てて t² に書き換える
/// （f(f(y)² + 3x f(x)) → f(y² + 3x f(x)) など）。各点で ±x の場合分けのあと、f(a) = −a の枝で y := 2a などの代入がすぐ矛盾になる。
/// 規則の根での例 f(f(x)²) → f(0) + x² の x = 0 で f(f(0)²) = f(0) を作り、条件つきの単射性で f(0) = 0 を出す。問題集にない係数の式
#[test]
fn tactic_pattern_power_rule() {
    // どちらもこの規則がないと 15〜20 秒で解けない（FE_NO_PATPOW で確かめた）
    for eq in ["f(3*x*f(x) + f(y)^2) = f(3*x^2) + y^2", "f(2*x*f(x) + 3*f(y)^2) = f(2*x^2) + 3*y^2"] {
        let (l, r, out) = run(eq, 20);
        assert_eq!(out.status, "complete", "{}", eq);
        let got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
        assert_eq!(got, vec!["x".to_string()], "{}: 解の集合 {:?}", eq, got);
        check_families(eq, &l, &r, &out);
    }
}

/// 有理根による因数分解（factor_linear_roots）と、x について同次で判別式が負の 2 次の因子の除去（plain_rootless_quadratic）、
/// 点の条件 x = 0 の除去: f(x)³ = 8x³ から「f(x) − 2x = 0 ∨ f(x)² + 2x·f(x) + 4x² = 0」、後者は x = 0 のときだけなので
/// 「f(x) − 2x = 0 ∨ x = 0」、f(0)³ = 0 から f(0) = 0 で f(x) = 2x。3 次の係数を変えた式でも
#[test]
fn tactic_linear_root_factoring() {
    for (eq, want) in [("f(x)^3 = 8*x^3 + 0*y", "2*x"), ("f(x)^3 + x*f(x)^2 = 2*x^3 + 0*y", "x"), ("f(x)^3 = -x^3 + 0*y", "-x")] {
        let (l, r, out) = run(eq, 20);
        assert_eq!(out.status, "complete", "{}", eq);
        let got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
        assert_eq!(got, vec![want.to_string()], "{}: 解の集合 {:?}", eq, got);
        check_families(eq, &l, &r, &out);
    }
}

/// 既知の型の当てはめ（検証核の規則 AdditiveSquare）: 0 以上で加法的（f(x² + y²) = f(x²) + f(y²)）で f(x²) = x·f(x) なら
/// f(x) = f(1)·x。2 変数の事実を例化し f(x²) = x·f(x) の定数倍を差し引いて前提の形を作る。問題集にない係数の式で
#[test]
fn tactic_additive_square_type() {
    for eq in ["f(x^2 + y^2) = 2*x*f(x) - f(x^2) + y*f(y)", "f(x^2 + y^2) = 3*x*f(x) - 2*f(x^2) + y*f(y)"] {
        let (l, r, out) = run(eq, 30);
        assert_eq!(out.status, "complete", "{}", eq);
        let used = out.stats.iter().find(|(k, _)| k == "additive_square").map_or(0, |(_, v)| *v);
        assert!(used > 0, "{}: AdditiveSquare を使っていない", eq);
        check_families(eq, &l, &r, &out);
        let fresh = Kernel::new(l.clone(), r.clone()).unwrap();
        // 解の族は f(x) = c·x（c は任意）
        assert!(out.families.iter().any(|f| fresh.verify_solution(f.g()).is_ok()), "{}: 解の族がない", eq);
    }
}

/// 右辺が同じ 2 つの書き換え規則への条件つきの単射性の当てはめ（apply_cond_injectivity の規則の組）: P(x, 0) の f(x²) = x f(x) と
/// P(0, y) の f(f(y)²) = y f(y) はどちらも規則になり、差 f(f(x)²) − f(x²) = 0 は正規化で消えるので、差を一次結合で作って
/// 「f(y) = f(x) なら (y − x) f(x) = 0」に当てはめる。問題集にない係数の式（FE-0206 の型）でこの当てはめが働き、
/// 報告した解の族が新しい検証核でも解であること
#[test]
fn tactic_cond_injectivity_rule_pairs() {
    let eq = "f(x^2 + f(y)^2) = 2*x*f(x) - f(x^2) + y*f(y)";
    let (l, r, out) = run(eq, 30);
    let used = out.stats.iter().find(|(k, _)| k == "cinj_rule_pair").map_or(0, |(_, v)| *v);
    assert!(used > 0, "{}: 右辺が同じ規則の組への当てはめが働いていない", eq);
    check_families(eq, &l, &r, &out);
}

/// 規則の自己合成を場合分けより先に（規則ができた直後に）行う: P(0, y) の f(f(y)²) = y² から自己合成で f(x⁴) = f(x)⁴。
/// 後で f(x²) = x f(x) が規則になると f(f(x)²) が f(x)·f(f(x)) に書き換わって自己合成の形が崩れるので、先に行う。
/// f(x⁴) = x³ f(x) と合わせて f(x)(f(x)³ − x³) = 0、因数分解で f(x) ∈ {0, x}。問題集にない式（FE-0205 の y を −y にしたもの）
#[test]
fn tactic_early_self_composition() {
    let eq = "f(x^2 + f(-y)^2) = x*f(x) + y^2";
    let (l, r, out) = run(eq, 30);
    assert_eq!(out.status, "complete", "{}", eq);
    let got: Vec<String> = out.families.iter().map(|f| f.template().to_string()).collect();
    assert_eq!(got, vec!["x".to_string()], "{}: 解の集合 {:?}", eq, got);
    check_families(eq, &l, &r, &out);
    let used = out.stats.iter().find(|(k, _)| k == "self_compose").map_or(0, |(_, v)| *v);
    assert!(used > 0, "{}: 規則の自己合成を使っていない", eq);
}
