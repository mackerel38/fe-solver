# 手法の一覧

このソルバが使う手法を、検証核の規則・解の表現・探索の手法・足りない手法の系統に分けてまとめる。
手法を加えたり変えたりしたら、この一覧を更新する。各手法には「効く方程式の類」と「対応するテスト」を書く。

- 検証核: `crates/kernel`（事実を作れるのはここの規則だけ）
- 探索: `crates/solver/src/search/`（どの規則をどの順で呼ぶかを決める）、`engine.rs`（証明つきの書き換え）。
  手法ごとのファイル: `mod.rs`（探索の流れ）、`substitution.rs`（3.1 代入）、`elimination.rs`（3.2 消去・因数分解）、
  `splits.rs`（3.3 場合分け）、`lemmas.rs`（単射性・零点の補題）、`properties.rs`（3.4 性質・既知の型）、
  `reduction.rs`（3.5 帰着）、`finalize.rs`（3.6 解の形の確定）、`shift.rs`（3.8 対称性・値の補題・平行移動型）、
  `util.rs`（共通の補助関数）
- テスト: 規則ごと `crates/kernel/tests/rules.rs`、負のテスト `crates/solver/tests/negative.rs`、
  手法の汎用性（データベース外の方程式）`crates/solver/tests/tactics.rs`

## 1. 検証核の規則（事実を作る規則）

| 規則 | 内容 | テスト（rules.rs） |
|---|---|---|
| Axiom | 与えられた方程式 | axiom_is_the_equation |
| Instantiate | 全称の事実の変数に任意の式を代入する | instantiate_ok_and_errors |
| LinComb | 等式リテラルの多項式係数の一次結合（他のリテラルは選言として残る） | lincomb_ok_and_errors |
| Congruence | p = 0 なら f(u + m·p) = f(u)（他のリテラルは残る） | congruence_ok_and_errors |
| EqOrNe | p = 0 ∨ p ≠ 0（排中律のリテラル版） | eq_or_ne_rule |
| ZeroProduct / NonzeroFactor | 積が 0 なら因子のどれかが 0、0 でない因子で割る | zero_product_and_nonzero_factor |
| Resolve | 導出原理（L ∨ A と ¬L ∨ B から A ∨ B） | resolve_ok_and_errors |
| Trichotomy / StrictNe | 三分律、> 0 なら ≠ 0 | trichotomy_and_strict_ne |
| PosComb / MulIneq | 非負の結合、不等式の積 | pos_comb_rules, mul_ineq_rule |
| SquareRange | 変数が 2 乗でだけ現れる事実を t ≥ 0 の事実にする | square_range_rule |
| InvAxiom / Weaken | u = 0 ∨ u·inv(u) = 1、A から A ∨ B | inv_axiom_and_weaken |
| CauchyBounded | 加法的で片側に有界なら 1 次関数 | cauchy_bounded_rule |
| AffineXY | 既知の型 f(a·xy + g(x)) = a·x·f(y) + h(x)（g, h は y を含まない。x と y の役割が逆でもよい。前提は「x = 0 ∨ …」の x ≠ 0 でだけ成り立つ形でもよい）なら f(x) = (f(1) − f(0))x + f(0)（D35, D37） | affine_xy_rule |
| AffineFF | 既知の型 f(c·f(x)f(y) + g(x)) = d·y·f(x) + h(x)（c, d ≠ 0）なら f は 1 次（全単射になり、逆関数で変数を取り替えると x ≠ 0 版の AffineXY に帰着。D37） | affine_ff_rule |
| （解の族の検証）verify_solution / verify_piecewise / verify_additive(_kind) / verify_arbitrary | 事実は作らず、解の族の値（検証済みの印）だけを作る。詳細は 2 節 | 2 節の各テスト |
| ImportLemma | 別に解いた方程式（補題）の解の集合を取り込む | import_lemma_rule |
| 場合分け | 変数を共有しない選言の分割（SplitComponents）、排中律（SplitExcludedMiddle）、Merge、AbandonSplit | split_components_rejects_pointwise_disjunction, merge_rules, abandon_split_rule など |

## 2. 解の表現と検証

| 表現 | 検証 | 確定（葉を閉じる） | テスト |
|---|---|---|---|
| 多項式の族 f(x) = g(x; c…)（パラメータは独立な記号） | verify_solution（代入して恒等式） | mark_solution（∀x f(x) = g(x)） | verify_solution_rule |
| 区分的な族（区切り点、各区間で多項式） | verify_piecewise（x, y の符号と引数の区間で場合分け） | mark_piecewise（区間ごとの事実） | piecewise_verification, piecewise_marking |
| 加法的関数を含む族 f(x) = A(x) + g(x)（A は任意の加法的関数） | verify_additive（A を有理数係数の和で展開して恒等式） | mark_additive（f − g が加法的） | verify_additive_rule, mark_additive_rule |
| 条件つきの加法的な族（A(A(x)) = x の対合・A(A(x)) = A(x) の射影） | verify_additive_kind（A(A(u)) を u・A(u) に置き換えて展開） | mark_additive_constrained（加法性 + 条件） | additive_kinds_rule |
| 任意の区間をもつ族（区分的な族の一部の開区間で、f が任意の値・0 以上 / 以下の任意の値・各点で 2 つの式の一方）。病的な解の存在の証明（特殊解決）に使う | verify_arbitrary（区分的な族と同じ場合分けで、任意の区間での値 f(v) を引数ごとに独立な記号として恒等式を確かめる。0 以上 / 以下の記号の符号は区間の判定に使い、各点の選択は 2 通りに分けて同じ引数の選択をそろえる。D34） | なし（存在の証明だけ。解の集合を決めたと主張しない。complete / special と同時に成り立てば内部エラー） | arbitrary_family_verification, tactic_arbitrary_family, negative_no_arbitrary_family_for_rigid_equations, negative_arbitrary_family_examples_are_genuine |

まだ表現できない解の型（失敗の分析で見つかったもの）:
- パラメータを含む区分的な族（x ≠ 0 で 0、x = 0 で任意の c）。試作したが不採用（D30）
- 区切り点がパラメータの区分的な族（x ≥ c で x、x < c で −x）
- 半直線上で任意の関数、各点で ±x を自由に選ぶ解: 区切り点 0 で片側が x・−x・0、反対側が任意のものは、任意の区間をもつ族で
  病的な解の存在まで示せるようになった（D34）。解の集合全体（集合 S の閉包条件で決まる族など）はまだ表現できない
- 乗法的・指数型（ℚ 上のベクトル空間で作る）、2 倍で閉じた集合で決まる解、像が部分群で剰余類の代表元を任意に選ぶ解（FE-0007 型）

## 3. 探索の手法

### 3.1 代入（事実の例化）
| 手法 | 何をするか | 効く類・例 | テスト |
|---|---|---|---|
| 基本の代入 | 0, ±1, ±x, f(x), f(0), 2x, 2, ±1/2 の組を 2 変数の事実に代入 | ほぼすべて | 全体の計測 |
| 2 変数の代入 | P(f(x), y), P(x, f(y)), P(−x, y), P(y, x), P(f(x), f(y)) など | 単射・全射の議論 | 全体の計測 |
| ずらし・和差の代入 | P(x, y ± 1), P(x + 1, y), P(x, 2y), P(x − 1, y), P(x, y ± f(0)), P(x + y, −y), P(x ± y, y), P(x, y − x), P(x ± f(0), y) | 解答で多い P(x, y + c) 型 | 全体の計測 |
| 特別な点 | 場合分けで導入した定数（f(a) ≠ 0 の a など）、f の値が定数とわかる点 | 零点・不動点を使う議論 | 全体の計測 |
| 打ち消しの代入 | f の引数を変数や 0 にする（1 次の変換、正定値化） | f(x + g(y)) 型 | 全体の計測 |
| 引数を等しくする代入 | 2 つの f の引数の差が 1 次なら解く、v·(av + b) なら v で割って解く、係数が閉じた可逆な式なら逆数で解く | f(x² + x f(y)) = f(x²) + f(xy) など | 全体の計測 |
| 分数の代入 | v := (v − r)/(c·w) など。逆数の公理で w ≠ 0 の場合、排中律と合同性で w = 0 の場合を作り、導出原理で ∀x,y の等式にする | f(x² + c·xy) = f(x)² + f(c·xy) など（y := y/x で帰着） | tactic_fraction_substitution |
| 分母が一般の式の分数の代入 | f の引数が変数 v について 1 次で係数が他方の変数 w の式 a(w)（f(y) + y、f(x) − x など）なら、v := (v − r)/a(w)、v := −r/a(w)、2 つの引数の差についても同様。t = inv(a(w)) を含む式を a(w)·t = 1 で簡約し（主項の書き換え）、逆数の公理・合同性・一次結合で「a(w) = 0 ∨ E' = 0」（InvAxiom, Congruence, LinComb）。第 0 ラウンドから | f(xf(y) + xy) = xf(y) + xy（y ごとに x := x/(f(y) + y)）、f(x² + yf(x)) = f(x)² + f(xy)（y := x²/(x − f(x)) で各点の選言 f(x) ∈ {0, x}） | tactic_general_denominator_fraction |
| 入れ子の引数を定数にする分数の代入 | f の引数（入れ子の中も含む）が c·xy なら v := K/(c·w)（K = 1, −1, この枝で f の値がわかる閉じた点）。w ≠ 0 の場合の合同性を入れ子の内側から作り（inv_items）、f の外に残る 1/w は両辺に w^k（k ≤ 2）を掛けて消す（逆数の公理で w^k·(1/w)^k = 1、LinComb）。w = 0 の場合は排中律で別に示す | P(x, 1/x)、f(s) = 0 の s で P(x, s/x)（f(x + f(xy)) = f(x) + y·f(x) など） | tactic_inner_constant_fraction |
| 規則に導かれる代入 | 1 変数の規則 f(T(v)) → …（T は f を含む）があれば、f(v) を（入れ子の中も含めて）含む 2 変数・1 変数の事実で v := T(v)（Instantiate、追加時に規則で書き換わる）。T の変数が f の中にしかない場合（f(x) + c）も含む | P(1, y) の f(f(y) + c) = y + d から y := f(y) + c。f(x f(y) + g(x)) = xy + h(x) を既知の型 f(xy + …) = x f(y) + … にする | tactic_rule_guided_substitution |
| 規則の自己合成 | 1 変数の規則 f(T(x)) = R(x)（T は f(x) を含む）に x := T(x) を代入し、内側の f(T(x)) だけを合同性で R(x) に書き換える（外側から書き換えると 0 = 0 になるので明示的に作る。Instantiate, Congruence, LinComb） | P(1, y) の f(f(y) + c) = y + d から平行移動 f(y + c + d) = f(y) + c + d（f(x f(x) + f(xy)) = x f(x) + xy など） | tactic_self_composition |
| 全射性の証人 | f(u(x)) = a·x + b なら v := u((v − b)/a) で f(v) を v にする（証人の式の大きさの上限 40。f(x − f(0)²) + f(0)² が 30）。係数 a は 0 でない有理数か、逆数のわかる閉じた式（f(a) ≠ 0 の f(a) など）。2 変数の事実に加えて、x が f(x) を通してだけ現れる 1 変数の事実にも代入する | f(f(x) + …) 型、f(xf(x) + xf(y)) = f(x)² + yf(x)（f(a) ≠ 0 の点で y について 1 次） | tactic_surjectivity_chain, tactic_surjectivity_witness_large |
| f の外の部分を 0 にする代入 | v を引数に含む f を除いた部分を c₁·v + c₀ とみて、c₁ が定数でなく c₀ が c₁ で割り切れるなら v := −c₀/c₁ | f(x)² + y·f(x) = f(x)(y + f(x)) で y := −f(x) | tactic_surjectivity_chain |
| 1 変数の事実の自己代入 | −x, 0, 1, f(x), ±x², −1, x ± 1 | 1 変数の事実の整理 | 全体の計測 |
| 右辺を 0 にする代入 | 1 変数の事実から x を引数に含む最大の f の項を除いた残りを単項式の因子で割り、x について 1 次 a·x + c（c は閉じた式）なら x := −c/a（Instantiate） | f(x f(x)) = f(x)(x + f(0)) で x := −f(0)（零点の事実が出る） | 全体の計測 |
| 逆数の代入 x := K/x | 1 変数の事実（条件「x = 0」つきでもよい）の f の引数に K/x（K は 0 でない有理数か逆数のわかる閉じた式）があれば x := K/x とし、K·(K/x)⁻¹ を x に約す（逆数の公理 2 つと排中律・一次結合・導出原理で x = 0 ∨ (K/x)⁻¹ = x/K を作り、合同性で f の引数の中を置き換える）。f の外に残る 1/x は x^k（k ≤ 2）を掛けて消す。結果は「x = 0 ∨ …」。分数の代入で f の引数がちょうど K/x の形の逆数だけが残る場合は、その結果も条件つきの事実として持つ（InvAxiom, EqOrNe, LinComb, Resolve, Instantiate, Congruence） | f(x² + f(xy)) = x f(x) + x f(y) の P(x, b/x)（f(b) = 0）から x ≠ 0 で x·f(b/x) = 0、x := b/x で f(x) = 0 | tactic_reciprocal_substitution |
| 逆数のわかる係数での 1 次の代入 | 1 変数の事実の f の引数が c·x + d（c は逆数のわかる閉じた式）なら x := (x − d)/c。安くて決定的なので、場合分けより先に毎ラウンド（Instantiate） | 零点の補題の否定側: f(k) = 0, k ≠ 0 から f(k·x) = 0、x := x/k で f ≡ 0 | tactic_zero_lemma_chain |
| 条件の外せる点での例化 | 2 つ以上のリテラルをもつ事実の等式リテラル p(w) = 0 について、この枝の閉じた ≠ の事実で p(K) ≠ 0 とわかる定数 K で w := K と例化（追加時に既知の ≠ でリテラルが外れる。Instantiate, Resolve）。場合分けより先に毎ラウンド | 「f(x) = 0 ∨ f(y) − y = f(x) − x」と f(a) ≠ 0 から f(y) = y + f(a) − a（f(x + y·f(x)) = f(x) + y·f(x) の型） | tactic_discharge_conditions |

### 3.2 書き換え・消去
- 証明つきの書き換え（engine.rs）: 1 変数の単位等式を「大きい原子 → 小さい式」の規則にして、事実を正規化する。べき・逆数の規則、条件付き規則（平方和で条件を外す）
- 消去: 1 変数・2 変数の単位等式の一次結合で原子を消す
- 右辺が同じ事実の比較: c·f(A₁) = R と c·f(A₂) = R から f(A₁) = f(A₂)
- 加法性による展開: 加法性がわかった枝で f(和) を f の和にする
- 条件つきの事実の整理: 1 つの変数しか使わない 2 変数の節は 1 変数にし（Instantiate）、等式リテラルの単項式の因子を零積で分ける
  （f(x)² = 0 → f(x) = 0。ZeroProduct）。分母が一般の式の分数の代入の結論に使う
- 1 つの原子のべき = 0: 変数が 1 つまでの単位等式 c·a^k = 0（k ≥ 2）は、加える時点で零積の規則（ZeroProduct）で a = 0 に直す
  （べきの規則として残すと a = 0 を書き換えに使えない。例: f(0)⁴ = 0 から f(0) = 0）（tactic_power_zero_from_value_lemma）
- 閉じた u ≠ 0 の逆数: 仮定や事実として加わったときに加えて、書き換えで新しく閉じた u ≠ 0 になったとき
  （f(b) − b ≠ 0 と f(b) = 0 から b ≠ 0 など）にも、逆数の公理で u·inv(u) = 1 を登録する（InvAxiom, Resolve）

### 3.3 場合分け（排中律など）
| 手法 | 内容 | 深さ |
|---|---|---|
| f ≡ 0 | 0 が解なら「∀x f(x) = 0」か「ある j で f(j) ≠ 0」 | 制限なし（1 回） |
| 恒等関数 | 「∀x f(x) = x」か「ある a で f(a) ≠ a」 | 4 まで |
| 単射性の補題 | 「f(x) = f(y) ⇒ x = y」か否か。否定側を閉じられなければ取り消す。単射性がわかったら y := 0 の例で零点の補題「f(x) = 0 ⇒ x = 0」も登録する（f(0) = 0 のとき）。f の値で決まる量の補題（単射性を直接与える）は第 0 ラウンドから。わかった単射性は、選言（変数のないものも）と場合分け前の因数分解のリテラル f(s) − f(t) = 0 を s − t = 0 にする（tactic_injectivity_in_disjunction） | 4 まで |
| 零点の補題 | 「f(x) = 0 ⇒ x = 0」か否か。f が式 T の値で 0 になる事実（選言のリテラルを含む）があれば場合分けより先に試す。f ≡ 0 が解で ≠ の事実のない枝では試さず「試した」とも記録しない（f(j) ≠ 0 の子で試す）。わかったら選言の中の f(s) = 0 も s = 0 にする（Instantiate, Resolve）。当てはめは場合分けより先に毎ラウンド（tactic_zero_lemma_in_disjunction） | 5 まで |
| 閉じた係数 | 係数 a が 0 か 0 でないか | 5 未満 |
| 各点の選言 | 「各点で g₁ か g₂」を候補ごとの排中律で全体の場合に（各点→全体の推論を正しく行う）。否定側の枝では反例の点 a で選言を例化する。閉じた点（a, −a など）での例化は代入を 1 回行った後（先に場合分けが増えないように） | 10 まで |
| 閉じた因数分解・変数を共有しない選言 | 因子ごとに分ける | 10 まで |

### 3.4 性質・既知の型
- 符号の議論の基本部品（elimination.rs）: 閉じた u ≠ 0 から u² > 0（Trichotomy, Resolve, MulIneq 2 回。枝で使い回す）。
  平方和の判定 prove_positive_sos: 式が「正の係数 × 平方」の和で、厳密に正の項（正の定数か u ≠ 0 の u²）を含めば正（PosComb）。
  平方でない単項式は、2 項の単位等式 α·m + β·s = 0（s は平方）で平方に置き換える（PosComb の等式の項）。
  正とわかったリテラルは選言から外す（drop_rootless）（tactic_sign_reasoning_sos）
- 各点の選言の例化（splits.rs の pointwise_instances）: 閉じた点に加えて、1 変数の事実に現れる f の引数（変数を含む式）でも
  例化し、規則で書き換えた後に正の値の判定で偽の側を外す（例: f(t) ∈ {0, t} と f(a² + y²) = a² + f(y)² から f(y)² = y²）
- 平方の値域: 変数が 2 乗でだけ現れる事実から t ≥ 0 での事実
- 符号の併合: 「x < 0 ∨ Q」と「x > 0 ∨ Q」から Q
- コーシーの方程式への帰着: 加法性 + 片側の有界性 → 1 次関数（CauchyBounded）
- 加法的な族による特殊解決: 加法性（と対合・射影の条件）がわかった葉を加法的な族で確定（tactic_additive_family_cauchy_type, tactic_involution_family）

### 3.5 帰着
- 導いた 2 変数の等式を新しい方程式として別に解き、完全解決すれば補題として取り込む（ImportLemma）。第 4 ラウンドから・1 回・最大 3 秒
- 既知の型の当てはめ（reduction.rs の apply_known_types）: 2 変数の単位等式（と「x = 0 ∨ …」の 2 リテラルの事実）が
  f(a·xy + g(x)) = a·x·f(y) + h(x) の型なら AffineXY、f(c·f(x)f(y) + g(x)) = d·y·f(x) + h(x) の型なら AffineFF で f は 1 次。
  場合分けより先に毎ラウンド（形が合わなければ検証核が拒否するだけ）。tactic_affine_ff_type も参照。
  型の見つけ方: 「f(α(x,y) + g(x)) = β(x,y) + h(x)」で g, h を具体的な関数にした例をソルバで解き、どの例でも 1 次の解だけに
  なる型を候補にして証明を探す（ソルバが表せない解を見落とすので、候補は数学的に確かめる。例: f(f(x)f(y)) = xy は 1/x も解）。
  効く類: f(x f(x) + xy) = f(x)² + x f(y)、f(f(x²) + xy) = f(x)² + x f(y) など（問題集の 93 問の解答が使う一般の命題）。
  規則に導かれる代入（3.1）と組み合わせて f(x f(y) + g(x)) = xy + h(x) の型にも効く（tactic_affine_xy_type, tactic_rule_guided_substitution）
- 見つけた解に導かれる補題の推測（lemmas.rs の speculate_lemmas・try_lemma）: 枝と矛盾しない多項式の解の候補がすべて満たす性質
  （f(0) = 0、奇関数、f(f(x)) = x、f(x + 1) = f(x) + c、f(1) = c、偶関数、f(f(x)) = f(x)）を、否定側を限られた時間で閉じられれば
  補題にする（排中律・AbandonSplit）。補題の側は深さを増やさず同じラウンドから続ける。探索の予定の最後の段階（幅 2 以上）だけで行う
  （tactic_solution_guided_lemmas）

### 3.6 解の形の確定
- f(x) = g(x) の規則が得られたら、パラメータの自己整合性を確かめて mark_solution
- 区分的な葉（負・0・正の側の事実がそろう）、加法的な葉

### 3.8 対称性・値の補題・平行移動型（shift.rs）
| 手法 | 何をするか（使う規則） | 効く類・例 | テスト |
|---|---|---|---|
| 入れ替えの差 | 2 変数の事実 p(x, y) と、x と y を入れ替えた例の差 p(x, y) − p(y, x)（Instantiate, LinComb）。入れ替えた例は既知として加えないので差を別に作る | 右辺が x, y について対称: f(xf(y) + f(xy)) = xy + f(xy) から f(xf(y) + f(xy)) = f(yf(x) + f(xy)) | tactic_swap_difference_and_value_injectivity |
| ずらしの差 | 2 変数の事実 p(x, y) と、ずらした例 p(x, y ± 1)、p(x ± 1, y)、平行移動の事実 f(x + K) = a·f(x) + b の閉じた K でのずらし（追加時に規則で書き換わる）の差。そろえる係数は有理数か閉じた式。項が減るか、変数そのものの f（f(x), f(y)）が減るものを加える（Instantiate, LinComb） | f(xf(x) + xy) = x² + f(x)f(y) と f(t + 1) = f(t) + 1 から f(xf(x) + xy + x) = f(xf(x) + xy) + f(x)、さらに分数の代入で加法性 | tactic_shift_difference |
| f の値で決まる量の補題 | 1 変数の事実 c·f(g(f(y))) + R(y) = 0 から「f(y) = f(z) ⇒ R(y) = R(z)」（EqOrNe, Congruence, LinComb）。結果がちょうど「y = z ∨ f(y) ≠ f(z)」なら単射性として登録 | P(1, x) 型の事実 f(2f(x)) = x + f(x) から単射性 | tactic_swap_difference_and_value_injectivity |
| 条件つき単射性の当てはめ | 「Q(x, y) ∨ f(y) ≠ f(x)」を、変数のない事実・小さい 1 変数の事実 f(s₁) = f(s₂) に代入して導出原理で Q(s₂, s₁)（Instantiate, Resolve）。1 回 scaled(40) 個まで | f(f(x)²) = x·f(x) から「f(a) = f(b) ≠ 0 なら a = b」 | 全体の計測 |
| 平行移動の補題 | f(x + A(y)) = f(x) + B(y) から「A(y) = A(z) ⇒ B(y) = B(z)」と、x := x − A(−y) の 2 例の差による周期の補題 f(x + A(y) − A(−y)) = f(x) + B(y) − B(−y) | 平行移動型 f(x + T(y)) = f(x) + S(y)（ただし対象の多くはまだ解けない） | 全体の計測 |

### 3.9 病的な解の候補（finalize.rs の find_arb_candidates）
| 手法 | 何をするか（使う規則） | 効く類・例 | テスト |
|---|---|---|---|
| 任意の区間をもつ族の候補 | 区切り点 0 で、片側を g ∈ {x, −x, 0}、反対側を「任意の値・0 以上・0 以下・各点で x か −x・0 か x・0 か −x」とした 36 通りを verify_arbitrary で確かめ、最初に通ったものを病的な解の存在（special_exist）として報告する | f の引数がいつも 0 以上になる型（f(x² + f(y²)) = x² + y²、f(f(x) + f(y)²) = f(x) + f(y)²）、f の値が 2 乗や t·f(t) でだけ現れる型（f(x)² = x²、f(x f(x) + y f(y)) = x f(x) + y f(y)） | tactic_arbitrary_family |

### 3.7 時間と幅
- 反復拡幅: 探索幅 0.5 → 1 → 2 を時間の 25% / 35% / 残りで独立に解き直す。残り時間があれば幅を倍にして続ける（上限 16）
- 補題の試行（零点の補題・単射性・解に導かれる推測）の否定側の枝は持ち時間が短いので、その中では補題の推測をしない（in_trial）
- 条件つきの単射性（f の値で決まる量の補題「f(y) = f(x) なら Q(x, y)」）の当てはめは、単射性・零点の補題と同じく場合分けより
  先にも行う（導出原理だけで安い。各ラウンドの最後だけだと、根の枝で場合分けが先に起きて使われない）
- 速さ（結果を変えない実装の工夫。engine.rs・matching.rs）: 書き換え規則は照合用に変数を移した左辺（pat）を作るときに 1 回だけ
  持ち、左辺が変数を含まない規則は一致だけを見る。照合の中の代入の適用は、決まった変数を含まない式を作り直さない。新しい規則を
  入れたら正規化のキャッシュを丸ごと消す（項目ごとに照合するより速い）。gdb でスタックを採る簡易プロファイルで重い箇所を探した

## 4. 足りない手法の系統（失敗の分類との対応）

評価セットで今も解けない問題の、解答が使う手法（既見の答えが普通の問題 98 問、重複あり）:

| 系統 | 問題数 | 今の状態 |
|---|---|---|
| 符号・不等式の議論（矛盾のための比較、平方 ≥ 0、十分大きい値、奇偶で反対側へ） | 64 | 平方の値域・符号の併合・正定値化だけ |
| 特別な点の代入（f(a) = 0 の a、f(a) = f(b) の 2 点、f(a) ≠ 0 の a） | 51 | 場合分けの定数で一部 |
| 単射・全射の議論の連鎖 | 38 | 単射性・零点の補題、全射性の証人、f の値で決まる量の補題からの単射性、条件つき単射性（3.8） |
| 分母に変数・f を含む分数の代入 | 24 | 分母が変数のもの、分母が他方の変数の一般の式のもの（3.1）。結論の f の引数に分数が残る代入（P(a, (a − f(a))/a) など）はまだ |
| 他の問題への帰着 | 22 | 帰着先が未解決のことが多い |
| 各点の場合分け | 14 | 候補ごとの排中律 |
| 対合の利用 | 11 | 書き換えで一部 |
| 平行移動型 f(x + T(y)) = f(x) + S(y) の推論（評価で 11 問） | 11 | 平行移動の補題（3.8）を入れたが、対象はまだ解けない。全射性・周期性・単射性の連鎖と、平行移動の量の集合の議論が要る |
| 帰納法（整数・有理数倍） | 3 | 検証核に規則がない |

## 5. 入力の一般化についての前提（拡張するときに変える場所）

- 定義域・値域は ℝ（検証核の三分律・平方の値域・区分的な族の検証が ℝ を前提にしている）
- 変数は x, y の 2 つ（検証核の Axiom は 2 変数。探索の代入は 2 変数前提。事実は 3 変数以上も表せる）
- 未知関数は f 1 つ（Atom::F が 1 種類）
- 方程式は等式 1 つ（不等式・連立は未対応。検証核の節は不等式リテラルを持てる）
- パーサ: 問題集の文法に厳密な parse_strict と、一般の式を読む parse_general
