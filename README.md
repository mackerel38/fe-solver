# R→R 関数方程式の自動ソルバ

問題集 https://gghx0.github.io/fe-project/ の関数方程式 `f(A + B) = C + D`（f: ℝ → ℝ）を自動で解き、
日本語の証明文を出力するソルバ。証明済みの事実は小さな検証核（`crates/kernel`）の推論規則でしか作れない。

## 構成

| パス | 内容 |
|---|---|
| `crates/kernel` (fe_kernel) | 検証核。有理数係数の多項式・節・推論規則・場合分けの木・解の検証。探索部に依存しない |
| `crates/render` (fe_render) | 検証核の導出記録から日本語の証明文を機械的に生成する |
| `crates/solver` (fe_solver) | パーサ・探索部・CLI |
| `scripts/fetch_data.py` | 問題データの取得（`data/problems.json`, `data/source.json`） |
| `scripts/make_split.py` | 評価・初見・挑戦セットの分割（`data/split.json` に固定済み） |
| `scripts/bench.py` | ベンチマーク（全問並列・時間制限・前回との差分・テスト実行） |

## ビルド

```
cargo build --release
```

## 1 問解く

```
./target/release/fe_solver solve FE-0004              # 問題 ID で（証明文を表示）
./target/release/fe_solver solve "f(x + f(y)) = x + y" # 方程式を直接（+ - * ^ 括弧, f(...), x, y, 整数）
./target/release/fe_solver solve FE-0004 --timeout 300 # 時間制限（秒, 既定 60）
./target/release/fe_solver solve FE-0004 --json        # 結果を 1 行の JSON で（--proof で証明文を標準エラーへ）
./target/release/fe_solver solve FE-0004 --width 2    # 探索幅を固定（代入数・生成元の数などの倍率。既定は反復拡幅）
./target/release/fe_solver solve FE-0004 --schedule 0.5:0.25,1:0.35,2:1  # 幅:時間の割合 の予定（反復拡幅）
./target/release/fe_solver list seen                   # 問題一覧（seen / unseen(=初見) / challenge / all）
```

既定の探索は反復拡幅: 幅 0.5 で時間の 25%、幅 1 で 35%、幅 2 で残りを使い、それぞれ独立に解いて完全解決した時点で終える
（環境変数 `FE_SCHEDULE="0.5:0.25,1:0.35,2:1"` でも変更できる）。

出力の状態は次のいずれか。
- **完全解決**: 解の集合と、それ以外に解がないことの証明（場合分けの木に沿った日本語の証明文と検算）
- **特殊解決**: 解の集合に「任意の加法的関数 A を使った f(x) = A(x) + c」などの族を含む場合（コーシーの関数方程式型）。
  すべての場合が閉じるか解の形が決まっていれば、解の集合とそれ以外に解がないことの証明を出す（`special`）。
  解の集合は決められなくても、任意の加法的関数を含む族が解であること（病的な解の存在）を示せた場合も特殊解決とする（`special_exist`）。
  加法的関数の族が解であることは、A を有理数係数の和について展開した恒等式として検証核が確かめる
- **部分結果**: 見つけた解（検証核で代入を確認済み）と、証明済みの事実の一覧、止まった理由
- **未解決**: 証明済みの事実の一覧と、止まった理由

## 全問のベンチマーク

```
python3 scripts/bench.py                                 # 全セット（評価・初見 300 秒/問, 挑戦 1800 秒/問）＋全テスト
python3 scripts/bench.py --sets seen,unseen --timeout 60 # 評価セットだけを改善ループ用の制限で
python3 scripts/bench.py --ids FE-0001,FE-0004 --no-tests
```

最後にセットごとの解決数（完全解決 + 特殊解決。病的な解の存在だけを示したものは別に数える）・失敗理由の分類・前回との差分・テスト（負のテストを含む）の結果を表示する。
問題ごとの結果は `bench/runs/<日時>/results.jsonl`、集計は `summary.json`、最新の集計は `bench/latest.json`（いずれも git には入れない）。
`--save-proofs` で問題ごとの証明文・報告を `<出力先>/proofs/` に保存する。

## GitHub での実行と公開（GitHub Actions / Pages）

- `.github/workflows/ci.yml`: push・PR のたびに全テスト（検証核の規則テスト・パーサ・負のテスト）を実行する。
- `.github/workflows/bench.yml`（ワークフロー名 benchmark）: 手動起動（Actions タブ → benchmark → Run workflow）。
  全問を 20 分割して並列に解き（`scripts/bench.py --shard K/20`）、結果を集約して（`scripts/merge_results.py`）、
  結果と問題ごとの証明のページを作り（`scripts/build_site.py`）、GitHub Pages に公開する。
  時間制限（評価・挑戦の 1 問あたり秒数）と解くセットは起動時に指定できる。集約した結果はアーティファクト `merged-results` にも残る。
- `.github/workflows/publish.yml`（ワークフロー名 publish）: benchmark の集約結果（アーティファクト `merged-results`）から
  サイトを作って GitHub Pages に公開する。benchmark の最後に自動で呼ばれる。計測をやり直さずに公開だけやり直すときは、
  Actions タブ → publish → Run workflow で、benchmark の実行 ID（実行の URL の `runs/<ID>`）を指定する。
- 初回の準備: リポジトリの Settings → Pages → Build and deployment の Source を「GitHub Actions」にする。
- 生成物（`bench/runs/`, `reports/`, `site/` など）はリポジトリに入れない（`.gitignore`）。手元では従来どおり
  `python3 scripts/bench.py` などで作れる。

手元でサイトを作る例:

```
python3 scripts/bench.py --sets seen,unseen --timeout 60 --save-proofs --out out
python3 scripts/merge_results.py out --out merged
python3 scripts/build_site.py merged --out site   # site/index.html を開く
```

## テスト

```
cargo test --release --workspace
```

- `crates/kernel/tests/rules.rs`: 推論規則ごとのテスト（正しい使い方と、誤った使い方の拒否）
- `crates/kernel/src/lib.rs` の doctest: クレート外から事実を偽造できないこと（コンパイル失敗テスト）
- `crates/solver/tests/parse_all.rs`: 全 847 問 1625 式が About ページの文法で厳密にパースでき、f(x)=x が解であること
- `crates/solver/tests/negative.rs`: 負のテスト（複数解・病的な解をもつ方程式で一意性を主張しない、壊した方程式で偽の結論を出さない）

## 探索の主な手法（要約）

すべての事実は検証核の推論規則で作る。探索部はどの規則をどの順で呼ぶかを決めるだけ。

- 代入: 0, ±1, ±x, f(x), f(0), 2x, ±1/2 などの組、P(f(x), y) などの 2 変数の代入、ずらし・和差の代入（P(x, y ± 1), P(x ± y, y) など）、
  閉じた値（−f(0), ±f(1), f(0)²）、引数を変数や 0 にする打ち消しの代入、2 つの f の引数を等しくする代入、
  分数の代入（v := (v − r)/(c·w)。w ≠ 0 と w = 0 の場合を合わせて ∀x,y の等式にする）
- 書き換え: 1 変数の事実を規則にした証明つきの書き換え、相互簡約、べき・逆数の規則、条件付き規則
- 消去: 1 変数・2 変数の事実の一次結合による消去
- 場合分け（排中律）: f ≡ 0、恒等関数、単射性、零点の補題（f(k) = 0 ⇒ k = 0）、閉じた係数、各点の選言、変数を共有しない選言
- 性質の利用: 平方の値域（x ≥ 0）、符号の併合、コーシーの方程式への帰着（有界な加法的関数）、加法性による展開、全射性の証人
- 帰着: 導いた 2 変数の等式を別の問題として解き、補題として取り込む
- 解の形: 多項式の族（パラメータつき）、0 を区切り点とする区分的な族、加法的関数を含む族（特殊解決）
- 時間: 探索幅を 0.5 → 1 → 2 と広げながら独立に解き直す（反復拡幅）

## 健全性の仕組み（要約）

- `fe_kernel::Fact` はフィールド非公開で、`Kernel` の推論規則メソッドだけが作れる（両クレートとも `#![forbid(unsafe_code)]`）。
- 式の同一性は有理数係数の多項式の正規形の一致で判定（浮動小数点・乱数は使わない）。
- 解であることの確認も、f に候補を代入した恒等式の厳密な記号計算で行う。
- 場合分けは網羅的なもの（変数を共有しない選言・排中律）だけで、「各点で x か −x」を全体の場合分けにはできない。
- 各推論規則が正しい根拠は `crates/kernel/src/kernel.rs` のコメントに書いてある。
