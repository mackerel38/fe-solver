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
| `DECISIONS.md` / `QUESTIONS.md` / `PROGRESS.md` | 設計判断・質問・進捗 |

## ビルド

```
cargo build --release
```

## 1 問解く

```
./target/release/fe_solver solve FE-0004              # 問題 ID で（証明文を表示）
./target/release/fe_solver solve "f(x + f(y)) = x + y" # 方程式を直接（+ - * ^ 括弧, f(...), x, y, 整数）
./target/release/fe_solver solve FE-0004 --timeout 60  # 時間制限（秒, 既定 20）
./target/release/fe_solver solve FE-0004 --json        # 結果を 1 行の JSON で（--proof で証明文を標準エラーへ）
./target/release/fe_solver list seen                   # 問題一覧（seen / unseen(=初見) / challenge / all）
```

出力の状態は次のいずれか。
- **完全解決**: 解の集合と、それ以外に解がないことの証明（場合分けの木に沿った日本語の証明文と検算）
- **部分結果**: 見つけた解（検証核で代入を確認済み）と、証明済みの事実の一覧、止まった理由
- **未解決**: 証明済みの事実の一覧と、止まった理由

## 全問のベンチマーク

```
python3 scripts/bench.py                                 # 全セット（評価・初見 60 秒/問, 挑戦 300 秒/問）＋全テスト
python3 scripts/bench.py --sets seen,unseen --timeout 5  # 評価セットだけを短い制限で
python3 scripts/bench.py --ids FE-0001,FE-0004 --no-tests
```

最後にセットごとの完全解決数・失敗理由の分類・前回との差分・テスト（負のテストを含む）の結果を表示する。
問題ごとの結果は `bench/runs/<日時>/results.jsonl`、集計は `summary.json`、最新の集計は `bench/latest.json`。

## テスト

```
cargo test --release --workspace
```

- `crates/kernel/tests/rules.rs`: 推論規則ごとのテスト（正しい使い方と、誤った使い方の拒否）
- `crates/kernel/src/lib.rs` の doctest: クレート外から事実を偽造できないこと（コンパイル失敗テスト）
- `crates/solver/tests/parse_all.rs`: 全 847 問 1625 式が About ページの文法で厳密にパースでき、f(x)=x が解であること
- `crates/solver/tests/negative.rs`: 負のテスト（複数解・病的な解をもつ方程式で一意性を主張しない、壊した方程式で偽の結論を出さない）

## 健全性の仕組み（要約）

- `fe_kernel::Fact` はフィールド非公開で、`Kernel` の推論規則メソッドだけが作れる（両クレートとも `#![forbid(unsafe_code)]`）。
- 式の同一性は有理数係数の多項式の正規形の一致で判定（浮動小数点・乱数は使わない）。
- 解であることの確認も、f に候補を代入した恒等式の厳密な記号計算で行う。
- 場合分けは網羅的なもの（変数を共有しない選言・排中律）だけで、「各点で x か −x」を全体の場合分けにはできない。
- 詳細は `DECISIONS.md` の D5 以降と `crates/kernel/src/kernel.rs` のコメント。
