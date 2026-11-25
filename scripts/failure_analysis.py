#!/usr/bin/env python3
"""評価セットの失敗の分析（改善が頭打ちになったときの、残った問題の分析用）。

ベンチマーク結果（既定は bench/latest.json の実行）の失敗問題を、
  - 止まった理由（時間切れ / 解の形を導けない / …）
  - 到達した手法（f≡0 の場合分け・単射性・平方の値域・各点の場合分け・加法性・コーシー…）
  - 見つけた解の型（f=x のみ, {0,x}, {x,−x}, 区分的な解を含む, …）
で集計して表示する。外部解答は使わない（初見セットの解答を読まないため）。
"""
import collections
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main():
    if len(sys.argv) > 1:
        run_dir = sys.argv[1]
    else:
        latest = json.load(open(os.path.join(ROOT, "bench", "latest.json"), encoding="utf-8"))
        run_dir = os.path.join(ROOT, "bench", "runs", latest["run"])
    rs = [json.loads(l) for l in open(os.path.join(run_dir, "results.jsonl"), encoding="utf-8")]
    ev = [r for r in rs if r["set"] in ("seen", "unseen")]
    fail = [r for r in ev if r["status"] != "complete"]
    print(f"実行: {os.path.relpath(run_dir, ROOT)}  評価セット {len(ev)} 問中 失敗 {len(fail)} 問")
    print("\n止まった理由:")
    for k, v in collections.Counter(r["class"] for r in fail).most_common():
        print(f"  {k}: {v}")
    tags = collections.Counter()
    for r in fail:
        st = r.get("stats", {})
        for key, name in [("zero_split", "f≡0 の場合分け"), ("inj_proved", "単射性（証明済み）"), ("zinj_proved", "零点の補題"),
                          ("square_range", "平方の値域"), ("pointwise_split", "各点の場合分け"), ("additive_found", "加法性"),
                          ("cauchy", "コーシー"), ("coef_split", "係数の場合分け"), ("reduce_import", "帰着"),
                          ("piecewise_leaf", "区分的な葉")]:
            if st.get(key):
                tags[name] += 1
    print("\n失敗問題で到達した手法（重複あり）:")
    for k, v in tags.most_common():
        print(f"  {k}: {v}")
    print("\n見つけた解の型:")
    def kind(r):
        fs = r.get("found", [])
        pw = any("（x" in f for f in fs)
        poly = tuple(sorted(f for f in fs if "（x" not in f))
        return (poly, "＋区分的" if pw else "")
    for k, v in collections.Counter(kind(r) for r in fail).most_common(12):
        print(f"  {v:4d}  {'、'.join(k[0])}{k[1]}")


if __name__ == "__main__":
    main()
