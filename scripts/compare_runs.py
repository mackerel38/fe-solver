#!/usr/bin/env python3
"""2 つのベンチマーク（GitHub Actions の実行、または手元の結果のディレクトリ）を比べる。

使い方: python3 scripts/compare_runs.py <基準> <候補>
  それぞれ、GitHub Actions の benchmark の実行 ID（数字。アーティファクト merged-results を gh でダウンロードする）か、
  results.jsonl を含むディレクトリ。
表示: セットごとの解決数（完全解決 + 特殊解決）・特殊解決（病的な解の存在のみ）、解けるようになった問題・解けなくなった問題。
"""
import json
import os
import subprocess
import sys
import tempfile

SOLVED = ("complete", "special")
NAMES = {"seen": "既見", "unseen": "初見", "challenge": "挑戦"}
REPO = os.environ.get("FE_REPO", "mackerel38/fe-solver")


def load(src):
    if os.path.isdir(src):
        d = src
    else:
        d = os.path.join(tempfile.gettempdir(), f"fe-run-{src}")
        if not os.path.exists(os.path.join(d, "results.jsonl")):
            os.makedirs(d, exist_ok=True)
            subprocess.run(["gh", "run", "download", src, "-R", REPO, "-n", "merged-results", "-D", d], check=True)
    return {json.loads(l)["id"]: json.loads(l) for l in open(os.path.join(d, "results.jsonl"), encoding="utf-8")}


def main():
    a, b = load(sys.argv[1]), load(sys.argv[2])
    common = sorted(set(a) & set(b))
    for st in ("seen", "unseen", "challenge"):
        ids = [i for i in common if a[i]["set"] == st]
        if not ids:
            continue
        sa = sum(a[i]["status"] in SOLVED for i in ids)
        sb = sum(b[i]["status"] in SOLVED for i in ids)
        ea = sum(a[i]["status"] == "special_exist" for i in ids)
        eb = sum(b[i]["status"] == "special_exist" for i in ids)
        print(f"{NAMES[st]}: 解決 {sa} → {sb}（{sb - sa:+d}）/ {len(ids)}、病的な解の存在のみ {ea} → {eb}")
    ev = [i for i in common if a[i]["set"] in ("seen", "unseen")]
    if ev:
        sa = sum(a[i]["status"] in SOLVED for i in ev)
        sb = sum(b[i]["status"] in SOLVED for i in ev)
        print(f"評価セット全体: 解決 {sa} → {sb}（{sb - sa:+d}）/ {len(ev)}")
    gained = [i for i in common if a[i]["status"] not in SOLVED and b[i]["status"] in SOLVED]
    lost = [i for i in common if a[i]["status"] in SOLVED and b[i]["status"] not in SOLVED]
    print(f"解けるようになった {len(gained)}: {' '.join(gained)}")
    print(f"解けなくなった {len(lost)}: {' '.join(lost)}")
    crash = [i for i in common if b[i]["status"] == "crash"]
    if crash:
        print("候補の異常終了:", " ".join(f"{i}({b[i]['reasons'][0][:80]})" for i in crash))


if __name__ == "__main__":
    main()
