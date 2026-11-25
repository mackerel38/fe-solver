#!/usr/bin/env python3
"""挑戦セット（サイトで open の問題）の結果レポートを作る。

ベンチマークの結果（既定は bench/latest.json の実行）から、
  - 完全解決した挑戦問題: 解の集合と日本語の証明（ソルバで解き直して保存）
  - 完全解決していないが、f(x) = x 以外の解（検証核で代入を確認済み）が見つかった挑戦問題
を reports/CHALLENGE.md と reports/challenge/FE-XXXX.md に書き出す。

使い方: python3 scripts/challenge_report.py [--run bench/runs/<日時>] [--timeout 秒]
"""
import argparse
import concurrent.futures as cf
import json
import os
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, "target", "release", "fe_solver")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", default="")
    ap.add_argument("--timeout", type=float, default=600.0)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    args = ap.parse_args()
    if args.run:
        run_dir = args.run if os.path.isabs(args.run) else os.path.join(ROOT, args.run)
    else:
        latest = json.load(open(os.path.join(ROOT, "bench", "latest.json"), encoding="utf-8"))
        run_dir = os.path.join(ROOT, "bench", "runs", latest["run"])
    results = [json.loads(l) for l in open(os.path.join(run_dir, "results.jsonl"), encoding="utf-8")]
    ch = [r for r in results if r.get("set") == "challenge"]
    problems = {p["id"]: p for p in json.load(open(os.path.join(ROOT, "data", "problems.json"), encoding="utf-8"))}
    complete = sorted((r for r in ch if r["status"] == "complete"), key=lambda r: r["id"])
    others = sorted((r for r in ch if r["status"] != "complete" and any(f != "f(x) = x" for f in r.get("found", []))),
                    key=lambda r: r["id"])

    out_dir = os.path.join(ROOT, "reports", "challenge")
    os.makedirs(out_dir, exist_ok=True)

    def solve(pid):
        p = subprocess.run([BIN, "solve", pid, "--timeout", str(args.timeout)], capture_output=True, text=True,
                           timeout=args.timeout * 2 + 60)
        return p.stdout

    texts = {}
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(solve, r["id"]): r["id"] for r in complete}
        for fu in cf.as_completed(futs):
            texts[futs[fu]] = fu.result()
    for r in complete:
        pid = r["id"]
        eq = problems[pid]["equations"][0]["display"]
        text = texts.get(pid, "")
        with open(os.path.join(out_dir, pid + ".md"), "w", encoding="utf-8") as fp:
            fp.write(f"# {pid}（挑戦セット）: {eq}\n\n- 解: {'、'.join(r['families']) or '（解なし）'}\n\n")
            if not text.startswith("状態: 完全解決"):
                fp.write("（注: 解き直しで完全解決を再現できなかった。ベンチマーク時の結果のみ記載）\n\n")
            fp.write("```\n" + text.rstrip() + "\n```\n")

    with open(os.path.join(ROOT, "reports", "CHALLENGE.md"), "w", encoding="utf-8") as fp:
        fp.write("# 挑戦セット（サイトで open の問題）の結果\n\n")
        fp.write(f"ベンチマーク `{os.path.relpath(run_dir, ROOT)}` の結果（挑戦セット {len(ch)} 問）。\n\n")
        fp.write(f"## 完全解決した問題（{len(complete)} 問）\n\n")
        fp.write("証明は `reports/challenge/FE-XXXX.md`（ソルバが検証核の導出記録から生成したもの）。\n\n")
        if complete:
            fp.write("| ID | 方程式 | 解の集合 |\n|---|---|---|\n")
            for r in complete:
                fp.write(f"| [{r['id']}](challenge/{r['id']}.md) | `{problems[r['id']]['equations'][0]['display']}` | "
                         f"{'、'.join(r['families'])} |\n")
        fp.write(f"\n## 完全解決していないが f(x) = x 以外の解が見つかった問題（{len(others)} 問）\n\n")
        fp.write("見つかった解はすべて検証核で代入を確認済み。ただし、これ以外に解がないことは示せていない。\n\n")
        if others:
            fp.write("| ID | 方程式 | 見つかった解 | 止まった理由 |\n|---|---|---|---|\n")
            for r in others:
                reasons = "; ".join(r.get("reasons", []))[:120]
                fp.write(f"| {r['id']} | `{problems[r['id']]['equations'][0]['display']}` | {'、'.join(r['found'])} | {reasons} |\n")
    print(f"挑戦セット: 完全解決 {len(complete)} 問、f(x)=x 以外の解が見つかった問題 {len(others)} 問 → reports/CHALLENGE.md")


if __name__ == "__main__":
    main()
