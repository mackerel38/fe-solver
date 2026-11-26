#!/usr/bin/env python3
"""完全解決した問題の解答一覧（日本語）を作る。

最新のベンチマーク（bench/latest.json）で完全解決した問題を、ソルバで解き直して証明文を保存する。
証明文はソルバ（fe_render）が検証核の導出記録から機械的に生成したもので、このスクリプトは書き換えない。

使い方: python3 scripts/solved_report.py [--timeout 秒] [--run bench/runs/<日時> または集約結果のディレクトリ]
結果のディレクトリに proofs/FE-XXXX.txt（bench.py --save-proofs や GitHub Actions の集約結果）があれば、解き直さずにそれを使う。
出力:   reports/SOLVED.md（一覧）, reports/solved/FE-XXXX.md（問題ごとの証明）
"""
import argparse
import concurrent.futures as cf
import json
import os
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, "target", "release", "fe_solver")
SET_NAME = {"seen": "評価（既見）", "unseen": "評価（初見）", "challenge": "挑戦"}


def solve(pid, timeout):
    p = subprocess.run([BIN, "solve", pid, "--timeout", str(timeout)], capture_output=True, text=True,
                       timeout=timeout * 2 + 30)
    return p.stdout


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=float, default=30.0)
    ap.add_argument("--run", default="")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    args = ap.parse_args()
    if args.run:
        run_dir = os.path.join(ROOT, args.run) if not os.path.isabs(args.run) else args.run
    else:
        latest = json.load(open(os.path.join(ROOT, "bench", "latest.json"), encoding="utf-8"))
        run_dir = os.path.join(ROOT, "bench", "runs", latest["run"])
    results = [json.loads(l) for l in open(os.path.join(run_dir, "results.jsonl"), encoding="utf-8")]
    done = [r for r in results if r["status"] in ("complete", "special") and r.get("set") in ("seen", "unseen")]
    problems = {p["id"]: p for p in json.load(open(os.path.join(ROOT, "data", "problems.json"), encoding="utf-8"))}

    out_dir = os.path.join(ROOT, "reports", "solved")
    os.makedirs(out_dir, exist_ok=True)
    texts = {}
    pdir = os.path.join(run_dir, "proofs")
    todo = []
    for r in done:
        pp = os.path.join(pdir, r["id"] + ".txt")
        if os.path.exists(pp):
            texts[r["id"]] = open(pp, encoding="utf-8").read()
        else:
            todo.append(r)
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(solve, r["id"], args.timeout): r["id"] for r in todo}
        for fu in cf.as_completed(futs):
            texts[futs[fu]] = fu.result()

    rows = []
    for r in sorted(done, key=lambda r: r["id"]):
        pid = r["id"]
        text = texts.get(pid, "")
        ok = text.startswith(("状態: 完全解決", "状態: 特殊解決"))
        eq = problems[pid]["equations"][0]["display"]
        sols = "、".join(r["families"]) if r["families"] else "（解なし）"
        with open(os.path.join(out_dir, pid + ".md"), "w", encoding="utf-8") as fp:
            fp.write(f"# {pid}: {eq}\n\n")
            fp.write(f"- セット: {SET_NAME.get(r['set'], r['set'])}\n")
            fp.write(f"- 解: {sols}\n\n")
            if not ok:
                fp.write("（注: 解き直しで完全解決を再現できなかった。ベンチマーク時の結果のみ記載）\n\n")
            fp.write("```\n" + text.rstrip() + "\n```\n")
        rows.append((pid, SET_NAME.get(r["set"], r["set"]), eq, sols, ok))

    with open(os.path.join(ROOT, "reports", "SOLVED.md"), "w", encoding="utf-8") as fp:
        fp.write("# 解決した問題の一覧（評価セット）\n\n")
        fp.write(f"ベンチマーク `{os.path.relpath(run_dir, ROOT)}` で解決（完全解決・特殊解決）した {len(rows)} 問。"
                 "各問題の日本語の証明は `reports/solved/FE-XXXX.md`（ソルバが検証核の導出記録から生成したもの）。\n\n")
        counts = {}
        for row in rows:
            counts[row[1]] = counts.get(row[1], 0) + 1
        fp.write("内訳: " + "、".join(f"{k} {v} 問" for k, v in counts.items()) + "\n\n")
        fp.write("| ID | セット | 方程式 | 解 |\n|---|---|---|---|\n")
        for pid, sname, eq, sols, ok in rows:
            mark = "" if ok else " ※"
            fp.write(f"| [{pid}](solved/{pid}.md) | {sname} | `{eq}` | {sols}{mark} |\n")
        if any(not r[4] for r in rows):
            fp.write("\n※ 解き直しで完全解決を再現できなかったもの（時間依存）。\n")
    print(f"{len(rows)} 問を reports/SOLVED.md と reports/solved/ に書き出した"
          f"（再現できなかったもの {sum(1 for r in rows if not r[4])} 問）")


if __name__ == "__main__":
    main()
