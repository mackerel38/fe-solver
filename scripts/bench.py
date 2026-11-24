#!/usr/bin/env python3
"""ベンチマーク: 全問を時間制限つきで並列に解き、結果を記録して前回と比較し、テストも実行して要約する。

使い方:
  python3 scripts/bench.py                       # 全セット（評価 20 秒 / 挑戦 60 秒）+ テスト
  python3 scripts/bench.py --sets seen,unseen    # 評価セットだけ
  python3 scripts/bench.py --timeout 5 --challenge-timeout 5 --jobs 4 --no-tests
  python3 scripts/bench.py --ids FE-0001,FE-0004

出力:
  bench/runs/<日時>/results.jsonl  問題ごとの結果（状態・解・理由・時間・統計）
  bench/runs/<日時>/summary.json   セットごとの集計・テスト結果・前回との差分
  bench/latest.json                最新の summary（次回の比較元）
"""
import argparse
import concurrent.futures as cf
import datetime
import json
import os
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, "target", "release", "fe_solver")


def load(path):
    with open(path, encoding="utf-8") as fp:
        return json.load(fp)


def run_one(pid, timeout):
    t0 = time.time()
    try:
        p = subprocess.run([BIN, "solve", pid, "--timeout", str(timeout), "--json"],
                           capture_output=True, text=True, timeout=timeout * 2 + 15)
        dt = time.time() - t0
        line = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else ""
        if p.returncode != 0 or not line.startswith("{"):
            err = (p.stderr or "").strip().splitlines()
            return {"id": pid, "status": "crash", "reasons": [err[-1] if err else f"exit {p.returncode}"],
                    "time_ms": int(dt * 1000), "families": [], "found": []}
        r = json.loads(line)
        r["wall_ms"] = int(dt * 1000)
        return r
    except subprocess.TimeoutExpired:
        return {"id": pid, "status": "killed", "reasons": ["外部の時間制限で強制終了"],
                "time_ms": int((time.time() - t0) * 1000), "families": [], "found": []}


def classify(r):
    """失敗理由の分類キー"""
    if r["status"] == "complete":
        return "complete"
    if r["status"] in ("crash", "killed"):
        return r["status"]
    rs = r.get("reasons", [])
    keys = set()
    for s in rs:
        s = re.sub(r"^枝\d+: ", "", s)
        if "内部エラー" in s:
            keys.add("internal_error")
        elif "時間切れ" in s:
            keys.add("timeout")
        elif "パラメータ" in s:
            keys.add("params_undetermined")
        elif "f(x) = g(x)" in s:
            keys.add("no_solution_form")
        else:
            keys.add("other")
    if not keys:
        return "other"
    order = ["internal_error", "timeout", "params_undetermined", "no_solution_form", "other"]
    return [k for k in order if k in keys][0]


def run_tests():
    """cargo test（検証核の規則テスト・パーサのテスト・負のテストを含む）"""
    p = subprocess.run(["cargo", "test", "--release", "--workspace"], cwd=ROOT, capture_output=True, text=True)
    out = p.stdout + p.stderr
    passed = sum(int(m) for m in re.findall(r"test result: \w+\. (\d+) passed", out))
    failed = sum(int(m) for m in re.findall(r"(\d+) failed", out))
    failing = re.findall(r"^test (\S+) \.\.\. FAILED", out, re.M)
    neg = re.findall(r"^test (negative\S*|\S*negative\S*) \.\.\. (\w+)", out, re.M)
    return {"ok": p.returncode == 0, "passed": passed, "failed": failed, "failing": failing,
            "negative": {"passed": sum(1 for _, s in neg if s == "ok"), "total": len(neg)},
            "tail": out.strip().splitlines()[-3:]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sets", default="seen,unseen,challenge")
    ap.add_argument("--timeout", type=float, default=20.0, help="評価・未見セットの 1 問あたり秒数")
    ap.add_argument("--challenge-timeout", type=float, default=60.0)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--ids", default="")
    ap.add_argument("--no-tests", action="store_true")
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--tag", default="")
    args = ap.parse_args()

    if not args.no_build:
        subprocess.run(["cargo", "build", "--release", "-q"], cwd=ROOT, check=True)
    split = load(os.path.join(ROOT, "data", "split.json"))
    set_of = {}
    for i in split["evaluation_seen"]:
        set_of[i] = "seen"
    for i in split["unseen"]:
        set_of[i] = "unseen"
    for i in split["challenge"]:
        set_of[i] = "challenge"
    wanted = set(args.sets.split(","))
    ids = [i for i in sorted(set_of) if set_of[i] in wanted]
    if args.ids:
        ids = [i for i in args.ids.split(",") if i in set_of]

    stamp = datetime.datetime.now().strftime("%Y%m%d-%H%M%S") + (("-" + args.tag) if args.tag else "")
    out_dir = os.path.join(ROOT, "bench", "runs", stamp)
    os.makedirs(out_dir, exist_ok=True)
    results = {}
    t0 = time.time()
    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {}
        for pid in ids:
            to = args.challenge_timeout if set_of[pid] == "challenge" else args.timeout
            futs[ex.submit(run_one, pid, to)] = pid
        done = 0
        for fu in cf.as_completed(futs):
            r = fu.result()
            r["set"] = set_of[r["id"]]
            r["class"] = classify(r)
            results[r["id"]] = r
            done += 1
            if done % 50 == 0:
                print(f"  {done}/{len(ids)} ({time.time() - t0:.0f}s)", file=sys.stderr)
    with open(os.path.join(out_dir, "results.jsonl"), "w", encoding="utf-8") as fp:
        for pid in sorted(results):
            fp.write(json.dumps(results[pid], ensure_ascii=False) + "\n")

    # 集計
    sets = {}
    for pid, r in results.items():
        s = sets.setdefault(r["set"], {"total": 0, "complete": 0, "partial": 0, "unresolved": 0, "crash": 0,
                                       "killed": 0, "classes": {}})
        s["total"] += 1
        s[r["status"]] = s.get(r["status"], 0) + 1
        s["classes"][r["class"]] = s["classes"].get(r["class"], 0) + 1
    if "seen" in sets or "unseen" in sets:
        ev = {"total": 0, "complete": 0}
        for k in ("seen", "unseen"):
            if k in sets:
                ev["total"] += sets[k]["total"]
                ev["complete"] += sets[k]["complete"]
        sets["evaluation(=seen+unseen)"] = ev

    # 前回との差分
    latest = os.path.join(ROOT, "bench", "latest.json")
    diff = {"gained": [], "lost": []}
    if os.path.exists(latest):
        prev = load(latest)
        prev_complete = set(prev.get("complete_ids", []))
        prev_ids = set(prev.get("ids", []))
        now_complete = {i for i, r in results.items() if r["status"] == "complete"}
        diff["gained"] = sorted(now_complete - prev_complete)
        diff["lost"] = sorted((prev_complete & set(results)) - now_complete)
        diff["previous_run"] = prev.get("run")
        diff["compared_ids"] = len(prev_ids & set(results))

    tests = None if args.no_tests else run_tests()
    unsound = [i for i, r in results.items() if r["status"] == "crash"]
    summary = {
        "run": stamp,
        "elapsed_s": round(time.time() - t0, 1),
        "timeouts": {"evaluation": args.timeout, "challenge": args.challenge_timeout},
        "sets": sets,
        "diff": diff,
        "tests": tests,
        "ids": sorted(results),
        "complete_ids": sorted(i for i, r in results.items() if r["status"] == "complete"),
        "crash_ids": unsound,
    }
    with open(os.path.join(out_dir, "summary.json"), "w", encoding="utf-8") as fp:
        json.dump(summary, fp, ensure_ascii=False, indent=1)
    full = not args.ids and wanted >= {"seen", "unseen"}
    if full:
        with open(latest, "w", encoding="utf-8") as fp:
            json.dump(summary, fp, ensure_ascii=False, indent=1)

    # 表示
    print(f"\n== ベンチマーク {stamp} ({summary['elapsed_s']} 秒, 評価 {args.timeout}s/問, 挑戦 {args.challenge_timeout}s/問)")
    names = {"seen": "評価セット(既見)", "unseen": "未見セット", "challenge": "挑戦セット",
             "evaluation(=seen+unseen)": "評価セット全体"}
    for k in ("evaluation(=seen+unseen)", "seen", "unseen", "challenge"):
        if k in sets:
            s = sets[k]
            extra = ""
            if "classes" in s:
                cl = ", ".join(f"{a}:{b}" for a, b in sorted(s["classes"].items(), key=lambda t: -t[1]))
                extra = f"  [{cl}]"
            print(f"  {names[k]}: 完全解決 {s['complete']}/{s['total']}{extra}")
    if diff.get("previous_run"):
        print(f"  前回 ({diff['previous_run']}) との差分: +{len(diff['gained'])} {diff['gained'][:20]}  "
              f"-{len(diff['lost'])} {diff['lost'][:20]}")
    if tests is not None:
        print(f"  テスト: {'成功' if tests['ok'] else '失敗'}  passed={tests['passed']} failed={tests['failed']} "
              f"負のテスト {tests['negative']['passed']}/{tests['negative']['total']} 成功")
        if tests["failing"]:
            print("  失敗したテスト:", tests["failing"])
    if unsound:
        print("  クラッシュ:", unsound[:20])
    print(f"  結果: {out_dir}")


if __name__ == "__main__":
    main()
