#!/usr/bin/env python3
"""分割実行（bench.py --shard）の結果を 1 つにまとめる。

使い方: python3 scripts/merge_results.py <分割の出力ディレクトリ…> --out merged [--tests tests.txt] [--meta k=v …]
出力: merged/results.jsonl, merged/proofs/, merged/summary.json, merged/tests.txt
"""
import argparse
import json
import os
import re
import shutil

NAMES = {"seen": "評価セット(既見)", "unseen": "初見セット", "challenge": "挑戦セット"}


def parse_tests(text):
    passed = sum(int(m) for m in re.findall(r"test result: \w+\. (\d+) passed", text))
    failed = sum(int(m) for m in re.findall(r"(\d+) failed", text))
    failing = re.findall(r"^test (\S+) \.\.\. FAILED", text, re.M)
    neg = re.findall(r"^test (\S*negative\S*) \.\.\. (\w+)", text, re.M)
    ok = "test result: FAILED" not in text and passed > 0
    return {"ok": ok, "passed": passed, "failed": failed, "failing": failing,
            "negative": {"passed": sum(1 for _, s in neg if s == "ok"), "total": len(neg)}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dirs", nargs="+")
    ap.add_argument("--out", required=True)
    ap.add_argument("--tests", default="")
    ap.add_argument("--meta", nargs="*", default=[])
    args = ap.parse_args()
    os.makedirs(os.path.join(args.out, "proofs"), exist_ok=True)
    results = {}
    for d in args.dirs:
        rp = os.path.join(d, "results.jsonl")
        if not os.path.exists(rp):
            continue
        for line in open(rp, encoding="utf-8"):
            r = json.loads(line)
            results[r["id"]] = r
        pd = os.path.join(d, "proofs")
        if os.path.isdir(pd):
            for name in os.listdir(pd):
                shutil.copy(os.path.join(pd, name), os.path.join(args.out, "proofs", name))
    with open(os.path.join(args.out, "results.jsonl"), "w", encoding="utf-8") as fp:
        for pid in sorted(results):
            fp.write(json.dumps(results[pid], ensure_ascii=False) + "\n")
    sets = {}
    for r in results.values():
        s = sets.setdefault(r["set"], {"total": 0, "solved": 0, "complete": 0, "special": 0, "special_exist": 0,
                                       "partial": 0, "unresolved": 0, "crash": 0, "killed": 0, "skipped": 0,
                                       "classes": {}})
        s["total"] += 1
        s[r["status"]] = s.get(r["status"], 0) + 1
        if r["status"] in ("complete", "special"):
            s["solved"] += 1
        s["classes"][r.get("class", "?")] = s["classes"].get(r.get("class", "?"), 0) + 1
    ev = {"total": 0, "solved": 0, "complete": 0, "special": 0, "special_exist": 0}
    for k in ("seen", "unseen"):
        if k in sets:
            for key in ev:
                ev[key] += sets[k][key]
    sets["evaluation(=seen+unseen)"] = ev
    tests = None
    if args.tests and os.path.exists(args.tests):
        text = open(args.tests, encoding="utf-8", errors="replace").read()
        shutil.copy(args.tests, os.path.join(args.out, "tests.txt"))
        tests = parse_tests(text)
    meta = dict(kv.split("=", 1) for kv in args.meta)
    summary = {"sets": sets, "tests": tests, "meta": meta,
               "solved_ids": sorted(i for i, r in results.items() if r["status"] in ("complete", "special")),
               "complete_ids": sorted(i for i, r in results.items() if r["status"] == "complete")}
    with open(os.path.join(args.out, "summary.json"), "w", encoding="utf-8") as fp:
        json.dump(summary, fp, ensure_ascii=False, indent=1)
    print("== ベンチマーク（分割実行の集約）")
    for k, name in (("evaluation(=seen+unseen)", "評価セット全体"), ("seen", NAMES["seen"]),
                    ("unseen", NAMES["unseen"]), ("challenge", NAMES["challenge"])):
        if k in sets:
            print(f"  {name}: 解決 {sets[k]['solved']}/{sets[k]['total']}（完全解決 {sets[k]['complete']}, "
                  f"特殊解決 {sets[k]['special']}; 病的な解の存在のみ {sets[k]['special_exist']}）")
    if tests:
        print(f"  テスト: {'成功' if tests['ok'] else '失敗'} passed={tests['passed']} failed={tests['failed']} "
              f"負のテスト {tests['negative']['passed']}/{tests['negative']['total']} 成功")


if __name__ == "__main__":
    main()
