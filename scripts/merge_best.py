#!/usr/bin/env python3
"""公開用に、新しい計測結果と公開中のサイトの結果を問題ごとに比べ、良い方を残す。

一度解けた問題が、計測の揺れなどで次の計測で解けなくても、サイト上で未解決に戻らないようにするため。
順位: 解決（complete, special）> 病的な解の存在のみ（special_exist）> 部分結果・未解決 > 異常終了など。
同じ順位なら新しい計測の結果を使う。残した古い結果の証明文は公開中のサイトから取ってくる。

使い方: python3 scripts/merge_best.py <新しい集約結果のディレクトリ> --out best [--prev-url URL] [--run ID]
  --prev-url を省くか、そこにデータがなければ新しい結果だけを使う。
出力: <out>/results.jsonl, <out>/proofs/FE-XXXX.txt
"""
import argparse
import json
import os
import shutil
import urllib.error
import urllib.request

RANK = {"complete": 3, "special": 3, "special_exist": 2, "partial": 1, "unresolved": 1}


def rank(r):
    return RANK.get(r.get("status"), 0)


def fetch(url):
    try:
        with urllib.request.urlopen(url, timeout=30) as resp:
            return resp.read().decode("utf-8")
    except (urllib.error.URLError, TimeoutError, ValueError):
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("new_dir")
    ap.add_argument("--out", required=True)
    ap.add_argument("--prev-url", default="")
    ap.add_argument("--run", default="", help="新しい計測の識別子（結果に記録する）")
    args = ap.parse_args()
    os.makedirs(os.path.join(args.out, "proofs"), exist_ok=True)

    new = {}
    for line in open(os.path.join(args.new_dir, "results.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        if args.run:
            r["run"] = args.run
        new[r["id"]] = r

    prev = {}
    base = args.prev_url.rstrip("/") + "/" if args.prev_url else ""
    if base:
        text = fetch(base + "data/results.jsonl")
        if text:
            for line in text.splitlines():
                if line.strip():
                    r = json.loads(line)
                    prev[r["id"]] = r
    print(f"新しい結果 {len(new)} 問、公開中の結果 {len(prev)} 問")

    best = {}
    kept_old = []
    for pid in sorted(set(new) | set(prev)):
        n, p = new.get(pid), prev.get(pid)
        if n is None or (p is not None and rank(p) > rank(n)):
            best[pid] = p
            kept_old.append(pid)
        else:
            best[pid] = n

    missing = []
    for pid, r in best.items():
        dst = os.path.join(args.out, "proofs", pid + ".txt")
        if pid in kept_old:
            text = fetch(base + "data/proofs/" + pid + ".txt") if base else None
            if text is None:
                missing.append(pid)
                continue
            with open(dst, "w", encoding="utf-8") as fp:
                fp.write(text)
        else:
            src = os.path.join(args.new_dir, "proofs", pid + ".txt")
            if os.path.exists(src):
                shutil.copy(src, dst)

    # 証明文を取れなかった古い結果は使わず、新しい結果に戻す（結果と証明の組を崩さない）
    for pid in missing:
        if pid in new:
            best[pid] = new[pid]
            kept_old.remove(pid)
            src = os.path.join(args.new_dir, "proofs", pid + ".txt")
            if os.path.exists(src):
                shutil.copy(src, os.path.join(args.out, "proofs", pid + ".txt"))
        else:
            del best[pid]
            kept_old.remove(pid)

    with open(os.path.join(args.out, "results.jsonl"), "w", encoding="utf-8") as fp:
        for pid in sorted(best):
            fp.write(json.dumps(best[pid], ensure_ascii=False) + "\n")
    solved = sum(1 for r in best.values() if rank(r) == 3)
    print(f"統合: {len(best)} 問（解決 {solved}）。前の結果を残した問題 {len(kept_old)}: {' '.join(kept_old[:30])}")
    if missing:
        print(f"証明文を取れず新しい結果を使った問題: {' '.join(missing[:30])}")


if __name__ == "__main__":
    main()
