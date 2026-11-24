#!/usr/bin/env python3
"""問題集データの取得スクリプト。

取得元:
  - サイト: https://gghx0.github.io/fe-project/ （状態の照合に使う）
  - 公開元リポジトリ: https://github.com/gghx0/fe-project
      data/fe_database.json   全847問の方程式（x<->y 対称で同一視したグループ）
      data/fe_references.json 出典（AoPS スレッドなど）
      solutions/FE-*.md       frontmatter の status（solved/open）・著者など

注意: solutions/*.md の本文（解答）は取り込まない。frontmatter だけを抽出する。
      未見セットの外部解答を読まないための措置（DECISIONS.md 参照）。

使い方: python3 -I scripts/fetch_data.py [作業用ディレクトリ]
出力: data/problems.json, data/source.json, data/raw/*
"""
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import urllib.request

SITE = "https://gghx0.github.io/fe-project/"
REPO = "https://github.com/gghx0/fe-project.git"
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, "data")


def parse_frontmatter(text):
    """YAML frontmatter のうち、単純な `key: value` と `key: [a, b]` だけを読む。"""
    m = re.match(r"---\r?\n(.*?)\r?\n---", text, re.S)
    if not m:
        return {}
    out = {}
    for line in m.group(1).splitlines():
        if ":" not in line:
            continue
        k, v = line.split(":", 1)
        k, v = k.strip(), v.strip()
        if v.startswith("[") and v.endswith("]"):
            items = [s.strip().strip("'\"") for s in v[1:-1].split(",") if s.strip()]
            out[k] = items
        elif v in ("null", "~", ""):
            out[k] = None
        else:
            out[k] = v.strip("'\"")
    return out


def main():
    work = sys.argv[1] if len(sys.argv) > 1 else tempfile.mkdtemp(prefix="fe_fetch_")
    os.makedirs(work, exist_ok=True)
    fetched_at = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")

    repo_dir = os.path.join(work, "fe-project")
    if not os.path.isdir(repo_dir):
        subprocess.run(["git", "clone", "-q", REPO, repo_dir], check=True)
    commit = subprocess.run(["git", "-C", repo_dir, "rev-parse", "HEAD"],
                            check=True, capture_output=True, text=True).stdout.strip()
    commit_date = subprocess.run(["git", "-C", repo_dir, "log", "-1", "--format=%cI"],
                                 check=True, capture_output=True, text=True).stdout.strip()

    with open(os.path.join(repo_dir, "data", "fe_database.json"), encoding="utf-8") as fp:
        database = json.load(fp)
    with open(os.path.join(repo_dir, "data", "fe_references.json"), encoding="utf-8") as fp:
        references = json.load(fp)

    # solutions/*.md の frontmatter のみ
    meta = {}
    sol_dir = os.path.join(repo_dir, "solutions")
    for name in sorted(os.listdir(sol_dir)):
        m = re.fullmatch(r"(FE-\d{4})\.md", name)
        if not m:
            continue
        with open(os.path.join(sol_dir, name), encoding="utf-8") as fp:
            fm = parse_frontmatter(fp.read())
        meta[m.group(1)] = {k: fm.get(k) for k in ("status", "authors", "verified_by",
                                                     "date_resolved", "tags") if k in fm}

    # デプロイ済みサイトの状態（照合用）
    with urllib.request.urlopen(SITE, timeout=60) as resp:
        html = resp.read().decode("utf-8")
    site_status = {}
    for st, num in re.findall(r'class="fe-card [\w-]+" data-status="([\w-]+)" data-problem-number="(\d+)"', html):
        site_status["FE-%04d" % int(num)] = st

    problems = []
    mismatches = []
    for rec in database:
        pid = rec["id"]
        status = (meta.get(pid) or {}).get("status") or "open"  # サイトと同じ既定値
        if site_status.get(pid) != status:
            mismatches.append((pid, status, site_status.get(pid)))
        problems.append({
            "id": pid,
            "self_symmetric": rec["self_symmetric"],
            "equations": rec["equations"],
            "status": status,
            "solution_meta": meta.get(pid),
            "references": references.get(pid, []),
        })

    if mismatches:
        print("WARNING: repository and site status differ:", mismatches[:20], file=sys.stderr)

    os.makedirs(os.path.join(DATA, "raw"), exist_ok=True)
    for name in ("fe_database.json", "fe_references.json", "fe_index.txt"):
        with open(os.path.join(repo_dir, "data", name), "rb") as src, \
                open(os.path.join(DATA, "raw", name), "wb") as dst:
            dst.write(src.read())
    with open(os.path.join(DATA, "problems.json"), "w", encoding="utf-8") as fp:
        json.dump(problems, fp, ensure_ascii=False, indent=1)
        fp.write("\n")

    def sha(path):
        with open(path, "rb") as fp:
            return hashlib.sha256(fp.read()).hexdigest()

    counts = {}
    for p in problems:
        counts[p["status"]] = counts.get(p["status"], 0) + 1
    source = {
        "fetched_at_utc": fetched_at,
        "site": SITE,
        "about": SITE + "about",
        "repository": REPO,
        "repository_commit": commit,
        "repository_commit_date": commit_date,
        "files": {
            "data/raw/fe_database.json": sha(os.path.join(DATA, "raw", "fe_database.json")),
            "data/raw/fe_references.json": sha(os.path.join(DATA, "raw", "fe_references.json")),
            "data/problems.json": sha(os.path.join(DATA, "problems.json")),
        },
        "status_source": "solutions/FE-XXXX.md の frontmatter `status`（無ければ open）。デプロイ済みサイトの data-status と照合済み",
        "status_site_mismatches": len(mismatches),
        "counts": {"problems": len(problems), "literal_equations": sum(len(p["equations"]) for p in problems), **counts},
    }
    with open(os.path.join(DATA, "source.json"), "w", encoding="utf-8") as fp:
        json.dump(source, fp, ensure_ascii=False, indent=1)
        fp.write("\n")
    print(json.dumps(source, ensure_ascii=False, indent=1))


if __name__ == "__main__":
    main()
