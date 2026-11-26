#!/usr/bin/env python3
"""GitHub Pages 用の静的サイトを作る（問題の一覧と、問題ごとの結果・証明）。

使い方: python3 scripts/build_site.py <集約した結果のディレクトリ> --out site
入力: <dir>/results.jsonl, <dir>/proofs/FE-XXXX.txt, data/problems.json
証明文はソルバ（fe_render）が検証核の導出記録から生成したものを、そのまま表示する（このスクリプトは書き換えない）。
"""
import argparse
import html
import json
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATUS_NAME = {"complete": "完全解決", "partial": "部分結果", "unresolved": "未解決", "crash": "異常終了",
               "killed": "強制終了", "skipped": "未実行"}

CSS = """
* { box-sizing: border-box; }
body { color:#111; background:#f5f5f5; margin:0; font-family: system-ui, sans-serif; line-height:1.5; }
nav { background:#fff; border-bottom:1px solid #e5e5e5; }
nav div { max-width:1000px; margin:0 auto; padding:14px 20px; display:flex; gap:20px; align-items:center; }
nav a { color:#111; text-decoration:none; } nav a:hover { text-decoration:underline; }
nav .brand { font-weight:700; margin-right:auto; }
main { max-width:1000px; margin:0 auto; padding:28px 20px 60px; }
h1 { margin:0 0 24px; }
.stats { display:grid; grid-template-columns:repeat(4,1fr); gap:12px; margin-bottom:28px; }
.stat { text-align:center; background:#fff; border-top:4px solid #222; border-radius:10px; padding:16px; }
.stat strong { display:block; font-size:1.6rem; } .stat span { color:#666; font-size:.9rem; }
.stat.ok { border-top-color:#2e7d32; } .stat.ng { border-top-color:#c62828; }
.filters { display:flex; flex-wrap:wrap; gap:8px; margin-bottom:16px; }
.filters button { font:inherit; font-size:.95rem; background:#fff; color:#111; border:1px solid #c8c8c8;
  border-radius:8px; padding:6px 14px; cursor:pointer; }
.filters button.on { background:#222; color:#fff; border-color:#222; }
.list { display:grid; grid-template-columns:repeat(auto-fit,minmax(450px,1fr)); gap:16px; }
.card { display:block; color:inherit; text-decoration:none; border-left:6px solid; border-radius:10px; padding:18px 20px;
  transition: background .15s; }
.card.ok { background:#f0f9f1; border-left-color:#2e7d32; } .card.ok:hover { background:#e6f5e8; }
.card.ng { background:#fff1f1; border-left-color:#c62828; } .card.ng:hover { background:#ffe8e8; }
.card[hidden] { display:none; }
.head { display:flex; justify-content:space-between; align-items:center; gap:12px; }
.head h2 { margin:0; font-size:1.25rem; }
.status { font-weight:600; } .ok .status { color:#2e7d32; } .ng .status { color:#c62828; }
.eq { font-family: "Cambria Math", "STIX Two Math", "Latin Modern Math", Georgia, serif; font-size:1.15rem;
  margin:12px 0 4px; overflow-x:auto; white-space:nowrap; }
.sol { color:#444; font-size:.92rem; }
.problem .eq { font-size:1.4rem; margin:20px 0; }
.problem .sol { font-size:1rem; }
h3 { margin:32px 0 10px; font-size:1.1rem; }
pre { background:#fff; border:1px solid #e2e2e2; border-radius:10px; padding:16px; white-space:pre-wrap;
  word-break:break-word; font-size:.88rem; line-height:1.55; margin:0; }
.pager { display:flex; justify-content:space-between; margin-top:28px; }
.pager a, .src a { color:#3451a3; text-decoration:none; } .pager a:hover, .src a:hover { text-decoration:underline; }
.src { color:#666; font-size:.9rem; margin-top:8px; }
@media (max-width:640px) { .stats { grid-template-columns:repeat(2,1fr); } .list { grid-template-columns:1fr; } }
"""

FILTER_JS = """
<script>
for (const b of document.querySelectorAll('.filters button')) {
  b.addEventListener('click', () => {
    for (const o of document.querySelectorAll('.filters button')) o.classList.toggle('on', o === b);
    for (const c of document.querySelectorAll('.card')) c.hidden = !(b.dataset.v === 'all' || c.dataset.st === b.dataset.v);
  });
}
</script>
"""


def esc(s):
    return html.escape(str(s))


def math(s):
    """方程式の表示: x^2 を上付きにするだけ（文字列そのものは変えない）"""
    return re.sub(r"\^(\d+)", r"<sup>\1</sup>", esc(s))


def num(pid):
    return int(pid.split("-")[1])


def page(title, body, depth=0):
    up = "../" * depth
    nav = (f'<nav><div><a class="brand" href="{up}index.html">FE Solver</a>'
           '<a href="https://gghx0.github.io/fe-project/">問題集</a></div></nav>')
    return (f'<!DOCTYPE html><html lang="ja"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width, initial-scale=1"><title>{esc(title)}</title>'
            f'<style>{CSS}</style></head><body>{nav}<main>{body}</main></body></html>')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run_dir")
    ap.add_argument("--out", default="site")
    args = ap.parse_args()
    rd = args.run_dir
    results = {}
    for line in open(os.path.join(rd, "results.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        results[r["id"]] = r
    problems = {p["id"]: p for p in json.load(open(os.path.join(ROOT, "data", "problems.json"), encoding="utf-8"))}
    ids = sorted(problems, key=num)
    os.makedirs(os.path.join(args.out, "p"), exist_ok=True)

    def sols(r):
        if not r:
            return ""
        return "、".join((r.get("families") if r["status"] == "complete" else r.get("found")) or [])

    def head(pid, r, tag_level="h2"):
        ok = r and r["status"] == "complete"
        st = STATUS_NAME.get(r["status"], r["status"]) if r else "未計測"
        return (f'<div class="head"><{tag_level}>#{num(pid)}</{tag_level}>'
                f'<span class="status">{st}</span></div>'), ("ok" if ok else "ng")

    # 問題ごとのページ
    for k, pid in enumerate(ids):
        p, r = problems[pid], results.get(pid)
        h, cls = head(pid, r, "h1")
        eqs = "".join(f'<div class="eq">{math(e["display"])}</div>' for e in p["equations"][:1])
        body = f'<div class="problem {cls}">{h}{eqs}'
        s = sols(r)
        if r and r["status"] == "complete":
            body += f'<div class="sol">解: {esc(s) if s else "なし"}</div>'
        elif s:
            body += f'<div class="sol">見つけた解: {esc(s)}</div>'
        body += (f'<div class="src"><a href="https://gghx0.github.io/fe-project/fe/{num(pid):04d}">問題集 #{num(pid)}</a>'
                 + "".join(f' · <a href="{esc(x["url"])}">{esc(x.get("label", "出典"))}</a>' for x in p.get("references", []))
                 + "</div></div>")
        proof_path = os.path.join(rd, "proofs", pid + ".txt")
        if os.path.exists(proof_path):
            title = "証明" if r and r["status"] == "complete" else "途中経過"
            body += f"<h3>{title}</h3><pre>{esc(open(proof_path, encoding='utf-8').read().strip())}</pre>"
        prev_l = f'<a href="{ids[k - 1]}.html">← #{num(ids[k - 1])}</a>' if k > 0 else "<span></span>"
        next_l = f'<a href="{ids[k + 1]}.html">#{num(ids[k + 1])} →</a>' if k + 1 < len(ids) else "<span></span>"
        body += f'<div class="pager">{prev_l}{next_l}</div>'
        with open(os.path.join(args.out, "p", pid + ".html"), "w", encoding="utf-8") as fp:
            fp.write(page(f"#{num(pid)} | FE Solver", body, depth=1))

    # 一覧
    done = sum(1 for r in results.values() if r["status"] == "complete")
    total = len(results)

    def stat(value, label, cls=""):
        return f'<div class="stat {cls}"><strong>{value}</strong><span>{label}</span></div>'

    stats = (stat(total, "全問題") + stat(done, "完全解決", "ok") + stat(total - done, "未完了", "ng") +
             stat(f"{100 * done / total:.1f}%" if total else "—", "解決率", "ok"))
    filters = ('<div class="filters"><button data-v="all" class="on">すべて</button>'
               '<button data-v="ok">完全解決</button><button data-v="ng">未完了</button></div>')
    cards = ""
    for pid in ids:
        r = results.get(pid)
        if not r:
            continue
        h, cls = head(pid, r)
        s = sols(r)
        sol_html = f'<div class="sol">{esc(s)}</div>' if s and r["status"] == "complete" else ""
        cards += (f'<a class="card {cls}" href="p/{pid}.html" data-st="{cls}">{h}'
                  f'<div class="eq">{math(problems[pid]["equations"][0]["display"])}</div>{sol_html}</a>')
    body = f'<h1>FE Solver</h1><div class="stats">{stats}</div>{filters}<div class="list">{cards}</div>{FILTER_JS}'
    with open(os.path.join(args.out, "index.html"), "w", encoding="utf-8") as fp:
        fp.write(page("FE Solver", body))

    print(f"サイトを {args.out} に作成（問題ページ {len(ids)}、完全解決 {done}）")


if __name__ == "__main__":
    main()
