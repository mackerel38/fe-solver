#!/usr/bin/env python3
"""GitHub Pages 用の静的サイトを作る（結果の一覧と問題ごとの証明）。

使い方: python3 scripts/build_site.py <集約した結果のディレクトリ> --out site
入力: <dir>/results.jsonl, <dir>/proofs/FE-XXXX.txt, <dir>/summary.json, <dir>/tests.txt（任意）, data/problems.json
証明文はソルバ（fe_render）が検証核の導出記録から生成したものを、そのまま表示する（このスクリプトは書き換えない）。
"""
import argparse
import html
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SET_NAME = {"seen": "評価（既見）", "unseen": "評価（初見）", "challenge": "挑戦"}
STATUS_NAME = {"complete": "完全解決", "partial": "部分結果", "unresolved": "未解決", "crash": "異常終了",
               "killed": "強制終了", "skipped": "未実行"}

CSS = """
:root { color-scheme: light dark; --fg:#1d1f23; --muted:#5d6470; --bg:#fbfbfc; --card:#fff; --line:#e3e5e8;
  --ok:#1f7a3a; --warn:#9a6700; --accent:#2457a6; }
@media (prefers-color-scheme: dark) { :root { --fg:#e6e8eb; --muted:#a2a8b2; --bg:#15171a; --card:#1d2024;
  --line:#30343a; --ok:#5cc27a; --warn:#d7a23a; --accent:#7aa7ef; } }
* { box-sizing: border-box; }
body { margin:0; font-family: system-ui, -apple-system, "Hiragino Sans", "Noto Sans JP", sans-serif;
  color: var(--fg); background: var(--bg); line-height: 1.6; }
main { max-width: 1040px; margin: 0 auto; padding: 28px 18px 60px; }
a { color: var(--accent); text-decoration: none; } a:hover { text-decoration: underline; }
h1 { font-size: 1.6rem; margin: 0 0 6px; } h2 { font-size: 1.2rem; margin: 32px 0 10px; }
.muted { color: var(--muted); font-size: .92rem; }
nav { display:flex; gap:16px; flex-wrap: wrap; margin: 10px 0 22px; font-size: .95rem; }
.cards { display:grid; grid-template-columns: repeat(auto-fit, minmax(190px, 1fr)); gap: 12px; }
.card { background: var(--card); border: 1px solid var(--line); border-radius: 10px; padding: 14px 16px; }
.card .num { font-size: 1.6rem; font-weight: 650; font-variant-numeric: tabular-nums; }
.card .lbl { color: var(--muted); font-size: .88rem; }
table { width: 100%; border-collapse: collapse; background: var(--card); border: 1px solid var(--line);
  border-radius: 10px; overflow: hidden; font-size: .93rem; }
th, td { text-align: left; padding: 7px 10px; border-bottom: 1px solid var(--line); vertical-align: top; }
th { font-weight: 600; color: var(--muted); font-size: .85rem; }
tr:last-child td { border-bottom: none; }
code, pre { font-family: ui-monospace, "SFMono-Regular", Menlo, Consolas, monospace; }
pre { background: var(--card); border: 1px solid var(--line); border-radius: 10px; padding: 14px 16px;
  white-space: pre-wrap; word-break: break-word; font-size: .88rem; line-height: 1.55; }
.ok { color: var(--ok); font-weight: 600; } .warn { color: var(--warn); }
input[type=search] { width: 100%; padding: 8px 10px; border: 1px solid var(--line); border-radius: 8px;
  background: var(--card); color: var(--fg); margin: 6px 0 12px; font-size: .95rem; }
"""

FILTER_JS = """
<script>
function filt(inp, tid) {
  const q = inp.value.trim().toLowerCase();
  for (const tr of document.querySelectorAll('#' + tid + ' tbody tr')) {
    tr.style.display = tr.textContent.toLowerCase().includes(q) ? '' : 'none';
  }
}
</script>
"""


def page(title, body, depth=0):
    up = "../" * depth
    nav = (f'<nav><a href="{up}index.html">概要</a><a href="{up}solved.html">完全解決した問題</a>'
           f'<a href="{up}all.html">全問題</a><a href="{up}tests.html">テスト</a></nav>')
    return (f'<!DOCTYPE html><html lang="ja"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width, initial-scale=1"><title>{html.escape(title)}</title>'
            f'<style>{CSS}</style></head><body><main>{nav}{body}</main>{FILTER_JS}</body></html>')


def esc(s):
    return html.escape(str(s))


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
    summary = json.load(open(os.path.join(rd, "summary.json"), encoding="utf-8"))
    problems = {p["id"]: p for p in json.load(open(os.path.join(ROOT, "data", "problems.json"), encoding="utf-8"))}
    os.makedirs(os.path.join(args.out, "p"), exist_ok=True)

    def sols(r):
        return "、".join(r.get("families") or []) if r["status"] == "complete" else "、".join(r.get("found") or [])

    # 問題ごとのページ
    for pid, p in problems.items():
        r = results.get(pid)
        eqs = "<br>".join(f"<code>{esc(e['display'])}</code>" for e in p["equations"])
        refs = " ".join(f'<a href="{esc(x["url"])}">{esc(x.get("label", "link"))}</a>' for x in p.get("references", []))
        site_link = f'https://gghx0.github.io/fe-project/fe/{pid[3:]}'
        rows = [("方程式", eqs), ("セット", esc(SET_NAME.get(r["set"], r["set"]) if r else "（未計測）")),
                ("サイト上の状態", f'{esc(p["status"])}（<a href="{site_link}">問題ページ</a>）'),
                ("出典", refs or "—")]
        body = f"<h1>{esc(pid)}</h1>"
        if r:
            st = STATUS_NAME.get(r["status"], r["status"])
            cls = "ok" if r["status"] == "complete" else "warn"
            rows.append(("結果", f'<span class="{cls}">{esc(st)}</span>（{r.get("time_ms", 0) / 1000:.1f} 秒）'))
            if r["status"] == "complete":
                rows.append(("解の集合", esc(sols(r)) or "（解なし）"))
            else:
                rows.append(("見つけた解", esc(sols(r)) or "—"))
                rows.append(("止まった理由", esc("; ".join(r.get("reasons", [])))))
        body += "<table>" + "".join(f"<tr><th>{k}</th><td>{v}</td></tr>" for k, v in rows) + "</table>"
        proof_path = os.path.join(rd, "proofs", pid + ".txt")
        if os.path.exists(proof_path):
            title = "証明" if r and r["status"] == "complete" else "報告（見つけた解と証明済みの事実）"
            body += f"<h2>{title}</h2><pre>{esc(open(proof_path, encoding='utf-8').read().strip())}</pre>"
        with open(os.path.join(args.out, "p", pid + ".html"), "w", encoding="utf-8") as fp:
            fp.write(page(f"{pid} | 関数方程式ソルバ", body, depth=1))

    # 概要
    sets = summary["sets"]
    meta = summary.get("meta", {})
    def card(key, label):
        s = sets.get(key)
        if not s:
            return ""
        return f'<div class="card"><div class="num">{s["complete"]} / {s["total"]}</div><div class="lbl">{label} 完全解決</div></div>'
    cards = (card("evaluation(=seen+unseen)", "評価セット全体") + card("seen", "評価（既見）") +
             card("unseen", "評価（初見）") + card("challenge", "挑戦セット（サイトで未解決）"))
    t = summary.get("tests")
    tests_html = ("（未実行）" if not t else
                  f'<span class="{"ok" if t["ok"] else "warn"}">{"成功" if t["ok"] else "失敗"}</span>: '
                  f'passed {t["passed"]}, failed {t["failed"]}、負のテスト {t["negative"]["passed"]}/{t["negative"]["total"]} 成功')
    meta_html = "、".join(f"{esc(k)}: {esc(v)}" for k, v in meta.items())
    body = ("<h1>R→R 関数方程式ソルバ: 結果と証明</h1>"
            '<p class="muted">問題集 <a href="https://gghx0.github.io/fe-project/">FE Project</a> の全 847 問を解いた結果。'
            "証明はソルバが検証核の導出記録から機械的に生成した日本語の証明文で、誤った事実を作れない構成（小さな検証核の推論規則だけが"
            "事実を作る）になっている。</p>"
            f'<p class="muted">{meta_html}</p><div class="cards">{cards}</div>'
            f"<h2>テスト</h2><p>{tests_html}（<a href=\"tests.html\">出力</a>）</p>")
    ch = sorted((r for r in results.values() if r["set"] == "challenge" and r["status"] == "complete"), key=lambda r: r["id"])
    if ch:
        body += "<h2>挑戦セット（サイトで未解決）で完全解決した問題</h2><table><thead><tr><th>ID</th><th>方程式</th><th>解の集合</th></tr></thead><tbody>"
        for r in ch:
            body += (f'<tr><td><a href="p/{r["id"]}.html">{r["id"]}</a></td>'
                     f'<td><code>{esc(problems[r["id"]]["equations"][0]["display"])}</code></td><td>{esc(sols(r))}</td></tr>')
        body += "</tbody></table>"
    with open(os.path.join(args.out, "index.html"), "w", encoding="utf-8") as fp:
        fp.write(page("関数方程式ソルバ: 結果と証明", body))

    # 完全解決した問題
    def table(rows, tid):
        h = (f'<input type="search" placeholder="絞り込み（ID・方程式・解）" oninput="filt(this, \'{tid}\')">'
             f'<table id="{tid}"><thead><tr><th>ID</th><th>セット</th><th>方程式</th><th>解</th></tr></thead><tbody>')
        for r in rows:
            h += (f'<tr><td><a href="p/{r["id"]}.html">{r["id"]}</a></td><td>{esc(SET_NAME.get(r["set"], r["set"]))}</td>'
                  f'<td><code>{esc(problems[r["id"]]["equations"][0]["display"])}</code></td><td>{esc(sols(r))}</td></tr>')
        return h + "</tbody></table>"
    done = sorted((r for r in results.values() if r["status"] == "complete"), key=lambda r: r["id"])
    body = f"<h1>完全解決した問題（{len(done)} 問）</h1>" + table(done, "solved")
    with open(os.path.join(args.out, "solved.html"), "w", encoding="utf-8") as fp:
        fp.write(page("完全解決した問題", body))

    # 全問題
    body = "<h1>全問題</h1><input type=\"search\" placeholder=\"絞り込み（ID・方程式・状態）\" oninput=\"filt(this, 'all')\">"
    body += '<table id="all"><thead><tr><th>ID</th><th>セット</th><th>方程式</th><th>結果</th><th>解 / 見つけた解</th></tr></thead><tbody>'
    for pid in sorted(problems):
        r = results.get(pid)
        if not r:
            continue
        st = STATUS_NAME.get(r["status"], r["status"])
        cls = "ok" if r["status"] == "complete" else ""
        body += (f'<tr><td><a href="p/{pid}.html">{pid}</a></td><td>{esc(SET_NAME.get(r["set"], r["set"]))}</td>'
                 f'<td><code>{esc(problems[pid]["equations"][0]["display"])}</code></td>'
                 f'<td class="{cls}">{esc(st)}</td><td>{esc(sols(r))}</td></tr>')
    body += "</tbody></table>"
    with open(os.path.join(args.out, "all.html"), "w", encoding="utf-8") as fp:
        fp.write(page("全問題", body))

    # テスト
    tp = os.path.join(rd, "tests.txt")
    tbody = f"<pre>{esc(open(tp, encoding='utf-8', errors='replace').read())}</pre>" if os.path.exists(tp) else "<p>（未実行）</p>"
    with open(os.path.join(args.out, "tests.html"), "w", encoding="utf-8") as fp:
        fp.write(page("テスト", "<h1>テストの出力</h1>" + tbody))
    print(f"サイトを {args.out} に作成（問題ページ {len(problems)}、完全解決 {len(done)}）")


if __name__ == "__main__":
    main()
