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
import shutil

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

CSS = """
* { box-sizing: border-box; }
body { color:#111; background:#f5f5f5; margin:0; font-family: system-ui, sans-serif; line-height:1.5; }
nav { background:#fff; border-bottom:1px solid #e5e5e5; }
nav div { max-width:1000px; margin:0 auto; padding:14px 20px; display:flex; gap:20px; align-items:center; }
nav a { color:#111; text-decoration:none; } nav a:hover { text-decoration:underline; }
nav .brand { font-weight:700; margin-right:auto; }
main { max-width:1000px; margin:0 auto; padding:28px 20px 60px; }
h1 { margin:0 0 24px; }
.stats { display:grid; grid-template-columns:repeat(5,1fr); gap:12px; margin-bottom:28px; }
.stat { text-align:center; background:#fff; border-top:4px solid #222; border-radius:10px; padding:16px; }
.stat strong { display:block; font-size:1.6rem; } .stat span { color:#666; font-size:.9rem; }
.stat.ok { border-top-color:#2e7d32; } .stat.ng { border-top-color:#c62828; } .stat.sp { border-top-color:#d99a00; }
.filters { display:flex; flex-wrap:wrap; gap:8px; margin-bottom:16px; }
.filters button { font:inherit; font-size:.95rem; background:#fff; color:#111; border:1px solid #c8c8c8;
  border-radius:8px; padding:6px 14px; cursor:pointer; }
.filters button.on { background:#222; color:#fff; border-color:#222; }
.filters .gap { width:16px; }
.list { display:grid; grid-template-columns:repeat(auto-fit,minmax(450px,1fr)); gap:16px; }
.card { display:block; color:inherit; text-decoration:none; border-left:6px solid; border-radius:10px; padding:18px 20px;
  transition: background .15s; }
.card.ok { background:#f0f9f1; border-left-color:#2e7d32; } .card.ok:hover { background:#e6f5e8; }
.card.ng { background:#fff1f1; border-left-color:#c62828; } .card.ng:hover { background:#ffe8e8; }
.card.sp { background:#fff8df; border-left-color:#d99a00; } .card.sp:hover { background:#fff1bd; }
.card[hidden] { display:none; }
.head { display:flex; justify-content:space-between; align-items:center; gap:12px; }
.head h2 { margin:0; font-size:1.25rem; }
.status { font-weight:600; } .ok .status { color:#2e7d32; } .ng .status { color:#c62828; } .sp .status { color:#9a5b00; }
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
@media (max-width:640px) { .stats { grid-template-columns:repeat(3,1fr); } .list { grid-template-columns:1fr; } }
"""

FILTER_JS = """
<script>
// st: ソルバの結果, site: 問題集サイトでの状態（データ取得時点）
const state = { st: 'all', site: 'all' };
for (const b of document.querySelectorAll('.filters button')) {
  b.addEventListener('click', () => {
    const k = b.dataset.k;
    state[k] = b.dataset.v;
    for (const o of document.querySelectorAll('.filters button[data-k="' + k + '"]')) o.classList.toggle('on', o === b);
    for (const c of document.querySelectorAll('.card')) {
      c.hidden = !((state.st === 'all' || c.dataset.st === state.st) && (state.site === 'all' || c.dataset.site === state.site));
    }
  });
}
</script>
"""


# ソルバの以前の版が出していた定型の言い回しを、今の版の言い回しに置き換える（意味は変えない。数学の内容には触れない）。
# 公開中の結果を残す仕組み（merge_best.py）で古い証明文が残っても、表示がそろうようにするため。
OLD_PHRASES = [
    ("見つけた解（検証核で代入を確認済み）:", "見つけた解:"),
    ("証明済みの事実（根の枝。導出つき）:", "証明済みの事実:"),
    ("状態: 特殊解決（病的な解の存在）", "状態: 特殊解決"),
    ("どの場合も両辺が一致する（検証核で確認）。", "どの場合も両辺が一致する。"),
    ("片側に有界なので（コーシーの方程式）", "片側に有界なので"),
    ("補題として解くと（下の【補題】）解は次に限るので", "下の【補題】より、解は次に限るので"),
    ("（この場合は未解決）", "この場合は未解決。"),
    ("加法的関数には ax の形でないもの（ハメル基底を使って作れる）も存在するので、これらは病的な解である。",
     "ハメル基底を使うと ax の形でない A も作れるので、これらには病的な解が含まれる。"),
]
OLD_PHRASE_RE = [
    # 「このような A には ax の形でないもの（…）も存在するので、これらは病的な解である。」
    (re.compile(r"このような A には ax の形でないもの（(.+?)）も存在するので、これらは病的な解である。"),
     lambda m: (m.group(1)[:-3] + "とすると" if m.group(1).endswith("とする") else m.group(1) + "と") + " ax の形でない A も作れるので、これらには病的な解が含まれる。"),
]


def normalize_text(t):
    for a, b in OLD_PHRASES:
        t = t.replace(a, b)
    for rx, f in OLD_PHRASE_RE:
        t = rx.sub(f, t)
    # 止まった理由の内部の枝番号（「  枝4: 時間切れ」）を外し、同じ理由はまとめる
    lines = t.split("\n")
    out, i = [], 0
    while i < len(lines):
        out.append(lines[i])
        if lines[i].strip() == "止まった理由:":
            why = []
            i += 1
            while i < len(lines) and lines[i].startswith("  "):
                r = re.sub(r"^  枝\d+: ", "", lines[i]).strip()
                hit = [w for w in why if w[0] == r]
                if hit:
                    hit[0][1] += 1
                else:
                    why.append([r, 1])
                i += 1
            for r, n in why:
                out.append(f"  {r}（{n} つの場合）" if n > 1 else f"  {r}")
            continue
        i += 1
    return "\n".join(out)


def prune_by_additive(lst):
    """表示用: 加法的関数を含む族（「A(x)」）を先頭にし、それに含まれる多項式の族（0, x, −x, cx, x + c など）を省く。
    ソルバの以前の版の結果にも同じ表示をするため、文字列で判定する（数学の内容は変えない）。"""
    adds = [t for t in lst if "A(" in t]
    if not adds:
        return lst
    kinds = []
    for a in adds:
        if "A(A(x)) = x" in a:
            kinds.append("inv")
        elif "A(A(x)) = A(x)" in a:
            kinds.append("proj")
        elif re.match(r"f\(x\) = A\(x\) [+-]", a):
            kinds.append("free_c")
        else:
            kinds.append("free")

    def lin(t):
        m = re.fullmatch(r"f\(x\) = (.+?)(（.+ は任意の実数）)?", t)
        if not m:
            return None
        e = m.group(1).replace(" ", "")
        if e == "0":
            return ("0", "0")
        mm = re.fullmatch(r"(-?)(\(\d+/\d+\)|\d+|c\d*)?x([+-](?:\(\d+/\d+\)|\d+|c\d*))?", e)
        if not mm:
            return None
        return ((mm.group(1) or "") + (mm.group(2) or "1"), mm.group(3) or "0")

    def subsumed(t):
        l = lin(t)
        if l is None:
            return False
        coef, const = l
        for k in kinds:
            if k == "free_c" or (k == "free" and const == "0"):
                return True
            if k == "inv" and const == "0" and coef in ("1", "-1"):
                return True
            if k == "proj" and const == "0" and coef in ("0", "1"):
                return True
        return False

    return adds + [t for t in lst if "A(" not in t and not subsumed(t)]


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
    # 次の公開で「良い方を残す」ための生データ（scripts/merge_best.py が読む）
    os.makedirs(os.path.join(args.out, "data", "proofs"), exist_ok=True)
    shutil.copy(os.path.join(rd, "results.jsonl"), os.path.join(args.out, "data", "results.jsonl"))
    pdir = os.path.join(rd, "proofs")
    if os.path.isdir(pdir):
        for name in os.listdir(pdir):
            text = open(os.path.join(pdir, name), encoding="utf-8").read()
            with open(os.path.join(args.out, "data", "proofs", name), "w", encoding="utf-8") as fp:
                fp.write(normalize_text(text))

    def kind(r):
        """表示の分類: ok = 解決（完全解決）, sp = 特殊解決（加法的関数を含む族・病的な解の存在）, ng = 未解決"""
        if r and r["status"] == "complete":
            return "ok"
        if r and r["status"] in ("special", "special_exist"):
            return "sp"
        return "ng"

    def sols(r):
        if not r:
            return ""
        return "、".join(prune_by_additive((r.get("families") if r["status"] in ("complete", "special") else r.get("found")) or []))

    def head(pid, r, tag_level="h2"):
        cls = kind(r)
        st = {"ok": "解決", "sp": "特殊解決", "ng": "未解決"}[cls] if r else "未計測"
        return (f'<div class="head"><{tag_level}>#{num(pid)}</{tag_level}>'
                f'<span class="status">{st}</span></div>'), cls

    # 問題ごとのページ
    for k, pid in enumerate(ids):
        p, r = problems[pid], results.get(pid)
        h, cls = head(pid, r, "h1")
        eqs = "".join(f'<div class="eq">{math(e["display"])}</div>' for e in p["equations"][:1])
        body = f'<div class="problem {cls}">{h}{eqs}'
        s = sols(r)
        if r and r["status"] in ("complete", "special"):
            body += f'<div class="sol">解: {esc(s) if s else "なし"}</div>'
        elif s:
            body += f'<div class="sol">見つけた解: {esc(s)}</div>'
        body += (f'<div class="src"><a href="https://gghx0.github.io/fe-project/fe/{num(pid):04d}">問題集 #{num(pid)}</a>'
                 + "".join(f' · <a href="{esc(x["url"])}">{esc(x.get("label", "出典"))}</a>' for x in p.get("references", []))
                 + "</div></div>")
        proof_path = os.path.join(rd, "proofs", pid + ".txt")
        if os.path.exists(proof_path):
            title = "証明" if r and r["status"] in ("complete", "special") else "途中経過"
            body += f"<h3>{title}</h3><pre>{esc(normalize_text(open(proof_path, encoding='utf-8').read()).strip())}</pre>"
        prev_l = f'<a href="{ids[k - 1]}.html">← #{num(ids[k - 1])}</a>' if k > 0 else "<span></span>"
        next_l = f'<a href="{ids[k + 1]}.html">#{num(ids[k + 1])} →</a>' if k + 1 < len(ids) else "<span></span>"
        body += f'<div class="pager">{prev_l}{next_l}</div>'
        with open(os.path.join(args.out, "p", pid + ".html"), "w", encoding="utf-8") as fp:
            fp.write(page(f"#{num(pid)} | FE Solver", body, depth=1))

    # 一覧
    done = sum(1 for r in results.values() if kind(r) == "ok")
    special = sum(1 for r in results.values() if kind(r) == "sp")
    total = len(results)

    def stat(value, label, cls=""):
        return f'<div class="stat {cls}"><strong>{value}</strong><span>{label}</span></div>'

    stats = (stat(total, "全問題") + stat(done, "解決", "ok") + stat(special, "特殊解決", "sp") +
             stat(total - done - special, "未解決", "ng") +
             stat(f"{100 * (done + special) / total:.1f}%" if total else "—", "解決率", "ok"))
    filters = ('<div class="filters">'
               '<button data-k="st" data-v="all" class="on">すべて</button>'
               '<button data-k="st" data-v="ng">未解決</button><button data-k="st" data-v="sp">特殊解決</button>'
               '<button data-k="st" data-v="ok">解決</button>'
               '<span class="gap"></span>'
               '<button data-k="site" data-v="all" class="on">All</button>'
               '<button data-k="site" data-v="open">Open</button><button data-k="site" data-v="solved">Solved</button>'
               '</div>')
    cards = ""
    for pid in ids:
        r = results.get(pid)
        if not r:
            continue
        h, cls = head(pid, r)
        s = sols(r)
        sol_html = f'<div class="sol">{esc(s)}</div>' if s and r["status"] in ("complete", "special") else ""
        cards += (f'<a class="card {cls}" href="p/{pid}.html" data-st="{cls}" data-site="{esc(problems[pid]["status"])}">{h}'
                  f'<div class="eq">{math(problems[pid]["equations"][0]["display"])}</div>{sol_html}</a>')
    body = f'<h1>FE Solver</h1><div class="stats">{stats}</div>{filters}<div class="list">{cards}</div>{FILTER_JS}'
    with open(os.path.join(args.out, "index.html"), "w", encoding="utf-8") as fp:
        fp.write(page("FE Solver", body))

    print(f"サイトを {args.out} に作成（問題ページ {len(ids)}、解決 {done}、特殊解決 {special}）")


if __name__ == "__main__":
    main()
