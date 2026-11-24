#!/usr/bin/env python3
"""評価セット/初見セット/挑戦セットの分割を作る（一度だけ実行し、結果を data/split.json に固定する）。

- 評価セット: サイトで solved の問題
- 初見セット: 評価セットから random.Random(SEED).sample で UNSEEN_COUNT 問を抽出
- 挑戦セット: solved 以外（open）
data/split.json が既にある場合は上書きしない（分け方の固定）。
"""
import json, os, random, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SEED = 20261125
UNSEEN_COUNT = 110  # 評価セット 552 問の約 20%
out = os.path.join(ROOT, "data", "split.json")
if os.path.exists(out) and "--force" not in sys.argv:
    sys.exit("data/split.json already exists; the split is fixed")
problems = json.load(open(os.path.join(ROOT, "data", "problems.json"), encoding="utf-8"))
evaluation = sorted(p["id"] for p in problems if p["status"] == "solved")
challenge = sorted(p["id"] for p in problems if p["status"] != "solved")
unseen = sorted(random.Random(SEED).sample(evaluation, UNSEEN_COUNT))
split = {
    "method": f"random.Random({SEED}).sample(sorted(solved ids), {UNSEEN_COUNT}) (Python {sys.version.split()[0]})",
    "seed": SEED,
    "evaluation": evaluation,
    "unseen": unseen,
    "evaluation_seen": [i for i in evaluation if i not in set(unseen)],
    "challenge": challenge,
}
json.dump(split, open(out, "w", encoding="utf-8"), indent=1)
print({k: len(v) for k, v in split.items() if isinstance(v, list)})
