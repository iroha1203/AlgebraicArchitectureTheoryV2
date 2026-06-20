# GOALS — 研究目標

GOAL とは、研究で成し遂げたい能力や到達像である。証明したい定理の一覧ではない。定義と改訂は人間の判断による。`$research-loop` は、active な GOAL に対して候補を探索し、三審判、Lean 検証または証拠固定、SCORE 監査、PR レビューを通して、GOAL の能力がどれだけ増えたかを積み上げる。

ここは GOAL を状態ごとに並べた参照文書である。ただし状態の正本は GitHub の tracking Issue にあり、この文書はその写しにすぎない。active な GOAL は、サイクルの先頭で `$research-loop` が「goal 欠陥」を検査する。必要な項目は末尾の「GOAL カードの型」にまとめた。カードの中に現れる NT 番号や大定理 G1-G8 は、[docs/note の AG 版考察ノート](../docs/note/aat_ag_porting_bridges_grand_theorems.md) で定義している。

## active

(まだない。active な GOAL がないあいだは `$research-loop` を起動しても回らない。draft は、GOAL カードの型を満たしたうえで人間の判断により active へ昇格する。)

## draft(人間の確認待ち)

(なし)

## inactive

(なし)

---

## GOAL カードの型

active な GOAL は、次の項目をすべて備えていなければならない。draft はここへ昇格する前にすべて埋める。足りない場合、`$research-loop` は `goal defect` として止まる。

- `id` と `status: active`。
- `research aim`: 研究で成し遂げたい能力や到達像。
- `core tension`: 何が分かれば本当に非自明で、何が解ければ理論の景色が変わるか。
- `claim boundary`: どの語彙、law universe、coverage topology、係数、profile の上で語るか。
- `capability categories`: SCORE を配分する能力カテゴリ。例: quantity、invariance、computability、interpretation、obstruction、unification。
- `score threshold`: ひとつの研究フェーズを区切るために必要な合計 SCORE。
- `portfolio constraint`: ひとつの方向だけで点を稼いでフェーズを区切らないための条件。
- `phase boundary criteria`: 研究としてキリが良いと判定する条件。
- `reward rubric`: SCORE の採点規則。base score、evidence multiplier、penalty を分けて読めること。
- `dullness filter`: 定義展開、既存定理の即時系、名前替え、小補題量産を弾く基準。
- `frontier`: 探索してよい周辺領域。反例、obstruction、予想の強化、新しい不変量、別領域との橋を含めてよい。
- 任意の `spine`: 現時点の仮説的な道筋。固定計画ではなく、壊す、鋭くする、置き換える対象として扱う。
