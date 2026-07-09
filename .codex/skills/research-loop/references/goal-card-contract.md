# GOAL Card Contract

探索型 GOAL card が満たすべき契約。`research mode: target-theorem` の GOAL は `$target-theorem-loop <goal-id>` の対象である。

## 必須項目

active な score-phase GOAL は、候補を落とすための報酬関数を持つ。次が不足する場合は `goal defect` として止める。

- `id` と `status: active`。
- `research mode` は省略または `score-phase`。`target-theorem` は対象外。
- `research aim`: 研究で成し遂げたい能力や到達像。
- `core tension`: 何が分かれば非自明で、何が解ければ理論の景色が変わるか。
- `rival`: 比較対象にする既存概念、手法、tooling、理論枠組み。
- `claim boundary`: どの語彙、law universe、coverage topology、係数、profile の上で語るか。
- `capability categories`: SCORE を配分する能力カテゴリ。
- `threshold policy`: active SCORE threshold を tracking Issue でどう設定・読むかの方針。
- `portfolio constraint`: ひとつの方向だけで点を稼いでフェーズを区切らないための条件。
- `phase boundary criteria`: 研究としてキリが良いと判定する条件。
- `reward rubric`: SCORE の採点規則。
- `dullness filter`: 定義展開、既存定理の即時系、名前替え、小補題量産を弾く基準。
- `frontier`: 探索してよい周辺領域。

## 任意項目

`spine` を置いてもよいが、固定計画ではなく現在の仮説として扱う。探索結果が spine を壊す、鋭くする、置き換えるなら、それ自体を評価する。

`genius target theorem` は通常の SCORE 探索内の希少 target seed として扱う。これは `$target-theorem-loop` の GOAL mode ではなく、SCORE phase 内の研究プログラム候補である。target を置くだけで `1000` 点を加算してはならない。

## 欠陥判定

次のいずれかに当たる場合は G1 へ進まない。

- GOAL が active ではない。
- `research mode: target-theorem` である。
- reward rubric または dullness filter がなく、候補を落とせない。
- rival が空、または rival に対する有効差分を候補へ要求できない。
- claim boundary が曖昧で、成果がどの語彙や profile の上の主張か判定できない。
- threshold policy はあるが、tracking Issue に active threshold がなく、起動引数にも threshold がない。この場合は `threshold missing` とする。
- portfolio constraint または phase boundary criteria がなく、SCORE 到達後にフェーズ区切りを判定できない。
- frontier が狭すぎて定義展開しか許さない、または広すぎて GOAL への寄与を判定できない。

欠陥を見つけたら、GOAL 本文は編集せず、tracking Issue コメントまたは別 Issue に改訂案を残す。
