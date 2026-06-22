# GOAL Card Contract

G0 で GOAL card を検査するときだけ読む。GOAL は「証明したい定理一覧」ではなく、研究で成し遂げたい能力や到達像である。

## 必須項目

active な GOAL は、候補を落とすための報酬関数を持つ。次が不足する場合は `goal defect` として止める。

- `id` と `status: active`。
- `research aim`: 研究で成し遂げたい能力や到達像。
- `core tension`: 何が分かれば非自明で、何が解ければ理論の景色が変わるか。
- `rival`: 比較対象にする既存概念、手法、tooling、理論枠組み。候補は、その rival が得意なことを把握したうえで、どの能力で勝つ、統合する、分離する、または測定可能にするのかを述べる。
- `claim boundary`: どの語彙、law universe、coverage topology、係数、profile の上で語るか。
- `capability categories`: SCORE を配分する能力カテゴリ。例: quantity、invariance、computability、interpretation、obstruction、unification。
- `threshold policy`: active SCORE threshold を tracking Issue でどう設定・読むかの方針。固定値ではなく、フェーズごとの運用パラメータとして扱う。
- `portfolio constraint`: ひとつの方向だけで点を稼いでフェーズを区切らないための条件。例: 3 カテゴリ以上で正の SCORE、最低 1 件は Lean proved。
- `phase boundary criteria`: 研究としてキリが良いと判定する条件。例: coherent な report section / paper seed になる、主要な insight が揃った、次は探索より整理が有利である。
- `reward rubric`: SCORE の採点規則。
- `dullness filter`: 定義展開、既存定理の即時系、名前替え、小補題量産を弾く基準。
- `frontier`: 探索してよい周辺領域。反例、obstruction、予想の強化、新しい不変量、別領域との橋を含めてよい。

## 任意項目

`spine` を置いてもよいが、それは固定計画ではなく現在の仮説として扱う。探索結果が spine を壊す、鋭くする、置き換えるなら、それ自体を高く評価する。

## 欠陥判定

次のいずれかに当たる場合は G1 へ進まない。

- GOAL が active ではない。
- reward rubric または dullness filter がなく、候補を落とせない。
- rival が空、または rival に対する有効差分を候補へ要求できない。
- claim boundary が曖昧で、成果がどの語彙や profile の上の主張か判定できない。
- threshold policy はあるが、tracking Issue に active threshold がなく、起動引数にも threshold がない。この場合は `goal defect` ではなく `threshold missing` とする。
- portfolio constraint または phase boundary criteria がなく、SCORE 到達後にフェーズ区切りを判定できない。
- frontier が狭すぎて定義展開しか許さない、または広すぎて GOAL への寄与を判定できない。

欠陥を見つけたら、GOAL 本文は編集せず、tracking Issue コメントまたは別 Issue に改訂案を残す。
