# reports — 研究貢献レポート

ここには、SCORE 監査を通った研究結果を、GOAL の能力がどう増えたかという形でまとめる。GOAL 一つにつき一つのファイル(`<goal-id>.md`)とし、研究サイクルで新たな貢献が確定するたびに書き足していく(研究の流れ全体は [research/README.md](../README.md) にある)。メモである docs/note とも、正本(canonical)として保護される本文(`docs/aat/algebraic_geometric_theory/`)とも別物である。本文への取り込みや canonical への昇格は、ループの外で人間が判断する。

レポートは定理一覧ではない。各成果について、候補名、候補種別、証拠段階、final SCORE、カテゴリ、GOAL に対する delta、まだ開いている問いを書く。

## 載せてよいもの

独立した SCORE 監査が `confirm` または `reduce` と判定した成果だけを載せる。それぞれに証拠段階を明記する。

- `proved-in-research` — sorry を残さず証明できたもの。「証明した」と書いてよいのは、これだけである。
- `conjectured-sorry` — 結論部だけを sorry で保留した予想。予想として書き、証明したとは書かない。
- `finite-evidence` — 有限例、計算例、具体的 architecture family での検算を固定したもの。
- `orientation-evidence` — 反例、obstruction、予想の強化、新しい不変量など、GOAL の見方を変える証拠を固定したもの。

これら以外(`stated`、`failed`、まだ証拠固定していないもの)は載せない。

## SCORE の書き方

各成果には、SCORE 監査の内訳を残す。

```text
candidate:
candidate_type:
evidence_stage:
base_score:
evidence_multiplier:
penalty:
final_score:
category:
goal_delta:
project_value_delta:
formalization_quality:
open_questions:
```

SCORE は研究能力の増分に対して与える。証明数、ファイル数、定理数の多さには与えない。Lean proof は、価値を生む主張の信頼度を上げる証拠として扱う。

## 主張の規律

結果を書き加えるときは、独立した監査でこの規律に照らして確かめる。判定の詳細は [AAT guideline](../../docs/aat/guideline.md) と [`$research-loop`](../../.codex/skills/research-loop/SKILL.md) に従う。

- 主張は、その GOAL の claim boundary([GOALS](../GOALS.md) の「GOAL カードの型」が定める)の上に相対化して述べる。
- 測って 0 だったこと(measured_zero)と、そもそも測っていないこと(unmeasured)を区別する。
- AAT の内側に source observation、measurement tooling、ArchMap validation の完全性 claim を持ち込まない。
- 現実のコード全体、意味宇宙全体、未来の予測といった、際限のない主張は載せない。
- `Formal/AG` 本体を直接編集して得た成果を、このループの成果として扱わない。形式化は `Formal/AG/Research` 側に置く。
