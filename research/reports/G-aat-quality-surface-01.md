# G-aat-quality-surface-01 report

この report は、atom-supported quality geometry によってアーキテクチャ品質を certificate geometry として読むための研究成果を記録する。状態の正本は GitHub tracking Issue に置き、ここには SCORE 監査を通った成果だけを載せる。

## Current SCORE

- total SCORE: 120
- category scores:
  - obstruction / repair-potential / atom-supported-quality-geometry: 120
- evidence portfolio:
  - proved-in-research: 1

## Cycle 1: Minimal-support hitting theorem for local repair

```text
candidate: Minimal-support hitting theorem for local repair
candidate_type: closure
evidence_stage: proved-in-research
base_score: 60
evidence_multiplier: 2.0
penalty: 0
final_score: 120
category: obstruction/repair-potential/atom-supported-quality-geometry
goal_delta: minimal atom support family が local repair の必要条件を与えることを Lean-proved の定理として固定し、support-local repair theorem frontier を前進させる。
project_value_delta: Research sandbox 内で Quality Surface の repair-potential / obstruction 軸に paper seed 素材を追加する。traceability、certificate transport、profile curvature はこの成果ではまだ進めない。
formalization_quality: pass。nonempty antichain としての minimal support family、locality boundary、elimination semantics、finite two-support example が Lean で明示されている。
open_questions: locality を具体 calculus から導く theorem、trace field つき support certificate、profile transport / curvature と repair support の相互作用、scalar-collapse separation。
```

### Result

`Formal/AG/Research/QualitySurface/SupportHitting.lean` は、有限 atom vocabulary 上の local repair support calculus を定義する。各 obstruction certificate は nonempty antichain としての selected minimal atom support family を持つ。local repair が repair support `H` と交わらない support を残すとき、obstruction を eliminate する repair support はすべての selected minimal support を hit する。

Lean 証拠は二段になっている。

- `missed_minSupport_survives`: repair support が selected minimal support を miss すると、その support が repair 後にも残るため obstruction は eliminate されない。
- `hits_every_minSupport_of_eliminates`: repair が obstruction を eliminate するなら、repair support は selected minimal support family の全要素を hit する。

toy calculus では atom `{a,b,c}` 上に二つの selected minimal support `{a,b}` と `{c}` を固定する。repair `{a}` は `{c}` を miss するため obstruction を eliminate できず、repair `{a,c}` は両 support を hit する。この有限例が、単一の chosen support ではなく minimal support family 全体を見る必要を示す。

### Next Frontier

次サイクルでは、portfolio constraint の残りを埋めるために `scalar-collapse separation by support antichains` または `finite profile-curvature detector on a square cell` を優先する。前者は scalar reading と certificate geometry の fold を分離し、後者は certificate transport / profile curvature を直接進める。
