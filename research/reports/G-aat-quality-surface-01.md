# G-aat-quality-surface-01 report

この report は、atom-supported quality geometry によってアーキテクチャ品質を certificate geometry として読むための研究成果を記録する。状態の正本は GitHub tracking Issue に置き、ここには SCORE 監査を通った成果だけを載せる。

## Current SCORE

- total SCORE: 280
- category scores:
  - obstruction / repair-potential / atom-supported-quality-geometry: 120
  - ridge-fold / atom-supported-quality-geometry / repair-potential / multi-axis-signature: 160
- evidence portfolio:
  - proved-in-research: 2

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

## Cycle 2: Scalar-collapse separation by support antichains

```text
candidate: Scalar-collapse separation by support antichains
candidate_type: orientation
evidence_stage: proved-in-research
base_score: 80
evidence_multiplier: 2.0
penalty: 0
final_score: 160
category: ridge-fold/atom-supported-quality-geometry/repair-potential/multi-axis-signature
goal_delta: scalar reading / verdict が一致しても support antichain と repair hitting requirement は復元できないことを Lean-proved finite witness として固定し、scalar-collapse frontier と support-local repair 後の第二必須 frontier を埋める。
project_value_delta: Lean evidence、paper seed、tooling / website explanation に使える reading-fold 分離を追加する。profile transport / curvature はこの成果ではまだ進めない。
formalization_quality: pass。`selectedViolationCount` projection、同一 scalar / verdict、異なる support family、hitting requirement 1 / 2、nonempty antichain、one / two branch shape、nonfaithfulness theorem が Lean で明示されている。
open_questions: selected scalar projection の広い class、profile transport / curvature、finite trace field、loss-aware visualization の一般 theorem。
```

### Result

`Formal/AG/Research/QualitySurface/ScalarCollapse.lean` は、二つの finite certificate を同じ scalar fiber に置く。`scalarReading` は full certificate tuple の `selectedViolationCount` への projection であり、二つの certificate は同じ scalar reading と同じ verdict を持つ。一方で、一方の selected support family は一つの branch、もう一方は二つの branch を持ち、repair hitting requirement も 1 と 2 に分かれる。

Lean 証拠は次を固定する。

- `supportFamily_antichain`: 両 certificate の selected support family は nonempty antichain として振る舞う。
- `repairRequirement_matches_supportFamily`: repair hitting requirement は selected support family の one-branch / two-branch shape に対応する。
- `same_scalar_and_verdict_but_supportRepair_diff`: scalar reading と verdict が一致しても、support family と repair hitting requirement は異なる。
- `scalarReading_not_faithful_to_supportRepair`: selected scalar reading は support / repair frontier に faithful ではない。

この結果により、Quality Surface の scalar view は lossful projection であり、背後の certificate geometry を保持しなければ repair frontier を失うことが有限例として固定された。

### Next Frontier

次サイクルでは、portfolio constraint の残りである `finite profile-curvature detector on a square cell` または `trace-natural certificate transport bridge` を優先する。前者は certificate transport / profile curvature を直接進め、後者は traceability と transport の接続を作る。
