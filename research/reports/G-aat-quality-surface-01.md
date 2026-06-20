# G-aat-quality-surface-01 report

この report は、atom-supported quality geometry によってアーキテクチャ品質を certificate geometry として読むための研究成果を記録する。状態の正本は GitHub tracking Issue に置き、ここには SCORE 監査を通った成果だけを載せる。

## Current SCORE

- total SCORE: 850
- category scores:
  - obstruction / repair-potential / atom-supported-quality-geometry: 120
  - ridge-fold / atom-supported-quality-geometry / repair-potential / multi-axis-signature: 160
  - profile-curvature / certificate-transport / computability / ridge-fold / repair-potential: 170
  - traceability / certificate-transport / invariance / atom-supported-quality-geometry: 120
  - traceability / quality-surface / multi-axis-signature / computability / ridge-fold: 130
  - traceability / quality-surface / certificate-transport / repair-potential / ridge-fold: 150
- evidence portfolio:
  - proved-in-research: 6

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

## Cycle 3: Finite square cell profile-curvature detector

```text
candidate: Finite square cell profile-curvature detector
candidate_type: computability
evidence_stage: proved-in-research
base_score: 85
evidence_multiplier: 2.0
penalty: 0
final_score: 170
category: profile-curvature/certificate-transport/computability/ridge-fold/repair-potential
goal_delta: scalar reading と verdict が二つの profile-change path で一致しても、support antichain と repair hitting requirement が分岐する finite square を Lean-proved witness として固定し、profile-curvature frontier を前進させる。
project_value_delta: AAT Research / Lean / paper seed に、Quality Surface の二次元性を path-ordered certificate transport の coherence failure として説明する素材を追加する。tooling / website への接続は将来の説明 surface に留める。
formalization_quality: pass。`CertificateAt` による profile-typed certificate space、typed `EdgeTransport`、四辺 transport、二つの upper-right path composite、full-certificate regularity、curvature-as-coherence-failure が Lean で明示されている。
open_questions: trace-natural certificate transport、measured-zero / unmeasured / trace-missing separation、profile curvature の broader detector class、finite codebase trace example。
```

### Result

`Formal/AG/Research/QualitySurface/ProfileCurvature.lean` は、有限 profile square を定義する。
lower-left の seed certificate から upper-right へ到達する path として、law strengthening 後に cover
refinement を行う `lawThenCover` と、cover refinement 後に law strengthening を行う
`coverThenLaw` を置く。四つの edge comparison map は typed `EdgeTransport` として与えられ、
二つの path composite はどちらも `CertificateAt upperRight` に入る。

Lean 証拠は次を固定する。

- `same_scalarReading_after_paths`: 二つの path は selected scalar reading で一致する。
- `same_verdict_after_paths`: 二つの path は selected verdict で一致する。
- `supportAndRepairPathDiscrepancy_seed`: 二つの path は selected support family と repair hitting
  requirement で分岐する。
- `curvatureCell_of_supportRepair_path_discrepancy`: support または repair の path discrepancy は
  full-certificate regularity を破る。
- `same_scalar_verdict_but_curved_square`: scalar reading と verdict は flat でも、full certificate
  geometry は curvature cell になる。

この結果により、Quality Surface の二次元性は頂点値の grid ではなく、profile change に沿う certificate
transport の path coherence として固定された。scalar view が flat に見える square でも、support / repair
frontier は曲がりうる。

## Cycle 4: Trace-natural certificate transport bridge

```text
candidate: Trace-natural certificate transport bridge
candidate_type: bridge
evidence_stage: proved-in-research
base_score: 60
evidence_multiplier: 2.0
penalty: 0
final_score: 120
category: traceability/certificate-transport/invariance/atom-supported-quality-geometry
goal_delta: trace field を support transport の保存対象として Lean-backed に接続し、support transport と trace naturality failure を有限 witness で分離する。
project_value_delta: AAT Research の traceability surface と将来の ArchMap / website 説明面に使える橋を追加する。ただし toy finite witness であり、finite codebase trace example でも profile-curvature 本体でもない。
formalization_quality: pass。`TraceAvailableOn`、`TraceMissingOn`、`TransportedSupport`、`TraceNatural`、preservation theorem、finite missing-trace witness が Lean で明示されている。
open_questions: profile-typed certificate tuple 全体への trace transport 統合、finite codebase trace example、measured-zero / unmeasured / trace-missing separation、trace curvature detector。
```

### Result

`Formal/AG/Research/QualitySurface/TraceTransport.lean` は、support atom を target atom へ運ぶ
`TransportedSupport` と、partial trace field の availability / missing predicate を定義する。
`TraceNatural` は、selected source support 上で target trace field が atom transport と trace-token map に可換であることを表す。

Lean 証拠は次を固定する。

- `traceAvailableOn_transport_of_traceNatural`: source support 上で trace token が利用可能で、profile change が
  trace naturality を満たすなら、transported target support 上でも trace token が利用可能である。
- `targetTraceAvailable_of_traceNatural`: finite witness の natural target trace field は target support 上で traced である。
- `targetTraceMissing_not_traceNatural`: transported support の `bPrime` で trace token が欠ける target trace field は
  trace naturality を満たさない。
- `missingTraceOn_targetSupport`: target support には trace-missing atom が存在する。
- `support_transport_without_trace_naturality_has_missing_trace`: support transport は成立しても、trace naturality がなければ
  transported support に missing trace が残る。

この結果により、supporting atom family を運ぶことと、利用可能な trace token を運ぶことが分離された。
AAT 内部では source extraction completeness を主張せず、利用可能な trace token の保存条件だけを certificate transport の
一部として扱う。

## Cycle 5: Measured-zero / unmeasured / trace-missing separation

```text
candidate: Measured-zero / unmeasured / trace-missing separation
candidate_type: orientation
evidence_stage: proved-in-research
base_score: 65
evidence_multiplier: 2.0
penalty: 0
final_score: 130
category: traceability/quality-surface/multi-axis-signature/computability/ridge-fold
goal_delta: 同じ visible scalar `0` と selected verdict の下で、測定済みゼロ、未測定、trace 欠落が異なる certificate state と obligation を持つことを Lean-proved finite witness として固定する。
project_value_delta: cycle 2 の scalar collapse と cycle 4 の trace transport を接続し、loss-aware Quality Surface 表示で zero-looking state を drill-down すべき理由を paper seed として追加する。
formalization_quality: pass。`QualityCertificate` に actual measurement、selector、support、trace field、obligation が明示され、`SelectedTraceMissing`、三状態主 theorem、trace-missing 専用 nonfaithfulness theorem が Lean で証明されている。
open_questions: 三状態分離の一般定理化、profile-typed certificate tuple への trace status 統合、finite codebase trace example、trace curvature detector。
```

### Result

`Formal/AG/Research/QualitySurface/StateSeparation.lean` は、同じ visible scalar reading `0` と同じ
selected verdict を持つ三つの finite certificate を構成する。`visibleScalarReading` は display convention
であり、actual measurement とは別フィールドとして扱われる。

Lean 証拠は次を固定する。

- `measuredZero_has_actual_zero`: measured-zero は actual measurement として `some 0` を持つ。
- `unmeasured_has_no_actual_measurement`: unmeasured は actual measurement を持たず、selector outside である。
- `traceMissing_has_selected_support_and_missing_trace`: trace-missing は selected support と
  `TraceTransport.TraceMissingOn` による missing trace を持つ。
- `zeroLooking_certificates_state_separated`: 三状態は scalar/verdict では一致するが、actual measurement、
  selector state、selected trace-missing evidence、obligation、protected state signature で分離される。
- `scalarVerdict_not_faithful_to_selectedTraceMissing`: scalar/verdict projection は selected support と
  trace field から導かれる trace-missing state を復元できない。

この結果により、Quality Surface の zero-looking surface は、測定済みゼロ、未測定、trace 欠落を
同じ数値に潰す lossful layer であることが Lean-backed に固定された。UI / report / paper surface では、
zero value だけでなく measurement state、selector state、trace evidence、obligation を保持する必要がある。

## Cycle 6: Finite trace-locus certificate grid

```text
candidate: Finite trace-locus certificate grid
candidate_type: bridge
evidence_stage: proved-in-research
base_score: 75
evidence_multiplier: 2.0
penalty: 0
final_score: 150
category: traceability/quality-surface/certificate-transport/repair-potential/ridge-fold
goal_delta: 同じ visible scalar、selected verdict、selected support の下でも、trace locus と repair frontier が分岐することを Lean-proved finite witness として固定する。
project_value_delta: cycle 4 の trace transport と cycle 5 の trace-missing state separation を、support 内の trace locus / exact repair frontier という drill-down surface へ接続する。
formalization_quality: pass/high。finite support、trace field、missing locus、repair frontier、faithfulness 述語が明示され、主要 theorem は axiom-free / sorry-free で証明されている。
open_questions: 任意有限 support への一般化、profile-typed certificate tuple への統合、finite codebase trace example、trace curvature detector との接続。
```

### Result

`Formal/AG/Research/QualitySurface/TraceLocus.lean` は、finite support atom `{api, database, queue}` 上で、
同じ visible scalar reading、同じ selected verdict、同じ selected support を持つ二つの trace-locus certificate
を構成する。一方は selected support 全体で trace token を持ち、もう一方は database atom の trace token を欠く。

Lean 証拠は次を固定する。

- `trace_locus_partition`: selected support は available trace locus と missing trace locus に分解される。
- `trace_available_missing_disjoint`: available locus と missing locus は交わらない。
- `fullTrace_available_on_support`: full certificate は selected support 上で trace token を持つ。
- `partialTrace_missing_on_support`: partial certificate は selected support 上で missing trace を持つ。
- `partialTrace_missing_locus_exact_database`: partial certificate の missing locus は database atom ちょうどである。
- `partialTrace_repair_frontier_matches_missing_locus`: partial certificate の repair frontier は missing locus と一致する。
- `surfaceSupport_not_faithful_to_missing_locus`: scalar / verdict / selected support projection は missing locus を復元できない。
- `surfaceSupport_not_faithful_to_repair_frontier`: 同じ projection は repair frontier も復元できない。
- `same_surface_support_but_trace_locus_diff`: 同じ visible surface / support の下で trace locus と repair frontier が分岐する。

この結果により、Quality Surface の traceability surface は global な traced / missing label ではなく、
support 内の locus decomposition と repair frontier を保持すべきであることが Lean-backed に固定された。
support まで表示しても、trace locus と repair frontier はなお lossful projection の下に隠れうる。

### Next Frontier

次サイクルでは、`trace curvature detector` または `finite codebase trace example` を優先する。前者は
profile-curvature と trace-missing / trace-locus state を結びつけ、後者は Research sandbox の finite trace
locus を codebase-facing paper seed に近づける。
