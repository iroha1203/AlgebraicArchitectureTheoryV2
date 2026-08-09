# G-105-aat-structural-cover-invariance — 構造台 Čech nerve の底不変性

- 一次仕様: [`research/goals/G-105-aat-structural-cover-invariance.md`](../goals/G-105-aat-structural-cover-invariance.md)
- tracking Issue: [#3950](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3950)
- evidence PR: [#3953](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/3953)
- target theorem: Structural Cover Base Invariance Theorem
- proof state: `target-refuted`
- completion candidate: `no`

この report は固定 GOAL の証拠索引と proof obligation delta を記録する。
target statement と completion criteria の正本は GOAL カードであり、この
report はそれらを再定義しない。

## Verification scope

- 追加した 5 module は manifest focused check と parent serial targeted build を
  それぞれ通過した。
- parent の `lake build ResearchLean.AG` では 5 module すべてが replay され、
  namespace axiom audit は standard axioms only で通過した。
- 同集約 build は、G-105 差分の通過後に既存依存を 4275 / 4521 まで検証した時点で、
  machine load を抑えるというユーザー判断により中断した。したがって集約 target
  全体の final exit は未確認であり、失敗としては記録しない。

## Proof obligation state

- 完了(Cycle 1): I0 canonical support nerve generation。抽出台から chart、
  ordered pair intersection、ordered triple intersection、endpoint、face boundary を
  直接生成する `nerveOf` を固定した。`CoverNerve` の incidence field は cell subtype
  の射影であり、独立な incidence 入力を持たない。
- 完了(Cycle 1): `allSupport` / `structuralSupport` と variant 版を同じ
  constructor へ接続した。構造 phase は base doctrine と family で一度だけ分類する。
- 完了(Cycle 1): FiniteModel carrier 上の doctrine-derived fixture で、非恒等
  semantic variant、両相の非空性、抽出台変更による generated all-Atom nerve の
  実変化を同時に証明した。したがって `nerveOf` は定数構成ではない。
- 完了(Cycle 2): I1 構造 nerve の canonical equality。任意の
  `variant ∈ family.members` について、base 分類を共有した structural support の
  点ごとの同値を `Structural` から導き、生成 `CoverNerve` が等式として一致することを
  証明した。
- 完了(Cycle 3): I2 全 Atom nerve 可変性。family 内の同一非恒等 variant に
  membership、両相非空、generated all-Atom `CoverNerve` の不等式を結合した有限
  target witness を固定した。
- 完了(Cycle 4): I3a 生成係数複体と G-102 phase representability。
  variant の actual support から `(cell, source)` 座標と Čech 差分を生成し、
  chart / edge / face の G-102 `Structural` 判定が元の incident pair 条件と
  同値であることを証明した。
- 完了(Cycle 5): I3b-1 support inclusion restriction と H¹ naturality。
  actual-support inclusion から tuple / source-label preserving coordinate map を生成し、
  large-to-small restriction の cochain map 性と任意 raw cocycle の quotient H¹
  naturality を証明した。
- 完了(Cycle 6): I3b-2 ConditionE 方向仮定下の構造局在化と
  variant 間固定。base structural support から共通複体を先に生成し、
  各 member の構造 subcomplex との label-preserving 相互逆対応および両
  differential 可換性を証明した。
- 反証(Cycle 7): I4 共通 raw local datum からの H¹ 発火 witness。
  固定した source-labelled 係数生成規則では、各 source の supported
  chart が全 ordered pair / triple を生成し、その summand は cone になる。
  任意 raw cocycle の anchor primitive を構成して全 generated all-complex の
  `H1Zero` を証明したため、(v) の nonzero large class は存在しない。

## Cycle 1 — canonical support nerve generation

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/StructuralCover/NerveGeneration.lean`](../lean/ResearchLean/AG/StructuralCover/NerveGeneration.lean)
- primary declarations:
  - `SupportChart`, `SupportEdge`, `SupportFace`, `nerveOf`
  - `chartOfSupport`, `edgeOfCommonSupport`, `faceOfCommonSupport`
  - `nerveOf_congr`
  - `nerveOfAll`, `nerveOfStructural`, `nerveOfVariantAll`,
    `nerveOfVariantStructural`
  - `NerveGenerationWitness.nerve_generation_nonconstant`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - targeted module build: pass
  - namespace axiom audit: 41 declarations、standard axioms only
  - 主要 theorem の `#print axioms`: standard axioms only
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`: clean
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta

- discharged: `nerve 生成構成`。cell と incidence は `extracts` から生成される。
- remaining: 構造 nerve 不変性、全 Atom nerve 可変性、係数生成と comparison、
  係数局在と比較可能性、distinguished class の生成と naturality、診断変化発火 witness。

### Provenance / proof-use / escape audit

- certificate provenance: support subtype の witness は doctrine extraction から来る。
  proof-bearing incidence certificate や選択済み nerve は入力しない。
- proof-use: 一重・二重・三重 support がそれぞれ cell type と incidence の構成に
  実使用される。
- structure-field escape: none found。`CoverNerve` の endpoint / face field は
  tuple projection、overlap proof field は subtype property そのものである。
- route integrity: pass。有限 fixture は semantic support を nerve 構成前に固定し、
  nonidentity variant、structural pair、semantic pair、nerve variation を同一 data で示す。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-105-aat-structural-cover-invariance
target_theorem: Structural Cover Base Invariance Theorem
cycle: 1
decision: approve
result_type: proof-obligation-discharged
proof_obligation: I0 canonical support nerve generation
proof_obligation_delta: doctrine extraction alone now generates the full Cech tuple incidence and has a finite nonconstancy witness
primary_specification:
  source: research/goals/G-105-aat-structural-cover-invariance.md
  version: ffb4b146606e19a1bc7407d23638147839b2a209
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/StructuralCover/NerveGeneration.lean
    declarations:
      - nerveOf
      - nerveOf_congr
      - nerveOfAll
      - nerveOfStructural
      - nerveOfVariantAll
      - nerveOfVariantStructural
      - NerveGenerationWitness.nerve_generation_nonconstant
premise_delta:
  discharged:
    - nerve generation construction
  remaining:
    - structural nerve equality
    - all-Atom nerve variability target witness
    - generated coefficient complexes and restriction comparison
    - coefficient localization and comparability
    - distinguished class provenance and naturality
    - diagnostic firing witness
certificate_provenance:
  discharged:
    - support cells and incidence are generated from doctrine extraction
  unresolved:
    - I1-I4 provenance obligations
proof_use_audit:
  used_material_premises:
    - one-point, pairwise, and triple support construct the corresponding cells and incidence
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: I1 structural nerve equality for every declared family member
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 7 — universal generated H¹ vanishing blocker

- decision: `approve`
- result type: `blocker-fixed`
- target proof state: `target-refuted`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/StructuralCover/GeneratedH1Vanishing.lean`](../lean/ResearchLean/AG/StructuralCover/GeneratedH1Vanishing.lean)
- primary declarations:
  - `generatedSourceAnchor`, `generatedAnchorChart`, `generatedAnchorEdge`,
    `generatedAnchorFace`
  - `generatedAnchorFace_edge0`, `generatedAnchorFace_edge1`,
    `generatedAnchorFace_edge2`
  - `generatedCocyclePrimitive`, `generatedD0_cocyclePrimitive`
  - `generatedEveryCocycle_is_boundary`
  - `generatedAllComplex_h1Zero`
  - `generatedRawH1Class_eq_zero`
  - `generated_firing_witness_impossible`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - parent serial targeted module build: pass
  - namespace axiom audit: 16 declarations、standard axioms only
  - 主要 theorem / constructor の `#print axioms`: standard axioms only
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`: clean
- T3 independent audit: `approve / blocker-fixed`

### Blocking finding

source label `s` に対し、`s` が抽出する chart が一つでもあれば
anchor `a_s` をその台から選べる。任意の generated edge
`(a,b,s)` に対して `(a_s,a,b,s)` は canonical generated face である。
raw cocycle `z` の式をこの face で読むと

`z(a,b,s) = z(a_s,b,s) - z(a_s,a,s)`

となる。したがって `p_z(a,s) := z(a_s,a,s)` と置けば
`d₀ p_z = z`。これは選択した一類ではなく全 cocycle を boundary にし、
generated all-complex の H¹ 全体を零化する。

よって FiniteModel、非恒等 support inclusion、両相非空を追加しても、
固定 GOAL (v) の `[omega_large] ≠ 0` は実現できない。異なる
source を edge ごとに使うと chart coordinate も source ごとに分離し、
一つの source を共有すると全 triple face が生成されるため、有限 square
による回避も成立しない。semantic quotient H¹ への読み替えは別命題であり、
固定 GOAL の `all_large -> all_small` comparison を完了したことにはできない。

### Premise delta and audits

- discharged: 全 generated raw cocycle の canonical primitive、degree-one exactness、
  generated all-complex の `H1Zero`、canonical restriction を含む firing 不可能性。
- remaining: 固定 GOAL (v) は未証明ではなく、現生成規則の下で不可能。
- certificate provenance: anchor は source support の非空性だけに依存し、
  cochain・class・desired conclusion に依存しない。cone face は既存 support から
  生成される。
- proof-use: `d₁ z = 0` は anchor-left-right face で実使用され、三つの
  boundary equality が primitive 式の向きを固定する。
- structure-field escape: none found。exactness / contraction / H1Zero を field で受けない。
- route integrity: pass。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-105-aat-structural-cover-invariance
target_theorem: Structural Cover Base Invariance Theorem
cycle: 7
decision: approve
result_type: blocker-fixed
proof_obligation: I4 universal generated H1 vanishing route-integrity obstruction
proof_obligation_delta: the fixed nonzero-to-zero firing conclusion is formally impossible under the accepted coefficient generator
primary_specification:
  source: research/goals/G-105-aat-structural-cover-invariance.md
  version: ffb4b146606e19a1bc7407d23638147839b2a209
  status: target-refuted
lean_artifacts:
  - file: research/lean/ResearchLean/AG/StructuralCover/GeneratedH1Vanishing.lean
    declarations:
      - generatedD0_cocyclePrimitive
      - generatedEveryCocycle_is_boundary
      - generatedAllComplex_h1Zero
      - generatedRawH1Class_eq_zero
      - generated_firing_witness_impossible
premise_delta:
  discharged:
    - generated degree-one exactness
    - universal generated all-complex H1Zero
    - canonical-restriction firing impossibility
  remaining:
    - fixed I4 nonzero large class is impossible
certificate_provenance:
  discharged:
    - source support generates anchor and cone incidence before any class conclusion
  unresolved: []
proof_use_audit:
  used_material_premises:
    - generated support, raw cocycle equation, and three cone-face boundary identities
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings:
  - every source-labelled generated summand is a cone
  - every generated raw cocycle is a boundary
  - the required nonzero large H1 class cannot exist
next_obligation: revise the GOAL version or coefficient generator before any new proof loop
completion_candidate: false
target_proof_state: target-refuted
tracking_issue_closed: false
```

## Cycle 6 — common structural localization and cross-variant fixedness

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/StructuralCover/StructuralLocalization.lean`](../lean/ResearchLean/AG/StructuralCover/StructuralLocalization.lean)
- primary declarations:
  - `CommonStructuralChartCoordinate`, `CommonStructuralEdgeCoordinate`,
    `CommonStructuralFaceCoordinate`
  - `commonStructuralD0`, `commonStructuralD1`, `commonStructuralComplex`
  - `commonChartCoordinateEquiv`, `commonEdgeCoordinateEquiv`,
    `commonFaceCoordinateEquiv`
  - `structural0EquivCommon`, `structural1EquivCommon`,
    `structural2EquivCommon`
  - `structuralEquivCommon_comm0`, `structuralEquivCommon_comm1`
  - `structuralFixed0`, `structuralFixed1`, `structuralFixed2`
  - `generatedStructuralComplex_fixed`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - parent serial targeted module build: pass
  - namespace axiom audit: 51 declarations、standard axioms only
  - 主要 theorem / constructor の `#print axioms`: standard axioms only
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`: clean
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta and audits

- discharged: base structural support からの variant-independent common Q-complex、
  各 member の G-102 structural subcomplex との三次数 label-wise `LinearEquiv`、
  両 differential 可換性、共通複体を介する pairwise fixedness。
- remaining: 一つの共通 raw local datum による有限非恒等 inclusion-pair
  H¹ nonzero-to-zero 発火 witness。
- certificate provenance: common coordinate / incidence は variant 選択前の
  `structuralSupport` と `nerveOfStructural` から生成される。逆写像は
  family membership、structural support equivalence、phase iff から生成する。
- proof-use: ConditionE は各 variant の `structuralD0` / `structuralD1` の
  型付けにだけ使い、incidence は五つの boundary compatibility と可換則に
  実使用される。
- structure-field escape: none found。共通複体・equivalence・逆律・可換則は
  入力 certificate ではなく生成定義と theorem である。
- route integrity: pass。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-105-aat-structural-cover-invariance
target_theorem: Structural Cover Base Invariance Theorem
cycle: 6
decision: approve
result_type: proof-obligation-discharged
proof_obligation: I3b-2 common structural localization and cross-variant fixedness
proof_obligation_delta: every declared member structural subcomplex is canonically the one base-generated common complex
primary_specification:
  source: research/goals/G-105-aat-structural-cover-invariance.md
  version: ffb4b146606e19a1bc7407d23638147839b2a209
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/StructuralCover/StructuralLocalization.lean
    declarations:
      - commonStructuralComplex
      - commonChartCoordinateEquiv
      - commonEdgeCoordinateEquiv
      - commonFaceCoordinateEquiv
      - structural0EquivCommon
      - structural1EquivCommon
      - structural2EquivCommon
      - structuralEquivCommon_comm0
      - structuralEquivCommon_comm1
      - generatedStructuralComplex_fixed
premise_delta:
  discharged:
    - ConditionE-direction structural localization
    - cross-variant structural-complex fixedness
  remaining:
    - finite common-raw-datum diagnostic firing witness
certificate_provenance:
  discharged:
    - base structural support generates the common complex before variants
    - family membership and phase equivalence generate the coordinate inverses
  unresolved:
    - finite firing datum and class nonvanishing provenance
proof_use_audit:
  used_material_premises:
    - family membership, structural support equivalence, phase iff, ConditionE, and tuple incidence
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: I4 finite common-raw-datum nonzero-to-zero H1 firing witness
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 5 — support-inclusion restriction and arbitrary-cocycle H¹ naturality

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/StructuralCover/RestrictionComparison.lean`](../lean/ResearchLean/AG/StructuralCover/RestrictionComparison.lean)
- primary declarations:
  - `ActualSupportIncluded`
  - `includedChartMap`, `includedEdgeMap`, `includedFaceMap`
  - `includedGeneratedChartMap`, `includedGeneratedEdgeMap`,
    `includedGeneratedFaceMap`
  - `generatedRestriction0`, `generatedRestriction1`, `generatedRestriction2`
  - `generatedRestrictionHom`, `generatedRestrictedCocycle`
  - `generatedRestrictionH1_naturality`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - parent serial targeted module build: pass
  - namespace axiom audit: 21 declarations、standard axioms only
  - 主要 theorem / constructor の `#print axioms`: standard axioms only
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`: clean
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta and audits

- discharged: atomwise actual-support inclusion からの canonical cell / coordinate map、
  large-to-small restriction cochain map、任意 raw cocycle の quotient H¹ naturality。
- remaining: ConditionE 方向仮定下の structural localization と variant 間固定、
  共通 raw datum の有限発火 witness。
- certificate provenance: `ActualSupportIncluded` は `replaceSemantic.extracts` 間の
  点ごとの含意であり、各 support proof の輸送に使用される。
  comparison Hom や H¹ map を入力しない。
- proof-use: tuple と source label を保つ五つの boundary compatibility が
  `comm0` / `comm1` を生成し、別仮定 `d₁ z = 0` が restricted cocycle を作る。
- structure-field escape: none found。`ThreeCochainComplex.Hom` は入力ではなく
  三次数の restriction と両可換則を持つ生成出力である。
- route integrity: pass。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-105-aat-structural-cover-invariance
target_theorem: Structural Cover Base Invariance Theorem
cycle: 5
decision: approve
result_type: proof-obligation-discharged
proof_obligation: I3b-1 generated restriction and arbitrary-cocycle H1 naturality
proof_obligation_delta: actual-support inclusion now generates the quotient-level large-to-small comparison
primary_specification:
  source: research/goals/G-105-aat-structural-cover-invariance.md
  version: ffb4b146606e19a1bc7407d23638147839b2a209
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/StructuralCover/RestrictionComparison.lean
    declarations:
      - ActualSupportIncluded
      - includedGeneratedChartMap
      - includedGeneratedEdgeMap
      - includedGeneratedFaceMap
      - generatedRestrictionHom
      - generatedRestrictedCocycle
      - generatedRestrictionH1_naturality
premise_delta:
  discharged:
    - support-inclusion restriction cochain map
    - arbitrary-raw-cocycle quotient H1 naturality
  remaining:
    - ConditionE structural localization and cross-variant fixedness
    - finite common-datum diagnostic firing witness
certificate_provenance:
  discharged:
    - actual-support inclusion transports every tuple support and source label
    - reviewed h1Map is applied to the generated cochain Hom
  unresolved:
    - structural localization and finite witness provenance
proof_use_audit:
  used_material_premises:
    - atomwise support inclusion, tuple boundary compatibility, and raw cocycle equation
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: I3b-2 ConditionE structural localization and cross-variant fixedness
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 4 — generated coefficient complex and G-102 phase bridge

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean file:
  [`research/lean/ResearchLean/AG/StructuralCover/CoefficientGeneration.lean`](../lean/ResearchLean/AG/StructuralCover/CoefficientGeneration.lean)
- primary declarations:
  - `cellDoctrine`, `cellVariant`, `cellFamily`, `cellFamily_structural_iff`
  - `GeneratedChartLabel`, `GeneratedEdgeLabel`, `GeneratedFaceLabel`
  - `generatedIndexing`, `generatedD0`, `generatedD1`, `generatedAllComplex`
  - `generatedCoefficientComplex`
  - `generated_chart_phase_iff`, `generated_edge_phase_iff`,
    `generated_face_phase_iff`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - parent serial targeted module build: pass
  - namespace axiom audit: 23 declarations、standard axioms only
  - 主要 theorem / constructor の `#print axioms`: standard axioms only
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`: clean
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta and audits

- discharged: variant の actual extraction support からの `(cell, source)` 座標、
  label-preserving Čech 差分、G-102 係数複体、chart / edge / face の
  phase equivalence。
- remaining: ConditionE を方向仮定とした structural localization、support
  inclusion restriction、任意 cocycle の H¹ naturality、共通 raw datum の有限発火 witness。
- certificate provenance: derived Atom は元 Atom の有限 cell、derived extraction は
  actual extraction の conjunction、derived family は元 family の direct image である。
  phase-selected sentinel や opaque complex を入力しない。
- proof-use: family membership、coordinate の support proof、tuple incidence、有限性は
  すべて生成座標・差分・phase iff に使用される。
- structure-field escape: none found。`all` は `generatedAllComplex`、`d0` / `d1`
  は tuple incidence の交代式で生成される。
- route integrity: pass。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-105-aat-structural-cover-invariance
target_theorem: Structural Cover Base Invariance Theorem
cycle: 4
decision: approve
result_type: proof-obligation-discharged
proof_obligation: I3a generated coefficient complex and G-102 phase representability
proof_obligation_delta: actual support now generates all coordinates and differentials, with chart-edge-face phase equivalences
primary_specification:
  source: research/goals/G-105-aat-structural-cover-invariance.md
  version: ffb4b146606e19a1bc7407d23638147839b2a209
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/StructuralCover/CoefficientGeneration.lean
    declarations:
      - cellFamily_structural_iff
      - generatedIndexing
      - generatedAllComplex
      - generatedCoefficientComplex
      - generated_chart_phase_iff
      - generated_edge_phase_iff
      - generated_face_phase_iff
premise_delta:
  discharged:
    - generated coefficient rules
    - G-102 chart-edge-face phase representability
  remaining:
    - ConditionE structural localization
    - support-inclusion restriction cochain map
    - arbitrary-cocycle H1 naturality
    - finite common-datum diagnostic firing witness
certificate_provenance:
  discharged:
    - finite-cell conjunction doctrine and direct-image family generate the G-102 pairs
    - support labels and tuple incidence generate coordinates and differentials
  unresolved:
    - comparison and finite H1 class provenance
proof_use_audit:
  used_material_premises:
    - family membership, coordinate support, tuple incidence, and finite support
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: I3b support-inclusion restriction, structural localization, and arbitrary-cocycle H1 naturality
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 3 — all-Atom nerve variability target witness

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean declaration: `NerveGenerationWitness.allAtomNerve_variability`
- verification: focused check / targeted module build / 44-declaration namespace axiom
  audit / target `#print axioms` は pass。placeholder、hidden / bidirectional Unicode、
  privacy、`git diff --check` は clean。
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta and audits

- discharged: `全 Atom nerve 可変性`。一つの existential variant が family member、
  nonidentity、両相非空、generated `CoverNerve` 不等式を同時に満たす。
- remaining: 係数生成と comparison、係数局在と比較可能性、distinguished class の
  生成と naturality、診断変化発火 witness。
- certificate provenance: doctrine extraction と同じ `nerveOf` 生成規則に由来し、
  incidence / variability certificate を入力しない。
- proof-use / structure-field / route-integrity / cheat-route audits:
  material premise は全て使用、escape finding なし、route pass、4 cheat route は
  `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-105-aat-structural-cover-invariance
target_theorem: Structural Cover Base Invariance Theorem
cycle: 3
decision: approve
result_type: proof-obligation-discharged
proof_obligation: I2 finite all-Atom nerve variability target witness
proof_obligation_delta: one declared nonidentity variant now carries both phases and actual generated CoverNerve inequality
primary_specification:
  source: research/goals/G-105-aat-structural-cover-invariance.md
  version: ffb4b146606e19a1bc7407d23638147839b2a209
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/StructuralCover/NerveGeneration.lean
    declarations:
      - NerveGenerationWitness.allAtomNerve_variability
premise_delta:
  discharged:
    - all-Atom nerve variability finite witness
  remaining:
    - generated coefficient complexes and restriction comparison
    - coefficient localization and comparability
    - distinguished class provenance and naturality
    - diagnostic firing witness
certificate_provenance:
  discharged:
    - doctrine support generates both compared nerves for the same bound variant
  unresolved:
    - I3-I4 provenance obligations
proof_use_audit:
  used_material_premises:
    - membership, nonidentity, both phases, and nerve inequality for the same variant
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: I3 coefficient localization and inclusion-pair comparison
completion_candidate: false
tracking_issue_closed: false
```

## Cycle 2 — structural nerve canonical equality

- decision: `approve`
- result type: `proof-obligation-discharged`
- completion candidate: `no`
- Lean declarations:
  - `variantStructuralSupport_iff`
  - `nerveOfVariantStructural_eq_nerveOfStructural`
- verification:
  - manifest 登録済み単一ファイル focused check: pass
  - targeted module build: pass
  - namespace axiom audit: 43 declarations、standard axioms only
  - 対象 theorem の `#print axioms`: standard axioms only
  - placeholder、hidden / bidirectional Unicode、privacy、`git diff --check`: clean
- T3 independent audit: `approve / proof-obligation-discharged`

### Premise delta

- discharged: `構造 nerve 不変性`。family member の extraction 同値から
  support 同値を導き、`nerveOf_congr` で `CoverNerve` の等式を得た。
- remaining: 全 Atom nerve 可変性、係数生成と comparison、係数局在と比較可能性、
  distinguished class の生成と naturality、診断変化発火 witness。

### Provenance / proof-use / escape audit

- certificate provenance: invariance field はなく、`family.Structural` の定義と
  `variant ∈ family.members` だけから生成する。
- proof-use: membership は `Structural` の全称量化を対象 variant へ特殊化する
  両方向で使われる。
- structure-field escape: none found。
- route integrity: pass。variant 側で phase を再分類せず base phase を共有する。
- cheat-route audit: target-fitting construction / vacuity / one-way-as-equivalence /
  GOAL-report reinterpretation はいずれも `none-found`。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-105-aat-structural-cover-invariance
target_theorem: Structural Cover Base Invariance Theorem
cycle: 2
decision: approve
result_type: proof-obligation-discharged
proof_obligation: I1 structural nerve canonical equality
proof_obligation_delta: every declared variant has exactly the base structural generated nerve
primary_specification:
  source: research/goals/G-105-aat-structural-cover-invariance.md
  version: ffb4b146606e19a1bc7407d23638147839b2a209
  status: recorded
lean_artifacts:
  - file: research/lean/ResearchLean/AG/StructuralCover/NerveGeneration.lean
    declarations:
      - variantStructuralSupport_iff
      - nerveOfVariantStructural_eq_nerveOfStructural
premise_delta:
  discharged:
    - structural nerve invariance as CoverNerve equality
  remaining:
    - all-Atom nerve variability target witness
    - generated coefficient complexes and restriction comparison
    - coefficient localization and comparability
    - distinguished class provenance and naturality
    - diagnostic firing witness
certificate_provenance:
  discharged:
    - Structural and family membership generate the support equality
  unresolved:
    - I2-I4 provenance obligations
proof_use_audit:
  used_material_premises:
    - family membership and Structural extraction equivalence
  unused_material_premises: []
structure_field_escape_audit:
  status: none-found
  concerns: []
route_integrity_audit:
  status: pass
  concerns: []
cheat_route_audit:
  target_fitting_construction: none-found
  vacuity_or_degeneracy: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
blocking_findings: []
next_obligation: I2 finite all-Atom nerve variability target witness
completion_candidate: false
tracking_issue_closed: false
```
