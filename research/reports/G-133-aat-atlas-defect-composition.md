# G-133：Atlasの欠損対象と解像度比較の合成

一次仕様は active カード `d1d247eca8001b8c979cbfbdce3ba56d78bc68dd` の
[T0・A–F・W](../goals/G-133-aat-atlas-defect-composition.md)。設計4文書と
共通基準は `4cf8b67084ba6acd62b281490a2cb9b205e64f30`、既存宣言は
`aa544f1755484cb05894f7fb54631be8dd7203a7` を参照する。開始時 main は
`58c8c0abab7ad23a704d3a32020538e944ec1101`。再利用対応表のAtlas source は
参照版から変更されていない。activation PR #5262 は merge 済み。

## Cycle 1 selection

```yaml
ledger_type: target_cycle_result
goal: G-133-aat-atlas-defect-composition
cycle: 1
goal_blob_sha: 8904a7d3bf428e0307499a40be4db1ba9091c51a
base_oid: 58c8c0abab7ad23a704d3a32020538e944ec1101
tracking_issue: 5261
report_path: research/reports/G-133-aat-atlas-defect-composition.md
selection:
  proof_state_ref: 'Issue #5261: 未開始、accepted cycleなし'
  proof_dag_predecessors:
    - 'G-104 report cycle 8–13 / PR #3943; reuse-map §1'
    - 'G-107 report cycle 1・3–6・8 / PR #3994; reuse-map §1'
  milestone: 'M1 / A・W1: 実生成比較の合成と指定原始入力'
  proof_obligations:
    - 原始部分incidence比較の合成と全fieldの放電、恒等・結合則
    - reading因子、Law降下、全subsetの逆像の一致
    - 全三次数と既存H¹商で直接生成比較と合成の一致
    - W1の共通Source・真の三reading・非定数Law・全支持セル・二射
    - W1の直接生成Homの標準Law座標での恒等作用
  exit_criteria:
    - T0の全量化でAの構成と等式をLeanで確認
    - W1の全原始dataと全input fieldをLeanで生成
    - W1の直接生成Homの全次数の恒等作用を確認
    - focused check・全宣言axiom・placeholder・Unicode・privacy・import scan
  selection_reason: B・C・Fの実生成比較を同じ原始入力へ接続する最初の未完依存を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AtlasDefectComposition/ComparisonComposition.lean
    - ResearchLean/AG/AtlasDefectComposition/GeneratedComposition.lean
    - ResearchLean/AG/AtlasDefectComposition/WitnessOneInput.lean
  risks:
    - 直接比較をcochain合成として定義して構成義務を消さない
    - 部分集合・ラベルの依存型transportを全成分で確認
    - W1を行列入力で代替しない
    - face-emptyやConditionCを一般T0へ追加しない
  unchecked:
    - 全未実装義務、A–F・Wの完了判定
```

## Cycle 2時点の全targetのproof obligation

M1のLean構成は以下に対応させる。Cycle 1/M1はPR #5263で独立査読・root受理・CI成功後にmerge済み。Cycle 2/M2はPR #5264で独立査読・非中心指摘の直接対応・root受理・CI成功後にmerge済みである。C・D・E・F、W1の錐、W2・W3は未証明。
全体の completion candidate ではない。Formal移植とArchSig実装対応は未実施。
Research全体buildとローカルFormal全体buildは実行しない。

## Cycle 1 の宣言対応

受理対象は次の102宣言。各module末尾の標準公理検査は自動生成field・constructorも対象にする。
cycle scaffold は残していない。

| ファイル | 対応条項 | 構成と使用先 |
| --- | --- | --- |
| ComparisonComposition.lean | A・T0 | 原始比較の合成、全incidence、支持適合、reading因子、subset逆像、細adequacy、三段Law降下 |
| ComparisonLaws.lean | A | 全原始成分のext、既存恒等との両単位則、結合則、全Lawの恒等Hom・H¹ |
| GeneratedComposition.lean | A | 既存Law座標・Option比較から全三次数の直接生成Hom等式、既存H¹商の等式 |
| SubsetComposition.lean | A | 任意のsubsetの生成Hom合成、canonical逆像族の全複体transportとH¹等式 |
| FullSupportCoordinates.lean | W1のM1構成 | 全台のセル・発生ラベル座標と線形同型。Source証人から逆座標を生成 |
| WitnessOneInput.lean | W1の原始入力 | 八点Source、真の三reading、非定数Law、二ラベル、指定支持セルと二射、直接セル名保持 |
| WitnessOneDirect.lean | W1のM1構成 | K1の全台、同じセル・Lawラベルによる直接生成Homの次数0・1・2の恒等作用 |

### Material premise の出所と使用経路

| 入力／義務 | 分類 | 放電・使用先 |
| --- | --- | --- |
| Source、reading全射、coarse順序、全有限セルと既存incidence・chart支持 | T0由来 (`ambient-boundary`) | comparisonFactor_uniqueとcomparisonComp全fieldで使用。W1では原始表から構成 |
| laws、粗adequacy、有限Source | T0由来 (`ambient-boundary`) | K0生成座標と有限複体。Law値型の有限性は追加しない |
| 細adequacy | 放電済み (`discharge-required`) | adequate_of_coarser → WitnessOne.adequate₁/₂、一般比較への適用 |
| 合成射と支持・incidence条件 | 放電済み (`discharge-required`) | comparisonCompがchart・Option.bindから全fieldを生成。edge/face支持は既存K1から導出 |
| 直接生成Hom・H¹の合成 | 放電済み (`discharge-required`) | coordinate部分合成 → 生成pullbackの全次数 → Hom等号 → cochainComp_h1Map |
| subset等号による移送 | 放電済み (`discharge-required`) | comparisonFactor_preimage_comp → transportHom → aSubnerveComparisonHom_comp/h1Map_comp |
| 全台座標のsupport=univ | 一般APIでは方向仮定、W1では放電済み | chartSupport_univ₀/₁/₂、K1のedgeSupport_univ₀/₁/₂、空face型 → fullCoordinateEquiv |
| W1のSource・Law・支持セル・二射・真のreading差 | 放電済み (`discharge-required`) | q₀/₁/₂、not_coarser₁₀/₂₁、law_nonconstant、N₀/₁/₂、M₀₁/₁₂ |
| W1の直接Homの恒等作用 | 放電済み (`discharge-required`) | direct_chart/edge → direct_chartCoordinate/edgeCoordinate → direct_standard0/1/2 |
| B–F・W1の類と相殺・W2・W3 | 未証明 | 次の到達点へ保持 |

新しいstructure・Prop述語・supplied certificateは追加していない。既存Homの可換式は
cochainCompにおいて入力二射から生成する。直接セル比較はcochainCompに依存せず、
既存generatedComparisonHomとaSubnerveComparisonHomがそのセル射を読む。

全台の逆座標は既存LawValueLabelのSource証人を使う。元のセル名・Law・値を保持し、
非零H¹・相殺rank・錐の寄与はM2以降の未完義務として残す。

### Spine declaration list

`ComparisonComposition.lean`:

```text
AAT.AG.AtlasDefectComposition.comparisonFactor_comp
AAT.AG.AtlasDefectComposition.adequate_of_coarser
AAT.AG.AtlasDefectComposition.comparisonFactor_preimage_comp
AAT.AG.AtlasDefectComposition.lawDescend_comp_three
AAT.AG.AtlasDefectComposition.comparisonComp
AAT.AG.AtlasDefectComposition.comparisonComp_chartMap
AAT.AG.AtlasDefectComposition.comparisonComp_edgeMap
AAT.AG.AtlasDefectComposition.comparisonComp_faceMap
```

`ComparisonLaws.lean`:

```text
AAT.AG.AtlasDefectComposition.comparison_ext
AAT.AG.AtlasDefectComposition.comparisonComp_id_left
AAT.AG.AtlasDefectComposition.comparisonComp_id_right
AAT.AG.AtlasDefectComposition.comparisonComp_assoc
AAT.AG.AtlasDefectComposition.cochainId
AAT.AG.AtlasDefectComposition.cochainId_h1Map
AAT.AG.AtlasDefectComposition.identity_generatedComparisonHom
AAT.AG.AtlasDefectComposition.identity_generatedComparisonH1Map
```

`FullSupportCoordinates.lean`:

```text
AAT.AG.AtlasDefectComposition.fullCoordinateEquiv
AAT.AG.AtlasDefectComposition.fullCoordinateEquiv_symm_cell
AAT.AG.AtlasDefectComposition.fullCochainEquiv
AAT.AG.AtlasDefectComposition.fullCochainEquiv_apply
```

`GeneratedComposition.lean`:

```text
AAT.AG.AtlasDefectComposition.cochainComp
AAT.AG.AtlasDefectComposition.cochainComp_f0
AAT.AG.AtlasDefectComposition.cochainComp_f1
AAT.AG.AtlasDefectComposition.cochainComp_f2
AAT.AG.AtlasDefectComposition.cochain_ext
AAT.AG.AtlasDefectComposition.cochainComp_h1Map
AAT.AG.AtlasDefectComposition.chartCoordinateMap_comp
AAT.AG.AtlasDefectComposition.edgeCoordinateMapOption_comp
AAT.AG.AtlasDefectComposition.faceCoordinateMapOption_comp
AAT.AG.AtlasDefectComposition.generatedPullback0_comp
AAT.AG.AtlasDefectComposition.generatedPullback1_comp
AAT.AG.AtlasDefectComposition.generatedPullback2_comp
AAT.AG.AtlasDefectComposition.generatedComparisonHom_comp
AAT.AG.AtlasDefectComposition.generatedComparisonH1Map_comp
```

`SubsetComposition.lean`:

```text
AAT.AG.AtlasDefectComposition.subsetMapsTo_comp
AAT.AG.AtlasDefectComposition.targetSubsetChartMap_comp
AAT.AG.AtlasDefectComposition.targetSubsetEdgeMapOption_comp
AAT.AG.AtlasDefectComposition.targetSubsetFaceMapOption_comp
AAT.AG.AtlasDefectComposition.targetSubsetPullback0_comp
AAT.AG.AtlasDefectComposition.targetSubsetPullback1_comp
AAT.AG.AtlasDefectComposition.targetSubsetPullback2_comp
AAT.AG.AtlasDefectComposition.targetSubsetComparisonHom_comp
AAT.AG.AtlasDefectComposition.targetSubsetComparisonHom_h1Map_comp
AAT.AG.AtlasDefectComposition.transportHom
AAT.AG.AtlasDefectComposition.transportHom_rfl
AAT.AG.AtlasDefectComposition.targetSubsetComparisonHom_transport
AAT.AG.AtlasDefectComposition.aSubnerveComparisonHom_comp
AAT.AG.AtlasDefectComposition.aSubnerveComparisonHom_h1Map_comp
```

`WitnessOneDirect.lean`:

```text
AAT.AG.AtlasDefectComposition.WitnessOne.chartSupport_univ₀
AAT.AG.AtlasDefectComposition.WitnessOne.edgeSupport_univ₀
AAT.AG.AtlasDefectComposition.WitnessOne.faceSupport_univ₀
AAT.AG.AtlasDefectComposition.WitnessOne.chartSupport_univ₁
AAT.AG.AtlasDefectComposition.WitnessOne.edgeSupport_univ₁
AAT.AG.AtlasDefectComposition.WitnessOne.faceSupport_univ₁
AAT.AG.AtlasDefectComposition.WitnessOne.chartSupport_univ₂
AAT.AG.AtlasDefectComposition.WitnessOne.edgeSupport_univ₂
AAT.AG.AtlasDefectComposition.WitnessOne.faceSupport_univ₂
AAT.AG.AtlasDefectComposition.WitnessOne.coordinate0₀
AAT.AG.AtlasDefectComposition.WitnessOne.standard0₀
AAT.AG.AtlasDefectComposition.WitnessOne.coordinate1₀
AAT.AG.AtlasDefectComposition.WitnessOne.standard1₀
AAT.AG.AtlasDefectComposition.WitnessOne.coordinate2₀
AAT.AG.AtlasDefectComposition.WitnessOne.standard2₀
AAT.AG.AtlasDefectComposition.WitnessOne.coordinate0₂
AAT.AG.AtlasDefectComposition.WitnessOne.standard0₂
AAT.AG.AtlasDefectComposition.WitnessOne.coordinate1₂
AAT.AG.AtlasDefectComposition.WitnessOne.standard1₂
AAT.AG.AtlasDefectComposition.WitnessOne.coordinate2₂
AAT.AG.AtlasDefectComposition.WitnessOne.standard2₂
AAT.AG.AtlasDefectComposition.WitnessOne.direct_chartCoordinate
AAT.AG.AtlasDefectComposition.WitnessOne.direct_edgeCoordinate
AAT.AG.AtlasDefectComposition.WitnessOne.direct_standard0
AAT.AG.AtlasDefectComposition.WitnessOne.direct_standard1
AAT.AG.AtlasDefectComposition.WitnessOne.direct_standard2
```

`WitnessOneInput.lean`:

```text
AAT.AG.AtlasDefectComposition.WitnessOne.Source
AAT.AG.AtlasDefectComposition.WitnessOne.q₀
AAT.AG.AtlasDefectComposition.WitnessOne.q₁
AAT.AG.AtlasDefectComposition.WitnessOne.q₂
AAT.AG.AtlasDefectComposition.WitnessOne.coarser₀₁
AAT.AG.AtlasDefectComposition.WitnessOne.coarser₁₂
AAT.AG.AtlasDefectComposition.WitnessOne.not_coarser₁₀
AAT.AG.AtlasDefectComposition.WitnessOne.not_coarser₂₁
AAT.AG.AtlasDefectComposition.WitnessOne.laws
AAT.AG.AtlasDefectComposition.WitnessOne.adequate₀
AAT.AG.AtlasDefectComposition.WitnessOne.adequate₁
AAT.AG.AtlasDefectComposition.WitnessOne.adequate₂
AAT.AG.AtlasDefectComposition.WitnessOne.law_nonconstant
AAT.AG.AtlasDefectComposition.WitnessOne.factor₀₁
AAT.AG.AtlasDefectComposition.WitnessOne.factor₁₂
AAT.AG.AtlasDefectComposition.WitnessOne.triangle
AAT.AG.AtlasDefectComposition.WitnessOne.twoTriangles
AAT.AG.AtlasDefectComposition.WitnessOne.N₀
AAT.AG.AtlasDefectComposition.WitnessOne.N₁
AAT.AG.AtlasDefectComposition.WitnessOne.N₂
AAT.AG.AtlasDefectComposition.WitnessOne.M₀₁
AAT.AG.AtlasDefectComposition.WitnessOne.M₁₂
AAT.AG.AtlasDefectComposition.WitnessOne.M₀₂
AAT.AG.AtlasDefectComposition.WitnessOne.direct_chart
AAT.AG.AtlasDefectComposition.WitnessOne.direct_edge
AAT.AG.AtlasDefectComposition.WitnessOne.label
AAT.AG.AtlasDefectComposition.WitnessOne.labels_distinct
AAT.AG.AtlasDefectComposition.WitnessOne.labels_exhaust
```

## Cycle 1 result（独立査読前のproposal）

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: M1の全原始比較・全次数・既存H¹・W1指定入力と直接Homの標準座標恒等作用を構成
  exit_criteria_status:
    - T0の全subsetと任意の既存原始二射でAを証明
    - W1の同じSource・三reading・Law・支持セルと二射を構成
    - W1の直接生成Homの全三次数の標準Law座標での恒等作用を証明
    - 対象moduleの検証と102宣言の公理監査を実行
  split_reason: none
  completion_candidate: no
  lean_artifacts:
    - ComparisonComposition.lean
    - ComparisonLaws.lean
    - GeneratedComposition.lean
    - SubsetComposition.lean
    - FullSupportCoordinates.lean
    - WitnessOneInput.lean
    - WitnessOneDirect.lean
  evidence: [Spine declaration list, 各module末尾の標準公理検査, 全102宣言のprint axioms]
  claim_mapping:
    theorem_names: [comparisonFactor_comp, comparisonComp_assoc, generatedComparisonHom_comp, generatedComparisonH1Map_comp, aSubnerveComparisonHom_comp, aSubnerveComparisonHom_h1Map_comp, direct_standard0, direct_standard1, direct_standard2]
    source_labels: [T0, A, W1のM1構成]
    conjuncts:
      - 原始セル比較の合成と全field: comparisonComp
      - 恒等と結合: comparisonComp_id_left/right/assoc
      - reading・Law・subset同定: comparisonFactor_comp/preimage_comp, lawDescend_comp_three
      - 全Lawと全subsetの直接生成Hom・H¹: generatedComparisonHom/H1Map_comp, aSubnerveComparisonHom/h1Map_comp
      - W1の指定原始data: WitnessOneInputの全構成と真の細分化・非定数Law
      - W1の直接Homの標準Law座標での恒等作用: direct_standard0/1/2
    undischarged_assumptions: []
    acceptance_point: M1の終了条件。B–F・W1の非零相殺と錐・W2・W3は未証明
    port_status: unported
audits:
  premise_delta:
    discharged: [細adequacy, 原始合成の全field, reading・subset・Lawの同定, 直接生成Hom・H¹合成, W1全原始入力, W1直接Homの標準座標恒等作用]
    remaining: [B, C, D, E, F, W1の類・欠損・相殺・錐, W2, W3a, W3b]
  certificate_provenance:
    discharged: [comparisonCompは二射から生成, W1全幾何は原始表から生成, fullCoordinateEquivの逆はSource発生ラベルから生成]
    unresolved: []
  proof_use:
    used: [Reading全射は因子一意性とLaw降下, incidence全fieldとchart支持は原始合成, LawとadequacyはK0座標, subset因子適合は選択セルtransport]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [下記検証記録]
  blocking_findings: [独立PR査読は未実施]
  next_obligation: M2の実H¹六項列と相殺、同じW1での非零類・rank・欠損
```

### 検証記録

- 新規7fileそれぞれを `cd research/lean && lake env lean ResearchLean/AG/AtlasDefectComposition/<file>.lean` でfocused検証。各段階の修正後に再確認した。
- 必要なmoduleのtargeted buildはrootだけが実行。最終 `SubsetComposition`・`ComparisonLaws`・`WitnessOneDirect` とその依存7moduleは成功。標準公理監査の宣言数は8、8、4、14、14、26、28（上のfile順とは異なりSpine一覧のアルファベット順）。
- `.tmp/g133-cycle1-axioms.lean` で上の102宣言すべてに `#print axioms` を実行。使用公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
- 新規7file、report、module manifestにhidden/BiDi、placeholder、privacy、禁止語scanを実行。対象sourceに新規placeholderはない。本体からResearchへのimport scanはno match。
- `git diff --check` を実行。恒久設計・GOAL・本体Formal・toolingは変更していない。
- Research全体build、ローカルFormal全体build、B–F・W1の非零相殺・W2・W3の検証は未実施。

公理ログSHA-256: `7bcb4fc6470d3842d8b32173d4d7cc4fe70032dbede95927590a2319e1027caf`。

## Cycle 1 受理記録

PR #5263、固定head `5e6a391bdc0429ec8cc1f7f2228de1efa6756395`、merge
`0eaff60bc58c5b47a06500fcf082161975944483`。数学2・Lean2の独立査読はすべて
`No major findings`、rootの標準review-pr統合とacceptance-contractも合格。
監査: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5263#issuecomment-5998154046
CI全passとIssue同期: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5261#issuecomment-5998192267
受理resultはM1の `proof-obligation-discharged`。全GOALの最終監査は未実施。

## Cycle 2 selection

```yaml
ledger_type: target_cycle_result
goal: G-133-aat-atlas-defect-composition
cycle: 2
goal_blob_sha: 8904a7d3bf428e0307499a40be4db1ba9091c51a
base_oid: 0eaff60bc58c5b47a06500fcf082161975944483
tracking_issue: 5261
report_path: research/reports/G-133-aat-atlas-defect-composition.md
selection:
  proof_state_ref: 'Issue #5261 / accepted cycle 1 M1; report Cycle 1受理記録'
  proof_dag_predecessors:
    - 'M1 / PR #5263, fixed head 5e6a391bdc0429ec8cc1f7f2228de1efa6756395'
    - 'G-107 DefectSemantics / PR #3994; reuse-map'
    - 'G-132 face-empty graph H¹ API / PR #5259; reuse-map（参照候補、今回のproof-useなし）'
  milestone: 'M2 / B・W1: 実H¹の相殺と欠損'
  proof_obligations:
    - 六項列の全線形射、標準完全性、相殺像の内部商同定
    - 自然数による二欠損公式、恒等・合成・共通入力の2-out-of-3
    - 実生成H¹と代表cocycleによる後段消滅・前段像の意味
    - W1のperiod商同型、実生成二射の包含・射影作用
    - W1の指定非零類、相殺rankと各ラベル・Law全体のH¹次元・欠損
  exit_criteria:
    - Bの構成・全完全性と二欠損公式を同じ実比較へ接続
    - 同じW1原始入力からperiodと非零相殺証人を生成して指定値を証明
    - Law全体の値と二ラベルの重複度を保持
    - focused/targeted check・全対象宣言axiom・共通scan
  selection_reason: 同じ三比較のM1結果から未完の相殺と欠損へ直接進む
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AtlasDefectComposition/DefectSequence.lean
    - ResearchLean/AG/AtlasDefectComposition/GeneratedDefect.lean
    - ResearchLean/AG/AtlasDefectComposition/WitnessOnePeriods.lean
  risks:
    - 一般線形代数だけでM2を終了しない
    - 六項完全性やrankを入力certificateとして受け取らない
    - 原始生成H¹を抽象行列例へ差し替えない
    - 共通Aの量化と全q1部分集合の一様不変性を混同しない
  unchecked:
    - M2の全選定義務は実装・監査中
    - C–F/W残部とGOAL全体の最終監査は未完
```

## Cycle 2 の宣言対応

Bの一般六項完全列・二つの自然数欠損公式を、同じLaw族・共通Aのcanonical逆像族の
実H¹比較へ接続した。subset等号transportは実H¹の二欠損を保存するので、欠損公式と
2-out-of-3は移送前の直接生成Homのliteral `blockDefect` に対して述べる。
G-107 `aSubnerveDefect` はこの同じH¹写像の `blockDefect` である。
零射を含む六項列の両端も、零部分空間を零対象とする `Function.Exact` で確認した。

| file | 条項／使用先 | 生成と証拠 |
| --- | --- | --- |
| DefectSequence | B | 包含・核への前段写像・χ・二商射を入力f,gから構成。全完全性、両端、相殺像の内部商、二次元公式 |
| GeneratedDefect | B | 実H¹商の代表元判定、全Law・共通Aの実六項列と直接欠損公式、零欠損の恒等・合成・全方向2-out-of-3 |
| FullSupportBlocks | W1/M2 | 実発生ラベルfiberと名付きセルの両逆、実block微分と端点差分 |
| FullSupportGraph | W1/M2 | 指定空face型の全cycle座標、実degree-zero像の両方向同定、既存H¹の名付き辺商同型 |
| FullSupportPullback | W1/M2 | 既存部分block座標射のsome/none両分岐を名付き辺へ移す |
| WitnessOnePeriods | W1/M2 | 指定セル微分の像＝period核、period全射、既存実H¹商のperiod同型と次元1,2,1 |
| WitnessOneComparison | W1/M2 | 原始射の実生成引き戻し→既存H¹→包含・射影・直接period保持 |
| WitnessOneCancellation | W1/M2 | 実欠損(0,1),(1,0),(0,0)、指定辺34の実cocycle/class・後段消滅・χ非零・rank1、実余核＝ℚ²/(ℚ×0)と(0,1)類 |
| LawH1Family | B/W1/M2 | G-104の既存直和同定と生成写像の自然性の全ラベル成分API |
| WitnessOneFullLaw | W1/M2 | 二実ラベルの保持、全Law実H¹次元2,4,2、生成包含・射影、欠損(0,2),(2,0),(0,0)、χrank2 |

### Material premise / provenance / proof-use

| 行 | 分類 | 出所・放電・使用経路 |
| --- | --- | --- |
| K線形f,gと有限次元U,V,W | 一般補題の入力 | 各線形写像の核・像・literal商から射を生成。欠損公式で標準rank-nullityを使用。完全性は有限性を必要としない |
| 実H¹二射・有限次元 | T0と既存構成から放電 | 原始M、Law・adequacy、subset逆像→既存生成Hom→既存h1Map。有限性はThreeCochainComplexの既存instance |
| gf＝直接H¹ | 放電済み | M1のgeneratedComparisonH1Map_comp、aSubnerveComparisonHom_h1Map_comp。subset移送の欠損保存をcases equalityで確認 |
| 六項完全性・χrank・内部商 | 放電済み | DefectSequenceの代表元証明と標準Function.Exact、quotKerEquivRange。certificate fieldとして受け取らない |
| 相殺の代表元の意味 | 放電済み | h1Map_mk、商の零/等号・mkQ全射から実primitiveと粗cocycleの存在へ両方向。入力zは実ker d1 |
| 全台 | 一般補助APIでは方向仮定、W1では放電済み | M1の全chart/K1 edge支持定理を渡す。一般Bへ追加しない |
| face空型 | W1の固定入力 | Empty.faceから全edge cochainが実cycle。一般Bの量化を縮めない |
| period核＝実微分像・period全射 | 放電済み | triangle/twoTrianglesの実incidenceから差分を生成。明示primitiveと辺12/34のcochainを構成して両方向と全射を証明 |
| H¹空間と比較の行列表示 | 出力として放電 | 元のLaw block座標・実微分・実部分pullback・商を通したperiod同型と評価。行列を原始入力に加えない |
| 指定辺34の非零χ | 放電済み | middleCycle→既存middleClass→middle_killed→middleKernel。χ零なら前段像に入り、第二periodが0＝1となる矛盾 |
| 二発生ラベルと全Law値 | 放電済み | M1 label/source証人・labels_exhaust→labelEquivBool、既存G-104直和・生成比較自然性→全ラベルperiod族。各成分を保持 |
| C–F、W1の錐・追加項、W2/W3 | 未完義務 | M3–M6に保持。今回のcompletion candidateはno |

新しいcertificate構造やProp述語は追加していない。完全性・rank・primitive・H¹同型を
入力fieldへ移さず、入力二射から構成する。一般補助APIのfull supportとface空性はW1だけに
使う。相殺rank1/2は同じ実比較のkernel formulaへ実欠損を代入して導き、非零類は
指定cochainから別途固定している。一般線形代数だけでM2を閉じていない。

G-132のface-emptyな可視graph APIも再利用候補として読んだ。今回の全台W1では、M1の
セル×発生ラベル同定をそのfiberへ制限し、G-104の既存block微分・実H¹商に直接接続する
経路を採用した。G-132の整数修復・ReflectionConditionや実貼り合わせを仮定せず、
G-132の定理を今回の新規相殺成果として数えていない。これはproof method/API選択であり、
固定target・指定入力・終了条件を変更していない。

### Cycle 2 spine declaration list

受理spineは以下の119の明示宣言。各module末尾の標準公理監査は、同moduleで生成される
simp用補助宣言を含む全非internal宣言と、それらの依存を検査する。cycle scaffoldは残さない。

`DefectSequence.lean`:

```text
AAT.AG.AtlasDefectComposition.DefectSequence.first
AAT.AG.AtlasDefectComposition.DefectSequence.second
AAT.AG.AtlasDefectComposition.DefectSequence.cancellation
AAT.AG.AtlasDefectComposition.DefectSequence.cancellation_apply
AAT.AG.AtlasDefectComposition.DefectSequence.cancellation_eq_zero_iff
AAT.AG.AtlasDefectComposition.DefectSequence.fourth
AAT.AG.AtlasDefectComposition.DefectSequence.fifth
AAT.AG.AtlasDefectComposition.DefectSequence.first_injective
AAT.AG.AtlasDefectComposition.DefectSequence.exact_first_second
AAT.AG.AtlasDefectComposition.DefectSequence.exact_second_cancellation
AAT.AG.AtlasDefectComposition.DefectSequence.exact_cancellation_fourth
AAT.AG.AtlasDefectComposition.DefectSequence.exact_fourth_fifth
AAT.AG.AtlasDefectComposition.DefectSequence.fifth_surjective
AAT.AG.AtlasDefectComposition.DefectSequence.exact_zero_first
AAT.AG.AtlasDefectComposition.DefectSequence.exact_fifth_zero
AAT.AG.AtlasDefectComposition.DefectSequence.sixTerm_exact
AAT.AG.AtlasDefectComposition.DefectSequence.cancellation_ker
AAT.AG.AtlasDefectComposition.DefectSequence.cancellationQuotientEquiv
AAT.AG.AtlasDefectComposition.DefectSequence.kernel_dimension
AAT.AG.AtlasDefectComposition.DefectSequence.cokernel_dimension
```

`FullSupportBlocks.lean`:

```text
AAT.AG.AtlasDefectComposition.fullBlockCoordinateEquiv
AAT.AG.AtlasDefectComposition.fullBlockCoordinateEquiv_symm_cell
AAT.AG.AtlasDefectComposition.fullBlockCochainEquiv
AAT.AG.AtlasDefectComposition.fullBlockCochainEquiv_apply
AAT.AG.AtlasDefectComposition.fullBlock_d0
```

`FullSupportGraph.lean`:

```text
AAT.AG.AtlasDefectComposition.graphDifference
AAT.AG.AtlasDefectComposition.graphDifference_apply
AAT.AG.AtlasDefectComposition.fullBlockGraphCyclesEquiv
AAT.AG.AtlasDefectComposition.fullBlockGraph_image
AAT.AG.AtlasDefectComposition.fullBlockGraphH1Equiv
AAT.AG.AtlasDefectComposition.fullBlockGraphH1Equiv_mk
```

`FullSupportPullback.lean`:

```text
AAT.AG.AtlasDefectComposition.fullBlock_pullback1_some
AAT.AG.AtlasDefectComposition.fullBlock_pullback1_none
```

`GeneratedDefect.lean`:

```text
AAT.AG.AtlasDefectComposition.h1Map_mk_eq_zero_iff
AAT.AG.AtlasDefectComposition.h1_mk_mem_range_iff
AAT.AG.AtlasDefectComposition.cancellation_mk_eq_zero_iff
AAT.AG.AtlasDefectComposition.zeroDefect_comp
AAT.AG.AtlasDefectComposition.zeroDefect_second
AAT.AG.AtlasDefectComposition.zeroDefect_first
AAT.AG.AtlasDefectComposition.zeroDefect_id
AAT.AG.AtlasDefectComposition.generated_sixTerm_exact
AAT.AG.AtlasDefectComposition.generated_kernel_dimension
AAT.AG.AtlasDefectComposition.generated_cokernel_dimension
AAT.AG.AtlasDefectComposition.generated_zeroDefect_twoOfThree
AAT.AG.AtlasDefectComposition.transportHom_defect
AAT.AG.AtlasDefectComposition.aSubnerve_sixTerm_exact
AAT.AG.AtlasDefectComposition.aSubnerve_kernel_dimension
AAT.AG.AtlasDefectComposition.aSubnerve_cokernel_dimension
AAT.AG.AtlasDefectComposition.aSubnerve_zeroDefect_twoOfThree
```

`LawH1Family.lean`:

```text
AAT.AG.AtlasDefectComposition.lawH1FamilyEquiv
AAT.AG.AtlasDefectComposition.lawH1FamilyMap_component
```

`WitnessOneCancellation.lean`:

```text
AAT.AG.AtlasDefectComposition.WitnessOne.forward
AAT.AG.AtlasDefectComposition.WitnessOne.backward
AAT.AG.AtlasDefectComposition.WitnessOne.direct
AAT.AG.AtlasDefectComposition.WitnessOne.forward_injective
AAT.AG.AtlasDefectComposition.WitnessOne.backward_surjective
AAT.AG.AtlasDefectComposition.WitnessOne.direct_bijective
AAT.AG.AtlasDefectComposition.WitnessOne.direct_eq_comp
AAT.AG.AtlasDefectComposition.WitnessOne.forward_defect
AAT.AG.AtlasDefectComposition.WitnessOne.backward_defect
AAT.AG.AtlasDefectComposition.WitnessOne.direct_defect
AAT.AG.AtlasDefectComposition.WitnessOne.middleCycle
AAT.AG.AtlasDefectComposition.WitnessOne.middleClass
AAT.AG.AtlasDefectComposition.WitnessOne.middle_periods
AAT.AG.AtlasDefectComposition.WitnessOne.middle_killed
AAT.AG.AtlasDefectComposition.WitnessOne.middleKernel
AAT.AG.AtlasDefectComposition.WitnessOne.middle_nonzero
AAT.AG.AtlasDefectComposition.WitnessOne.cancellation_nonzero
AAT.AG.AtlasDefectComposition.WitnessOne.cancellation_rank
AAT.AG.AtlasDefectComposition.WitnessOne.forward_range_period
AAT.AG.AtlasDefectComposition.WitnessOne.forwardCokernelEquiv
AAT.AG.AtlasDefectComposition.WitnessOne.cancellation_period_quotient
AAT.AG.AtlasDefectComposition.WitnessOne.middle_cancellation_period
```

`WitnessOneComparison.lean`:

```text
AAT.AG.AtlasDefectComposition.WitnessOne.forward_standard1
AAT.AG.AtlasDefectComposition.WitnessOne.backward_standard1
AAT.AG.AtlasDefectComposition.WitnessOne.direct_block_standard1
AAT.AG.AtlasDefectComposition.WitnessOne.forward_period
AAT.AG.AtlasDefectComposition.WitnessOne.backward_period
AAT.AG.AtlasDefectComposition.WitnessOne.direct_block_period
```

`WitnessOneFullLaw.lean`:

```text
AAT.AG.AtlasDefectComposition.WitnessOne.labelEquivBool
AAT.AG.AtlasDefectComposition.WitnessOne.label_card
AAT.AG.AtlasDefectComposition.WitnessOne.fullPeriod₀
AAT.AG.AtlasDefectComposition.WitnessOne.fullPeriods₁
AAT.AG.AtlasDefectComposition.WitnessOne.fullPeriod₂
AAT.AG.AtlasDefectComposition.WitnessOne.fullForward
AAT.AG.AtlasDefectComposition.WitnessOne.fullBackward
AAT.AG.AtlasDefectComposition.WitnessOne.fullDirect
AAT.AG.AtlasDefectComposition.WitnessOne.full_forward_periods
AAT.AG.AtlasDefectComposition.WitnessOne.full_backward_periods
AAT.AG.AtlasDefectComposition.WitnessOne.full_direct_period
AAT.AG.AtlasDefectComposition.WitnessOne.full_h1_dimension₀
AAT.AG.AtlasDefectComposition.WitnessOne.full_h1_dimension₁
AAT.AG.AtlasDefectComposition.WitnessOne.full_h1_dimension₂
AAT.AG.AtlasDefectComposition.WitnessOne.full_forward_injective
AAT.AG.AtlasDefectComposition.WitnessOne.full_backward_surjective
AAT.AG.AtlasDefectComposition.WitnessOne.full_direct_bijective
AAT.AG.AtlasDefectComposition.WitnessOne.full_forward_defect
AAT.AG.AtlasDefectComposition.WitnessOne.full_backward_defect
AAT.AG.AtlasDefectComposition.WitnessOne.full_direct_defect
AAT.AG.AtlasDefectComposition.WitnessOne.full_cancellation_rank
```

`WitnessOnePeriods.lean`:

```text
AAT.AG.AtlasDefectComposition.WitnessOne.trianglePeriod
AAT.AG.AtlasDefectComposition.WitnessOne.twoTrianglePeriods
AAT.AG.AtlasDefectComposition.WitnessOne.trianglePeriod_kernel
AAT.AG.AtlasDefectComposition.WitnessOne.twoTrianglePeriods_kernel
AAT.AG.AtlasDefectComposition.WitnessOne.trianglePeriod_surjective
AAT.AG.AtlasDefectComposition.WitnessOne.twoTrianglePeriods_surjective
AAT.AG.AtlasDefectComposition.WitnessOne.triangleQuotientPeriod
AAT.AG.AtlasDefectComposition.WitnessOne.twoTriangleQuotientPeriods
AAT.AG.AtlasDefectComposition.WitnessOne.triangleQuotientPeriod_mk
AAT.AG.AtlasDefectComposition.WitnessOne.twoTriangleQuotientPeriods_mk
AAT.AG.AtlasDefectComposition.WitnessOne.h1Period₀
AAT.AG.AtlasDefectComposition.WitnessOne.h1Periods₁
AAT.AG.AtlasDefectComposition.WitnessOne.h1Period₂
AAT.AG.AtlasDefectComposition.WitnessOne.h1Period₀_mk
AAT.AG.AtlasDefectComposition.WitnessOne.h1Periods₁_mk
AAT.AG.AtlasDefectComposition.WitnessOne.h1Period₂_mk
AAT.AG.AtlasDefectComposition.WitnessOne.h1_dimension₀
AAT.AG.AtlasDefectComposition.WitnessOne.h1_dimension₁
AAT.AG.AtlasDefectComposition.WitnessOne.h1_dimension₂
```
## Cycle 2 result（独立査読前のproposal）

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Bの全六項射・完全性・χ内部商・二公式・実代表元の意味・共通入力2-out-of-3とW1指定類/実欠損/全Law値を閉じた
  exit_criteria_status:
    - 一般線形構成を実生成H¹二射へ適用しM1の直接比較等号へ接続
    - 同じW1の指定Source/Law/台/セル/二射からperiod同型と辺34の非零相殺証人を生成
    - 各ラベルrank1と全Law rank2・指定H¹次元と欠損を確認
    - 対象fileのfocused/targeted検証と全明示宣言の公理監査・共通scanを実施
  split_reason: none
  completion_candidate: no
  lean_artifacts: [Cycle 2 spine declaration listの119宣言]
  evidence: [DefectSequence/GeneratedDefect/WitnessOnePeriods/WitnessOneComparison/WitnessOneCancellation/WitnessOneFullLaw]
  claim_mapping:
    theorem_names: [上のspineと条項対応]
    source_labels: [B, W1/M2, T0]
    conjuncts: [上のfile表とmaterial premise表]
    undischarged_assumptions: [C–F/W1の錐と追加項/W2/W3は今回の到達点外で未完]
    acceptance_point: M2の全終了条件を同じ原始入力と実生成比較で満たしたproposal
    port_status: unported
audits:
  premise_delta:
    discharged: [六項列/χ商/二公式/代表元/2-out-of-3/W1period・非零類・rank・欠損/全Law]
    remaining: [M3–M6と全GOAL完了監査]
  certificate_provenance:
    discharged: [全写像と同型と指定類が入力二射・既存Law座標・実微分から生成]
    unresolved: []
  proof_use:
    used: [固定入力/既存H¹商/部分射/全台/空face/二実ラベル/G-104分解/G-107欠損]
    unused: [G-132graphAPIは読取参照候補のみ、material premiseとして追加していない]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [Cycle 2検証記録]
  blocking_findings: [独立PR査読は未実施]
  next_obligation: M3の標準零延長/既存H¹/全次数錐/W3とW1錐の追加項
```

### Cycle 2 検証記録

新規10fileの各実装段階でfocused checkを行い、必要な依存だけrootがtargeted buildした。
最終 `lake build ResearchLean.AG.AtlasDefectComposition.WitnessOneFullLaw` は対象新規10moduleと
その必要依存のcheckとして成功した。Research全体build・aggregate elaboration・local Formal
全体buildは実行していない。対象module末尾監査は標準公理のみ。

`.tmp/g133-cycle2-axioms.lean` は上の119明示宣言へ `#print axioms` を実行する。
公理はpropext・Classical.choice・Quot.soundのみ。対象source/report/manifestのplaceholder、
hidden/BiDi、privacy、語彙scanとFormal→Research import scan、git diff --checkはclean。
恒久設計・GOAL本文・本体Formal・toolingの変更はない。Formal移植とArchSig実装は未実施。
C–F、W1の錐と追加項、W2/W3、全GOAL最終監査は未完。

Cycle 2公理ログSHA-256: `77514a8cd09bc8febf807385c181ac842ab558182f667e7b0643404d282dbafd`。119宣言のsource/scratch/log集合を突合し、欠落・余剰なし。


### Cycle 2 初回査読への非中心修正

固定head `56146528815154604b164ccb41431592d22d9922` の4 laneはMinor issues、中心findingなし。
統合記録は [PR #5264初回監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5264#issuecomment-5999038869)。
指摘された7補題のdocstring、graphDifference_apply、cancellation_apply/cancellation_eq_zero_iff、
実欠損の公開次元公式・rank-nullityを使う証明へ修正した。statement・定義値・既存宣言・
入力契約・台帳statusは変更しない。追加API3件を含む119宣言へ公理監査を更新した。
直接対応の資格と解消はfresh単一agentの確認対象である。

初回の直接対応確認はF1/F3/F4の解消と資格内を確認したが、F2の同じperiod核証明の
逆方向に残るchange評価（旧行40）を未解消とした。その一箇所もgraphDifference_apply
経由へ直し、再度fresh単一agentの直接対応確認へ渡す。中心findingの追加はない。


## Cycle 2 受理記録

[PR #5264最終受理監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5264#issuecomment-5999396250)が
固定head `34b0a6eafba940c26922430bab79d9438ff73fa7` をapprove / proof-obligation-discharged（M2）と判定した。
初回4laneは中心findingなし、非中心Minor issues。別fresh単一agentの直接対応確認でF1–F4を
すべて実体解消・資格内と確認。merge `a51385022f5dbccfca96166abf435b89f274c0c6`、
CI Lean37346099851・Tool37346099881・Workers da1dcb60-2001-460c-a42f-ee8ac5aa0b4b全pass。
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5261#issuecomment-5999424199)。
GOALはactive、全completion candidateではない。

## Cycle 3 selection

```yaml
ledger_type: target_cycle_result
goal: G-133-aat-atlas-defect-composition
cycle: 3
goal_blob_sha: 8904a7d3bf428e0307499a40be4db1ba9091c51a
base_oid: a51385022f5dbccfca96166abf435b89f274c0c6
tracking_issue: 5261
report_path: research/reports/G-133-aat-atlas-defect-composition.md
selection:
  proof_state_ref: 'M1/M2 accepted: PR #5263/#5264; Issue #5261同期'
  proof_dag_predecessors: [M1の実Hom合成, M2の実H¹/W1 period, 固定mathlib mappingCone/homology API]
  milestone: 'M3 / C・W1錐・W3: 標準錐と次数別寄与'
  proof_obligations:
    - 三項有理複体のℤ次数への零延長、全Hom、恒等/合成と既存H¹の自然同型
    - 実生成Homの標準mappingConeとカード順序(y,x)の明示成分同定/微分
    - 全整数mでの余核/錐H^m/次核の短完全列、端点、次数0/1と二欠損の接続
    - 指定W3a/W3bの原始reading・Law・支持セルと比較、追加寄与と全指定次元
    - 同じW1各ラベル/全Lawの錐次元と追加項零
  exit_criteria:
    - Cの全量化・全次数を既存H¹および標準mathlib錐へ接続
    - W3a/W3bの実原始入力と全評価値をLeanで生成
    - 同じW1の錐値と追加寄与零を実入力から証明
    - focused/targeted、spine全axiom、placeholder/Unicode/privacy/import方向scan成功
  selection_reason: Dの対象分解とFのtriangle/filtrationが依存する標準複体への接続を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [ZeroExtension.lean, ConeCoordinates.lean, ConeExactSequence.lean, WitnessThreeInput.lean]
  risks:
    - 独自錐recordを標準mappingConeへの同型なしで閉じない
    - source/target順序と負号、次数-1を保持
    - H0余核/H2核の追加寄与を一般入力へ零と仮定しない
    - W3の行列を入力fieldへ供給せず原始セル微分から評価
  unchecked: [Cの未実装義務, D/E/F, W2, 全GOAL完了監査]
```


## Cycle 3 checkpoint proposal

標準錐の一般構成、自然短完全列、既存H¹/端のH⁰/H²との同定、および
W1全発生ラベルとW3の実block具体例を同じ原始入力から閉じた。32 Lean file・303明示宣言に
またがる再利用可能な複体/錐APIが独立に成立したため、ここで分割する。
元のM3終了条件は維持する。W1全Lawの錐・追加項とW3の唯一ラベルから全Lawへの
対象同定は、Law別の全成分/標準錐分解を構成する次cycleの残義務とする。
Cの証拠と各ラベルの数値は全GOAL完了判定を含まない。

```yaml
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta:
    - Cの零延長・全Hom・恒等/合成・既存H¹自然同型を構成
    - 標準mappingConeへの両方向成分同定と全mの指定順序/符号を証明
    - 標準長完全列から全mの実余核/錐homology/次核の自然短完全列と端同型を構成
    - W3a/W3bの原始入力を生成し、実blockのJ、追加項、錐全四次数を評価
    - W3bの実錐空間次元4,9,7,1と実微分rank4,5,1を証明
    - W1全ラベルの実錐次数0/1と追加項零を証明
    - 指定錐射影/包含の同型条件と追加項零性の必要十分条件を両方向で証明
  exit_criteria_status:
    - Cの全次数/標準mathlib錐/既存H¹との接続は閉じた
    - W3の実block指定値は閉じた; 唯一ラベルと全Lawの対象同定は未完
    - W1の全発生ラベルの実錐/追加項は閉じた; 全Lawの錐は未完
    - 独立PR査読は次段階; 全GOAL最終査読は未実施
  split_reason: 再利用可能な一般複体/錐APIと実block例が成立し、32fileの検査責務と次の全Law対象分解を一度の監査に混ぜず確認するため
  completion_candidate: no
  lean_artifacts: [以下Cycle 3 spine]
  evidence: [全303明示宣言のLean証明と実入力構成]
  claim_mapping:
    theorem_names: [cone_short_exact, cone_homology_dimension, oldH1Equiv_natural, actualA_cone_homology_dimensions, actualB_cone_homology_dimensions, actual_extra_terms_zero]
    source_labels: [C, W1の各ラベル錐, W3の実block]
    conjuncts:
      - C零延長/標準H1自然性: ZeroExtension・EndpointHomology・EndpointNaturality
      - C全m成分/符号: ConeCoordinates
      - C全m短完全列/自然性/次元/端: ConeHomologySequence・ConeExactSequence・ConeNaturality・ConeEndDegrees
      - C条件付き同型/両方向/追加項零性: ShortExactFiveConditions・ConeConditional
      - W3原始入力/指定原始微分rank: WitnessThreeInput・WitnessThreeRanks
      - W3実比較/実錐/追加項: NamedComparison・NamedHomology・WitnessThreeNamed・WitnessThreeActual
      - W1全発生ラベル実錐/追加項: WitnessOneEndpoints・WitnessOneCones
    undischarged_assumptions: []
    acceptance_point: 元の終了条件を縮めず、全Law対象同定を未完として残すcheckpoint
    port_status: unported
```

### Cycle 3 premise と証明経路

有限Source・任意有限supported nerve・有理係数・既存三項複体の微分平方零は
T0に明示された入力幾何と生成元である。一般線形補助の可換正方形・exactnessは方向仮定であり、
実入力への適用では generatedComparisonHom、全成分同型、標準長完全列で生成している。
有限値型・Condition C・comparisonの単射/全射・face空性を一般Cへ追加しない。
Fintype Sourceから実発生LawValueLabelの有限性を使い、任意のambient valueを列挙しない。

既存G-107 ThreeCochainComplex.CochainEquivを用い、別の同値recordを設けない。
ZeroExtensionは標準CochainComplex.of/ModuleCat short homologyへ接続する。
ConeCoordinatesは標準mappingConeのprojection/injectionで両逆と微分を証明する。
ConeHomologySequenceは標準distinguished triangleの長完全列を使い、exactnessをfieldで供給しない。
ShortExactFiveは実kernel/range/quotientからinjection/projectionを構成する。
全台とface空性はW1および指定全台W3の座標計算の方向仮定だけで、T0一般定理へ伝播しない。

W3bの終端H²は指定三項複体の実商である。原始セルの面像を三つの自由面値で構成し、
指定rank3とfine rank1を得た。錐微分rankは実homology次元加法式から得る。
W1の次数0定数核は各chartの原始辺差分で証明し、実chart比較で定数を保つ。
新述語extraTermsZeroは二つの実次元零性の積であり、W1で成立しW3aで不成立を証明する。

### Cycle 3 spine

以下303明示宣言を修正後受理候補とする。新規31fileと既存FullSupportPullbackの新規3宣言を
列挙し、既存宣言は前cycleの受理依存として扱う。自動生成projection/simp定理は各module末尾の
標準公理監査にも含まれる。scratch/開発用試行は受理spineへ含めない。

- `research/lean/ResearchLean/AG/AtlasDefectComposition/CochainEquivalence.lean`

```text
AAT.AG.AtlasDefectComposition.cochainEquiv_hom_inv
AAT.AG.AtlasDefectComposition.cochainEquiv_inv_hom
AAT.AG.AtlasDefectComposition.cochainEquivZeroExtensionIso
AAT.AG.AtlasDefectComposition.cochainEquiv_h1_standard
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ComparisonHomology.lean`

```text
AAT.AG.AtlasDefectComposition.standardH1KernelEquiv
AAT.AG.AtlasDefectComposition.standardH1CokernelEquiv
AAT.AG.AtlasDefectComposition.standardH0_bijective_iff
AAT.AG.AtlasDefectComposition.standardH2_bijective_iff
AAT.AG.AtlasDefectComposition.standardH1_defect
AAT.AG.AtlasDefectComposition.blockDefect_kernel_dimension
AAT.AG.AtlasDefectComposition.blockDefect_cokernel_dimension
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ComplexIsoRanks.lean`

```text
AAT.AG.AtlasDefectComposition.complexIso_d_rank
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ConeConditional.lean`

```text
AAT.AG.AtlasDefectComposition.coneKernelProjection_bijective_iff
AAT.AG.AtlasDefectComposition.coneCokernelInclusion_bijective_iff
AAT.AG.AtlasDefectComposition.coneKernelProjectionEquiv
AAT.AG.AtlasDefectComposition.coneCokernelInclusionEquiv
AAT.AG.AtlasDefectComposition.coneKernelProjectionEquiv_apply
AAT.AG.AtlasDefectComposition.coneCokernelInclusionEquiv_apply
AAT.AG.AtlasDefectComposition.cokernel_zero_iff_surjective
AAT.AG.AtlasDefectComposition.kernel_zero_iff_injective
AAT.AG.AtlasDefectComposition.comparison_H0_cokernel_zero_iff
AAT.AG.AtlasDefectComposition.comparison_H2_kernel_zero_iff
AAT.AG.AtlasDefectComposition.comparisonConeH0KernelEquiv
AAT.AG.AtlasDefectComposition.comparisonConeH1CokernelEquiv
AAT.AG.AtlasDefectComposition.comparisonConeH0KernelEquiv_apply
AAT.AG.AtlasDefectComposition.comparisonConeH1CokernelEquiv_apply
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ConeCoordinates.lean`

```text
AAT.AG.AtlasDefectComposition.coneCoordinateEquiv
AAT.AG.AtlasDefectComposition.coneCoordinateEquiv_snd
AAT.AG.AtlasDefectComposition.coneCoordinateEquiv_fst
AAT.AG.AtlasDefectComposition.coneCoordinateEquiv_symm_snd
AAT.AG.AtlasDefectComposition.coneCoordinateEquiv_symm_fst
AAT.AG.AtlasDefectComposition.coneCoordinateEquiv_d
AAT.AG.AtlasDefectComposition.comparisonCone
AAT.AG.AtlasDefectComposition.coneDegreeFiniteDimensional
AAT.AG.AtlasDefectComposition.comparisonCone_isZero
AAT.AG.AtlasDefectComposition.comparisonConeMinusOneEquiv
AAT.AG.AtlasDefectComposition.comparisonConeZeroEquiv
AAT.AG.AtlasDefectComposition.comparisonConeOneEquiv
AAT.AG.AtlasDefectComposition.comparisonConeTwoEquiv
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ConeDimensionCalculus.lean`

```text
AAT.AG.AtlasDefectComposition.shortComplex_boundary_rank
AAT.AG.AtlasDefectComposition.shortComplex_homology_dimension
AAT.AG.AtlasDefectComposition.complex_homology_dimension
AAT.AG.AtlasDefectComposition.complex_homology_isZero
AAT.AG.AtlasDefectComposition.comparisonCone_homology_isZero
AAT.AG.AtlasDefectComposition.comparisonCone_dimension_defect
AAT.AG.AtlasDefectComposition.comparisonCone_dimension_minus_one
AAT.AG.AtlasDefectComposition.comparisonCone_dimension_two
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ConeEndDegrees.lean`

```text
AAT.AG.AtlasDefectComposition.comparisonConeHMinusOneEquiv
AAT.AG.AtlasDefectComposition.comparisonConeHTwoEquiv
AAT.AG.AtlasDefectComposition.comparisonCone_dimension_zero
AAT.AG.AtlasDefectComposition.comparisonCone_dimension_one
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ConeEquivalence.lean`

```text
AAT.AG.AtlasDefectComposition.coneIso_inverse_square
AAT.AG.AtlasDefectComposition.coneMapIso
AAT.AG.AtlasDefectComposition.coneHomologyEquiv
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ConeExactSequence.lean`

```text
AAT.AG.AtlasDefectComposition.coneCokernelInclusion
AAT.AG.AtlasDefectComposition.coneKernelProjection
AAT.AG.AtlasDefectComposition.coneCokernelInclusion_mk
AAT.AG.AtlasDefectComposition.coneKernelProjection_val
AAT.AG.AtlasDefectComposition.coneCokernelInclusion_injective
AAT.AG.AtlasDefectComposition.cone_short_function_exact
AAT.AG.AtlasDefectComposition.coneKernelProjection_surjective
AAT.AG.AtlasDefectComposition.coneShortComplex
AAT.AG.AtlasDefectComposition.cone_short_exact
AAT.AG.AtlasDefectComposition.moduleCatHomologyFiniteDimensional
AAT.AG.AtlasDefectComposition.cochainHomologyFiniteDimensional
AAT.AG.AtlasDefectComposition.cone_homology_dimension
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ConeHomologySequence.lean`

```text
AAT.AG.AtlasDefectComposition.transportShortComplex
AAT.AG.AtlasDefectComposition.transportShortComplexIso
AAT.AG.AtlasDefectComposition.transportShortComplex_exact
AAT.AG.AtlasDefectComposition.coneConnecting
AAT.AG.AtlasDefectComposition.coneTargetSequence
AAT.AG.AtlasDefectComposition.coneTargetSequence_f
AAT.AG.AtlasDefectComposition.coneTargetSequence_g
AAT.AG.AtlasDefectComposition.cone_target_exact
AAT.AG.AtlasDefectComposition.coneMiddleSequence
AAT.AG.AtlasDefectComposition.coneMiddleSequence_f
AAT.AG.AtlasDefectComposition.coneMiddleSequence_g
AAT.AG.AtlasDefectComposition.cone_middle_exact
AAT.AG.AtlasDefectComposition.coneSourceSequence
AAT.AG.AtlasDefectComposition.coneSourceSequence_f
AAT.AG.AtlasDefectComposition.coneSourceSequence_g
AAT.AG.AtlasDefectComposition.cone_source_exact
AAT.AG.AtlasDefectComposition.homologyFactors_inv_natural
AAT.AG.AtlasDefectComposition.homologyFactors_hom_natural
AAT.AG.AtlasDefectComposition.coneConnecting_natural
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ConeNaturality.lean`

```text
AAT.AG.AtlasDefectComposition.homology_square
AAT.AG.AtlasDefectComposition.homologyCokernelMap
AAT.AG.AtlasDefectComposition.homologyKernelMap
AAT.AG.AtlasDefectComposition.homologyCokernelMap_mk
AAT.AG.AtlasDefectComposition.homologyKernelMap_val
AAT.AG.AtlasDefectComposition.coneCokernelInclusion_natural
AAT.AG.AtlasDefectComposition.coneKernelProjection_natural
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/EndpointHomology.lean`

```text
AAT.AG.AtlasDefectComposition.oldZeroShort
AAT.AG.AtlasDefectComposition.oldTwoShort
AAT.AG.AtlasDefectComposition.zeroExtensionZeroScIso
AAT.AG.AtlasDefectComposition.zeroExtensionTwoScIso
AAT.AG.AtlasDefectComposition.oldH0Iso
AAT.AG.AtlasDefectComposition.oldH2Iso
AAT.AG.AtlasDefectComposition.oldH0Equiv
AAT.AG.AtlasDefectComposition.oldH2Equiv
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/EndpointNaturality.lean`

```text
AAT.AG.AtlasDefectComposition.oldH0Map
AAT.AG.AtlasDefectComposition.oldH2Map
AAT.AG.AtlasDefectComposition.oldH0Map_val
AAT.AG.AtlasDefectComposition.oldH2Map_mk
AAT.AG.AtlasDefectComposition.oldZeroShortMap
AAT.AG.AtlasDefectComposition.oldTwoShortMap
AAT.AG.AtlasDefectComposition.zeroExtensionZeroScIso_natural
AAT.AG.AtlasDefectComposition.zeroExtensionTwoScIso_natural
AAT.AG.AtlasDefectComposition.oldZeroCycles_natural
AAT.AG.AtlasDefectComposition.oldTwoOpcycles_natural
AAT.AG.AtlasDefectComposition.oldH0Iso_natural
AAT.AG.AtlasDefectComposition.oldH2Iso_natural
AAT.AG.AtlasDefectComposition.oldH0Equiv_natural
AAT.AG.AtlasDefectComposition.oldH2Equiv_natural
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/FullSupportIncidence.lean`

```text
AAT.AG.AtlasDefectComposition.fullBlock_d1
AAT.AG.AtlasDefectComposition.faceDifference
AAT.AG.AtlasDefectComposition.faceDifference_apply
AAT.AG.AtlasDefectComposition.named_d1_d0
AAT.AG.AtlasDefectComposition.namedComplex
AAT.AG.AtlasDefectComposition.namedComplex_d0_apply
AAT.AG.AtlasDefectComposition.namedComplex_d1_apply
AAT.AG.AtlasDefectComposition.mem_ker_namedComplex_d0_iff
AAT.AG.AtlasDefectComposition.fullBlockNamedEquivalence
AAT.AG.AtlasDefectComposition.fullSupport_edge
AAT.AG.AtlasDefectComposition.fullSupport_face
AAT.AG.AtlasDefectComposition.fullBlockNamed_d0_rank
AAT.AG.AtlasDefectComposition.fullBlockNamed_d1_rank
AAT.AG.AtlasDefectComposition.fullBlockNamedHomologyEquiv
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/FullSupportPullback.lean`

```text
AAT.AG.AtlasDefectComposition.fullBlock_pullback0
AAT.AG.AtlasDefectComposition.fullBlock_pullback2_some
AAT.AG.AtlasDefectComposition.fullBlock_pullback2_none
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/HomologyConjugation.lean`

```text
AAT.AG.AtlasDefectComposition.homologyConjugation_square
AAT.AG.AtlasDefectComposition.homologyConjugation_defect
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/HomologyDimensions.lean`

```text
AAT.AG.AtlasDefectComposition.finrank_range_codRestrict
AAT.AG.AtlasDefectComposition.oldH1_dimension
AAT.AG.AtlasDefectComposition.standardH0_dimension
AAT.AG.AtlasDefectComposition.standardH1_dimension
AAT.AG.AtlasDefectComposition.standardH2_dimension
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/LinearConjugation.lean`

```text
AAT.AG.AtlasDefectComposition.LinearConjugation.range_map
AAT.AG.AtlasDefectComposition.LinearConjugation.kernel_map
AAT.AG.AtlasDefectComposition.LinearConjugation.kernelEquiv
AAT.AG.AtlasDefectComposition.LinearConjugation.cokernelEquiv
AAT.AG.AtlasDefectComposition.LinearConjugation.kernelEquiv_val
AAT.AG.AtlasDefectComposition.LinearConjugation.cokernelEquiv_mk
AAT.AG.AtlasDefectComposition.LinearConjugation.range_dimension
AAT.AG.AtlasDefectComposition.LinearConjugation.bijective_iff
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/NamedComparison.lean`

```text
AAT.AG.AtlasDefectComposition.namedComparisonHom
AAT.AG.AtlasDefectComposition.namedComparisonHom_square
AAT.AG.AtlasDefectComposition.namedComparisonHom_f0
AAT.AG.AtlasDefectComposition.namedComparisonHom_f1_some
AAT.AG.AtlasDefectComposition.namedComparisonHom_f1_none
AAT.AG.AtlasDefectComposition.namedComparisonHom_f2_some
AAT.AG.AtlasDefectComposition.namedComparisonHom_f2_none
AAT.AG.AtlasDefectComposition.namedComparison_zeroExtension_square
AAT.AG.AtlasDefectComposition.fullBlockNamedConeIso
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/NamedHomology.lean`

```text
AAT.AG.AtlasDefectComposition.fullBlockNamedHomology_defect
AAT.AG.AtlasDefectComposition.fullBlockNamedCone_homology_dimension
AAT.AG.AtlasDefectComposition.fullBlockNamedCone_degree_dimension
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ShortExactFive.lean`

```text
AAT.AG.AtlasDefectComposition.ShortExactFive.inclusion
AAT.AG.AtlasDefectComposition.ShortExactFive.projection
AAT.AG.AtlasDefectComposition.ShortExactFive.inclusion_mk
AAT.AG.AtlasDefectComposition.ShortExactFive.projection_val
AAT.AG.AtlasDefectComposition.ShortExactFive.inclusion_injective
AAT.AG.AtlasDefectComposition.ShortExactFive.exact
AAT.AG.AtlasDefectComposition.ShortExactFive.projection_surjective
AAT.AG.AtlasDefectComposition.ShortExactFive.dimension
AAT.AG.AtlasDefectComposition.ShortExactFive.middleEquivKernel
AAT.AG.AtlasDefectComposition.ShortExactFive.cokernelEquivMiddle
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ShortExactFiveConditions.lean`

```text
AAT.AG.AtlasDefectComposition.ShortExactFive.projection_bijective_iff
AAT.AG.AtlasDefectComposition.ShortExactFive.inclusion_bijective_iff
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/WitnessOneCones.lean`

```text
AAT.AG.AtlasDefectComposition.WitnessOne.actual₀₁
AAT.AG.AtlasDefectComposition.WitnessOne.actual₁₂
AAT.AG.AtlasDefectComposition.WitnessOne.actual₀₂
AAT.AG.AtlasDefectComposition.WitnessOne.forward_standard_defect_named
AAT.AG.AtlasDefectComposition.WitnessOne.backward_standard_defect_named
AAT.AG.AtlasDefectComposition.WitnessOne.direct_standard_defect_named
AAT.AG.AtlasDefectComposition.WitnessOne.actual_H0_defects
AAT.AG.AtlasDefectComposition.WitnessOne.actual_H2_defects
AAT.AG.AtlasDefectComposition.WitnessOne.extraTermsZero
AAT.AG.AtlasDefectComposition.WitnessOne.extraTermsZero_of_defects
AAT.AG.AtlasDefectComposition.WitnessOne.actual_extra_terms_zero
AAT.AG.AtlasDefectComposition.WitnessOne.extraTermsZero_W3a_false
AAT.AG.AtlasDefectComposition.WitnessOne.forward_cone_dimensions
AAT.AG.AtlasDefectComposition.WitnessOne.backward_cone_dimensions
AAT.AG.AtlasDefectComposition.WitnessOne.direct_cone_dimensions
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/WitnessOneEndpoints.lean`

```text
AAT.AG.AtlasDefectComposition.WitnessOne.constants₀
AAT.AG.AtlasDefectComposition.WitnessOne.constants₂
AAT.AG.AtlasDefectComposition.WitnessOne.constants₁
AAT.AG.AtlasDefectComposition.WitnessOne.named₀₁
AAT.AG.AtlasDefectComposition.WitnessOne.named₁₂
AAT.AG.AtlasDefectComposition.WitnessOne.named₀₂
AAT.AG.AtlasDefectComposition.WitnessOne.constants_forward
AAT.AG.AtlasDefectComposition.WitnessOne.constants_backward
AAT.AG.AtlasDefectComposition.WitnessOne.constants_direct
AAT.AG.AtlasDefectComposition.WitnessOne.named_H0_defects
AAT.AG.AtlasDefectComposition.WitnessOne.H2_dimensions
AAT.AG.AtlasDefectComposition.WitnessOne.named_H2_defects
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/WitnessThreeActual.lean`

```text
AAT.AG.AtlasDefectComposition.WitnessThree.actualA
AAT.AG.AtlasDefectComposition.WitnessThree.actualB
AAT.AG.AtlasDefectComposition.WitnessThree.actualA_coneIso
AAT.AG.AtlasDefectComposition.WitnessThree.actualB_coneIso
AAT.AG.AtlasDefectComposition.WitnessThree.actualA_defect_named
AAT.AG.AtlasDefectComposition.WitnessThree.actualB_defect_named
AAT.AG.AtlasDefectComposition.WitnessThree.actualA_H1_defect
AAT.AG.AtlasDefectComposition.WitnessThree.actualB_H1_defect
AAT.AG.AtlasDefectComposition.WitnessThree.actualA_H0_cokernel_dimension
AAT.AG.AtlasDefectComposition.WitnessThree.actualB_H2_kernel_dimension
AAT.AG.AtlasDefectComposition.WitnessThree.actualA_cone_homology_dimension
AAT.AG.AtlasDefectComposition.WitnessThree.actualB_cone_homology_dimension
AAT.AG.AtlasDefectComposition.WitnessThree.actualA_cone_homology_dimensions
AAT.AG.AtlasDefectComposition.WitnessThree.actualB_cone_homology_dimensions
AAT.AG.AtlasDefectComposition.WitnessThree.actualB_cone_degree_dimension
AAT.AG.AtlasDefectComposition.WitnessThree.actualB_cone_dimensions
AAT.AG.AtlasDefectComposition.WitnessThree.actualB_cone_differential_ranks
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/WitnessThreeConeA.lean`

```text
AAT.AG.AtlasDefectComposition.WitnessThree.A₀_d0_zero
AAT.AG.AtlasDefectComposition.WitnessThree.A₀_ranks
AAT.AG.AtlasDefectComposition.WitnessThree.A₁_ranks
AAT.AG.AtlasDefectComposition.WitnessThree.A_homology_dimensions
AAT.AG.AtlasDefectComposition.WitnessThree.namedA_oldH0_injective
AAT.AG.AtlasDefectComposition.WitnessThree.namedA_H0_injective
AAT.AG.AtlasDefectComposition.WitnessThree.namedA_H0_defect
AAT.AG.AtlasDefectComposition.WitnessThree.namedA_H1_defect
AAT.AG.AtlasDefectComposition.WitnessThree.namedA_H2_defect
AAT.AG.AtlasDefectComposition.WitnessThree.namedA_oldH1_defect
AAT.AG.AtlasDefectComposition.WitnessThree.namedA_cone_homology_dimensions
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/WitnessThreeConeB.lean`

```text
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_standardH0_bijective
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_H0_defect
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_H1_defect
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_oldH1_defect
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_H2_defect
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_cone_homology_dimensions
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/WitnessThreeConeRanks.lean`

```text
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_cone_dimensions
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_cone_finite
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_cone_d_before_zero
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_cone_differential_ranks
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/WitnessThreeInput.lean`

```text
AAT.AG.AtlasDefectComposition.WitnessThree.Source
AAT.AG.AtlasDefectComposition.WitnessThree.q₀
AAT.AG.AtlasDefectComposition.WitnessThree.q₁
AAT.AG.AtlasDefectComposition.WitnessThree.coarser
AAT.AG.AtlasDefectComposition.WitnessThree.not_coarser
AAT.AG.AtlasDefectComposition.WitnessThree.laws
AAT.AG.AtlasDefectComposition.WitnessThree.adequate₀
AAT.AG.AtlasDefectComposition.WitnessThree.adequate₁
AAT.AG.AtlasDefectComposition.WitnessThree.label
AAT.AG.AtlasDefectComposition.WitnessThree.label_unique
AAT.AG.AtlasDefectComposition.WitnessThree.isolated
AAT.AG.AtlasDefectComposition.WitnessThree.A₀
AAT.AG.AtlasDefectComposition.WitnessThree.A₁
AAT.AG.AtlasDefectComposition.WitnessThree.MA
AAT.AG.AtlasDefectComposition.WitnessThree.tetrahedron
AAT.AG.AtlasDefectComposition.WitnessThree.filledTriangle
AAT.AG.AtlasDefectComposition.WitnessThree.B₀
AAT.AG.AtlasDefectComposition.WitnessThree.B₁
AAT.AG.AtlasDefectComposition.WitnessThree.MB
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/WitnessThreeNamed.lean`

```text
AAT.AG.AtlasDefectComposition.WitnessThree.eqA₀
AAT.AG.AtlasDefectComposition.WitnessThree.eqA₁
AAT.AG.AtlasDefectComposition.WitnessThree.eqB₀
AAT.AG.AtlasDefectComposition.WitnessThree.eqB₁
AAT.AG.AtlasDefectComposition.WitnessThree.namedA
AAT.AG.AtlasDefectComposition.WitnessThree.namedB
AAT.AG.AtlasDefectComposition.WitnessThree.namedA_f0
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_f0
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_f1
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_f2
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_H0_constants
AAT.AG.AtlasDefectComposition.WitnessThree.namedB_H0_bijective
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/WitnessThreeRanks.lean`

```text
AAT.AG.AtlasDefectComposition.WitnessThree.tetrahedronConstants
AAT.AG.AtlasDefectComposition.WitnessThree.triangleConstants
AAT.AG.AtlasDefectComposition.WitnessThree.tetrahedronFaceImage
AAT.AG.AtlasDefectComposition.WitnessThree.triangleFace_surjective
AAT.AG.AtlasDefectComposition.WitnessThree.tetrahedron_d0_rank
AAT.AG.AtlasDefectComposition.WitnessThree.tetrahedron_d1_rank
AAT.AG.AtlasDefectComposition.WitnessThree.triangle_d0_rank
AAT.AG.AtlasDefectComposition.WitnessThree.triangle_d1_rank
AAT.AG.AtlasDefectComposition.WitnessThree.tetrahedron_homology_dimensions
AAT.AG.AtlasDefectComposition.WitnessThree.triangle_homology_dimensions
```

- `research/lean/ResearchLean/AG/AtlasDefectComposition/ZeroExtension.lean`

```text
AAT.AG.AtlasDefectComposition.degreeObject
AAT.AG.AtlasDefectComposition.degreeDifferential
AAT.AG.AtlasDefectComposition.degreeDifferential_square
AAT.AG.AtlasDefectComposition.zeroExtension
AAT.AG.AtlasDefectComposition.degreeMap
AAT.AG.AtlasDefectComposition.degreeMap_comm
AAT.AG.AtlasDefectComposition.zeroExtensionMap
AAT.AG.AtlasDefectComposition.zeroExtensionMap_comp
AAT.AG.AtlasDefectComposition.oldShort
AAT.AG.AtlasDefectComposition.zeroExtensionScIso
AAT.AG.AtlasDefectComposition.oldH1Iso
AAT.AG.AtlasDefectComposition.oldShortMap
AAT.AG.AtlasDefectComposition.oldShortMapData
AAT.AG.AtlasDefectComposition.oldShortMap_homology
AAT.AG.AtlasDefectComposition.zeroExtensionScIso_natural
AAT.AG.AtlasDefectComposition.oldH1Iso_natural
AAT.AG.AtlasDefectComposition.degreeObjectFiniteDimensional
AAT.AG.AtlasDefectComposition.zeroExtension_X
AAT.AG.AtlasDefectComposition.degreeObject_isZero
AAT.AG.AtlasDefectComposition.zeroExtension_d
AAT.AG.AtlasDefectComposition.zeroExtensionMap_f
AAT.AG.AtlasDefectComposition.zeroExtensionMap_id
AAT.AG.AtlasDefectComposition.oldH1Equiv
AAT.AG.AtlasDefectComposition.oldH1Equiv_natural
AAT.AG.AtlasDefectComposition.zeroExtensionDegreeFiniteDimensional
AAT.AG.AtlasDefectComposition.zeroExtension_homology_isZero
AAT.AG.AtlasDefectComposition.homologyTransport_natural
```

### Cycle 3 初回headの検証と監査入力

rootが実装段階ごとのfocused/targeted checkを行った。最終検証は
`cd research/lean` から
`lake build ResearchLean.AG.AtlasDefectComposition.WitnessOneCones ResearchLean.AG.AtlasDefectComposition.ConeNaturality`
で対象新規29module、FullSupportPullback、および必要な依存を検査し成功（3829 jobs）。
Research全体・aggregate・全file loop・local Formal全体buildは未実施。

`.tmp/g133-cycle3-axioms.lean` の単一scratchから284宣言の `#print axioms` を実行した。
source/spine/scratch/logの名前集合は欠落・余剰なし。propext・Classical.choice・Quot.soundのみ。
公理ログSHA-256は `776c32dfd02f8993ab71bfd9fa2b7910ff594cd48e15ecdfc09e8ca5d9581fd2`。
対象source/reportのplaceholder・hidden/BiDiはclean。privacy scanのヒットは既存の公開GitHub
監査URLだけで、新規ローカルパスなし。語彙scanは旧Cycle2の既存一行のみ、新規行にヒットなし。
FormalからResearchへのimportヒットなし。git diff --checkはclean。

```yaml
audits:
  premise_delta:
    discharged:
      - 実生成Homの三成分可換性を生成元と既存cochain同値から構成
      - 標準三角の長完全列から実核像のexactnessを構成
      - W3の全支持/因子化/セルincidenceを原始有限表から生成
      - W1の定数核同型と追加項零を原始差分/実chart比較から証明
    remaining: []
  certificate_provenance:
    discharged: [標準mappingCone両逆, 標準homology自然性, 実生成block比較, 原始セルrank]
    unresolved: []
  proof_use:
    used: [標準長完全列, 既存G107 cochain同値, 原始chart/edge/face, M2実H1欠損]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [上記targeted check, 284宣言公理ログ, 機械scan]
  blocking_findings: [独立PR査読は未実施]
  next_obligation: M3残の全Law対象同定/W1全Law錐をM4の実全成分/錐直和分解とともに構成
```

D/E/F・W2と全GOAL最終独立監査は未完。Formal移植・ArchSig実装は未実施。
恒久設計とGOAL本文は変更していない。Cycle3の内容受理は固定PR headの独立査読へ渡す。


### Cycle 3 初回監査と本筋修正

[PR #5265初回監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5265#issuecomment-6001002538)は
head `1460ce22a8a9b8f5d014c7fc0519e9e1c09dee9f` に対し数学A/B・LeanAがMinor issues、
LeanBがMajor revisionsを返した。中心/非中心の区分に差があるF3を、rootは中心findingとして扱う。

F1の公開微分評価・次数0核membership APIを追加し、指定rank・定数核・chart引き戻しの
下流証明を公開APIへ移す。F2の禁止語を具体的な入力幾何へ置換する。
F3のGOAL前提台帳228行・設計README105–106行を未完義務から落としていた記載を修正し、
全次数の指定射の同型条件、その両方向、追加項零性との同値と既存H¹への条件付き同型を構成する。

これらは元のM3終了条件に含まれる。元selection・GOAL・設計・result型を変更しない。
全Lawの錐対象同定とW1全Lawの錐値は引き続き未完であり、結果はproof-checkpointである。
修正後headはfresh4laneの正式再実行へ渡し、初回内容判定を再利用しない。


### Cycle 3 修正後の条項対応

`coneKernelProjection_bijective_iff` と `coneCokernelInclusion_bijective_iff` は、
標準長完全列から構成した指定射そのものの全単射性を、全整数mでそれぞれ
Hᵐ比較の全射性・Hᵐ⁺¹比較の単射性と同値にする。ShortExactFiveConditionsの
三つのexactnessは標準錐の `cone_target_exact`、`cone_middle_exact`、`cone_source_exact`
から供給し、AAT入力にexactnessを追加しない。

`comparison_H0_cokernel_zero_iff` と `comparison_H2_kernel_zero_iff` は、
実追加項の次元零性との必要十分条件を証明する。
`comparisonConeH0KernelEquiv` と `comparisonConeH1CokernelEquiv` は、
指定射影・包含を旧H¹の実核・余核へ移した条件付き線形同型である。
各apply則で移送後の射を固定する。条件はこの同型に限る方向仮定であり、
一般Cの構成には課さない。W1の実追加項零はWitnessOneConesで既に放電され、
W3a/bが検出する非零追加項を同じ条件で排除しない。


### Cycle 3 修正後の検証と監査入力

rootの必要依存targeted checkは
`lake build ResearchLean.AG.AtlasDefectComposition.WitnessOneCones ResearchLean.AG.AtlasDefectComposition.ConeNaturality ResearchLean.AG.AtlasDefectComposition.ConeConditional`
で成功（3831 jobs）。単一scratchの303宣言公理監査も成功し、
source/spine/scratch/logの名前集合は303で一致、欠落・余剰なし。
依存公理はpropext・Classical.choice・Quot.soundのみ。
ログSHA-256は `d689b30db0a331c7e5991759afbe1bf0a7e97675a85b5046f76bf77c66691ea6`。
32 Lean fileとreportのplaceholder・hidden/BiDi・privacy scan、
本体からResearchへのimport検査、git diff --checkはclean。
Research全体・aggregate・全file loop build、Formal移植・ArchSig実装、
全GOAL最終監査は未実施。F1/F2/F3の修正実体をfresh4lane正式再実行で監査する。


## Cycle 3 受理と Cycle 4 selection

PR #5265のhead `a78de2d9386d5f3877407f008988d17dea4a474e` に対する
[正式再実行1とroot acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5265#issuecomment-6001311085)は
fresh数学A/B・LeanA/BすべてNo major findings。proof-checkpointとして受理し、
merge commit `a3f33aaaac842385f85c8494597e3bd5ccb802bc` でmainへ統合した。
M3全Law接続は残り、GOALはactive、Issue #5261はopen。

```yaml
ledger_type: target_cycle_result
goal: G-133-aat-atlas-defect-composition
cycle: 4
goal_blob_sha: 8904a7d3bf428e0307499a40be4db1ba9091c51a
base_oid: a3f33aaaac842385f85c8494597e3bd5ccb802bc
tracking_issue: 5261
report_path: research/reports/G-133-aat-atlas-defect-composition.md
selection:
  proof_state_ref: Cycle3正式再実行1受理とIssue5261
  proof_dag_predecessors: [M1生成合成, M2実H1相殺, M3標準錐checkpoint, G104Law同値, G107labelFiber自然性]
  milestone: M4の実Law対象分解とM3全Law残の閉鎖
  proof_obligations:
    - 既存三次数block同値を全Law複体と有限直和へ接続し生成Hom全成分を同定
    - 実Law比較の核/余核/標準錐/自然短完全列を同じラベル有限直和へ分解
    - Bの六項列の全射とχおよび相殺rankを同じ分解で同定
    - 同じ粗fiberと細逆像の実subset比較へ全次数/錐/旧H1を接続
    - 指示Lawのselected true blockと空A零複体を構成し全Lawと区別
    - W1全Lawの錐と追加項、W3唯一ラベルから全Lawへの対象同定を評価
    - 同署名ラベルの重複度を保持
  exit_criteria:
    - Dの全対象と全指定射の可換同定がLeanで成立
    - 実生成比較/実subset比較の元と全次数の対応を保持
    - W1全Law錐/追加項とW3全Law指定値が同じ実入力から成立
    - 指示Law/空A/重複度をLeanで確認
    - 対象focused/targeted・全spineaxiom・scanを完了
  selection_reason: CをAAT実Lawへ集約しBの相殺と同じ構造で結び、EとFへの対象分解を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [LawCochainDecomposition.lean, FiniteComplexFamily.lean, LawConeDecomposition.lean, LawDefectDecomposition.lean]
  risks:
    - 次元公式だけで対象/射同定を代替しない
    - Law値型全体の有限性を追加しない
    - 全Lawを指示Lawtrue blockへ取り違えない
    - 署名重複ラベルを集合へ圧縮しない
  unchecked: [Dの未実装義務, E/F/W2, 全GOAL最終監査]
```


### Cycle 4 構成と条項対応

T0の有限Source・実セル比較・粗側adequacyを保持し、値型全体の有限性、
ConditionC、H¹比較の単射/全射、面の空性を一般分解へ追加しない。
細側adequacyは既存Aの因子化による値を使える。

| 固定条項 | 実体と指定射の証拠 |
| --- | --- |
| D: 全Law三次数複体と実比較 | LawCochainDecompositionの三つのblock同値と生成Hom成分、LawStandardDecompositionのzeroExtensionIsoと自然性、LawDirectSumTargetsの圏論的直和同型と自然性 |
| D: 実核・余核とJの二成分 | LawDefectDecompositionの実H¹/全次数kernel/cokernel同型とval/mk則、LawSubsetDefectDecompositionの同じ粗fiber・逆像からのJ和 |
| D: 標準錐 | FiniteConeFamilyの符号付き全次数座標・微分・projection、LawConeDecompositionの実錐同型、LawSubsetConeDecompositionの同じ粗fiber・canonical逆像錐への圏論的直和同型 |
| D: Cの短完全列の全指定射 | LawProjectionの実projection-square、LawShortExactDecompositionの核/余核元と標準包含/射影の全次数component則。Cの標準exactnessを同型で移す |
| D: Bの六項列・χ・r | DefectConjugation/FiniteDefectConjugationの六対象同型・全五射component則・χ像同型、LawSixTermDecompositionとLawFiberSixTermDecompositionの実生成比較/実fiber比較とrank和 |
| D: 同じ粗fiberと細逆像 | LawFiberDecompositionの全三次数比較square、labelValueFiber_eq_preimageを使うcanonical比較transport、LawFiberH1Familyの実H¹比較square。直接比較同定はAの独立生成合成定理を使う |
| D: selected true blockと空A | IndicatorSelectedBlockの非空A指示Lawのselected block・実錐同型。EmptySubsetの実三次数零性・零延長・homology・空比較錐零性。指示Law全体をtrue blockへ同一視しない |
| D/W1: 重複度 | 全分解はLawValueLabelの有限族/有限直和を使い、同台ラベルを消さない。既存WitnessOneFullLawの二発生ラベル・J倍化・χ rank2と今回の全Law錐値が同じ入力を使う |
| M3残/W1・W3 | WitnessOneFullLawConesは全Law錐H⁰/H¹が(0,2),(2,0),(0,0)、全追加項零。WitnessThreeFullLawは唯一発生ラベルから実全Law比較へ移し、H⁰余核1/H²核1、全錐homology値、W3bの各次数4,9,7,1と微分rank4,5,1を保持 |

FiniteComplexFamilyは実degreewise有限族をproductの普遍性から構成し、
圏論的有限直和と全次数homologyに接続する。FiniteLinearFamilyは実核・像・商を
成分へ移す。これらの一般線形代数部分だけではDの放電にならず、上表の
既存G104/G107三次数・H¹同値、実generatedComparisonHom、labelFiberComparisonHom、
aSubnerveComparisonHomへの接続を同じspineへ含める。

短完全列の自然性はCのconeCokernelInclusion_naturalとconeKernelProjection_naturalを
実blockProjectionへ適用する。標準錐の対象・射の同定であり、canonical分裂を選ばない。
LawFiberSixTermDecompositionは原始入力の三段実fiberを使う。粗fiberと細fiberの
canonical逆像同定はLawFiberDecompositionのcomparison squareで与え、
LawSubsetDefectDecompositionはJの両成分についてそのtransportを明示する。

### Cycle 4 受理候補spine

変更対象32 Lean fileの全316宣言を対象とする。新規一般補題だけでなく、
実Law接続・具体例・局所instanceと、既受理fileに追加した公開APIを含む。

| File（AtlasDefectComposition内） | 全対象宣言（AAT.AG.AtlasDefectComposition以下） |
| --- | --- |
| CochainEquivalence.lean | `cochainEquiv_hom_inv`, `cochainEquiv_inv_hom`, `cochainEquivZeroExtensionIso`, `cochainEquivZeroExtensionIso_hom`, `cochainEquiv_h1_standard` |
| ConeCoordinates.lean | `coneCoordinateEquiv`, `coneCoordinateEquiv_snd`, `coneCoordinateEquiv_fst`, `coneCoordinateEquiv_symm_snd`, `coneCoordinateEquiv_symm_fst`, `coneCoordinateEquiv_d`, `coneCoordinateEquiv_d_apply`, `coneCoordinateEquiv_map`, `comparisonCone`, `comparisonCone_eq`, `coneDegreeFiniteDimensional`, `comparisonCone_isZero`, `comparisonConeMinusOneEquiv`, `comparisonConeZeroEquiv`, `comparisonConeOneEquiv`, `comparisonConeTwoEquiv` |
| ConeEquivalence.lean | `coneIso_inverse_square`, `coneMapIso`, `coneMapIso_hom`, `coneHomologyEquiv` |
| DefectConjugation.lean | `DefectConjugation.comp_square`, `DefectConjugation.kernelFirst`, `DefectConjugation.kernelComposite`, `DefectConjugation.kernelLast`, `DefectConjugation.cokernelFirst`, `DefectConjugation.cokernelComposite`, `DefectConjugation.cokernelLast`, `DefectConjugation.first_natural`, `DefectConjugation.second_natural`, `DefectConjugation.cancellation_natural`, `DefectConjugation.fourth_natural`, `DefectConjugation.fifth_natural`, `DefectConjugation.cancellation_range`, `DefectConjugation.cancellationRangeEquiv` |
| DefectSequence.lean | `DefectSequence.first`, `DefectSequence.second`, `DefectSequence.cancellation`, `DefectSequence.cancellation_apply`, `DefectSequence.cancellation_eq_zero_iff`, `DefectSequence.fourth`, `DefectSequence.fifth`, `DefectSequence.first_val`, `DefectSequence.second_val`, `DefectSequence.fourth_mk`, `DefectSequence.fifth_mk`, `DefectSequence.first_injective`, `DefectSequence.exact_first_second`, `DefectSequence.exact_second_cancellation`, `DefectSequence.exact_cancellation_fourth`, `DefectSequence.exact_fourth_fifth`, `DefectSequence.fifth_surjective`, `DefectSequence.exact_zero_first`, `DefectSequence.exact_fifth_zero`, `DefectSequence.sixTerm_exact`, `DefectSequence.cancellation_ker`, `DefectSequence.cancellationQuotientEquiv`, `DefectSequence.kernel_dimension`, `DefectSequence.cokernel_dimension` |
| EmptySubset.lean | `emptySubsetChartIsEmpty`, `emptySubsetEdgeIsEmpty`, `emptySubsetFaceIsEmpty`, `emptySubsetC0Subsingleton`, `emptySubsetC1Subsingleton`, `emptySubsetC2Subsingleton`, `zeroExtension_isZero_X`, `emptySubset_isZero_X`, `emptySubset_isZero_homology`, `emptySubsetCone_isZero_X` |
| FiniteComplexFamily.lean | `FiniteComplexFamily.complex`, `FiniteComplexFamily.degreeSubsingleton`, `FiniteComplexFamily.d_apply`, `FiniteComplexFamily.projection`, `FiniteComplexFamily.map`, `FiniteComplexFamily.map_apply`, `FiniteComplexFamily.map_projection`, `FiniteComplexFamily.map_id`, `FiniteComplexFamily.map_comp`, `FiniteComplexFamily.iso`, `FiniteComplexFamily.fan`, `FiniteComplexFamily.fanIsLimit`, `FiniteComplexFamily.productIso`, `FiniteComplexFamily.degreeFiniteDimensional`, `FiniteComplexFamily.directSumIso`, `FiniteComplexFamily.directSumIso_projection`, `FiniteComplexFamily.directSumIso_natural`, `FiniteComplexFamily.additivePreservesFamily`, `FiniteComplexFamily.homologyIso`, `FiniteComplexFamily.homologyIso_projection`, `FiniteComplexFamily.homologyEquiv`, `FiniteComplexFamily.homologyEquiv_component`, `FiniteComplexFamily.homologyEquiv_natural` |
| FiniteConeFamily.lean | `FiniteConeFamily.productFamilyEquiv`, `FiniteConeFamily.degreeEquiv`, `FiniteConeFamily.degreeEquiv_component`, `FiniteConeFamily.degreeEquiv_d`, `FiniteConeFamily.iso`, `FiniteConeFamily.iso_apply`, `FiniteConeFamily.iso_projection` |
| FiniteDefectConjugation.lean | `FiniteDefectConjugation.firstEquiv`, `FiniteDefectConjugation.secondEquiv`, `FiniteDefectConjugation.thirdEquiv`, `FiniteDefectConjugation.fourthEquiv`, `FiniteDefectConjugation.fifthEquiv`, `FiniteDefectConjugation.sixthEquiv`, `FiniteDefectConjugation.first_component`, `FiniteDefectConjugation.second_component`, `FiniteDefectConjugation.cancellation_component`, `FiniteDefectConjugation.fourth_component`, `FiniteDefectConjugation.fifth_component`, `FiniteDefectConjugation.cancellationRangeEquiv` |
| FiniteDefectFamily.lean | `FiniteDefectFamily.kernelComposite`, `FiniteDefectFamily.cokernelComposite`, `FiniteDefectFamily.first_component`, `FiniteDefectFamily.second_component`, `FiniteDefectFamily.cancellation_component`, `FiniteDefectFamily.fourth_component`, `FiniteDefectFamily.fifth_component`, `FiniteDefectFamily.cancellation_square`, `FiniteDefectFamily.cancellationRangeEquiv` |
| FiniteLinearFamily.lean | `FiniteLinearFamily.map`, `FiniteLinearFamily.map_apply`, `FiniteLinearFamily.kernelEquiv`, `FiniteLinearFamily.kernelEquiv_val`, `FiniteLinearFamily.range_eq`, `FiniteLinearFamily.rangeEquiv`, `FiniteLinearFamily.rangeEquiv_val`, `FiniteLinearFamily.cokernelEquiv`, `FiniteLinearFamily.cokernelEquiv_mk` |
| IndicatorSelectedBlock.lean | `indicatorSelectedZeroExtensionIso`, `indicatorSelectedConeIso` |
| LawCochainDecomposition.lean | `lawFamily0Equiv`, `lawFamily1Equiv`, `lawFamily2Equiv`, `lawFamilyCochainEquiv`, `lawFamily_natural0`, `lawFamily_natural1`, `lawFamily_natural2` |
| LawConeDecomposition.lean | `lawConeFamilyIso`, `lawConeDirectSumIso`, `lawConeHomologyEquiv`, `lawConeFamilyIso_hom`, `lawConeHomologyEquiv_component_family`, `lawConeFiniteBiproducts` |
| LawDefectDecomposition.lean | `lawH1Comparison_square`, `lawH1KernelFamilyEquiv`, `lawH1CokernelFamilyEquiv`, `lawH1KernelFamilyEquiv_val`, `lawH1CokernelFamilyEquiv_mk`, `lawH1Defect_sum`, `lawStandardKernelFamilyEquiv`, `lawStandardCokernelFamilyEquiv`, `lawStandardKernelFamilyEquiv_val`, `lawStandardCokernelFamilyEquiv_mk` |
| LawDirectSumTargets.lean | `lawZeroExtensionDirectSumIso`, `lawZeroExtensionDirectSumIso_natural`, `lawH1KernelDirectSumEquiv`, `lawH1CokernelDirectSumEquiv`, `lawStandardKernelDirectSumEquiv`, `lawStandardCokernelDirectSumEquiv`, `lawDirectSumFiniteBiproducts` |
| LawFiberDecomposition.lean | `lawBlockFiberZeroExtensionIso`, `lawBlockFiber_comparison_square`, `lawBlockFiberZeroExtensionIso_natural`, `lawBlockFiberConeIso`, `lawFiberComparison_canonical`, `subsetComparisonZeroExtension_square`, `lawBlockSelectedSubsetZeroExtensionIso`, `lawBlockSelectedSubsetZeroExtensionIso_natural`, `lawBlockSelectedSubsetConeIso`, `lawBlockCanonicalConeIso` |
| LawFiberH1Family.lean | `lawFiberH1FamilyEquiv`, `lawFiberH1Comparison_square` |
| LawFiberSixTermDecomposition.lean | `LawFiberSixTermDecomposition.kernelFirstFamilyEquiv`, `LawFiberSixTermDecomposition.kernelCompositeFamilyEquiv`, `LawFiberSixTermDecomposition.kernelLastFamilyEquiv`, `LawFiberSixTermDecomposition.cokernelFirstFamilyEquiv`, `LawFiberSixTermDecomposition.cokernelCompositeFamilyEquiv`, `LawFiberSixTermDecomposition.cokernelLastFamilyEquiv`, `LawFiberSixTermDecomposition.first_component`, `LawFiberSixTermDecomposition.second_component`, `LawFiberSixTermDecomposition.cancellation_component`, `LawFiberSixTermDecomposition.fourth_component`, `LawFiberSixTermDecomposition.fifth_component`, `LawFiberSixTermDecomposition.cancellationRangeFamilyEquiv`, `LawFiberSixTermDecomposition.cancellation_rank_sum` |
| LawProjection.lean | `lawBlockZeroExtensionProjection`, `lawBlockZeroExtensionProjection_natural`, `lawStandardHomologyEquiv_component`, `lawConeBlockProjection`, `lawConeFamilyIso_projection`, `lawConeHomologyEquiv_component` |
| LawShortExactDecomposition.lean | `lawStandardCokernelFamilyEquiv_component`, `lawStandardKernelFamilyEquiv_component`, `lawConeCokernelInclusion_component`, `lawConeKernelProjection_component` |
| LawSixTermDecomposition.lean | `LawSixTermDecomposition.kernelFirstFamilyEquiv`, `LawSixTermDecomposition.kernelCompositeFamilyEquiv`, `LawSixTermDecomposition.kernelLastFamilyEquiv`, `LawSixTermDecomposition.cokernelFirstFamilyEquiv`, `LawSixTermDecomposition.cokernelCompositeFamilyEquiv`, `LawSixTermDecomposition.cokernelLastFamilyEquiv`, `LawSixTermDecomposition.first_component`, `LawSixTermDecomposition.second_component`, `LawSixTermDecomposition.cancellation_component`, `LawSixTermDecomposition.fourth_component`, `LawSixTermDecomposition.fifth_component`, `LawSixTermDecomposition.cancellationRangeFamilyEquiv`, `LawSixTermDecomposition.cancellation_rank_sum` |
| LawStandardDecomposition.lean | `lawZeroExtensionIso`, `lawFamily_comparison_square`, `lawZeroExtensionIso_natural`, `lawStandardHomologyEquiv`, `lawStandardHomologyEquiv_natural`, `lawStandardHomologyEquiv_component_family` |
| LawStandardDimensions.lean | `lawStandardDefect_sum` |
| LawSubsetConeDecomposition.lean | `lawSubsetConeFamilyIso`, `lawSubsetConeDirectSumIso`, `lawSubsetConeHomologyEquiv`, `lawSubsetConeHomology_dimension`, `lawSubsetConeFiniteBiproducts` |
| LawSubsetDefectDecomposition.lean | `lawFiberH1KernelFamilyEquiv`, `lawFiberH1CokernelFamilyEquiv`, `lawFiberH1KernelFamilyEquiv_val`, `lawFiberH1CokernelFamilyEquiv_mk`, `lawFiberH1Defect_sum`, `lawFiberDefect_canonical`, `lawH1Defect_subset_sum` |
| LawUniqueBlock.lean | `lawUniqueBlockZeroExtensionIso`, `lawUniqueBlockZeroExtensionIso_natural`, `lawUniqueBlockConeIso`, `lawUniqueBlockStandardDefect`, `lawUniqueBlockConeHomology_dimension`, `lawUniqueBlockConeDegree_dimension`, `lawUniqueBlockCone_d_rank` |
| ThreeComplexFamily.lean | `ThreeComplexFamily.complex`, `ThreeComplexFamily.d0_apply`, `ThreeComplexFamily.d1_apply`, `ThreeComplexFamily.map`, `ThreeComplexFamily.map0_apply`, `ThreeComplexFamily.map1_apply`, `ThreeComplexFamily.map2_apply`, `ThreeComplexFamily.degreeEquiv`, `ThreeComplexFamily.degreeEquiv0_apply`, `ThreeComplexFamily.degreeEquiv1_apply`, `ThreeComplexFamily.degreeEquiv2_apply`, `ThreeComplexFamily.degreeEquiv_d`, `ThreeComplexFamily.zeroExtensionIso`, `ThreeComplexFamily.zeroExtensionIso_apply`, `ThreeComplexFamily.degreeEquiv_natural`, `ThreeComplexFamily.zeroExtensionIso_natural` |
| UniqueComplexFamily.lean | `UniqueComplexFamily.evaluationEquiv`, `UniqueComplexFamily.evaluationEquiv_apply`, `UniqueComplexFamily.iso`, `UniqueComplexFamily.iso_hom` |
| WitnessOneFullLawCones.lean | `WitnessOne.fullActual₀₁`, `WitnessOne.fullActual₁₂`, `WitnessOne.fullActual₀₂`, `WitnessOne.full_forward_cone_dimensions`, `WitnessOne.full_backward_cone_dimensions`, `WitnessOne.full_direct_cone_dimensions`, `WitnessOne.full_endpoint_defects`, `WitnessOne.full_extra_terms_zero` |
| WitnessThreeFullLaw.lean | `WitnessThree.labelsSubsingleton`, `WitnessThree.fullActualA`, `WitnessThree.fullActualB`, `WitnessThree.fullActualA_standard_defect`, `WitnessThree.fullActualB_standard_defect`, `WitnessThree.fullActualA_H1_defect`, `WitnessThree.fullActualB_H1_defect`, `WitnessThree.fullActualA_H0_cokernel_dimension`, `WitnessThree.fullActualB_H2_kernel_dimension`, `WitnessThree.fullActualA_cone_homology_dimension`, `WitnessThree.fullActualB_cone_homology_dimension`, `WitnessThree.fullActualA_cone_homology_dimensions`, `WitnessThree.fullActualB_cone_homology_dimensions`, `WitnessThree.fullActualB_cone_degree_dimension`, `WitnessThree.fullActualB_cone_dimensions`, `WitnessThree.fullActualB_cone_differential_ranks` |
| ZeroExtension.lean | `degreeObject`, `degreeDifferential`, `degreeDifferential_square`, `zeroExtension`, `degreeMap`, `degreeMap_comm`, `zeroExtensionMap`, `zeroExtensionMap_comp`, `oldShort`, `zeroExtensionScIso`, `oldH1Iso`, `oldShortMap`, `oldShortMapData`, `oldShortMap_homology`, `zeroExtensionScIso_natural`, `oldH1Iso_natural`, `degreeObjectFiniteDimensional`, `zeroExtension_X`, `degreeObject_isZero`, `zeroExtension_d`, `zeroExtensionMap_f`, `zeroExtensionMap_id`, `oldH1Equiv`, `oldH1Equiv_natural`, `zeroExtensionDegreeFiniteDimensional`, `zeroExtension_homology_isZero`, `homologyTransport_natural`, `zeroExtension_d0_apply`, `zeroExtension_d1_apply`, `zeroExtension_d_zero`, `zeroExtensionMap_f0_apply`, `zeroExtensionMap_f1_apply`, `zeroExtensionMap_f2_apply` |


### Cycle 4 検証とresult proposal

rootの必要依存targeted checkは以下の明示targetで成功（3860 jobs）。

```text
lake build ResearchLean.AG.AtlasDefectComposition.LawDirectSumTargets ResearchLean.AG.AtlasDefectComposition.LawShortExactDecomposition ResearchLean.AG.AtlasDefectComposition.LawFiberSixTermDecomposition ResearchLean.AG.AtlasDefectComposition.WitnessOneFullLawCones ResearchLean.AG.AtlasDefectComposition.WitnessThreeFullLaw ResearchLean.AG.AtlasDefectComposition.EmptySubset ResearchLean.AG.AtlasDefectComposition.IndicatorSelectedBlock
```

単一scratchの全316宣言の公理監査も成功。sourceの各module公理検査の対象数、
上のspine、scratch、ログの宣言数は316で一致し、名前の欠落・余剰はない。
依存公理はpropext・Classical.choice・Quot.soundのみ。ログSHA-256は
`8c1873602546dc1a35f8557cdd5555cb2ceb4f8bd0c5857a06f4d927a4652519`。
placeholder・hidden/BiDi・新規行の語彙・本体からResearchへのimport・diff checkはclean。
privacyパターンの7件は既存の公開GitHub監査URLのみで、ローカルパス/非公開値はない。
保護本文・恒久設計・GOAL本文・Formal・toolingに変更はない。
Research全体・aggregate・全file loop build、Formal移植、ArchSig実装、
全GOAL独立完了監査は未実施。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - Dの実全Law複体/比較/全次数核余核/標準錐を有限直和へ同定
    - C短完全列とB六項列の全指定射/相殺像を実ラベル比較へ同定
    - 同じ粗fiberと細逆像の実部分集合比較を三次数/標準錐/旧H1へ接続
    - 非空Aselected true blockと空A零複体を構成
    - W1/W3実全Law対象と指定値を同じ原始入力から評価
  exit_criteria_status:
    - D全対象と全指定射: 上の条項対応と316宣言
    - 実生成比較/実subset比較: LawFiberDecompositionとLawSubsetDefectDecomposition
    - W1/W3全Law指定値: WitnessOneFullLawConesとWitnessThreeFullLaw
    - 指示Law/空A/重複度: IndicatorSelectedBlock/EmptySubset/全LawValueLabel有限直和
    - targeted/axiom/scan: 上記成功
  split_reason: none
  completion_candidate: no
  lean_artifacts: [上記32file316宣言spine]
  evidence: [実Law比較可換同型, 同じ粗fiber逆像の錐直和同型, 指定射component則, W1/W3実全Law評価]
  claim_mapping:
    theorem_names: [lawSubsetConeDirectSumIso, lawH1Defect_subset_sum, LawFiberSixTermDecomposition.cancellation_rank_sum, lawConeCokernelInclusion_component, lawConeKernelProjection_component]
    source_labels: [GOAL D, GOAL C全Law対象, 設計W1/W3全Law値]
    conjuncts: [上記条項対応表]
    undischarged_assumptions: []
    acceptance_point: Dの元と射の可換同定を実入力へ接続しM3全Law残を閉じる
    port_status: unported
audits:
  premise_delta:
    discharged: [実Law三次数/H1同値からの標準複体自然性, finite product普遍性からの直和, 実projectionによる全次数短完全列自然性, 同じ原始W1/W3からの全Law評価]
    remaining: []
  certificate_provenance:
    discharged: [G104block同値, G107fiber同値/逆像等号, 標準mappingCone, 実指示Lawtrue label, 原始セル表]
    unresolved: []
  proof_use:
    used: [三次数block微分可換性, 全次数comparison square, 標準cone自然性, 実H1相殺, 全LawValueLabel添字]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [3860jobs targeted, 316宣言公理ログ, 上記scan]
  blocking_findings: [独立PRレビューは未実施]
  next_obligation: M5の台署名商/二普遍性/selected block加法性/台制限自然性とW2
```

このresultは独立PR監査へ渡すproposalである。E/F/W2・全GOAL最終監査は未完、
GOALはactive、tracking Issueはopen。M3/M4の受理判断は固定headの監査コメントに置く。


## Cycle 4 内容受理と Cycle 5 selection

PR #5266の修正head `5134712871383bb9f88d832a069757052c0a26d0` は
[独立監査と有資格直接対応/root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5266#issuecomment-6002459758)で
DとM3全Law残をproof-obligation-dischargedとして内容受理した。
CI待機中のためmerge・Issue checkbox同期は未実施。固定PR headを保持し、
別branchで次の選定を記録する。M4のmerge条件・全GOALの完了条件を緩めない。

```yaml
ledger_type: target_cycle_result
goal: G-133-aat-atlas-defect-composition
cycle: 5
goal_blob_sha: 8904a7d3bf428e0307499a40be4db1ba9091c51a
base_oid: 5134712871383bb9f88d832a069757052c0a26d0
tracking_issue: 5261
report_path: research/reports/G-133-aat-atlas-defect-composition.md
selection:
  proof_state_ref: Cycle4固定headの内容受理監査（CI待機/merge未実施）
  proof_dag_predecessors: [M1実生成合成, M2実相殺, M3標準錐, M4実Law直和接続]
  milestone: M5の台署名による構造の分類と欠損の輸送
  proof_obligations:
    - 両側三次数の名付き全セル署名・Galois接続・閉包・join商/像/閉集合同型
    - 全セル復元の有限join商圏の終対象と通常の商の逆向き普遍性
    - 同署名によるセル/incidence/退化宣言/実比較/複体/錐同定
    - selected block族の指定射/非交和と重複度による分類・加法的自由普遍性
    - 実Lawからの比較/錐復元と指示Lawtrue単独blockへの一意評価
    - 署名op上の両側複体/比較/錐/H1核余核関手
    - 全三段セルの共通署名と各pair射影・B全射/χ自然性
    - W2同じ原始入力の異署名同零欠損/真の閉包/同署名別subsetとW1重複度
  exit_criteria:
    - E全構成/全方向/対象と指定射をLeanで証明
    - Dの実入力/直和へ接続し自由線形同型で指定射を拡張しない
    - W2とW1署名/重複度を原始入力から評価
    - 対象focused/必要依存targeted・全spineaxiom・scanを完了
  selection_reason: 台の構造を同じ比較群へ戻してFの自然な多段towerを支える
  expected_result_type: proof-obligation-discharged
  lean_targets: [SupportSignature.lean, SignatureUniversal.lean, SubsetRestriction.lean, SelectedBlockFamily.lean, WitnessTwo.lean]
  risks:
    - 粗側または次数1だけの署名へ縮めない
    - 二普遍性の射方向を混同しない
    - 固定閉集合のjoin/bottomを素朴なunion/emptyで代替しない
    - 名付きセル復元と任意の線形同型を混同しない
    - 同署名ラベルの重複度とselected単独評価の一意性を保持
    - pair別に共通Aを選び直さない
  unchecked: [E/W2未実装, F, 全GOAL最終独立監査, Cycle4CIとmerge]
```

### Cycle 4 の merge 証拠（cycle 5 の実装中に同期）

- PR #5266、受理固定 head `5134712871383bb9f88d832a069757052c0a26d0`、merge `6dd8f2260591085f88bc949097e4f46a91ba54b7`、2026-10-05T21:23:10Z。
- 内容受入: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5266#issuecomment-6002459758 。非中心 F1/F2 は fresh 直接確認で解消済み。
- 全8必須 CI 成功。Lean run `37370346054`、Tool run `37370345912`。hosted runner 未取得で未実行取消しとなった jobs を同じ head で再実行して解消した。Research aggregate/full build は実行していない。
- cycle 4 の結果は `proof-obligation-discharged`。M3 全Law例残と D 全条項を受理し、E/F/W2 と最終累積完了監査は未完である。
- cycle 5 の固定 selection base は実装前に記録した `5134712871383bb9f88d832a069757052c0a26d0` を維持する。merge commit と同じ数学 tree であり、selection を実装後に改訂しない。GOAL active、tracking Issue open を維持する。


### Cycle 5 条項と実入力経路

すべてのsubset（空集合を含む）を同じ粗targetから引き戻す。台署名・台制限関手では
Sourceとセル型のuniverseを独立に量化する。実Law比較・錐復元とJ評価は既存Law APIの
`TargetSupportedNerve.{u,u}` に接続し、Lawの値型全体にFintypeを要求しない。

| 固定要求 | 今回の証拠と生成経路 |
| --- | --- |
| E・六つの名付きセル | `SupportSignature.Cell/family` は粗細chart/edge/faceをSumの六tagで区別し、`mem_family_coarseChart` 等の六membershipと `alpha_eq_iff` は元のsubset選択と同じ逆像選択を同定する。 |
| Galois/閉包/商/像/Fix | `SignatureGeometry.galois`、`closureOperator`、`quotientEquiv`、`closedOrderIso`、`SignatureGeometry.quotientOrderIso/quotientClosedOrderIso`。閉集合joinはclosure(union)、bottomはclosure(empty)。元の名付きセル包含を使う。 |
| 指定商圏の終対象 | `SignatureGeometry.Presentation/PresentationHom` は有限join半束、全subsetからの全射、全セルdecoderと両正方形を保持する。`terminalHom` をdecoderの像へのcorestrictionから構成し、`signatureIsTerminal` が全対象・全指定射の一意性を示す。 |
| 逆向きの普通の商普遍性 | `quotientFactor/quotient_universal` は署名核を消す任意のSupBotHomについて、署名から評価先への一意因子化を示す。decoderの終射と向きを混同しない。 |
| incidence・退化・全比較の復元 | `SubsetRestriction` は同じ元のセルの包含と辺両端/面三辺を使う。`SupportRestriction.chart_square/edge_option_square/face_option_square` は元のOption宣言も保持し、`pullback0_square/1_square/2_square/comparison_square` を証明する。`SubsetEquivalence` と `SupportReconstruction` は同署名の両向き包含から実cochain、標準複体、実錐同型を作る。 |
| 台の反対向き関手 | `SupportFunctor.coarseFunctor/fineFunctor/comparisonNat`、`SupportFunctor.coneFunctor/coneHomologyFunctor`、`SupportFunctor.h1KernelFunctor/h1CokernelFunctor`。canonical gamma代表を使い、制限の恒等/合成は元の座標で証明する。`SupportDefectValue.value_dimension` は旧H¹の実Jと標準H¹核余核の次元表を同定する。 |
| selected族の指定射と対称モノイド圏 | `SelectedFamilies.Family/Hom` は有限subset族と非bottom添字の署名保存全単射だけを持つ。`SelectedFamilyOperations` の元の非交和/reindexから `SelectedFamilyMonoidal` のMonoidal/Braided/Symmetric instancesを構成し、`multiplicity_classifies` で同型類を分類する。 |
| 零block削除と比較・錐の復元 | `SupportZeroBlock` はsigma=bottomから六セル空を証明する。`SelectedFamilyComplex` のactive同型、`FiniteFamilyZeroDeletion`、`FiniteFamilyReindex`、`SelectedFamilyReconstruction` は元のblock同型と添字並べ替えを使う。`SelectedFamilyComplex.reconstruction_square` と `SelectedFamilyComplex.canonical_square` が全比較射も保つ。任意の線形同型を族の射に加えない。 |
| 多重度と自由加法的普遍性 | `SelectedFamilies.canonical_multiplicity` と `SelectedFamilies.multiplicity_classifies` は有限supportの全多重度を実現/分類する。`SelectedFamilies.additive_universal` は任意の可換加法モノイドBに値を持つ指定評価を単独block値の和として全一意に表す。`SelectedFamilies.freeMonoid_universal/freeEvaluation_multiplicity` でFinsuppの自由可換モノイドへ接続する。 |
| 実Lawと指示Lawへの接続 | `lawSelected_square/lawMultiplicity_square` はDのラベルfiberと同じ細逆像族を使い、実全Law比較を多重度モデルへ同定する。`lawMultiplicityConeIso` は実全Law錐を同定する。`SupportSignature.nonbottomIndicatorConeIso` は非bottom代表の非空性から指示Lawtrue単独blockへ接続する。`SupportDefectValue.law_evaluation` は実全LawJへ適用する。 |
| 全三段共通署名とpair射影 | `SupportStages.Cell` は任意有限段の全セルを段階/次数/セル名で区別する。`SupportStages.pairProjection/pairProjection_sigma` と `ThreeStageSignatures.projection₀₁/projection₀₂/projection₁₂` は共通Aの各pair署名を復元する。`pairComparison_comp` は独立に生成した直接比較と合成を同定する。 |
| Bの全指定射とχの自然性 | `SupportStages.sixTerm_natural/sixTerm_signature_natural` は実H¹の二正方形を `pairH1_square` から放電し、first/second/cancellation/fourth/fifthの全五射を同じ全段台制限と可換にする。終端の零射も一意である。 |
| W2同じ原始入力 | `WitnessTwoInput` はFin3 Source、恒等reading/比較、Bool chartのsupport {0,1}/{2}、空edge/faceを構成する。`WitnessTwoGeometry` の原始membershipから同署名別subsetと真の閉包を証明する。`WitnessTwo.signature_card/quotient_card` は4、`actualDefect_zero` は全Aで(0,0)、`different_signature_same_defect/no_defect_decoder` は名付きセルが診断値から復元不能な同じ二subsetを評価する。 |
| W1二ラベルの重複度 | `WitnessOne.label_fiber/label_sigma` は既存W1の同じ原始Law降下からfiberを取り、`singleton_sigma_eq/singleton_nonbottom/shared_multiplicity` で共有非bottom署名の多重度2を評価する。`fullLawMultiplicityConeIso` はその実全Law錐へ接続する。 |

### Cycle 5 premise・proof-use・依存DAG

| premise / field | 役割 | 放電と使用先 |
| --- | --- | --- |
| reading/有限支持nerve/原始部分比較/粗adequacy | ambient-boundary | T0のまま保持。六tagのmembership・Option正方形・LawSelected正方形へ使用。W2は全fieldを原始表から構成。 |
| Presentationの全射とdecoder square | 指定圏の対象の定義 | Eが量化する対象そのもの。実signaturePresentationではsigma_surjectiveと実alphaを使って構成し、terminalHomの値が像にあることと一意性へ使用。 |
| 同署名/署名包含/SelectedLE | 一般transportのdirection-hypothesis、E適用はdischarge-required | 原始全セルalphaのmembershipからcoarseLE/fineLE/stageLEとOption正方形を導出する。同署名の指定同型と全関手/自然性で使用。 |
| Family.Homのactive全単射と署名等号 | 設計§4の指定射の定義 | multiplicity_classifiesの両方向とcanonical代表で生成。元のセル固定block同型とfinite reindexへ使用。 |
| AdditiveEvaluationの不変/非交和/零条件 | 設計§4の評価対象の定義 | 任意v(bottom)=0からevaluationOfValuesを生成。任意IからsignatureValueを単独selected blockで生成し、有限添字帰納法で全族の和と一意性を証明。 |
| outside blockが零 / reindexの比較square | 一般補助のdirection-hypothesis、実適用はdischarge-required | SupportZeroBlockの六セル空から全次数Subsingletonを証明、各blockの実三次数comparison squareと原始添字の全単射から放電。削除/挿入/全比較/錐同型へ使用。 |
| six-term helperのhf/hg | 一般補助のdirection-hypothesis、実適用はdischarge-required | SubsetComparisonNaturalityとSupportStages.pairH1_squareで実入力から放電。全五指定射とχの自然性へ使用。 |
| 非bottom代表の非空性 | discharge-required | SupportSignature.representative_nonemptyにより証明し、M4指示Lawtrue blockへ適用。 |
| 有限LawValueLabel | discharge-required | 既存Source有限からの発生ラベル有限性。全値型有限性を使わず実LawSelectedFamilyの添字と有限和/多重度へ使用。 |

今回のDAGは原始支持セル→六tag選択→Galois/署名→実セル制限→全比較正方形→
標準複体/錐/旧H¹核余核である。別枝は指定有限族→active添字→多重度→
元のblock同型/並べ替え→実全Law比較と錐の復元、評価の自由性である。
全段支持セル→共通署名→pair射影/実全段制限→実H¹正方形→Bの全五射/χ自然性を接続した。
W2とW1多重度はこれらと同じ原始生成経路を使う。

再利用はM1 #5263（実生成合成）、M2 #5264（実六項列と旧H¹欠損）、
M3 #5265（標準零拡張/自然な旧H¹同型/実錐）、M4 #5266
（実Lawの全次数fiber分解/同じ逆像族/指示Law/finite cone family）の受理版を使う。
版と受理参照は前節の各固定headにあり、今回の使用箇所に関係するsource変更はない。
mathlibはLean 4.28.0、commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。
標準Category/Monoidal/Finsupp/finite product/ModuleCat kernel・cokernel/cone/homology APIを
各適用条件と引数で使用する。既存結果の存在や名前のみを接続証拠にはしない。

### Cycle 5 修正headの全spine proposal

新規44ファイルの非internal宣言579をmodule provenanceから固定する。
M1–M4の累積spineは各前節を維持する。生成structure fieldとinstance、補助定理も監査する。
初回552一覧との差分は公開API・W2実Law接続27宣言の純増である。
`SelectedFamilies.AdditiveEvaluation.mk.congr_simp` の自動生成名1件が変更され、
当該sourceの定義・statement・構成は維持する。

| ファイル | 全宣言（prefix AAT.AG.AtlasDefectComposition を省略） |
| --- | --- |
| FiniteFamilyReindex.lean | `FiniteFamilyReindex.blockIso`, `FiniteFamilyReindex.blockIso_hom`, `FiniteFamilyReindex.degreeEquiv`, `FiniteFamilyReindex.degreeEquiv_apply`, `FiniteFamilyReindex.degreeEquiv_d`, `FiniteFamilyReindex.iso`, `FiniteFamilyReindex.iso_hom_apply`, `FiniteFamilyReindex.reindexIso` |
| FiniteFamilyReindexNaturality.lean | `FiniteFamilyReindex.block_square`, `FiniteFamilyReindex.square` |
| FiniteFamilyZeroDeletion.lean | `FiniteFamilyZeroDeletion.degreeEquiv`, `FiniteFamilyZeroDeletion.degreeEquiv.congr_simp`, `FiniteFamilyZeroDeletion.degreeEquiv_d`, `FiniteFamilyZeroDeletion.extendDegree`, `FiniteFamilyZeroDeletion.extendDegree_apply`, `FiniteFamilyZeroDeletion.iso`, `FiniteFamilyZeroDeletion.iso_apply`, `FiniteFamilyZeroDeletion.restrictDegree`, `FiniteFamilyZeroDeletion.restrictDegree_apply` |
| LawSignatureComparison.lean | `lawBlockSelectedSubsetZeroExtensionIso.congr_simp`, `lawMultiplicityCoarseIso`, `lawMultiplicityFineIso`, `lawMultiplicity_square`, `lawSelectedCoarseIso`, `lawSelectedFineIso`, `lawSelected_square` |
| LawSignatureRestoration.lean | `lawMultiplicityConeHomologyEquiv`, `lawMultiplicityConeIso`, `lawSelectedComparisonConeIso`, `lawSelectedFamily` |
| SelectedFamilies.lean | `SelectedFamilies.Active`, `SelectedFamilies.Family`, `SelectedFamilies.Family.Index`, `SelectedFamilies.Family.casesOn`, `SelectedFamilies.Family.ctorIdx`, `SelectedFamilies.Family.finite`, `SelectedFamilies.Family.mk`, `SelectedFamilies.Family.mk.inj`, `SelectedFamilies.Family.mk.injEq`, `SelectedFamilies.Family.mk.noConfusion`, `SelectedFamilies.Family.mk.sizeOf_spec`, `SelectedFamilies.Family.noConfusion`, `SelectedFamilies.Family.noConfusionType`, `SelectedFamilies.Family.rec`, `SelectedFamilies.Family.recOn`, `SelectedFamilies.Family.subset`, `SelectedFamilies.Fiber`, `SelectedFamilies.Hom`, `SelectedFamilies.Hom.casesOn`, `SelectedFamilies.Hom.ctorIdx`, `SelectedFamilies.Hom.equiv`, `SelectedFamilies.Hom.mk`, `SelectedFamilies.Hom.mk.inj`, `SelectedFamilies.Hom.mk.injEq`, `SelectedFamilies.Hom.mk.noConfusion`, `SelectedFamilies.Hom.mk.sizeOf_spec`, `SelectedFamilies.Hom.noConfusion`, `SelectedFamilies.Hom.noConfusionType`, `SelectedFamilies.Hom.rec`, `SelectedFamilies.Hom.recOn`, `SelectedFamilies.Hom.signature_eq`, `SelectedFamilies.NonzeroSignature`, `SelectedFamilies.activeSignature`, `SelectedFamilies.familyCategory`, `SelectedFamilies.fiberEquiv`, `SelectedFamilies.homComp`, `SelectedFamilies.homId`, `SelectedFamilies.homOfFiberCards`, `SelectedFamilies.homSymm`, `SelectedFamilies.hom_ext`, `SelectedFamilies.hom_ext_iff`, `SelectedFamilies.isoOfHom`, `SelectedFamilies.multiplicity`, `SelectedFamilies.multiplicity_apply`, `SelectedFamilies.multiplicity_classifies`, `SelectedFamilies.multiplicity_eq_of_hom` |
| SelectedFamilyAdditive.lean | `SelectedFamilies.AdditiveEvaluation`, `SelectedFamilies.AdditiveEvaluation.casesOn`, `SelectedFamilies.AdditiveEvaluation.ctorIdx`, `SelectedFamilies.AdditiveEvaluation.empty`, `SelectedFamilies.AdditiveEvaluation.eval`, `SelectedFamilies.AdditiveEvaluation.invariant`, `SelectedFamilies.AdditiveEvaluation.mk`, `SelectedFamilies.AdditiveEvaluation.mk.inj`, `SelectedFamilies.AdditiveEvaluation.mk.injEq`, `SelectedFamilies.AdditiveEvaluation.mk.noConfusion`, `SelectedFamilies.AdditiveEvaluation.mk.sizeOf_spec`, `SelectedFamilies.AdditiveEvaluation.noConfusion`, `SelectedFamilies.AdditiveEvaluation.noConfusionType`, `SelectedFamilies.AdditiveEvaluation.rec`, `SelectedFamilies.AdditiveEvaluation.recOn`, `SelectedFamilies.AdditiveEvaluation.sum`, `SelectedFamilies.AdditiveEvaluation.zero_single`, `SelectedFamilies.eval_family`, `SelectedFamilies.eval_ofBlocks`, `SelectedFamilies.ofBlocks`, `SelectedFamilies.single_eval_eq` |
| SelectedFamilyCanonical.lean | `SelectedFamilies.MultiplicityIndex`, `SelectedFamilies.canonicalActiveEquiv`, `SelectedFamilies.canonicalFamily`, `SelectedFamilies.canonicalFiberEquiv`, `SelectedFamilies.canonical_active_signature`, `SelectedFamilies.canonical_classifies`, `SelectedFamilies.canonical_multiplicity`, `SelectedFamilies.canonical_sigma`, `SelectedFamilies.multiplicityFiberEquiv`, `SelectedFamilies.multiplicityIndexEquiv`, `SelectedFamilies.multiplicityIndexFinite`, `SelectedFamilies.multiplicity_surjective` |
| SelectedFamilyCanonicalComparison.lean | `SelectedFamilyComplex.canonicalCoarseIso`, `SelectedFamilyComplex.canonicalFineIso`, `SelectedFamilyComplex.canonicalHom`, `SelectedFamilyComplex.canonical_square` |
| SelectedFamilyComparison.lean | `SelectedFamilyComplex.activeReconstruction_square`, `SelectedFamilyComplex.reconstruction_square` |
| SelectedFamilyComplex.lean | `SelectedFamilyComplex.active_square`, `SelectedFamilyComplex.coarse`, `SelectedFamilyComplex.coarseActiveIso`, `SelectedFamilyComplex.coarseBlock`, `SelectedFamilyComplex.coarseZero`, `SelectedFamilyComplex.comparison`, `SelectedFamilyComplex.comparisonBlock`, `SelectedFamilyComplex.coneActiveIso`, `SelectedFamilyComplex.coneBlock`, `SelectedFamilyComplex.coneZero`, `SelectedFamilyComplex.fine`, `SelectedFamilyComplex.fineActiveIso`, `SelectedFamilyComplex.fineBlock`, `SelectedFamilyComplex.fineZero` |
| SelectedFamilyFreeMonoid.lean | `SelectedFamilies.freeEvaluation`, `SelectedFamilies.freeEvaluation_multiplicity`, `SelectedFamilies.freeEvaluation_single`, `SelectedFamilies.freeEvaluation_unique`, `SelectedFamilies.freeMonoid_universal` |
| SelectedFamilyMonoidal.lean | `SelectedFamilies.familyBraided`, `SelectedFamilies.familyMonoidal`, `SelectedFamilies.familySymmetric` |
| SelectedFamilyMultiplicity.lean | `SelectedFamilies.emptyFiberIsEmpty`, `SelectedFamilies.fiberSumEquiv`, `SelectedFamilies.multiplicity.congr_simp`, `SelectedFamilies.multiplicity_empty`, `SelectedFamilies.multiplicity_sum` |
| SelectedFamilyOperations.lean | `SelectedFamilies.activeSumEquiv`, `SelectedFamilies.associatorHom`, `SelectedFamilies.braidingHom`, `SelectedFamilies.empty`, `SelectedFamilies.emptyIndexIsEmpty`, `SelectedFamilies.leftUnitorHom`, `SelectedFamilies.reindexHom`, `SelectedFamilies.rightUnitorHom`, `SelectedFamilies.single`, `SelectedFamilies.singleHom`, `SelectedFamilies.sum`, `SelectedFamilies.tensorHom` |
| SelectedFamilyReconstruction.lean | `SelectedFamilyComplex.blockAlphaEq`, `SelectedFamilyComplex.block_square`, `SelectedFamilyComplex.canonicalConeHomologyEquiv`, `SelectedFamilyComplex.canonicalConeIso`, `SelectedFamilyComplex.coarseBlockIso`, `SelectedFamilyComplex.coarseReconstructionIso`, `SelectedFamilyComplex.coarseReconstructionIso_hom`, `SelectedFamilyComplex.coneBlockIso`, `SelectedFamilyComplex.coneReconstructionIso`, `SelectedFamilyComplex.fineBlockIso`, `SelectedFamilyComplex.fineReconstructionIso`, `SelectedFamilyComplex.fineReconstructionIso_hom` |
| SelectedFamilyUniversal.lean | `SelectedFamilies.additive_universal`, `SelectedFamilies.evaluationOfValues`, `SelectedFamilies.evaluationOfValues_eval`, `SelectedFamilies.signatureValue`, `SelectedFamilies.signatureValue_bot`, `SelectedFamilies.signatureValue_represents`, `SelectedFamilies.signatureValue_sigma`, `SelectedFamilies.signatureValue_unique`, `SelectedFamilies.valueSum`, `SelectedFamilies.valueSum_active`, `SelectedFamilies.valueSum_eq_sum`, `SelectedFamilies.valueSum_invariant`, `SelectedFamilies.valueSum_single`, `SelectedFamilies.valueSum_sum` |
| SignatureGeometry.lean | `SignatureGeometry.ClosedSubset`, `SignatureGeometry.Signature`, `SignatureGeometry.alpha`, `SignatureGeometry.alpha_closure`, `SignatureGeometry.alpha_empty`, `SignatureGeometry.alpha_gamma_alpha`, `SignatureGeometry.alpha_gamma_signature`, `SignatureGeometry.alpha_mono`, `SignatureGeometry.alpha_union`, `SignatureGeometry.closedEquiv`, `SignatureGeometry.closedOrderBot`, `SignatureGeometry.closedOrderIso`, `SignatureGeometry.closedSemilatticeSup`, `SignatureGeometry.closed_bot_val`, `SignatureGeometry.closed_sup_val`, `SignatureGeometry.closure`, `SignatureGeometry.closureOperator`, `SignatureGeometry.closure_idempotent`, `SignatureGeometry.closure_mono`, `SignatureGeometry.galois`, `SignatureGeometry.gamma`, `SignatureGeometry.gamma_mono`, `SignatureGeometry.inclusionHom`, `SignatureGeometry.mem_alpha`, `SignatureGeometry.mem_gamma`, `SignatureGeometry.quotientEquiv`, `SignatureGeometry.sigma`, `SignatureGeometry.sigmaHom`, `SignatureGeometry.sigma_eq_iff`, `SignatureGeometry.sigma_gamma_signature`, `SignatureGeometry.sigma_surjective`, `SignatureGeometry.sigma_val`, `SignatureGeometry.signatureFinite`, `SignatureGeometry.signatureOrderBot`, `SignatureGeometry.signatureSemilatticeSup`, `SignatureGeometry.signatureSetoid`, `SignatureGeometry.signature_bot_val`, `SignatureGeometry.signature_sup_val`, `SignatureGeometry.subset_closure` |
| SignatureQuotient.lean | `SignatureGeometry.SignatureQuotient`, `SignatureGeometry.closedOrderIso_sup`, `SignatureGeometry.quotientClosedOrderIso`, `SignatureGeometry.quotientEquiv_mk`, `SignatureGeometry.quotientFinite`, `SignatureGeometry.quotientOrderBot`, `SignatureGeometry.quotientOrderIso`, `SignatureGeometry.quotientPartialOrder`, `SignatureGeometry.quotientSemilatticeSup`, `SignatureGeometry.quotient_mk_empty`, `SignatureGeometry.quotient_mk_union`, `SignatureGeometry.signature_join_congr` |
| SignatureUniversal.lean | `SignatureGeometry.Presentation`, `SignatureGeometry.Presentation.Carrier`, `SignatureGeometry.Presentation.bot`, `SignatureGeometry.Presentation.casesOn`, `SignatureGeometry.Presentation.ctorIdx`, `SignatureGeometry.Presentation.decode`, `SignatureGeometry.Presentation.decode_encode`, `SignatureGeometry.Presentation.encode`, `SignatureGeometry.Presentation.encode_surjective`, `SignatureGeometry.Presentation.finite`, `SignatureGeometry.Presentation.mk`, `SignatureGeometry.Presentation.mk.inj`, `SignatureGeometry.Presentation.mk.injEq`, `SignatureGeometry.Presentation.mk.noConfusion`, `SignatureGeometry.Presentation.mk.sizeOf_spec`, `SignatureGeometry.Presentation.noConfusion`, `SignatureGeometry.Presentation.noConfusionType`, `SignatureGeometry.Presentation.rec`, `SignatureGeometry.Presentation.recOn`, `SignatureGeometry.Presentation.sup`, `SignatureGeometry.PresentationHom`, `SignatureGeometry.PresentationHom.casesOn`, `SignatureGeometry.PresentationHom.ctorIdx`, `SignatureGeometry.PresentationHom.decode_comm`, `SignatureGeometry.PresentationHom.encode_comm`, `SignatureGeometry.PresentationHom.map`, `SignatureGeometry.PresentationHom.mk`, `SignatureGeometry.PresentationHom.mk.inj`, `SignatureGeometry.PresentationHom.mk.injEq`, `SignatureGeometry.PresentationHom.mk.noConfusion`, `SignatureGeometry.PresentationHom.mk.sizeOf_spec`, `SignatureGeometry.PresentationHom.noConfusion`, `SignatureGeometry.PresentationHom.noConfusionType`, `SignatureGeometry.PresentationHom.rec`, `SignatureGeometry.PresentationHom.recOn`, `SignatureGeometry.presentationCategory`, `SignatureGeometry.presentationHomComp`, `SignatureGeometry.presentationHomId`, `SignatureGeometry.presentationHom_ext`, `SignatureGeometry.presentationHom_ext_iff`, `SignatureGeometry.quotientFactor`, `SignatureGeometry.quotientFactor_comp`, `SignatureGeometry.quotientFactor_sigma`, `SignatureGeometry.quotientFactor_unique`, `SignatureGeometry.quotient_universal`, `SignatureGeometry.signatureIsTerminal`, `SignatureGeometry.signaturePresentation`, `SignatureGeometry.terminalHom`, `SignatureGeometry.terminalHom_unique`, `SignatureGeometry.terminalHom_val` |
| SixTermNaturality.lean | `SixTermNaturality.cancellation_natural`, `SixTermNaturality.cokernelMap`, `SixTermNaturality.cokernelMap.congr_simp`, `SixTermNaturality.cokernelMap_mk`, `SixTermNaturality.comp_square`, `SixTermNaturality.fifth_natural`, `SixTermNaturality.first_natural`, `SixTermNaturality.fourth_natural`, `SixTermNaturality.kernelMap`, `SixTermNaturality.kernelMap_val`, `SixTermNaturality.second_natural` |
| SubsetComparisonNaturality.lean | `SubsetComparisonNaturality.chart_square`, `SubsetComparisonNaturality.comparison_square`, `SubsetComparisonNaturality.edge_option_square`, `SubsetComparisonNaturality.face_option_square`, `SubsetComparisonNaturality.pullback0_square`, `SubsetComparisonNaturality.pullback1_square`, `SubsetComparisonNaturality.pullback2_square` |
| SubsetEquivalence.lean | `SubsetRestriction.chartEquiv`, `SubsetRestriction.cochainEquiv`, `SubsetRestriction.cochainEquiv_symm_toHom`, `SubsetRestriction.cochainEquiv_toHom`, `SubsetRestriction.complexIso`, `SubsetRestriction.edgeEquiv`, `SubsetRestriction.equiv0`, `SubsetRestriction.equiv0_symm_toLinearMap`, `SubsetRestriction.equiv0_toLinearMap`, `SubsetRestriction.equiv1`, `SubsetRestriction.equiv1_symm_toLinearMap`, `SubsetRestriction.equiv1_toLinearMap`, `SubsetRestriction.equiv2`, `SubsetRestriction.equiv2_symm_toLinearMap`, `SubsetRestriction.equiv2_toLinearMap`, `SubsetRestriction.faceEquiv`, `SubsetRestriction.h1Equiv` |
| SubsetRestriction.lean | `SubsetRestriction.SelectedLE`, `SubsetRestriction.chartInclusion`, `SubsetRestriction.chartInclusion.congr_simp`, `SubsetRestriction.chartInclusion_edgeLeft`, `SubsetRestriction.chartInclusion_edgeRight`, `SubsetRestriction.chartInclusion_val`, `SubsetRestriction.edgeInclusion`, `SubsetRestriction.edgeInclusion.congr_simp`, `SubsetRestriction.edgeInclusion_faceEdge0`, `SubsetRestriction.edgeInclusion_faceEdge1`, `SubsetRestriction.edgeInclusion_faceEdge2`, `SubsetRestriction.edgeInclusion_val`, `SubsetRestriction.faceInclusion`, `SubsetRestriction.faceInclusion.congr_simp`, `SubsetRestriction.faceInclusion_val`, `SubsetRestriction.hom`, `SubsetRestriction.hom_comp`, `SubsetRestriction.hom_f0`, `SubsetRestriction.hom_f1`, `SubsetRestriction.hom_f2`, `SubsetRestriction.hom_id`, `SubsetRestriction.restrict0`, `SubsetRestriction.restrict0.congr_simp`, `SubsetRestriction.restrict0_apply`, `SubsetRestriction.restrict1`, `SubsetRestriction.restrict1.congr_simp`, `SubsetRestriction.restrict1_apply`, `SubsetRestriction.restrict2`, `SubsetRestriction.restrict2.congr_simp`, `SubsetRestriction.restrict2_apply`, `SubsetRestriction.restrict_d0`, `SubsetRestriction.restrict_d1`, `SubsetRestriction.selectedLE_of_subset`, `SubsetRestriction.selectedLE_refl`, `SubsetRestriction.selectedLE_trans` |
| SupportConeFunctor.lean | `SupportFunctor.coarseMap.congr_simp`, `SupportFunctor.cone`, `SupportFunctor.coneFunctor`, `SupportFunctor.coneHomologyFunctor`, `SupportFunctor.coneMap`, `SupportFunctor.coneMap_comp`, `SupportFunctor.coneMap_id`, `SupportFunctor.fineMap.congr_simp` |
| SupportDefectFunctor.lean | `SupportFunctor.h1Cokernel`, `SupportFunctor.h1CokernelFunctor`, `SupportFunctor.h1CokernelMap`, `SupportFunctor.h1CokernelMap.congr_simp`, `SupportFunctor.h1CokernelMap_comp`, `SupportFunctor.h1CokernelMap_id`, `SupportFunctor.h1CokernelMap_mk`, `SupportFunctor.h1Kernel`, `SupportFunctor.h1KernelFunctor`, `SupportFunctor.h1KernelMap`, `SupportFunctor.h1KernelMap.congr_simp`, `SupportFunctor.h1KernelMap_comp`, `SupportFunctor.h1KernelMap_id`, `SupportFunctor.h1KernelMap_val` |
| SupportDefectValue.lean | `SelectedFamilies.evaluationOfValues.congr_simp`, `SupportDefectValue.actual`, `SupportDefectValue.evaluation`, `SupportDefectValue.evaluation_actual`, `SupportDefectValue.law_evaluation`, `SupportDefectValue.same_alpha`, `SupportDefectValue.value`, `SupportDefectValue.value_bot`, `SupportDefectValue.value_dimension`, `SupportDefectValue.value_sigma`, `SupportReconstruction.coarseEquiv.congr_simp`, `SupportReconstruction.fineEquiv.congr_simp` |
| SupportFunctor.lean | `SupportFunctor.alpha_le`, `SupportFunctor.alpha_representative`, `SupportFunctor.coarseComplex`, `SupportFunctor.coarseFunctor`, `SupportFunctor.coarseMap`, `SupportFunctor.coarseMap_comp`, `SupportFunctor.coarseMap_id`, `SupportFunctor.comparison`, `SupportFunctor.comparisonNat`, `SupportFunctor.comparison_natural`, `SupportFunctor.fineComplex`, `SupportFunctor.fineFunctor`, `SupportFunctor.fineMap`, `SupportFunctor.fineMap_comp`, `SupportFunctor.fineMap_id`, `SupportFunctor.representative`, `SupportFunctor.representative_mono` |
| SupportNonbottomRealization.lean | `SupportSignature.nonbottomIndicatorConeIso`, `SupportSignature.nonbottom_nonempty`, `SupportSignature.representative_nonempty` |
| SupportReconstruction.lean | `SupportReconstruction.closureConeIso`, `SupportReconstruction.coarseEquiv`, `SupportReconstruction.coarseIso`, `SupportReconstruction.comparison_square`, `SupportReconstruction.complex_square`, `SupportReconstruction.coneHomologyEquiv`, `SupportReconstruction.coneIso`, `SupportReconstruction.fineEquiv`, `SupportReconstruction.fineIso`, `SupportReconstruction.representativeConeIso`, `SupportReconstruction.representative_eq` |
| SupportRestriction.lean | `SupportRestriction.chart_square`, `SupportRestriction.coarseLE`, `SupportRestriction.comparison_square`, `SupportRestriction.complex_square`, `SupportRestriction.edge_option_square`, `SupportRestriction.face_option_square`, `SupportRestriction.fineLE`, `SupportRestriction.pullback0_square`, `SupportRestriction.pullback1_square`, `SupportRestriction.pullback2_square`, `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.targetSubsetPullback1.congr_simp`, `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.targetSubsetPullback2.congr_simp` |
| SupportSignature.lean | `SupportSignature.Cell`, `SupportSignature.Signature`, `SupportSignature.alpha`, `SupportSignature.alpha.congr_simp`, `SupportSignature.alpha_eq_iff`, `SupportSignature.coarseChart`, `SupportSignature.coarseEdge`, `SupportSignature.coarseFace`, `SupportSignature.family`, `SupportSignature.family.congr_simp`, `SupportSignature.fineChart`, `SupportSignature.fineEdge`, `SupportSignature.fineFace`, `SupportSignature.mem_alpha_coarseChart`, `SupportSignature.mem_alpha_coarseEdge`, `SupportSignature.mem_alpha_coarseFace`, `SupportSignature.mem_alpha_fineChart`, `SupportSignature.mem_alpha_fineEdge`, `SupportSignature.mem_alpha_fineFace`, `SupportSignature.mem_family_coarseChart`, `SupportSignature.mem_family_coarseEdge`, `SupportSignature.mem_family_coarseFace`, `SupportSignature.mem_family_fineChart`, `SupportSignature.mem_family_fineEdge`, `SupportSignature.mem_family_fineFace`, `SupportSignature.sigma`, `SupportSignature.sigma_eq_iff` |
| SupportStageComparison.lean | `SupportStages.pairComparison`, `SupportStages.pairComparison_canonical`, `SupportStages.pairComparison_square`, `SupportStages.pairH1_square`, `SupportStages.pair_mapsTo`, `SupportStages.stageRestriction.congr_simp` |
| SupportStageProjections.lean | `SupportStages.factor_pair`, `SupportStages.pairEncode`, `SupportStages.pairProjection`, `SupportStages.pairProjection_sigma`, `SupportStages.pair_alpha_mono`, `SupportStages.pair_preimage`, `SupportStages.pair_respects` |
| SupportStageSignatures.lean | `SupportStages.Cell`, `SupportStages.Signature`, `SupportStages.StageCell`, `SupportStages.alpha`, `SupportStages.alpha.congr_simp`, `SupportStages.cellFinite`, `SupportStages.family`, `SupportStages.family.congr_simp`, `SupportStages.mem_alpha`, `SupportStages.sigma`, `SupportStages.stageComplex`, `SupportStages.stageLE`, `SupportStages.stageRestriction`, `SupportStages.support` |
| SupportStageSixTerm.lean | `SupportStages.alpha_representative`, `SupportStages.pairComparison_comp`, `SupportStages.representative`, `SupportStages.representativeLE`, `SupportStages.sixTerm_natural`, `SupportStages.sixTerm_signature_natural` |
| SupportZeroBlock.lean | `SupportZeroBlock.alpha_empty`, `SupportZeroBlock.coarseChartIsEmpty`, `SupportZeroBlock.coarseEdgeIsEmpty`, `SupportZeroBlock.coarseFaceIsEmpty`, `SupportZeroBlock.coarse_isZero_X`, `SupportZeroBlock.coarse_subsingleton_X`, `SupportZeroBlock.cone_isZero_X`, `SupportZeroBlock.cone_subsingleton_X`, `SupportZeroBlock.fineChartIsEmpty`, `SupportZeroBlock.fineEdgeIsEmpty`, `SupportZeroBlock.fineFaceIsEmpty`, `SupportZeroBlock.fine_isZero_X`, `SupportZeroBlock.fine_subsingleton_X` |
| ThreeStageSignatures.lean | `ThreeStageSignatures.Cell`, `ThreeStageSignatures.Signature`, `ThreeStageSignatures.coarsers`, `ThreeStageSignatures.nerves`, `ThreeStageSignatures.projection₀₁`, `ThreeStageSignatures.projection₀₁_sigma`, `ThreeStageSignatures.projection₀₂`, `ThreeStageSignatures.projection₀₂_sigma`, `ThreeStageSignatures.projection₁₂`, `ThreeStageSignatures.projection₁₂_sigma`, `ThreeStageSignatures.readings`, `ThreeStageSignatures.sigma` |
| WitnessOneSignatureMultiplicity.lean | `WitnessOne.fullLawMultiplicityConeIso`, `WitnessOne.label_fiber`, `WitnessOne.label_sigma`, `WitnessOne.selected`, `WitnessOne.sharedFiberEquiv`, `WitnessOne.sharedSignature`, `WitnessOne.shared_multiplicity`, `WitnessOne.singleton_alpha_eq`, `WitnessOne.singleton_nonbottom`, `WitnessOne.singleton_sigma_eq` |
| WitnessTwoGeometry.lean | `WitnessTwo.alpha_eq_iff`, `WitnessTwo.closure_a`, `WitnessTwo.coarse_chart_select`, `WitnessTwo.coarse_false_mem`, `WitnessTwo.coarse_true_mem`, `WitnessTwo.fine_chart_select`, `WitnessTwo.mem_gamma_alpha`, `WitnessTwo.sigma_a_eq_b`, `WitnessTwo.sigma_a_ne_c`, `WitnessTwo.sigma_eq_iff` |
| WitnessTwoInput.lean | `WitnessTwo.M`, `WitnessTwo.N`, `WitnessTwo.Source`, `WitnessTwo.adequate`, `WitnessTwo.alpha`, `WitnessTwo.coarser`, `WitnessTwo.factor_self`, `WitnessTwo.family`, `WitnessTwo.laws`, `WitnessTwo.nerve`, `WitnessTwo.q`, `WitnessTwo.sigma`, `WitnessTwo.support` |
| WitnessTwoLawMultiplicity.lean | `WitnessTwo.activeA`, `WitnessTwo.activeB`, `WitnessTwo.active_a_b_signature`, `WitnessTwo.active_a_ne_b`, `WitnessTwo.fullLawMultiplicityConeIso`, `WitnessTwo.fullLawSelectedCoarseIso`, `WitnessTwo.fullLawSelected_square`, `WitnessTwo.label`, `WitnessTwo.labelEquivSource`, `WitnessTwo.label_card`, `WitnessTwo.label_fiber`, `WitnessTwo.label_sigma_iff`, `WitnessTwo.labels_a_ne_b`, `WitnessTwo.labels_exhaust`, `WitnessTwo.not_selectedLE_a_c`, `WitnessTwo.selected`, `WitnessTwo.sharedFiberEquiv`, `WitnessTwo.sharedSignature`, `WitnessTwo.shared_multiplicity`, `WitnessTwo.singleton_nonbottom` |
| WitnessTwoTargets.lean | `WitnessTwo.actualDefect_zero`, `WitnessTwo.actualH1_bijective`, `WitnessTwo.chartSelection`, `WitnessTwo.chartSelection_bijective`, `WitnessTwo.closure_strict`, `WitnessTwo.different_signature_same_defect`, `WitnessTwo.no_defect_decoder`, `WitnessTwo.quotient_card`, `WitnessTwo.signatureEquiv`, `WitnessTwo.signature_card`, `WitnessTwo.subsetC1Subsingleton`, `WitnessTwo.subsetH1Subsingleton` |
| ZeroH1.lean | `h1_subsingleton_of_C1` |

### Cycle 5 初回headの検証とresult proposal

rootの必要依存targeted checkは次の明示7対象で成功（3874 jobs）。

```text
lake build ResearchLean.AG.AtlasDefectComposition.LawSignatureComparison ResearchLean.AG.AtlasDefectComposition.SupportDefectValue ResearchLean.AG.AtlasDefectComposition.ThreeStageSignatures ResearchLean.AG.AtlasDefectComposition.SupportNonbottomRealization ResearchLean.AG.AtlasDefectComposition.WitnessTwoTargets ResearchLean.AG.AtlasDefectComposition.WitnessOneSignatureMultiplicity ResearchLean.AG.AtlasDefectComposition.SignatureQuotient
```

最終の不要simp引数削除後、WitnessOneSignatureMultiplicityの必要依存targeted checkも成功。
全42ファイルにstandard axiom assertionがあり、単一scratchの全552宣言の
`#print axioms`が成功した。上のspine、module metadata、scratch、ログの宣言集合は
552で完全一致し、依存公理はpropext・Classical.choice・Quot.soundのみ。
公理ログSHA-256は `4f54deccc5d29c629d59733c311c93417baef871199fd9df761fe53372fbcd0b`。
placeholder（reportの検査項目名を除く）・hidden/BiDi・本体からResearchへのimport・
新規行の語彙・diff checkはclean。privacyの9件は既存公開監査URLまたは既存スキル参照のみ。
保護本文・恒久設計・GOAL本文・Formal・toolingに変更はない。
Research全体・aggregate・全file loop build、Formal移植、ArchSig実装は未実施。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: [Eの全名付きセル署名と二普遍性, 指定対称モノイド族と全多重度分類と自由加法的普遍性, 実全Law比較と錐の復元, 共通全段署名とpair射影とB全五射自然性, W2全指定値とW1共有署名多重度2]
  exit_criteria_status:
    - E全構成/全方向/指定対象と射: 上の条項対応と552宣言
    - Dの実入力/直和への接続: lawMultiplicity_squareとlawMultiplicityConeIso
    - W2/W1原始評価: WitnessTwoTargetsとWitnessOneSignatureMultiplicity
    - targeted/全宣言公理/scan: 上記成功
  split_reason: none
  completion_candidate: no
  lean_artifacts: [上記42file552宣言spine]
  evidence: [六tag原始membership, 全セル復元終対象と逆向き商因子化, 実比較自然変換, 指定多重度canonical復元, 単独selected blockの自由評価, 実全段制限と六項列全射可換性, 原始W2全評価]
  claim_mapping:
    theorem_names: [signatureIsTerminal, quotient_universal, multiplicity_classifies, additive_universal, freeMonoid_universal, lawMultiplicity_square, lawMultiplicityConeIso, sixTerm_signature_natural, no_defect_decoder, shared_multiplicity]
    source_labels: [GOAL E, 設計台署名§4, GOAL W2, W1の二ラベル重複度]
    conjuncts: [上記条項対応表]
    undischarged_assumptions: []
    acceptance_point: 全セル選択と実比較を保持してEの分類/復元/自然性を閉じる
    port_status: unported
audits:
  premise_delta:
    discharged: [原始alphaからのSelectedLE, 原始Option正方形, 零署名の実全次数零, 多重度からの指定添字全単射, 実H1比較正方形, 非bottom代表非空, 原始W2全fieldと同時指定値]
    remaining: []
  certificate_provenance:
    discharged: [元のセル名の六tag, Galoisからのcanonical閉集合代表, 元の非交和のcoherence, Finsupp各有限fiber, M4の実Lawラベルfiberと同じ細逆像]
    unresolved: []
  proof_use:
    used: [全セルmembershipと全三次数制限, 元の部分比較, 旧H1自然同型, 実Law比較正方形, 非bottom添字と多重度, 任意加法的評価の単独blockと有限帰納法]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [3874jobs targeted, 552宣言公理ログ, 上記scan]
  blocking_findings: [独立PRレビュー未実施]
  next_obligation: Fの実錐合成triangleと有限tower/モデルfiltration/逐次商/台とLaw自然性、および全GOAL独立完了監査
```

このresultは独立PR監査へ渡すproposalである。Fと全GOAL最終監査は未完であり、
GOAL active、tracking Issue openを維持する。


### Cycle 5 初回監査と本筋修正

初回 head `9c5ccb1a74f248b8ed838e91ceccf3c32d92c233` は
[標準PR初回監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5267#issuecomment-6004451791)
で `Needs changes / Major revisions`。数学A/LeanAは非中心指摘、数学B/LeanBは
固定W2の実Law値a,bの別直和成分への具体的接続欠落を中心findingとした。
rootは設計witnesses末尾の要求と一次sourceを照合し、初回headのM5結果を
proof-checkpointとして記録する。一般EとW1重複度は当該W2適用を代替しない。
固定target・選定終了条件を維持し、同じcycleの本筋修正で閉じる。

- 中心F1: `WitnessTwoLawMultiplicity` で原始恒等Lawの全三ラベルと元Sourceの全単射、
  ラベルfiber={t}、a≠b、全単独署名の非bottom性を証明する。元のa,bは別active添字であり、
  同じ全セル署名を持つ。実ラベルfiberと二点の全単射から共有多重度2を評価し、
  `fullLawSelected_square/fullLawMultiplicityConeIso` へ同じ実Law/adequacy/原始比較を渡す。
- 非中心F2: module名をnamespaceにしたreport参照を実宣言名へ訂正。
  非bottom実現は `SupportSignature.nonbottomIndicatorConeIso`。
- 非中心F3: W2の原始false chartから `not_selectedLE_a_c` を証明し、
  `selectedLE_refl` の成立例と不成立例を対にする。
- 非中心F4: `coarseLE/fineLE/stageLE/coarsers` は同じ命題と証明のtheoremに変更。
  元の使用premiseをincludeして量化を維持する。
- 非中心F5: `evaluationOfValues_eval/valueSum_eq_sum`、
  `blockIso_hom/iso_hom_apply`、`coarseReconstructionIso_hom/fineReconstructionIso_hom`、
  `h1_subsingleton_of_C1` の基本APIを補い、下流5箇所を公開APIへ接続する。

新規接続のmaterial premiseはW2原始Law/adequacyと原始支持のみであり、
ラベル同値・fiber・非bottom・多重度・別添字・実比較squareはすべて放電する出力である。
補助零H¹ APIのC1零性は一般direction-hypothesis、W2適用では原始edge空から生成する。
本筋修正のため、直接対応ではなくfresh4本の正式再実行で検査する。

### Cycle 5 修正headの検証とresult proposal

rootは `research/lean` から以下の必要な7 targetを同じsourceで検証した。

```text
lake build ResearchLean.AG.AtlasDefectComposition.WitnessTwoLawMultiplicity ResearchLean.AG.AtlasDefectComposition.LawSignatureComparison ResearchLean.AG.AtlasDefectComposition.SupportDefectValue ResearchLean.AG.AtlasDefectComposition.ThreeStageSignatures ResearchLean.AG.AtlasDefectComposition.SupportNonbottomRealization ResearchLean.AG.AtlasDefectComposition.WitnessOneSignatureMultiplicity ResearchLean.AG.AtlasDefectComposition.SignatureQuotient
```

exit 0、3876 jobs。修正headの全44ファイル・579宣言を単一scratchの
`#print axioms` で全件照合し、標準 `propext/Classical.choice/Quot.sound` のみ。
公理ログ SHA-256: `0fe89b43641db23aa5130a92cde80c10c5df7303226711288b758be21aee369d`。
placeholderはLean source 0件、reportの検査項目名2件のみ。hidden/BiDi 0、
privacyは公開PR/Issue参照10件のみ、Formal→Research import 0、diff check clean、
新規禁止語彙0。scan出力 SHA-256: `02481d7b2696935f1758dd6989f784a0c1267e7a18d4873bab168fbf1e22cecd`。

元のCycle 5 selection・終了条件をすべて維持する。Eの全構成とW2の原始Law三成分、
W1の多重度2まで同じ入力から接続した結果を `proof-obligation-discharged` として提案する。
M5の未放電material premiseはない。正式再実行1のfresh4本レビューとroot acceptanceは未実施。
completion candidate: no。次obligationはFと全GOALの独立完了監査である。

## Cycle 5 受理と Cycle 6 selection

M5は [標準正式再実行1](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5267#issuecomment-6004831782)
と [有資格直接対応・root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5267#issuecomment-6004936940)
を経て `proof-obligation-discharged` として受理した。初回W2実Law接続Majorは
同じ原始Lawの三ラベル・a/b別成分・共有多重度2と実全Law比較/錐の構成で解消し、
fresh4本正式再実行1が中心findingなしと確認した。非中心report4箇所は新規単独確認で解消した。
最終head `4b0f87d4ad3b34e3ab938c9a19ceb712092e3999`、PR #5267、
merge `7ac334319fe1a72b2a98fa0f4357493685477af3`、2026-10-05T23:00:28Z。
全8 CI成功、44ファイル579宣言の標準公理監査成功。Issue M5同期は
[merge記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5261#issuecomment-6004978178)にある。
M1–M5受理済み、Fと全GOAL独立完了監査は未完である。

```yaml
ledger_type: target_cycle_result
goal: G-133-aat-atlas-defect-composition
cycle: 6
goal_blob_sha: 8904a7d3bf428e0307499a40be4db1ba9091c51a
base_oid: 7ac334319fe1a72b2a98fa0f4357493685477af3
tracking_issue: 5261
report_path: research/reports/G-133-aat-atlas-defect-composition.md
selection:
  proof_state_ref: Cycle5受理監査・merge・Issue同期と固定GOAL F/設計3.3
  proof_dag_predecessors: [M1原始比較合成, M2実H1六項と相殺, M3零延長と標準錐, M4実Law有限直和, M5全段台署名と実制限]
  milestone: M6の実錐合成triangleと有限多段tower・モデルfiltrationの統合
  proof_obligations:
    - Aの独立生成直接比較をmiddle objectとする標準distinguished triangle
    - 全整数次数の三射成分・shift符号・標準homotopy
    - 任意有限reading列と全隣接原始部分セル比較からの累積比較生成
    - 同じ基底subset逆像族の全段複体と実比較の関手性
    - 累積錐E0のcontractibilityと隣接錐を結ぶ有限tower
    - 各累積錐へのchain homotopy同値を持つ有限次元・有界モデル
    - 零から始まる次数別単射の有限filtrationと逐次cokernelの隣接錐へのchain homotopy同値
    - 全段共通台制限とLaw全発生ラベル分解の自然性
    - 三段特殊化・A–FとWの累積構成対応と全GOAL完了証拠
  exit_criteria:
    - F全量化と全構成を原始入力からLeanで生成し元の射の単射性を仮定しない
    - 指定triangleの三射・符号・台制限・Law分解の対応を証明
    - 任意有限段数n=0を含め実tower・モデル有限filtration・逐次商の同値を証明
    - 三段特殊化と全段共通署名・Law有限直和の対応を証明
    - 対象focused/必要依存targeted・全累積spine公理・scanと標準PR監査を完了
    - 同じ固定headの全GOAL独立4本完了監査とroot再照合を完了
  selection_reason: Fのみが数学条項の未完であり既受理A–E/Wを任意有限比較列の同じ構成へ接続する
  expected_result_type: proof-obligation-discharged
  lean_targets: [ConeCompositionTriangle.lean, MappingCylinderModel.lean, FiniteComparisonChain.lean, CumulativeConeTower.lean, FiniteConeFiltration.lean, ConeFiltrationNaturality.lean]
  risks:
    - 元の累積錐射をそのまま部分複体と宣言しない
    - cochain合成から直接比較を定義して原始比較生成義務を消さない
    - distinguished triangleをH1核余核六項列と混同しない
    - shift負号とtarget/source成分順序を保持する
    - モデル変更の有限次元性と有界性を同じ構成から導く
    - 単射性・手供給exactness/同値/自然性を追加入力にしない
    - 同じ基底subsetと全発生Lawラベルを保持する
  unchecked: [F未実装, 全GOAL完了監査未実施]
```

## Cycle 6：有限単射モデルの部分成果

固定M6の終了条件を維持したまま、独立に再利用できる有限単射モデルを
`proof-checkpoint` として提案する。F全体とG-133全体の完了は未判定である。

原始reading/nerve/隣接セル射から `rawPath` を構成し、隣接射が入力そのものに
一致することを証明した。`lawPathDiagram` と `subsetPathDiagram` は各対で
元の生成手続きを適用し、原始圏の恒等・合成から関手則を導く。
subsetは同じq₀から全段へ引き戻し、初段の逆像を元のsubsetへ戻す同型も構成した。

`compositionTriangle` は独立直接比較をmiddleに保持する。第一射
`(y,x) ↦ (vy,x)`、第二射 `(z,x) ↦ (z,ux)`、三射目のshiftを外した
`−fst(v) ≫ inr(u)`を全整数次数で証明した。二射の合成については
標準inlから `compositionTriangleNullHomotopy` を生成し、chain mapの零等号を入力にしない。
標準distinguished性と反復錐・後段錐のchain homotopy同値へ接続した。

モデルは `Cone(id K) ⊞ L`、包含は `k ↦ ((k,0),φk)`、射影は第二成分である。
指定商射は標準錐への `((z,x),y) ↦ (y−φz,−x)` を持つ実chain mapである。
次数別左逆・右逆と恒等分解から実短完全性を証明し、実cokernelを標準錐へ
普遍性で同定した。射影のchain homotopy同値は恒等錐のcontractibilityから導いた。

累積錐E₀を実零複体に置き換え、各段でこのモデルを反復する。
各包含は全次数で単射であり、実cokernelは隣接錐とchain homotopy同値である。
terminal modelへの合成埋め込みから実Subobjectの有限filtrationを構成し、
初段⊥・終段⊤と単調性、その実隣接包含の実cokernelの同値まで証明した。
段iのモデルは全次数で有限次元、次数−iから2の外で零対象である。
有限段数n=0を含み、元の比較の単射性は仮定しない。

原始diagramの実自然変換は累積錐射・モデル包含・指定射影・指定商射と
可換する。各段モデルと累積錐は恒等・合成・加法を保つ関手になった。
全段共通署名の包含から、同じ原始subset入力のモデルtower制限を生成した。
全Law原始diagramにも同じ有限モデル構成を適用した。

全三射の台制限・Law分解への自然性、全発生ラベルの直和によるモデルの
同定、有限diagramの元の対射への公開同定、三段特殊化、全GOAL完了監査は
未完であり、次cycleへ保持する。既受理A–E/Wの結果は変更していない。

```yaml
ledger_type: target_cycle_result
goal: G-133-aat-atlas-defect-composition
cycle: 6
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta:
    - 独立直接比較triangle・三射符号・標準null homotopy・distinguished性を構成
    - 全有限原始pathと同じq0全subset/全Lawの独立生成diagramを構成
    - E0 contractibilityから零始点の実単射モデルtowerを構成
    - 実Subobject有限filtrationと実隣接cokernelの隣接錐へのhomotopy同値を構成
    - 全次数有限次元性・有限次数範囲を原始三項複体から放電
    - 実モデルの包含・射影・商射の自然性と加法的関手則を放電
  exit_criteria_status:
    - 任意有限段数とn0を含む実モデルfiltration構成は放電
    - 全三射の台制限/Law分解自然性・全Lawラベルモデル分解・三段特殊化は未完
    - 全GOAL独立4本完了監査とroot再照合は未実施
  split_reason: 実原始diagramからの零始点有限単射モデルと実Subobject逐次商の同値が独立に再利用できる定理として完成したため。この部分成果を監査し、元のM6終了条件と残る統合義務を次cycleに保持する
  completion_candidate: no
  lean_artifacts: [下表15module/179public宣言]
  evidence: [compositionTriangle_distinguished, MappingCylinder.cokernelIso, ConeTower.successiveQuotientEquiv, ConeTower.filtrationQuotientEquiv, ConeTower.modelBounded, subsetPathDiagram, lawPathDiagram]
  claim_mapping:
    theorem_names: [下表全public宣言]
    source_labels: [GOAL F, 設計3.3/4/5 M6]
    conjuncts: [実triangle符号/同値, 原始有限diagram, 実単射filtration/逐次商, 有限次元/次数範囲, 指定モデル射の自然性]
    undischarged_assumptions: []
    acceptance_point: 固定M6の部分成果。未完統合義務を保持したproof-checkpoint
    port_status: unported
audits:
  premise_delta:
    discharged: [入力原始比較の圏法則/生成関手則, 全次数単射性, 実短完全性/cokernel普遍性, projection homotopy同値, bounded finite-dimensional model]
    remaining: []
  certificate_provenance:
    discharged: [原始pathとdiagramは原始セル比較から生成, splitting/homotopy/naturalityは実射から証明, ModelStage/ModelStageMap fieldは反復構成内で生成]
    unresolved: []
  proof_use:
    used: [M1全原始合成/独立生成比較, M3標準錐/零延長, M5全段共通署名/実制限, mathlib標準triangle/contractibility, 実次数分裂/普遍性]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [次節検証・正式PR監査待ち]
  blocking_findings: []
  next_obligation: 元のM6終了条件を維持し全三射自然性・全Lawモデル分解・元の有限対射同定・三段特殊化・独立完了監査を続ける
```

### Cycle 6宣言spine

Lean環境のmodule provenanceから抽出した15module/179public宣言を列挙する。
生成されたstructure constructor/accessorと旧名のdeprecated aliasも含む。
全累積spineは134module/1529宣言である。

| module | public declaration |
| --- | --- |
| [BoundedConeModels](../../research/lean/ResearchLean/AG/AtlasDefectComposition/BoundedConeModels.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.coneBounded`<br>`AAT.AG.AtlasDefectComposition.ConeTower.coneFiniteDimensional`<br>`AAT.AG.AtlasDefectComposition.ConeTower.cone_bounded`<br>`AAT.AG.AtlasDefectComposition.ConeTower.cone_finite_dimensional`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelBounded`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelFiniteDimensional`<br>`AAT.AG.AtlasDefectComposition.ConeTower.model_bounded`<br>`AAT.AG.AtlasDefectComposition.ConeTower.model_finite_dimensional`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.degree_isZero` |
| [ConeCompositionHomotopy](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeCompositionHomotopy.lean) | `AAT.AG.AtlasDefectComposition.compositionTriangleNullHomotopy`<br>`AAT.AG.AtlasDefectComposition.compositionTriangle_third` |
| [ConeCompositionTriangle](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeCompositionTriangle.lean) | `AAT.AG.AtlasDefectComposition.compositionTriangle`<br>`AAT.AG.AtlasDefectComposition.compositionTriangleConeEquiv`<br>`AAT.AG.AtlasDefectComposition.compositionTriangle_distinguished`<br>`AAT.AG.AtlasDefectComposition.compositionTriangle_eq`<br>`AAT.AG.AtlasDefectComposition.compositionTriangle_first`<br>`AAT.AG.AtlasDefectComposition.compositionTriangle_mor₁`<br>`AAT.AG.AtlasDefectComposition.compositionTriangle_second` |
| [ConeHomotopyTransport](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeHomotopyTransport.lean) | `AAT.AG.AtlasDefectComposition.coneMapHomotopyEquiv`<br>`AAT.AG.AtlasDefectComposition.homotopyEquivOfIsIsoMap` |
| [ConeModelFunctors](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeModelFunctors.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.coneFunctor`<br>`AAT.AG.AtlasDefectComposition.ConeTower.coneFunctor_additive`<br>`AAT.AG.AtlasDefectComposition.ConeTower.coneMap_add`<br>`AAT.AG.AtlasDefectComposition.ConeTower.coneMap_comp`<br>`AAT.AG.AtlasDefectComposition.ConeTower.coneMap_id`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelFunctor`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelFunctor_additive`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelMap_add`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelMap_comp`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelMap_id` |
| [CumulativeConeNaturality](../../research/lean/ResearchLean/AG/AtlasDefectComposition/CumulativeConeNaturality.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.casesOn`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.ctorIdx`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.hom`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.mk`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.mk.inj`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.mk.injEq`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.mk.noConfusion`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.mk.sizeOf_spec`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.noConfusion`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.noConfusionType`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.rec`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.recOn`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStageMap.square`<br>`AAT.AG.AtlasDefectComposition.ConeTower.augmentation_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.coneMap`<br>`AAT.AG.AtlasDefectComposition.ConeTower.inclusion_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelArrow_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelMap`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelMap_succ`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelMap_zero`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelNatTrans`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotient_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.stageMap`<br>`AAT.AG.AtlasDefectComposition.ConeTower.step_natural` |
| [CumulativeConeTower](../../research/lean/ResearchLean/AG/AtlasDefectComposition/CumulativeConeTower.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.ModelStage`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.casesOn`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.complex`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.ctorIdx`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.equivalence`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.mk`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.mk.inj`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.mk.injEq`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.mk.noConfusion`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.mk.sizeOf_spec`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.noConfusion`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.noConfusionType`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.rec`<br>`AAT.AG.AtlasDefectComposition.ConeTower.ModelStage.recOn`<br>`AAT.AG.AtlasDefectComposition.ConeTower.adjacent`<br>`AAT.AG.AtlasDefectComposition.ConeTower.augmentation`<br>`AAT.AG.AtlasDefectComposition.ConeTower.augmentation_square`<br>`AAT.AG.AtlasDefectComposition.ConeTower.augmentation_zero_hom`<br>`AAT.AG.AtlasDefectComposition.ConeTower.cone`<br>`AAT.AG.AtlasDefectComposition.ConeTower.cumulative`<br>`AAT.AG.AtlasDefectComposition.ConeTower.cumulative_comp`<br>`AAT.AG.AtlasDefectComposition.ConeTower.cumulative_zero`<br>`AAT.AG.AtlasDefectComposition.ConeTower.inclusion`<br>`AAT.AG.AtlasDefectComposition.ConeTower.inclusion_degree_mono`<br>`AAT.AG.AtlasDefectComposition.ConeTower.inclusion_mono`<br>`AAT.AG.AtlasDefectComposition.ConeTower.initialEquiv`<br>`AAT.AG.AtlasDefectComposition.ConeTower.model`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelArrow`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelDiagram`<br>`AAT.AG.AtlasDefectComposition.ConeTower.model_zero`<br>`AAT.AG.AtlasDefectComposition.ConeTower.stage`<br>`AAT.AG.AtlasDefectComposition.ConeTower.step`<br>`AAT.AG.AtlasDefectComposition.ConeTower.stepConeEquiv`<br>`AAT.AG.AtlasDefectComposition.ConeTower.step_eq`<br>`AAT.AG.AtlasDefectComposition.ConeTower.successiveQuotientEquiv`<br>`AAT.AG.AtlasDefectComposition.ConeTower.triangle`<br>`AAT.AG.AtlasDefectComposition.ConeTower.triangle_distinguished`<br>`AAT.AG.AtlasDefectComposition.ConeTower.zeroContractible` |
| [FiniteConeFiltration](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteConeFiltration.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.clamp`<br>`AAT.AG.AtlasDefectComposition.ConeTower.embedding`<br>`AAT.AG.AtlasDefectComposition.ConeTower.embedding_mono`<br>`AAT.AG.AtlasDefectComposition.ConeTower.extend`<br>`AAT.AG.AtlasDefectComposition.ConeTower.extend_obj`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtration`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationInclusion`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationInclusion_eq`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientEquiv`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtration_last`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtration_monotone`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtration_zero`<br>`AAT.AG.AtlasDefectComposition.ConeTower.modelDiagram_map_mono` |
| [FiniteModelApplication](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteModelApplication.lean) | `AAT.AG.AtlasDefectComposition.lawFiltrationQuotientEquiv`<br>`AAT.AG.AtlasDefectComposition.lawModelFiltration`<br>`AAT.AG.AtlasDefectComposition.lawModel_finiteDimensional`<br>`AAT.AG.AtlasDefectComposition.lawModel_isZero`<br>`AAT.AG.AtlasDefectComposition.lawTowerInput`<br>`AAT.AG.AtlasDefectComposition.lawTowerInput_finiteDimensional`<br>`AAT.AG.AtlasDefectComposition.lawTowerInput_isZero`<br>`AAT.AG.AtlasDefectComposition.subsetFiltrationQuotientEquiv`<br>`AAT.AG.AtlasDefectComposition.subsetModelEquiv`<br>`AAT.AG.AtlasDefectComposition.subsetModelFiltration`<br>`AAT.AG.AtlasDefectComposition.subsetModelRestriction`<br>`AAT.AG.AtlasDefectComposition.subsetModel_finiteDimensional`<br>`AAT.AG.AtlasDefectComposition.subsetModel_isZero`<br>`AAT.AG.AtlasDefectComposition.subsetTowerInput`<br>`AAT.AG.AtlasDefectComposition.subsetTowerInput_finiteDimensional`<br>`AAT.AG.AtlasDefectComposition.subsetTowerInput_isZero` |
| [FiniteRawPath](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteRawPath.lean) | `AAT.AG.AtlasDefectComposition.lawPathDiagram`<br>`AAT.AG.AtlasDefectComposition.pathAdequate`<br>`AAT.AG.AtlasDefectComposition.pathCoarser`<br>`AAT.AG.AtlasDefectComposition.rawPath`<br>`AAT.AG.AtlasDefectComposition.rawPath_adjacent`<br>`AAT.AG.AtlasDefectComposition.rawPath_obj` |
| [FiniteSubsetPath](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteSubsetPath.lean) | `AAT.AG.AtlasDefectComposition.pathNerves`<br>`AAT.AG.AtlasDefectComposition.pathReadings`<br>`AAT.AG.AtlasDefectComposition.path_initial_preimage`<br>`AAT.AG.AtlasDefectComposition.subsetPathDiagram`<br>`AAT.AG.AtlasDefectComposition.subsetPathInitialIso`<br>`AAT.AG.AtlasDefectComposition.subsetPathRestriction` |
| [MappingCylinderModel](../../research/lean/ResearchLean/AG/AtlasDefectComposition/MappingCylinderModel.lean) | `AAT.AG.AtlasDefectComposition.MappingCylinder.cokernelIso`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.degreeFiniteDimensional`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.degreeRetraction`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.degreeSection`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.degreeSplitting`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.factorization`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.inclusion`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.inclusion_degreeRetraction`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.inclusion_degree_mono`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.inclusion_mono`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.inclusion_quotient`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.model`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.projection`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.projectionHomotopyEquiv`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.quotient`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.shortComplex`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.shortExact`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.short_exact` |
| [MappingCylinderNaturality](../../research/lean/ResearchLean/AG/AtlasDefectComposition/MappingCylinderNaturality.lean) | `AAT.AG.AtlasDefectComposition.MappingCylinder.inclusion_natural`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.map`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.map_add`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.map_comp`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.map_id`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.projection_natural`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.quotient_natural` |
| [RawComparisonCategory](../../research/lean/ResearchLean/AG/AtlasDefectComposition/RawComparisonCategory.lean) | `AAT.AG.AtlasDefectComposition.RawResolution`<br>`AAT.AG.AtlasDefectComposition.RawResolution.Hom`<br>`AAT.AG.AtlasDefectComposition.RawResolution.casesOn`<br>`AAT.AG.AtlasDefectComposition.RawResolution.compose`<br>`AAT.AG.AtlasDefectComposition.RawResolution.ctorIdx`<br>`AAT.AG.AtlasDefectComposition.RawResolution.identity`<br>`AAT.AG.AtlasDefectComposition.RawResolution.mk`<br>`AAT.AG.AtlasDefectComposition.RawResolution.mk.inj`<br>`AAT.AG.AtlasDefectComposition.RawResolution.mk.injEq`<br>`AAT.AG.AtlasDefectComposition.RawResolution.mk.noConfusion`<br>`AAT.AG.AtlasDefectComposition.RawResolution.mk.sizeOf_spec`<br>`AAT.AG.AtlasDefectComposition.RawResolution.nerve`<br>`AAT.AG.AtlasDefectComposition.RawResolution.noConfusion`<br>`AAT.AG.AtlasDefectComposition.RawResolution.noConfusionType`<br>`AAT.AG.AtlasDefectComposition.RawResolution.reading`<br>`AAT.AG.AtlasDefectComposition.RawResolution.rec`<br>`AAT.AG.AtlasDefectComposition.RawResolution.recOn`<br>`AAT.AG.AtlasDefectComposition.rawResolutionCategory` |
| [SubsetComparisonIdentity](../../research/lean/ResearchLean/AG/AtlasDefectComposition/SubsetComparisonIdentity.lean) | `AAT.AG.AtlasDefectComposition.comparisonFactor_self`<br>`AAT.AG.AtlasDefectComposition.identity_targetSubsetComparisonHom` |

### Cycle 6検証

rootが必要な単一非aggregate target
`ResearchLean.AG.AtlasDefectComposition.FiniteModelApplication` をbuildし、
3832 jobsで成功した。このtargetの依存として新規15moduleをelaborateした。
Research全体・aggregate root・全file再elaborationは実行していない。

既受理分を含む134moduleのcompiled metadataから累積1518宣言を抽出し、
単一scratchで全件の `#print axioms` を照合した。1518/1518件、欠落・余分・
エラー・標準外公理は零件。46宣言は公理非依存、残りは
`propext` / `Classical.choice` / `Quot.sound` の範囲である。
公理監査log SHA-256:
`ef71bd73fbc28302bb26ed31e75306a489b9bf9ca61452e72b5f5dab846838e7`。

新規Lean sourceのplaceholder、hidden/BiDi、privacy、語彙scanと
Formal本線からResearchへのimport scanは検出なし。reportの既存操作名
に含まれる英語 `axiom` はLean宣言ではない。変更は15ResearchLean moduleと
本reportに限る。正式PRレビュー・root acceptance・CI・merge同期は
固定headのPR監査コメントとtracking Issueに記録する。

検証の限界: 全三射自然性・全Lawモデル直和・元の有限対射同定・三段特殊化・
全GOAL完了監査は未実施。Formal移植とArchSig実装は本cycleの対象外である。

### Cycle 6公開API整備

標準PR査読が名指しした公開APIとして `MappingCylinder.map_add`、
`compositionTriangle_mor₁`、`ConeTower.step_eq`、`model_zero`、
`augmentation_zero_hom`、`modelMap_zero/modelMap_succ` を追加した。
下流の恒等・合成・加法証明はこれらの式を使い、別moduleのモデル値を展開しない。
`stageMap` の零段は証明field内で指定射影の公開式を使う。計算成分は同じである。

Prop宣言 `pathCoarser/pathAdequate` をtheoremとして登録し、
同じ型・量化・証明を保持した。後者は元の粗adequacy引数を明示的にincludeし、
元のsignatureにないSourceのFintypeを追加しない。
`short_exact`、`cone_finite_dimensional/model_finite_dimensional`、
`cone_bounded/model_bounded` を公開し、元の五定理名もdeprecated指定で保持した。

初回のcompiled metadataにあった `ConeTower.stage.eq_def` は、
`stage` を下流でsimp展開した際の遅延生成宣言である。公開式へ置き換えた後の
metadataでは生成されないため、更新spineから除いた。source宣言の削除、
既存statement・モデル値・instance値・import方向・ledger statusの変更は行っていない。
新規12公開APIを含む更新179宣言と、無変更の受理済み1350宣言を累積対象にする。

更新版の必要単一target buildは3832 jobsで成功した。更新179宣言は
単一scratchの全件 `#print axioms` で標準公理のみ、欠落・余分・エラー零。
新log SHA-256: `55f45d719d8c889acc1ad5f03dee7f4c23281e050aa42960e4657f16ff0cc4de`。
無変更の既受理1350宣言は前節の累積公理logの同名記録を再利用し、
1529宣言の集合と全件標準公理依存を照合した。46宣言は公理非依存。
集合照合した連結log SHA-256: `db0435d06101cbba514baa9e5b4f238091eec46c0742a63f338b00df101ddb05`。
更新spine/追加宣言のscanと差分検査はclean。修正後の資格・解消判定は
固定headのPR監査記録へ追記する。

## Cycle 7 selection：有限多段の全指定射・Law分解・三段接続

```yaml
ledger_type: target_cycle_result
goal: G-133-aat-atlas-defect-composition
cycle: 7
goal_blob_sha: 8904a7d3bf428e0307499a40be4db1ba9091c51a
base_oid: df6a7820b690ba3f366f25be95625f1c1323bf37
tracking_issue: 5261
report_path: research/reports/G-133-aat-atlas-defect-composition.md
selection:
  proof_state_ref: "Issue #5261 Cycle 6受理コメント6006712595、PR #5268最終監査6006687731、report Cycle6"
  proof_dag_predecessors: [M1全原始比較合成, M2全実相殺, M3零延長と標準錐, M4全Law直和, M5全段台署名と制限, Cycle6実有限単射モデルと実逐次商]
  milestone: "元Cycle6のM6全終了条件を維持し、Fの全三射自然性、有限対射同定、全Lawモデルと実商の直和、三段特殊化を閉じる"
  proof_obligations: [clamp延長の元Fin全対射同定, compositionTriangle全三射の自然性, 指定homotopy同値のhomと実cokernelの自然性, 実Subobject包含と商の台制限, 共通署名反対圏の有限diagramとモデル, 同じq0発生ラベルfiberによる全Lawdiagram直和, 全モデル包含と射影と逐次商の直和整合, 原始三段pathと独立生成全比較の一致, A–FとW統合]
  exit_criteria: [任意nをn0込みで元有限全対象全対射へ同定, 任意cochain可換squareでtriangle全三射と指定逐次商射が可換, 任意台包含と全段共通署名で実モデル包含と実商が自然, 全Law発生ラベルを重複のまま全段モデルと全逐次商へ直和同定, 三段T0入力とM1独立原始M02がF構成へ一致, 固定A–F/W全条項と全premiseを累積証拠へ対応, 別独立4本の完了監査で全completion条件確認]
  selection_reason: "受理済み有限filtrationを実比較の全自然性・分解へ接続し、残るFのproof distanceを直接縮める"
  expected_result_type: proof-obligation-discharged
  lean_targets: [FiniteIndexTransport, ConeCompositionNaturality, ConeTowerQuotientNaturality, SubobjectFiltrationNaturality, FiniteSignatureDiagram, LawPathBiproduct, ModelBiproductNaturality, LawFiniteModelDecomposition, LawFiltrationQuotientDecomposition, ThreeStageFinitePath, ThreeStageConeIntegration]
  risks: [直接射を合成で再定義しない, 最後のshift射を省略しない, 原比較Monoを受領しない, Lawラベルを同署名で潰さない, 実cokernelと実Subobjectを抽象値で代替しない, HEと自然性fieldを外部入力にしない]
  unchecked: [全三射自然性, 全Lawモデル直和と実商対応, 有限全対射公開同定, 三段特殊化, 全GOAL独立完了監査]
```

Cycle 6は固定head `0fa7739ddb3d49a08bd1941f8cf8062084f81736`、merge `df6a7820b690ba3f366f25be95625f1c1323bf37` により受理した。初回4本の非中心事項は有資格な新規直接確認で全解消し、[root最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5268#issuecomment-6006687731)と[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5261#issuecomment-6006712595)を保持する。元M6終了条件と全GOAL completion gateは維持する。

### Cycle 7 構成と全target対応

有限原始pathの対象は元のreading・nerveそのもので、全対射は原始圏の
chart/Option edge/Option face合成である。`finiteExtendIso_natural` は
任意の `n` と全 `Fin (n+1)` 射で元diagramへの可換式を与え、零段も含む。

`compositionTriangleMap` は独立な直接射を保持した任意のcochain正方形から
三錐の射を作り、最後のshift射を含む三可換式を生成する。
`compositionTriangleConeEquiv_inv_natural` は標準反復錐の指定射を追い、
`successiveQuotientEquiv_hom_natural` は実cokernelからの指定同値のhomに接続する。
`filtrationMap` は実Subobjectのunderlying同型で元モデル射を移した射である。
実arrow・実ofLE包含・実cokernel map・指定商同値のhomの全可換式を証明した。
これらから加法的関手と自然変換を作り、共通全セル署名の反対圏へ前合成する。

Lawの同定は同じ最初のreadingの各発生ラベルfiberから行う。
`lawPathBiproductIso` は全有限diagramの実同型であり、任意の全対射と可換する。
加法的構成への標準biproduct保存を通して、モデル・累積錐・隣接錐・実モデル商・
実Subobject underlying・実ofLE包含のcokernelへ全ラベルを保持した同型を作る。
包含・augmentation・商射・指定商同値のhom・triangleの全三射は同じ同型の下で直和になる。
同署名の異なるLawラベルを同一視する操作は用いない。

`ThreeStagePath.path_direct` は元の全原始M02合成そのものである。
`law_finite_triangle` は元の独立全Law生成三射への等号、
`lawTowerTriangleIso` はその三錐へ全三射での同型を与える。
subset版は `subset_direct` と `SupportStages.pairComparison_canonical` で
元のaSubnerve生成射を各対の逆像へtransportし、`subsetInitialIso` で初段を
元の同じAへ戻す。`subsetTowerTriangleIso` はその実三錐への同型である。
W1の同じ非定数Law・二つの原始比較へ適用した実filtration商のhomologyは
第一商0,2・第二商2,0・terminalモデル0,0である。
これらは既存の実生成全Law錐の評価と指定homotopy同値から導く。

以下は全固定要求と現在の累積証拠を対応させる。先行cycleの状態記述は
当該cycle時点の記録であり、本節が現時点の証拠対応である。
宣言名は `AAT.AG.AtlasDefectComposition` を共通接頭辞とする。

| 固定要求 | 入力から結論までの実証拠と使用経路 |
| --- | --- |
| T0の同じSource、全原始セル・部分incidence、任意Lawと任意A | 既存 `TargetSupportedNerve` / `TargetSupportedNerveMorphism` を量化。`comparisonComp` は全fieldを生成。`adequate_of_coarser` で細adequacyを導出。`rawPath_obj/rawPath_adjacent` は全有限隣接入力を保持 |
| Aの原始合成・全三次数・H¹、恒等・結合、因子・Law降下・逆像 | `ComparisonComposition/ComparisonLaws/GeneratedComposition/SubsetComposition` のM1全宣言。直接Homは原始合成へ既存生成手続きを適用し、全計算成分の等号からH¹商へ降ろす |
| Bの六対象、全五射、両端、相殺range商、自然数寸法式 | `DefectSequence` と `GeneratedDefect` のM2全構成。実H¹射へM1の直接合成を適用し、代表cocycle・primitiveを `GeneratedDefect` で追う |
| Bの共通A/Lawの恒等・合成・二つから一つの零欠損 | `GeneratedDefect` の実比較族への全方向。途中で別Lawを追加する量化は使わない |
| Cの全整数次数・指定符号順序・既存H¹同型・標準錐 | `ZeroExtension/ComparisonHomology/ConeCoordinates`。零延長の全次数から旧H¹と標準homologyを自然同定 |
| Cの任意mの実短完全列、−1/2端同型、0/1寸法、条件付き追加項消去の両向き | `ConeHomologySequence/ConeExactSequence/ConeNaturality/ConeEndDegrees/ConeConditional`。標準長完全列の実各射から短完全列を構成し、H⁰全射/H²単射の条件は追加項消去にだけ使う |
| Dの同じ発生ラベルfiber、実比較・H¹・核余核・錐・短完全列 | `LawFiberDecomposition/LawStandardDecomposition/LawDefectDecomposition/LawConeDecomposition/LawSubsetConeDecomposition`。元の全ラベル同値と比較正方形を各実構成へ渡す |
| Dの六項全射・χ・相殺rank・欠損和 | `LawSixTermDecomposition/LawFiberSixTermDecomposition/LawStandardDimensions`。全五射のcomponent等号、実range同値からrank和を得る |
| Dの非空Aの指示Lawtrue block、空A零、補集合との区別 | `IndicatorSelectedBlock/EmptySubset` と `LawFiberDecomposition`。単独blockだけをAへ同定し、全Lawの別blockは保持 |
| Eの六側次数タグ・元セル、α/γ・閉包・join・bottom・quotient/image/Fix同型 | `SupportSignature/SignatureGeometry/SignatureQuotient/SignatureUniversal` 系のM5宣言。元セル選択の全六成分から同じ署名を作り、subset quotientとimage/Fixを同定 |
| Eのdecoder対象全射pと全セル復元d、終対象と通常商の一意因子化 | `SignatureUniversal` 系。実対象・射のbottom/join・二可換条件を保つ。診断値だけのdecoderに差し替えない |
| EのLaw有限block族、active全単射射、零block削除、重複度、加法的普遍性 | `SelectedFamilies/FiniteFamilyReindex/FiniteFamilyZeroDeletion/LawSignatureComparison/LawSignatureRestoration/SelectedFamilyFreeMonoid/SelectedFamilyUniversal` 系。ラベルをactive添字に保持し、同署名でも多重和を保持 |
| EのΣop複体・比較・錐・H¹核余核と三段のB全射自然性 | `SupportFunctor/SupportConeFunctor/SupportDefectFunctor/SupportStageComparison/SupportStageSixTerm`。実セル制限から各関手を構成、共通全段署名でχを含む五射が可換 |
| Fの実三錐triangle・distinguished・式と符号・全三射自然性 | `ConeCompositionTriangle/ConeCompositionHomotopy/ConeCompositionNaturality`。元の直接射を保持して標準triangleをtransportし、任意可換squareで最後のshift射まで証明 |
| Fの任意有限段n0込み・元の全対射・累積/隣接錐tower | `FiniteRawPath/FiniteSubsetPath/FiniteIndexTransport/CumulativeConeTower`。原始圏から独立生成した全pairへ有限延長の自然同型を適用 |
| Fの零始点有限次数FDモデル・実Mono包含・実Subobject filtration・実逐次商HE | `MappingCylinderModel/BoundedConeModels/FiniteConeFiltration/FiniteModelApplication`。元の射のMonoを受け取らず、mapping cylinderのdegree retractionからMonoを導出し、実cokernelを隣接錐へHE同定 |
| Fの台制限と全指定商射、共通署名反対圏 | `ConeTowerQuotientNaturality/SubobjectFiltrationNaturality/FiltrationNaturalFunctors/FiniteSignatureDiagram`。実arrow・包含・商射・指定HE homを同じ元の制限でtransport |
| Fの全Lawモデル/実filter/実商の直和と全指定射、三段特殊化 | `LawPathBiproduct/LawFiniteModelDecomposition/LawFiltrationQuotientDecomposition/ThreeStageFinitePath/ThreeStageConeIntegration`。同じq0各fiber図式の実biproduct同型と加法的自然性を全三射へ適用 |
| W1の真の三reading・非定数Law・実非零H¹/χ・primitive・0,1/1,0/0,0・全二ラベル | `WitnessOneInput/WitnessOneComparison/WitnessOnePeriods/WitnessOneCancellation/WitnessOneFullLaw/WitnessOneCones/WitnessOneFullLawCones/WitnessOneSignatureMultiplicity`。元セル表→既存生成比較→実類/実商→非零χ/rank1、全Lawrank2と次元2/4/2。`WitnessOneFiniteModels` は同じ原始入力へFを適用 |
| W2の同じ全原始入力で異署名同零J・同署名異subset・真の閉包・四署名・実Law同署名二ラベル | `WitnessTwoInput/WitnessTwoGeometry/WitnessTwoTargets/WitnessTwoLawMultiplicity`。Fin3の指定台{0,1}/{2}、恒等全原始比較。実Lawラベルa/bの相違・同署名・多重度2を同時に評価 |
| W3aのH¹零とH⁰余核、W3bのH¹零とH²核、全錐次数寄与 | `WitnessThreeInput/WitnessThreeNamed/WitnessThreeRanks/WitnessThreeActual/WitnessThreeConeA/WitnessThreeConeB/WitnessThreeConeRanks/WitnessThreeFullLaw`。隔離二chartへの実比較とtetrahedron→filled triangleの実全cell比較を生成し、追加寄与1と他次数0を計算 |

### Cycle 7 material premiseとDAG

| premise | 分類と状態 | 生成元・proof-use |
| --- | --- | --- |
| 有限Source・全射reading・有限支持nerve・原始部分incidence・q0 Law adequacy・全subset | T0由来 `ambient-boundary` / `justified-boundary` | RawResolutionと既存生成関数、全対diagramで使用。Wでは原始表とSource証人から全fieldを構成 |
| 細Law adequacy、発生ラベルと有限次元性 | `discharge-required` / `discharged` | `adequate_of_coarser/pathAdequate`、Source有限性→実発生label、元のfinite cell座標→旧H¹/全整数次数FD→有限model |
| 全原始M02・Hom/H¹合成、subset/Law transport | `discharge-required` / `discharged` | M1全field→生成全成分→商。finitePath全pairと `law_direct_comp` の入力へ使用 |
| B全exactness・χ・代表primitive・range商・寸法 | `discharge-required` / `discharged` | M2の実linear quotient構成と実生成比較への同定。Law全射直和とW1非零類に使用 |
| C全次数標準錐・H¹同定・SES・端同型 | `discharge-required` / `discharged` | M3零延長と標準長完全列、M4自然なLaw分解、Fの三錐とW3追加項に使用 |
| H⁰全射・H²単射 | C追加項消去だけの `direction-hypothesis` / `justified-boundary` | `ConeConditional` のiff。一般T0に追加せず、W1では `full_extra_terms_zero`、W3では非零追加項を実証 |
| 全Lawblock・同fiber複体/射・全直和と重複度 | `discharge-required` / `discharged` | M4実同型→M5activeラベル族→Cycle7全有限diagram同型と加法的biproduct保存→全指定射 |
| 全cell署名・Galois/閉包/quotient・decoder二普遍性・Law加法評価 | `discharge-required` / `discharged` | M5実cell選択と有限join構成。decoderは全cell選択復元がEで許された対象条件であり、結論供給ではない |
| 全triangle・HE・モデルMono・有限次数・実filter・実cokernel | `discharge-required` / `discharged` | 標準符号三角/標準指定反復錐HE→mapping cylinder実retraction→帰納モデル→実Mono→Subobject/ofLE/cokernel→隣接錐HE。ModelStageのequivalence fieldもstageの再帰で生成 |
| 台restriction/同署名transport、Law全指定射自然性 | `discharge-required` / `discharged` | 元セル制限の実平方→任意diagram自然変換→モデル/実filter/実商の指定式→全三射/指定HE homの可換式 |
| 三段とW1–W3の原始入力・指定非自明性・同時評価 | `discharge-required` / `discharged` | 各Witness入力moduleから実生成比較と既存商を追う。W1商モデルの0,2/2,0/0,0は元の同じ実錐評価を使用 |

受理済みDAGの参照版とreview refsは各cycle節にある。
G-104/G-107/G-132の再利用箇所は設計reuse-mapの指定に従い、現在の
statement・必要定義・適用引数を照合する。Lean4.28.0、mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365` の標準APIを使用する。
今回のspineに未放電数学premiseを申告していない。全GOAL完了の認定は
固定headの標準PR査読と別の独立4本完了査読の結果を待つ。
Formal移植は `unported (Research-proved)`、ArchSigへの対応実装は別作業である。

### Cycle 7宣言spine

compiled module provenanceで新規18moduleと先行10moduleへの公開API追加を抽出した。
追加spineは192宣言、全累積spineは152module/1721宣言である。
先行宣言のstatementと構成値を変更せず、指定射・projectionのAPIを追加した。
全宣言の公理監査はこの累積リスト全件を対象にする。

| module | 追加public declaration |
| --- | --- |
| [ComparisonComposition](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ComparisonComposition.lean) | `AAT.AG.ResolutionInvariance.comparisonFactor.congr_simp`<br>`AAT.AG.ResolutionInvariance.lawDescend.congr_simp` |
| [ConeCompositionEquivNaturality](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeCompositionEquivNaturality.lean) | `AAT.AG.AtlasDefectComposition.compositionConeEquiv_inv_natural`<br>`AAT.AG.AtlasDefectComposition.compositionTriangleConeEquiv_inv_natural` |
| [ConeCompositionNaturality](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeCompositionNaturality.lean) | `AAT.AG.AtlasDefectComposition.compositionTriangleMap`<br>`AAT.AG.AtlasDefectComposition.compositionTriangle_first_natural`<br>`AAT.AG.AtlasDefectComposition.compositionTriangle_second_natural`<br>`AAT.AG.AtlasDefectComposition.compositionTriangle_third_natural`<br>`AAT.AG.AtlasDefectComposition.composition_direct_square` |
| [ConeCompositionTriangle](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeCompositionTriangle.lean) | `AAT.AG.AtlasDefectComposition.compositionTriangle_mor₂`<br>`AAT.AG.AtlasDefectComposition.compositionTriangle_mor₃` |
| [ConeHomotopyTransport](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeHomotopyTransport.lean) | `AAT.AG.AtlasDefectComposition.coneMapHomotopyEquiv_hom` |
| [ConeTowerNaturalFunctors](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeTowerNaturalFunctors.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.adjacentConeFunctor`<br>`AAT.AG.AtlasDefectComposition.ConeTower.adjacentConeFunctor_additive`<br>`AAT.AG.AtlasDefectComposition.ConeTower.adjacentConeMap_add`<br>`AAT.AG.AtlasDefectComposition.ConeTower.adjacentConeMap_comp`<br>`AAT.AG.AtlasDefectComposition.ConeTower.adjacentConeMap_id`<br>`AAT.AG.AtlasDefectComposition.ConeTower.augmentationNatTrans`<br>`AAT.AG.AtlasDefectComposition.ConeTower.inclusionNatTrans`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotientEquivNatTrans`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotientFunctor`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotientFunctor_additive`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotientMap_add`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotientMap_comp`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotientMap_id`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotientProjectionNatTrans`<br>`AAT.AG.AtlasDefectComposition.ConeTower.triangleFirstNatTrans`<br>`AAT.AG.AtlasDefectComposition.ConeTower.triangleSecondNatTrans`<br>`AAT.AG.AtlasDefectComposition.ConeTower.triangleThirdNatTrans` |
| [ConeTowerQuotientNaturality](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeTowerQuotientNaturality.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.modelCone_augmentation_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotientMap`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotientMap_π`<br>`AAT.AG.AtlasDefectComposition.ConeTower.quotientMap_π_assoc`<br>`AAT.AG.AtlasDefectComposition.ConeTower.stepConeEquiv_hom_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.successiveQuotientEquiv_hom_natural`<br>`AAT.AG.AtlasDefectComposition.MappingCylinder.cokernelIso_natural` |
| [ConeTowerTriangleNaturality](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ConeTowerTriangleNaturality.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.adjacentConeMap`<br>`AAT.AG.AtlasDefectComposition.ConeTower.triangleMap`<br>`AAT.AG.AtlasDefectComposition.ConeTower.triangle_first_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.triangle_second_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.triangle_third_natural` |
| [CumulativeConeNaturality](../../research/lean/ResearchLean/AG/AtlasDefectComposition/CumulativeConeNaturality.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.modelNatTrans_app` |
| [CumulativeConeTower](../../research/lean/ResearchLean/AG/AtlasDefectComposition/CumulativeConeTower.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.stepConeEquiv_hom`<br>`AAT.AG.AtlasDefectComposition.ConeTower.successiveQuotientEquiv_hom` |
| [FiltrationNaturalFunctors](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiltrationNaturalFunctors.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.filtrationInclusionNatTrans`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationMap_add`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationMap_comp`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationMap_id`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientEquivNatTrans`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientFunctor`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientFunctor_additive`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientMap_add`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientMap_comp`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientMap_id`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientMap_π`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientMap_π_assoc`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientProjectionNatTrans`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationStageFunctor`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationStageFunctor_additive` |
| [FiniteComplexFamily](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteComplexFamily.lean) | `AAT.AG.AtlasDefectComposition.FiniteComplexFamily.iso_hom`<br>`AAT.AG.AtlasDefectComposition.FiniteComplexFamily.iso_natural`<br>`CategoryTheory.Limits.isBilimitOfPreserves.congr_simp` |
| [FiniteConeFiltration](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteConeFiltration.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientEquiv_hom`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtration_arrow` |
| [FiniteDiagramBiproduct](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteDiagramBiproduct.lean) | `AAT.AG.AtlasDefectComposition.FiniteComplexFamily.diagram`<br>`AAT.AG.AtlasDefectComposition.FiniteComplexFamily.diagramBiproductComponentIso`<br>`AAT.AG.AtlasDefectComposition.FiniteComplexFamily.diagramBiproductComponentIso_projection`<br>`AAT.AG.AtlasDefectComposition.FiniteComplexFamily.diagramBiproductIso`<br>`AAT.AG.AtlasDefectComposition.FiniteComplexFamily.diagram_map`<br>`AAT.AG.AtlasDefectComposition.FiniteComplexFamily.diagram_obj`<br>`AAT.AG.AtlasDefectComposition.FiniteComplexFamily.instHasBiproductFunctorCochainComplexModuleCatRatInt_researchLean`<br>`AAT.AG.AtlasDefectComposition.FiniteComplexFamily.instPreservesBiproductFunctorCochainComplexModuleCatRatIntObjEvaluation_researchLean` |
| [FiniteIndexTransport](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteIndexTransport.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.extendFunctor`<br>`AAT.AG.AtlasDefectComposition.ConeTower.extendFunctor_additive`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteClampIso`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteExtendIso`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteExtendIso_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteIndex`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteModelFunctor` |
| [FiniteRawPath](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteRawPath.lean) | `AAT.AG.AtlasDefectComposition.lawPathDiagram_map`<br>`AAT.AG.AtlasDefectComposition.lawPathDiagram_obj` |
| [FiniteSignatureDiagram](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteSignatureDiagram.lean) | `AAT.AG.AtlasDefectComposition.PathSignature`<br>`AAT.AG.AtlasDefectComposition.signatureAdjacentConeFunctor`<br>`AAT.AG.AtlasDefectComposition.signatureAugmentation`<br>`AAT.AG.AtlasDefectComposition.signatureConeFunctor`<br>`AAT.AG.AtlasDefectComposition.signatureFiltrationInclusion`<br>`AAT.AG.AtlasDefectComposition.signatureFiltrationQuotientEquivalence`<br>`AAT.AG.AtlasDefectComposition.signatureFiltrationQuotientFunctor`<br>`AAT.AG.AtlasDefectComposition.signatureFiltrationStageFunctor`<br>`AAT.AG.AtlasDefectComposition.signatureInclusion`<br>`AAT.AG.AtlasDefectComposition.signatureModelFunctor`<br>`AAT.AG.AtlasDefectComposition.signaturePathDiagram`<br>`AAT.AG.AtlasDefectComposition.signatureQuotientEquivalence`<br>`AAT.AG.AtlasDefectComposition.signatureQuotientFunctor`<br>`AAT.AG.AtlasDefectComposition.subsetPathSameSignatureIso`<br>`AAT.AG.AtlasDefectComposition.subsetPathSignatureIso` |
| [FiniteSubsetPath](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteSubsetPath.lean) | `AAT.AG.AtlasDefectComposition.subsetPathDiagram_map`<br>`AAT.AG.AtlasDefectComposition.subsetPathDiagram_obj`<br>`AAT.AG.AtlasDefectComposition.subsetPathRestriction_app`<br>`AAT.AG.AtlasDefectComposition.subsetPathRestriction_comp`<br>`AAT.AG.AtlasDefectComposition.subsetPathRestriction_id` |
| [FiniteThreeStageTriangle](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FiniteThreeStageTriangle.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.finiteDirect`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteFirst`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteInitialIso`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteLastIso`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteMiddleIso`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteSecond`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteTowerTriangleIso`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finiteTriangle`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finite_direct_comp`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finite_direct_square`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finite_first_square`<br>`AAT.AG.AtlasDefectComposition.ConeTower.finite_second_square` |
| [FullSupportBlocks](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FullSupportBlocks.lean) | `AAT.AG.AtlasDefectComposition.fullBlockCoordinateEquiv.congr_simp` |
| [FullSupportGraph](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FullSupportGraph.lean) | `AAT.AG.AtlasDefectComposition.fullBlockCochainEquiv.congr_simp` |
| [FullSupportPullback](../../research/lean/ResearchLean/AG/AtlasDefectComposition/FullSupportPullback.lean) | `AAT.AG.AtlasDefectComposition.fullBlock_pullback1_none`<br>`AAT.AG.AtlasDefectComposition.fullBlock_pullback1_some` |
| [LawFiltrationQuotientDecomposition](../../research/lean/ResearchLean/AG/AtlasDefectComposition/LawFiltrationQuotientDecomposition.lean) | `AAT.AG.AtlasDefectComposition.instHasBiproductLawValueLabelCochainComplexModuleCatRatIntCompFunctorFinHAddNatOfNatObjLawLabelPathDiagram_1`<br>`AAT.AG.AtlasDefectComposition.lawFiltrationQuotientSumIso`<br>`AAT.AG.AtlasDefectComposition.lawFiltrationStageSumIso`<br>`AAT.AG.AtlasDefectComposition.law_filtration_inclusion_sum`<br>`AAT.AG.AtlasDefectComposition.law_filtration_quotient_equivalence_sum`<br>`AAT.AG.AtlasDefectComposition.law_filtration_quotient_projection_sum` |
| [LawFiniteModelDecomposition](../../research/lean/ResearchLean/AG/AtlasDefectComposition/LawFiniteModelDecomposition.lean) | `AAT.AG.AtlasDefectComposition.instHasBiproductLawValueLabelCochainComplexModuleCatRatIntCompFunctorFinHAddNatOfNatObjLawLabelPathDiagram`<br>`AAT.AG.AtlasDefectComposition.instHasBiproductLawValueLabelFunctorFinHAddNatOfNatCochainComplexModuleCatRatIntLawLabelPathDiagram_1`<br>`AAT.AG.AtlasDefectComposition.lawAdjacentConeSumIso`<br>`AAT.AG.AtlasDefectComposition.lawConeSumIso`<br>`AAT.AG.AtlasDefectComposition.lawConstructionSumIso`<br>`AAT.AG.AtlasDefectComposition.lawConstructionSumIso_natural`<br>`AAT.AG.AtlasDefectComposition.lawConstructionSumIso_projection`<br>`AAT.AG.AtlasDefectComposition.lawModelSumIso`<br>`AAT.AG.AtlasDefectComposition.lawPathProjection`<br>`AAT.AG.AtlasDefectComposition.lawQuotientSumIso`<br>`AAT.AG.AtlasDefectComposition.law_model_augmentation_sum`<br>`AAT.AG.AtlasDefectComposition.law_model_inclusion_sum`<br>`AAT.AG.AtlasDefectComposition.law_quotient_equivalence_sum`<br>`AAT.AG.AtlasDefectComposition.law_quotient_projection_sum`<br>`AAT.AG.AtlasDefectComposition.law_triangle_first_sum`<br>`AAT.AG.AtlasDefectComposition.law_triangle_second_sum`<br>`AAT.AG.AtlasDefectComposition.law_triangle_third_sum` |
| [LawPathBiproduct](../../research/lean/ResearchLean/AG/AtlasDefectComposition/LawPathBiproduct.lean) | `AAT.AG.AtlasDefectComposition.instHasBiproductLawValueLabelFunctorFinHAddNatOfNatCochainComplexModuleCatRatIntLawLabelPathDiagram`<br>`AAT.AG.AtlasDefectComposition.lawLabelPathDiagram`<br>`AAT.AG.AtlasDefectComposition.lawPathBiproductIso`<br>`AAT.AG.AtlasDefectComposition.lawPathBiproductIso_natural`<br>`AAT.AG.AtlasDefectComposition.lawPathBlockIso`<br>`AAT.AG.AtlasDefectComposition.lawPathBlockIso_natural`<br>`AAT.AG.AtlasDefectComposition.lawPathFamilyIso`<br>`AAT.AG.AtlasDefectComposition.lawPathFamilyIso_natural`<br>`AAT.AG.AtlasDefectComposition.lawPathFamilyNatIso` |
| [MappingCylinderModel](../../research/lean/ResearchLean/AG/AtlasDefectComposition/MappingCylinderModel.lean) | `AAT.AG.AtlasDefectComposition.MappingCylinder.cokernelIso_π_hom` |
| [ModelBiproductNaturality](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ModelBiproductNaturality.lean) | `AAT.AG.AtlasDefectComposition.additiveSumIso`<br>`AAT.AG.AtlasDefectComposition.additiveSumIso.congr_simp`<br>`AAT.AG.AtlasDefectComposition.additiveSumIso_natural`<br>`AAT.AG.AtlasDefectComposition.additiveSumIso_projection` |
| [ShortExactFiveConditions](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ShortExactFiveConditions.lean) | `AAT.AG.AtlasDefectComposition.ShortExactFive.projection.congr_simp` |
| [SubobjectFiltrationNaturality](../../research/lean/ResearchLean/AG/AtlasDefectComposition/SubobjectFiltrationNaturality.lean) | `AAT.AG.AtlasDefectComposition.ConeTower.embedding_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationInclusion_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationMap`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationMap_arrow`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientEquiv_hom_natural`<br>`AAT.AG.AtlasDefectComposition.ConeTower.filtrationQuotientMap` |
| [SubsetComposition](../../research/lean/ResearchLean/AG/AtlasDefectComposition/SubsetComposition.lean) | `AAT.AG.ResolutionInvariance.TargetSupportedNerveMorphism.targetSubsetPullback0.congr_simp` |
| [SupportStageSignatures](../../research/lean/ResearchLean/AG/AtlasDefectComposition/SupportStageSignatures.lean) | `AAT.AG.AtlasDefectComposition.SupportStages.stageRestriction_comp`<br>`AAT.AG.AtlasDefectComposition.SupportStages.stageRestriction_id` |
| [ThreeStageConeIntegration](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ThreeStageConeIntegration.lean) | `AAT.AG.AtlasDefectComposition.ThreeStagePath.lawTowerTriangleIso`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.law_direct_comp`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.law_finite_triangle`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.subsetInitialIso`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.subsetTowerTriangleIso` |
| [ThreeStageFinitePath](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ThreeStageFinitePath.lean) | `AAT.AG.AtlasDefectComposition.ThreeStagePath.law_direct`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.path`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.path_direct`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.path_first`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.path_nerves`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.path_readings`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.path_second`<br>`AAT.AG.AtlasDefectComposition.ThreeStagePath.subset_direct` |
| [WitnessOneFiniteModels](../../research/lean/ResearchLean/AG/AtlasDefectComposition/WitnessOneFiniteModels.lean) | `AAT.AG.AtlasDefectComposition.WitnessOne.finiteFiltration`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finiteFirstQuotientEquiv`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finitePath`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finiteQuotientLawSumIso`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finiteSecondQuotientEquiv`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finiteTerminalEquiv`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finiteTower`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finiteTriangleIso`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finite_adjacent_second`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finite_cumulative_direct`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finite_cumulative_first`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finite_first_quotient_dimensions`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finite_second_quotient_dimensions`<br>`AAT.AG.AtlasDefectComposition.WitnessOne.finite_terminal_dimensions` |
| [ZeroExtension](../../research/lean/ResearchLean/AG/AtlasDefectComposition/ZeroExtension.lean) | `CategoryTheory.ShortComplex.LeftHomologyMapData.mk.congr_simp` |

### Cycle 7 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "有限全対射同定、全triangle三射と指定商同値homの自然性、実Subobject/実商の制限、全Law finite diagram/モデル/filter/商の直和、元原始三段とW1への接続を追加"
  exit_criteria_status: [任意nとn0の元全対射を自然同定, 任意cochain正方形で全三射を証明, 台包含と共通署名で実filter/商が自然, 元q0全発生ラベルを全実構成へ保持, 原始M02の独立生成三段triangleへ全三射同型, A–F/Wと全premiseを前節へ対応, 独立完了査読はPRゲート合格後に別起動]
  split_reason: none
  completion_candidate: yes
  lean_artifacts: [前節192追加spine, 受理済み1529宣言]
  evidence: [全target対応表, material premise/DAG表, root focused buildと公理監査]
  claim_mapping:
    theorem_names: [compositionTriangleMap, ConeTower.finiteExtendIso_natural, ConeTower.filtrationQuotientEquiv_hom_natural, lawPathBiproductIso, lawConstructionSumIso_natural, ThreeStagePath.lawTowerTriangleIso, WitnessOne.finite_first_quotient_dimensions, WitnessOne.finite_second_quotient_dimensions]
    source_labels: [T0, A, B, C, D, E, F, W1, W2, W3a, W3b]
    conjuncts: [前節全target対応表]
    undischarged_assumptions: []
    acceptance_point: "固定全targetに対応する実構成の数学的義務を閉じたproposal。正式PRレビュー、root受理、別4本完了査読、CI、merge、Issue同期の認定を待つ"
    port_status: unported
  unchecked: [標準PR正式4本, root最終受理, 別独立4本完了監査, CIとmerge同期]
audits:
  premise_delta:
    discharged: [前節全discharge-required行]
    remaining: []
  certificate_provenance:
    discharged: [原始有限pathから全diagram, 原始同q0 Lawから全有限biproduct, mapping cylinder再帰から実モデルMonoと実逐次商HE, W1原始入力から実filter商の評価]
    unresolved: []
  proof_use:
    used: [全target対応表とmaterial premise/DAG表]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [次節検証, 固定headの正式PR監査コメント]
  blocking_findings: []
  next_obligation: 標準PRゲートを実施し固定headの別独立4本完了監査へ進む
```

### Cycle 7検証

rootの必要な非aggregate target `WitnessOneFiniteModels` buildは3894 jobsで成功した。
その依存で三段接続・全指定射・Lawモデル/filtration/商分解を確認した。
`WitnessTwoLawMultiplicity`、`WitnessThreeFullLaw`、`WitnessOneSignatureMultiplicity`
の必要な回帰target buildも3881 jobsで成功した。
Research全体・aggregate root・全source file loopの再elaborationは実行していない。

152moduleのcompiled metadataから累積1721宣言を抽出した。追加192宣言は
単一scratchの全件 `#print axioms` で確認し、無変更の1529先行宣言は
Cycle6の受理済み全件記録を再利用した。先行Lean差分に削除・置換行は零件で、
計算成分・statement・proof termを保持している。集合照合は欠落・余分・
エラー・標準外公理零件、46宣言は公理非依存、残りは
`propext` / `Classical.choice` / `Quot.sound` の範囲である。
追加公理log SHA-256: `5bf01fcc1fae501c3c87fc3cc762f20ccab77ab61bd0a4eff036a2d858e49a71`。
累積照合log SHA-256: `645fefbee5bd469f549df43a69e32c8af143ccbf67c98d1dfe2bad73afd2078e`。

placeholder、hidden/BiDi、privacy、新規禁止語彙、FormalからResearchへの
import scanと `git diff --check` は検出なし。変更はG-133のResearchLeanと本reportのみ。
正式PR査読と別独立4本完了監査、CI、merge、Issue同期の証拠は
この最終snapshotに対するPRコメントへ記録する。
Formal移植とArchSig対応実装は実施していない。

## G-133 全targetの完了認定

Cycle7の固定head `74cb93564070661509ac0c2f842596e63d0957fa` に対する
[正式完了台帳](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007700344)で、
固定T0・A–F・Wと完了条件1–4を一つのGOALとして `target-theorem-proved` と認定した。
停止条件は `target-theorem-proved`。全 `discharge-required` は放電済みで、
固定target内の残るResearch証明義務・blocker・中心未確認はない。
Cycle7までのproposalと未チェック欄は各時点の記録であり、上記台帳が完了判定である。

[標準PRレビュー・root受入](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007458427)は
新規数学2本・Lean2本で実施し、その合格後に
[同じheadのfinal packet](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007476134)から
別の新規数学2本・Lean2本による全GOAL完了監査を実施した。
[数学A](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007685629)、
[数学B](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007687147)、
[Lean A](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007688766)、
[Lean B](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269#issuecomment-6007690413)と
root統合はすべて `No major findings`。全15gate・全13回帰scenarioはpass。

[PR #5269](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5269)は
同headのCI全8チェック成功後、2026-10-06T01:53:19Zに
merge `2e0f452c97af56ea4fe2db1f9ca134630d872c58` としてmainへ反映した。
認定結果・merge・CI・全検証範囲は[tracking Issue #5261](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5261)にも同期した。
GOALのstatusと索引はループ停止後の認定結果同期であり、固定target本文と設計4文書は変更していない。
Issueは人間の明示close指示なしでopenを維持する。

公理監査は152module・累積1721宣言の全件を対応させ、新192宣言のfresh出力と
無変更1529宣言の受理済み記録を照合した。標準外・欠落・余分は零件、46宣言は公理非依存。
必要な非aggregate target検証と、完了Lean各laneの指定単一file検証は成功した。
Research全体・aggregate・全source file loopのbuildは実行していない。
Researchでの有理複体・実比較の証明であり、Formal移植は
`unported (Research-proved)`、ArchSigへの係数・実装対応は別作業である。
