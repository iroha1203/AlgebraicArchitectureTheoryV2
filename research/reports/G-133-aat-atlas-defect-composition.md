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

## 全targetのproof obligation

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
