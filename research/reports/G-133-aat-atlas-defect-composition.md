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

M1のLean構成は以下に対応させる。Cycle 1/M1はPR #5263で独立査読・root受理・CI成功後にmerge済み。Cycle 2/M2は実相殺・欠損とW1の指定類について検証済み、独立査読前である。C・D・E・F、W1の錐、W2・W3は未証明。
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

受理spineは以下の116の明示宣言。各module末尾の標準公理監査は、同moduleで生成される
simp用補助宣言を含む全非internal宣言と、それらの依存を検査する。cycle scaffoldは残さない。

`DefectSequence.lean`:

```text
AAT.AG.AtlasDefectComposition.DefectSequence.first
AAT.AG.AtlasDefectComposition.DefectSequence.second
AAT.AG.AtlasDefectComposition.DefectSequence.cancellation
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
  lean_artifacts: [Cycle 2 spine declaration listの116宣言]
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

`.tmp/g133-cycle2-axioms.lean` は上の116明示宣言へ `#print axioms` を実行する。
公理はpropext・Classical.choice・Quot.soundのみ。対象source/report/manifestのplaceholder、
hidden/BiDi、privacy、語彙scanとFormal→Research import scan、git diff --checkはclean。
恒久設計・GOAL本文・本体Formal・toolingの変更はない。Formal移植とArchSig実装は未実施。
C–F、W1の錐と追加項、W2/W3、全GOAL最終監査は未完。

Cycle 2公理ログSHA-256: `2d61caf7c17fb752ffb66f01c19c27006a4d5c99a0ee5200283743220b88675a`。116宣言のsource/scratch/log集合を突合し、欠落・余剰なし。
