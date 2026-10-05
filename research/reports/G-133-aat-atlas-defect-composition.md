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

M1のLean構成は以下に対応させる。独立査読による受理は未確定。B・C・D・E・F、W1の類・非零相殺と錐、W2・W3は未証明。
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
