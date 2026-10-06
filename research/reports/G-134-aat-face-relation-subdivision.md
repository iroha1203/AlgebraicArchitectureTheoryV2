# G-134：面の関係による診断保存細分化

固定入力は tracking Issue [#5272](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272)
の参照版。GOAL commit `9a3690d4ba9f771ec714b354ec4c097daf4a99b0`、
共通基準・設計 commit `299b32cc56775b24bb12ffaab8fe17742d2580da`、
既存宣言 commit `6c3a960540cd0107abb549bc124338c9f1acd57b`。
Research証拠は本体への未移植。固定target全体は未完了。

## Cycle 1 selection

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 1
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: f4e3540887907b8f461f6d2fb6c4a94315f70bbb
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: '#5272 / 未着手'
  proof_dag_predecessors:
    - ResolutionInvariance.SupportedNerveMorphism
    - ResolutionInvariance.GeneratedComparisonMap
    - AtlasDefectComposition.ComparisonComposition
  milestone: 'P1–P2：Aの混在比較から実生成Homへの構成'
  proof_obligations:
    - 原始incidence、支持輸送、旧比較の埋め込み
    - 恒等とOption.bind合成の許容性
    - 原始零和から全A・各Lawのchain/cochain比較
    - 全三次数と既存H1での生成合成・旧比較との一致
    - 既存comm1失敗入力の原始零和違反
  exit_criteria:
    - 上記全義務を原始入力からLean宣言へ対応
    - focused checkと全対象宣言の標準公理監査
  selection_reason: '新比較と実診断への接続が全基本変形の共通依存である'
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/FaceRelationSubdivision/IncidenceComparison.lean
  risks:
    - 原始零和とLaw座標での相殺の同定
    - 旧比較専用APIへの接続
  unchecked:
    - P1–P2の各構成は実装中
```

## 全targetの現proof obligation

P1–P2はPR #5274で受理・マージ済み。P3（全基本変形・逆縮約）、P4（有限合成・実診断・錐）、
P5（E・W1–W3）は未証明。GOAL T0・A–E・Wと完了条件は変更しない。

## Cycle 1：条項と構成の対応

P1–P2の受理候補。以下は今回の数学的到達点への対応であり、全GOALの完了判定は残る。

| 固定条項 | 生成物・宣言 | 原始入力・使用経路 |
| --- | --- | --- |
| Aの原始比較 | `IncidenceSupportedComparison`, `optionCell_incidence_iff`, `optionCell_incidence_bind` | 独立なセル名の自由ℤ加群で退化面の符号付き零和を検査。三辺の個別退化を要求しない |
| Aの台 | `edgeSupport_compatible`, `faceSupport_compatible` | chart台包含・端点・三辺のincidenceからK1台の包含を導出 |
| Aの原始恒等・合成 | `identity`, `comp`, `comp_identity_left/right`, `comp_assoc` | 全三計算成分の等号。面の退化は零和をOption.bindへ再代入して導出 |
| Aの全Law実比較 | `generatedPullback0/1/2`, `generatedPullback_comm0/1`, `generatedComparisonHom`, `generatedComparisonH1Map` | SourceのLaw降下からCellCoordinateを生成。相殺する像のcell・law・valueが一致することを証明 |
| T0の細adequacy | `generatedComparisonHomFromCoarse` | G-133 `adequate_of_coarser`を粗adequacyへ適用し、上の実生成Homに渡す |
| Aの全ラベルの成分比較 | `generatedBlockComparisonHom`, `generatedPullback0/1/2_block_component` | 発生ラベルを個別に保持。Value型の有限性を追加しない |
| Aの全支持部分集合 | `targetSubsetComparisonHom`, `aSubnerveComparisonHom` | 支持セルの選択と同じ原始比較を用いる。空A・空辺台・空面台を除外しない |
| T0・AのchainとDの双対 | `K0/1/2`, `chainD1/2`, `chainD1_comp_chainD2`, `supportedChain`, `supportedChainHom` | 支持セル名の自由ℚ加群、端点差分と三辺和。mathlib `ChainComplex (ModuleCat ℚ) ℤ`へ零延長 |
| Dの全三次数での同じ射 | `freeDualEquiv`, `chainD1/2_dual`, `supportedChainMap0/1/2_dual`, `labelFiberComparison_naturality0/1/2` | chainの基底評価、既存subset微分・独立Law座標生成・既存block/fiber同値を同じ射で照合 |
| Aの直接生成と合成 | `generatedComparisonHom_comp`, `generatedComparisonH1Map_comp`, `generatedBlockComparisonHom_comp`, `generatedBlockComparisonH1Map_comp`, `aSubnerveComparisonHom_comp`, `aSubnerveComparisonHom_h1Map_comp` | 直接射を原始Option.bindから生成。G-133汎用 `cochainComp`と既存H¹商の写像へ接続 |
| Aの旧比較への特殊化 | `ofHereditary`, `ofHereditary_comp`, `ofHereditary_identity`, `ofHereditary_generatedComparisonHom`, `ofHereditary_generatedBlockComparisonHom`, `ofHereditary_aSubnerveComparisonHom`, 各H¹一致 | 旧3退化fieldから原始零和を導出。全計算成分の一致を証明し、混在比較を旧型に戻さない |
| Aの指定失敗例 | `degenerateFace_primitive_incidence_fails`, `no_incidenceComparison_with_obstruction_maps` | 既存 `DegenerateFaceComm1Obstruction` と同じloop三重出現・比較表で1−1+1=1を評価 |
| 新比較の非空虚性とB§2の原始constructor | `TriangleAddition.supported`, `collapse`, `collapse_mixed_degenerate`, `collapse_not_hereditary` | 任意の旧辺（loopを含む）を保持してfreshセルを追加。K1台等号と0−e+eの相殺を生成 |

## 前提の出所と使用

| 前提 | role | 放電・使用先 |
| --- | --- | --- |
| Reading、有限supported nerve、有限Source、ℚ | ambient-boundary | T0の入力。Source有限性は実座標・発生ラベルの有限性に用いる。支持chain自体は有限nerveだけを用いる |
| 共通FiniteLawFamilyと粗adequacy | ambient-boundary | T0の任意Law。値の輸送を `lawDescend_comparisonFactor` から構成 |
| 細adequacy | discharge-required（T0への適用） | `adequate_of_coarser` と `generatedComparisonHomFromCoarse`。一般APIの二adequacy引数はこの生成証拠とproof irrelevanceで同定可能 |
| chart台包含、写るセルのincidence、退化辺端点一致、面の原始零和 | direction-hypothesis（Aの一般比較） | 台輸送と実微分の可換性。B§2の原始収縮ではconstructorから全fieldを放電 |
| 支持部分集合のmaps-to条件 | direction-hypothesis（一般化したsubset API） | Aの逆像の場合はmembershipそのものから放電。Law fiberでは降下の等式で放電 |
| 同型・chain-map式・cohomology保存・ホモトピー | 入力fieldにない | chainとcochain写像、可換性は今回の構成出力。B–Cの逆・ホモトピー・同型は次到達点の未証明義務 |

`face_none_incidence`はAが明示する自由ℤ加群の原始入力条件であり、Lawの微分可換性を供給するfieldではない。
この一般条件を三角形追加で構成した証拠と、旧端点反例が条件に違反する証拠を同時に保持する。

## 使用する既存宣言と受理参照

既存版は `6c3a960540cd0107abb549bc124338c9f1acd57b`。
G-104はPR [#3943](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/3943)、
G-107はPR [#3994](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/3994)、
G-133の汎用合成はPR [#5263](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5263)、
零延長はPR [#5265](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5265)の受理記録を参照する。
使用するstatement・定義・適用引数は今回のsourceで照合する。

- `ResolutionInvariance/SupportedNerveMorphism.lean`: SHA-256 `7c0d0dd51fb2dda75c4e79c5bee07042421899ad931f79ddeed6269adc53f55f`。
- `ResolutionInvariance/GeneratedComparisonMap.lean`: SHA-256 `0f9269aa2e1efe95ff7d033aa40769149e48687f88c855dd104f12fb28e95a9d`。
- `ResolutionInvariance/LawGeneratedComplex.lean`: SHA-256 `0abedb60a37d49a75adf2dbe89c6bc0b85c00161bc9f9f746cb8aa46c18d4585`。
- `ResolutionInvariance/ComparisonData.lean`: SHA-256 `8a15e8795a23071bcb90616399926807825dd315be264b16cf60b119b1663b21`。
- `ResolutionInvariance/LawValueBlockDecomposition.lean`: SHA-256 `27b917985525ad42bf79000e0333922f7cfd1e002389c20603f410fb8b4ce26a`。
- `ResolutionInvariance/LawValueBlockComparison.lean`: SHA-256 `0e48d2f141906b45bd09060abc01aa5dda6aa4a2e7ae739ffbc4e8a6f8b57815`。
- `ResolutionInvariance/DegenerateFaceComm1Obstruction.lean`: SHA-256 `a83073cead80e6fe3405f62711ae23d52783da22d396b6ea15314822f507ee3d`。
- `UniformInvariance/ASubnerveReduction.lean`: SHA-256 `af3f89ed9c5ff83d74885d0dc29dd0948cf9453cef0fc83346d587db5dd82218`。
- `AtlasDefectComposition/ComparisonComposition.lean`: SHA-256 `9ad198d35970359648355a4dd3c42e54d54da2bdf6c8f9bf389e61dcaad6d2ae`。
- `AtlasDefectComposition/GeneratedComposition.lean`: SHA-256 `01c82cd8bf9b419f3ade04d9bde0e8149e8491bb18e8089139ab71195d269331`。
- `AtlasDefectComposition/ComparisonLaws.lean`: SHA-256 `e61737923de36bf9fb285bad35060c221dea112f3800468c14ba0a5c41a04c3b`。
- `AtlasDefectComposition/ZeroExtension.lean`: SHA-256 `a626c0d5f3f6ccc1e1a12c76f321ac4918fcf08e430e56f85c408ac618b9b5ec`。

## Cycle 1 spine declaration list

受理候補は次の明示宣言。structureの自動生成constructor・field・recursorは各module末尾の標準公理検査にも含める。
探索用宣言は混在させていない。


### BlockComposition.lean

- `AAT.AG.FaceRelationSubdivision.chartBlockCoordinateMap_comp`
- `AAT.AG.FaceRelationSubdivision.edgeBlockCoordinateMapOption_comp`
- `AAT.AG.FaceRelationSubdivision.faceBlockCoordinateMapOption_comp`
- `AAT.AG.FaceRelationSubdivision.generatedBlockPullback0_comp`
- `AAT.AG.FaceRelationSubdivision.generatedBlockPullback1_comp`
- `AAT.AG.FaceRelationSubdivision.generatedBlockPullback2_comp`
- `AAT.AG.FaceRelationSubdivision.generatedBlockComparisonHom_comp`
- `AAT.AG.FaceRelationSubdivision.generatedBlockComparisonH1Map_comp`
- `AAT.AG.FaceRelationSubdivision.identity_generatedBlockComparisonHom`
- `AAT.AG.FaceRelationSubdivision.identity_generatedBlockComparisonH1Map`

### GeneratedComparison.lean

- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartCoordinateMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceCoordinateMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMapOption`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMapOption_eq_none`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMapOption_eq_some`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceCoordinateMapOption`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceCoordinateMapOption_eq_none`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceCoordinateMapOption_eq_some`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartCoordinateMap_edgeLeftCoordinate`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartCoordinateMap_edgeRightCoordinate`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartCoordinateMap_edgeLeft_eq_right_of_none`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMap_faceEdge0Coordinate`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMap_faceEdge1Coordinate`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMap_faceEdge2Coordinate`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback0`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback1`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback2`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback0_apply`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback1_apply`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback2_apply`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMapOption_faceEdge01`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMapOption_faceEdge12`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback_comm0`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback_comm1`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedComparisonHom`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedComparisonH1Map`

### GeneratedComposition.lean

- `AAT.AG.FaceRelationSubdivision.chartCoordinateMap_comp`
- `AAT.AG.FaceRelationSubdivision.edgeCoordinateMapOption_comp`
- `AAT.AG.FaceRelationSubdivision.faceCoordinateMapOption_comp`
- `AAT.AG.FaceRelationSubdivision.generatedPullback0_comp`
- `AAT.AG.FaceRelationSubdivision.generatedPullback1_comp`
- `AAT.AG.FaceRelationSubdivision.generatedPullback2_comp`
- `AAT.AG.FaceRelationSubdivision.generatedComparisonHom_comp`
- `AAT.AG.FaceRelationSubdivision.generatedComparisonH1Map_comp`
- `AAT.AG.FaceRelationSubdivision.identity_generatedComparisonHom`
- `AAT.AG.FaceRelationSubdivision.identity_generatedComparisonH1Map`
- `AAT.AG.FaceRelationSubdivision.generatedComparisonHomFromCoarse`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_chartCoordinateMap`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_edgeCoordinateMapOption`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_faceCoordinateMapOption`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_generatedComparisonHom`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_generatedComparisonH1Map`

### HereditarySpecialization.lean

- `AAT.AG.FaceRelationSubdivision.ofHereditary_generatedBlockComparisonHom`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_generatedBlockComparisonH1Map`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_targetSubsetComparisonHom`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_aSubnerveComparisonHom`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_aSubnerveComparisonHom_h1Map`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_labelFiberComparisonHom`
- `AAT.AG.FaceRelationSubdivision.ofHereditary_identity`

### IncidenceComparison.lean

- `AAT.AG.FaceRelationSubdivision.optionCell`
- `AAT.AG.FaceRelationSubdivision.optionCell_none`
- `AAT.AG.FaceRelationSubdivision.optionCell_some`
- `AAT.AG.FaceRelationSubdivision.optionCell_incidence_iff`
- `AAT.AG.FaceRelationSubdivision.optionCell_incidence_bind`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.ofHereditary`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.ext`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeSupport_compatible`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceSupport_compatible`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.comp`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.comp_chartMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.comp_edgeMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.comp_faceMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.identity`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.comp_identity_left`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.comp_identity_right`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.comp_assoc`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.ofHereditary_comp`

### IncidenceObstruction.lean

- `AAT.AG.FaceRelationSubdivision.degenerateFace_primitive_incidence_fails`
- `AAT.AG.FaceRelationSubdivision.no_incidenceComparison_with_obstruction_maps`

### LawBlockComparison.lean

- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartCoordinateMap_lawValueLabel`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMap_lawValueLabel`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceCoordinateMap_lawValueLabel`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartBlockCoordinateMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeBlockCoordinateMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceBlockCoordinateMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeBlockCoordinateMapOption`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceBlockCoordinateMapOption`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeBlockCoordinateMapOption_eq_none`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeBlockCoordinateMapOption_eq_some`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceBlockCoordinateMapOption_eq_none`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceBlockCoordinateMapOption_eq_some`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceMap_eq_some_of_faceBlockCoordinateMapOption_eq_some`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartBlockCoordinateMap_edgeLeftBlockCoordinate`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartBlockCoordinateMap_edgeRightBlockCoordinate`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartBlockCoordinateMap_edgeLeft_eq_right_of_none`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeBlockCoordinateMap_faceEdge0BlockCoordinate`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeBlockCoordinateMap_faceEdge1BlockCoordinate`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeBlockCoordinateMap_faceEdge2BlockCoordinate`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedBlockPullback0`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedBlockPullback1`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedBlockPullback2`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedBlockPullback0_apply`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedBlockPullback1_apply`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedBlockPullback2_apply`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedBlockPullback_comm0`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeBlockCoordinateMapOption_faceEdge01`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeBlockCoordinateMapOption_faceEdge12`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedBlockPullback_comm1`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedBlockComparisonHom`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedBlockComparisonH1Map`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback0_block_component`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback1_block_component`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedPullback2_block_component`

### SubsetComparison.lean

- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetChartMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetEdgeMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetFaceMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetEdgeMapOption`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetFaceMapOption`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetEdgeMapOption_eq_none`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetEdgeMapOption_eq_some`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetFaceMapOption_eq_none`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetFaceMapOption_eq_some`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetChartMap_edgeLeft`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetChartMap_edgeRight`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetChartMap_edgeLeft_eq_right_of_none`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetEdgeMap_faceEdge0`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetEdgeMap_faceEdge1`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetEdgeMap_faceEdge2`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetPullback0`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetPullback1`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetPullback2`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetPullback0_apply`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetPullback1_apply`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetPullback2_apply`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetPullback_comm0`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetEdgeMapOption_faceEdge01`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetEdgeMapOption_faceEdge12`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetPullback_comm1`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetComparisonHom`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.aSubnerveComparisonHom`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.labelFiberComparisonHom`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.labelFiberEquivBlock_chartMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.labelFiberEquivBlock_edgeMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.labelFiberEquivBlock_faceMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.labelFiberComparison_naturality0`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.labelFiberComparison_naturality1`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.labelFiberComparison_naturality2`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.labelFiberComparison_naturality`

### SubsetComposition.lean

- `AAT.AG.FaceRelationSubdivision.subsetMapsTo_comp`
- `AAT.AG.FaceRelationSubdivision.targetSubsetChartMap_comp`
- `AAT.AG.FaceRelationSubdivision.targetSubsetEdgeMapOption_comp`
- `AAT.AG.FaceRelationSubdivision.targetSubsetFaceMapOption_comp`
- `AAT.AG.FaceRelationSubdivision.targetSubsetPullback0_comp`
- `AAT.AG.FaceRelationSubdivision.targetSubsetPullback1_comp`
- `AAT.AG.FaceRelationSubdivision.targetSubsetPullback2_comp`
- `AAT.AG.FaceRelationSubdivision.targetSubsetComparisonHom_comp`
- `AAT.AG.FaceRelationSubdivision.targetSubsetComparisonHom_h1Map_comp`
- `AAT.AG.FaceRelationSubdivision.subsetTransportHom`
- `AAT.AG.FaceRelationSubdivision.transportHom_rfl`
- `AAT.AG.FaceRelationSubdivision.targetSubsetComparisonHom_transport`
- `AAT.AG.FaceRelationSubdivision.aSubnerveComparisonHom_comp`
- `AAT.AG.FaceRelationSubdivision.aSubnerveComparisonHom_h1Map_comp`

### SupportedChain.lean

- `AAT.AG.FaceRelationSubdivision.freeMap`
- `AAT.AG.FaceRelationSubdivision.freeMap_single`
- `AAT.AG.FaceRelationSubdivision.freeDualEquiv`
- `AAT.AG.FaceRelationSubdivision.freeDualEquiv_single`
- `AAT.AG.FaceRelationSubdivision.freeDual_separates`
- `AAT.AG.FaceRelationSubdivision.K0`
- `AAT.AG.FaceRelationSubdivision.K1`
- `AAT.AG.FaceRelationSubdivision.K2`
- `AAT.AG.FaceRelationSubdivision.chainD1`
- `AAT.AG.FaceRelationSubdivision.chainD2`
- `AAT.AG.FaceRelationSubdivision.chainD1_single`
- `AAT.AG.FaceRelationSubdivision.chainD2_single`
- `AAT.AG.FaceRelationSubdivision.chainD1_dual`
- `AAT.AG.FaceRelationSubdivision.chainD2_dual`
- `AAT.AG.FaceRelationSubdivision.chainD1_comp_chainD2`
- `AAT.AG.FaceRelationSubdivision.rationalOptionCell`
- `AAT.AG.FaceRelationSubdivision.rationalOptionCell_dual`
- `AAT.AG.FaceRelationSubdivision.chainDegreeObject`
- `AAT.AG.FaceRelationSubdivision.chainDegreeDifferential`
- `AAT.AG.FaceRelationSubdivision.chainDegreeDifferential_square`
- `AAT.AG.FaceRelationSubdivision.supportedChain`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap0`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap0_single`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap0_dual`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap1`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap1_single`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap1_dual`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap2`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap2_single`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap2_dual`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap_comm1`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainMap_comm2`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainDegreeMap`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainDegreeMap_comm`
- `AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.supportedChainHom`

### TriangleGeometry.lean

- `AAT.AG.FaceRelationSubdivision.TriangleAddition.nerve`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.supported`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.chartSupport_old`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.chartSupport_new`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.edgeSupport_c`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.edgeSupport_e2`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.edgeSupport_old`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.faceSupport_new`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.faceSupport_old`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.self_factor`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.collapse`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.collapse_mixed_degenerate`
- `AAT.AG.FaceRelationSubdivision.TriangleAddition.collapse_not_hereditary`

## Cycle 1検証と結果proposal

- 対象11fileについて、単一fileの `lake env lean` focused checkを実行し、importに必要な対象fileだけを `-o` で確認した。Researchの全体build・aggregate root・全file loopは実行していない。
- 各対象moduleの `#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision` は成功。明示212宣言すべての `#print axioms` を一時監査fileで実行し、source/spine/logの名前集合は欠落・余剰なし。依存公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
- placeholder、hidden/BiDi Unicode、privacy/local-path、Research import方向、語彙scanと `git diff --check` はclean。
- この検証記録時点（Cycle 1 PR作成前）ではCI・独立PR査読は未実施。全GOALの独立完了査読は完了候補で実施する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: 'P1–P2：原始比較・全支持chain・実Law/block/subset生成・全次数の同じ射・H¹合成・旧比較特殊化・指定反例排除を構成'
  exit_criteria_status:
    - '条項対応は上表、原始条件・使用経路は前提表とsource'
    - '対象focused check・標準公理検査・明示212宣言のaxiom audit成功'
  split_reason: none
  completion_candidate: no
  lean_artifacts: [Cycle 1 spine declaration list]
  evidence: [IncidenceComparison, GeneratedComparison, GeneratedComposition, LawBlockComparison, SubsetComparison, SubsetComposition, BlockComposition, SupportedChain, HereditarySpecialization, IncidenceObstruction, TriangleGeometry]
  claim_mapping:
    theorem_names: [Cycle 1 spine declaration list]
    source_labels: [T0, A, Dの支持chain・実座標同定, B§2の原始幾何]
    conjuncts: [Cycle 1条項対応表]
    undischarged_assumptions: []
    acceptance_point: '選定したP1–P2の終了条件への構成proposal。独立査読で受理判定する'
    port_status: unported
audits:
  premise_delta:
    discharged: [fine adequacy, K1 support transport, chain differential square-zero, generated comm0/comm1, subset fiber maps-to, hereditary embedding, primitive composition, triangle primitive collapse]
    remaining: ['P3–P5：全基本変形・逆・ホモトピー、有限列、標準診断・錐への残る接続、E・W1–W3']
  certificate_provenance:
    discharged: [raw incidence to generated chain and cochain maps]
    unresolved: []
  proof_use:
    used: [primitive incidence, endpoint incidence, chart support compatibility, law descent, coarse adequacy, subset maps-to]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ['11対象file focused check', '212 explicit declaration axiom audit', '各module標準公理検査', '横断scan']
  blocking_findings: []
  next_obligation: 'P3：三角形追加・面付き辺分割・逆縮約・reading変更の全支持r・s・hと標準homotopy同値'
```

P3–P5とGOAL全体の完了条件は未完了。恒久設計・GOALの固定targetは変更していない。


## Cycle 1：受理参照

PR [#5274](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5274)、
最終head `4567a17951821c1c36b27afe08c473114b9fbfac`、
merge `b723f2dc34a370c51f33fa7fdd4dca3154fa4815`。
独立数学2本・Lean2本の標準査読と、非中心指摘に限る新規単一査読の修正確認を経て、
選定P1–P2を `proof-obligation-discharged` として受理した。
[標準監査・root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5274#issuecomment-6020448130)、
[tracking記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272#issuecomment-6020482602)。
全GOALの完了候補ではなく、GOAL active、Issue OPENを維持する。

## Cycle 2：selection（実装前）

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 2
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: b723f2dc34a370c51f33fa7fdd4dca3154fa4815
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: Issue 5272 comment 6020482602 / Cycle 1 acceptance PR5274
  proof_dag_predecessors:
    - Cycle 1 primitive mixed comparison / supported chain / physical Law and fiber Hom
    - G-133 standard zero extension / oldH1Equiv / generic full Hom APIs
  milestone: P3、固定Bの全基本変形を原始入力から支持を保つ両方向・homotopyへ接続する
  proof_obligations:
    - 三角形追加のr/s/hと全Aのchain式
    - 任意の面に接する辺分割、全出現別セルと台、r/s/hと全Aのchain式
    - 局所セル・全接続・台のpatternからの原始逆縮約と旧入力の復元/名前同型
    - 台の逆像reading変更とrename、細adequacyと支持セルの同定
    - chain双対の実subset・各Law fiberに対する標準cochainホモトピー同値とH0/H1/H2
    - 指定されたlift選択s'、t、同じH1 readbackと代表のpotential補正
  exit_criteria:
    - Bの4操作と表示同型の全fieldを固定幾何から生成し、結論certificateを入力にしない
    - 全Aでr/s/hの指定基底像と台保持、chain-map、rs=id、id-sr=dh+hdを全3次数で証明する
    - 原始局所逆patternから旧入力を復元し、constructorの出力との全セル名/incidence/台同型を構成する
    - reading pullbackは真の任意reading細分を扱い、比較因子と全Aのtransportを証明する
    - 同じ生成r/sの双対を既存実subset/fiberへ照合して標準HomotopyEquivと全H0/H1/H2同型を得る
    - 三角形追加と辺分割で設計§7の指定lift有限和とpotential補正を同じ写像で証明する
  selection_reason: Aで許す比較からBの診断保存変形を実際に往復させ、Cの有限列帰納に必要な単段の保存義務を放電する
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/FaceRelationSubdivision/SupportedBasis.lean
    - ResearchLean/AG/FaceRelationSubdivision/ThreeHomotopy.lean
    - ResearchLean/AG/FaceRelationSubdivision/TriangleContraction.lean
    - ResearchLean/AG/FaceRelationSubdivision/EdgeSubdivision.lean
    - ResearchLean/AG/FaceRelationSubdivision/ElementaryInverse.lean
    - ResearchLean/AG/FaceRelationSubdivision/ReadingPullback.lean
    - ResearchLean/AG/FaceRelationSubdivision/LiftChoice.lean
  risks:
    - repeated face occurrencesとloopを同じ旧辺に潰さず位置別に保持する
    - 逆patternの接続条件を出力同型・homotopy供給fieldに置き換えない
    - finite sum supportが空A/空辺台にも閉じる
    - 同じ比較/逆と実Law座標の式・旧H1商を対応させる
  unchecked:
    - P3の各構成はこれから実装する
```

## Cycle 2：独立に再利用できる二つの強い追加操作

原始入力 `N : TargetSupportedNerve q` と任意の指定辺eから、三角形追加と面付き辺分割を構成した。
旧面内で同じ辺が三回現れる場合にも、Occurrenceは面名とFin3位置の組である。
各s/hの基底像は設計§2・3の有限和そのものであり、全セル上でr/sのchain式、
rs=id、sr+dh+hd=idを検査した。台包含から同じ有限和を任意Aへ制限する。

| GOAL/設計 | 新しい証拠 | 使用する入力・放電 |
| --- | --- | --- |
| B/設計§1–3、任意Aの台保持 | SupportedBasisMap.selectedEmbed_comm / selected_square_of_raw_square / selected_eq_of_raw_eq | 非零基底項への台包含。TriangleAddition.s0–2/h0–1、EdgeSubdivision.s0–2/h0–1が原始K1台から生成 |
| B/設計§2、三角形追加 | TriangleAddition.rs0–2 / r_comm01–12 / s_comm01–12 / sr_h0–2 | Nの端点・面incidenceと新セル表。結論certificate引数なし |
| B/設計§3、全出現の面付き辺分割 | EdgeSubdivision.supported / collapse / slot_boundary / rs0–2 / r_comm01–12 / s_comm01–12 / sr_h0–2 | Fin3位置と全Occurrence。slot_boundaryが各符号位置を同じ面有限和へ接続 |
| B/全Aの同じ実cochain比較 | IncidenceSupportedComparison.basisHom_eq_generated、両操作.rHom_eq_generated | 原始Option像の自由加群射の双対とCycle1の実targetSubsetComparisonHomを全3次数で照合 |
| B/H0・H1・H2、標準homotopy | threeHomotopy、SubsetChainContraction.cochainHomotopyEquiv、両操作.chainContraction / homologyIso_hom | 汎用recordは構成出力。両操作が全fieldを指定r/s/hから放電し、Mathlib標準HomotopyEquivと同じhomologyMapへ送る |
| B/既存H1商 | 両操作.oldH1ComparisonIso_hom | G133 oldH1Iso_naturalを再利用し、既存商の同型の順方向が同じ実比較のh1Mapと証明 |

### Material premise・provenance・proof-use

本文由来は有限セル、非空chart台、K1、面incidence、同一readingの任意辺eである。
台保存をstrong equivalence入力に増やしていない。SupportedBasisMapのfieldは有限基底像と
非零項への台包含だけで、chain-mapや同型を含まない。slotSectionの台包含は
S(F)⊆S(e)、h0/h1はK1台等式から導く。

SubsetChainContractionの方向式は一般bridgeの明示的仮定である。
このrecordだけをGOAL Bの証拠には採用しない。TriangleAddition.chainContractionと
EdgeSubdivision.chainContractionが全fieldを原始入力N/eから生成することを採用する。
threeHomotopyは点ごとの三項補正式からMathlib標準Homotopyを構成する一般補題であり、
その方向式は同じr/s/hの全セル式を選択・双対化して両constructorで放電される。
一般bridgeの結論相当fieldを原始操作入力へ移すrouteは使用していない。

非空性はCycle1のtriangle geometryと、任意の合法N/eへの二つのconstructorから継承する。
chartの非空台を保持し、空A/空辺台/loop/反復辺を排除する追加仮定はない。
全Source空の場合は辺eを指定できるinstanceがないという固定設計§5の量化を保つ。
汎用方向recordは操作の許容predicateではなく構成出力なので、不成立の操作をこのrecordで
却下する分類は行わない。primitive比較の不成立instanceはCycle1のIncidenceObstructionにある。

### 今回の明示spine

Cycle1受理spineに加え、以下の278明示宣言を今回のspineとして固定する。
名前のprefixは `AAT.AG.FaceRelationSubdivision`。generated構造射影・recursorも各module末尾の
標準公理検査の対象である。新しいcycle scaffoldは残していない。

```text
Selected
selectedEmbed
selectedEmbed_single
selectedEmbed_injective
subtypeDomain_single_selected
SupportedBasisMap
SupportedBasisMap.raw
SupportedBasisMap.selected
SupportedBasisMap.basis_support_selected
SupportedBasisMap.selectedEmbed_basis
SupportedBasisMap.selectedEmbed_comm
SupportedBasisMap.raw_single
SupportedBasisMap.selected_single
SupportedBasisMap.selectedEmbed_apply
SupportedBasisMap.selected_eq_of_raw_eq
SupportedBasisMap.selected_square_of_raw_square
SupportedBasisMap.raw_apply
SupportedBasisMap.raw_point_support
SupportedBasisMap.comp
SupportedBasisMap.raw_comp
SupportedBasisMap.selected_comp
SupportedBasisMap.ofSingle
SupportedBasisMap.zero
SupportedBasisMap.add
SupportedBasisMap.neg
SupportedBasisMap.raw_add
SupportedBasisMap.raw_neg
SupportedBasisMap.identity
SupportedBasisMap.raw_identity
SupportedBasisMap.selected_identity
SupportedBasisMap.selected_add
SupportedBasisMap.selected_neg
SupportedBasisMap.selected_identity_correction
SupportedBasisMap.ofOption
SupportedBasisMap.ofSingle_basis
SupportedBasisMap.ofOption_basis
SupportedBasisMap.zero_basis
SupportedBasisMap.add_basis
SupportedBasisMap.neg_basis
SupportedBasisMap.comp_basis
SupportedBasisMap.selected_comp_eq_identity
homotopyComponent
homotopyComponent_zero
threeHomotopy
TargetSupportedNerve.rightBasis
TargetSupportedNerve.leftBasis
TargetSupportedNerve.face0Basis
TargetSupportedNerve.face1Basis
TargetSupportedNerve.face2Basis
TargetSupportedNerve.rawD1
TargetSupportedNerve.rawD2
TargetSupportedNerve.rawD1_basis
TargetSupportedNerve.rawD2_basis
TargetSupportedNerve.rawD1_comp_rawD2
TargetSupportedNerve.selected_rawD1
TargetSupportedNerve.selected_rawD2
dualCellMap
dualCellMap_dual
dualCellMap_apply
dualCellMap_comp
dualCellMap_identity
dualSubsetHom
dualSubsetHom_f0
dualSubsetHom_f1
dualSubsetHom_f2
IncidenceSupportedComparison.basis0
IncidenceSupportedComparison.basis1
IncidenceSupportedComparison.basis2
IncidenceSupportedComparison.basis0_image
IncidenceSupportedComparison.basis1_image
IncidenceSupportedComparison.basis2_image
IncidenceSupportedComparison.selfSubsetMapsTo
IncidenceSupportedComparison.selected_basis0_eq
IncidenceSupportedComparison.selected_basis1_eq
IncidenceSupportedComparison.selected_basis2_eq
IncidenceSupportedComparison.basisHom
IncidenceSupportedComparison.basisHom_eq_generated
SubsetChainContraction
SubsetChainContraction.rHom
SubsetChainContraction.sHom
SubsetChainContraction.cochain_rs
SubsetChainContraction.cochain_correction0
SubsetChainContraction.cochain_correction1
SubsetChainContraction.cochain_correction2
SubsetChainContraction.cochainHomotopyEquiv
SubsetChainContraction.cochainHomotopyEquiv_hom
SubsetChainContraction.cochainHomotopyEquiv_inv
SubsetChainContraction.homologyIso
SubsetChainContraction.homologyIso_hom
SubsetChainContraction.oldH1ComparisonIso
SubsetChainContraction.oldH1ComparisonIso_hom
TriangleAddition.inclusion
TriangleAddition.r0
TriangleAddition.r1
TriangleAddition.r2
TriangleAddition.s0
TriangleAddition.s1
TriangleAddition.s2
TriangleAddition.h0
TriangleAddition.h1
TriangleAddition.r0_basis
TriangleAddition.r1_basis
TriangleAddition.r2_basis
TriangleAddition.s0_basis
TriangleAddition.s1_basis
TriangleAddition.s2_basis
TriangleAddition.h0_old_basis
TriangleAddition.h0_new_basis
TriangleAddition.h1_old_basis
TriangleAddition.h1_c_basis
TriangleAddition.h1_e2_basis
TriangleAddition.r0_single
TriangleAddition.r1_single
TriangleAddition.r2_single
TriangleAddition.s0_single
TriangleAddition.s1_single
TriangleAddition.s2_single
TriangleAddition.h0_old
TriangleAddition.h0_new
TriangleAddition.h1_old
TriangleAddition.h1_c
TriangleAddition.h1_e2
TriangleAddition.rs0
TriangleAddition.rs1
TriangleAddition.rs2
TriangleAddition.r_comm01
TriangleAddition.r_comm12
TriangleAddition.s_comm01
TriangleAddition.s_comm12
TriangleAddition.sr_h0
TriangleAddition.sr_h1
TriangleAddition.sr_h2
TriangleAddition.rHom
TriangleAddition.sHom
TriangleAddition.selected_rs0
TriangleAddition.selected_rs1
TriangleAddition.selected_rs2
TriangleAddition.selected_sr_h0
TriangleAddition.selected_sr_h1
TriangleAddition.selected_sr_h2
TriangleAddition.chainContraction
TriangleAddition.cochainHomotopyEquiv
TriangleAddition.rHom_eq_generated
TriangleAddition.chainContraction_rHom
TriangleAddition.chainContraction_sHom
TriangleAddition.homologyIso
TriangleAddition.homologyIso_hom
TriangleAddition.oldH1ComparisonIso
TriangleAddition.oldH1ComparisonIso_hom
EdgeSubdivision.faceSlot
EdgeSubdivision.faceSlot_zero
EdgeSubdivision.faceSlot_one
EdgeSubdivision.faceSlot_two
EdgeSubdivision.Occurrence
EdgeSubdivision.RetainedEdge
EdgeSubdivision.Edge
EdgeSubdivision.Face
EdgeSubdivision.centerEdge
EdgeSubdivision.nerve
EdgeSubdivision.centerEdge_left
EdgeSubdivision.centerEdge_right
EdgeSubdivision.supported
EdgeSubdivision.chartSupport_old
EdgeSubdivision.chartSupport_new
EdgeSubdivision.edgeSupport_old
EdgeSubdivision.edgeSupport_c
EdgeSubdivision.edgeSupport_b
EdgeSubdivision.edgeSupport_diagonal
EdgeSubdivision.edgeSupport_center
EdgeSubdivision.faceSupport_center
EdgeSubdivision.faceSupport_triangle
EdgeSubdivision.chartImage
EdgeSubdivision.edgeImage
EdgeSubdivision.faceImage
EdgeSubdivision.edgeImage_center
EdgeSubdivision.collapse
EdgeSubdivision.diagonal_injective
EdgeSubdivision.triangle_injective
EdgeSubdivision.retired_edge_absent
EdgeSubdivision.edgeLeft_old
EdgeSubdivision.edgeRight_old
EdgeSubdivision.edgeLeft_c
EdgeSubdivision.edgeRight_c
EdgeSubdivision.edgeLeft_b
EdgeSubdivision.edgeRight_b
EdgeSubdivision.edgeLeft_diagonal
EdgeSubdivision.edgeRight_diagonal
EdgeSubdivision.faceEdge0_center
EdgeSubdivision.faceEdge0_triangle
EdgeSubdivision.faceEdge1_center
EdgeSubdivision.faceEdge1_triangle
EdgeSubdivision.faceEdge2_center
EdgeSubdivision.faceEdge2_triangle
EdgeSubdivision.chartImage_old
EdgeSubdivision.chartImage_new
EdgeSubdivision.edgeImage_old
EdgeSubdivision.edgeImage_c
EdgeSubdivision.edgeImage_b
EdgeSubdivision.edgeImage_diagonal
EdgeSubdivision.faceImage_center
EdgeSubdivision.faceImage_triangle
EdgeSubdivision.centerEdge_of_eq
EdgeSubdivision.centerEdge_of_ne
EdgeSubdivision.r0
EdgeSubdivision.r1
EdgeSubdivision.r2
EdgeSubdivision.s0
EdgeSubdivision.s1
EdgeSubdivision.centerSection
EdgeSubdivision.slotSection
EdgeSubdivision.s2
EdgeSubdivision.h0
EdgeSubdivision.h1
EdgeSubdivision.r0_basis
EdgeSubdivision.r1_basis
EdgeSubdivision.r2_basis
EdgeSubdivision.s0_basis
EdgeSubdivision.s1_target_basis
EdgeSubdivision.s1_retained_basis
EdgeSubdivision.centerSection_basis
EdgeSubdivision.slotSection_basis
EdgeSubdivision.s2_basis
EdgeSubdivision.h0_old_basis
EdgeSubdivision.h0_new_basis
EdgeSubdivision.h1_old_basis
EdgeSubdivision.h1_segment_basis
EdgeSubdivision.h1_diagonal_basis
EdgeSubdivision.rs0
EdgeSubdivision.rs1
EdgeSubdivision.rs2
EdgeSubdivision.r_comm01
EdgeSubdivision.r_comm12
EdgeSubdivision.s_comm01
EdgeSubdivision.slot_boundary
EdgeSubdivision.s_comm12
EdgeSubdivision.h1_center
EdgeSubdivision.sr_h0
EdgeSubdivision.sr_h1
EdgeSubdivision.sr_h2
EdgeSubdivision.rHom
EdgeSubdivision.sHom
EdgeSubdivision.selected_rs0
EdgeSubdivision.selected_rs1
EdgeSubdivision.selected_rs2
EdgeSubdivision.selected_sr_h0
EdgeSubdivision.selected_sr_h1
EdgeSubdivision.selected_sr_h2
EdgeSubdivision.chainContraction
EdgeSubdivision.cochainHomotopyEquiv
EdgeSubdivision.rHom_eq_generated
EdgeSubdivision.chainContraction_rHom
EdgeSubdivision.chainContraction_sHom
EdgeSubdivision.homologyIso
EdgeSubdivision.homologyIso_hom
EdgeSubdivision.oldH1ComparisonIso
EdgeSubdivision.oldH1ComparisonIso_hom
freeMap_apply
rationalOptionCell_none
rationalOptionCell_some
TriangleAddition.edgeLeft_old
TriangleAddition.edgeRight_old
TriangleAddition.edgeLeft_c
TriangleAddition.edgeRight_c
TriangleAddition.edgeLeft_e2
TriangleAddition.edgeRight_e2
TriangleAddition.faceEdge0_old
TriangleAddition.faceEdge1_old
TriangleAddition.faceEdge2_old
TriangleAddition.faceEdge0_new
TriangleAddition.faceEdge1_new
TriangleAddition.faceEdge2_new
TriangleAddition.collapse_chart_old
TriangleAddition.collapse_chart_new
TriangleAddition.collapse_edge_old
TriangleAddition.collapse_edge_c
TriangleAddition.collapse_edge_e2
TriangleAddition.collapse_face_old
TriangleAddition.collapse_face_new
```

### focused validation

対象9新規moduleと2既存API追加moduleを、それぞれ実装段階の単一file checkで検証した。
必要なtargeted olean生成を行い、全Research build、aggregate root、全file loopは実施していない。
各module末尾の標準公理検査は成功した。278宣言の全 `#print axioms` をまとめて照会し、
source/spine/log集合に欠落・余剰はない。propext/Classical.choice/Quot.soundだけであり、
sorryAxはない。axiom照会ログSHA-256: `ffb2e5a837ed5c1d833b8cd62ca84aac0d039d01000483a8a129429bf4999f01`。

### Cycle 2 result proposal

```yaml
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta:
    - 三角形追加と面付き辺分割の原始幾何・台・全セルr/s/h・全Aの標準homotopy同値を構成
    - 同じ実生成subset比較と全3次数で一致、全標準homology同型と既存H1商同型の順方向を照合
  exit_criteria_status:
    - 達成：設計§2–3の原始操作、全Aの指定r/s/hとchain式、rs=id、全3次数の収縮式
    - 達成：二つの追加操作の同じ実subset比較の標準HomotopyEquivと全H0/H1/H2
    - 未完：逆縮約の全接続を検査する原始patternと復元/名前同型
    - 未完：任意reading pullbackとrename、および細adequacy
    - 未完：各Law fiber/blockの標準同値への残る接続
    - 未完：指定lift s'、t、H1 readbackと代表potential補正
  split_reason: >-
    二つの追加操作の強い保存定理が、原始入力から全Aの同じ実比較まで閉じた独立再利用可能な
    定理になった。台を保つ有限基底和と標準双対bridgeを含む9新規moduleの依存群を先に
    固定して査読できる数学的checkpointとする。元のP3 milestone/exit条件を変更せず、
    逆pattern・reading変更・lift選択は別の依存群として未完のまま継続する。
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/FaceRelationSubdivision/{SupportedBasis,ThreeHomotopy,RawSupportedChain,ChainDualMap,IncidenceBasis,SubsetContraction,TriangleContraction,EdgeSubdivision,EdgeContraction}.lean
  claim_mapping:
    source_labels: [GOAL B, design elementary-moves §1–3]
    undischarged_assumptions: []
    acceptance_point: 独立再利用可能な二つの追加操作の強い保存定理、P3全終了条件は未完
    port_status: unported
  audits:
    structure_field_escape: none-found
    route_integrity: pass
    vacuity: none-found
    one_way_as_equivalence: none-found
    goal_or_report_reinterpretation: none-found
    next_obligation: P3の原始逆pattern、reading pullback/rename、Law fiber/block接続、lift選択
```

独立査読とCIの結果・Cycle2受理判定は固定PR headへの監査コメントに記録する。
GOALはactive、Issue5272はOPENであり、この状態を固定targetの証明判定に代用しない。
P3の残り、P4–P5、全目標完了監査は未実施である。
