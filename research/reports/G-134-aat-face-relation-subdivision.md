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

P1–P2はPR #5274で、P3の三角形追加と面付き辺分割はPR #5275で受理・マージ済み。
P3のreading pullbackとセル名同型はPR #5276で受理・マージ済み。原始逆patternはCycle4の査読前、liftは未証明。
P4（有限合成・一般有限和Law・錐/欠損）とP5（E・W1–W3）は未証明。
GOAL T0・A–E・Wと完了条件は変更しない。

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
非空虚性の不成立側は指定dataと性質を照合する。SupportedBasisMap.zeroは任意の台で成立する一方、
SupportedBasisMap.no_single_image_to_empty_supportは全台から空台への指定非零基底像が
台適合を満たせないと示す。SubsetChainContractionの成立側は二つの原始constructor、
不成立側はno_contraction_with_zero_r0であり、旧選択頂点があるとき指定r0=0がrs0=idを
満たせないことを基底で評価する。primitive比較の不成立instanceはCycle1のIncidenceObstructionにある。

### 今回の明示spine

Cycle1受理spineに加え、以下の282明示宣言を今回のspineとして固定する。
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
SupportedBasisMap.no_single_image_to_empty_support
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
SubsetChainContraction.no_contraction_with_zero_r0
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
EdgeSubdivision.occurrenceFintype
EdgeSubdivision.retainedEdgeFintype
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
各module末尾の標準公理検査は成功した。282宣言の全 `#print axioms` をまとめて照会し、
source/spine/log集合に欠落・余剰はない。propext/Classical.choice/Quot.soundだけであり、
sorryAxはない。axiom照会ログSHA-256: `03874ce99a1fc14536e21d979b442015cf428a4e8b11c7cd5a6188e93068b9b3`。

公式focused経路でもEdgeSubdivisionとEdgeContractionの単一file checkが成功した。
新規9manifest行のmodule/source対応は全件正しい。

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

## Cycle 2 acceptance / Cycle 3 selection

Cycle2はPR5275 final head `0c85defb6676e97fd6b153e14346d5c27b72cdde` を独立数学2/Lean2査読、
非中心5項目の直接修正確認、root acceptance、必須CI成功の後に受理した。
merge `d41fd4ef340d5839694e90142de3dc429372e5d6`。
査読・受理コメント: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5275#issuecomment-6021665035 。
Issue同期: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272#issuecomment-6021720866 。
resultはproof-checkpointであり、元のP3全終了条件とその未完欄は維持する。

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 3
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: d41fd4ef340d5839694e90142de3dc429372e5d6
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: Cycle2 accepted proof-checkpoint / Issue comment6021720866
  proof_dag_predecessors: [P1, P2, Cycle2.SubsetChainContraction, G133.zeroExtension]
  milestone: GOAL T0/B/Dのreading pullbackと支持セル名同型を実生成比較の標準同値へ接続
  proof_obligations:
    - 原始セル名全単射・incidence・chart台逆像から比較を生成
    - 全射因子を使用してchart非空性、K1辺/面台逆像、全Aで選択セル全単射を生成
    - 同じ基底名のr/sと零h、両逆・chain式を原始表から生成
    - 全Aの標準HomotopyEquivと同じ実subset比較の全次数一致・H1読み戻し
    - 粗adequacyから細adequacy、同じLaw/valueの座標輸送と実Law比較の全次数同値
  exit_criteria:
    - 任意reading比較のpullback constructorと同readingの支持名前同型constructorがある
    - 全Aと全Lawの三次数で逆を構成し、同じ実比較の標準同値/旧H1同型に接続する
    - Source/LawValue有限性や非空A等の追加仮定なし、入力にchain式や診断同型を持たない
    - focused checks、全明示宣言axiom audit、共通scan、独立PR review、acceptanceを通す
  selection_reason: 逆縮約復元の表示同型にも必要な共通依存を閉じ、真のreading変更のW1へ進む
  expected_result_type: proof-obligation-discharged
  lean_targets: [FaceRelationSubdivision/CellPresentationEquiv.lean, FaceRelationSubdivision/ReadingPullback.lean]
  risks: [支持選択の逆に因子全射性が必要, 値の等式だけでLaw座標や実射を代替しない]
  unchecked: [P3逆pattern/lift, P4有限合成/一般Law/cone, P5 E/W, 全目標完了監査]
```

### Cycle 3 proof DAG / premise mapping

| 固定条項 | 原始入力 → 構成・使用先 | 分類 |
| --- | --- | --- |
| T0/B §5：任意reading比較 | `readingPullback` は同じセル表、非空chart台を因子全射から構成。`readingPresentation` が同じ名前とincidenceを放電 | 本文由来reading・非空台、構成放電 |
| B：セル名・台を保つ表示同型 | `CellRename.nerve/supported/presentation` が任意の名前全単射から端点・三辺・台・有限性を生成 | 本文由来名前全単射、他条件放電 |
| B：全Aの選択セル | `edgeSupport_eq/faceSupport_eq` はK1。`selected_iff/selectedEquiv` は因子全射と逆像から両方向を生成 | 放電済み |
| B：r/s/h、chain式と両逆 | `r0/1/2` は選択セルのFinsupp延長、逆は同じ逆セル名、h=0。`r*_eq_generated`、`r_comm*`、`inverse_comm`、`chainContraction` | 放電済み、収縮recordは出力 |
| D：同じ実subset比較 | `rHom_eq_generated`、`cochainHomotopyEquiv_hom`、`homologyIso_hom`、`oldH1ComparisonIso_hom` | 全三次数・全標準次数・既存H1へ接続 |
| T0：細adequacy | `fineAdequate` はG-133 `adequate_of_coarser` を使い粗adequacyから生成 | 粗adequacy本文由来、細は放電 |
| D：実Law座標 | `coordinateEquiv` は同じセル/Law/valueを保持し、発生証明を降下と因子全射から生成。`lawCochain*_eq_generated` は独立生成座標式と照合 | 放電済み、Law値型有限性を追加しない |
| D：各Law/valueラベル | `blockCoordinateEquiv` は同じ座標全単射を各ラベルへ制限。`blockCochainEquiv_toHom` と `blockZeroExtensionIso_hom` は同じ実生成Hom | 放電済み、別ラベルの重複度保持 |
| D：新比較クラスのG-133接続 | `LawFiberBridge` は新比較の三次数自然性を既存対象同型へ接続し、実block/fiber Homと標準錐の同じ正方形を証明 | 放電済み、旧比較を入力にしない |
| B/D：各LawのH0/H1/H2 | `law/block/fiberHomologyIso_hom` は同じ実生成Homの全整数次数同型。`law/blockH1Equiv_apply` と `fiberOldH1Iso_hom` は既存商の実射 | 放電済み |

`CellPresentationEquiv` の入力fieldは、セル名全単射、原始端点・三辺、chart台逆像である。
chain式・保存結論・診断同型は入力にない。`readingPresentation` と `CellRename.presentation`
が正instance族を与え、`no_presentation_with_incompatible_chart` が指定dataの台不適合から
certificate不存在を証明する。一般表示同型の各fieldは支持輸送・選択セル構成・
原始比較のincidence・生成chain式に使用される。`inverse_comm` の可換式は一般bridgeの
方向仮定であり、ここでは原始生成比較から放電する。

Cycle3の実装targetsには、当初の二moduleに加え、同じ終了条件の名前constructorを所有する
`CellRename`、新比較のG-133射接続を所有する `LawFiberBridge`、各Lawラベルの両逆を所有する
`LawPresentation` を含める。milestoneと終了条件は変更しない。
P3の原始逆縮約patternとlift選択、P4有限合成・一般有限和Law比較・cone/defect、
P5 E/W、全目標完了監査は未完として継続する。

### Cycle 3 explicit declaration spine

130明示宣言をsourceから列挙し、全件axiom照会の対象とする。

```text
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.edgeSupport_eq
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.faceSupport_eq
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.comparison
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.comparison_chart
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.comparison_edge
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.comparison_face
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.subsetMapsTo
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.selected_iff
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.selectedEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.selectedEquiv_val
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chartSelected
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.edgeSelected
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.faceSelected
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chartSelected_val
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.edgeSelected_val
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.faceSelected_val
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r0_single
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r0_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r1_single
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r1_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r2_single
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r2_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r_comm01
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r_comm12
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.inverse_comm
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chainContraction
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.cochainHomotopyEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rHom_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.homologyIso
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.homologyIso_hom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.oldH1ComparisonIso
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.oldH1ComparisonIso_hom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r0_symm_single
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chainContraction_r0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chainContraction_s0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r1_symm_single
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chainContraction_r1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chainContraction_s1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.r2_symm_single
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chainContraction_r2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chainContraction_s2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chainContraction_h0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chainContraction_h1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.cochainHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.cochainHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.readingPullback
AAT.AG.FaceRelationSubdivision.readingPullback_nerve
AAT.AG.FaceRelationSubdivision.readingPullback_chartSupport
AAT.AG.FaceRelationSubdivision.readingPresentation
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.fineAdequate
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.coordinateEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.coordinateEquiv_cell
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.coordinateEquiv_law
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chartCoordinateEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.edgeCoordinateEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.faceCoordinateEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chartCoordinateEquiv_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.edgeCoordinateEquiv_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.faceCoordinateEquiv_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochain0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochain0_apply
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochain0_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochain1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochain1_apply
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochain1_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochain2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochain2_apply
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochain2_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochainEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawCochainEquiv_toHom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawZeroExtensionIso
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawZeroExtensionIso_hom
AAT.AG.FaceRelationSubdivision.CellRename.nerve
AAT.AG.FaceRelationSubdivision.CellRename.supported
AAT.AG.FaceRelationSubdivision.CellRename.chartSupport
AAT.AG.FaceRelationSubdivision.CellRename.edgeLeft
AAT.AG.FaceRelationSubdivision.CellRename.edgeRight
AAT.AG.FaceRelationSubdivision.CellRename.faceEdge0
AAT.AG.FaceRelationSubdivision.CellRename.faceEdge1
AAT.AG.FaceRelationSubdivision.CellRename.faceEdge2
AAT.AG.FaceRelationSubdivision.CellRename.presentation
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.no_presentation_with_incompatible_chart
AAT.AG.FaceRelationSubdivision.lawBlockFiber_comparison_square
AAT.AG.FaceRelationSubdivision.lawBlockFiberZeroExtensionIso_natural
AAT.AG.FaceRelationSubdivision.lawBlockFiberConeIso
AAT.AG.FaceRelationSubdivision.lawFiberComparison_canonical
AAT.AG.FaceRelationSubdivision.subsetComparisonZeroExtension_square
AAT.AG.FaceRelationSubdivision.lawBlockSelectedSubsetZeroExtensionIso
AAT.AG.FaceRelationSubdivision.lawBlockSelectedSubsetZeroExtensionIso_natural
AAT.AG.FaceRelationSubdivision.lawBlockSelectedSubsetConeIso
AAT.AG.FaceRelationSubdivision.lawBlockCanonicalConeIso
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.coordinateEquiv_label
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCoordinateEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chartBlockEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.chartBlockEquiv_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochain0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochain0_apply
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochain0_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.edgeBlockEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.edgeBlockEquiv_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochain1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochain1_apply
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochain1_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.faceBlockEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.faceBlockEquiv_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochain2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochain2_apply
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochain2_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochainEquiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockCochainEquiv_toHom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockZeroExtensionIso
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockZeroExtensionIso_hom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawH1Equiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawH1Equiv_apply
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawHomologyIso
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawHomologyIso_hom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockH1Equiv
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockH1Equiv_apply
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockHomologyIso
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.blockHomologyIso_hom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.fiberZeroExtensionIso
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.fiberZeroExtensionIso_hom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.fiberHomologyIso
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.fiberHomologyIso_hom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.fiberOldH1Iso
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.fiberOldH1Iso_hom
```

新規source SHA-256:

- `CellPresentationEquiv.lean`: `480e04916a2569a319e37a2831c4f32bf655567e3dd21975bc735d1ca2e26c91`
- `ReadingPullback.lean`: `4758f84b4d9ca13b8ca22939a496760d92c1a8c7383a17fd40d1e2cdb7a58848`
- `CellRename.lean`: `c1be3c0792cdbb9cf738fb1daf088c90cc2d9ec6ba642e5376f67119be03e384`
- `LawFiberBridge.lean`: `fd7adac7c9aba8ce26f1fbc95301d99ee84c368538b5a2fc09c24c7dba4044e6`
- `LawPresentation.lean`: `655feff1d39a16b7bf1e52e7e087600414f36853f3cfe9e713159bc03664875f`

### Cycle 3 validation / result proposal

5新規moduleをそれぞれ単一file checkで検証し、公式focused経路でも
`LawPresentation.lean` と `CellRename.lean` を確認した。全module末尾の標準公理検査は成功。
130明示宣言の全 `#print axioms` 照会はsource/spine/query/log間で欠落・余剰・重複がなく、
propext/Classical.choice/Quot.soundだけである。axiom照会ログSHA-256:
`732bda1c2e11fcf0305bafa57a0f6804a6de21ffa8f32e69f5686d2a8ec3b0f4`。
placeholder、hidden/BiDi、privacy、本体→Research import、diff whitespaceのscanはclean。
manifestは新規5行をmodule/sourceのTSVで登録し、Research全体buildとaggregate rootは実施していない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - 任意reading逆像変更と任意セル名取り直しを原始表から生成
    - 全Aの支持セル全単射、r/sと零h、chain式、両逆を生成
    - 全三次数の同じ実subset比較と標準HomotopyEquiv/全homology/旧H1商同型を照合
    - 粗adequacyから細adequacy、Law座標の同じcell/law/value全単射、各ラベル全単射を生成
    - 同じ実Law/block/fiber Homの全標準次数同型、実H1商の読み戻しを構成
    - 新比較クラス用のblock/fiber/標準錐正方形とcanonical逆像への射接続を証明
  exit_criteria_status:
    - 数学的構成・接続の全条件達成、追加仮定なし
    - focused/axiom/共通scan達成
    - 独立PR review/acceptance/CIは固定PR headに対する監査で判定する
  split_reason: none
  completion_candidate: no
  lean_artifacts:
    - FaceRelationSubdivision/{CellPresentationEquiv,ReadingPullback,CellRename,LawFiberBridge,LawPresentation}.lean
  claim_mapping:
    source_labels: [GOAL T0/B/D, elementary-moves §5, GOAL Bの支持セル表示同型]
    undischarged_assumptions: []
    acceptance_point: reading pullbackと支持セル名同型という選定した到達点、固定GOAL全体は未完
    port_status: unported
  audits:
    structure_field_escape: none-found
    route_integrity: pass
    vacuity: none-found
    one_way_as_equivalence: none-found
    next_obligation: P3原始逆patternとlift、P4一般有限和Law/有限合成/cone/defect、P5 E/W
```

### Cycle 3 非中心指摘への対応

[初回独立査読](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5276#issuecomment-6022191250) は数学2本が `No major findings`、Lean 2本が
`Minor issues`。中心指摘は0、重複統合した非中心指摘は、Propの証明である
`subsetMapsTo` と `fineAdequate` の2宣言を `theorem` とする1件であった。
名前・型・引数・証明本体を保って変更した。`fineAdequate` では元のdefが証明本体から
取り込んでいた `h` と `hc` を `include` で明示した。新しい仮定・宣言は追加していない。
修正した2moduleと依存する `LawPresentation` / `CellRename` の単一file check、
全130宣言の公理照会を再実施した。直接対応の資格と解消は固定修正headの新規独立確認で判定する。


## Cycle 3 acceptance / Cycle 4 selection

Cycle3はPR [#5276](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5276)、
final head `d15101a6e85d62ea74d85db8328d5dc574e06034`、merge
`48d46a1e57b740bba35c6e02ea9e174293fe8c39`で受理した。
初回の非中心1項目を修正し、直接対応資格喪失を受けて新規4laneで正式再査読。
全4本 `No major findings`、[最終受入れ](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5276#issuecomment-6022476554)。
全130宣言公理監査・focused・scanと全8CI checks成功。Research全体buildは未実施、
本体実build/kernel auditはResearchonly selectorでskipped。

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 4
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: 48d46a1e57b740bba35c6e02ea9e174293fe8c39
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: Cycle3 accepted / fixed target B・elementary-moves §4
  proof_dag_predecessors: [TriangleAddition, EdgeSubdivision, SubsetChainContraction, CellPresentationEquiv]
  milestone: P3原始逆縮約の両局所patternから復元入力と元表示への同型・同じ支持収縮を生成
  proof_obligations:
    - 指定局所セルのfreshness・端点・三辺・chart台等号・全接続を原始条件で保持
    - 三角形逆patternの保持セルと全incidence・K1台を構成
    - 辺分割逆patternの保持セル・共通辺・中心面・全出現位置を構成
    - 復元入力の正操作と元入力のセル/支持表示同型を原始条件から生成
    - 同じr/s/hを表示同型で移し全Aのchain式・両逆・実subset Homと標準同値へ接続
    - 正操作の出力で両patternが実現し、追加接続がある指定dataは拒否されることを証明
  exit_criteria:
    - 両patternの復元・両逆と原始incidence/台同型をLeanで閉じる
    - 全Aの同じ基底収縮・全標準次数同型・実H1への接続
    - 成立入力族と全接続条件不成立の実証、focused/全宣言axiom/共通scan
  selection_reason: supplied旧入力/診断同型なしの原始逆patternがP3と任意有限列の未接続node
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - FaceRelationSubdivision/PrimitiveTriangleInverse.lean
    - FaceRelationSubdivision/PrimitiveSubdivisionInverse.lean
    - FaceRelationSubdivision/{TriangleInverseContraction,SubdivisionInverseContraction}.lean
  risks: [全接続の完全性, 重複位置を潰さない復元, 同じ射の表示transport, 逆操作の方向]
  unchecked: [独立PR review・acceptance・CIは固定headで判定]
```

Cycle2で固定したP3全体の終了条件は保持する。本cycleで原始逆patternの幾何・支持収縮を
扱い、持ち上げ選択と一般有限和Law座標の生成・有限合成・E/Wは未完義務として残す。

### Cycle 4 claim / premise / route evidence

| 固定条項と構成義務 | 原始入力と放電 | 同じ射への接続 |
| --- | --- | --- |
| B・elementary §4 三角形逆pattern | `TriangleInversePattern` は局所セル名・端点・三辺・台等号・全接続のみ。`restored` は保持セル部分型から構成し、頂点freshnessは基底辺と全接続から導く | `presentation` の全セル名全単射・5 incidence・chart台からK1辺面台の同型を生成 |
| B・elementary §4 辺分割逆pattern | `SubdivisionInversePattern` は全対角名・三角面名・中心面とFin3位置・対角辺全出現iffを保持。出現型の有限性は対角名の単射と有限辺から導く | `occurrenceEquiv` が復元共通辺の全出現と原始指定出現の両逆。`presentation` は全名前・incidence・chart台を復元 |
| B 全Aのr/s/h | 正操作の既受理基底r/s/hと、原始復元表示から`sameR0/1/2`を構成。`renameFine` が同じr/s/hを明示共役しchain式・rs・sr補正式を証明 | 両`chainContraction`の8計算成分は旧有限基底式と表示の合成。標準同値のhom/invは同じrHom/sHom |
| A/D 新比較との接続 | 正操作の原始collapseと原始逆表示のOption表を`collapse`で直接合成する。実cochain射を逆算して原始表を定義しない | 両`rHom_eq_generated` が全3成分の実subset Hom等号。`homologyIso_hom_generated`・`oldH1ComparisonIso_hom_generated` は全標準次数・既存H1商の同じ実写像 |
| B 逆操作の方向 | `inverseCochainHomotopyEquiv` は構成済み二射と二homotopyを交換する | `inverseHomologyIso_hom` と `inverseOldH1ComparisonIso_hom` は逆縮約方向の実sHom/h1Map。順方向も同じrHom |
| 原始patternの成立・拒否 | `ofAddition`・`ofSubdivision` は任意旧入力/指定辺の正操作から全fieldを生成。追加の三角形操作で第三辺がfresh頂点へ接続する | `double_addition_rejects_first_pattern`・`addition_rejects_subdivision_pattern` は最初の指定局所名のpatternを拒否。別局所名のpatternまで否定しない |

material premise: `Source/q/N` と有限supported nerveの原始幾何はambient-boundary。
各patternのfreshness・端点・三辺・chart台・全接続は設計§4のdirection-hypothesisであり、
成立族では`ofAddition/ofSubdivision`が原始正操作入力から放電する。旧入力、表示同型、
収縮、H1同型、錐消滅をpattern fieldへ持ち込まない。汎用`renameFine`の収縮と表示可換性は
direction-hypothesisだが、両適用点で既受理正操作と今回の表示constructorから放電する。
出現型のFintypeを追加仮定にせず、`occurrenceFintype`が原始対角単射から生成する。
名前の有限choiceは削除族の等号判定と全出現iffに使用し、H1診断から名前を選ばない。
loopの両端点一致、同一面内の三重出現、空出現、空A、空辺台を除外する仮定はない。
指定された非零H1のW1–W3計算はP5の未完義務として維持する。

依存はCycle2受理版のTriangleGeometry/TriangleContraction/EdgeSubdivision/EdgeContraction、
IncidenceBasis/SubsetContraction/SupportedBasis/ChainDualMap、Cycle1受理版のSubsetComposition、
Cycle3受理版のCellPresentationEquivを使用する。各sourceはその受理版から変更しない。
受理refは本reportの各cycle acceptance節。mathlibの`Finsupp.domLCongr`、
`Equiv`/`LinearEquiv`両逆と等号transport、`HomotopyEquiv.symm/toHomologyIso`を固定版で用いる。
新比較の原始Option表から既存実subset比較を生成するrouteと、原始r/s/hを双対化するrouteを
独立に構成し、全3成分の等号で接続した。一般有限和Law座標とその全ラベル/錐接続はP4で扱う。

### Cycle 4 accepted-spine proposal

以下は新規sourceの明示宣言全件(構造の自動生成fieldを除く)で、helper・instanceも含む。
原始fieldを含む各module末尾の標準公理検査も別に行う。

| module | 明示宣言数 |
| --- | ---: |
| `PrimitiveCellDeletion` | 10 |
| `PrimitiveTriangleInverse` | 26 |
| `PrimitiveSubdivisionInverse` | 42 |
| `PresentationInverse` | 23 |
| `ContractionTransport` | 2 |
| `TriangleInverseContraction` | 29 |
| `SubdivisionReconstruction` | 15 |
| `SubdivisionInverseInstances` | 6 |
| `SubdivisionInverseContraction` | 29 |

```text
AAT.AG.FaceRelationSubdivision.deleteOneEquiv
AAT.AG.FaceRelationSubdivision.deleteOneEquiv_old
AAT.AG.FaceRelationSubdivision.deleteOneEquiv_new
AAT.AG.FaceRelationSubdivision.deleteTwoEquiv
AAT.AG.FaceRelationSubdivision.deleteTwoEquiv_old
AAT.AG.FaceRelationSubdivision.deleteTwoEquiv_false
AAT.AG.FaceRelationSubdivision.deleteTwoEquiv_true
AAT.AG.FaceRelationSubdivision.deleteFamilyEquiv
AAT.AG.FaceRelationSubdivision.deleteFamilyEquiv_old
AAT.AG.FaceRelationSubdivision.deleteFamilyEquiv_new
AAT.AG.FaceRelationSubdivision.TriangleInversePattern
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.OldChart
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.OldEdge
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.OldFace
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.retained_left
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.retained_right
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.retained_slot
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.oldLeft
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.oldRight
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.oldSlot
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.restoredNerve
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.restored
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.restoredBase
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.vertex_ne_left
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.vertex_ne_right
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.restored_chartSupport
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.restored_edgeSupport
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.restored_faceSupport
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.presentation
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.presentation_old_edge
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.presentation_connector
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.presentation_second
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.presentation_face
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.ofAddition
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.no_pattern_with_extra_edge
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.double_addition_rejects_first_pattern
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.occurrenceFintype
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.triangle_injective
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.position_slot
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.position_injective
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.removedEdge
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.removedEdge_injective
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.OldChart
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.RetainedEdge
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.OldFace
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.OldEdge
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.retained_ne_connector
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.retained_ne_second
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.retained_left
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.retained_right
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldSlot_ne_connector
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldSlot_ne_second
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldLeftVertex
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldRightVertex
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldLeft
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldRight
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldSlot
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldSlot_of_diagonal
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldSlot_eq_common_iff
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldSlot_of_no_diagonal
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldSlot_left
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldSlot_right
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.restoredNerve
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.restored
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.commonEdge
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.restored_chartSupport
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.restored_commonSupport
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.restored_faceSlot
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.positionFace
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.toOccurrence
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.ofOccurrence
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.ofOccurrence_slot
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.ofOccurrence_toOccurrence
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.toOccurrence_ofOccurrence
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.occurrenceEquiv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.occurrenceEquiv_apply
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.occurrenceEquiv_symm_apply
AAT.AG.FaceRelationSubdivision.self_factor_eq_id
AAT.AG.FaceRelationSubdivision.self_preimage
AAT.AG.FaceRelationSubdivision.linearEquiv_square_cast
AAT.AG.FaceRelationSubdivision.linearEquiv_cast_eq
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.symmSelf
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.symmSelf_chart
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.symmSelf_edge
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.symmSelf_face
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR_comm01
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR_comm12
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameContraction
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR0_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR1_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR2_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR0_symmSelf
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR1_symmSelf
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameR2_symmSelf
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameHom
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sameHom_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.inverseDual_eq_symmSelf
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.renameFine
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.renameFine_rHom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.chainContraction
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.chainContraction_r0
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.chainContraction_r1
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.chainContraction_r2
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.chainContraction_s0
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.chainContraction_s1
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.chainContraction_s2
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.chainContraction_h0
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.chainContraction_h1
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.rHom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.sHom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.cochainHomotopyEquiv
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.cochainHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.cochainHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.homologyIso
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.homologyIso_hom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.oldH1ComparisonIso
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.oldH1ComparisonIso_hom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.collapse
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.rHom_eq_generated
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.homologyIso_hom_generated
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.oldH1ComparisonIso_hom_generated
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.inverseCochainHomotopyEquiv
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.inverseCochainHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.inverseCochainHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.inverseHomologyIso
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.inverseHomologyIso_hom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.inverseOldH1ComparisonIso
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.inverseOldH1ComparisonIso_hom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.retainedEquiv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.retainedEquiv_symm_apply
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.retainedEquiv_apply_of_val_eq
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.recoveredEdgeEquiv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.recoveredFaceEquiv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.recoveredEdge_old
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.recoveredEdge_connector
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.recoveredEdge_second
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.recoveredEdge_diagonal
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.recoveredFace_old
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.recoveredFace_triangle
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.recovered_centerEdge
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.retained_left_val
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.retained_right_val
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.presentation
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.centerEdge_eq_diagonal_iff
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.center_slot
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.center_not_connector_second
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.ofSubdivision
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.no_pattern_with_extra_edge
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.addition_rejects_subdivision_pattern
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.chainContraction
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.chainContraction_r0
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.chainContraction_r1
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.chainContraction_r2
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.chainContraction_s0
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.chainContraction_s1
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.chainContraction_s2
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.chainContraction_h0
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.chainContraction_h1
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.rHom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.sHom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.cochainHomotopyEquiv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.cochainHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.cochainHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.homologyIso
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.homologyIso_hom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldH1ComparisonIso
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldH1ComparisonIso_hom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.collapse
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.rHom_eq_generated
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.homologyIso_hom_generated
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.oldH1ComparisonIso_hom_generated
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.inverseCochainHomotopyEquiv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.inverseCochainHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.inverseCochainHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.inverseHomologyIso
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.inverseHomologyIso_hom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.inverseOldH1ComparisonIso
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.inverseOldH1ComparisonIso_hom
```

新規source SHA-256:

- `PrimitiveCellDeletion.lean`: `911d0747f09d1f227a411419799cc44843b8c38bbb8bb7724dc3ed1fa292000e`
- `PrimitiveTriangleInverse.lean`: `dcef554930bab020f90de2f7f21b7a98338de174646118c82c3e697cc2241ab9`
- `PrimitiveSubdivisionInverse.lean`: `2b293bf12dd89acb9851c40938a88ee3eb6bc7749e5d6af36316474bd11be00e`
- `PresentationInverse.lean`: `3d0ed75e164caeec5bf9dc9509d303f5a5b9c909dc0a2142805dbdd475152b91`
- `ContractionTransport.lean`: `0bd21d90342fea243ad73d7aaa3769444cd5bbc240f87ca534a6db8d59b9a7c5`
- `TriangleInverseContraction.lean`: `4519507e161625df8aa6f6caad5f919ca5db7b63c76512c34d6ad03e70da6a3a`
- `SubdivisionReconstruction.lean`: `83f8b2b45b34652e9ecea090be6de460f56ec8e6e51e512ca9ec1b1ef320f10f`
- `SubdivisionInverseInstances.lean`: `a49da06decf3641368f9203c6307f7d20f0a68176655098dac6a94bda4101287`
- `SubdivisionInverseContraction.lean`: `a172a973b12acb7c1648f6461f5139be9dbc7f2ce3c998d4fb262da6120f668b`

### Cycle 4 validation / result proposal

新規9moduleをそれぞれ必要な単一file checkで検証し、公式focused経路で
`TriangleInverseContraction.lean`・`SubdivisionInverseContraction.lean`・
`SubdivisionInverseInstances.lean` を確認した。全9moduleの標準公理検査は成功。
182明示宣言を全件 `#print axioms` し、source/spine/query/logの集合一致、欠落・余剰・重複なし、
propext/Classical.choice/Quot.soundのみを確認した。axiom log SHA-256:
`deaf34f01b365d1ad15e3d1e654602c023425009933d589dd5f6c47a8d753b3a`。
placeholder、hidden/BiDi、privacy、manifest TSV/実在/一意性、diff whitespace scanはclean。
追加importは9つのResearchLean source内だけで、FormalからResearchへのimportは追加していない。
Research全体build、aggregate root、全file loop、本体full buildは未実施。
CIと独立査読は固定PR headに対するgateで判定する。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - 両原始逆patternから旧入力・全セル表示同型と支持を構成
    - 全面内出現の復元両逆と共通辺K1台を構成
    - 全Aの同じr/s/hを移送しchain式・両逆・補正式を生成
    - 順逆両方向の標準HomotopyEquiv/全homology/既存H1商の実写像を照合
    - 原始Option表の直接生成比較と同じ実rHomを全3成分で照合
    - 任意正操作の全接続pattern生成と追加第三辺による指定pattern拒否を証明
  exit_criteria_status:
    - 選定した到達点の全数学的条件と検証条件を達成
    - 独立PR review/acceptance/CIは固定PR headで判定
  split_reason: none
  completion_candidate: no
  claim_mapping:
    source_labels: [GOAL B原始逆縮約, elementary-moves §4, A/Dの実subset比較接続]
    undischarged_assumptions: []
    acceptance_point: 選定した両原始逆patternの到達点、元のP3全終了条件と全GOALは未完
    port_status: unported
  audits:
    structure_field_escape: none-found
    route_integrity: pass
    vacuity: none-found
    one_way_as_equivalence: none-found
    next_obligation: P3持ち上げ選択、P4一般有限和Law/有限合成/制限/cone/defect、P5 E/W1-W3
```

### Cycle 4 非中心findingへの修正

[初回4査読](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5277#issuecomment-6023355173) は数学BがNo major findings、数学A/Lean A/Lean BがMinor issues。
中心0、重複統合した非中心1件は、`recovered_centerEdge`内の保持辺全単射の定義展開。
指名された公開補題`retainedEquiv_apply_of_val_eq`を追加し、当該証明から定義展開を除いた。
既存theorem/def/instanceのsignature・def/instance本体・値・import方向・statusは変更しない。
追加補題の標準公理と全182宣言照会、修正source/下流endpointのfocused、共通scanを確認した。
修正範囲と直接対応の資格・finding解消は、新規の単一確認担当が独立に判定する。


## Cycle 4 acceptance / Cycle 5 selection

Cycle 4は[PR #5277](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5277)で受理。
final head `e25e9b82b6d3016e21423a9a5cc1663fd9c3e0e7`、merge
`0a250d1d3aa39be9a8f535a21530a37457af626b`。
[初回4本・資格を満たす新規直接確認・最終受入れ](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5277#issuecomment-6023355173)、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272#issuecomment-6023602728)。
初回中心0/統合非中心1を公開API補題で修正し、直接確認が資格・解消を確認。
selected resultはproof-obligation-discharged、全targetはtarget-proof-checkpoint。
最終headの8CI checks成功。Research integrityを実行、Formal full build/kernel等は
Research-only selectorによりSKIPPED。Research全体build/aggregate/全file loopは未実施。
全182宣言は標準3公理のみ、Formal未移植。

以下はCycle 5の実装前selection。Cycle 2の元P3全終了条件は維持する。

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 5
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: 0a250d1d3aa39be9a8f535a21530a37457af626b
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: Cycle 4受入れおよびIssue同期
  proof_dag_predecessors: [TriangleContraction, EdgeContraction, SupportedBasis, SubsetContraction, ThreeHomotopy, ZeroExtension]
  milestone: B/P3の指定三角面で結ばれる持ち上げ選択と同じH1読み戻し
  proof_obligations:
    - 原始t1の有限和と非零項の支持包含を両正操作について構成
    - s'=s+∂t+t∂と補正hから全Aのchain式・rs・srを証明
    - 指定旧辺と旧面の補正式を原始セル基底で評価
    - 実双対s'とsの標準cochainホモトピー・全homology・既存H1写像の一致
    - 三角形追加のcocycle道の等式とfresh頂点potential補正を全支持で証明
    - 分割の任意指定出現対角道の等式と同じH1読み戻し
  exit_criteria:
    - 上記全義務を原始幾何から生成して閉じる
    - 任意A、空支持、loop、重複出現を縮小しない
    - 全宣言axiom照会とfocused/scan、固定head独立査読を通過
  selection_reason: 受理済み両収縮からP3残義務の持ち上げ選択を直接閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [LiftVariation, TriangleLift, SubdivisionLift, CocycleNormalization]
  risks: [tを保存結論fieldに移さない, 実sHomの射一致, 旧面符号の反映, 非選択connectorの零補正]
  unchecked: [P4一般Law有限和, P4有限合成制限cone欠損, P5 E/W1-W3, 全target独立完了監査]
```

### Cycle 5 構成と固定条項の対応

到達点はB/P3・基本変形§7の指定持ち上げである。原始入力はreading上の任意N・eと、
分割では指定出現o。幾何を先に固定し、Aを後で任意に取る。Lawの有限和座標への一般拡張は
P4の残義務であり、このcycleで全B/C/Dを完了とはしない。

| 固定義務 | 構成・宣言 | 実写像への接続 |
| --- | --- | --- |
| s'=s+∂t+t∂と同じrの収縮 | `SubsetChainContraction.varyLift` | 同じr0/1/2、s0/1/2、h0/1の公開評価、chain/rs/sr全fieldを方向式から証明 |
| 三角形追加のe→f、指定道c+e2 | `TriangleAddition.liftT` / `liftedS1_target_basis` | 原始有限和の台包含、全Aの`liftedContraction_s1/s2` |
| 分割のe→-t_o、指定対角道d_o | `EdgeSubdivision.liftT` / `liftedS1_target_basis` | 任意o、原始有限和の台包含、全Aの`liftedContraction_s1/s2` |
| 各旧面の符号補正 | 両namespaceの`liftedS2_basis` | 位置0−位置1+位置2を個別評価。同面の重複出現を同一化しない |
| 補正面のr2像が零 | 両namespaceの`liftT_r2_zero` / `liftT_selected_r2_zero` | 原始collapse基底式から全Aへ零延長単射で制限 |
| 実s'とsの標準ホモトピー | `liftHomotopy` / 両`liftedHomotopy` | 同じ実sHomを零延長し、補正の次数1→0を0、2→1をdual tにする |
| 同じ全homology・既存H1読み戻し | `varyLift_homologyMap/h1Map` / 両`liftedContraction_homologyMap/h1Map` | G-133 oldH1Iso自然性で同じh1Mapそのものの等号を証明 |
| 同じr比較の保持 | 両`liftedContraction_rHom` | 受理済み原始collapseからの実rHomと同じ。代替比較を導入しない |
| cocycle道の評価 | 両`cocycle_path`と選択面constructor | 旧e選択から同じ台の実新面を選択し、既存targetSubsetComplex.d1を評価 |
| fresh頂点potential | `TriangleAddition.freshPotential_old/new` | 原始h0の同じ双対、旧頂点0・fresh頂点z(c) |
| 非選択connectorの零補正 | `no_fresh_of_no_connector` / `freshPotential_zero_of_no_connector` | 台等号からfresh座標も存在せず、同じpotential全体が零 |
| 補正後c=0・e2=旧e | `normalized_connector/second` | `normalized_eq_readback`から同じ実r/sの座標評価へ接続 |
| 代表の既存H1商での一致 | `cocycle_readback_class` / `normalized_readback_class` | 同じboundaryToCyclesのrangeに明示potentialの負を提示し、実mkQで等号 |

一般bridgeは出力recordCとt、r2t=0を方向仮定にする。両基本操作ではCを受理済み原始
constructorから生成し、tを原始セル表から生成、r2t=0を原始基底式から証明する。
実sHomの変更を結論fieldに受け取らない。指定出現がない分割には代替道の指定自体がなく、
既受理の通常sectionが全Aで存在する。代替道の定理は任意の指定oを量化する。
loop、任意旧面、符号の異なる重複出現、空のA・辺台・面台を除外しない。
空Sourceの辺指定操作のinstance不在はT0の意味通りで、全targetの空列はP4に残る。

### Cycle 5 material premise / provenance / proof-use

| premise | 分類 | 出所と使用・放電 |
| --- | --- | --- |
| Reading/N/e、K1、原始incidence | ambient-boundary | T0入力。支持t、原始微分、旧r/s/h生成へ使用 |
| 分割で指定したo | ambient-boundary | 固定§7の指定出現。独立名の面・対角辺への像へ使用 |
| 任意A | ambient-boundary | 原始像の支持制限・同じ実subset複体へ使用 |
| bridge Cの収縮式 | direction-hypothesis / 適用でdischarge-required | PR #5275の両原始収縮constructor。現在版は公開projection APIだけ追加、旧statement/証明/def値は不変 |
| 原始tと支持包含 | discharge-required | 両liftTで旧eと追加面のK1台等号から生成。tを手渡ししない |
| r2t=0 | direction-hypothesis / 適用でdischarge-required | 両liftT_r2_zero→selected_r2_zeroで同じcollapseから放電 |
| cocycle d1z=0 | direction-hypothesis | 比較する代表の定義通り。新面の道の等式とh0補正へ使用 |
| Homotopy/全homology/H1一致 | discharge-required | dualCellMapのadd/comp/微分API→threeHomotopy→mathlib homologyMap_eq→oldH1Iso_natural |
| potential補正の境界membership | discharge-required | 同じboundaryToCyclesへpotentialの負を明示し、Subtype/extと既存商mkQで証明 |

依存の追跡はCycle 2受入れ[PR #5275](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5275#issuecomment-6021665035)、
merge `d41fd4ef340d5839694e90142de3dc429372e5d6`のSupportedBasis/ThreeHomotopy/
RawSupportedChain/ChainDualMap/SubsetContraction/TriangleContraction/EdgeContractionと、
既記録G-133のZeroExtension.oldH1Iso_naturalまで。再利用する型・式・適用引数を確認した。
既存4sourceの今回差分は公開評価API25宣言の追加だけで、既存宣言のsignature・証明・
def/instance本体・値・import方向を変更しない。新旧全APIが現在source上で一致する。
mathlibのHomotopy.homologyMap_eqとSubmodule.Quotient.eqを固定mathlib版で使用する。

### Cycle 5 受理spine候補

新規4moduleの87明示宣言と、既存4moduleの新公開API25宣言の計112宣言を固定する。
その他の既存宣言は受理済みpredecessor。新規全sourceのassertは各module内の生成補助宣言も
検査する（LiftVariationのmacroは19、明示spineは18）。scaffoldを受理spineへ混ぜない。

```text
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_s0
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_s1
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_s2
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_h0
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_h1
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_r0
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_r1
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_r2
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_rHom
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_sHom_f0
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_sHom_f1
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_sHom_f2
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.liftHomotopy
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_homologyMap
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.varyLift_h1Map
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.cocycle_normalize
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.cocycle_readback_class
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftT
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftT_basis
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS1
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS2
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS1_raw
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS2_raw
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS1_basis
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS2_basis_image
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS1_selected
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS2_selected
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS1_target_basis
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS2_basis
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftT_r2_zero
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftT_selected_r2_zero
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedContraction
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedContraction_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedContraction_s1
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedContraction_s2
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedContraction_rHom
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedHomotopy
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedContraction_homologyMap
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedContraction_h1Map
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftT
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftT_basis
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS2
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS1_raw
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS2_raw
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS1_basis
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS2_basis_image
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS1_selected
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS2_selected
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS1_target_basis
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS2_basis
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftT_r2_zero
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftT_selected_r2_zero
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedContraction
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedContraction_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedContraction_s1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedContraction_s2
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedContraction_rHom
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedHomotopy
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedContraction_homologyMap
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedContraction_h1Map
AAT.AG.FaceRelationSubdivision.TriangleAddition.selectedNewFace
AAT.AG.FaceRelationSubdivision.TriangleAddition.selectedNewFace_val
AAT.AG.FaceRelationSubdivision.TriangleAddition.connectorOfFresh
AAT.AG.FaceRelationSubdivision.TriangleAddition.connectorOfFresh_val
AAT.AG.FaceRelationSubdivision.TriangleAddition.freshPotential
AAT.AG.FaceRelationSubdivision.TriangleAddition.freshPotential_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.freshPotential_old
AAT.AG.FaceRelationSubdivision.TriangleAddition.freshPotential_new
AAT.AG.FaceRelationSubdivision.TriangleAddition.no_fresh_of_no_connector
AAT.AG.FaceRelationSubdivision.TriangleAddition.freshPotential_zero_of_no_connector
AAT.AG.FaceRelationSubdivision.TriangleAddition.cocycle_path
AAT.AG.FaceRelationSubdivision.TriangleAddition.normalized_eq_readback
AAT.AG.FaceRelationSubdivision.TriangleAddition.normalized_readback_class
AAT.AG.FaceRelationSubdivision.TriangleAddition.selectedOldEdge
AAT.AG.FaceRelationSubdivision.TriangleAddition.selectedOldEdge_val
AAT.AG.FaceRelationSubdivision.TriangleAddition.selectedSecond
AAT.AG.FaceRelationSubdivision.TriangleAddition.selectedSecond_val
AAT.AG.FaceRelationSubdivision.TriangleAddition.rHom_connector
AAT.AG.FaceRelationSubdivision.TriangleAddition.rHom_second
AAT.AG.FaceRelationSubdivision.TriangleAddition.sHom_old
AAT.AG.FaceRelationSubdivision.TriangleAddition.normalized_connector
AAT.AG.FaceRelationSubdivision.TriangleAddition.normalized_second
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.selectedTriangle
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.selectedTriangle_val
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.cocycle_path
AAT.AG.FaceRelationSubdivision.dualCellMap_add
AAT.AG.FaceRelationSubdivision.dualCellMap_chainD1
AAT.AG.FaceRelationSubdivision.dualCellMap_chainD2
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.rHom_f0
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.rHom_f1
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.rHom_f2
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.sHom_f0
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.sHom_f1
AAT.AG.FaceRelationSubdivision.SubsetChainContraction.sHom_f2
AAT.AG.FaceRelationSubdivision.TriangleAddition.chainContraction_r0
AAT.AG.FaceRelationSubdivision.TriangleAddition.chainContraction_r1
AAT.AG.FaceRelationSubdivision.TriangleAddition.chainContraction_r2
AAT.AG.FaceRelationSubdivision.TriangleAddition.chainContraction_s0
AAT.AG.FaceRelationSubdivision.TriangleAddition.chainContraction_s1
AAT.AG.FaceRelationSubdivision.TriangleAddition.chainContraction_s2
AAT.AG.FaceRelationSubdivision.TriangleAddition.chainContraction_h0
AAT.AG.FaceRelationSubdivision.TriangleAddition.chainContraction_h1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.chainContraction_r0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.chainContraction_r1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.chainContraction_r2
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.chainContraction_s0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.chainContraction_s1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.chainContraction_s2
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.chainContraction_h0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.chainContraction_h1
```

現在の対象source SHA-256（既存sourceはAPI追加後の版）:

- `LiftVariation.lean`: `792d75aed58d1162ab7e8fcf45ee45fdef613464d94d2401d692443106884bdf`（今回の明示spine 18）
- `TriangleLift.lean`: `3ad9fab4b70814892709f567b6b5a412aac64a4d1a851592330b7fd8095f1288`（今回の明示spine 22）
- `SubdivisionLift.lean`: `37154f4410e01fa6d4378474445f7aba462b5ab507b3e8533f4b90e52215d0e7`（今回の明示spine 22）
- `CocycleNormalization.lean`: `07f3fb014244cbfb5ed00e37ceedc82ecc290bc1131de2a6315beebaacbc4e4b`（今回の明示spine 25）
- `ChainDualMap.lean`: `e630b42e46ba8df6ec285d34f5d34d0ad40c154447ed971e91765c24faa41edf`（今回の明示spine 3）
- `SubsetContraction.lean`: `f73e39ec95177c1a8cca4e5334fefb62d0f7fd11fea29b53d11f7ef265bf2b53`（今回の明示spine 6）
- `TriangleContraction.lean`: `8cb2eef0953e8942e74e43b19e7ebd65e030e884bf7bb016c52350e9c537ba6d`（今回の明示spine 8）
- `EdgeContraction.lean`: `40f704cddc1c9bbf6c53264eb66f3ac097c0fae8b3033142bce864c3bff486d2`（今回の明示spine 8）

### Cycle 5 validation / result proposal

新規4moduleと公開APIを追加した既存4moduleを必要な単一file checkで確認した。
公式focused経路でTriangleLift・SubdivisionLift・CocycleNormalizationを検査、
最後の商接続/API整理後にLiftVariationとCocycleNormalizationを再確認した。
112明示宣言すべてを#print axiomsし、source/spine/query/logの集合一致、重複・欠落・余剰なし、
標準propext/Classical.choice/Quot.soundのみを確認。log SHA-256: `998af15f79f4e2da8f602594b91bd02c9c1b48d64ea937d4323656df10f66a62`。
placeholder、hidden/BiDi、privacy、manifest TSV/実在/一意性、diff whitespace scanはclean。
新規module登録後のtracked import方向・公開artifact scanは固定commitでも検査する。
Research全体build、aggregate root、全file loop、本体full buildは未実施。独立PR査読/CIは
固定headのgateで判定する。Research証拠はFormal未移植、ArchSig実装を変更していない。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - 両原始tと支持を生成し指定旧辺/旧面の有限和補正を評価
    - 全Aの新section・同じr・補正hから全chain/rs/sr式を生成
    - 同じ実sHomの標準ホモトピーと全homology/既存H1写像等号
    - 選択新面のcocycle道とfresh potential、非選択成分の零補正
    - 補正後の実座標c=0/e2=旧e、同じ既存H1商での代表等号
  exit_criteria_status:
    - 選定した持ち上げ到達点の全数学的条件・検証を達成
    - 独立PR review/acceptance/CIは固定PR headで判定
  split_reason: none
  completion_candidate: no
  claim_mapping:
    source_labels: [GOAL B持ち上げ選択, elementary-moves §7, D既存H1への同じ実subset射接続]
    undischarged_assumptions: []
    acceptance_point: 選定した支持持ち上げ変更の到達点、元P3の各Law拡張と全targetは未完
    port_status: unported
  audits:
    structure_field_escape: none-found
    route_integrity: pass
    vacuity: none-found
    one_way_as_equivalence: none-found
    next_obligation: P4一般有限和Law/有限合成/制限/cone/defect、P5 E/W1-W3、別の全target完了監査
```
