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

## Cycle 3時点の全target proof obligation

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

新規4moduleの87明示宣言と、既存4moduleの新公開API25宣言、査読で名指しされた
所有moduleの公開API1宣言の計113宣言を固定する。
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
AAT.AG.ResolutionInvariance.TargetSupportedNerve.targetSubsetComplex_d0
```

現在の対象source SHA-256（既存sourceはAPI追加後の版）:

- `LiftVariation.lean`: `ba096624bb7a9b576a09d566262e757d623a15cd8d4359407fe6ce7a5625d733`（今回の明示spine 18）
- `TriangleLift.lean`: `3ad9fab4b70814892709f567b6b5a412aac64a4d1a851592330b7fd8095f1288`（今回の明示spine 22）
- `SubdivisionLift.lean`: `37154f4410e01fa6d4378474445f7aba462b5ab507b3e8533f4b90e52215d0e7`（今回の明示spine 22）
- `CocycleNormalization.lean`: `07f3fb014244cbfb5ed00e37ceedc82ecc290bc1131de2a6315beebaacbc4e4b`（今回の明示spine 25）
- `ChainDualMap.lean`: `e630b42e46ba8df6ec285d34f5d34d0ad40c154447ed971e91765c24faa41edf`（今回の明示spine 3）
- `SubsetContraction.lean`: `f73e39ec95177c1a8cca4e5334fefb62d0f7fd11fea29b53d11f7ef265bf2b53`（今回の明示spine 6）
- `TriangleContraction.lean`: `8cb2eef0953e8942e74e43b19e7ebd65e030e884bf7bb016c52350e9c537ba6d`（今回の明示spine 8）
- `EdgeContraction.lean`: `40f704cddc1c9bbf6c53264eb66f3ac097c0fae8b3033142bce864c3bff486d2`（今回の明示spine 8）

- `ASubnerveReduction.lean`: `88d14f9220df4cf630983ee77bef92daa171ed562678e2519aaccf302d113037`（査読修正の明示spine 1）

### Cycle 5 validation / result proposal

新規4moduleと公開APIを追加した既存4moduleを必要な単一file checkで確認した。
公式focused経路でTriangleLift・SubdivisionLift・CocycleNormalizationを検査、
最後の商接続/API整理後にLiftVariationとCocycleNormalizationを再確認した。
113明示宣言すべてを#print axiomsし、source/spine/query/logの集合一致、重複・欠落・余剰なし、
標準propext/Classical.choice/Quot.soundのみを確認。log SHA-256: `d20e39906194e80adc87d2d1fc68509b8bf849b9faacf2bf688683f3421ce4d3`。
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

### Cycle 5 非中心findingへの直接対応

初回固定head `07df221521f277de03ec69190263a3c1507489b2` の独立数学2本・Lean2本は
中心0/統合非中心1。3laneはNo major findings、Lean BはMinor issues。
[初回監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5278#issuecomment-6024205175)。
`cocycle_readback_class` のtargetSubsetComplex.d0直接展開を、findingで名指しされた
所有moduleの公開API `TargetSupportedNerve.targetSubsetComplex_d0` の適用へ置換した。
既存宣言のsignature、def/instance本体・値、import、statusは変更しない。追加宣言は
指名された補助API1件だけ。spine/件数/hashを同じ113宣言へ同期した。
修正所有module・LiftVariation・下流CocycleNormalizationの単一checkと公式focused、
全113axiom照会、共通scanを実施。資格とfinding解消は新規単一確認で独立判定する。


## Cycle 5 acceptance / Cycle 6 selection

Cycle 5は[PR #5278](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5278)で受理。
final head `a3ad908b46b9d872a5ce34127da7ae865e6f908c`、merge
`57df5cad964a7416b5e2c8461e33f4f2cac6f205`。
[初回独立4本・有資格直接確認・root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5278#issuecomment-6024205175)、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272#issuecomment-6024327920)。選定支持持ち上げ到達点はproof-obligation-discharged、全targetは
未完のtarget-proof-checkpoint。全113宣言標準3公理、focused/scan成功、最終8CI成功。
Research integrity実行、Formal build/cache/kernel/premiseはSKIPPED、Formal未移植。

以下はCycle 6の実装前selection。元P3/P4の全終了条件を維持する。

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 6
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: 57df5cad964a7416b5e2c8461e33f4f2cac6f205
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: Cycle 5受入れとIssue同期
  proof_dag_predecessors: [SupportedBasis, ChainDualMap, LawGeneratedComplex, ASubnerveReduction, GeneratedComparison]
  milestone: D/P4の同じreading上の原始有限和Law座標生成と実fiber比較への同定
  proof_obligations:
    - 非零原始セル像ごとに同じLaw/valueのCellCoordinateを入力支持から構成
    - 有限基底像と実双対有限和を独立生成しラベル重複を保持
    - 各ラベルfiberの同じselected原始射と座標有限和の実可換式
    - 原始微分のLaw座標化と既存lawGeneratedD0/D1の全射等号
    - 原始chain-map三成分から同じ実Law Homとblock/fiber射を構成
    - 正操作r/sの原始有限和へ適用し同じ旧生成rの全三成分と既存H1自然性へ接続
  exit_criteria:
    - 上記を任意adequate Law族で原始有限和から生成し閉じる
    - Value型有限性・全台・非空辺面台・端点相異性を追加しない
    - source/spine公理照会・focused/scanと固定head独立査読を通過
  selection_reason: 有限和へ送るs/hを実Law診断に接続する未放電D生成経路を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [LawFiniteCoordinates, LawFiniteFiber, LawFiniteDifferential, LawFiniteHom, ElementaryLawMaps]
  risks: [fiber共役を独立生成の代替にしない, 同じセルLaw値の保持, 実射の全三成分, 方向仮定の具体適用での放電]
  unchecked: [Law収縮標準ホモトピー全次数, 有限列と支持制限, cone欠損, E/W1-W3, 全target完了監査]
```

### Cycle 6 構成・固定条項・実射の対応

D/P4の独立生成を、同じreading上の任意支持有限和へ広げた。Law座標射をfiberの
共役から定義せず、非零係数ごとに同じセル像・Law名・値の発生証明を支持包含から作る。
そのsupport.attach上のFinsupp有限和を自由線形延長し、同じ射を実双対へ送る。
発生target witnessはproofであり、重複基底を作らない。別Law名の同じ台・値を同一化しない。

| 固定義務 | 宣言・構成 | 同じ実射への接続 |
| --- | --- | --- |
| 原始有限和のLaw座標生成 | `lawCoordinate/lawBasis/lawRaw/lawDual` | 同じセル/law/valueとラベルの公開API、原始係数による`lawDual_apply` |
| 同じラベルfiberの比較 | `lawFiberRead_joint_injective` / `lawDual_fiber` | 全座標へ読み取り等号を反映。原始selected有限和の同じ実双対 |
| 合成・加法・符号・恒等 | `lawDual_comp/add/neg/identity/eq_of_raw_eq/square` | 自分の原始finiteMapを先に生成し、同じ実cochainの全射等号 |
| 同じ実微分 | `lawFiberRead_d0/d1` / `lawDual_rawD1/rawD2` | 同じK1支持・セル・Lawから既存lawGeneratedD0/D1そのものを全射等号で同定 |
| 全三成分の実Law Hom | `lawFiniteHom` / `lawFiniteFiber_square` | 原始chain-map方向式→Law微分可換性、同じselected subsetFiniteHomへの全3成分正方形 |
| 独立block有限和 | `lawBlockCoordinate/Basis/Raw/Dual` / `lawDual_block` | 原始非零係数を同じ発生label subtypeへ送り、全Law/blockの射等号 |
| 実block Homと同じfiber | `blockFiniteHom` / `blockFiniteFiber_square` | 独立有限和3成分と既存block微分、同じfiber射との正方形 |
| 全Law/block実比較 | `lawBlockHom` / `lawFiniteBlock_square` | 同じblock projectionの全3成分が座標制限、独立Law射と独立block射の可換式 |
| 原始Option比較の特殊化 | `basisLaw0/1/2_eq_generated` / `basisLawHom_eq_generated` | 原始零/単一係数を評価して、同じ既存混在退化生成Homに全3成分一致 |
| 三角形追加・面付き辺分割r/s/h | 両namespaceの`lawR/lawS/lawH0/lawH1` | 受理済み原始r/s/hから生成、raw chain方向式を具体適用で放電 |
| 同じ正操作比較・逆写像 | 両`lawR_eq_generated` / `lawR_fiber/lawS_fiber` | 実rは既存同じcollapse生成Hom、実sは同じ支持収縮sectionと全3成分一致 |
| 既存H1商・標準接続 | 全`*_h1_square`、両`lawR/S_h1_fiber/h1_standard` | 同じh1Mapで可換。G-133 oldH1Equiv_naturalを同じ実Law射へ適用 |

一般有限和の原始I/Jは有限性を必要としないが、各像はFinsupp有限supportである。
実Law複体のconstructorでSource有限性とNの有限セルをT0通りに使う。
Law値型全体の有限性を仮定しない。全A選択、空A・空台、loop、重複出現は既受理の
支持基底生成をそのまま用いる。各fiberは同じlabelValueFiberであり、同台の別labelは別入力。
同じreading上の有限和生成がこの到達点であり、reading変更との任意有限列・Law収縮の
標準Homotopyと全次数同型・制限・全Law分解/錐/欠損の最終接続は後続P4に残す。
原始逆patternの表示輸送も受理済みであるが、逆縮約のLaw収縮最終endpointをここで完了としない。

### Cycle 6 material premise / provenance / proof-use

| material premise | 分類 | 出所・生成・使用 |
| --- | --- | --- |
| Source/reading、supported nerve・K1・ℚ | ambient-boundary | T0。lawDescend、原始r/s/h、支持セル・既存微分生成 |
| 任意adequate Law族 | ambient-boundary | T0で量化。same Law/valueの生成証明とlabelValueFiberに使用 |
| 汎用SupportedBasisMap有限像と台包含 | direction-hypothesis / 適用でdischarge-required | 非零係数→同じ支持target→出力CellCoordinate。具体r/s/hはPR5275の原始constructorが支持を生成 |
| 原始chain方向式h0/h1 | direction-hypothesis / 適用でdischarge-required | Law微分可換式と実Hom全fieldへ使用。正操作ではr_comm/s_comm原始基底証明から放電 |
| ラベル保存、微分一致、射一致、H1自然性 | discharge-required | 同じセル名/labelの座標等号、原始有限和、実双対と旧自然性からの出力 |
| block/fiber対象同値 | discharge-required / 受理predecessorで放電 | G-107 ASubnerveReductionの同じセル/label同値。射の定義に代用せず、独立有限和の項ごとの一致と実正方形を別に証明 |

方向仮定にH1同型・標準Homotopy・期待rankはない。汎用chain式を基本操作の入力fieldへ
移していない。両正操作constructorのraw r/s証明を実適用し、Law Homの可換性を生成した。
Lawブロックのhomotopy・全次数同型は今回の結論に追加していない。

依存: Cycle1のIncidenceComparison/GeneratedComparison/LawBlockComparisonと、
Cycle2 PR5275のSupportedBasis/RawSupportedChain/ChainDualMap/IncidenceBasis/
TriangleContraction/EdgeContraction、Cycle5 PR5278の公開projection API。
G-104 LawGeneratedComplex/LawValueBlockDecomposition、G-107 ASubnerveReduction、
G-133 ZeroExtension.oldH1Equiv_natural・cochainComp_h1Mapは既記録受理版/参照で追跡する。
現在の型・式・適用引数を確認した。今回の既存4sourceは公開API11宣言の追加だけであり、
既存signature、proof、def/instance本体・値、import方向は不変。
追加APIはdualのneg/zero、原始比較座標のcell3、block incidence underlying座標5、
subset微分d1の同じ射である。下流は所有moduleの公開APIを使い、直接展開しない。

### Cycle 6 受理spine候補

新規9moduleの118明示宣言＋既存4module公開API11宣言＝129宣言を固定する。
macroは生成補助宣言も検査するため、明示spine件数と区別する。

```text
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawCoordinate
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawCoordinate_cell
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawCoordinate_law
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawCoordinate_value
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawCoordinate_label
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawBasis
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawRaw
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawRaw_single
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_apply
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_apply_zero
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_apply_single
AAT.AG.FaceRelationSubdivision.lawFiberRead
AAT.AG.FaceRelationSubdivision.lawFiberRead_apply
AAT.AG.FaceRelationSubdivision.lawFiberRead_joint_injective
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.selected_single_attached
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.dual_selected_apply
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_fiber
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_eq_of_raw_eq
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_comp
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_identity
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_add
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_neg
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_square
AAT.AG.FaceRelationSubdivision.lawFiberRead_d0
AAT.AG.FaceRelationSubdivision.lawFiberRead_d1
AAT.AG.FaceRelationSubdivision.lawDual_rawD1
AAT.AG.FaceRelationSubdivision.lawDual_rawD2
AAT.AG.FaceRelationSubdivision.subsetFiniteHom
AAT.AG.FaceRelationSubdivision.subsetFiniteHom_f0
AAT.AG.FaceRelationSubdivision.subsetFiniteHom_f1
AAT.AG.FaceRelationSubdivision.subsetFiniteHom_f2
AAT.AG.FaceRelationSubdivision.lawFiniteHom
AAT.AG.FaceRelationSubdivision.lawFiniteHom_f0
AAT.AG.FaceRelationSubdivision.lawFiniteHom_f1
AAT.AG.FaceRelationSubdivision.lawFiniteHom_f2
AAT.AG.FaceRelationSubdivision.lawFiberHom
AAT.AG.FaceRelationSubdivision.lawFiberHom_f0
AAT.AG.FaceRelationSubdivision.lawFiberHom_f1
AAT.AG.FaceRelationSubdivision.lawFiberHom_f2
AAT.AG.FaceRelationSubdivision.lawFiniteFiber_square
AAT.AG.FaceRelationSubdivision.lawFiniteFiber_h1_square
AAT.AG.FaceRelationSubdivision.lawBlockRead
AAT.AG.FaceRelationSubdivision.lawBlockRead_apply
AAT.AG.FaceRelationSubdivision.blockFiberEquiv
AAT.AG.FaceRelationSubdivision.blockFiberEquiv_apply
AAT.AG.FaceRelationSubdivision.blockFiberEquiv_read
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawBlockCoordinate
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawBlockCoordinate_cell
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawBlockCoordinate_val
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawBlockBasis
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawBlockRaw
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawBlockDual
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawBlockRaw_single
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawBlockDual_apply
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_block
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawBlockDual_fiber
AAT.AG.FaceRelationSubdivision.blockFiber_d0
AAT.AG.FaceRelationSubdivision.blockFiber_d1
AAT.AG.FaceRelationSubdivision.lawBlockHom
AAT.AG.FaceRelationSubdivision.lawBlockHom_f0
AAT.AG.FaceRelationSubdivision.lawBlockHom_f1
AAT.AG.FaceRelationSubdivision.lawBlockHom_f2
AAT.AG.FaceRelationSubdivision.blockFiniteHom
AAT.AG.FaceRelationSubdivision.blockFiniteHom_f0
AAT.AG.FaceRelationSubdivision.blockFiniteHom_f1
AAT.AG.FaceRelationSubdivision.blockFiniteHom_f2
AAT.AG.FaceRelationSubdivision.blockFiniteFiber_square
AAT.AG.FaceRelationSubdivision.blockFiniteFiber_h1_square
AAT.AG.FaceRelationSubdivision.lawFiniteBlock_square
AAT.AG.FaceRelationSubdivision.lawFiniteBlock_h1_square
AAT.AG.FaceRelationSubdivision.coordinate_eq_of_cell_label
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.basisLaw0_eq_generated
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.basisLaw1_eq_generated
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.basisLaw2_eq_generated
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.basisLawHom_eq_generated
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawR
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawS
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawH0
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawH1
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawR_eq_generated
AAT.AG.FaceRelationSubdivision.TriangleAddition.rSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.sSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawR_fiber
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawS_fiber
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawR_h1_fiber
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawS_h1_fiber
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawR_f0
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawR_f1
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawR_f2
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawS_f0
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawS_f1
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawS_f2
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawH0_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawH1_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawR_h1_standard
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawS_h1_standard
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawR
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawS
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawH0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawH1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawR_eq_generated
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.sSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawR_fiber
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawS_fiber
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawR_h1_fiber
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawS_h1_fiber
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawR_f0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawR_f1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawR_f2
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawS_f0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawS_f1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawS_f2
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawH0_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawH1_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawR_h1_standard
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawS_h1_standard
AAT.AG.FaceRelationSubdivision.dualCellMap_neg
AAT.AG.FaceRelationSubdivision.dualCellMap_zero
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartCoordinateMap_cell
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeCoordinateMap_cell
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceCoordinateMap_cell
AAT.AG.ResolutionInvariance.TargetSupportedNerve.edgeLeftBlockCoordinate_val
AAT.AG.ResolutionInvariance.TargetSupportedNerve.edgeRightBlockCoordinate_val
AAT.AG.ResolutionInvariance.TargetSupportedNerve.faceEdge0BlockCoordinate_val
AAT.AG.ResolutionInvariance.TargetSupportedNerve.faceEdge1BlockCoordinate_val
AAT.AG.ResolutionInvariance.TargetSupportedNerve.faceEdge2BlockCoordinate_val
AAT.AG.ResolutionInvariance.TargetSupportedNerve.targetSubsetComplex_d1
```

現在の対象source SHA-256:

- `FaceRelationSubdivision/LawFiniteCoordinates.lean`: `54ad7db4f1774625b3d981083aea9ff337dd4d1d20fa8e4293d9a57944a658b9`（今回の明示spine 12）
- `FaceRelationSubdivision/LawFiniteFiber.lean`: `45661567bf172b93214b980358fba86f1c18ceeb8f8093b48d0653d40d671111`（今回の明示spine 6）
- `FaceRelationSubdivision/LawFiniteFunctor.lean`: `0ace72e4544b22b87191a7920cafbf6215c7c010cd884357f6dc0d39efb80759`（今回の明示spine 6）
- `FaceRelationSubdivision/LawFiniteDifferential.lean`: `ef782ee77a08d7387ba264aef53a3709d166a63be7f64e0750df09c08a499bb5`（今回の明示spine 4）
- `FaceRelationSubdivision/LawFiniteHom.lean`: `ed90ab35e9bcd733dfdb263ade9b20bd525a5fd3bf79e449b8d099df7acb76eb`（今回の明示spine 14）
- `FaceRelationSubdivision/LawFiniteBlock.lean`: `bf393a0e7c89b97f664f564db36ac57ac072138c5a2b26f30918c514e475c6d3`（今回の明示spine 15）
- `FaceRelationSubdivision/LawFiniteBlockHom.lean`: `a5bddffaf54d2edcd523b40f3bbb7e23223b71ceb403c514e20f140192f2b9d8`（今回の明示spine 14）
- `FaceRelationSubdivision/LawFiniteOption.lean`: `0a7e66486eb86d1e374bf803fce3370a5f974d36c8bcbe81a06488a73afaf769`（今回の明示spine 5）
- `FaceRelationSubdivision/ElementaryLawMaps.lean`: `640d675209f88d2985c5f6d0979fd923513beddf0aa8a4a7e7554c817b4e5991`（今回の明示spine 42）
- `FaceRelationSubdivision/ChainDualMap.lean`: `2b42720356c01f706273f4eb16fc47610df2c344b441b38e6d9a49d1010424bb`（今回の明示spine 2）
- `FaceRelationSubdivision/GeneratedComparison.lean`: `cb3eeaf04abe9d79b9f4ea6af2973bec1898058a24efb6826f8b35650bcd93b1`（今回の明示spine 3）
- `ResolutionInvariance/LawValueBlockDecomposition.lean`: `01f3f11eeefdd9cef7c6cd489808955b48c7cfedb568c35095963652fc5c7708`（今回の明示spine 5）
- `UniformInvariance/ASubnerveReduction.lean`: `4c47300a5c2c9979b3615e9c91fa338968c436265112825d2d20b6a48c685c18`（今回の明示spine 1）

### Cycle 6 validation / result proposal

対象単一file checksを各実装段階で実行し、最終ElementaryLawMaps・LawFiniteBlockHom・
LawFiniteOptionを公式focused経路でも確認。全129宣言のsource/spine/query/log集合一致、
重複・欠落・余剰なし、標準propext/Classical.choice/Quot.soundのみ。
axiom log SHA-256 `58ef241598cbd9410260dce7d7613669a4a40a56c3bd0bdf0b7dfda6fa0fddcd`。
placeholder、hidden/BiDi、privacy、manifest TSV/実在/一意性、diff whitespaceを確認。
固定GOAL blobは不変。固定commitのimport方向・public scan、独立PR査読・CIはPR gateで確定する。
Research full build/aggregate/全file loop、Formal full build、Formal移植、ArchSig実装は未実施。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - 同じCellCoordinateの原始有限和をfiber共役から独立生成
    - 同じラベルのselected双対射と原始Law/block射の全成分等号
    - 既存lawGeneratedD0/D1へ原始有限和微分を実射等号で同定
    - 原始chain式から実Law/block Homを構成し同じfiber/H1正方形
    - 両正操作r/s/hのLaw有限和と同じ既存collapse/H1自然性へ接続
  exit_criteria_status:
    - 選定した独立有限和生成・実射同定の数学的条件を達成
    - 固定head独立PR review/acceptance/CIで最終判定
  split_reason: none
  completion_candidate: no
  claim_mapping:
    source_labels: [D原始有限和Law生成, B正操作r/s/hのLaw有限和, D同じ実比較と既存H1]
    undischarged_assumptions: []
    acceptance_point: 選定した同じreading上の独立Law有限和到達点、P3/P4全終了条件は維持
    port_status: unported
  audits:
    structure_field_escape: none-found
    route_integrity: pass
    vacuity: none-found
    one_way_as_equivalence: none-found
    next_obligation: Law収縮全次数/逆縮約輸送/持ち上げ、有限列/制限/分解/cone/defect、E/W1-W3、別の全target完了監査
```


### Cycle 6 非中心API指摘の修正

初回固定headのLean Aは `lawFiniteBlock_square` の三箇所のcochain合成成分直接展開を
非中心findingとして挙げた。既存公開 `cochainComp_f0/f1/f2` の書き換えへ置換し、
statement、def/instance本体・値、import、宣言集合、statusは保持した。
修正scopeは当該proof内部とこの証拠記載/source hashのみ。独立直接対応で資格と解消を判定する。

## Cycle 6 acceptance / Cycle 7 selection

Cycle 6はPR [#5279](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5279)、
固定head `6648ce7dc705d03e02efee16a4a4e77ec31fbb54`、merge
`2150dab039f19f5a3445672aef2966f4eda78351` として受理。
[初回独立4査読・有資格直接対応・root acceptance](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5279#issuecomment-6024904512)、
[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272#issuecomment-6025005089)。
選定resultはproof-obligation-discharged、全固定targetは未完、Research未移植。

以下を実装前selectionとして固定する。

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 7
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: 2150dab039f19f5a3445672aef2966f4eda78351
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: Cycle6受理とIssue6025005089
  proof_dag_predecessors: [Cycle2原始正操作r/s/h, Cycle6独立Law有限和/実射, G133零延長/旧H1/標準錐短完全列]
  milestone: B/Dの両正操作の同じ実Law/block射の標準ホモトピー同値と全次数診断
  proof_obligations:
    - 原始rs/sr恒等式を独立Law有限和の同じ射へ移す
    - 同じ実Law r/sと原始hの標準HomotopyEquivを構成
    - 各labelの同じ実block有限和射も既存fiber収縮と接続して標準同値
    - 全整数次数homology同型、同じ旧H1比較の同型と零blockDefect
    - 同じ比較の標準錐をG133短完全列へ渡し全整数次数のhomology零性
  exit_criteria:
    - 任意T0入力と任意adequate Lawの両正操作について全上記結論
    - 原始r/s/hの構成と同じ独立Law/block射の等号を放電
    - 空台/空Law/loop/重複出現の追加除外なし、Value有限性追加なし
    - 対象focused/全spineaxiom/共通scanと固定head独立PR査読
  selection_reason: Dの独立射生成から保存結論までの未接続を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [LawFiniteIdentities, ElementaryLawHomotopy, ElementaryBlockHomotopy, HomotopyDiagnostics, ElementaryDiagnostics]
  risks: [方向仮定の具体放電, 原始hの符号, 同じ射へのhomology/錐接続, no-unfold API]
  unchecked: [上記新規構成と接続の実装/検証/独立査読]
```

元P3/P4全終了条件は維持。逆縮約のLaw最終輸送・持ち上げ選択、任意有限操作列、
支持制限、全Law分解の新比較API、E/W1–W3、別の全target4本完了監査は後続義務。
このselectionを全B/C/Dの完了へ読み替えない。completion candidateではない。


### Cycle 7 claim mapping / premise discharge

| 固定条項・選定結論 | 入力からの構成・同じ実射との接続 |
| --- | --- |
| B/Dの原始rs/sr式から実Law恒等式 | `SupportedBasisMap.lawDual_comp_eq_identity`、`lawDual_add_eq_identity`、`lawDual_add_add_eq_identity` が独立生成Law有限和へ移す。両操作の `law_cochain_rs`、`law_correction0/1/2` は受理済み原始基底計算を具体適用 |
| B/Dの同じLaw二射と標準ホモトピー | 両 `lawHomotopyEquiv` のhom/invは同じ `lawR/lawS`、補正は同じ原始 `lawH0/lawH1`。三項補正式→`threeHomotopy`→mathlib `HomotopyEquiv`。合成から恒等へのfieldは補正の向きを反転 |
| 各labelの同じ独立block二射 | 両 `blockR/blockS` は原始r/s有限和の独立座標化。`blockR_fiber/blockS_fiber` は全三成分正方形を原始subset収縮の同じrHom/sHomへ同定 |
| 標準block同値の実射接続 | `transportHomotopyEquiv` は一般対象同型による移送。両 `blockHomotopyEquiv_hom/inv` が正方形から独立生成block射へ等号を証明し、対象同型存在だけで保存を推論しない |
| 全整数次数のLaw/block同型と同じ逆射 | 両 `lawHomologyIso/blockHomologyIso` とhom/inv API。同じ実r/sの標準homology mapそのもの。次数0/1/2を含む |
| 同じ既存H1比較と零欠損 | `homotopyOldH1Iso_hom/inv` に同じr/sを渡す。両 `lawOldH1Iso/blockOldH1Iso`、`lawH1/blockH1_bijective`、`lawH1/blockH1_blockDefect_zero`。旧商と実 `blockDefect` を変更しない |
| 同じ実比較の全次数標準錐零性 | `cone_homology_isZero_of_bijective` はG133の実余核/錐/次核の短完全列を使用。両 `lawCone_isZero/blockCone_isZero/subsetCone_isZero` は構成した同じ射を渡す |
| 全Aの実subset零欠損 | 両 `subsetH1_blockDefect_zero`。任意Aの原始収縮の同じrHomを渡し、空Aも含む |

material premiseを独立に検査できるよう、一般bridgeと具体適用を区別する。

| material premise | role | 放電・使用 |
| --- | --- | --- |
| T0のSource/Reading/N/ℚ、任意指定辺e、Law有限族とadequacy | ambient-boundary / GOAL入力 | 既存型・原始操作constructor・Law有限和座標生成。空Law、空辺/面台、loop、出現重複を除外しない。Value全体のFintypeを追加しない |
| raw往復/補正式 | direction-hypothesis（汎用）/ discharge-required（両正操作） | `TriangleAddition` と `EdgeSubdivision` の受理済み `rs0/1/2`・`sr_h0/1/2` から具体放電。原始r/s/hの支持包含はCycle2 constructorから生成 |
| 標準HomotopyEquiv Eと同じhom/invの等号 | direction-hypothesis（diagnostics/transport）/ discharge-required（具体操作） | 両 `lawHomotopyEquiv` はraw式から全fieldを生成。両block同値は原始fiber収縮と既存対象同型から生成し、独立射の三成分正方形でhom/invを同定 |
| 既存block/fiber対象同型 | discharge-required / 受理predecessorで放電 | G107の同じ支持セル座標同値、G133 `lawBlockFiberZeroExtensionIso` の現在型・公開hom式を使用。今回の射自然性は別に放電 |
| 全次数の実homology全単射 | direction-hypothesis（cone一般補題）/ discharge-required（具体操作） | 原始操作から構成したmathlib HomotopyEquivの `toHomologyIso` で全整数次数に放電。期待次元を入力しない |
| H1のFiniteDimensional | discharge-required / 既存有限複体instanceで放電 | T0有限Source/有限セル→実cochain有限次元→既存H1商。零欠損のみに使用し、錐零性には不要 |
| 結論相当fieldを入力へ移すrisk | conclusion-equivalent-risk | 操作入力はN/e/Law/adequacyだけ。r/s/h・往復・homotopy・同型・零性は出力constructor/定理。新規Prop/certificate/structure/instanceなし |

新規定義は標準 `HomotopyEquiv`、`toHomologyIso`、既存H1商、実 `blockDefect`、
G133標準mappingCone/実短完全列へ接続する。一般transportの方向仮定を、
具体操作でも受け取るだけの形にはしていない。

### Cycle 7 provenance / proof-use

Cycle2の原始正操作r/s/h、全raw恒等式と全A収縮を現在sourceで照合。
Cycle6 PR #5279の独立Law/block有限和、全三成分正方形、実微分等号を同じ引数で使用。
G107のblock/fiber同値とG133の旧H1自然性、標準錐短完全列は前記受理ref・使用版を保持し、
現在statementと適用条件を確認。mathlib版は前記固定版で、標準HomotopyEquivの
trans/ofIso/toHomologyIso、標準mappingConeの型・符号を使用する。

既存 `ComparisonLaws` にcochain恒等の次数別評価3件、`LawFiberDecomposition` に
block/fiber標準同型のhom評価1件を追加。既存signature/proof/def-instance本体値/importは不変。
Law有限和恒等式は既存公開comp/add/raw/微分APIを使い、標準block移送は公開hom式と
三成分正方形を使う。diagnosticsの旧H1同型は自然性によって同じ実射へ着地する。
錐の余核は全射性から零、次核は単射性から零、その実短完全列から錐homology零性を得る。

### Cycle 7 accepted-spine proposal

5新moduleの83明示宣言と既存API追加4件、全87件を今回のspineとする。
compiler生成の補助宣言は明示spine件数から分ける。

```text
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_comp_eq_identity
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_add_eq_identity
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.lawDual_add_add_eq_identity
AAT.AG.FaceRelationSubdivision.TriangleAddition.law_cochain_rs
AAT.AG.FaceRelationSubdivision.TriangleAddition.law_correction0
AAT.AG.FaceRelationSubdivision.TriangleAddition.law_correction1
AAT.AG.FaceRelationSubdivision.TriangleAddition.law_correction2
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawHomotopyEquiv
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.law_cochain_rs
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.law_correction0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.law_correction1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.law_correction2
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawHomotopyEquiv
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.transportHomotopyEquiv
AAT.AG.FaceRelationSubdivision.transportHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.transportHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.transportHomotopyEquiv_hom_eq
AAT.AG.FaceRelationSubdivision.transportHomotopyEquiv_inv_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockR
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockS
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockR_fiber
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockS_fiber
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockHomotopyEquiv
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockR
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockS
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockR_fiber
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockS_fiber
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockHomotopyEquiv
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.homotopyOldH1Iso
AAT.AG.FaceRelationSubdivision.homotopyOldH1Iso_hom
AAT.AG.FaceRelationSubdivision.homotopyOldH1Iso_inv
AAT.AG.FaceRelationSubdivision.homotopyH1_bijective
AAT.AG.FaceRelationSubdivision.homotopyH1_blockDefect_zero
AAT.AG.FaceRelationSubdivision.cone_homology_isZero_of_bijective
AAT.AG.FaceRelationSubdivision.homotopyCone_isZero
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawHomologyIso
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawHomologyIso_hom
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawHomologyIso_inv
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawOldH1Iso
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawOldH1Iso_hom
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawOldH1Iso_inv
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawH1_bijective
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawH1_blockDefect_zero
AAT.AG.FaceRelationSubdivision.TriangleAddition.lawCone_isZero
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockHomologyIso
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockHomologyIso_hom
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockHomologyIso_inv
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockOldH1Iso
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockOldH1Iso_hom
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockOldH1Iso_inv
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockH1_bijective
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockH1_blockDefect_zero
AAT.AG.FaceRelationSubdivision.TriangleAddition.blockCone_isZero
AAT.AG.FaceRelationSubdivision.TriangleAddition.subsetCone_isZero
AAT.AG.FaceRelationSubdivision.TriangleAddition.subsetH1_blockDefect_zero
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawHomologyIso
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawHomologyIso_hom
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawHomologyIso_inv
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawOldH1Iso
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawOldH1Iso_hom
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawOldH1Iso_inv
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawH1_bijective
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawH1_blockDefect_zero
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.lawCone_isZero
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockHomologyIso
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockHomologyIso_hom
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockHomologyIso_inv
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockOldH1Iso
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockOldH1Iso_hom
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockOldH1Iso_inv
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockH1_bijective
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockH1_blockDefect_zero
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.blockCone_isZero
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.subsetCone_isZero
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.subsetH1_blockDefect_zero
AAT.AG.AtlasDefectComposition.cochainId_f0
AAT.AG.AtlasDefectComposition.cochainId_f1
AAT.AG.AtlasDefectComposition.cochainId_f2
AAT.AG.AtlasDefectComposition.lawBlockFiberZeroExtensionIso_hom
```

現在の対象source SHA-256:

- `FaceRelationSubdivision/LawFiniteIdentities.lean`: `63cf78711ef720f4953330fda6b5eabc29ebeb9c2be10b1a29c184f5c38cd766`（今回の明示spine 3）
- `FaceRelationSubdivision/ElementaryLawHomotopy.lean`: `751a7d625e1363a237e924cf46ee85a145b4b897a99ef53cc1d3ac4141497336`（今回の明示spine 14）
- `FaceRelationSubdivision/ElementaryBlockHomotopy.lean`: `3aab89e26b0cbcc52ed18d018e00e63b644486ee4987338e0279ed501dfde249`（今回の明示spine 19）
- `FaceRelationSubdivision/HomotopyDiagnostics.lean`: `0b9d65b5cfe76b2d6fd788c8e61bf749fa8d5cf56088c5b2f2d7a6f8f9bd017b`（今回の明示spine 7）
- `FaceRelationSubdivision/ElementaryDiagnostics.lean`: `80f90e4ce6199d113448e4cc526447ba3c7f3f9ee3f19cd52f764416da41bb9e`（今回の明示spine 40）
- `AtlasDefectComposition/ComparisonLaws.lean`: `45ffd13d6aaf63271211ac6274e50153150a118e1616ac3178cc9e6f14c55382`（今回の明示spine 3）
- `AtlasDefectComposition/LawFiberDecomposition.lean`: `392dcb8479f19baa64b7be39e5d93418f0149ccf06985c86ed860e2ce1187622`（今回の明示spine 1）

### Cycle 7 focused validation / result

root の対象別検証は、新規5 module と2 owner API、および official focused selector `--focused ResearchLean/AG/FaceRelationSubdivision/ElementaryDiagnostics.lean` を通過した。Research full build / aggregate elaboration は実行していない。87 個の明示 spine と axiom query / output の集合は一致し、全て `propext`、`Classical.choice`、`Quot.sound` のみである。ログ SHA-256 は `f1421618f1405121fc02e68f9c23d3d6be9226916c1aa1a8dd74f93100223af1`。manifest の TSV・module/source 一意性・source 存在、import/package 方向、placeholder、hidden/BiDi Unicode、privacy、`git diff --check` を確認した。CI と独立査読は固定 PR head に対して別途実施する。

- proposed cycle result: `proof-obligation-discharged`
- selection exit: discharge済み。同じ原始 r/s/h から生成した Law 比較と独立 block 比較を、全整数次数の実 homology map / inverse、既存 H¹ map、零 defect、標準 mapping cone の全次数零性へ接続した。
- split: none
- completion_candidate: no
- next obligations: 逆操作の実 Law transport、Law lift choices、任意有限列と台 restriction の自然性、新比較に対する Law decomposition / diagnostic API、E および W1–W3、全固定目標の別4本完了監査。
- fixed target 全体: 未完。Research 証明であり、Formal 移植と ArchSig 実装は本 cycle の判定外。GOAL と設計文書の固定 target は変更していない。

## Cycle 7 accepted / Cycle 8 selection

Cycle7 は PR #5280、head `2694cc2849ff5858bab40442c46840e30b3e67f8`、merge `4ee97f87e880c3726e91b1523f8691f2b61e0db6` で受理した。[独立4本・root受入れ・実CI範囲](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5280#issuecomment-6025499850)、[全87公理の再現可能証拠](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5280#issuecomment-6025424336)、[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272#issuecomment-6025523858)。4本すべてNo major findings。全8 CI成功、Formal実build/kernel/premiseはSKIPPED。全目標は未完。

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 8
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: 4ee97f87e880c3726e91b1523f8691f2b61e0db6
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: Cycle7受理とIssue6025523858
  proof_dag_predecessors: [Cycle4原始逆patternと復元表示, Cycle5指定原始lift, Cycle6独立Law有限和, Cycle7実Law同値と診断]
  milestone: B/Dの原始逆縮約と指定lift選択を同じ独立実Law比較へ接続
  proof_obligations:
    - 全原始逆patternから復元した正操作と表示により同じ実Law r/sを生成し独立有限和との等号を放電
    - 同じ逆Law比較の標準同値と全整数次数・旧H1・零欠損・標準錐へ接続
    - 両指定liftの独立原始有限和からLaw射と補正を生成し全次数・旧H1読み戻し一致を証明
    - 同じLaw cocycle代表のh0補正・同じH1類を原始式へ接続
  exit_criteria:
    - 任意T0入力/任意原始逆pattern/adequate Lawについてr/s生成・同定と診断接続
    - 両正操作の指定lift式を同じLaw座標・実微分・実H1へ接続
    - 全Aの受理済み原始逆収縮/liftの支持式を維持しValue有限性/非空台等の追加条件なし
    - 全spine focused/axiom/scanと固定headの独立PR査読
  selection_reason: 正操作の独立Law収縮を逆・liftへ拡張しB/Dの未接続を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [FiniteHomComposition, PresentationLawInverse, InverseLawContraction, LawLiftVariation, ElementaryLawLift, LawCocycleNormalization]
  risks: [表示逆射の同定, 独立Law有限和の合成, raw chain式, homotopyの符号, 旧H1自然性]
  unchecked: [選定した新規構成/接続/検証/独立査読]
```

元P3/P4の全終了条件は保持。任意有限操作列、支持制限の自然性、一般Law/錐/欠損分解、E/W1–W3と別4本の全固定target完了監査は後続義務。このselectionは全目標完了候補ではない。

### Cycle 8 claim mapping / material premise / proof-use

| 選定義務 | 入力からの構成と同じ実射への接続 |
| --- | --- |
| 原始Option表の全セルchain式 | `IncidenceSupportedComparison.basis_comm01/12`。端点・三辺番号・混在退化の原始零和を全セル基底で評価し、空台セルも含める。`basisSubsetFiniteHom_eq` は同じ実subset生成射へ接続 |
| 原始有限和のLaw合成 | `finiteComp_comm01/12` と `lawFiniteHom_comp`。台を保つ原始有限和の直接合成を作り、同じ独立Law射の全三成分合成と同定 |
| 原始表示の両逆 | `comparison_comp_symmSelf/symmSelf_comparison_comp` の全三成分恒等から `lawZeroExtensionIso_inv`。順表示・逆表示を同じ生成射に同定 |
| 逆patternの独立実Law二射 | 両 `lawR` は原始collapse Option表、`lawS` は復元正section有限和と原始表示の直接合成。`presentationLawSection_f0/1/2` が各有限和を公開し、両 `lawR_comp/lawS_comp` が生成合成との等号を証明 |
| 逆patternの同じ実fiber二射 | 両 `rSubsetFiniteHom_eq/sSubsetFiniteHom_eq` と `lawR_fiber/lawS_fiber`。任意Aの原始有限和双対が受理済みC4の実rHom/sHomであり、Lawは同じlabel fiberへ全三成分着地 |
| 逆patternの標準同値と逆向き操作 | 両 `lawHomotopyEquiv` は復元正操作の原始同値と原始表示の逆を合成。hom/invが同じ独立実Law二射に等しいことを別途証明。`inverseLawHomotopyEquiv` は同じ二射を逆向きに使う |
| 全次数・旧H1・零欠損・錐 | 両 `lawHomologyIso_hom/inv`、`lawOldH1Iso_hom/inv`、`lawR/lawS_blockDefect_zero`、`lawR/lawS_cone_isZero`。同じr/sの全整数次数mapをG133旧H1自然性・実標準錐へ接続 |
| 指定持ち上げの同じ原始有限和 | `lawLift_raw_comm01/12` から `lawLiftHom`。両 `liftedLawS` はC5の原始 `liftedS1/2` を独立Law座標化。辺分割は任意 `Occurrence` を量化し、負のtと各出現の別名を保持 |
| 指定持ち上げの実Law/fiber/旧H1 | 両 `liftedLawS_eq_variation`、`liftedSubsetFiniteHom_eq`、`liftedLawS_fiber/h1_fiber`、`liftedLawHomotopy`、`liftedLawS_homologyMap/h1Map`。原始有限和の等号から同じ全A収縮・全整数次数・旧商の読み戻し一致へ接続 |
| cocycleの実代表と同じ類 | 両 `law_cocycle_normalize` は同じ原始lawH0と実d0の補正。`law_cocycle_readback_class` は既存boundaryToCyclesの商で具体境界 `-lawH0(z)` を示す。別の指定道も `liftedLawS_readback_class` で同じ旧H1類 |

T0の有限Source・全射Reading・有限supported nerve・K1・ℚ、任意Law/adequacyは入力として保持する。逆patternのfreshness/全接続/台等号は固定Bの原始許容条件であり、C4が復元旧入力と正操作の表示を全field生成する。標準同値・実射等号・zero defect・cone zero・期待rankはpattern入力にない。

raw chain式は一般bridgeでdirection-hypothesis、具体正section・表示・collapse・liftでdischarge-requiredとして基底表/原始incidenceから放電。表示の両逆は名前の全単射から生成する。tはC5の指定旧辺/指定面内出現から生成し、一般variationのt条件を具体操作に供給済み結論として残さない。全整数次数の同型・旧H1商の同じ射・実欠損・錐はC7の受理済み現在statementに同じ引数を渡す。

Law座標有限和はC6の `CellCoordinate` を用い、各非零項の支持包含から同じcell/law/value座標を生成する。対象fiber同型からLaw二射を定義しない。C4の原始hは正操作のhの表示共役であり、Law標準同値は同じ正操作ホモトピーと原始表示を使用する。支持選択の具体二射は別に同定する。

H1有限次元性は既存有限セル/発生座標/商instanceから導出し零欠損で使用する。錐零性はC7の同じ実短完全列による全n判定を使用。空A/空辺・面台/空Lawを除外せず、Value全体の有限性、非loop、面内出現の一意性を追加しない。辺分割のliftは指定Occurrenceが存在する場合の選択であり、元操作自体の入力を面に接する辺へ限定しない。

新規generic map/homotopyのcertificate fieldは出力で、具体constructorが全条件を生成する。新規Prop/structure/instanceはない。既存ownerの追加は恒等Option表の3評価、基底Homの3評価、両逆patternのcollapse式/section次数別評価の各4件、計14 public APIのみ。既存signature/proof/def-instance本体/importは不変。

依存はC1 #5274の同じ新比較と生成合成、C2 #5275、C3 #5276、C4 #5277、C5 #5278、C6 #5279、C7 #5280の前記受理版・hash・review refと現在statement/今回適用を保持。標準mathlibのHomotopyEquiv.trans/ofIso/symm、Homotopy.homologyMap_eq、ModuleCatと旧商のAPIは固定版を使用。

### Cycle 8 accepted-spine proposal

新規6 moduleの119明示宣言、既存owner API追加14件、計133件。

```text
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.basis_comm01
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.basis_comm12
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.basisSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.raw_square_comp
AAT.AG.FaceRelationSubdivision.finiteComp_comm01
AAT.AG.FaceRelationSubdivision.finiteComp_comm12
AAT.AG.FaceRelationSubdivision.lawFiniteHom_comp
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.comparison_comp_symmSelf
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.symmSelf_comparison_comp
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.lawZeroExtensionIso_inv
AAT.AG.FaceRelationSubdivision.presentationLawSection
AAT.AG.FaceRelationSubdivision.presentationLawSection_eq_finite
AAT.AG.FaceRelationSubdivision.presentationLawSection_f0
AAT.AG.FaceRelationSubdivision.presentationLawSection_f1
AAT.AG.FaceRelationSubdivision.presentationLawSection_f2
AAT.AG.FaceRelationSubdivision.presentationLawSection_eq
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawR
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawS
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawR_eq_generated
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawS_eq_finite
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawR_comp
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawS_comp
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.rSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.sSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawR_fiber
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawS_fiber
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawHomotopyEquiv
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawHomotopyEquiv_hom_formula
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawHomotopyEquiv_inv_formula
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.inverseLawHomotopyEquiv
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.inverseLawHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.inverseLawHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawHomologyIso
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawHomologyIso_hom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawHomologyIso_inv
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawOldH1Iso
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawOldH1Iso_hom
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawOldH1Iso_inv
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawR_blockDefect_zero
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawS_blockDefect_zero
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawR_cone_isZero
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.lawS_cone_isZero
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawR
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawS
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawR_eq_generated
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawS_eq_finite
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawR_comp
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawS_comp
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.rSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.sSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawR_fiber
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawS_fiber
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawHomotopyEquiv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawHomotopyEquiv_hom_formula
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawHomotopyEquiv_inv_formula
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.inverseLawHomotopyEquiv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.inverseLawHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.inverseLawHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawHomologyIso
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawHomologyIso_hom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawHomologyIso_inv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawOldH1Iso
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawOldH1Iso_hom
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawOldH1Iso_inv
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawR_blockDefect_zero
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawS_blockDefect_zero
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawR_cone_isZero
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.lawS_cone_isZero
AAT.AG.FaceRelationSubdivision.lawLift_raw_comm01
AAT.AG.FaceRelationSubdivision.lawLift_raw_comm12
AAT.AG.FaceRelationSubdivision.lawLiftHom
AAT.AG.FaceRelationSubdivision.lawLiftHom_f0
AAT.AG.FaceRelationSubdivision.lawLiftHom_f1
AAT.AG.FaceRelationSubdivision.lawLiftHom_f2
AAT.AG.FaceRelationSubdivision.lawLiftHom_correction1
AAT.AG.FaceRelationSubdivision.lawLiftHom_correction2
AAT.AG.FaceRelationSubdivision.lawLiftHomotopy
AAT.AG.FaceRelationSubdivision.lawLiftHom_homologyMap
AAT.AG.FaceRelationSubdivision.lawLiftHom_h1Map
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS_comm01
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedS_comm12
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS_f0
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS_f1
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS_f2
AAT.AG.FaceRelationSubdivision.TriangleAddition.sLawFiniteHom_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS_eq_variation
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS_eq_finite
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS_fiber
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS_h1_fiber
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawHomotopy
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS_homologyMap
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS_h1Map
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS_comm01
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedS_comm12
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS_f0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS_f1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS_f2
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.sLawFiniteHom_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS_eq_variation
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedSubsetFiniteHom_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS_eq_finite
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS_fiber
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS_h1_fiber
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawHomotopy
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS_homologyMap
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS_h1Map
AAT.AG.FaceRelationSubdivision.TriangleAddition.law_cocycle_normalize
AAT.AG.FaceRelationSubdivision.TriangleAddition.law_cocycle_readback_class
AAT.AG.FaceRelationSubdivision.TriangleAddition.liftedLawS_readback_class
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.law_cocycle_normalize
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.law_cocycle_readback_class
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.liftedLawS_readback_class
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.identity_chartMap
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.identity_edgeMap
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.identity_faceMap
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.basisHom_f0
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.basisHom_f1
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.basisHom_f2
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.sHom_f0
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.sHom_f1
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.sHom_f2
AAT.AG.FaceRelationSubdivision.TriangleInversePattern.collapse_eq
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.sHom_f0
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.sHom_f1
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.sHom_f2
AAT.AG.FaceRelationSubdivision.SubdivisionInversePattern.collapse_eq
```

今回の対象source SHA-256（path / 明示spine数 / hash）:

```tsv
research/lean/ResearchLean/AG/FaceRelationSubdivision/FiniteHomComposition.lean	7	e7a7abe24cb7bd5195ed5f5f93b79fee38bed6b1c5280d197af9b4a59ab352fa
research/lean/ResearchLean/AG/FaceRelationSubdivision/PresentationLawInverse.lean	9	27376f5a0fda646c2a20be27e3df9806eb8c35639bf3664078cb97b517760bb8
research/lean/ResearchLean/AG/FaceRelationSubdivision/InverseLawContraction.lean	56	449ff757503ce90e53fb48db24efeebda4b87a4a08fdd8b0576d253074212fdc
research/lean/ResearchLean/AG/FaceRelationSubdivision/LawLiftVariation.lean	11	0e97cf067fb14c95d21a28c79f4c316a05d8ff44d5dede0e34dfc3c29ae8b9ec
research/lean/ResearchLean/AG/FaceRelationSubdivision/ElementaryLawLift.lean	30	a5e3cadef3c0023e87fb3fb39db18d89ed0c3aef385b0c6663c5dcb6c083ab86
research/lean/ResearchLean/AG/FaceRelationSubdivision/LawCocycleNormalization.lean	6	ffe6ac6a941f62b8f0879cc3ef272af267675bfa53e3f0780d3593174f81224a
research/lean/ResearchLean/AG/FaceRelationSubdivision/IncidenceComparison.lean	3	e3ef579ea59b2202a5a7b840ff5f81565ed65548835671ec71b57081e74bd545
research/lean/ResearchLean/AG/FaceRelationSubdivision/IncidenceBasis.lean	3	5cbf03334bfa2026c428cf024724c0b8e56796e67a2ea4d6450def32f7272f9f
research/lean/ResearchLean/AG/FaceRelationSubdivision/TriangleInverseContraction.lean	4	8f1a6dbc99fdf110686d7504e1b91066f8aac850528444b48455800cdcd8790d
research/lean/ResearchLean/AG/FaceRelationSubdivision/SubdivisionInverseContraction.lean	4	b85754735ec912d50de5ab8d81668c72007550d40b6303f7b4af7755bffd72bf
```

### Cycle 8 focused validation / proposed result

root の新規6 module と4 owner API変更を対象別 `lake env lean` で確認。official focused selectors は `InverseLawContraction.lean` と `LawCocycleNormalization.lean` を別々に実行し成功。Research full build、aggregate、全file elaborationは未実施。

133 個の明示 source/spine/query/output 集合が一致し、依存は標準 `propext`、`Classical.choice`、`Quot.sound` のみ。各module末尾の標準公理macroもcompiler生成補助宣言を含めて成功。公理log SHA-256は `f50abb29c75310771969583944903dd11103491ee85fc9b6e4f2f99ee67f8eae`。manifestのTSV/一意性/source存在、import/package静的方向、placeholder/Unicode/privacy/語彙/diff scanを確認。固定commit公開面scan、CIと独立査読はPR固定headで実施する。

- proposed_result_type: `proof-obligation-discharged`
- exit_criteria_status: 原始両逆patternの独立Law二射/全三成分実fiber接続/標準正逆同値/全整数次数と旧H1/零欠損/実錐接続、両指定liftの独立実Law二射/同じ任意Aの実fiber/全整数次数と旧H1/具体cocycle境界を放電。
- split_reason: none
- completion_candidate: no
- selected obligation の undischarged material premise: なし。独立PR査読で検算する。
- next_obligation: 任意有限操作列の原始直接有限和・正逆二homotopy、支持制限の自然性、新比較の一般Law/錐/欠損分解、E/W1–W3、別4本の全固定target監査。
- 全固定target: 未完。Research証明はFormal未移植。固定GOAL/恒久設計/仮定/量化/指定例は不変。

## Cycle 8 accepted / Cycle 9 selection

Cycle8 は PR #5281、head `ad0f7e3f77acf22ecf9634f3fa43aa64abeba1d6`、merge `943fcc5db711f4fcdfcd35f722137331f2b6b209` で受理した。[新規独立4本・root受入れ・実CI範囲](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5281#issuecomment-6025963377)、[全133公理の再現可能証拠](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5281#issuecomment-6025864333)、[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272#issuecomment-6025981414)。全4本No major findings、findingなし。全8CI成功、Formal実build/kernel/premiseはSKIPPED。全目標未完。

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 9
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: 943fcc5db711f4fcdfcd35f722137331f2b6b209
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: Cycle8受理と上記Issue同期
  proof_dag_predecessors: [Cycle1新比較/独立Law/block/subset生成, Cycle2支持有限和/双対, Cycle6独立有限和Law/block/fiber, Cycle7実錐, Cycle8原始有限和合成]
  milestone: C/Dの同じ支持有限和射を支持制限および全Law実分解の射へ接続
  proof_obligations:
    - 任意A包含Bの同じ選択セル包含と双対制限を生成し全SupportedBasisMapのr/s/hと可換
    - 原始微分と同じ支持包含から既存subset制限Homを生成し全三成分の自然性を証明
    - 新混在比較の全Law/全ラベル自然性を全三次数と既存H1/標準全次数で構成
    - 新混在比較の同じLaw射の核/余核/実欠損と標準錐を全ラベル/原始fiberへ分解
    - 独立有限和Law射とblock射にも同じ全ラベル接続を構成しsection/h/後続有限列で再利用可能にする
    - 旧hereditary比較の同じ実生成射への受理済み特殊化を新しい接続に適用
  exit_criteria:
    - 全A包含B/全原始支持有限和のchain自然性と実双対制限自然性
    - 任意qc先行qf/任意新比較/任意adequate Lawの全三成分および旧H1/全整数次数可換図式
    - 同じ射の実核/余核同値と錐族/直和同型を構成し同台ラベル重複度を保持
    - 独立原始有限和の具体適用で一般方向仮定を放電し全spine検証と独立PR査読
  selection_reason: P4の未接続な支持制限/全Law分解を閉じ有限操作列と指定余核例へ同じ実射で接続する
  expected_result_type: proof-obligation-discharged
  lean_targets: [SupportRestriction, SubsetRestriction, LawComparisonDecomposition, LawComparisonDefect, LawComparisonCone, LawFiniteDecomposition]
  risks: [双対合成の向き, 有限ラベルprojection一致, 旧H1自然性, 全次数実錐, 相同型の射一致]
  unchecked: [選定した新規構成/接続/検証/独立査読]
```

元P4の全終了条件は保持。任意有限操作列、原始直接有限和と二homotopy、全操作での実診断への一体接続は後続義務。E/W1–W3と別4本の全固定target完了監査も残す。今回は独立再利用できる支持制限と実分解の一般接続を到達点として選定し、全P4や全targetの完了とは扱わない。

### Cycle 9 claim mapping / premise / proof DAG

| 固定条項・選定義務 | 構成・同じ実射の接続 | 出力 |
| --- | --- | --- |
| C: 全A包含B | `selectedInclude` は同じセルの基底包含、`selectedRestrict` はその双対。`selected_include_natural` と `dual_selected_restrict_natural` は任意の原始 `SupportedBasisMap` を量化 | 比較r・逆s・h0/h1にも同じ式を適用。空A、空台、loop、重複出現を除かない |
| C/D: 同じsubset制限 | 原始d1/d2に上記自然性を適用し既存 `targetSubsetComplex` のd0/d1へ同定。`subsetRestrictHom` と `subsetFinite_restrict_square` | 全三成分・既存H1・標準零延長の可換式、恒等・合成 |
| A/D: 異なるreadingの新比較の制限 | `restrict_pullback0/1/2` は両subsetの因子適合と同じ原始セル像から導出 | `subset_restrict_square/h1_square`。Option.noneの零像とOption.someの同じセル名を保持 |
| D: 全Law/全ラベル | `LawMapDecomposition` の一般可換式を、新比較の独立生成Law/block式で放電 | `lawFamily_square`、`lawZeroExtension_square`、全整数次数 `lawStandardHomology_natural`、旧H1 `lawH1Family_natural` |
| D: 同じ新比較の実核・余核 | 上記自然性を `LinearConjugation` と `FiniteLinearFamily` の実線形同値に渡す | H1および標準全次数の核・余核同値、元/商代表の評価、二欠損の和 |
| D: 同じ新比較の標準錐 | 同じ全三成分射の標準正方形を `coneMapIso` に渡し `FiniteConeFamily.iso` へ接続 | `lawConeFamilyIso/DirectSumIso/HomologyEquiv`、全次数の実projection |
| D: 同じ原始fiberの実診断 | 受理済みC1のblock/fiber次数1自然性→既存商、C3のcanonical逆像の全三成分等号→同じ錐 | `lawFiberH1Kernel/CokernelFamilyEquiv`、`lawH1Defect_subset_sum`、`lawSubsetConeFamily/DirectSumIso/HomologyEquiv` |
| C/D: 独立有限和の全Law分解 | C6の原始非零項ごとの同じLaw名・値の生成式を使い `lawDual_block` を既存Law族座標へ同定 | `lawFiniteFamily_natural0/1/2`、全三成分/標準全次数/旧商、実核・余核/欠損、実錐族・直和・全次数 |
| A/D: 旧hereditary APIの特殊化 | C1の埋め込みの全三成分等号を上記新クラスの自然性・欠損・錐へ適用 | `hereditary_lawFamily/ZeroExtension_square`、同じ旧実射の欠損和・原始fiber錐同型と全次数projection |

一般bridgeの方向仮定と、原始比較/有限和への具体適用を分ける。`LawMapDecomposition` の三つの可換式は direction-hypothesis（一般補題の仮定）であり、新混在比較ではC1の独立生成 `generatedPullback*_block_component`、有限和ではC6の `lawDual_block` から放電する。核・余核・錐はその同じ実射を用いて構成する。任意の相同型や期待rankを入力にしていない。

T0のSource/Reading/有限supported nerve/K1/ℚと任意Law/adequacy、新比較Aの原始incidence・支持適合、CのA包含Bは ambient-boundary（固定入力）。SupportBasisMapの基底像・非零項の支持包含は原始有限和の入力であり、基本操作への適用はC2/C4/C6/C8の受理済み生成構成から供給される。原始chain正方形は一般有限和bridgeの direction-hypothesis、具体r/sへの適用は受理済み原始端点/三辺符号和/section合成から discharge-required として放電する。細reading adequacyはC1の `adequate_of_coarser` を使用でき、Value全体の有限性を追加しない。

`selectedInclude_embed` で零延長後の原始セル像を一致させ、その単射性で自然性を証明する。Lawの三次数の座標同定と既存商の元評価APIをownerに追加し、下流は公開APIから証明する。標準錐は対象同型だけでなく同じ射の可換式を入力としてG-133へ渡す。全ラベル族の添字は `LawValueLabel laws` のままであり、等しいfiber台によってラベルを同一視しない。空Law族も同じ有限族APIで量化する。

使用する受理済み依存は、C1（原始新比較/独立Law/block/subset/H1、旧比較の全三成分特殊化）、C2（原始支持基底射/選択零延長/双対）、C3（同じblock/fiber/選択subset/錐の接続）、C6（独立Law有限和とblock有限和/実fiber/微分）、C8（同じ有限和Hom）、G-133（Law族/零延長、有限族kernel/cokernel/cone、実Homの標準homology/錐）である。受理commit・source版・review参照は上記各cycleと先行依存表に固定済み。現在の使用statement・必要定義・適用引数を確認し、今回のowner差分は評価/接続APIの追加18件だけで既存定義・statement・importは不変。

新規の述語・certificate structure はない。有限biproductの局所instanceはmathlibの既存有限積から導出する。選択済みhomology同型、欠損零、診断rankをfieldに保持していない。

### Cycle 9 spine / source evidence

9新規moduleの明示宣言98件（局所instanceを含む）、7既存ownerのpublic API追加18件、合計116件をこのcycleのspineとする。compiler生成補助宣言は各module末尾の標準公理macroでも確認する。

```text
AAT.AG.FaceRelationSubdivision.selectedInclude
AAT.AG.FaceRelationSubdivision.selectedInclude_single
AAT.AG.FaceRelationSubdivision.selectedInclude_embed
AAT.AG.FaceRelationSubdivision.selectedInclude_embed_apply
AAT.AG.FaceRelationSubdivision.selectedInclude_refl
AAT.AG.FaceRelationSubdivision.selectedInclude_comp
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.selected_include_natural
AAT.AG.FaceRelationSubdivision.selectedRestrict
AAT.AG.FaceRelationSubdivision.selectedRestrict_eq_dual
AAT.AG.FaceRelationSubdivision.selectedRestrict_apply
AAT.AG.FaceRelationSubdivision.selectedRestrict_refl
AAT.AG.FaceRelationSubdivision.selectedRestrict_comp
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.dual_selected_restrict_natural
AAT.AG.FaceRelationSubdivision.subsetRestrict_comm0
AAT.AG.FaceRelationSubdivision.subsetRestrict_comm1
AAT.AG.FaceRelationSubdivision.subsetRestrictHom
AAT.AG.FaceRelationSubdivision.subsetRestrictHom_f0
AAT.AG.FaceRelationSubdivision.subsetRestrictHom_f1
AAT.AG.FaceRelationSubdivision.subsetRestrictHom_f2
AAT.AG.FaceRelationSubdivision.subsetRestrictHom_refl
AAT.AG.FaceRelationSubdivision.subsetRestrictHom_comp
AAT.AG.FaceRelationSubdivision.subsetFinite_restrict_square
AAT.AG.FaceRelationSubdivision.subsetFinite_restrict_h1_square
AAT.AG.FaceRelationSubdivision.subsetFinite_restrict_zeroExtension_square
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.restrict_pullback0
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.restrict_pullback1
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.restrict_pullback2
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.subset_restrict_square
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.subset_restrict_h1_square
AAT.AG.FaceRelationSubdivision.LawMapDecomposition.family_square
AAT.AG.FaceRelationSubdivision.LawMapDecomposition.zeroExtension_square
AAT.AG.FaceRelationSubdivision.LawMapDecomposition.standard_homology_natural
AAT.AG.FaceRelationSubdivision.LawMapDecomposition.h1_natural
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.lawFamily_natural0
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.lawFamily_natural1
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.lawFamily_natural2
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.lawFamily_square
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.lawZeroExtension_square
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.lawStandardHomology_natural
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.lawH1Family_natural
AAT.AG.FaceRelationSubdivision.lawH1Comparison_square
AAT.AG.FaceRelationSubdivision.lawH1KernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.lawH1CokernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.lawH1KernelFamilyEquiv_val
AAT.AG.FaceRelationSubdivision.lawH1CokernelFamilyEquiv_mk
AAT.AG.FaceRelationSubdivision.lawH1Defect_sum
AAT.AG.FaceRelationSubdivision.lawStandardKernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.lawStandardCokernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.lawStandardKernelFamilyEquiv_val
AAT.AG.FaceRelationSubdivision.lawStandardCokernelFamilyEquiv_mk
AAT.AG.FaceRelationSubdivision.lawComparisonConeFiniteBiproducts
AAT.AG.FaceRelationSubdivision.lawConeFamilyIso
AAT.AG.FaceRelationSubdivision.lawConeDirectSumIso
AAT.AG.FaceRelationSubdivision.lawConeHomologyEquiv
AAT.AG.FaceRelationSubdivision.lawConeFamilyIso_hom
AAT.AG.FaceRelationSubdivision.lawConeHomologyEquiv_component_family
AAT.AG.FaceRelationSubdivision.lawFiniteDecompositionBiproducts
AAT.AG.FaceRelationSubdivision.lawFamily0Equiv_eq_read
AAT.AG.FaceRelationSubdivision.lawFamily1Equiv_eq_read
AAT.AG.FaceRelationSubdivision.lawFamily2Equiv_eq_read
AAT.AG.FaceRelationSubdivision.lawFiniteFamily_natural0
AAT.AG.FaceRelationSubdivision.lawFiniteFamily_natural1
AAT.AG.FaceRelationSubdivision.lawFiniteFamily_natural2
AAT.AG.FaceRelationSubdivision.lawFiniteFamily_square
AAT.AG.FaceRelationSubdivision.lawFiniteZeroExtension_square
AAT.AG.FaceRelationSubdivision.lawFiniteStandardHomology_natural
AAT.AG.FaceRelationSubdivision.lawFiniteH1Family_natural
AAT.AG.FaceRelationSubdivision.lawFiniteH1Family_square
AAT.AG.FaceRelationSubdivision.lawFiniteKernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.lawFiniteCokernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.lawFiniteKernelFamilyEquiv_val
AAT.AG.FaceRelationSubdivision.lawFiniteCokernelFamilyEquiv_mk
AAT.AG.FaceRelationSubdivision.lawFiniteDefect_sum
AAT.AG.FaceRelationSubdivision.lawFiniteConeFamilyIso
AAT.AG.FaceRelationSubdivision.lawFiniteConeDirectSumIso
AAT.AG.FaceRelationSubdivision.lawFiniteConeHomologyEquiv
AAT.AG.FaceRelationSubdivision.lawFiniteConeFamilyIso_hom
AAT.AG.FaceRelationSubdivision.lawFiniteConeHomologyEquiv_component
AAT.AG.FaceRelationSubdivision.lawComparisonFiberFiniteBiproducts
AAT.AG.FaceRelationSubdivision.labelFiberH1_natural
AAT.AG.FaceRelationSubdivision.lawFiberH1Comparison_square
AAT.AG.FaceRelationSubdivision.lawFiberH1KernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.lawFiberH1CokernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.lawFiberH1KernelFamilyEquiv_val
AAT.AG.FaceRelationSubdivision.lawFiberH1CokernelFamilyEquiv_mk
AAT.AG.FaceRelationSubdivision.lawFiberH1Defect_sum
AAT.AG.FaceRelationSubdivision.lawFiberDefect_canonical
AAT.AG.FaceRelationSubdivision.lawH1Defect_subset_sum
AAT.AG.FaceRelationSubdivision.lawSubsetConeFamilyIso
AAT.AG.FaceRelationSubdivision.lawSubsetConeDirectSumIso
AAT.AG.FaceRelationSubdivision.lawSubsetConeHomologyEquiv
AAT.AG.FaceRelationSubdivision.lawSubsetConeHomology_dimension
AAT.AG.FaceRelationSubdivision.hereditary_lawFamily_square
AAT.AG.FaceRelationSubdivision.hereditary_lawZeroExtension_square
AAT.AG.FaceRelationSubdivision.hereditary_lawH1Defect_subset_sum
AAT.AG.FaceRelationSubdivision.hereditary_lawSubsetConeFamilyIso
AAT.AG.FaceRelationSubdivision.hereditary_lawSubsetConeHomologyEquiv
AAT.AG.FaceRelationSubdivision.hereditary_lawSubsetConeHomologyEquiv_component
AAT.AG.AtlasDefectComposition.lawFamily0Equiv_apply
AAT.AG.AtlasDefectComposition.lawFamilyCochainEquiv_f0
AAT.AG.AtlasDefectComposition.lawFamily1Equiv_apply
AAT.AG.AtlasDefectComposition.lawFamilyCochainEquiv_f1
AAT.AG.AtlasDefectComposition.lawFamily2Equiv_apply
AAT.AG.AtlasDefectComposition.lawFamilyCochainEquiv_f2
AAT.AG.AtlasDefectComposition.lawFiberH1FamilyEquiv_apply
AAT.AG.AtlasDefectComposition.lawH1FamilyEquiv_mk_component
AAT.AG.AtlasDefectComposition.lawZeroExtensionIso_hom
AAT.AG.AtlasDefectComposition.lawStandardHomologyEquiv_apply
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetComparisonHom_f0
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetComparisonHom_f1
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetComparisonHom_f2
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetChartMap_val
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetEdgeMap_val
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.targetSubsetFaceMap_val
AAT.AG.FaceRelationSubdivision.subsetTransportHom_eq_transportHom
AAT.AG.ResolutionInvariance.TargetSupportedNerve.lawGeneratedBlockCyclesEquiv_component_val
```

今回の対象source SHA-256（path / 明示spine数 / hash）:

```tsv
research/lean/ResearchLean/AG/FaceRelationSubdivision/SupportRestriction.lean	13	03420a6b2aca2ebe4726022ce3279bd54e3c4de8b011b16d071ec3d2d8b6894b
research/lean/ResearchLean/AG/FaceRelationSubdivision/SubsetRestriction.lean	11	cea0f9be7eecd812242f05fac119dd07cfb894fb3a58844b36a1d9171665e18c
research/lean/ResearchLean/AG/FaceRelationSubdivision/ComparisonRestriction.lean	5	3b3118ca8e37f4f926d750ae4566a65ba04723acb0e32cb2d6f1a1ea281fb3b0
research/lean/ResearchLean/AG/FaceRelationSubdivision/LawComparisonDecomposition.lean	11	496ba43e5989e9bb309860976a432ed31df91e9c6c286237a6b92b6172434f63
research/lean/ResearchLean/AG/FaceRelationSubdivision/LawComparisonDefect.lean	10	ba062facc20c993767ee9ce423fbc0573ece5da57ee5c7c7993abc8e34cb8b72
research/lean/ResearchLean/AG/FaceRelationSubdivision/LawComparisonCone.lean	6	8c4f924d6eaf1f0bd3631bf636d82a54960a111826418b9015b66a4a9a335169
research/lean/ResearchLean/AG/FaceRelationSubdivision/LawFiniteDecomposition.lean	22	3811136165dfd4da77e71c6f8ac815b0f286a04a0686d20e47e04d37fecfc364
research/lean/ResearchLean/AG/FaceRelationSubdivision/LawComparisonFiberDiagnostics.lean	14	99fbd72c77adf71ff6cec151ce0dda3c804f541459039c2280cdf41d86e25206
research/lean/ResearchLean/AG/FaceRelationSubdivision/HereditaryDiagnostics.lean	6	6b7ba65c935ba3d0a40eae00021b41b355cf8b5c5e609001157fc721d05947cf
research/lean/ResearchLean/AG/AtlasDefectComposition/LawCochainDecomposition.lean	6	70c7f50b14cbc8e85048c4fd94505832e2850868599651f9b24620da56901288
research/lean/ResearchLean/AG/AtlasDefectComposition/LawFiberH1Family.lean	1	2b5f35773a0b1abd9cf16e110e8b861cbdf673a959783471b924a23a106b1fbb
research/lean/ResearchLean/AG/AtlasDefectComposition/LawH1Family.lean	1	facb6338c772e54678886d33dbe0cebea9dfa76433a8a82fa2fc3028b5d0c3ff
research/lean/ResearchLean/AG/AtlasDefectComposition/LawStandardDecomposition.lean	2	17c9cdac3acb993d26030d23b70e4e0dae84733ecc500901e111062d492b4869
research/lean/ResearchLean/AG/FaceRelationSubdivision/SubsetComparison.lean	6	de4a474ce4cf0295bd62afe3e8668a07101a50ee6060c9783ea026d949ffd299
research/lean/ResearchLean/AG/FaceRelationSubdivision/SubsetComposition.lean	1	2cfd539bca7c8df7c2f787188e73a977b0f9e80f70b41155ad7dd86b15161844
research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockCohomology.lean	1	7c2b3412e45f58ea66c9fb48ca781cb6b3cd168a51a18ac4b87825622d5d460b
```

### Cycle 9 focused validation / proposed result

rootは新規9moduleと必要7owner APIを対象別 `lake env lean` で検証した。official focused selectorは `HereditaryDiagnostics.lean`、`ComparisonRestriction.lean` をそれぞれ実行し成功。前者はLaw分解・実核/余核・錐・独立有限和分解への接続、後者は支持包含/双対/実subset制限/混在比較を含む。Research full build、aggregate、全file elaborationは未実施。

全116の明示source/spine/query/output集合が一致し、標準 `propext`、`Classical.choice`、`Quot.sound` のみ。公理log SHA-256 `2cc7bf13a18069afefa00043e82d65c7e5675e4df1f6fd0f548f8e5b0f3a2f85`。manifest TSV/一意性/source存在、静的import/package方向、placeholder/hidden/BiDi/privacy/新規文章の語彙、diffを検査して成功。固定commit公開面、CI、独立査読はPR固定headで判定する。

- proposed_result_type: `proof-obligation-discharged`
- exit_criteria_status: 選定した全支持制限・一般新比較の実分解・独立有限和の実分解・同じ旧射への特殊化を放電。
- split_reason: none
- completion_candidate: no
- selected obligation の undischarged material premise: なし。独立PR査読で検算する。
- next_obligation: 任意有限操作列の原始直接有限和、正逆二homotopy、reading変更を含む同じ実射の合成、E/W1–W3、別4本の全固定target完了監査。
- 全固定target: 未完。Research証明はFormal未移植。固定GOAL/恒久設計/仮定/量化/指定例は不変。

## Cycle 9 受理同期

PR [#5282](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5282) final head `062134827d0b41b7bb5a73db97a17bddebbc2ef7`は新規独立4本がすべて `No major findings`、root [統合受入れ](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5282#issuecomment-6026457541). merge `7f169e370dfc0f28229bae2b81b69b7a4ab538ac`、[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272#issuecomment-6026513855). 全8 CI job成功、Research/Toolingの実step成功。Formal Lean setup/cache/build/kernel/premise実stepはSKIPPEDであり、Formal job名をFormal検証証拠に数えない。選定義務を放電し、全targetはactiveのまま未完。

## Cycle 10 selection — 原始有限操作列

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 10
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: 7f169e370dfc0f28229bae2b81b69b7a4ab538ac
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: Cycle 9受理 / Issue comment 6026513855
  proof_dag_predecessors: [受理済みC1-C9, G-133の実射API]
  milestone: C/P4の原始有限列から、reading細分化・逆操作を含む両ホモトピーと同じ実診断を構成する
  proof_obligations:
    - 原始セル像・incidenceを保ち、支持述語をSourceへ逆像する
    - 正操作・原始逆pattern・台を保つ表示・reading逆像から双方向の原始chain出力を生成する
    - 原始操作列の有限帰納により基底有限和の直接r/sと両ホモトピーを生成する
    - 混在readingの独立Law座標有限和が元の各Law/valueラベルを保つ
    - 直接subset/Law射の全三成分が段階合成と等しく、空列・恒等・括り直し・全支持制限を満たす
    - 同じ射を旧H1・標準全次数homology・欠損零・実錐・G-133合成三角へ接続する
  exit_criteria:
    - 原始入力は幾何のみで、chain同値・homotopy同値・rank・診断certificateを操作入力に置かない
    - 全有限長・全初期Aを量化し、空台・loop・面辺の重複出現を含む
    - 独立生成した同じ比較/逆を全三次数と実旧H1診断で用いる
    - 両ホモトピー、全A包含Bの自然性、空列/恒等/括り直し、実合成への接続
    - focused検証・全報告宣言の公理/静的scanの成功後、新規独立PR査読を行う
  selection_reason: Eと指定例に先立ち、残る一般P4有限列構成を閉じる
  expected_result_type: proof-obligation-discharged
  lean_targets: [SourceSupportedBasis, RawChainEquivalence, PrimitiveOperationPath, MixedLawFiniteCoordinates, OperationPathDiagnostics]
  risks: [反変合成順序, 逆ホモトピーの符号, Source支持と実subsetの接続, 独立Law生成, 同じ射の錐の出所]
  unchecked: [新構成, 接続, 検証, 独立査読]
```

実装前に終了条件を固定する。E/W1–W3と別の全固定target独立4本完了監査を後続義務として保持する。終了条件を満たす前に全P4/全target完了とはしない。Research証拠はFormal未移植。

### Cycle 10 構成・条項対応・前提の使用

支持だけを `sourceSupport q supp := q.read ⁻¹' supp` へ移す。セル名、端点、面の三出現、係数は保つ。`SourceSupportedBasis` は原始有限和を同じSource支持で読み、`RawChainEquivalence` はr0/r1/r2・s0/s1/s2・h0/h1・k0/k1とchain式・両補正式を保持する**出力**である。操作の入力にこのrecordやホモトピー同値を置かない。

`PrimitiveOperation` のconstructorは三角形追加、辺分割、両原始逆pattern、原始セル表示だけである。reading細分化は同じセル名と支持逆像の表示から生成する。正操作は受理済みC2の基底表をSourceへ移す。逆操作はC4の復元幾何、正表、原始表示、正逆交換から出力する。表示の双方向表は全単射とincidence・支持適合から作る。`PrimitiveOperationPath` のnil/snoc帰納が任意有限長を量化し、直接r/sと両補正を計算する。

| 固定条項・選定義務 | 原始構成と同じ実射の接続 | 証明済み出力 |
| --- | --- | --- |
| C/P4: 原始有限列 | `RawChainEquivalence.trans` はr=r01∘r12、s=s12∘s01、h=h12+s12∘h01∘r12、k=k01+r01∘k12∘s01。`rawEquivalence` が各原始constructorとsnocで生成 | 四chain式、六補正式、全10計算成分の恒等/結合律、任意長の直接有限和 |
| C: 実subsetへの接続 | `MixedSelectedBasis` はSource原始非零項ごとに実selectedセルを選び独立有限和を作る。零延長の可換式で原始和と同定 | 実 `targetSubsetComplex` のD0/D1と可換するr/s、標準両ホモトピー、同じ旧H1/標準全整数次数 |
| C: 空列・段階合成・括り直し | `RawMapComposition`、`OperationSubsetFunctor`、`OperationPathFunctor` | 実subset対象の等号transportを含む空列r/s恒等、全三成分の段階合成、全原始10成分の括り直し。異なる操作列の同一視を要求しない |
| C: 全A包含B | `MixedRestrictionHom`、`OperationPathRestriction`、`HomotopyComponentNaturality`、`RawHomotopyRestriction` | 比較/逆の全三成分・旧H1・零延長と、両標準Homotopyの全整数成分が同じ制限と可換 |
| D: 混在readingの独立Law和 | `SourceLawCoordinates`、`MixedLawFiniteCoordinates` は同じSource非零項から同じLaw名/値と実セル座標を生成 | 実全Law D0/D1の可換式、独立比較r/s、全ラベルの各block和と同じfiber射への同定。Value全体の有限性を追加しない |
| C/D: 同じ射の診断 | `RawLawHomotopy`、`RawBlockHomotopy`、`OperationPathDiagnostics`、`RawBlockDiagnostics` | 比較/逆の同じ旧H1が同型、欠損二成分が零、全整数次数の同じ標準射の相同型、同じ標準錐の相同零 |
| D: 実分解 | `MixedLawDecomposition`、`OperationPathLawBlocks` はC9の分解bridgeを列出力に適用 | 同じ実核/余核のラベル族同値と欠損和、同じ実錐族/直和/全次数projection |
| C: G-133への接続 | `OperationPathFunctor` は同じ生成Law射の段階等号を `compositionTriangle` へ渡す | 同じ比較射の錐合成三角とdistinguished判定 |
| B/C: 基本操作・逆との同一性 | `ElementaryRawConnection`、`PresentationRawConnection/TargetConnection/Symmetry`、`InverseRawLawConnection/TargetConnection` | C2の実subset、C6/C7の実Law r/s/h、C1/C3の表示、新比較と逆、C4/C8の復元逆の全三成分等号 |
| B/C: 持ち上げの選択 | `RawLiftContext` はC5/C8の指定補正を任意の前後実射で合成する | 指定任意面出現の持ち上げと同じ列sectionの標準ホモトピー、全次数homologyと旧H1の等号 |

T0の有限Source、Reading、有限supported nerve、K1、係数ℚ、任意有限Law族と初期adequacy、Cの任意A包含Bは ambient-boundary（固定入力）。reading coarserと原始表示の全単射/incidence/支持は許された原始幾何であり、補正式や相同型を保持しない。細reading adequacyは列のcoarser定理とC1の `adequate_of_coarser` で導く。一般 `RawChainEquivalence` の十式はdirection-hypothesisとして補題に現れるが、各原始操作・有限列の具体適用では上記生成定理からdischarge-requiredとして放電する。Law座標のcell選択はSource witnessと非零項の支持保存から導出し、生成射を後で座標同型へ同定する。

chain式は実D0/D1射の構成へ、六補正式は実両ホモトピーへ、その同じr/sの標準相同型・旧H1・欠損・錐へ使用する。支持は選択セルの存在と全A/Bの自然性へ、Law adequacyは各原始Source項の同じLaw/value選択と全ラベル分解へ使用する。等しいfiber台でもラベルを同一視しない。一般有限列には空列・空台・loop・重複面出現を含む。`RawChainEquivalence.not_zero_chart_output` は粗chartがある出力のr0/s0/k0全零が補正式と矛盾することを証明する。指定例の非自明性はE/W1–W3で別に評価する。

受理済みC1–C9とG-133のsource版・hash・review参照は上記に固定済み。今回は現在の使用statement・必要な定義・適用引数を確認して再利用する。既存owner差分は `SupportedBasis` の原始零/ext API、`GeneratedComparison` の全三成分API、`ThreeHomotopy` の成分APIの計9件だけで、既存定義・statement・instance・importは不変。下流はowner公開APIを使う。Source複体への共役を経由する初期補助案は作業用に保全し、今回のspine/manifest/証拠から除外した。実selected/Law有限和を独立生成する上記構成を使う。

### Cycle 10 spine / source evidence

新規44moduleと既存3ownerの追加APIについて、47sourceの454宣言（原始操作の2型と7constructorを含む）を今回のspineに固定する。compiler生成補助宣言は各module末尾の標準公理macroでも検査する。

```text
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_targetR_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_targetS_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_lawR_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_lawS_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_lawH0_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_lawH1_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_targetR_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_targetS_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_lawR_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_lawS_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_lawH0_eq
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_lawH1_eq
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_r0
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_r1
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_r2
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_s0
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_s1
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_s2
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_h0
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawEquivalence_h1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_r0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_r1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_r2
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_s0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_s1
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_s2
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_h0
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawEquivalence_h1
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedComparisonHom_f0
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedComparisonHom_f1
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.generatedComparisonHom_f2
AAT.AG.FaceRelationSubdivision.homotopyComponent_natural
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.triangleInverse_lawR_eq
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.triangleInverse_lawS_eq
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.subdivisionInverse_lawR_eq
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.subdivisionInverse_lawS_eq
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.triangleInverse_targetR_eq
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.triangleInverse_targetS_eq
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.subdivisionInverse_targetR_eq
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.subdivisionInverse_targetS_eq
AAT.AG.FaceRelationSubdivision.labelFiber_source_preimage
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawBlockCoordinate
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawBlockCoordinate_cell
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawBlockCoordinate_val
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawBlockBasis
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawBlockRaw
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawBlockDual
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawBlockRaw_single
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawBlockDual_apply
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_block
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawBlockDual_fiber
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_fiber
AAT.AG.FaceRelationSubdivision.mixedBlockFiniteHom
AAT.AG.FaceRelationSubdivision.mixedBlockFiniteHom_f0
AAT.AG.FaceRelationSubdivision.mixedBlockFiniteHom_f1
AAT.AG.FaceRelationSubdivision.mixedBlockFiniteHom_f2
AAT.AG.FaceRelationSubdivision.mixedBlockFiniteFiber_square
AAT.AG.FaceRelationSubdivision.mixedLawFiniteBlock_square
AAT.AG.FaceRelationSubdivision.mixedBlockFiniteFiber_h1_square
AAT.AG.FaceRelationSubdivision.mixedLawFiniteBlock_h1_square
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLaw_correction_two
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLaw_correction_three
AAT.AG.FaceRelationSubdivision.mixedLawDecompositionBiproducts
AAT.AG.FaceRelationSubdivision.mixedLawFiniteFamily_natural0
AAT.AG.FaceRelationSubdivision.mixedLawFiniteFamily_natural1
AAT.AG.FaceRelationSubdivision.mixedLawFiniteFamily_natural2
AAT.AG.FaceRelationSubdivision.mixedLawFiniteFamily_square
AAT.AG.FaceRelationSubdivision.mixedLawFiniteZeroExtension_square
AAT.AG.FaceRelationSubdivision.mixedLawFiniteStandardHomology_natural
AAT.AG.FaceRelationSubdivision.mixedLawFiniteH1Family_natural
AAT.AG.FaceRelationSubdivision.mixedLawFiniteH1Family_square
AAT.AG.FaceRelationSubdivision.mixedLawFiniteKernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.mixedLawFiniteCokernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.mixedLawFiniteKernelFamilyEquiv_val
AAT.AG.FaceRelationSubdivision.mixedLawFiniteCokernelFamilyEquiv_mk
AAT.AG.FaceRelationSubdivision.mixedLawFiniteDefect_sum
AAT.AG.FaceRelationSubdivision.mixedLawFiniteConeFamilyIso
AAT.AG.FaceRelationSubdivision.mixedLawFiniteConeDirectSumIso
AAT.AG.FaceRelationSubdivision.mixedLawFiniteConeHomologyEquiv
AAT.AG.FaceRelationSubdivision.mixedLawFiniteConeFamilyIso_hom
AAT.AG.FaceRelationSubdivision.mixedLawFiniteConeHomologyEquiv_component
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.toSource_mixedLawCoordinate
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.toSource_mixedLawDual
AAT.AG.FaceRelationSubdivision.mixedLaw_sourceD1
AAT.AG.FaceRelationSubdivision.mixedLaw_sourceD2
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawCoordinate
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawCoordinate_cell
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawCoordinate_law
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawCoordinate_value
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawCoordinate_label
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawBasis
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawRaw
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawRaw_single
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_apply
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawCoordinate_source
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_source
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_apply_zero
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_apply_single
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_eq_of_raw_eq
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_comp
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_add
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_neg
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_identity
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedLawDual_square
AAT.AG.FaceRelationSubdivision.mixedLawFiniteHom
AAT.AG.FaceRelationSubdivision.mixedLawFiniteHom_f0
AAT.AG.FaceRelationSubdivision.mixedLawFiniteHom_f1
AAT.AG.FaceRelationSubdivision.mixedLawFiniteHom_f2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawR
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawS
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawR_f0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawR_f1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawR_f2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawS_f0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawS_f1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawS_f2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawR_symm
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawS_symm
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetR_restrict_square
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetR_restrict_h1_square
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetS_restrict_square
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetS_restrict_h1_square
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.target_h0_restrict_natural
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.target_h1_restrict_natural
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.target_k0_restrict_natural
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.target_k1_restrict_natural
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelectedCell
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelectedCell_val
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelectedBasis
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelected
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelected_single
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelectedEmbed_basis
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelectedEmbed_comm
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelectedEmbed_apply
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelectedDual_apply
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelected_eq_of_raw_eq
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelected_comp
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelected_add
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelected_identity
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.toSource_mixedSelected
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelected_square
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelectedDual_correction_two
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelectedDual_correction_three
AAT.AG.FaceRelationSubdivision.mixedSubsetFiniteHom
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetRHom
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetSHom
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetRHom_f0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetRHom_f1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetRHom_f2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetSHom_f0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetSHom_f1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetSHom_f2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetRHom_symm
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetSHom_symm
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.target_correction0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.target_correction1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.target_correction2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetFineHomotopy
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetFineHomotopy_hom
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetHomotopyEquiv
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.subsetSourceTransportHom
AAT.AG.FaceRelationSubdivision.subsetSourceTransportHom_rfl
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetRHom_transport
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetSHom_transport
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelected_include_natural
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.mixedSelected_dual_restrict_natural
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.single
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.rawEquivalence_single
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.append
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.append_nil
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.append_snoc
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.nil_append
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.append_assoc
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.rawEquivalence_append
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetHomologyIso
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetHomologyIso_hom
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetHomologyIso_inv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetOldH1Iso
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetOldH1Iso_hom
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetOldH1Iso_inv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetH1_bijective
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetDefect_zero
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetCone_isZero
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetSH1_bijective
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetSDefect_zero
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetSCone_isZero
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawHomologyIso
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawHomologyIso_hom
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawHomologyIso_inv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawOldH1Iso
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawOldH1Iso_hom
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawOldH1Iso_inv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawH1_bijective
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawDefect_zero
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawCone_isZero
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawSH1_bijective
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawSDefect_zero
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawSCone_isZero
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.targetSubset_nil
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.targetSubset_append
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawR_append
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawS_append
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawR_append_h1
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawS_append_h1
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawR_append_zeroExtension
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawCompositionTriangle
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawCompositionTriangle_distinguished
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawR_nil
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawS_nil
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.blockR
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.blockS
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.blockHomotopyEquiv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.blockHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.blockHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawR_block_square
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawR_block_h1_square
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawRKernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawRCokernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawRDefect_sum
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawRConeFamilyIso
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawRConeHomologyEquiv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.blockDefect_zero
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.blockCone_isZero
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetR
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetS
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetHomotopyEquiv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetR_eq_raw
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetS_eq_raw
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawR
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawS
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawHomotopyEquiv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawR_eq_raw
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.lawS_eq_raw
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.targetSubset_mono
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetR_restrict_square
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetR_restrict_h1_square
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetR_restrict_zeroExtension_square
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetS_restrict_square
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetS_restrict_h1_square
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetS_restrict_zeroExtension_square
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetR_nil
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetS_nil
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetR_append
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.subsetS_append
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_lawR_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_lawR_zeroExtension
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_lawRS
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_lawS_zeroExtension
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.source_support_eq
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceForward
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceBackward
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceForward_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceBackward_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceS0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceS1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceS2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR0_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR1_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR2_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceS0_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceS1_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceS2_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR_comm01
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR_comm12
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceForward_backward
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceBackward_forward
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.raw_inverse_comm
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceRS0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceSR0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceRS1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceSR1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceRS2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceSR2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceS_comm01
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceS_comm12
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_r0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_r1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_r2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_s0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_s1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_s2
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_h0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_h1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_k0
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_k1
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_symmSelf
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR0_eq_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR1_eq_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.sourceR2_eq_basis
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_targetR_eq_generated
AAT.AG.FaceRelationSubdivision.CellPresentationEquiv.rawEquivalence_targetS_eq_generated
AAT.AG.FaceRelationSubdivision.PrimitiveOperation
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.rawEquivalence
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.rawEquivalence_triangle
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.rawEquivalence_subdivision
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.rawEquivalence_triangleInverse
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.rawEquivalence_subdivisionInverse
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.rawEquivalence_presentation
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.coarser
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.reading
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.rawEquivalence
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.rawEquivalence_nil
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.rawEquivalence_snoc
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.coarser
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.adequate
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.targetSubset
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.targetSubset_eq_preimage
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.source_subset_eq
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.triangle
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.subdivision
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.triangleInverse
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.subdivisionInverse
AAT.AG.FaceRelationSubdivision.PrimitiveOperation.presentation
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.nil
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.snoc
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockHomologyIso
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockHomologyIso_hom
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockHomologyIso_inv
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockOldH1Iso
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockOldH1Iso_hom
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockOldH1Iso_inv
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockH1_bijective
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockDefect_zero
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockCone_isZero
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockSH1_bijective
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockSDefect_zero
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockSCone_isZero
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockR
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockS
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockR_f0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockR_f1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockR_f2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockS_f0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockS_f1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockS_f2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockR_fiber
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockS_fiber
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockHomotopyEquiv
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.blockHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.RawChainEquivalence
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm_r0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm_r1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm_r2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm_s0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm_s1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm_s2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm_h0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm_h1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.composedH0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.composedH1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.composedH0_raw
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.composedH1_raw
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.composed_sr_h0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.composed_sr_h1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.composed_sr_h2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_r0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_r1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_r2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_s0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_s1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_s2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_h0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_h1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_k0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_k1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_r0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_r1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_r2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_s0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_s1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_s2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.ext
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_h0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_h1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_k0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_k1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm_k0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.symm_k1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_assoc
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.refl_trans
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.trans_refl
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetFineHomotopy_restrict_natural
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetCoarseHomotopy_restrict_natural
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.fineHomotopy_restrict_natural
AAT.AG.FaceRelationSubdivision.PrimitiveOperationPath.coarseHomotopy_restrict_natural
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.law_correction0
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.law_correction1
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.law_correction2
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawFineHomotopy
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawHomotopyEquiv
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawHomotopyEquiv_hom
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawHomotopyEquiv_inv
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawLiftContextHomotopy
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawLiftContext_homologyMap
AAT.AG.FaceRelationSubdivision.TriangleAddition.rawLiftContext_h1Map
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawLiftContextHomotopy
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawLiftContext_homologyMap
AAT.AG.FaceRelationSubdivision.EdgeSubdivision.rawLiftContext_h1Map
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetRHom_trans
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetSHom_trans
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetRHom_refl
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.targetSHom_refl
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawR_trans
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawS_trans
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawR_refl
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.lawS_refl
AAT.AG.FaceRelationSubdivision.RawChainEquivalence.not_zero_chart_output
AAT.AG.FaceRelationSubdivision.sourceReading
AAT.AG.FaceRelationSubdivision.sourceReading_read
AAT.AG.FaceRelationSubdivision.sourceAdequate
AAT.AG.FaceRelationSubdivision.lawDescend_sourceReading
AAT.AG.FaceRelationSubdivision.sourceCoordinateEquiv
AAT.AG.FaceRelationSubdivision.sourceCoordinateEquiv_cell
AAT.AG.FaceRelationSubdivision.sourceCoordinateEquiv_law
AAT.AG.FaceRelationSubdivision.sourceCoordinateEquiv_value
AAT.AG.FaceRelationSubdivision.sourceCoordinateRead
AAT.AG.FaceRelationSubdivision.sourceCoordinateRead_apply
AAT.AG.FaceRelationSubdivision.sourceSupport
AAT.AG.FaceRelationSubdivision.mem_sourceSupport
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.toSource
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.toSource_basis
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.toSource_raw
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.toSource_comp
AAT.AG.FaceRelationSubdivision.TargetSupportedNerve.sourceD1
AAT.AG.FaceRelationSubdivision.TargetSupportedNerve.sourceD2
AAT.AG.FaceRelationSubdivision.TargetSupportedNerve.sourceD1_eq_toSource
AAT.AG.FaceRelationSubdivision.TargetSupportedNerve.sourceD2_eq_toSource
AAT.AG.FaceRelationSubdivision.TargetSupportedNerve.sourceD1_raw
AAT.AG.FaceRelationSubdivision.TargetSupportedNerve.sourceD2_raw
AAT.AG.FaceRelationSubdivision.readingPullback_source_chart
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.ext
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.ext_raw
AAT.AG.FaceRelationSubdivision.SupportedBasisMap.raw_zero
AAT.AG.FaceRelationSubdivision.homotopyComponent_10
AAT.AG.FaceRelationSubdivision.homotopyComponent_21
AAT.AG.FaceRelationSubdivision.homotopyComponent_zero_of_ne
```

対象source SHA-256（path / 今回spine数 / hash）:

```tsv
research/lean/ResearchLean/AG/FaceRelationSubdivision/ElementaryRawConnection.lean	12	39fa26d25e02a22e8c5c8c5cc6b738351c7301c6e2881d3fa8c2d83668096c5c
research/lean/ResearchLean/AG/FaceRelationSubdivision/ElementaryRawEquivalence.lean	18	5747dbb8cbb572d7628e60f024d0f7fefd85f74d9e7bd67649888874d2002e91
research/lean/ResearchLean/AG/FaceRelationSubdivision/GeneratedComparison.lean	3	66237b19c29dd64f367f898d97f822a01f798f976915077a921ed15b3a6a4af4
research/lean/ResearchLean/AG/FaceRelationSubdivision/HomotopyComponentNaturality.lean	1	87efc41e099a0eba497c47c91ee0ed23679cfb66c734c09510b43c4c4e359e05
research/lean/ResearchLean/AG/FaceRelationSubdivision/InverseRawLawConnection.lean	4	0d33da2998c91d0c122d43083bd3c6812bec71856feba752dfc10e13e82023b8
research/lean/ResearchLean/AG/FaceRelationSubdivision/InverseRawTargetConnection.lean	4	844279197b72e78eaf46c529ec000d6938f013754a83054fb0962423290d6cfa
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedLawBlock.lean	12	665609462afee3c786aecdfb14ddb887cf9050ad05273cf665962f2f96b05fca
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedLawBlockHom.lean	8	662fae6dbb16db9d8fdabfb78b84a2421b2e760d98cb1970bfd4ee21e6f63f1e
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedLawCorrections.lean	2	5b9cd5c8a7d702fdfec1125b23d3513d6d7b86c61bda29c7b4738df31d62ef12
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedLawDecomposition.lean	19	b5a02583de52c8ee41649483ea198f6d9fa3c2c1c1e0d95ca38dc05af23f69d1
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedLawDifferential.lean	4	ae5e7f8eb70d9e623f6bc924ee5df3d03d119e50c9eba8c757ceb11f8c60d5fc
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedLawFiniteCoordinates.lean	14	c50edfaf42bd5033888720684c14cf7a2a4bb2c46bff212c0639f0b2b076f5d4
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedLawFiniteFunctor.lean	6	f604494aa0dd72704685b45996d278f6a2dcd59045f587ac05a81ebe73a7d5c1
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedLawFiniteHom.lean	14	5f789cce7efaf209b9e866ff7adab869d88d2e3cca40491a15e3e9e2bb35da4a
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedRestrictionHom.lean	8	946a9e47f5fd024c040f36f73fa9d7d8f5f858038f33526ed69f4a99c10d45c0
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedSelectedBasis.lean	9	e4c9d9f1d20dace3da466c9eb62acb2d8b09fde8fd009ed87c2b6db246eb1640
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedSelectedFunctor.lean	6	4de224e774b81a5d9b1a2dd834a6f405a2163bd305b0710b67260cb67b86fdf8
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedSubsetCorrections.lean	2	46111359ecce61c489897ae07f3712e3c7dcc0410fee20eb220ff952ee210d23
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedSubsetHom.lean	11	eab3ad4d469067762177ea70a0713a32c5d8172ffa0aadffb3f80d46700bbd86
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedSubsetHomotopy.lean	8	f868edc4cd4e73ba051493596c8e145512a30628cd60b626984bb44026b2c841
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedSubsetTransport.lean	4	fd15a967efedcca47e7b22db071febeac10117fe4090ba706628dcc44f30530b
research/lean/ResearchLean/AG/FaceRelationSubdivision/MixedSupportRestriction.lean	2	480ba069bbc9633b9076b72af1f2a7416da9adf754e2cf7fcadfc582785586de
research/lean/ResearchLean/AG/FaceRelationSubdivision/OperationPathComposition.lean	8	cd08eb7ed31e3caf166c0fe6fd07387a1ee0cc7627aeb7b31220be0a277b769c
research/lean/ResearchLean/AG/FaceRelationSubdivision/OperationPathDiagnostics.lean	24	fe9371efd3e537a3bb1fdf8ef93c73d4e468c4542f06fec8b4ff845a25b88ca0
research/lean/ResearchLean/AG/FaceRelationSubdivision/OperationPathFunctor.lean	11	723882aa0699cdabd932327b68e9a52423b50504b74faf4a0358fc89ecf4ad9c
research/lean/ResearchLean/AG/FaceRelationSubdivision/OperationPathLawBlocks.lean	14	0a493b537ed49b1278de4a38d72af374fe7df66ed26816d992d763127ccb876d
research/lean/ResearchLean/AG/FaceRelationSubdivision/OperationPathMaps.lean	14	0139acadd5f82518f9b9fcfe48ae3c025169b5d265dea655c2da6cf866dfbb39
research/lean/ResearchLean/AG/FaceRelationSubdivision/OperationPathRestriction.lean	7	8c3baedbe41fd26baf3d7ce8eae7a41935a6fecaedae264ee60e392b0e769b14
research/lean/ResearchLean/AG/FaceRelationSubdivision/OperationSubsetFunctor.lean	4	d48dddeb8d1d18ee742ff1c413d13d099416246e7d24c39305cdbb9d1d724e40
research/lean/ResearchLean/AG/FaceRelationSubdivision/PresentationRawConnection.lean	4	d4fc5976cd578b0792c7b5b1d70c5e196ff031e280e174cd2774a2f9401cf011
research/lean/ResearchLean/AG/FaceRelationSubdivision/PresentationRawEquivalence.lean	41	30eba6c2bea72c54abf52462df1790b017440b782241c6a80fb44a743c2f4477
research/lean/ResearchLean/AG/FaceRelationSubdivision/PresentationRawSymmetry.lean	1	019b6622eb48c7bf84e9830b7c8f1ef6f5783dd9070291b91f8eb14d01449a69
research/lean/ResearchLean/AG/FaceRelationSubdivision/PresentationRawTargetConnection.lean	5	eb9258fc14103e3f566e476559a41d18fc649530d522f5615c8ef1a625e7f80a
research/lean/ResearchLean/AG/FaceRelationSubdivision/PrimitiveOperationPath.lean	25	99f34dc8a6a372084dc465ae746f7f54dbe28bf5632450b784e3c89d8e54f1d9
research/lean/ResearchLean/AG/FaceRelationSubdivision/RawBlockDiagnostics.lean	12	e788a2881d29b20035bc1d48e3ae33bbf21fc537384902f0ce2de66eca3526a1
research/lean/ResearchLean/AG/FaceRelationSubdivision/RawBlockHomotopy.lean	13	52dcaa91a9d81e334e1e14f71f1f5f00248d64596846a8ff737f8f8cb7371bbf
research/lean/ResearchLean/AG/FaceRelationSubdivision/RawChainEquivalence.lean	42	e44c4432445bf93c71a0e4d54261c45f3f8f953650622fecf1533c1af0d7c17d
research/lean/ResearchLean/AG/FaceRelationSubdivision/RawCompositionLaws.lean	3	6390d348c14a68244eae816e69fb2f67feade26c1679bc6d7e1fbaa72ae2d9f8
research/lean/ResearchLean/AG/FaceRelationSubdivision/RawHomotopyRestriction.lean	4	503b8808d40295ad4f7555457d3eb3fdcac9e2db4b56fc80aa0a786098b42f7f
research/lean/ResearchLean/AG/FaceRelationSubdivision/RawLawHomotopy.lean	7	08e84a3830040afebc11dc06c174dd8aa907cc38549dbca495377a9b51103292
research/lean/ResearchLean/AG/FaceRelationSubdivision/RawLiftContext.lean	6	ff12624e0fc4debe0d4e4a388841bce5e1dd8b0d9edef32bc77294c308480c6d
research/lean/ResearchLean/AG/FaceRelationSubdivision/RawMapComposition.lean	8	2a4c0d924206948f6b2bad7c1d867caa44fd4e19c9aa5e652629505121b2df7d
research/lean/ResearchLean/AG/FaceRelationSubdivision/RawNonvacuity.lean	1	486e62c0c29c93137f21485b458f14e80b0987948b694a8d6dc9b6b2f88aa7d6
research/lean/ResearchLean/AG/FaceRelationSubdivision/SourceLawCoordinates.lean	10	c99cf1da847c88064b234dc749cc4bb50623b480a26079c80d9852c26e92a0d8
research/lean/ResearchLean/AG/FaceRelationSubdivision/SourceSupportedBasis.lean	13	1d6820638f83e77733d3bf395f5bd4c34df2ba960934eb4f952795b4b2921c7e
research/lean/ResearchLean/AG/FaceRelationSubdivision/SupportedBasis.lean	3	c4292cd8333df247895da7f5f345f8c8ff49f517d7c7c34ac3406729864039de
research/lean/ResearchLean/AG/FaceRelationSubdivision/ThreeHomotopy.lean	3	e8a5bb38077c7f06fc682cb2fb72cb08f50b4da4db1b37a86ef54e45bc2b0eed
```

### Cycle 10 focused validation / proposed result

rootは必要な新規44moduleと既存3ownerを対象別 `lake env lean` で検証した。official focused selectorは `RawHomotopyRestriction.lean`、`OperationPathLawBlocks.lean`、`OperationSubsetFunctor.lean` をそれぞれ実行し成功。両標準ホモトピーの全支持制限、実Law/blockの分解・診断、同じ実subsetの空列/合成を被覆する。Research full build、aggregate、全file elaborationは未実施。

全454の明示source/spine/query/output集合が一致し、標準 `propext`、`Classical.choice`、`Quot.sound` のみ。公理log SHA-256 `ff707009fbcfa42713afa785526a96cf2c49db5898f71f5dbcdb9a1ce7ae2c89`。47source SHA-256、manifest TSV/一意性/source存在、静的import/package方向（228module）、placeholder/hidden/BiDi/privacy/新規文章の語彙、diffを検査して成功。固定commit公開面、CI、独立査読はPR固定headで判定する。

- proposed_result_type: `proof-obligation-discharged`
- exit_criteria_status: 選定した原始有限列の直接r/s・両補正・混在readingの実subset/独立Law生成・全三成分の合成/空列・全支持制限・実診断への接続を放電。
- split_reason: none
- completion_candidate: no
- selected obligation の undischarged material premise: なし。独立PR査読で検算する。
- certificate_provenance: 原始constructorと有限帰納から十式を構成し、実座標の非零項選択は支持保存とadequacyから導出。
- proof_use: 十式→実chain/両ホモトピー→同じ比較/逆の標準相同型・旧H1・欠損・錐。支持→選択/制限、adequacy→元の全Lawラベル生成/分解。
- structure_field_escape: none-found（原始入力と出力recordを区別）。
- route_integrity: pass。target_fitting/vacuity/one_way_as_equivalence/goal_or_report_reinterpretation: none-found。
- next_obligation: Eの二次関係反復、W1–W3の固定原始例と失敗例の全評価、別4本の全固定target完了監査。
- 全固定target: 未完。Research証明はFormal未移植、ArchSig実装変更なし。固定GOAL/恒久設計/仮定/量化/指定例は不変。


### Cycle 10 受理・同期

PR #5283、固定head `85516e645faa507dfc97c0dd607e209da7071c22`、merge `196125e049ba96b908bd01ca1352d8579666ab7a`。
[最終root監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5283#issuecomment-6027498363)と[新規直接確認](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5283#issuecomment-6027595301)、[Issue同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272#issuecomment-6027683257)。初回独立数学2・Lean2はMinor issues、中心findingなし。全3非中心findingを有資格な直接対応で解消し当該gate合格同等、Cycle10 proof-obligation-discharged。全454公理/47hash、root対象別とofficial3focused、各lane単一focused成功。最終head Actions `37548040279` / `37548040450` の実7jobとexternal Cloudflare成功。Formal実build/kernel/premise stepはSKIPPED。全Research build/aggregate/全file elaboration未実施。GOAL active/Issue OPEN、E/W1–W3と別の全固定target完了監査が残る。

### Cycle 11 selection — 面複製の一般実比較とW3

- ledger_type: target_cycle_result
- goal: G-134-aat-face-relation-subdivision
- cycle: 11
- goal_blob_sha: `28cbf1944d708b059cd8c4fd22f07cd8d5e1476c`
- base_oid: `196125e049ba96b908bd01ca1352d8579666ab7a`
- tracking_issue: 5272
- proof_state_ref: Cycle10受理・Issue同期および固定GOAL E/W3
- proof_dag_predecessors: C1新比較/旧埋め込み、C9全Law/fiber核余核/錐、G133 EndpointNaturality/ConeEndDegrees/NamedComparison
- milestone: 任意有限supported nerveの原始面Fから一枚の別名面を生成し、同じ全支持/各Law実比較のH¹保存と、Fが選択された場合の実H²余核および同じ標準錐H²をℚに同定する。指定W3の同時成立をこの一般構成へ接続する。
- proof_obligations: 原始face複製とK1台、旧セル恒等/fresh→F比較と旧埋め込みの同じ三成分射；全A/H¹と任意adequate Law各label/全Law保存；差fresh−Fの全射・核と実f2像の一致・実H²余核ℚ・同じ錐H²ℚ；W3 SourceBool/identityReading/identityLaw/3頂点4辺loop/同じ一面表からperiodと複製単独類・H¹ℚ恒等/H²0→ℚ・各labelと全Law2成分。
- exit_criteria: 上記一般量化と指定W3全同時条件に実宣言対応あり；同じ独立実生成微分/比較との全三成分接続あり；期待rank/相同型/非零余核を入力fieldに置かない；対象全宣言公理・focused・scanと独立PR gate完了。
- selection_reason: EはBの強い全次数同値との差を担い、W3は一般Eと同じ非零H¹例で検算する依存した到達点である。
- expected_result_type: proof-obligation-discharged
- lean_targets: FaceDuplicationGeometry、FaceDuplicationComparison、FaceDuplicationHomology、FaceDuplicationLaw、WitnessThree系
- risks: H¹の同じ次数1だけを全Hom等号と誤表示しない；H²商のkernel/rangeを抽象入力にせず原始表で放電；Law二ラベルを合併しない；標準錐は同じ実比較；W3固定period・単独cochainを全三成分実生成に接続。
- unchecked: 構成実装前。完成宣言/検証/独立査読で解消する。completion_candidateはno。

### Cycle 11 証拠対応と前提放電

この到達点は固定EとW3を扱い、W1/W2a–cおよび別の累積完了監査は次義務に残す。
一般Eは任意のsupported nerve・原始面F・全target部分集合Aを先に取り、Law側は有限Source上の任意adequate FiniteLawFamilyを後から取る。値型全体の有限性を追加しない。

| 固定条項 | 同じ入力・実射への証拠 |
| --- | --- |
| E原始追加 | `FaceDuplication.nerve/supported/fold/collapse/sectionMap`：元のchart/edge、Face=旧Face⊕PUnit、fresh→F、K1台は元のFの台。原始端点・面番号・台の全fieldを構成 |
| E全AのH¹ | `subsetHom/reverseSubsetHom` はC1の新比較から独立生成。`subsetHom_f1/reverseSubsetHom_f1`、二つのH¹合成恒等、`subsetH1Equiv_toLinearMap`。`subsetHom_eq_hereditary` は全三成分で旧射と同じ |
| E各Law/全Law | `blockHom/lawHom` は同じ原始comparisonと実CellCoordinate/既存D0,D1から独立生成。`block_subset_square` は全三次数、`blockH1Equiv_toLinearMap/lawH1Equiv_toLinearMap` は実H¹比較と同一 |
| E選択面の実余核 | `difference`=fresh−F、`difference_surjective/difference_kernel` はfresh単独と旧面制限から核=実f2像を証明。`differential_range_le` は実comm1とf1恒等から導出。`oldH2CokernelEquiv_mk` は実二重商の代表値を同じ差として評価 |
| E標準H²/同じ錐 | `standardH2CokernelOldEquiv` は同じHomのoldH2自然性。`standardH2CokernelEquiv/coneH2Equiv` はともにℚ。実blockも全三成分のcone同型からℚ。全ラベル選択時は`LawValueLabel laws → ℚ`、同じ台のラベルも別成分 |
| E全次数同値との差 | `freshOnly_cokernel_nonzero`、`standardH2_not_surjective`、`not_homotopy_equivalence`：同じ生成比較を正方向に持つ鎖ホモトピー同値を排除。選択面があるというEの条件を使用 |
| W3原始表/連結/非定数 | `ConnectedFaceWitness.q/laws/adequate/law_nonconstant/labels_distinct/labelEquiv`。3頂点Fin3、4辺Fin4、F=(0,1,2)、k=3のloop。`loop_attached/every_vertex_connected` で全頂点はvと辺e,aで連結。`WitnessThree.N/fine/comparison` は全chart台と一般Eから構成 |
| W3独立実微分と同じ射 | `blockEquiv/fineBlockEquiv` と原始endpointからD0を評価、D1はe−a+bが旧一面/細二面で同じ。`named_square` は新比較の独立実blockHomを旧埋め込みAPI経由で同じnamedHomへ接続。named写像をLaw写像の定義にはしない |
| W3同じ非零H¹ | `loopPeriod/fineLoopPeriod` の核は実boundaryToCycles像（具体potential![0,z(e),z(a)]）。`namedH1Equiv/fineNamedH1Equiv` は実H¹商→ℚ。`block_h1_identity/law_h1_identity`、`blockLoopClass_nonzero/mapped_blockLoopClass` は同じk単独1を保存 |
| W3 H²とfresh単独 | 旧実D1全射、旧標準H²零。細差の核=実D1像から`fineNamedH2Equiv/fineBlockStandardH2Equiv`→ℚ。`fineBlockStandardH2Equiv_mk/blockFreshClass_difference` は独立実degree2 classをfresh差1へ送り、`blockFresh_cokernel_nonzero` は同じ実H²比較の余核非零 |
| W3二ラベルを保持 | `labelPairEquiv` は元ラベルfalse/trueをℚ²へ個別評価。全Law H¹/細H¹は同じperiodでℚ²、旧標準H²零、細標準H²ℚ²、同じH²余核と錐H²ℚ²。各labelは一般Eの`face_selected`へ実適用 |

material premise：一般有限Source/全射reading/有限nerve/非空chart台/ℚ/adequate LawはT0入力。原始FはEの入力。
H²一般部分のhF（台∩Aが非空）はEが指定するdirection-hypothesisで、W3では全台と`labelValueFiber_nonempty`から`face_selected`が放電する。
二重商一般補題`endCokernelEquiv`のrangeD1≤rangef2は補題の方向仮定で、E適用では`differential_range_le`が同じ実comm1とf1恒等から放電する。
W3のfinite instance、surjectivity、adequacy、二ラベル、原始incidence、K1、全台、非定数Law、periodの核/全射、非零類、旧D1全射、細D1像は原始表から構成・証明した。
同型、期待rank、chain-map certificate、H²余核、相同型は入力fieldにない。

proof-use：chart台/K1→支持セル・選択面→元/fresh次数2座標。実比較comm1→二重商。差の核/全射→旧H²余核→同じ標準H²→同じ標準coneH²。独立Law三成分平方→旧H¹/標準H²自然性→各ラベル診断。具体potentialとk単独1→同じ連結入力の非零H¹、fresh単独1→実H²余核非零。元ラベルの同値→全Law二成分。

### Cycle 11 依存とAPI差分

C1/C9の受理済み新比較・旧埋め込み・全Law/fiber/錐接続は上のCycle1/Cycle9受入れ参照と同じ現在sourceに適用する。
G-133の`EndpointNaturality.oldH2Equiv_natural`、`ConeEndDegrees.comparisonConeHTwoEquiv`、`NamedComparison.namedComparisonHom_square`、`FullSupportIncidence.fullBlockNamedEquivalence/fullBlockNamedHomologyEquiv` はPR [#5265](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5265)で受理済み。
[同PR正式再査読・受入れ](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5265#issuecomment-6001311085)。同PR head `a78de2d9386d5f3877407f008988d17dea4a474e`、merge `a3f33aaaac842385f85c8494597e3bd5ccb802bc`、Endpoint/ConeEndDegrees source commit `1460ce22a8a9b8f5d014c7fc0519e9e1c09dee9f`、FullSupport source commit `a78de2d9386d5f3877407f008988d17dea4a474e`。現在statement、必要な定義、適用引数を確認。
今回は既存ownerへ4個の公開APIのみ追加：`ThreeCochainComplex.Hom.h1Map_eq_of_f1_eq`、`range_oldH2Map`、`fullBlockNamedHomologyEquiv_apply`、`fullBlockNamedHomologyEquiv_oldH2_mk`。既存定義値/statement/証明は不変。
これはno-unfold規律のowner APIで、下流が旧H¹/二重商/標準H²の内部定義を展開して接続する方法を採らない。
標準toolchain/mathlibは固定版のまま。sourceの差分は次のhash表へ固定する。

### Cycle 11 明示spine

新規12moduleと既存3owner APIの明示201宣言を受理候補として固定する。cycle scaffoldはspineへ混在させていない。

```text
AAT.AG.AtlasDefectComposition.range_oldH2Map
AAT.AG.AtlasDefectComposition.fullBlockNamedHomologyEquiv_apply
AAT.AG.AtlasDefectComposition.fullBlockNamedHomologyEquiv_oldH2_mk
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.q
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.laws
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.adequate
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.law_nonconstant
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.label
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.labels_distinct
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.labelEquiv
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.labelEquiv_symm
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.labelEquiv_label
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.nerve
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.supported
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.edgeLeft
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.edgeRight
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.faceEdge0
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.faceEdge1
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.faceEdge2
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.chartSupport
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.loop_attached
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.connecting_edges
AAT.AG.FaceRelationSubdivision.ConnectedFaceWitness.every_vertex_connected
AAT.AG.FaceRelationSubdivision.endCokernelEquiv
AAT.AG.FaceRelationSubdivision.endCokernelEquiv_mk
AAT.AG.FaceRelationSubdivision.FaceDuplication.comparison
AAT.AG.FaceRelationSubdivision.FaceDuplication.reverseComparison
AAT.AG.FaceRelationSubdivision.FaceDuplication.comparison_eq_ofHereditary
AAT.AG.FaceRelationSubdivision.FaceDuplication.subset_compatible
AAT.AG.FaceRelationSubdivision.FaceDuplication.subsetHom
AAT.AG.FaceRelationSubdivision.FaceDuplication.reverseSubsetHom
AAT.AG.FaceRelationSubdivision.FaceDuplication.comparison_chart
AAT.AG.FaceRelationSubdivision.FaceDuplication.comparison_edge
AAT.AG.FaceRelationSubdivision.FaceDuplication.comparison_face
AAT.AG.FaceRelationSubdivision.FaceDuplication.reverseComparison_chart
AAT.AG.FaceRelationSubdivision.FaceDuplication.reverseComparison_edge
AAT.AG.FaceRelationSubdivision.FaceDuplication.reverseComparison_face
AAT.AG.FaceRelationSubdivision.FaceDuplication.subsetHom_f1
AAT.AG.FaceRelationSubdivision.FaceDuplication.reverseSubsetHom_f1
AAT.AG.FaceRelationSubdivision.FaceDuplication.subsetHom_f2_eq
AAT.AG.FaceRelationSubdivision.FaceDuplication.reverse_h1Map_comp
AAT.AG.FaceRelationSubdivision.FaceDuplication.h1Map_reverse_comp
AAT.AG.FaceRelationSubdivision.FaceDuplication.subsetH1Equiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.subsetH1Equiv_toLinearMap
AAT.AG.FaceRelationSubdivision.FaceDuplication.subsetHom_eq_hereditary
AAT.AG.FaceRelationSubdivision.FaceDuplication.oldFace
AAT.AG.FaceRelationSubdivision.FaceDuplication.foldFace
AAT.AG.FaceRelationSubdivision.FaceDuplication.oldFace_val
AAT.AG.FaceRelationSubdivision.FaceDuplication.foldFace_val
AAT.AG.FaceRelationSubdivision.FaceDuplication.foldFace_oldFace
AAT.AG.FaceRelationSubdivision.FaceDuplication.subsetHom_f2
AAT.AG.FaceRelationSubdivision.FaceDuplication.subsetHom_f2_old
AAT.AG.FaceRelationSubdivision.FaceDuplication.selectedFace
AAT.AG.FaceRelationSubdivision.FaceDuplication.freshFace
AAT.AG.FaceRelationSubdivision.FaceDuplication.selectedFace_val
AAT.AG.FaceRelationSubdivision.FaceDuplication.freshFace_val
AAT.AG.FaceRelationSubdivision.FaceDuplication.foldFace_fresh
AAT.AG.FaceRelationSubdivision.FaceDuplication.difference
AAT.AG.FaceRelationSubdivision.FaceDuplication.difference_apply
AAT.AG.FaceRelationSubdivision.FaceDuplication.freshOnly
AAT.AG.FaceRelationSubdivision.FaceDuplication.freshOnly_old
AAT.AG.FaceRelationSubdivision.FaceDuplication.freshOnly_fresh
AAT.AG.FaceRelationSubdivision.FaceDuplication.difference_freshOnly
AAT.AG.FaceRelationSubdivision.FaceDuplication.difference_surjective
AAT.AG.FaceRelationSubdivision.FaceDuplication.difference_f2
AAT.AG.FaceRelationSubdivision.FaceDuplication.difference_kernel
AAT.AG.FaceRelationSubdivision.FaceDuplication.differential_range_le
AAT.AG.FaceRelationSubdivision.FaceDuplication.difference_d1
AAT.AG.FaceRelationSubdivision.FaceDuplication.fold
AAT.AG.FaceRelationSubdivision.FaceDuplication.nerve
AAT.AG.FaceRelationSubdivision.FaceDuplication.supported
AAT.AG.FaceRelationSubdivision.FaceDuplication.chartSupport_eq
AAT.AG.FaceRelationSubdivision.FaceDuplication.edgeSupport_eq
AAT.AG.FaceRelationSubdivision.FaceDuplication.edgeLeft_eq
AAT.AG.FaceRelationSubdivision.FaceDuplication.edgeRight_eq
AAT.AG.FaceRelationSubdivision.FaceDuplication.faceSupport_fold
AAT.AG.FaceRelationSubdivision.FaceDuplication.faceSupport_old
AAT.AG.FaceRelationSubdivision.FaceDuplication.faceSupport_new
AAT.AG.FaceRelationSubdivision.FaceDuplication.collapse
AAT.AG.FaceRelationSubdivision.FaceDuplication.sectionMap
AAT.AG.FaceRelationSubdivision.FaceDuplication.fold_old
AAT.AG.FaceRelationSubdivision.FaceDuplication.fold_new
AAT.AG.FaceRelationSubdivision.FaceDuplication.faceEdge0_fold
AAT.AG.FaceRelationSubdivision.FaceDuplication.faceEdge1_fold
AAT.AG.FaceRelationSubdivision.FaceDuplication.faceEdge2_fold
AAT.AG.FaceRelationSubdivision.FaceDuplication.collapse_chart
AAT.AG.FaceRelationSubdivision.FaceDuplication.collapse_edge
AAT.AG.FaceRelationSubdivision.FaceDuplication.collapse_face
AAT.AG.FaceRelationSubdivision.FaceDuplication.section_chart
AAT.AG.FaceRelationSubdivision.FaceDuplication.section_edge
AAT.AG.FaceRelationSubdivision.FaceDuplication.section_face
AAT.AG.FaceRelationSubdivision.FaceDuplication.degreeTwoQuotientEquiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.degreeTwoQuotientEquiv_mk
AAT.AG.FaceRelationSubdivision.FaceDuplication.oldH2CokernelEquiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.oldH2CokernelEquiv_mk
AAT.AG.FaceRelationSubdivision.FaceDuplication.freshOnly_cokernel_nonzero
AAT.AG.FaceRelationSubdivision.FaceDuplication.standardH2CokernelOldEquiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.standardH2CokernelEquiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.coneH2Equiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.lawHom
AAT.AG.FaceRelationSubdivision.FaceDuplication.blockHom
AAT.AG.FaceRelationSubdivision.FaceDuplication.blockHom_eq_hereditary
AAT.AG.FaceRelationSubdivision.FaceDuplication.block_subset_square
AAT.AG.FaceRelationSubdivision.FaceDuplication.blockH1Equiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.blockH1Equiv_toLinearMap
AAT.AG.FaceRelationSubdivision.FaceDuplication.lawH1Equiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.lawH1Equiv_toLinearMap
AAT.AG.FaceRelationSubdivision.FaceDuplication.blockConeH2Equiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.blockStandardH2CokernelEquiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.blockOldH2CokernelEquiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.lawConeH2Equiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.lawStandardH2CokernelEquiv
AAT.AG.FaceRelationSubdivision.FaceDuplication.standardH2_not_surjective
AAT.AG.FaceRelationSubdivision.FaceDuplication.not_homotopy_equivalence
AAT.AG.FaceRelationSubdivision.WitnessThree.d1_surjective
AAT.AG.FaceRelationSubdivision.WitnessThree.named_oldH2_subsingleton
AAT.AG.FaceRelationSubdivision.WitnessThree.namedDifference
AAT.AG.FaceRelationSubdivision.WitnessThree.namedDifference_apply
AAT.AG.FaceRelationSubdivision.WitnessThree.namedFreshOnly
AAT.AG.FaceRelationSubdivision.WitnessThree.namedDifference_freshOnly
AAT.AG.FaceRelationSubdivision.WitnessThree.namedDifference_surjective
AAT.AG.FaceRelationSubdivision.WitnessThree.namedDifference_kernel
AAT.AG.FaceRelationSubdivision.WitnessThree.fineNamedH2Equiv
AAT.AG.FaceRelationSubdivision.WitnessThree.fineNamedH2Equiv_mk
AAT.AG.FaceRelationSubdivision.WitnessThree.named_fresh_class_nonzero
AAT.AG.FaceRelationSubdivision.WitnessThree.block_standardH2_subsingleton
AAT.AG.FaceRelationSubdivision.WitnessThree.fineBlockStandardH2Equiv
AAT.AG.FaceRelationSubdivision.WitnessThree.fineBlockStandardH2Equiv_mk
AAT.AG.FaceRelationSubdivision.WitnessThree.blockFreshOnly
AAT.AG.FaceRelationSubdivision.WitnessThree.blockFreshClass
AAT.AG.FaceRelationSubdivision.WitnessThree.blockFreshClass_difference
AAT.AG.FaceRelationSubdivision.WitnessThree.blockFreshClass_nonzero
AAT.AG.FaceRelationSubdivision.WitnessThree.block_h2Map_zero
AAT.AG.FaceRelationSubdivision.WitnessThree.blockFresh_cokernel_nonzero
AAT.AG.FaceRelationSubdivision.WitnessThree.blockH1Period
AAT.AG.FaceRelationSubdivision.WitnessThree.fineBlockH1Period
AAT.AG.FaceRelationSubdivision.WitnessThree.block_h1_identity
AAT.AG.FaceRelationSubdivision.WitnessThree.blockLoopClass
AAT.AG.FaceRelationSubdivision.WitnessThree.blockLoopClass_period
AAT.AG.FaceRelationSubdivision.WitnessThree.blockLoopClass_nonzero
AAT.AG.FaceRelationSubdivision.WitnessThree.mapped_blockLoopClass_nonzero
AAT.AG.FaceRelationSubdivision.WitnessThree.fineBlockLoopClass
AAT.AG.FaceRelationSubdivision.WitnessThree.fineBlockLoopClass_period
AAT.AG.FaceRelationSubdivision.WitnessThree.mapped_blockLoopClass
AAT.AG.FaceRelationSubdivision.WitnessThree.face_selected
AAT.AG.FaceRelationSubdivision.WitnessThree.blockH2CokernelEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.blockConeH2Equiv
AAT.AG.FaceRelationSubdivision.WitnessThree.lawH2CokernelFamilyEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.lawConeH2FamilyEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.labelPairEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.lawH1Period
AAT.AG.FaceRelationSubdivision.WitnessThree.fineLawH1Period
AAT.AG.FaceRelationSubdivision.WitnessThree.law_h1_identity
AAT.AG.FaceRelationSubdivision.WitnessThree.lawH1PairEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.fineLawH1PairEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.law_standardH2_subsingleton
AAT.AG.FaceRelationSubdivision.WitnessThree.fineLawStandardH2PairEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.law_h2Map_zero
AAT.AG.FaceRelationSubdivision.WitnessThree.lawH2CokernelPairEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.lawConeH2PairEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.N
AAT.AG.FaceRelationSubdivision.WitnessThree.fine
AAT.AG.FaceRelationSubdivision.WitnessThree.comparison
AAT.AG.FaceRelationSubdivision.WitnessThree.chart_full
AAT.AG.FaceRelationSubdivision.WitnessThree.edge_full
AAT.AG.FaceRelationSubdivision.WitnessThree.face_full
AAT.AG.FaceRelationSubdivision.WitnessThree.fine_chart_full
AAT.AG.FaceRelationSubdivision.WitnessThree.fine_edge_full
AAT.AG.FaceRelationSubdivision.WitnessThree.fine_face_full
AAT.AG.FaceRelationSubdivision.WitnessThree.blockEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.fineBlockEquiv
AAT.AG.FaceRelationSubdivision.WitnessThree.d0_apply
AAT.AG.FaceRelationSubdivision.WitnessThree.d1_apply
AAT.AG.FaceRelationSubdivision.WitnessThree.fine_d0_apply
AAT.AG.FaceRelationSubdivision.WitnessThree.fine_d1_apply
AAT.AG.FaceRelationSubdivision.WitnessThree.namedHom
AAT.AG.FaceRelationSubdivision.WitnessThree.named_square
AAT.AG.FaceRelationSubdivision.WitnessThree.named_f1
AAT.AG.FaceRelationSubdivision.WitnessThree.named_f2
AAT.AG.FaceRelationSubdivision.WitnessThree.loopPeriod
AAT.AG.FaceRelationSubdivision.WitnessThree.fineLoopPeriod
AAT.AG.FaceRelationSubdivision.WitnessThree.loopPeriod_apply
AAT.AG.FaceRelationSubdivision.WitnessThree.fineLoopPeriod_apply
AAT.AG.FaceRelationSubdivision.WitnessThree.cycle_relation
AAT.AG.FaceRelationSubdivision.WitnessThree.fine_cycle_relation
AAT.AG.FaceRelationSubdivision.WitnessThree.loopPeriod_kernel
AAT.AG.FaceRelationSubdivision.WitnessThree.fineLoopPeriod_kernel
AAT.AG.FaceRelationSubdivision.WitnessThree.loopOnly
AAT.AG.FaceRelationSubdivision.WitnessThree.fineLoopOnly
AAT.AG.FaceRelationSubdivision.WitnessThree.loopPeriod_loopOnly
AAT.AG.FaceRelationSubdivision.WitnessThree.fineLoopPeriod_loopOnly
AAT.AG.FaceRelationSubdivision.WitnessThree.loopPeriod_surjective
AAT.AG.FaceRelationSubdivision.WitnessThree.fineLoopPeriod_surjective
AAT.AG.FaceRelationSubdivision.WitnessThree.namedH1Equiv
AAT.AG.FaceRelationSubdivision.WitnessThree.fineNamedH1Equiv
AAT.AG.FaceRelationSubdivision.WitnessThree.namedH1Equiv_mk
AAT.AG.FaceRelationSubdivision.WitnessThree.fineNamedH1Equiv_mk
AAT.AG.FaceRelationSubdivision.WitnessThree.named_h1_identity
AAT.AG.FaceRelationSubdivision.WitnessThree.loop_class_nonzero
AAT.AG.FaceRelationSubdivision.WitnessThree.fine_loop_class_nonzero
AAT.AG.TwoPhase.ThreeCochainComplex.Hom.h1Map_eq_of_f1_eq
```

### Cycle 11 source hashes

```text
research/lean/ResearchLean/AG/AtlasDefectComposition/EndpointNaturality.lean	1	04e56cbecdd1fc4a7c0056533c58e590750e0eb81a2f0c6371cdebde8f446b80
research/lean/ResearchLean/AG/AtlasDefectComposition/FullSupportIncidence.lean	2	46843cd005d929fb8deb0d2a8aa577a9e064b434e4e627f2049411b1dbf9c2e7
research/lean/ResearchLean/AG/FaceRelationSubdivision/ConnectedFaceWitnessInput.lean	20	e2ea6ec3a2235e2dc6c1ce4f63beb720c8e369e218bb79518ee6acc00abf9da5
research/lean/ResearchLean/AG/FaceRelationSubdivision/EndCokernel.lean	2	5dcabaa498b3c8048722b25aff0e027dfd7ad8b478e82ca7bdb1da9d1312c07e
research/lean/ResearchLean/AG/FaceRelationSubdivision/FaceDuplicationComparison.lean	20	11e130ad640b54f9686cc9add08ab1dbd6cc8e5d7ed05c76a246a5912d680229
research/lean/ResearchLean/AG/FaceRelationSubdivision/FaceDuplicationDegreeTwo.lean	23	f0e59af509e3568d8836bad2235f0192b76634ac95a157001e515111d433b935
research/lean/ResearchLean/AG/FaceRelationSubdivision/FaceDuplicationGeometry.lean	23	1454e63d524b133b552f96c6c657fe15a640485521fbd2eda2788c37ec83e03a
research/lean/ResearchLean/AG/FaceRelationSubdivision/FaceDuplicationHomology.lean	8	0991938d64d0727c5369289f01509bdbb6c82d78bbb9ded596c295bf34218136
research/lean/ResearchLean/AG/FaceRelationSubdivision/FaceDuplicationLaw.lean	13	76bb6e3b298be460026300707dbfde24f7afb90bf14a8b12dff49166842795a2
research/lean/ResearchLean/AG/FaceRelationSubdivision/FaceDuplicationSeparation.lean	2	e985be31349170f1fdb593d18620ee110227e8bab4903f1c298321f8655d8b9d
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessThreeDegreeTwo.lean	20	3bb7acd9aeee29c1e4ca38308a18f9b9264bd2398491604d56309e0862edf782
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessThreeDiagnostics.lean	26	7110da57ca54de0a526d5278f085bee34cd728d85d163174d219366871e399a0
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessThreeInput.lean	19	9d3124d4e0afd5fc5cabf0a82fbac1078b5573453394860f48a1882c24e0af4d
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessThreePeriods.lean	21	72e8e663a519d590a469bdfc9b48e3e26cfa4689e0ec5f8bb0ffee34fcad1f9a
research/lean/ResearchLean/AG/TwoPhase/CohomologyComparison.lean	1	6aaf6dbe8cd564153ca4d7cddbc55d60beb1e4d97ae1d78abfe5b2d4ca42b9f2
```

### Cycle 11 validation / result proposal

rootの対象別focused elaborationは新規12moduleと既存3owner APIで成功。最終official単一selectorは `WitnessThreeDiagnostics.lean`（26宣言）、`FaceDuplicationLaw.lean`（13）、`FaceDuplicationSeparation.lean`（2）を各別に成功。追加連結/非定数APIを持つ`ConnectedFaceWitnessInput.lean`も最終20宣言のfocused成功。
全201のsource/spine/明示#print query/出力集合一致、標準propext/Classical.choice/Quot.soundのみ。公理log SHA-256 `2b792b93220f381e2facba69ce7fc0a2cca1ac5b8921d75295544e61fac20731`。
15source hash、research-modules.txtの12新規登録/TSV一意性/全2211行source存在、import存在/方向、placeholder/hidden/BiDi/privacy、diffを機械確認。全Research build/aggregate/全file elaborationは未実施。CI・固定head独立査読はPRコメントで判定する。

- proposed_result_type: `proof-obligation-discharged`
- proof_obligation_delta / exit_criteria_status: 一般Eの全A/任意Law H¹保存、選択面H²実余核/同じ標準錐ℚ、全次数同値との差、同じ原始W3の全指定同時成立を宣言と入力生成で放電。
- split_reason: none
- completion_candidate: no
- selected obligation の undischarged material premise: なし（独立PR gateで検算）。
- certificate_provenance: 原始face追加→全field→独立実比較。二重商/difference/period/標準相同型は出力。
- structure_field_escape: none-found。route_integrity: pass。target_fitting/vacuity/one_way_as_equivalence/goal_or_report_reinterpretation: none-found。
- blocking_findings: PR独立査読前。
- next_obligation: W1 paired witness全評価、W2a–cの固定退化入力全評価、別4本の累積全固定target完了監査。
- 全固定target: 未完。GOAL active、Issue OPEN。Research成果はFormal未移植。ArchSig実装変更なし。固定GOAL/恒久設計/仮定/量化/指定例は不変。


### Cycle 11 merged receipt

PR #5284 final head `c6138111c0cb60fe566cbdcda77a4702791422ae` は merge `c36d19589ccc9a75cbfc03cf5af354e1989dd417`（2026-10-07T00:34:47Z）で main に反映済み。
数学2本・Lean2本の独立査読は全て `No major findings`。正式コメントは 6028135595 / 6028130150 / 6028148636 / 6028124788。
[root 最終受入れ](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5284#issuecomment-6028150343) は `Mergeable / No major findings / proof-obligation-discharged`。
[Issue 同期](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272#issuecomment-6028207465) で E/W3 の受理と W1/W2/別完了監査の残存を記録した。
exact-head CI 8チェック成功。Lean 37551599979 / Tool 37551599978。Formal 実 build/kernel/premise-diff は SKIPPED、Research 全体 build・aggregate・全file elaboration は未実施。

## Cycle 12 selection: W1 の全 paired witness

```yaml
ledger_type: target_cycle_result
goal: G-134-aat-face-relation-subdivision
cycle: 12
goal_blob_sha: 28cbf1944d708b059cd8c4fd22f07cd8d5e1476c
base_oid: c36d19589ccc9a75cbfc03cf5af354e1989dd417
tracking_issue: 5272
report_path: research/reports/G-134-aat-face-relation-subdivision.md
selection:
  proof_state_ref: C11 merged receipt / Issue 6028207465
  proof_dag_predecessors: [C1 incidence generation, C2 triangle contraction, C3 reading presentation, C9 Law decomposition, C10 finite composition, G133 full support incidence]
  milestone: 固定 W1 の原始 paired 入力・全 period 同定・同じ subset/block/Law 比較と実欠損を閉じる
  proof_obligations:
    - Source Bool×Bool の非対称 reading 順序と同じ非定数 Law の二ラベル
    - reading 逆像＋三角形追加の Kplus と面だけを除いた Kminus、原始 rminus=rplus j と実 uminus=jstar uplus
    - 同一連結成分の非零 loop、二辺の同じ粗像による C5 失敗、旧 hereditary field 不成立
    - 原始端点・面から生成した period 商、plus の x→x と minus の x→(x,0)
    - 同じ実比較の各ラベル核余核・全 Law 余核 Q²・blockDefect (0,0)/(0,2)
    - 全非空 A⊆Bool の同じ subset 比較と空 A の零複体恒等
  exit_criteria:
    - 全指定 W1 条項を入力からの宣言・具体類・同じ実射に対応させる
    - 外部 rank/同型/保存証明 field を置かず、全 selected material premise を放電する
    - source/spine/axiom query/output の全宣言一致と focused/必要 targeted/共通 scan を完了する
  selection_reason: 最終完了への未接続指定例 W1 を全要求同時に消化する
  expected_result_type: proof-obligation-discharged
  lean_targets: [WitnessOneInput, WitnessOneComparison, IncidenceNamedComparison, WitnessOnePeriods, WitnessOneDiagnostics, WitnessOneSubset]
  risks: [混在比較を旧 hereditary API で置換しない, named 座標は実生成後の出力として全三成分 square を証明する, 面削除以外の paired 入力を変えない, 全 subset と二 Law ラベルを保持する]
  unchecked: [W1 の実装と全指定接続, 固定 head 独立 PR gate]
```

この cycle は W1 の全要求を終了条件とし、W2a–c は次の数学的到達点とする。全 target 完了候補ではない。


### Cycle 12 claim mapping / premise / generation DAG

固定 W1 は `WitnessOneInput` → `WitnessOneComparison` → `WitnessOnePeriods` → `WitnessOnePeriodMaps` → `WitnessOneCokernel` → `WitnessOneDiagnostics` と、`FullSupportSubset` / `FullSupportSubsetComparison` → `WitnessOneSubset` で同じ入力から実現する。

| 固定 W1 の要求 | 入力からの実証拠 |
| --- | --- |
| Source Bool×Bool、qc=fst、qf=id、真の順序、実因子fst | `Source/qc/qf`, `coarser`, `not_reverse`, `factor_apply`。reading 自体が全射証明を含む constructor。 |
| 同じ非定数 Law と二発生ラベル | `laws`, `coarseAdequate/fineAdequate`, `law_nonconstant`, `label`, `labels_distinct`, `labelEquiv`。値型有限を一般仮定にしない。 |
| 粗 v,w / e1,k / 面なし、細三角形追加、面だけ除去 | `N/pulled/plus/minusNerve/minus`, `paired_table`。`plus` は C3 reading 逆像 → C1 triangle 原始 constructor の指定合成。 |
| chart 全台と K1 の辺・面台 | `chart_full`, `plus_chart_full`, `minus_chart_full` とそれぞれの `edge_full/face_full`。 |
| 非零 loop と変更部分の同一連結成分 | `loop_attached`, `every_vertex_connected` と `old_loop_nonzero/plus_loop_nonzero/minus_loop_nonzero`。 |
| 原始比較、包含、同じ三次数合成 | `inclusion/j/rPlus/rMinus`, `primitive_composition`, `block_composition/law_composition/subset_composition`。原始 r 表から各実射を独立生成。 |
| C5 失敗、旧 hereditary 条件不成立 | `distinct_lifts_same_image`, `edge_lift_uniqueness_fails`, `not_hereditary`。同じ e1/e2 と同じ f の辺像による反証。 |
| 新比較クラスと G133 全台名付き表の接続 | `IncidenceFullSupportPullback.fullBlock_pullback0/1_some/1_none/2_some/2_none`, `incidenceNamedHom`, `incidenceNamedHom_square`, `plus_named_square/minus_named_square`。全三成分同時の実正方形。 |
| 粗・plus の k period、minus の k と c−e1+e2 | `oldPeriod/plusPeriod/minusPeriod`, `plus_cycle_iff`, 三つの `*_kernel` と `*_surjective`、`oldH1Period/plusH1Period/minusH1Period`。核からの逆構成は v=0,w=z(e1),v'=z(c)。 |
| 同じ実 H¹ 比較 x→x / x→(x,0) | `plus_named_identity/minus_named_injection`, `plus_block_identity/minus_block_injection`, `plus_law_period_identity/minus_law_period_injection`。matrix は出力評価であり入力でない。 |
| 同じ loop 単独1を同じ loop 単独1へ送り非零 | `oldBlockLoop/plusBlockLoop/minusBlockLoop`, `*_period`, `plus_maps_loop/minus_maps_loop`, `*_loop_nonzero`。 |
| e2 単独1は minus の追加実余核類、plus では面微分1 | `minusSection`, `e2_plus_d1_one/e2_not_plus_cycle`, `minusBlockExtra`, `minusBlockCokernel_mk`, `minus_extra_cokernel_nonzero`。 |
| 一ラベル実核/余核 (0,0)/(0,Q) | `plus_block_injective/surjective`, `minus_block_injective`, `plus_kernel_subsingleton/plus_cokernel_subsingleton/minus_kernel_subsingleton`, `minusBlockCokernel`。 |
| 二ラベル全 Law 実余核Q²、実欠損 (0,0)/(0,2) | `minusLawCokernel`, `labelPairEquiv`, 全 Law 核・余核零定理、`plus_block_defect/minus_block_defect/plus_law_defect/minus_law_defect`。C9 の同じ独立実比較分解を適用。 |
| すべての非空 A の実 subset と空 A の零比較 | `fineSubset_nonempty`, `oldSubsetEquiv/plusSubsetEquiv/minusSubsetEquiv`, `plus_subset_square/minus_subset_square`, 三つの `*SubsetPeriod`, `plus_subset_identity/minus_subset_injection/minusSubsetCokernel`, `plus_subset_bijective/minus_subset_injective`, `emptySubsetEquiv/plus_empty_identity/minus_empty_identity`。 |

material premise の役割と使用:

- W1 の有限 Source/全射/セル有限性/非空 chart/K1/符号は原始入力 constructor と `chart_full` 群から放電し、実 Law・subset 微分の生成に使用する。
- adequacy、真の reading 細分、二発生ラベル、連結性は具体評価と原始道から放電する。rank・相同型・期待余核を field/argument に置かない。
- 一般 `IncidenceFullSupportPullback` / `incidenceNamedHom_square` の M、全台、adequacy は direction-hypothesis。W1 では rPlus/rMinus、各全台、具体 adequacy を渡して discharge-required の適用を閉じる。
- 一般 `fullSubsetNamedEquiv/fullSubsetNamed_square` の全台と A/B 非空は direction-hypothesis。W1 の全非空 A 分岐では全台定理・因子全射の `fineSubset_nonempty` から放電し、空 A 分岐を別の実零複体同型で閉じる。
- period 商同型・named 三項同型・実 kernel/cokernel 同型・二ラベル同型は入力ではなく出力。旧 `CochainEquiv.h1Equiv_naturality_apply` を同じ実射の全三成分正方形から適用する。
- structure-field escape: 新規 certificate input はない。既存 Hom/CochainEquiv の comm/両逆 field は原始表、potential、kernel/surjectivity の証明から生成する。primitive incidence M に実診断結論の field はない。
- no-unfold: 新しい semantic constructor の基本 API を同じ owner に置く。既存 `LawBlockComparison` に chart/edge/face block coordinate のセル評価 API を3本だけ追加して利用する。既存定義・statement・proof は変更しない。

再利用依存は report の既受理 C1/C3/C9 と G133 #5265 に接続する。G133 の `FullSupportBlocks/FullSupportIncidence/CochainEquivalence/LinearConjugation` は現在の source・仮定・適用引数を実読した。C9 の実全 Law 族分解は現在の `LawComparisonDefect` の同じ rPlus/rMinus に適用する。標準 Lean/mathlib 版は固定版のまま。

### Cycle 12 accepted-spine proposal

全205の明示宣言（新規11moduleの202宣言＋既存ownerの3 API）を以下に固定する。全12sourceのhashと明示 query/output の集合を機械照合した。

```text
AAT.AG.FaceRelationSubdivision.fullSelected
AAT.AG.FaceRelationSubdivision.fullSelected_val
AAT.AG.FaceRelationSubdivision.fullSelectedCochain
AAT.AG.FaceRelationSubdivision.fullSelectedCochain_apply
AAT.AG.FaceRelationSubdivision.fullSubsetNamedEquiv
AAT.AG.FaceRelationSubdivision.fullSubsetNamedEquiv_e0
AAT.AG.FaceRelationSubdivision.fullSubsetNamedEquiv_e1
AAT.AG.FaceRelationSubdivision.fullSubsetNamedEquiv_e2
AAT.AG.FaceRelationSubdivision.fullSubsetNamed_square
AAT.AG.FaceRelationSubdivision.fullBlock_pullback1_some
AAT.AG.FaceRelationSubdivision.fullBlock_pullback1_none
AAT.AG.FaceRelationSubdivision.fullBlock_pullback0
AAT.AG.FaceRelationSubdivision.fullBlock_pullback2_some
AAT.AG.FaceRelationSubdivision.fullBlock_pullback2_none
AAT.AG.FaceRelationSubdivision.namedOptionPullback
AAT.AG.FaceRelationSubdivision.namedOptionPullback_apply
AAT.AG.FaceRelationSubdivision.incidenceNamedHom
AAT.AG.FaceRelationSubdivision.incidenceNamedHom_f0
AAT.AG.FaceRelationSubdivision.incidenceNamedHom_f1
AAT.AG.FaceRelationSubdivision.incidenceNamedHom_f2
AAT.AG.FaceRelationSubdivision.incidenceNamedHom_square
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.chartBlockCoordinateMap_cell
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.edgeBlockCoordinateMap_cell
AAT.AG.FaceRelationSubdivision.IncidenceSupportedComparison.faceBlockCoordinateMap_cell
AAT.AG.FaceRelationSubdivision.WitnessOne.periodInjection
AAT.AG.FaceRelationSubdivision.WitnessOne.periodInjection_apply
AAT.AG.FaceRelationSubdivision.WitnessOne.extraProjection
AAT.AG.FaceRelationSubdivision.WitnessOne.extraProjection_apply
AAT.AG.FaceRelationSubdivision.WitnessOne.periodInjection_injective
AAT.AG.FaceRelationSubdivision.WitnessOne.extraProjection_kernel
AAT.AG.FaceRelationSubdivision.WitnessOne.extraProjection_surjective
AAT.AG.FaceRelationSubdivision.WitnessOne.injectionCokernel
AAT.AG.FaceRelationSubdivision.WitnessOne.injectionCokernel_mk
AAT.AG.FaceRelationSubdivision.WitnessOne.minusBlockCokernel
AAT.AG.FaceRelationSubdivision.WitnessOne.minusBlockCokernel_mk
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_extra_cokernel_nonzero
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_block_injective
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_block_surjective
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_block_injective
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_kernel_subsingleton
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_cokernel_subsingleton
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_kernel_subsingleton
AAT.AG.FaceRelationSubdivision.WitnessOne.inclusion
AAT.AG.FaceRelationSubdivision.WitnessOne.j
AAT.AG.FaceRelationSubdivision.WitnessOne.rPlus
AAT.AG.FaceRelationSubdivision.WitnessOne.rMinus
AAT.AG.FaceRelationSubdivision.WitnessOne.primitive_composition
AAT.AG.FaceRelationSubdivision.WitnessOne.rPlus_chart_old
AAT.AG.FaceRelationSubdivision.WitnessOne.rPlus_chart_new
AAT.AG.FaceRelationSubdivision.WitnessOne.rPlus_edge_old
AAT.AG.FaceRelationSubdivision.WitnessOne.rPlus_edge_c
AAT.AG.FaceRelationSubdivision.WitnessOne.rPlus_edge_e2
AAT.AG.FaceRelationSubdivision.WitnessOne.rPlus_face
AAT.AG.FaceRelationSubdivision.WitnessOne.rMinus_chart
AAT.AG.FaceRelationSubdivision.WitnessOne.rMinus_edge
AAT.AG.FaceRelationSubdivision.WitnessOne.distinct_lifts_same_image
AAT.AG.FaceRelationSubdivision.WitnessOne.edge_lift_uniqueness_fails
AAT.AG.FaceRelationSubdivision.WitnessOne.not_hereditary
AAT.AG.FaceRelationSubdivision.WitnessOne.blockEquiv
AAT.AG.FaceRelationSubdivision.WitnessOne.plusBlockEquiv
AAT.AG.FaceRelationSubdivision.WitnessOne.minusBlockEquiv
AAT.AG.FaceRelationSubdivision.WitnessOne.plusBlockHom
AAT.AG.FaceRelationSubdivision.WitnessOne.minusBlockHom
AAT.AG.FaceRelationSubdivision.WitnessOne.block_composition
AAT.AG.FaceRelationSubdivision.WitnessOne.plusLawHom
AAT.AG.FaceRelationSubdivision.WitnessOne.minusLawHom
AAT.AG.FaceRelationSubdivision.WitnessOne.law_composition
AAT.AG.FaceRelationSubdivision.WitnessOne.plusNamedHom
AAT.AG.FaceRelationSubdivision.WitnessOne.minusNamedHom
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_named_square
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_named_square
AAT.AG.FaceRelationSubdivision.WitnessOne.labelPairEquiv
AAT.AG.FaceRelationSubdivision.WitnessOne.minusLawCokernel
AAT.AG.FaceRelationSubdivision.WitnessOne.plusLaw_kernel_subsingleton
AAT.AG.FaceRelationSubdivision.WitnessOne.plusLaw_cokernel_subsingleton
AAT.AG.FaceRelationSubdivision.WitnessOne.minusLaw_kernel_subsingleton
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_block_defect
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_block_defect
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_law_defect
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_law_defect
AAT.AG.FaceRelationSubdivision.WitnessOne.oldLawPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.plusLawPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.minusLawPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_law_period_identity
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_law_period_injection
AAT.AG.FaceRelationSubdivision.WitnessOne.Source
AAT.AG.FaceRelationSubdivision.WitnessOne.qc
AAT.AG.FaceRelationSubdivision.WitnessOne.qf
AAT.AG.FaceRelationSubdivision.WitnessOne.laws
AAT.AG.FaceRelationSubdivision.WitnessOne.coarseAdequate
AAT.AG.FaceRelationSubdivision.WitnessOne.fineAdequate
AAT.AG.FaceRelationSubdivision.WitnessOne.coarser
AAT.AG.FaceRelationSubdivision.WitnessOne.not_reverse
AAT.AG.FaceRelationSubdivision.WitnessOne.factor_apply
AAT.AG.FaceRelationSubdivision.WitnessOne.law_nonconstant
AAT.AG.FaceRelationSubdivision.WitnessOne.label
AAT.AG.FaceRelationSubdivision.WitnessOne.labels_distinct
AAT.AG.FaceRelationSubdivision.WitnessOne.labelEquiv
AAT.AG.FaceRelationSubdivision.WitnessOne.labelEquiv_symm
AAT.AG.FaceRelationSubdivision.WitnessOne.labelEquiv_label
AAT.AG.FaceRelationSubdivision.WitnessOne.nerve
AAT.AG.FaceRelationSubdivision.WitnessOne.N
AAT.AG.FaceRelationSubdivision.WitnessOne.pulled
AAT.AG.FaceRelationSubdivision.WitnessOne.plus
AAT.AG.FaceRelationSubdivision.WitnessOne.minusNerve
AAT.AG.FaceRelationSubdivision.WitnessOne.minus
AAT.AG.FaceRelationSubdivision.WitnessOne.paired_table
AAT.AG.FaceRelationSubdivision.WitnessOne.chart_full
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_chart_full
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_chart_full
AAT.AG.FaceRelationSubdivision.WitnessOne.edge_full
AAT.AG.FaceRelationSubdivision.WitnessOne.face_full
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_edge_full
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_face_full
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_edge_full
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_face_full
AAT.AG.FaceRelationSubdivision.WitnessOne.d0_apply
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_d0_old
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_d0_c
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_d0_e2
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_d1_apply
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_d0_eq
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_d0_old
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_d0_c
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_d0_e2
AAT.AG.FaceRelationSubdivision.WitnessOne.loop_attached
AAT.AG.FaceRelationSubdivision.WitnessOne.every_vertex_connected
AAT.AG.FaceRelationSubdivision.WitnessOne.plusNamed_old
AAT.AG.FaceRelationSubdivision.WitnessOne.plusNamed_c
AAT.AG.FaceRelationSubdivision.WitnessOne.plusNamed_e2
AAT.AG.FaceRelationSubdivision.WitnessOne.minusNamed_old
AAT.AG.FaceRelationSubdivision.WitnessOne.minusNamed_c
AAT.AG.FaceRelationSubdivision.WitnessOne.minusNamed_e2
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_named_identity
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_named_injection
AAT.AG.FaceRelationSubdivision.WitnessOne.oldBlockPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.plusBlockPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.minusBlockPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_block_identity
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_block_injection
AAT.AG.FaceRelationSubdivision.WitnessOne.oldBlockLoop
AAT.AG.FaceRelationSubdivision.WitnessOne.plusBlockLoop
AAT.AG.FaceRelationSubdivision.WitnessOne.minusBlockLoop
AAT.AG.FaceRelationSubdivision.WitnessOne.minusBlockExtra
AAT.AG.FaceRelationSubdivision.WitnessOne.oldBlockLoop_period
AAT.AG.FaceRelationSubdivision.WitnessOne.plusBlockLoop_period
AAT.AG.FaceRelationSubdivision.WitnessOne.minusBlockLoop_period
AAT.AG.FaceRelationSubdivision.WitnessOne.minusBlockExtra_period
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_maps_loop
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_maps_loop
AAT.AG.FaceRelationSubdivision.WitnessOne.old_loop_nonzero
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_loop_nonzero
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_loop_nonzero
AAT.AG.FaceRelationSubdivision.WitnessOne.oldPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.plusPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.minusPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.oldPeriod_apply
AAT.AG.FaceRelationSubdivision.WitnessOne.plusPeriod_apply
AAT.AG.FaceRelationSubdivision.WitnessOne.minusPeriod_apply
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_cycle_iff
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_cycle_relation
AAT.AG.FaceRelationSubdivision.WitnessOne.oldPeriod_kernel
AAT.AG.FaceRelationSubdivision.WitnessOne.plusPeriod_kernel
AAT.AG.FaceRelationSubdivision.WitnessOne.minusPeriod_kernel
AAT.AG.FaceRelationSubdivision.WitnessOne.oldLoopOnly
AAT.AG.FaceRelationSubdivision.WitnessOne.plusLoopOnly
AAT.AG.FaceRelationSubdivision.WitnessOne.minusSection
AAT.AG.FaceRelationSubdivision.WitnessOne.oldPeriod_loop
AAT.AG.FaceRelationSubdivision.WitnessOne.plusPeriod_loop
AAT.AG.FaceRelationSubdivision.WitnessOne.minusPeriod_section
AAT.AG.FaceRelationSubdivision.WitnessOne.oldPeriod_surjective
AAT.AG.FaceRelationSubdivision.WitnessOne.plusPeriod_surjective
AAT.AG.FaceRelationSubdivision.WitnessOne.minusPeriod_surjective
AAT.AG.FaceRelationSubdivision.WitnessOne.oldH1Period
AAT.AG.FaceRelationSubdivision.WitnessOne.plusH1Period
AAT.AG.FaceRelationSubdivision.WitnessOne.minusH1Period
AAT.AG.FaceRelationSubdivision.WitnessOne.oldH1Period_mk
AAT.AG.FaceRelationSubdivision.WitnessOne.plusH1Period_mk
AAT.AG.FaceRelationSubdivision.WitnessOne.minusH1Period_mk
AAT.AG.FaceRelationSubdivision.WitnessOne.e2_plus_d1_one
AAT.AG.FaceRelationSubdivision.WitnessOne.e2_not_plus_cycle
AAT.AG.FaceRelationSubdivision.WitnessOne.fineSubset
AAT.AG.FaceRelationSubdivision.WitnessOne.fineSubset_nonempty
AAT.AG.FaceRelationSubdivision.WitnessOne.subset_compatible
AAT.AG.FaceRelationSubdivision.WitnessOne.plusSubsetHom
AAT.AG.FaceRelationSubdivision.WitnessOne.minusSubsetHom
AAT.AG.FaceRelationSubdivision.WitnessOne.j_subset_compatible
AAT.AG.FaceRelationSubdivision.WitnessOne.subset_composition
AAT.AG.FaceRelationSubdivision.WitnessOne.oldSubsetEquiv
AAT.AG.FaceRelationSubdivision.WitnessOne.plusSubsetEquiv
AAT.AG.FaceRelationSubdivision.WitnessOne.minusSubsetEquiv
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_subset_square
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_subset_square
AAT.AG.FaceRelationSubdivision.WitnessOne.oldSubsetPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.plusSubsetPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.minusSubsetPeriod
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_subset_identity
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_subset_injection
AAT.AG.FaceRelationSubdivision.WitnessOne.minusSubsetCokernel
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_subset_bijective
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_subset_injective
AAT.AG.FaceRelationSubdivision.WitnessOne.fineSubset_empty
AAT.AG.FaceRelationSubdivision.WitnessOne.emptySubsetEquiv
AAT.AG.FaceRelationSubdivision.WitnessOne.plus_empty_identity
AAT.AG.FaceRelationSubdivision.WitnessOne.minus_empty_identity
```

### Cycle 12 source hashes

```text
research/lean/ResearchLean/AG/FaceRelationSubdivision/FullSupportSubset.lean	8	fca59459f4bd2929503d6d7d81d5f458911d6c926c4d64a324151f96b3780d9a
research/lean/ResearchLean/AG/FaceRelationSubdivision/FullSupportSubsetComparison.lean	1	893423de007db0a677b7f933408bab4041ee9f45011f7042f1c79de8d98e15b0
research/lean/ResearchLean/AG/FaceRelationSubdivision/IncidenceFullSupportPullback.lean	5	93e3f546f9c6a736864d3907dade7b7f4f03e312c1aa2c3b55d18830713b8c02
research/lean/ResearchLean/AG/FaceRelationSubdivision/IncidenceNamedComparison.lean	7	56698b687013379306b13fb3bcf912d081a76ec3d4a6a71e1b644687e65f602a
research/lean/ResearchLean/AG/FaceRelationSubdivision/LawBlockComparison.lean	3	3693e88db3869c443cd490f69e9bdf7c7ce5c24ed153b16e9d5247d717131a91
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessOneCokernel.lean	18	cadd62936450ebc8aa182459de5d9ac19f588a6669dc8b87089ed7d43439d732
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessOneComparison.lean	29	17458d7bc4805cfddad36c281a2112233eb173f030eef7d6e4e5f157122ff1fb
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessOneDiagnostics.lean	14	fc3153e09a68e103c304aeda3a277eecc8bce26ffb3ea269d7179eaf23bb354f
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessOneInput.lean	42	53452d383799618adfd17ebf948ac09634efd3d578fd9bcd824f835835a72ba1
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessOnePeriodMaps.lean	26	5ca30a309100032a885b5301ad7c16f5afbb34af8905845056f724d877d09b42
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessOnePeriods.lean	28	e4323bc4049f566de85b7fd7e6ff2793dc25ca0c30f676c9190508f95ee7e687
research/lean/ResearchLean/AG/FaceRelationSubdivision/WitnessOneSubset.lean	24	3685db6fe7a65bf0b583a127ff8416e347007cdb5c1ff5a411777f78d51b4c78
```

### Cycle 12 validation / result proposal

root の必要な個別 targeted check は新規11moduleと既存 owner の3 APIで成功。最終 official focused selector は `WitnessOneDiagnostics.lean`（14宣言）と `WitnessOneSubset.lean`（24宣言）で各別に成功。全205の source/spine/明示 #print query/output の集合が一致し、標準 `propext` / `Classical.choice` / `Quot.sound` のみ。
公理 log SHA-256 `5840b3bb46781f02211e184af9fbc06ad6e63c7dfabc3ea6218e2be21be6dcac`。12source hash、manifest の11新規登録・全2222行の一意性/存在、import存在/方向、placeholder/hidden/BiDi/privacy、diffを確認。Research 全体 build・aggregate・全file elaboration は未実施。CI・固定head独立査読は PR コメントで判定する。

- proposed_result_type: `proof-obligation-discharged`
- proof_obligation_delta / exit_criteria_status: 固定 W1 の原始 paired 入力、同じ全三成分比較・合成、period の核からの逆構成、非零 loop/追加実余核、全非空 subset/空 subset、二ラベル全 Law 余核・実欠損を入力から閉じた。
- split_reason: none
- completion_candidate: no
- selected obligation の undischarged material premise: なし（独立 PR gate で検算）。
- certificate_provenance: 原始 reading/chart/edge/face/support → 独立実 subset/block/Law 生成 → 全三成分 named square → 同じ実 H¹ と余核。potential/単独 cochain と商同型は出力。
- proof_use: K1 と adequacy を生成で、原始 incidence を Hom.comm で、非空 A と因子全射を選択で、具体 potential と二単独 cochain を quotient 同定で、全三成分 square を実 H¹ 自然性で、ラベル全単射を二成分 Law 余核で使用。
- structure_field_escape: none-found。route_integrity: pass。target_fitting/vacuity/one_way_as_equivalence/goal_or_report_reinterpretation: none-found。
- blocking_findings: 独立 PR 査読前。
- next_obligation: W2a–c の全固定入力・同じ収縮式・実診断への適用、別4本の累積全固定target完了監査。
- 全固定 target は未完。GOAL active、Issue OPEN。Research成果は Formal 未移植。固定 GOAL/恒久設計/仮定/量化/指定例は不変。
