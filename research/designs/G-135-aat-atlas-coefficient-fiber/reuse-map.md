# G-135：再利用、接続義務、新規構成

既存sourceの参照版は `53b6a674a29807605a943b6f6304e7b17c2da0d6`。
以下でRIは `AAT.AG.ResolutionInvariance`、FRSは `AAT.AG.FaceRelationSubdivision`、
ADCは `AAT.AG.AtlasDefectComposition` を表す。
対象同型、与えられた射の同定、新しい対象の構成を分けて記す。

## 1. 原始入力と実比較

| ファイル・実在宣言 | 再利用できる型・内容 | G-135の接続義務 |
| --- | --- | --- |
| [ComparisonData.lean](../../lean/ResearchLean/AG/ResolutionInvariance/ComparisonData.lean)：`RI.comparisonFactor`、`lawDescend_comparisonFactor`、[ComparisonComposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ComparisonComposition.lean)：`ADC.adequate_of_coarser` | 全射readingの因子、Law値の一致、細adequacy | 新しいfiber・順像の成分を同じ台とLawへ対応 |
| [LawGeneratedComplex.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean)：`RI.TargetSupportedNerve`、`lawGeneratedD0`、`lawGeneratedD1`、`lawGeneratedComplex` | K1台と実Law座標の三項複体 | Law側P・二射・完全列の自然性は新規 |
| [ASubnerveReduction.lean](../../lean/ResearchLean/AG/UniformInvariance/ASubnerveReduction.lean)：`targetSubsetComplex`、`labelValueFiber`、`labelValueFiber_eq_preimage`、`lawValueBlockTargetSubsetComplexEquiv` | 任意Aの複体とLaw値fiberへの対象同値 | セル逆像Φとは別の添字。新fiber項の供給元にはしない |
| [IncidenceComparison.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/IncidenceComparison.lean)：`FRS.IncidenceSupportedComparison`、`optionCell_incidence_iff`、`optionCell_incidence_bind`、`ofHereditary`、`comp` | 全域chart・部分edge/face、符号付き退化条件、混在分類、合成 | carrier関手とincidence圏、Φ・Γ・Λは新規構成 |
| [SubsetComparison.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/SubsetComparison.lean)：`IncidenceSupportedComparison.aSubnerveComparisonHom`、`labelFiberComparison_naturality0/1/2` | 全A・同じLaw blockの混在比較 | η・εを別に生成し、合成がこのHomであると全次数で証明 |
| [GeneratedComparison.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/GeneratedComparison.lean)：`generatedPullback0/1/2`、`generatedPullback_comm0/1`、`generatedComparisonHom`、`generatedComparisonH1Map` | 原始Law・台・Mからの実Homと既存H¹写像 | 新しいLaw順像の二射をこれらへ同定 |
| [SupportedChain.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/SupportedChain.lean)：`K0/1/2`、`chainD1/2`、`chainD1_comp_chainD2`、`freeDualEquiv`、`supportedChainHom`、`supportedChainMap0/1/2_dual` | 支持自由chain・実微分と比較の双対式 | L、商、成分係数のPとの同型は新規。chain-map式を再仮定しない |

## 2. G-133の標準構成とG-134の混在比較

| ファイル・宣言 | 適用できる入力 | 再利用後も要する証明 |
| --- | --- | --- |
| [ZeroExtension.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ZeroExtension.lean)：`zeroExtension`、`zeroExtensionMap`、`oldH1Equiv`、`oldH1Equiv_natural` | 任意のℚ三項複体とHom | P・Qを三項として構成し、同じH¹商へ接続 |
| [DefectSequence.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/DefectSequence.lean)：`DefectSequence.cancellation`、`sixTerm_exact`、`kernel_dimension`、`cokernel_dimension` | 任意の合成可能な有限次元線形二射 | εのH¹単射性を新しい短完全列から導出。相殺射が零でもτは非零になり得る |
| [ConeExactSequence.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ConeExactSequence.lean)：`cone_short_exact`、`cone_homology_dimension` | 任意の標準cochain射。次元式は有限次元性を使う | LからQへの同定、fiber錐→Qの擬同型、連結射の符号 |
| [ConeCompositionTriangle.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ConeCompositionTriangle.lean)：`compositionTriangle`、`compositionTriangle_distinguished`、`compositionTriangle_first`、`compositionTriangle_second` | 二射と独立な直接射、その合成等号 | η・ε・既存uとAで証明した等号を渡す。標準triangleの再証明は不要 |
| [LawComparisonFiberDiagnostics.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/LawComparisonFiberDiagnostics.lean)：`lawFiberH1Comparison_square`、`lawH1Defect_subset_sum`、`lawSubsetConeDirectSumIso`、`lawSubsetConeHomologyEquiv` | **混在** `IncidenceSupportedComparison` の実Law比較 | 既存の総錐・総欠損の分解は直接使える。P・L・R・τのLaw分解は新規 |
| [SupportRestriction.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/SupportRestriction.lean)：`selectedInclude`、`selectedRestrict`、`dual_selected_restrict_natural` | 支持基底写像とAの包含 | Γの成分合流・L包含・Rとτの自然性を構成 |
| [DefectSemantics.lean](../../lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean)：`RI.blockDefect`、`blockDefect_eq_zero_iff_bijective` | 有限次元線形射の核・余核 | 新しい完全列の値を同じ実H¹射の二成分へ戻す |

混在Law自然性と錐分解には、上表のFRS宣言を使う。
G-133の `LawFiberDecomposition`、`LawSubsetConeDecomposition` の旧M専用版へ
混在比較を変換し直す必要はない。汎用の標準錐・完全列は比較の種類に依存しない。

## 3. 保存操作・既存例

| ファイル・宣言 | 保持する内容 | G-135で追加する内容 |
| --- | --- | --- |
| [TriangleGeometry.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/TriangleGeometry.lean)：`TriangleAddition.supported`、`collapse`、[EdgeSubdivision.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/EdgeSubdivision.lean)：`EdgeSubdivision.supported`、`collapse` | 原始セル・台からの混在比較 | 同じ比較でΦ・Γ・順像を計算 |
| [ElementaryDiagnostics.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/ElementaryDiagnostics.lean)：`TriangleAddition.subsetH1_blockDefect_zero`、`subsetCone_isZero`、`EdgeSubdivision.subsetH1_blockDefect_zero`、`subsetCone_isZero` | 任意のAと指定基本変形の実診断保存・全次数錐零性 | ηのH¹同型とker τ=0を同じuへ接続。Pの次数別同型を前提にしない |
| [WitnessOneDiagnostics.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/WitnessOneDiagnostics.lean)：`WitnessOne.plus_block_defect`、`minus_block_defect`、`plus_law_defect`、`minus_law_defect` | 非零H¹を持つ面あり・なしの実欠損 | W4でfiberが区間であることと係数差による説明を証明 |
| [FaceDuplicationLawEndpoints.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/FaceDuplicationLawEndpoints.lean)：`FaceDuplication.blockStandardH0_bijective`、`blockStandardH2_injective`、[WitnessThreeDiagnostics.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/WitnessThreeDiagnostics.lean) | 同じ面複製比較の端次数と指定例 | P=C′、ε=id、ηの面係数対角写像への同定 |
| [ResolutionInvarianceConditions.lean](../../lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean)：`TargetSupportedNerveMorphism.CoordinateFiberEdge`、[ConditionC3NonnecessityWitness.lean](../../lean/ResearchLean/AG/UniformInvariance/ConditionC3NonnecessityWitness.lean)：`R1ConditionC3Witness.presentation`、`c3_not_necessary` | 旧C3はmapped self-loopも数える。指定例の比較はセルを同名のsomeへ送る | この同じ表のΦは選択された点の族。全AのC3′と旧C3失敗を併記する接続 |

## 4. 標準数学への接続と新規部分

mathlibの参照版は `8f9d9cff6bd728b17a24e163c9402775d9e6a365`（`lake-manifest.json`）。

| 標準source | API・役割 | Atlas側の構成義務 |
| --- | --- | --- |
| `Mathlib/CategoryTheory/Functor/KanExtension/Basic.lean`、`Pointwise.lean` | `Functor.IsRightKanExtension`、`rightKanExtension`、`rightKanExtensionCounit`、有限comma圏の極限 | carrier関手、成分式、係数射、unit・評価とcochainの一致 |
| `Mathlib/Algebra/Homology/HomologySequence.lean`、`HomologySequenceLemmas.lean` | `HomologicalComplex.HomologySequence.δ`、`δ_eq`、`homology_exact₁/₂/₃`、自然性 | P→C′→Qの標準ShortExact、H⁰Q=0、Rとの同定、τの代表式 |
| `Mathlib/Algebra/Homology/HomotopyCategory/SpectralObject.lean` | `HomotopyCategory.spectralObjectMappingCone` | carrier filtrationの低次数ページとd₁・d₂の具体的同定 |

新規の中心は、順像の普遍性と原始成分式、退化部分複体との同定、混在関係のκ、
Rを始域とするτ、pure消滅と一般消滅の有限判定、および指定例の同じ実診断への適用である。
標準の右Kan拡張や写像錐が存在することだけでは、これらの接続義務は満たされない。
