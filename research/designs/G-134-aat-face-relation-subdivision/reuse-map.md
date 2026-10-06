# G-134：既存宣言、必要な接続、新規構成

既存sourceの参照版は `6c3a960540cd0107abb549bc124338c9f1acd57b`。
以下の `RI` は `AAT.AG.ResolutionInvariance`、`ADC` は
`AAT.AG.AtlasDefectComposition`、`TP` は `AAT.AG.TwoPhase` を表す。
宣言の再利用は、その型が受け取る入力と[GOAL](../../goals/G-134-aat-face-relation-subdivision.md)
の構成対象を一致させて行う。

## 1. 原始入力・既存診断

| 既存ファイル・宣言 | 型と再利用できる内容 | 新たな接続・構成義務 |
| --- | --- | --- |
| [Reading.lean](../../lean/ResearchLean/AG/CanonicalResolution/Reading.lean)：`Reading`、`Reading.CoarserThan`、`FiniteLawFamily.Adequate` | 全射reading、kernel包含、Law評価の因子化 | 指定例の全射・adequacyを原始表から証明 |
| [ComparisonData.lean](../../lean/ResearchLean/AG/ResolutionInvariance/ComparisonData.lean)：`RI.comparisonFactor`、`comparisonFactor_surjective`、`comparisonFactor_unique`、`lawDescend_comparisonFactor` | readingとadequacyから因子・値の一致を生成 | 台の逆像によるreading変更と混在比較のLaw座標へ適用 |
| [LawGeneratedComplex.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean)：`RI.TargetSupportedNerve`、`CellCoordinate.ext`、`TargetSupportedNerve.edgeSupport`、`faceSupport`、`lawGeneratedD0`、`lawGeneratedD1`、`lawGeneratedComplex` | 有限な名前付き三角セル、非空chart台、K1、発生値の座標と実微分 | 支持chain双対との同定、二つの基本変形のsupported nerve constructor。旧複体の定義は再利用 |
| [SupportedNerveMorphism.lean](../../lean/ResearchLean/AG/ResolutionInvariance/SupportedNerveMorphism.lean)：`RI.TargetSupportedNerveMorphism`、同 `edgeSupport_compatible`、`faceSupport_compatible` | 退化面の全三辺が退化する比較。写るセルの台適合はchartから導出 | 新比較型・台適合の導出・旧比較の埋め込み。混在比較をこの旧型へ渡すことはできない |
| [GeneratedComparisonMap.lean](../../lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean)：`TargetSupportedNerveMorphism.generatedPullback0/1/2`、`generatedPullback_comm0`、`generatedPullback_comm1`、`generatedComparisonHom`、`generatedComparisonH1Map` | 旧比較と共通Law・両adequacy・有限Sourceから実Homを生成 | 新比較から同じ座標式を生成し、原始零和からcomm1を証明。旧比較へ特殊化した全成分等号 |
| [DegenerateFaceComm1Obstruction.lean](../../lean/ResearchLean/AG/ResolutionInvariance/DegenerateFaceComm1Obstruction.lean)：`RI.DegenerateFaceComm1Obstruction.generated_pullback_comm1_fails` | loopへの非零像と三重出現を持つ実Law入力でcomm1が破れる | 原始零和条件がこの表で破れることを示す。端点だけを用いる弱化の反例として保持 |
| [LawValueBlockDecomposition.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockDecomposition.lean)：`RI.LawValueLabel`、`TargetSupportedNerve.chartCochainBlockEquiv`、`edgeCochainBlockEquiv`、`faceCochainBlockEquiv` | 対象複体の全ラベルへの分解。値型全体の有限性は不要 | 新比較・section・ホモトピーの成分自然性を別途証明 |
| [ASubnerveReduction.lean](../../lean/ResearchLean/AG/UniformInvariance/ASubnerveReduction.lean)：`TargetSupportedNerve.targetSubsetComplex`、`RI.labelValueFiber`、`labelValueFiber_eq_preimage`、`TargetSupportedNerve.lawValueBlockTargetSubsetComplexEquiv` | 台がAと交わるセル、Law blockと同じfiberの複体の同値 | 新比較のsubset Homとblock比較の全次数可換図式。既存の `aSubnerveComparisonHom` と `labelFiberComparison_naturality` は旧比較を引数に取る |
| [CohomologyComparison.lean](../../lean/ResearchLean/AG/TwoPhase/CohomologyComparison.lean)：`TP.ThreeCochainComplex.H1`、同 `Hom.h1Map`、`Hom.h1Map_mk` | 任意の体上の有限三項複体の既存H¹商と実写像 | 新しい生成Homを同じ商へ渡す。別のH¹を定義して終えない |
| [DefectSemantics.lean](../../lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean)：`RI.blockDefect`、`blockDefect_eq_zero_iff_bijective` | 任意の有限次元線形写像の実核・余核の次元 | Dで同定した実H¹比較の零欠損、W1の非零余核に直接適用 |

## 2. G-133の一般APIと旧比較に依存するAPI

| 既存ファイル・宣言 | 再利用の型 | 必要な接続 |
| --- | --- | --- |
| [ComparisonComposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ComparisonComposition.lean)：`ADC.adequate_of_coarser`、`comparisonFactor_comp`、`comparisonFactor_preimage_comp` | readingだけの一般補題 | 有限列の共通Law・共通Aへ直接適用。同ファイルの `comparisonComp` の比較型は旧型なので新規合成が必要 |
| [GeneratedComposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/GeneratedComposition.lean)：`ADC.cochainComp`、`cochainComp_h1Map`、`cochain_ext` | 任意の三項複体Hom | 直接生成したセル比較との全成分一致を新規に証明し、これらへ接続 |
| [ZeroExtension.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ZeroExtension.lean)：`ADC.zeroExtension`、`zeroExtensionMap`、`zeroExtensionMap_comp`、`oldH1Equiv`、`oldH1Equiv_natural` | 任意のℚ三項複体・Hom。旧比較に依存しない | 支持chain双対のホモトピーを標準複体へ移す接続は新規。既存商との自然同型自体は再利用 |
| [CochainEquivalence.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/CochainEquivalence.lean)：`ADC.cochainEquivZeroExtensionIso` | 次数ごとの線形同型を持つ `CochainEquiv` | Law・座標・表示の同値に使う。セル数が増える細分化のr・sは次数ごとの同型ではなく、別途 `HomotopyEquiv` にする |
| [LawCochainDecomposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/LawCochainDecomposition.lean)：`ADC.lawFamilyCochainEquiv` | 対象のLaw有限族表示。比較を引数に取らない | 対象同値は直接再利用。同ファイルの `lawFamily_natural0/1/2` は旧比較用なので新しい三つの自然性が必要 |
| [LawStandardDecomposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/LawStandardDecomposition.lean)：`ADC.lawZeroExtensionIso`、`lawFamily_comparison_square`、`lawZeroExtensionIso_natural` | 最初は対象同型、後二者は旧比較を引数に取る | 新しいLaw比較の可換正方形を証明して零延長の同じ同型へ渡す |
| [LawFiberDecomposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/LawFiberDecomposition.lean)：`ADC.lawBlockFiberZeroExtensionIso`、`lawBlockFiber_comparison_square`、`lawFiberComparison_canonical` | 最初は対象同型、後二者は旧block／subset比較の同定 | 新比較でも同じfiber逆像を使い、比較の正方形と集合transportを新規に証明 |
| [ThreeComplexFamily.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ThreeComplexFamily.lean)：`ADC.ThreeComplexFamily.complex`、`map` | 任意の有限三項複体族と成分Hom | 新比較・sectionを成分別に作って直接再利用。ホモトピーの有限族化を追加 |
| [ConeEquivalence.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ConeEquivalence.lean)：`ADC.coneMapIso`、[FiniteConeFamily.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/FiniteConeFamily.lean)：`ADC.FiniteConeFamily.iso` | 任意の標準複体と同型可換正方形、任意の成分射の有限族 | 新比較のLaw自然性を渡して錐を分解する。標準錐の定義・符号は再利用 |
| [LawConeDecomposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/LawConeDecomposition.lean)：`ADC.lawConeDirectSumIso`、[LawSubsetConeDecomposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/LawSubsetConeDecomposition.lean)：`ADC.lawSubsetConeDirectSumIso` | 旧 `TargetSupportedNerveMorphism` を要求する専用API | 前行の一般APIと新しい自然性から新比較版を構成し、旧版との一致を証明 |
| [LawDefectDecomposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/LawDefectDecomposition.lean)：`ADC.lawH1KernelFamilyEquiv`、`lawH1CokernelFamilyEquiv`、[LawSubsetDefectDecomposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/LawSubsetDefectDecomposition.lean)：`ADC.lawH1Defect_subset_sum` | 旧比較の実H¹と成分写像の可換図式からの核・余核 | 新H¹自然性から同じ核・余核の同定を構成。W1の二ラベルを保持 |
| [ConeExactSequence.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ConeExactSequence.lean)：`ADC.cone_short_exact`、`cone_homology_dimension` | 任意のℤ添字標準cochain写像。次元式だけ有限次元条件を使う | 全次数同型からの錐の零性、W3のH²余核へ直接適用 |
| [ConeCompositionTriangle.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ConeCompositionTriangle.lean)：`ADC.compositionTriangle`、`compositionTriangle_distinguished` | 任意の二射と、独立した直接射が合成に等しいという証明 | 新しい直接生成・合成一致を渡す。G-133の有限tower・filtration全体を再構成する必要はない |

## 3. 参考手法と別の対象

| 既存成果 | 使える範囲とG-134の新規義務 |
| --- | --- |
| [ConditionC5NonnecessityWitness.lean](../../lean/ResearchLean/AG/UniformInvariance/ConditionC5NonnecessityWitness.lean)：`RI.R1ConditionC5Witness.c5_not_necessary`、`aSubnerveComparisonHom_h1Map_bijective` | 実入力からのperiod・余核計算の参考。二面が粗面へ写る旧比較であり、W1の零へ写る混在面の証明にはならない |
| [FiniteComparisonPresentation.lean](../../lean/ResearchLean/AG/UniformInvariance/FiniteComparisonPresentation.lean)：`RI.FiniteComparisonPresentation` | 原始有限表を先に固定する方法は再利用できる。型は旧退化条件を持つため、新比較の表と検証を別途構成する。旧checkerの結果を混在比較の証拠にしない |
| [RelativeRepairComposition/SubdivisionHomotopy.lean](../../lean/ResearchLean/AG/RelativeRepairComposition/SubdivisionHomotopy.lean)：`AAT.AG.RelativeRepairComposition.Subdivision.relativeHomotopyEquiv`、`relativeCollapse`、`relativeSection`、`relativeHomologyIso` | `OriginalTowerPresentation`、factorization、固定領域・候補辺、局所係数を持つ別の相対修復複体。実写像の式から標準homotopy同値へ進む参考手法。AATのLaw支持セルとの同値は供給せず、G-134のr・s・hへ直接特殊化できない |
| [VisibleCycleReflection/GraphH1Comparison.lean](../../lean/ResearchLean/AG/VisibleCycleReflection/GraphH1Comparison.lean)：`AAT.AG.VisibleCycleReflection.visibleBlockH1Equiv` | face型が空のグラフのperiod計算に限る。W1の面あり側や一般基本変形には、面を持つ既存H¹商とDの同定を使う |

新規の中心構成は、混在退化比較、全支持でのr・s・h、出現位置ごとの再三角形化、
逆縮約の原始パターン、有限操作列、指定例の同じ実診断への適用である。
標準のhomotopy理論はmathlibに接続する。使用版は
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`（`lake-manifest.json`）であり、
`HomotopyEquiv`、`HomotopyEquiv.trans`、`HomotopyEquiv.toHomologyIso` と標準写像錐の
型・次数・符号を使う（mathlib `Mathlib/Algebra/Homology/Homotopy.lean`）。
