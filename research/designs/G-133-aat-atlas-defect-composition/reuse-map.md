# G-133：既存宣言・接続補題・新規部分

参照版は `aa544f1755484cb05894f7fb54631be8dd7203a7`。
以下は現sourceの定義・statement・仮定を照合した再利用計画であり、新規接続の検証結果ではない。
G-104/G-107由来の宣言をG-132の成果として数えない。

先行成果の受理記録は、[G-104 report](../../reports/G-104-aat-resolution-invariance.md)の
Cycle 8–13・完了判定と [PR #3943](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/3943)、
[G-107 report](../../reports/G-107-aat-uniform-invariance-characterization.md)のCycle 1・3–6・8と
[PR #3994の監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/3994#issuecomment-5279154319)を参照する。
実装時は今回使う宣言・適用引数をreportへ対応させる。

## 1. G-132以前のAtlasからの再利用

以下の `RI` は `AAT.AG.ResolutionInvariance`、`TP` は `AAT.AG.TwoPhase` を表す。
`N` は `RI.TargetSupportedNerve q`、`M` は二つのその対象間の既存部分比較である。

| ファイル・実在宣言 | 型・仮定・既に得られる内容 | G-133で接続する先 |
| --- | --- | --- |
| [Reading.lean](../../lean/ResearchLean/AG/CanonicalResolution/Reading.lean)：`Reading`、`Reading.CoarserThan`、`FiniteLawFamily.Adequate` | 全射Source読み、kernel包含、Law評価の因子化。H¹条件は持たない | T0。三段の細かいreadingのadequacyを粗側から導出 |
| [ComparisonData.lean](../../lean/ResearchLean/AG/ResolutionInvariance/ComparisonData.lean)：`RI.comparisonFactor`、`comparisonFactor_commutes`、`comparisonFactor_unique`、`lawDescend_comparisonFactor` | readingの順序とadequacyから因子・Law降下・値の一致を生成 | A。三段の因子合成は一意性から導く新規補題 |
| [LawGeneratedComplex.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean)：`RI.TargetSupportedNerve`、`RI.CellCoordinate`、`N.edgeSupport`、`N.faceSupport`、`N.lawGeneratedComplex` | 有限セル、非空chart台、面の端点整合。辺・面台は交差、K0座標は発生するLaw・値。有限Sourceから有限次元のℚ三項複体 | T0・A・D・W。供給するのはセル・台・評価で、微分は出力 |
| [SupportedNerveMorphism.lean](../../lean/ResearchLean/AG/ResolutionInvariance/SupportedNerveMorphism.lean)：`RI.TargetSupportedNerveMorphism`、`M.edgeSupport_compatible`、`M.faceSupport_compatible` | 細→粗のchart全域写像とedge/face部分写像。退化面は全三辺が退化。edge/face台適合はchart適合から導く | A。合成と全fieldの放電を新規に構成 |
| [GeneratedComparisonMap.lean](../../lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean)：`M.generatedPullback0/1/2`、`generatedPullback_comm0/1`、`generatedComparisonHom`、`generatedComparisonH1Map` | 共通Law、両adequacy、有限Source。退化セルを零へ送る粗→細の生成Homと既存H¹商の線形写像 | A・Bの指示対象。三段合成等式はこのファイルにはない |
| [CoefficientComplex.lean](../../lean/ResearchLean/AG/TwoPhase/CoefficientComplex.lean)：`TP.ThreeCochainComplex`、同 `Hom` | 有限次元のC0・C1・C2、二微分と二つの可換式 | C。ℤ添字mathlib複体への零延長は新しい接続 |
| [CohomologyComparison.lean](../../lean/ResearchLean/AG/TwoPhase/CohomologyComparison.lean)：`ThreeCochainComplex.H1`、`Hom.cyclesMap`、`Hom.h1Map`、`Hom.h1Map_mk`、`Hom.range_h1Map` | 任意の体上の有限三項複体。H¹は `ker d1 / range boundaryToCycles` | A・B・C。既存商を変えずHom合成・標準homologyの自然同型を作る |
| [LawValueBlockDecomposition.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockDecomposition.lean)：`RI.LawValueLabel`、`CellCoordinate.cochainBlockEquiv`、`N.chartCochainBlockEquiv`、`edgeCochainBlockEquiv`、`faceCochainBlockEquiv`、`lawGeneratedD0_block_intertwining`、`lawGeneratedD1_block_intertwining` | 有限SourceとLaw。値型自体の有限性は不要。次数別の有限直和同値と微分の可換性 | D。ラベル重複度を保持したcochain・錐分解 |
| [LawValueBlockCohomology.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockCohomology.lean)：`N.lawGeneratedH1BlockEquiv`、`lawGeneratedH1BlockEquiv_mk_component` | 全体H¹とblock H¹の直和の線形同値、代表元の成分式 | D・W。分解そのものは再利用 |
| [LawValueBlockComparison.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparison.lean)：`M.generatedBlockComparisonHom`、`generatedBlockComparisonH1Map`、`generatedPullback0_block_component`、`generatedPullback1_block_component`、`generatedPullback2_block_component` | 同じラベルのblock写像と全次数の生成比較との成分一致 | D。H¹だけでなく錐へ進むための入力 |
| [LawValueBlockComparisonNaturality.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonNaturality.lean)：`M.generatedBlockComparisonH1DirectSumMap`、`generatedComparisonH1Map_block_naturality` | `fineBlockEquiv ∘ globalMap = blockSumMap ∘ coarseBlockEquiv`。`ConditionC`不要 | B・D。一般の比較で核・余核とχを直和へ移す |
| [ASubnerveReduction.lean](../../lean/ResearchLean/AG/UniformInvariance/ASubnerveReduction.lean)：`N.targetSubsetComplex`、`RI.labelValueFiber`、`labelValueFiber_eq_preimage`、`N.lawValueBlockTargetSubsetComplexEquiv` | 台と部分集合が交わるセルの定数ℚ複体。block fiberとA-subnerveを同定 | D・E。三段のfiberと署名の同定 |
| 同ファイル：`M.targetSubsetComparisonHom`、`aSubnerveComparisonHom`、`labelFiberComparison_naturality` | 前者は細subsetが粗subsetへ写る条件、後者はcanonical逆像を使用。naturalityは全三次数 | A・B・D。任意Aを扱い、空Aも保持 |
| [UniformityReduction.lean](../../lean/ResearchLean/AG/UniformInvariance/UniformityReduction.lean)：`ThreeCochainComplex.CochainEquiv.h1Equiv`、`h1Equiv_naturality_apply`、`M.labelFiberComparison_h1_naturality` | cochain同値から既存商の同値、比較のH¹自然性 | A・Dのsubtype transportと商の対応 |
| [IndicatorLawFamily.lean](../../lean/ResearchLean/AG/UniformInvariance/IndicatorLawFamily.lean)：`indicatorLawFamily`、`indicatorLawFamily_adequate_both`、`indicatorLawFamilyTrueLabel`、`indicatorLawFamily_trueFiber_eq`、`indicatorLawFamily_trueFineFiber_eq_preimage` | 指示Lawのtrueラベルには `A.Nonempty` が必要。Law全体は補集合のfalseラベルも持ちうる | D・Eの任意非空Aのselected block実現 |
| [DefectSemantics.lean](../../lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean)：`RI.blockDefect`、`blockDefect_eq_finrank_sub_range`、`blockDefect_eq_zero_iff_bijective`、`M.aSubnerveDefect` | 核のfinrankと実際の `codomain / range` のfinrank。零性同値には有限次元性が必要 | B。三段のχ・完全列・欠損合成は新規接続 |
| [UniformityInstancePairs.lean](../../lean/ResearchLean/AG/UniformInvariance/UniformityInstancePairs.lean)：`TargetSupportedNerveMorphism.identityMorphism`、`identityMorphism_targetSubsetComparisonHom_h1Map` | 任意の同じreading・supported nerve上の恒等比較 | Aの恒等、W2。異なるreading間のM02そのものとは区別 |
| [FiniteComparisonPresentation.lean](../../lean/ResearchLean/AG/UniformInvariance/FiniteComparisonPresentation.lean)：`FiniteComparisonPresentation`、`toGeometry`、`computedFactor_eq_comparisonFactor` | 二段の有限表とincidence・全射・適合条件から既存幾何を作る | Wの表現候補。三段の共通Sourceと合成表は新たに構成 |
| [PresentationASubnerveDefect.lean](../../lean/ResearchLean/AG/UniformInvariance/PresentationASubnerveDefect.lean)：`computedASubnerveDefect`、`computedASubnerveDefect_eq_aSubnerveDefect` | 有理rank計算を実際のH¹比較の欠損へ接続 | Wの検算と理論上の有限表。Rust実装への同値定理ではない |

`generatedComparisonH1Map_bijective` 等のC0–C6を仮定する十分条件は、
今回の一般合成・相殺・錐の構成の前提には使わない。W1は後段chart写像が全射でない。

## 2. G-132からの再利用

受理記録は [G-132 report](../../reports/G-132-aat-visible-cycle-reflection.md)、
[Issue #5250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5250)、
[PR #5259](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5259)とその先行cycleにある。
以下の名前空間は特記しない限り `AAT.AG.VisibleCycleReflection`。

| ファイル・宣言 | 実際の仮定・出力 | 使用計画 |
| --- | --- | --- |
| [VisibleCoordinates.lean](../../lean/ResearchLean/AG/VisibleCycleReflection/VisibleCoordinates.lean)：`blockCellEquiv`、`visibleCochain0Equiv`、`visibleCochain1Equiv`、`visibleD0_intertwining` | 同じラベルが台に現れるセルへのblock座標同値、頂点差分の一致 | W1のgraph period計算に再利用可能。比較の合成や錐の定理を含むとは扱わない |
| [GraphH1Comparison.lean](../../lean/ResearchLean/AG/VisibleCycleReflection/GraphH1Comparison.lean)：`visibleBlockH1Equiv`、`visibleBlockH1Equiv_mk` | 有限Source、adequacy、**face型の空性**の下でblock H¹を辺cochain／頂点差分へ同定 | W1のみに使用可能。面を持つW3bや一般T0へこの前提を持ち込まない |
| 同ファイル：`actualCechDiagnosticH1Map_factorization` | `GeneratorPresentation`、実face-empty被覆、`ReflectionCondition` の下で、整数障害の加法H¹→有理診断を係数変更と可視制限に分解 | 関連成果の区別用。G-133の粗細間のℚ線形 `generatedComparisonH1Map` そのものではなく、A–Fの前提にも採用しない |

G-132の橋・可視閉路・整数補正・実貼り合わせ・失敗入力の定理は、今回の六項列や
台署名の普遍性を証明するものではない。G-130/G-131の相対修復・観測最適性も
同じ理由で本targetの必須predecessorに追加しない。

## 3. 標準数学APIと新しい接続

mathlibの参照版は `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。

| ファイル・宣言 | 再利用する標準構成 | G-133で新たに証明する対応 |
| --- | --- | --- |
| [MappingCone.lean](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean)：`CochainComplex.mappingCone`、`mappingCone.inr`、`mappingCone.fst`、`mappingCone.isZero_X_iff` | ℤ添字cochain複体の錐。sourceの次数m+1とtargetの次数mを使う | 既存三項複体の零延長、既存H¹商との同型、Cの符号・次数・短完全列 |
| [Pretriangulated.lean](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean)：`CochainComplex.mappingCone.map`、`map_id`、`map_comp` | 可換正方形からの錐の射と関手性 | 台制限・Law blockの実可換図式を渡し、Eの錐関手へ |
| [Triangulated.lean](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean)：`CochainComplex.mappingConeCompTriangle`、`mappingConeCompHomotopyEquiv`、`HomotopyCategory.mappingConeCompTriangleh_distinguished` | 合成錐のtriangle、反復錐と後段錐のhomotopy同値 | Aで作った直接比較への移送、Fの有限towerとfiltration |
| [SnakeLemma.lean](https://github.com/leanprover-community/mathlib4/blob/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean)：`CategoryTheory.ShortComplex.SnakeInput.snake_lemma`、`naturality_δ` | abelian圏の完全列と連結射の自然性 | Bの六項を構成する場合の再利用候補。一般入力recordの存在だけでAAT比較への接続を済ませない |
| `LinearMap.ker`、`LinearMap.range`、`Submodule.mapQ`、`LinearMap.finrank_range_add_finrank_ker`、`Submodule.finrank_quotient_add_finrank` | 実線形写像の核・余核・rankと次元 | Bのχ、商の同型と欠損合成。すでに `DefectSemantics` が使用するAPI |

公式の[写像錐API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.html)も参照できるが、
実装時は上の固定版にある型・符号で照合する。

## 4. 接続補題と本質的な新規部分の分担

| 区分 | 構成・証明義務 | GOAL |
| --- | --- | --- |
| 新しい接続補題 | 因子合成、部分incidence射の合成、Law座標とsubset transport、既存Hom・H¹の合成 | A |
| 新しい接続補題 | 三項複体とmathlibの零延長・homology、錐の符号、直和の交換 | C・D |
| 新しい接続補題 | 台包含のcochain制限、kernel/cokernelとχの自然性、三段署名への射影 | E |
| 新規のAAT構成と主張 | 同じ実入力の生成比較で相殺類を同定し、非零χと直接比較の零欠損を実現 | B・W1 |
| 新規のAAT構成と主張 | 全比較セルを復元する最粗商、実Lawから重複度付き署名への表現と対象・射を保つ復元 | E・W2 |
| 標準構成の新しい適用 | 実生成比較の錐の各次数・合成triangle・有限filtration、2-cellを持つ追加寄与例 | C・F・W3 |

本表の新規欄はすべて未実装のproof obligationである。
既存の同型・完全列の再包装だけでは、生成経路と指定例の義務は放電されない。
