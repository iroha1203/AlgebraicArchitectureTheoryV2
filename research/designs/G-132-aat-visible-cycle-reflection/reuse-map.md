# G-132：既存宣言の型・仮定・接続

参照版は `7547b0d1dc9d523e63c0e8596180dd61e6119529`。
`ObstructionDiagnosticBridge` の受理記録は[G-125 report](../../reports/G-125-aat-obstruction-diagnostic-bridge.md)と
[PR #4822](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4822)、
[PR #4825](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4825#issuecomment-5746968898)を参照する。
ここでは現sourceの型と定義を読んだ適用計画を示す。G-132の新しい接続を検証済みとは扱わない。

以下では `P : GeneratorPresentation laws`、`D : TargetSupportedNerve q`、
`G : ContextOpenSupport S`、`C : FaceEmptyAATCechCover D G`、
`x : ActualCechAffineLocalData P C` とする。後三者を使う宣言は原則として
`[IsEmpty D.nerve.FaceComponent]` を持ち、H¹・有限座標の宣言は `[Fintype Source]` も使う。
これらの型はGOAL Aの構成から供給する。

## 1. 係数、実cochain、既存障害

最初の二列の宣言は、特記しない限り
`AAT.AG.ObstructionDiagnosticBridge.GeneratorPresentation` 名前空間にある。

| ファイル・宣言 | 実際の入力と結論 | 区分・G-132で残る仕事 |
| --- | --- | --- |
| [GeneratorPresentation.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/GeneratorPresentation.lean)：`blockLabelEquiv` | `hReflection : P.ReflectionCondition` から `P.Block ≃ LawValueLabel laws`。`Related` は原始関係の `Relation.EqvGen` | 再利用。$`R_q`$ を使う。共通chart代表は不要 |
| [PresentationGroup.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/PresentationGroup.lean)：`presentationGroupEquivBlocks` | 原始関係から作った加法合同の商 `P.PresentationGroup ≃+ FreeAbelianGroup P.Block`。$`R_q`$ は不要 | 再利用。上のラベル同値・有限座標表示と合成して $`\theta`$ を作る部分が新接続 |
| [CoefficientComparison.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/CoefficientComparison.lean)：`coefficientComparison`、`coefficientComparison_generatorClass_apply`、`blockToLawCoefficients_apply_blockLabel`、`coefficientComparison_injective` | 比較は `M_R →+ (LawValueLabel laws → ℚ)`。基底はラベルのdeltaへ写る。block係数回収と単射性には $`R_q`$ が必要 | 再利用。係数の単射性からH¹の単射性は直ちには出ない。Aの評価式とBの非零基底に使用 |
| [LocallyConstantCoefficient.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/LocallyConstantCoefficient.lean)：`locallyConstantAddCommGrpPresheaf_isSheaf`、`locallyConstantSectionEquiv`、`locallyConstantSectionEquiv_restriction` | 位相空間上の局所定数 $`M_R`$ 値層。非空preconnectedな開集合で切断と `M_R` が加法同値、制限が値を保つ | 再利用。Aの連結chartと交差へ適用する |
| [AATLocallyConstantObstruction.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/AATLocallyConstantObstruction.lean)：`aatLocallyConstantObstructionSheaf`、`aatLocallyConstantObstructionSectionEquiv`、`aatLocallyConstantObstructionSectionEquiv_restriction` | `G : ContextOpenSupport S` は `support` と `continuous` を持つ。これから既存 `ObstructionSheaf` を作り、非空preconnectedな台で座標とrestrictionを同定する | 条件付きAPIを再利用。新しいsiteの `continuous` はAで構成する義務 |
| [FaceEmptyCechNormalization.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/FaceEmptyCechNormalization.lean)：`FaceEmptyAATCechCover`、`faceEmptyCechComplex` | base・chart/edge context・restriction・各台の非空preconnected性。入力には被覆のadmissibility、全交差収載、幾何的三重交差の空性は入っていない | 新しい完全な実被覆から構成して再利用。recordの存在だけではT0・Aを満たさない |
| 同ファイル：`faceEmptyCechCochain0Equiv`、`faceEmptyCechCochain1Equiv` | 実切断の積から `Chart → M_R`、`EdgeComponent → M_R` への加法同値 | 再利用。正規化だけでなく逆写像を整数補正・失敗入力の実切断に使う |
| 同ファイル：`faceEmptyCech_d0_normalizes`、`faceEmptyCech_d1_eq_zero` | 前者は実restriction微分と `presentationD0` の一致。後者は供給された空face型からの零微分 | 再利用。幾何の完全性を先に放電し、Aの通常グラフ複体へ接続する |
| 同ファイル：`actualCechCoefficientCochain0`、`actualCechCoefficientCochain1`、`actualCechCoefficient_comm0/1` | 実cochainから既存のchart/edge Law座標への加法射、両微分との可換性 | 再利用。可視ラベル座標での評価が係数変更・制限と一致する部分は新接続 |
| [ActualCechH1Comparison.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/ActualCechH1Comparison.lean)：`actualCechDiagnosticH1Map` | `(P.faceEmptyCechComplex C).AdditiveCechH1 →+ (D.lawGeneratedComplex laws hadequate).H1`。cocycle保存とcoboundaryの像から商へ降ろす | 再利用。Aの比較の指示対象そのもの。元の射を有理線形同型と呼ばない |
| [SpecifiedAffineObstruction.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedAffineObstruction.lean)：`ActualCechAffineLocalData`、同名前空間の `actualMismatch`、`diagnosticMismatch`、`h1_map_actual_class_eq_diagnostic_class` | `transition : Cn 1`、`localState : Cn 0`。独立したLaw評価式に対し `Φ actualClass = diagnosticClass` を証明。共通代表と $`R_q`$ は不要 | 再利用。Aの全 $`(\xi,p)`$ と指定類の一致に適用する |
| 同名前空間：`actual_class_adjust_local_state` | `localState` に任意の実0-cochainを加えても `actualClass` は不変 | 再利用。固定遷移で局所表示だけ変える操作と、Bの失敗入力の生成を区別する |
| [ExistingObstructionBridge.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/ExistingObstructionBridge.lean)：`ActualCechAffineLocalData.existingDescentObstructionClass`、`existingDescentAdditiveClass_eq_actualClass` | 既存 `GluingMismatchData`・`descentCocycle`・`descentObstructionClass` を使う。legacy `CoverRelativeHn 1` を `legacyCechH1EquivAdditiveCechH1` で移すと `actualClass` に等しい | 再利用。左右の実restrictionとtransitionから比較を作る現在の経路を保持。Aの指定類とBの非零性へ |
| [IntegralReflection.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/IntegralReflection.lean)：`AAT.AG.ObstructionDiagnosticBridge.IntegralReflection.exists_integral_correction` | 任意の `source target : Edge → Vertex`、`z : Edge → Block → ℤ`、`b : Vertex → Block → ℚ` と **全辺の** 差の一致から整数補正の存在を得る | 再利用。診断零から全N上の `b` を導くことは新規義務。floorを使うための前提を入力に追加しない |
| [SpecifiedClassReflection.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedClassReflection.lean)：`ActualCechAffineLocalData.diagnostic_class_eq_zero_iff_actual_class_eq_zero` | `hadequate`、`hsupport : CommonLabelChartSupport D laws hadequate`、`hReflection` を取る | 旧十分条件の比較用。W1には直接適用できず、Bの三条件同値を既証明とする根拠には使わない |

## 2. 既存のラベル分解

次は `AAT.AG.ResolutionInvariance.TargetSupportedNerve` の宣言である。
分解の部分を今回の新規結果として数えず、通常の可視グラフ複体への同定を新しい接続とする。

| ファイル・宣言 | 型・使用条件 | 新しい接続 |
| --- | --- | --- |
| [LawGeneratedComplex.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean)：`TargetSupportedNerve.edgeSupport`、`CellCoordinate`、`lawGeneratedD0` | 台は同じtargetの共通所属。座標はcell・Law・値と発生の存在証明で、target証人は座標の成分ではない | 可視頂点・辺との同値を作り、同じ値の別証人を重複させない |
| [LawValueBlockDecomposition.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockDecomposition.lean)：`ChartBlockCoordinate`、`EdgeBlockCoordinate`、`lawValueBlockComplex` | `CellCoordinate.lawValueLabel` のfiberとその右−左微分 | `N_λ` の頂点・辺へのcell射影が同値であり、端点・微分を保つことを証明 |
| 同ファイル：`chartCochainBlockEquiv`、`edgeCochainBlockEquiv`、`lawGeneratedD0_block_intertwining`、`lawGeneratedD1_block_intertwining` | 有限Sourceから生成される有限ラベル集合の直和への線形同値と微分の可換性 | グラフcochainの同値と合成する。ここまでの診断分解自体は $`R_q`$ を要しない |
| [LawValueBlockCohomology.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockCohomology.lean)：`lawGeneratedH1BlockEquiv`、`lawGeneratedH1BlockEquiv_mk_component` | 既存H¹商と各block H¹商の有限直和の線形同値、代表元の各成分の計算式 | Aの実比較を各可視グラフH¹への制限へ追う。$`R_q`$ は整数障害側の座標化で使用 |

## 3. 特殊化された実被覆と新規結果

| 既存の所在 | そのまま使える範囲 | 一般化・新規構成 |
| --- | --- | --- |
| [FiniteCoverGeometry.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/FiniteCoverGeometry.lean) | `SelectedFiniteGeometry.Space`、`patch`、`CompleteFaceIndex` と固定粗細被覆の非空・連結・完全face証明 | 任意の有限単純グラフの頂点≤接続辺点、完全edge index、W1–W3の被覆を構成する。八点・固定粗細被覆を一般結果として引用しない |
| [PointGeneratorAtomInput.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/PointGeneratorAtomInput.lean)、[CombinedAtomContextSupport.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomContextSupport.lean)、[CombinedAtomContextContinuity.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomContextContinuity.lean) | 固定point/generator carrier、context、台のproduct一致、cover・continuityの証明構成 | T0の点空間と原始生成子に一般化する。新しい定理を新Research領域へ置き、既存の特殊化を読み替えない |
| [CombinedAtomActualNerve.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomActualNerve.lean) | 固定site・固定nerveの `fineCechCover`、`coarseCechCover` | 新しい完全nerveと診断台を持つcover recordを実restrictionから構成 |
| [SelectedFiniteObstructionExamples.lean](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedFiniteObstructionExamples.lean) | 固定三角形のperiodと既存類の計算方法 | 一般の非橋辺から閉路を構成し、そのperiodで任意の失敗入力の既存類を検出する |
| Mathlib `Combinatorics/SimpleGraph/Connectivity/Connected.lean`：`SimpleGraph.IsBridge`、`isBridge_iff`、`isBridge_iff_mem_and_forall_cycle_notMem` | 辺削除後に両端が到達不能という定義と、どの閉路にも現れないことによる特徴づけ | 成分数による橋、chainのcycle space、可視部分のH₁全射性を接続する |
| G-125の整数補正・既存障害のAPI | 診断→係数・類・補正の各接続 | アフィン状態層 $`\mathcal T_\xi`$ の局所自明化・層条件・実貼り合わせは新規。既存の類の一致を貼り合わせ証明と同一視しない |

標準ライブラリの参照版はLean `v4.28.0`、mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`（`lake-manifest.json`）。
これらのグラフ宣言は通常の単純グラフを扱う。loop・平行辺のある一般graphの結果を使う場合は、
別の型・仮定として表示し、T0のnerveとの対応を省略しない。
