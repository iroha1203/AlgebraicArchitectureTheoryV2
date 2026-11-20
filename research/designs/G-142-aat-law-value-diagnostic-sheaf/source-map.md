# G-142の固定target・source・仮定の対応

## 固定targetとの対応

[GOALのA–G・W](../../goals/G-142-aat-law-value-diagnostic-sheaf.md)に対応する紙上証明を以下に置く。既存Lean宣言への接続は同じdataのmapを同定するものであり、この文書群全体のLean形式化を意味しない。

| 固定target | 証明 | 原始入力から得るもの |
| --- | --- | --- |
| A 全有限入力・整数診断 | [A1](integer-diagnostics.md) | 全射readingからの値、重複を除くlabel、端点による `d¹d⁰=0` |
| A Tensor・K0/K1・比較 | [A2](integer-diagnostics.md) | 有限delta basis、両微分、退化cellを零とするgenerated map |
| A Flat・faithfully flat | [A3](integer-diagnostics.md) | cycle・coboundaryの完全列、指定類の零性反映 |
| B Scalar readout・GL | [B1](diagnostic-sheaves.md) | 原始式評価、traceの不変性、成分の変換則 |
| B Root scheme・実restriction | [B2](diagnostic-sheaves.md) | monic商、空支持、閉埋込み、層の両微分 |
| B Stalk・任意base change | [B3–B4](diagnostic-sheaves.md) | 相異なる幾何root、K0/K1、非flatを含む基底変更 |
| B 診断係数・partition・普遍族 | [B4–B5](diagnostic-sheaves.md) | 項のflatness、導来tensor、差の零・可逆条件、CRT、普遍座標 |
| B Reading代入 | [B4・B6](diagnostic-sheaves.md) | 同じ式のpullback、finite descentのequalizer、Source合併のcomponent map |
| C 全partition粗化・特殊化 | [C1–C2](collision-comparison.md) | 値別の部分複体、合併からの制限、strict henselian局所成分 |
| C 二値合流・核・余核 | [C3](collision-comparison.md) | cellごとの短完全列、連結map、同型条件とrank |
| C 任意有限block族・順序 | [C2・C4](collision-comparison.md) | 全交差の二重複体、cellwise収縮、spectral sequence、同じ合成map |
| D 任意locally closed条件 | [D1](dimension-realization.md) | 指定cycleと全頂点source、全係数体の次元、空・単元・零の場合 |
| D 任意有限値関数・原始表示 | [D2](dimension-realization.md) | Boolean atomと有限直和、rank1の原始演算、`M_P≅B` |
| D Pseudo-coherent複体の不存在 | [D3](dimension-realization.md) | generic点から原点への次元下降、derived fiberの上半連続性との矛盾 |
| E 同じ実操作・原始relation | [E1–E2](specified-obstruction.md) | 補正readout、局所表示核、辺の連結性、整数表示群 |
| E 実Ob・Čech・SAGA | [E3–E4](specified-obstruction.md) | 全context、実交差、`av↦a e_(Law,0)`、符号map、指定residual |
| E 零性反映・定数診断族 | [E5–E6](specified-obstruction.md) | spanning treeの自由H¹、実section、既存反映仮定との比較 |
| F 有限空間・実修復 | [F1–F3](atlas-refinement.md) | 八点空間の二被覆、逆像bundle、追加一致Law、全解と作用 |
| F Atlas C0–C6 | [F4](atlas-refinement.md) | 同じsource・reading・支持の全field、表示群、既存H¹同型との可換性 |
| F 評価fiber・有限反復 | [F5–F6](atlas-refinement.md) | regular評価とlocally closed条件、候補の逆map、groupoid、恒等・合成 |
| F 情報を落とすreading | [F7](atlas-refinement.md) | 実線形mapの自由係数、像と全fiber、評価の因子分解条件 |
| G 実現・共有規則・全補完 | [G1](relative-decision.md) | 全実際のmap、保存式、指定R点での像、decode |
| G 三量化・全係数条件 | [G2–G3](relative-decision.md) | 整合実現の証人、空の場合、部分関手、自己同型 |
| G Reading・全解・局所選択 | [G4](relative-decision.md) | pullback、非空fiber、相互回復、係数・改名・合成、descent |
| G 十分追加観測 | [G5](relative-decision.md) | 派生Bool評価、像への全射reading、異判定対とkernel |
| G 全包含極小集合の算法 | [G6](relative-decision.md) | 原始有限評価、全分離集合、停止性、必要十分性、完全性 |
| G 幾何的四分類 | [G7](relative-decision.md) | 構成可能像、全fiber、有効計算域、指定R点との比較 |
| W1–W6 | [指定例](witnesses.md) | 指定した全入力・式・写像による計算 |

## 先行する紙上証明と原始仕様

| Source | 使用箇所 |
| --- | --- |
| [G-139 原始意味](../G-139-aat-law-generated-relative-geometry/primitive-semantics.md)、[多項式実現](../G-139-aat-law-generated-relative-geometry/polynomial-realizations.md) | B1・D2・G1。独立な実現と全R点、原始評価、有限表示、実AAT context |
| [G-140 全Homの幾何](../G-140-aat-semantic-change-category/geometry-and-descent.md)、[条件付き変更](../G-140-aat-semantic-change-category/conditional-changes.md) | F5・F7・G1–G4。実際の状態map、翻訳、評価、全解、三量化 |
| [G-140 台帳P5](../G-140-aat-semantic-change-category/ledger-specialization.md) | W6。同じfinish式と `μδ(1−ρ)` |
| [G-141 graph修復G1–G5](../G-141-aat-coherent-repair-effectivity/graph-repair.md) | E–F・W3。実bundle・Ob・State・全context・SAGA・全修復 |
| [G-141 descentと選択C7–C9](../G-141-aat-coherent-repair-effectivity/descent-and-selection.md) | G4・W5。全候補descentと平方根のtorsor |
| [G-141 有限計算D1–D7](../G-141-aat-coherent-repair-effectivity/effective-solving.md) | F7・G1・G6–G7。有限還元、原始式、実像、全fiber、係数域 |
| [G-141 指定例H8・H11](../G-141-aat-coherent-repair-effectivity/witnesses.md) | W3・W6。同じoffset、固定頂点、finish残差 |
| [n1020 §4・14・16](../../../docs/note/n1020_shigure_polynomial_specializations.md) | 原始scalar・実修復と診断・共有候補の設計。証明は本ディレクトリの各節 |

## 既存Lean宣言への具体的な接続

| 宣言・source | 紙上で同定するdataとmap |
| --- | --- |
| [Reading.factors_iff_kernel、FiniteLawFamily.adequate_iff_kernel](../../lean/ResearchLean/AG/CanonicalResolution/Reading.lean) | A1の原始Law descent、G5の候補を含むsource `X : Type u` と像への全射。判定値域を `ULift.{u} Bool` として同じuniverseに揃える |
| [comparisonFactor、Law descent](../../lean/ResearchLean/AG/ResolutionInvariance/ComparisonData.lean) | A2・B6・F4の同じ粗細readingと値の一致 |
| [CellCoordinate、lawGeneratedD0/D1/Complex](../../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean) | A1–A2のlabel、右−左、三辺の交代和、Q係数。B3の直接同定は `chartSupport_nonempty` を持つ場合で、空chart支持は零直和成分を許す本文の拡張 |
| [TargetSupportedNerveMorphism](../../lean/ResearchLean/AG/ResolutionInvariance/SupportedNerveMorphism.lean)、[generatedPullback0/1/2](../../lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean) | A2・F4のchart map・部分edge/face map、退化時零、同じcochain map |
| [lawValueBlockComplex](../../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockDecomposition.lean)、[lawGeneratedH1BlockEquiv](../../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockCohomology.lean) | B3・C1で同じ `(Law,value)` のcoordinateを読む分解 |
| [GeneratorPresentation](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/GeneratorPresentation.lean)、[PresentationGroup](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/PresentationGroup.lean) | E2の実制限から得たrelation、局所核・連結性、整数の生成元商 |
| [coefficientComparison](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/CoefficientComparison.lean) | E3の `[e]↦e_(Law,0)`、整数から有理係数へのmap |
| [ContextOpenSupport](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/AATLocallyConstantObstruction.lean)、[FaceEmptyAATCechCover](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/FaceEmptyCechNormalization.lean) | E3の全contextの実openと実product交差、非空連結section |
| [CochainComparison](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/CochainComparison.lean)、[actualCechDiagnosticH1Map](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/ActualCechH1Comparison.lean) | E3–E4・F3の生成元像、両微分、H¹の同じ商map |
| [ActualCechAffineLocalData、h1_map_actual_class_eq_diagnostic_class](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedAffineObstruction.lean) | E4の `R=Z` と `Z→Q` 比較で、符号map後の `transition=−b`、`localState=λ`、`r=dλ−b` を同定。一般環 `R` の `Λ=R` 版は本文で構成 |
| [CommonLabelChartSupport](../../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedClassReflection.lean) | E5で三辺cycleに対し偽と証明。零性反映は別途spanning treeから得る |
| [ConditionC0–C6](../../lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean)、[generatedComparisonH1Map_bijective](../../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonBijectivity.lean) | F4で各fieldを原始支持から放電し、F3の実比較へ同定 |
| [SAGA LiftFiberData](../../../Formal/AG/SemanticRepair/Saga/EquationLift.lean)、[PartIVBridge](../../../Formal/AG/SemanticRepair/Saga/PartIVBridge.lean) | G-141 G3–G5を介してE3–E5・F3へ。実residual、全tupleの空交差、`Tδ=dT` |

## 仮定の使用箇所

| 仮定・生成する条件 | 使用箇所と内容 |
| --- | --- |
| 有限source・Law・cell | A2の有限basis、Bの有限rootと直和、Cの有限二重複体 |
| Adequateな全射reading | A1の一意な値の降下。F4では値0と明示した全射から証明 |
| 任意scheme、regularな `f` | B2のmonic商とB4の任意基底変更。Noetherian性・flat性は不要 |
| `Λ→Λ'` がflat | A3の通常のH¹等とのtensor交換。B4の項別tensor同型には不要 |
| Faithfully flatまたは個別の単射証明 | A3・E5の指定類の零性反映。E5の `Z→Q` は自由H¹から証明 |
| 有限表示 `B=Spec A` | D2の有限原始presentation。D1のcycle構成は同じregular値を使う |
| 非空な有限連結単純graph、少なくとも一辺 | Eの非空chart・実pair・空face・relationの連結性・tree座標 |
| 実制約と追加一致Law | F2・F5の全解の逆map。H¹同型だけから修復fiber同値を出さない |
| Regular評価とlocally closed条件 | F5の全R fiber比較。一般readingではF7の実際の因子分解を検査 |
| 整合実現の非空証人 | G2–G3の確定判定。空fiberの全称条件は別に分類 |
| 同じ原始保存式と全補完の比較 | G1・G4の判定保存・反映。Law値のadequacyのみを用いない |
| 有効な有限還元・係数評価 | G6の全保存・観測等値の停止する判定。有限集合性だけを算法の根拠としない |
| Noetherian基礎環、有限型、構成可能な成立集合 | G7の幾何的四分類。像の有効計算にはG-141 Dの係数域も用いる |
| 全 `R` 代数への量化 | G3の自然な部分関手。固定体・全幾何点との相違はW6 |

## 標準数学への依存

[有限射のétale順像](https://stacks.math.columbia.edu/tag/03QN)のstalk表示、任意base change、有限全射descentをB3–B6で使う。重複rootを持つ場合も、幾何fiberの点集合と同じ制限mapで適用する。

[導来fiberのBetti数の上半連続性](https://stacks.math.columbia.edu/tag/0BDI)をD3でpseudo-coherent複体へ適用する。W2の下降を示す特殊化が矛盾を与える。

[Chevalleyの定理](https://stacks.math.columbia.edu/tag/054K)をG7の二つの構成可能像に使う。指定R点での像・regular選択・冪零方向の判定への追加結論は含めない。

有限複体の長完全列、bounded double complexのspectral sequence、有限graphのtree積分は、それぞれC3、C4、E5で使うmapと完全性を本文中に構成した。
