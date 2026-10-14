# G-137：既存宣言、接続義務、新規部分

調査したsource版はmain `f3ae0eab35186e2259fa030eb23fb4657180a868`。
Leanはv4.28.0、mathlibは `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。
既存sourceの宣言・型・主な前提を読んだ対応であり、この文書作成ではLeanを再実行していない。
active化時の参照版固定は[カードの読み取り手順](../../../.codex/skills/target-theorem-loop/references/target-goal-contract.md)に従う。

RI=`AAT.AG.ResolutionInvariance`、ADC=`AAT.AG.AtlasDefectComposition`、
FRS=`AAT.AG.FaceRelationSubdivision`、ACF=`AAT.AG.AtlasCoefficientFiber`、
AGW=`AAT.AG.AtlasGluingWidth` と略す。

## 1. 先行GOALの扱い

G-135は[Research完了記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6078348119)
で全固定目標を完了している。受理PRは[#5318](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5318)、
mergeは `ed16acc02229fdfe3846303de341d600878f03dc`。
調査版ではカード・GOAL索引にactive、reportに最終監査前の表現が残るが、
これをResearchの未完了の根拠にはしない。

G-136は[Research完了とmetadata同期の記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321#issuecomment-6117232196)
に対応し、カード・索引もcompletedである。受理PRは
[#5336](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5336)、
mergeは `4681fd5927aee176d9e2b91019a9f7448e0fe4be`。
G-135・G-136のResearch完了とFormalへの未移植を区別する。
この設計では先行カード・reportの状態表示を変更しない。

G-133・G-134の受理経路は、それぞれの
[report](../../reports/G-133-aat-atlas-defect-composition.md)・
[report](../../reports/G-134-aat-face-relation-subdivision.md)と
tracking Issue [#5261](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5261)・
[#5272](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272)から追える。

## 2. 原始構造と実比較

| 既存ファイル・宣言 | 型と利用できる内容 | G-137で必要な接続 |
| --- | --- | --- |
| [ComparisonData.lean](../../lean/ResearchLean/AG/ResolutionInvariance/ComparisonData.lean)：`RI.comparisonFactor`、`comparisonFactor_unique` | 全射readingとCoarserThanから唯一のtarget因子を生成 | T/Pへの商写像・二段の商因子と同定。chart分割の順序は別に証明 |
| [LawGeneratedComplex.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean)：`RI.TargetSupportedNerve`、`edgeSupport`、`lawGeneratedComplex` | 有限セル・非空chart台・面端点式からK1台と実Law複体を生成 | T0と全商の表を構成。粗辺台は再計算したK1交差 |
| [IncidenceComparison.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/IncidenceComparison.lean)：`FRS.IncidenceSupportedComparison`、`ofHereditary`、`comp` | chart全域、edge/faceはOption、端点と符号付き面条件。比較同型は入力にない | 原始商の部分セル像を生成し旧型にも接続。面条件は空型から放電 |
| [SubsetComparison.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/SubsetComparison.lean)：`IncidenceSupportedComparison.aSubnerveComparisonHom` | 任意Aの粗→細cochain射、細側はtarget因子の逆像 | u_Rと二段のuをこの同じHomとして扱う |
| [HereditarySpecialization.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/HereditarySpecialization.lean)：`FRS.ofHereditary_aSubnerveComparisonHom_h1Map` | 新旧の実subset H¹写像が等しい | G-107・G-133の旧比較用定理をG-137へ適用 |
| [UniformityReduction.lean](../../lean/ResearchLean/AG/UniformInvariance/UniformityReduction.lean)：`TargetSupportedNerveMorphism.uniformInvariance_iff_allNonemptyASubnerveH1Bijective` | 有限Source、旧hereditary比較。全adequate Lawと全非空Aの実H¹同型を同値にする | 生成した旧比較へ適用し、空Aの零複体を加えてT0のSafeへ接続 |
| [LawComparisonFiberDiagnostics.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/LawComparisonFiberDiagnostics.lean)：`FRS.lawFiberH1Comparison_square`、`lawFiberH1KernelFamilyEquiv`、`lawFiberH1CokernelFamilyEquiv`、`lawH1Defect_subset_sum` | 混在比較の実Law射を全ラベルのsubset射へ共役し、核・余核・数値和を得る | 同じu_RのLaw側証拠と指定例の重複ラベルを同定 |

## 3. 合成、欠損、係数とfiber

| 既存ファイル・宣言 | 型と利用できる内容 | G-137で必要な接続 |
| --- | --- | --- |
| [ComparisonComposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ComparisonComposition.lean)：`ADC.adequate_of_coarser`、`comparisonFactor_comp` | 粗adequacyから細adequacy、三readingの因子合成 | q_Rのadequacyと二段の商因子に適用 |
| [SubsetComposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/SubsetComposition.lean)：`ADC.aSubnerveComparisonHom_h1Map_comp` | 旧二比較のH¹合成。最粗側Aの逆像を中間側で使う | 原始商の直接比較との一致を先に証明して適用 |
| [GeneratedDefect.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/GeneratedDefect.lean)：`ADC.aSubnerve_zeroDefect_twoOfThree` | 同じA・逆像での実三比較について零欠損の2-out-of-3 | 安全R≤R′間の比較に適用。全中間target部分集合へ量化を拡大しない |
| [DefectSequence.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/DefectSequence.lean)：`ADC.DefectSequence.sixTerm_exact`、`cancellation` | 一般線形二射の実核・余核・相殺 | 合成を説明する既存資産。分割joinの安全性をこの定理から直接結論しない |
| [DefectMaps.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/DefectMaps.lean)：`ACF.directH1`、`directH1_old`、`directH1_factor`、`directKernelUnitEquiv` | 原始M・Aの独立比較と旧H¹商の同定、T=H¹ε∘H¹η、同じ元の核同型 | T_Rを同じdirectH1へ移送。任意の同次元線形同型で代替しない |
| [DefectShortExact.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/DefectShortExact.lean)：`ACF.coefficientCokernel_shortExact` | 同じM・Aからcoker(H¹η)→coker(T)→ker(τ)の実短完全列を生成 | 不安全Rの余核と、係数/fiberによる説明を接続 |
| [DefectDiagnostics.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/DefectDiagnostics.lean)：`ACF.coefficient_zeroDefect_iff` | J=0 iff H¹η全単射かつτ単射 | Aの保存条件への接続。これ自体はG-137の新定理ではない |
| [PurePreservation.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/PurePreservation.lean)：`ACF.pure_zeroDefect_iff` | MixedFaceが空の下で係数同型と全ΦのH¹消滅による保存判定 | 空面から条件を放電して使える。係数条件を省かない |
| [FinitePreservationDecision.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/FinitePreservationDecision.lean)：`ACF.primitiveDiagnostic_eq_blockDefect`、`allAPreservationDecision_eq_true_iff` | 原始d0/d1・実比較行列からJを計算し、全Aの零性を有限判定 | 新規の全分割対列挙と接続。表から非零代表を返す構成は追加義務 |

G-133のW1は、二閉路を持つ中間nerveからの非零相殺を示す。
後段のchart写像は全射でないため、G-137の商規則の例としてそのまま使わない。
一般の合成定理と、固定した商poset上の閉性を区別するための既存比較である。

## 4. 自然性とG-136の既証明部分

| 既存ファイル・宣言 | 実際に示していること | G-137の責務 |
| --- | --- | --- |
| [CellRename.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/CellRename.lean)：`FRS.CellRename.supported`、`presentation` | 固定readingのセル名変更から台を保つ表示同型を生成 | 原始同型のセル部分に再利用。Source/target再添字づけと分割への群作用を新たに接続 |
| [SupportConnecting.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/SupportConnecting.lean)：`ACF.supportConnecting_tau` | 固定MでA⊆Bに沿うR・τの自然性 | 自己同型によるMの変更とは別の図式。支持制限の接続に再利用 |
| [SupportCones.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/SupportCones.lean)：`ACF.supportStandardDirect`、`supportTotalCone` | 同じ直接比較の支持制限の可換性と錐射 | 部分集合の逆像・同じ比較を追う資産。選択関数の自然性そのものではない |
| [PrimitiveGluing.lean](../../lean/ResearchLean/AG/AtlasGluingWidth/PrimitiveGluing.lean)：`AGW.PrimitiveGluing.defect_zero_iff`、`defect_dimension` | 局所J_A=J_B=0の下で、同じ合併比較のJが実qの核・余核とZで決まり、J=0 iff q全単射かつZ=0 | 証明済み。分割の共通粗化へ名前を変えて再利用できる定理ではない |
| [LawDefect.lean](../../lean/ResearchLean/AG/AtlasGluingWidth/LawDefect.lean)：`AGW.LawDefect.defect_zero_iff` | 各labelの局所零性と領域による値fiber被覆から同じ全Law比較の保存iff | 同じラベルと比較で既に接続済み。G-137の新規完了条件に再掲しない |
| [WidthObservation.lean](../../lean/ResearchLean/AG/AtlasGluingWidth/WidthObservation.lean)：`AGW.Width.plus_defect`、`proper_defect`、`full_defect` | 全幅族でproper領域の零欠損とfull領域のhiddenを原始入力から証明 | W3のn=2と新しく生成した商の同型を証明して、判定の回帰に使う |
| [WidthHidden.lean](../../lean/ResearchLean/AG/AtlasGluingWidth/WidthHidden.lean)：`AGW.Width.gluing_hidden_nonzero`、`coefficient_hidden_same` | 標準連結射の同じ非零hidden類とG-135側の対応 | W3の非零代表の出所。同じuの同定を経て利用 |

G-134の面あり/なしpaired例、G-135のW3の非零τとW5のκによる適合は、
面を持つ原始入力で既に区別されている。T0が面を持たないことは、それらの結果を
未証明へ戻す理由にならない。面付き商を追加する場合は別途商規則を固定する必要がある。

## 5. 真に新しい数学的仕事

1. 独立なtarget・chart分割対からの全商と、固定fine入力上での因子化の分類。
2. 実診断の安全性で切り出した有限poset、全極大元、最大元と全共通上界の判定。
3. 原始同型の全作用、固定極大元と同型に自然な選択の同値。
4. 同じ規則の下での $`P_G,P_J,P_N` の成立または原始反例による決着。

標準的な同値関係の束、有限半順序、群作用、線形核・商にはmathlibの概念を用いる。
ArchSigの宣言からrealizationや写像を作る処理は、その処理系の責務である。
G-137が生成・証明するのは、上で明示した数学的な原始有限入力の商と比較である。
