# G-136：既存宣言・接続補題・新規構成

参照版はmain `ed16acc02229fdfe3846303de341d600878f03dc`。
RI=`AAT.AG.ResolutionInvariance`、ADC=`AAT.AG.AtlasDefectComposition`、
FRS=`AAT.AG.FaceRelationSubdivision`、ACF=`AAT.AG.AtlasCoefficientFiber` と略す。
以下は同版のsourceで宣言・型・主要前提を照合した対応である。
今後作る補題には既存宣言と同じstatusを与えない。

G-135は[全固定目標の完了記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290#issuecomment-6078348119)
でResearchの `target-theorem-proved` が確定している。Formalは `unported (Research-proved)`。
初期reportのcandidate表現やtracking IssueのOPEN状態から、Researchの未完了を推定しない。
この設計は既存GOAL・reportの実行状態を更新しない。

## 1. 原始入力、部分複体、実比較

| 既存ファイル・宣言 | 実際の型・仮定と再利用内容 | G-136の接続・新規義務 |
| --- | --- | --- |
| [ComparisonData.lean](../../lean/ResearchLean/AG/ResolutionInvariance/ComparisonData.lean)：`RI.comparisonFactor`、`comparisonFactor_unique`、`lawDescend_comparisonFactor` | 全射readingとCoarserThanから因子を生成。Lawの可換式は粗細adequacyを使う | 指定族で生成因子=fst、Law値の粗細逆像を同定 |
| [ComparisonComposition.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ComparisonComposition.lean)：`ADC.adequate_of_coarser` | 粗adequacyとreading順序から細adequacy | 新しいadequacy fieldを加えず、D・Eで適用 |
| [LawGeneratedComplex.lean](../../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean)：`RI.TargetSupportedNerve`、`edgeSupport`、`faceSupport`、`CellCoordinate.ext`、`lawGeneratedComplex` | 有限セル、非空chart台、三つの面端点等式。辺台は両端交差、面台は三辺交差。座標はcell/law/value | 元の微分と座標等号を再利用。真のセル交差は新構成。幅族のK1は原表から放電 |
| [ASubnerveReduction.lean](../../lean/ResearchLean/AG/UniformInvariance/ASubnerveReduction.lean)：`TargetSupportedNerve.targetSubsetComplex`、`labelValueFiber_eq_preimage`、`lawValueBlockTargetSubsetComplexEquiv` | セルの台が任意Aと交わる定数ℚ複体。Law値blockと三次数の同値 | N_Xには直接使える。I=N_A∩N_BをN_(A∩B)へ置換するAPIではない |
| [IncidenceComparison.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/IncidenceComparison.lean)：`FRS.IncidenceSupportedComparison`、`edgeSupport_compatible`、`faceSupport_compatible`、`ofHereditary` | chart全域、辺・面Option、端点・mapped面・退化面の符号付き零和、chart台包含。線形完全性は入力にない | Iの両所属証拠を輸送し、原始部分比較を制限する |
| [SubsetComparison.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/SubsetComparison.lean)：`IncidenceSupportedComparison.aSubnerveComparisonHom`、`labelFiberComparison_naturality0/1/2` | 任意Aに対しcoarse C_A→fine C_(π⁻¹A)のHom。混在退化を含む | A/B/Uのuを独立に生成済みのこのHomへ同定。新u_Iは原始Mから作る |
| [SubsetRestriction.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/SubsetRestriction.lean)：`ADC.SubsetRestriction.SelectedLE`、`hom`、`hom_comp` | 二つのtarget部分集合の選択セル包含から逆向きHomを作る。集合包含より弱いSelectedLEを許す | 同じセル評価とincidence証明を再利用。任意の交差セル述語を受ける型ではないためI用の包含は新規 |
| [SupportRestriction.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/SupportRestriction.lean)、[SubsetRestriction.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/SubsetRestriction.lean)：`selectedInclude`、`selectedRestrict`、`subsetRestrictHom` | A⊆Bの同じ元セル包含・双対制限。微分との可換性は原始支持chainから証明済み | U→A/Bに直接適用。I用の制限と、旧ADC評価式との一致は接続補題 |

## 2. 標準錐・完全列・実欠損

| 既存ファイル・宣言 | 実際の入力・結論 | G-136の仕事 |
| --- | --- | --- |
| [ZeroExtension.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ZeroExtension.lean)：`zeroExtension`、`zeroExtensionMap`、`oldH1Equiv`、`oldH1Equiv_natural` | 任意のℚ三項複体・Hom。ℤ次数標準複体と既存H¹商の自然な同型 | 新I複体・SESをこの表現へ接続 |
| [ConeCoordinates.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ConeCoordinates.lean)：`coneCoordinateEquiv_d`、`coneCoordinateEquiv_map` | 任意の標準cochain射、可換正方形。target/source座標の微分は(dy+ux,−dx) | 粗細SESの両座標から錐SESを新たに証明 |
| [ConeExactSequence.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ConeExactSequence.lean)：`cone_short_exact`、`cone_homology_dimension` | 全整数mのcoker Hᵐ→HᵐCone→ker Hᵐ⁺¹。次元式はその次数の有限次元性を使う | Bの錐LESの各項と結び、隣接次数の寄与を残す |
| [ShortExactFive.lean](../../lean/ResearchLean/AG/AtlasDefectComposition/ShortExactFive.lean)：`inclusion`、`projection`、`exact`、`dimension` | 五項の実線形射と三つのFunction.Exactを入力。literal range quotientとkernelを出力 | AからMVの完全性を放電してQ/P短列に適用 |
| [DefectSemantics.lean](../../lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean)：`RI.blockDefect`、`blockDefect_eq_zero_iff_bijective` | 一般有限次元ℚ線形射の核次元・余核次元と同型の同値 | 新snakeの結果を既存u_X.h1Mapへ戻す |
| [LawComparisonFiberDiagnostics.lean](../../lean/ResearchLean/AG/FaceRelationSubdivision/LawComparisonFiberDiagnostics.lean)：`lawFiberH1Comparison_square`、`lawH1Defect_subset_sum`、`lawSubsetConeHomologyEquiv` | 有限Source、有限Law族、粗細adequacy、混在M。実Law比較と全ラベルの部分集合比較 | 各λの領域和の結果を有限和へ接続。G-133の旧hereditary専用Law定理へ混在Mを変換しない |

G-133の `compositionTriangle` は**比較射の合成**を扱う。
G-136の **領域の和**のSESは別の構成であり、同triangleの呼出しだけでは得られない。
前表の標準錐、台包含、五項列の商核APIを再利用する。

## 3. G-135の固定X分解

| 既存ファイル・宣言 | 実際の型・前提 | G-136での接続 |
| --- | --- | --- |
| [DefectMaps.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/DefectMaps.lean)：`ACF.directH1`、`directH1_old`、`directH1_factor`、`directKernelUnitEquiv` | 任意の原始混在MとA。直接射は元aSubnerveComparisonHomの標準H¹。η/εの合成等式と元を保つ核同型 | 通常X=A/B/UでT_Xを同じ直接射へ接続。Dの核比較に使う |
| [DefectShortExact.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/DefectShortExact.lean)：`coefficientCokernelInclusion`、`totalCokernelFiberProjection`、`coefficientCokernel_shortExact` | 同じM・Aからcoker H¹η→coker T→ker τの実射・完全性を構成。追加のfiber消滅前提なし | Uの同じ余核をMV側SESの中間項に同定。両分解の端項は別対象 |
| [DefectDiagnostics.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/DefectDiagnostics.lean)：`directH1_defect`、`coefficient_zeroDefect_iff` | Jの一致と、J=0 iff H¹η全単射かつτ単射。一般混在Mに適用 | Cの局所J零仮定を固定X分解の条件として読める。Eのpath/cycleで実発火 |
| [SupportCones.lean](../../lean/ResearchLean/AG/AtlasCoefficientFiber/SupportCones.lean)：`supportStandardDirect`、`supportTotalCone` | A⊆Bによる同じ実uの正方形と標準錐射。原Mを固定 | U→A/Bの錐射を接続。Iは別のセル選択なのでこのAPIの直接適用先にしない |

G-135の固定A分解は再利用できるが、そこに領域和MVや任意kの反例族が含まれるとは扱わない。
逆に、これらの新規部分のために受理済みの順像・R・τの構成を未証明へ戻さない。

## 4. 標準数学と新規構成

mathlibはrepoの `lake-manifest.json` が固定する版を使う。
`Mathlib/Algebra/Homology/HomologySequence.lean` の
`CategoryTheory.ShortComplex.ShortExact.δ`、同namespaceの `δ_eq`・`homology_exact₁/₂/₃`、
`Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean` の `CategoryTheory.ShortComplex.SnakeInput`
を標準接続先とする。SES・snake入力の可換性と完全性は原始セルから作る。

| 新規対象 | 必須の数学的仕事 |
| --- | --- |
| 真のセル交差 | 両所属証拠の別点を許す閉じた選択、元incidenceと部分比較の制限 |
| 領域SES・錐LES | 次数別延長と貼り合わせ、原始粗細可換性、標準δの代表式・符号 |
| Q/P比較・一次欠損 | literal kernel/cokernel、snake、局所H¹同型の下でcoker p≅Z |
| 実診断への接続 | 同じTと旧H¹商、Lawの有限和、固定X fiber分解との対応 |
| 全有限幅反例 | 原始K1表、全真部分集合のforest、閉路period、Law値クラス幅、k=0 |

## 5. G-130との差

[RelativeCoverComplex.lean](../../lean/ResearchLean/AG/RelativeRepairComposition/RelativeCoverComplex.lean)
の `RelativeCover.C0/C1/C2/C3` は、G-129の `LocalCoefficients` と閉じた領域U・固定部分Pから、
Pで零となる元セル添字の可換群族を作る。辺には実輸送係数があり、面・3-cellまで扱う。
[CoverPlanConnecting.lean](../../lean/ResearchLean/AG/RelativeRepairComposition/CoverPlanConnecting.lean)
の `connecting_plan_class` は局所修復planのH²障害と連結射を結ぶ。

G-136では有限支持nerveの定数ℚの0・1・2次複体、二つのreading間のH¹比較、
その核・余核が対象である。固定部分P、可動辺S、実修復groupoidを入力に持たない。
したがってG-130のrelative修復の定理を、同じ名の貼り合わせ定理として直接適用しない。
セル評価・延長・連結射の証明構成は参考にできるが、次数と係数と実比較の同定は別に必要である。
