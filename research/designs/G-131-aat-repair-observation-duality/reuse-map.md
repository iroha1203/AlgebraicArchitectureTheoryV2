# G-131：完成済みG-130の再利用対応

[固定GOAL A–E](../../goals/G-131-aat-repair-observation-duality.md)と
[設計](README.md)を、G-130の使用宣言に対応させる。
以下の「直接適用」は記載した入力・仮定を満たした後の既存APIの適用、
「接続補題」は同じ入力・座標・写像への同定、「新規証明」はG-131固有の結論を表す。

G-130の参照版は最終受理head `549b7e3ccab1c9686a108530e1b0a4b4f38eee86`
（[最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5179#issuecomment-5966982329)、
[完了記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5132#issuecomment-5966995993)）。
同版の[report](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/549b7e3ccab1c9686a108530e1b0a4b4f38eee86/research/reports/G-130-aat-relative-repair-composition.md)
のC13・C15・C24に以下の宣言と前提の生成・使用を照合する。
G-130 A–F・W1–W5の成果は `unported (Research-proved)` としてResearch側から使う。
G-128等の既存資産と共通基準の固定版は[#5133の初期記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5133#issuecomment-5915620714)に従う。

以下のファイルは `research/lean/ResearchLean/AG/RelativeRepairComposition/` 以下、
宣言は `AAT.AG.RelativeRepairComposition.` を補って読む。
`NativeAffine`以下は全アフィン自己同型の射影塔を対象にし、一般の圏の塔には
`SupportedNativeEquation`・`OriginalRanges`のAPIを使う。

## 1. 実入力から同じ右辺・修復へ（A）

一般の塔では、G-130と同じ `OriginalTowerPresentation` の元辺・core・参照lift・比較、
強い辺、可換な全核、全単射な核輸送、比較の中央化、元3-cell整合を保持する。
閉領域 $`P`$ とその面での基準実操作の整合を用いる。
線形化には同一体上の全核moduleと核輸送の線形性、有限座標には全核の基底を用いる。
これらは一般族の原始条件であり、Eの具体族では元操作から放電する。

| 使用ファイル・宣言 | 入力・仮定と直接適用の入出力 | G-131の接続補題・新規証明 |
| --- | --- | --- |
| `SupportedNativeEquation.lean`：`SupportedNativeEquation.repairEquiv`、`repair_value`、`repair_inverse_value`、`inverse_choice` | 元塔 $`T`$、閉 $`P`$、候補・許可辺、P上の実面整合から、独立な `SupportedRepair` と `SupportedEquation.Objects` を往復。固定辺 $`P\cup(\mathsf E\setminus S)`$、全辺補正と元choiceを保つ | 各 $`X`$ の塔・固定規則を同じ入力族へ対応。成功を仮定して可否を定義せず、独立修復の非空性を両逆から移す |
| `NativeAffineRepairs.lean`：`NativeAffine.repairEquivalence`、`repairEquivalence_inverse_value` | 同じ元全アフィン操作L/R、comparison translation、参照面の線形成分一致、固定辺から、native `SupportedRepair` と独立な全アフィン `NativeAffine.Repair` を往復。全操作の値と固定条件を保つ | 全アフィン族では上の支持方程式の逆写像に合成し、元の実関数への復元に使う |
| `AffinePrimitiveFamily.lean`：`NativeAffine.familyOriginal`、`familyReference`、`familyComparisons`、`familyTower`、`familyDefectLinear`、`family_defect_affine` | 一つのmodule $`A`$ 上の元全アフィン操作 $`L,R`$、比較translation $`c`$、線形なtranslationパラメータ $`\theta_L,\theta_R,\eta`$、参照両経路の線形成分一致から全 $`v`$ の実操作と $`\delta_0+\Delta v`$ を生成。$`\Delta=\eta+d^1_{\rm vector}\theta_R`$ | この入力型で表せる族に直接適用。一般族ではその表示または同じ実経路評価との接続を証明する。$`\nu(X_v)=v`$ と全 $`X`$ の原始問い合わせ評価一致はAの入力条件、Eでは新規の構成・証明義務 |
| `AffineFamilyLaws.lean`：`NativeAffine.family_three_law`、`family_fixed_face` | baselineの元3-route整合と $`d^2_{\rm vector}\eta=0`$ から全vの3-cell整合。baselineのP面整合と $`\Delta v|_{P^2}=0`$ から全vのP面整合 | 具体族の同じパラメータでこれらの条件を放電する。Pの操作値は入力間で変わり得るが、その入力の修復中の実操作を保持する |
| `AffineFamilyRelativeDefect.lean`：`NativeAffine.familyRelativeLinear`、`family_native_relative_defect`、`AffineFamilyDifferentials.lean`：`family_relative_d1`、`AffineFamilyEquationCoordinates.lean`：`family_equation_iff`、`familyEquationObjects` | 同じ $`K,L,R,c,\theta_L,\theta_R,\eta,P`$、上記線形整合・P条件から、全vのnative係数・相対微分をbaseへ同定し、実defectを $`\delta_0+\Delta v`$ と同じ相対余鎖上で同定。禁止候補も保つ | G-131の $`b_0=-\delta_0,B=-\Delta`$ を同じ面基底へ移す。G-130の正defectの線形項 $`\Delta`$ とG-131の負defectの $`B`$ の符号を区別する |
| `AffineFamilyNativeEquation.lean`：`NativeAffine.familyNativeEquationEquivalence`、`family_native_equation_edge_value`、`family_native_equation_label_value` | 上記同じ入力で全v・全許可範囲の実修復groupoidをbaseの支持方程式へ往復。全辺補正と全頂点ラベルを保持 | Aの元実操作への復元に使う。数値出力の基底値と、逆写像の全辺値が一致することを接続する |

全アフィン族の既存構成は共通module $`A`$ を使う。一般族の異なる頂点係数や別の
圏の塔への適用は、同じ係数・輸送・微分・実操作の対応を構成してから行う。
この適用対象の差は、固定GOAL Aの一般族をアフィン族だけへ変更する理由にはならない。

## 2. 全範囲の方程式、商と不能証拠（A・D）

| 使用ファイル・宣言 | 入力・仮定と直接適用の入出力 | G-131の接続補題・新規証明 |
| --- | --- | --- |
| `OriginalCandidateColumns.lean`：`OriginalColumns.alwaysSpace`、`D`、`column`、`differential_named_sum` | 線形な全核係数、閉P、P外の元候補名、有限な元辺族から、常時許容空間 $`X_0`$ と全候補核 $`A_e`$、元相対 $`d^1`$ の分解を構成 | $`D_S(x,y)=D_0x+\sum_{e\in S}C_ey_e`$ を $`X_0\times\prod_{e\in S}A_e`$ 上で構成。全核の基底から数値 $`h`$ の元辺値へ戻し、禁止候補を零にする |
| `OriginalRangeEquations.lean`：`OriginalRanges.objects_nonempty_iff_equation`、`restore`、`objects_nonempty_iff_range`、`OriginalRangeClassification.lean`：`repair_nonempty_iff_range` | 元塔の条件に加え全核module、線形輸送、候補のP外所属、辺のFintype・等値判定・候補所属判定、P面整合から、全Sの独立実修復・同じ分解方程式・商 $`\mathsf O=C_P^2/\operatorname{im}D_0`$ の候補像所属を対応 | 上の $`D_S`$ と $`-\delta(X)=b_0+B\nu(X)`$ を代入し、Aの三つの同値を接続する |
| `CokernelAllColumns.lean`：`CokernelNamed.secondQuotient`、`secondQuotient_value`（`CokernelNamedRanges.lean`：`column`、`quotient_sum`） | 有限な列族、線形 $`D_0,C_e`$ から $`\mathsf O/\mathsf R_{\rm all}\cong C_P^2/(\operatorname{im}D_0+\operatorname{im}\sum C_e)`$、同じ面代表元の一致 | **接続補題が必要**：列族を $`e\in S`$ に制限して適用し、`all`の像を元名による $`\mathsf R_S`$、分母を $`\operatorname{im}D_S`$ と同定する。逆向きの同型で $`q_Sr`$ を $`q_0r\bmod\mathsf R_S`$ へ送る。全候補版だけで任意Sを済ませない |
| `AffineFamilyDualClassification.lean`：`NativeAffine.family_obstruction_affine`、`family_repair_nonempty_iff_range`、`family_failed_repair_dual` | §1の同じ族、P外候補、有限元辺・所属判定から、全v/Sで $`o(v)=q_0(-\delta_0)-q_0(\Delta v)`$、実修復可否と候補像、失敗時の $`\phi(o(v))\ne0`$・許可列で零を得る | 一般塔は `OriginalRangeClassification.failed_repair_dual` を使用。$`\phi`$ の $`\mathsf R_S`$ 上の零から残存商上の $`\ell`$ を構成し、上記同型で同じ不能値を対応させる |
| `NamedDualRanges.lean`：`NamedDual.support`、`annihilates_iff`、`failure_witness` | $`\phi`$ と全元候補列 $`B_e=q_0C_e`$ から、$`E_\phi=\{e:\phi B_e\ne0\}`$ と像和での消失を対応 | Dの追加方向が同じ評価を変える条件をこの元名の支持へ移す。取得条件は $`(\ell q_SB)|_N`$ の原始評価span所属として新しく証明する |

ここで商は同じ全面空間のcokernelである。Bの $`\operatorname{im}(q_SB)`$ は
この入力族から実現される方向として構成する。
G-130の全候補・誘導 $`d^2`$ の核を用いるH²比較を、任意Sの残存商全体へ置き換えない。

## 3. 有限構成と観測取得（C・D）

| 使用ファイル・宣言 | 入力・仮定と直接適用の入出力 | G-131の接続補題・新規証明 |
| --- | --- | --- |
| `OriginalPublicRanges.lean`：`OriginalPublicRanges.public_nonempty_iff_range`、`publicKernelEquiv`、`restore_edge_value` | §2の同じ元塔・線形係数、有限体・全核基底・有限閉被覆・全セル/index列挙・所属判定から、生成局所公開関係の可否と同じ候補像判定を対応。成功公開値と全private核から全実修復を往復 | Aの「局所記号的関係を合成した判定」の接続に使う。Cの既知情報 $`\eta`$ は何を受領したかで定め、復元器の存在だけで未知の公開値を既知としない |
| `OriginalFiniteCorrection.lean`：`OriginalFiniteCorrection.find`、`restoreFound`、`find_isSome_iff`、`OriginalFiniteRepair.lean`：`OriginalFiniteRepair.restoreFound`、`success_decision_iff` | 同じ線形係数・全核基底、有限体、完全な体/辺列挙、面/辺の有限性・等値判定、P/候補/Sの所属判定、**取得済みの**相対右辺から、全元辺数値補正を探索。返却値自身から全方程式・禁止候補零を証明し実操作へ復元 | 数値十分集合の応答と既知情報から $`r=b_0+Bv`$ を数値として復元し、base係数で $`\delta=-r`$ を渡す。実入力の未取得 $`\nu(X)`$ や $`\delta(X)`$ を手続きの引数に追加しない。判定側は $`q_Sr`$ の取得で足り、右辺全体の取得を強制しない |
| `OriginalFiniteDual.lean`：`OriginalFiniteDual.find`、`find_isSome_iff`、`quotientDual`、`quotientDual_value`、`quotientDual_spec`、`OriginalFiniteRepair.lean`：`failure_decision_iff` | 同じ完全な体/面列挙・全核基底・元常時列/候補列・取得済み右辺を使い、有限行探索で失敗を検出し、返却行を元商の双対へ降ろす | 数値右辺取得後の証拠生成に直接適用。判定のみ十分な観測から証拠値を取得する場合は、Dの引き戻し評価のspan条件を別に証明する |
| `SymbolicInterfaceUpdates.lean`：`SymbolicInterface.rhs_difference`、`section_update`、`reconstruction_update` | 固定 $`D,F,\sigma,B,r`$ から $`B(w-v)`$ と復元の $`\sigma B(w-v)`$ を計算。線形sectionの正確性はG-130の生成器で得る | Dの更新通知でどの値が既知かを $`L,s,N`$ へ反映することと、最小追加問い合わせ数は新規証明 |
| `AffineFamilySymbolicCover.lean`：`NativeAffine.familyNativeSymbolicEquivalence`、`familySymbolicObjects`、`family_symbolic_inverse_edge_value`、`AffineFamilySymbolicRanges.lean`：`family_symbolic_range_square` | $`A=\operatorname{Fin}d\to k`$ の同じ族、有限体・閉被覆・完全列挙・§1のP条件から、一度生成した局所消去・section・全自由度を各v/Sで実修復へ戻し、範囲包含と交換 | この座標型の族に直接適用。一般の全核基底での族には座標接続を用いる。異なる入力値間では右辺を更新し、各fiberの可否を判定する |

`find`の探索結果から `restoreFound` の条件を得る順で使う。
`computedRepair`の可解性引数や `computedDual` の不能性引数を、未知入力の答えを
受け取る原始問い合わせとしては使わない。数値座標の探索・正確性と、非計算的な
圏の実射への数学的復元を区別する。

G-128への加法群作用、観測表・修復述語・原始問い合わせ手続きの相互シミュレーションは
[設計 §2.1・4](README.md#4-線形観測と点作用)の新規接続である。
G-130の復元やG-128のBool判定から、数値出力の下限は得られない。
Cでは成功基準点の同じ応答列を実入力 $`X_{v_*+n}`$ で再現し、判定には
$`q_SB n=0`$、同じ数値補正には $`Bn=0`$ が必要なことを証明する。
全不能fiberの零回、十分集合なしの無限大、最小集合を用いた達成手続きも新規証明である。

## 4. 同じ指定網・全実現と分割（E）

W1は `negative=true`（$`a=-I`$）を使い、候補は元名 $`b,c`$、補正は
$`(u,h,z,v)`$ の全四値を保持する。

| 使用ファイル・宣言 | 直接適用の入出力 | G-131の接続補題・新規証明 |
| --- | --- | --- |
| `W1AffineInput.lean`：`W1AffineInput.reference`、`linear_faces`、`originalTower`、`W1ActualRepairs.lean`：`W1ActualRepairs.actualParametersEquiv`、`nativeParametersEquiv`、`actualRepair`、`parameters_operations` | 全 $`x,y\in\mathbb F_3`$ の元六操作、全核・輸送・固定rx/ryと独立全実修復を構成。全Sで四数値と元操作を往復 | $`X_{(x,y)}`$ を同じ入力で構成し、`reference`のrx/ryと `NativeAffineKernel.lean` の `NativeAffine.translation_apply` から原始評価 $`r_x(0)=x,r_y(0)=y`$、$`\nu(X_v)=v`$ を証明 |
| `W1RelativeCoefficients.lean`：`W1RelativeCoefficients.signedDefect_coordinates`、`relative_d1_first`、`relative_d1_second_negative` | 同じ全面座標で $`-\delta=(x,y)`$、元相対微分の二式 $`u+z=x,u-z+v=y`$ | Aの $`b_0=0,B=I`$ と同じ $`D_S`$ に接続。数値出力の右辺一致から二座標が必要となる下限をCへ適用 |
| `W1PermissionClassification.lean`：`W1PermissionClassification.negative_empty_exists_iff`、`negativeActualEquiv`、`W1DualMinimalRanges.lean`：`W1DualMinimalRanges.actual_range_iff`、`range_contains_iff`、`nonempty_range_top`、`dualCoordinate_obstruction` | 全x/yで空範囲は $`x=y`$ iff、元候補名の任意非空範囲は常時可解、同じ双対値はy−x。全private hと許可されたzを保持 | Eの候補非空の全ケース、既知なし/xのみ/両値の表をCの核条件から導く。修復数の既存計算を問い合わせ回数と同一視しない |
| `W1GeneratedRelations.lean`：`W1GeneratedRelations.left_relation`、`right_relation` | 独立に生成した全局所関係を同じ二式へ対応 | **接続補題が必要**：同じ公開座標を使い、関係そのものからx/yを回収する。各関係が非空で、その定数値を一意に決めることを示し、「両具体的関係受領」の情報fiberを両値既知へ同定する |
| `W1SymbolicLocalStructure.lean`：`W1SymbolicLocalStructure.section_same`、`W1SymbolicPublicMatrices.lean`：`W1SymbolicPublicMatrices.public_matrix_same`、`W1SymbolicGeneratedRows.lean`：`W1SymbolicGeneratedRows.generated_rows_same`、`W1SymbolicActualUpdates.lean`：`W1SymbolicActualUpdates.symbolic_signed_rhs`、`zero_to_nonzero_empty` | 同じ実入力から生成したsection・行列・公開行の値非依存と全x/yの右辺、指定更新の空範囲成否を保持 | y更新後の通知内容をCの既知情報へ写し、数値出力の追加一回/零回を証明 |
| `W1SubdivisionRepairs.lean`：`W1SubdivisionRepairs.repairEquiv`、`W1SubdivisionCoordinates.lean`：`W1SubdivisionCoordinates.collapse_coordinate`、`all_pairs` | 同じ実因子・自由fresh頂点・全Sで新修復 $`\cong`$ 旧修復 $`\times\mathbb F_3`$。任意 $`r`$ の分割補正 $`(r,h+r)`$ と縮約 $`\beta-\alpha=h`$ | rx/ryと原始評価を保つ同じ問い合わせ手続きの往復を構成。任意既知rで旧数値出力から全分割補正を戻し、逆は数値縮約で回数を保つ。対象集合の全単射だけで最適回数を済ませない |

Eの $`\mathbb F_2`$ の $`K^+`$ は、G-130 W5の三辺二面網へ新候補loop cを
追加した四辺の表示である。W5の `W5ActualSolvability.global_iff` は候補なしの網の
定理なので、K⁺の候補許可時の可解性へ直接適用しない。
[n1017 §5.3](../../../docs/note/n1017_aat_relative_boundary_repair_and_observation.md#53-同一表示の候補解禁原始観測修復出力)
の元四辺・二面・固定a/b・候補c・全 $`(b_1,b_2)`$ を新しく構成し、
`NativeAffine`の塔・全核・実修復対応と§1–3を適用する。
同じ実合成から $`u=b_1,u+z=b_2`$、問い合わせの評価、数値出力の二回最適値と
参照式 $`e:=a,c:=b\circ a^{-1}`$ の零回生成・両面の実等号を新しく証明する。

## 5. 依存と検証対象

構成順は、原始族・全実現・原始評価 → 同じ実微分と負defect → $`D_S,q_S`$ と
元名の商対応 → 既知情報fiberと観測十分性 → 原始問い合わせ手続きの下限・達成 →
観測取得済み数値と実操作への復元とする。
未知値の取得前に使うのは構造行列・候補名・基底・記号的右辺であり、
障害の値や既存の成功修復を既知情報の入力へ移さない。

G-131で検証するのは接続補題と新規証明である。先行宣言の使用時には固定版の
signature・必要な定義・同じ適用引数・proof-useを照合し、reportへ記録する。
GOALの固定target・前提構成台帳・完了条件をこの設計表で増減しない。
