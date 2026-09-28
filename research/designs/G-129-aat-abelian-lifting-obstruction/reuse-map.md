# G-129：既存実装・接続・新規構成の対応

[実装設計](README.md)で使う一次実装を列挙する。
Research pathは `research/lean/ResearchLean/AG/`、mathlib pathは `Mathlib/` からの相対とする。
mathlibは[Research packageのmanifest](../../lean/lake-manifest.json)が指定する版を使う。
参照版の固定はGOALのactive化時にtracking Issueへ記録する。

「再利用」は既存の入力・結論をそのまま使うもの、「接続」は同じ対象・射・値との一致を
新しく証明するもの、「新規」はG-129の数学的な構成・証明を指す。

## 1. 有限表示と任意の関手上の輸送

以下の任意の関手上の宣言は `AAT.AG.TransportCoherence.Arbitrary` 内にある。

| 既存path・宣言 | 既存の入力と結論 | G-129での扱い |
| --- | --- | --- |
| [TransportCoherence/FinitePresentation.lean](../../lean/ResearchLean/AG/TransportCoherence/FinitePresentation.lean)：`PresentedPath`、`WhiskeredFace`、`RewriteStep`、`RewritePasting`、`FiniteTransportPresentation` | 有限な頂点・辺・面・3-cell。面の向き、前後の道、貼り合わせの型を保持する | 再利用。加法的評価と共通の `SquarePresentation` は新規 |
| [TransportCoherence/ArbitraryFinitePresentation.lean](../../lean/ResearchLean/AG/TransportCoherence/ArbitraryFinitePresentation.lean)：`FiberAut`、`LiftData`、`TransportData` | 任意の関手のfiber自己同型、強い辺の持ち上げ、底での道の一致と指定比較 | 再利用。塔の射影準同型とその実際の核、下段データの生成は新規 |
| 同ファイル：`reselectedEdgeLift`、`reselectedPathLift`、`reselectedPathLift_isStronglyCocartesian` | 終点自己同型による辺・道の再選択と強い性質の保存 | 再利用。GOALの核補正を既存の `EdgeReselection` に含める |
| 同ファイル：`canonicalFaceComparator`、`canonicalFaceComparator_fac`、`rawFaceDefect` | 標準比較を一意性から構成し、defectを `u * m⁻¹` として定義する | 再利用。射影後の比較一致、defectの核所属・加法化は新規 |
| [TransportCoherence/ArbitraryObstruction.lean](../../lean/ResearchLean/AG/TransportCoherence/ArbitraryObstruction.lean)：`whiskerFiberAutHom`、`whiskerFiberAut_fac` | 道に沿うfiber自己同型の群準同型と特徴づけ | 再利用。射影との可換式、核への制限、全単射性からの同型、面条件との同値は新規 |
| 同ファイル：`pathReselectionTransition`、`pathReselectionTransition_fac` | 現在の辺の選択と補正後の選択を結ぶ道の標準比較 | 接続。核補正では同じ比較が `T_w(h)` の包含と一致することを証明する |
| 同ファイル：`canonicalFaceComparator_transition`、`rawFaceDefect_transition` | 非可換な順序と指定比較の共役を保った変換則 | 再利用して加法化する。核の可換性だけでなく指定比較の中心化条件を使う |
| 同ファイル：`orientedFaceComparator`、`pastingComparator`、`pastingRawDefect` | 接尾辞に沿う輸送、逆向きの逆元、順序付きの貼り合わせ | 接続。核への制限後に符号付き `pastingSum` と一致させる |
| 同ファイル：`canonicalPastingComparator_unique`、`AuthoredSyzygy`、`rawDefect_cocycle_of_authoredSyzygy` | 同じ始点・終点の貼り合わせの標準比較は一致し、指定比較の一致からraw defectの一致を導く | 再利用。得られるのは非可換な等式であり、`d2 δ = 0` への接続は新規 |

既存の `whiskerFiberAutHom` の型は群準同型である。
核上の同型性はGOALの条件2を通じて得る。辺や道の全射性・単射性を追加で仮定しない。

## 2. 第4章の実際の射影と解

以下は `AAT.AG.CrossStageCoherence` 内の宣言である。

| 既存path・宣言 | 既存の入力と結論 | G-129での扱い |
| --- | --- | --- |
| [UpperObstruction.lean](../../lean/ResearchLean/AG/CrossStageCoherence/UpperObstruction.lean)：`TwoLayerLiftData`、`TwoLayerTransportData`、`TwoLayerLiftData.pathLift_compositeStrong` | 幾何・coreの各辺の強い持ち上げと、その合成の強い性質 | 再利用。一般の `Arbitrary.TransportData` への変換と道の評価の一致は新規 |
| [ObstructionGroups.lean](../../lean/ResearchLean/AG/CrossStageCoherence/ObstructionGroups.lean)：`compositeFiberPushforward`、`innerFiberAutSubgroup_eq_ker`、`innerFiberInclusion` | 幾何自己同型の実際の射影と、その核としての `InnerFiberAut` | 接続。一般側の射影との可換図式を示し、核の群同型を構成する |
| 同ファイル：`CompositeFiberAut.ext_of_strong_fac`、`canonicalCompositeFiberComparator` | 同じ強い持ち上げを通る比較の一意性と標準比較 | 再利用。一般側と幾何側の比較を射の因子分解で一致させる |
| [PastingObstruction.lean](../../lean/ResearchLean/AG/CrossStageCoherence/PastingObstruction.lean)：`upperWhiskerCompositeFiberAut`、`upperWhiskerCompositeFiberAut_fac` | 元の幾何の道に沿う上段自己同型の輸送 | 接続。一般側の核輸送との一致を同じ射の特徴づけから示す |
| 同ファイル：`upperAuthoredPastingComparator`、`UpperSyzygyCompatible`、`upperRawDefect_cocycle_of_syzygy` | 上段の指定比較の貼り合わせと、指定3-cell上のraw defectの等式 | 接続。一般の貼り合わせと段ごとに一致させる |
| [SectionDecomposition.lean](../../lean/ResearchLean/AG/CrossStageCoherence/SectionDecomposition.lean)：`EdgeSectionFamily`、`CoreAlignmentAt`、`sectionCellComparator_pushforward_eq_authored` | 同じcoreの辺の持ち上げ、射の等式としての整列、標準比較の射影一致 | 再利用。(A2)をこの整列条件へ対応させる |
| 同ファイル：`sectionInnerObstruction`、`sectionInnerObstruction_inclusion` | 核所属を証明して得る実際の内側defectと、その包含の値 | 接続。一般側の `innerDefect` と元の自己同型として一致させる |
| [RelativeObstruction.lean](../../lean/ResearchLean/AG/CrossStageCoherence/RelativeObstruction.lean)：`relativeUpperReselection`、`relativeEdgeSection_alignment`、`relativeInnerDefectCochain` | 核による全辺の再選択、core整列の保存、補正後の実際のdefect | 再利用・接続。`δ+d1 h` がこの同じ値になることを示す |
| 同ファイル：`SectionRelativeCoherentizable`、`innerVanishesAt_iff_sectionRelativeCoherentizable` | 核補正の軌道が恒等defectに達することと、実際の整合する再選択の存在が同値 | 接続。G-129では軌道の存在条件を同じ `H2` の零性へ移す |
| 同ファイル：`sectionReplacementGauge`、`sectionReplacementGauge_mul_first`、`sectionRelativeCoherentizable_replacement_iff` | 同じcoreの二つの持ち上げの差、元の辺の復元、基準の置換による存在判定の不変性 | 再利用・接続。一般側の差と一致させ、障害類とtorsorの基準選択対応へ使う |

`ArbitraryFinitePresentation.lean` の `packageFiberAutMulEquiv`・`packageTransportData` は
`packageProjection` に対するcore段の接続である。上段の幾何packageへの接続には、
そのまま転用せず `CompositeFiberAut` と一般の `FiberAut` の群同型を構成する。

## 3. G-127と群拡大

| 既存path・宣言 | 既存の入力と結論 | G-129での扱い |
| --- | --- | --- |
| [ProtocolHolonomy/LiftableVisible.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/LiftableVisible.lean)：`projectionToLiftable`、`projectionToLiftable_surjective`、`projectionToLiftable_ker` | 実際の可視射影を持ち上げ可能な像へ制限し、同じ核と全射性を得る | 再利用。この射影を一対象圏の関手へ移す |
| 同ファイル：`verticalLiftEquivLiftableKernel`、`verticalLiftInclusion`、`liftable_shortExact` | 元の垂直なfiber全単射と実際の核の群同型、同じ包含を持つ短完全列 | 接続。係数の元を元の各頂点のfiber写像へ戻す |
| [ProtocolHolonomy/TwoVertexTotalGroup.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/TwoVertexTotalGroup.lean)：`twoVertexC4` | `Multiplicative (ZMod 4)` と指定例の実際の変更群の群同型 | 再利用。単に同型型を使うだけでなく、次行の射影等式と組み合わせる |
| [ProtocolHolonomy/TwoVertexQuotient.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/TwoVertexQuotient.lean)：`twoVertexC2`、`twoVertexActualProjection`、`twoVertex_projection_is_mod_two` | 同じ可視群の `C2` 表示と、実際の射影がmod 2になる等式 | 再利用。二つの持ち上げの面defectと障害類は新規計算 |
| [ProtocolHolonomy/TwoVertexNoSection.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/TwoVertexNoSection.lean)：`twoVertex_no_group_section` | 同じ可視射影に群準同型のsectionが存在しない | 接続。新しく計算した障害からBを使ってこの結論を再取得し、同じ射影であることを照合する |
| [ProtocolHolonomy/LiftFiberTorsor.lean](../../lean/ResearchLean/AG/ProtocolHolonomy/LiftFiberTorsor.lean)：`liftEquivLiftableFiber`、`liftableFiber_action_free`、`liftableFiber_action_transitive` | 一つの可視元の上の持ち上げに、核が右から自由・推移的に作用する | 各辺のfiberを扱う参考。G-129の全辺同時の左補正と `Z1`・`H1` の作用は新規 |

G-127の右作用は `MulOpposite` を介して表されている。
G-129では終点に核を左から掛けるため、既存の作用instanceを同じものとして流用しない。

## 4. 幾何packageの具体例

| 既存path・宣言 | 既存の入力と結論 | G-129での扱い |
| --- | --- | --- |
| [CrossStageCoherence/FiniteWitnesses.lean](../../lean/ResearchLean/AG/CrossStageCoherence/FiniteWitnesses.lean)：`FiniteCrossStageWitness.package`、`symmetricRaw`、`symmetricRaw_swap` | 対角的な `Int × Int` 係数のraw系を持ち、係数交換を保つ実際の幾何package | 具体入力の第一候補として再利用する |
| 同ファイル：`site_nonempty`、`has_actual_cover`、`raw_relation_nonzero` | 非空のsite、実際の被覆、非零のraw関係式 | 同じpackageを使う場合、そのまま完了条件4へ渡す |
| 同ファイル：`coefficientSwapTotal_square`、`innerSwap`、`innerSwap_ne_one` | 係数交換から作る非恒等の核自己同型 | 指定比較の構成に再利用。核全体の可換性は新規の証明義務 |
| [GeometryTransport/Categories.lean](../../lean/ResearchLean/AG/GeometryTransport/Categories.lean)：`GeomReadHom.ext`、`GeometryTotalHom.ext` | 係数写像とsupport・axis・observable比較の全成分による射の外延性 | 核の可換性を、同じcore上の全計算成分の等式から証明する |
| [CrossStageCoherence/RootEffectivityWitness.lean](../../lean/ResearchLean/AG/CrossStageCoherence/RootEffectivityWitness.lean)：`coefficientEquiv`、`coefficient_image_cases`、`coefficient_square_fixes_distinguished` | 別の具体packageに対し、係数自己同型の平方が `(1,0)` を固定する | 証明方法を再利用する。`Int × Int` の環自己同型についての補題へ切り出し、採用packageの実際の写像に適用する接続は新規 |
| [CrossStageCoherence/IdentityEdgeLiftSpecialization.lean](../../lean/ResearchLean/AG/CrossStageCoherence/IdentityEdgeLiftSpecialization.lean)：`liftData`、`data`、`upper_canonical_eq_one` | 任意のpackageと有限表示から恒等辺の入力を作り、実際の標準比較が恒等と証明する | 再利用。共通の3-cell付き表示と非恒等の指定比較を渡す |

`FiniteCrossStageWitness.witnessData` は、core整合と辺ごとの持ち上げを同時に与えられない
現象を扱う入力である。G-129の具体例ではpackageと核自己同型を使い、辺・core・指定比較を
[具体例設計](witnesses.md#4-第4章の幾何package)に従って構成する。

## 5. mathlibと新規構成

| mathlib path・宣言 | 役割 | G-129で新しく証明する部分 |
| --- | --- | --- |
| `Algebra/Group/Equiv/Defs.lean`：`MulEquiv.ofBijective` | 構成した核準同型の全単射性を群同型へ移す | その写像が元の強い輸送から生成されたこと |
| `CategoryTheory/PathCategory/Basic.lean`：`Paths.lift`、`CategoryTheory/Quotient.lean`：`Quotient.lift` | 辺の輸送から道の関手を作り、面関係へ降下する | `PresentedPath` との変換、面の輸送一致、元の生成辺の評価 |
| `Algebra/Homology/HomologicalComplex.lean`：`CochainComplex.of` | 次数ごとの加法群・微分からnativeな複体を作る | `d0`・`d1`・`d2` と二つの合成零 |
| `Algebra/Homology/ShortComplex/Ab.lean`：`abToCycles`、`abHomologyIso` | 三項のhomologyと、核の中の像による商の一致 | 同じ `d0,d1,d2` を代入し、障害の代表と零性を対応させる |
| `GroupTheory/QuotientGroup/Defs.lean`：`QuotientAddGroup.mk'`、`eq_zero_iff` | 可換群の商と零類の所属条件 | 原始入力から得たdefectの商類、補正方程式との双方向対応 |
| `Algebra/AddTorsor/Defs.lean`：`AddTorsor` | 自由・推移的な加法作用と差のnativeな構造 | 実際の解に対する作用・差・二つの消去法則 |
| `GroupTheory/GroupAction/Defs.lean`：`AddAction.orbitRel` | 頂点作用による同値関係 | 軌道関係と差が `d0` の像に入る条件の一致、`H1` の作用の降下 |
| `CategoryTheory/SingleObj.lean`：`MonoidHom.toFunctor`、`SingleObj.comp_as_mul` | 群拡大を一対象圏の塔へ移す | fiber自己同型・射影・核・輸送と元の群の一致 |
| `GroupTheory/Perm/Sign.lean`：`Equiv.Perm.sign`、`sign_swap`、`sign_surjective` | `S3` の符号射影 | `C3` と実際の核の同型、共役の反転、三つの解と頂点作用 |

既存の群コホモロジーの低次数APIを、有限表示 $`K`$ のコホモロジーと同一視して使わない。
今回の微分・障害・解は、同じ `PresentedPath` と `RewritePasting` から構成する。
