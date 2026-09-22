# 主張と証拠の対応

論文の各主張・成立条件と、根拠となる数学本文・Lean sourceを対応づける。
一次資料の版は各章に示し、本文用の有限例と既存の形式化の範囲を各項目で区別する。
書誌・引用箇所・引用する版は[文献確認記録](references.csv)による。
共通基準は[論文作成ガイドライン](../../../docs/paper/guideline.md)に従う。

## 固定版の構成5.37と追加Lean宣言

[固定版 `719f81f47d410701fd82c2bc88613cc140c59377` の構成5.37](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/719f81f47d410701fd82c2bc88613cc140c59377/outreach/paper/rising-sea/ja/08-base-change.md#L1018)の完全幾何の二経路は、任意の`BCSemanticInput`、南西のcoreと完全幾何、対応する基点の等式、exactなCartesian平方から生成する。`endpoint_eq`は本文のcoreが南西の基点上にあるという入力を表す。

| 固定本文の結論 | Lean宣言 |
| --- | --- |
| 左引き戻し・上輸送と下輸送・右引き戻しの二経路、および直接比較と三角式 | [SemanticDerivedEndpointBridge](../../../research/lean/ResearchLean/AG/FullGeometryNormalization/SemanticDerivedEndpointBridge.lean) の `semanticDerivedDirectGeometryAt`、`semanticDerivedViaBaseGeometryAt`、`semanticDerivedBarAlphaIsoAt` と [SemanticDerivedBarAlphaTriangle](../../../research/lean/ResearchLean/AG/FullGeometryNormalization/SemanticDerivedBarAlphaTriangle.lean) の `semanticDerivedBarAlphaIsoAt_triangle` |
| G-118で生成された両端との同型、生成mateと直接mateの一致 | [SemanticDerivedGeneratedEndpointBridge](../../../research/lean/ResearchLean/AG/FullGeometryNormalization/SemanticDerivedGeneratedEndpointBridge.lean) の `semanticDerivedBToGeneratedBaseNorthwestIsoAt`、`semanticDerivedGeneratedPulledToTNorthwestIsoAt`、`semanticDerivedGeneratedMateOnLiteralEndpoints_triangle`、`semanticDerivedGeneratedMateOnLiteralEndpoints_eq_literal` |
| 比較射のunit・端点比較・G-118のmate・端点比較・counitの五因子式 | 同moduleの `semanticDerivedBarAlphaIsoAt_generatedFiveFactor_hom` |
| 診断入力のface `z` にあるcore `P_z` への特殊化 | [SemanticDerivedDiagnosticEndpointBridge](../../../research/lean/ResearchLean/AG/FullGeometryNormalization/SemanticDerivedDiagnosticEndpointBridge.lean) の `semanticDiagnosticSourceCoreAt`、`semanticDiagnosticDirectGeometryAt`、`semanticDiagnosticViaBaseGeometryAt`、`semanticDiagnosticBarAlphaIsoAt`、`semanticDiagnosticBarAlphaIsoAt_triangle`、`semanticDiagnosticBarAlphaIsoAt_generatedFiveFactor_hom` |

## 固定版の補題6.15と追加Lean宣言

[固定版 `719f81f47d410701fd82c2bc88613cc140c59377` の補題6.15](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/719f81f47d410701fd82c2bc88613cc140c59377/outreach/paper/rising-sea/ja/09-idempotent-normalization.md#L368)が述べる任意のexactなpointed底射は、`ExtInstHom`で表す。`CanonicalObjectNormalizationAdmissible`は、正規化を定める側のcoreに対する本文の`Ad`条件であり、輸送先または引き戻し先の条件はこの入力から導く。

| 固定本文の結論 | Lean宣言 |
| --- | --- |
| coreの輸送・引き戻しによる`Ad`保存 | [SemanticExactCoreNormalizationNaturality](../../../research/lean/ResearchLean/AG/FullGeometryNormalization/SemanticExactCoreNormalizationNaturality.lean) の `canonicalCoreNormalizationAdmissible_semanticTransport`、`canonicalCoreNormalizationAdmissible_semanticPull` |
| coreの生成liftとの交換(6.17)と関手による保存(6.16) | 同moduleの `semanticCoreFiberLift_normalization_natural`、`semanticCoreInverseLift_normalization_natural`、`semanticCoreFiberTransportFunctor_map_normalization`、`semanticCoreInverseReindexFunctor_map_normalization`。後者の引き戻し関手は既存のsemantic-global関手と `semanticCoreInverseReindexToGlobalIso` で比較する |
| 完全幾何の輸送による`Ad`保存、liftとの交換、関手による保存 | [SemanticExactNormalizationPush](../../../research/lean/ResearchLean/AG/FullGeometryNormalization/SemanticExactNormalizationPush.lean) の `canonicalGeometryNormalizationAdmissible_semanticExactTransport`、`semanticGeomFiberLift_normalization_natural`、`semanticGeomFiberTransportFunctor_map_normalization` |
| 完全幾何の引き戻しと`Ad`保存、liftとの交換、関手による保存 | [SemanticExactGeometryPull](../../../research/lean/ResearchLean/AG/FullGeometryNormalization/SemanticExactGeometryPull.lean) の `semanticGeometryPullFunctor` と [SemanticExactNormalizationNaturality](../../../research/lean/ResearchLean/AG/FullGeometryNormalization/SemanticExactNormalizationNaturality.lean) の `canonicalGeometryNormalizationAdmissible_semanticExactPull`、`semanticGeometryPullLift_normalization_natural`、`semanticGeometryPullFunctor_map_normalization` |

以下のC型表は、そこに明記した固定版の既存宣言と本文修正との対応を記す。上の追加宣言によって、その固定版の入力や当時の判定を遡って変更するものではない。

## C型の本文修正と既存宣言の対応

対象は Issue #4847 の F18・F19・F20・F23・F24・F31・F37・F40 と F25。
参照する Lean source の固定版は `ceaf361ec0533c954ba03089879ec8c5d8a4fff9`。
以下は本文修正の対応であり、A/B型の検証完了を表すものではない。
今回の個別の特例を、C型の結論を紙上証明で保持する根拠にはしない。

| 対象 | 本文へ反映する対象・仮定・結論 | 既存宣言 |
| --- | --- | --- |
| F18・4.13–4.16 | 抽出の底に沿う標準core・幾何輸送の関手、合成・単位比較、射影との整合 | [CorePseudofunctor][c4-core-pseudo] の `coreFiberTransportFunctor`、`coreFiberCompositor_assoc`、`coreFiberCompositor_left_unit`、`coreFiberCompositor_right_unit`。[Pseudofunctor][c4-geom-pseudo] の `geomFiberCompositor_assoc`、`geomFiberCompositor_left_unit`、`geomFiberCompositor_right_unit`。[TowerCompatibility][c4-tower] の `towerTransportComparison_compositor`、`towerTransportComparison_unitor` |
| F18・4.17–4.23 | 有限比較図式のcore、抽出の底に関して強い辺、底の二道の等号、指定自己同型。再選択の作用と消滅 | [FinitePresentation][c4-presentation] の `AdmissibleLiftData`、`AdmissibleTransportData`、`pathReselectionTransition_mul`、`reselectionStep_one`、`reselectionStep_mul`。[VanishingCoherence][c4-vanishing] の `transportObstructionVanishes_iff_coherentizable` |
| F18・4.24–4.27 | 同じcoreデータで後続道への自己同型輸送、貼り合わせ、指定syzygyに沿う等式、閉じた不一致 | `whiskerFiberAut`、`whiskerFiberAut_fac`。[PastingObstruction][c4-pasting] の `canonicalPastingComparator_fac`、`rawDefect_cocycle_of_syzygy`、`closedPastingRawObstruction_eq_conjugate`、`closedPastingRawObstruction_eq_one_iff` |
| F19・4.31–4.34 | 幾何の辺はp-strong、射影した辺はq-strong。同じedge sectionでの射影・分解・同時消滅 | [UpperObstruction](../../../research/lean/ResearchLean/AG/CrossStageCoherence/UpperObstruction.lean) の `TwoLayerLiftData`、`pushforward_upperCanonicalTwoCellComparator`、`pushforward_upperRawTwoCellDefect`。[SectionDecomposition][c4-section] の `totalObstruction_kernel_decomposition`、[GlobalVanishing][c4-global] の `jointVanishes_iff_alignedSectionVanishes` |
| F20・1.34後、4.36–4.39 | 共通view・基準viewと有限基準fiber。役割別写像、get/put平方、固定viewの対応、可逆変更の両逆。非単射例はUnit×Boolの定値自己射 | [相対lens][c4-lens] の `LensAATRelativeForwardMorphism`、`typedObjectMap`、`get_square`、`put_square`、`identityVisibleEquiv`、`ofLensInvertibleChange`、`toLensInvertibleChange`。[FixedFLensConnection](../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFLensConnection.lean) の `normalForm`、`hiddenPermutation_unique`。[LensSemanticFiniteDetermination](../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensSemanticFiniteDetermination.lean) の `constantFalseHom`、`constantFalseHom_res_not_injective` |
| F20・4.41の適用 | 固定viewのlens・固定schemaのプロトコルの比較群対応 | [充満忠実な比較の輸送][c4-fully-faithful] の `generatedArrowComparisonMulEquivOfFullyFaithful`、`lensAATIndependentPackageComparisonMulEquiv`、`protocolAATIndependentPackageComparisonMulEquiv` |
| F23・5.7 | 一般のexact射について、存在定理から選んだ標準cartesian liftの合成・単位の整合 | [ExactBottomGlobalLiftCoherence](../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLiftCoherence.lean) の `exact_bottom_semantic_global_reindex_functor`、`exact_bottom_semantic_global_compositor`、`exact_bottom_semantic_global_unitor`、`exact_bottom_semantic_global_pentagon`、`exact_bottom_semantic_global_triangle` |
| F24・5.10–5.12 | Atomの等号判定、有限codeのcospan・compatibleな選択source・診断図式から生成した平方のmate、可逆性、選択変更との比較 | [BCSchema](../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/BCSchema.lean) の `BCPresentation`。[CoreBeckChevalleyMate](../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMate.lean) の `coreBeckChevalleyMate`。[PackageProjectionBeckChevalleyExactness](../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactness.lean) の `coreBeckChevalleyMate_isIso`。[選択変更](../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateCleavageIndependence.lean) の `coreBeckChevalleyCleavageMate_selectedComparison` |
| F25・5.14–5.15 | 正規化とAtom置換による輸送後のcodeそのものの等号 | [Schema](../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/Schema.lean) の `CartPresentationBetween.extraction_eq`。[CoverageClassification][c5-coverage] の `finiteCofiniteExtractionCode_eq_of_mem_range`、`endpointFiniteTargetCofinitePresentation` |
| F31・5.37–5.40 | 有限codeで実現した平方、同じ有限図式のcore・lift・終点・底の二道・指定比較、面、係数環、完全幾何から生成する比較 | [BCRelativeSchema](../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchema.lean) の `AuthoredSupportContext`、`AuthoredBCDatumSquare`。[標準比較][c5-derived-mate] の `authoredExactBarAlphaIsoAt`、[三角式][c5-alpha-triangle] の `authoredExactBarAlphaIsoAt_triangle`、[射影][c5-alpha-projection] の `authoredExactBarAlphaIsoAt_projection`、[分解][c5-beta-factor] の `authoredExactBarDAt`、`authoredExactBarBetaAt_factor` |
| F31・6.15 | Coreと前向き幾何の標準liftの一般性を保持。完全幾何の引き戻し・fiber関手上の保存は有限codeで実現された射 | [ExactNormalizationNaturality][c6-exact-naturality] の `transportAlongHom_normalization_natural`、`inverseCorePackageHom_normalization_natural`、`geomTransportAlongHom_normalization_natural`、`exactGeometryPullLift_normalization_natural`、`geomFiberTransportFunctor_map_normalization`、`exactGeometryPullFunctor_map_normalization` |
| F31・6.16–6.17 | 5.37の同じ入力からの冪等射・可逆性分類・Karoubi同型・core射影 | [分類][c6-beta-classification] の `authoredExactBarProjectorsAt_eq_endpoint_normalizations`、`authoredExactBarBetaAt_isIso_iff_not_selected`、[射影][c6-beta-projection] の `authoredExactBarBetaAt_projection` |
| F31・7.21–7.22、8.21 | 同じ生成比較のsection・fiber・再構成。三軸の具体例は削除 | [ExactBarAlphaCanonicalComparisonSection](../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaCanonicalComparisonSection.lean) の `authoredExactCanonicalComparisonSectionHom`、[ExactBarBetaBottomQualifiedClassification](../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaBottomQualifiedClassification.lean) の `authoredExactBottomComparisonSectionHom`、[原始再構成](../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean) のG122入力と全Homの再構成 |
| F37・7.3–7.5 | 完全幾何の比較と底固定の端点変更群、射圏の可逆変更、射影核とfiber、可逆比較の共役 | [QualifiedComparisonGroup](../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/QualifiedComparisonGroup.lean) の `qualifiedComparisonReversibleMulEquiv`。[QualifiedComparisonStabilizer](../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonStabilizer.lean) の `qualifiedComparisonSourceProjectionKernelMulEquiv`、`qualifiedComparisonTargetProjectionKernelMulEquiv`、`qualifiedComparisonIsoGraphMulEquiv` |
| F40・7.25–7.26、7.30 | 積の再添字式、許容可視部分群上の分裂短完全列、各fiberと置換族の対応・個数、指定点を固定する版 | [FixedFSplitExactSequenceAndTorsor](../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFSplitExactSequenceAndTorsor.lean) の `isGroupShortExact`、`canonicalSection_rightInverse`、`componentGroupEquivProjectionFiber`。[指定点版](../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFPointedSplitExactSequenceAndTorsor.lean)、[個数](../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFFiberCardinality.lean)、[具体例](../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFFiniteExamples.lean) |

F37の系7.5で全端点群を用いる場合は、任意の圏の同型に対する
[G122GeneratedComparisonGroup](../../../research/lean/ResearchLean/AG/RealizationReconstruction/G122GeneratedComparisonGroup.lean)
の `generatedArrowComparisonSourceEquiv` に対応させる。
F20・F40の依存先である命題7.27は同じ積lensの自己変更へ限定し、
[FixedFLensConnection](../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFLensConnection.lean)
の `equivPreservingFollowingChanges`、`normalForm`、`equivHiddenPermutations`、
`natCard_productLensChanges`、`preservesSection_iff` に対応させる。
任意lensへの群同型の移送、直積群への同定は残さない。


### 式番号の対応

命題・定理・例の番号は維持した。式は次のように詰め、本文中の参照も同時に更新した。

| 修正前の式番号 | 修正後 |
| --- | --- |
| 4.31、4.47 | 削除 |
| 4.32–4.46 | 4.31–4.45 |
| 4.48–4.52 | 4.46–4.50 |
| 5.40–5.41 | 削除 |
| 5.42–5.48 | 5.40–5.46 |
| 7.43 | 削除 |
| 7.44–7.47 | 7.43–7.46 |

この表には、式の内容も修正した箇所を含む。旧(4.45)–(4.46)に対応する新(4.44)–(4.45)は、
余積による表示を四役割の写像と二つの可換平方へ置き換えた。
旧(7.45)に対応する新(7.44)は、同じ積lensの正規形に内容を限定した。

## 第1章 相対的アーキテクチャの構成

- 原稿: [第1章](ja/04-relative-architecture.md)。
- 一次資料の固定版: `babd4d0ba63384991b488d3779f19d0b239365e2`。
- 原稿 SHA-256: `14f49d54fe1b9295b5d1bfe28636ba8b66c41af7ce46878da354e8cc6d50db40`。

| ID | 原稿の節・主張 | 種類 | 対象・仮定 | 一次資料の箇所 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- | --- |
| C1-01 | §1.1、命題1.4 | 数学 | 非空の Atom 語彙、五座標の外延性、抽出 doctrine と source | [数学本文 I §§1–3][math-i]、[Axioms][axioms] の `AtomAxiomSystem`、`ExtractionDoctrine`、抽出族の構成と一意性 | 正規化を含む抽出述語を明記し、存在一意性を外延性から証明 |
| C1-02 | §1.2、定理1.18 | 数学 | 有限抽出族、族を保つ composition、configuration を保つ object reading、operation reading | [数学本文 I §§4–6・10][math-i]、[ObjectAlgebra][object-algebra]、[AATCore][core] の `generate`、`algebra_object_nonempty_iff_reachable` と生成成分の定理 | operation を作用写像と同一視せず、最小閉包と有限到達可能性を両向きに証明 |
| C1-03 | §§1.3–1.4、命題1.16 | 数学 | 対象依存の残差、必須添字、有限符号付き query、健全性と必須添字上の完全性 | [数学本文 I §§7–9][math-i]、[AATCore][core]、[ReadingFunctoriality/Core][reading-core]、[LawfulnessZero][lawfulness] | circuit の不在と方程式の成立に必要な条件を明記。量の零性との同値は零を反映する集約を条件として記載 |
| C1-04 | §§1.5–1.6、命題1.21・1.23、例1.24 | 数学 | 小さい前順序文脈圏、選択した pullback、被覆要件 | [数学本文 II §§2–13][math-ii]、[Coverage][coverage]、[Topology][topology]、[Stacks Tag 00YW](https://stacks.math.columbia.edu/tag/00YW)、[Tag 00ZG](https://stacks.math.columbia.edu/tag/00ZG) | 生成位相と情報の可視性を区別。層化の構成・普遍性と、貼り合わせを追加する二点の例を記述 |
| C1-05 | 定義1.25、補題1.26、章末 | 数学 | 係数環、座標・構造関係、多項式制限によるイデアル保存。方程式と幾何の対応には実現の条件が必要 | [StructureSheaf][structure-sheaf]、[GeometryTransport/Basic][geometry-basic] の raw system の再添字づけ・係数変更、[WitnessIdeal][witness-ideal]、[Correspondence][law-correspondence] | 商前層と係数変更を記述。第2章への接続では、記号的座標から作るイデアルと対象ごとの残差を区別し、両者を結ぶ実現の条件を明記 |
| C1-06 | §1.7、命題1.29、定理1.31 | 数学 | Atom の全単射、一般の source 写像、exact core 射、被覆・overlap・係数・raw system・文脈データの比較 | [AtomFoundation/Doctrine][doctrine]、[Core の exact 射][reading-core]、[AtomFoundation/Categories][atom-categories]、[GeometryTransport/Categories][geometry-categories]、[ThreeStageProjection][three-stage] | 構成成分を定義してから射影の関手性を証明。文脈の前順序性と raw 表示データの等式を明記 |
| C1-07 | §1.8、命題1.33・1.34、例1.35 | 数学 | 全域lens、共通view・基準viewと有限基準fiber。可視変更の正規形は同じ積lensの自己変更 | [LensSemantics][lens-semantics] の `canonicalNormalFormEquiv`、`homEquivFiberMap`、[相対的な操作保存][lens-relative]、[FGMPS04 §3.1](https://www.cis.upenn.edu/~bcpierce/papers/newlenses-full.pdf) | 固定viewの積表示と射の制限・延長。可視変更は同じV×KのnormalFormと隠れた置換の一意性へ限定。既存の4対2の例は今回の検証完了に含めない |
| C1-08 | §1.9、命題1.37・1.38 | 数学 | 有限グラフ・有限宣言関係・有限状態、観測関手、一般の意味保存射 | [ProtocolSchema][protocol-schema]、[ProtocolSemantics][protocol-semantics]、[ProtocolFinitePresentation][protocol-presentation]、[ProtocolReconstruction][protocol-reconstruction]、[Spivak12 §§3.2・3.4–3.5](https://arxiv.org/pdf/1009.1166v3) | 有限表から全経路への延長を合同関係と帰納法で証明。adapter の保存を頂点成分の平方で説明 |
| C1-09 | 構成1.39・1.40、命題1.41 | 数学 | 型の役割と操作名の有限語彙、状態値を持つ source、法則をまだ課していない操作データ | [CSAATArchitectureObjects][cs-objects]、[CSAATLawSystems][cs-laws] の role 対象・名前付き操作・抽出・Lawfulness 同値 | source と Atom の役割を区別し、非単射の状態写像を保持。Law は固定 carrier の操作データを評価。定数環前層を一文脈へ制限した場合を本文に構成し、三法則・経路等式との同値を証明 |
| C1-10 | 定義1.42、命題1.43 | 数学 | 明示した型付き役割写像と、get/put または edge/observe の可換性 | [CSAATTypedOperationTranslation][cs-typed]、[CSAATForwardMorphisms][cs-forward]、[ProtocolReconstruction][protocol-reconstruction] | 型付き射と意味保存射の Hom 全単射を両逆・恒等・合成まで証明。§1.7 の exact core 射とは射の定義を区別 |

[math-i]: ../../../docs/aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md
[math-ii]: ../../../docs/aat/algebraic_geometric_theory/part_2_architecture_geometry_sites_sheaves.md
[axioms]: ../../../Formal/AG/Atom/Axioms.lean
[core]: ../../../Formal/AG/Atom/AATCore.lean
[object-algebra]: ../../../Formal/AG/Atom/ObjectAlgebra.lean
[lawfulness]: ../../../Formal/AG/Atom/LawfulnessZero.lean
[coverage]: ../../../Formal/AG/Site/Coverage.lean
[topology]: ../../../Formal/AG/Site/Topology.lean
[reading-core]: ../../../Formal/AG/ReadingFunctoriality/Core.lean
[structure-sheaf]: ../../../Formal/AG/LawAlgebra/StructureSheaf.lean
[witness-ideal]: ../../../Formal/AG/LawAlgebra/WitnessIdeal.lean
[law-correspondence]: ../../../Formal/AG/LawAlgebra/Correspondence.lean
[doctrine]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Doctrine.lean
[atom-categories]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Categories.lean
[geometry-basic]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Basic.lean
[geometry-categories]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Categories.lean
[three-stage]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/ThreeStageProjection.lean
[lens-semantics]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/LensSemantics.lean
[lens-relative]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATLensRelativeOperationSquares.lean
[protocol-schema]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSchema.lean
[protocol-semantics]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSemantics.lean
[protocol-presentation]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolFinitePresentation.lean
[protocol-reconstruction]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolReconstruction.lean
[cs-objects]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATArchitectureObjects.lean
[cs-laws]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATLawSystems.lean
[cs-typed]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATTypedOperationTranslation.lean
[cs-forward]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATForwardMorphisms.lean

## 第2章 Lawの幾何と局所整合性

- 原稿: [第2章](ja/05-law-geometry.md)。
- 一次資料の固定版: `313086df1e2071236b64ffd454615e927e428e26`。
- 原稿 SHA-256: `e97b905662d639ce5d605351e67f581732f169c21aa36faaaf9b3e915e53d65b`。
- [図2.1](figures/ch02-finite-covers.svg)の SHA-256: `0827c5487af26d4fde58149668d3900089ac27dbe6b680999bf171a6bc8f9e4e`。

| ID | 原稿の節・主張 | 種類 | 対象・仮定 | 一次資料の箇所 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- | --- |
| C2-01 | §2.1、定義2.1・命題2.2 | 数学 | 構造関係の商、observable ring との表示同型、制限との整合 | [数学本文 III §§4・8、定理8.3][c2-math-iii]、第1章の定義1.25 | 配置の関手を定義し、多項式環と商の普遍性から自然な全単射を証明。原稿では有限性を仮定せず、任意の元が有限個の変数だけを使う普遍性を用いる |
| C2-02 | 定義2.3・命題2.4 | 数学 | 記号的生成元の制限則、必須添字、層化したイデアルの像 | [数学本文 III §§5–6][c2-math-iii]、[WitnessIdeal][witness-ideal] | 生成元の有限和から制限の包含と層化後のイデアル性を確認。必須添字の和を明示 |
| C2-03 | §§2.1–2.2、構成2.6・定理2.9・系2.11 | 数学 | 評価関手のアフィン表現、残差の正則性、開部分の比較・合成条件、被覆と重なりを保つchart対応 | [数学本文 III §§5.2–5.2C・11.1][c2-math-iii]、[Correspondence][law-correspondence]、[Stacks 01HR](https://stacks.math.columbia.edu/tag/01HR)・[01JA](https://stacks.math.columbia.edu/tag/01JA)・[01HP](https://stacks.math.columbia.edu/tag/01HP) | 方程式と残差の評価を等しくする商を作り、生成元の評価と局所化を証明。siteのイデアルとschemeのイデアルの比較を指定。加群の引き戻しの零性ではなく、構造層内で生成するイデアルの零性を用いる。対象の残差へ戻る同型は系2.11の追加条件 |
| C2-04 | §2.3、構成2.12・命題2.15 | 数学 | 商係数、対象依存の残差、circuitの健全性・完全性、自然な係数実現と非零性 | [数学本文 III §5.1A][c2-math-iii]、[数学本文 IV §2.1A][c2-math-iv]、[数学本文 X §5.1][c2-math-x] | 文脈ごとの残差の失敗、局所configuration上の有限query、制限に安定な選択circuit族、局所健全性・局所完全性を明記。記号的生成元と残差類を区別し、集約の相殺条件を分離して単独circuitの検出命題を証明 |
| C2-05 | §2.4、補題2.17・例2.19 | 数学 | 固定した有限単射射被覆、アーベル群値の係数、空交差の零係数 | [数学本文 IV §§3–4][c2-math-iv]、[数学本文 X §2][c2-math-x] | 微分の合成、固定被覆の商群、三chartのperiodによる同型を本文で計算 |
| C2-06 | §2.5、命題2.21・定理2.22・系2.23 | 数学 | 交差図式上の自由かつ推移的な作用、局所atlas、空交差の高々一元性、実際の状態の層条件 | [数学本文 IV §§5・11][c2-math-iv]、[数学本文 X §8][c2-math-x]、[Stacks 03AG](https://stacks.math.columbia.edu/tag/03AG) | 差のcocycle、atlas変更によるcoboundary、補正後の貼り合わせを証明。自己交差・逆向き・空交差の一致を確認。Lawful状態が層になる理由と、有限検査からLawfulnessへ進むための条件を明記 |
| C2-07 | §2.6、命題2.24–2.28 | 数学 | 有限次元・有限長、連結な交差、定数係数、forestの制限全射、単体のchainとcochain | [数学本文 IV §§12–13][c2-math-iv] | 容量下界、Euler交代和、nerve比較、forest消滅、Stokesを証明。群の次元と指定類の非零性を区別 |
| C2-08 | 命題2.29 | 数学 | 有限単体複体の二部分複体による分解、共通の定数係数 | [数学本文 IV §§8–9・13][c2-math-iv] | 原稿では有限cochainの場合を構成。制限の差の全射、持ち上げ独立性、零性の同値、境界とのペアリングを直接証明 |
| C2-09 | §2.7、命題2.32・例2.33–2.34 | 数学 | 宣言した意味変形族に対する抽出の不変性、構造座標、条件S、構造側の一次コホモロジー消滅 | [DependencyProfile][c2-two-phase-dependency]、[CoefficientComplex][c2-two-phase-complex]、[CohomologyComparison][c2-two-phase-h1]、[ForestSupport][c2-two-phase-forest]、[FiniteWitnesses][c2-two-phase-finite] | AtomKindだけの分類を用いず、商の微分と単射性を証明。条件S（原資料のConditionE）の不成立例と、それだけでは単射にならない例を計算。例2.34とLeanの複体はともに二組の二頂点・二平行辺からなる。原稿の一般の体に対し、Leanの係数はZMod 2 |
| C2-10 | §2.8、定義2.35・補題2.36 | 数学 | 有限source・Law族、Law値を保つ原始関係、整数係数 | [PresentationGroup][c2-presentation] の `presentationGroupEquivBlocks` | 生成子関係の商と成分ごとの自由アーベル群の両逆を証明。四生成子・二関係の例を計算 |
| C2-11 | 構成2.37–2.39 | 数学 | 選定した点・生成子のAtom族、開集合に対応する文脈、三chart・四chart、局所定数係数 | [PointGeneratorAtomInput][c2-atoms]、[FiniteCoverGeometry][c2-cover-geometry]、[CombinedAtomContextSupport][c2-support]、[CombinedAtomContextContinuity][c2-continuity]、[CombinedAtomActualNerve][c2-nerve] | 原稿では全生成子を読む開集合文脈の部分圏を明示して構成。より大きな文脈siteとの同値は主張しない。八点の位相から被覆・連結性・三重交差の空性を示し、実際の切断と制限でČech座標を得る |
| C2-12 | 命題2.40–2.41・例2.42 | 数学 | 同じ整数係数と実被覆、任意のchart状態と辺遷移 | [SpecifiedAffineObstruction][c2-affine]、[ExistingObstructionBridge][c2-existing]、[CombinedAtomSpecifiedObstruction][c2-specified]、[SelectedFiniteObstructionExamples][c2-selected-examples] の `coarse_nonzero_actual` | 原始関係の方程式が評価・制限・平行移動で成立することを証明。実際の比較から指定cocycleを作り、torsorの貼り合わせ障害との一致と局所状態変更による類の不変性を記述 |
| C2-13 | §2.9、定義2.43–構成2.46 | 数学 | semantic atom、supported generator、制限で保たれる修復関係、修復語の作用、別に選ぶ方程式側のlift | [数学本文 X §§3–6][c2-math-x]、[SAGA §§3.4–4](https://arxiv.org/html/2608.21458v1) | 二つの係数と二つの残差をそれぞれ構成。作用からtorsorを導く条件と、修復生成元を対象依存の残差類へ送る写像を明記 |
| C2-14 | §2.10、補題2.48・定理2.49 | 数学 | 生成元に関して同変な局所状態写像、関係と生成元の完全性、空交差の正規化 | [数学本文 X §§6–7][c2-math-x]、[EquationRealization][c2-saga-realization] の `equationRelationSound`、[KappaComparison][c2-saga-kappa]、[SAGA 定理5.1(i)–(ii)](https://arxiv.org/html/2608.21458v1#S5) | 関係の健全性を状態写像と自由作用から導出。係数同型、次数0〜2の複体同型、一次コホモロジー同型を証明。独立に選んだatlasの差を明示的なcoboundaryとして比較 |
| C2-15 | 系2.50・例2.51 | 数学 | 実際の修復状態の層条件、固定被覆、独立な偶奇表示と剰余表示 | [数学本文 X §§8・10.2][c2-math-x]、[SAGA 定理5.1(iii)・5.2、例5.3](https://arxiv.org/html/2608.21458v1#S5) | 零類から補正と層の貼り合わせを経て実際の修復へ進むことを証明。四chartの非零periodと遷移変更後の零類を検算 |

[図2.1](figures/ch02-finite-covers.svg)は、八点空間の八本の順序関係と、四chart・三chartのnerveを示す。
図の三角形に面はなく、辺点の記号 `e_{01}` は一次資料の `k` と同じ点を指す。

[c2-math-iii]: ../../../docs/aat/algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md
[c2-math-iv]: ../../../docs/aat/algebraic_geometric_theory/part_4_obstruction_cohomology.md
[c2-math-x]: ../../../docs/aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md
[c2-two-phase-dependency]: ../../../research/lean/ResearchLean/AG/TwoPhase/DependencyProfile.lean
[c2-two-phase-complex]: ../../../research/lean/ResearchLean/AG/TwoPhase/CoefficientComplex.lean
[c2-two-phase-h1]: ../../../research/lean/ResearchLean/AG/TwoPhase/CohomologyComparison.lean
[c2-two-phase-forest]: ../../../research/lean/ResearchLean/AG/TwoPhase/ForestSupport.lean
[c2-two-phase-finite]: ../../../research/lean/ResearchLean/AG/TwoPhase/FiniteWitnesses.lean
[c2-presentation]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/PresentationGroup.lean
[c2-atoms]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/PointGeneratorAtomInput.lean
[c2-cover-geometry]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/FiniteCoverGeometry.lean
[c2-support]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomContextSupport.lean
[c2-continuity]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomContextContinuity.lean
[c2-nerve]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomActualNerve.lean
[c2-affine]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedAffineObstruction.lean
[c2-existing]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/ExistingObstructionBridge.lean
[c2-specified]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomSpecifiedObstruction.lean
[c2-saga-kappa]: ../../../Formal/AG/SemanticRepair/Saga/KappaComparison.lean
[c2-selected-examples]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedFiniteObstructionExamples.lean
[c2-saga-realization]: ../../../Formal/AG/SemanticRepair/Saga/EquationRealization.lean

## 第3章 標準解像度と診断不変性

- 原稿: [第3章](ja/06-resolution-invariance.md)。
- 一次資料の固定版: `8d949b2c116551f680f9792842e79e58d529e30a`。
- 原稿 SHA-256: `45afaa65c6cffd7ddccbf9f188ad0c43a40592e853ba5103cc460192f83176fe`。

| ID | 原稿の箇所 | 入力・成立条件 | 一次資料の箇所 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- |
| C3-01 | 定義3.1–定理3.4・例3.5 | 同じsource上の全射、有限Law族、評価の降下 | [Reading][c3-reading]、[JointKernel][c3-joint] | kernel上の恒常性と降下、canonical factorの全射性、joint kernel商の普遍性・一意性を証明 |
| C3-02 | 構成3.6–例3.8 | 有限source、評価値と抽出結果の等号判定、指定されたdoctrine族 | [Effective][c3-effective]、[Admissible][c3-admissible]、[正例][c3-positive]・[反例][c3-negative] | partitionを計算し、抽出結果のkernelとの一致を判定。六sourceの二つの真の細分から、adequacyだけでは表示可能性が従わないことを示す |
| C3-03 | 定義3.9–命題3.12 | 有限nerve、chartの台、辺・面の交差台、adequacy、有理係数 | [LawGeneratedComplex][c3-complex] | 座標はLawと相異なる値の組とし、witnessを座標に加えない。二つの微分とLaw値ごとの直和分解を記述 |
| C3-04 | 定義3.13・命題3.14 | chart写像、辺・面の部分写像、台の包含、縮約面の三辺の縮約 | [SupportedNerveMorphism][c3-morphism]、[GeneratedComparisonMap][c3-map] | 実際の座標式からcochain比較を生成し、二つの微分平方とH¹写像を証明 |
| C3-05 | 定義3.15–定理3.17・例3.18 | C0・C5・C6は全体、C1–C4は各Law-value block。C3は有理chainで定義 | [条件C][c3-conditions]、[block比較の全単射][c3-bijective]、[SelectedReadingConditionC][c3-selected-c] | fiber内部の道積分による補正、単射性、辺・面の持ち上げによる全射性を証明。三chart・四chartの具体例を与える |
| C3-06 | 例3.19 | 全体のchart台、三source、二つのLaw、異なるnerveの比較 | [AdequateConditionCFailure][c3-adequate-failure]、[CanonicalInadequateFalsePositive][c3-false-positive]、[CanonicalInadequateHiddenClass][c3-hidden] | loopと道、道と平行二辺を本文用の小例として計算。共通Lawのadequacyと被覆条件を分け、追加Lawが降下しない場合も説明 |
| C3-07 | 定義3.20–命題3.23 | 同じ比較幾何、全adequate有限Law族、明示的有限表示 | [UniformityReduction][c3-uniform]、[DefectSemantics][c3-defect]、[UniformPresentationDecider][c3-decider] | Law値のfiberによる部分nerveの同定とindicator Lawの逆方向を証明。実比較の核・余核の次元による判定を有理行列計算として示す |
| C3-08 | 系3.24・例3.25 | 全非空target部分集合、C0–C6、全体のchart台 | [AtlasPositioning][c3-atlas] | 各条項を部分集合とLaw-value blockの間で移す。条項の非必要性は本文用に七つの小例を構成し、各実比較の階数を別途検算。既存の七つのLean witnessと同じ有限表であるとは主張しない |
| C3-09 | 定義3.26–命題3.28 | 接続役割別の隣接色とclip2個数を読む、本文で定義した局所観測 | [T3/T6の有限入力][c3-t3t6]、[一様性の相違][c3-t3t6-uniform] | 同じ有限入力について局所型の一致と周期3・6のcocycleを直接計算。観測の範囲は下記に明記 |
| C3-10 | 定義3.29–命題3.32 | 語彙・解像度・source意味論・正規化を固定し、意味readingと許可述語を変える族。source別の有理係数 | [NerveGeneration][c3-struct-nerve]、[StructuralLocalization][c3-struct-local]、[GeneratedH1Vanishing][c3-struct-zero] | 構造台を族全体で残る抽出対として定め、nerveの一致を証明。各sourceの基準Atomを用いてすべてのcocycleのprimitiveを構成 |
| C3-11 | 構成3.33–例3.35 | ラベルを保つ原始関係、整数presentation係数 | [CoefficientComparison][c3-coefficient] | 同じラベルに属する関係成分の係数和としてεを定義。同ラベルの連結性による単射性と、二生成子・空関係の非単射例を示す |
| C3-12 | 構成3.36・定理3.37 | 連結なchart・非空二重交差、異なる三chartの交差が空、局所定数な整数係数、任意の局所データ | [FaceEmptyCechNormalization][c3-normalization]、[ActualCechH1Comparison][c3-h1]、[CombinedAtomSpecifiedObstruction][c3-specified] | 実際の切断・制限からφを定め、同じ入力で独立に書いた診断生成式とのcochain等式を示す。Φは整数係数から有理係数への加法的準同型として扱う |
| C3-13 | 定義3.38–例3.41 | 同ラベル生成子の原始関係による連結性、各ラベルの全chart共通代表 | [IntegralReflection][c3-integral]、[SpecifiedClassReflection][c3-reflection]、[CombinedAtomSpecifiedReflection][c3-selected-reflection] | 有理primitiveの床関数から整数primitiveを作り、実切断へ戻して零性を反映。共通代表を欠く反例は本文の被覆上で別途構成 |
| C3-14 | 構成3.42・定理3.43 | 同じ点・生成子Atom入力、第一成分Law、粗いreadingと恒等reading、実際の三chart・四chartの細分 | [SelectedReadingRefinement][c3-refinement]、[CombinedAtomReadingNaturality][c3-naturality] | 内部辺を零へ送る実restrictionを計算し、cochainの比較平方、局所データと指定類の輸送を証明 |
| C3-15 | 定理3.44・例3.45 | 同じ入力で両端の反映条件とC0–C6が成立し、canonical factorは非単射 | [SelectedReadingConditionC][c3-selected-c]、[SelectedFiniteObstructionExamples][c3-examples] | 四つの零性の同値を合成。非零mismatchを持つ零障害例と非零障害例について、整数・有理periodを粗細両側で計算 |
| C3-16 | §3.11末尾 | 対応する交差図式、制限と可換な係数同型、対応するLaw・witness・軸 | [数学本文VIII §7][c3-math-viii]、[Stacks Tag 09UY](https://stacks.math.columbia.edu/tag/09UY) | 固定被覆の各次数のcochain同型から、対応する障害類の零性同値を説明 |

### 局所観測と有限例の範囲

定義3.26の `Obs_loc` は、接続役割別の色・個数を読む観測である。
[GLocalV1Nonfactorization][c3-full-local] の `G_local-v1` は、終端簡約、半径1の接続情報、
targetの同時再ラベル等を含む別の観測仕様である。
命題3.28はT3/T6の同じ生の入力を使い、定義3.26の観測について直接証明する。
既存仕様全体の非因子化とは区別する。

例3.25の七例は、共通loop成分により全行でC3も破れる。
主張は七条項それぞれの非必要性であり、他の六条項をすべて満たすという独立性ではない。

章末のコードレビュー例は、標準解像度・条件C・指定障害類の零性反映の応用可能性を示す。
実コード上のモデル構成・仮定の検証・有効性の実験結果は含まない。

[c3-reading]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/Reading.lean
[c3-joint]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/JointKernel.lean
[c3-effective]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/Effective.lean
[c3-admissible]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/Admissible.lean
[c3-positive]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/PositiveWitness.lean
[c3-negative]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/NegativeWitness.lean
[c3-complex]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean
[c3-morphism]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/SupportedNerveMorphism.lean
[c3-map]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean
[c3-conditions]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean
[c3-bijective]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonBijectivity.lean
[c3-adequate-failure]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/AdequateConditionCFailure.lean
[c3-false-positive]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/CanonicalInadequateFalsePositive.lean
[c3-hidden]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/CanonicalInadequateHiddenClass.lean
[c3-uniform]: ../../../research/lean/ResearchLean/AG/UniformInvariance/UniformityReduction.lean
[c3-defect]: ../../../research/lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean
[c3-decider]: ../../../research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationDecider.lean
[c3-atlas]: ../../../research/lean/ResearchLean/AG/UniformInvariance/AtlasPositioning.lean
[c3-t3t6]: ../../../research/lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Witnesses.lean
[c3-t3t6-uniform]: ../../../research/lean/ResearchLean/AG/UniformInvariance/GLocalV1T3T6Uniformity.lean
[c3-full-local]: ../../../research/lean/ResearchLean/AG/UniformInvariance/GLocalV1Nonfactorization.lean
[c3-struct-nerve]: ../../../research/lean/ResearchLean/AG/StructuralCover/NerveGeneration.lean
[c3-struct-local]: ../../../research/lean/ResearchLean/AG/StructuralCover/StructuralLocalization.lean
[c3-struct-zero]: ../../../research/lean/ResearchLean/AG/StructuralCover/GeneratedH1Vanishing.lean
[c3-coefficient]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CoefficientComparison.lean
[c3-normalization]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/FaceEmptyCechNormalization.lean
[c3-h1]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/ActualCechH1Comparison.lean
[c3-specified]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomSpecifiedObstruction.lean
[c3-integral]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/IntegralReflection.lean
[c3-reflection]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedClassReflection.lean
[c3-selected-reflection]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomSpecifiedReflection.lean
[c3-refinement]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedReadingRefinement.lean
[c3-naturality]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomReadingNaturality.lean
[c3-selected-c]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedReadingConditionC.lean
[c3-examples]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedFiniteObstructionExamples.lean
[c3-math-viii]: ../../../docs/aat/algebraic_geometric_theory/part_8_measurement_theory.md

## 第4章 輸送と合成の整合性

- 原稿: [第4章](ja/07-transport-coherence.md)。
- 一次資料の固定版: `bb9c533efbd68adc0e8004a90e5a782c8497a1c2`。
- 原稿 SHA-256: `45fd889da90a59abb00bdcac0efc3801bffe61850c8731eef9841fda7b7fee87`。

| ID | 原稿の箇所 | 入力・成立条件 | 一次資料の箇所 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- |
| C4-01 | 定義4.1・補題4.2 | 関手、任意の底の後続射を量化する強いopcartesian射 | [Coreの普遍性][c4-core-opcart]、[liftの一意性][c4-core-unique]、[Stacks Tag 02XJ](https://stacks.math.columbia.edu/tag/02XJ) | 任意の後続射について存在一意性を定義し、vertical同型の一意性、恒等・合成の閉性を証明。Stacksの強いcartesian射の双対であることを明記 |
| C4-02 | 構成4.3–定理4.5 | Exactな抽出射、Atom全単射、一般のsource写像、元のcore | [AtomFoundation/Transport][c4-core-transport]、[Opcartesian][c4-core-opcart] | configuration・対象形成・名前付きoperation・方程式・detector・invariant・signatureを再添字づけし、任意のexactな後続射に対する因子を逆再添字づけで構成。各成分の一意性を確認 |
| C4-03 | 例4.6・構成4.7 | 前向き抽出保存、Atom全単射、追加抽出族の有限性、実際のbase operation、方程式とdetector健全性 | [RefinementObstruction][c4-refinement-obstruction]、[RefinementSupply][c4-refinement-supply] | 三Atomの交換と追加によるexact性の失敗を記述。追加operationの向きは拡大基点から旧基点の像とし、到達可能性と像の上でのquery・受理保存を導出 |
| C4-04 | 構成4.8–定理4.11 | Coreの文脈同値、被覆要件の存在量化像、選択overlap、同じ係数でのraw system再添字づけ、三つの実現比較 | [GeometryTransport/Transport][c4-geom-transport]、[Supply][c4-geom-supply]、[Factorization][c4-geom-factor]、[Opcartesian][c4-geom-opcart] | 一般のcore射にはH_geomを必要十分な存在条件として示す。標準core輸送では三つの可逆な実現比較を構成し、任意のcoreの後続射について幾何の因子を構成・一意化 |
| C4-05 | 補題4.12–定理4.16 | 抽出の底に沿う標準core・幾何lift、fiberの対象とvertical射、coreへの射影 | [CorePseudofunctor][c4-core-pseudo]、[Pseudofunctor][c4-geom-pseudo]、[TowerCompatibility][c4-tower] | 標準輸送の関手、compositor、unitor、自然性、三重合成・単位・射影整合を対応づける |
| C4-06 | 定義4.17–構成4.18 | 有限グラフの各頂点のcore、抽出の底で等しい二道、強い辺lift、底固定の指定自己同型 | [FinitePresentation][c4-presentation] | AdmissibleLiftData・AdmissibleTransportDataに揃え、指定比較と標準比較の差を定義する |
| C4-07 | 定義4.19・補題4.21–定理4.23 | 同じcoreの有限比較データ、終点fiber群の再選択、現在の選択を含む作用空間 | [FinitePresentation][c4-presentation]、[VanishingCoherence][c4-vanishing] | 道の終点変化、作用則、消滅と整合性を既存宣言に対応づける。番号外の一般群圏の二辺公式を削除 |
| C4-08 | 補題4.24–命題4.27 | 同じcoreデータの後続道、向き付きの貼り合わせ、指定した有限syzygy | [PastingObstruction][c4-pasting] | 後続道への自己同型と因子化、標準貼り合わせの端点式、syzygy条件下の等式、閉じた不一致の共役式を保持。群準同型という追加結論と二因子公式を削除 |
| C4-09 | 例4.20・例4.28–例4.29 | S3の独立な平行二辺、共有辺の二要求、三比較の有限計算 | [VanishingCoherence][c4-vanishing]、[FiniteWitnesses][c4-finite]、[UnifiedObstruction][c4-unified] | 元から記載された有限計算を保持し、限定後のcoreの定理への適用という説明を外す。A/B型の検証完了とは扱わない |
| C4-10 | 定義4.30–定理4.33 | 有限図式の幾何のp-strongな辺、射影したq-strongな辺、底の二道の一致、指定比較 | [SectionDecomposition][c4-section] | TwoLayerLiftDataに揃えて射影を示す。整列したedge sectionに対し、核と順序を保つdefect分解を記述 |
| C4-11 | 定理4.34 | 同じ二段の強い辺、整列したedge section、核の再選択、全ての面 | [GlobalVanishing][c4-global] | 同じsection上の幾何の整合性と核の補正を対応づける。Coreだけの消滅定理を幾何へ代入しない |
| C4-12 | 例4.35 | S4、選択した二軸の安定化群とC2の直積、一頂点・二loop・二面 | [CrossStageCoherence/FiniteWitnesses][c4-stage-finite]の四軸と平方根の機構 | K→S4の有限群の方程式。S4の二つの平方根がどちらもKへ持ち上がらず、核の条件は解ける例。幾何packageの実例とはしない。元の例の個別照合はA/B側に残る |
| C4-13 | 定義4.36–例4.39 | 共通V・v₀、有限基準fiber、一般の状態写像とV上の自己写像 | [CSAATLensRelativeOperationSquares][c4-lens]、第1章の定義1.32・命題1.34・例1.35・定義1.42 | 四役割のh,u,h,h×uとget/put平方、固定viewの対応、全単射を備えた変更の両逆。Unit×Boolの定値自己射の非単射性を既存宣言へ対応させる |
| C4-14 | 命題4.40 | 固定プロトコル、名前付き生成辺、頂点写像、観測とadapter | [CSAATProtocolAdapterSquares][c4-protocol]、第1章の命題1.38・式(1.23) | 命題1.38を適用して生成辺から全実行への保存を得て、式(1.23)からadapter平方を頂点成分で特徴づける |
| C4-15 | §4.12、定理4.41・章末 | 充満忠実関手と比較射。CSへの適用は固定viewのlens・固定schemaのプロトコル | [CSAATFullyFaithfulComparisonTransport][c4-fully-faithful]、第1章の命題1.43 | 比較保存群と射影の対応を保持。相対view全体の充満忠実性と任意の意味論の圏へのdefect理論の代入を削除 |

概要とまとめの注文APIの例は、構成4.18・定理4.23・命題4.37・4.38・4.40の応用可能性を示す。
実開発での実証結果は含まない。

[c4-core-transport]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Transport.lean
[c4-core-opcart]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Opcartesian.lean
[c4-core-unique]: ../../../research/lean/ResearchLean/AG/AtomFoundation/LiftUniqueness.lean
[c4-refinement-obstruction]: ../../../research/lean/ResearchLean/AG/AtomFoundation/RefinementObstruction.lean
[c4-refinement-supply]: ../../../research/lean/ResearchLean/AG/AtomFoundation/RefinementSupply.lean
[c4-geom-transport]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Transport.lean
[c4-geom-supply]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Supply.lean
[c4-geom-factor]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Factorization.lean
[c4-geom-opcart]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Opcartesian.lean
[c4-core-pseudo]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/CorePseudofunctor.lean
[c4-geom-pseudo]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/Pseudofunctor.lean
[c4-tower]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/TowerCompatibility.lean
[c4-presentation]: ../../../research/lean/ResearchLean/AG/TransportCoherence/FinitePresentation.lean
[c4-vanishing]: ../../../research/lean/ResearchLean/AG/TransportCoherence/VanishingCoherence.lean
[c4-pasting]: ../../../research/lean/ResearchLean/AG/TransportCoherence/PastingObstruction.lean
[c4-finite]: ../../../research/lean/ResearchLean/AG/TransportCoherence/FiniteWitnesses.lean
[c4-unified]: ../../../research/lean/ResearchLean/AG/TransportCoherence/UnifiedObstruction.lean
[c4-section]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/SectionDecomposition.lean
[c4-global]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/GlobalVanishing.lean
[c4-stage-finite]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/FiniteWitnesses.lean
[c4-lens]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATLensRelativeOperationSquares.lean
[c4-protocol]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATProtocolAdapterSquares.lean
[c4-fully-faithful]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATFullyFaithfulComparisonTransport.lean

## 第5章 基底変換と生成比較

- 原稿: [第5章](ja/08-base-change.md)。
- 一次資料の固定版: `9364f25d1b54dff9ad059ae95c71d0404626d0d6`。
- 原稿 SHA-256: `8ce677c00c994881f6cf2617e0f4991a449b1f25cea7fd12a3e685b6303a84e7`。

| ID | 原稿の箇所 | 入力・成立条件 | 一次資料の箇所 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- |
| C5-01 | 構成5.1・命題5.2・例5.3 | 同じAtom carrier、exactなcospan、一般のcone。Pointed版ではcompatibleな選択source | [DoctrinePullback][c5-pullback]、[PointedDoctrinePullback][c5-pointed] | Sourceのcompatible pair、成分ごとの正規化、第一成分の抽出を定義。第二射影のAtom成分をe₂⁻¹e₁とし、Atom成分が恒等とは限らない全coneに普遍射を構成・一意化 |
| C5-02 | 定義5.4・構成5.5・定理5.6 | 任意のsemantic exact底射、任意のtarget core。有限codeによる表示は仮定しない | [CartesianTarget][c5-cartesian]、[ExactBottomGlobalLift][c5-global]、[Stacks §4.33](https://stacks.math.columbia.edu/tag/02XJ) | 有限な選択族を逆Atom写像で戻し、対象形成・operation・方程式・detector・invariant・signatureを再添字づけ。任意の先行底射を量化する強いcartesian性を上段の逆から証明 |
| C5-03 | 補題5.7・命題5.8・例5.9 | 一般のexact射について存在定理から固定した標準cartesian liftと標準の前向き輸送 | [GlobalLiftCoherence][c5-global-coherence]、[PackageProjectionBeckChevalleyExactness][c5-bc-exactness]、[TransportEquivalence][c5-transport-equiv] | 標準選択の引き戻し関手、単位・合成比較と整合性を記述。一般の任意cleavageについての一括した主張を除く |
| C5-04 | 構成5.10–命題5.12・例5.13 | Atom等号判定、有限codeのcospan・compatibleな選択source・有限診断図式から生成した平方 | [CoreBeckChevalleyMate][c5-bc-mate]、[PackageProjectionBeckChevalleyExactness][c5-bc-exactness] | 標準mate、三角式、可逆性を対応づける。5.12は任意比較の一致判定から、liftの選択変更と両端同型の比較式へ置換 |
| C5-05 | 定義5.14・定理5.15・例5.16 | Source有限表、既定値・有限例外、有限台Atom置換。正規化後に輸送したcode自体の等号を要求 | [Schema][c5-code]、[CoverageSchema][c5-coverage-schema]、[CoverageClassification][c5-coverage] | 抽出述語の評価の同値とcode等号を区別。端点の表示を選び直すcoverageと固定code間のHomを分け、第8章と条件を同期 |
| C5-06 | 定義5.17・構成5.18 | 有限の底の図式、辺平方、sourceの強い辺lift、頂点でのcanonical輸送 | [IndexedBaseDiagram][c5-diagram]、[IndexedDiagnosticAssembly][c5-assembly] | 生成辺から道の自然性を帰納的に導出し、同じ平方で上段の辺を因子分解。合成・単位・貼り合わせを一意性から比較 |
| C5-07 | 命題5.19・例5.20 | 変更前の関係、変更先の生の辺と可換平方の族。Epiは指定面の始点での消去に使用 | [IndexedRawFamilyClassification][c5-raw-family] | 面の両経路は頂点射との前合成後に等しいことを示す。本文の十分条件は指定面の始点だけにepiを要求し、既存Leanの生成辺の始点も含むSupportEpiより弱い条件で、本文内の消去証明を用いる。全対象・全平行射への一様な消去条件とepiの同値は、固定した図式の整合性の必要条件とは区別する。二点のsourceで非epiの失敗例と整合する対照例を構成 |
| C5-08 | 構成5.21・定理5.22・例5.23 | 両端で関係を満たす固定図式、同じ入力から生成した辺と指定比較、全てのedge gauge | [EndpointExactness][c5-endpoint]、[CoherenceExactness][c5-coherence]、[ObstructionExactness][c5-obstruction]、[OrbitExactness][c5-orbit] | Fiber同値から終点群の同型を作り、cochain・再選択を両方向へ対応づける。標準比較とraw defectの自然性を示し、整合性、消滅する再選択の存在、任意cochainの軌道所属を保存・反映。S3の例は本文内の群による検算 |
| C5-09 | 定義5.24・定理5.25 | 前向きの抽出保存、上段のexact条件、target coreが存在する選択点での抽出の反映 | [RealizedSupport][c5-realized]、[Refinement Projection][c5-ref-projection]、[Qualification][c5-qualification] | 実現台をcore fiberの非空性で定義。反映条件から逆再添字づけを作り、逆に任意のliftの選択族等式から反映を導く。空fiberの空虚な場合を明示 |
| C5-10 | 構成5.26・命題5.27 | Exact cospanと一方のlegへのrefinement、compatibleなsource対。逆方向にはその点の実現台条件 | [Configuration][c5-ref-configuration]、[Regime][c5-regime]、[Mate][c5-ref-mate]、[Qualification][c5-qualification] | 前向きの平方を反映条件なしで作る。Exactな第一射影によるcore輸送で実現台を移し、二つの逆経路とmateを構成。全compatible点での分類と、恒等・合成の閉性を証明 |
| C5-11 | 例5.28・例5.29 | 三Atom、二source、非自明なAtom交換、各点の実core。別に無限抽出による空fiber | [Refinement Witnesses][c5-ref-witnesses] | 前向きだけの点と、compatibleな入力をallへ絞ると逆輸送できる点を対照化。本文用の小例ではcomposition・対象形成・恒等operation・空Law等を指定し、coreの存在を説明。既存witness packageをそのまま引用したとは扱わない |
| C5-12 | 定義5.30・構成5.31・定理5.32前半 | 生成したcore liftの上段逆、完全な被覆・overlap・raw systemと同じ係数環 | [RefinementGeometry][c5-ref-geometry]、[UpperGeometryCleavage][c5-upper-cleavage]、[UpperGeometryCleavageRealization][c5-upper-realization]、[UpperGeometryMate][c5-upper-mate] | 幾何の全成分を引き戻し、coreと幾何の二段のcartesian性からmate・逆・下段射影・三角形・係数恒等を構成。任意の一方向の幾何射を可逆とは扱わない |
| C5-13 | 定理5.32後半・補題5.33 | 有限根付き図式、同じ底のfiberのsource core図式、二段の強い辺lift、固定係数、同じsourceから引き戻す指定比較 | [CompatibleInput][c5-compatible-input]、[UpperRefinementBCProblem][c5-upper-problem]、[CompatibleMateNaturality][c5-compatible-natural]、[CompatibleGlobalMate][c5-compatible-global]、[SolutionContracts][c5-solution-contracts]、[SolutionEquivalence][c5-solution-equiv] | 辺と指定比較のintertwiningを二段のcartesian一意性から証明。端点同型によるc⁻¹sbと逆を明示し、三角形・道・貼り合わせを含む解と再選択軌道を両方向へ移す |
| C5-14 | 命題5.34–命題5.36 | 既存のview制限と四状態の計算、残す操作・関係のプロトコルとadapter | 第1章の定義1.32・1.36と第4章の命題4.40。元のF30の個別検証は未実施 | 一般の相対lens同型によるview制限の移送を削除。四状態の元の計算とプロトコルの制限は保持し、A/B型の検証完了には含めない |
| C5-15 | 構成5.37・命題5.38 | Atom等号判定、有限codeで実現した平方、同じ図式のcore・強い辺、各面の終点b₁・底の二道、指定比較、面、係数環、完全幾何 | [ExactDerivedMateComposite][c5-derived-mate]、[ExactDerivedBarAlphaTriangle][c5-alpha-triangle]、[ExactDerivedBarAlphaProjection][c5-alpha-projection] | AuthoredBCDatumSquareの全入力を本文に列挙し、その同じ入力の実二経路・標準同型・三角式・core射影へ対応させる |
| C5-16 | 定義5.39・構成5.40・まとめ | 構成5.37の共通入力と同じ図式のcochain、元coreのAd条件 | [ObjectNormalization][c5-normalization]、[CanonicalNormalization][c5-geom-normalization]、[ExactBarBetaFactorization][c5-beta-factor]、[ExactBarBetaProjection][c5-beta-projection] | 元の正規化の定義を保持し、同じ有限表示された平方とcochainから選ぶ自己射・β・barβ・射影を記述 |

モノリスの分割例では、業務操作を読む場合と通信・失敗・再試行まで読む場合とで、
入力と保存条件をそれぞれ指定する。説明の対象は指定した範囲の比較であり、実コードの評価結果は含まない。

[c5-pullback]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/DoctrinePullback.lean
[c5-pointed]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullback.lean
[c5-cartesian]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
[c5-global]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLift.lean
[c5-global-coherence]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLiftCoherence.lean
[c5-bc-mate]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMate.lean
[c5-bc-exactness]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactness.lean
[c5-transport-equiv]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/TransportEquivalence.lean
[c5-code]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/Schema.lean
[c5-coverage-schema]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageSchema.lean
[c5-coverage]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClassification.lean
[c5-diagram]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IndexedBaseDiagram.lean
[c5-assembly]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticAssembly.lean
[c5-raw-family]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IndexedRawFamilyClassification.lean
[c5-endpoint]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/EndpointExactness.lean
[c5-coherence]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/CoherenceExactness.lean
[c5-obstruction]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/ObstructionExactness.lean
[c5-orbit]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/OrbitExactness.lean
[c5-realized]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/RealizedSupport.lean
[c5-ref-projection]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Projection.lean
[c5-qualification]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Qualification.lean
[c5-ref-configuration]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Configuration.lean
[c5-regime]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Regime.lean
[c5-ref-mate]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Mate.lean
[c5-ref-witnesses]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Witnesses.lean
[c5-ref-geometry]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementGeometry.lean
[c5-upper-cleavage]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean
[c5-upper-realization]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavageRealization.lean
[c5-upper-mate]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryMate.lean
[c5-compatible-input]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleInput.lean
[c5-upper-problem]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperRefinementBCProblem.lean
[c5-compatible-natural]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleMateNaturality.lean
[c5-compatible-global]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleGlobalMate.lean
[c5-solution-contracts]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSolutionContracts.lean
[c5-solution-equiv]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSolutionEquivalence.lean
[c5-derived-mate]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedMateComposite.lean
[c5-alpha-triangle]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedBarAlphaTriangle.lean
[c5-alpha-projection]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedBarAlphaProjection.lean
[c5-normalization]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalization.lean
[c5-geom-normalization]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalization.lean
[c5-beta-factor]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFactorization.lean
[c5-beta-projection]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaProjection.lean

## 第6章 冪等正規化と実現

- 原稿: [第6章](ja/09-idempotent-normalization.md)。
- 一次資料の固定版: `12884419d705624be39e8a87393ed50385395469`。
- 原稿 SHA-256: `b09a3690e2d51759c1574a9e955e5a38acc6342927e0f8bbaa6e683cb0812114`。
- [図6.1](figures/ch06-karoubi-arrow.svg)の SHA-256: `6e37897fd7912478b5b3391100dead8fa1eb3c8318759bfd97e2519a197dae4a`。

| ID | 原稿の箇所 | 入力・成立条件 | 一次資料の箇所 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- |
| C6-01 | 構成6.1–例6.4 | 対象形成のconfiguration保存、全architecture object、任意の値集合 | [ConfigurationDescent][c6-descent] | 射影とsection、固定点とconfigurationの対応、商、正規化で不変な写像の一意因子化を証明。四対象のモデルはこの集合上の構成を説明する本文用の例 |
| C6-02 | 定理6.5 | 定義5.39のAd。型の等号に沿うoperation写像 | [Core normalization][c6-core-normalization]、[IdempotentExchangeNormalization][c6-idempotence] | 対象だけでなく、operation・底・文脈・方程式・invariant・signatureを含む射全体の冪等性を証明。任意の選択同型を型の同一視と扱わない |
| C6-03 | 補題6.6 | 任意のcore射の対象形成・configuration保存。Adは不要 | [CanonicalObjectNormalizationNaturality][c6-object-naturality] | 対象写像の自然性を導き、operationまで含む自然性の条件と分ける |
| C6-04 | 命題6.7・定理6.8 | 任意のconfiguration上の全architecture object。Core内の分裂は両射がcore射であることを要求 | [DistinctArchitectureObjects][c6-distinct]、[InternalNormalizationSplitNoGo][c6-no-split] | 一元型・二元型の対象から非単射性を示す。仮想的なsectionの単射性と対象自然性から、全対象が固定点になる矛盾を導く |
| C6-05 | 定義6.9–例6.13 | 任意の圏、同型α、冪等射d | [RawFailureLocus][c6-raw-failure]、[Karoubi image][c6-image] | 冪等完備化・分裂を定義から説明。β=dα、e=α⁻¹dα、γ=α⁻¹dについて両側逆を計算し、元の圏の可逆性と像の同型を区別。四点の例は本文の有限集合の計算 |
| C6-06 | 定理6.14・命題6.22 | Adを満たすcoreを持つ完全幾何と、その充満部分圏の全射 | [CanonicalNormalization][c6-geom-normalization] | Coreと被覆・overlap・係数・support・軸・observable・raw systemを含めて冪等性と片側吸収を確認。正規化関手の充満性、coreへの射影、底・係数の保存を証明 |
| C6-07 | 補題6.15 | 一般exact射のcore liftと幾何の前向きlift。完全幾何の引き戻しとfiber関手上の正規化保存にはAtom等号判定とRealizableHom | [ExactNormalizationNaturality][c6-exact-naturality] | 一般のliftの交換式と、有限codeで実現された射についての幾何のmap-normalizationを分けて記述 |
| C6-08 | 定理6.16 | 構成5.37の有限codeによる共通入力、同じ面・cochain・元core・係数・完全幾何 | [ExactDerivedBarAlphaTriangle][c6-alpha-triangle]、[ExactBarAlphaNormalizationNaturality][c6-alpha-naturality]、[ExactBarBetaFactorization][c6-beta-factor]、[ExactBarBetaClassification][c6-beta-classification] | 同じ生成比較の冪等分解、可逆性分類、像の同型と端点正規化との一致を既存宣言へ対応させる |
| C6-09 | 命題6.17 | 定理6.16の同じ有限code入力と生成された端点同型 | [ExactBarBetaProjection][c6-beta-projection]、[G116KaroubiPlacement][c6-placement] | 標準比較・二冪等射・生成比較を同じcore射影と端点同型で対応づける |
| C6-10 | 例6.18 | 元から本文に定めた一Atom・一source、二軸、configurationのHomをoperationとするcoreと完全幾何 | 第1章の元の入力、定理6.5・命題6.7・定理6.14。元のF32の個別検証は未実施 | 正規化自体の例へ縮小。有限code・AuthoredBCDatumSquareとの対応がない生成比較への適用を削除。6.25で用いる元のcoreは保持し、A/B型の検証完了とは扱わない |
| C6-11 | 補題6.19–定理6.21 | Ad coreの充満部分圏、全てのcore射 | [CanonicalNormalizationAbsorption][c6-absorption]、[NormalizationCategory][c6-category]、[NormalizationProjection][c6-projection] | N_Q f N_P=f N_Pを全成分で示す。Sandwich条件を満たす射の圏、恒等射N_P、充満関手f↦f N_Pを構成 |
| C6-12 | 命題6.23・命題6.24 | 同じ充満部分圏。正規化のoperation写像を固定 | [NormalizationNaturalityFailure][c6-naturality-failure]、[ModificationBlocker][c6-operation-coherence] | Karoubi内の包含の自然性を片側吸収から証明。逆方向の族の自然性をf N_P=N_Q f、さらにoperation成分の等式と同値とする |
| C6-13 | 例6.25 | 例6.18をHom×Boolのoperationへ拡張。元の対象に依存するBool反転 | [ModificationCounterexample][c6-counterexample]、[NormalizationNaturalityFailure][c6-naturality-failure] | 型の違いを使う既存反例の仕組みを、本文のcore上に構成。f²=1、fN=N、Nf≠fNを示す。f≠1とfN=Nから正規化関手の非忠実性も本文内で導く |
| C6-14 | 定義6.26–命題6.28 | 任意の圏と関手、三段の射影 | [KaroubiArrowEquivalence][c6-arrow-equivalence]、[FunctorNaturality][c6-functor-naturality]、[ThreeStageProjection][c6-three-stage] | 冪等平方(c,e,d)をdceへ送る関手と逆を構成。往復の同型・自然性、関手への適合と射影の合成を成分で証明 |
| C6-15 | 構成6.29 | 比較の圏の全対象、同型の端点変更 | [MaximalSubgroupoid][c6-groupoid]、[G116KaroubiPlacement][c6-placement] | 非可逆な比較も対象に残す最大亜群を説明。J(β)と像の間のβの端点と恒等射を区別 |
| C6-16 | 命題6.30と四状態の例・命題6.31 | 固定viewのlens三法則と有限な基準fiber、有限状態のプロトコル実現、実行・観測を保つ冪等adapter | 第1章の定義1.32・命題1.33・命題1.34・定義1.36・命題1.38 | 積表示で自己射を(v,k)↦(v,t(k))と書き、tの固定点から同じLensの圏内で任意の冪等射を分裂させる。四状態から二状態への射はその具体例として検算。プロトコルは固定点集合を実行・観測へ制限し、二つの意味保存adapterの分裂を直接証明。状態ごとの冪等性だけでは実行が閉じない反例を付す。本文で証明した帰結であり、同じCS命題のLean形式化を示すものではない |

[c6-descent]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ConfigurationDescent.lean
[c6-core-normalization]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalization.lean
[c6-idempotence]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeNormalization.lean
[c6-object-naturality]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CanonicalObjectNormalizationNaturality.lean
[c6-distinct]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/DistinctArchitectureObjects.lean
[c6-no-split]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/InternalNormalizationSplitNoGo.lean
[c6-raw-failure]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeRawFailureLocus.lean
[c6-image]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeKaroubiImage.lean
[c6-geom-normalization]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalization.lean
[c6-exact-naturality]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactNormalizationNaturality.lean
[c6-alpha-triangle]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedBarAlphaTriangle.lean
[c6-alpha-naturality]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaNormalizationNaturality.lean
[c6-beta-factor]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFactorization.lean
[c6-beta-classification]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaClassification.lean
[c6-beta-projection]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaProjection.lean
[c6-beta-witness]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFiniteWitness.lean
[c6-absorption]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/CanonicalNormalizationAbsorption.lean
[c6-category]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationCategory.lean
[c6-projection]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationProjection.lean
[c6-naturality-failure]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationNaturalityFailure.lean
[c6-operation-coherence]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorModificationBlocker.lean
[c6-counterexample]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorModificationCounterexample.lean
[c6-arrow-equivalence]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/KaroubiArrowEquivalence.lean
[c6-functor-naturality]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/FunctorNaturality.lean
[c6-three-stage]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/ThreeStageProjection.lean
[c6-groupoid]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/MaximalSubgroupoid.lean
[c6-placement]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/G116KaroubiPlacement.lean

## 第7章 比較を保つ変更と情報

- 原稿: [第7章](ja/10-comparison-and-information.md)。
- 一次資料の固定版: `c08b1a0e078a242e4683fdb375dc1e7c6a3c4e14`。
- 原稿 SHA-256: `f3214e74b8a16353e1408dde31b421fb3e33b2179860e34cb787d900b1e30b86`。
- [図7.1](figures/ch07-refactoring-workers.svg)の SHA-256: `eaa505fc2aa5158d917a3d6d5ad9e11e22ca899e1b232b8aaa2711483b3ceb15`。

| ID | 原稿の箇所 | 入力・成立条件 | 一次資料の箇所 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- |
| C7-01 | 例7.1 | 一頂点・一名前付きループ、二状態、恒等操作と反転操作 | [PeriodSeparation][c7-period] | 共通部品へ切り出す更新処理が、決済区分を保持する場合と反転する場合を小さな状態機械で説明。既存の二対象の有限witnessそのものではなく、本文用の別の例として定義・評価する |
| C7-02 | 定義7.2・命題7.3 | 完全幾何の比較と底固定の端点変更群。比較自身の底は任意 | [QualifiedComparisonStabilizer][c7-stabilizer]、[QualifiedComparisonGroup][c7-object-group] | 底固定の比較保存群とArr(Kar(E_geom))の底固定可逆変更群の同型、端点射影を記述 |
| C7-03 | 定理7.4・系7.5 | 7.4は完全幾何と底固定群。7.5はその可逆比較、および任意圏の全端点群の場合 | [QualifiedComparisonStabilizer][c7-stabilizer] | 射影核・像・追随fiberをqualified宣言へ対応させる。一般圏の全端点群の共役同型にはgeneratedArrowComparisonSourceEquivを使用 |
| C7-04 | 定理7.6 | 第5章§5.8の共通sourceと二経路、底を固定するsource自己同型 | [QualifiedComparisonGeneratedClassification][c7-generated] | 実際の二経路の因子化と生成mateの三角形から、core・幾何のcartesian一意性を順に使って適合性を証明。独立なsource変更の差を残余部分群へ帰着する |
| C7-05 | 命題7.7 | 各sourceの底・係数固定同型から、辺・面・輸送の選択を移して入力を再構成 | [SourcePresentation F0][c7-source-input]、[F1][c7-source-legs]、[F2][c7-source-changes]、[F3][c7-source-comparison] | 新しい入力を作ってから両経路を生成し、普遍性から端点同型・比較と変更の共役式を得る。完成済み比較の共役を入力とはしない |
| C7-06 | 定義7.8〜命題7.10 | 群準同型O、部分群Γ。Oの全射性は不要 | [ObservationKernel][c7-observation] | 判定の因子化とker O⊆Γ、飽和、観測fiber、基点付き剰余類を証明。計算可能な判定手続きの存在とは区別する |
| C7-07 | 系7.11 | 完全幾何の同型比較と底固定端点群、係数観測 | [EndpointKernelClassification][c7-coefficient] | K/Lを剰余類集合とし、[(a,b)]↦bT(a)⁻¹を両逆つきで証明。S3の対角部分群の非正規性を計算。入力表示変更との整合は命題7.7から導く。実生成比較の不可視な対は構成7.20で別途構成する |
| C7-08 | 命題7.12 | 関手による全端点自己同型群の写像、admissible core・完全幾何の充満部分圏 | [NormalizationComparisonGroup][c7-normalization-group]、第6章の定理6.21・命題6.22 | 関手性から比較保存を、射影の等式から底固定群への制限を導く |
| C7-09 | 構成7.13・定理7.14 | dc=ceを満たす冪等射と中心化群。一般準同型rにはr(Γ₀)⊆Δ | [KaroubiRestriction][c7-karoubi]、[GroupHomRestriction][c7-group-restriction] | 保存、反映の二条件、適合するliftの存在・右核torsor、短完全列を証明。全端点群の核と適合部分群上の核を区別する |
| C7-10 | 例7.15・例7.16 | 三点集合、恒等比較。定値冪等射とfiberサイズ1・2の冪等射 | [KaroubiRestrictionFiniteWitness][c7-karoubi-witness] | 不適合対が像で適合する計算と、fiberサイズが異なるため像の交換を持ち上げられない証明を本文に置く |
| C7-11 | 構成7.17 | Configurationと全付随データの積表示、選択対象と共通の基準元 | [CanonicalNormalizationObjectSection][c7-object-section] | 出発・到着の二つの交換を合成して、選択対象を保つ延長を構成。中間の交換の消去から恒等・合成則を得る |
| C7-12 | 補題7.18 | Adを満たすcoreを持つ完全幾何。型の等式に沿うoperationの同一視 | [CoreSection][c7-core-section]、[GeometrySection][c7-geometry-section]、[AutomorphismSection][c7-aut-section] | 正規化・射の適用・型の復元でoperationと対象依存の保存則を構成。残りの幾何成分を保持し、全射成分の恒等・合成・吸収から群準同型sectionを得る |
| C7-13 | 定理7.19 | 両端がAdを満たす完全幾何の任意の同型比較 | [CanonicalNormalizationIsoComparisonSection][c7-iso-section] | Sourceのsectionと元の比較による共役を組み合わせ、両端で独立に選んだsectionの自然性を仮定せずに比較を保つsectionを構成。底・係数保持も証明 |
| C7-14 | 構成7.20 | 同じ完全幾何と、選択値以外の二つの付随データ | [AmbientKernelObjectSwap][c7-swap]、[CoreLift][c7-swap-core]、[GeometryLift][c7-swap-geometry] | 実際の非恒等・対合な対象写像をoperation・全幾何成分へ延長。正規化による吸収と底・係数固定を示す |
| C7-15 | 定理7.21 | 構成5.37の有限code・core・強い辺・面の終点・底の二道・指定比較から生成したα、元coreのAd | [ExactBarAlphaCanonicalComparisonSection][c7-alpha-section]、[Exactness][c7-alpha-exactness]、[AmbientKernelComparisonWitness][c7-ambient-witness] | 同じ入力のsection、分裂短完全列、右torsor、反映の失敗に対象を揃える |
| C7-16 | 系7.22 | 構成5.37の共通入力、同じ図式のcochain、5.40の選択、正規化と交換する端点変更 | [ExactBarBetaComparisonSection][c7-beta-section]、[ExactBarBetaComparisonGroup][c7-beta-group]、[BottomQualifiedClassification][c7-beta-bottom] | 同じ生成比較について、sectionと保存・反映の分類、底固定版を記述 |
| C7-17 | 定義7.23〜系7.26 | 有向多重グラフ、内部状態Kを恒等に運ぶ辺、可視部分群H。個数にはV,Kの有限性 | [FixedFComponentClassification][c7-components]、[AllAutomorphismGroup][c7-all-group]、[SplitExactSequenceAndTorsor][c7-split]、[FiberCardinality][c7-cardinality] | 再添字積、分裂短完全列、section、右torsor、fiber個数、指定点版を保持。半直積同型を削除 |
| C7-18 | 命題7.27・例7.28 | 同じ積lens V×K、基準view、有限K、固定した可視置換u | [FixedFLensConnection][c7-lens]、[FixedFLensGroupConnection][c7-lens-group]、第1章の命題1.33 | 操作保存変更と追随変更の全単射、一意な隠れた置換、個数、指定section保存を既存宣言へ対応。任意lensの共役移送・群同型・直積同定を削除。例7.28の元の有限計算は検証完了に含めない |
| C7-19 | 命題7.29・例7.30 | 有限グラフで全状態K・全辺が恒等。二ワーカーの四頂点・二辺・Bool | [FixedFProtocolConnection][c7-protocol]、[FixedFProtocolGroupConnection][c7-protocol-group]、[FixedFFiniteExamples][c7-examples] | 分裂短完全列とfiberの対応、16対4と交換に追随する4個を保持。全変更群の半直積同型と位数8を削除 |
| C7-20 | §7.8導入・末尾・まとめ | 固定viewのlens・固定schemaのプロトコル、型付き射への充満忠実関手 | 命題1.43、定理4.41、[CSAATFullyFaithfulComparisonTransport][c4-fully-faithful] | 定理4.41による比較保存群と端点射影の対応へ限定。一般可視変更への拡張、および7.4からの核・torsor分類の適用を削除 |

[c7-period]: ../../../Formal/AG/RepresentationAnalysis/PeriodSeparation.lean
[c7-stabilizer]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonStabilizer.lean
[c7-object-group]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/QualifiedComparisonGroup.lean
[c7-generated]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonGeneratedClassification.lean
[c7-source-input]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF0.lean
[c7-source-legs]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF1.lean
[c7-source-changes]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF2.lean
[c7-source-comparison]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF3.lean
[c7-observation]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/ObservationKernel.lean
[c7-coefficient]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/EndpointKernelClassification.lean
[c7-normalization-group]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationComparisonGroup.lean
[c7-karoubi]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/KaroubiRestriction.lean
[c7-group-restriction]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/GroupHomRestriction.lean
[c7-karoubi-witness]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/KaroubiRestrictionFiniteWitness.lean
[c7-object-section]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationObjectSection.lean
[c7-core-section]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationCoreSection.lean
[c7-geometry-section]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationGeometrySection.lean
[c7-aut-section]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationAutomorphismSection.lean
[c7-iso-section]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalizationIsoComparisonSection.lean
[c7-swap]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/AmbientKernelObjectSwap.lean
[c7-swap-core]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/AmbientKernelCoreLift.lean
[c7-swap-geometry]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/AmbientKernelGeometryLift.lean
[c7-alpha-section]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaCanonicalComparisonSection.lean
[c7-alpha-exactness]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaCanonicalComparisonExactness.lean
[c7-ambient-witness]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/AmbientKernelComparisonWitness.lean
[c7-beta-section]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaComparisonSection.lean
[c7-beta-group]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaComparisonGroup.lean
[c7-beta-bottom]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaBottomQualifiedClassification.lean
[c7-components]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFComponentClassification.lean
[c7-all-group]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFAllAutomorphismGroup.lean
[c7-split]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFSplitExactSequenceAndTorsor.lean
[c7-cardinality]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFFiberCardinality.lean
[c7-lens]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFLensConnection.lean
[c7-lens-group]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFLensGroupConnection.lean
[c7-protocol]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFProtocolConnection.lean
[c7-protocol-group]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFProtocolGroupConnection.lean
[c7-examples]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFFiniteExamples.lean

## 第8章 表示と局所再構成

- 原稿: [第8章](ja/11-local-reconstruction.md)。
- 一次資料の固定版: `b738623af29f015ab2d12e11c94411c74f26d311`。
- 原稿 SHA-256: `a1f668eb10a3ce196d04b1895374a100b5ba8766366e02bc745910f0952cc020`。
- [図8.1](figures/ch08-local-reconstruction.svg)の SHA-256: `4b486994f4297015a6c2f98dd0a6eb08e1d0ef3af5607f39f2a5ede436cc7591`。

| ID | 原稿の箇所 | 入力・成立条件 | 一次資料の箇所 | 原稿での構成・証明 |
| --- | --- | --- | --- | --- |
| C8-01 | 定義8.1・命題8.2 | 離散集合D、Bool値、既定値と有限例外。Dの有限・無限を区別 | [OnePointCode][c8-one-point]、[EvaluationClassification][c8-evaluation]、[CodeFibers][c8-code-fibers] | 一点コンパクト化の位相を定義し、無限遠での値と連続性からcodeを回復。無限Dの評価の単射性、有限Dの各評価に対する二つのcodeを証明 |
| C8-02 | §8.1の位相的な言い換え | 第5章定理5.15の端点同型を許すcoverage。両Source有限、target抽出有限または余有限 | [CoverageTopology][c8-coverage]、[DiscreteCompactness][c8-compactness]、定理5.15 | 連続延長と有限例外表を対応づけ、離散Sourceのcompactnessを有限性へ帰着。固定端点間のHomと区別 |
| C8-03 | 命題8.3・例8.4 | 固定code間の意味的射。正規化後の既定値の保存と、実際のAtom置換の有限support | [FixedArrowClassification][c8-fixed]、[FixedArrowConsequences][c8-fixed-consequences]、[FinOneCounterexample][c8-fin-one] | 必要性と実際の置換を使う十分性を証明。表示の射をdecoded equalityで商することを明記。一Atomの既定値0/1による非充満性を計算 |
| C8-04 | 系8.5 | 有限Atom carrier。正規化後の抽出codeが既定値falseとなる充満部分圏 | [FiniteFullSubcategory][c8-full]、[FiniteCodeNormalization][c8-code-normalization]、[FiniteNormalizationRealizationIso][c8-code-iso] | 評価を保つ正規化、全射成分の有限support、既定値保存から充満忠実性を導く。decodeとの自然同型を示し、raw codeの等号と区別 |
| C8-06 | 定義8.6〜補題8.9・例8.10 | 依存する値の型、全有限query集合、型付きBool graph、各行の存在一意性 | [IndependentFiniteFragments][c8-fragments]、[IndependentCarrierGraphReadings][c8-graphs] | 単点glueと制限の両逆、graphと関数の両逆・恒等・合成を証明。整合する全偽graphと非一意なgraphによってrow条件の役割を説明 |
| C8-07 | 定義8.11・定義8.15 | 原始評価の有限support、型参照、量化されたrow条件、有限carrierのcover、逆graph | [IndependentFiniteGraphLawFormula][c8-formulas]、[共通の有限support評価][c8-common] | 一式の有限supportと全量化・整合族全体の有限性を区別。操作の作用を保つ可換式を具体的な有限graph評価として説明 |
| C8-08 | 定理8.12 | Hom分離、Hom組立て、同型までの対象組立て | [LocalReconstructionEquivalence][c8-principle]、[Stacks Tag 02C3](https://stacks.math.columbia.edu/tag/02C3) | Hom両逆、存在一意性、充満忠実性・本質的全射性を導く。逆関手と単位・余単位を本文に構成 |
| C8-09 | 構成8.13・定義8.14 | Atomの集合とrepresentative/explicit geometryの射の方式を固定。形式化のParameter.geometryに対応 | [共通の原始再構成][c8-common]、[ExplicitExactGeometryHom][c8-explicit] | 完全幾何と全許容Homから実現圏を定義。二方式のraw・context作用・realizationの差を明示。CS入力は構成8.22へ分離 |
| C8-10 | 定義8.15・補題8.16 | source/target/Homのquery、原始objectデータ、独立な型・保存式、整合後の補助選択の商 | [GeometryPrimitiveDeclaration][c8-geometry-declaration]、[GeometryHomPrimitiveDeclaration][c8-hom-declaration]、[InvariantQuotient][c8-invariant-quotient]、[GeometryCategoryReconstruction][c8-geometry-category] | 局所対象と射を原始データから定め、成分ごとのgraph合成から局所圏を作る。補助invariant witnessだけを消し、全保持成分を残す |
| C8-11 | 補題8.17 | 完全幾何の全原始条件。source/core/context/site/raw/realizationの依存順 | [GeometryPrimitiveAssembly][c8-geometry-assembly]、[GeometryCategoryReconstruction][c8-geometry-category]、[InvariantQuotient][c8-invariant-quotient] | 型の依存順に対象を構成し、全Homの成分をgraphから組み立てる。保存式、raw二方式、証明上の補助選択、再読取りの両逆を説明 |
| C8-14 | 定理8.18・系8.19 | Atomの集合と完全幾何の射の二方式。任意の完全幾何の端点対、非可逆を含む全許容Hom | [共通の原始再構成][c8-common]、[一般原理][c8-principle] | 補題8.17で両方式の分離・組立てを証明し、定理8.12を適用。原始reader自身が主同値の前向き関手となり、Hom両逆・存在一意性・恒等・合成・評価・同型反映を得る。CSの補題を依存先に含めない |
| C8-22 | 概要・§8.6の金融例・図8.1・まとめ | 同一通貨・手数料なしの行内送金。指定取引と正の金額に対する完了・出金・入金・仕訳のBool読み取り。完全幾何の再構成には定義8.15の全原始データと条件を要求 | 定義8.11・8.15、補題8.17、定理8.18、[共通の原始再構成][c8-common]。業務領域の分担のみ[BIAN9](https://bian.org/wp-content/uploads/2024/12/BIAN-Service-Landscape-V9_0-Value-Chain-View.pdf)を参照 | 完了の含意を三つの整数残差で表し、不整合な対応候補の残差(1,1,0)を計算。担当ごとの記述と有限query片を区別し、対象は同型まで、固定端点間の射は一意に回復する条件付き適用を説明。金融の状態・Lawは本文用に定めた説明例であり、金融システム全体の形式化や実装の検証結果ではない |
| C8-15 | 例8.20 | タグ付きoperationの全source-choiceと一様flip、canonical正規化、explicit geometry | [共通のタグ入力][c8-common]、[TagChangeExactGeometryLocalModel][c8-tag-model]、[TagChangeCanonicalNormalizationGeometryLaws][c8-tag-normalization] | 実際のoperation成分の変化を読む。全source-choiceと正規化を同じnative圏から回復し、configurationだけの観測との差を説明 |
| C8-16 | 例8.21 | 構成5.37の有限code・図式・core・強い辺・終点・底の二道・指定比較、同じ面・cochain・係数・完全幾何 | [共通の固定生成入力][c8-common]、[G122OriginalInput][c8-original-input]、[ExactBarBetaFiniteWitness][c8-fixed-witness] | 同じ生成比較の元幾何・二経路・α/β/e/d・全端点自己同型を回復。具体的な三軸の有限例は削除 |
| C8-12 | 構成8.22・補題8.23・系8.25 | get/putの三法則、有限基準fiber。全状態写像にget/put保存を要求 | [IndependentLensPrimitiveReconstruction][c8-lens-primitive] | CS適用節で局所圏を定義し、carrier・get/putのgraphと有限coverから独立なLensを構成。Homの二条件と両逆を証明し、一般再構成原理から圏同値を得る |
| C8-13 | 構成8.22・補題8.24・系8.25 | 有限schema、関係、観測関手、有限な各状態集合。全頂点写像に辺・観測保存を要求 | [IndependentProtocolPrimitiveReconstruction][c8-protocol-primitive]、命題1.37・1.38、補題8.7・8.9 | CS適用節で局所圏を定義し、graphから生成辺・観測・頂点写像を構成。命題1.37・1.38から実現と意味保存射を得て、読み取りと組立てのHom両逆を示す。一般再構成原理から圏同値を得る |
| C8-17 | 命題8.26・例8.27 | 同じVとv₀のLens、有限基準fiber間の任意写像。非単射を許す | [LensSemantics][c8-lens-semantics]、[LensFiberModelEquivalence][c8-lens-fiber]、命題1.33・1.34 | 命題1.34のres/extの式と両逆を適用。例8.27は基準fiberの3値を2値へ送る非単射な表を用い、get/putを保つ一意な延長を示す |
| C8-18 | 命題8.28・例8.29 | 全生成辺の自然性と全頂点の観測保存を満たす表。例は二頂点一辺、Bool対の4状態、第一成分の観測、両頂点で恒等の対応候補 | [ProtocolSemantics][c8-protocol-semantics]、[ProtocolObservedRestrictionEquivalence][c8-protocol-reading]、命題1.38 | 必要性は自然性・観測保存から、延長の存在と一意性は命題1.38から導出。第二成分を0へ置き換える辺の作用は観測を保つが、第二成分1の二状態で候補の自然性が失敗する |
| C8-19 | 系8.30 | 有限基準fiber/頂点状態の列挙、finite decoder、共通primitive同値の単位 | [LensFinitePresentation][c8-lens-presentation]、[ProtocolFinitePresentation][c8-protocol-presentation]、[共通のCS比較][c8-common] | 有限decoderの充満忠実性・本質的全射性と、直接reader/共通同値経由readerの自然同型を示す。原稿の向きは形式化のcomparison isoの逆に対応 |
| C8-20 | 命題8.31 | Lens/観測付きprotocolの冪等射、有限decoder、KarとArr | [CSKaroubiReconstruction][c8-cs-karoubi]、[共通のCS Karoubi・Arrow接続][c8-common]、定理6.27、命題6.30・6.31 | 命題6.30・6.31による分裂を用い、retract生成、Karoubiへの延長、包含上のdecoder、射圏と端点評価の整合を本文で説明 |
| C8-23 | §8.8・概要・まとめ | 記憶領域のbit数、モデルの型・係数・contextと読み取り範囲を指定。有限query集合、各値の有限符号化、明示された有限列挙と計算可能な評価・等号判定 | 定義8.6・補題8.7、定理8.18、§8.7の有限表示、[有限片と貼り合わせ][c8-fragments] | 有限query集合の整合族を全体表と制限から回復する。金融例の完了・仕訳だけでは二候補を区別できず、出金・入金の読み取りで区別できることを計算。情報の十分性、有限の検査手順、時間・記憶費用を区別し、主同値から計算費用の上界は主張しない |
| C8-05 | 命題8.32・§8.9 | 底圏の一点Source、Atom=ℕ、常に真の抽出。計算可能性を制限しない全自己同型と可算な構文集合 | [NatAdjacentSwap][c8-adjacent]、[NatSubsetSwaps][c8-subsets]、[CountableSyntaxObstruction][c8-countable] | P(ℕ)から実際の自己同型への単射を構成し、可算decoderの非全射性を証明。無限対象の補足に配置し、有限資源の実装の不可能性とはしない。無限supportでも有限規則で記述できる隣接対交換により、表形式と規則の記述能力を区別。選択Atom族が無限なのでcoreの例とはしない |
| C8-21 | 命題8.33・§8.9 | タグsource-choice部分群、全有限Bool table。有限と無限の添字Ωを区別 | [TagChangeFiniteReadingRecovery][c8-tag-recovery]、[TagChangeFiniteGroupReconstruction][c8-tag-group]、補題8.7 | 全有限片の逆極限と点ごとの加法の対応を証明。全自己同型群を分類せず、source-choice部分群に限定。有限Ωでは全体表で決定でき、無限Ωでは任意の有限片の外の一点で異なる二つの変更を構成する。第一の濃度の反例とは必要な条件を区別 |

### 主同値と形式化の対応

定理8.18・系8.19は `Parameter.geometry` の両方式への特殊化、
構成8.22・系8.25は `Parameter.lens` と `Parameter.protocol` への特殊化に対応する。
本文では、各入力の独立な局所条件から組立てを証明し、定理8.12をそれぞれに適用する。
[IndependentAATPrimitiveReconstruction][c8-common] の対応する宣言は次のとおりである。

- 入力・原始値: `Parameter`、`NativeCategory`、`ObjectQuery`、`HomQuery`、`Query`、`Value`、`Fragment`、`Compatible`。
- 独立な局所条件: `ObjectTableLaws`、`LawfulObjectFamily`、`HomTableCertificate`、`LawfulHomFamily`。
- 局所圏との対応: `localObjectFamilyEquiv`、`localHomFamilyEquiv`。
- 分離と組立て: `assembleObjectFamily`、`assembleHomFamily`、`localHomFamily_read_assemble`、`assembleHomFamily_read`、`nativeHom_eq_of_commonFamily_eq`。
- 主結果: `reconstructionData`、`homSeparation`、`existsUnique_preimage`、`equivalence`、`equivalence_functor`、`homEquiv`。
- CSとの整合: `lensFiberComparisonIso`、`protocolObservedComparisonIso`、`lensFiniteDecoder_retractGeneratedBy`、`protocolFiniteDecoder_retractGeneratedBy`、`lensKaroubiEquivalence`、`protocolKaroubiEquivalence`、`lensKaroubiArrowEquivalence`、`protocolKaroubiArrowEquivalence`。

完全幾何の主同値は、対象と全Homの再構成を扱う。
投影・正規化・比較群・section・核・fiber・有限決定性までの全体の統合は、[数学棚卸し](mathematics-inventory.md)§8.5の改訂版の範囲である。
系8.30・命題8.31は、構成済みのCSのdecoder・retract・Karoubi・Arrとの接続を述べる。
命題8.33は個別のタグ読み取りの結果であり、共通primitive readerについての一般有限決定定理とはしない。

§8.6の行内送金例で示すのはLawの評価部分であり、完全幾何の全成分を構成した例ではない。
BIANの引用は業務領域の分担に限り、Lawと再構成の根拠は本文の定義と証明による。

[c8-one-point]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/OnePointCode.lean
[c8-evaluation]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/EvaluationClassification.lean
[c8-code-fibers]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CodeFibers.lean
[c8-coverage]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CoverageTopology.lean
[c8-compactness]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/DiscreteCompactness.lean
[c8-fixed]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FixedArrowClassification.lean
[c8-fixed-consequences]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FixedArrowConsequences.lean
[c8-fin-one]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FinOneCounterexample.lean
[c8-full]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteFullSubcategory.lean
[c8-code-normalization]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteCodeNormalization.lean
[c8-code-iso]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteNormalizationRealizationIso.lean
[c8-adjacent]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/NatAdjacentSwap.lean
[c8-subsets]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/NatSubsetSwaps.lean
[c8-countable]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CountableSyntaxObstruction.lean
[c8-fragments]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentFiniteFragments.lean
[c8-graphs]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentCarrierGraphReadings.lean
[c8-formulas]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentFiniteGraphLawFormula.lean
[c8-principle]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LocalReconstructionEquivalence.lean
[c8-common]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean
[c8-explicit]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATExplicitExactGeometryHom.lean
[c8-geometry-declaration]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryPrimitiveDeclaration.lean
[c8-hom-declaration]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryHomPrimitiveDeclaration.lean
[c8-invariant-quotient]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryHomInvariantQuotient.lean
[c8-geometry-category]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryCategoryReconstruction.lean
[c8-geometry-assembly]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryPrimitiveAssembly.lean
[c8-lens-primitive]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentLensPrimitiveReconstruction.lean
[c8-protocol-primitive]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentProtocolPrimitiveReconstruction.lean
[c8-tag-model]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryLocalModel.lean
[c8-tag-normalization]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeCanonicalNormalizationGeometryLaws.lean
[c8-original-input]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/G122OriginalInput.lean
[c8-fixed-witness]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFiniteWitness.lean
[c8-lens-semantics]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/LensSemantics.lean
[c8-lens-fiber]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensFiberModelEquivalence.lean
[c8-protocol-semantics]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSemantics.lean
[c8-protocol-reading]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedRestrictionEquivalence.lean
[c8-lens-presentation]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/LensFinitePresentation.lean
[c8-protocol-presentation]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolFinitePresentation.lean
[c8-cs-karoubi]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSKaroubiReconstruction.lean
[c8-tag-recovery]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteReadingRecovery.lean
[c8-tag-group]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteGroupReconstruction.lean

## Related Workの比較と出典

[Related Work](ja/12-related-work.md)は、主要21文献を六つの比較軸へ配置し、
既存研究の対象・仮定・射・結論と、本稿の構成を対応づける。
冒頭は、AATの対象と構造保存射、および比較する分野を示す。
R.7は六つの比較を踏まえたAATの位置づけを述べる。
個別の問題を共通の構成の特殊な場合として捉えるRising Seaの方針は、
[構成マスター](paper-structure.md)の§§2–3に対応する。
操作保存の分類は、第7章の定理7.24・7.25による。積lensの固定可視置換上の対応は命題7.27、プロトコルへの群構造の接続は命題7.29に分ける。
SAGAから継承する結果、lensの積表示、圏同値の一般判定、Cauchy completionの出典を示す。

### 比較する数学と固定版

比較に用いる一次資料は、commit `64fb370d89559aa59b1a31bcbd38e97c531d99c5` の第1〜7章原稿、
数学棚卸し、第8章の以下の個別構成・一般原理である。C型の修正には本書冒頭の固定版と対応表を適用する。
第8章の参照は、章と構成名による。

| 本文の箇所 | 比較する結果・条件 | 本稿側の証拠 |
| --- | --- | --- |
| R.1 | Lawの値による相対core、方程式・イデアル・零点、型付き意味保存射 | [第1章](ja/04-relative-architecture.md)の命題1.38・1.43、[第2章](ja/05-law-geometry.md)の定理2.9、および本書の該当章の一次証拠対応 |
| R.2 | 係数と修復状態のtorsor、層条件の下での指定障害類の零性、SAGAからの継承 | 第2章の定理2.22・2.49、系2.50。[第3章](ja/06-resolution-invariance.md)の定理3.40・3.43・3.44。判定対象は指定障害類の零性であり、実状態の延長にはtorsorと層の条件を用いる |
| R.3 | Law-valueに十分なreading、条件C、指定診断の零性反映、観測核による所属判定 | 第3章の定理3.4・3.17・3.40、[第7章](ja/10-comparison-and-information.md)の定理7.9。係数全体の同型と指定類の判定を区別 |
| R.4 | exactなreading変更からの輸送・引き戻し、随伴同値、mate、生成比較の冪等分解 | [第4章](ja/07-transport-coherence.md)の定理4.5・4.11・4.15、[第5章](ja/08-base-change.md)の命題5.8・定理5.11・命題5.12、[第6章](ja/09-idempotent-normalization.md)の定理6.16 |
| R.5 | 全域lens、基準fiberと任意の意味保存射、操作グラフによる比較を保つ可逆変更の分類 | 第1章の命題1.33・1.34、第7章の定理7.24・7.25・命題7.27・7.29。分類は固定した意味論の下で、操作が隠れた状態をそのまま運ぶモデルを対象とする |
| R.6の一般原理 | Hom分離、Hom組立て、対象の同型による組立てからの充満忠実性・本質的全射性・圏同値 | [LocalReconstructionEquivalence][rw-local]の`ReconstructionData.homEquiv`、`fullyFaithful`、`essSurj`、`equivalence`。標準判定の外部出典はStacks Tag 02C3 |
| R.6のlens | get/put graph、三法則、有限基準fiberからの対象・全Homの組立て | [IndependentLensPrimitiveReconstruction][rw-lens]の`homAssembly`、`objectAssembly`、`reconstructionData`、`equivalence`、`assembleHom_eq_homEquivFiberMap_symm` |
| R.6のプロトコル | 生成辺・観測graph、経路関係、各頂点の有限な状態集合とその有限リスト被覆、一般射の保存等式 | [IndependentProtocolPrimitiveReconstruction][rw-protocol]の`Object.state_cover`、`Object.state_finite`、`readingFunctor`、`homAssembly`、`objectAssembly`、`reconstructionData`、`equivalence` |
| R.6の完全幾何 | 独立な原始対象、局所Homの不変量による商、対象・全Homの両逆と恒等・合成 | [IndependentGeometryCategoryReconstruction][rw-geometry]の`representativeReadingHomEquiv`・`explicitReadingHomEquiv`、各`HomAssembly`・`ObjectAssembly`、`representativeEquivalence`・`explicitEquivalence`。局所対象と射の定義、成分ごとの保存条件、端点同型による射の対応 |
| R.6のretractと比較 | lens・protocolの有限表示からのKaroubi再構成と射の圏への拡張 | [CSKaroubiReconstruction][rw-karoubi]のlens・protocol各`KaroubiReconstructionEquivalence`、`RestrictionIso`、`KaroubiArrowReconstructionEquivalence`。第6章の定理6.12・6.16・6.27とも対応 |

### 引用する版と範囲

- 書誌は[文献](ja/14-references.md)、引用内容と原典の箇所・版は[文献確認記録](references.csv)に対応する。
- Cousot and Cousotの参照箇所はpp. 240–243。Goguenの層意味論は公開稿の箇所番号を用いる。
- Lawvereの原典は1963年PNAS論文。Kellyの引用は集合で豊穣化された場合を対象とする。
- Institutionの充足条件は定義1、署名の余極限からの理論の構成は定理11とその帰結による。
- 『Algebraic Databases』は2025年第3版を用いる。R.6の表示の射と意味の射の忠実性に関する訂正はAppendix B.1–B.3、migrationの構成は§§6–7、二重圏での移送・queryの記述は定義8.13・命題8.14・補題8.18・§§8.25–8.26・9による。
- Gibson・Young・SAGAは版を固定したプレプリントとして扱う。Youngの引用対象はsiteと完全束値の前層の提案である。
- 主要21文献と補足候補4件の役割は[収録案](related-work-plan.md)に記す。

### 原稿と書誌の識別情報

書誌と結合原稿の識別情報は次のとおりとする。結合原稿の範囲と連結順はREADMEの定義による。

| 対象 | SHA-256 |
| --- | --- |
| Related Work本文 | `6b911a7e42b70a69ca356f8bd799897ac7ad24dc3426cec8aa2fec588c16f0cd` |
| 書誌 | `bdb267f950d7747c510cd1c411f1e3da821808be623064933e67d12667828884` |
| READMEに定めた要旨〜結び（要旨・序論・準備節・第1〜8章・Related Work・結び）の結合原稿 | `2c5650e9a54f57219d8c53195de61be05510117d00777a01bdb5d5eab10808c6` |

[rw-local]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LocalReconstructionEquivalence.lean
[rw-lens]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentLensPrimitiveReconstruction.lean
[rw-protocol]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentProtocolPrimitiveReconstruction.lean
[rw-geometry]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryCategoryReconstruction.lean
[rw-karoubi]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSKaroubiReconstruction.lean
