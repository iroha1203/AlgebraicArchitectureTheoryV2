# G-124 C–E：パートIII・IVの実装設計

[固定GOAL A–E](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/18540a67e277997376dc5833de4a608c6f526987/research/goals/G-124-aat-local-semantic-reconstruction.md)を満たすための、構成・証明の依存順と受入条件を定める。GOAL blob は `4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`。新規構成の名前は提案名であり、この文書はそのLean証明を与えたものではない。

一次資料は[全体設計](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4711#issuecomment-5742767034)、[パートII設計](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4711#issuecomment-5754509275)、[A/Bの受理記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4711#issuecomment-5760376776)。実装参照は `9585e4fcb650928a6adc135e281200de939e20cc` に固定する。以下の `LSR/` は `research/lean/ResearchLean/AG/LocalSemanticReconstruction/`、`RR/` は `research/lean/ResearchLean/AG/RealizationReconstruction/` を表す。

## 1. 構成を固定する

全条項で `IndependentAATPrimitiveReconstruction.Parameter`、`NativeCategory`、`LocalCategory`、`Query`、`reading`、`equivalence` を使う。以下ではこれらを `Θ, R_Θ, M_Θ, Λ_Θ, N_Θ` と書く。対象・全許容Homの意味、representative/explicitの二方式、非可逆なCS射を維持する。

| 必要な基盤 | 再利用する実装 | 追加する仕事 |
| --- | --- | --- |
| 一つの主同値 | `LSR/IndependentAATPrimitiveReconstruction.lean` の `reconstructionData`、`homEquiv`、`equivalence`、`localTable_read` | C–Eを同じreaderの出力へ接続する |
| 投影に必要な点評価 | `IndependentGeometryPrimitiveDeclaration`、`PackageAssembly.lower`、`Coefficient.assemble`、context/observable/realizationの各点API | 既存成分assemblerを用いた投影先の圏・関手と自然同型 |
| 全比較群の輸送 | `RR/CSAATFullyFaithfulComparisonTransport.lean` の `generatedArrowComparisonMulEquivOfFullyFaithful` | `N_Θ`への適用と、投影・正規化・制限準同型との可換式 |
| KaroubiとArrowの交換 | `RealizationComparisonIdempotents/FunctorNaturality.lean`、`ThreeStageProjection.lean`、主Nの `primitiveKaroubiReading` | 任意Θでの主Nと局所三投影の対応へ特殊化する |
| 核と全lift fiberの輸送 | `RR/CSAATRestrictionKernelFiberTransport.lean` の `kernelMulEquiv`、`fiberEquiv`、`fiberEquiv_smul` | 主Nと局所正規化の可換squareを証明して渡す |
| Dの一般判定 | `LSR/PermutationRestrictionCriteria.lean`、`FiniteDeterminingComponents.lean`、`FiniteCoherentExtension.lean` | 任意有限頂点集合の生tableを `FiniteReading` と同定する |
| Dの計算 | `LSR/FiniteEffectiveness.lean`、`FinitePermutationExampleCardinality.lean` | 共通読み取りとの一致、計算結果と既存fiberの一致 |
| タグの群・整合族 | `LSR/TagChangeGroupLaw.lean`、`TagChangeFiniteGroupReconstruction.lean`、主Nの `taggedLocalComparison` | operation queryとの一点評価、既存整合族の普遍性、辺なしDへの適用 |
| 一般CS射の有限決定 | `LSR/LensSemanticFiniteDetermination.lean`、`ProtocolObservedFiniteDetermination.lean` | 共通primitive tableによる有限読み取りと既存decoderの可換式 |
| 可逆CS変更 | `RR/FixedFLensGroupConnection.lean`、`FixedFProtocolGroupConnection.lean`、`FixedFSemidirectProduct.lean` | 既存分裂の核と主Nの自己同型の接続、既存作用の局所評価 |
| 追加の再利用可能な成果 | `LSR/SemanticGeneratedComparisonReconstruction.lean`、`RR/FixedFSemidirectProduct.lean`、`GeneralRelativeLens*.lean` | 必要な評価式だけを利用し、固定G-122例と固定CS入力へ戻す |

一般の生成比較についての自己同型回復、FixedFの半直積、相対lensの意味論を再証明しない。これらの一般化をG-124の追加達成条件にもしない。

既存宣言と接続の詳細は[再利用対応表](reuse-map.md)に固定する。以下の作業単位は受入責務を表し、単位内の全定理を新設する指定ではない。

## 2. 構成上の選択

| 点 | 採用する設計 | 理由 |
| --- | --- | --- |
| 底投影 | `geometryProjection`でcoreを取り、`packageProjection`まで合成した `crossStageProjection` を底固定条件に使う | G-122の既存bottomは `ExtractionInstance` への写像。core全体の固定はこれより強い |
| 三投影の実装 | 保持するprimitive fieldと型依存先を選び、その部分だけを組み立てる | 完全実現の逆関手を通すだけでは局所データからの構成を示さない。三つの汎用表示言語を新設する必要もない |
| 正規化の対象 | 任意のKaroubi対象を運ぶ一般結果と、既存admissibilityの下のcanonical正規化を分けて構成する | `geometryNormalizationFunctor`はadmissible full subcategory上で定義される |
| タグ読み取り | `taggedIdentityOperation A`に対する `upper.operationMap` のBool成分を読む | source-choice族のlower `base` はすべて恒等。元設計§8.2の「source-action成分」をlower source写像として実装すると分離できない |
| Dの読み取り単位 | 頂点ごとの `Perm(K)` と、一点対ごとのprimitive graph queryの対応を明記する | 任意の無限Kでは、一つの置換は有限個のgraph queryでは一般に決まらない |
| 可逆CS変更 | 既存sectionと半直積によりvisible変更と核を分け、核を主Nで読む | visible変更を保った群構造と添字移動は既存実装で与えられる。新たな再添字付け対象・関手を必須にしない |
| 実効性 | 明示列挙・等号判定・元の操作評価からプログラムを構成する | `Finite`からの古典的列挙選択と、入力として与えられた計算用列挙は役割が異なる |

## 3. パートIII：Cを閉じる

### III-1. 底・観測・係数を局所データから投影する

各 `Θ` と `j ∈ {bottom, observation, coefficient}` について、投影先の圏 `B^j_Θ`、意味側の `P^j_R : R_Θ ⥤ B^j_Θ`、局所側の `P^j_M : M_Θ ⥤ B^j_Θ` を構成する。投影先の対象・射は保持したデータとその保存則で定義する。完全幾何へ持ち上がることを投影先の条件にしない。

`P^j_M`は `localObjectTable` と `localHomTable` の成分選択から作る。底には `IndependentCoreTableAssembly.finiteExtractionEquiv` と `IndependentGeometryHomPrimitive.PackageAssembly.lower`、係数には `Coefficient.assemble`、観測には既存 `Context.assemble`・`Observable.assemble` とrestriction自然性のAPIを使う。完全な `assembleObject` / `assembleHom` を定義の経路に置かない。補助invariant witnessに関する選択独立性は `InvariantWitness.retained`・`point`・`auxiliary_choice_independent` を適用する。新規部分は投影先の圏、これらの成分からの関手、および主Nとの自然同型である。

| 投影 | 保持するもの | 同定先 |
| --- | --- | --- |
| 底 | extractionの原始データ、source map、pointed Atom作用と元の保存式。geometryではcoreへの中間投影も保持する | geometryでは `geometryProjection ⋙ packageProjection`。admissible対象では `rawGeometryBottomProjection`。CSでは `CSAATArchitectureObjects` のextraction doctrineと全Homのsource map |
| 観測 | context、順序・restriction、observable環と点評価、Support/Axis/Observable、元の射の作用 | contextの変化とrestriction自然性を持つ圏。representative方式の選択restrictionとexplicit方式のactual context-actionをそれぞれ保持する。CSではget/観測squareと既存の観測reader |
| 係数 | 係数carrierと環演算、係数graphからの一方向の環準同型 | `CommRingCat`。CSの既存AAT接続では固定された `ℤ` と恒等写像 |

観測対象の型を形成するarchitecture object等も依存先として保持する。観測を一つの集合や単なる族tagへ落とさない。射の合成はcontext作用を合成し、その後で各fiberの写像を再添字付けする。

CSの底の対象は、それぞれ `lensAATExtractionDoctrine X` / `protocolAATExtractionDoctrine X` と選択source `.point` の組とする。射は `lensAATExactDoctrineHom` / `protocolAATExactDoctrineHom` と `.point` の保存である。既存の恒等・合成の式、およびstate sourceにおける元の状態写像の評価をそのまま使う。局所側ではcarrierの点graphから役割付きsourceとその写像を組み立てる。この構成は非単射な状態写像にも適用する。

CSの観測投影先も具体化する。lensでは `get : Carrier → View` とget-squareを持つ `Type` 上のslice、protocolでは商経路上のstate functorから固定observation functorへの自然変換を対象とするsliceを使う。局所側ではget点評価、またはstate/edge/observe点評価から直接構成する。後者のpath作用は既存の生成辺からの拡張を使う。三投影のために完全なCS実現のassemblerを経由する必要はない。

証明する式は、同じ投影先への自然同型

\[
  \eta_j : P^j_M\circ N_\Theta \cong P^j_R.
\]

各componentの評価、射の自然性、係数写像、両geometry方式とCSのnative readerとの一致まで与える。投影先の構成に付随するcanonicalな同型がある場合は、その共役を底固定条件の比較にも明示する。

受入条件は三つの自然同型と元の評価式であり、`P_M := N^{-1} ⋙ P_R`という定義だけでは満たさない。

### III-2. 正規化、Karoubi/Arrow、任意比較の全群

一般の `Kar(N_Θ)`、`Arr(N_Θ)`、`Kar(Arr(N_Θ))` にはmathlibの `functorExtension₂`、`Functor.mapArrow` とG-119の `karoubiArrowMap`・`arrowKaroubiMap` を適用する。交換・自然性・単位・合成は `karoubiArrowNaturalityIso` と既存評価補題を使う。nativeの三段投影は `ThreeStageProjection` にあり、固定G-122の主NによるKaroubi評価も `primitiveKaroubiReading_*` にある。残るのは任意Θと新しい局所三投影を結ぶ評価式である。

canonical正規化では、既存 `CanonicalObjectNormalizationAdmissible` の内容を局所primitive条件へ展開し、その条件とnative条件の対応を証明する。これによって対応するfull subcategoryへNを制限する。全Rの射に新しい条件を追加しない。

局所projector `e^M_X` はnormalize/object formation等の点値から作り、native projectorについて

\[
 N(e_X)=e^M_{N X},\qquad (e^M_X)^2=e^M_X
\]

を証明する。既存の吸収式 `e_Y f e_X=f e_X` を局所式に接続し、正規化後の射を通常の合成記法で `f e_X` とする。正規化後の恒等は `e_X`。一般射について `f e_X=e_Y f` を新たに要求しない。taggedのexplicit normalizationは既存の構成と生成則をそのまま対応させる。

任意 `c:X→Y` には

\[
 \Phi_c:\Gamma_c\cong\Gamma_{N(c)},\qquad
 (u,v)\longmapsto(Nu,Nv)
\]

を `generatedArrowComparisonMulEquivOfFullyFaithful` と、主同値から得たfull faithfulnessで得る。この既存宣言には全射性と逆写像が含まれる。局所側の `Aut` は既存 `M_Θ` の局所Homと逆Homでできている。新たな全比較群輸送の一般証明を作らず、既存の `generatedArrowComparison_source_compatibility` と、同型比較の場合の `generatedArrowComparison_section_compatibility` を用い、主Nの点評価を追加する。

さらに、両端自己同型の評価、三投影、指定許容部分群、底固定部分群について可換式を証明する。部分群の保存・反映を「Nは同値だから」で省略せず、III-1の自然同型を使用する。

G-120には準同型・部分群を同じ同型で運び、

\[
 f^{-1}(B)=A\iff\ker f\le A\ \land\ f(A)=B\cap\operatorname{range}(f)
\]

と、liftの存在判定、存在する各fiberの核作用、全射の場合の短完全列を対応させる。一般の比較cに対してsectionや全射性を追加しない。

群論部分は `GroupHomRestriction` の既存定理、指定部分群・観測図式の輸送は `ObservationEquiv` の `mem_compatible_iff`・`kernelEquiv`・`compatibleKernelEquiv`・`fiberEquiv` を使う。AAT側で追加する責務は、同型と投影から可換squareと部分群のmap等式を証明することにある。

### III-3. primitive kernelとG-122の三場合

固定する入力は `finiteAxisFoldBCDatumSquare`、cell `second`、係数 `ℤ`、同じ `finiteAxisFoldFixedCoefficientGeometryFamily`。`IndependentAATPrimitiveReconstruction`のoriginal/direct/via-base対象、二つのcochain、`barAlpha/barBeta/barE/barD`を直接使う。

これらの生成射の点評価、`barBeta`の因子分解・projectorの冪等性・定数cochainでの等式、Karoubi対象とその主Nでの評価は既存宣言を引用する。旧twisted座標から主NのArrowへ入る `finiteAxisFoldTwistedComparison`、その左右評価、`read_raw`、`multiply` も既存経路として使う。

正規化前後の群同型について

\[
 \Phi_{\mathrm{norm}}\circ\nu=\nu_{\mathrm{loc}}\circ\Phi_{\mathrm{raw}}
\]

を証明する。`ν_loc`はIII-2の局所正規化から構成する。次の二群を別々に扱う。

- `K_res = ker(Γ_c → Γ_normalized)`：比較squareを保つ群に制限した核。
- `K_amb = ker(Aut(X)×Aut(Y) → Aut(normalized X)×Aut(normalized Y))`：両端自己同型群全体の核。

局所kernelの条件は、局所forward/backward Homの逆式、比較square（restricted側）、正規化後の各点値がKaroubi恒等と一致する式である。`FullKernel`やnative自己同型をprimitive値として格納しない。`K_res ≃* K_res,loc` とambient側の同型には `RestrictionKernelFiberTransport.kernelMulEquiv` を使う。新規部分は局所kernel条件の独立な定義、上の可換square、および二核の包含の局所評価である。

既存 `G122FullComparisonKernelDecomposition.FullKernel` は制限準同型の全核である。この「全核」をambient核と同一視しない。局所表示の全元性は、任意の既存核の元のreadと、任意の局所核の元のassemblyの両逆で証明する。特殊なcarrier置換による有限分類を追加課題にしない。

`G122FullComparisonTwistedGroup`のsectionと座標式

\[
 r=s(\nu r)k,\qquad k=s(\nu r)^{-1}r
\]

を局所側に運ぶ。積は既存の右作用・opposite規約を保ち、第二のnormalized座標による共役を含める。全lift fiberには `RestrictionKernelFiberTransport.fiberEquiv` と `fiberEquiv_smul` を使い、自由推移性と一意なkernel変位は同モジュールと固定G-122の既存定理を適用する。

| 固定する場合 | 同じ局所表示から回復する結論 |
| --- | --- |
| `initialRawDefectCochain` の `barBeta` | 元の生成式、projectorによる因子分解、非可逆性と `barAlpha` との差、元の比較squareと該当するG-120判定 |
| 定数 `1` cochainの `barBeta` | 同じ幾何と両端の同定、`barBeta=barAlpha`、その同型に対する既存sectionと底・係数成分 |
| `barAlpha` とcanonical正規化 | 元/正規化後の全比較群、底固定部分群、section、分裂短完全列、restricted/ambientの二核、全lift fiber |

`G122RestrictedAmbientKernelSeparation`の `ambientElement` がrestricted核の像に入らないこと、およびその元が底・係数を固定することを、局所側の同じ元で再現する。非可逆な第一の場合へ同型比較用の共役sectionを適用しない。Cの各箇条書きは、適用される仮定と既存宣言を三場合ごとに対応表へ載せる。

## 4. パートIV：D・Eと主定理を閉じる

### IV-1. 同じ有限読み取りとDの判定

`FiniteReading.Separates`、`Extends`、`Determining`、`EffectivenessProgram`、`Effective`を共通の定義として維持する。主NのHom queryはすでに `ULift Bool` を値に持つため、Hom用に別の有限決定性の定義を作る必要はない。

主Nを使う各適用の指定読み取り `r_i` と共通primitive tableについて、全対象射fで

\[
 r_i(f)=\operatorname{decode}_i(\operatorname{localHomTable}(Nf))
\]

を証明する。依存する値は既存protocol方式の役割付きsigma型で扱い、tag一致を独立な局所条件にする。有限値を扱う場合は、decodeに必要なprimitive queryの有限集合と評価の一致も与える。

一般判定は任意の `Q=(V,E,s,t)`、`K`、`H≤Aut(Q)` と任意の固定visible変更 `u∈H` に独立に量化する。`[Nontrivial K]` がGOALの `|K|≥2` に対応する。全V・E・Kの有限性や、任意Qの主Σへの埋込みを一般判定の前提にしない。Eの適用で、指定された操作系と主Nの読み取りを接続する。

`S : Finset V` に対し、

\[
 \operatorname{Coherent}_S(\varphi)
 \iff \forall e,\ s(e),t(e)\in S\Rightarrow
                  \varphi_{s(e)}=\varphi_{t(e)}
\]

という既存の `FiniteCoherentExtension.EdgeCoherent` を使う。生頂点tableと成分族の同値 `componentFamilyEquivCoherentVertexTable`、`PermutationRestriction.restrictPreservingChange_injective_iff_meetsEveryFullComponent`、`restrictPreservingChange_surjective_iff_retainsFullConnectivity`、`hasFiniteDeterminingPreservingRestriction_iff` を用い、一般Qのまま `FiniteReading` のFinset表現へ運ぶ。

1. `Separates(S) ↔ S` が全成分と交わる。
2. `Extends(S) ↔` 同じ全体成分にあるSの二頂点が誘導graph内でも連結。
3. `∃ finite S, Determining(S) ↔ Finite(π₀(Q))`。各成分から一頂点を選ぶ構成を含める。

この読み取りは頂点での `Perm(K)` 値を読む。Kが無限の一般判定でも有効である。一つの置換を有限個のBool graphセルで決定できるとは結論しない。有限Kでは一点対graphの有限tableとの同値を別途与える。

実効性には `[Fintype V] [DecidableEq V] [Fintype E] [Fintype K] [DecidableEq K]` と、Sの判定・元の操作評価を入力として固定する。整合性は実際のretained edgeで判定する。`permutationEffectivenessProgram`の正確な読み戻しには `RetainsFullConnectivity Q S` を渡し、上の延長判定に対応させる。有限性だけから、延長条件を満たさないSでの成功を主張しない。

この条件は新しい一律の制約にせず、Dの延長判定の右辺として明示する。成分代表を選んだ決定集合ではその条件を構成から証明し、有限例でも具体的なSから放電する。区別・延長・実効性はそれぞれの定義と証拠を持たせる。「別個の定義」を三性質の論理的独立性という主張に読み替えない。

プログラム本体、拒否・読み戻しの証明は `permutationEffectivenessProgram` をそのまま使う。出力型とprojection fiberの同値、Bool lensの2元fiber、protocolの4元fiber、および `(card K)!^(card π₀(Q))` は `FinitePermutationExampleCardinality` の既存宣言を参照する。有限graphのprotocolには既に `FiniteReading` 上の区別・延長の両同値と代表点による決定集合がある。一般Dへ接続するときは、その有限graph仮定を引き継がず、上記の一般定理からFinset表現へ移す。

### IV-2. タグ族：operation読み取り、逆極限、非区別、flip

`Ω := ArchitectureObject FiniteModel.carrier`、`T_χ`は既存の任意source-choice自己同型とする。`χ`の読み取りは

\[
 \chi(A)=\bigl(T_\chi.\mathrm{upper.operationMap}
                       (\mathrm{taggedIdentityOperation}\ A)\bigr).2.
\]

共通Homの `.operation A A A A` のpoint graphからこのBool値を読む。false-tagged identityがtrue-tagged identityへ送られる一点対を使い、`taggedSourceChoice_read_point`と既存readbackの一致を証明する。`.source` queryで代用しない。

既存 `taggedSourceChoiceGroupEquiv` と `taggedSourceChoiceSubgroupMulEquivCoherentFamily` を使う。有限tableのrestriction、`CoherentFamily.value`、singleton assemblyと両逆、群構造は実装済みである。追加はこれらを準同型として束ね、任意の群からの整合する射影族に対するliftと一意性を示すことだけである。既存の整合族型を逆極限の担体として使う。

タグtableを主局所Homへ送る経路は既存 `taggedLocalComparison` を使う。整合族bを `TagChangeGeneratedLocalModel.LocalSection` の `⟨false,b⟩` とし、そのHom像をJ(b)とする。`read_assemble`、`taggedInverse_read_normalForm`、`taggedLocalComparison_normalForm_table`、`taggedLocalComparison_read_represented` をrawの場合へ特殊化し、全整合族bについて

\[
 J(b)=N(T_{\operatorname{assemble}(b)}),\qquad
 \operatorname{asm}_N(J(b))=T_{\operatorname{assemble}(b)}
\]

を得る。第二式にはBの既存のHom両逆を使う。これをE1bとBの回復の同定とし、全queryを生成する別のタグassemblerは新設しない。

辺なしのgraph `Q_Ω` と `K=Bool` をDへ代入する。Boolの二つの置換とxorの `C₂` を同定し、`π₀(Q_Ω)≃Ω` を示す。Dの同じ判定から「有限決定集合が存在する iff Ωが有限」を得る。実際のΩでは `architectureObjectInfinite` と、任意有限Sの外の一点だけを反転する既存witnessを接続する。

同じ対象の `t=T_true` とcanonical projector eで `t²=1`、`et=te`、`et≠e` を共通局所Hom等式へ運ぶ。すべての `T_χ` がeと可換だとは仮定しない。逆極限同型、有限非区別、uniform flipの三式を同じ入力・同じ `J,N` について束ねる。

### IV-3. CSの二層、decoderと比較群

一般射については次を接続する。

| 族 | 有限入力と独立な整合条件 | 主Nへの接続 |
| --- | --- | --- |
| lens | `K_X=g_X⁻¹(v₀)` から `K_Y` へのtable。一般射ではすべてのtableが適法 | 既存 `LensRealization.res/ext`、`homEquivFiberMap`、`lensFiberComparisonIso` |
| protocol | 全頂点/状態のtable。tag一致、生成辺square、観測square | 既存 `ProtocolObservedFiniteDetermination.assembleTable`、`protocolObservedComparisonIso` とpoint評価 |

lensでは既存式 `f_h(x)=put_Y(h(put_X(x,v₀)),get_X(x))`、protocolでは `assembleTable` の全商経路への自然性を使う。一般射の区別・延長・実効性は `LensSemanticFiniteDetermination` と `ProtocolObservedFiniteDetermination`、非単射例は主Nの既存宣言を適用する。追加する式は、この小さい値tableと主Nの有限primitive query選択の一致に限る。

両端の有限fiber/stateの列挙があるときは、値tableを全入力・全出力の有限graph tableへ変換し、同じ共通queryへ埋め込む。型参照セルは固定endpointから供給する。意味側の有限決定集合の存在には元の `Finite` を使い、計算結果を主張する場合は列挙を明示入力にする。

主Nのファイルには既に `lensFiniteDecoder`、`protocolFiniteDecoder`、両 `*_retractGeneratedBy`、`*KaroubiEquivalence`、`*KaroubiRestrictionIso`、`*KaroubiArrowEquivalence`、fiber/observed比較自然同型がある。`lensFiniteDecoderFiberIso`・`protocolFiniteDecoderObservedIso`、および旧全体readerへの `cycle79*Primitive*ReadingIso` も使う。それらの圏・関手・自然同型を再作成せず、小さい値tableからのrestriction/extensionの評価を既存図式へ接続する。

可逆変更は既存FixedF接続の入力範囲で、全visible subgroup Hを保持して扱う。`FixedFLensGroupConnection` / `FixedFProtocolGroupConnection` の `mulEquivFollowingGroup` と `FixedFSemidirectProduct.actualEquivSemidirect` を合成する。群Gのprojection pと既存section sについて、destination成分の規約は

\[
 u=p(g),\qquad k=g\,s(u)^{-1},\qquad g=k\,s(u)
\]

である。新規の接続は `ker(p)` と固定visible意味圏の `Aut(X)` の同定、およびその自己同型を主Nで読んだ点評価である。product lensには `LensRealization.productIsoOfEquiv` と既存hidden permutation分類、FixedF protocolには成分置換を各頂点に評価する写像と `execution_naturality` を使う。いずれも逆Homとその両逆の評価まで接続する。

この同定と主Nの自己同型輸送で、既存 `ComponentGroup` を局所Homと逆Homからなる群に移し、`componentAction` も同じ群同型で運ぶ。全群は既存半直積のこの座標変更で得る。追加の汎用的なview/schema再添字付け対象・関手は、固定E2の完了条件には置かない。実際のvisible変更とoperation名の作用は、元の群同型と次の既存評価式で回復する。

protocolのsource頂点での式は既存の規約どおり

\[
 (g_1g_2)_v=g_{1,\,u_2(v)}\circ g_{2,v}
\]

であり、destination成分との変換には `FixedFSemidirectProduct.realize_fiberPerm` を使う。projection・section・核・各fiberの作用は両 `GroupConnection` と `RestrictionKernelFiberTransport` の既存宣言を適用する。Cへの接続は一般の意味保存射の比較群と、上記の核の自己同型輸送で行う。visible変更を含むprotocolのadapter squareは既存 `protocolChangeAdapterSquare_iff_vertices` と `execution_naturality` の式を同じ局所点評価へ写し、添字移動を保持する。

Dの連結成分判定は各固定uのfiberへ適用する。lensは全域putで全fiberが基準fiberに結ばれ、protocolは各成分から一頂点を選ぶ。hidden tableだけで異なるuまで区別できるとは結論しない。

実効性では既存 `LensFiniteDetermination` と `ProtocolFiniteDetermination` のプログラムを使い、一般射の実効性とは入力・整合条件を分ける。protocolの一般射には既存プログラムが必要とする観測値の等号判定を明示する。観測carrierの有限性を追加しない。

計算する出力は既存プログラムが返す実際の意味保存射・追随変更である。その有限読み戻しが共通primitive readingと一致することを証明する。主Nの全queryを扱う古典的なgraph assemblyへ計算可能性を移したとは扱わない。

### IV-4. 同じA–Eを主定理にまとめる

主結果の名前を仮に `aatLocalSemanticReconstruction` とする。構成済みの `Σ,D,Λ,R,M,N` を固定し、次を一つの定理族として出力する。

- 任意Θに対するA/Bの既存全対象・全Hom再構成。
- 同じΘと任意比較cに対する三投影、正規化/Karoubi/Arrow、全比較群と各制限の整合。
- 独立に任意Q・K・H・uへ量化されたDの三判定と、指定有限入力の実効性。
- 固定G-122三場合と、タグ・lens・protocolへの同じ構成の適用。

主定理の引数に、三投影の可換性、kernel同型、E1の主Nとの一致、CSの核・作用と主Nの整合を未証明のfieldとして受け取らない。それらの構成をここまでの証明から渡す。定義・データを返す部分は `def`、等式・判定は `theorem` とし、定理名一個の存在を受入条件にしない。

## 5. 実装順と完了判定

| 作業単位 | その単位で閉じる責務 | 依存 |
| --- | --- | --- |
| III-1 | 既存成分assemblerから三投影を圏化し、主Nとの自然同型を与える | A/B |
| III-2 | 局所正規化と投影squareを構成し、既存Kar/Arr・全比較群・G-120輸送を適用する | III-1 |
| III-3 | 全primitive kernel条件と正規化squareを示し、既存の二核・section・fiber・三場合へ接続する | III-2 |
| IV-1 | 一般Dの既存判定を共通Finset読みに接続し、既存計算・個数を適用する | A/B |
| IV-2 | 既存整合族の普遍性、rawタグ経路の主Nとの一致、辺なしDと既存flipを接続する | III-2、IV-1 |
| IV-3 | CSの小さいtableと共通queryの一致、既存分裂の核と主Nの自己同型・作用を接続する | III-2、IV-1 |
| IV-4 | A–Eの一括statement、条項・宣言・前提生成元・proof-useの対応、最終監査 | 上記すべて |

III-3までがC、IV-1がD、IV-2/3がEを閉じる単位である。各単位は必要な接続とその評価式まで含めてPRにまとめる。単なるaliasや一方の経路だけのPRを増やさない。

設計を壊す実装を検出する最小例を固定する。

1. タグのlower source写像が同じでもoperation queryが異なる二つの変更。
2. 同じ底を持つ二つの非可逆係数写像を区別する既存geometry例。
3. 正規化後の恒等 `e` とraw恒等の区別、およびambient核の元がrestricted核に入らない固定例。
4. path `0–1–2` の `S={0,2}`：区別は成立し、二端点の異なる値は局所edge条件を満たすが延長不能。
5. 二つの孤立頂点の一方だけを読む例：全tableが延長できるが区別不能。
6. lensのconstant map、protocolの非単射adapter。可逆table用のbijective条件を一般Homへ流用しない。
7. 非恒等visible変更を持つlens、成分を交換するprotocol。visibleを恒等に制限したり、再添字付けを落とした積では回復できない。
8. 有限tableの誤ったtag、生成辺square違反、観測square違反に対する拒否と、成功時の正確な読み戻し。

実装検証は変更した非aggregate fileのfocused check、必要な対象moduleだけの確認、報告対象宣言のaxiom監査、placeholder・Unicode・privacy・import方向の検査で行う。Research全体buildは実行しない。

最終packetは固定headについて、GOALの各条項、同じreader、三場合・三適用の評価、全material premiseの生成元と使用先、検証出力を対応させる。既存A/Bの証拠を再利用し、後続変更との接続を確認する。実行履歴・査読結果はPR/Issueへ、主張と証拠の対応は既存G-124 reportへ置く。

適用する完了規則はactive化時に指定された版の `target-theorem-loop` と `math-lean-review`。標準PRレビュー後に別の最終Math A/B・Lean A/Bの四本を行い、累積A–Eに中心未確認項目がなく、全前提が放電され、四本と統合判定が `No major findings` の場合に `target-theorem-proved` とする。tracking Issueのclose判断はその数学的判定と分ける。

論文への帰結整理では、一般の圏同値・群輸送・逆極限・成分判定と、AATのprimitive評価・三投影・固定G-122の回復・CS二族への具体的適用を区別する。論文や検討ノートの同期編集を証明義務には加えない。

## 6. 設計判断の直接の根拠

以下は冒頭で固定した実装commitへのリンクである。

| 設計判断 | 確認する宣言 |
| --- | --- |
| タグはoperation作用で読む | [source-choiceの構成と読み戻し](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/MandatoryCFiniteReferenceObstruction.lean#L29-L91) |
| 底固定はextractionへの射影で判定する | [rawGeometryBottomProjection](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/FullGeometryNormalization/GeometryBottomQualifiedComparisonGroup.lean#L27-L43) |
| 正規化はadmissibilityと吸収式を用いる | [admissible full subcategoryとabsorption](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalization.lean#L176-L213) |
| CSの底投影は全Homを扱える | [lensのexact doctrine写像](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/CSAATArchitectureObjects.lean#L355-L408)、[protocolの同構成](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/CSAATArchitectureObjects.lean#L725-L782) |
| visible変更を固定viewのHomに直接入れない | [LensInvertibleChangeのget/put式](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/FixedFLensConnection.lean#L29-L43) |
| protocol群の積は添字を動かす | [ProtocolChangeGroupの積](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/FixedFProtocolGroupConnection.lean#L89-L104) |
| 延長条件を実効性の読み戻しへ渡す | [permutationEffectivenessProgram](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteEffectiveness.lean#L133-L159) |
