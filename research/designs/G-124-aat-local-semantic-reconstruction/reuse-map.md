# G-124 パートIII・IV：再利用対応表

対象は[実装設計](README.md)のIII-1からIV-4。参照するソースは `9585e4fcb650928a6adc135e281200de939e20cc` に固定する。既存宣言の型・定義・証明本体に基づき、再利用する構成と追加する接続を定める。

12項目について、既存の構成を再利用する範囲と、同じ主同値Nに対して残る証明を分ける。既存宣言の別名や同内容の新モジュールは成果として数えない。

## 1. 再利用対応表

| # | 設計箇所 | 再利用できる宣言と内容 | 新規に残る接続 |
| --- | --- | --- | --- |
| 1 | III-1 成分assembler | [finiteExtractionEquiv](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentCoreTableAssembly.lean#L109)、[PackageAssembly.lower](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryHomPackageAssembly.lean#L94)、[Coefficient.assemble](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryHomCoefficientLaws.lean#L34)、[Observable.assemble](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryHomObservableReadings.lean#L107)。補助invariantの[選択独立性](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryHomInvariantQuotient.lean#L108)もある。 | 底・観測・係数の投影先の圏と局所関手、主Nとの自然同型。成分の組立て・商のwell-definednessを再証明しない。 |
| 2 | III-2 Kar/Arr・投影 | mathlibの `functorExtension₂`・`Functor.mapArrow`、[karoubiArrowNaturalityIso](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationComparisonIdempotents/FunctorNaturality.lean#L201)、[nativeの三段投影](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationComparisonIdempotents/ThreeStageProjection.lean#L48)、[primitiveKaroubiReading](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3306)。 | 一般Θでの局所三投影と正規化とのsquare。canonical admissibilityとprojectorのprimitive評価。 |
| 3 | III-2 任意比較の全群 | [generatedArrowComparisonMulEquivOfFullyFaithful](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/CSAATFullyFaithfulComparisonTransport.lean#L93)は逆写像・単射・全射を含む群同型。source評価、同型比較のsectionとの整合もある。 | 主Nへの適用、両端点評価、三投影と許容部分群への制限。一般群同型の逆写像を新作しない。 |
| 4 | III-2/3 核・全fiber・G-120 | [kernelMulEquiv](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/CSAATRestrictionKernelFiberTransport.lean#L99)、[fiberEquiv](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/CSAATRestrictionKernelFiberTransport.lean#L123)、同 `fiberEquiv_smul`。G-120の[ObservationEquiv](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/ComparisonInformationLoss/ObservationTransport.lean#L31)にも部分群・核・fiberの輸送がある。 | 主Nおよび局所正規化による可換squareと部分群map等式を構成する。群論的な輸送自体は既存APIへ渡す。 |
| 5 | III-3 固定G-122入力 | 主Nの[固定parameter・三対象](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3071)、[barAlpha/barBeta/barE/barD](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3097)、点評価、因子分解、冪等性、[定数cochainのbarBeta=barAlpha](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3251)、Karoubi評価。 | 三場合ごとの全群・部分群・正規化・二核のprimitive分類への接続。入力と基本生成式は再作成しない。 |
| 6 | III-3 twisted座標 | [finiteAxisFoldTwistedComparison](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3419)は既に旧twisted局所圏から主NのArrowへ入る。左右評価、[read_raw](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3466)、[multiply](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3491)まである。 | 全primitive kernel条件と正規化square。旧 `FullKernel` 座標の全元性だけではprimitive表示の全元性を済ませない。 |
| 7 | IV-1 一般D・計算・個数 | [一般Q/Kの区別・延長判定](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/PermutationRestrictionCriteria.lean#L38)、[有限決定集合の存在判定](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/PermutationRestrictionCriteria.lean#L128)、[componentFamilyEquivCoherentVertexTable](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteCoherentExtension.lean#L131)、[permutationEffectivenessProgram](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteEffectiveness.lean#L133)、[実際のfiberとの同値と個数](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/FinitePermutationExampleCardinality.lean#L37)。 | 一般Qのまま共通 `FiniteReading` のFinset表現へ移す接続。既存アルゴリズム・Bool例・階乗個数を新規成果として再証明しない。 |
| 8 | IV-2 タグの整合族と群 | [CoherentFamily](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteReconstruction.lean#L58)、read/assembleと両逆、[taggedSourceChoiceSubgroupMulEquivCoherentFamily](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteGroupReconstruction.lean#L175)、有限非区別witnessまである。 | 同じ整合族型で群準同型としての射影、任意の整合射影族のliftと一意性。新しい逆極限担体・singleton assemblerは不要。 |
| 9 | IV-2 タグの主NへのJ | [taggedLocalComparison](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L2965)、[taggedLocalComparison_normalForm_table](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3045)、[taggedLocalComparison_read_represented](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3598)。`LocalSection` の `⟨false,b⟩` を既存mapへ渡せる。 | rawの場合への特殊化でJを定め、Bの両逆と同定する。operationの一点query、辺なしD、同じJでのflipとの接続。全queryを作る別のタグassemblerは不要。 |
| 10 | IV-3 CSの有限table | [一般lensのassembleTable](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensSemanticFiniteDetermination.lean#L87)、[一般protocolのassembleTable](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedFiniteDetermination.lean#L228)と区別・延長・実効性。可逆層は `LensFiniteDetermination`・`ProtocolFiniteDetermination` にある。 | 小さい値tableと主Nの有限primitive query選択の一致。一般protocolのassemblerは商経路の自然性まで証明済み。 |
| 11 | IV-3 主NのCS再構成 | [lens/protocolFiniteDecoder](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L2705)、retract生成、Karoubi同値・restriction自然同型、Arrow版。さらに[decoderとfiber/observed経路の自然同型](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3659)、[旧全体readerとのKaroubi整合](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3755)、[同Arrow整合](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean#L3880)もある。 | 有限値tableのrestriction/extensionを既存図式の評価へ接続する。decoder・圏・関手・自然同型の再構築は不要。 |
| 12 | IV-3 visible変更と群 | [lensのmulEquivFollowingGroup](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/FixedFLensGroupConnection.lean#L247)、[protocolの同群同型](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/FixedFProtocolGroupConnection.lean#L245)、両projection・section・核・fiber。さらに[actualEquivSemidirect](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/FixedFSemidirectProduct.lean#L209)、[componentAction](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/FixedFSemidirectProduct.lean#L48)、[adapter squareの頂点判定](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/RealizationReconstruction/FixedFProtocolConnection.lean#L580)がある。 | projection核と固定visible意味圏の自己同型の同定、その主Nによる点評価、既存作用の同じ群同型での輸送。汎用view/schema再添字付け圏を新たな完了条件にしない。 |

## 2. 既存APIによる構成

### タグのJ

`J(b) := taggedLocalComparison.map ⟨false,b⟩` を使う。`TagChangeGeneratedLocalModel.read_assemble`、主Nのnormal-form評価、`taggedLocalComparison_read_represented` を組み合わせる。Bとの回復一致にはBの既存Hom両逆を使う。新たな全query用の組立てと、その全法則の再証明を設けない。

### CSの有限decoder

主Nのファイルにはdecoder本体からretract生成、Karoubi/Arrow、既存fiber/observed経路・旧全体readerとの自然同型まである。残る有限tableの仕事は、どのprimitive queryを読むか、値tableとどう変換するか、その有限読み戻しが既存decoder図式の評価に一致するかである。

### visible変更を含むCS群

固定visibleの意味圏に、visible変更を持つ全群を直接押し込まない。既存分裂 `p:G→H`、`s:H→G` で

\[
 u=p(g),\qquad k=g\,s(u)^{-1},\qquad g=k\,s(u)
\]

とし、核を主Nの自己同型へ接続する。全visible subgroup Hはそのまま保持し、`componentAction` を同じ群同型で移す。protocolの積の添字移動は

\[
 (g_1g_2)_v=g_{1,u_2(v)}\circ g_{2,v}
\]

の既存評価を使う。destination成分への変換は `realize_fiberPerm` にある。kernelとnative `Aut(X)` の同定、逆Homの両逆、主Nによる評価は新規の接続として残す。これを証明せずにE2完了とはしない。

G-122の既存twisted座標は `r=s(νr)k` の規約を使う。CSの上記destination座標と左右を混ぜず、それぞれの既存積・opposite核作用に従う。

## 3. 接続で満たす条件

- **三投影と局所正規化**：nativeの投影や一般Kar/Arrが存在しても、同じprimitive Mでの成分構成と主Nとの自然同型は必要。
- **全primitive kernel**：[全source-kernel分解](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122FullSourceKernelExactDecomposition.lean#L6)は実際の自己同型を座標に持つ。[complete graphによる分離](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122CompleteGraphKernelReconstruction.lean#L6)は任意の独立整合graphの組立てを結論しない。[任意carrierの核部分族](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/9585e4fcb650928a6adc135e281200de939e20cc/research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122ArbitraryCarrierKernelReconstruction.lean#L6)も全核の分類ではない。
- **一般D**：`ProtocolFiniteDetermination` の共通 `FiniteReading` 上の同値は有限graph等を前提とする。任意Q・Kへ量化するDは `PermutationRestrictionCriteria` から接続し、この有限性を持ち込まない。無限Kの置換値一つを有限個のBool queryで決定できるとはしない。
- **タグの逆極限**：整合族の群同型はある。既存担体を用いた準同型のliftと一意性を、逆極限の普遍性として明示する証明は残る。
- **同じ主Nへの接続**：族tagへのdiscrete投影はCの底・観測・係数の三投影ではない。一般geometryだけの比較回復や、単なる `Equiv` は、全Θの `MulEquiv`・部分群・投影squareの代用にはならない。

## 4. 実装する接続

1. III-1/2：成分assemblerからの三投影、primitive正規化、主Nとの可換式。
2. III-3：独立な全primitive kernel条件、正規化square、既存二核・全fiber・三場合の評価への接続。
3. IV-1：一般Dを共通Finset読みに移すadapterと、既存計算結果の読み戻し。
4. IV-2：タグoperation query、既存整合族の普遍性、既存Jとの一致、辺なしDへの適用。
5. IV-3：CSの有限queryと値tableの一致、既存分裂の核と主Nの自己同型・作用の整合。
6. IV-4：同一のA–Eのstatementと、条項・宣言・前提生成元・proof-useの対応。

この範囲では既存定理の接続を中心に実装できる。Cの三投影・正規化・全primitive kernelは独立した構成と証明が残るため、単なる既存APIの別名化では閉じない。
