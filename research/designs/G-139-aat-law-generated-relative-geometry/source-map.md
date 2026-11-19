# 固定target・原始source・仮定の対応

## 固定targetへの対応

| 固定targetの条項 | 紙上証明 | 結論の生成元 |
| --- | --- | --- |
| N1 任意many-sorted意味圏 | [N1.1–N1.3](primitive-semantics.md) | 実際のsort mapと保存式。恒等・合成・termは関数と有限syntaxの帰納 |
| N1 Atom・generic object・opaque・geometry | [N1.3、G-124比較](primitive-semantics.md) | 元のfield、関数graph、既存原始宣言の段階的組立て |
| N2 copying、全環・全Hom・零環 | [N2.1–N2.3](copying-and-totality.md) | basisのコピーとcounit。行ごとの有限冪等元分割 |
| N2 nilpotent lift、量との違い | [N2.4](copying-and-totality.md)、[B1.4–B1.5](descent-and-algebraicity.md) | 冪等元の一意lift、局所split Homのdescent、dual numbersの標準lift |
| N3 全profile、合成、三反例、G-124 query | [N3.1–N3.2](copying-and-totality.md) | 行ごとのsupportと有限和。all-false、identity、合成query |
| N4 任意fiber lens・空view・protocol | [N4.1–N4.2](primitive-semantics.md) | 三lens等式、実際のview/state map、functorと全自然変換 |
| N5 図式・全候補・評価と自然性 | [N5.1–N5.3](primitive-semantics.md) | 頂点・辺・関係、許容規則、固定比較の全field |
| A 任意量・任意Lawの相対Spec | [A1](quantity-and-extension.md) | `Q,ρ,I` を原始式から生成し、評価帰納法から表現同値 |
| A 全代数・線形quantity・QC module | [A2](quantity-and-extension.md) | 環／線形保存のLaw、Symと相対Specの普遍性 |
| B copyingとσの各stack、native基点、全Hom | [B1.1–B1.4](descent-and-algebraicity.md) | QC descent、実際の係数作用、冪等分割の加重和 |
| B 相対Spec、全scheme pullback、自然性 | [B2](descent-and-algebraicity.md) | `Q,ρ,I` の同型によるdescent、各affine上のA1 |
| B 射と対応空間、補集合Law | [B3](descent-and-algebraicity.md) | domain/Law-input map、普遍target quantityによるideal検査 |
| B sheafificationとscalar extension | [B4](descent-and-algebraicity.md)、[P3.2](polynomial-realizations.md) | localizationとstalk、既存APIのflatness・sheaf保存の個別放電 |
| C symbolic coordinateとactual residual、三解釈 | [C1](quantity-and-extension.md)、[P1a](polynomial-realizations.md) | graph、固定native値のtensor、選択された普遍多項式 |
| C 全自然operationと全regular extension | [C2–C3](quantity-and-extension.md) | 普遍tuple、有限単項式supportの全chart、全native一致式 |
| C 無限体・有限体・整数chart | [C3・C3.1](quantity-and-extension.md) | Vandermonde、剰余次数と補間、`2b₂=1` |
| C 有限supportと逆極限 | [C4](quantity-and-extension.md) | zero extensionとrestriction、全座標1の反例 |
| C coherence・普遍残差・零点family | [C5](quantity-and-extension.md) | 普遍tuple上の全係数等式、profileごとの商環 |
| C 三module familyと比較 | [C6](quantity-and-extension.md) | basis評価、双対の比較map、有限projective条件 |
| D duality・frame・生成規則・商stack | [D1–D2](descent-and-algebraicity.md) | snake式からdual basis、各Homの相対Spec、frame torsor |
| D 二つの非有効化・profile判定 | [D3–D4](descent-and-algebraicity.md) | 無限積、無限次元stabilizer接空間、profileの直接計算 |
| P1 独立Sem/RealとAtom残差、全context | [P1–P1a](polynomial-realizations.md) | quotient・全射同値、共通carrierの値graph、点supportの内部 |
| P2 chart・descent・非flat base change・表現 | [P2・P2.1](polynomial-realizations.md) | 生成列の基底open、matrixの逆変換、QC descent、extended ideal |
| P3 reading・自然性・既存API比較 | [P3–P3.2](polynomial-realizations.md) | syntax代入、Law導出、同じ普遍実現と同じ装飾 |
| P4 GL商と生成元忘却 | [P4](polynomial-realizations.md) | 独立実現のframe、Surj行列open、実際のinertia |
| P5 全指定証人 | [証人](witnesses.md) | W1–W3・W5–W8の具体的原始入力、matrix、kernel、残差 |
| P6 図式と評価の特殊化 | [P6](polynomial-realizations.md) | N5の全dataの成分式化、指定有限還元の両方向の導出 |

## 原始sourceと既存Lean宣言

ここでの役割は、既存の語彙・原始入力・証明済み部分を確定することである。新しい紙上定理を、これらの宣言がすでにLeanで証明しているとは表示しない。

| source | 実際に使う内容 | 本稿で追加する内容 |
| --- | --- | --- |
| [Atom](../../../Formal/AG/Atom/Atom.lean)、[Configuration](../../../Formal/AG/Atom/Configuration.lean)、[ObjectAlgebra](../../../Formal/AG/Atom/ObjectAlgebra.lean) | 五座標、三つのconfiguration relation、`ConfigurationHom` の実際の保存条件 | N1の意味圏への解釈、同じ条件の対象・射の読み戻し |
| [ArchitectureObject](../../../Formal/AG/Atom/ArchitectureObject.lean) | `StructureMaps`、`SelectedQuantities` と各選択値 | 実際の関数による新しい射、型・値への忘却 |
| [GeneralRelativeLens](../../lean/ResearchLean/AG/RealizationReconstruction/GeneralRelativeLens.lean) | `productEquiv`、`normalForm`、`productMap` | copyingへの輸送、係数・descentとの比較 |
| [IndependentCarrierGraphReadings](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentCarrierGraphReadings.lean) | `IsTyped`、`IsTotal`、`compose_finite_support` | 同じqueryに対する冪等係数表示、全profileと非一様性 |
| [IndependentAATPrimitiveReconstruction](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean) | `Parameter`、`NativeCategory`、`LocalCategory` の各family | N1の宣言と係数familyを区別した比較 |
| [IndependentGeometryPrimitiveAssembly](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryPrimitiveAssembly.lean) | `foundation`、`dependent`、`stages`、`assemble` | 同じfield順のmany-sorted解釈 |
| [IndependentGeometryCategoryReconstruction](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryCategoryReconstruction.lean) | `representativeReadingHomEquiv`、`explicitReadingHomEquiv` とそのidentity/composition、両modeのread/assembleとequivalence | 係数化後のnative回復、全環の追加Homとの区別 |
| [IndependentGeometryHomNativeFullRecovery](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryHomNativeFullRecovery.lean) | `localRepresentative_assemble`、`localExplicit_assemble` | 元の係数map・raw data・全context actionを落とさない比較 |
| [IndependentLensPrimitiveReconstruction](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentLensPrimitiveReconstruction.lean)、[IndependentProtocolPrimitiveReconstruction](../../lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentProtocolPrimitiveReconstruction.lean) | 実際のstate/view、path、自然変換のreadingとassembly | 任意signatureへの組込みとcopying・σの各比較 |
| [Equation.Basic](../../../Formal/AG/Equation/Basic.lean) | `violationCoordinate`、`equationResidual`、全context・全Atomでの `EquationLawful` | raw graph decode、普遍残差と評価残差の別々の系、同じ入力での充足同値 |
| [Context](../../../Formal/AG/Site/Context.lean)、[ContextCategory](../../../Formal/AG/Site/ContextCategory.lean) | `IsRestriction`、`contextMorphismPreorderCategory`、実際のsupport map | 全contextの点supportから `U_W` と係数restrictionを生成 |
| [StandardScheme](../../../Formal/AG/LawAlgebra/StandardScheme.lean) | scheme・decoration・atlasの格納型。表現同値を入力とする `EquationObservableRealization` 等 | P2で表現同値とatlasを構成。入力fieldの射影を証明の代わりにしない |
| [StandardSchemeCoefficient](../../../Formal/AG/ReadingFunctoriality/StandardSchemeCoefficient.lean) | `baseChange`、`baseChangeUnderlyingIso` とflat/sheaf仮定 | 同じ装飾付き入力での比較、適用する係数変更での仮定放電 |

## Material premiseの所在

| 条件 | 役割 | 本稿での扱い |
| --- | --- | --- |
| 小さい集合・有限arity・有限syntax | 量化する原始入力 | 無限個のsort、変数、Lawは保持。各式のみ有限 |
| 既存relation、domain、選択値 | 原始入力 | 保存式をそのまま使う。relation反映や選択witnessを追加しない |
| copyingの局所split性 | Bの構成するstackの対象条件 | N2のsplit対象からdescent formsを作り、全Homを降下 |
| nativeのmodule作用と式 | σ経路の原始入力 | pure tensorと有限式で生成。任意関数のregular extensionはC3で分類 |
| quantity domainとLaw入力の輸送 | B3で全quantityの射を得る条件 | 原始sort mapとterm式から検査。失敗時もnative射と対応空間を保持 |
| dualityのevaluation/coevaluationとsnake | Dの明示された十分条件 | 有限projective性・frameをここから導出 |
| Markingとopen overlap | scheme化の条件 | 全射性でinertia消滅、選択列とdeterminantでopen overlapを構成 |
| finite presentationとLawの有効な有限還元 | P6の有限化経路の条件 | 有限構文のcompilerと両方向の解同値を証明。一般familyはN5に保持 |
| 既存APIのdecorated入力 | P3.2に明示された比較範囲 | 普遍実現・選択chartと同じ入力だけを比較。全contextのaffine性は要求しない |
| flatness・sheaf保存 | 既存APIへの適用条件 | finite projective係数変更では全limit保存から放電。P2の表現自体は非flat射にも自然 |
| connectedかつ非零 | 一個の係数環からnative Homを回復する十分条件 | N2の一般全Hom分類とは別。零環と非連結の挙動も証明 |
| 非零基礎環 | Dの無限familyの非有効化例 | 零環は空schemeとなることを明示 |

## 標準数学の使用箇所

可換代数の多項式環・Sym・商・局所化の普遍性、有限projective moduleの基本性質、およびschemeのopen接着を通常の標準定理として用いる。descentや商の存在には次の一次資料を使い、本稿で入力を構成してから適用する。

| 標準結果 | 使用箇所 |
| --- | --- |
| [QC moduleとすべての射のfpqc descent, 023T](https://stacks.math.columbia.edu/tag/023T) | B1.2、B2、P2.1、P4のmoduleとmapの降下 |
| [相対Spec, 01LQ](https://stacks.math.columbia.edu/tag/01LQ) | A2・B2のQC代数から相対affine schemeへの構成 |
| [Dualityとfinite projective, 0FNJ](https://stacks.math.columbia.edu/tag/0FNJ)、[局所有限自由性, 00NX](https://stacks.math.columbia.edu/tag/00NX) | D1。本文にもdual basisの生成を記載 |
| [Grassmannian, 089T](https://stacks.math.columbia.edu/tag/089T) | P2の生成列からの基底open。本文でoverlapと被覆を証明 |
| [商stackの代数性, 06PI](https://stacks.math.columbia.edu/tag/06PI) | D2・P4。有限積GLのsmooth作用groupoidを構成して適用 |
| [無限積の反例, 078E](https://stacks.math.columbia.edu/tag/078E) | D3の独立なline quotient族 |
| [Isomの局所有限型性, 04XR](https://stacks.math.columbia.edu/tag/04XR) | D3の無限自由moduleのstabilizerによる反証 |

この依存は紙上証明の標準定理への依存であり、Leanライブラリへの実装済み対応を意味しない。新規形式化では、上の各構成とsource対応を同じ量化・同じ残差・同じ全Homで実装する必要がある。
