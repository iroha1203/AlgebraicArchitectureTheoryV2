# n1014: 独立な実現と有限表示からの再構成 — G-123の設計

[n1010 §6・§7.2・§9.5](n1010_aat_post_annapurna_conjectures_research_plan.md) のS5を、
G-123として設計する。[n1012](n1012_aat_unified_theory_foundations_paper_plan.md) 第8章の
到達点は、実現と比較の圏を再構成し、第7章の比較を保つ変更の分類を表示側から回復することである。
CS側の独立な意味、二つの実現圏・表示圏・decoderの具体案、共通の変更分類は
[n1015](n1015_aat_reconstruction_cs_correspondence_design.md) に置く。
研究目標と完了条件は
[G-123のdraftカード](../../research/goals/G-123-aat-realization-reconstruction.md) にまとめる。
本ノートは構成の選択理由と、入力・表示の具体化に必要な検討を扱う。

## 1. 論文の到達点と設計基準

### 1.1 論文の結びから定める到達点

G-123が担う主結果の目標を次に置く。

> 明示したAtom・Law・operationのデータ条件を満たす実現の族について、対象と比較の圏を
> 有限表示から再構成する。その対応は底への投影と観測に整合し、比較を保つ変更の分類を
> 表示側から回復する。

ここで有限に記述する成分と、係数環等のパラメータは、主定理の入力として明記する。
再構成する実現の族と許容射は、表示とは独立した意味上の条件から定める。
具体的な実現圏・表示圏・decoderとデータ条件をG-123のAで構成し、
その同じ入力族についてB以降を証明する。完全幾何に対する定義の具体化は§6.2に示す。

論文の結びは、次の三つの結果を同じ対象と写像について接続して得る。

| 結果 | 本文で明らかになること | G-123の構成 |
| --- | --- | --- |
| 保持する情報の特定 | 対象への作用が一致しても、operationへの作用が異なる変更がある | §3の分離例と、operationの同一性を保持する実現の定義 |
| 実現と比較の再構成 | 表示から対象・射・比較の可換性を保存・反映し、実現の族全体を回復できる | §4の独立な構成、四つの性質の証明、二つの圏同値 |
| 変更の分類の回復 | 比較を保つ可逆変更、変更の持ち上げ、その選択の自由度を表示側でも同じように分類できる | §5の底・観測との整合、比較群、section、核とlift fiberの対応 |

この接続によって、n1012の中心の問いである「診断の一致と、構造の比較や比較を保つ変更の
成立はどう違うか」に、表示からの回復まで含めて答える。一般再構成原理の仮定を
Atom・Law・operationの具体的なデータから証明する部分が、AAT固有の数学的な仕事になる。

### 1.2 対象範囲を選ぶ基準

有限carrier版とパラメータ相対版は、§1.1の到達点に照らして評価する。
次を満たす対象族を主定理の対象として設計する。

1. 対象族は、指定したデータ条件を満たす任意の入力を扱う。構成と証明は、その族の中の
   対象・operation・比較について一様に与える。
2. 対象族に、G-122の生成比較と変更の分類を接続する。§5で固定する三つの場合の
   端点・比較・section・核を同じ対応で運び、各入力がデータ条件を満たすことを証明する。
3. operationの同一性と比較の可換性を保持する。分離例は、保持する各データの役割を
   確かめるために使う。
4. n1012のCS適用に、独立した入力構成と対応命題を与えられる条件を選ぶ。
   論文では、設計モデル間の対応とサービス・クライアント間の対応について、
   比較を保つ可逆変更を同じ定理で分類し、共通に得られる条件または帰結を示す。

有限carrier版でも、これらを満たす対象族について一般定理を得れば、論文の主結果になり得る。
パラメータ相対版では、無限の基礎データの上で有限な生成データを使い、同じ到達点を目指す。
どちらを採る場合も、入力族と許容射を固定するときに、上の各接続が成立する範囲を示す。
各接続で用いる入力・写像の数学的な定義を、G-123のactive化までに具体化する。
再構成とその接続を証明する仕事は、G-123の実行に置く。

### 1.3 既存成果の使用

既存の成果と新しく構成するものを分ける。

| 項目 | 既存の根拠 | G-123での使用 |
| --- | --- | --- |
| 比較と冪等完備化の交換 | G-119の `karoubiArrowEquivalence` | 実現の再構成から比較の圏の再構成へ進む |
| 有限decoderの射の表示可能性 | G-121の固定code間の分類、有限carrier版、可算構文の非全射性 | 表示する射と、有限に符号化するデータを決める |
| 完全幾何の正規化と生成比較 | G-122の `canonicalGeometryNormalization`、実生成 `barAlpha`・`barBeta` | 再構成で保持する射と投影を特定する |
| 比較群、section、核、lift fiber | G-120・G-122の全群版と底を固定する版 | 表示側と実現側で同じ変更の分類を得る |
| 操作の情報を残す必要性 | G-117の `taggedOperationPackage` と既存のoperation-map計算 | 対象だけを読む関手の非忠実性を新しく検査する |
| 一般再構成原理 | n1010 (15)、mathlibのKaroubi関手延長 | AATで個別に証明する四つの性質をまとめる |

G-119〜G-122の受理済み定理と、以下の新しい構成・定理候補を同じ証明状態として扱わない。
G-123のLean実装と完了判定はこれから行う。

## 2. 有限性は成分ごとに指定する

`ArchitectureObject U` はconfigurationに加えて、`StructureMaps` と `SelectedQuantities`
という型、およびその選択値を持つ。`U.Atom` の有限性だけから、この対象型全体の有限性は出ない。
また `OperationReading.Op A B` は、configuration homを実現するoperationの型であり、
そのconfiguration mapの単射性は要求されていない。

従って表示の設計では、少なくとも次の成分を区別する。

| 成分 | 決める内容 |
| --- | --- |
| Atomと有限Source | Atom carrier、有限Source table、normalize、抽出、選択点 |
| 対象 | configuration、構造・量のreading、対象間の写像 |
| operation | 両端、operationの同一性、configurationへの実現、operation間の写像 |
| Law・invariant・signature | 添字、評価、残差、選択条件、写像と評価の整合 |
| 完全幾何 | context、Support・Axis・Observable、読取りと制限、coverageとoverlap |
| 係数・raw data | 係数環とその写像、座標・関係式、restriction、raw compatibility |

有限carrier版では、有限とする各carrierをこの表に沿って列挙する。
パラメータ相対版では、構文の外に固定する型・値・写像を列挙し、decoderがどのパラメータを
読むかを示す。いずれも「有限な記述」を構文木の大きさ、tableの大きさ、パラメータの情報量に
分ける。特定のsemantic射を表すために、その射全体を新しい定数として加える方法は採らない。

### 2.1 二つの設計案

次の二案は排他的ではない。有限にするcarrierと、構文の外に置くパラメータは別々に
指定できる。n1010 §6.1は全packageの再構成を前提にせず、Atom・Law・operation等の
具体的なデータ条件で対象範囲を固定する方針である。従って「パラメータ相対版」を
選ぶことと、「G-122の一般入力と全変更をそのまま再構成すること」は別の判断になる。

| 項目 | 有限carrier版 | パラメータ相対版 |
| --- | --- | --- |
| 対象範囲 | 列挙した対象・operation・添字carrierの有限性をデータ条件にする | 一般のcarrierを保持し、表示に使用するパラメータと構文を別に固定する |
| 有限であるもの | 対象・射を記述するtable。係数等の扱いは別途指定する | 各表示の構文木・table・パラメータ参照の個数 |
| 充満性の仕事 | 任意の許容射の各成分を同じ端点のtableへ符号化する | 任意の許容射を、固定したパラメータと生成規則から有限な式で構成する |
| G-122との接続 | 実際の生成対象・射・section・核の元が、そのデータ条件を満たすかを個別に証明する | G-122の一般入力と変更を扱えるだけの構文があるかを証明する |
| 設計で特定する事項 | 有限にする各carrierと、その条件の下で許される射 | パラメータの型と由来、式の生成規則、評価、式の等号、許される射 |

「全成分が有限」という一括した制限は採らない。例えばG-122の固定例の係数は `ℤ` であり、
有限個の座標や関係式を用いることと、係数環を有限集合にすることは異なる。
有限carrier版でも係数をパラメータとして残す設計は可能である。

パラメータ相対の有限性の基本例は `a + bX + cX²` である。式は有限で、
`a,b,c` の所属する係数環は無限でもよい。同様に、Atom carrierやreadingを固定した上で、
有限個の生成操作から作る射を考えられる。その場合も、実現側の任意の許容射がその形で
書けることは別の定理であり、構文の定義から自動的には従わない。

射まで有限表示する基本例は、固定した環 `k` 上の有限自由加群間の線形写像
`k^m → k^n` である。`k` は無限でもよく、写像は `n × m` 個の係数からなる行列で
表される。各標準基底の像が任意の線形写像を一意に定めるため、有限な行列から
対象間の全線形写像を回復できる。この例はパラメータ相対な有限表示の説明であり、
AATの対象やoperationが有限自由加群であるという主張ではない。
AATでは、これに相当する生成データと、許容射をその上の有限なデータから復元する定理を
具体的に構成する必要がある。

### 2.2 一般版を選ぶために必要な確認

G-121は、可算な構文から固定された無限carrierの全自己同型を列挙するdecoderの
非全射性を証明している。またAtomが有限でも、上段の対象型とoperation型は一般に有限に
ならない。従って、G-122の一般性を保つ設計では、必要な情報をどの成分で保持するかを
個別に説明する必要がある。

パラメータ相対版を主案として採用するには、次を具体化する。

1. 実現 `R` の対象・射をAtom・Law・operation等のデータから独立に定める。
   許容射の条件にも、decoderの像や「この構文で書けること」を用いない。
2. パラメータ、構文、評価を定め、任意の完成射を一つの定数として受け取る構成と区別する。
3. G-122の実生成対象・射と、比較群・section・核の元について表示を構成する。
4. それらの例示に加え、固定した対象範囲の全称的な充満性・忠実性・冪等完備性・retract生成を証明する。

一般版がこの条件を満たすことは、新しく検証する研究課題である。パラメータを導入した
ことだけを理由に、G-122のすべての対象・変更を再構成できるとは判断しない。

### 2.3 具体化した二つの表示

CSへの適用を、次の独立な実現と構文から設計する。正確な法則と写像はn1015に定める。

| 具体案 | 実現の意味による対象条件 | 有限表示とdecoder | 回復する射 |
| --- | --- | --- | --- |
| `R_lens(V)`、`P_lens`、`F_lens` | 全域get/putの三法則と、基準viewのfiberの有限性。view `V`は一般の集合 | 有限補完tableから積lensを生成する。任意の実現を`c↦(get(c),put(c,v₀))`で回復する | getとputの両方を保つすべての射。可視変更に相対的な版では、可視変更と有限fiberの写像で記述する |
| `R_proto(Q,L,O)`、`P_proto`、`F_proto` | 操作の経路圏の有限carrier値関手と、観測への自然変換 | 生成操作のtableを経路に沿って評価する。経路等式と観測保存を課す | 全操作と観測を保つ自然変換。生成辺の可換式から全実行経路の可換式を導く |

各decoderについて、同じ端点の符号化と射の等号、冪等射の像を用いる証明案を与えた。
両案ともdecoderは既に圏同値となる見込みであり、Karoubiによる再構成はその帰結である。
これらは完全幾何の`R`を固定したことを意味しない。そこへの対応は§6で別に指定する。

## 3. operationを残す実現の分離試験

n1010 §7.2の試験には、G-117の既存の端点依存flipをそのまま使わず、
全端点で一様にBoolタグを反転する自己同型 `t` を構成する。
`e` を同じ `taggedOperationPackage` のcanonical正規化とする。

新しく証明する計算は、`t² = 1`、`et = te`、およびoperationのBool成分における
`et ≠ e` である。これにより `et` はKaroubi対象 `(P,e)` の自己同型となる。
`t` の対象写像は恒等なので、対象の固定点だけを読む関手では `et` と恒等射 `e` の像が一致する。
同じ入力・同じ射について、operationを保持する実現では両者を区別する。

この試験で固定するものは `taggedOperationPackage`、そのadmissibility、
`taggedBoolOperation` の初期タグ `false` である。新しい一様flip、その可換性、
Karoubi射としての型付け、非忠実性はG-123で証明する。

## 4. 再構成原理とAAT固有の証明義務

独立な実現圏を `R`、表示圏を `P`、decoderを `F : P → R` とする。
証明義務は次の四つに分ける。

1. **充満性**: 固定した表示対象間の任意の実現射に、同じ端点を持つ表示射を構成する。
2. **忠実性**: 実現で等しい二つの表示射が、固定した構文の等式・商の下で等しいと示す。
3. **冪等完備性**: `R` の任意の冪等射を、実現側のデータと写像から分裂する。
4. **retract生成**: 任意の `X : R` に対して表示対象 `p` と
   `i : X → F(p)`、`r : F(p) → X`、`ri = 1_X` を構成する。

この四つから

\[
  \overline F : \operatorname{Kar}(P) \simeq R,
  \qquad
  \operatorname{Kar}(\operatorname{Arr}(P)) \simeq \operatorname{Arr}(R)
\]

を得る。一般原理では四つの性質を仮定する。AATへの適用では、それぞれを対象の
データ条件から証明する。`R` の定義にdecoderの像、`Kar(P)`、retractの存在証拠を用いない。

最初の同値の射は、選んだ分裂を `i_p : X_p → F(p)`、`r_p : F(p) → X_p`
と書くと、sandwich射 `f : (p,e) → (q,d)` を `r_q F(f) i_p` へ送る。
逆方向では充満性で `i_q h r_p` の原像を取り、忠実性でsandwich条件を反映する。
本質的全射性ではretractの冪等射 `ir` を充満性で戻し、忠実性で冪等性を反映する。
分裂の選択の変更に対しては、生成した自然同型とその整合を示す。

## 5. 論文の最後の系まで接続する

`c : X → Y` に対し、比較を保つ変更を

\[
 \Gamma_c=\{(u,v)\in\operatorname{Aut}(X)\times\operatorname{Aut}(Y)
              \mid vc=cu\}
\]

とする。対象と比較射の再構成から、表示側の対応する比較群との群同型を構成する。
単に群が抽象的に同型であると示すだけでなく、両端の自己同型とその評価を対応させる。

底と観測については、実現側に独立に定めた投影・観測と、表示側から生成するものの間で、
再構成同値に沿う自然同型を作る。底を固定する資格は、その自然同型とretractの両射が
底でどの写像になるかを計算して運ぶ。

G-122への接続では、実際の `barAlpha`、`barBeta`、二つの冪等射について、
表示対象・表示射・端点同型を構成して投影を照合する。その同じ対応で、次を運ぶ。

- selectorの成り立つ場合・成り立たない場合、およびcanonical正規化の場合の反映判定。
- 比較を保つ変更のsectionと、両端の底・係数写像。
- 制限準同型の分裂短完全列と、lift fiber上の核の自由かつ推移的な作用。
- 反映不成立を示すambientな核の元と、その元が元の比較を保たないこと。

最後の核と、lift fiberに作用する制限準同型の核は、それぞれの型と写像を保って運ぶ。
固定例には、G-122のfinite axis-fold、生成cochain、cell `second`、係数 `ℤ` と、
§3のoperationタグの例を使う。

## 6. G-123の主定理へ接続する設計

### 6.1 GOALカードとの対応

要求命題・量化・前提の役割・完了条件は[G-123カード](../../research/goals/G-123-aat-realization-reconstruction.md)
に定める。本ノートの§2・§4はカードA・B、§3はC、§5はD、n1015のCS対応はE・Fを説明する。
G-122への一般接続は構成したデータ条件を満たす入力について与え、カードDの生成比較例を
必ず収録する。その入力族の比較群の全元を運ぶ要求と、特定の射を表示する要求を区別する。

### 6.2 完全幾何の表示で未確定の構成

`R_lens`や`R_proto`の有限性から、完全幾何のすべての射の有限表示は従わない。
現在のsourceにおいて回復の対象となる成分と、その設計上の要求は次の通りである。

| sourceの成分 | 独立な実現と表示で必要な構成 |
| --- | --- |
| `SignedExactCoreReadingHom.objectMap` | `ArchitectureObject U`全体上の作用を、選んだ生成データから一意に回復する構成。選んだCS対象への制限だけではこの射の等号は決まらない |
| `operationMap` | すべての端点にわたるoperationの作用と、その同一性を回復する構成。configuration-mapが同じoperationも区別する |
| `equationTransport`・invariant・signature | contextと観測環の輸送、Law評価、残差、添字・座標の写像を同じ入力から生成する構成 |
| `GeomReadHom` | coverage・overlap・係数・raw restrictionと、全context上のSupport・Axis・Observableの写像および自然性を生成する構成 |
| sourceと実現の射の対応 | 上の構成を合成・恒等と整合させ、任意の許容射を読み戻す逆写像を与えること |

G-122の`canonicalGeometryNormalization`は、context・係数・局所実現を恒等に保つ。
その正規化を通っただけでは、これらのデータを有限の状態tableへ置き換えられない。
従って、有限表示の対象条件には、各写像族を生成するデータと、その生成の十分性を特定する必要がある。
完成済みのcore/geometry射をパラメータとして再入力する方法では、この仕事は済まない。

この表の構成をカードAの義務として切り出し、Bの四性質とDの生成比較への接続を
その構成について証明する目標にした。完全幾何に対する実現・構文・decoderの
具体的な定義は、draftからactiveへ進む際に確定する設計事項である。
パラメータの型、意味上の対象条件、許容射、生成規則、構文の等号、G-122の収録範囲を
定義として揃える。確定した定義で充満性等が成立するかは、G-123の証明課題として扱う。
この具体化の進行と判断はtracking Issueへ記録する。

## 7. 参照する実装

| 対象 | source・宣言 |
| --- | --- |
| 対象・operation | `Formal/AG/Atom/ArchitectureObject.lean`、`ObjectAlgebra.lean` |
| 元のcoreと完全な変更 | `Formal/AG/ReadingFunctoriality/Core.lean` の `ReadingCore`、`SignedExactCoreReadingHom` |
| 完全幾何の射 | `research/lean/ResearchLean/AG/GeometryTransport/Categories.lean` の `GeomReadHom`、`GeometryTotalHom` |
| G-119の交換同値 | `RealizationComparisonIdempotents/KaroubiArrowEquivalence.lean` の `karoubiArrowEquivalence` |
| G-121の表示可能性 | `FiniteDecoderRepresentability/FixedArrowClassification.lean`、`FiniteFullSubcategory.lean` |
| G-121の可算構文の限界 | `FiniteDecoderRepresentability/CountableSyntaxObstruction.lean` の `countableDecoder_not_surjective` |
| operationタグ | `DoctrineFiberProduct/LaxDiagnosticProjectorModificationCounterexample.lean` の `taggedOperationPackage`、`taggedBoolOperation` |
| G-122の完全幾何の正規化 | `FullGeometryNormalization/CanonicalNormalization.lean` |
| G-122の固定例 | `FullGeometryNormalization/ExactBarBetaFiniteWitness.lean` |
| G-122の比較群とfiber | `FullGeometryNormalization/ExactBarAlphaCanonicalComparisonExactness.lean`、`ExactBarBetaBottomQualifiedClassification.lean` |
| 一般関手延長 | mathlib `CategoryTheory/Idempotents/FunctorExtension.lean` の `functorExtension`、`karoubiUniversal` |

省略したResearchのpathは `research/lean/ResearchLean/AG/` からの相対pathである。
実行時の参照版と各宣言の使用先は、G-123のtracking Issueとreportに記録する。
