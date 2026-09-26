# G-124-aat-local-semantic-reconstruction — 局所意味表示からの再構成と有限決定性

- `id`: `G-124-aat-local-semantic-reconstruction`
- `status`: `completed`
- `research mode`: `target-theorem`
- `tracking issue`: [#4711](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4711)
- `source`: [G-123の総括とG-124の研究目標案(#4520)](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4520#issuecomment-5712533071)、[G-123 report](../reports/G-123-aat-realization-reconstruction.md)
- `paper plan`: [n1012 第8章(第7章の系の回復を含む)](../../docs/note/n1012_aat_unified_theory_foundations_paper_plan.md)

## 研究目的

Atom・Law・operation・完全幾何の局所構造とその整合から、意味の実現・許容射・比較を
再構成し、その再構成がいつ有限データで決定されるかを明らかにする。全域の射を一個の
有限構文と対応させたG-123の要求に代えて、全域の射を整合する局所データの族と対応させる。
局所片は有限に組み立て、局所片の添字と整合族全体には無限を許す。意味論的に自然な射は
可逆に限らず全て残す。

G-123の受理済み成果を既存定理として引き継ぐ。lens・プロトコルの有限Karoubi再構成と
読み戻し、充満忠実関手に沿う比較群輸送、操作の連結性による追随変更の分類、
G-122の生成比較の回収基盤である。G-123の障害の記録は対象の側から使う。特に、
有限構文の充満性を破ったタグ変更族そのものを、全有限片からの再構成と有限読み取りでの
決定不能が両立する最初の例として分類する。

一般再構成原理の成立条件を対象の操作・関係・制限から導き、同じ構成・定理から
lens・プロトコル・G-122の分類へ帰結を戻す。有限データで決まる場合と決まらない場合を
同じ定義の下で説明し、n1012第8章の表示と再構成の主結果をこの目標の成果で与える。

## 固定target

A–Eを一つの主定理の構成部分とする。合成順は `gf=g∘f`、`Kar(C)` は冪等完備化、
`Arr(C)` は射の圏を表す。構成する宣言・圏・写像は研究成果であり、完成済みの入力として
受け取らない。G-123までの受理済み宣言は既存定理として接続し、同じ内容の再証明を
要求しない。指示対象の特定は「既存宣言の参照」にある。

### A. 入力宣言・実現圏・局所読み取り

パラメータの型を指定する一つの宣言 `Σ` と、Atom・Law・operation・完全幾何の
データ条件 `D`、局所読み取りの宣言を構成する。量化順は、一つの `Σ,D` と
局所読み取り宣言の構成、その宣言の任意のパラメータ `Θ`、その下の任意の対象・射とする。

条件 `D_Θ` を満たす実現と、指定した構造を保つすべての写像から圏 `R_Θ` を定める。
射は可逆に限らない。対象・射の条件に、局所データ族の延長可能性、decoderの像、
有限表示の存在を用いない。入力宣言では、G-123 Aと同じ成分区分
(Atom・対象/operation/Law・invariant・signature/完全幾何/係数・raw data)ごとに、
保持するパラメータの型、評価、射が保つ等式を特定する。carrierや係数環など
パラメータとして残す無限データの型・由来も宣言に含める。

同じ `Θ` に対し、局所読み取りの添字型 `Λ_Θ` と、各添字の局所値型・読み取り写像を
構成する。局所値型は型付き図式・table・パラメータ参照から有限に組み立て、
各局所片の有限性を示す。読み取りは既存の原始構造の評価(operationの両端・作用、
Lawの添字・評価・残差、rawの座標・restriction、contextの読取り・制限、
coverage・overlap、Support・Axis・Observable)として構成し、既存の読取り・制限との
対応を証明する。一つの局所値に全域の写像や完成した射を保持しない。任意の完成した
core/geometry射を一つの定数として受け取る構成は採らない。

`D_Θ` の必須収録は次の四族とし、各族が条件を満たすことを構成・証明する。
`D` を再構成の結論から定めない。

| 族 | 収録する内容 |
| --- | --- |
| タグ付きoperation入力 | `taggedOperationPackage` とそのcanonical正規化、一様flip、source-choice族の全元を `R_Θ` の対象・射として収録する |
| G-122の固定生成比較例 | `finiteAxisFoldBCDatumSquare`、`finiteAxisFoldFixedCoefficientGeometryFamily`、cell `second`、係数 `ℤ` の生成比較・正規化・端点自己同型 |
| lens族 | 全域get/putの三法則と有限な基準fiber `g⁻¹(v₀)` を満たす実現と、独立に指定した意味保存射の全範囲 |
| プロトコル族 | 商経路圏上の観測を持つ有限carrier実現と、観測を保つ自然変換の全範囲 |

### B. 局所モデル圏と再構成の主定理

同じ `Θ` に対し、局所モデルの圏 `M_Θ` を定める。対象は整合式を満たす局所値の族、
射は局所射データの整合族とし、恒等・合成は成分ごとに定める。整合式は局所データの
間の等式(制限・overlap・operation輸送・Law・係数の整合)として独立に定め、全域の
射の存在や延長可能性を整合式の定義に含めない。

原始読み取りから関手 `N_Θ:R_Θ→M_Θ` を構成する。一般再構成原理として、
局所読み取りの族が次の二性質を満たす圏で `N` が圏同値になることを証明する。

1. **分離**: 読み取りの組が対象・射を区別する。
2. **組立て**: 任意の整合族が全域の対象・射の読み取りとして得られる。

一般原理ではこの二性質を仮定してよい。AATへの適用ではAのデータから得た証明を渡す。
主同値

\[
 N_\Theta:\mathcal R_\Theta\simeq\mathcal M_\Theta,\qquad
 \operatorname{Hom}_{\mathcal R_\Theta}(X,Y)
 \underset{\operatorname{asm}}{\overset{\operatorname{read}}{\rightleftarrows}}
 \operatorname{Hom}_{\mathcal M_\Theta}(N_\Theta X,N_\Theta Y),\qquad
 \operatorname{read}\operatorname{asm}=1,\quad
 \operatorname{asm}\operatorname{read}=1
 \tag{B1}
\]

を証明する。一意性(分離)と存在(組立て)は個別に証明する。対象については、任意の
局所モデル対象に対し、読み取りがそれと同型になる実現を構成し、同型・恒等・合成・
評価との整合を示す。

### C. 投影・正規化・比較群の整合とG-122分類の回復

底・観測・係数への投影を局所データから `M_Θ` 側にも構成し、`N_Θ` に沿う自然同型を
証明する。同じ対応で係数写像も運ぶ。`c:X→Y` の比較群を

\[
 \Gamma_c=\{(u,v)\in\operatorname{Aut}(X)\times\operatorname{Aut}(Y)
                  \mid vc=cu\}
 \tag{C1}
\]

とし、任意の比較 `c` について同型 `Γ_c ≅ Γ_{N_Θ(c)}` を構成する。構成には充満忠実
関手に沿う既存の比較群輸送を接続し、両端自己同型の評価、底を固定する部分群と指定する
許容部分群への制限、G-120の群準同型分類との整合を証明する。正規化後の比較
(Karoubi対象間の射)も同じ対応で保存・反映し、`Kar`・`Arr` への延長はG-119の
`karoubiArrowEquivalence` へ接続する。

Aで収録したG-122の固定生成例について、生成cochain `initialRawDefectCochain` による
`barBeta`、同じ幾何で定数 `1` のcochainを用いた `barBeta`、同じ入力の `barAlpha` と
canonical正規化の三つの場合の入力・分類を、局所モデル側の表示から回復する。回復対象は
次のとおりとし、元の全比較群と底を固定する比較群を区別して、対象とした群の全元を運ぶ。
特定のsectionや核の元だけの表示から全体の回復を結論しない。

- 可逆性と反映の判定、比較を保つ変更のsection、sectionの底・係数成分。
- 制限準同型の分裂短完全列と、各lift fiber上の核の自由かつ推移的な作用。
- 制限準同型の核とambientな核の区別、反映不成立を示す核の元とその判定。

### D. 有限決定性の定義と一般判定

対象とする射・変更の集合と局所読み取りの族に対し、有限読み取り方式(読み取り添字の
有限部分集合 `S`)の三性質を別個に定義する。どれか一つから他を導かない。この定義を
A–Bの局所読み取り宣言とEの各適用で共通に使う。

1. **区別**: `S` の読み取りの組が対象とした集合の上で単射になる。
2. **延長**: `S` に制限した整合条件を満たす任意のデータが、全域の射・変更へ延長できる。
3. **実効**: `S` 上のデータを列挙可能な有限入力として特定した上で、その整合判定が
   決定可能で、延長が計算できる。

区別と延長を同時に満たす `S` を決定集合と書く。区別・延長は局所成分の個数についての
判定であり、一つの局所値の情報量を制限しない。有限量のデータによる決定を主張する
箇所では、局所値型の有限性を別に特定する(Aの局所片の有限性、Eの各有限table)。

一般判定は操作系について独立に量化する。任意の有向多重グラフ `Q=(V,E,s,t)`、
集合 `K`、`H≤Aut(Q)` について、受理済みの追随変更の分類(連結成分ごとの置換族への
降下、分裂短完全列、lift fiberの核作用)を既存定理として使い、`|K|≥2` のもとで、
各可視変更上の追随変更の集合と、頂点 `v∈S⊆V` での隠れた置換の読み取りについて
次を証明する。

- 区別 ⟺ `S` が向きを忘れた全連結成分と交わる。
- 延長 ⟺ 同じ連結成分に属する `S` の任意の二頂点が、`S` の頂点とその間の辺だけで
  結ばれる。ここで `S` 上の整合条件は、両端が `S` に属する辺の等式
  `φ_{s(e)}=φ_{t(e)}` とする。
- 決定集合の存在 ⟺ `π₀(Q)` が有限。各成分から一頂点を選ぶ `S` が決定集合になる
  ことも示す。
- 実効は、`V`・`E`・`K` の有限性を列挙table(頂点・辺・値の有限な一覧と等号判定)として
  入力に固定した上で述べる。その入力について `S` 上の整合判定の決定可能性と延長の
  計算可能性を与え、既存の有限例・fiber個数の宣言に接続する。

### E. 二つの具体的決定とCS意味論への帰結

**E1. タグ変更族。** 既存のsource-choice族に合成・逆を明示して群構造を与え、
点ごとのBool反転の積との群同型

\[
 C_2^{\Omega}\;\xrightarrow{\;\sim\;}\;\{T_\chi\},\qquad
 \Omega=\operatorname{ArchitectureObject}(\text{固定入力})
 \tag{E1a}
\]

を構成する。既存の各点読み戻しを局所読み取りとし、Dと同じ定義を適用して次を
同じ族について証明する。

- 全有限片からの再構成: 有限部分集合への制限写像による逆極限との同型
  \[
   C_2^{\Omega}\cong\varprojlim_{S\subseteq_{\mathrm{fin}}\Omega}C_2^{S}
   \tag{E1b}
  \]
  を構成する。逆向きは整合族から各点の値を読む。この同型を、Bの主同値による
  タグ変更族の回復と同定する。
- 有限決定不能: 既存の `architectureObjectInfinite` から、任意の有限 `S⊂Ω` に対して
  `S` 上で恒等と一致する非恒等のタグ変更を構成し、区別を満たす有限読み取り方式が
  存在しないことを証明する。辺のない操作系としてDの一般判定へ対応させ、決定集合の
  存在 ⟺ `Ω` が有限、を同じ判定から導く。
- 一様flipの分離: 定数 `true` の像 `t` について `t²=1`、`et=te`、`et≠e` を既存宣言との
  対応で保持する。分類の対象はタグ変更族とし、対象幾何の全自己同型群の決定は
  この条項の要求に含めない。

**E2. lens・プロトコルの有限決定と既存再構成の整合。** 二層に分けて証明する。

一般の意味保存射の層では、lens族・プロトコル族の全射にA–Bの局所再構成とDの三性質の
定義を適用する。lensの基準fiber table、プロトコルの頂点table・生成辺の評価を
読み取り方式とし、既存の有限表示によるKaroubi再構成(retract生成・`Arr` 版を含む)の
制限・延長をBの主同値と整合させる自然同型・可換図式を構成して、この読み取り方式が
区別・延長を満たすことを既存定理の接続として示す。有限表示からのKaroubi再構成の
強い結論はこの二族で保持し、全入力への一律の要求とはしない。

可逆変更族の層では、Dの連結成分による必要十分条件を、FixedF操作系(各頂点で同じ
隠れ状態を持ち、各辺が隠れ状態を恒等に運ぶ)と、既存接続が対応させるlens・
プロトコルの可逆変更族へ適用する。lensの追随変更では、全域putが全fiberを基準fiberへ
結ぶことから基準fiberの読み取りが決定集合になることを、プロトコルの可逆変更族では、
成分ごとの頂点選択が決定集合になることを、同じ判定から導く。連結成分による
必要十分条件の適用対象は、この操作系と可逆変更族とする。

両層で、lens・プロトコルの既存比較群輸送をCの群同型と接続し、追随変更のsection・核・
lift fiberを局所表示側からも回復する。

## 既存宣言の参照

Research pathは `research/lean/ResearchLean/AG/` からの相対とする。解決commitは
active化時にtracking Issueへ記録する。

| 用途 | path・宣言 |
| --- | --- |
| G-119の交換同値(C) | `RealizationComparisonIdempotents/KaroubiArrowEquivalence.lean` の `karoubiArrowEquivalence` |
| G-120の群準同型分類(C・D) | `ComparisonInformationLoss/GroupHomRestriction.lean` |
| タグ付き入力と一様flip(A・E1) | `DoctrineFiberProduct/LaxDiagnosticProjectorModificationCounterexample.lean` の `taggedOperationPackage`、`RealizationReconstruction/AATUniformFlipKaroubi.lean` の一様flip宣言群 |
| source-choice族と読み戻し(A・E1) | `RealizationReconstruction/MandatoryCExplicitExactGeometryObstruction.lean` の `taggedSourceChoiceExplicitExactGeometryMorphism`、`readTaggedSourceChoiceExplicitExactGeometry`、同 `_injective` |
| `Ω` の無限性(E1) | `RealizationReconstruction/MandatoryCFiniteReferenceObstruction.lean` の `architectureObjectInfinite` |
| G-122の固定生成例(A・C) | `DoctrineFiberProduct/BCDiagnosticAxisFoldComparisonWitnesses.lean` の `finiteAxisFoldBCDatumSquare`、`FullGeometryNormalization/ExactBarBetaFiniteWitness.lean` の `finiteAxisFoldFixedCoefficientGeometryFamily`、`TransportCoherence/FinitePresentation.lean` の `initialRawDefectCochain` |
| G-122比較群の完全性とfiber(C) | `FullGeometryNormalization/ExactBarAlphaCanonicalComparisonExactness.lean` の `authoredExactCanonicalComparison_shortExact`、`authoredExactCanonicalComparisonLiftFiber_existsUnique_smul_eq` |
| G-123のG-122回収基盤(C) | `RealizationReconstruction/G122GeneratedComparisonGroup.lean`、`G122RestrictedAmbientKernelSeparation.lean` |
| 比較群輸送(C・E2) | `RealizationReconstruction/CSAATFullyFaithfulComparisonTransport.lean` の `generatedArrowComparisonMulEquivOfFullyFaithful`、lens・protocolの両 `MulEquiv` |
| 追随変更の分類(D) | `RealizationReconstruction/FixedFComponentClassification.lean` の `equivComponentPermutationFamilies`、`preservingEquivComponentPermutationFamilies`、`FixedFSplitExactSequenceAndTorsor.lean` の `isGroupShortExact`、`projectionFiber_action_free`、`projectionFiber_action_transitive` |
| 有限例と個数(D) | `RealizationReconstruction/FixedFFiniteExamples.lean`、`FixedFFiberCardinality.lean` |
| lens・プロトコル意味論(A・E2) | `RealizationReconstruction/LensSemantics.lean`、`ProtocolSemantics.lean` |
| 既存Karoubi再構成(E2) | `RealizationReconstruction/CSKaroubiReconstruction.lean` の `lensKaroubiReconstructionEquivalence`、`protocolKaroubiReconstructionEquivalence`、両retract定理と `Arr` 版 |
| 可逆変更族への既存接続(E2) | `RealizationReconstruction/FixedFLensConnection.lean` の `LensInvertibleChange`、`FixedFProtocolConnection.lean`、`FixedFProtocolGroupConnection.lean` の `ProtocolChangeGroup`、lens側GroupConnection |

## 前提・構成台帳

| 対象・対応条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 宣言 `Σ`、パラメータ `Θ`、条件 `D_Θ`、実現圏 `R_Θ`(A) | `Σ,D` は構成義務。確定した各パラメータ値は入力として保持 | Aの成分別宣言、独立な対象・射条件、必須入力四族の収録証明 | 原始データからB–Eへ |
| 局所読み取り宣言 `Λ_Θ`・局所値型・読み取り(A) | 構成義務 | 各局所片の有限性、原始評価との対応 | 既存の読取り・制限・overlapからB・Dへ |
| `M_Θ`、`N_Θ`、`read`・`asm`(B) | 構成・証明義務 | 整合式の独立な定義、(B1)、一意性と存在の個別証明 | Aの整合式からC–Eへ。延長可能性を整合式の定義へ移さない |
| 分離・組立て(B) | 一般原理では仮定、AAT適用では放電義務 | Bの二性質 | Aのデータから(B1)へ。結論相当の仮定への移動を確認する |
| 交換同値・群準同型分類(C) | 既存定理として使用 | `karoubiArrowEquivalence`、`GroupHomRestriction` | G-119・G-120からCの整合へ |
| G-122の生成比較・分類と回収基盤(C) | 既存定理として使用。局所表示からの回復は証明義務 | Cの三場合、全群・二種類の核・fiber | G-122・G-123の受理済み宣言から局所モデル側の回復へ |
| 有限決定性の三定義と一般判定(D) | 構成・証明義務 | Dの各同値と決定集合の存在判定 | 追随変更の既存分類からEの三適用へ |
| 追随変更の分類(D) | 既存定理として使用 | 成分降下・分裂短完全列・fiberの核作用 | G-123の受理済み宣言からDの判定へ |
| タグ変更族と `Ω` の無限性(E1) | 既存宣言・定理を入力として保持。群構造・逆極限・決定不能は証明義務 | (E1a)・(E1b)、非区別の構成、一様flip分離の保持 | Cycle 188の受理済み宣言からDの適用と有限性の限界の説明へ |
| lens・プロトコルの意味論と既存再構成(E2) | 意味論・法則は入力として保持。既存再構成・輸送・可逆変更族接続は既存定理として使用。整合は証明義務 | E2の二層(一般射の読み取り方式の区別・延長、可逆変更族への判定適用)、自然同型・可換図式、群接続 | G-123の受理済み宣言からB・Dとの整合とCSへの帰結へ |

## 完了条件

1. A–Eを同じ宣言・実現・局所表示の構成について確定し、Bの主同値、Cの回復、Dの判定、
   Eの三適用(タグ変更族・lens・プロトコル)を含む主定理をLeanで証明する。達成として
   認める結果は `target-theorem-proved` とする。E1の有限決定不能は、指定した命題
   (任意の有限 `S` での非区別)の証明として扱う。それ以外の固定主張への反例は共通の
   反証停止規則で扱う。
2. Cの三場合、E1の同一族での同時成立((E1b)の同型・非区別・一様flip分離)、E2の
   決定集合と既存再構成の整合、Dの実効性の有限例(既存FixedF有限例への接続)について、
   固定した入力・写像・評価を証明し、一般定理への適用と対応させる。
3. `research/lean/ResearchLean/AG/` に定義・定理・witnessを置き、
   `research/reports/G-124-aat-local-semantic-reconstruction.md` に条項と宣言、
   前提の出所・使用先、検証証拠を対応させる。実行状態はtracking Issueに記録する。
   継承する受理済み宣言は接続として記録し、同じ内容の再証明を完了条件にしない。
4. n1012第8章に向けた主張と証拠の対応をreportへまとめる。一般圏論・逆極限・群論への
   帰属と、AAT固有の構成・接続を区別し、二つのCSの問題が同じ機構から得た帰結と、
   有限データで決まる場合と決まらない場合の同一定義下の説明を示す。
5. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従って完了を判定する。適用版、最終検証、査読、完了ledgerはIssue・reportへ置く。
