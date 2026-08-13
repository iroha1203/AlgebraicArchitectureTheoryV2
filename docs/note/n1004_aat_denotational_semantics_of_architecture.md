# アーキテクチャの表示的意味論としてのAAT — 再読ノート

本ノートは考察ノートである。新しい公理・定義・定理は導入しない。
現行AAT数学本文(第I部〜第X部)を「アーキテクチャの表示的意味論」という一つの視座で
再読し、既存の構成要素がその意味論の部品として実現されていることを固定する。
動機は、実務の設計議論において可換図式による整理が議論を収束させたという観察である。
可換であるべき箇所と可換でない箇所の分離が、そのまま設計上の合意点と判断点の分離になった。
本ノートはこの観察を一回性の技法ではなく、AATが最初から備えている意味論的構造の
手動実行として位置づける。

参照:

- [第I部 Atom・対象・法則](../aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md)
  (定義1.1、§5、§7、例7.4、定義8.1)
- [第II部 Architecture Geometry・Site・Sheaf](../aat/algebraic_geometric_theory/part_2_architecture_geometry_sites_sheaves.md)
  (定義8.1、定義10.1)
- [第III部 Law Algebra・Obstruction Ideal・Lawful Locus](../aat/algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md)
- [第IV部 Obstruction / Cohomology](../aat/algebraic_geometric_theory/part_4_obstruction_cohomology.md)
- [第V部 Derived Law Geometry / Repair](../aat/algebraic_geometric_theory/part_5_derived_law_geometry_repair.md)
- [第VI部 Singularity・Monodromy・Stack](../aat/algebraic_geometric_theory/part_6_singularity_monodromy_stack.md)
- [第IX部 Evolution Geometry](../aat/algebraic_geometric_theory/part_9_evolution_geometry.md)
- [第VII部 Representation・Periods・Analysis](../aat/algebraic_geometric_theory/part_7_representation_periods_analysis.md)
  (定義2.1、原則2.2、§4、定理6.1、例6.2)
- [第X部 Semantic Repair / Descent / SAGA](../aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md)
  (§3、定理8.2、系8.3、原則8.4)
- [Conormal first-order descent 設計ノート](aat_descent_theorem_value_and_route.md)

---

## 1. 中心命題

> **AATは、アーキテクチャの表示的意味論である。**
> ただしそれは、可換性を公理とし大域的な表示関数を前提する古典版ではない。
> 構文は観測から生成され、表示はまず局所的にのみ与えられ、大域表示の存在は
> 障害類の消滅と同値であり、破れは一級の測定対象である。
> 古典的表示的意味論は、被覆が自明で全図式の可換が要求される退化ケースとして
> この枠組みに含まれる。

この命題は新定理ではなく読みである。以下では、この読みを支える対応が
現行本文のどの構成要素で実現済みかを部品単位で示し、そのうえで古典版との差分を
三つの転回として言語化する。

---

## 2. 古典的表示的意味論の骨格

Scott–Strachey流の表示的意味論は、次の部品からなる。

1. **構文**: プログラムを生成する項の文法。
2. **意味領域**: 表示が値を取る数学的対象(領域、圏、代数)。
3. **表示関数** `⟦−⟧`: 構文から意味領域への合成的な割り当て。
   部分の意味から全体の意味が決まる(compositionality)。
4. **意味等式**: 二つの構文的対象が同じ表示を持つという等式。
   プログラム変換・最適化・リファクタリングの正当性はここに帰着する。
5. **適合性の問い**: 意味論が操作的挙動に対して健全か(soundness / adequacy)、
   完全か(full abstraction)。

Lawvereの関手的意味論はこれを圏論的に定式化する。理論は圏として提示され、
モデルはそこからの関手であり、意味等式は図式の可換性である。

---

## 3. 部品対応表

表示的意味論の各部品は、現行AAT本文の既存構成でそれぞれ実現されている。

| 表示的意味論の部品 | AATでの実現 | 本文の位置 |
| --- | --- | --- |
| 構文 | Atomが生成するpresentation、architecture context圏、AAT site | 第I部 定義1.1、第II部 定義4.1 / 8.1 |
| 意味領域 | representation target族: `Graph`、`Matrix`、`StateAlgebra`、`SemanticSpace`、`EffectSpace` 等、および係数sheaf | 第VII部 定義2.1、第IV部 |
| 表示関手 `⟦−⟧` | analytic representation `R : AATSch -> Target`(計算可能な対象へのfunctorとして定義済み) | 第VII部 定義2.1 |
| 合成性 | 局所表示から大域表示を組み立てるsheaf conditionとdescent(assembly方向)、およびoperationの合成を保存するrepresentationのfunctor性(定義として宣言) | 第II部 定義10.1、第X部、第VII部 定義2.1 |
| 意味等式 | law reading = equation system。lawfulnessはequation residualの消滅から生成される | 第I部 §7(例7.4)、第III部 |
| 意味等式の失敗 | semantic obstruction(residualの非同時消滅)とそのobstruction circuit | 第I部 定義8.1 / 8.2、第IV部 |
| 健全性・完全性 | representationのpreservation / reflection / conservative / faithful | 第VII部 §4 |
| full abstraction現象 | Period Separation: 同一graphが semantic / effect readingで分離される | 第VII部 定理6.1、例6.2 |

二点を強調する。

第一に、表示関手は比喩ではない。第VII部定義2.1は analytic representation を
「architecture schemeから計算可能な対象へのfunctor」として直接定義しており、
semantic Atomのschema(第I部 §5)は `denotes` という語彙で結果値への意味割り当てを
最初から保持している。表示的意味論の語彙は、本文にとって外来ではない。

第二に、第VII部§4のpreservation / reflectionは、表示的意味論の古典的な中心問題
(意味論は挙動に対して健全か、完全か)のアーキテクチャ版として読める。
preservationは構造的性質(zero / obstruction)が表示に写る方向(定義4.1)、
reflectionは表示上の性質から追加仮定(coverage、witness completeness等、定義4.2)の
もとで構造的性質を回収する方向であり、conservative / faithfulはその強さの階層である。
診断の語彙では、preservationは見逃しの排除、reflectionは誤検出の排除に対応する。
定理6.1(Period Separation)の例6.2は、粗い表示(graph)では一致する二つの対象が
細かい表示(semantic / effect reading)で分離されることを示す。これは
「表示の解像度がfull abstractionの成否を決める」というプログラム意味論の
古典的現象に対応するアーキテクチャ上の現象である。

---

最後に、この対応表は二水準を区別して読む。第VII部の `R : AATSch -> Target` は
常に与えられる **total analytic reading** であり、入力があれば必ず値を返す。
一方、第X部の大域切断は存在自体が定理の対象になる **coherent semantic
realization** である。表示的意味論の語彙では、前者が表示関手、後者が
「大域的な意味」にあたる。この区別が、§6の存在定理を正しく読む前提になる:
readingは常に取れるが、整合的な実現は取れるとは限らない。

## 4. Atomの位置 — 構文と意味の一元生成

部品対応表の中で、Atomの役割は他の部品と同格ではない。この意味論の
可能性条件そのものである。

古典的表示的意味論では、構文と意味領域は独立に与えられた二つの世界であり、
表示関数 `⟦−⟧` はその間の橋だった。プログラムでこの構図が成立したのは、
構文が言語定義によって最初から与えられていたからである。アーキテクチャには
所与の構文がない。記述言語を先に発明する経路は、記述と実装の二重管理を
宿命として抱え込む。Atomはこの欠落への回答である。観測される型付き事実の
語彙(第I部 定義1.1)が構文の生成元になり、語彙は閉じた列挙ではなく
新しいAtom familyへ開かれている(第I部 例1.2)。本文は「Atomは生成元として
扱われる」(第I部 §1)とこの役割を宣言しており、initial algebra semanticsに
おけるsignatureの役割のアーキテクチャ版にあたる。

決定的なのは、生成がsyntax側にとどまらないことである。構文(presentation、
context圏、site)がAtomから生成されると同時に、意味の住む場所である係数も
law経由でAtomから生成され(K0/K1係数生成契約)、lawfulnessは
「equation residualの消滅から生成され、別のtruth fieldを持たない」(第I部 §7)。
すなわちこの意味論において、表示関手は独立な二世界を結ぶ橋ではなく、
**Atomからの単一の生成過程の因子化**である。観測起点の構文生成(転回1)が
可能なのは、この一元生成による。

この視座から、Atom基礎論の隊列「Atom Is All You Need」(G-101〜G-104)は
意味論的完全性の定理化として再読できる。診断意味論の全体がAtom以外の
外部入力を要さないことを、係数生成契約とその hereditary 化、解像度不変性の
順で段階的に証明してきた隊列である。Atomが最大の武器であるという直感は、
この隊列によって既に定理の形で支えられている。

## 5. 三つの転回

部品対応だけなら、AATは関手的意味論の一適用にすぎない。
アーキテクチャの表示的意味論を固有の理論にするのは、次の三つの転回である。

### 転回1: 構文は書かれるのではなく、観測される

古典的表示的意味論では、構文は人間が書いた項として与えられ、意味論は
その解釈として後から定義される。AATでは順序が逆転する。source code が正であり、
Atomは観測によって抽出され、構文(Atom presentation、context圏、site)は
観測結果から生成される。この転回は本文内に接地を持つ。第I部定義10.4Aの
core readingは source と extraction doctrine を理論の構成データとして含み、
`Extracts_D(s, a)` / `Atomize_D(s)` が観測から構文への生成を与える。
ArchMapはこの抽出のtooling実現である。意味論が仕様の側にあり実装がそれに
従うのではなく、実装の観測から意味論の構文が立ち上がる。

この転回により、表示的意味論は設計時の文書ではなく測定装置になる。
spec を先行させる形式手法との対比軸(spec先行不要・source code 正の観測から)は、
意味論の語彙で言えば「構文の生成点を authored syntax から observed syntax へ移す」
という一点に集約される。

### 転回2: 表示は局所優先であり、大域表示の存在は定理の対象である

古典版では表示関数は全域的に定義され、プログラム全体の表示は常に存在する。
アーキテクチャではこの前提が成立しない。表示はまず architecture context ごとの
局所的な切断(section)として与えられ、大域表示とは選択されたcover上で
局所表示が貼り合わさって得られる大域切断である。

したがって「アーキテクチャ全体の意味」は定義によって自動的に存在するものではなく、
存在自体が定理の対象になる。この存在定理は現行理論で、係数の異なる二本として
証明済みである。

第一に、第X部定理8.2(Grounded Global Gluing)はsemantic係数について

```text
Nonempty P_sem(W)  <->  [r_sem] = 0  <->  [r_E] = 0
```

を固定する。ここで係数はsemantic Atomの `denotes` から生成され(第X部§3)、
`P_sem` の切断は文字通り局所semantic stateである。したがってこの定理においては
「表示=切断」は読み替えではなく構成そのものであり、semantic axis上で
大域表示の存在が障害類の消滅と同値になる。

第二に、conormal first-order descent定理はlaw idealのfirst-order係数
`ConDef = I/I^2` について、section `s` の局所liftの族が定めるconnecting class

```text
partial_U(s) in CechH1(U, ConDef)
```

の消滅が大域liftの存在と同値であることを固定する。

表示的意味論の語彙に読み替えれば、両者は
**大域表示の存在 ⟺ 障害類の消滅** という、アーキテクチャの表示的意味論の
存在定理である。古典的表示的意味論は、coverが自明で
障害類が常に消滅する退化ケースとしてこの構図に埋め込まれる。

### 転回3: 破れはエラーではなく、測定対象である

古典版では、可換であるべき図式が可換にならないなら、それは意味論の定義の失敗であり、
定義を修正して可換にする以外の選択肢がない。アーキテクチャでは事情が異なる。
可換性の破れ(結果整合性、並行操作の適用順序、chart間の読みの不一致)は
排除すべき欠陥である場合と、設計上引き受けた判断である場合の両方がありうる。

AATはこの破れを一級のデータとして扱う。equation residualの非消滅は
semantic obstruction(第I部 定義8.1)として定義され、obstruction circuitとして
有限に提示され、第IV部で係数対象への実現を経てcohomology類として測定される。
破れの存在だけでなく、どのcover・どのoverlapで・どの類として破れているかが
局在化される。

この転回が、実務の設計議論で観察された効果の理論的説明である。
議論が紛糾するのは、参加者が暗黙に異なる可換性の仮定を置いているときである。
図式を外在化すると、可換であるべき箇所(合意すべき等式)と可換でない箇所
(引き受けるべき破れ)が分離され、議論の対象が「どちらの経路が正しいか」から
「この破れを引き受けるか」へ移る。前者は収束しにくく、後者は判断として決着する。

破れを2-cellとして保持しlax構造として読む方向は、現行本文の範囲では未構成であり、
後続の研究対象である(2-cell raw defectの取り扱いはdraft段階のGOAL候補にある)。

---

## 6. 証明済み定理の表示的読み替え

この視座のもとで、既証明の主要定理は次のように読み替えられる。
いずれも読み替えであり、statementの変更を含まない。

| 定理 | 表示的意味論としての読み |
| --- | --- |
| 第X部 定理8.2(Grounded Global Gluing) | semantic係数上の大域表示の存在定理。`Nonempty P_sem(W) ⟺ [r_sem]=0` |
| Conormal first-order descent定理 | `ConDef = I/I^2` 係数上の存在定理。局所liftが大域化する必要十分条件は `partial_U(s)` の消滅 |
| Global lift fiberのtorsor構造 | 大域表示は一意ではなく、存在すれば `H^0` のtorsor。表示の選択の自由度の定量化 |
| Atlas定理(Diagnostic Resolution Invariance) | 表示的意味論のwell-definedness定理。固定条件C(C0–C6)を満たすresolution comparisonの下で、読みの解像度を変えてもH^1診断がcanonical同型で両立する。条件を外すと不変性が破れる反例3種を同じtheorem packageが保持する |
| Period Separation(第VII部 定理6.1) | 表示の細分の存在定理。粗い表示で一致する対象が細かい表示で分離される |
| 第VII部 §4 preservation / reflection | 意味論の健全性・完全性の問いのアーキテクチャ版 |
| G-107(Uniform Invariance Defect Semantics and Nonfactorization Theorem、2026-08-13 proved) | well-definedness の完全な地図。零 locus の座標(`J_A` 還元)・決定可能性(sound / complete decider)・既知の安全域の位置(`Condition-C locus ⊊ uniform locus`、7 witness で真性)・観測限界(`G_local-v1` 相対の非分解性)を一組で固定 |

特にAtlas定理の位置づけを固定しておく。表示的意味論が意味論の名に値するためには、
意味が構文の提示の仕方(読みの解像度の選択)に依存してはならない。
Atlas定理は固定条件Cの下でこの不変性を証明しており、条件Cはこの意味論が
well-definedである範囲を正確に切り出す記述になっている。反例3種は
その範囲の外で意味論が実際に壊れることまで定理packageの内側で示す。
成立域と崩壊例の両方を一つのpackageで保持するwell-definedness定理は、
古典的表示的意味論に対応物がない。

さらにこの階層は二方向に立つ。representation族に「Rが R' を経由して因子化する」
という前順序を置くと(この前順序自体は本ノートが導入する読みであり、
第VII部の族は無順序で提示される)、Period Separationはこの前順序で真の細分が
起こることの存在定理である: graph表示で一致する二つのgeometryが
semantic / effect表示で分離されることは、後者が前者を経由して因子化しないことの
観測的証拠である。一方Atlas定理は、law familyを固定した解像度方向の粗さ順序
(研究層で定義済みの `CoarserThan`、unported)について、adequateな区間上で
診断reading `H^1` がcanonical同型を除いて定数であることを言う。合わせると、
この意味論の観測的同値は、**軸の追加によって真に細分され、同一軸内の
adequateな解像度変更では不変である**という二方向の階層をなす。
抽象解釈のGalois接続階層と対比すると差分が鋭く出る。健全な抽象化では
粗化の損失は片側(偽警報のみ)に限られるが、adequacyを割った粗化は
偽の類の発生と真の類の隠蔽の両側で破れる(Atlas定理の反例対)。
この解像度階層はプラトーと両側の崩落で構成される。

---

## 7. 実例: イベントソーシング

イベントソーシングは、この意味論の一インスタンスとして次のように写る。
targetを `StateAlgebra` / `EffectSpace` に取った場合の specialization である。

| イベントソーシングの構成 | AAT Atom / law での実現 |
| --- | --- |
| イベント | `effect(e)` + `relation_emits(m, e)` |
| 集約の状態 | `state(C, x : X)` |
| イベント適用(apply) | operation + `relation_writes(m, x)`。ここからstate transition lawが立ち上がる(第I部 §5) |
| リプレイ | law reading `EffectReplayLawful`(第I部 例7.4) |
| 適用順序の可換性 | law reading `StateTransitionCommutative`(第I部 例7.4) |
| プロジェクション / リードモデル | `semantic(q(y), denotes ...)` + projection law |
| 結果整合性 | 選択されたcover上の可換性の破れ。排除ではなく測定の対象(§5 転回3) |

第I部§5の「dependency graph が acyclic でも、state transition が可換でないことがある」
という記述は、イベントソーシングにおける本質的な観察(構造依存が健全でも
適用順序の可換性は別の問いである)を、本文がAtom語彙の水準で先取りしていたことを示す。

### 設計時と観測時の二相構造

この実例から、意味論の運用像として二相構造が読み取れる。

1. **設計時(選択の相)**: 設計議論において可換図式として合意される内容は、
   equation system の選択である。どの図式の可換を要求し、どの破れを引き受けるかを
   決めることは、law reading と cover の選択に対応する。
2. **観測時(測定の相)**: 実装後、選択された equation system に対する residual を
   観測から計算し、合意が実装で成立しているかを判定する。これはArchSigが
   機械化している操作である。

二相は同じ equation system の選択と測定であり、仕様と実装の二重管理は発生しない。
設計時の合意はそのまま観測時の測定基準になる。冒頭の観察
(可換図式が設計議論を収束させた)は、第一相の手動実行だったと位置づけられる。

---

## 8. 系譜上の位置

この視座は次の系譜に接続する。表示のtargetは有限に提示された計算可能対象として
選択される(第VII部 定義2.1)。

- **Scott–Strachey**: 表示的意味論の原型。全域的表示関数と意味領域。
  アーキテクチャ版は、これを表示の局所化と存在の定理化の方向へ組み替える。
- **Lawvere(関手的意味論)**: 理論=圏、モデル=関手、等式=可換図式。
  アーキテクチャ版の表示関手(第VII部 定義2.1)はこの直系にある。
- **Institutions(Goguen–Burstall)**: 仕様の抽象模型論。標語
  「Truth is invariant under change of notation」に対し、Atlas定理は
  この標語のアーキテクチャ版の定理化(成立条件Cと崩壊反例つき)にあたる。
- **圏論的アーキテクチャ記述(Fiadeiro、CommUnity)と categorical systems theory**:
  設計を圏の図式、合成をcolimitとして扱う合成の理論。そこでは合成は常に構成可能で
  あり、大域的意味の存在は定理の対象にならない。AATはこれに対し、存在自体を
  定理化し障害を測定する診断の理論として立つ。
- **層意味論(Goguenのsheaf semantics for concurrent interacting objectsを含む)**:
  意味をsite上の層として持ち、系の挙動をlimitで与える伝統。AATのringed AAT toposと
  係数sheafはこの伝統の上に立ち、意味の大域化を障害類つきのdescent定理で
  制御する点で先へ進む。
- **抽象解釈(Cousot)**: 意味論の解像度階層をGalois接続で統一する伝統。
  §6の二方向階層はこれと対比され、adequacyの両側崩落が差分になる。
- **層論的contextuality(Abramsky–Brandenburgerの系譜)**: 経験的モデルの
  大域切断の不在をČech的障害として読む先行。大域切断の障害を診断に使う手には
  ここに先例がある。AATの差分は、site・係数・law・readingがAtomから一緒に
  生成され、reading間の輸送と解像度不変性まで同じ理論に入ることにある。
- **工学系譜(reflexion models)**: 設計モデルと抽出モデルの差分計算の実践。
  §7の二相構造は、この実践から設計記述と実装観測の二重管理を取り除き、
  差分を類としてwell-definedに局在化した形にあたる。

プログラムコード水準では、Čech cohomologyによる解析の統一が同時期に独立に
提案されている(sheaf-cohomological program analysis、2026)。H^1をsoftware診断に
用いる路線の妥当性を傍証する近接研究であり、AATはアーキテクチャ水準のlaw選択と
証明済みtheorem package(descent、torsor、Atlas)で区別される。

アーキテクチャの表示的意味論の固有性は、単独の部品ではなく束にある。
観測起点の構文生成(転回1)、存在の定理化(転回2)、破れの測定(転回3)、
二相構造(§7)を、Atomからの一元生成(§4)と証明済み定理群の上で
一つの意味論として提示する読み自体がこの合流点に立つ。

---

## 9. 意味の幾何 — 存在定理の先にあるもの

意味論の歴史は、意味に構造を与えていく歴史として読める。最初は集合と関数。
Scottが順序と位相を与え、再帰と近似が語れるようになった。圏論が合成の構造を
与えた。この系列の次の段が幾何であり、そこに立つのがAATである。
表示的意味論の伝統には「意味が存在するか」という問いはあったが、
「意味たちのなす空間がどんな形をしているか」という問いは立たなかった。
AATの代数幾何は、この問いを診断の実質として構成する。

- **失敗は空間を切り出す**。意味等式の失敗はobstruction idealを生成し、
  lawful locusを切り出す(第III部)。どこまでが合法かは、判定値ではなく
  空間の部分として存在する。
- **破れは解剖できる**。障害は類として測られるだけでなく、特異点・monodromy・
  stackの語彙で解剖される(第VI部)。同じ非可換でも、孤立した貼り間違いと
  設計全体を巻き込む捻れは別の病理であり、要する手当てが異なる。
- **修理は変形理論である**。conormal係数 `I/I^2` は、設計をどの方向に
  first-order変形すれば合法へ届くかの接空間を与える(第V部、
  conormal first-order descent定理)。修理候補の空間そのものが幾何的対象になる。
- **進化は時間方向の幾何である**。設計変更の履歴は空間の族として読まれる(第IX部)。

したがってこの意味論は二段構えになる。表示的意味論の層(§1〜§8)は
「大域的な意味が存在するか」に答え、存在定理と障害類を与える。幾何の層は
その先で「存在しないとき、失敗がどんな形をしていて、どの方向に動けば
存在に至るか」に答える。会議室の言葉で言えば、可換図式は破れの位置を教え、
幾何は破れの型と手術を教える。

系譜(§8)の言葉で締めれば: 意味論の伝統は意味に順序・位相・圏を与えてきた。
AATはそこに幾何を与える。存在定理の先に形の理論を持つことが、
この表示的意味論の最後の固有性である。

## 10. 帰結と後続候補

本ノートの帰結は三つある。

1. **理論の自己記述の更新**: AATは「代数幾何によるアーキテクチャ診断」であると同時に、
   「アーキテクチャの表示的意味論」として一枚で語れる。後者はプログラム意味論の
   語彙を持つ読者への最短の入口を与える。
2. **論文Aの位置づけ素材**: related work にプログラム意味論の系譜(Scott–Strachey、
   Lawvere、層意味論)を置き、AATをその合流点として位置づける構図が使える。
   §6の読み替え表は、既証明定理を意味論の言葉で提示する際の対応表になる。
   §4は、Atom基礎論の隊列を意味論的完全性の証明として提示するstory線を与える。
3. **outreach の骨格**: 「アーキテクチャに表示的意味論はあるか」という問いから入り、
   設計議論の収束という実務的効果に着地する記事構成が成立する。
   §7の二相構造は、理論と実務ツールの関係を一文で説明する
   (設計時に方程式を選び、観測時に residual を測る)。

後続候補は次のとおり。いずれも本ノートの範囲には含めず、証明はすべて未着手の
candidateとして扱う。

- **意味のモジュライ化**。将来の定義候補 `Sem_r(A) := Γ(X_A^r, P_r)` として、
  意味論の返り値を単一の値ではなく大域実現の空間(空でありうる)に置く。
  空でないことの判定=障害類消滅(第X部定理8.2)、選択の自由度=`H^0` torsor、
  first-order repair方向=`I/I^2` が、この空間の幾何の記述として一列に並ぶ。
  §9の幾何の層は、この定義の下で読みから構成へ昇格する。
- **Semantic Scheme Representability(山頂candidate)**。係数代数 `R` ごとの
  coherent lawful realization を集めるfunctor `Sem_{A,r}(R)` が、architecture
  scheme `M_{A,r}` により `Sem_{A,r}(R) ≃ Hom(Spec R, M_{A,r})` として
  表現されること。law=方程式系により、chart局所の表現可能性は
  law algebraの商の `Spec` としてほぼ定義から従い、主張の実質はcover上の
  descent貼り合わせにある。成立すれば `AATSch` の名が定理として換金され、
  Atlas定理はsemantic schemeの座標非依存性の `H^1` shadowとして再配置される。
  実現の自己同型を数える場合、目標はscheme表現可能性からstack表現可能性へ
  上がる。カード草案は本節末尾。
- **Resolution Diagnostic Local-System**。law family `L` に対するreadingの圏
  `Read_L` を構成し、診断 `D_L(q) := H^1(C_L(q))` をfunctorとして立てる。
  条件Cを満たす射は同型へ写り、一般の射にはjump data
  `J_L := (dim ker, dim coker)` を付ける。この構図で一様不変性の診断
  (G-107)が対象とするのは、単一 `D_L` の同型領域ではなく、全adequate
  law familyにわたる共通部分
  `Z_univ := { f | ∀ adequate L, J_L(f) = (0, 0) }`
  (universal zero-jump領域)である。条項系への反例は層別に読む。
  記号は条項系ごとに分けて読む(以下 `C*` = 探索期の歴史候補
  `CStarV3SupportActive`。G-104の条件Cおよび現行の幾何述語
  `ConditionCAllA` とは別述語)。uniform ∧ ¬C* 型は `Z_univ \ C*` の
  universal zero-jump点であり、jumpはどこにもない — syntacticな
  条項locusがsemanticな同型領域を過小近似している証拠となる
  (exact fixture: CONTRACTIBLE-TRIANGLE)。C* ∧ ¬uniform 型は
  真のjumpを持つ `C* \ Z_univ` の点である(exact fixture:
  PROPER-CHAIN3-PLUS-BRIDGE-DIGON — 歴史C*が粗側cycleの解像だけを
  検査し、非critical領域上の細側cycle新規生成を見ない穴。同fixtureでは
  G-104の条件C自体は成立しない — parallel liftによりC5相当が破れる —
  ため、条件Cの十分性とは矛盾しない)。jump locusのデータに
  なるのは後者と一般のnonuniform射であり、前者を jump locus と呼ぶのは
  層の取り違えになる。なお `Z_univ` を有限syntactic条項系で切り出すiff
  プログラムは、登録済み半径1観測grammar `G_local-v1` に相対する分離
  不能性(T3/T6の2点分離、Stop B終端)で閉じており、現在の開問題は
  「決定可能な内側近似はどこまで押せるか」と「どの大域情報を1成分
  足せば特徴づけに届くか」である。(2026-08-13 更新)この pair 水準の
  三本柱は G-107 の `target-theorem-proved` で完了した — `Z_univ` の
  座標((i) `J_A` 還元)・決定可能性((ii) sound / complete decider)・
  `Condition-C locus ⊊ Z_univ`((iii)(iv))・`G_local-v1` 非分解性
  ((v)、grammar 相対)がいずれも Lean theorem として固定された
  (正本 = G-107 report)。上記の開問題2点は後続カードの frontier に
  残る。functor性の合成整合は
  2-cell整合(後述の二層構成)の領分であり、終着はreading圏上のsemanticsの
  fibration / stack。reading空間は有限poset上のpersistence module
  (プラトーとjump locus)として読める。
- **semantic saturationの定理化**。生成された全-support nerveがsourceごとに
  cone化して `H^1 = 0` になる形式化結果は、「情報を無差別に充填すると
  診断幾何が消える」ことの定理として再読できる。law-selected nerve・
  relative cohomology・semantic quotientの必要性を導く方向のcandidate。
- **破れの2-cell化(lax表示)の二層構成**。語りの層=lax表示、定義と定理の層=
  有限presentation+gauge orbit(draft段階のGOAL候補の2-cell raw defect)。
  この分業により、一般coherence理論を経由せずにlax語彙で語れる。
  candidate statementは「raw defect δのgauge orbit消滅 ⟺ strict表示への
  coherent化可能」であり、当該GOALのtarget theoremの読み替えとして
  新しい証明義務を追加しない。本文側の接地は第X部原則8.4(nonabelian torsor /
  higher coherenceは独立statementを要する)。この構成では、単一の破れは
  辺gaugeで常に吸収され、真の不変量は閉配置上のdefect比の共役類に立つ。
  可換設計と非可換設計の判別は「δ=1か」ではなく「orbit不変量が自明か」で行われ、
  coherence等式の実務的内容は調停の順序独立性になる。
  descent(H^1、証明済み)→ 2-cell整合(H^2読み、syzygy整合仮定つき)という
  表示の次数階段が揃う。
- **解像度階層のcandidate statement群**。(1) `L`-adequateな読みの `CoarserThan`
  順序における最粗元 `q_L` の存在とC-実現可能性(診断の正規形化)。
  (2) C-実現可能なnerve対の範囲で「粗化が診断を保つ ⟺ `L`-adequate」
  (adequacyの必要性。条件C必要十分化ハントの第二段と相補する隣接statement)。
  (3) law部分族 `L ⊆ L'` に対する `H^1_L` の `H^1_{L'}` へのblock部分和としての
  canonical埋め込み(Period Separationのlaw語彙での定理化)。
- **full abstraction問題の再来の定理化**。「どのrepresentation familyでも
  faithfulにならないaxisが存在するか」という問いとして立てる。
  Period Separationが素材になる。
- **二相構造(§7)の tooling 側での明示化**。設計時に選択した equation system を
  そのまま LawPolicy 入力として引き渡す運用の具体化。

### カード草案 — Semantic Scheme Representability(昇格前の素描)

本草案はGOALカードではない。research/goals/ への昇格時にcard contractへ
書き直す前提の素描であり、statementの固定もレビューもまだ経ていない。

- 仮id: `G-1xx-aat-semantic-scheme-representability`
- 呼び名: **SHIGURE**(Semantic–Hom Identification: Geometric Universal
  Representability Equivalence)。呼び名は山頂 candidate の地位に留め、
  正式名 Semantic Scheme Representability を維持する(証明前の昇格は
  しない。Atlas 定理の命名規律を踏襲)。
- research aim(素描): Atomとlawから生成されたcoherent realization functor
  `Sem_{A,r} : CommAlg -> Set`(またはGroupoid)を、係数代数に自然な同値
  `Sem_{A,r}(R) ≃ Hom(Spec R, M_{A,r})` で表現するarchitecture scheme
  `M_{A,r}` を、law algebraとobstruction idealのaffine chartから
  貼り合わせて構成する。表現同値はadmissibleなreading変更と両立する。
- core tension(素描): 最大リスクは循環定義。realization functorを
  `M` への射として定義すれば表現可能性は恒真に堕ちる。functorは
  Atom / lawデータからの**R値方程式解**として独立に定義し、表現可能性を
  定理側に置く。affine chart水準はlaw algebraの商の `Spec` でほぼ定義的に
  従うため、主張の実質は (a) functorの独立定義の非退化性、(b) cover上の
  descent貼り合わせ、(c) reading変更との両立、の三点に置く。
- 前提機構(着手条件): ①K0 / K1係数生成契約の**base change**
  (`ℚ` 固定からR-代数への一般化)— 最初の技術的関門であり、単独の
  先行カード候補。②set値 / groupoid値の分岐の裁定(実現の自己同型を
  数えるか)。groupoid値ならscheme表現可能性ではなくstack表現可能性が
  目標になり、輸送の2-cell整合(G-106)が前提に入る。
- 依存(素描): law=方程式系(G-06)、descent定理(第X部・conormal)、
  G-101(reading間輸送)、G-106(高次整合。stack版のみ)、
  local-system構想(G-107 program context)、係数base change(未着手)。
- target theorem候補(素描、未固定):

  ```text
  Semantic Scheme Representability (candidate):
  有限regimeと明示descent条件の下で、Atom / lawから独立に定義された
  coherent realization functor Sem_{A,r} に対し、law algebraの
  affine chartの貼り合わせとして構成される M_{A,r} が存在し、
  R に自然な同値 Sem_{A,r}(R) ≃ Hom(Spec R, M_{A,r}) が成り立つ。
  admissibleなreading変更 q ≤ q' に対し、表現はcanonical射で両立する。
  ```

- failure policy(素描): scheme表現可能性が閉じない場合、その障害
  (実現の自己同型・貼り合わせの2-障害)はstack昇格の必要性の証拠として
  換金する。affine水準が恒真化した場合はfunctor定義の独立性を作り直す。
- 昇格条件: base changeカードの完了(または並走スコープの確定)と、
  set / groupoid分岐の裁定。それまで本草案はノート内に置く。

## 11. 研究プログラムの名 — Semantic Geometry of Architecture

本ノートから開く研究プログラムを次の名で呼ぶ。

> **Semantic Geometry of Architecture**
>
> Atomとlawから生成される意味のモジュライと、その存在・障害・変形・
> 特異性・reading間輸送・Scheme / Stack表現可能性を研究する幾何。

語順が内容である。これは幾何を道具に意味を説明する geometric semantics では
ない。coherent semantic realization そのものがモジュライをなし、意味が空間を
持つ — その空間を研究する幾何である。表示的意味論(§1〜§8)はこの
プログラムへの入口であり、意味の幾何(§9)と山頂candidate(§10)がその
最初の行程表にあたる。

位置づけは三層+動力学の座で固定する。

```text
AAT — 純粋数学的土台(第I〜X部): 意味の空間の静力学
Semantic Geometry of Architecture — AATの上に開く研究プログラム
SAGA — その中の証明済み定理系列の一つ(貼り合わせ・修理・descent、第X部)
SFT — 意味の空間の上の動力学(field-shaped software evolution)
```

SFTの座は本プログラムの発見によって一段明確になる(構想としての記録であり、
SFT本文への持ち込みは別作業とする)。意味がモジュライ空間を持つなら、
開発とはその空間内の**軌道**である。SFTの field / force / attractor / basin
は、意味のモジュライの上で文字通りの読みを獲得する — basinは意味の空間の
吸引域、修理はconormal方向への運動、特異点は流れが滑らかに延長されない点。
進化幾何(第IX部)が semantic scheme の族として運動学を与え、SFTがその上の
動力学を研究する。AATが相空間を作り、SFTがその上の力学を語る、という
静力学と動力学の分業である。依存方向は現行interface正本の通り
AAT → SFT の片方向を保つ(SFTはモジュライを観測量・状態空間として
受け取り、数学的核を置き換えない)。

命名規律: 本リポジトリでは、この名を**略さない**。頭字語はGrothendieckの
Séminaire de Géométrie Algébriqueと衝突するため使用せず、常に
Semantic Geometry of Architecture と綴る。既存の確立語彙 SAGA(第X部の
定理系列)とは別物であり、併記する場合は上の位置づけで区別する。
