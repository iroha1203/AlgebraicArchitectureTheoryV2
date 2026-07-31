# Atom Is All You Need — Atom 基礎論・最初の考察

2026-07-29 のディスカッションのまとめ。**完成された理論ではない**。
AAT の次目標「Atom 基礎論の補強」に向けた最初の考察として、
到達した見取り図・定理候補・適用範囲・NEXT ACTION を固定する。
Codex・有識者・マルチエージェント探索との議論往復と敵対レビューを
反映済み(経緯はコミットログと PR の記録)。

第I部本文([part_1_atoms_objects_laws.md](../aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md))は
保護ファイルであり、本ノートは本文を改訂しない。本文への反映は
3条件ゲート(人間の明示指示・相互レビュー・人間 merge)を通る将来作業とする。

参照:

- [第I部 Atom・対象・法則](../aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md)
  (定義1.1、semantic Atom、公理A0–A8、命題A9、ExtractionDoctrine)
- [第III部 Law Algebra / Obstruction Ideal](../aat/algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md)
  (law の equation system 化、nu/epsilon 二族)
- [第IV部 Obstruction / Cohomology](../aat/algebraic_geometric_theory/part_4_obstruction_cohomology.md)
  (H^0 visible defect / H^1 gluing obstruction / H^2 coherence obstruction の区分)
- [第X部 Semantic Repair / Descent / SAGA](../aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md)
- [one-cent ドリフト実例](../../tools/archsig/examples/practical-rust-service/README.md)
- `Formal/AG/Atom/`(AtomCarrier / AtomAxiomSystem / Atomizes)、
  `Formal/AG/Atom/AATCore.lean`(CoreReading / AATCorePackage)、
  `Formal/AG/ReadingFunctoriality/`(ReadingCore と reading 間比較の上層)、
  `Formal/AG/AxiomAudit.lean`

---

## 0. 動機

AAT は SAGA 定理まで到達したが、出発点の Atom まわりは公理として
置かれたままである。仮定が強く、Atom 公理系が CS 的に自然で妥当である
ことの理論づけがない。次目標は Atom の基礎論を固めることである。

目標の標語は「Atom に作用する方程式系から代数幾何が立ち上がる」。
本ノートの検討を経て、この「立ち上がる」の意味は確定した:
Atom と方程式系は幾何的読みの**選択空間を制約**し、representable な場合に
canonical な読みが立つ(§3、§6)。幾何の導出(創発)ではなく、
この条件付き canonical 性を指す。

## 1. 土台 — 相対性原理

ソフトウェアは本質的に相対的な存在である。選択された OS・処理系・言語・
フレームワーク・仕様の上で、相対的に成り立つ。したがってソフトウェアから
抽出される Atom も、意味 Atom はもちろん構造 Atom まで含めて、
相対的であるのが自然である。

```text
相対的な Atom と相対的な方程式系から立ち上がる、相対的な幾何。それが AAT。
```

到達目標は Grothendieck の相対的視点(relative point of view)である。
EGA 以降の代数幾何では対象は射 X -> S であり、性質(平坦・固有・滑らか)は
すべて底 S に相対的な射の性質として定義される。ソフトウェアは底の塔の上の
ファイバーであり、Atom は**宣言された底の上の族**である。現段階の
「Grothendieck 的」は比喩であり、doctrine の変更に対して Atom family・
site・係数・障害類がどう輸送されるかを構成できたとき、はじめて数学になる。
本目標の理論的内容はこの**輸送の構成**にある(§3、§8)。輸送の形式化
仕様と達成階梯(Gr0–Gr4)は §3.5 に固定した: 現在 Gr1(statement 化)に
到達済みであり、この比喩宣言の撤回条件は Gr2(§12 スライス a–c の
Lean 構成)である。

タイトル「Atom Is All You Need」のテーゼは、因子化として固定する。

```text
AAT が語れるすべてのアーキテクチャ的結論は、Atom 層を通して factor する。
Atom は、すべての読みが通る唯一のボトルネック・インターフェースである。
```

Atom は万物を導出する源泉ではなく、すべてが通る唯一の関門である。
これは L-adequacy(§5)を結論一般へ広げた完全性テーゼであり、
修辞ではなく検証対象である(§8 候補7)。

相対性が相対主義(何でもあり)に堕ちない支えは三つある。

1. **底は実行可能な契約である。** OS は現に動き、コンパイラはバイナリとして
   存在し、仕様はテストが執行する。各層の言語ゲームには物理的・機械的な
   執行者がいる。
2. **相対化には残余がある。** 底に残る非相対的なものは inscription
   (書かれた source そのもの)と実行可能 artifact である。絶対なのは意味
   ではなく銘刻であり、だからこそ digest による再現性が成り立つ。
   相対化されるのは意味であって、銘刻の同一性ではない。
3. **相対性は圏をなす。** 底の間には射(細分・翻訳・base change)があり、
   理論の内容は「何がどう運ばれるか」の関手性として語られる。
   relativism ではなく functoriality。

客観性については定義の分業を置く。フレームの共有度と執行力は、なぜその
フレームが選ばれ構造 Atom が絶対に見えるのかを説明する**発生論**。
理論内部で客観性が何を意味するかは、§3 の輸送安定性が**内容論**として
定義する。

現場の実践がこの見方を経験的に追認している: "works on my machine"
(輸送の安定性の欠如)、Docker(底の塔ごと同梱して出荷)、
C の未定義動作(仕様底の穴に処理系ごとの底が挿入され、同一ソースから
異なる Atom 族が立ち上がる)、Hyrum の法則(宣言された仕様底と
事実上依存されている底の乖離)。

## 2. 柱1 — Atom の二相(構造 / 意味)

Atom は大きく二種に分類できる。

- **構造 Atom**: component や relation など、ソースから機械的に取り出せるもの
- **意味 Atom**: semantic であり、使われ方(言語ゲーム)によって決まるもの

この分類は、抽出の**依存 profile** から導出する。A8 の ExtractionDoctrine
`D = (V, Γ, R, ρ, E, N)` を、構文的成分 `(V, ρ, E, N)`(語彙・解像度・
言語仕様の読み・正規化)と語用論的成分 `(Γ, R)`(use-context と use-rule)に
分解した上で:

```text
固定した許容変形族に対して、Extracts_D(s,a) の真偽が
doctrine のどの成分の変更で動くかを記録したものを a の依存 profile と呼ぶ。

構造的: profile が (Γ, R) に不感
意味的: profile が (Γ, R) に感応
```

AtomKind の分割を採らないのは、contract(型シグネチャは構造的、振る舞い
契約は意味的)や authority(RBAC 設定は構造的、信頼関係は意味的)のように
現行 schema の多くが両相にまたがるからである。`semantic iff not 構造的`
という補集合定義を採らないのは、比較不能・抽出失敗・正規化差のような
別種の状態まで意味 Atom 側へ混入するからである。profile を先に置けば、
混合例は例外ではなく主対象になる。

この定義の下で、構造 Atom とは「すべての言語ゲームが同意する事実」であり、
「一意に取り出せる」の正確な内容は使用文脈の取り替えに対する不変性である。
A8 の「一意性の相対化」とも、後期ウィトゲンシュタインの立場とも整合する。
構造 / 意味は絶対 / 相対の区別ではなく、**底の塔のどの深さで抽出が安定
するかの深度スペクトル**の両端であり、依存 profile はその座標である。
構造 Atom が絶対に見えるのは、依存する底(言語仕様+コンパイラ)が広く
共有され機械執行されているからである。本文化する際は二分類を主役にし、
profile の全次数は注記に留める。

**幾何対応(仮説)**: 構造 Atom は幾何の底(site・被覆・nerve)を張り、
意味 Atom はその上の切断として振る舞う。one-cent ドリフトでは呼び出し
グラフ(構造)が被覆を与え、金額解釈(意味)が各パッチ上の切断、流儀の
食い違いが 1-コサイクルだった。大域的に定まる事実と、局所的な使用でしか
定まらない事実の二種があるから、局所的使用を大域的意味へ貼り合わせる問題
=層の条件が必然的に生じる。これが「なぜ AAT が層理論的になるのか」への
答えである。

## 3. 柱2 — 読みの規律(接地・反証・輸送)

「読み方を変えれば Atom も変わる」を工学として強くする締め具は三つある:
接地、反証、輸送。

### 3.1 接地 — 意味 Atom は証拠から計算される

意味 Atom の抽出は、evidence の観測、rule による解釈、Atom の採用の三段に
factorize する。

```text
Extracts_D(s,a) -> ∃ e, Observed_D(s,e) ∧ Interprets_R(e,a)
```

逆向き(観測された evidence から Atom が必ず採用される)は completeness
として別 statement に置く。`semantic(amount, denotes cents)` を主張するには、
100倍している箇所、cents を名乗る変数名、単位を検査するテストといった
構造的証拠 `e` への参照が要る。doctrine の自由度は「証拠の読み規則の選択」に
縛られ、二つの doctrine の差分は diff 可能な成果物になる。接地条件は
doctrine の許容性条件として置き、A0–A8 は無傷のまま保つ。

実装形は、existential を data に強めた grounding certificate を採る。

```text
Grounding_D(s,a) := Σ e, Observed_D(s,e) × Interprets_R(e,a)
```

extractor は Atom と certificate の組を返し、certificate を忘却したものが
canonical Atom family になる(A8 の family uniqueness は忘却後も維持)。
doctrine 間の差分は「同じ Atom をどの evidence と rule で採用したか」の
diff になり、counter-witness が実行可能になる。

### 3.2 反証 — 読みは誤りうる

接地された読みの反証器は三つ。

- counter-witness: 採用した意味 Atom と矛盾する構造的証人の提示
- holdout での予測失敗: 読みが予測する障害 / 非障害が別の観測で外れる
- doctrine 射との非可換: 輸送と抽出が可換にならない

「現に動いているシステムに大量の非零障害を出す読みは疑わしい」は
反証条件に採らない。実際に不整合な系を正しく読めば、大量に出てよい
からである。

### 3.3 輸送 — reading の塔と lift

工学が要求すべきは Atom の絶対性ではなく**結論の安定性**であり、
安定性は三つの別 statement に分ける。

```text
(1) doctrine 同値に対する不変性
(2) refinement に対する保存・反映
(3) 一般の翻訳 / base change に沿った輸送
```

この三つを語る土台は doctrine の圏である。ただし doctrine の射
`f : D -> D'` だけから site・係数・障害類の comparison は生えない。
現行 Lean では `ExtractionDoctrine` が直接決めるのは `extracts` と
canonical Atom family までで、その先は `CoreReading`(composition /
object / equation / invariant / signature / operation の読み)と
`ReadingCore`(geometry・coefficient・raw restriction system)が
別データとして載る。必要なのは、doctrine の変更を full reading の変更へ
持ち上げる **lift のデータまたは定理**である。

full reading は単一の圏に丸めず、段階の異なる reading を**射影の塔**に置く。

```text
Doct_U       : doctrine そのもの
ExtInst_U    : pointed extraction instance (D : ExtractionDoctrine U, s : D.Source)
CoreRead_U,S : 固定した U・AtomAxiomSystem S 上の AATCorePackage
GeomRead_U   : ReadingCore(core + geometry + coefficient + raw)
ObProblem(p) : local data から具体的 obstruction class を導く問題

ObProblem -> GeomRead -> CoreRead -> ExtInst -> Doct
```

塔の各段には現行実装上の根拠がある。

- **`ExtInst` の分離**: canonical Atom family を決めるのは doctrine と
  source の組である(`CoreReading` 自身が `doctrine` と依存型の `source` を
  別々に持つ)。doctrine 単体を対象にすると、atomization comparison の
  段階で source の輸送が後付けになる。
- **core 段の対象は `AATCorePackage`**: `CoreReading` は生成レシピであり、
  既存の `SignedExactCoreReadingHom` / `PositiveCoreReadingHom` も
  `AATCorePackage` の間の射として定義されている。
- **class 構成は最上段 `ObProblem`**: `ReadingCore` は scheme・ideal・class を
  意図的に後段へ残している(docstring に明記)。concrete class は local data
  から構成し、naturality を上段で証明する。これは結論相当データの先渡し
  (certificate escape)を避ける規律の圏論版でもある。

各段の上には複数の選択がありえ、下の射に沿って上の対象を運べるとは
限らない。**運べる場合の lift が transport** であり、上の三分類は性質の
異なる lift として整理する。4つの comparison は塔の段ごとに分ける:

- `ExtInst -> Doct`: source と extraction の comparison
- `CoreRead -> ExtInst`: composition・object・equation・invariant・
  signature・operation の lift
- `GeomRead -> CoreRead`: site・topology・coefficient・raw system の lift
- `ObProblem -> GeomRead`: 構成された cocycle / class の naturality

こうすると、lift がどの段で失敗したかを常に特定できる。実装上は、既存の
`Formal/AG/ReadingFunctoriality/` が上層(reading 間比較)を持つため、
塔は **Atom 抽出から既存 ReadingFunctoriality へ接続する下層**として置く。
一般論(indexed category / fibration)は最初から実装せず、固定した
`AtomCarrier U` 上で具体的な lift から始める。**最優先構成対象は塔の下層
(`ExtInst -> Doct` と `CoreRead -> ExtInst`)である。**

### 3.4 Agent SKILL — constructor から section への梯子

一回の SKILL 実行が行うのは、入力 `(D, s, Law, evidence)` の上の fiber から
admissible な object を一つ構成することである。その位置づけは梯子で測る。

```text
partial certified constructor -> cleavage -> section
```

まずは admissible な入力部分圏上の **partial certified constructor**。
射に沿う transport を選ぶ段階は cleavage / lifting operation。
functoriality が証明できた時点で、初めて section と呼ぶ。section の非存在は
「Agent が instance designer の判断を完全には消せない理由」として意味のある
結果になる。「人間に代数幾何を選ばせず SKILL が理論を抽象化する」という
既定の製品方針は、この梯子のどこまで登れたかとして測定できる。

### 3.5 輸送の形式化仕様 — Gr1 から Gr2 へ

グロタンディーク的相対性(§1)の償還条件を、現行 Lean シグネチャに
対する仕様として固定する。鍵は次の事実である: **上層の輸送データ型は
実装済みであり**(`SignedExactCoreReadingHom` の field 群)、未了なのは
**底(doctrine の射)からのその構成**である。§1 の四成分は field に
対応物を既に持つ。

```text
Atom family の輸送     ↔ extraction_eq
                          (Q.family = P.family.transport atomEquiv)
係数(方程式系)の輸送 ↔ equationTransport(EquationSystemExactTransport)
障害検出データの輸送   ↔ detectorCode_eq(signed template の transport)
site 側の素材          ↔ objectMap / configuration_eq
                          (nerve への接続は候補9 が担う)
```

したがって「比喩ではなく数学」への正確な残作業は、これらの field を
結論として導く底の射の圏と lift の構成に尽きる。以下を設計判断として
固定する。

**(1) Doct_U の射。** `ExtractionDoctrine U` の間の射 `σ : D -> D'` は
次のデータ:

```text
sourceMap  : D.Source -> D'.Source
atomMap    : U.Atom -> U.Atom(exact 版は U.Atom ≃ U.Atom)
normalize 可換: sourceMap ∘ D.normalize = D'.normalize ∘ sourceMap
admission 比較(二種):
  exact 射     : D.extracts s a ⟺ D'.extracts (sourceMap s) (atomMap a)
  refinement 射: D.extracts s a ⟹ D'.extracts (sourceMap s) (atomMap a)
                 (反映は独立条件として分離)
```

スライス b の「exact / refinement の二種類の下層射」の正確な内容は
この二つである。carrier `U` は第一次イテレーションでは固定する(§3.3)。

**(2) ExtInst_U と射影。** 対象 `(D, s)`、射 `(D, s) -> (D', s')` は
`σ : D -> D'` と `s' = σ.sourceMap s` の組。忘却 `ExtInst_U -> Doct_U`
が塔の最下段の射影になる。

**(3) 輸送の第一 statement。** exact 射に対する atomize の自然性:

```text
D'.atomize (σ.sourceMap s) = (D.atomize s).transport σ.atomEquiv
```

これは `SignedExactCoreReadingHom.extraction_eq` と同じ等式であり、
**塔仕様と既存実装の握手点**である。refinement 射では等式が包含に
弱まり、反映の失敗が「新しい Atom がどの family・composition に
入るか」の追加データを要求する。

**(4) 輸送 = opcartesian lift。** package の hom `F : P -> Q` が
`σ` の上にあるとは、F の底への射影が σ に一致すること。F が
opcartesian であるとは、σ を通して factor する任意の hom が F を
通して一意に factor すること。**transport とは opcartesian lift の
選択(op-cleavage)である。** 引き戻し側の cartesian lift も存在する
とき射影は bifibration になり、§6 の polarity の随伴はその categorical
形として回収される。「Grothendieck 的」の語はここで比喩から装置名に
変わる — 塔の射影を Grothendieck (op)fibration として立てる、という
文字通りの意味である。

**(5) Gr2 の証明対象4点**(スライス a–c の形式仕様):

```text
(i)   transportAlong: exact σ と P から Q = P.transport(σ) を構成し、
      tautological hom P -> Q が σ の上の opcartesian であることを示す
(ii)  opcartesian lift の同型を除く一意性(FiniteModel 上)
(iii) refinement 負例: exact lift が存在しない σ_ref を一つ構成し、
      lift に本当に必要な追加仮定(新規 Atom の composition /
      equation データの供給)を抽出する
(iv)  四成分の輸送((3) 冒頭の field 対応)が (i) の一本の構成から
      すべて導出されることの確認
```

**達成階梯**(§1 の比喩宣言の償還スケジュール):

```text
Gr0 比喩(本ノート初版の状態)
Gr1 statement 化: 四成分すべてに定理候補+機構+検査計画(本節で到達)
Gr2 構成された実例: 上記 (i)–(iv) が FiniteModel + Lean で立つ
Gr3 擬関手的整合: 候補17 の 2-障害込みで輸送が段横断に合成する
Gr4 base change 完備: doctrine 圏の fiber product(§10 ギャップ2)込みで
    相対的視点の全操作が閉じる
```

Gr2 が立った時点で §1 の比喩宣言は撤回可能になり、Gr4 で EGA 的な
意味の相対性に届く。descent 側(第X部・候補11・13)が先行して厚く、
base change 側が最後に残るのは、代数幾何の歴史と同じ順序である。
(記号 Gr は換金在庫の G1–G7(§9)との衝突を避けるための接頭辞である。)

### 3.6 沈黙の規律と系譜

読みに依存する結論は消さず、依存することを明示 scope として結論の近くに
書く(沈黙の規律の定理化)。この沈黙は前期ウィトゲンシュタイン(語り得ぬ
ものへの沈黙)の姿勢、意味 Atom の「意味は使用」は後期(言語ゲーム)の
姿勢であり、AAT は**論考的沈黙を言語ゲームごとに複数化して使う**:
「私の contract の限界が私の結論の限界である」を、宣言されたゲームごとに
立てる。

CS の実績ある道具はすべてこの形をしている(型検査は型システムに、
静的解析は抽象領域に、モデル検査は抽象化に相対的)。強さの根拠は、
フレームが宣言され、フレーム固定の下で決定的・再現可能で、健全性定理が
フレームとの関係を保証していることにある。Atom 基礎論の健全性定理の形:

```text
接地された doctrine の下で抽出は決定的かつ再現可能(A8 の強化)
診断は doctrine 同値の下で不変(新規)
```

科学哲学の系譜でも同じ位置にある。接地は doctrine を制約するが決定しない
— Duhem–Quine の過小決定であり、「宣言・版管理・diff・不変性定理」は
その古典的問題への工学的応答として読める(R4 の論拠に加える)。

ArchMap 実務での抽出(機械的に取れる部分)と調停(判断が要る部分)の
分割線は、構造 / 意味の分割線と一致している。抽出コストと再現性の経済が
理論の二分類と同じ場所で折れることは、CS 的自然さの経験的証拠である。

## 4. 柱3 — 欠陥の相対性

構文エラーは構造的で一意に見えるが、one cent をどう扱うか、小数点以下を
切り捨てるかは仕様であり、仕様に相対化される問題である。AAT の語彙では:

```text
欠陥とは、コード単独の性質ではなく、選択された geometry・law・係数・
local data が生成する graded obstruction class の非消滅であり、
その非消滅が対応する effectivity failure を表す。
```

第IV部は H^0 の visible defect、H^1 の gluing obstruction、H^2 の
coherence obstruction、concrete class の指定を分けている。個々の bug と
class の同一視は、その class を生成する**比較定理がある場合の系**として置く。

相対性は三層に分解される。

1. **そもそも欠陥か** — 方程式系の選択に相対的。方程式系を宣言しなければ
   バグは未定義。ArchSig が LawPolicy なしに結論を出さない入力トライアド
   規律の理論側の根拠である。
2. **どこが悪いか** — 固定した複体の中で、代表コサイクルの取り方は一意で
   なく、代表の取り替えで責任は coboundary 分だけ移動する。**blame は
   ゲージ選択**であり、「A と B のどちらが直すべきか」が決着しないのは
   認識不足ではなく構造である。
3. **欠陥があること** — 方程式系を固定すれば不変。どの代表を選んでも、
   どこへ責任を移しても、類が非零である事実は消えない。

「欠陥 = violation」は方程式系の規範的権威を前提する。AAT は仕様がなぜ
拘束するかを説明せず、**拘束性を入力として受け取る**(宣言され執行される
contract に還元する)。これは一つのコミットメントであり、入力トライアド
規律と同じ姿勢の理論版である。

系として、現場の既知現象が再現される:

- 全サービス単体テスト pass で結合すると壊れる = 局所 lawful で大域類が非零
- 結合バグが難しい = H^1 に住むものは局在化できない
- 「バグではなく仕様です」= 方程式系の弱化に沿って類をゼロへ押し出す操作。
  デスコープは修理の一種として理論に乗り、SAGA 的 repair(coboundary での
  放電)と仕様弱化(要求自体を削る)が数学的に区別できる二種の放電になる
- 構文エラーが絶対に見える = 文法フレームが言語共同体全体に共有され
  コンパイラが執行しているから。欠陥の客観性もフレーム共有度のスペクトル

コホモロジー次数は実務の分類と対応する(仮説):

```text
0次の欠陥: 一つのパッチ上で方程式を破る = 単体テストで捕まるバグ
1次の欠陥: 局所的に合法、重なりで不一致 = 結合バグ(局在不能、blame はゲージ)
```

「CS 的に Atom 公理が自然か」への答え方はここで変わる。公理を外部理論と
突き合わせて弁護するのではなく、**この公理系から出発すると、エンジニアが
全員知っている現象群が定理の系として再現される**ことを自然さの論拠にする。

## 5. 柱4 — 解像度の原理

Atom の原始性は存在論ではなく宣言である。定義1.1 の「それ以上分解**せずに
扱う**」の「扱う」が仕事をしており、Atom は分解停止の宣言である。だから
底なし(終対象なし)でも理論は困らない。下へ降りることは真理へ近づく
ことではない。

アセンブラを Atom とすることへの違和感の正体は、語彙と方程式系の解像度の
不整合である。アーキテクチャの法(金額の同定、認可の保存、契約の可換性)は
アセンブラの語彙の上では表現を持たず、方程式が何も語れない Atom 族の上の
幾何は構造を持たない。逆にコンパイラ検証や組込みのタイミング解析なら、
ISA 上の方程式系が現にそこに住んでおり、アセンブラ Atom が正しい解像度になる。

```text
Atom の解像度は、語りたい方程式系が語れる解像度によって決まる。
方程式が沈黙する深さまで降りない。
```

定式化は二段。第一段は、`(V, ρ)` と方程式系を「Law が表現可能」という
条件で結ばれた compatible triple `(V, ρ, Law)` として定義する。第二段は
普遍性である。選択した law family `L` に対して、source の読み `q` が
**`L`-adequate** であるとは、すべての law evaluation が `q` を通して
factor すること。`L`-adequate な atomization を factorization で順序づけ、
最も粗い adequate reading が存在するとき、それを **law-relative canonical
resolution** と呼ぶ。

```text
atomization reading = 選択した方程式系に対する最小十分抽象
Atom = その reading の下での primitive
```

これで「方程式が沈黙する深さまで降りない」は標語ではなく普遍性で言え、
Agent の resolution 選択は「最小十分な読みを探す」という具体的な仕事になる。
最粗の adequate reading の存在は保証されず、その非存在も「なぜ instance
designer の選択が残るのか」を説明する意味のある結果である(§6)。

解像度の選択は、底の共有度(深いほど普遍的)と方程式の表現力(深いほど
痩せる)のトレードオフの上の選択である。doctrine の選択は理論のユーザー
ではなくインスタンス設計者の仕事であり、「エンジニアは代数幾何を習得
しなくてよい、SKILL が理論を抽象化する」という既定方針の理論的根拠になる。

## 6. Atom が先か方程式系が先か

「最小十分抽象」(§5)からは、Atom が先か方程式系が先かという問いが立つ。
答えはレベルを分けると定まる。

**対象レベル(doctrine 固定後)では Atom が先である。** A0(primitive
existence)と A5(law non-generation)がそのまま立ち、law は Atom を
選別するだけで生成しない。A5・A6 は、対象レベルを設計レベルから守る
公理として読み直せる: doctrine が固定された後は、law も観測も Atom を
生成しない。

**設計レベル(doctrine を選ぶ)では、どちらも先ではない。** 定式化は
二つのレベルを分ける。law family `L` に対する adequacy を二項関係
`Adequate(q, L)` として置くと、任意の二項関係が与えるのは readings と
laws の**冪集合の間**の polarity(antitone Galois connection)である。
formal concept は readings の集合と laws の集合の閉対であり、個々の
compatible triple が自動的に閉対になるわけではない。point-valued な随伴

```text
res(L) ≤ q  ⟺  L ⊆ Expr(q)
```

が立つのは、`L` を adequate にする readings の集合(extent)が最小元
`res(L)` を持つ、すなわち **extent が principal** な場合に限る。
順序は次のとおり。

```text
1. adequacy relation から冪集合上の concept lattice を作る
2. どの extent が principal かを特徴づける
3. principal な場合だけ res(L) を reading として取り出す
```

この言葉で、compatible triple(§5)は principal extent に対応する閉構造の
点表現であり、閉包はどの law からも見えない Atom を刈る操作になる
(「方程式が沈黙する深さの Atom はノイズ」の定理化)。閉包が冪等でも、
異なる初期値が同じ閉対へ到達するとは限らない。二つの入口の合流は、
「両者が同じ formal concept を生成する条件」として別 theorem に立てる。

明快な**基準模型**がある。source 上の全 law evaluation が関数として
与えられる ambient な Set の世界では、joint-kernel quotient

```text
x ~_L y  iff  すべての l ∈ L について eval_l(x) = eval_l(y)
q_L : Source -> Source / ~_L
```

が常に最粗の `L`-adequate reading になる。**ambient には canonical
resolution が必ず存在する。** 難しい問いは「その quotient が許容 doctrine・
有限性・計算可能性・接地条件の中で表現可能か」であり、`res(L)` の非存在は
**選んだ admissible reading class における representability failure**
として読む。この二段構え(ambient での存在+admissible class 相対の
表現可能性)は論文の主結果になりうる。CS 側では minimal sufficient
statistic や Myhill–Nerode 型の最小商(観測で分離する最粗の合同)との
接続が見える。

「どちらが先か」を随伴で解消するのは、代数幾何が通った道でもある
(空間が先か環が先か — `Spec ⊣ Γ`、Gelfand 双対性)。言語ゲームにおいて
語と規則が相互構成的であることとも整合する。実務にも両方の入口が実在する:

```text
グリーンフィールド設計 = 方程式系が先
  (要求から必要な観測語彙を導出する。q_L の構成)
レガシー考古学 = Atom が先
  (まず抽出し、その語彙で表現可能な law を発見する。Expr(q) の計算)
```

ArchSig の沈黙規律はここで運用上の検出器になる: **評価できない law に
対する沈黙は、non-adequacy の実行時検出**である。

## 7. 既存ソフトウェア意味論との接続

Atom 基礎論は白地に立つのではない。§5–6 の adequacy / canonical
resolution の構図は、既存のプログラミング言語意味論の中心問題と
項ごとに対応する。Atom 基礎論は土台であり、それ自体の新規性は要求
しない。土台は既知の枯れた構造だけで組まれているほど強く、接続の
多さは脅威ではなく信頼性の証拠である。接続を明示することは三重に効く。

1. **証明技術の輸入**: 定理候補に既存の証明技術と先例を輸入できる
2. **自然さの証拠**: 既知の理論がインスタンスとして再現されることが、
   既知の工学現象の再現(R4)と並ぶ自然さの論拠になる
3. **仮定監査**: 各接続点の古典定理は既知の最小仮定を持つ
   (Hennessy–Milner の image-finiteness、complete shell の Scott
   連続性、Cook の expressiveness)。A0–A8+接地条件がそこへ正しく
   特殊化するかの突合が「仮定が適切か」の実行可能な検査になる。
   AAT の仮定が古典の最小仮定より強く出る箇所は、弱化すべき仮定か、
   architecture スケールで本当に必要な追加仮定かの判定問題になり、
   どちらに転んでも成果である

### 7.1 full abstraction との対応(定理候補6の正体)

§5 の L-adequacy と §6 の ambient joint-kernel quotient は、表示的
意味論の adequacy / full abstraction と正確に対応する。

```text
law family L                   ↔ 観測文脈の族(contexts + observable)
eval_l                         ↔ obs(C[−])
L-adequate な読み q            ↔ 健全(adequate)な表示モデル:
                                  ker q ⊆ ~_L(⟦M⟧=⟦N⟧ ⟹ M ≅_ctx N)
最粗の adequate reading res(L) ↔ fully abstract モデル: ker ⟦−⟧ = ≅_ctx
ambient q_L(常に存在)        ↔ Milner 1977 の項モデル商構成
admissible class 内の          ↔ full abstraction 問題そのもの
representability                  (その商を「良い圏」で表示できるか)
```

用語の向きも衝突しない(PL 意味論の adequacy は健全方向であり、
本ノートの L-adequacy と同方向)。§6 の二段構え「ambient では常に存在、
難しいのは admissible class 内の表現可能性」は PCF の歴史そのものである。

- Milner 1977: fully abstract モデルは項の観測同値による商として常に
  存在する(§6 の ambient 存在に対応)
- Plotkin の parallel-or: Scott domain という admissible class では
  その商が表現できない(representability failure の古典例)
- ゲーム意味論(Abramsky–Jagadeesan–Malacaria / Hyland–Ong):
  別の admissible class を発明して解決した。ただしゲーム意味論ですら
  最後に extensional quotient を一度かける。商を構造的に表示すること
  自体の本質的困難の証言である
- Loader 2001: 有限 PCF の観測同値は決定不能。representability の
  特徴づけが一般には決定不能でありうる先例であり、実験スライスを
  有限モデルに絞る現行方針(§12)の防御材料になる

この対応により定理候補6は認知された難問の系譜に着地し、logical
relations や definability 論法といった証明技術を輸入できる。

発展形として、コンパイラを言語間の翻訳と見る fully abstract
compilation(文脈同値の保存・反映)と、それを trace property / safety /
hyperproperty / relational hyperproperty のクラス別に成層した robust
property preservation 階層(Abate 他)がある。full abstraction はその
一点にすぎず、hyperproperty は一般に refinement-closed でないことも
既知である。base change に沿った輸送(§8 候補3)を law class ごとに
成層する先例になる。

### 7.2 抽象解釈 — principal extent 失敗の実務先例

§6 の polarity(antitone Galois connection)の同族である Galois 接続は
抽象解釈(Cousot–Cousot)の土台である。効く先例は二つ。

- 多面体ドメイン(Cousot–Halbwachs 1978)には Galois 接続がない。
  円板に最小の外接多面体は存在しないからである。「principal extent が
  立たない」ことの、実用中の抽象ドメインでの具体例
- その実務的応答が widening 演算子である。canonical な選択がないとき
  instance designer が非正準な選択を明示的に注入する装置であり、
  「res(L) の非存在は instance designer の選択が残る理由」(§5–6)の
  工学的裏づけになる

さらに completeness 理論と repair の系譜が効く。

- complete shell(Giacobazzi–Ranzato–Scozzari): 任意の抽象領域を
  与えられた関数について complete にする最も抽象的な精細化が構成的に
  存在する。固定した admissible class 内での canonical refinement の
  構成的存在定理であり、候補6の中間問題(adequacy shell)の雛形になる
- abstract interpretation repair: プログラムではなく抽象領域(読み)の
  側を修理する系譜がすでにある。放電経路の三分法(§8 候補5)の先例

抽象領域を「証明したい性質から選ぶ」ことは抽象解釈の実務ではすでに
規範であり、§5 の解像度原理はその定理化として位置づく。

### 7.3 観測同値の族 — concept lattice の既製インスタンス

- van Glabbeek の linear-time / branching-time spectrum: 観測概念の族を
  パラメータに、プロセス同値が束をなすことを網羅した仕事。§6 の
  「adequacy relation から concept lattice を作る」の、プロセス代数で
  完遂済みの実例
- テスト意味論(De Nicola–Hennessy): may / must テストの選択で同値が
  変わる。law family の取り替えで `~_L` が変わることの定理群
- 双模倣は観測を尊重する最粗の合同であり、partition refinement
  アルゴリズムは有限状態での `q_L` の実効的計算に相当する。
  スライス d(§12)には既製のアルゴリズム系譜があることになる
- Hennessy–Milner 定理: image-finite な遷移系では論理的同値と双模倣が
  一致する。有限性仮定つき representability の古典形である。coalgebra
  版では final coalgebra の存在と Hennessy–Milner 性を持つ論理の存在が
  同値になる(Goldblatt)。「canonical な最小模型の存在 ⟺ law family
  の表現力」という、候補6が目指す statement と同じ形の既存定理

### 7.4 institution 理論 — 輸送 statement の最近傍先行研究

Goguen–Burstall の institution は「truth is invariant under change of
notation」を公理化した抽象モデル理論である。satisfaction condition

```text
M'|_σ ⊨ φ  ⟺  M' ⊨ σ(φ)
```

は §3.3 の輸送不変性 statement の直接の祖先であり、signature ↔ 語彙
`V`、sentence ↔ law、model ↔ 読み、と対応する。Diaconescu の
Grothendieck institution(institution の族への Grothendieck 構成)は
reading の塔を fibration として扱う際の既製の道具立てであり、
定理候補3(輸送定理群)の related work の正本はここになる。

### 7.5 その他の接続

- Hoare 論理の相対的完全性(Cook 1978): 完全性は表明言語の
  expressiveness に相対的である。§5 の compatible triple「Law が
  表現可能」条件の公理的意味論版
- Gurevich の ASM テーゼ: あらゆるアルゴリズムは固有の抽象化水準で
  忠実に捕捉できる(逐次版は公準から証明済み)。解像度の原理の従兄弟
- domain theory in logical form(Abramsky): 観測可能性質と領域の
  Stone 型双対。§6 の `Spec ⊣ Γ` 類比の、CS に内在する実例
- ゲーム意味論と言語ゲーム: full abstraction を最終的に解いたのは
  「意味は相互作用(使用)である」を文字通り数学化したゲーム意味論で
  あり、本ノートの後期ウィトゲンシュタイン路線と full abstraction
  路線は歴史的に同じ場所で合流している。論文の narrative として使える

### 7.6 障害コホモロジーの先行適用

貼り合わせ障害を Čech コホモロジーで測る手法自体には、CS 隣接領域に
先行適用がある。AAT の位置づけはこれらとの対比で決まる(§7.7)。

- 量子文脈依存性(Abramsky–Barbosa 他): 局所測定結果の presheaf に
  対する Čech H^1 で大域切断の障害を特徴づける。関係データベースや
  制約充足への展開も本人たちが行っている。重要な既知の限界として、
  この障害の非零は十分条件どまりであり、類が零でも大域切断が存在
  しない false negative がある。後続研究は係数を semi-module(半環
  係数)へ一般化して解消した。アーベル群化で正値性情報が落ちることが
  原因である(§8 候補8へ接続)
- センサーデータ融合(Robinson): 観測の一貫性を層で測り、大域切断
  からの距離 consistency radius という定量的障害を定義する
- 分散計算: 分散タスクの可解性を task sheaf の大域切断として特徴づけ、
  決定空間の障害をコホモロジーで記述する仕事がある
- 並行計算の directed algebraic topology(Fajstrup–Goubault–Haucourt–
  Mimram–Raussen): 実行空間のホモトピー / ホモロジーで並行系を分類する
- 2026 年に入っても近接領域の論文が続いている(model-based systems
  engineering の多視点一貫性、AI agent の theory shift 検出、component
  ensemble の層意味論)。続出はこの種の土台への需要の証拠であり、
  novelty 競争の脅威ではなく related work を丁寧にする理由として扱う

### 7.7 AAT の差分と評価規準

長い CS と数学の歴史の上に立ち、既知構造の再配置であることをむしろ
積極的に示す。差分の特定は novelty の主張ではなく、新規性の主張を
上層(SAGA・輸送定理群・tooling)へ正しく配置するための位置特定で
ある。差分は四つ。

1. **フレーム選択自体が対象。** 古典意味論は言語と観測を一度固定して
   全プログラムを研究する。AAT は doctrine の圏と reading の塔を作り、
   フレーム間輸送を主題化する。最近傍の institutions にも、抽出・接地・
   障害層はない
2. **コホモロジー層の置き場所。** 障害コホモロジーの使用自体は §7.6 の
   とおり先行がある。AAT の差分は「何の上のコホモロジーか」にある:
   site と被覆が law equation system と doctrine から立ち、係数が
   観測商(Atom 層)の上に載り、全体が doctrine 相対で輸送定理群を
   伴う。PL 意味論本体(§7.1–7.5)に限れば H^1 は現れない
3. **抽出の主題化。** 意味論は構文を所与とする。AAT は source からの
   抽出と grounding certificate を理論対象にする
4. **合成性の軸の取り替え。** 表示的意味論の compositionality は
   構文木上の準同型性、AAT の層条件は被覆上の貼り合わせである

位置づけの規律: 各接続は自分から明記し引用する(候補6は full
abstraction の一般化である、等)。その上で、土台の評価規準は新規性
ではなく次の四つに置く。

1. **自然さ**: 既知の工学現象(R4)と既知の理論(§7.1–7.6)が系・
   インスタンスとして再現される
2. **仮定の適切さ**: 仮定監査(§7 冒頭)に耐える
3. **普遍性(条件付き)**: 宣言された底と law family を持つ任意の
   ソフトウェアに適用でき、種別横断のインスタンスで例証される(R5)
4. **fruitfulness**: 上層が現に建っている(SAGA 定理・ArchSig)。
   土台の有効性を約束ではなく実績で示す

## 8. 定理候補(すべて未証明の仮説。反例探索を先行させる)

判定規律として **strip test** を置く: AAT 固有の構造(二相分解・接地・
doctrine の塔・architecture site)を仮定から抜いたとき、古典定理に
退化するか無意味になる statement だけを新規性の担い手と数える。
退化しないものは古典理論の翻訳であり、土台の較正(§7)として扱う。
新規性は個々の部品ではなく、古典的機構(長完全列・comparison map・
定義可能性)を AAT 固有の構造が指定する場所で発火させる交差点に立つ。
この規律の下で、候補1・4・5・7・8・9・10 が非自明性の担い手、
候補2(a)・3・6 は土台の較正寄りである。

候補11–19 は探索由来であり、strip test 通過を採録条件とした。候補1–10 が単一の読みの内部を垂直に掘る(二相・解像度・接地)のに
対し、11 以降は別の鉱脈に立つ: 読みの複数性(11)、正当化の層(12)、
被覆の適格性と取り替え(13・18)、二相軸の全次数化・族化(14・16)、
law 族の方向(15)、二階の整合(17)、source 側の対称性(19)。
候補20 は換金在庫(§9)からの昇格、候補21–29 は換金探索由来である。
探索段階で比喩どまりの案(properness = 負債有界性、generic point =
典型実行、flaky = 多重度、epsilon = 双対数)は換金テストで棄却済み。

1. **二相長完全列と非輪状定理(obstruction support の鋭化)**: 層の
   短完全列が立つ条件下で、長完全列から次を導く。

   ```text
   0 -> F_struct -> F_all -> F_sem -> 0
   H^1(F_struct) = 0 のとき H^1(F_all) ↪ H^1(F_sem)
   ```

   構造 nerve が木状(依存グラフに 1-サイクルなし)なら構造側 H^1 の
   消滅条件が整い、「非輪状アーキテクチャでは結合バグはすべて意味的で
   ある」が定理になる。対偶「構造サイクルはある種の結合欠陥の必要条件」
   は one-cent が nerve の 1-サイクル上に立つ事実と整合し、「ループが
   結合バグの住処」という folklore が系として導出される(R4 直結の
   反証可能な予言)。無条件版(「非零の障害類は必ず意味 Atom の上に
   support される」)は採らない。大域的 canonical family の存在だけでは
   flasque 性も descent 有効性も従わず、構造データ自体も build
   configuration・生成コード・schema version などで貼り合わないことが
   あるからである。まず「構造 Atom だけでも descent が失敗する反例」
   または「短完全列と消滅を成立させる最小仮定」を探索する。なお消滅
   機構単体(forest + face なし + restriction 全射 ⟹ H^1 = 0)は
   第IV部定理12.4 として既存であり、本候補の新規部分は二相分解との
   積にある(研究ループでの再証明を避ける)。face が loop を埋める
   regime では `H^1(F_struct) = 0` 条件にも系12.3 の face 補正が要る。
2. **Blame gauge(二分)**: (a) 固定した複体の中で代表元が coboundary 分
   だけ動くこと(cohomology の statement)。(b) doctrine の変更で複体
   そのものが変わること(comparison map と naturality が必要)。
   blame の移動(a)と defect class の輸送(b)を混同しない。
   後段の拡張として、修正コスト・authority・ownership・risk の非対称性を
   gauge orbit 上の cost functional として置き、運用方針に相対的な
   gauge fixing で修正候補を選ぶ道がある(「canonical blame はない」を
   「何も選べない」にしない。ArchSig が修理候補の提示まで進む際に効く)。
   構成的インスタンス: 基点 chart(オーナー)を宣言すると各 divisor 類は
   一意の q-reduced 代表を持ち、Dhar の burning algorithm で計算可能
   (候補20 の系)。正準性はオーナー宣言に相対化され、宣言変更で正規形は
   予測可能に変わる — オーナー宣言 = 入力 contract という ArchSig の
   姿勢と同型。
3. **輸送定理群(lift の存在と性質)**: reading の塔(§3)の各段の射影の
   下で、下層射に沿った (1) doctrine 同値不変性 (2) refinement 保存・反映
   (3) 一般の翻訳 / base change 輸送。段ごと・種類ごとに別の仮定と結論を
   持つ lift statement とし、lift が存在しない場合にその段の transport へ
   本当に必要な追加仮定を抽出することも成果と数える。輸送の強さが
   law のクラスに依存することは最初から前提にする。robust property
   preservation 階層と hyperproperty の refinement 非閉性(§7.1)が、
   (2) の保存・反映が law class ごとに割れることの既知例である。
4. **診断の解像度不変性**: 二つの L-adequate な読み `q ≤ q'` に対し、
   law 由来の係数で計算した障害類が comparison map の下で canonical に
   同型になる条件の特定。

   ```text
   adequate な範囲内では、解像度の選択は診断を変えない
   ```

   直観的根拠は「係数は law が生成し、law は潰された区別を見ない」だが、
   被覆の像の振る舞いに条件が要り、そこが定理の中身になる。系:
   必要以上に細かく測っても診断は増えない(過剰解像度の無益性)。
   ArchSig の粒度選択が暗黙に依存する事実の定理化である。範囲外
   (inadequate な粗化)での偽の類の発生・真の類の隠蔽の定量化を対に
   する。接地された doctrine の下での抽出の決定性・再現可能性
   (旧・健全性候補)は定義的基盤としてこの候補の前提に置く。
5. **デスコープの押し出し**: 方程式系の弱化に沿う類の押し出しとしての
   仕様変更。repair(coboundary 放電)との数学的区別。弱化で類は消えるが
   repair cochain は存在しない例の構成を含む。この二つに、読みの修理
   (doctrine の変更で類を消す輸送。抽象解釈の domain repair が先例。
   §7.2)を加えた放電経路の三分法として扱う。第三の経路は複体そのものを
   取り替えるため、候補2(b) の comparison map を要する。
6. **Law-relative canonical resolution(representability)**:
   (a) adequacy relation の concept lattice における principal extent の
   特徴づけ。(b) ambient joint-kernel quotient `q_L` の、許容 doctrine・
   有限性・計算可能性・接地条件の中での representability の特徴づけ
   (§5–6)。representable なら解像度選択の普遍性が立ち、failure なら
   それ自体が「instance designer の選択が残る理由」の記述になる。
   (c) 二つの入口(方程式系先行 / Atom 先行)が同じ formal concept を
   生成する合流条件。本候補は full abstraction 問題の AAT 版である
   (§7.1 の対応表)。(b) の一般的特徴づけは Loader 型の決定不能性に
   阻まれうるため、まず有限モデル(§12 スライス d)で representability
   の正例・負例を固定する。(b) の中間問題として、res(L) が
   representable でない場合にも、与えられた読み q を含む最粗の
   L-adequate 精細化(adequacy shell)の構成的存在を問える(complete
   shell が先例。§7.2)。statement の雛形は「canonical resolution の
   存在 ⟺ law family の expressivity」という Goldblatt 型の双条件
   (§7.3)。
7. **Beth 型因子化定理(Atom-interface completeness の精密化)**:
   因子化テーゼ(§1)を invariance ⟹ definability の形に立てる。

   ```text
   doctrine 同値で不変な結論は、canonical Atom family を通して factor する
   ```

   古典論理の Beth definability(暗黙に定義可能なら明示的に定義可能)と
   同型の statement であり、Craig interpolation 系の証明技術を輸入する。
   Beth 性は論理によって成立したり破れたりするから、この定理は
   doctrine の圏の性質に依存する実質的内容を持ち、成立条件の特徴づけ
   自体が結果になる。Atom 層を迂回する結論の反例探索を先行させる。
8. **係数忠実性(coefficient faithfulness)**: 係数構造の選択が、障害類の
   どの effectivity failure を検出できるか(忠実性)を決めることの定式化。
   contextuality のコホモロジーでは類が零でも貼り合わせ不能な false
   negative が知られ、semi-module 係数への一般化で解消された(§7.6)。
   AAT の nu/epsilon 二族についても (a) 類零だが貼り合わせ不能な例の
   構成 (b) 忠実性が改善する係数一般化の特徴づけ、を問う。既存の
   faithfulness 検証で観測された判別力の天井(判別が support 対で
   止まる現象)の理論的説明を目標に含める。
9. **構造被覆の底不変性**: 構造 Atom の定義(依存 profile が (Γ, R) に
   不感)から、構造 Atom が張る nerve は語用論的 doctrine 変更で不変で
   あり、意味的読みの取り替えで変わるのは係数だけであることを導く。

   ```text
   構造が空間を運び、意味が係数を運ぶ。
   ゆえに異なる言語ゲームの障害類は同一複体上で比較可能。
   ```

   blame の doctrine 間比較(候補2(b))が well-defined になる前提条件で
   あり、二相分解が単なる分類ではなく比較可能性の前提条件であることを
   示す。§2 の幾何対応仮説の定理化。
10. **接地による representability の分離**: 接地条件は admissible
    reading への計算可能性・観測可能性制約であり、古典 full abstraction
    に対応物がない。res(L) が ambient にも有限読みにも存在するのに、
    どの接地された doctrine でも表現できない law family の存在を問う。
    存在すれば証拠ベース抽出の原理的天井(Agent SKILL が到達できる
    範囲の理論的限界、R2)を与える分離定理、不存在なら観測的に閉じた
    evidence rule の下での grounding 設計の健全性定理。どちらに転んでも
    AAT 固有の結果になる。
11. **連合抽出の降下定理(federated extraction descent)**: 被覆の各
    パッチに doctrine `D_i` を割り当て、重なり上に comparison 射
    `φ_ij` を与えた連合読みに対して:

    ```text
    大域 canonical Atom family が存在する
      ⟺ {φ_ij} が triple overlap で cocycle 条件を満たし、
         対応する非可換 H^1 型障害が消える
    ```

    doctrine comparison の groupoid に値を取る Čech 機構(descent
    ノートの ConDef_U torsor 機構が足場)。維持されている翻訳射の集合が
    到達可能な大域結論の上界を与える — Conway の法則の語彙内再現
    (現実組織への claim ではなく、パッチへの doctrine 割り当てという
    語彙内構成)。単一 doctrine 前提だった候補群の水平方向の空白を埋める。
12. **接地証明書の torsor 分類**: 固定した canonical Atom family を
    接地する grounding certificate 系の同型類を、evidence 自己同型層
    `Aut_E` 係数の H^1 で分類する。(a) Atom family・障害類が全一致でも
    certificate 系が非同型な二つの読みの存在(忘却の非保存性)
    (b) 「結論は合成できるが正当化が合成できない」状態の特徴づけ。
    因子化テーゼ(候補7)の範囲を精密に確定させる: 結論は Atom 層を
    通して factor するが、certificate は factor しない。「各サービスは
    監査を通ったが全体の監査証跡が組み立たない」現象の定理化。
13. **有効降下被覆の comonadicity 特徴づけ**: 制限・再貼り合わせの
    随伴が comonadic(Beck 条件)であることと、その被覆上で descent が
    有効であることの同値。SAGA(第X部)は被覆を固定した上での類の
    消滅を語る — どの被覆が descent に適格かという被覆側の特徴づけが
    欠落ピースである。系: 分割の失敗には二種類ある(類が非零/被覆
    自体が降下に不適格)。後者は law 違反が一つもなくても分割が
    貼り合わせデータを失う場合として区別される。
14. **深度 filtration スペクトル系列**: 依存 profile(§2)の全次数が
    係数層に底の塔の深さによる filtration を誘導し、そのスペクトル
    系列が有限被覆・有限深度で収束する。候補1の二相完全列はこの
    filtration の2段切断として再現される(§2「profile の全次数は注記に
    留める」の定理版)。works on my machine は OS 深度の graded piece、
    Hyrum の法則は深度間の漏出写像 d_1 に住む(R4 直結)。
15. **law 拡大の単調性と宣言差の障害**: `L ⊆ L'` に沿って obstruction
    ideal は単調に増大し、押し出しの下で類は消えない(候補5の弱化の
    双対方向)。宣言族 L_decl と、別入力として宣言された利用側の族
    L_use に対し、L_decl-無障害だが L_use-非零となる変更は差分
    `L_use \ L_decl` の support で決まる。semantic versioning の
    非対称性(minor は安全のはず/それでも壊れる)の定理化。
16. **構造性の半連続性**: doctrine の連続的変形(底の弱化・use-context
    の拡大)の族の上で、依存 profile の深度は上半連続 — 構造 Atom の
    locus は開、意味 Atom への退化は閉 locus 上で起きる。逆方向の
    ジャンプ(意味 → 構造)は底の強化(執行者の追加)なしには起きない。
    API 契約の腐敗・deprecation が「構造性の喪失」として語彙に乗る。
17. **transport 整合の 2-障害族**: 比較射の合成が閉じない障害は
    2-cocycle 型の不変量をなす。三つの実現を同一機構(pseudofunctor
    coherence)の現れとして統一的に立てる: (a) 塔の cleavage の段間
    合成(段ごとに lift が在っても end-to-end で失敗しうる) (b)
    doctrine 圏の菱形の二経路輸送の食い違い(dependency hell)
    (c) 三つ以上の reading の pairwise 調停の非結合性(pairwise には
    翻訳可能なのに三者整合の共通語彙が組めない)。(c) は ArchMap 調停
    SKILL に pairwise 調停では原理的に足りない場合があることの根拠を
    与える(R2 直結)。
18. **漸進的移行の望遠鏡分解**: 同一 source 領域の二被覆 U_old, U_new の
    間の無停止 migration 計画 = 各ステップの seam(新旧共存領域)の
    comparison 類がその場で coboundary 放電可能な中間被覆の有限列。
    その存在が、大域 comparison 類の局所 support 類への filtration
    分解可能性と同値(anti-corruption layer = seam 上の comparison iso
    を実装する cochain)。第IX部 temporal descent が固定被覆上の状態
    遷移の貼り合わせを語るのに対し、これは被覆自体の取り替え列という
    補完軸である。
19. **L-gauge 群と診断不変性**: `q_L` を通して恒等へ降りる source 変形の
    全体は群をなし(L-gauge 群)、その作用の下で障害類は不変。逆に、
    admissible doctrine 族の全診断を不変にする変形は L-gauge に限る
    (完全性方向)。第VI部の refactor groupoid `Ref_U(X)`(architecture
    状態レベル、不変量保存が定義に入る)に対し、これは source 側から
    群を内在的に定義して不変性を定理として導く下部構造である。
    「テストが緑でも壊れる」は `L_use ⊋ L_decl` の場合として候補15へ
    接続する。
20. **修理予算の genus 税(graph Riemann–Roch)**: nerve の 1-骨格
    (頂点 = chart、辺 = pairwise overlap の連結成分。第IV部 §12 の
    多重グラフ読みが既定)への Baker–Norine 理論の移植(§9 G2 からの
    昇格)。divisor `D` = 修理容量分布、
    敵対側 `E` = H^0 可視欠陥の需要配置、genus `g` = b_1(1-骨格)
    (系12.3)。確定形:

    ```text
    連結のとき r(D) ≥ deg(D) − g(無条件)
    deg(D) ≥ 2g−1 のとき等式 r(D) = deg(D) − g
    g = 0(木)のとき deg(D) ≥ 0 なら r(D) = deg(D): 予算は満額換金される
    ```

    サイクル1本が保証被覆力から正確に1単位を税として取る — 候補1の
    量的対物。`K` は超過結合 divisor(接続数 − 2)と読む(「内在的
    負債」の規範的読みは導出不能のため採らない)。chip-firing は
    blame gauge(1-cochain への δf)と同じ δ の随伴の二面をなす
    Laplacian δ*δ の 0-chain 側の影であり、coboundary 放電そのもの
    ではない。regime 宣言: face を選ばない 1-骨格 regime(face が
    loop を埋める場合は保守的上界)、非連結は成分ごと(r は min、
    g は |E|−|V|+c)、Euler Accounting(系12.5)の等式への昇格は
    stalk dimension 一定 regime に限る。数学は Baker–Norine の適用で
    あり、AAT 固有性は辞書と regime 拡張に在る(非自明担い手と土台
    較正の中間と申告する)。
21. **再配分の有限障害群(sandpile Jacobian)**: deg 0 の予算再配分が
    chip-firing で実現可能 ⟺ `Jac(G) = Div^0/Prin` における類が零。
    `|Jac(G)|` = 全域木の個数(Kirchhoff)。予算中立でも局所移動では
    届かない再配分が存在し、その障害は `H^1(N, Z) ≅ Z^g` とは別の
    torsion 側に住む — H^1 に住まない新種の障害の導入。候補20 と同じ
    1-骨格 regime 宣言を共有し、FiniteModel で全計算可能。
22. **集約の忠実性定理(finite pushforward)**: 集約射 `ρ`(サービス群
    → 粗い測定単位)に trace map 付き pushforward が定義できるとき、
    `ρ_*` が障害類を忠実に運ぶ(`H^n(Y, ρ_* Ob) ≅ H^n(X, Ob)`)⟺
    各集約単位の fiber が内部 obstruction-acyclic。Leray の有限退化。
    第VIII部 §7 が「別途固定する」と宣言だけした pushforward の存在
    条件の定理化であり、候補1の fiber ごと版がロールアップ測定の
    健全性条件として再登場する。候補4(adequate 商方向)と直交する
    射(集約)方向。
23. **path 検査十分性(付値判定法の有限版)**: reading 射の separated /
    proper を operation path 族(第VI部 §8)による判定十分性として
    特徴づける: separated ⟺ 任意の path 上で一致する二つの診断切断は
    大域一致、proper ⟺ 端点の欠けた検証 path が一意に完備化できる
    (path の極限でだけ現れる振る舞いが存在しない)。宣言された path
    族と law family に相対的な「有限個の one-parameter 検証(回帰
    テスト系列)で大域性質が決まる条件」の型であり、無制限の「テストで
    全部わかる」claim にはならない。第X部の presheaf separatedness
    (層条件の分離性)とは別概念であることを明記して使う。
24. **翻訳の分岐公式(Riemann–Hurwitz)**: reading 射 `f` の
    ramification locus を `Ram(f) = supp Ω_{X/Y}`(law が見る区別を
    `f` が潰す場所)と定義する。étale(flat + 不分岐)なら障害類の
    輸送は忠実、一般には食い違いが `Ram(f)` 上に support される。
    グラフの harmonic morphism に対する Riemann–Hurwitz(Baker–Norine
    系で確立済み)により、genus の変化が分岐補正付き等式になる —
    「分割はサイクルを増やす、ただし縫い目で潰した分だけ割引」。
    候補11 の連合障害の由来分解(monodromy 由来 / 翻訳損失由来)を
    与える。lossy adapter の損失箇所が locus として測れる。
25. **組合せ的解消定理(blow-up = adapter 導入)**: 中心 = singular
    stratum(第VI部の God object = law loci の非横断的交点)、
    exceptional divisor = normal cone(第VI部 5.2)の射影化 = 合流して
    いた law 方向ごとに一枚ずつ立つ interface の族。square-free regime
    では blow-up は単体複体の stellar subdivision に一致し、許容中心の
    有限列で全 stratum を U-smooth にできる(常に停止。Hironaka の
    帰納が有限 regime で退化する)。解消列の最小長 = God object の
    解体深度という新しい複雑度不変量。候補18(被覆の取り替え列)の
    空間側対応物。
26. **潜在欠陥と被約化不可視性**: square-free regime の外で
    `I_Ob(W)` が radical でないとき、latent defect :=
    `rad(I_Ob)/I_Ob` の非零元は pointwise evaluation では不可視
    (`V(I) = V(rad I)`)だが、first-order deformation test(第VI部
    DefTest の nilpotent thickening に沿う lifting。標準的には
    `k[t]/(t²)` probe)は一般に区別する。定理形:
    latent defect の存在 ⟺ 評価不可視・変形可視な差分の存在。
    全チェックが緑なのに変更に抵抗する brittleness の定理化 — 潜在
    欠陥は観測ではなく refactor 計画でだけ見える債務。square-free
    regime は構成的に radical のため、どこで radical 性が切れるかという
    regime の成立条件自体が定理の一部になる。なお epsilon 族の双対数
    読みは本文不支持(§9 G1 の検証)。
27. **law 干渉の局所交叉多重度(Serre 型)**: defect point `p` における
    `mult_p(U,V) := Σ_{i≥0} (−1)^i length_p Tor_i(U,V)_p`(Tor_0 を
    明示的に含める。`i ≥ 1` 部分が第V部の LawConflict_i)。有限
    monomial regime・次元条件の下で well-defined・機械計算可能・非負で
    あり、derived-transverse なら `mult_p = length_p Tor_0`、
    `mult_p = 0` ⟺ 交叉が improper(次元条件の不足)。blame gauge に
    不変。第V部定理7.3 の yes / no を点ごとの非負整数へ定量化し、
    ArchSig の severity 集計に gauge 不変量を供給する。第V部 12.2
    (大域 graded 級数の恒等式)とは別物(点局所の数+正値性+gauge
    不変性)。
28. **law system の syzygy と Hochster 対応**: 単一 law universe の
    `I_Ob` の minimal free resolution の graded Betti 数 `β_{i,j}` を
    law system の内部構造不変量として読む(`β_0` = 非冗長 generator
    数、`β_1` = law 間 syzygy)。square-free regime では Hochster の
    公式により witness complex の位相が冗長構造を完全に決める。
    LawPolicy 冗長性監査の機械化(law-equation-surface の版数間 Betti
    差分で law 追加の独立 / 派生を判定)。conflict Tor(二 universe 間)
    に対する単一 universe 自己方向の空白を埋める。導来解禁(§9 G7)の
    最初の換金であり、有限ホモロジー代数経由という経路条件に合致。
29. **変形理論の表示不変性**: presented ambient law algebra の二つの
    表示が同じ law algebra sheaf を与えるとき、tangent / obstruction
    spaces(`L_{S/U}` 由来)は canonical に同型 — cotangent complex の
    quasi-iso 不変性の doctrine 相対版。SKILL が law を書き下す順序・
    冗長性が repair 障害判定を変えないという tooling の暗黙前提の
    定理化。反例側: presentation-stability を落とすと `T^1` が表示
    依存になる有限例の構成。strip test は本リスト中最弱であり、表示
    クラスが doctrine 選択に紐づく点を statement に明示することが
    非退化性の条件(自己申告として記録)。

検証は `Formal/AG/Atom/` の既存形式化(AtomCarrier / AtomAxiomSystem /
Atomizes)と `AxiomAudit.lean` を足場に、疎結合 sandbox
(`research/lean/ResearchLean/`)から積む。

## 9. 代数幾何の換金在庫(機構の輸入候補)

候補1–29 が個々の定理であるのに対し、本節は定理の族を生む機構の
輸入候補を在庫として固定する。背景診断: AAT がこれまで換金したのは
site の位相(被覆・nerve)と線形係数のコホモロジーであり、構造層の
環構造(Spec・非被約性・多重度・正値性・双対性)は、第III部に代数側の
素材があるのに幾何としてはほぼ未使用である。輸入の規律は strip test の
鏡像として置く。

```text
換金テスト: AG の概念は
(a) 定義構造にソフトウェアの指示対象があり
(b) 層+H^1 では到達できない定理を生み
(c) 有限 regime で検査可能
のとき初めて輸入する。
```

- **G1 潜在欠陥の非被約構造**: 候補26 に換金済み。検証結果: 「radical
  であれば」条件は第III部に既出、square-free regime は構成的に radical
  のため非被約の内容は regime の外に住む。epsilon 族の双対数読みは
  本文不支持(第III部定義5.1 に冪零性の公理なし)、無限小は第VI部の
  nilpotent thickening(標準的には `k[t]/(t²)` probe)側から入る。
  候補8(係数忠実性)と直結
- **G2 グラフ Riemann–Roch**: 候補20・21 に換金済み(確定辞書:
  D = 修理容量、E = 欠陥需要、K = 超過結合 divisor)
- **G3 射の性質辞書**: 候補22–24 に換金済み(集約の忠実性 / path 検査
  十分性 / 分岐公式)。第VIII部が測定 pushforward に「別途固定」と
  宣言だけした finite map・properness 条件の定理化がその中核
- **G4 blow-up と特異点解消**: 候補25 に換金済み。square-free regime
  では stellar subdivision に一致して常に停止、という有限化が要点
- **G5 豊富観測と消滅定理**: 再定式化の方針が確定。ample / Picard
  twist に指示対象は見つからないが、第VIII部 §8 の sheaf Laplacian と
  その非零最小固有値(spectral gap)が positivity の指示対象として既在。
  「観測 witness の追加が spectral gap を単調に押し上げ、harmonic
  debt(定理8.6)が減衰する」という Laplacian 版消滅定理として立てる
  (ample の語は捨てる)。次波の換金候補
- **G6 blame の moduli と stack の必要性**: 実現可能性高。gauge
  自己同型の非自明性は有限条件(nerve の 1-サイクル+
  非自明な大域単元)で保証でき、moduli 関手は候補16 の変形族が供給、
  商の受け皿は第VI部 refactor groupoid が既在。次波の換金候補
- **G7 導来方向(2026-07-29 解禁)**: 2026-07-05 の据え置き合意を解除。
  経路条件は維持する: ∞-圏の正面からではなく有限ホモロジー代数
  (鎖複体・Tor/Ext)経由で、第V部の Tor_0 表示を足場に入る。門の
  順序の見立て: (1) 法則の導来交叉 = ポリシー冗長性診断 (2) 修理空間の
  π_0 / π_1 = 移行手順の順序依存性 (3) 変形理論 = 第IX部の再基礎づけ。
  最初の換金は候補27(局所交叉多重度。門(1) の交叉側)・候補28
  (syzygy。門(1) の冗長性診断側)

輸入しない側: 交叉理論・Bezout(第IV部 Euler Accounting との突合が
先)、数論的方向(Frobenius 等。指示対象未同定で装飾リスク最大)。

## 10. アーキテクチャスキームへの橋

Atom 基礎論の論文群が完了した後の次理論(アーキテクチャスキーム)に
対し、本ノートの成果がどこまで基礎になれているかを固定する。スキーム
とは「環の Spec を局所モデルとし、貼り合わせで得られ、射の性質で
語られる幾何対象」であり、各要求に対する供給は次のとおり。

- 安定な底空間 ← 候補9(構造 nerve の底不変性)
- 局所モデルの環 ← 第III部 Law Algebra+環側換金(候補26–28)
- affine 性の理論 ← 候補6(`res(L)` の representability = affine
  chart の存在判定と読める)
- 貼り合わせ ← 候補11(連合降下)・13(comonadicity)・17(gluing
  data の 2-整合)
- 射の性質辞書 ← 候補22–24(proper・separated・étale・flat・分岐)
- 相対的視点 ← §1・§3(底の塔・base change・輸送)
- 非被約構造・特異点 ← 候補25–26

残ギャップは五つ。いずれも土台の欠陥ではなく、スキーム理論自体の
第一章とすべきものである。

1. **Spec 関手の構成**と局所環付き site 構造の指定。Boolean regime は
   零次元(生成点なし)のため、非自明な位相の供給源(deformation 側
   `k[Coord]` か、site の被覆位相か)の設計判断を含む
2. **doctrine 圏の極限構造と fiber product**(base change の心臓。
   doctrine 圏の定義自体が先行課題として保留されている箇所)
3. **affine 被覆の存在定理**: 「任意の読みは L-adequate affine chart で
   被覆できるか」を定理とするか公理とするかの選択
4. **定義流儀の選択**: 局所環付き site か functor of points か
   (reading の塔は後者を示唆)
5. **scheme で足りない可能性の織り込み**: representability failure
   (候補6)と gauge 自己同型(§9 G6)は、scheme → algebraic space →
   stack の階段が最初から必要になることを予言する。土台がこの予言を
   出せること自体が、基礎として機能している証拠である

Lean 側の種として `StandardScheme` と GAGA 契約が形式化の足場に既在。

## 11. 範囲外・明示 scope

- **終対象な底は置かない。** 「究極の底」(ハードウェア、物理法則)の存在は
  仮定しない。絶対的な底の存在仮定は相対性原理と衝突する。
- **底の圏の内部構造は AAT の範囲外。** OS・処理系・言語・フレームワーク・
  仕様という選択軸の独立性や入れ子(底の圏のファイバー構造)は扱わない。
  AAT は底を与えられた入力として受け取り、底の由来については沈黙する
  (ArchSig が入力 contract の由来を詮索しないのと同じ責務分割)。
  輸送を語るには底の間の射が一本あれば足りる。
- **宣言された doctrine と生きた実践の忠実性は範囲外(沈黙として明示)。**
  接地条件は宣言済み doctrine の下で Atom を証拠に接地するが、その doctrine
  がチームの現実の言語ゲームを忠実に表すかは、底の由来と同様に AAT は
  語らない。将来対象の候補としてのみ記す: 宣言された読みと de facto の
  読みの乖離(doctrine drift)を、両者の間の障害類として測る道はありうる。
- **規則をその規則たらしめるものの分析は範囲外。** 執行者は因果的であって
  規範的ではない(規則遵守のパラドックス)。AAT は執行された実践を所与と
  して受け取り、規則の規範性の根拠は問わない。
- **本文第I部は本ノートでは改訂しない。** 反映は3条件ゲートを通る将来作業。
- 本ノートの主張はすべて AAT の語彙内の主張であり、現実のソフトウェア全体・
  意味宇宙全体への無制限 claim を含まない。

## 12. NEXT ACTION

次の要件を同時に満たす Atom 基礎論を、Codex を交えて徹底的に詰め、
**論文にする**。

```text
R1. 相対的だが、工学としての要件を満たす
    (接地・反証器・輸送定理群で「読み替え耐性」を定理化)
R2. Agent SKILL で実用的な抽出が可能
    (軽量モデルで構造 Atom を機械抽出、意味 Atom は grounding certificate
     つき調停。SKILL は partial certified constructor から始め、
     cleavage・functoriality の梯子で section へ昇格を測る。
     抽出経済の分割線が理論の分割線と一致することを製品条件として維持)
R3. AAT の土台を支える
    (A0–A8 を壊さず、二相・接地・欠陥相対性・解像度原理を
     定義+定理として積み、Atom から site / sheaf / 障害へ至る
     選択の階段(塔)を再構成する)
R4. CS として自然
    (既知の工学現象群 — 結合バグの局在不能性、blame 論争の非決着性、
     "not a bug" 論法、works on my machine、Docker、Hyrum の法則 —
     が系として再現されることを自然さの論拠とする)
R5. 条件付き普遍性
    (宣言された底と law family を持つ任意のソフトウェアに適用できる。
     無制限 claim ではなく、種別横断のインスタンス — microservices の
     one-cent、組込み / ISA 解析(§5)、データパイプライン等 — の
     構成で例証する。仮定監査(§7 冒頭)を論文の作業項目に含める)
```

**最初の詰め対象は reading の塔の下層(`ExtInst -> Doct` と
`CoreRead -> ExtInst`)**(§3)。lift の形が定まると、輸送・客観性・解像度・
定理候補の statement を順に固定できる。geometry・class までの lift は
最初は要求しない(失敗した段の特定を優先する)。

**最初の研究スライス**(Codex・有識者との往復で合意した叩き台): 既存
`FiniteModel` の固定 carrier と抽出足場を使い、同じ有限モデル上で
次を構成して二相・接地・blame・デスコープ・輸送を検査する。

```text
a. pointed extraction instance (D, s) を対象にした下層圏を作り、
   同じ source から二つの doctrine D0, D1 が異なる Atom family を出す
   最小例を固定する
b. exact / refinement の二種類の下層射を定義する
c. AATCorePackage への lift の正例と負例を一つずつ作る。
   正例は既存 SignedExactCoreReadingHom / PositiveCoreReadingHom へ
   接続し、負例から core lift に本当に必要な追加仮定を抽出する
d. ambient joint-kernel quotient q_L を構成し、admissible reading class
   の中での representability を検査する(q_L の構成には bisimulation の
   partition refinement 系アルゴリズムが流用できる。§7.3)
e. 構造 Atom だけでも descent が失敗する反例、
   または失敗を排除する最小仮定
f. 固定 doctrine 内の二つの blame 代表と、それらを結ぶ coboundary
g. law の弱化で class は消えるが repair cochain は存在しない例
```

a–d までで塔の下層・lift・Agent constructor・canonical resolution の核が
同じ有限模型に乗り、`ReadingCore`(geometry 段)へ進む理由も明確になる。
スライス a–c の形式仕様(Doct 射の二種・opcartesian lift・証明対象4点)は
§3.5 に固定済みであり、a–c の完了が達成階梯 Gr2 = §1 の比喩宣言の撤回
条件に一致する。

想定する進め方(未確定、着手時に PRD / 研究 GOAL 化して確定する):

1. 本ノートを地図として研究 GOAL(例: G-aat-atom-foundation-01)または
   PRD を起草し、問いと採否規律を固定する。reading の塔の下層接続と
   実験スライス a–g を最初のスコープに置く
2. Codex の研究ループで定理候補群(§8 の 1–29。まず非自明性の担い手
   から)を探索・反証・Lean 検証にかける。§9 の換金在庫は機構単位で
   別 GOAL に切る
3. 生き残った骨格で論文を構成する(下記ロードマップの4本構成。
   先頭は論文A「Atom Is All You Need」)
4. 固まった成果を3条件ゲート経由で第I部・第II部へ反映する

**論文ロードマップ(4本構成)**。各論文は研究ループの
生存者だけで構成する(§8 は候補であって約束ではなく、収録リストは縮む
前提)。執筆着手 gate: A は Gr2 達成(§3.5)、B–D は各核候補の正例が
Lean で立つこと。全論文で §7.7 の評価規準と換金テスト / strip test を
明記し、related work は自分から位置づける。推奨順序は **A → D → B → C**
(A は全論文の依存先。D は確立済み組合せ定理の移植中心で生存率が高く、
完了時に §10 の橋 = アーキテクチャスキーム理論の入口が開く。B は工学的
共鳴が最強だが非可換 H^1 と 2-圏的整合の新規構成リスクが中、C は最も
投機的なので最後尾で研究ループの蓄積を活かす)。

- **A「Atom Is All You Need — 相対的 Atom の基礎論」**
  問い: 相対的な Atom の上に、読み替えに耐える工学的結論は立つか。
  §1–7 の土台本文+輸送の形式化(§3.5、Lean 成果物込み)。
  収録候補: 1, 2, 3, 4, 5, 6, 7, 9, 10(非自明核は 1+4、候補7 が
  完全性テーゼの精密形、候補6 は related work 側の較正)
- **B「連合する読み — 複数読みの障害理論」**
  問い: 読みが複数共存するとき、何が貼り合い、何が原理的に貼り合わ
  ないか。収録候補: 11, 13, 15, 17, 18, 19, 24(Conway・dependency
  hell・semver・strangler・lossy adapter が系として出る一本)
- **C「診断の認識論 — 測定・正当化・忠実性」**
  問い: 宣言された観測の下で、診断は何を主張でき、その正当化はどこ
  まで合成できるか。収録候補: 8, 12, 14, 16, 22, 23(+G5 spectral
  消滅を将来枠として言及)
- **D「アーキテクチャの代数 — 欠陥の定量化とスキームへの前奏」**
  問い: 欠陥・修理・複雑度は、law algebra の代数的量としてどこまで
  測れるか。収録候補: 20, 21, 25, 26, 27, 28, 29(+G6)。§10 の橋を
  outlook に置き、アーキテクチャスキーム理論への直接の入口とする

割当は 9+7+6+7 = 29 で全候補に孤児なし。

**論文Aの題と投稿戦略**。論文Aの題は「Relative Atoms: A Foundation
for the Algebraic Geometry of Software Architecture」とする。
「Atom Is All You Need」はプロジェクト名・アウトリーチ surface
(website・登壇・解説記事)の名前として使い分け、ジャーナル原稿では
標語として序文で一度だけ使う。その際、万能宣言ではないこと —
必要性(因子化テーゼ、候補7)+生成性(最小限の宣言から豊かな理論が
立ち上がる、§7.7 の fruitfulness)の二重読みであり、万能の読みは
AAT 自身の境界規律が排除すること — を自分で相対化して示す。

投稿戦略: 第一候補 JLAMP、次いで LMCS・MSCS、SE 寄りに架けるなら
Formal Aspects of Computing。別経路として会議(CALCO / FoSSaCS、
Lean 形式化を主役に切り出すなら ITP / CPP)→ジャーナル特集号。
preprint + DOI(Zenodo / arXiv)を先行させる二段構えを取る。
投稿判断の gate は執筆力ではなく証明であり、Gr2+候補1・4 の証明+
one-cent 実例が揃った時点で JLAMP / LMCS 級が現実的射程になる。
研究 GOAL の受け入れ規準はこの査読水準を目線に書く。

## 付録A. law の定義域と層別観測 — 形式手法実務家の反応から(2026-07-31)

形式検証の実務家(Alloy / TLA+ ユーザー)との対話を起点とした考察の
記録。本文(§0–12)確定後の追記であり、位置づけは §9 の換金在庫と
同じく候補である。観測・抽出の運用に関わる部分(A.2 後半、A.3)は
ArchMap / ArchSig 側の artifact contract の設計素材であって、AAT 内部
の主張ではない。

### A.1 反応 — 事前形式化の不要と二重抽象化

形式検証の実務家からの評価は二点。

- Alloy / TLA+ 系は事前にモデル / spec を書き切るコストが実務上の壁。
  AAT はソースコードを正として atom と law で分析するため、spec 先行の
  形式化が不要である。
- 「ソースコードを atom、仕様を law で抽象化する」二重抽象化が新鮮に
  映った。refinement の一方向構図(spec が正であり、コードが適合を
  問われる)に対し、AAT では観測(atom)と方程式(law)が対等な二系統
  入力として同じ代数的土俵に乗る。

前者は後者の帰結である。spec がモデル(正)でなくなった瞬間に「先に
完全な spec を書く」義務が消え、law は後から、部分的に、必要な語彙の
分だけ書けばよくなる。

### A.2 law 駆動の部分観測と「law は atom を生まない」

派生した着想: law が与えられたら、その語彙に合わせて必要な atom だけ
観測する。例: 「JWT は30分で期限切れになる」という law に対し、JWT
関連コードから expired-at を atom として取る。全域の網羅抽出を前提と
しない。

これは責務憲章
([archmap_lawpolicy_archsig_responsibility_charter.md](../tool/archmap_lawpolicy_archsig_responsibility_charter.md))
の「law は atom を生成しない、coordinate を生成しない、law は loci を
切り出す」と一見緊張するが、次の解釈で決着する。

**law は atom の部分集合に適用される。切り出される部分集合とは law の
定義域である。** f ∈ O(U) と書くとき、U の指定は U に点を作ることでは
ない。定義域の指定は law の言明(型)の一部であって、atom の生成では
ない。この読みの利得:

- 定義域の外では law は「未検査」でも「不成立」でもなく**未定義**で
  ある。沈黙の規律(§3.6)が「まだ語っていない」から「そもそも語る文が
  存在しない」へ強化される。
- SAFE_WITHIN_POLICY 型の肯定的結論は最初から定義域 U で添字づけられ、
  部分観測の SAFE が全体の SAFE に誤読される罠が型のレベルで塞がる。
  非対称性も明示される: 違反検出(非零類)は部分観測でも存在言明として
  有効だが、肯定的認証は宣言された定義域内に限る。
- 憲章の「loci を切り出す」は定義域の指定という canonical reading に
  収束する。

残る技術ギャップは一点である。定義域は atom 空間の部分集合だが、抽出は
ソースコード空間で走る。実際の観測スコープは、観測写像に沿った定義域の
引き戻しの**安全側過大近似**になる(過大は無害、過小は取り逃し)。
contract に刻むのは次の二点で足りる。

1. どの過大近似を使ったか。
2. 抽出器に方程式の内容を見せない(観測が law の期待に対して盲目で
   あること = 反証可能性の保持)。

### A.3 層別観測 — 空間は全域、切断は定義域上

抽出方針の層別: **relation / component は機械的にコードベース全域、
semantic / contract は law の定義域のみ**。

- relation / component は底空間(被覆・位相・nerve)を張る層であり、
  制限と貼り合わせを語る足場として全域が要る。静的解析で安く決定的に
  取れる。
- semantic / contract は切断の値の層であり、方程式が住む定義域上で
  評価できれば足りる。LLM 解釈を要する高コスト層をここに限定する。

「空間は全域・切断は定義域上」という配分は、層理論の要求とコスト構造が
同じ線で割れる整列である。全域の機械層グラフが先にあれば、A.2 の
引き戻し過大近似を file glob の当て推量ではなく**グラフ上の近傍計算**
として監査可能に導出できる。汚染防火壁の必要も semantic 層だけに縮む
(機械層は決定的である)。

注意: 定義域が全域に及ぶ law では semantic コストが戻る。仮説「大域的
law は機械層語彙で書ける傾向があり、semantic / contract を要する law は
局所定義域に寄る傾向がある」は fixture で検証する。one-cent も同構図で
ある(三角形の発見 = 機械層の位相、ドリフト = semantic 層の切断)。

### A.4 形式手法との対応と claim boundary

この層別は形式手法の二大関心に対応する: 機械層 = Alloy 的な関係語彙の
検査、semantic / contract 層 = 仕様・意味論の検査。ただし claim
boundary を守る。Alloy の本領は有界モデル発見(「この形の設計すべて」
への量化と反例探索)であり、AAT の機械層検査は観測された現物
1インスタンス上の評価である。正確な語りは「Alloy 相当」ではなく
「**Alloy が扱う関係語彙の検査を、モデルではなく観測された現物に
対して**」である。TLA+ に対しても代替を claim しない。補完の構図
(AAT が観測で危険な loci を特定し、クリティカルな部分だけ精密検証に
回す)は語れる。

### A.5 幾何への展望(換金テスト待ちの vista)

定義域解釈の先に見える候補。いずれも §9 の在庫と同じく換金テスト
(ArchSig が計算できる何か、または Lean が証明できる何かへの換金)を
通過するまで理論には入れない。

- law の定義域が方程式の切る locus であるなら、law の全体が atom 空間
  の幾何(Zariski 的位相: 閉集合 = law たちの零点集合)を定義する。
  空間が先にあって方程式が住むのではなく、方程式を通じて空間を知る
  順序の再現である。
- 複数 law の定義域の交叉 = 契約どうしの干渉領域。退化した交叉で
  素朴な交わりが情報を落とす場合の導来的交叉(Tor)は、導来AG解禁後の
  最初の換金候補である。
- law の移植 = 観測写像に沿った引き戻し。連合(論文B)は組織の被覆に
  沿った descent であり、A.2 の引き戻しはこの一般論の最初の一例に
  あたる。
- 非零障害類の立つ loci を特異点、repair を解消(blow-up)と見る描像
  (最も投機的)。

### A.6 供給パイプライン — 規範の源泉から計算まで

A.1–A.3 の帰結を役割分担として配線する。A.2 後半・A.3 と同じく
tooling 側の設計素材である。

1. 人間が仕様・アーキテクチャ規約・設計ルールを決める(規範の源泉。
   自然言語でよい)。
2. AI Agent がそれを law = 方程式+定義域へコンパイルする。成果物の
   置き場は law-equation-surface と LawPolicy であり、入力トライアドに
   新カテゴリは増えない。
3. 別の Agent が観測する。機械層(relation / component)は全域、
   semantic / contract は law の定義域(の引き戻し過大近似)のみ。
4. ArchSig が観測と方程式から診断結論を計算する。

事前形式化のコストは消えるのではなく、正しい担い手へ移る。
Alloy / TLA+ の壁は人間が形式化を書き切ることだった(A.1)。この
パイプラインでは形式化(law 定義)は Agent の仕事であり、人間は自分の
語彙で規範を語るだけでよい。エンジニアは代数幾何を習得しなくてよいと
いう抽象化原則が、law の供給側にも貫徹される。

規律は二点。

- **law 定義役と抽出役は分離する。** 「law にあった atom を取り出す」の
  「あった」は定義域一致(domain-matched)であって期待一致
  (expectation-matched)ではない。law 定義役は仕様を見て方程式を書く。
  抽出役は定義域だけを受け取り、方程式の内容を見ない(A.2 の防火壁の
  配線先)。一つの Agent が一息にやると、期待に合わせた atom の整形 =
  law が atom を生む事故への滑り台になる。
- **law 定義もまた誤りうる読みである。** 規約 → 方程式のコンパイルは
  解釈であり、誤読しうる。「この方程式はこのルールのこの文の形式化で
  ある」という traceability を人間が監査できる形で残す(semantic Atom の
  grounding certificate(§3.1)と同型の機構)。受け入れテストと最終判断と
  いう人間の役割がこの段でも効く。
