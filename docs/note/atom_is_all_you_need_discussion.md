# Atom Is All You Need — Atom 基礎論・最初の考察

2026-07-29 のディスカッションのまとめ。**完成された理論ではない**。
AAT の次目標「Atom 基礎論の補強」に向けた最初の考察として、
到達した見取り図・定理候補・適用範囲・NEXT ACTION を固定する。
Codex・有識者との議論往復と敵対レビューを反映済み(経緯は PR #3852)。

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
本目標の理論的内容はこの**輸送の構成**にある(§3、§7)。

タイトル「Atom Is All You Need」のテーゼは、因子化として固定する。

```text
AAT が語れるすべてのアーキテクチャ的結論は、Atom 層を通して factor する。
Atom は、すべての読みが通る唯一のボトルネック・インターフェースである。
```

Atom は万物を導出する源泉ではなく、すべてが通る唯一の関門である。
これは L-adequacy(§5)を結論一般へ広げた完全性テーゼであり、
修辞ではなく検証対象である(§7 候補7)。

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

### 3.5 沈黙の規律と系譜

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

## 7. 定理候補(すべて未証明の仮説。反例探索を先行させる)

1. **Obstruction support(条件付き)**: 目標とする形:

   ```text
   0 -> F_struct -> F_all -> F_sem -> 0
   H^1(F_struct) = 0 または restriction の全射性を仮定するとき、
   具体的 obstruction class の像が semantic quotient 側で検出される
   ```

   無条件版(「非零の障害類は必ず意味 Atom の上に support される」)は
   採らない。大域的 canonical family の存在だけでは flasque 性も descent
   有効性も従わず、構造データ自体も build configuration・生成コード・
   schema version などで貼り合わないことがあるからである。まず
   「構造 Atom だけでも descent が失敗する反例」または「失敗を排除する
   最小仮定」を探索する。
2. **Blame gauge(二分)**: (a) 固定した複体の中で代表元が coboundary 分
   だけ動くこと(cohomology の statement)。(b) doctrine の変更で複体
   そのものが変わること(comparison map と naturality が必要)。
   blame の移動(a)と defect class の輸送(b)を混同しない。
   後段の拡張として、修正コスト・authority・ownership・risk の非対称性を
   gauge orbit 上の cost functional として置き、運用方針に相対的な
   gauge fixing で修正候補を選ぶ道がある(「canonical blame はない」を
   「何も選べない」にしない。ArchSig が修理候補の提示まで進む際に効く)。
3. **輸送定理群(lift の存在と性質)**: reading の塔(§3)の各段の射影の
   下で、下層射に沿った (1) doctrine 同値不変性 (2) refinement 保存・反映
   (3) 一般の翻訳 / base change 輸送。段ごと・種類ごとに別の仮定と結論を
   持つ lift statement とし、lift が存在しない場合にその段の transport へ
   本当に必要な追加仮定を抽出することも成果と数える。
4. **健全性**: 接地された doctrine の下で抽出は決定的・再現可能、
   診断は doctrine 同値で不変。
5. **デスコープの押し出し**: 方程式系の弱化に沿う類の押し出しとしての
   仕様変更。repair(coboundary 放電)との数学的区別。弱化で類は消えるが
   repair cochain は存在しない例の構成を含む。
6. **Law-relative canonical resolution(representability)**:
   (a) adequacy relation の concept lattice における principal extent の
   特徴づけ。(b) ambient joint-kernel quotient `q_L` の、許容 doctrine・
   有限性・計算可能性・接地条件の中での representability の特徴づけ
   (§5–6)。representable なら解像度選択の普遍性が立ち、failure なら
   それ自体が「instance designer の選択が残る理由」の記述になる。
   (c) 二つの入口(方程式系先行 / Atom 先行)が同じ formal concept を
   生成する合流条件。
7. **Atom-interface completeness(因子化テーゼ)**: AAT の語彙で述べられる
   結論が Atom 層(atomization reading)を通して factor することの特徴づけ
   (§1)。L-adequacy の law evaluation から結論一般への拡張。
   Atom 層を迂回する結論の反例探索を先行させる。

検証は `Formal/AG/Atom/` の既存形式化(AtomCarrier / AtomAxiomSystem /
Atomizes)と `AxiomAudit.lean` を足場に、疎結合 sandbox
(`research/lean/ResearchLean/`)から積む。

## 8. 範囲外・明示 scope

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

## 9. NEXT ACTION

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
   の中での representability を検査する
e. 構造 Atom だけでも descent が失敗する反例、
   または失敗を排除する最小仮定
f. 固定 doctrine 内の二つの blame 代表と、それらを結ぶ coboundary
g. law の弱化で class は消えるが repair cochain は存在しない例
```

a–d までで塔の下層・lift・Agent constructor・canonical resolution の核が
同じ有限模型に乗り、`ReadingCore`(geometry 段)へ進む理由も明確になる。

想定する進め方(未確定、着手時に PRD / 研究 GOAL 化して確定する):

1. 本ノートを地図として研究 GOAL(例: G-aat-atom-foundation-01)または
   PRD を起草し、問いと採否規律を固定する。reading の塔の下層接続と
   実験スライス a–g を最初のスコープに置く
2. Codex の研究ループで定理候補 1–7 を探索・反証・Lean 検証にかける
3. 生き残った骨格で論文を構成する(SAGA 論文の次の一本。
   「Atom Is All You Need」— 相対性原理と二相 Atom の下での因子化テーゼ、
   および幾何的読みの選択空間と条件付き canonical resolution
   (representability)を主結果とする)
4. 固まった成果を3条件ゲート経由で第I部・第II部へ反映する
