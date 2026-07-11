# Software Field Theory: The Dynamics of Software Evolution on Architecture Geometry(アーキテクチャ幾何の上のソフトウェア進化力学)

Software Field Theory, SFT は、AAT が与えるアーキテクチャ幾何の時間発展を扱う力学系の理論である。

```text
AAT はソフトウェアに空間を与える。
SFT はソフトウェアに時間を与える。
開発は、その時空の中の力学である。
```

- 版: v2.0-P3(2026-07-04)
- 完全部: 序、第I部(開発時空)、第II部(力の幾何)、第III部(マージと降下)、
  第IV部(参加者と組織)、第VI部(力学)、第IX部(観測と制御)、
  第X部(寿命と長期挙動)、付録 A–G
- 予告部: 第V部(Conway 対応)、第VII部(変形と可能性)、第VIII部(開発の統計力学)
- 設計の正典: [SFT v2 理論骨格ノート](../note/sft_development_spacetime_dynamics_skeleton.md)。
  本文と骨格が食い違う場合、完全部については本文を、予告部については骨格を正とする。
- 旧本文(SFT v1, computational theory)は
  [`docs/archive/2026-07-04-sft-v1-computational-theory/`](../archive/2026-07-04-sft-v1-computational-theory/software_field_theory.md)
  に退避した。旧概念との対応は付録 F に置く。

## 序 The New Object(新しい対象)

### 1. v2 contract(本文の読み方)

```text
SFT v2 の本文は、現実の開発活動を直接定義しない。
本文の対象は、selected profile によって構成された開発系 𝔇 と、
その上の生成子 T_Π の解軌道である。

実在の repository / PR / CI / organization との対応は、
付録 A の解釈境界を通じてのみ読む。

したがって SFT v2 の定理は、現実の開発系についての無条件主張ではなく、
selected development system の内部定理、Certified bounded inference、
Model theorem、または Empirical hypothesis である。
```

本文中の主張ラベルは次の梯子で読む。

```text
Formal theorem:
  公理・定義・仮定から証明される数学的命題。

Certified bounded inference:
  有限性、選択された cover / 係数 / 調整群などの仮定の下で成立する相対的推論。

Analytic reading:
  構成された対象を距離、質量、residue などで読む表現。

Model theorem:
  明示された確率・エージェント模型の内部での定理。
  同じ模型族の中で結論が成立しない相が非空であることを併せて示す(模型非自明性)。

Empirical hypothesis:
  現実の開発系についての仮説。付録 B の台帳で管理し、
  事前固定 profile と棄却条件を持つ。定理と混同しない。

定理候補:
  今後の定義・証明設計を示す本文内の候補。
  Lean の中央 proof obligation になるのは、docs/aat の台帳に対応行を置いた場合だけである。

命題候補:
  定理候補と同格の、命題水準の候補ラベル。
```

### 2. 何の理論か

SFT の対象は、ソフトウェア進化 — コードベースと開発組織の時間発展 — である。
SFT はこれを、AAT が構成するアーキテクチャ幾何の上の力学系として扱う。

```text
場   = AAT site 上の層データ(場の配置)
力   = 台と輸送データをもつ場の部分変換
衝突 = 貼り合わせの障害(コホモロジー類・Tor)
安定 = 評価汎函数と方針の適合(Lyapunov 読み)
```

看板のスローガンは次である。

```text
コードベースは場であり、
PR は力であり、
開発組織は力の源である。

場は力のコストを形作り、力は場を変え、
源は場を見て力を生み、目標は要求とともに動く。

開発とは、アーキテクチャ幾何の上を流れる場の時間発展である。
```

これはスローガンである。本文の核では「場の配置 = selected Atom family 上の層データ」であり、
「コードベース ↔ Atom family」「PR ↔ 力」という読みは付録 A の解釈境界を一度通す。

理論が最初に与えるものを一つだけ挙げる: テキスト衝突なしで auto-merge が通っても
壊れるマージがある。本文はその壊れ方を、台の validity・法則の Čech H¹・導来の Tor という
三つの独立な障害水準に分解し(第III部)、4 頂点の有限実例の上で全水準を手計算して見せる
(付録 D)。これが P1 の中心成果である。

旧 SFT(v1)は、field / force / attractor を「物理量ではない」と宣言して簿記概念へ分解する
計算理論だった。その封印は、古典 AAT の上では場や力に実体を与える幾何が存在しなかったことによる。
AAT が代数幾何(site、層、obstruction ideal、cohomology、導来幾何、evolution geometry)へ
進化したことで、封印は不要になった。v2 は語の指す先を実在の数学的対象に置き直す。

### 3. 開発系(中心対象の概観)

SFT v2 の中心対象は**開発系(Development System)**である。

```text
𝔇 = (𝒯, 𝔛, 𝔖, Π, 𝔐)

𝒯 : 開発トレース site(時間)          — 第I部
𝔛 : 進化族 + 辺上の輸送データ(空間)  — 第I部
𝔖 : 源構造(開発組織)                — 第IV部(P2 で完全化)
Π : 方針(運動の法則)                — 第VI部(P2 で完全化)
𝔐 : 計測輪郭の族(観測)             — 第IX部(P3 で完全化)
```

五成分は「時間・空間・源・法則・観測」であり、力学系の標準装備に対応する。
ただし力学系としての実質は、五成分そのものではなく、第I部 §9 の生成子と挙動空間が与える。

依存方向は片方向である。

```text
AAT は SFT に依存しない。
SFT は AAT に依存する。
```

SFT は AAT の対象を使うが再定義しない。SFT が新しい純数学(トレース site、力の複体、
組織対応)を構成するのは自由だが、それは SFT 側の数学であり、AAT 本文を書き換えない。
AAT の定義・定理・定理候補に対して「昇格・後継・本体化」を宣言せず、
SFT 側の対応物は「SFT 側対応定理候補」と呼び、AAT 側の対象とは比較命題で接続する。
AAT アンカーは proved / certified / candidate の状態を区別して引用する。
定義の引用は無印でよい。定理・系・命題の引用には証明状態を付す。

AAT 輸入語の最小 gloss(正確な定義は AAT 本文):

```text
law universe U    : 選択された law の族(AAT 第III部)
law algebra       : law が生成する可換代数の層(AAT 第III部)
obstruction ideal : law 不成立の witness が生成する ideal 層 I_Ob(AAT 第III部)
lawful locus      : I_Ob が切り出す部分幾何(AAT 第V部 定義2.1)
obstruction mass  : 選ばれた測定 profile での障害の質量読み(AAT 第VIII部)
additive regime   : law データの差が abelian 係数として読める選択された体制(AAT 第X部 §4)
presentation 圏 / valid state : 配置の表示の圏と、その選択された部分圏(§20 の選択データ)
```

### 4. 規律(D1′–D8)

本文全体を拘束する設計原理。骨格ノート §2 の本文化である。

```text
D1′ 実在性(使用強制つき):
  核概念はすべて数学的キャリアを持つ。さらに、核概念が名乗る構造
  (cover / restriction / pairing / 汎函数)は、少なくとも一つの定理または
  付録 D の正準有限実例の仮定・結論・計算で本質的に使われなければならない。
  使われない構造は名乗らない(site ではなく圏、層ではなく割り当てと書く)。

D2 相対性と沈黙:
  すべての主張は selected evolution profile / vocabulary / law universe /
  coverage / coefficient / measurement profile に相対化される。
  選ばれていない事象・遷移・軸について本文は沈黙する。
  構成データ(site、係数、cocycle、輸送)が固定されていない式は、
  定義ではなく reading schema として扱う(AAT 第IX部 定義3.4 の規律の継承)。

D3 片方向依存と語法規律:
  §3 の通り。

D4 純数学本文と解釈境界の分離:
  実在物との対応は付録 A に一度だけ置く。本文はコードベース・commit・PR という語を
  定義の index に使わない。tooling(FieldSig)は本文の外。

D5 主張の梯子:
  §1 の通り。SFT の Formal theorem / 定理候補が Lean proof obligation になるのは
  docs/aat 台帳に対応行を置いた場合だけである。

D6 模型非自明性:
  Model theorem は、同じ模型族の中で結論が成立しない相の非空性を併せて示す。
  望ましい標準形は相境界定理である。

D7 反証規律:
  Empirical hypothesis は (a) 事前固定 measurement profile、(b) 棄却条件、
  (c) profile 安定性を必須列として付録 B の台帳に置く。
  検証時の profile 事後再選択は反証の回避として扱い、別仮説として行を分ける。

D8 選択データ優先:
  普遍性(colimit / pullback / pushout)への依存を定義に置かない。
  merge の base、branch 間の輸送、力の接続、complement はすべて
  evolution profile の選択データである。
  (AAT 第II部 定義7.1 の生成位相方式と、第X部 定理6.4「Incidence Is Data」の方式の継承)
```

### 5. 非主張

SFT v2 は次を扱わない。これらは失敗や残タスクではなく、理論の外部である。

```text
プロダクト価値の判定(law universe の価値は外生入力である)
個人の意図・心理・信念・学習(trace に現れる生成だけを扱う)
悪意ある源の意味論(trust boundary の型だけを与える)
lifecycle 判断(修復・migration・削除の選択。定理 57.2 の系が指す人間の選択)
runtime コストの経済学(計器の一軸としてのみ扱う)
一般 AI 安全性
未選択の事象・遷移・軸(D2 の沈黙)
```

### 6. 部の地図と現在の状態

| 部 | 題 | 状態 |
| --- | --- | --- |
| I | 開発時空 | 完全(P1) |
| II | 力の幾何 | 完全(P1) |
| III | マージと降下 | 完全(P1)。§23・§25 は予告 |
| IV | 参加者と組織 | 完全(P2) |
| V | Conway 対応 | 予告(P4、研究課題) |
| VI | 力学: 運動の法則 | 完全(P2) |
| VII | 変形と可能性 | 予告(P4) |
| VIII | 開発の統計力学 | 予告(P4) |
| IX | 観測と制御 | 完全(P3) |
| X | 寿命と長期挙動 | 完全(P3) |
| 付録 | 境界と実例 | 完全(A–G。D.1–8 は P1、D.9–13 は P2、D.14–16 は P3) |

P1 の焦点は三つである: マージ診断 filtration(第III部)、力の曲率と merge residue(第II部)、
追跡可能性の限界(第VI部 T0)。P2 は第IV部と第VI部を完全化した
(組織の源構造、質量収支則、方針階層と CLF、内生コスト吸収域、ゲージ合同、レビューの盲点)。
P3 は第IX部と第X部を完全化した(可観測性 = annihilator 消滅、フィードバック安定化、
有効力の枯渇と吸収性、migration = 開発系の射に沿った場の輸送)。U 定数 regime(P1–P3)では law universe は時間で動かない。
動く regime は law-universe transport が定義されるまで(P4 以降)reading schema として扱う。
P5(aat_interface・README・guideline の v2 化、台帳分別)は本文の部ではなく配線の段である(付録 G)。

## 第I部 開発時空(Development Spacetime)

問い(この部の採否規律): 分岐し合流する時間の上で、幾何の族と可能軌道の空間は、
普遍性に依存せず選択データだけから立つか。実現した記録と生成の法則は、
検査可能な witness で接続されるか。

### 7. 開発トレース site

時間は線形ではない。開発は分岐し、合流する。第I部は、バージョン履歴の有限 DAG を
site として扱い、その上にアーキテクチャ幾何の族を載せる。

#### 定義 7.1 Evolution Profile

SFT v2 の evolution profile `E` は、次の選択データの組である。

```text
E := (
  頂点集合と辺集合(有限 DAG。辺は selected forward transition),
  admissible merge family の集合(どの {A_i -> M} を被覆と宣言するか),
  base 選択(各 admissible merge family に対する selected base と overlap データ),
  rewrite policy(履歴書き換えをどう商に写すか; 定義 7.6),
  輸送データ(各辺の u_e; 定義 8.3),
  law universe(P1 では定数 U),
  係数と調整群の選択(第III部 段階1 で使用),
)
```

以下の構成はすべて `E` に相対化される。`E` に含まれない事象・遷移について本文は沈黙する。

#### 定義 7.2 開発トレース圏

`E` の有限 DAG 上の自由圏を開発トレース圏と呼び、`𝒯_E` と書く。
対象は selected version state、射は selected forward transition の有限合成である。

```text
revert は新しい前進辺として扱う。逆射は導入しない。
categorical inverse が必要な regime は、別の selected 構造として隔離する。
```

#### 定義 7.3 トレース位相(生成位相)

`E` の admissible merge family `{A_i -> M}` を被覆の生成元と宣言し、
`𝒯_E` 上の被覆構造を次の閉包で定義する。

```text
(i)   同型(恒等)被覆: {M -> M} は M を被覆する。
(ii)  宣言被覆: E の admissible merge family {A_i -> M} は M を被覆する。
(iii) 引き戻し閉包: sieve S が M を被覆し、h : N -> M が射なら、
      h による S の引き戻し sieve は N を被覆する。
(iv)  合成閉包: S が M を被覆し、S の各射に対しその domain の被覆 sieve を選ぶと、
      それらの合成が生成する sieve は M を被覆する。
(v)   飽和: 被覆 sieve を含む sieve は被覆する。

トレース位相 := 宣言被覆を含み (i)(iii)(iv)(v) で閉じた最小の sieve 族。
```

これは AAT 第II部 定義7.1(admissible cover から生成される最小の Grothendieck topology)
の方式の借用である。semantic な条件から base change や transitivity が自動的に従うとは
仮定せず、生成側で公理を閉じる。生成位相の sieve は有限 DAG 上で有限的に列挙できる
(付録 D.2 で実例を列挙する)。

#### 原則 7.4 Base Is Data(base はデータである)

branch 対の「共通の底」(overlap)は、圏論的 pullback として計算しない。
`E` の base 選択データとして与える。

```text
理由 1: バージョン圏は pullback を持たない。criss-cross 履歴では
        極大共通祖先が複数あり、標準的な overlap は存在しない。
理由 2: マージ点は colimit ではない。同じ親対から相異なる解決 M, M′ が作れる。
        解決は貼り合わせの選択であり(第III部)、普遍性と両立しない。
```

これは AAT 第X部 定理6.4「Incidence Is Data」(certified)の方式の継承である。
criss-cross の正準実例は付録 D.6 に置く。

#### 原則 7.5 マージ被覆

マージ点はその親 branch たちに被覆される。

```text
{A -> M, C -> M} covers M.
```

この一文が第III部(マージ=降下)の土台である。線形履歴は宣言被覆が空(同型被覆のみ)の
退化例である。

#### 定義 7.6 履歴書き換え商

rewrite policy は、トレース圏の間の functor

```text
q : 𝒯_E -> 𝒯_{E′}
```

であって、選択された部分図式(たとえばダイヤモンドの内部)を単一辺へ潰すものである。
squash はダイヤモンド内部の対象を消し、rebase は辺を別の底点上の新しい辺に写す。

#### 定理候補 7.7 Witness 生存

履歴書き換え商 `q` の下で、第II部・第III部の witness(曲率 witness、衝突類)の
生存・消滅は次の形で分類されると期待する。

```text
q がダイヤモンド内部を潰すなら、そのダイヤモンドの merge residue witness は
𝒯_{E′} 上では表現を持たない(消滅)。
q が辺の細分・直列化に留まるなら、witness は q に沿って輸送される(生存)。
```

系として測定契約が従う: witness の計算は書き換え前の trace 上で行う(付録 A)。
分類の完全な形は、輸送データの q-適合を固定して初めて定理になる。

### 8. 進化族と場の配置

#### 定義 8.1 Fiber

各対象 `t ∈ 𝒯_E` に、selected Atom family `A_t` 上の AAT 幾何を割り当てる。

```text
𝔛_t := X_{A_t}^{V, U, J, k}
```

記法注記: AAT 正典の記法は `X_C^{V,U,J,k}`(AG README。AAT 付録 A.2 はパラメータ組
`(V,U,J,k)` を扱う)である。本文の `X_{A_t}^{V,U,J,k}` は AAT 記法の再定義ではなく、
解釈境界を通じて得られた selected Atom family を index に使う SFT 側の
selected-family notation である。数学本文にコードベースは現れない(D4)。

P1 では law universe `U` は 𝒯 上で定数である(U_t 定数 regime)。

#### 定義 8.2 場の配置

fiber `𝔛_t` 上の選ばれた層データ一式を、時点 `t` の場の配置と呼ぶ。

```text
Φ_t := (構造層 O^U, law algebra, obstruction ideal I_Ob, 選ばれた semantic 層・state 層)
```

「コードベースは場である」というスローガンの本文内の実体はこれである:
場の配置は selected Atom family の AAT 影であり、選ばれていない側面については沈黙する。

#### 定義 8.3 輸送データ(quiver connection 方式)

`𝒯_E` の各 selected 辺 `e : t -> t′` に、部分 context 対応

```text
u_e : 𝔛_t <- K_e -> 𝔛_{t′}
```

(span。生成・削除された context は対応の外)と、cover 適合条件
(K_e の像が両側で selected cover と両立すること)を、`E` の明示データとして与える。

```text
輸送は辺生成子の上にだけ与え、path へは自由合成で延長する。
平行 path 上の輸送の一致は要求しない。
```

#### 原則 8.4 欠損が場の強さである

平行 path 上の輸送の一致(pseudofunctor coherence)を公理にしない。
マージ点でそれを要求すると、第II部のダイヤモンドホロノミー(この理論の中心対象)が
恒等的に消える。平行輸送の不一致は、除去すべき欠陥ではなく、測るべき量である。

#### 定義 8.5 歴史

トレース路に沿った場の配置の整合族(prestack / presheaf level)を歴史と呼ぶ。

```text
歴史 := 路 t_0 -> t_1 -> ... -> t_n と、各辺の輸送に沿って比較された配置の族 (Φ_{t_i})
```

#### 原則 8.6 Descent Is a Diagnosis(降下は公理ではなく診断である)

merge cover に対する層条件(descent)を歴史に課さない。
課すと `Φ_M` が親と base から一意に決まり、衝突解決の自由が消える。
descent の成立・不成立は、第III部の診断述語(衝突類の零性)である。

#### 定義 8.7 場の記憶

トレース site `𝒯_E` と、その上に堆積した配置・力・witness の全体を場の記憶と呼ぶ。
記憶は独立概念ではない: 開発時空そのものが記憶である。

### 9. 観測系と生成模型

トレース site は実現した履歴の記録であり、それ自体は運動法則ではない。
力学系を名乗るには、可能な軌道の空間と、それを生成する法則が要る。
本節はこの二つを分離して与える。

#### 定義 9.1 ObservedDevelopmentSystem

実現済みのトレース site `𝒯_E` と配置族 `(Φ_t)`、および各辺の力の記録(第II部)を持つ組を
ObservedDevelopmentSystem(観測系)と呼ぶ。観測系は記録であり、法則を含まない。

#### 定義 9.2 GenerativeDevelopmentModel

次のデータの組を GenerativeDevelopmentModel(生成模型)と呼ぶ。

```text
(source rule, policy Π, admissible force schema family, measurement rule)
```

成分の対応: source rule は 𝔖 の生成(第IV部で構造化)、measurement rule は 𝔐 の読みであり、
P1 では 𝔇 の (𝔖, Π, 𝔐) が生成模型を与える。記号 𝒪 は 𝔖 の状態部分を指す。

生成模型は生成子(閉ループ更新対応)を定める。分岐・合流を生成できるよう、
状態は単一の配置ではなく **frontier(トレース DAG の反鎖上の配置の族)**である。

```text
T_Π : frontier ⇒ P(次の frontier と、それを実現する step)

step は三種:
  前進   — frontier の一枝に力を適用する(源が可視場を見て生成し、方針が選好する)
  分岐   — 一枝を複製する(branch)
  マージ — 複数親の配置の組(例: (Φ_A, Φ_C))と selected base を引数に取り、
           貼り合わせの選択(第III部)で一枝に合流する
```

`T_Π` は非決定・方針添字つきである(coalgebra 状態 -> P(ラベル × 状態) の形。状態 = frontier)。
P1 では `𝒪`(組織状態)と `U` は定数として扱ってよい(第IV部で可変化する)。

#### 定義 9.3 挙動空間

初期 frontier から `T_Π` が生成する frontier 列と、その step 群が押し出す
トレース DAG・配置族の全体を挙動空間と呼ぶ。

```text
𝔗(𝔇, Π) := { T_Π の許容軌道(frontier 列が押し出す DAG つきトレースと配置族) }
```

Π を引数に明示するのは、同じ (𝒯, 𝔛, 𝔖, 𝔐) の下で方針だけを差し替えて
挙動空間を比較するためである(第VI部)。
到達集合・吸収類・可制御性(第VI部・第IX部)は、すべて挙動空間上の量化である。

#### 定理 9.4 TraceRealization [Certified bounded inference]

有限の観測系と生成模型を固定する。このとき次は同値である。

```text
(a) 観測 trace は T_Π の解軌道である(挙動空間の元として実現される)。
(b) 観測 trace の各辺に、
      source generation witness(その力が source rule から生成可能)
      policy selection witness(その力が Π の下で選択可能)
      transport witness(輸送データとの適合)
      field update witness(配置の更新が力の適用と一致)
    が存在する。
    マージ辺の witness は、親組の配置(例: (Φ_A, Φ_C))と selected base を
    引数に取る貼り合わせ選択を含み、隣接辺と頂点配置を共有する(整合条件)。
```

証明の読み: (b) ⇒ (a) は step の個数に関する帰納で、witness を繋いで
frontier 列を構成する(分岐は複製 step、マージ辺は親組を引数に取るマージ step になる)。
(a) ⇒ (b) は解軌道の定義の展開である。内容は同値性そのものではなく、
(b) が辺ごとに独立に検査可能な形になっている点にある。

#### 原則 9.5 Reconstruction Is Not Realization(命名規律)

`T_Π` を観測 trace から後付けで構成した場合(source rule を trace の生成で定義するなど)、
定理 9.4 の主張は定義から真になる。その場合は定理ではなく reconstruction lemma と呼ぶ。
定理 9.4 が内容を持つのは、生成模型が trace と独立に宣言されている場合だけである。

### 10. 第I部の結論

```text
時間 = 有限 DAG 上の自由圏 + 生成位相(マージ被覆)
空間 = selected Atom family 上の AAT 幾何の族 + 辺上の輸送データ
記録 = 観測系(trace と配置の堆積)
法則 = 生成模型(T_Π)と挙動空間
接続 = TraceRealization(witness による検査可能な同値)
```

第I部は、未選択の遷移・事象・輸送について主張しない。
次の第II部では、この時空の上の力を定義し、その合成の順序依存性(曲率)を測る。

## 第II部 力の幾何(The Geometry of Forces)

問い(この部の採否規律): 力の合成の順序依存性は、選ばれた接続に相対化された
残差として定義可能で、有限実例で計算可能か。

### 11. ForceSchema

力は二層で定式化する。位置(trace 辺)に載る前の schema と、trace 上の実現である。
この分離により、commute・再適用・輸送・曲率を schema の水準で語り、
trace 上の力をその実現として扱える。

#### 定義 11.1 ForceSchema

```text
s := (W_s, C_s, φ_s, dom_s, τ(s))

W_s   : 台(触る範囲の selected context family)
C_s   : selected complement family
        ({W_s, C_s} が fiber の selected cover をなす。
         complement は補集合演算ではなく選択データである)
φ_s   : 局所作用(dom_s を満たす配置の W_s 部分に働く)
dom_s : domain 条件(φ_s が適用可能な W_s 上の局所配置の述語)
τ(s)  : 力の型(定義 11.3)
```

ForceSchema は trace 辺にはまだ載っていない。

#### 公理 11.2 Locality

```text
φ_s は Φ|_{W_s} のみに依存し、dom_s を満たす任意の配置に適用できる
(patch 型の部分局所作用素)。
```

この公理が力の再適用・輸送を可能にする。W_s の外の配置は φ_s の値に影響しない。

#### 定義 11.3 力の型分類

```text
τ(s) ∈ { 点 / 法則 / コスト / semantic / 目標編集 / 選択 }

点        : 場の配置側を動かす(state・structure・law データ成分を含む。feature / repair)
法則      : law universe・law algebra の構造側を動かす(P1 では U 定数のため凍結。
            場の配置の law データ成分(セクション)への作用は「点」型に属する)
コスト    : コスト幾何を動かす(第VI部で可視化)
semantic  : selected semantic 層への作用
目標編集  : lawful locus の目標側を動かす(spec の書き換え。第VI部)
選択      : 貼り合わせ・却下の選択(第III部の解決、第IV部のレビュー)
```

特別な二類に名前を与える。

```text
refactor force := selected semantic 射影が零の力(選ばれた semantic profile に相対的)
repair force   := 選ばれた障害類(第III部では衝突類と呼ぶ)を消す方向の力
                  (AAT 第V部 repair、第X部 SAGA の読み)
```

役割(エンジニア・アーキテクト・PdM)は力の型の分布として第IV部で導入する。
役割は人ではなく力に付く。

#### 定義 11.4 作用痕と closure 割り当て

```text
作用痕 footprint(s) :=
  dom_s が読む context の族
  ∪ φ_s の適用が(restriction 誘導効果を含めて)層データ比較を非恒等にし得る context の族
  (law データの restriction 先を含む)

closure 割り当て cl(s) :=
  E(または schema)の選択データとして与える context 族。W_s ⊆ cl(s) を要求する。
```

原則 22.1 の契約は「cl(s) ⊇ footprint(s) の証明」を意味する。

#### 公理 11.5 効果封じ込め

```text
φ_s の適用は、restriction 誘導効果を含めて cl(s) の外の層データ比較を恒等に保つ。
```

公理 11.2 は読みの局所性、公理 11.5 は書きの封じ込めである。両者は独立の仮定である。

### 12. AppliedForce

#### 定義 12.1 AppliedForce

```text
f := (e, s, u_f, witness)

e       : t -> t′ (𝒯_E の辺)
s       : ForceSchema
u_f     : selected 輸送(complement 同一視を含む。定義 8.3 の u_e と適合)
witness : before / after 配置と適用の証拠(定理 9.4 の field update witness)
```

#### 原則 12.2 「台の外では恒等」の正確な形

異なる fiber の間に補集合は存在しない。「台の外では恒等」は次の条件文である。

```text
u_f に沿った C_s 上の層データ比較が恒等である。
```

complement `C_s` は選択データであり、この条件は `E` の輸送データに相対化される。

### 13. 接続

#### 定義 13.1 接続(selected transport 規則の族)

分岐した二つの力(共通の始点から別々の辺に載った AppliedForce)の間で、
一方を他方の後へ輸送する規則の族を接続と呼ぶ。

```text
接続 := ダイヤモンド(span と辺の対)ごとに選択された transport 規則の族。
接続が対 (f, g) に両輸送 g^f(f の後へ輸送された g)と
f_g(g の後へ輸送された f)を与えるとき、この対を輸送可能と呼ぶ。
cl(定義 11.4)が互いに素な対には、自明輸送(g^f = g, f_g = f)を常に選べる。
```

接続は evolution profile の選択データであり、正準ではない。

#### 原則 13.2 正準接続は存在しない

第II部・第III部の曲率・ホロノミー・merge residue は、すべて選択された接続に相対化される。
異なる接続は異なる残差を与える。接続の実例(patch commute、操作変換、rebase 規則)は
付録 A・E で解釈境界側に置く。

### 14. Commute

#### 定義 14.1 Commute(曲率零の証明書)

選択された接続が対 `(f, g)` に両輸送を与え、かつ selected 比較水準で等式

```text
g^f ∘ f = f_g ∘ g
```

が成立するとき、commute `(f, g) ↦ (g^f, f_g)` が定義されると言う。
commute は部分演算であり、その定義可能性は「二辺形が閉じる」ことの証明書
(定義 15.1 の曲率が零であること)と同値である。
trace 上の AppliedForce は schema 合成の実現として扱う。

#### 原則 14.2 輸送不能対が第一の障害である

輸送可能ですらない対(g を f の後へ輸送する規則が選ばれた接続に無い)は、
第III部の filtration に入る前の、最初の衝突である。
合成記号 `f∘g` を、両者が同じ始点を持つ schema 対に対して無条件に書かない。

#### 定理 14.3 遠隔可換 [Certified bounded inference]

仮定:

```text
(i)   closure 割り当ては原則 22.1 の契約を満たす
      (cl は作用痕の証明された過大近似である; 定義 11.4)。
(ii)  cl(f) ∩ cl(g) = ∅(selected cover の意味で)。
(iii) 公理 11.2(読みの局所性)と公理 11.5(効果封じ込め)。
(iv)  初期配置で dom_f と dom_g がともに成立する。
```

結論:

```text
自明輸送の下で commute (f, g) は定義される(g^f = g, f_g = f)。
両順序の合成は同じ配置を与える(δ(f, g) = 0)。
```

証明の読み: 作用域(定義 11.1)と効果封じ込め(公理 11.5)により、
f の適用は cl(f) の外の層データ比較を恒等に保つ。(ii) と (iv) により、
f の適用は g の domain 条件を保存し、逆も成り立つ。
したがって両順序の合成が定義され、配置の各成分
(cl(f) 部・cl(g) 部・残り)への作用が順序に依存しない。

(i) が仮定に含まれる理由: cl が作用痕の過小近似なら、(ii) が見かけ上成立しても
実際の作用痕が重なり、結論は保証されない(unsound)。付録 D.4 に、
file 水準では素だが cl が重なる実例を置く。

### 15. 力の曲率

#### 定義 15.1 力の曲率

選択された接続が両輸送を与える対 `(f, g)`(輸送可能な対)に対し、二辺形

```text
g^f ∘ f  と  f_g ∘ g
```

の比較残差 witness を力の曲率と呼び、`δ(f, g)` と書く。
`δ(f, g) = 0`(selected 比較水準で両合成の結果が一致)であることと、
commute `(f, g)` が定義されること(定義 14.1)は同値である。

abelian 係数 regime では、`δ(f, g)` は宣言された受け皿の値として読む。
受け皿は次のいずれかを `E` で宣言する。

```text
(a) AAT 第VI部 定義9.4(presentation two-complex)の 2-cell 値
(b) t-依存 selected incidence site 上の total complex の (1,1) 成分(定理候補 17.1 の受け皿)
(c) selected 共有 context 上の law 係数値(abelian regime での直接差。付録 D はこれを使う)
```

#### 原則 15.2 受け皿未固定の式は reading schema である

受け皿(複体・係数・比較)が固定されていない曲率の式は、定義ではなく
reading schema として扱う(D2。AAT 第IX部 定義3.4 の規律の継承)。

命名注記: 本文の「力の曲率」は、AAT 第VIII部 定義8.9 Curvature Transfer Spectrum
(スペクトル曲率 reading)とは別対象である。本文では常に「力の曲率」と修飾する。

### 16. ダイヤモンドホロノミー

#### 定義 16.1 ダイヤモンドホロノミーと merge residue

ダイヤモンド

```text
B -> A -> M
B -> C -> M
```

と選択された接続に対し、B 上の選ばれた層データを二つの経路に沿って M へ平行輸送し、
その比較残差をダイヤモンドホロノミーまたは merge residue と呼ぶ。

```text
residue(diamond) := 比較(transport_{B->A->M}(section), transport_{B->C->M}(section))
```

DAG に逆射はないため、「一周」ではなく「二つの平行輸送の M 上での比較」として定義する。
abelian 係数 regime では residue は差として読める(付録 D.5 で計算する)。

#### 定理 16.2 局所零曲率から大域零残差は従わない(非含意)[Certified bounded inference]

受け皿を先に固定する: k 枝の admissible family と対ごとの比較同型(接続の選択)に対し、
branch ごとの大域調整(coboundary)で全辺値を同時に消せるかを問い、その障害を
nerve 上の selected abelian 係数の H¹ で読む(**大域同定残差**。
二枝の場合は定義 16.1 の merge residue の abelian 読みと一致する; 定数 fiber regime)。

主張: 対ごとの二辺形がすべて閉じる(選ばれた接続での曲率零)ことから、
大域同定残差の消滅は従わない。

証明: 付録 D.12 の有限反例(三枝被覆の nerve 上の Z/2 係数で、辺値 (0, 0, 1) は
対ごとには閉じ方の witness だが、大域調整の三式の和が 0 = 1 となり解なし。
[(0, 0, 1)] ≠ 0 ∈ H¹(∂Δ², Z/2) = Z/2)。

AAT 第VI部の monodromy、第IV部 §9 の Boundary Holonomy Theorem(certified)が
AAT 側の対応構造である。Lean 化(L3)は別途進める。

### 17. 可積分性

#### 定理候補 17.1 力の可積分性障害(SFT 側対応)

AppliedForce `f` の temporal mismatch 類

```text
ob(f) ∈ H¹(t-依存 selected incidence site, selected abelian 係数)
```

が定義されているとする。このとき

```text
ob(f) ≠ 0 ⇒ f は selected cover 上の大域 lawful 進化へ積分できない
```

と期待する。受け皿となる t-依存 incidence site の構成は SFT 側の新規数学であり
(骨格ノート §10)、構成・係数・検出性を固定して初めて定理になる。
この帰結に依存する本文の主張は、すべて conditional として扱う。

#### 命題候補 17.2 固定 fiber regime での比較

すべての輸送データ `u_e` が恒等で fiber が固定される regime では、
定理候補 17.1 の受け皿は AAT 第IX部の固定積 site `Tr_E × X` に還元され、
主張は AAT 第IX部 定理候補7.2(Force Integrability Obstruction)と一致すると期待する。
AAT 側の定理候補は AAT 側にそのまま残る(D3)。両者の関係はこの比較命題だけが担う。

### 18. 第II部の結論

```text
力       = ForceSchema(台・complement・局所作用・型)+ AppliedForce(辺上の実現)
接続     = 選択された transport 規則の族(正準でない)。輸送可能性が最初の関門
可換     = commute(曲率零の証明書)。素な cl なら自明(定理 14.3)
曲率     = 二辺形の比較残差(受け皿宣言つき)
ホロノミー = ダイヤモンドの平行輸送比較 = merge residue
可積分性 = H¹ 類による障害(conditional; AAT IX 7.2 の SFT 側対応)
```

第II部は、接続と受け皿が選択されていない対について曲率・残差を主張しない。
次の第III部では、merge residue を三段の診断 filtration へ展開する。

## 第III部 マージと降下(Merge and Descent)

問い(この部の採否規律): マージの障害は独立な水準に分解され、各水準は
別の機械(validity / Čech H¹ / Tor)と別の有限実例で測れるか。

### 19. バージョン管理は降下理論である

マージ点は親 branch たちに被覆される(原則 7.5)。branch 上の局所データからマージ点の
大域データを作ることは、被覆上の降下である。降下は公理ではなく診断であり(原則 8.6)、
マージ解決とは貼り合わせデータの選択である。

本部の主定理は、マージの障害を三つの独立な段階に分解する診断 filtration である。

### 20. 三段の診断 filtration

以下、`E` のダイヤモンド(span `A <- B -> C` と cover `{A -> M, C -> M}`、selected base `B`)
を固定する。

#### 定義 20.1 段階0: 台(selected cocone の validity)

選択された presentation 圏と融合手続き `amalg(A, C; B)` に対し、段階0 の診断は次である。

```text
段階0 通過 := amalg が valid state の部分圏の中に結果を持つ。

二つの失敗様式を区別する:
  不存在    — selected 圏に融合が存在しない。
  非正準性  — 融合は存在するが標準的な選択が存在しない(選択データが要る)。
```

集合的な presentation 圏では自由融合はほぼ常に存在する。いわゆるテキスト衝突の実体は
多くの場合「非正準性」または validity 失敗であり、「押し出しの不存在」ではない。

#### 原則 20.2 押し出し語の限定

「押し出し」の語は presentation・状態圏の水準でのみ使う。トレース site の側では
cover の語だけを使う。マージ点を colimit と読まない(原則 7.4)。

#### 定義 20.3 段階1: 法則(base の nerve 上の Čech H¹)

段階0 を通過したダイヤモンドに対し、次の選択データを宣言する。

```text
係数     : selected abelian 係数(law データの差を読む層 F; AAT 第X部の additive regime)
nerve    : cover {A -> M, C -> M} の nerve。overlap は selected base B(のデータ)
調整群   : G_A, G_C — 各 branch 上で許される調整(selected。
           branch のテスト・契約で固定された自由度の残り)
```

mismatch cochain と衝突類を次で定める。overlap は trace 頂点そのものではなく、
base 選択データが指定する fiber 内の selected context 族である。

```text
δ⁰ : G_A × G_C -> Γ(overlap, F),  δ⁰(g_A, g_C) := g_A|_overlap − g_C|_overlap

m(A, C) ∈ Γ(overlap, F) := 輸送された law セクションの overlap 上の差
[m] ∈ H¹_E := Γ(overlap, F) / im δ⁰

段階1 通過 := [m] = 0(許された調整の範囲で law データが貼れる)
```

これは cover 相対の Čech 読みであり(AAT 第IV部)、調整群つきの additive H¹ は
AAT 第X部 §4(certified)の機械の借用である。
注記: 定義 16.1 の merge residue とこの衝突類の同一視は、定数 fiber・恒等輸送の
regime に限る(付録 D はこの regime にある)。

#### 定義 20.4 段階2: 導来(transported loci の Tor)

段階0・1 を通過し、貼り合わせの選択によって `𝔛_M` と law データが構成されたとする。
同定データ(branch 由来の law loci を `𝔛_M` 内の部分対象として同定する選択)を明示的仮定とし、
二つの transported law loci の導来交叉を読む。

```text
段階2 通過 := 選ばれた正次数で Tor が消える(導来交叉が古典交叉に一致する)。
段階2 障害 := 正次数の Tor ≠ 0(古典的には貼れたが、導来交叉が衝突を記憶している)。
```

次数 0 の Tor₀ = R/(I+J) は古典交叉の非空性の判定であり、段階2 ではなく
法則充足の別診断として扱う(AAT 第V部の LawConflict₀ と整合)。
AAT 第V部(定義4.1 導来 joint lawful locus、定理6.1 Derived Law Conflict(certified)、
命題5.5 monomial conflict calculation(certified))がこの段階の機械を与える。
「テキストは貼れたが意味が壊れる」の数学的実体はここにある。

#### 定理 20.5 マージ診断 filtration [Certified bounded inference]

`E` の有限ダイヤモンドと、宣言された融合手続き・係数・調整群・同定データを固定する。
このとき:

```text
(i)   三つの診断は列をなして well-defined である。各段階の診断は、
      前段階の通過(と、その段階までの選択データ)に相対化されて定義される。
      段階0 が不成立なら、段階1 以降は未定義または conditional である。

(ii)  三段は独立な障害を測る。すなわち、
      段階0 通過かつ段階1 障害の有限例、および
      段階0・1 通過かつ段階2 障害の有限例が存在する(付録 D.5)。

(iii) 段階0・1 が通過するなら、その通過 witness(valid な融合結果と、
      調整後に overlap 上で一致する law セクションの組)から、
      base 契約(原則 22.2)の下で、貼り合わされた law データつきの
      マージ配置が構成できる。段階2 の通過は、その配置の上で選ばれた law 対の
      導来残差が無いことを言う。法則の充足可能性(joint lawful locus の非空性)は、
      三段のいずれからも従わない(別診断である)。
```

証明の読み: (i) は定義の連鎖である。(ii) は付録 D.5 の二つの計算
(rounding の H¹ = Z/2 の非零類と、shared witness factor の Tor ≠ 0)が実例を与える。
(iii) は、段階1 の通過 witness が調整後の一致セクションを与え、base 契約により
overlap が共有 law restriction 先を過大近似しているため、一致が貼り合わせに十分になる。
段階2 は構成にではなく導来残差の不在に寄与する。

内容は分類の完全性ではなく、診断の分解にある: 三つの障害は別の水準に住み、
別の機械で測られ、別の実例で分離される。

### 21. 並列開発の平坦性

#### 定理 21.1 素な台の合流 [Certified bounded inference]

有限個の ForceSchema の族 `{s_1, ..., s_n}` が、原則 22.1 の契約の下で
pairwise に `cl(s_i) ∩ cl(s_j) = ∅` を満たすなら:

```text
すべての対で commute が定義され輸送は自明であり(定理 14.3)、
任意の適用順序が同じ配置を与える。
この族が誘導する任意のダイヤモンドの merge residue は零であり、
自明な調整群の下で段階1 の衝突類も零である。
```

証明の読み: 定理 14.3 を対に適用し、順序の入れ替えの有限列で任意の置換を実現する。
残差零は、両経路の輸送がともに「各台成分への独立な適用」に一致することから従う。

#### Model theorem 21.2 可換化への持ち上げ(CRDT 型模型)

状態を metadata(一意 ID、因果時計、tombstone)で拡大し、更新を
**schema 指定元との join として作用させ**(delta-state 型: u_a(x) = x ∨ a)、
状態代数を join 半束(結合・可換・冪等)とし、配送仮定
(causal delivery、または冪等な再配送)を置いた模型族を考える。この模型の内部では:

```text
(一) join の対称性から、すべてのダイヤモンドの merge residue は零である。
(二) delta 型更新の逐次可換性(u_a ∘ u_b = u_b ∘ u_a が半束律から従う)から、
     台が重なる concurrent 対に対しても δ(f, g) は構成的に消える。
```

模型非自明性(D6): 同じ模型族で更新を非冪等な作用(例: counter の +1)に置き換え、
at-least-once 配送(重複配送)を許すと、再配送の重複により複製間の状態が
1 と 2 に分岐し、残差非零の実例になる。両相は非空である。

命名注記: これは力の代数の「可換化(商)」ではなく、可換な理論への**持ち上げ**である。
局所可換(曲率零)から大域順序非依存は従わない(定理 16.2)ため、
(一)と(二)は別命題として述べた。inflationary(x ≤ u(x))だけでは
逐次可換は従わない(u(x) = 2x と v(x) = x + 1 は非可換)ことにも注意する。

### 22. 台と base の健全性契約

#### 原則 22.1 closure は作用痕の過大近似でなければならない

第II部・第III部のすべての「素な台」仮定における closure 割り当ては、
作用痕(定義 11.4)の**証明された過大近似**である。

```text
過大近似(cl ⊇ footprint)で「素」 ⇒ 定理の結論が使える(安全側)。
過小近似で「素」                  ⇒ 結論は保証されない(unsound)。
```

作用痕は law データの restriction 先(共有 contract context)を含む。
付録 D.4 に、file 水準の台は素だが cl が重なる正準実例を置く。
実在の開発系での closure の推定は付録 A の計器契約である。

#### 原則 22.2 base は過大近似でなければならない(base 契約)

段階1 の診断は selected base の overlap データの上でしか mismatch を見ない。
したがって次を契約とする。

```text
selected base の overlap データは、マージ点上の共有 law restriction 先の
証明された過大近似である。
```

過小近似の base では、真の law 衝突が overlap の外に隠れ、診断は unsound になる
(付録 D.6 の base = B1 は、この契約に違反する選択の実例である)。

### 23. 積方向のダイヤモンド(予告)

トレース site の積方向(feature flag / tenant / 環境)にも分岐と収束は現れる。

```text
flag on / off   = 積方向の二つの仮想 branch
flag 除去       = 積方向のマージ
```

積方向のダイヤモンドにも §20–§22 の機械がそのまま適用できる(statement level)。
trunk-based 開発では、ダイヤモンドは branch 軸ではなく flag 軸に立つ。
本節の完全化は第VIII部(アンサンブル)とともに P4 で行う。

### 24. 履歴書き換えとの関係

squash はダイヤモンド内部を潰すため、その merge residue witness は書き換え後の
trace 上に表現を持たない(定理候補 7.7)。したがって測定契約が従う:

```text
曲率・残差・衝突類の witness は、履歴書き換えの前の trace 上で計算する。
```

これは本文の定理ではなく、付録 A の解釈境界(計器契約)に属する。

### 25. エージェント並列度への系(予告)

定理 21.1 と原則 22.1 は、次の形の Model theorem を示唆する。
第VIII部の模型宣言の下で定理化する(定理候補)。

```text
N 個の源が生成する schema の台(closure)の重なり分布が与えられた模型では、
安全に並列適用できる族のサイズは、重なり確率と残差の分布で上下から抑えられる。
源が共通の delegator を持つ(相関する)ほど重なり確率は上がり、
独立性を仮定した並列度の見積もりは危険側に外れる。
```

反証仮説 H4(diversity premium)が付録 B の台帳でこの系に対応する。

### 26. 第III部の結論

```text
マージ     = cover 上の降下の問題
診断       = 三段 filtration(台の validity / 法則の Čech H¹ / 導来の Tor)
解決       = 貼り合わせデータの選択(普遍性ではない)
並列性     = 素な closure 台の合流(定理)+ 可換化への持ち上げ(模型)
健全性     = 台の過大近似契約
```

第III部は、宣言されていない融合手続き・係数・調整群・同定データについて衝突を主張しない。

## 第IV部 参加者と組織(Participants and Sources)

問い(この部の採否規律): 開発組織は、意図・心理に沈黙したまま、
力の生成・所有・可視性・選択の構造として数学化できるか。
その構造は定理か有限実例で実際に使われるか。

### 27. 組織圏と源

#### 定義 27.1 組織圏

時点 t の組織圏 `𝒪_t` を次で与える。

```text
対象: participant / team / mob(複数 participant の合成源)/
      delegator(model・prompt・policy・規約などの生成様式の共有元)
射:   selected reporting / collaboration / delegation
```

役割(role)は対象にしない。役割は力の型の分布として人に付く(定義 29.3)。
「site」は名乗らない: 組織側の被覆データ(communication cover)を使う定理は
第V部(P4)で立つため、その導入も第V部に置く。それまで `𝒪_t` は圏である(D1′)。
reporting / collaboration 射と mob 対象は、第V部(Conway)・第VIII部(アンサンブル)で
使う選択データの予約であり、P2 の定理・実例で使うのは delegation 射だけである。

#### 原則 27.2 沈黙規律

意図・心理・信念・文化は扱わない。trace に現れる生成・選択だけを扱う(序 §5)。

#### 定義 27.3 組織状態

`𝒪` は源構造 𝔖 の状態部分である(定義 9.2 の記号)。P1 で定数とした `𝒪` は、
以後 𝒯 上の族として扱ってよい(reorg は組織側への力である。
組織と幾何の結合力学は第V部・第VIII部)。

### 28. 所有と可視性

#### 定義 28.1 所有対応

```text
own_t ⊆ 𝒪_t の対象 × fiber の selected context 族
```

participant / team に selected context 族を割り当てる選択データ。
ownership 由来の被覆 index は第V部(Conway 対応)で使う。
P2 での使用は可視性・バス係数(定義 28.3)と付録 D.9 の実例である。

#### 定義 28.2 可視性割り当て

participant `p` に、`p` が読める場の部分データ `V_p ⊆ Φ_t` を割り当てる。
「層」を名乗るのは restriction 構造を使う定理が立ってからにする(D1′)。

#### 定義 28.3 バス係数とバス事象

```text
context W のバス係数 := W を可視に持つ participant の数(selected 可視性の下で)
バス事象           := バス係数 1 の context の唯一保持者の離脱
```

可視性の力学は analytic reading として読む: オンボーディング = V_p の成長、
AI participant の V_p はセッション毎に蒸発し、組織記憶は trace 側(場の記憶、定義 8.7)へ移る。

### 29. 生成・役割・目標場

#### 定義 29.1 生成

```text
gen_p : (V_p, 目標場) -> 提案された力(ForceSchema)の族
```

源は可視データと目標場だけから力を生成する(可視性の外は生成に現れない)。

#### 定義 29.2 提案された力と適用された力

提案 = gen の出力。適用 = 選択(§31)を経て trace に載った AppliedForce。
レビューによる修正は「提案された力の置換」として記録し、両者の区別を保存する
(旧 ProposalAccounting が守っていた区別の継承; 付録 F)。

#### 定義 29.3 役割プロファイル

participant `p` の役割プロファイルとは、選ばれた窓内で `p` が生成した力の
型分布(定義 11.3 の τ の分布)である。役割は力に付き、人には分布として付く。
役割の流動性 = プロファイルの移動。実務上の役割名(エンジニア・アーキテクト・
デザイナー・PdM・レビュアー)との対応は付録 A に置く。
AI agent は専用公理を持たない participant であり、違いは生成率・可視性・
delegator 相関(§30)の形だけである。

#### 定義 29.4 目標場

lawful locus の目標を指定する選択データ。gen への入力であり、場には直接作用しない
(二段構造: 目標場 → 源 → 力)。P1–P2 の U 定数 regime では凍結されている。
「ポテンシャル」の呼称は、gen の応答公理(ギャップ単調性)を置いた模型でのみ許す(付録 C)。
目標編集の力(τ の一類)はこの目標場への作用である。

### 30. 相関の担い手

#### 定義 30.1 delegator 分解と相関

力 `f` の源 `p` が delegator `d` を delegation 射で経由するとき、`f` は `d` 由来の
生成様式を持つと言う。

```text
二つの力が相関する ⇔ その源が共通の delegator を経由して分解する
```

第III部 §25 と第VIII部の並列度・アンサンブルにおける独立性の仮定は、
共通 delegator が無いことを要求する。同一 model / prompt 由来のエージェント群の
力は独立でない(実例は付録 D.9、経験仮説は台帳 H4)。

### 31. レビュー: 計器評価と降下選択

#### 定義 31.1 レビュー

提案された力(またはマージの貼り合わせ候補)に対する、次の二つの合成をレビューと呼ぶ。

```text
(i)  計器評価: 𝔐 の pairing の読み(検出 ⇔ ⟨m, α⟩ ≠ 0)
(ii) 降下データの選択: 第III部の解決の選択、または却下
```

#### 定義 31.2 ラバースタンプ

分離能力が退化した計器族での選択(承認は続くが計測が止まっている状態)。

#### 命題 31.3 レビューの盲点 [Certified bounded inference]

仮定: additive regime(候補空間が類の torsor であり、二候補の差の類 α が
well-defined)、pairing の線形性(⟨m, x + α⟩ = ⟨m, x⟩ + ⟨m, α⟩)、
レビューの選択が計器読みの関数であること。

主張: 計器族が類 α を検出しない(すべての計器 m で ⟨m, α⟩ = 0)なら、
α だけ異なる二つの候補に対してレビューの選択は一致する(レビューは α-盲目である)。

証明の読み: 検出しないなら二候補の計器読みは一致する。選択は読みの関数だから一致する。
内容は「レビューが守れるのは計器が見る範囲だけである」という境界を pairing の言葉で
固定する点にある(第IX部の可観測性と沈黙軸有界結合の前哨)。実例は付録 D.9。

#### 原則 31.4 レビューは完全性の証明ではない

レビュー通過は、選ばれた計器族と選択の記録であり、未測定軸の安全を含意しない(D2)。

### 32. 第IV部の結論

```text
組織   = 圏(participant / team / mob / delegator と delegation 射)
所有   = own(選択データ)、可視性 = V_p、バス係数・バス事象
生成   = gen(可視データと目標場から提案された力へ)
役割   = 力の型分布(人には分布として付く)
相関   = 共通 delegator 経由の分解
レビュー = 計器評価 + 降下選択。盲点は pairing で決まる(命題 31.3)
```

第IV部は、意図・心理・文化について沈黙する。communication cover と Conway 対応は
第V部(P4)で扱う。

## 第V部 Conway 対応(予告; P4、研究課題)

第V部は communication cover(組織側)と ownership 由来の被覆(幾何側)という
独立に定義された二つの被覆データの適合と障害を扱う。定式化は cohomology からではなく、
二つの被覆の refinement / common refinement / nerve map の不整合という有限組合せ論から始める。

```text
Conway 障害(研究課題; statement 未確定)
reorg / refactor 双対(障害を消す二方向)
```

採否条件: 正準有限実例で適合例(障害零)と障害非零例の両方を構成できること。
それまで本理論は Conway 対応を定理と呼ばない。経験的な mirroring 研究との対応は
付録 B の台帳(D7 の棄却条件つき)で扱う。
(節番号 33–35 は本部の完全化時に使う予約である。)

## 第VI部 力学: 運動の法則(Laws of Motion)

本部は、理論全体を貫く力学的な像 — 追跡力学 — と、汎函数と力の類型の適合(質量収支則)、
方針の階層(CLF)、内生コストの吸収域、ゲージの商を扱う。
有限系の停止性(整礎 ⇒ 停止)は自明であり、本部の内容はそこには置かない。
内容は「どの汎函数が、どの力の類に対して、どの模型の下で Lyapunov になるか」に宿る。

問い(この部の採否規律): 修復と注入の競争、コストの内生化、ゲージの商は、
模型非自明(D6)な定理として述べられるか。汎函数と力の類型の適合は
実例で計算できるか。

### 36. 追跡力学の設定

#### 定義 36.1 ギャップ汎函数

selected な非負値汎函数

```text
e : 場の配置 -> 非負値
```

をギャップ汎函数と呼ぶ。代表例は、選ばれた測定 profile での obstruction mass、
および distance-to-flatness(AAT 第VII部 定義10.2)である。
U 定数 regime(P1–P3)では目標(lawful locus)は動かず、ギャップの時間比較に
law universe 輸送は不要である。

#### 定義 36.2 追跡模型

追跡模型は、挙動空間(定義 9.3)上の軌道に沿ったギャップ列 `(e_t)` に対する
次の模型公理の選択である。

```text
上側公理(修復の効果と目標移動の上界):
  e_{t+1} <= max(0, e_t − r_min) + v_max

下側公理(修復能力の上界と目標移動の下界):
  e_{t+1} >= e_t − r_max + v_min

r_min <= r_max : 一段あたりの修復効果の下界・上界(模型データ)
v_min <= v_max : 一段あたりのギャップ注入の下界・上界(模型データ)
```

注入 v の読み: 注入 = 目標移動または力による新規障害質量。U 定数 regime(P1–P3)では
目標移動の実現子は凍結されており、v の実現子は後者(力による注入)である。
目標移動としての読みは、law-universe transport が定義され次第(P4 以降)activate される。
利子(定義 37.3)を読む場合は、さらにコスト読み cost_t(repair | Φ_t) と
baseline_cost_t を模型データとして宣言する。

上側・下側は独立に選択できる。可能性(有界性)と不可能性(成長)は、
同じ不等式の上下ではなく、別々の公理を持つ二つの模型定理として述べる。

### 37. T0 追跡定理

#### 定理 37.1 Tracking Model A: 究極有界性 [Model theorem]

上側公理を満たす模型で `r_min > v_max` なら:

```text
(i)  e_t > r_min の間、ギャップは一段あたり少なくとも r_min − v_max 減る。
(ii) 一度 e_t <= r_min になれば、以後 e_{t+1} <= v_max。
(iii) したがって limsup e_t <= v_max であり、
      到達時間は ceil((e_0 − r_min) / (r_min − v_max)) + 1 で抑えられる。
```

証明の読み: (i) e_{t+1} <= e_t − r_min + v_max = e_t − (r_min − v_max)。
(ii) e_t <= r_min なら max(0, e_t − r_min) = 0。(iii) は (i)(ii) の帰納である。

模型非自明性(D6): 同じ模型族で `r_min < v_max` を選ぶと、
下側公理を併せ持つ実例(定理 37.2)でギャップは非有界になる。両相は非空であり、
`r_min = v_max` の帯が regime 境界である(完全な相構造は第VIII部)。

#### 定理 37.2 Impossibility Model B: 線形成長 [Model theorem]

下側公理を満たす模型で `v_min > r_max` なら、`ε := v_min − r_max > 0` として:

```text
e_t >= e_0 + ε t (すべての方針について)
```

証明の読み: 下側公理より e_{t+1} >= e_t + (v_min − r_max) = e_t + ε。帰納で従う。

この定理は方針に対する全称主張であり、「どんな方針でも追跡は失敗する」という
不可能性の形をしている。修復効果の上界 `r_max` の実体は、AAT 第VIII部 系8.7
(Essential Repair Lower Bound; certified)の読みで与えられる:
修復 route のコストは調和質量に比例して下から抑えられるため、
一段の固定予算で消せる障害質量には上界があり、
したがって達成可能な修復効果 δ_t には上界 r_max がある。
修復コストの下界は、開発速度の限界として読める。

#### 定義 37.3 技術的負債(利子つき)

```text
負債ストック       : D_t := e_t
利子(carrying cost): I_t := cost_t(repair | Φ_t) − baseline_cost_t
                      (baseline は模型データ。自己相互作用 — 現在の配置が
                       修復のコストを押し上げる分 — を測る)
技術的負債汎函数   : Debt_T := Σ_t w_t e_t + λ Σ_t I_t(重み w, λ は selected)
```

ギャップ積分だけでは「将来の変更コストを増やす」という負債の本性(interest)が消える。
利子項が、内生コスト吸収域(P2)と骨化(第VII部)への接続を与える。
cost 読みは定義 36.2 の模型データである。コスト幾何は §39–40 で固定する。

Lehman の第一法則(絶えざる変化)は、この理論では「v_min は零にならない」という
Empirical hypothesis である(付録 B、行 H5)。

### 38. 質量収支則

#### 定義 38.1 収支分解

selected mass 汎函数 `Φ_M`(定義 36.1 のギャップ汎函数の実例)と一段の力 `f` に対し、
質量変化の帰属を模型データとして宣言する。

```text
ΔΦ = In(f) − Out(f) + Res(f)

In(f)  : 注入(feature / 目標編集に帰属する新規 witness 質量)
Out(f) : 散逸(repair が消した質量)
Res(f) : マージ段の residue の質量読み(第III部 段階1 の衝突類の質量)
```

型ごとの公理(宣言): repair は In = 0、refactor は(gauge 不変 regime で)ΔΦ = 0、
マージ段だけが Res を持つ。

#### 定理 38.2 汎函数と力の類型の適合 [Certified bounded inference]

仮定: selected mass は選ばれた regime で (i) refactor 不変(semantic 零の力で不変)、
(ii) repair 非増加、を満たす(この仮定を満たす mass の存在は regime 依存であり、
付録 D.11 が有限実例を、AAT 第VIII部 定理8.5 Finite Hodge Decomposition・
定理8.6 Harmonic Debt Minimality(いずれも certified)の harmonic mass が
AAT 側の代表例を与える)。

結論:

```text
前進段のみからなり、各段の力の型が {repair, refactor} に属する軌道で、
Φ_M は非増加である(Φ_M はこの力の類の共通 Lyapunov 汎函数である)。
feature を許すと In > 0 で増加する軌道が存在し、
マージ段を許すと Res > 0 で増加する軌道が存在する(いずれも付録 D.10)。
```

証明の読み: (i)(ii) と収支分解の型公理から、前進段の ΔΦ ≤ 0。増加側は実例で示す。
マージ段(貼り合わせの選択; 選択型の力)は Res の符号を制御しない第三の源であり、
{repair, refactor} 軌道の限定はマージ段の除外を含む(第III部との接続点)。
内容は不等式ではなく適合性にある: どの汎函数がどの力の類に対して単調かは
regime の宣言事項であり、類を広げると単調性は壊れる。

#### 系 38.3 有限散逸停止

有限状態・整礎値の regime で {repair, refactor}-軌道が strict に散逸するなら有限停止する。
これは AAT 第IX部 定理5.3(certified)の特殊例であり、内容は定理 38.2 の適合性側にある
(停止性そのものは整礎帰納法の一行である)。

### 39. 方針の階層と CLF

#### 定義 39.1 方針の階層

```text
近視眼的散逸方針: 各段で評価汎函数を下げる力だけを選ぶ
有限先読み方針:   深さ B の探索で選ぶ
Bellman 最適方針: cost-to-go 値函数 V を最小化する
```

#### 定義 39.2 値函数

目標集合 `{Φ_M = 0}` への到達コストの下限を `V(x)` と書く(有限模型での最短路値)。

#### 補題 39.3 Φ–V 上下界 [Certified bounded inference]

仮定: 一段の質量減少は高々 `r_max`、一段のコストは `c_min` 以上。
さらにある方針が、到達可能な各状態で一段あたり質量を `r_min` 以上減らし、
一段コストは `c_max` 以下とする。結論:

```text
(Φ_M(x) / r_max) · c_min <= V(x) <= ceil(Φ_M(x) / r_min) · c_max
```

証明の読み: 下界は「任意の到達列は少なくとも Φ/r_max 段を要する」から。
上界はその方針の軌道が実現する。

#### 原則 39.4 近視眼と最適は別の運動原理である

cost 最小軌道は途中で Φ_M が上がってよい(migration は典型的に一旦悪化して直す)。
一段ごとの単調降下(近視眼)は局所最小に捕まり得る(数値実例は付録 D.10)。
統一装置は値函数 V を Lyapunov に採る control Lyapunov function(CLF)であり、
補題 39.3 が Φ_M と V の橋である。「測地線」の語は metric enrichment から
length minimizer を実構成するまで使わない(付録 C)。

### 40. 内生コストの吸収域

#### 定義 40.1 内生コスト追跡模型

```text
状態: 質量 n ∈ ℕ = {0, 1, 2, ...}(上限を置かない)
段:   行動の選択は注入前の質量で行い、注入と行動の効果は同じ段に作用する:
      n_{t+1} = max(0, n_t + I − R)
      I ∈ {0, 1}: 注入(確率 λ で 1; 0 < λ < 1)
      R ∈ {0, 1}: 修復を選んだ場合、成功確率 p_r で 1(0 < p_r < 1、λ < p_r を仮定)
行動: 修復 — コスト c(n) = c_0 · (1 + n)
      (自己相互作用の公理: 修復コストは現在質量に単調増加)
      機能 — 質量変化 0(価値を得る)。コスト c_f(定数)

方針: 貪欲     = 各段でコスト最小の行動を選ぶ(同額では修復を選ぶ)
      ρ-方針  = 段の比率 ρ で修復、残り 1 − ρ で機能を選ぶ(質量に依存しない)

n_0    := min{ n : c(n) > c_f }(c は非有界単調なので有限)
mud 類 := [n_0, ∞)

p_r < 1 の仮定は本質的である: p_r = 1 では貪欲帯(n < n_0)で上向きの一段
(確率 λ(1 − p_r))が起きず、質量が n_0 に到達できない。
λ < p_r の仮定は有界相の非空性に必要である(ρ_c = λ / p_r < 1 を保証する)。
```

コストが現在の質量に単調依存する(単調性公理)ことが「内生」の最小形であり、
「場が力のコストを形作る」(自己相互作用)の最小の実現である。
metric enrichment からの完全な導出(骨格の要件)は第VII部(P4)の課題として申告する。
有限上限 N を吸収として置く変種では、任意の方針が確率 1 で吸収され相の区別は消える
(準安定時間の指数増大としてのみ残る)。有限系に真の相転移がないことの実例である(付録 C)。

#### 定理 40.2 内生コスト吸収域 [Model theorem]

```text
(a) 貪欲方針: 選択時質量 n >= n_0 では修復を選ばない。質量は確率 1 で
    mud 類 [n_0, ∞) に入り、以後は単調非減少かつ注入が無限回起きるため
    確率 1 で発散する(mud 類は almost-sure の罠である)。
(b) ρ-方針: ρ > ρ_c = λ / p_r なら、V(n) = n を Lyapunov として一段の
    期待ドリフトは λ − ρ · p_r < 0(n >= 1)であり(Foster–Lyapunov 条件)、
    鎖は正再帰。増分有界と一様負ドリフトから定常分布の平均は有限
    (幾何 tail の標準論法)。
(c) ρ < ρ_c では一様正ドリフト λ − ρ · p_r > 0 と増分有界により質量は
    確率 1 で発散する。ρ_c = λ / p_r が相境界であり、λ < p_r の仮定の下で
    両相(発散 / 有界)はともに非空である(D6 の標準形)。
```

証明の読み: (a) 選択時 n >= n_0 で c(n) >= c(n_0) > c_f だから貪欲は機能を選び、
以後の増分は I >= 0 で単調非減少。注入は独立に確率 λ で起き続けるため
(Borel–Cantelli)、質量は確率 1 で発散する。n < n_0 の帯では、一段で +1 になる
確率は λ(1 − p_r) > 0(注入かつ修復失敗)であり、これが n_0 回連続する
確率 (λ(1 − p_r))^{n_0} > 0 の事象が独立に無限回試行されるため、
[n_0, ∞) 到達は確率 1。(b) 期待ドリフト計算と Foster–Lyapunov。
(c) は一様正ドリフトの標準論法((a) からは従わないことに注意)。

量化子の語法: (a)(b)(c) はいずれも分布主張(almost sure / 定常平均)である。
全経路量化(must)はこの模型では成立しない — 注入が一度も起きない軌道は
挙動空間の許容軌道として存在する。may / must を使う場合は分布主張と区別して明記する。

#### 原則 40.3 場の設計

アーキテクチャ設計・統治設計とは、内生コスト c(n) の形と c_f との交点 n_0、
および実効修復比率 ρ を動かすことである(旧 attractor engineering の転生)。
「良い設計は正しい変更を最小抵抗経路にする」の模型内の実体は、
n_0 を大きく(修復が安いまま保たれる帯を広く)、ρ_c を小さく(需要に対して
修復が効く)保つことである。

### 41. ゲージ合同

#### 定義 41.1 ゲージ関係

semantic 零の力(refactor; 定義 11.3)の有限列で**相互に到達できる**(両方向)
配置を関係 `≈` で結ぶ(相互到達)。refactor は一般に可逆でないため、
一方向到達は前順序にとどまる。相互到達と対称推移閉包(zigzag)は一般に異なる関係であり、
どちらを採るかは宣言事項である — 本文は相互到達を既定とする。

#### 定義 41.2 両立性

`≈` が次を満たすとき、両立する congruence / bisimulation と呼ぶ。

```text
(i)   遷移両立: Φ ≈ Φ′ なら、Φ からの各許容 step に対し、Φ′ からの許容 step が
      存在して行き先が again ≈ で対応する(双模倣)
(ii)  cost 両立: cost は ≈ 不変
(iii) 観測両立: 計器読み(pairing)は ≈ 不変
(iv)  衝突両立: 衝突類・residue の読みは ≈ 不変
(v)   ギャップ両立: selected ギャップ汎函数 Φ_M は ≈ 不変
      (目標集合 {Φ_M = 0} の飽和。値函数の降下に必要)
```

#### 定理 41.3 商への降下 [Certified bounded inference]

両立する `≈` の下で、値函数 V・到達集合・衝突類は商系 `𝔗(𝔇, Π)/≈` の上に
well-defined に降下する。

証明の読み: 代表の取り替えに対する不変性が (i)–(v) そのものであり、
商での定義が代表の選び方に依らない((v) が目標集合の飽和を与え、
V の降下を可能にする)。標準的な商力学系の議論である。

「リファクタは(≈ が両立する限りで)可能性を変えない」の正確な形であり、
無条件の主張ではない: (i)–(v) は selected semantic profile・cost・計器に相対化された
検証事項である(実例は付録 D.11)。変分構造を定義するまで Noether を名乗らない(付録 C)。

### 42. 第VI部の結論

```text
設定   = ギャップ汎函数と追跡模型(§36)
T0     = Model A: 究極有界 / Model B: 線形成長(§37)
収支   = ΔΦ = In − Out + Res、refactor 項 = 0。適合性が内容(§38)
方針   = 近視眼 / 先読み / Bellman。Φ–V 上下界(§39)
吸収域 = 内生コストの下で ρ_c = λ / p_r が相境界(§40)
ゲージ = 両立する ≈ の下で商へ降下(§41)
```

第VI部は、宣言されていない mass 帰属・模型データ・両立性について主張しない。
目標が動く regime(law-universe transport)と、それに伴うギャップ輸送補題
(目標移動時のギャップ値の輸送; AAT 第VIII部 定義6.1 Witness Perturbation Distance・
定理候補6.5 が anchor)は P4 以降の対象である。

## 第VII部 変形と可能性(予告; P4)

第VII部は「この設計からどんな進化が可能か」を、予測ではなく現在の幾何の変形理論として読む。

```text
変形空間(AAT の Ext 次数規約: automorphism = Ext^{-1}, 一次変形 = Ext^0, 拡張障害 = Ext^1)
剛性と骨化(有効変形空間の単調減少)
モジュライ(分解 stack の族の中の path)
```

AAT アンカーは第VI部 §3(cotangent / tangent complex)・§6(Square-Zero Lifting、
Kuranishi; certified)。
ただし AAT の変形理論は固定 geometry 内の変形であり、アーキテクチャ配置そのもの・
law 構造そのものの変形理論は SFT 側の新規数学である(research loop の対象)。
旧 ForecastCone の「可能性」side の後継はこの部に住む。
(節番号 43–46 は本部の完全化時に使う予約である。)

## 第VIII部 開発の統計力学(予告; P4)

第VIII部は力のアンサンブル(delegator ごとの生成核 + 相関パラメータ)を扱う。
すべて Model theorem / Empirical hypothesis の規律下で書く。

```text
アーキテクチャエントロピー(measurement packet 繊維計数; 比較可能性条件つき)
第二法則(実体は計数補題; 統治相の非空性を併示)
regime 境界(誘導連鎖の再帰 / 推移境界。「相転移」は n → ∞ の族でのみ)
throughput(台の重なり分布と review 帯域からの導出。安全並列度の上界)
diversity premium(混成 delegator 群の優位; 台帳 H4)
```

(節番号 47–50 は本部の完全化時に使う予約である。)

## 第IX部 観測と制御(Observation and Control)

問い(この部の採否規律): 観測は pairing として、統治は観測に基づく方針の変換として立ち、
沈黙軸の危険を仮定に顕在化した安定化が、模型非自明な定理として述べられるか。

### 51. 計器と可観測性

#### 定義 51.1 計器族と読み

計器族 `𝔐_t` は、序 §3 の成分 𝔐 の実体であり、本節が完全化する:
各時点 t に、読み対象の類 `α`(衝突類・残差類・質量読みの差)への宣言された
pairing `⟨m, α⟩` の有限族を与える(受け皿は `E` の選択。付録 D は定義 15.1 (c) 型)。
時間添字は計器族が時間発展することを表し、その更新は定義 53.2 の作用である。
軌道に沿った読みは列 `y_t = (⟨m, ·⟩)_{m ∈ 𝔐_t}` である。
観測写像(どの類をどの時点でどの受け皿で読むか)は模型データとして宣言する。
AAT 側 anchor は第VII部 §5 の period family(定義)。

#### 定義 51.2 沈黙部分空間

```text
Ann(𝔐) := { α : すべての m ∈ 𝔐 で ⟨m, α⟩ = 0 }(沈黙軸の全体)
```

#### 命題 51.3 可観測性 = annihilator 消滅 [Certified bounded inference]

abelian regime(pairing の α 側の加法性)で次は同値である。

```text
(i)   計器族は類を分離する(α ≠ 0 なら、ある m で ⟨m, α⟩ ≠ 0)
(ii)  Ann(𝔐) = 0
(iii) α ↦ (⟨m, α⟩)_m は単射
```

証明の読み: α 側の加法性の下での言い換えである。内容は同値性そのものではなく、
可観測性を「pairing の非退化」という代数条件へ固定する点にある
(有限 regime では (ii) が有限検査可能になる — 有限性は同値にではなく検査に効く)。
命題 31.3(レビューの盲点)は、この条件の否定側(Ann ≠ 0)の帰結である。

#### 原則 51.4 沈黙規律

`Ann(𝔐) ≠ 0` の軸について本文は語らない(D2)。ただし §54 は、
「語らない軸が測定軸へ結合する」という危険そのものを仮定 (2) として顕在化する。

### 52. 可制御性

#### 定義 52.1 閉ループ生成子と統治された到達集合

controller(定義 53.1)を固定し、拡大状態(frontier × 観測履歴)の上の一段対応

```text
T_C : (frontier, y_0..y_t) ⇒ P(次の拡大状態)
      各段、Π_t = C(y_0..y_t) を適用した生成子 T_{Π_t} の一段と、観測の追記
```

を閉ループ生成子と呼び、その許容軌道の全体を `𝔗(𝔇, C)` と書く。
閉ループ軌道は一般にどの固定 Π の挙動空間 `𝔗(𝔇, Π)` にも属さない
(方針が時変のため)。統治された到達集合とは、`𝔗(𝔇, C)` の軌道が到達できる
配置の集合であり、可制御性と定理 54.2 の仮定 (3) の量化はすべてこの集合の上にある。

### 53. Controller

#### 定義 53.1 Controller(supervisor)

```text
C : 観測列 (y_0, ..., y_t) ↦ (方針 Π_t, 計器族 𝔐_{t+1})
    (選好・許容の変更と、計器族の更新の対)
```

controller は生成子 `T_Π` の Π を観測依存・時変にし、あわせて計器族を更新する
作用として読む(閉ループ生成子は定義 52.1)。

#### 定義 53.2 計器族の拡大は controller の作用である

計器の追加・削除(`𝔐_t -> 𝔐_{t+1}`)も controller の作用の一型である
(旧 InstrumentingIntervention の転生; 付録 F)。統治の設計変数は方針だけでなく
計器族である。

#### 定義 53.3 incident と rollback

incident = 非計画の計器読み値(運用側計器の発火)。rollback = revert 力の適用
(selected forward transition; 定義 7.2)。incident 対応は
「計器族の拡大 + repair 力 + 台帳更新」の合成として読む(解釈境界: 付録 A)。

#### 原則 53.4 参照枠は輸入しない

離散事象系の監督制御(Ramadge–Wonham: 可制御事象・可観測事象・supervisor 合成)は
本部の参照枠だが、その定理は輸入しない。接続は付録 E の三行書式に置く。

### 54. 安定化

#### 定義 54.1 閉ループ追跡模型

定義 36.2 の追跡模型に観測と controller を加える(すべて模型データ):

```text
観測:     ê_t = e_t + η_t(ギャップの推定)
顕在注入: v_t <= v_max(測定軸に見える注入)
隠れ注入: h_t <= h_max(沈黙軸から測定軸への結合による注入)
controller: ê_t > θ のとき修復を発動する(しきい値方針)

閉ループ遷移公理(場合分けの上側公理):
  発動段:   e_{t+1} <= max(0, e_t − δ_t) + v_t + h_t(δ_t >= r_min は仮定 (3))
  非発動段: e_{t+1} <= e_t + v_t + h_t
反例側(D6)は、この上側公理を等式で実現する実例として宣言する(付録 D.14)。
```

#### 定理 54.2 フィードバック安定化 [Model theorem]

仮定:

```text
(1) Φ-detectability:      |η_t| <= ε(推定誤差の一様上界)
(2) 沈黙軸の有界結合:      h_t <= h_max
(3) 一様修復可制御性:      統治された到達集合(定義 52.1)の各配置で、
                          発動時に δ_t >= r_min の修復が選択できる
(4) 目標速度上界:          v_t <= v_max
```

注記: 骨格ノートの旗艦 T8 の第 5 点「計器の源独立性」は、(1) の一様性を実務で
成立させる条件であり(計器が力と共通の delegator を経由すると ε の一様性が
破れ得る; §30)、定理の仮定としては (1) に吸収される。
骨格 §6 は T8 を Certified bounded 目標としたが、P3 はスカラー閉ループ模型上の
Model theorem として実装した。certified 化(挙動空間上の量化の固定)は後続とする。

結論:

```text
r_min > v_max + h_max なら、閉ループ軌道の e_t は究極有界であり、
帯の大きさは θ + ε + v_max + h_max の程度である。
漸近安定(e_t -> 0)は主張しない。
```

証明の読み: e_t > θ + ε なら ê_t > θ で修復が発動し、一段の純変化は
高々 −(r_min − v_max − h_max) < 0。したがって帯 [0, θ + ε] の超過は有限段で解消され、
帯内(および ê_t の誤差による誤発動域)からの一段の増分は v_max + h_max で抑えられる
(誤発動段は減少するのでなお良い)。究極の帯は θ + ε + v_max + h_max で抑えられる。
定理 37.1(Tracking Model A)の閉ループ版である。

模型非自明性(D6): (2) を外す(h_max >= r_min − v_max に取る)と、沈黙軸に蓄積した
負債が測定軸へ結合して発散する反例が存在する(付録 D.14)。両相は非空である。

#### 原則 54.3 安定化は観測の関数である

同じ源・同じ方針でも、計器族が貧しければ (1)(2) が破れ、安定化は失敗する。
可観測性(命題 51.3)と安定化(定理 54.2)の間に、統治の設計問題が住む。

### 55. 第IX部の結論

```text
観測   = pairing(可観測性 = annihilator 消滅; 命題 51.3)
可制御 = controller 下の到達集合(挙動空間上の量化)
統治   = supervisor(方針の時変化)+ 計器族の拡大 + incident 対応
安定化 = 5 仮定の下の究極有界(定理 54.2)。漸近安定は主張しない
```

第IX部は、宣言されていない pairing・計器族・controller について主張しない。

## 第X部 寿命と長期挙動(Lifecycle and the Long Run)

問い(この部の採否規律): 系の老いと死は、予算と有効力の言葉で、吸収性の定理として
述べられるか。migration は開発系の射に沿った場の輸送として型を持つか。

### 56. 軌道の regime

#### 定義 56.1 regime 分類

選ばれた指標(質量水準、予算内有効力の集合、修復コストの水準)による軌道の区間分類を
regime と呼ぶ。

```text
誕生(配置の初期化)
-> 成長(有効力が豊富。質量の変動が大きい)
-> 安定(質量有界帯。定理 40.2 (b) の正再帰相)
-> 骨化(予算内有効力の集合の単調縮小)
-> 終焉(枯渇; 定義 57.1)
```

分類は selected 指標に相対的であり、regime の系列そのものは記述であって定理ではない。

#### 原則 56.2 骨化の本命は変形理論である

「有効力の縮小」の内在的な読み(変形空間の単調減少、剛性)は第VII部(P4)の対象である。
本部は、力と予算の言葉による外在的な読みだけを使う。

### 57. 終焉

#### 定義 57.1 有効力の枯渇(P3 版)

予算 `b` の下で、配置 Φ が枯渇しているとは:

```text
{ 許容力 f : cost(f) <= b、かつ f の適用が selected ギャップ汎函数を
  strict に減らす、または selected 目標方向成分が非零 } = ∅
```

「strict に減らす」の様相は realizable で読む: 選ばれた模型の下で strict 減少を
実現し得ること(確率模型では成功枝の存在。確実性を要求すると p_r < 1 の模型で
許容力が恒真的に空になり、定義が死ぬ)。
U 定数 regime(P1–P3)では目標方向項は凍結されており、条件は第一項だけで読む。
非改善の力(feature・refactor)は枯渇状態でも存在し得るため、
単純な「力の不存在」では死を定義できない(骨格の恒偽回避の継承)。
変形理論による内在版(Ext 類の言葉)は第VII部(P4)で精密化する。

#### 定理 57.2 終焉の吸収性 [Model theorem]

模型公理:

```text
(i)   コストは質量のみの単調関数である(定義 40.1 の自己相互作用の公理)
(ii)  selected ギャップ汎函数の strict 減少は repair だけが実現し、
      その他の力は質量を減らさない
(iii) 予算 b は外生で固定。許容軌道とは、各段の力のコストが b 以下の軌道である
(iv)  可用性: repair は常に許容であり、唯一の障害はコストである
      (この公理の下で、枯渇 ⇔ c(n) > b)
```

結論: 枯渇した(公理 (iv) により c(n) > b の)配置から出発する許容軌道は、
すべて枯渇状態に留まる(枯渇は吸収的である)。

証明の読み: 予算内では repair が選べない((iv) と c(n) > b)ので、各段は
非 repair の力であり、(ii) より質量は非減少、(i) より修復コストは非減少。
したがって「c > b」は軌道に沿って保存される。(iv) を外すと、repair の適用可能性が
配置に依存する模型で、質量を変えない力が repair を可能にして脱枯渇する反例が作れる
— 吸収性はコスト証人つき枯渇の性質である。

模型非自明性(D6): 予算を b′ > c(n) に引き上げれば修復が許容になり脱出できる。
枯渇は予算相対の状態であり、吸収相と脱出可能相は予算パラメータでともに非空である。

系: 終焉は失敗ではなく、予算に相対的な状態である。修復・migration・削除の選択
(lifecycle 判断)は、この定理の外側にある人間の選択である(非主張; 序 §5)。

#### 定義 57.3 終焉判定の入力

判定に使う質量・コストの読みには、runtime 側計器(定義 53.3 の incident を含む)を
含める(旧 EndOfLifeDecision の runtime risk 軸の継承; 付録 F)。

### 58. migration・継承・供給

#### 定義 58.1 開発系の射

```text
開発系の射 𝔇 -> 𝔇′ :=
  トレース functor + fiber の部分 context 対応 + 源対応 + 計器対応の整合的な組
  (すべて選択データ。対応の外の context・計器は輸送されない)
Π は対応させない — 方針は各系に固有の運動法則であり、射は運動学のみを写す。
```

系の置換(継承)は、この射で型を持つ: 継承 = 後継系への開発系の射と、
その射に沿った場・記憶の輸送である。

#### 定義 58.2 migration

migration = 開発系の射に沿った場の輸送(base change)。輸送された law データの
貼り合わせと残差は第III部の三段 filtration で診断する。semantic repair の descent
(AAT 第X部 SAGA; certified)が AAT 側の anchor である。
migration の「成功」は宣言された診断の通過であり、無条件の同値ではない。
対応の外に落ちた context(廃止面)は沈黙として扱い、残タスク化しない。

#### 定義 58.3 供給と trust boundary

供給 = 他の開発系が生成した力の輸入(依存の更新)。輸入は供給元からの
開発系の(部分)射 𝔇′ -> 𝔇 に沿った base change として読む。輸入された力は
trust boundary の型(どの delegator・どの契約に相対化して受け入れるか)だけを持つ。
悪意の意味論は非主張である(序 §5)。

### 59. 第X部の結論

```text
regime    = 選ばれた指標による区間分類(誕生 -> 成長 -> 安定 -> 骨化 -> 終焉)
終焉      = 予算内有効力の枯渇(定義 57.1)+ 吸収性(定理 57.2; 予算相対)
migration = 開発系の射に沿った場の輸送(診断は第III部と SAGA)
継承      = 後継系への射と場・記憶の輸送
供給      = 外部力の輸入(𝔇′ -> 𝔇 の base change 読み。trust boundary の型のみ)
```

第X部は、宣言されていない予算・指標・射について主張しない。
変形理論による精密化(骨化・進化容量)は第VII部(P4)の対象である。

## 付録 A 解釈境界(Interpretation Boundary)

本文はモデル化された開発系についての純数学である。実在物との対応は本表を通じてのみ読む。
本文の定義・定理はこの表に依存しない(境界の所在を示す指示は除く; D4)。

| 実在物 | 理論対象 |
| --- | --- |
| リポジトリ状態 | selected Atom family `A_t` と fiber `𝔛_t`(観測は ArchMap 側の artifact contract) |
| commit / PR | 力(ForceSchema + AppliedForce)。提案された力と適用された力を区別する |
| branch / merge | span / selected cocone / cover(base 選択はデータ) |
| merge queue の投機ビルド | 曲率計器(両順序輸送の比較; 台帳 H2) |
| squash / rebase / force-push | トレース商 functor(定義 7.6)。witness は書き換え前に計算する |
| org chart / CODEOWNERS | 組織圏 + ownership 対応(communication cover は別途観測; 第IV部) |
| model / prompt / policy | delegator(相関の担い手; 第IV部) |
| PRD / design doc / issue | 目標場(lawful locus の移動; P1 では凍結) |
| CI / テスト | 計器(period pairing; 第IX部) |
| deploy / rollback | selected transition |
| incident | 非計画の計器読み値(第IX部) |
| レビュー | 計器評価 + 降下データの選択(第IV部) |
| AI agent | participant(delegator 相関を持つ源) |
| エンジニア / アーキテクト / デザイナー / PdM / レビュアー | 役割プロファイル(定義 29.3)。主に生成する力の型がそれぞれ 点 / 法則・コスト / semantic / 目標編集 / 選択 |
| 依存 bump / 外部ライブラリ更新 | 他の開発系が生成した力の輸入(第X部) |

計器契約(実在物側で本理論の定理を使うための義務):

```text
(1) closure の過大近似: 定理の「素」仮定に使う closure 割り当ては、
    作用痕(定義 11.4)の証明された過大近似でなければならない(原則 22.1)。
    実在物側の推定では selected dependency closure(import / schema / config
    依存の閉包)を cl の供給源として使う。
    過小近似の cl で「素だから安全」と結論する使い方は unsound である。

(2) トレースの源: 𝒯_E の構成素材は、可変な ref graph ではなく
    不変イベントログ(PR / review / merge イベント)を推奨する。

(3) 書き換え前計算: 曲率・残差・衝突類の witness は、
    履歴書き換え(squash / rebase)の前の trace 上で計算する(§24)。
```

## 付録 B 主張の梯子と Empirical hypothesis 台帳

主張ラベルの梯子は序 §1 の通り。Empirical hypothesis は次の必須列を持つ(D7)。
profile の事後再選択は反証の回避として扱い、別仮説として行を分ける。

| ID | 仮説 | 事前固定 profile | 棄却条件 | profile 安定性 | status |
| --- | --- | --- | --- | --- | --- |
| H1 | 三層衝突の分離: テキスト衝突なしで auto-merge した変更対のうち、selected dependency closure の重なりを持つものは、持たない対照群より短期 revert / hotfix 率が有意に高く、テキスト重なり単独ではこれを予測しない | closure 定義(import / schema / config 依存)、観測窓(k 日)、対象母集団を検証開始前に固定 | closure 重なり群と対照群の revert / hotfix 率に有意差がない(または符号が逆) | 宣言された closure 定義族に亘る成立を要求 | 未検証 |
| H2 | 曲率計器: 両順序の投機適用による δ(f,g) の witness は、diff サイズ基準を超えて post-merge 欠陥を予測する | 投機適用の手続き(merge queue 両順序ビルド)、欠陥の定義、比較基準(diff サイズ回帰)を固定 | δ witness の追加予測力が diff サイズ基準に対して有意でない | 単一 CI 構成でまず検証、複数構成へ拡張 | 未検証 |
| H3 | レビュー負荷の regime 遷移: 負荷閾値超過期間は、承認レート維持のままラバースタンプ徴候(大 diff の承認遅延減・コメント零)を示し、遅延して障害質量 proxy が上昇する | 負荷指標、徴候の operational 定義、障害質量 proxy、遅延窓を固定 | 閾値超過期間に徴候が現れない、または proxy 上昇と無相関 | 組織規模の異なる 2 母集団での再現を要求 | 未検証 |
| H4 | diversity premium: 同能力の混成 delegator 群は、単一 delegator 群より hotspot 重なり衝突率が低い | 能力対等条件、hotspot 定義、衝突率の測り方を固定 | 混成群の衝突率が単一群以上 | モデル世代を跨ぐ再現を要求 | 未検証 |
| H5 | Lehman 継続変化: 生きた開発系では目標移動の下界 v_min は零にならない(定理 37.2 の前提が現実で持続的に満たされる) | 「生きた系」の operational 定義(利用・変更の下限)、v の proxy(要求流入率)を固定 | 生きた系で v proxy が持続的に零 | 複数ドメインでの成立を要求 | 未検証 |

SFT の Formal theorem / 定理候補が Lean proof obligation になるのは、
docs/aat の台帳(lean_theorem_index / proof_obligations)に対応行を置いた場合だけである(D5)。

## 付録 C 物理アナロジー辞書(3 列)

語が指す先が実在の数学的対象になることが「本物」の意味である。物理の定理は輸入しない。

| 語 | 指す数学的対象 | 区分 | 注意 |
| --- | --- | --- | --- |
| 場 | AAT site 上の層データ(場の配置) | 安全 | 場の方程式は輸入しない |
| 力 | ForceSchema / AppliedForce | 安全 | ニュートン力学の力ではない |
| 接続 | selected transport 規則の族 | 安全 | 正準接続は存在しない(選択データ) |
| 力の曲率 | commute 二辺形の比較残差 | 安全 | AAT 第VIII部 定義8.9(スペクトル曲率 reading)とは別対象 |
| ホロノミー | ダイヤモンドの平行輸送比較残差 | 安全 | 逆射不要の定義。physical gauge 場は輸入しない |
| ゲージ変換 | semantic 射影が零の力(refactor) | 条件付き | 可逆な部分に限っても群でなく groupoid であり、一般には可逆性も落ちる(高々圏)。gauge 性は selected semantic profile の関数 |
| 目標場 | lawful locus を動かす目標 | 条件付き | 「ポテンシャル」は gen の応答公理(ギャップ単調性)を置いた模型のみ |
| 散逸 / Lyapunov | 評価汎函数と方針の適合 | 条件付き | 有限系の停止性は自明。内容は汎函数と力の類型の適合(P2 の質量収支則) |
| エントロピー | measurement packet 繊維計数(比較可能性条件つき) | 条件付き | 有限決定系では減少し得る(第VIII部) |
| regime 境界 | 誘導連鎖の再帰 / 推移境界 | 条件付き | 「相転移」は n → ∞ の族の sharp threshold のみ。有限系に非解析性はない |
| 輸入禁止 | — | — | Bianchi 恒等式、Jacobi 場・測地線偏差、gradient flow、臨界指数・普遍性、エネルギー保存則。「測地線」も metric enrichment から length minimizer を実構成するまでは保留語 |

## 付録 D 正準有限実例(Canonical Finite Example)

小さな開発系を一つ固定し、本文の中心概念をすべてその上で手計算する。
D.1–D.8 は P1 受け入れ契約(D.8)の、D.9–D.13 は P2 必置照合(D.13)の、
D.14–D.16 は P3 必置照合(D.16)の witness である。

### D.1 開発系の有限 record

```text
𝔇 = (𝒯, 𝔛, 𝔖, Π, M) を次で与える。

𝒯 : 頂点 {B, A, C, M}、辺 a : B->A, c : B->C, p_A : A->M, p_C : C->M(定義 D.2)
𝔛 : 定数 fiber(context poset は D.3。輸送 u_e はすべて恒等)
𝔖 : 参加者 {team_P, team_Y}。own(team_P) = {Pricing, UI}, own(team_Y) = {Payment}
    (own は P1 の計算では使わず、D.9 のバス係数・レビューの実例で使用する)。
    gen(team_P) = {s_P, s_U}, gen(team_Y) = {s_Y}(D.4)。delegator なし。
Π : accept-all(生成された力をすべて選択; 単位コスト)
𝔐 : 計器族 {m_test}(contract rounding test; D.7)
E : 曲率の受け皿 = 定義 15.1 (c)(共有 context 上の law 係数の直接差)。
    係数・調整群は D.3 / D.5、base = B(criss-cross 変種は D.6)
```

記号注記: 本例のマージ頂点 M と開発系の計測成分 𝔐 は別の対象である。

生成模型は trace と独立に上のように宣言されているため、定理 9.4 は内容を持つ:
以下の trace の各辺には生成・選択・輸送・更新の witness が存在し
(マージ辺の witness は親組 (Φ_A, Φ_C) と base B を引数に取る)、
この trace は T_Π の解軌道である。

### D.2 トレース site と生成位相

射は恒等のほか:

```text
a : B->A,  c : B->C,  p_A : A->M,  p_C : C->M,
p_A∘a : B->M,  p_C∘c : B->M(B から M への二つの異なる射 = 二つの経路)
```

宣言被覆は {p_A, p_C}(base 選択 = B)。生成位相の被覆 sieve を列挙する:

```text
M 上: 生成 sieve S_M = {p_A, p_C, p_A∘a, p_C∘c}(M への非恒等射全体)と極大 sieve。
A, B, C 上: 極大 sieve のみ。

閉包の確認:
  引き戻し: S_M を p_A に沿って引き戻すと {h | p_A∘h ∈ S_M} = A 上の極大 sieve。
            p_A∘a に沿えば B 上の極大 sieve。いずれも被覆(公理 (i))。
  合成:     S_M の各射の domain に極大 sieve を選んでも S_M 自身が生成される。
  飽和:     S_M を含む真上位の sieve は極大 sieve のみで、これは (i) により被覆である。
```

有限 DAG 上で定義 7.3 の閉包が有限的に閉じることの実例である。

### D.3 fiber と場の配置

fiber の context poset(全時点で共通):

```text
Contract <= Pricing,  Contract <= Payment,  UI(独立)
```

law データ係数(第III部 段階1 用の selected abelian 係数):

```text
F(Pricing) = F(Payment) = F(Contract) = Z/2 = {0 = floor, 1 = half-even}
F(UI) = 0、restriction はすべて恒等(Contract へ向けて)

law algebra(段階2 用; 配置の成分として宣言):
  R = k[x, y, z](x = 「discount 適用済み」witness atom、y, z は補助 witness)
  witness ideal 対: I = (xy)(L1: discount 冪等性)、J = (xz)(L2: rounding 安定性)
```

B での配置: rounding セクション未選択(law データは基底値 0 = floor を仮置き)。

### D.4 力: schema・applied・commute(受け入れ契約 3)

```text
s_P := (W = {Pricing}, C = {Payment, UI},     φ = 「Pricing の rounding := 0」,
        dom = 自明, τ = 点(law データ成分))
s_Y := (W = {Payment}, C = {Pricing, UI},     φ = 「Payment の rounding := 1」,
        dom = 自明, τ = 点(law データ成分))
s_U := (W = {UI},      C = {Pricing, Payment}, φ = 「UI 文言変更」, dom = 自明, τ = 点)

closure 割り当て(選択データ; 定義 11.4、原則 22.1 の契約対象):
  cl(s_P) = {Pricing, Contract}, cl(s_Y) = {Payment, Contract}, cl(s_U) = {UI}
({W, C} は selected cover をなす。Contract は Pricing / Payment 経由で被覆に含まれる)
```

applied: `f_P = (a, s_P, id, witness)`、`f_Y = (c, s_Y, id, witness)`。

commute の実例:

```text
(s_P, s_U): cl が素(定理 14.3 の仮定成立)
  => commute 定義済み・輸送自明・両順序の合成が一致。

(s_P, s_Y): file 水準の台 {Pricing} と {Payment} は素だが、
  cl は Contract で重なる => 定理 14.3 は適用できない。
  presentation 水準の合成は両順序とも定義されるが、law データ水準の
  二辺形比較は Contract 上で 0 と 1 に分かれ、δ(s_P, s_Y) = 1 ∈ F(Contract)。
  台の過大近似契約(原則 22.1)が「file 台の素性では足りない」ことの実例である。
```

### D.5 ダイヤモンドと三段 filtration(受け入れ契約 4)

ダイヤモンド `B -> A -> M, B -> C -> M`(cover {p_A, p_C}、base B)。

段階0(台): file 水準の編集は素なので、宣言された融合手続きの結果は valid。通過。

段階1(法則の Čech H¹):

```text
輸送された law セクション: A 側は Contract 上 0(floor)、C 側は 1(half-even)。
mismatch: m = 0 − 1 = 1 ∈ F(B での overlap) = Z/2。
調整群(selected): G_A = G_C = 0(各 branch のテストが rounding を固定している)。
衝突類: [m] ∈ Z/2 / 0 = Z/2, [m] = 1 ≠ 0。

=> テキストは貼れたが、許された調整の範囲で law データは貼れない(法則衝突)。
   これは同時に、B の law セクションを二経路で M へ輸送した比較残差、
   すなわちダイヤモンドホロノミー(定義 16.1)の非零実例である:
   merge residue = 段階1 の衝突類。

参考: G_A = Z/2(A 側の調整を許す)を選ぶと [m] = 0 になる。
解決(rounding := 1 に統一する repair force)は、調整群の外の
明示的な貼り合わせの選択として記録される — 解決は選択である(§19)。
```

段階2(導来の Tor)。解決後の `𝔛_M` 上で、D.3 で配置の law algebra 成分として
宣言した R = k[x, y, z] と law 対 (I, J) = ((xy), (xz)) を読む。

```text
L1・L2 の witness ideal データは両 branch で同一に輸送される
(overlap 上の mismatch = 0、調整群自明)。この law 対について段階1 は
[m] = 0 で通過し、以下の段階2 だけが障害を出す。

古典交叉: V(xy) ∩ V(xz) は集合としては貼れている。
導来交叉: Tor_1^R(R/I, R/J) = (I ∩ J) / (I·J) = (xyz) / (x²yz) ≠ 0
(xyz は x²yz の倍数でないため)。

=> 二つの law は共有 witness 因子 x を通じて非横断的に交わる。
   古典的には貼れたが、導来交叉が衝突を記憶している(導来衝突)。
   AAT 第V部 定義4.1・命題5.5(monomial conflict calculation)・
   例5.6(shared witness factor)・定理6.1 の機械の実例化である。

対照(横断的な対): I = (xy), J′ = (zw) ⊂ k[x, y, z, w] なら
I ∩ J′ = (xyzw) = I·J′、したがって Tor_1 = 0(段階2 通過)。
```

同じ実例の上で、段階1 の障害(Čech H¹ の非零類)と段階2 の障害(Tor の非零)が
別の水準・別の機械・別の解決を持つことが見える。これが定理 20.5 (ii) の witness である。

### D.6 criss-cross 変種: base はデータである(原則 7.4)

頂点 {B1, B2, A, C, M}、辺 B1->A, B1->C, B2->A, B2->C, A->M, C->M。
B1 と B2 はともに A, C の共通祖先であり、標準的な base は存在しない。

```text
base = B2(rounding 契約が既に固定された時点)を選ぶと:
  overlap 係数 = Z/2、調整群 0 => 衝突類 [1] ≠ 0(D.5 と同じ)。

base = B1(rounding 契約の導入前。F_{B1}(overlap) = 0)を選ぶと:
  mismatch の受け皿が自明群 => 衝突類 = 0。

同じ branch 対でも、selected base によって診断は非零にも零にもなる。
診断は evolution profile E に相対的である(D2)。
ただし base = B1 は原則 22.2 の base 契約に違反する選択である
(共有 law restriction 先 Contract を overlap が過小近似する)。
その下での「衝突類 = 0」は unsound な診断の実例として読む。
契約を満たす base の中での選択の余地(criss-cross)と、
契約違反による見かけの通過は、区別して扱う。
```

### D.7 計器 pairing と T0 の数値例

計器 pairing(D1′ の使用強制の witness):

```text
m_test = contract rounding test。pairing ⟨m_test, [m]⟩ := [m] の評価 = 1 ≠ 0
=> 計器族 {m_test} は段階1 の衝突類を検出する。
計器族が空なら同じ類は検出されない(沈黙軸)。検出は pairing の非退化性の問題である。
```

T0(定理 37.1 / 37.2)の数値例:

```text
Model A: r_min = 3, v_max = 1, e_0 = 10。
  e の上界列: 10 -> 8 -> 6 -> 4 -> 2 -> 1 -> 1 -> ...
  到達時間の評価 ceil((10 − 3)/(3 − 1)) + 1 = 5、以後 e_t <= v_max = 1。
Model B: r_max = 1, v_min = 2(ε = 1), e_0 = 0。
  e_t >= t。どんな方針でもギャップは線形に成長する。
```

### D.8 P1 受け入れ契約の照合

```text
1. 開発系の有限 record が書ける            -> D.1
2. trace site + merge cover + base の有限例 -> D.2(+ criss-cross D.6)
3. schema / applied / commute / residue     -> D.4(commute)、D.5(residue = 段階1 類)
4. Čech H¹ と Tor の違いが同一実例上で見える -> D.5(段階1 = Z/2 の類、段階2 = (xyz)/(x²yz))
```

### D.9 組織の実例: 相関・バス係数・レビューの盲点(第IV部)

𝔖 を拡張する: delegator `d`(共有のコーディング規範・model)、AI participant `a_1, a_2`
(delegation 射 `a_i -> d`)。

```text
相関(定義 30.1): gen(a_1), gen(a_2) はともに d 由来の生成様式を持ち、
  同じ hotspot(Pricing)に台を持つ力を生成する。二つの力は相関し、
  台の重なり確率は独立積から外れる(第III部 §25 の独立性注意の実例)。

バス係数(定義 28.3): 可視性を own と一致させると、Payment を可視に持つのは
  team_Y のみ(バス係数 1)。team_Y の離脱はバス事象である。

レビューの盲点(命題 31.3): D.5 の解決(rounding := 1 への統一)は
  降下データの選択(定義 31.1 (ii))である。計器族 {m_test} は
  [m] = 1 を検出する(D.7)ので、選択は [m] に依存できた。
  計器族を空にすると、[m] だけ異なる二候補への選択は一致する
  (α-盲目 = ラバースタンプの形式的実例)。
```

### D.10 収支・吸収域・CLF の数値例(第VI部)

収支分解(定義 38.1)の bookkeeping を D.5 のダイヤモンドで読む
(mass = 段階1 衝突類の質量読み |[m]| ∈ {0, 1}):

```text
B(Φ = 0)
  -> 分岐と二つの力(feature 的注入: 各 branch 内では衝突なし、In = 0)
  -> マージ段: Res = +1([m] = 1)
  -> repair(統一の選択): Out = 1
  -> 解決後 Φ = 0。ΔΦ 合計 = 0 = In − Out + Res = 0 − 1 + 1 ✓
refactor(D.11 の rename)は ΔΦ = 0(型公理の実例)。
単独 feature 段の増加例: 新しい未検査の rounding context を導入する feature 力は
In = +1(ΔΦ = +1)。マージ段の増加例は上の Res = +1(帰属は Res であって In ではない)。
```

内生コスト吸収域(定理 40.2)の数値例:

```text
λ = 1/2, p_r = 3/4(λ < p_r ✓), c_0 = 1(c(n) = 1 + n), c_f = 3
n_0 = min{ n : 1 + n > 3 } = 3、ρ_c = λ / p_r = 2/3、mud 類 = [3, ∞)

貪欲: n < 3 では修復(c(n) <= 3 = c_f、同額は修復側)を選び、期待ドリフトは
  λ − p_r = −1/4 < 0。しかし一段で +1 になる確率は λ(1 − p_r) = 1/8 > 0 で、
  3 連続(確率 1/512)の試行が無限回あるため [3, ∞) 到達は確率 1。
  以後 c(n) >= 4 > 3 で修復を選ばず、質量は確率 1 で発散(almost-sure の罠)。
ρ = 0.8: 期待ドリフト <= 1/2 − 0.8 · 3/4 = −0.1 < 0 ⇒ 正再帰・平均質量有界。
ρ = 0.5: 期待ドリフト >= 1/2 − 0.5 · 3/4 = +0.125 ⇒ 確率 1 で発散
(相境界 ρ_c = 2/3 の両側が非空; D6)。
```

CLF(補題 39.3)の数値例。V は定義 39.2 の最短路値として評価する
(最良経路: 注入なし・修復全成功。確率模型の期待コストではない):
r_max = r_min = 1, c_min = 1、開始質量 n からの到達域で c_max = 1 + n。
補題 39.3 より n <= V(n) <= n(1 + n)。厳密値は
V(n) = Σ_{k=1..n} c(k) = n + n(n + 1)/2(例: V(10) = 65 ∈ [10, 110])。

近視眼と最適の乖離(原則 39.4)の 3 状態例:

```text
状態 x(Φ = 2)、y(Φ = 3)、z(Φ = 0)。許容 step: x -> y(migration 力)、y -> z。
x に repair 力は無い(修復不能構成)。
近視眼的散逸方針は x で停止する(Φ を上げる step を選ばない)。
Bellman は x -> y -> z で目標に到達する(一旦悪化して直す)。
```

### D.11 ゲージ合同の実例(第VI部)

rename refactor `ρ_n`: 名前 n を n′ へ(selected semantic profile = 観測可能な
rounding 挙動。名前は semantic 射影で消える)。

```text
両立の検証(定義 41.2):
  (i)  遷移両立: 各力の schema は名前に依らず適用可能(locality と dom の名前非依存)
  (ii) cost 両立: 単位コスト(D.1 の Π)は名前不変
  (iii) 観測両立: m_test は rounding 挙動だけを読む(名前不変)
  (iv) 衝突両立: [m] ∈ Z/2 の計算(D.5)は名前に現れない
  (v)  ギャップ両立: Φ_M(段階1 衝突類の質量読み)は名前に不変

定理 41.3 により、{Φ, ρ_n(Φ)} は商系の一点であり、
到達集合・[m]・V はその点の上で well-defined である。
定理 38.2 の refactor 不変 mass の実例でもある(ΔΦ = 0)。
```

### D.12 局所零曲率・大域非零残差の witness(定理 16.2 の証明)

トレース site を拡張する: 頂点 `E` と `M₃`、辺 `B -> E`、`A -> M₃`、`C -> M₃`、
`E -> M₃` を加え、admissible family `{A -> M₃, C -> M₃, E -> M₃}`(base 選択 = B)を
宣言する。対ごとの共有 context は互いに異なり、**三枝の三重共有 context は空**とする
(したがって nerve は中空三角形 ∂Δ² である。三重共有があれば nerve は Δ² となり
H¹ = 0、辺値 (0, 0, 1) は cocycle 条件を破る — 空性は構成データである):

```text
overlap(A, C) = K_AC, overlap(C, E) = K_CE, overlap(E, A) = K_EA(すべて別 context)
係数: 各 K 上の同定の取り替えを Z/2 で読む(名前 n / m の交換 = 1)

力の構成: A は K_EA 側の局所束縛だけを名前交換する refactor を含む。
比較同型(接続の選択): K_AC 上 = 0(恒等)、K_CE 上 = 0、K_EA 上 = 1(交換)

対ごとの曲率: 各対はそれぞれの比較同型で二辺形が閉じる(残差零)。
  ここでの「閉じる」は、各共有 context 上の受け皿 (c)(定義 15.1)での
  二辺形比較が、その辺の比較同型の下で一致することである。
  edge 値 (0, 0, 1) は各辺単独では常に閉じ方の witness である。

大域同定: branch ごとの大域的な付け替え g_A, g_C, g_E ∈ Z/2(調整 = coboundary)で
  edge 値を同時に消せるか:
    K_AC: g_A + g_C = 0,  K_CE: g_C + g_E = 0,  K_EA: g_E + g_A = 1
  三式の和は 0 = 1 となり解なし。

したがって [(0,0,1)] ≠ 0 ∈ H¹(三角形 nerve, Z/2) = Z/2。
対ごとの(局所)曲率はすべて零だが、三枝に整合する大域同定は存在しない。
```

これが定理 16.2 の有限反例 witness である。読みは「係数の同定系の monodromy」であり、
AAT 第VI部の monodromy・第IV部 §9 Boundary Holonomy Theorem(certified)の
SFT 実例化である。Lean 化は L3 の対象。

### D.13 P2 の必置照合

```text
第IV部 -> D.9(相関・バス係数・レビューの盲点の実例)
第VI部 -> D.10(収支 bookkeeping・吸収域の数値・CLF・近視眼と最適の乖離)
          D.11(ゲージ合同の両立検証)
          D.12(定理 16.2 の witness)
```

### D.14 可観測性と安定化の実例(第IX部)

可観測性(命題 51.3):

```text
類空間 A = Z/2(D.5 の段階1 衝突類)。
計器族 {m_test}: ⟨m_test, 1⟩ = 1 ≠ 0 ⇒ Ann = 0 ⇒ 分離(可観測)。
計器族 ∅:        Ann = Z/2 ≠ 0 ⇒ [m] は沈黙軸(命題 31.3 のレビュー盲点が発動する側)。
```

閉ループ安定化(定理 54.2)の数値:

```text
θ = 2, ε = 0, r_min = 3, v_max = 1, h_max = 1(r_min > v_max + h_max = 2 ✓)
e_0 = 10: e_t > θ の間は毎段発動し、純変化 <= −(r_min − v_max − h_max) = −1。
したがって遅くとも 8 段で帯(<= θ + ε = 2)に入る。
帯内では発動せず一段の跳ねは <= v_max + h_max = 2、超過すれば直ちに発動して戻る。
究極の帯は <= θ + ε + v_max + h_max = 4 である(究極有界)。

統治された到達集合(定義 52.1)の読み: この閉ループの到達集合は
帯 [0, θ + ε + v_max + h_max] = [0, 4] と初期超過分の下降路であり、
仮定 (3) はその各配置で修復が選択できることを言う。

ε > 0 の変種: θ = 2, ε = 1 では発動保証は e_t > 3 から。e_t = 2 で η_t = +1 の
誤発動が起き得るが、誤発動段は減少するだけで、究極の帯は
θ + ε + v_max + h_max = 5 で抑えられる(定理 54.2 の会計と一致)。

反例(D6; 仮定 (2) を外す): h_t = 3(h_max = 3 > r_min − v_max = 2)、
閉ループ遷移公理を等式で実現する実例をとる。
発動しても一段の純変化 = −3 + 1 + 3 = +1 > 0 で、e_t は発散する。
沈黙軸に蓄積した負債が測定軸へ結合する規模が修復帯域を超えると、
どんなしきい値方針でも安定化は失敗する。
```

### D.15 終焉と migration の実例(第X部)

終焉(定義 57.1・定理 57.2):

```text
定義 40.1 の数値(c(n) = 1 + n)で予算 b = 3 とする。
質量 n = 3 で c(3) = 4 > 3 ⇒ 枯渇(strict 減少を実現できる許容力が無い)。
模型公理 (i)(ii) の下で吸収的: 以後の許容力は質量を減らさず、コストは下がらない。
予算を b′ = 5 に引き上げると修復(c(3) = 4 <= 5)が許容になり脱出できる
(枯渇は予算相対; 両相非空 = D6)。
```

migration(定義 58.2):

```text
開発系の射: fiber の context {Pricing, Payment, Contract, UI} を
後継系の {Pricing′, Payment′, Contract′} へ写す(UI は対応の外 = 廃止面)。
law データ(解決後の rounding = 1)を対応に沿って輸送する。

単一源の輸送だけなら branch 対が無く、三段 filtration は発動しない
(「空虚な通過(非発動)」であり、検査したことにはならない — D.6 の規律)。
診断が働く migration ダイヤモンドを組む:
  A″ = 輸送された場(rounding = 1)、C″ = 後継系の既存場(rounding′ = 0 native)、
  base = 対応データ、overlap = Contract′。
  段階0: presentation 融合は valid(通過)。
  段階1: mismatch = 1 − 0 = 1 ∈ Z/2、調整群 0(後継系の契約テストが pin)
         ⇒ [m] = 1 ≠ 0 ⇒ migration には貼り合わせの明示的選択が要る
         (rounding′ := 1 の採用 = 移行時の破壊的契約変更の形式的実体)。
  段階2: 輸送された law 対 (I, J) = ((xy), (xz)) は shared witness factor を保存し、
         Tor₁ ≠ 0 のまま ⇒ migration は導来衝突を消さない(輸送不変)。

UI の脱落は沈黙として扱い、無条件の同値は主張しない。
```

### D.16 P3 の必置照合

```text
第IX部 -> D.14(annihilator 計算・閉ループ数値・仮定 (2) を外す発散反例)
第X部  -> D.15(枯渇の予算相対性と吸収性・migration の輸送診断)
```

## 付録 E 先行研究の接続

「包摂」を主張しない。各理論について「同型な部分 / SFT が加える層 / SFT が再導出しないもの」
の三行で接続を記す。

```text
Darcs patch theory:
  同型な部分: commute(定義 13.1)は Darcs の commutation と同じ形。
  加える層: 台の closure 契約、AAT 幾何上の law 水準の残差(段階1・2)。
  再導出しないもの: patch の内容水準の merge 正当性理論。

Mimram–Di Giusto(A Categorical Theory of Patches)/ Pijul:
  同型な部分: merge の圏論的定式化(押し出し)。
  加える層: 押し出しの語を presentation 圏に限定し(原則 20.2)、
             トレース側は cover と選択データで扱う三段 filtration。
  再導出しないもの: 押し出しの存在する patch 圏の設計そのもの。

Homotopical patch theory:
  同型な部分: 履歴 = 経路、patch law = 高次経路という方向。
  加える層: law データ係数の Čech / 導来水準の障害分類。
  再導出しないもの: HoTT 上の実装モデル。

操作変換(OT)/ CRDT:
  同型な部分: transport 規則 = 接続の実例。可換性による収束(SEC)。
  加える層: 「可換化ではなく持ち上げ」という位置づけ(Model theorem 21.2)、
             曲率・残差としての読み。
  再導出しないもの: TP1 / TP2・SEC の内容水準の正しさの証明。

Horwitz–Prins–Reps(program integration):
  同型な部分: 「テキストは貼れたが意味が壊れる」の検出という問題設定。
  加える層: 障害の三層分解(特に段階1 と段階2 の分離)と AAT 機械への接続。
  再導出しないもの: PDG に基づく干渉検出アルゴリズム。

Mazurkiewicz trace / conflict-serializability / Lipton mover:
  同型な部分: 独立性(素な台)による可換と直列化。
  加える層: 依存の幾何化(closure、law 係数)と残差の類。
  再導出しないもの: スケジューラ理論・DB 直列化理論の本体。

directed algebraic topology:
  同型な部分: 順序依存性の幾何化という方向。
  加える層: AAT の law / obstruction 係数での読み。
  再導出しないもの: 有向位相の一般理論。

監督制御(Ramadge–Wonham):
  同型な部分: supervisor 合成、可制御事象・可観測事象の区別(第IX部の参照枠)。
  加える層: AAT 幾何上の pairing 可観測性(命題 51.3)とギャップ汎函数の究極有界(定理 54.2)。
  再導出しないもの: 可制御性の言語理論(supremal controllable sublanguage 等)。

Conway / mirroring 研究、Lehman、change entropy(Hassan)、socio-technical 系:
  同型な部分: 経験的現象の同定(組織と構造の対応、継続変化、変更の乱雑さ)。
  加える層: それぞれ第V部(二被覆の不整合)、H5、第VIII部(比較可能性条件つき計数)。
  再導出しないもの: 経験的知見そのもの(台帳で仮説として扱う)。
```

## 付録 F 旧概念の処遇(v1 → v2)

| 旧 SFT 概念 | 処遇 | 行き先 |
| --- | --- | --- |
| SoftwareField | 転生 | 場の配置(定義 8.2) |
| DevelopmentField | 転生 | 開発系 𝔇(序 §3) |
| CodebaseAsFieldMemory | 吸収 | 場の記憶(定義 8.7) |
| ArtifactMediatedChange / Force | 転生 | ForceSchema / AppliedForce(第II部) |
| OperationSupport / OperationPolicy | 転生 | 生成模型と方針(定義 9.2; 完全化は P2) |
| ForecastCone | 廃棄(legacy 墓標化) | 挙動空間上の到達集合 + 計器射影 + governed reachable class(第VI・IX部)。可能性は変形空間(第VII部)。台帳側の分別は P5 |
| ConsequenceEnvelope | 廃棄 | 理論からは消える(report 書式としての再利用は tooling 側の別判断) |
| GovernanceIntervention / FieldUpdate | 転生 | 生成子 T_Π(定義 9.2)と controller(§53–54) |
| InstrumentingIntervention | 転生 | 計器族の拡大 = controller の作用(定義 53.2) |
| ProposalAccounting / Dissipation | 分割 | 提案/適用の区別(第IV部)、収支則(P2)、アンサンブル(第VIII部) |
| ReviewMediation | 転生 | 計器評価 + 降下データの選択(第IV部) |
| IncidentFeedback / runtime guard | 転生 | 非計画の計器読み値と controller(定義 53.3) |
| MigrationEnvelope | 転生 | migration = 開発系の射に沿った場の輸送(定義 58.2) |
| AI Proposal Governance | 分割 | delegator 相関つき源(第IV部)+ 監督制御(第IX部) |
| StableRegion / ReachablePreimage | 転生 | 挙動空間上の mud 類と almost-sure の罠(§40)、正再帰相 |
| Attractor Engineering | 転生 | 場の設計(コスト幾何の設計; 原則 40.3) |
| LifecycleTrajectory / EndOfLife | 転生 | 軌道 regime(定義 56.1)と終焉 = 有効力の枯渇(定義 57.1・定理 57.2) |
| Claim Level L0–L5 | 置換 | 主張の梯子(序 §1)+ 台帳(付録 B) |
| SFT Workbench / benchmark 節 | 撤去 | 理論本文から tooling 側へ(D4) |

旧 Lean 塔(`Formal/Arch/Evolution/` 配下 39 ファイル)は凍結である:
Formal.lean の import は維持(build 対象のまま)、変更は build 修復のみ、
新規参照は禁止、新塔が対応部を覆った時点で個別に削除判断する。

## 付録 G 系譜と執筆状態

```text
系譜:
  SFT v1(computational theory; ForecastCone 核)
    -> docs/archive/2026-07-04-sft-v1-computational-theory/
  Grothendieck–Derived AAT/SFT ポジションペーパー(docs/note/Grothendieck_Derived_AAT-SFT.md)
    — AAT 半分は AG 本文として実現済み。SFT 半分(§9)は本書が後継。
  SFT v2 理論骨格ノート(docs/note/sft_development_spacetime_dynamics_skeleton.md)
    — 敵対レビュー 5 本 + 有識者レビューを反映した設計の正典。

執筆状態(P3): 序・第I〜IV部・第VI部・第IX〜X部・付録が完全。
P1 本文は 3 方向の敵対レビュー(数学検証・骨格規律適合・通読整合;
MAJOR 12 件・MINOR 20 件)を経て修正済みである(2026-07-04)。
P2(第IV部完全化・第VI部完全化 §38–42・付録 D.9–D.13)は
敵対レビュー 2 方向(MAJOR 8 件・MINOR 12 件)を、
P3(第IX部 §51–55・第X部 §56–59・付録 D.14–D.16)も
敵対レビュー 2 方向(MAJOR 8 件・MINOR 12 件)を、同日に経て全件反映した。
第V/VII/VIII部は予告であり、規範的主張を置かない。
Lean 最初の的 L1–L3(有限トレース site・遠隔可換・merge residue)は
`research/lean/ResearchLean/AG/SFTDynamics/`(TraceSite / ForceSchema / MergeResidue)として
着手済みである(遠隔可換 = 定理 14.3 と D.5 の非零衝突類は Lean proved)。
aat_interface.md の v2 化・README / guideline の書き換え・台帳の分別は P5 で行う。
```
