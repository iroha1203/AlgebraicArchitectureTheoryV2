# ArchView Rebuild PRD
## Atom-native 3D Architecture Atlas

| 項目 | 内容 |
|---|---|
| 状態 | Draft |
| 位置づけ | 現行ArchViewとは別設計のゼロベース再構築 |
| 必須入力 | ArchMap |
| 任意入力 | 既存ArchSig run artifacts |
| 新しい永続データ構造 | **作らない** |
| 主利用者 | AATを知らない一般のソフトウェアエンジニア |
| 中心機能 | コードベース理解、ArchSig分析表示、改善箇所特定 |
| AI・自然言語質問 | Non-Goal |
| 自動修正・コード生成 | Non-Goal |

---

# 1. Product Definition

> **ArchViewは、ArchMapに記録されたAtomを直接3D空間へ構成し、コードベースの意味的アーキテクチャを理解するためのArchitecture Atlasである。**
>
> そのAtom geometryの上に、ArchSigが測定したLaw、局所・大域不整合、obstruction、repair targetを重ね、問題の意味から確認・改善すべきファイル、クラス、メソッドまで到達できるようにする。

ArchViewの中心は、ArchSig結果のレポート表示ではありません。

```text
ArchMap
  ↓
Atom-native Architecture Geometry
  ↓
コードベース理解
  ↓
ArchSig Analysis Overlay
  ↓
改善対象となるSourceへの到達
```

ArchMapはすでに、`sources`、`atoms`、`contexts`、`covers`を持っています。Atomには`kind`、`subject`、`axis`、`predicate`、`object`、`refs`があり、sourceには`path`、`symbol`、`line`を保持できます。したがって、新しいarchitecture world modelを作らなくても、コード理解とsource landingの基礎は既存のArchMapだけで構成できます。

---

# 2. Product Question

このPRDの採否を決める問いを、次の一文に固定します。

> **AATを知らず、対象コードベースを初めて見るエンジニアが、ArchMapと既存ArchSig artifactsだけを使い、コードを広範囲に読むことなく、アーキテクチャ構造を理解し、分析結果を説明し、改善対象となるsourceへ到達できるか。**

「できる」と判定するには、次の3条件を同時に満たす必要があります。

| 条件 | 判定内容 |
|---|---|
| Architecture Understanding | ArchMapだけで、主要Context、責務、状態、作用、contract、boundaryを説明できる |
| Analysis Understanding | ArchSig findingについて、局所事実、境界、不整合、大域結論を説明できる |
| Improvement Landing | findingから、根拠または改善候補となるfile、symbol、lineへ到達できる |

---

# 3. Scope

新ArchViewの製品機能は、以下の3つだけに絞ります。

## 3.1 コードベース理解

ArchMapを直接読み込み、Atomを中心にコードベースの意味的構造を描画します。

利用者が理解できることは次です。

- どのContextが存在するか
- どのContextがCoverに含まれるか
- 各ContextにどのAtomが存在するか
- 同じsubjectについて、どのcapability、state、effect、contractが記録されているか
- 複数Contextに共有されるAtomは何か
- どのContext間にrestrictionがあるか
- 各Atomはどのsourceに根ざしているか

## 3.2 ArchSig分析結果の表示

同じAtom geometryの上に、既存のArchSig artifactをoverlayします。

- measured support
- local observation
- mismatch
- section value
- gluing failure
- H¹ support
- obstruction support
- measured zero
- unmeasured / not computed
- gate decision
- repair target
- comparison result

分析表示のために別の3D世界を作りません。

## 3.3 改善箇所の特定

ArchSig findingを、ArchMapのAtomとsource refsを通じて次へ解決します。

```text
Finding
  ↓
Context / overlap / Atom support
  ↓
Source reference
  ↓
File
  ↓
Class / symbol
  ↓
Method / line
```

ただし、次の4種類を明確に分けます。

| 種別 | 意味 |
|---|---|
| Direct Evidence | 問題の直接根拠になったsource |
| Boundary Participant | 不一致境界の片側を構成するsource |
| Candidate Change Point | ArchSigまたはRepairPlanが変更候補として明示したsource |
| Validated Repair | target stateを再計測し、選択されたobstructionが解消されたsource |

---

# 4. Non-Goals

以下は本PRDには含めません。

- AIチャット
- 自然言語質問
- source codeからのAtom抽出
- ArchMap生成・編集
- コード生成
- patch生成
- 自動修正
- 一般的なcall graph viewer
- UML生成
- 新しいarchitecture data schema
- 新しいanalysis summary schema
- 将来予測
- runtime profiler
- IDEの代替
- 「このファイルを直せ」という根拠のない自動判断
- arbitrary risk score
- 重要度や健全性の推測

---

# 5. 過去の可視化ツールの壁に対する設計回答

## 5.1 構文を描くだけでは意味が分からない

従来の可視化は、file、class、LOC、dependencyを別の形に置き換えるものになりがちでした。

新ArchViewでは、表示の最小単位をAtomにします。

```text
PaymentService interprets price as BigDecimal
CancelService rounds refund to scale 2
Order stores price as String
Payment emits PaymentCompleted
Gateway requires authorization
```

Atomは、component、relation、capability、state、effect、authority、contract、semantic、runtimeなどを表せるprimitive architectural factです。

## 5.2 全部表示すると理解できない

全Atomを初期表示しません。

```text
Cover
  ↓
Context
  ↓
Subject group
  ↓
Atom
  ↓
Source
```

というsemantic zoomを採用します。

`Subject group`は新しいdomain entityではありません。Atomの`subject`が完全一致するものを、表示上まとめるだけです。

## 5.3 空間に意味がない

force layoutや乱数で座標を作りません。

位置は以下に限定します。

- Context: 明示されたrestrictionとAtom membershipから決定論的に配置
- Atom: 明示されたContext membershipの内側に配置
- 複数Context所属Atom: shared-support領域に配置
- Subject group: 完全一致subject内の表示上の集約
- Section: Contextの上にfiberとして配置
- Source: Inspector上で表示し、必要時だけAtomとの対応線を描画

座標そのものがLaw違反や重要度を意味することはありません。

## 5.4 分析とコードが分離する

ArchSigのfindingを、Atom geometryから切り離したカードだけで表示しません。

findingを選択した瞬間に、

- 該当Context
- 該当Atom
- 該当shared support
- source refs

が同時に選択されます。

## 5.5 見ても行動できない

すべてのfindingにSource Targetsを持たせます。

ただし、根拠と修正候補は分けます。

```text
問題の証拠がある
≠
必ずそこを変更すべき
```

---

# 6. Existing Input Contract

## 6.1 必須入力

```text
archmap.json
```

受理する主な既存フィールドは次です。

```text
sources
atoms
contexts
covers
```

## 6.2 任意入力

ArchSigのrun directoryを追加で読み込めます。

```text
normalized-archmap.json
archsig-analysis-summary.json
archsig-insight-report.json
archsig-measurement-packet.json
archsig-comparison-report.json
archsig-gate-report.json
archsig-run-manifest.json
```

ArchSigは現在、measurement packet、summary、insight report、compare report、gate reportなどを既存artifactとして出力しています。Insight reportはinspection queue、measurement packetはbounded evidence、compare reportはrun間比較、gate reportはCI判断面を担います。

## 6.3 Raw ArchMapとNormalized IDの対応

分析結果がnormalized Atom IDを参照する場合は、既存の`normalized-archmap.json`をidentity bridgeとして使います。

```text
normalizedAtomId
  ↓
sourceAtomId
  ↓
ArchMap atoms[].id
```

Normalized ArchMapには、`sourceAtomId`、`normalizedAtomId`、Atom kind、subject、axis、predicate、object、source refs、context membershipsがあります。

新しい対応表artifactは作りません。

---

# 7. Information Architecture

画面全体を3つのモードに分けます。

```text
Architecture | Analysis | Improve
```

これらは別sceneではありません。

- 同じ3D geometry
- 同じカメラ
- 同じ選択
- 同じsemantic zoom
- 同じInspector

を共有し、overlayと補助UIだけを切り替えます。

---

# 8. Main UI

```text
┌────────────────────────────────────────────────────────────────────┐
│ Repository / Revision / Cover     Architecture Analysis Improve    │
├───────────────────┬──────────────────────────────┬─────────────────┤
│ Scope Explorer    │                              │ Inspector       │
│                   │                              │                 │
│ Covers            │                              │ Summary         │
│ Contexts          │        3D Atom Atlas         │ Architecture    │
│ Subjects          │                              │ Evidence        │
│ Findings          │                              │ Source targets  │
│                   │                              │ Boundaries      │
│                   │                              │ Technical data  │
├───────────────────┴──────────────────────────────┴─────────────────┤
│ Breadcrumb / Selected objects / Source Target Drawer / Mini-map   │
└────────────────────────────────────────────────────────────────────┘
```

## 8.1 Top Bar

常設項目を絞ります。

```text
Repository
Revision
Selected Cover
Architecture | Analysis | Improve
3D | Top
Reset camera
Search
```

Theory、fidelity、raw data、schema情報は補助メニューへ置きます。

## 8.2 Scope Explorer

左側は、現在のArchMapに本当に存在する要素だけを表示します。

```text
Covers
  money-settlement-loop

Contexts
  cancellation
  inside-payment
  order

Subjects
  CancelService
  PaymentService
  Order
```

表示順は決定論的にします。

- 明示orderがあればその順
- なければID辞書順
- 件数順を使う場合は「Atom count順」とUI上に明記

「主要」「重要」といった意味的評価は勝手に付けません。

## 8.3 Inspector

Inspectorの情報順序は、どの要素を選んでも固定します。

1. **What is this?**
2. **Architecture facts**
3. **Analysis evidence**
4. **Source targets**
5. **Boundary / non-claims**
6. **Technical details**

一般ユーザーは上から読み、AATやartifactを確認したいユーザーは下まで開けます。

---

# 9. 3D Interaction Model

## 9.1 回転についての設計決定

**ユーザーによるカメラ回転は許可します。**

禁止するのは回転操作ではなく、データに存在しない意味をアニメーションで付加することです。

```text
Camera orbit
  → 許可

Selected Contextの周囲を回る
  → 許可

自動回転presentation
  → 既定OFF

F₂ class glyphを常時回転させ、
流れの向きがあるように見せる
  → 対応する測定がない限り禁止
```

カメラ操作と分析glyphの意味は分けます。

## 9.2 操作

| 操作 | 結果 |
|---|---|
| 左ドラッグ | カメラをorbit |
| 右ドラッグ / Shift+ドラッグ | 平行移動 |
| ホイール / ピンチ | semantic zoom |
| クリック | 選択 |
| ダブルクリック | 選択対象へfocus |
| Shift+クリック | 複数選択 |
| Esc | 一段前の選択へ戻る |
| F | 選択対象を画面中央へ |
| H | Cover全体を表示 |
| 1 | Top view |
| 2 | Isometric view |
| 3 | Front view |
| 0 | Camera reset |

## 9.3 回転範囲

通常のAtlasモードでは、

- 水平方向は360度回転可能
- 上下方向も広く回転可能
- rollは既定で固定
- 上下反転は既定では発生しない

とします。

選択対象の詳細を見る`Inspect object`状態では、選択ContextまたはAtom constellationをより自由に回転できます。

## 9.4 方向喪失の防止

常設するもの:

- 方位コンパス
- Mini-map
- Top / Isometric snap
- Reset
- Breadcrumb
- 現在選択中のCover / Context

3D操作の自由度を保ちながら、迷子にならないようにします。

---

# 10. Semantic Zoom

```text
Scope › Context › Subject › Atom › Source
```

画面下部に現在のレベルを表示します。

## Level 0: Scope

表示:

- Cover
- Context
- restriction
- ContextごとのAtom count

## Level 1: Context

表示:

- Context内のsubject groups
- 他Contextと共有されるAtom
- restriction
- shared support

## Level 2: Subject

表示:

- subjectが持つAtom
- capability
- state
- effect
- contract
- authority
- semantic interpretation
- runtime interaction

## Level 3: Atom

表示:

- subject
- predicate
- object
- kind
- axis
- Context membership
- source refs
- related finding

## Level 4: Source

表示:

- path
- symbol
- line
- section
- source kind
- 同じsourceに根ざす他Atom

Source codeそのものは3D空間へ大量表示せず、右側の固定パネルへ表示します。

---

# 11. Architecture Mode

Architecture Modeは、ArchSigを読み込んでいなくても成立する新ArchViewの本体です。

## 11.1 Context Geometry

Contextは、局所的なarchitecture viewを表すchartとして描きます。

AATにおいてContextは、component-local、feature-local、semantic slice、boundary slice、runtime sliceなど、同じarchitecture objectに対する局所的な読みです。

描画:

- 薄い半透明の曲面
- Atom countに応じた面積
- label
- Context ID
- source count
- restriction depth

面積は「重要度」ではなく、**明示的に所属しているAtom数**を表します。

## 11.2 Restriction

`contexts[].restrictsTo`から、restriction morphismを描きます。

- 矢印付きconnector
- hover時にsource Contextとtarget Contextを表示
- directionを明示
- dependencyとは呼ばない

AAT上でrestrictionは、大きいContextから小さいContextへ見える情報を制限する操作です。

## 11.3 Shared Support

同じAtomが複数Contextに明示的に所属している場合、Context間にshared-support領域を描きます。

重要な区別:

```text
shared Atom membership
  → ArchMapから描画できる

categorical pullback / measured overlap
  → 対応するartifactがある場合だけ主張できる
```

ArchMapしか読み込んでいない場合、UI名称は`Shared support`とします。

ArchSig packetが実際のcover nerveやoverlapを供給している場合だけ、`Measured overlap`として表示します。

## 11.4 Subject Group

同一Context内で`subject`が完全一致するAtomをまとめます。

```text
PaymentService
  capability
  semantic interpretation
  data state
  effect
```

Subject groupは、AATの新しいobjectではありません。

Inspectorに次を明示します。

```text
Layout grouping
Atoms grouped by exact subject equality.
This grouping does not create a new architectural fact.
```

## 11.5 Atom Glyph

| Atom kind | 通常表示 | 形 |
|---|---|---|
| component | Component | solid core |
| relation | Relation | joint |
| capability | Capability | prism |
| state | State | stacked disk |
| effect | Effect | burst |
| authority | Authority | gate |
| contract | Contract | frame |
| semantic | Meaning | lens |
| runtime | Runtime interaction | conduit |

Atom familyは形で区別し、分析状態は色で区別します。

---

# 12. AAT Geometry Rendering

AATの幾何を「数学用語のラベル」としてではなく、実際の形として利用します。

| AAT | 一般表示 | 描画条件 | 表現 |
|---|---|---|---|
| Atom | Architecture fact | ArchMap Atom | glyph |
| Context | Architecture area | ArchMap Context | chart |
| Cover | Selected scope | ArchMap Cover | chart集合 |
| Restriction | Local-view relation | `restrictsTo` | directed connector |
| Shared support | Shared facts | 複数Context membership | intersection zone |
| Section value | Local convention | explicit sectionValue Atom | fiber point / sheet |
| Agreement | Conventions agree | measured edge value | connected sheet |
| Mismatch | Conventions disagree | measured witness | broken sheet |
| Global section | System-wide agreement | explicit ArchSig conclusion | continuous sheet |
| H¹ support | Global inconsistency support | explicit class support | non-closing ribbon |
| Obstruction circuit | Minimal conflict | explicit minimal-support output | cage |
| Lawful locus | Valid region | explicit locus coordinates | zero-set geometry |
| Repair morphism | Candidate change | explicit repair data | source→target morphism |

## 段階的縮退

必要なデータがない場合、もっともらしい形を発明しません。

例:

```text
sectionValueなし
  → sheetを描かない

H¹ supportなし
  → obstruction ribbonを描かない

minimality証拠なし
  → obstruction circuitとは呼ばずsupportと表示

scalar fieldなし
  → contourやterrainを描かない

repair targetなし
  → repair handleを描かない
```

---

# 13. Analysis Mode

## 13.1 Analysisの読み込み

既存ArchSig run directoryを読み込みます。

検査:

- schema
- runId
- input digests
- ArchMap digest
- packet digest
- profile ref
- normalized ID mapping

一致しないoverlayはfail-closedで拒否します。

```text
Analysis rejected

The loaded measurement packet was not produced
from the current ArchMap.

Expected digest: ...
Received digest: ...
```

無理に一部だけ描画しません。

## 13.2 Finding List

左側にfindingを表示します。

```text
Global money conventions do not agree
Measured nonzero
3 contexts · 3 boundaries · 6 supporting atoms
```

raw conclusion codeはTechnical detailsへ置きます。

```text
MEASURED_NONGLUING_RESIDUAL_CLASS
```

## 13.3 Finding Selection

findingを選ぶと、同じArchitecture Atlas上で次を行います。

1. support Contextを残す
2. support Atomを強調する
3. support edge / shared supportを強調する
4. 他のgeometryを薄くする
5. Source Target Drawerを開く

## 13.4 段階的説明

AIは使わず、既存artifactの構造と固定テンプレートで説明します。

```text
1. Local facts
2. Shared boundaries
3. Global result
4. Source evidence
```

### Local facts

各Contextで観測されたAtomやsection valueを表示します。

### Shared boundaries

agreement、mismatch、unmeasuredを区別します。

### Global result

ArchSigが明示的に測定した結論だけを表示します。

### Source evidence

Atom refsとsource refsからsource targetへ降ります。

既存viewer実装でも、insight evidenceにはAtom refs、Context refs、source refsが使われ、source landingへ接続されています。新ArchViewではこの接続を補助機能ではなく中心UXにします。

---

# 14. Improve Mode

Improve Modeは、分析結果からsourceへ到達する作業面です。

## 14.1 Source Target Resolver

finding `F`について、既存artifactだけから次を解決します。

```text
Direct source refs from finding
  ∪
Source refs of support Atoms
  ∪
Source refs of explicit repair target Atoms
  ∪
Source refs of explicitly named boundary participants
```

結果は次でgroup化します。

```text
path
  └── symbol
      └── line
          └── supporting Atom
```

## 14.2 Source Target分類

### Direct Evidence

findingの`sourceRefs`またはdirect support Atomに根ざすsource。

```text
DIRECT EVIDENCE

CancelServiceImpl.java
CancelServiceImpl#calculateRefund
line 281
```

### Boundary Participant

mismatch edgeまたはrestrictionの両側を構成するsource。

```text
BOUNDARY PARTICIPANT

InsidePaymentServiceImpl.java
InsidePaymentServiceImpl#pay
line 142
```

### Candidate Change Point

ArchSigのrepair targetやRepairPlanが明示したAtom・source。

```text
CANDIDATE CHANGE POINT

Order.java
Order#price
line 42
```

### Validated Repair

target stateの再計測結果が、選択されたobstructionの消滅を明示している場合。

```text
VALIDATED IN HYPOTHETICAL TARGET

Order.java
Order#price
```

repositoryへ適用済みでない場合は、必ず`Hypothetical`を表示します。

## 14.3 改善候補がない場合

直接のrepair targetが供給されていないfindingを、勝手に修正候補へ昇格しません。

```text
No explicit repair target was supplied.

The locations below are evidence and inspection points,
not validated change recommendations.
```

現在のArchSigでも、hitting-set targetはcombinatorial repair supportであり、semantic repair operationが供給されるまではautomatic repairとして扱わない境界が明示されています。

## 14.4 Resolution Level

sourceごとに解決精度を表示します。

```text
METHOD LEVEL
CLASS / SYMBOL LEVEL
FILE LEVEL
UNRESOLVED
```

判定:

| 入力 | 表示 |
|---|---|
| path + symbol + line | Method / Symbol level |
| path + symbol | Symbol level |
| path + line | Line level |
| path only | File level |
| semantic ref only | Unresolved |

クラス名やメソッド名をsource textから推測しません。

---

# 15. Structured Search

自然言語質問は実装しません。

検索対象は明示データだけです。

```text
Atom ID
Atom label
subject
predicate
object
Context ID
Context label
Cover ID
source path
source symbol
finding title
conclusion code
```

検索結果は種類別に表示します。

```text
CONTEXTS
Payment

SUBJECTS
PaymentService

ATOMS
PaymentService interprets price as BigDecimal

SOURCES
InsidePaymentServiceImpl#pay

FINDINGS
Global money conventions do not agree
```

---

# 16. Visual State Language

色の意味を限定します。

| 表示 | 意味 |
|---|---|
| neutral blue-grey | 通常のarchitecture structure |
| cyan | 現在選択 |
| amber | measured nonzero / direct evidence |
| red | explicit gate block |
| blue | candidate change point |
| green | validated target / actual cleared result |
| grey hatch | unmeasured / unknown / not computed |
| translucent blue | hypothetical target |

Atom kindの識別は主に形で行います。

色だけで種類と分析状態を同時に表しません。

---

# 17. Honesty and Fidelity Requirements

「本物のツール」であることを、以下の規則で強制します。

## 17.1 Every Visual Element Has Provenance

描画要素を選ぶと、必ず次を表示します。

```text
Rendered from
ArchMap atom: ...
ArchMap context: ...
ArchSig packet row: ...
Source ref: ...

Visual channels
Position: derived
Shape: Atom kind
Size: observed Atom count
Color: measured conclusion
Animation: interaction only
```

## 17.2 No Invented Edges

以下から接続先を推測しません。

- object文字列の類似
- subject名の類似
- package名の類似
- embedding上の近さ
- AI推論
- filenameの近さ

edgeを描く条件は、明示されたrelation、restriction、membership、ArchSig supportだけです。

## 17.3 No Fake Geometry

禁止:

- scalar dataのないterrain
- direction dataのないflow
- minimality証拠のないobstruction circuit
- repair dataのないrepair arrow
- measurementのないgreen safe状態
- random jitter
- placeholder node
- demo用のfake finding

## 17.4 No Silent Omission

参照解決できなかった場合は、画面に件数と理由を出します。

```text
6 support references resolved
2 support references unresolved
```

## 17.5 Analysis Absence Is Normal

ArchSigを読み込んでいない場合、

```text
Architecture loaded
No analysis loaded
```

と表示します。

fakeなanalysisサンプルを表示しません。

---

# 18. Functional Requirements

## R1 — ArchMap Direct Loading

- ArchMapを単独で読み込める
- `sources / atoms / contexts / covers`を直接使う
- 新しいauthoritative artifactを要求しない
- schema不正は明示拒否
- 空ArchMapは明示状態を表示

## R2 — Deterministic Atom Atlas

- 同一ArchMapから同一配置を生成
- random layout禁止
- Context、subject、Atomの順序を固定
- Context membershipを超えたAtom配置をしない
- shared-supportは明示membershipからのみ生成

## R3 — Semantic Zoom

- Scope、Context、Subject、Atom、Sourceの5段階
- zoomによる表示密度切替
- 選択履歴
- breadcrumb
- focus / reset

## R4 — 3D Navigation

- user-controlled orbit
- pan
- zoom
- Top / Isometric / Front snap
- camera reset
- mini-map
- compass
- Flat view
- reduced-motion対応

## R5 — Architecture Inspector

Atom選択時に表示:

- fact
- kind
- axis
- contexts
- sources
- related findings

Context選択時に表示:

- member Atom count
- subjects
- restrictions
- shared support
- Cover membership

## R6 — Analysis Overlay

- 既存ArchSig artifactを読む
- normalized ID bridge
- digest整合
- support highlight
- local / overlap / globalの順で説明
- unmeasuredとzeroを区別
- unresolved refsを明示

## R7 — Improvement Locator

- findingからsource targetへ解決
- path / symbol / line表示
- evidence / boundary / candidate / validatedを区別
- resolution levelを表示
- editor URIまたはcopy pathを提供
- opaque score禁止

## R8 — Structured Search

- Atom、Context、Cover、source、findingを検索
- fuzzy text searchは許可
- semantic relationの推測は禁止
- 結果から3D位置へfocus

## R9 — Table / Outline Fallback

- 3Dと同じ情報をOutline表示できる
- keyboardだけで選択可能
- 3DとOutlineのselection同期
- 色以外の状態表現

---

# 19. Non-Functional Requirements

## Performance

正式なscale fixtureとして、既存train-ticket ArchMapを使用します。

実験結果では、2,118 atoms、43 contexts、3 covers、440 sourcesのArchMapが構成されています。

必須条件:

- 上記規模をsampleせずロード
- Context skeletonを先行表示
- Atomはprogressiveに追加
- UI threadの長時間blockを避ける
- 通常操作で30fps以上を目標
- ラベルを全Atom同時表示しない
- visible regionとzoom levelに応じてLODを適用

## Accessibility

- keyboard navigation
- focus indicator
- high contrast
- reduced motion
- color-independent shapes
- Outline view
- DOM上の選択要素説明
- source textコピー

## Locality

- ArchMap単独でArchitecture Modeが動作
- analysisは任意
- source snippet表示はrepository rootが供給された場合のみ
- repository rootがない場合もpath / symbol / lineは表示

---

# 20. Acceptance Criteria

## AC1 — Codebase Understanding

AAT未経験かつ対象repo未経験の参加者が、ArchMapだけを使用して次を説明できる。

1. 選択Coverに含まれるContext
2. 指定subjectのcapability
3. 指定subjectが保持するstate
4. 関係するeffectまたはcontract
5. 根拠source

正答率80%以上を合格とします。

## AC2 — 3D Usability

参加者が説明なし、または30秒以内の操作説明で次を実行できる。

- 回転
- pan
- zoom
- Context選択
- Subject選択
- Atom選択
- overviewへ戻る

全参加者がcamera resetに到達できることを必須とします。

## AC3 — Analysis Understanding

参加者がfindingを選び、次を説明できる。

- どの局所事実が存在するか
- どの境界に問題があるか
- なぜ大域的問題になるか
- どのsupportが根拠か
- 何が未観測か

## AC4 — Source Landing

finding選択後、3操作以内に次へ到達できる。

- file path
- symbol
- line
- supporting Atom

method-level sourceが存在しない場合は、利用者がその制限を認識できること。

## AC5 — Evidence / Repair Separation

参加者が次を区別できる。

- direct evidence
- candidate change point
- validated hypothetical repair
- actual repository change

誤認率10%未満を合格とします。

## AC6 — Fidelity

自動テストで次を保証します。

- 表示AtomはすべてArchMapに存在
- 表示ContextはすべてArchMapに存在
- restrictionはすべて`restrictsTo`に存在
- source targetはすべて既存source refへ解決
- analysis overlayは既存packetまたはinsight rowへ対応
- unsupported scalar fieldを描かない
- repair targetなしでcandidate表示をしない
- digest不一致を拒否

## AC7 — Determinism

同一入力を複数回読み込み、

- Context座標
- Subject配置
- Atom配置
- source target order

が一致すること。

## AC8 — Scale

train-ticket fixtureの、

- 2,118 atoms
- 43 contexts
- 3 covers
- 440 sources

を全件ロードし、検索・選択・source landingが成立すること。

## AC9 — No New Data Contract

本PRDの全機能が、次のみで成立すること。

- ArchMap
- normalized ArchMap
- existing ArchSig artifacts
- optional repository root

新規schemaを受け入れ条件にしないこと。

---

# 21. Rejection Conditions

以下のいずれかが発生した実装は、画面が美しくても却下します。

1. ArchMapにないAtomを描画した
2. 文字列類似からrelation edgeを推測した
3. 分析がない状態でwarningやrepairを表示した
4. direct evidenceを自動的にrepair targetとして扱った
5. source symbolを発明した
6. unmeasuredをmeasured zeroとして表示した
7. scalar fieldなしでterrainやcontourを描いた
8. random layoutを使用した
9. user-controlled camera rotationを禁止した
10. カメラ回転と、データglyphの意味的回転を混同した
11. AAT用語を理解しないと基本操作できなかった
12. raw conclusion codeだけを主説明として表示した
13. unresolved refを無言で捨てた
14. 新しいauthoritative world modelを必須にした
15. ArchSig analysisがなければArchitecture Modeが使えなかった

---

# 22. Implementation Sequence

## Phase 1 — Atom Atlas

実装:

- ArchMap loader
- validation
- Cover / Context
- restriction
- shared support
- subject grouping
- Atom glyph
- semantic zoom
- structured search
- source inspector
- 3D camera
- Outline view

Phase 1終了時点で、ArchSigなしのコードベース理解ツールとして成立させます。

## Phase 2 — ArchSig Overlay

実装:

- run directory loader
- normalized ID bridge
- summary / insight / packet
- finding list
- support highlighting
- gluing geometry
- unmeasured表示
- digest fail-closed

## Phase 3 — Improvement Locator

実装:

- source target resolver
- evidence / boundary / candidate / validated分類
- path / symbol / line grouping
- resolution level
- editor landing
- side-by-side boundary comparison

## Phase 4 — Hardening

実装:

- train-ticket scale
- performance
- accessibility
- deterministic screenshots
- fidelity tests
- AAT未経験者によるtask test
- error / empty / unresolved states

---

# 23. Final Product Identity

新ArchViewを一文で定義すると、次になります。

> **ArchViewは、ArchMapのAtom・Context・Coverを本物のarchitecture geometryとして3Dに構成し、その上にArchSigの測定結果を重ね、分析の意味から改善対象となるfile・class・methodまでを一つの操作空間で結ぶ、Atom-native Architecture Atlasである。**

製品の3本柱は最後まで変えません。

```text
Understand the codebase
  ArchMapのAtom geometryを読む

Understand the analysis
  同じgeometry上でArchSig evidenceを読む

Locate improvements
  support Atomからsourceへ降りる
```

この設計では、3Dは飾りではありません。Contextの局所性、Cover、restriction、shared support、section、gluing、obstructionを表現するための操作可能な幾何です。

同時に、描画対象、接続、色、source、修正候補のすべてが既存artifactへ追跡できるため、**見栄えだけのarchitecture visualizationではなく、コード理解と改善判断に実際に使える開発ツール**になります。
