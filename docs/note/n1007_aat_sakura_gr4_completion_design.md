# SAKURA 海域と Gr4 完了設計 — 命名記録と後続カード6枚の定義

本ノートは考察ノートである。新しい公理・定義・定理は導入せず、証明済み定理の
statement を変更しない。目的は三つある。第一に、Gr 階梯が立つ海域の固有名
**SAKURA** の命名を記録する。第二に、Gr4 完遂 gate 5項を閉じる後続カード
6枚(G-111〜G-116)を、義務の全数拾い出し(§3)・カード別設計(§4)・
ラインナップ全体の整合性監査(§5)まで詰めて定義する。第三に、Gr 系列の
成果を束ねる SAKURA 論文の構成裁定の素描を固定する(§8)。カードをバラで
レビューすると全体の被覆漏れが検出できないため、**全体整合は本ノートで
一度に設計し、義務台帳と担当対応は起票時に G-116 カード本文へ正本転記
する**(本ノートは Tier 4 の考察ノートであり拘束力を持たない — 完了判定の
正本は常にカード側に置く。§6)。将来の statement はすべて未証明の
candidate であり、カードの起票・昇格・採否はユーザー裁定に従う。
lifecycle の経緯(PR・Issue・cycle 履歴)は各 report と tracking Issue を
正本とし、本ノートには持ち込まない。

## 要旨

1. Gr 階梯(Gr0–Gr4、n1001 §3.5)が立つ海域の固有名を **SAKURA** と定める。
   説明名は **Sea of Coherent Readings**。命名体系は山頂の呼び名 SHIGURE
   と同じ register(季語の大文字ローマ字+数学の像を写す情景+英語
   backronym)の拡張である。
2. 命名の証明根拠は範囲併記で固定する — **開花宣言** = G-110 完遂
   (Gr2–Gr3 の証明+Gr4 exact-bottom 第一手。Gr0–Gr1 は statement 化段で
   あり達成 = 文書固定)、**満開** = Gr4 capstone 完遂(正式名は
   「Gr4 達成記録」— §7)。開花と満開の二段観測に倣い、G-109 の Gr3
   記録様式(範囲併記)を命名側にも適用する。
3. Gr4 完遂義務は G-110 カードと n1005 §4.3 から**全数拾い出して義務台帳
   O1–O20 に固定**した(§3)。域外(Gr4 に含めない隣接義務)も明示列挙
   し、capstone の範囲併記の正本とする。
4. 6枚の設計は §4 で固定する — 6枚共通の定型項目ブロック、各カードの
   責務(担当義務)、target theorem 骨格、錨(実在・実型を突合済みの
   reviewed 宣言)、供給契約、リスク、failure 骨格。**Lean 実査の要点:
   `DiagnosticConservative` と `ObProblem` 段は Lean に不在であり、
   G-113 / G-115 の新設建設義務である(`ObProblem` は AG 数学本文にも
   語が無く、class の Lean 指示対象は起票前の裁定事項)**。
5. 整合性監査(§5)で被覆行列(義務の全域・一意な担当割当)、重複防止の
   判定線5本、語彙正本規則、universe 設計規則、改訂伝播 DAG を固定する。
   G-116 capstone が義務台帳との突合の上で Gr4 達成を記録する(§7)。
6. SAKURA 論文の構成裁定の素描(§8): Foundation / Main 二階建て、中心
   図表 = 達成階梯対応表(G-116 成果物として義務化)、統一 statement
   candidate、差分表の充填先。**論文Bとの関係は裁定済み — SAKURA 論文は
   論文B「連合する読み」と同一の論文の現行版であり、旧計画は拘束
   しない**。

## 参照

**正本**(事実関係の判定基準):

- [G-110 カード](../../research/goals/G-110-aat-doctrine-fiber-product.md)
  (Gr4 完遂 gate 5項・(D) full-domain 移管・(B) universe 契約・frontier
  の正本)
- [G-110 report](../../research/reports/G-110-aat-doctrine-fiber-product.md)
  (完了判定 = `target-theorem-proved`)
- [G-109 カード](../../research/goals/G-109-aat-cross-stage-coherence.md)
  (Gr3 達成記録と範囲併記の様式、pseudofunctor 塔と frontier)
- [G-101 カード](../../research/goals/G-101-aat-atom-foundation.md)
  (Gr2 の証明対象 — 階梯対応表で遡及記載する。§8)
- Lean reviewed artifact(`research/lean/ResearchLean/AG/` 配下の
  `DoctrineFiberProduct` / `CrossStageCoherence` / `GeometryTransport` /
  `TransportCoherence` / `AtomFoundation`。§4 の錨は 2026-08-25 に
  宣言名と実型を突合済み)

**上流考察ノート**(定義・分割の初出。正本ではない):

- [n1001](n1001_atom_is_all_you_need_discussion.md)(§3.3 塔、§3.5
  達成階梯 Gr0–Gr4「相対的視点の全操作が閉じる」、論文ロードマップ)
- [n1004](n1004_aat_denotational_semantics_of_architecture.md)(§10
  SHIGURE の呼び名と backronym の初出、§11 研究プログラム命名記録)
- [n1005](n1005_aat_semantic_geometry_route_after_g107.md)(§4.3
  五層分解と独立 gate 分割、§5 隊列、§7 論文B「連合する読み」)
- [n1006](n1006_aat_atlas_reinforcement_plan.md)(Atlas 補強計画 —
  着手条件が Gr4 完了。論文構成裁定(二階建て・差分表)の様式前例)

## §1 SAKURA — 海域の命名記録

**命名対象**: Gr 階梯が立つ海域。G-106 / G-108 / G-109 / G-110 が渡った
水域であり、後続6枚が Gr4 達成記録まで渡り切る。

- 固有名: **SAKURA**。表記は大文字ローマ字(SHIGURE と同 register)。
  日本語文中は「SAKURA 海域」と書く。
- 説明名(英名): **Sea of Coherent Readings**。内容名として固有名と併用
  し、SAKURA 論文(§8 — 論文B「連合する読み」の現行版)の英題候補を
  兼ねる。
- backronym: **Semantic Ascent through Kartesian Universality and
  Relative Alignment**。K 綴りは backronym 上の意匠(cartesian の K
  転写)である。Ascent = 上昇(登路と海面)、Kartesian Universality =
  fiber product の普遍性と carrier 大域 cartesian lift(G-110 (A)(B))、
  Relative Alignment = 終対象を置かない相対原理と段横断整合(Gr3)。
  全語が証明済み内容に対応する。
- 命名日: 2026-08-25(G-110 完遂日)。

**情景**(SHIGURE の「片時雨 = descent 貼り合わせの写し絵」と同じ役割):

- 桜前線は列島を段階的に北上する。海域は上昇する海の一段であり、前線が
  届いた水域が咲く。Grothendieck が Récoltes et Semailles で語った
  「上昇する海(la mer qui monte)」への敬意は、人名でなく方法の像を
  経由して一段抽象化された形で残る。
- 開花の報は合格電報の言葉(サクラサク)と重なる。この体系では証明が
  立った時にだけ名が付くから、咲きは常に実である。
- 「満ちる」という動詞は潮と花に共有される。満ち潮と満開が同じ言葉で
  進行を刻む。
- 季節の弧: 晩春(SAKURA)から初冬(SHIGURE = 山頂)へ。命名体系
  そのものが登路の一年を刻み、後続の海域名にも季語の続きが自然に控える。
  次の海域の命名は、その海域の開花の時に行う。

**二段記録(範囲併記)**:

- **開花宣言** = G-110 完遂(2026-08-25)。証明根拠は **Gr2 の証明**
  (G-101)・**Gr3 の証明**(G-106+G-108+G-109 の三点セット、範囲は
  G-109 カードの記録に従う)・**Gr4 exact-bottom 第一手**(G-110 — 有限
  presentation 付き(realization 像)底層射上の全域 lift exact-bottom・
  diagnostic-covariant subcalculus)。Gr0(比喩)と Gr1(statement 化)は
  定義上 theorem 非適格な段であり、その達成は文書固定である(n1001
  §3.5)。各段の記録正本の所在は達成階梯対応表(§8)で固定し、Gr2 の
  正本行は G-116 の達成記録時に遡及記載する。
- **満開** = G-116 capstone 完遂。正式名は「Gr4 達成記録」であり、成立
  条件は §7 に置く(「満開」「開花」は本節の命名記録と outreach の愛称
  併記に限って使い、台帳・カード・判定条件の正式名には使わない)。

**運用**:

- outreach で SAKURA を使うときは Gr 階梯の経緯を一段添える(Atlas 命名の
  運用と同型)。
- 航海記事は海域の固有名を記さない方針を維持する。
- **論文での使用**: 原稿本文は説明名 Sea of Coherent Readings と系列の
  正式記述(G-106〜G-116 の theorem 名)を使い、SAKURA は序文で一度だけ
  標語として置く(n1001 の「Atom Is All You Need は序文で一度」の使い
  分け前例に従う。題名への採否は執筆時のユーザー裁定)。
- **情景の使用域**: 論文・英語 outreach で使う情景は桜前線(段階的到達 =
  階梯)のみとする。合格電報・「満ちる」の語共有・俗語への内蔵反論
  (開花 = 完了判定)は和文 outreach 専用とする。

**衝突調査(2026-08-25)**: 数学圏に SAKURA を冠する定理・予想は検索で
確認されない。近接分野では暗号の Sakura(tree hashing の coding)と
サイドチャネル評価ボード SAKURA-G / X、国内技術圏にさくらインターネット・
サクラエディタがあるが、いずれも海域名の使用域と重ならない軟衝突である。
追加調査: (a) 説明名 Sea of Coherent Readings は完全一致の既存名が確認
されない(近接ヒットは海洋物理の sea-level coherence 等の別分野のみ)。
(b) backronym の Semantic Ascent は Quine の確立術語(意味論的上昇)と
語が重なる — 分野が異なる軟衝突であり、論文では backronym を展開しないか
脚注で区別する。(c) 海の像は Vakil の教科書題 The Rising Sea(la mer qui
monte 由来)と系譜を共有する — 衝突ではなく敬意の系譜として明示処理する
(だからこそ海域の固有名には rising sea 系の語を使わない)。(d) 内部
命名空間: SAGA(修復の意味論の定理系列名)と SAKURA(Gr 階梯の海域名)は
役割が異なる — outreach ではこの判別文を添える。

## §2 Gr4 完遂 gate(正本の整列)

正本は G-110 カード program context。本節は番号の整列のみを行う。

- **gate (i)**: 全 semantic exact-bottom への coverage 拡張と全域作用・
  分類+(D) 診断 base change の full-domain 化(source-fiber incidence
  資格の解除 = global / indexed base-change schema の建設)。
- **gate (ii)**: refinement 系統(`RefinementDoctrineHom` の圏化と
  refinement base change)。
- **gate (iii)**: 上段(`GeomRead` / `ObProblem`)への base-change lift
  (Gr3 段横断輸送への接続 bridge)。
- **gate (iv)**: IsIso 水準の Beck–Chevalley exchange-failure の存否決定
  (存否は未決定の問い。本 sector と refinement / 上段 regime を含む
  設定で決定する)。
- **gate (v)**: 診断保守性・反射・orbit exactness の分類。

## §3 義務台帳 — Gr4 完遂義務の全数拾い出し

拾い出しの出典は次の4系統を全数走査した: (a) G-110 カード program
context の gate 5項、(b) G-110 カード (B) の「Gr4 gate 第一項に残る
数学的義務」条項、(c) G-110 カードの改訂裁定による移管文((C) の gate
第四項移管・(D) の full-domain = 第一項/保守性系 = 第五項移管)、
(d) G-110 カード frontier 節の gate 指定項目と n1005 §4.3 (D) の独立
gate 文。義務は O 番号で固定し、担当カードは §4、被覆の全域・一意性は
§5 で監査する。

| id | 義務 | 出典 | 担当 |
|---|---|---|---|
| O1 | global / indexed base-change schema の建設(全 `ExtractionInstance` 上の base 作用) | gate (i)・(B) 条項 | G-111 |
| O2 | 各固定 carrier 内の全 package に対する cocartesian 保存 lift | (B) 条項 | G-111 |
| O3 | 実 BC 経路との制限比較(incidence 資格付き部分域上で G-110 の direct / via-base 経路と一致) | gate (i)・(B) 条項 | G-111 |
| O4 | (D) の full-domain 化 = source-fiber incidence 資格の解除(indexed 版 (d1)–(d6)) | gate (i)・(D) 移管文 | G-111 |
| O5 | coverage 拡張第一段(有限 carrier・有限 Source 上の同型までの coverage) | gate (i)・frontier | G-112 |
| O6 | coverage 拡張第二段(sector 全域 — 成立か、成立域の特徴付けと反例かの決定) | gate (i)・frontier | G-112 |
| O7 | 全域作用・分類 = 左枝の読みで「全域 lift の realization 資格外への帰趨決定」(n1001 §3.5 の忠実転写) | gate (i) | G-112 |
| O8 | refinement 射の圏化(`RefinementDoctrineHom` を射とする圏構造) | gate (ii) | G-114 |
| O9 | refinement base change の帰趨決定と refinement 側 regime 型の建設 | gate (ii) | G-114 |
| O10 | `GeomRead` 段への base-change lift+Gr3 接続 bridge+上段 regime 型の建設 | gate (iii) | G-115 |
| O11 | `ObProblem` 段への base-change lift(class 構成は変更しない) | gate (iii) | G-115 |
| O12 | IsIso 水準 exchange-failure の存否決定(sector+refinement / 上段 regime を含む設定) | gate (iv)・(C) 移管文 | G-116 |
| O13 | `DiagnosticConservative` の定義と構造的生成 class の固定+十分性 theorem | gate (v)・n1005 §4.3 (D) | G-113 |
| O14 | target obstruction vanishing → source vanishing の反射 theorem(class 上) | gate (v) | G-113 |
| O15 | source reselection orbit の検出 theorem | gate (v) | G-113 |
| O16 | class 外で非零 obstruction が消える有限 witness(保守性の破れの実在) | gate (v) | G-113 |
| O17 | 診断 class の恒等・水平・垂直貼り合わせ閉性 | gate (v) | G-113 |
| O18 | 生成診断部分圏上の `Full` + `Faithful` 十分条件候補の statement 固定と生成 class との関係決定 | gate (v) | G-113 |
| O19 | Gr4 達成の範囲併記記録(義務台帳との突合+達成階梯対応表込み) | program context | G-116 |
| O20 | pointwise raw-defect reflection の分類(cochain 値水準の反射 — O14 の orbit / vanishing 水準とは別 statement) | (D) 移管文 | G-113 |

**台帳注記**:

- G-110 (D) の gate 第五項移管3項は O20(pointwise raw-defect
  reflection)・O15(source orbit の検出)・O14(vanishing 反射)に
  対応する — 移管義務の消滅なしをここで固定する。
- n1005 §4.3 (D) の「情報損失の分類」は O13(class 分類)と O16(破れの
  実在 = 情報損失の witness)が担う。
- **universe 注記**: O1・O2・O6・O7・O12 の universe 契約は F0 typing
  cycle で Lean の宇宙割当と型突合した上で確定する。symbolic universe で
  型不能と判明した場合は枝条件付き・endpoint 固定の契約へ**再表現**する
  (義務の削除ではない — G-110 (B) の枝条件付き universe 移送契約を設計
  前例とする)。

**域外リスト(Gr4 に含めない隣接義務 — capstone 範囲併記の正本)**:

- **carrier change(carrier `U` を動かす主張)**。Gr4 は底(doctrine)の
  取り替えであり、carrier(Atom の宇宙)軸は別軸である(G-110 claim
  boundary 筆頭の除外と G-109 frontier の明示を継承。下記 cross-universe
  reindexing とも別物)。係数軸は係数 base change カードが担う。
- 任意 package の cross-universe exact reindexing(G-110 (B) が「G-110
  にも Gr4 gate にも移管しない」と明示除外。O2 の固定 carrier 内量化とは
  別物)。
- (D) の `J_A` defect profile 枝(G-104 / G-107 語彙への拡張。係数 base
  change カードとの接続点 — G-110 frontier のまま)。
- G-109 (G) の core 押し出し `p` に沿う effectivity の保存・反射
  (G-109 frontier のまま。**O14 / O20 の診断反射とは別物** — O14 / O20
  は indexed BC 作用の target → source 方向、こちらは段射影 `p` の押し
  出し方向)。
- derived fiber product・bifibration 一般論・係数 base change(ℚ→R)・
  `ObProblem` 段の class 構成の変更・nerve / cover 接続(G-110 claim
  boundary の除外を継承)。
- 候補8(係数忠実性)・候補13(comonadicity)の引き受け先裁定
  (n1005 §4.4 — 係数 base change カード起草時の裁定事項)。

## §4 カード別設計 — 単責務6枚

**分割原理**: 一枚 = 一責務(gate (i) のみ schema 建設(診断・
cocartesian 側)と分類(lift・cartesian 側)の二枚に分ける)。gate 5項は
語彙が互いに異質であり、合併は statement の膨張を招く。単責務分割は
反証時の影響を一枚に局所化する(statement の conjunct 数が改訂コストと
相関するという運用実測 — 正本は各 tracking Issue)。以下の claim 骨格は
設計候補であり、conjunct の最終固定は各カードの起票・昇格レビューと F0
typing cycle で行う。錨に挙げた宣言は 2026-08-25 に Lean 木で実在と実型を
突合済み。

**6枚共通の定型項目ブロック(起票時に全カードへ複写する)**:

- `research mode`: `target-theorem`(6枚全て。G-116 の target theorem は
  O12 のみであり、達成記録 O19 は completion criteria+report 側の義務と
  する — 記録を theorem の conjunct にしない)。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `phase boundary criteria`: G-110 カードと同文(proved / refuted /
  checkpoint)。
- 二段 review gate: 標準 fixed-head `$review-pr`+completion 時の独立
  `$math-lean-review` 4査読(正本 = target-goal-contract.md。不変)。
- `claim boundary` 共通継承: 固定 carrier `U`・係数不変・終対象不導入・
  §3 域外リストの除外(carrier change 含む)。
- Lean 置き場所: 原則 `ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module(G-115 の上段接続は起票時に置き場所を固定)。既存 reviewed
  module は参照のみ。
- per-card 固有項目(core tension・rival・dullness filter 全文・
  portfolio constraint・material premise ledger・route integrity gate・
  anti-weakening rule)は起票時に各カードで書き、batch レビューの必須
  検査項目とする(§6)。

### G-111(仮 slug: `G-111-aat-indexed-base-change-schema`)

- **責務**: O1–O4。indexed / global base-change schema の建設と (D) の
  full-domain 化。
- **claim 骨格**: (a) 全 `ExtractionInstance` 上の base 作用を持つ
  indexed schema の定義(authored data は base 作用の生成データのみ —
  結論相当の certificate field 禁止は G-110 route gate を継承)、
  (b) 各固定 carrier 内の全 package に対する cocartesian 保存 lift、
  (c) 制限比較 theorem — **incidence 資格付き部分域上で**、indexed 作用の
  pointed pullback square への制限が G-110 の実 BC 二経路(direct /
  via-base)と一致する(現行二経路の型は incidence を引数に取るため、
  資格なし全域での一致は型に載らない — 資格の解除は (d) の新経路が担い、
  この分界を statement で固定する)、(d) incidence 資格なしの
  full-domain (d1)–(d6)(interpretation・endpoint 準同型・transported
  data・mapped reselection・coherence 保存・vanishing 保存)、
  (e) named finite nonvacuity(G-110 witness の indexed 昇格 — 初期
  defect 非恒等+reselection 非恒等)。
- **錨(ambient-boundary 予定)**:
  `no_universalBCDiagnosticSourceFiberIncidence`
  (`DoctrineFiberProduct/BCDiagnosticSourceFiberNoGoWitnesses.lean` —
  役割は「incidence 資格の解除が普遍生成では不可能なことを確定する範囲
  標識」。要件本体は G-110 カード正本から取る)、
  `transportObstructionVanishes_map` / `mapEdgeReselection`
  (`BCDiagnosticVanishingPreservation.lean`)、
  `CoreFiberFunctorDefectCochain` 系
  (`BCDiagnosticBaseChangeAutomorphism.lean` — 全域側の既存 seed 型:
  vertexwise core-fiber functor 族)、G-101 opcartesian 輸送。
- **供給契約**: G-113 の量化域(full-domain indexed action)、G-112 の
  作用面の基盤、G-116 の記録。**G-113 は G-111 の schema 型を再定義
  しない**(語彙正本規則、§5)。
- **リスク / dullness 骨格**: schema が pointed square 族の再包装に堕ちる
  経路(no-go theorem が排除した普遍生成の逆流)、base 作用を supplied
  certificate で受ける経路、制限比較 (c) の定義展開放電。**edge 適合
  データの資格**: full-domain の coherence 保存は現行の単一 functor 関手
  性証明では成立せず、vertexwise 族の edge 適合(naturality)データを
  要する — これを authored 生成データと結論相当 certificate のどちらに
  分類するかの資格条項を F0 前に固定する。universe 義務は F0 で型突合
  してから台帳固定(§3 universe 注記)。
- **failure 骨格**: schema の型不能は `goal-defect`、(d) の反例構成は
  中心 conjunct 反証 = `target-refuted`(fail-closed、改訂は人間裁定)。

### G-112(仮 slug: `G-112-aat-exact-bottom-coverage`)

- **責務**: O5–O7。coverage 拡張と全域分類(cartesian 側)。
- **claim 骨格**: (a) 第一段 coverage theorem — 有限 carrier・有限
  Source 上の全 semantic exact-bottom 射が同型まで realization 像に入る
  (G-110 frontier の第一段)、(b) 第二段 = sector 全域の帰趨決定 —
  全域 coverage theorem または「成立域の特徴付け+像外反例」の**二枝
  disjunction 単一命題**(G-110 (B) の分岐固定様式)。**設計事実**:
  (s1) の有限 Source 固定により、無限 Source を端点に持つ semantic 射は
  原理的に像外であり、負枝が構造的に近い。したがって負枝は cardinality
  反例だけでは放電と数えず、**成立域の特徴付け述語に G-110 `H_cart` と
  同水準の資格条項**(探索前固定の条件言語・結論非参照・同型不変性・
  閉性)を課す — 「realization 像の定義の言い換え」述語は資格違反と
  する。正枝の量化域(有限 Source 制限の有無)は起票時の裁定事項、
  (c) 全域 lift の帰趨 — G-110 左枝(全域 strong cartesian lift)の
  realization 資格外への拡張成立、または成立域の特徴付け+反例。
  **計上規律**: O6 正枝確定時に O7 が左枝定理の同型輸送の系として従う
  場合、独立放電と数えず系として記録する、(d) 拡張域での id / comp /
  pullback / pasting 閉性。
- **universe 予告**: 反例枝の witness は per-universe 固定または枝条件
  付き endpoint 契約で立てる(無限 carrier 反例は有限 fixture の内部
  生成 lift による universe 移送が使えず、cross-universe reindexing は
  域外のため — §3 universe 注記の適用第一号)。
- **錨**: `GlobalCartesianLift` / `CartesianRegime` /
  `cartesianRegimeOfDisjunction`
  (`DoctrineFiberProduct/CartesianRegimeSchema.lean`・
  `CartesianBranchArtifact.lean`)、`cartesianLiftNonexistence_isEmpty`
  (`CartesianBranch.lean`)、presentation 閉性 constructor 4種、
  `FiniteModel`(witness 計算)。
- **供給契約**: G-116 の範囲併記(coverage 到達段と確定枝の記録)。
  G-112 の分類結果は G-113 / G-114 / G-115 の量化域を変更しない(各
  カードは G-110 固定の realization 付き入力上で立つ — 並走可能性、§5
  依存 DAG)。
- **リスク / dullness 骨格**: (b) 負枝の言い換え述語(上記資格条項で
  排除)、cardinality 反例のみの放電、第一段 coverage の単一 fixture
  列挙代替。
- **failure 骨格**: (a) の反例は中心 conjunct 反証 = `target-refuted`。
  (b)(c) は二枝 disjunction なのでどちらの枝も成功、両枝とも閉じない
  場合は `target-blocked`。

### G-113(仮 slug: `G-113-aat-diagnostic-conservativity`)

- **責務**: O13–O18・O20。診断保守性・反射・orbit exactness の分類。
- **claim 骨格**: (a) **`DiagnosticConservative` の新設定義**(Lean 不在を
  実査確認済み — G-111 の full-domain indexed action 上の述語として本
  カードが建設する)、(b) 構造的生成 class の固定と十分性 theorem
  (class は探索前固定の構造条件で立て、結論参照を禁じる — G-110
  `H_cart` 資格条項の様式)、(c) 反射 theorem — class 上で target
  obstruction vanishing → source vanishing(**非自明性の根拠**: (d2)
  endpoint 群準同型は一般に非単射であり、G-110 の無条件 forward
  covariance からは逆向きが従わない — この根拠を statement 側に一文
  固定する)、(d) orbit 検出 theorem — source reselection orbit の非自明
  性が target で検出される、(e) **pointwise raw-defect reflection の分類
  (O20)** — cochain 値水準の反射が成立する class の固定または反例
  (O14 の orbit / vanishing 水準とは別 statement として立てる)、
  (f) class 外 witness — class に入らない作用で非零 obstruction が消える
  有限 witness(保守性の破れの実在 = class 制限の非空虚性)、(g) **class
  内 named nonvacuity witness** — 非恒等 defect・非恒等 reselection・非
  可逆成分を含む class 成員上で反射・検出が実発火する有限 witness(class
  が空・退化でも (b)(c)(d) が vacuous に立つ経路の排除)、(h) 診断 class
  の恒等・水平・垂直貼り合わせ閉性、(i) 生成診断部分圏上の `Full` +
  `Faithful` 十分条件候補の statement 固定と、生成 class との関係(含意・
  同値・反例)の決定。
- **錨**: G-111 indexed schema(依存 — 量化域)、`InReselectionOrbit`
  (`TransportCoherence/FinitePresentation.lean`)、
  `CoreFiberFunctorDefectCochain` 系
  (`BCDiagnosticBaseChangeAutomorphism.lean`)。
- **供給契約**: G-116 の記録。`DiagnosticConservative` の命名は本カード
  専属(§5 語彙正本規則)。
- **リスク / dullness 骨格**: 反射 (c) を可逆 fixture(全成分同型)だけで
  発火させる経路、class を「conservative と同値」の述語で立てる経路
  (結論の埋め込み)、(f) を空診断図式で満たす経路。**O14 / O20 の反射は
  G-109 effectivity 反射(域外)と別物** — この分界を statement に明記
  する(§5 判定線)。
- **failure 骨格**: (c)(d)(e) の反証は `target-refuted`(fail-closed)。
  (f) が原理的に不能(保守性が full-domain で無条件成立し class 制限が
  空虚)と定理化された場合も、その定理を成果として `target-refuted` と
  する。(i) は決定がどちらでも成功。

### G-114(仮 slug: `G-114-aat-refinement-base-change`)

- **責務**: O8–O9。refinement 系統。
- **claim 骨格**: (a) refinement 圏の構成 — `RefinementDoctrineHom`
  (`AtomFoundation/Doctrine.lean` に実在確認済み)を射とする圏構造
  (恒等・合成・結合律)と、**`Doct_U` からの比較 functor
  `Doct_U ⥤ Refin_U`**(exact hom を refinement として埋める方向。逆
  方向は `RefinementDoctrineHom` が `extraction_forward` のみを持ち
  `finiteExtractionRefinement_not_reflecting` が反射不能を定理化済みの
  ため型に載らない — 方向をこの形で固定する)、(b) refinement base
  change の帰趨決定 — **二枝 disjunction 単一命題**: 「(A) の fiber
  product が refinement 射を pullback で安定に持ち上げ、refinement に
  沿った BC 比較射と **mate 比較が定義される regime 型(reindexing・
  随伴相当の装置)**が建設できる」または「refinement pullback / regime
  の退化定理」。refinement 射は lax であり G-101 opcartesian 輸送の適用
  外のため、正枝を無条件には主張しない、(c) 非退化 witness(恒等でない
  refinement 射の pullback が非自明に立つ有限 fixture —
  `finiteExtractionRefinement` 系が素材)。
- **錨**: `RefinementDoctrineHom` / `finiteExtractionRefinement` 系
  (`AtomFoundation/Doctrine.lean`・`RefinementObstruction.lean`)、
  G-110 (A) fiber product 構成・`pointedPullback_isPullback`
  (`DoctrineFiberProduct/PointedDoctrinePullback.lean`)、presentation
  閉性 constructor。
- **供給契約**: **G-116 gate (iv) の refinement regime 型**(mate が
  定義される装置、または退化定理という帰趨)。G-116 は regime を新設
  建設できないため、この供給は成果物形式の義務である。
- **リスク / dullness 骨格**: 圏化が「hom の再ラベル」に堕ちる経路
  (合成の非自明性 witness を要求)、refinement pullback が恒等成分で
  vacuous に立つ経路。
- **failure 骨格**: (b) は二枝 disjunction なのでどちらの枝も成功
  (退化定理も帰趨確定として §7 条件1を満たす)。両枝とも閉じない場合は
  `target-blocked`。

### G-115(仮 slug: `G-115-aat-upper-stage-lift`)

- **責務**: O10–O11。上段への base-change lift と Gr3 接続 bridge。
- **claim 骨格**: (a) `GeomRead` 段 lift — pointed pullback square の BC
  構造(引き戻し・canonical mate)を geometry 段 fiber へ持ち上げ、
  G-109 pseudofunctor package(compositor / unitor・pseudonatural
  compatibility)と両立する形で段射影と可換にする。**上段 regime 型
  (G-116 が消費する mate 比較の型)を成果物形式に含める**、(b) Gr3
  接続 bridge — 持ち上げた BC 作用と G-109 の段横断輸送・G-110 の
  G-106 / G-109 coherence bridge との整合 theorem、(c) **`ObProblem`
  段** — Lean 実査の結果、`ObProblem` の語は research 木・Formal 木・
  AG 数学本文のいずれにも無く、塔語彙の初出は n1001 §3.3 である。class
  割当の Lean 指示対象は**起票前の裁定事項**とする: (i) Formal 木の
  障害 class(`H^1(X, Ob_U)` 系 — 二木 bridge 込みとなり最小でない)、
  (ii) research 木の orbit / defect 語彙上の最小 class 読み出し
  interface(推奨 — AG 本文の class との対応注記を義務化する)。裁定
  後、その interface 上への BC lift の naturality を固定する。class
  構成自体は変更しない(G-110 claim boundary の継承)、(d) 非退化発火
  witness — 非自明 geometry fiber 上の発火(G-108 系 fixture 資産が
  素材)に加え、**`ObProblem` interface 上でも非恒等 class 読み出しが
  BC lift で実際に動く fixture** を要求する(定数読み出しの vacuous
  naturality の排除)。
- **錨**: `CoreFiber` / `coreFiberTransportFunctor`
  (`CrossStageCoherence/CorePseudofunctor.lean`)、G-108
  `GeomReadCategory`(通称 GeomRead_U)/ `geomTransportAlongHom` 系
  (`GeometryTransport/`)、G-110 pullback reindexing functor・
  `pointedPullback_isPullback`。
- **供給契約**: G-116 gate (iv) の上段 regime 型。`ObProblem` interface
  の命名は本カード専属。
- **リスク / dullness 骨格**: lift を base equality 一本で代用する経路、
  離散段(`ExtInst -> Doct`)での vacuous 発火、`ObProblem` interface に
  class 構成の変更を紛れ込ませる経路、定数 class 読み出しでの vacuous
  naturality。
- **failure 骨格**: `ObProblem` interface の Lean 建設が型不能なら
  `target-blocked`(gate (iii) の縮小 = `ObProblem` 部分の分離は人間
  裁定であり、自動 weakening をしない)。

### G-116(仮 slug: `G-116-aat-gr4-capstone`)

- **責務**: O12(target theorem)・O19(completion criteria+report
  義務)。capstone。
- **target theorem 骨格(O12 のみ)**: IsIso 水準 Beck–Chevalley
  exchange-failure の存否決定 — **「全同型定理」または「¬IsIso の具体
  反例」の二枝 disjunction 単一命題**(G-110 (B) 様式: 排他性は反例が
  供給、網羅性は主張しない)。量化域 = G-110 sector+G-114 が供給する
  refinement regime 型+G-115 が供給する上段 regime 型(**capstone は
  単責務規律上 regime を新設建設しない** — 供給された成果物形式から
  組めない場合は起票前に gate (iv) の regime の意味の裁定へ差し戻す)。
  **量化域は authored datum 付き lax square を含める** — G-110 sector の
  pullback square 上の mate 同型は証明済みの正例(TargetTheorem の
  canonical mate exactness)であり、存否の未決部分は lax square と新
  regime 側にある。負例枝 witness の居住域をそこに限定し、既決正例の
  再包装(pullback-only)による正枝放電を dullness で排除する。上段
  regime の第二 universe(`GeomReadCategory` は二 universe)は端点固定と
  し、方式は F0 で確定する。
- **completion criteria+report 義務(O19)**: §7 の成立条件に従う
  Gr4 達成の範囲併記記録。**達成階梯対応表**(§8 — Gr0–Gr4 ↔ theorem
  package ↔ Lean 宣言錨 ↔ 記録正本の所在 ↔ 範囲限定、の5列。Gr2 =
  G-101 の遡及記載を含む)を report 成果物として義務化する。
- **錨**: G-111〜G-115 の final reviewed head(完遂後に固定)、G-110
  `MateCoherentRel` 正負対と TargetTheorem の mate exactness(既決正例の
  分界 — 本カードの存否決定はその未決部分の決定である)。
- **供給契約**: なし(終端)。
- **リスク / dullness 骨格**: 既決正例の再包装・退化 square(成分恒等・
  診断恒零)・vacuous な新 regime による「全同型」枝の放電、達成記録が
  義務台帳との突合を欠いて宣言だけで立つ経路。
- **failure 骨格**: 両枝とも閉じない場合は `target-blocked` であり
  **Gr4 は未達のまま**(記録だけ先行させない)。先行カードに帰趨未確定
  がある間は昇格しない(§5 依存 DAG)。

## §5 整合性監査 — ラインナップ全体

**被覆行列**: O1–O20 の各義務はちょうど一枚のカードが担当する(§3 の
担当列 — 義務からカードへの全域・一意な担当割当)。重複なし・漏れなし。
gate との対応 — gate (i) = O1–O7(G-111+G-112)、gate (ii) = O8–O9
(G-114)、gate (iii) = O10–O11(G-115)、gate (iv) = O12(G-116)、
gate (v) = O13–O18・O20(G-113)、達成記録 = O19(G-116)。

**重複防止の判定線(5本)**:

1. **G-111 / G-113**: G-111 = indexed 作用の存在と順方向性質(共変・
   経路整合)、G-113 = 同じ作用の逆方向性質(保守・反射・検出)。
   G-113 は G-111 の schema 型を再定義せず量化域として消費する。
2. **G-111 / G-112**: G-111 = 診断・輸送側(cocartesian 保存 lift =
   O2 を含む)、G-112 = cartesian lift・coverage 側。**cocartesian
   (O2)と strong cartesian(O7)は別の lift であり、混同は義務の
   二重計上・脱落の両リスクを持つ** — カード本文で相互参照する。
3. **G-113 の反射 / G-109 effectivity 反射**: 前者 = indexed BC 作用の
   target → source 方向(O14・O20)、後者 = 段射影 `p` の押し出し方向
   (域外・G-109 frontier のまま)。G-113 statement に分界を明記する。
4. **G-115 / G-116**: G-115 は regime 型(上段の BC 構造)を建設するが
   IsIso を主張しない。存否決定は G-116 専属(G-110 が `¬IsIso` を負例
   軸に採らなかった分界の継承)。
5. **既決 / 未決**: G-110 sector の pullback square 上の mate 同型は
   証明済みの正例であり、G-116 の存否決定の対象は lax square と
   refinement / 上段 regime に限る — 既決正例の再包装を全カードの
   dullness で排除する。

**語彙正本規則**: 6枚は G-101 / G-106 / G-108 / G-109 / G-110 の
reviewed 宣言を `ambient-boundary` として参照のみとし、再定義・改変を
しない(G-110 ledger の様式)。**錨は現行 head に実在する宣言名の現在形
参照のみとする** — 除去済み宣言・経緯付き参照(「旧〜」「履歴
artifact」)はカードに書かず、経緯は tracking Issue 側に置く。様式の
参照は「同型の様式(宣言名)」と書き、物語を持ち込まない。新設語彙の
命名権は単責務に従い一枚に専属させる — indexed schema 型 = G-111、
`DiagnosticConservative` = G-113、refinement 圏 = G-114、`ObProblem`
interface = G-115。命名の重複・分散を batch レビューで検査する。

**universe 設計規則(全カード共通)**: universe-polymorphic な義務は、
Lean の宇宙割当と F0 typing cycle で型突合してから台帳に固定する。
symbolic universe での成立が原理的に型不能な要求は台帳に置かず、枝条件
付き・endpoint 固定の契約で立てる(G-110 (B) の枝条件付き universe
移送契約を設計前例とする)。§3 の universe 注記(O1・O2・O6・O7・O12)が
この規則の適用対象を先に指名する — 台帳固定が型突合に先行する事故の
再演をここで防ぐ。

**依存 DAG と伝播規定**:

```
G-110 ──→ G-111 ──→ G-112
               └──→ G-113
G-110 ──────→ G-114 ──┐
G-110 / G-109 / G-108 → G-115 ─┴→ G-116(存否決定+達成記録)
```

- G-114 / G-115 は6枚の中ではどのカードにも依存せず、G-111 系と並走
  可能である(外部依存は G-114 = G-110、G-115 = G-110 に加え G-109 /
  G-108 の reviewed artifact)。G-112 の分類結果は他カードの量化域を
  変更しない(G-110 固定の realization 付き入力上で立つ)。
- 上流の statement 改訂時、依存する下流 draft は差し戻して再固定する
  (G-109 の伝播規定と同型)。G-111 改訂 → G-112 / G-113 へ、G-108 /
  G-109 / G-110 の改訂 → 参照カードへ、**G-111〜G-115 のいずれの改訂も
  G-116 へ伝播する**(達成記録の突合対象と範囲併記の内容が動くため)。
- G-116 は全カードの帰趨確定後にのみ昇格する(達成記録の突合が義務の
  ため)。

## §6 隊列運用

- **起票**: draft 6枚を一括 batch PR で起票する(Gr3/Gr4 カード3枚
  draft の batch 起票と同型)。G-110 完遂済みで錨 head は固定済みであり、
  起票条件は満たされている。**正本の所在**: 義務台帳(§3)と担当対応は
  起票時に **G-116 カード本文(達成記録の completion criteria)へ正本
  転記**し、batch PR 本文にも複写する。本ノートは Tier 4 の source note
  として参照に降格する(拘束力のないメモを完了判定の正本にしない)。
  **batch PR のレビュー対象は「カード6枚+転記済み義務台帳との突合」**
  (義務の脱落・二重計上・域外混入・共通定型ブロックの複写一致・per-card
  固有項目の充足を検査)であり、全体整合の検査はこの一回に集約する。
- **昇格**: 一枚ずつ、G-111 から。昇格時は敵対レビュー往復を経る。
  昇格順の推奨は依存 DAG に従い G-111 → (G-112 | G-113 | G-114 |
  G-115 は並走裁定) → G-116。
- **昇格レビューの右サイズ化(提案 — G-111 昇格前に正式裁定)**: 全体
  整合を batch レビューで先に閉じるため、昇格レビューはカード内部
  (statement の型・資格条項・witness 形)に限定できる。gate カードは
  reviewed artifact への錨止めを主とし、新設 schema の発明を statement
  に持ち込まない設計とする。この前提の下でレビュー上限を Claude
  3レーン+Codex 2巡とし、型細部は F0 typing cycle へ移す。**この上限は
  昇格レビュー限定であり、completion 側の二段 gate(target-goal-
  contract.md の標準 review+独立 `$math-lean-review`)は不変である**。
- **後続接続**: Gr4 達成記録は Atlas 補強論文(n1006)の着手条件を解く。
  SAKURA 論文(§8)との執筆順序はその時点のユーザー裁定。

## §7 Gr4 達成記録の成立条件 — Gr 系列の完了

**解釈規約**: Gr4 達成とは、**gate 全項の帰趨が定理で確定していること**を
いう(正枝である必要はない — n1001 §3.5「相対的視点の全操作が閉じる」の
本ノートでの読み。二枝 disjunction 義務はどちらの枝の確定も帰趨確定で
ある)。ただし記録の表現は exact-bottom 全域の分類と読める形を避け
(G-110 completion criteria の慎重条項の継承)、確定枝を全て併記する。
**裁定事項**: O6・O7・O12 がすべて反例枝で確定した場合の記録の見出し語
(「Gr4 達成」か「Gr4 帰趨決定+成立域限定」か)は、確定枝が出揃った
時点のユーザー裁定とする。

成立条件:

1. G-111〜G-115 が担当義務(O1–O11・O13–O18・O20)の帰趨を
   `target-theorem-proved` で確定している(二枝 disjunction 義務は
   どちらの枝でも成功 — G-114 (b) の退化定理も帰趨確定である)。義務は
   移管でのみ動かし、削除しない(G-110 の移管規律の継続)。
2. G-116 が O12 の存否をどちらかの枝で確定している。
3. G-116 が達成記録(O19)を完了している — 突合対象は O1–O11・
   O13–O18・O20(先行カードの fixed head・review 錨と突合)+O12
   (自己確定)。範囲併記は coverage の到達段(第一段 / 第二段)、
   O6 / O7 / O12・G-113 (i)・G-114 (b) の確定枝、§3 域外リスト
   (carrier change 含む)、達成階梯対応表(§8)を含む。

達成記録をもって Gr 階梯(Gr0–Gr4)は閉じる。以降の隊列(係数 base
change 方向)は n1005 §5 の後続 draft 候補に従い、次の海域の命名は §1 の
定めに従う。

## §8 SAKURA 論文 — 構成裁定の素描

Gr 系列(G-106 / G-108 / G-109 / G-110+後続6枚)の成果を束ねる論文の
構成裁定を素描する。様式前例は Atlas 補強計画(n1006)の論文構成裁定
(二階建て・差分表・最小成員 gate)。以下は candidate であり、正式裁定は
執筆 PRD 起草時にユーザーが行う。

- **問い(candidate、複数提示)**: (案1)「ソフトウェア意味論の底は
  どこまで相対化できるか — 底の取り替えの全操作(引き戻し・交換・診断
  輸送・貼り合わせ)は、どの範囲で定理として閉じるか」。(案2)「診断は
  base change に対して何を保存し、何を保存しないか — 保存の共変性と
  保守性の分類」。
- **構成 = Foundation / Main 二階建て**(n1006 §6 と同型):
  - Foundation(構成が主で失敗しえない層): G-101 圏・輸送 schema、
    G-106 障害語彙、G-108 塔上層、G-111 indexed schema、G-114 圏化、
    G-115 上段 interface。
  - Main(失敗しうる主張の層): G-109 障害合成と gluing、G-110 (A)–(E)
    (普遍性・左枝 lift・BC exactness と相対 canonicity・診断共変性・
    閉性)、G-112 coverage / 全域分類、G-113 保守性分類、G-116 存否
    決定。
- **中心図表 = 達成階梯対応表**(G-116 の report 成果物として義務化 —
  §4 G-116): 各段 Gr0–Gr4 ↔ theorem package ↔ Lean 宣言錨 ↔ 記録正本の
  所在 ↔ 範囲限定、の5列。Gr0–Gr1 は statement 化段(達成 = 文書固定、
  n1001 §3.5)、Gr2 = G-101(遡及記載)、Gr3 = G-109 記録、Gr4 = G-116
  記録。論文はこの表を骨格として階梯の主張を一枚で示す。
- **統一 statement candidate**: 「固定 carrier 上の doctrine 塔の相対
  base-change 帰趨確定定理(範囲併記付き)」の散文一本を Main の冒頭に
  置く。**O1–O20 の機械的 conjunction を単一 Lean 定理化する案は採ら
  ない**(義務台帳の定理化は防衛的過剰設計に収束するため)。見出し語
  (completeness / determination / classification)は確定枝を見て §7 の
  裁定と同時に選ぶ。
- **差分表の充填先(rival への肯定形の答え)**: 最近接一般論 = indexed /
  fibred category の base change(Grothendieck fibration・Bénabou)。
  差分は (1) 底が構文生成される doctrine 塔という具体対象への実装、
  (2) 診断障害理論(raw defect・reselection orbit・保守性分類)が base
  change と一体で輸送されること、(3) 全て Lean で固定されること、
  (4) 存否未決だった exchange-failure に決定を与えること。執筆時に
  n1006 §3 と同水準の差分表として充填する。
- **論文Bとの関係(裁定済み 2026-08-25)**: SAKURA 論文は論文B「連合
  する読み」(n1005 §7)と**同一の論文**であり、その現行版である。
  論文Bの旧計画(n1001 の問い・収録候補・ロードマップ上の位置)は
  **拘束しない** — 本節の構成裁定を正とし、旧計画の候補群は執筆 PRD
  起草時に採否を選び直す素材として扱う。Sea of Coherent Readings は
  同論文の英題候補を兼ねる(最終確定は執筆時)。
