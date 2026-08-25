# SAKURA 海域と Gr4 完了設計 — 命名記録と後続カード6枚の定義

本ノートは考察ノートである。新しい公理・定義・定理は導入せず、証明済み定理の
statement を変更しない。目的は二つある。第一に、Gr 階梯が立つ海域の固有名
**SAKURA** の命名を記録する。第二に、Gr4 完遂 gate 5項を閉じる後続カード
6枚(G-111〜G-116)を、義務の全数拾い出し(§3)・カード別設計(§4)・
ラインナップ全体の整合性監査(§5)まで詰めて定義する。カードをバラで
レビューすると全体の被覆漏れが検出できないため、**全体整合は本ノートで
一度に固定し、起票 batch PR のレビューは §5 の被覆行列との突合を必須
gate とする**。将来の statement はすべて未証明の candidate であり、
カードの起票・昇格・採否はユーザー裁定に従う。lifecycle の経緯
(PR・Issue・cycle 履歴)は各 report と tracking Issue を正本とし、
本ノートには持ち込まない。

## 要旨

1. Gr 階梯(Gr0–Gr4、n1001 §3.5)が立つ海域の固有名を **SAKURA** と定める。
   説明名は **Sea of Coherent Readings**。命名体系は山頂の呼び名 SHIGURE
   と同じ register(季語の大文字ローマ字+数学の像を写す情景+英語
   backronym)の拡張である。
2. 命名の証明根拠は範囲併記で固定する — **開花宣言** = G-110 完遂
   (Gr0–Gr3 の完全証明+Gr4 exact-bottom 第一手)、**満開** = Gr4
   capstone 完遂。開花と満開の二段観測に倣い、G-109 の Gr3 記録様式
   (範囲併記)を命名側にも適用する。
3. Gr4 完遂義務は G-110 カードと n1005 §4.3 から**全数拾い出して義務台帳
   O1–O19 に固定**した(§3)。域外(Gr4 に含めない隣接義務)も明示列挙
   し、capstone の範囲併記の正本とする。
4. 6枚の設計は §4 で固定する — 各カードの責務(担当義務)、target
   theorem 骨格、錨(実在確認済み reviewed 宣言)、供給契約、リスク、
   failure 骨格。**Lean 実査の要点: `DiagnosticConservative` と
   `ObProblem` 段は Lean に不在であり、G-113 / G-115 の新設建設義務で
   ある**。
5. 整合性監査(§5)で被覆行列(義務×カードの全単射)、重複防止の判定線
   4本、語彙正本規則、universe 設計規則、改訂伝播 DAG を固定する。
   G-116 capstone が義務台帳との突合の上で Gr4 達成 = SAKURA 満開を
   記録する(§7)。

## 参照

**正本**(事実関係の判定基準):

- [G-110 カード](../../research/goals/G-110-aat-doctrine-fiber-product.md)
  (Gr4 完遂 gate 5項・(D) full-domain 移管・(B) universe 契約・frontier
  の正本)
- [G-110 report](../../research/reports/G-110-aat-doctrine-fiber-product.md)
  (完了判定 = `target-theorem-proved`)
- [G-109 カード](../../research/goals/G-109-aat-cross-stage-coherence.md)
  (Gr3 達成記録と範囲併記の様式、pseudofunctor 塔と frontier)
- Lean reviewed artifact(`research/lean/ResearchLean/AG/` 配下の
  `DoctrineFiberProduct` / `CrossStageCoherence` / `GeometryTransport` /
  `TransportCoherence` / `AtomFoundation`。§4 の錨は 2026-08-25 に
  宣言名の実在を突合済み)

**上流考察ノート**(定義・分割の初出。正本ではない):

- [n1001](n1001_atom_is_all_you_need_discussion.md)(§3.3 塔、§3.5
  達成階梯 Gr0–Gr4「相対的視点の全操作が閉じる」)
- [n1004](n1004_aat_denotational_semantics_of_architecture.md)(§10
  SHIGURE の呼び名と backronym の初出、§11 研究プログラム命名記録)
- [n1005](n1005_aat_semantic_geometry_route_after_g107.md)(§4.3
  五層分解と独立 gate 分割、§5 隊列、§7 論文B「連合する読み」)
- [n1006](n1006_aat_atlas_reinforcement_plan.md)(Atlas 補強計画 —
  着手条件が Gr4 完了)

## §1 SAKURA — 海域の命名記録

**命名対象**: Gr 階梯が立つ海域。G-106 / G-108 / G-109 / G-110 が渡った
水域であり、後続6枚が満開まで渡り切る。

- 固有名: **SAKURA**。表記は大文字ローマ字(SHIGURE と同 register)。
  日本語文中は「SAKURA 海域」と書く。
- 説明名(英名): **Sea of Coherent Readings**。内容名として固有名と併用
  する(論文B「連合する読み」n1005 §7 と連動)。
- backronym: **Semantic Ascent through Kartesian Universality and
  Relative Alignment**。kartesian は fibration 文献の綴りを採る。
  Ascent = 上昇(登路と海面)、Kartesian Universality = fiber product の
  普遍性と carrier 大域 cartesian lift(G-110 (A)(B))、Relative
  Alignment = 終対象を置かない相対原理と段横断整合(Gr3)。全語が
  証明済み内容に対応する。
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

- **開花宣言** = G-110 完遂(2026-08-25)。証明根拠は Gr0–Gr3 の完全証明
  (Gr3 = G-106+G-108+G-109 の三点セット、範囲は G-109 カードの記録に
  従う)+Gr4 exact-bottom 第一手(G-110 — 有限 presentation 付き
  (realization 像)底層射上の全域 lift exact-bottom・diagnostic-covariant
  subcalculus)。
- **満開** = G-116 capstone 完遂(Gr4 達成記録)。満開の条件は §7。

**運用**:

- outreach で SAKURA を使うときは Gr 階梯の経緯を一段添える(Atlas 命名の
  運用と同型)。
- 航海記事は海域の固有名を記さない方針を維持する。
- 俗語の読みへの反論は体系が内蔵する(開花 = 完了判定)。

**衝突調査(2026-08-25)**: 数学圏に SAKURA を冠する定理・予想は検索で
確認されない。近接分野では暗号の Sakura(tree hashing の coding)と
サイドチャネル評価ボード SAKURA-G / X、国内技術圏にさくらインターネット・
サクラエディタがあるが、いずれも海域名の使用域と重ならない軟衝突である。

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
gate 文。義務は O 番号で固定し、担当カードは §4、被覆の全単射性は §5 で
監査する。

| id | 義務 | 出典 | 担当 |
|---|---|---|---|
| O1 | global / indexed base-change schema の建設(全 `ExtractionInstance` 上の base 作用) | gate (i)・(B) 条項 | G-111 |
| O2 | 各固定 carrier 内の全 package に対する cocartesian 保存 lift | (B) 条項 | G-111 |
| O3 | 実 BC 経路との制限比較(indexed 作用の pointed square 制限が G-110 の direct / via-base 経路と一致) | gate (i)・(B) 条項 | G-111 |
| O4 | (D) の full-domain 化 = source-fiber incidence 資格の解除(indexed 版 (d1)–(d6)) | gate (i)・(D) 移管文 | G-111 |
| O5 | coverage 拡張第一段(有限 carrier・有限 Source 上の同型までの coverage) | gate (i)・frontier | G-112 |
| O6 | coverage 拡張第二段(sector 全域 — 成立か、成立域の特徴付けと反例かの決定) | gate (i)・frontier | G-112 |
| O7 | 全域作用・分類 = 左枝の読みで「全域 lift の realization 資格外への帰趨決定」(n1001 §3.5 の忠実転写) | gate (i) | G-112 |
| O8 | refinement 射の圏化(`RefinementDoctrineHom` を射とする圏構造) | gate (ii) | G-114 |
| O9 | refinement base change((A) pullback との両立・refinement に沿った比較) | gate (ii) | G-114 |
| O10 | `GeomRead` 段への base-change lift+Gr3 接続 bridge | gate (iii) | G-115 |
| O11 | `ObProblem` 段への base-change lift(class 構成は変更しない) | gate (iii) | G-115 |
| O12 | IsIso 水準 exchange-failure の存否決定(sector+refinement / 上段 regime を含む設定) | gate (iv)・(C) 移管文 | G-116 |
| O13 | `DiagnosticConservative` の定義と構造的生成 class の固定+十分性 theorem | gate (v)・n1005 §4.3 (D) | G-113 |
| O14 | target vanishing → source vanishing の反射 theorem(class 上) | gate (v) | G-113 |
| O15 | source reselection orbit の検出 theorem | gate (v) | G-113 |
| O16 | class 外で非零 obstruction が消える有限 witness(保守性の破れの実在) | gate (v) | G-113 |
| O17 | 診断 class の恒等・水平・垂直貼り合わせ閉性 | gate (v) | G-113 |
| O18 | 生成診断部分圏上の `Full` + `Faithful` 十分条件候補の statement 固定と生成 class との関係決定 | gate (v) | G-113 |
| O19 | Gr4 達成の範囲併記記録(= SAKURA 満開。義務台帳との突合込み) | program context | G-116 |

**域外リスト(Gr4 に含めない隣接義務 — capstone 範囲併記の正本)**:

- 任意 package の cross-universe exact reindexing(G-110 (B) が「G-110
  にも Gr4 gate にも移管しない」と明示除外。O2 の固定 carrier 内量化とは
  別物)。
- (D) の `J_A` defect profile 枝(G-104 / G-107 語彙への拡張。係数 base
  change カードとの接続点 — G-110 frontier のまま)。
- G-109 (G) の core 押し出し `p` に沿う effectivity の保存・反射
  (G-109 frontier のまま。**O14 の診断反射とは別物** — O14 は indexed
  BC 作用の target → source 方向、こちらは段射影 `p` の押し出し方向)。
- derived fiber product・bifibration 一般論・係数 base change(ℚ→R)・
  `ObProblem` 段の class 構成の変更・nerve / cover 接続(G-110 claim
  boundary の除外を継承)。
- 候補8(係数忠実性)・候補13(comonadicity)の引き受け先裁定
  (n1005 §4.4 — 係数 base change カード起草時の裁定事項)。

## §4 カード別設計 — 単責務6枚

**分割原理**: 一枚 = 一責務(gate (i) のみ schema 建設(診断・
cocartesian 側)と分類(lift・cartesian 側)の二枚に分ける)。gate 5項は
語彙が互いに異質であり、合併は statement の膨張を招く。単責務分割は
反証時の影響を一枚に局所化する(statement の conjunct 数が cycle 数・
改訂回数と相関する実測: G-106 = 5 cycle から G-110 = 111 cycle まで)。
以下の claim 骨格は設計候補であり、conjunct の最終固定は各カードの起票・
昇格レビューと F0 typing cycle で行う。錨に挙げた宣言は 2026-08-25 に
Lean 木で実在を突合済み。

### G-111(仮 slug: `G-111-aat-indexed-base-change-schema`)

- **責務**: O1–O4。indexed / global base-change schema の建設と (D) の
  full-domain 化。
- **claim 骨格**: (a) 全 `ExtractionInstance` 上の base 作用を持つ
  indexed schema の定義(authored data は base 作用の生成データのみ —
  結論相当の certificate field 禁止は G-110 route gate を継承)、
  (b) 各固定 carrier 内の全 package に対する cocartesian 保存 lift、
  (c) 制限比較 theorem — indexed 作用を pointed pullback square に制限
  すると G-110 の実 BC 二経路(direct / via-base)と一致する、
  (d) incidence 資格なしの full-domain (d1)–(d6)(interpretation・
  endpoint 準同型・transported data・mapped reselection・coherence 保存・
  vanishing 保存)、(e) named finite nonvacuity(G-110 witness の
  indexed 昇格 — 初期 defect 非恒等+reselection 非恒等)。
- **錨(ambient-boundary 予定)**:
  `no_universalBCDiagnosticSourceFiberIncidence`
  (`DoctrineFiberProduct/BCDiagnosticSourceFiberNoGoWitnesses.lean` —
  現行 ordinary schema からの普遍生成不在を確定済み。**必要な indexed
  schema の形式要件を反面から特定する F0 の一次入力**)、
  `transportObstructionVanishes_map` / `mapEdgeReselection`
  (`BCDiagnosticVanishingPreservation.lean`)、G-101 opcartesian 輸送。
- **供給契約**: G-113 の量化域(full-domain indexed action)、G-112 の
  作用面の基盤、G-116 の記録。**G-113 は G-111 の schema 型を再定義
  しない**(語彙正本規則、§5)。
- **リスク / dullness 骨格**: schema が pointed square 族の再包装に堕ちる
  経路(no-go theorem が禁じた普遍生成の逆流)、base 作用を supplied
  certificate で受ける経路、制限比較 (c) の定義展開放電。universe 義務は
  F0 で Lean の宇宙割当と型突合してから台帳固定(§5 の設計規則)。
- **failure 骨格**: schema の型不能は `goal-defect`、(d) の反例構成は
  中心 conjunct 反証 = `target-refuted`(fail-closed、改訂は人間裁定)。

### G-112(仮 slug: `G-112-aat-exact-bottom-coverage`)

- **責務**: O5–O7。coverage 拡張と全域分類(cartesian 側)。
- **claim 骨格**: (a) 第一段 coverage theorem — 有限 carrier・有限
  Source 上の全 semantic exact-bottom 射が同型まで realization 像に入る
  (G-110 frontier の第一段。有限 carrier では全抽出述語が有限集合・全
  置換が有限 support という G-110 カードの観察が素材)、(b) 第二段 =
  sector 全域の帰趨決定 — 全域 coverage theorem または「成立域の特徴
  付け+像外反例」の**二枝 disjunction 単一命題**(G-110 (B) の分岐固定
  様式。無限 carrier 上の任意 semantic 射は有限 code を持つとは限らない
  ため、反例枝が生きている)、(c) 全域 lift の帰趨 — G-110 左枝(全域
  strong cartesian lift)の realization 資格外への拡張成立、または成立域
  の特徴付け+反例(「条件外入力の帰趨を決定する」の忠実転写)、
  (d) 拡張域での id / comp / pullback / pasting 閉性。
- **錨**: `GlobalCartesianLift` / `CartesianRegime` /
  `cartesianRegimeOfDisjunction`
  (`DoctrineFiberProduct/CartesianRegimeSchema.lean`・
  `CartesianBranchArtifact.lean`)、`cartesianLiftNonexistence_isEmpty`
  (`CartesianBranch.lean`)、presentation 閉性 constructor 4種、
  `FiniteModel`(witness 計算)。
- **供給契約**: G-116 の範囲併記(coverage 到達段の記録)。G-112 の
  分類結果は G-113 / G-114 / G-115 の量化域を変更しない(各カードは
  G-110 固定の realization 付き入力上で立つ — 分類の成立を待たない
  並走可能性、§5 依存 DAG)。
- **リスク / dullness 骨格**: (b) を「realization 像の定義の言い換え」で
  放電する経路(帰趨決定は像の外の入力に対する theorem を要求する)、
  第一段 coverage を単一 fixture の列挙で代替する経路。
- **failure 骨格**: (a) の反例は中心 conjunct 反証 = `target-refuted`。
  (b)(c) は二枝 disjunction なのでどちらの枝も成功、両枝とも閉じない
  場合は `target-blocked`。

### G-113(仮 slug: `G-113-aat-diagnostic-conservativity`)

- **責務**: O13–O18。診断保守性・反射・orbit exactness の分類。
- **claim 骨格**: (a) **`DiagnosticConservative` の新設定義**(Lean 不在を
  実査確認済み — G-111 の full-domain indexed action 上の述語として
  本カードが建設する)、(b) 構造的生成 class の固定と十分性 theorem
  (class membership → conservative。class は探索前固定の構造条件で
  立て、結論参照を禁じる — G-110 `H_cart` 資格条項の様式)、(c) 反射
  theorem — class 上で target obstruction vanishing → source vanishing、
  (d) orbit 検出 theorem — source reselection orbit の非自明性が target
  で検出される、(e) class 外 witness — class に入らない作用で非零
  obstruction が消える有限 witness(保守性の破れの実在 = class 制限の
  非空虚性)、(f) 診断 class の恒等・水平・垂直貼り合わせ閉性、
  (g) 生成診断部分圏上の `Full` + `Faithful` 十分条件候補の statement
  固定と、生成 class との関係(含意・同値・反例)の決定。
- **錨**: G-111 indexed schema(依存 — 量化域)、`InReselectionOrbit`
  (`TransportCoherence/FinitePresentation.lean`)、G-110 の旧 `H_bc` 系
  declaration(履歴 artifact — 素材として参照のみ)、
  `CoreFiberFunctorDefectCochain` 系
  (`DoctrineFiberProduct/BCDiagnosticBaseChangeAutomorphism.lean`)。
- **供給契約**: G-116 の記録。`DiagnosticConservative` の命名は本カード
  専属(§5 語彙正本規則)。
- **リスク / dullness 骨格**: 反射 (c) を可逆 fixture(全成分同型)だけで
  発火させる経路、class を「conservative と同値」の述語で立てる経路
  (結論の埋め込み)、(e) を空診断図式で満たす経路。**O14 の反射は
  G-109 effectivity 反射(域外)と別物** — この分界を statement に明記
  する(§5 判定線)。
- **failure 骨格**: (c)(d) の反例は class の縮小改訂ではなく
  `target-refuted`(fail-closed)。(g) は決定がどちらでも成功。

### G-114(仮 slug: `G-114-aat-refinement-base-change`)

- **責務**: O8–O9。refinement 系統。
- **claim 骨格**: (a) refinement 圏の構成 — `RefinementDoctrineHom`
  (`AtomFoundation/Doctrine.lean` に実在確認済み)を射とする圏構造
  (恒等・合成・結合律)と、`Doct_U` への忘却 / 比較 functor、
  (b) refinement base change — (A) の fiber product が refinement 射を
  pullback で安定に持ち上げること、refinement に沿った BC 比較射の構成と
  整合、(c) 非退化 witness(恒等でない refinement 射の pullback が非自明
  に立つ有限 fixture)。
- **錨**: `RefinementDoctrineHom`、G-110 (A) fiber product 構成・
  `pointedPullback_isPullback`
  (`DoctrineFiberProduct/PointedDoctrinePullback.lean`)、presentation
  閉性 constructor。
- **供給契約**: G-116 gate (iv) の refinement regime(存否決定の量化域の
  一部)。
- **リスク / dullness 骨格**: 圏化が「hom の再ラベル」に堕ちる経路
  (合成の非自明性 witness を要求)、refinement pullback が恒等成分で
  vacuous に立つ経路。
- **failure 骨格**: refinement pullback の非存在が定理化された場合は
  その退化定理を成果として `target-refuted`(G-110 (A) failure 様式)。

### G-115(仮 slug: `G-115-aat-upper-stage-lift`)

- **責務**: O10–O11。上段への base-change lift と Gr3 接続 bridge。
- **claim 骨格**: (a) `GeomRead` 段 lift — pointed pullback square の BC
  構造(引き戻し・canonical mate)を geometry 段 fiber へ持ち上げ、
  G-109 pseudofunctor package(compositor / unitor・pseudonatural
  compatibility)と両立する形で段射影と可換にする、(b) Gr3 接続
  bridge — 持ち上げた BC 作用と G-109 の段横断輸送・G-110 の
  G-106 / G-109 coherence bridge との整合 theorem、(c) **`ObProblem`
  段** — Lean 不在を実査確認済みのため、**class 割当の読み出し
  interface を最小構成で新設建設**した上で(G-109 が `ExtInst -> Doct`
  忘却 functor と離散 fiber theorem を新設した前例)、その上への BC
  lift の naturality を固定する。class 構成自体は変更しない(G-110
  claim boundary の継承)、(d) 非自明 geometry fiber 上の非退化発火
  witness(G-108 系 fixture の資産を素材とする)。
- **錨**: `CoreFiber` / `coreFiberTransportFunctor`
  (`CrossStageCoherence/CorePseudofunctor.lean`)、G-108
  `GeomRead_U` / `geomTransportAlongHom` 系(`GeometryTransport/`)、
  G-110 pullback reindexing functor・`pointedPullback_isPullback`。
- **供給契約**: G-116 gate (iv) の上段 regime。`ObProblem` interface の
  命名は本カード専属。
- **リスク / dullness 骨格**: lift を base equality 一本で代用する経路
  (G-109 (i) が禁じた形)、離散段(`ExtInst -> Doct`)での vacuous
  発火、`ObProblem` interface に class 構成の変更を紛れ込ませる経路。
- **failure 骨格**: `ObProblem` interface の Lean 建設が型不能なら
  `target-blocked`(gate (iii) の縮小 = `ObProblem` 部分の分離は人間
  裁定であり、自動 weakening をしない)。

### G-116(仮 slug: `G-116-aat-gr4-capstone`)

- **責務**: O12・O19。capstone。
- **claim 骨格**: (a) IsIso 水準 Beck–Chevalley exchange-failure の存否
  決定 — 量化域は G-110 sector+G-114 refinement regime+G-115 上段
  regime(gate (iv) の定めどおり)。**「全同型定理」または「¬IsIso の
  具体反例」の二枝 disjunction 単一命題**で固定する(G-110 (B) 様式:
  排他性は反例が供給、網羅性は主張しない)、(b) **Gr4 達成記録** —
  §3 義務台帳 O1–O18 の放電を先行カードの fixed head・review 錨と突合
  した上で、範囲併記付きで Gr4 達成 = SAKURA 満開を記録する(様式は
  G-109 の Gr3 記録。§7)。
- **錨**: G-111〜G-115 の final reviewed head(完遂後に固定)、G-110
  `MateCoherentRel` 正負対(`IsIso` は正例側の別 theorem という G-110 の
  分界を継承 — 本カードの存否決定はその未決部分の決定である)。
- **供給契約**: なし(終端)。
- **リスク / dullness 骨格**: 存否決定を退化 square(成分恒等・診断恒零)
  で放電する経路(G-110 dullness filter の継承)、達成記録が義務台帳との
  突合を欠いて宣言だけで立つ経路。
- **failure 骨格**: (a) の両枝とも閉じない場合は `target-blocked` であり
  **Gr4 は未達のまま**(記録だけ先行させない)。先行カードに未完遂が
  ある間は昇格しない(§5 依存 DAG)。

## §5 整合性監査 — ラインナップ全体

**被覆行列**: O1–O19 の各義務はちょうど一枚のカードが担当する(§3 の
担当列)。重複なし・漏れなし。gate との対応 — gate (i) = O1–O7
(G-111+G-112)、gate (ii) = O8–O9(G-114)、gate (iii) = O10–O11
(G-115)、gate (iv) = O12(G-116)、gate (v) = O13–O18(G-113)、
達成記録 = O19(G-116)。起票 batch PR のレビューは、この行列と各カード
本文の突合(義務の脱落・二重計上・域外混入の検査)を必須 gate とする。

**重複防止の判定線(4本)**:

1. **G-111 / G-113**: G-111 = indexed 作用の存在と順方向性質(共変・
   経路整合)、G-113 = 同じ作用の逆方向性質(保守・反射・検出)。
   G-113 は G-111 の schema 型を再定義せず量化域として消費する。
2. **G-111 / G-112**: G-111 = 診断・輸送側(cocartesian 保存 lift =
   O2 を含む)、G-112 = cartesian lift・coverage 側。**cocartesian
   (O2)と strong cartesian(O7)は別の lift であり、混同は義務の
   二重計上・脱落の両リスクを持つ** — カード本文で相互参照する。
3. **G-113 の反射 / G-109 effectivity 反射**: 前者 = indexed BC 作用の
   target → source 方向(O14)、後者 = 段射影 `p` の押し出し方向
   (域外・G-109 frontier のまま)。G-113 statement に分界を明記する。
4. **G-115 / G-116**: G-115 は regime(上段の BC 構造)を建設するが
   IsIso を主張しない。存否決定は G-116 専属(G-110 が `¬IsIso` を負例
   軸に採らなかった分界の継承)。

**語彙正本規則**: 6枚は G-101 / G-106 / G-108 / G-109 / G-110 の
reviewed 宣言を `ambient-boundary` として参照のみとし、再定義・改変を
しない(G-110 ledger の様式)。新設語彙の命名権は単責務に従い一枚に
専属させる — indexed schema 型 = G-111、`DiagnosticConservative` =
G-113、refinement 圏 = G-114、`ObProblem` interface = G-115。命名の
重複・分散を batch レビューで検査する。

**universe 設計規則(全カード共通)**: universe-polymorphic な義務は、
Lean の宇宙割当と F0 typing cycle で型突合してから台帳に固定する。
symbolic universe での成立が原理的に型不能な要求は台帳に置かず、枝条件
付き・endpoint 固定の契約で立てる(G-110 (B) の枝条件付き universe
移送契約を設計前例とする)。

**依存 DAG と伝播規定**:

```
G-110 ──→ G-111 ──→ G-112
               └──→ G-113
G-110 ──────→ G-114 ──┐
G-110 / G-109 → G-115 ─┴→ G-116(存否決定+達成記録)
```

- G-114 / G-115 は G-110 のみに依存し、G-111 系と並走可能である。
  G-112 の分類結果は他カードの量化域を変更しない(G-110 固定の
  realization 付き入力上で立つ)。
- 上流カードの statement 改訂時、依存する下流 draft は差し戻して再固定
  する(G-109 の伝播規定と同型)。G-111 改訂 → G-112 / G-113 へ、
  G-114 / G-115 改訂 → G-116 へ伝播する。
- G-116 は全カード完遂後にのみ昇格する(達成記録の突合が義務のため)。

## §6 隊列運用

- **起票**: draft 6枚を一括 batch PR で起票する(Gr3/Gr4 カード3枚
  draft の batch 起票と同型)。G-110 完遂済みで錨 head は固定済みであり、
  起票条件は満たされている。**batch PR のレビュー対象は「カード6枚+
  本ノート §3–§5 との整合」であり、全体整合の検査はこの一回に集約
  する**。
- **昇格**: 一枚ずつ、G-111 から。昇格時は敵対レビュー往復を経る。
  昇格順の推奨は依存 DAG に従い G-111 → (G-112 | G-113 | G-114 |
  G-115 は並走裁定) → G-116。
- **昇格レビューの右サイズ化(提案 — G-111 昇格前に正式裁定)**: 全体
  整合を batch レビューで先に閉じるため、昇格レビューはカード内部
  (statement の型・資格条項・witness 形)に限定できる。gate カードは
  reviewed artifact への錨止めを主とし、新設 schema の発明を statement
  に持ち込まない設計とする。この前提の下でレビュー上限を Claude
  3レーン+Codex 2巡とし、型細部は F0 typing cycle へ移す。
- **後続接続**: SAKURA 満開は Atlas 補強論文(n1006)の着手条件を解く。

## §7 満開の定義 — Gr 系列の完了

SAKURA 満開 = Gr4 達成の記録であり、次の全条件で成立する。

1. G-111〜G-115 が担当義務(§3 台帳 O1–O18 のうち各担当分)を
   `target-theorem-proved` で完遂している。義務は移管でのみ動かし、
   削除しない(G-110 の移管規律の継続)。
2. G-116 が O12(gate (iv) の存否)をどちらかの枝で確定している。
3. G-116 が義務台帳 O1–O18 の放電を先行カードの fixed head・review 錨と
   突合し、Gr4 達成を範囲併記付きで記録している(様式は G-109 の Gr3
   記録。coverage の到達段(第一段 / 第二段)、O6 / O7 / O12 の確定枝、
   §3 域外リストを併記する)。

満開の記録をもって Gr 階梯(Gr0–Gr4)は閉じ、SAKURA 海域は渡り切りと
なる。次の海域(係数 base change 方向、n1005 §5 の後続 draft 候補)の
命名は、その海域の開花の時に行う。
