# G-115-aat-upper-stage-lift — 上段への base-change lift と Gr3 接続

- `id`: `G-115-aat-upper-stage-lift`
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第三項の担当カード(担当義務 =
  O10–O11。義務台帳の正本は G-116 カード、設計の source note は n1007
  §3–§5)。6枚の中ではどのカードにも依存せず G-111 系と並走可能
  (外部依存は G-110 に加え G-109 / G-108 の reviewed artifact)。
  本カードの成果物は G-116 gate (iv) の上段 regime 型を供給する —
  G-116 は regime を新設建設しないため、この供給は成果物形式の義務で
  ある。改訂は G-116 の達成記録要件へ伝播する。**昇格前 gate:
  `ObProblem` の Lean 指示対象の裁定**(semantic adequacy 条件は
  target theorem (c))。
- `predecessor`: G-110(完遂済み。pointed pullback・reindexing
  functor。固定錨は G-111 カード ledger と同一)、G-109(core
  pseudofunctor package と段横断輸送。完遂済み。
  `research/lean/ResearchLean/AG/CrossStageCoherence/` 配下、
  unported)、G-108(geometry 段輸送。完遂済み。
  `research/lean/ResearchLean/AG/GeometryTransport/` 配下、unported。
  G-109 / G-108 の固定錨は G-110 カード ledger の錨を継承する)。
- `tracking issue`: 未起票(active 昇格時に起票)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 G-115)、
  [docs/note/n1001_atom_is_all_you_need_discussion.md](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§3.3 塔 — `ObProblem` 段の定義)、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (iii))、
  [G-109 カード](G-109-aat-cross-stage-coherence.md)(pseudofunctor 塔)
- `research aim`: G-110 の base change は塔の底(`Doct_U` /
  `ExtInst_U`)で立った。本カードはそれを塔の上段へ持ち上げる —
  `GeomRead` 段では G-109 の pseudofunctor 塔と両立する BC lift を、
  `ObProblem` 段では構成された障害類そのものの base-change naturality
  を固定する。これで Gr3(段横断整合)と Gr4(base change)が同じ塔の
  上で接続し、G-116 の存否決定に上段 regime を供給する。
- `core tension`: 最大リスクは `ObProblem` 段の **semantic adequacy**
  である — `ObProblem` の語は Lean(research 木・Formal 木)にも AG
  数学本文にも無く、n1001 §3.3 の塔にのみ住む。安易な class 読み出し
  interface を新設してその上の naturality だけ示すと、「代理 interface
  は閉じたが実際の障害類への接続は未証」のまま O11 が放電されたことに
  なってしまう。だから完了には adequacy bridge(interface が「構成
  された cocycle / class」を表すこと)と、その class の naturality への
  移送を義務化する。`GeomRead` 段側のリスクは lift の base equality
  一本での代用(G-109 (i) が禁じた形)である。
- `rival`: fibred 2-category の change of base・pseudofunctor の
  restriction 一般論。差は「AAT の具体塔の上で、診断障害類の
  naturality まで込みで Lean 固定する」点に置く。
- `claim boundary`: G-108 / G-109 で建設済みの塔の段(`GeomRead` 段・
  core 段)と G-110 の pointed pullback square の上で語る。`ObProblem`
  段の class 構成自体は変更しない(読み出しと naturality のみ)。
  carrier change・係数・段射影 `p` 方向の effectivity 反射・nerve /
  cover 接続は域外(G-116 カードの域外リストを継承)。
- `capability categories`: base-change、tower-lift、bridge、
  naturality。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: `GeomRead` 段 lift だけ、または `ObProblem`
  interface の定義だけで完了扱いしない。両段の lift・Gr3 接続
  bridge・adequacy bridge・両段の非退化発火 witness の全面に Lean
  artifact を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。lift を base equality 一本で代用する
  構成、離散段(`ExtInst -> Doct`)での vacuous 発火、`ObProblem`
  interface に class 構成の変更を紛れ込ませる構成、定数 class 読み出し
  での vacuous naturality、**adequacy bridge を欠く代理 interface での
  O11 放電**、G-109 pseudofunctor theorem の再証明を成果と数える構成。
- `frontier`: `ObProblem` 段の class naturality の一般化(class 構成を
  動かす方向 — 域外のまま観察のみ)、上段診断と G-113 保守性の相互
  作用、無限段の塔。

- `target theorem`: **Upper-Stage Base-Change Lift Theorem**。
  G-108 / G-109 / G-110 の設定の上で:
  1. **(a) `GeomRead` 段 lift**: pointed pullback square の BC 構造
     (引き戻し・canonical mate)を geometry 段 fiber へ持ち上げ、
     G-109 pseudofunctor package(compositor / unitor・pseudonatural
     compatibility)と両立する形で段射影と可換にする。**上段 regime 型
     (G-116 が消費する mate 比較の型)を成果物形式に含める**。
  2. **(b) Gr3 接続 bridge**: 持ち上げた BC 作用と G-109 の段横断
     輸送・G-110 の G-106 / G-109 coherence bridge との整合 theorem を
     証明する。
  3. **(c) `ObProblem` 段**: n1001 §3.3 の `ObProblem -> GeomRead` は
     「構成された cocycle / class の naturality」の段であり、本
     conjunct が閉じるべき対象は**構成された障害類そのものの
     base-change naturality** である。Lean 上の表現は起票時裁定の
     選択肢に従う(昇格前 gate — (i) Formal 木の障害 class 系(二木
     bridge 込み)、(ii) research 木の orbit / defect 語彙上の最小
     class 読み出し interface(推奨))。**完了には、選択した
     interface が「構成された cocycle / class」を表すことの adequacy
     bridge と、その class の base-change naturality への移送を含める
     (semantic adequacy 条件)。代理 interface 上の naturality だけ
     では放電と数えない。** class 構成自体は変更しない。
  4. **(d) 非退化発火 witness**: 非自明 geometry fiber 上の発火
     (G-108 系 fixture 資産が素材)と、`ObProblem` interface 上で
     非恒等 class 読み出しが BC lift で実際に動く fixture の両方を
     構成する。
- `target theorem boundary`: Lean 置き場所は起票時に固定する(原則
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。上段接続 module の分離は F0 で判断)。G-108 / G-109 /
  G-110 の reviewed module は参照のみ。完了面は (a)–(d) まで。class
  構成の変更・`p` 方向 effectivity・IsIso 水準の存否(G-116)は主張
  しない。
- `target proof artifacts`: `GeomRead` 段 BC lift 一式と段射影可換
  theorem、上段 regime 型、Gr3 接続 bridge theorem、`ObProblem`
  interface(裁定後の指示対象)と adequacy bridge、障害類の
  base-change naturality theorem、両段の非退化発火 witness、report
  `research/reports/G-115-aat-upper-stage-lift.md`。
- `target proof strategy`: 昇格前 gate(`ObProblem` 指示対象裁定)→
  F0 typing(lift・regime 型・interface・adequacy bridge の
  signature)→ K0 `GeomRead` 段 lift → K1 regime 型と Gr3 bridge →
  K2 `ObProblem` interface と adequacy bridge → K3 naturality →
  K4 witness と監査。既存成果の利用 map: `CoreFiber` /
  `coreFiberTransportFunctor`(G-109 pseudofunctor)、
  `GeomReadCategory`(通称 GeomRead_U)/ `geomTransportAlongHom` 系
  (G-108)、G-110 pullback reindexing functor・
  `pointedPullback_isPullback`。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head `$review-pr`
  +completion 時の独立 `$math-lean-review` 4査読全 `No major
  findings`)を通過すること(正本 = target-goal-contract.md)。
- `target premise discharge policy`: 入力(square・上段対象・witness
  fixture)だけを残せる。lift・naturality・adequacy の結論相当データの
  供給は放電と数えない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ(固定錨は
    G-111 カード ledger と同一)。
  - `G-109 core pseudofunctor package / G-108 GeometryTransport`:
    `ambient-boundary`。参照のみ、改変しない(固定錨は G-110 カード
    ledger の錨を継承)。
  - `GeomRead 段 BC lift と regime 型`: `discharge-required`。
  - `Gr3 接続 bridge`: `discharge-required`。
  - `ObProblem interface と adequacy bridge`: `discharge-required`
    (指示対象の裁定は昇格前 gate。adequacy bridge を欠く interface
    は放電と数えない)。
  - `障害類の base-change naturality`: `discharge-required`。
  - `両段の非退化発火 witness`: `discharge-required`。
- `target route integrity gate`: lift・mate・naturality は G-109 /
  G-110 の普遍性と reviewed API からのみ生成する(G-101 からの再建は
  しない)。`ObProblem` interface の指示対象は昇格前に裁定・固定し、
  証明後の差し替えをしない。witness fixture は proof obligation 選定
  時に固定する。禁止経路 — base equality による lift 代用、adequacy
  bridge の省略、class 構成の変更の混入。
- `target anti-weakening rule`: lift 存在・naturality・adequacy を
  theorem argument、typeclass、structure field、certificate field へ
  移して成功扱いしない。`ambient-boundary` に残せるのは入力幾何だけで
  ある。
- `target failure policy`: fail-closed を原則とする。`ObProblem`
  interface の Lean 建設が型不能なら `target-blocked`(gate (iii) の
  縮小 = `ObProblem` 部分の分離は人間裁定であり、自動 weakening を
  しない)。(a)(c) の反例(lift 不能・naturality の破れ)は中心
  conjunct 反証 = `target-refuted`。fixed target の変更は人間の別判断と
  する。
