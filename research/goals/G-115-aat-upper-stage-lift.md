# G-115-aat-upper-stage-lift — 上段への base-change lift と Gr3 接続

- `id`: `G-115-aat-upper-stage-lift`
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第三項の担当カード(担当義務 =
  O10–O11。義務台帳の正本は G-116 カード、設計の source note は n1007
  §3–§5)。G-114 revision 3 が供給する
  `ActiveRefinementBCContext` に依存する。上段 lift は任意の raw
  refinement ではなく、実際の target package と canonical mate を持つ
  active context 上でのみ構成する。
  **供給契約**: 本カードの成果物は G-116 gate (iv) の上段 regime 型を
  供給する — G-116 は regime を新設建設しないため、この供給は成果物
  形式の義務である。
- `predecessor`: G-114 revision 3(完遂後の fixed reviewed head。
  active refinement context・base/pulled mate の唯一の供給元)、
  G-110(完遂済み。pointed pullback・reindexing
  functor。固定錨は下記 ledger 行)、G-109(core pseudofunctor
  package と段横断輸送。完遂済み。
  `research/lean/ResearchLean/AG/CrossStageCoherence/` 配下、
  unported)、G-108(geometry 段輸送。完遂済み。
  `research/lean/ResearchLean/AG/GeometryTransport/` 配下、unported。
  固定錨は下記 ledger 行に直接記載)、G-106(完遂済み。(c) の指示対象
  = orbit / defect 語彙。固定錨は下記 ledger 行)。
- `tracking issue`: 未起票(active 昇格時に起票)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 G-115)、
  [docs/note/n1001_atom_is_all_you_need_discussion.md](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§3.3 塔 — `ObProblem` 段の定義)、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (iii))、
  [G-109 カード](G-109-aat-cross-stage-coherence.md)(pseudofunctor 塔)
- `research aim`: G-110 の exact base change と G-114 の
  realized-support refinement base change は塔の底(`Doct_U` /
  `ExtInst_U`)で立つ。本カードは G-114 の active context をそのまま
  塔の上段へ持ち上げる —
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
  移送を義務化する。もう一つの安価経路は底段の再包装 — O11 の
  naturality が G-111 の (d1)–(d6) の restatement で立つ形であり、
  上段 lift の実消費で防ぐ。`GeomRead` 段側のリスクは lift の base
  equality 一本での代用(G-109 (i) が禁じた形)である。
- `rival`: fibred 2-category の change of base・pseudofunctor の
  restriction 一般論。差は「AAT の具体塔の上で、診断障害類の
  naturality まで込みで Lean 固定する」点に置く。
- `claim boundary`: 固定した一般 carrier `U`、G-108 / G-109 で建設済み
  の塔の段(`GeomRead` 段・core 段)と G-114 の
  `ActiveRefinementBCContext` の上で語る。係数は動かさない。
  終対象・絶対積は導入しない。forward-only / inactive refinement は
  上段 mate の定義域に含めない。
  `ObProblem` 段の class 構成自体は変更しない(読み出しと naturality
  のみ)。carrier change・係数 base change・段射影 `p` 方向の
  effectivity 反射・nerve / cover 接続は域外(G-116 カードの域外
  リストを継承)。
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
  O11 放電**、**O11 の naturality を底段 (d1)–(d6) の restatement で
  立てる構成**(上段 lift の実消費を欠く形)、G-109 pseudofunctor
  theorem の再証明を成果と数える構成。
- `frontier`: `ObProblem` 段の class naturality の一般化(class 構成を
  動かす方向 — 域外のまま観察のみ)、上段診断と G-113 transport exactness の相互
  作用、無限段の塔。

- `target theorem`: **Upper-Stage Base-Change Lift Theorem**。
  G-108 / G-109 / G-110 と、G-114 が供給する任意の
  `ActiveRefinementBCContext` の上で:
  1. **(a) `GeomRead` 段 lift**: pointed pullback square の BC 構造
     (引き戻し・canonical mate)を geometry 段 fiber へ持ち上げ、
     G-109 pseudofunctor package と両立する形で段射影と可換にする。
     **可換の水準を固定する** — 可換は指定 canonical 2-cell による
     pseudonatural 可換(compositor / unitor との coherence 等式込み)
     とし、等式で立てる成分は F0 で列挙する(square ごとの ad hoc な
     iso 選択による「iso までの可換」は放電と数えない)。
     **G-114 の canonical mate を再構成せず proof-use し、上段 active
     regime 型(G-116 が消費する mate 比較の型)を成果物形式に含める**。
  2. **(b) Gr3 接続 bridge**: 持ち上げた BC 作用と G-109 の段横断
     輸送・G-110 の G-106 / G-109 coherence bridge との整合 theorem を
     証明する。
  3. **(c) `ObProblem` 段**: n1001 §3.3 の `ObProblem -> GeomRead` は
     「構成された cocycle / class の naturality」の段であり、本
     conjunct が閉じるべき対象は**構成された障害類そのものの
     base-change naturality** である。指示対象は G-106 の
     `rawDefectCochain` とその reselection orbit
     (`InReselectionOrbit`)の類に固定し、上段接続点は G-109 の
     `InUpperReselectionOrbit` とする。`ObProblem` interface はこの
     語彙上の最小 class 読み出しとして新設する(signature の設計のみ
     F0)。**完了には、interface がこの指示対象を表すことの adequacy
     bridge と、その class の base-change naturality への移送を含める**
     (semantic adequacy 条件)。代理 interface 上の naturality だけ
     では放電と数えない。さらに O11 の naturality は (a) の
     `GeomRead` 段 lift を proof term として実消費する上段 statement
     でなければならず、底段 (d1)–(d6) から段 lift を経由せず従う形は
     放電と数えない**(G-111 O4 との判定線)。class 構成自体は変更
     しない。
  4. **(d) 非退化発火 witness**: 非自明 geometry fiber 上の発火
     (G-108 系 fixture 資産が素材)と、`ObProblem` interface 上で
     非恒等 class 読み出しが BC lift で実際に動く fixture の両方を
     構成する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module で固定する(module 分割の詳細のみ F0 で判断する)。G-108 /
  G-109 / G-110 の reviewed module は参照のみ。完了面は (a)–(d)
  まで。class 構成の変更・`p` 方向 effectivity・IsIso 水準の存否
  (G-116)は主張しない。
- `target proof artifacts`: `GeomRead` 段 BC lift 一式と pseudonatural
  可換 theorem(coherence 等式込み)、上段 regime 型、Gr3 接続
  bridge theorem、`ObProblem` interface と adequacy bridge、障害類の
  base-change naturality theorem(段 lift の実消費付き)、両段の
  非退化発火 witness、report
  `research/reports/G-115-aat-upper-stage-lift.md`。
- `target proof strategy`: F0 typing(lift・regime 型・interface・
  adequacy bridge の signature、等式成分の列挙)→ K0 `GeomRead` 段
  lift → K1 regime 型と
  Gr3 bridge → K2 `ObProblem` interface と adequacy bridge →
  K3 naturality → K4 witness と監査。既存成果の利用 map:
  `CoreFiber` / `coreFiberTransportFunctor`(G-109 pseudofunctor)、
  `GeomReadCategory`(通称 GeomRead_U)/ `geomTransportAlongHom` 系
  (G-108)、G-110 pullback reindexing functor・
  `pointedPullback_isPullback`、G-106 `rawDefectCochain` /
  `InReselectionOrbit` と G-109 `InUpperReselectionOrbit`((c) の
  指示対象)、G-114
  `ActiveRefinementBCContext` / canonical base・pulled mate。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head
  `$review-pr`、completion candidate での Lean / report / tracking
  Issue 同期と final review packet 作成、独立 `$math-lean-review`
  4査読全 `No major findings`)を通過すること(正本 =
  target-goal-contract.md)。
- `target premise discharge policy`: 入力(square・上段対象・witness
  fixture)だけを残せる。lift・naturality・adequacy の結論相当データの
  供給は放電と数えない。
- `target material premise ledger`:
  - `G-114 active refinement context`: `ambient-boundary`。G-114 の
    reviewed theorem が actual target package と fixed condition から
    local regime を生成して構成した値のみを受け取る。proof-use = (a)
    の上段 mate の入力。
    forward-only / inactive configuration を regime fixture で active
    にする経路は禁止。
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)(支える結論 = pointed square と
    reindexing の設定)。
  - `G-109 core pseudofunctor package`: `ambient-boundary`。参照のみ、
    改変しない(固定錨は G-110 カード ledger の G-109 錨を継承:
    final reviewed head `b5ca4630`。proof-use = (a)(b) の両立対象)。
  - `G-108 GeometryTransport`: `ambient-boundary`。参照のみ、改変
    しない。**固定錨: 実装 PR #4015(final reviewed head `a1d70d01`、
    merge `12c3e6c2`)**(proof-use = `GeomReadCategory` /
    `geomTransportAlongHom` の消費と (d) の fixture 素材)。
  - `G-106 TransportCoherence`: `ambient-boundary`。参照のみ、改変
    しない。**固定錨: PR #4004–#4009(fixed head `d7b1d488`、merge
    `ae1ba0ea`)**(proof-use = (c) の指示対象と adequacy bridge の
    同定先)。
  - `GeomRead 段 BC lift と regime 型`: `discharge-required`(支える
    結論 = (a)。discharge artifact = lift 構成+pseudonatural 可換
    theorem+regime 型。結論相当でない理由 = 構成して証明する)。
  - `Gr3 接続 bridge`: `discharge-required`(支える結論 = (b)。
    proof-use = G-109 compositor / G-110 coherence bridge の実消費)。
  - `ObProblem interface と adequacy bridge`: `discharge-required`
    (支える結論 = (c)。adequacy bridge を欠く interface は放電と
    数えない)。
  - `障害類の base-change naturality`: `discharge-required`(支える
    結論 = (c)。proof-use = (a) の段 lift の実消費を audit で確認)。
  - `両段の非退化発火 witness`: `discharge-required`(支える結論 =
    (d))。
- `target route integrity gate`: lift・mate・naturality は G-109 /
  G-110 の普遍性、G-114 の canonical mate、reviewed API からのみ
  生成する(G-101 からの再建や G-114 reverse transport の再構成は
  しない)。`ObProblem` interface の指示対象は (c) で固定済みであり、
  証明後の差し替えをしない。witness fixture は proof obligation 選定
  時に固定する。禁止経路 — base equality による lift 代用、adequacy
  bridge の省略、底段共変性の restatement、class 構成の変更の混入。
- `target anti-weakening rule`: lift 存在・naturality・adequacy を
  theorem argument、typeclass、structure field、certificate field へ
  移して成功扱いしない。`ambient-boundary` に残せるのは入力幾何だけで
  ある。
- `target failure policy`: fail-closed を原則とする。`ObProblem`
  interface の Lean 建設が型不能・statement 不足と判明した場合は
  `goal-defect` で停止する(gate (iii) の縮小 = `ObProblem` 部分の
  分離は人間裁定であり、自動 weakening をしない)。(a)(c) の反例
  (lift 不能・naturality の破れ)は中心 conjunct 反証 =
  `target-refuted`。(b) bridge の反証も `target-refuted`。witness の
  停滞は `target-blocked`。fixed target の変更は人間の別判断とする。
