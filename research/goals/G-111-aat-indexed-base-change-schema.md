# G-111-aat-indexed-base-change-schema — indexed base-change schema と診断の full-domain 化

- `id`: `G-111-aat-indexed-base-change-schema`
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第一項前半の担当カード(担当義務 =
  O1–O4。義務台帳の正本は G-116 カード、設計の source note は n1007
  §3–§5)。Gr4 後続6枚(G-111〜G-116)の第一手であり、昇格順の先頭。
  依存は G-110 のみ(reviewed artifact への参照)。本カードの statement
  改訂は G-112 / G-113 の draft 差し戻しへ伝播し、あらゆる改訂は
  G-116 の達成記録要件へ伝播する(伝播規定の正本 = n1007 §5)。
- `predecessor`: G-110(doctrine fiber product と base change。完遂済み =
  `target-theorem-proved`。`research/lean/ResearchLean/AG/
  DoctrineFiberProduct/` 配下、unported。固定錨は下記 ledger 行)、
  G-101(opcartesian 普遍性)、G-106(raw defect / reselection 語彙)。
- `tracking issue`: 未起票(active 昇格時に起票)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 G-111、§5 判定線)、
  [docs/note/n1005_aat_semantic_geometry_route_after_g107.md](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§4.3 (D))、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (i)・(B) 条項・(D) 移管文)
- `research aim`: G-110 の診断 base change 共変性は source-fiber
  incidence 資格付きの pointed square 上で立った。本カードはこの資格を
  解除する — pointed square に依らず全 `ExtractionInstance` 上で base
  作用を持つ global / indexed base-change schema を建設し、その上で
  cocartesian 保存 lift・実 BC 経路との制限比較・無条件 (d1)–(d6)
  診断共変性を固定する。これが Gr4 gate 第一項の schema 面である
  (分類面は G-112)。
- `core tension`: 既存の schema no-go theorem が確定しているのは
  「incidence は ordinary schema から普遍生成できない」ことである。
  つまり full-domain 化は資格の形式的な除去では達成できず、base 作用を
  authored 生成データとして持つ新しい indexed schema を建てるしかない。
  最大リスクは二つ — schema が pointed square 族の再包装に堕ちること
  (no-go が排除した普遍生成の逆流)、そして full-domain の coherence
  保存が要求する vertexwise functor 族の edge 適合(naturality)データ
  が、生成データと結論相当 certificate のどちらに落ちるかの資格線で
  ある。後者の資格条項は F0 で最初に固定する。
- `rival`: indexed category / Grothendieck fibration の base change
  一般論。差は「doctrine 塔という構文生成された具体対象の上で、診断
  障害(raw defect・reselection orbit)込みの base 作用を Lean で固定
  する」点に置く。一般論の instantiation で済む部分は流用してよい。
- `claim boundary`: 固定した一般 carrier `U`、G-110 の presentation /
  semantic 二層と `Doct_U` / `ExtInst_U` / package 総圏の上で語る。
  係数は動かさない。終対象・絶対積は導入しない。carrier change・
  cross-universe exact reindexing・`J_A` defect profile 枝・derived 系は
  域外(G-116 カードの域外リストを継承)。診断の逆方向性質(保守性・
  反射・検出)は G-113 の担当であり本カードは主張しない(順方向のみ —
  n1007 §5 判定線1)。
- `capability categories`: schema-construction、base-change、
  diagnostic-covariance、closure。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: schema 定義だけ、または (d1)–(d3) だけで完了
  扱いしない。schema・cocartesian lift・制限比較・(d1)–(d6)・named
  finite nonvacuity の全面に Lean artifact を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。indexed schema を pointed square の族・
  再ラベルで立てる構成、base 作用や共変性 certificate を structure
  field で受ける構成、制限比較を定義展開(`Iff.rfl` 級)で放電する
  構成、恒等初期 defect・identity reselection だけの発火、診断が空
  (2-cell なし・障害恒零)の図式での共変性発火、cocartesian lift を
  単一 fixture の列挙で代替する構成。
- `frontier`: G-113(保守性分類)への供給面の観察、係数 base change
  カードとの接続点の観察、`J_A` defect profile 枝(域外のまま)、
  indexed schema の H² 方向の観察。

- `target theorem`: **Indexed Base-Change Schema and Full-Domain
  Diagnostic Covariance Theorem**。G-110 の設定の上で:
  1. **(a) indexed schema の建設**: 全 `ExtractionInstance` 上の base
     作用を持つ indexed base-change schema を定義する。authored data は
     base 作用の生成データのみとし、共変性・可換性の結論相当
     certificate を field に持たない(G-110 route gate の継承)。
     vertexwise core-fiber functor 族の edge 適合データの資格条項
     (生成データとしての置き場所と監査方法)は F0 で固定する。
  2. **(b) cocartesian 保存 lift**: 各固定 carrier 内の全 package に
     対する cocartesian 保存 lift を証明する。
  3. **(c) 制限比較**: **incidence 資格付き部分域上で**、indexed 作用の
     pointed pullback square への制限が G-110 の実 BC 二経路
     (direct / via-base)と一致することを証明する。現行二経路の型は
     incidence を引数に取るため、資格なし全域での一致は主張しない —
     資格の解除は (d) の新経路が担う(この分界を statement で固定)。
  4. **(d) full-domain 診断共変性**: incidence 資格なしの (d1)–(d6)
     (interpretation・endpoint 群準同型・transported data・mapped
     reselection・coherence 保存・vanishing 保存)を indexed schema 上で
     証明する。
  5. **(e) named finite nonvacuity**: 初期 raw defect 非恒等・source
     reselection 非恒等の同一 validated fixture 上で (d4)–(d6) が発火
     する witness を構成する(G-110 named witness の indexed 昇格)。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。G-110 / G-106 / G-101 の reviewed module は参照のみ。完了面は
  (a)–(e) まで。保守性・反射・orbit exactness(G-113)、coverage 分類
  (G-112)、上段 lift(G-115)は主張しない。universe 契約は F0 で型
  突合の上確定する(型不能時は枝条件付き契約へ再表現 — n1007 §5
  universe 設計規則)。
- `target proof artifacts`: indexed schema 型一式と well-formedness
  述語、base 作用の生成手続き、cocartesian 保存 lift theorem、制限比較
  theorem(incidence 資格付き部分域)、full-domain (d1)–(d6) theorem
  一式と診断比較写像、named finite nonvacuity witness、report
  `research/reports/G-111-aat-indexed-base-change-schema.md`。
- `target proof strategy`: F0 schema typing(indexed schema・edge 適合
  データの資格条項・universe 契約を elaboration の実フィードバック付き
  で固定)→ K0 schema 建設と base 作用 → K1 cocartesian 保存 lift →
  K2 制限比較 → K3 full-domain (d1)–(d6) → K4 named witness と閉性
  監査。既存成果の利用 map:
  `no_universalBCDiagnosticSourceFiberIncidence`(incidence 資格の解除
  が普遍生成では不可能なことを確定する範囲標識 — 要件本体は G-110
  カード正本)、`CoreFiberFunctorDefectCochain` 系(全域側の既存 seed
  型)、`transportObstructionVanishes_map` / `mapEdgeReselection`
  (incidence 域の既存経路 — 制限比較の対象)、G-101 opcartesian
  普遍性。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head `$review-pr`
  +completion 時の独立 `$math-lean-review` 4査読全 `No major
  findings`)を通過すること(正本 = target-goal-contract.md)。
- `target premise discharge policy`: 入力(presentation・authored 生成
  データ・witness fixture)だけを残せる。base 作用の値・共変性・
  vanishing 保存の結論相当データを certificate や structure field で
  受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)。G-101 / G-106 の固定錨は G-110
    カード ledger の錨を継承する。
  - `indexed schema authored 生成データ`: `discharge-required`。field
    役割と資格条項を F0 で固定し、結論相当 certificate の混入を audit
    で排除する。
  - `edge 適合(naturality)データ`: `discharge-required`。vertexwise
    functor 族の適合を生成データとして資格付けし、coherence 保存の
    proof term で実消費する(caller-supplied certificate は放電と数え
    ない)。
  - `cocartesian 保存 lift`: `discharge-required`。
  - `制限比較 theorem`: `discharge-required`(incidence 資格付き部分域
    上。incidence はこの行に限り `direction-hypothesis` として消費)。
  - `full-domain (d1)–(d6)`: `discharge-required`。
  - `named finite nonvacuity witness`: `discharge-required`。
- `target route integrity gate`: base 作用・診断比較写像は authored
  生成データと G-101 / G-110 普遍性からのみ生成する。schema 型を
  pointed square に依存させない。witness fixture は proof obligation
  選定時に固定し、証明後の target-fitting 選択をしない。禁止経路 —
  結論相当データの供給、定義的 bridge、pointed square 族の再ラベル。
- `target anti-weakening rule`: 共変性・vanishing 保存・cocartesian
  性を theorem argument、typeclass、structure field、certificate field
  へ移して成功扱いしない。`ambient-boundary` に残せるのは入力幾何
  だけである。
- `target failure policy`: fail-closed を原則とする。schema の型不能は
  `goal-defect`、(d) の反例構成(full-domain 共変性を否定する indexed
  入力)は中心 conjunct 反証 = `target-refuted`、witness の停滞は
  `target-blocked`。fixed target の変更は人間の別判断とする。
