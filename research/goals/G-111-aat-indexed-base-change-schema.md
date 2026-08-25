# G-111-aat-indexed-base-change-schema — indexed base-change schema と診断の full-domain 化

- `id`: `G-111-aat-indexed-base-change-schema`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第一項前半の担当カード(担当義務 =
  O1–O4。義務台帳の正本は G-116 カード、設計の source note は n1007
  §3–§5)。Gr4 後続6枚(G-111〜G-116)の第一手であり、昇格順の先頭。
  Gr4 後続6枚内の先行依存は G-110 のみ(そのほかは完遂済みカードの
  reviewed artifact 参照)。**供給契約**: 本
  カードの indexed schema 型は G-113 の量化域として成果物形式で供給
  する(G-113 は本カードの schema 型を再定義しない)。**lift の分界**:
  本カードの O2 は cocartesian 保存 lift であり、strong cartesian lift
  (O7)は G-112 の担当である — 両者は別の lift であり、混同は義務の
  二重計上・脱落の両リスクを持つ(G-112 と相互参照)。**新設語彙の
  命名権**: indexed schema 型の命名は本カード専属。本カードの
  statement 改訂は G-113 の draft 差し戻しへ伝播し、あらゆる改訂は
  G-116 の達成記録要件へ伝播する。依存する reviewed カード(G-110・
  G-109)の statement が改訂された場合、本カードは draft へ差し戻して
  再固定する(伝播規定)。
- `predecessor`: G-110(doctrine fiber product と base change。完遂済み =
  `target-theorem-proved`。`research/lean/ResearchLean/AG/
  DoctrineFiberProduct/` 配下、unported。固定錨は下記 ledger 行)、
  G-101(opcartesian 普遍性)、G-106(raw defect / reselection 語彙)、
  G-109(core pseudofunctor API — `CoreFiber` を型に含む seed を消費
  する)。
- `tracking issue`: 未起票(起票はマージ後・loop 起動前)
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
  最大リスクは三つ — schema が pointed square 族の再包装に堕ちること
  (no-go が排除した普遍生成の逆流)、well-formedness 述語や edge 適合
  データに結論(coherence / vanishing 保存)が埋め込まれること、そして
  full-domain 化が「incidence 付き instance の形式的一般化」に留まり
  資格解除の実質(資格外 instance の実在)を欠くこと。前二者は資格
  条項で、後者は proper-extension witness で防ぐ。
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
  n1007 §5 判定線1)。strong cartesian lift(O7)は G-112 の担当で
  あり本カードは主張しない(判定線2)。
- `capability categories`: schema-construction、base-change、
  diagnostic-covariance、closure。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: schema 定義だけ、または (d1)–(d3) だけで完了
  扱いしない。schema・cocartesian lift・制限比較・(d1)–(d6)・named
  finite nonvacuity・proper-extension witness の全面に Lean artifact を
  要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。indexed schema を pointed square の族・
  再ラベルで立てる構成、base 作用や共変性 certificate を structure
  field で受ける構成、**well-formedness 述語・edge 適合データに
  coherence 保存・vanishing 保存・可換性の結論語彙を埋め込む構成**
  ((d5)(d6) が述語射影で従う形)、制限比較を定義展開(`Iff.rfl` 級)
  で放電する構成、**cocartesian lift を G-101 定理の再 instantiation
  単独で放電する構成**(schema の base 作用との整合を欠く形)、恒等
  初期 defect・identity reselection だけの発火、診断が空(2-cell
  なし・障害恒零)の図式での共変性発火、cocartesian lift を単一
  fixture の列挙で代替する構成。
- `frontier`: G-113(保守性分類)への供給面の観察、係数 base change
  カードとの接続点の観察、`J_A` defect profile 枝(域外のまま)、
  indexed schema の H² 方向の観察。

- `target theorem`: **Indexed Base-Change Schema and Full-Domain
  Diagnostic Covariance Theorem**。G-110 の設定の上で:
  1. **(a) indexed schema の建設**: 全 `ExtractionInstance` 上の base
     作用を持つ indexed base-change schema を定義する。authored data は
     base 作用の生成データのみとし、共変性・可換性の結論相当
     certificate を field に持たない(G-110 route gate の継承)。
     **well-formedness 述語は decoder 全域性・型整合の決定可能条件に
     限り、coherence 保存・vanishing 保存・可換性の結論語彙を含まない
     (G-110 (s4) 様式の継承)**。vertexwise core-fiber functor 族の
     edge 適合(naturality)データは authored 生成データ(base 作用の
     生成データの一部)として資格付けし、資格条項を次に固定する。
     **置き場所と依存域**: indexed schema の生成データ層。型は functor
     族と診断 presentation の 1-cell / 2-cell に対する naturality 成分
     (自然変換成分+可換等式)のみ。成分は presentation と頂点
     instance の水準でのみ index し、診断 interpretation の admissible
     data(comparator・edge lift 値)への依存・出現を持たない。
     **語彙の線引き(provenance 基準)**: 作用層語彙 = G-109
     CoreFiber API・schema 自身の生成 transport / reindex functor・
     authored functor 族・圏論の合成 / iso 原始のみ。定義展開が
     `comparator` / `EdgeReselection` / `DefectCochain` /
     `CoherentAt` / `TransportObstructionVanishes` /
     `InReselectionOrbit` を導入する項は診断結論側とし、field の型・
     等式への出現を**定義展開閉包で**禁止する(名前の不出現では判定
     しない。線引きの追加・変更は target 改訂扱い)。**監査方法**:
     structure-field escape audit で (i) edge 適合 field が作用層語彙
     のみで型付けされること(定義展開閉包で判定)、(ii) (b)–(e) の
     どの conjunct も edge 適合 field の射影・定義展開同値・wrapper
     lemma 経由で放電されないこと、(iii) (d5)(d6) の proof term が
     source 側 coherence / vanishing 仮定を実消費すること(G-110
     route gate の消費条項様式)を検査する。F0 で診断語彙なしに
     型付け不能と判明した場合は `goal-defect` で停止する(failure
     policy と整合。signature の最終確定は F0 が担う)。
  2. **(b) cocartesian 保存 lift**: 各固定 carrier 内の全 package に
     対する cocartesian 保存 lift を、**indexed schema の base 作用に
     対する lift として**証明する(作用との整合等式 — G-101 lift との
     関係式 — を含む。G-101 定理の再 instantiation 単独は放電と数え
     ない)。
  3. **(c) 制限比較**: **incidence 資格付き部分域上で**、indexed 作用の
     pointed pullback square への制限が G-110 の実 BC 二経路
     (direct / via-base)と一致することを証明する。現行二経路の型は
     incidence を引数に取るため、資格なし全域での一致は主張しない —
     資格の解除は (d) の新経路が担う(この分界を statement で固定)。
     **一致の水準は成分等式を既定とし、等式で立たない成分は canonical
     iso+coherence 等式で立てる**(成分の割当は F0 で列挙する。無条件
     iso への一括弱化は改訂扱い)。
  4. **(d) full-domain 診断共変性**: incidence 資格なしの (d1)–(d6)
     (interpretation・endpoint 群準同型・transported data・mapped
     reselection・coherence 保存・vanishing 保存)を indexed schema 上で
     証明する。
  5. **(e) witness 対**: (i) named finite nonvacuity — 初期 raw defect
     非恒等・source reselection 非恒等の同一 validated fixture 上で
     (d4)–(d6) が発火する witness(G-110 witness の indexed 昇格)、
     (ii) **proper-extension witness** — incidence が存在しない
     (pointed-square 制限像の外にある)instance 上で (d) が発火する
     witness。当該 instance は 2-cell 非空で (i) と同水準の非退化条件
     を満たす(空虚発火の排除)。資格解除が新しい入力を実際に獲得した
     ことの実在証明であり、(i) だけでは代替できない。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。G-110 / G-109 / G-106 / G-101 の reviewed module は参照のみ。
  完了面は (a)–(e) まで。保守性・反射・orbit exactness(G-113)、
  coverage 分類(G-112)、上段 lift(G-115)は主張しない。universe
  契約は F0 で型突合の上確定する(型不能時は枝条件付き契約へ再表現 —
  G-116 カード台帳注記の universe 規律)。
- `target proof artifacts`: indexed schema 型一式と well-formedness
  述語(決定可能条件限定)、base 作用の生成手続き、edge 適合データの
  資格条項、cocartesian 保存 lift theorem と作用整合等式、制限比較
  theorem(incidence 資格付き部分域)、full-domain (d1)–(d6) theorem
  一式と診断比較写像、named finite nonvacuity witness、
  proper-extension witness、report
  `research/reports/G-111-aat-indexed-base-change-schema.md`。
- `target proof strategy`: F0 schema typing(indexed schema・universe
  契約を elaboration の実フィードバック付きで確定)→ K0 schema 建設と
  base 作用 → K1 cocartesian 保存 lift → K2 制限比較 → K3 full-domain
  (d1)–(d6) → K4 witness 対と閉性監査。既存成果の利用 map:
  `no_universalBCDiagnosticSourceFiberIncidence`(incidence 資格の解除
  が普遍生成では不可能なことを確定する範囲標識 — 要件本体は G-110
  カード正本)、`CoreFiberFunctorDefectCochain` 系(全域側の既存 seed
  型 — vertexwise core-fiber functor 族)、
  `transportObstructionVanishes_map` / `mapEdgeReselection`(**無条件
  fiberwise 保存層 — (d) full-domain 側の seed**)、
  `bcDiagnosticDirectTransportObstructionVanishes` /
  `bcDiagnosticViaBaseTransportObstructionVanishes` 系(**incidence
  引数を取る実 BC 二経路 — (c) 制限比較の対象**)、G-101 opcartesian
  普遍性。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head
  `$review-pr`、completion candidate での Lean / report / tracking
  Issue 同期と final review packet 作成、独立 `$math-lean-review`
  4査読全 `No major findings`)を通過すること(正本 =
  target-goal-contract.md)。
- `target premise discharge policy`: 入力(presentation・authored 生成
  データ・witness fixture)だけを残せる。base 作用の値・共変性・
  vanishing 保存の結論相当データを certificate や structure field で
  受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)。G-101 / G-106 の固定錨は G-110
    カード ledger の錨を継承する(支える結論 = 全 conjunct の設定。
    結論相当でない理由 = 入力幾何と既証明の環境)。
  - `G-109 core pseudofunctor API(CoreFiber)`: `ambient-boundary`。
    参照のみ、改変しない(固定錨は G-110 カード ledger の G-109 錨を
    継承。proof-use = base 作用の vertexwise functor 族の型)。
  - `indexed schema authored 生成データ`:
    `conclusion-equivalent-risk`(入力資格として残すが risk 種別で監査
    する)。役割 = base 作用の生成入力。監査 artifact = 生成手続きが
    (d1)–(d6)・制限比較水準の共変性・可換性を field から読まないこと
    の structure-field escape audit(edge 適合等式の消費は (a) 資格
    条項の範囲で許す。支える結論 = (a)(d)。結論相当でない理由 = 資格
    条項が結論語彙を排除し、共変性は (d) の theorem が生成する)。
  - `well-formedness 述語と edge 適合データの資格条項`:
    `discharge-required`。決定可能条件限定・結論非参照の資格 theorem /
    audit として放電する(支える結論 = (a) の schema 資格。proof-use =
    (d5)(d6) が述語射影で従わないことの監査)。
  - `cocartesian 保存 lift`: `discharge-required`。作用整合等式込み
    (支える結論 = (b)。discharge artifact = lift theorem+G-101 lift
    との関係式。結論相当でない理由 = lift は schema の base 作用から
    構成され、供給されない)。
  - `制限比較 theorem`: `discharge-required`。incidence 資格付き部分域
    上(incidence はこの行に限り `direction-hypothesis` として消費。
    支える結論 = (c)。proof-use = direct / via-base 経路の実定理との
    等式 / iso)。
  - `full-domain (d1)–(d6)`: `discharge-required`(支える結論 = (d)。
    discharge artifact = 6本の theorem と診断比較写像。結論相当でない
    理由 = 全て schema と普遍性から生成する)。
  - `witness 対(named nonvacuity+proper extension)`:
    `discharge-required`(支える結論 = (e)。discharge artifact = 同一
    validated fixture 上の発火証明+資格外 instance の実在証明)。
- `target route integrity gate`: base 作用・診断比較写像は authored
  生成データと G-101 / G-110 普遍性からのみ生成する。schema 型を
  pointed square に依存させない。well-formedness 述語・edge 適合
  データへの結論語彙の埋め込みを audit で排除する。witness fixture は
  proof obligation 選定時に固定し、証明後の target-fitting 選択を
  しない。禁止経路 — 結論相当データの供給、定義的 bridge、pointed
  square 族の再ラベル、G-101 定理の再 instantiation 単独での (b)
  放電、edge 適合 field への (b)(c) 相当等式の供給
  (`bcDiagnosticDirectFunctor` 系・G-101 lift 由来 functor の field
  型への出現は不可)。
- `target anti-weakening rule`: 共変性・vanishing 保存・cocartesian
  性を theorem argument、typeclass、structure field、certificate
  field、**well-formedness 述語**へ移して成功扱いしない。
  `ambient-boundary` に残せるのは入力幾何だけである。
- `target failure policy`: fail-closed を原則とする。schema の型不能・
  statement 不足は `goal-defect`、(d) の反例構成(full-domain 共変性を
  否定する indexed 入力)は中心 conjunct 反証 = `target-refuted`、
  witness の停滞は `target-blocked`。fixed target の変更は人間の別判断
  とする。
