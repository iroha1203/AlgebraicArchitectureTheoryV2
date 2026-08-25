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
  する(G-113 は本カードの schema 型を再定義しない)。indexed action
  の恒等・合成・pasting-coherence API も本カード(O1 の一部)が供給
  し、G-113 はその演算の上で診断 class の閉性(O17)を証明する。**lift の分界**:
  本カードの O2 は cocartesian lifted action((b1) canonical lift
  compatibility+(b2) 保存)であり、strong cartesian lift(O7)は
  G-112 の担当である — 両者は別の lift であり、混同は義務の
  二重計上・脱落の両リスクを持つ(G-112 と相互参照)。**新設語彙の
  命名権**: indexed schema 型の命名は本カード専属。本カードの
  statement 改訂は G-113 の draft 差し戻しへ伝播し、あらゆる改訂は
  G-116 の達成記録要件へ伝播する。依存する reviewed カード(G-110・
  G-109・G-106)の statement が改訂された場合、本カードは draft へ
  差し戻して再固定する(伝播規定。G-106 は `AdmissibleTransportData`・
  reselection・coherence / vanishing を statement で直接消費する論理
  依存)。G-101 は G-110 の reviewed 錨経由でのみ消費する(F0 で直接
  declaration 依存が生じた場合は伝播対象へ含める)。
- `predecessor`: G-110(doctrine fiber product と base change。完遂済み =
  `target-theorem-proved`。`research/lean/ResearchLean/AG/
  DoctrineFiberProduct/` 配下、unported。固定錨は下記 ledger 行)、
  G-101(opcartesian 普遍性)、G-106(raw defect / reselection 語彙)、
  G-109(core pseudofunctor API — `CoreFiber` を型に含む seed を消費
  する)。
- `tracking issue`: #4158(runtime state 正本。proof state・cycle
  履歴・F0 で確定した schema signature と許容 producer 一覧の fixed
  head はここに同期する)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 G-111、§5 判定線)、
  [docs/note/n1005_aat_semantic_geometry_route_after_g107.md](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§4.3 (D))、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (i)・(B) 条項・(D) 移管文)
- `research aim`: G-110 の診断 base change 共変性は source-fiber
  incidence 資格付きの pointed square 上で立った。本カードはこの資格を
  解除する — pointed square に依らず全 `ExtractionInstance` とその
  全ての射の上で base 作用を持つ global / indexed base-change schema
  を建設し、その上で
  cocartesian lifted action・実 BC 経路との制限比較・無条件 (d1)–(d6)
  診断共変性を固定する。これが Gr4 gate 第一項の schema 面である
  (分類面は G-112)。
- `core tension`: 既存の schema no-go theorem が確定しているのは
  「incidence は ordinary schema から普遍生成できない」ことである。
  つまり full-domain 化は資格の形式的な除去では達成できず、incidence
  経由の transported-data 生成とは別の生成経路を建てるしかない。本
  カードはその経路を、全 base 射に対する opcartesian 押し出し
  (canonical cleavage)経由の indexed transport として固定する。
  authored 入力は base 射・可換 square の有限 syntax(raw
  generator)に限り、functor・作用の値は供給しない。最大リスクは三つ
  — schema が pointed square 族の再包装に堕ちること(no-go が排除
  した普遍生成の逆流)、well-formedness 述語や edge law に結論
  (coherence / vanishing 保存)が埋め込まれること、そして
  full-domain 化が canonical cleavage の再記述・「incidence 付き
  instance の形式的一般化」に留まり、資格外 instance 上の診断
  transported data の実在を欠くこと。前二者は資格条項で、後者は
  proper-extension witness と dullness filter で防ぐ。
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
  扱いしない。schema(合成 API 込み)・cocartesian lifted action・
  制限比較 C0–C3・(d1)–(d6)・named finite nonvacuity・
  proper-extension witness の全面に Lean artifact を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。indexed schema を pointed square の族・
  再ラベルで立てる構成(量化域を square 由来射・relabel 射の部分類へ
  制限する形を含む)、base 作用や共変性 certificate を structure
  field で受ける構成、既存 total action の identity の包み直し・
  任意 functor 族の generic functoriality だけを schema 建設と数える
  構成、canonical cleavage(`coreFiberLift`)の再 instantiation 単独を
  (a) の建設・(d) の放電と数える構成((d3) arbitrary-source
  transported data((b2) を実消費する K2 成果物)の建設を欠く形)、
  paste の decode を comp と定義同値に潰す構成(square 水準の貼り
  合わせ義務の回避)、**well-formedness 述語・edge law に
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
  1. **(a) indexed schema の建設(三層分離)**: 全
     `ExtractionInstance` とその全ての射の上で base 作用を持つ
     indexed base-change schema を、次の三層で定義する。schema の
     量化域は `ExtInst_U` の全対象・全ての射・全ての base 可換
     square である(葉の許容に部分類への制限を置かない)。**raw
     generator 層** — authored 入力はこの層のみ。base 作用の有限
     生成データ(生成器)であり、各項は有限 syntax 木、葉 = 固定
     carrier 内 `ExtInst_U` の base 射(対象水準の transport index)
     と base 射の可換 square(射水準の transport index)— いずれも
     G-101 `ExtInst_U` API 水準の射データ(canonical cleavage は
     G-109)、constructor = id / comp(射・square の逐次合成)/
     paste(square の水平・垂直貼り合わせ — G-110 (E) の貼り合わせ
     様式)。functor・作用の値そのものを含まない(`CoreFiber X ⥤
     CoreFiber Y`
     型の族を authored 入力に置くことは作用の値の供給 = premise
     policy 違反)。**indexed action 層** — producer が raw generator
     から次の型の背骨で作用を生成する: base 成分 = raw 項が decode
     する `ExtInst_U` の射 / 可換 square(作用の index)、total 作用
     = 各 decode 射 σ に対する package 総圏上の transport で σ の
     上にあるもの(projection 整合 — 等式を既定とし canonical iso
     への割当は F0)+各 decode square に対する cross-fiber 総圏射の
     transport(cocartesian 普遍性で誘導される誘導成分)、fiber 作用
     = 各 σ が誘導する `CoreFiber` transport
     族(canonical cleavage = G-109 `coreFiberLift` からの誘導成分で
     あり独立入力ではない)。producer は id / comp / paste 項を恒等・
     合成・貼り合わせの transport へ写す(generated action の合成が
     schema の量化域で閉じる — G-113 供給 API の基礎)。
     **soundness 層** — projection 整合・id / comp / pasting
     coherence(生成 transport と decode 射 / square の合成・貼り
     合わせの整合 — square の二境界経路の生成 transport が canonical
     comparison で一致することを含む。等式で立たない成分は canonical
     iso+coherence 等式 — 割当は F0)を theorem として立てる
     (cocartesian 保存は (b) の独立義務であり、ここに重複計上
     しない)。共変性・可換性の結論相当 certificate を field に
     持たない(G-110 route gate の継承)。well-formedness 述語は
     decoder 全域性・型整合の決定可能条件に限り、結論語彙を含まない
     (G-110 (s4) 様式の継承)。**edge 適合(naturality)は universal
     action law として固定する** — 特定 presentation の edge 値に
     対する field ではなく、全 base 射・可換 square とその上の
     package 総圏射に対する
     作用の law とし、source interpretation の `edgeLift` 値はその
     law に代入する theorem argument としてのみ消費する。作用が
     presentation 非依存で composition(id / comp / path evaluation)
     に整合すること自体を本カードで要求する(3-cell 整合を field と
     theorem のどちらで持つかは F0 の選択)。**語彙の線引き
     (provenance 基準)**: raw generator / producer / law が使える
     のは G-101・G-109 CoreFiber API・圏論の合成 / iso 原始のみ。
     定義展開が `comparator` / `EdgeReselection` / `DefectCochain` /
     `CoherentAt` / `TransportObstructionVanishes` /
     `InReselectionOrbit` を導入する項の field・law への出現を
     **定義展開閉包で**禁止する(名前の不出現では判定しない。線引き
     の追加・変更は target 改訂扱い)。**監査方法**: (i) raw
     generator / law が上記語彙のみで型付けされることを **module
     boundary で固定する** — raw schema / generator module は
     G-101・G-109・圏論 API のみ import し、診断系 module が raw
     module を一方向に import する、(ii) (b)–(e) のどの conjunct も
     schema field / law の射影・定義展開同値・wrapper lemma 経由で
     放電されないこと、(iii) (d5)(d6) の proof term が source 側
     coherence / vanishing 仮定を実消費すること(G-110 route gate の
     消費条項様式)。**束縛条項**: (b)–(e) は同一の generated action
     (同一 producer 出力)を参照する dependent artifact として立てる
     — conjunct ごとの別 schema / 別 action の横継ぎは放電と数えない。
     F0 で診断語彙なしに型付け不能と判明した場合は failure policy に
     従う(signature の最終確定は F0 が担う)。
  2. **(b) cocartesian lifted action(O2 の二命題)**: 各固定
     carrier 内で (b1) **canonical lift compatibility** — raw 項の
     生成 transport による像と、decode 射に対する canonical
     cleavage(`coreFiberLift`)押し出しを、cocartesian 普遍性が誘導
     する canonical comparison で結び、id / comp(合成項の生成
     transport と合成射の cleavage)coherence を証明する。比較は
     total 層(producer 出力の総圏 transport)で行い、fiber 成分の
     葉での定義的一致は放電に数えない — 放電の中心は comp / paste
     項の coherence(G-101 普遍性の実消費)である(lift の
     存在は G-109 既証(`coreFiberLift`)であり再記述しない — 新規
     義務は生成 action と canonical cleavage の整合。G-101 / G-109
     定理の再 instantiation 単独は放電と数えない)、(b2) **保存** — 生成
     action の square transport が strongly cocartesian total
     morphism を strongly
     cocartesian に保存する(`map_stronglyCocartesian` 水準。engine
     界面への適合は K1.5 adapter の義務とし、界面変換で本命題を
     弱めない)。両者は
     別命題であり、片方で他方を代替しない。
  3. **(c) 制限比較(比較階層 C0–C3)**: indexed 作用の pointed
     pullback square への制限を G-110 の実 BC 二経路と次の4面で比較
     する。(C0) 生成二経路 functor(direct / via-base — presentation
     から生成され incidence 非依存)との functor 比較 — 比較対象は
     `BCPresentation` から producer 出力への canonical evaluation /
     restriction 経路で固定する(caller 後付けの比較対象選択は禁止)、
     (C1) incidence 資格付き ordinary interpretation 上の transported
     data(package・edge 資格・two-cell base・comparator)の比較、(C2) endpoint 作用・mapped
     reselection・edge / path law の比較、(C3) indexed→direct・
     indexed→via・G-110 direct↔via canonical comparison が作る三角形
     の coherence。incidence を要するのは transported data の生成段
     (C1–C2)であり、その資格なし全域での一致は主張しない — 資格の
     解除は (d) の新経路が担う(この分界を statement で固定)。
     **一致の水準は成分等式を既定とし、等式で立たない成分は canonical
     iso+coherence 等式で立てる**(成分の割当は F0 で列挙する。無条件
     iso への一括弱化は改訂扱い)。
  4. **(d) full-domain 診断共変性**: incidence 資格なしの (d1)–(d6)
     (interpretation・endpoint 群準同型・transported data・mapped
     reselection・coherence 保存・vanishing 保存)を、indexed schema
     の全量化域(全 base 射・可換 square)に沿って証明する。
  5. **(e) witness 対**: (i) named finite nonvacuity — 初期 raw defect
     非恒等・source reselection 非恒等の同一 validated fixture 上で
     (d4)–(d6) が発火する witness(G-110 witness の indexed 昇格)、
     (ii) **proper-extension witness** — 資格外の意味は
     `¬ BCDiagnosticSourceFiberIncidence P I`(presentation+
     interpretation 水準の否定)で固定する。witness 条件: 具体
     2-cell 上で初期 raw defect 非恒等・source reselection 非恒等・
     source coherence / vanishing 成立・generated target 側の
     coherence / vanishing 発火、かつ witness の action は (a) の
     同一 producer から生成する(fixture 専用の後付け action の禁止)。
     witness の transport index の base 射は非可逆(iso でない)と
     する — 可逆射に沿う transport は同値であり、資格解除の実在証明
     にならない。
     (i)(ii) の少なくとも一方で **action の非自明性を identity
     action との差で**要求する — 同一 producer 出力・同一 witness
     fixture 上の指定成分について、generated action の像が identity
     action による像と一致しないことを証明する(endpoint の型が
     異なる場合は fixture 固定時に選定した canonical equality / iso
     で比較する — 比較用 equality / iso は schema の canonical
     comparison 族(eqToHom・unitor / compositor・cocartesian 普遍性
     由来 comparison)の合成に限り、自由選定しない)。具体形は、
     endpoint を揃えた上での生成 transport
     像の差(`(T g).map f ≠ f` 水準)・生成 transport による fiber
     automorphism 像の差(`mapPackageFiberAut` 水準)、
     または named
     nonidentity BC fixture への C0 制限の指定成分が identity
     restriction の対応成分と一致しないこと、のいずれか(選定は
     witness fixture 固定時)。非恒等な source 成分の像が非恒等で
     あることは identity action でも成立するため artifact と数えず、
     transport functor 全体の不等式(endpoint を揃えた `T ≠ 𝟭`)単独も
     同様とする。資格解除が
     新しい入力を実際に獲得したことの実在証明であり、(i) だけでは
     代替できない。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。G-110 / G-109 / G-106 / G-101 の reviewed module は参照のみ。
  完了面は (a)–(e) まで。保守性・反射・orbit exactness(G-113)、
  coverage 分類(G-112)、上段 lift(G-115)は主張しない。universe
  契約は F0 で型突合の上確定する(型不能時は枝条件付き契約へ再表現 —
  G-116 カード台帳注記の universe 規律)。
- `target proof artifacts`: indexed schema 型一式(raw generator・
  producer・well-formedness 述語(決定可能条件限定))、universal
  edge law と composition 整合 theorem、indexed action の恒等・合成・
  pasting-coherence API(G-113 供給面)、cocartesian lifted action
  theorem((b1) canonical lift compatibility+(b2) 保存)、制限比較
  theorem 階層 C0–C3、full-domain
  (d1)–(d6) theorem 一式と診断比較写像、named finite nonvacuity
  witness、proper-extension witness、report
  `research/reports/G-111-aat-indexed-base-change-schema.md`。
- `target proof strategy`: F0 schema typing(raw generator・universe
  契約を elaboration の実フィードバック付きで確定し、許容 producer
  一覧を tracking Issue に fixed head で記録)→ K0 raw decode+生成
  transport(base / total / fiber)+projection 整合 → K1
  cocartesian 保存+canonical lift
  comparison → K1.5 transported-data 生成様式の morphism-indexed
  adapter(`DiagnosticPackageTotalAction` 様式)→ K2
  arbitrary-source transported data → K3 制限比較 C0–C3 → K4
  full-domain (d1)–(d6) → K5 witness 対と閉性・合成 API 監査
  (transported data の生成は `map_stronglyCocartesian` を要するため
  (b2) を K2 より先に置く — proof DAG の循環禁止)。既存成果の利用 map:
  `no_universalBCDiagnosticSourceFiberIncidence`(incidence 資格の解除
  が普遍生成では不可能なことを確定する範囲標識 — 要件本体は G-110
  カード正本)、`DiagnosticPackageTotalAction` /
  `BCDiagnosticTotalTransport` 系(**transported-data 生成様式
  (`map_stronglyCocartesian`・base congruence の law 水準)の seed
  — endofunctor 界面への直接 instantiation は要求しない。新規義務は
  schema 生成 transport からの診断 transported data の
  morphism-indexed 全域建設**)、`coreFiberLift` /
  `coreFiberLift_isStronglyCocartesian`(**canonical cleavage — 存在と
  strongly cocartesian 性は G-109 既証。新規義務は cleavage の再記述
  ではなく、生成 transport の coherence と診断 transported data の
  全域建設**)、`CoreFiberFunctorDefectCochain` 系
  (vertexwise seed 型)、`transportObstructionVanishes_map` /
  `mapEdgeReselection`(**無条件 fiberwise 保存層 — (d) full-domain
  側の seed**)、`bcDiagnosticDirectTransportObstructionVanishes` /
  `bcDiagnosticViaBaseTransportObstructionVanishes` 系(**incidence を
  要する transported-data 段の実経路 theorem — C1–C2 の比較対象**)、
  G-101 opcartesian 普遍性。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head
  `$review-pr`、completion candidate での Lean / report / tracking
  Issue 同期と final review packet 作成、独立 `$math-lean-review`
  4査読全 `No major findings`)を通過すること(正本 =
  target-goal-contract.md)。
- `target premise discharge policy`: 入力(presentation・raw
  generator の authored 生成データ・ordinary source diagnostic data・
  witness fixture)だけを残せる。**target 側**の package・edge 資格・
  two-cell base・comparator・reselection・coherence / vanishing
  certificate は全て generated output であり入力供給不可。base 作用の
  値・共変性・vanishing 保存の結論相当データを certificate や
  structure field で受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)。G-101 / G-106 の固定錨は G-110
    カード ledger の錨を継承する(支える結論 = 全 conjunct の設定。
    結論相当でない理由 = 入力幾何と既証明の環境)。
  - `G-109 core pseudofunctor API(CoreFiber)`: `ambient-boundary`。
    参照のみ、改変しない(固定錨は G-110 カード ledger の G-109 錨を
    継承。proof-use = canonical cleavage(`coreFiberLift`)と fiber
    作用(各 σ の `CoreFiber` transport 族)の型)。
  - `ordinary source diagnostic data(AdmissibleTransportData /
    BCDiagnosticInterpretation)`: `direction-hypothesis`。(d1)–(d6) の
    source 側入力(packages・`edgeLift`・edge 資格・two-cell base・
    authored comparator)。source reselection は (d4)、source
    `CoherentAt` は (d5)、source `TransportObstructionVanishes` は
    (d6) に限る仮定として消費する(結論相当でない理由 = G-111 が解除
    するのは incidence 資格のみで、source 側診断データは G-110 と同じ
    方向仮定のまま残る)。
  - `indexed schema authored 生成データ`:
    `conclusion-equivalent-risk`(入力資格として残すが risk 種別で監査
    する)。役割 = base 作用の生成入力(raw generator — base 射・
    可換 square の有限 syntax。値ではなく生成器)。監査 artifact =
    生成手続きが
    (d1)–(d6)・制限比較水準の共変性・可換性を field から読まないこと
    の structure-field escape audit(edge law の消費は (a) 資格条項の
    範囲で許す。支える結論 = (a)(d)。結論相当でない理由 = 資格
    条項が結論語彙を排除し、共変性は (d) の theorem が生成する)。
  - `well-formedness 述語と edge law の資格条項`:
    `discharge-required`。決定可能条件限定・結論非参照の資格 theorem /
    audit(module boundary 監査込み)として放電する(支える結論 =
    (a) の schema 資格。proof-use = (d5)(d6) が述語射影で従わないこと
    の監査)。
  - `cocartesian lifted action`: `discharge-required`(支える結論 =
    (b1)(b2)。discharge artifact = canonical lift comparison theorem
    (id / comp coherence 込み)+保存 theorem。結論相当でない理由 =
    比較射は生成 action と canonical cleavage から構成され、供給され
    ない)。
  - `制限比較 theorem 階層 C0–C3`: `discharge-required`。C1–C2 は
    incidence 資格付き部分域上(incidence はこの行に限り
    `direction-hypothesis` として消費。支える結論 = (c)。proof-use =
    direct / via-base 経路の実定理との等式 / iso と三角形 coherence)。
  - `full-domain (d1)–(d6)`: `discharge-required`(支える結論 = (d)。
    discharge artifact = 6本の theorem と診断比較写像。結論相当でない
    理由 = 全て schema と普遍性から生成する)。
  - `witness 対(named nonvacuity+proper extension)`:
    `discharge-required`(支える結論 = (e)。discharge artifact = 同一
    validated fixture 上の発火証明+資格外 instance の実在証明)。
- `target route integrity gate`: base 作用・診断比較写像は raw
  generator と G-101 / G-109 / G-110 reviewed API
  (`DiagnosticPackageTotalAction` / total transport engine 含む)から
  のみ生成する。schema 型を pointed square に依存させない。
  well-formedness 述語・edge law への結論語彙の埋め込みを module
  boundary audit で排除する。witness fixture は proof obligation 選定
  時に固定し、証明後の target-fitting 選択をしない。禁止経路 — 結論
  相当データの供給(target 側 diagnostic data の入力化を含む)、
  定義的 bridge、pointed square 族の再ラベル、G-101 定理の再
  instantiation 単独での (b) 放電、schema field / law への (b)(c)
  相当等式の供給(`bcDiagnosticDirectFunctor` 系・G-101 lift 由来
  functor の field 型への出現は不可 — 判定は (b)(c) 相当等式の供給と
  しての出現に限り、canonical comparison 族の coherence field は対象
  外)、conjunct 間の別 action 横継ぎ。
- `target anti-weakening rule`: 共変性・vanishing 保存・cocartesian
  性を theorem argument、typeclass、structure field、certificate
  field、**well-formedness 述語**へ移して成功扱いしない。
  `ambient-boundary` に残せるのは入力幾何だけである。
- `target failure policy`: fail-closed を原則とする。**表現不能**
  (同じ意味論を別 signature で表現すれば型が立つ場合 — 意味論を
  弱めない universe 枝条件付き再表現を含む)・statement 不足は
  `goal-defect`、**数学的反証**(固定意味論を満たす action / lift の
  非存在 theorem、または (d) の反例構成 = full-domain 共変性を否定
  する indexed 入力)は中心 conjunct 反証 = `target-refuted`、反例も
  証明もない構成停滞は `target-blocked`。fixed target の変更は人間の
  別判断とする。
