# G-115-aat-upper-stage-lift — 上段 base-change regime と障害 orbit 自然性

- `id`: `G-115-aat-upper-stage-lift`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第三項の担当カード(担当義務 =
  O10–O11。義務台帳の正本は G-116 カード、設計の source note は n1007
  §3–§5)。G-114 revision 3 が供給する
  `ActiveRefinementBCContext` に依存する。上段 lift は任意の raw
  refinement でも任意の `TwoLayerTransportData` でもなく、実際の target
  fiber 内に置かれた finite transport problem と canonical mate を持つ
  active context 上で、その成立域を exact に特徴付けてから構成する。
  **供給契約**: 本カードの成果物は G-116 gate (iv) の
  `ActiveUpperStageRegime` と、そこから生成される actual lifted mate を
  供給する。G-116 は regime、lift、mate を新設建設しない。
- `predecessor`: G-114 revision 3(完遂済み。active refinement
  context・base/pulled mate の唯一の供給元。固定錨は下記 ledger 行)、
  G-110(完遂済み。pointed pullback・reindexing
  functor。固定錨は下記 ledger 行)、G-109(core pseudofunctor
  package と段横断輸送。完遂済み。
  `research/lean/ResearchLean/AG/CrossStageCoherence/` 配下、
  unported)、G-108(geometry 段輸送。完遂済み。
  `research/lean/ResearchLean/AG/GeometryTransport/` 配下、unported。
  固定錨は下記 ledger 行に直接記載)、G-106(完遂済み。(c) の指示対象
  = orbit / defect 語彙。固定錨は下記 ledger 行)。
- `tracking issue`: [#4250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4250)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 G-115)、
  [docs/note/n1001_atom_is_all_you_need_discussion.md](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§3.3 塔 — `ObProblem` 段の定義)、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (iii))、
  [G-109 カード](G-109-aat-cross-stage-coherence.md)(pseudofunctor 塔)
- `research aim`: G-110 の exact base change と G-114 の
  realized-support refinement base change は塔の底(`Doct_U` /
  `ExtInst_U`)で立つ。本カードは、G-114 の canonical mate が G-108 の
  realization transport 条件を満たす exact upper-stage regime を
  特徴付け、その regime 上で `GeomRead` 段の BC action、G-109 の Gr3
  pseudofunctor coherence、構成済み upper raw-defect orbit の forward
  naturality を同じ格子図として固定する。これにより Gr3 の縦輸送と
  Gr4 の水平 base change を接続し、G-116 の `IsIso` 存否決定へ actual
  lifted mate を供給する。
- `core tension`: 上段作用は全 active refinement context に自動ではない。
  G-114 の `mateAtTarget` は `CoreFiber` の射である一方、G-108 は任意の
  package morphism の geometry lift に `HGeom` が必要かつ十分であり、
  `GeometryTransport.FiniteWitnesses.not_hGeom` /
  `no_geometryLift_to_any_target` がその条件を無条件には生成できないことを
  固定している。したがって `HGeom` を regime field に入れて universal
  lift と呼ぶのではなく、fiberwise finite problem 上の
  `UpperRealizationCompatible` を exact domain 条件として necessity /
  sufficiency の両方向で特徴付ける。`ObProblem` は代理 interface を新設
  せず、`InUpperReselectionOrbit` が定める actual orbit set を class
  object として読む。もう一つの安価経路は底段の再包装であり、O11 の
  proof term に lifted geometry action の実消費を要求して防ぐ。
- `rival`: fibred 2-category の change of base・pseudofunctor の
  restriction 一般論。差は「AAT の具体塔の上で、診断障害類の
  naturality まで込みで Lean 固定する」点に置く。
- `claim boundary`: 固定した一般 carrier `U`、G-108 / G-109 で建設済み
  の塔の段(`GeomRead` 段・core 段)、G-114 の
  `ActiveRefinementBCContext`、その target pointed fiber 内の finite
  `FiberwiseTwoLayerTransportData` の上で語る。係数は動かさない。
  終対象・絶対積は導入しない。forward-only / inactive refinement は
  上段 mate の定義域に含めない。
  orbit の同値性は G-116 で lifted mate の `IsIso` が得られた場合の
  corollary に限り、G-115 では forward naturality を無条件主張とする。
  class 構成自体は変更しない。carrier change・係数 base change・段射影 `p` 方向の
  effectivity 反射・nerve / cover 接続は域外(G-116 カードの域外
  リストを継承)。
- `capability categories`: base-change、tower-lift、bridge、
  naturality。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: G-108 の `HGeom ↔ GeomReadHom` を G-114 mate
  へ名前だけ特殊化した theorem、`GeomRead` 段 lift だけ、orbit set の
  定義だけでは完了扱いしない。fiberwise input の構成、exact regime
  classification、lifted mate、Gr3 接続、raw cochain commuting、orbit
  naturality、正負の regime witness、非恒等発火の全面に Lean artifact を
  要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、
  停滞なら `target-blocked`、反証なら `target-refuted`、全完了条件と
  final review を満たした場合だけ `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。lift を base equality 一本で代用する
  構成、`UpperRealizationCompatible` を lift / naturality field の包装に
  する構成、`ActiveUpperStageRegime` を caller-supplied lift certificate
  にする構成、離散段(`ExtInst -> Doct`)での vacuous 発火、orbit membership
  Prop だけを class object と呼ぶ構成、定数 orbit での vacuous
  naturality、**O11 の naturality を底段 (d1)–(d6) の restatement、
  または底段への pushforward 移送と既証明の底段 cochain 輸送
  (G-106 transition / G-113 O20 系)で立てる構成**(上段 lift の
  実消費を欠く形、pushforward で消える upper 成分に主張を持たない
  形)、G-109 pseudofunctor theorem の再証明、`Classical.em` だけによる
  regime 正負 witness の包装を成果と数える構成。
- `frontier`: lifted mate が `IsIso` の場合の orbit equivalence の帰趨
  (G-116 が決定)、上段診断と G-113 transport exactness の相互作用、
  fiberwise 制限を越える indexed family、無限段の塔。

- `revision 1 disposition`: 2026-08-29 の F0 typing で、単一の
  `ActiveRefinementBCContext` と任意の `TwoLayerTransportData` を結ぶ
  semantic primitive、および G-114 mate を geometry 段へ送る資格条件が
  statement に無いことを `goal defect` として固定した(tracking Issue
  #4250 comment `5462812441`)。revision 2 は target を弱めず、対象を
  target pointed fiber 内の finite problem として型付けし、G-108 の
  realization condition を exact regime classification として明示する。

- `target theorem`: **Upper-Stage Base-Change Regime and
  Obstruction-Orbit Naturality Theorem**。G-108 / G-109 / G-110 と、
  G-114 が供給する `ActiveRefinementBCContext` の上で:
  1. **(a) fiberwise input と exact upper-stage regime**: target pointed
     fiber `X := ctx.configuration.targetPointAt ctx.source` 内の finite
     presentationを、各 vertex が `GeomFiber X` の object、各 edge が
     fiber 内の射となる `FiberwiseTwoLayerTransportData` として構成し、
     既存 `TwoLayerTransportData` / `TwoLayerLiftData` への comparison を
     証明する。この raw input は lift、mate、naturality、cochain law、
     非退化 certificate を field に持たない。G-114 の二つの canonical
     core route と `ctx.mate` をこの finite problem の全 vertex / edgeへ
     評価し、各 generated route component に対する G-108 realization
     supply を述べる `UpperRealizationCompatible ctx data : Prop` を定義
     する。次の両方向を証明する:
     `UpperRealizationCompatible ctx data` から lifted geometry BC diagram
     を構成でき、任意のそのような diagram から同じ compatibility を
     回収できる。`ActiveUpperStageRegime` は compatible な raw input の
     subtype とし、lift / mate / coherence を field に持たせない。
  2. **(b) lifted mate と Gr3 接続**: `ActiveUpperStageRegime` 上で G-114
     の base route / pulled route に対応する geometry 段 functorと、
     `ctx.mate` から生成される actual lifted natural transformation を
     構成する。段射影との可換は `IsHomLift` 水準の等式とし、G-109 の
     compositor / unitor との pseudonatural coherence を証明する。
     「BC lift 後に Gr3 transport」と「Gr3 transport 後に BC lift」は
     独立に生成された二経路として比較し、一方を他方の定義にしない。
     この lifted mate を G-116 が消費する成果物として公開する。
  3. **(c) actual obstruction-orbit naturality**: 新しい proxy class は
     導入せず、`upperObstructionOrbit data : Set (UpperDefectCochain data)`
     を `InUpperReselectionOrbit data` の extent として定義する。membership
     iff により actual G-109 orbit との双方向 adequacy を固定する。
     (b) の lifted geometry functorから automorphism、upper cochain、edge
     reselection の map を構成し、`upperRawDefectCochain` commuting と
     `Set.MapsTo` による orbit の forward naturality を証明する。proof
     term は lifted geometry action を実消費し、core pushforward だけで
     閉じない。さらに lifted mate が `IsIso` の場合に限り、direct image
     equality / orbit equivalence を与える corollary を構成し、G-116へ
     渡す。無条件の orbit equivalence は主張しない。
  4. **(d) regime 正負と非退化発火 witness**: 非恒等 G-114 active
     refinement 上で `UpperRealizationCompatible` を満たす nontrivial
     fiberwise problem と、active core context / nonempty geometry inputを
     持ちながら compatibility を満たさない named problem を構成する。
     負例は G-108 `not_hGeom` / `no_geometryLift_to_any_target` の量化対象を
     G-114 generated route に実際に接続し、単なる任意 package hom の負例
     を再掲しない。正例では lifted BC action の像が identity action と
     異なる named component、および raw cochain または orbit set が実際に
     動く named componentを別 theorem で証明する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module で固定する(module 分割の詳細のみ F0 で判断する)。G-108 /
  G-109 / G-110 の reviewed module は参照のみ。完了面は (a)–(d)
  まで。law universe・site / cover は前提カードの固定を継承して動かさ
  ない。受理 Lean 宣言は premise / review / merge gate 通過までは
  static evidence に留まる。class 構成の変更・`p` 方向 effectivity・
  lifted mate の無条件 `IsIso` / orbit equivalence(G-116)は主張しない。
- `target proof artifacts`: `FiberwiseTwoLayerTransportData` と既存語彙への
  comparison、`UpperRealizationCompatible`、exact liftability iff、
  `ActiveUpperStageRegime`、生成された二つの geometry route functorと
  lifted mate、Gr3 pseudonatural coherence、`upperObstructionOrbit` と
  adequacy iff、cochain / reselection map、raw-cochain commuting、orbit
  forward naturality、`IsIso` conditional orbit equivalence、regime 正負
  witnessと非恒等発火 theorem、report
  `research/reports/G-115-aat-upper-stage-lift.md`。
- `target proof strategy`: F0 typing(fiberwise input、compatibility、regime、
  two geometry routes、lifted mate、orbit map の signature と等式成分の
  列挙)→ K0 fiberwise input と exact regime classification → K1 geometry
  route / lifted mate と Gr3 bridge → K2 orbit object / adequacy / raw-cochain
  commuting → K3 forward naturality と conditional equivalence → K4 正負
  witness と監査。既存成果の利用 map:
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
- `target premise discharge policy`: 入力である
  `ActiveRefinementBCContext` と raw `FiberwiseTwoLayerTransportData`、
  および sufficiency 方向だけに使う `UpperRealizationCompatible` を
  残せる。compatibility は `direction-hypothesis` であり、全 input への
  無条件供給や discharge 済み premise として扱わない。lift・mate・
  coherence・cochain law・naturality・非退化性の結論相当データの供給は
  放電と数えない。
- `target material premise ledger`:
  - `G-114 active refinement context`: `ambient-boundary`。G-114 の
    reviewed theorem が actual target package と fixed condition から
    local regime を生成して構成した値のみを受け取る。**固定錨:
    完了 PR #4246(fixed head `8f7ad8bf`、merge `3d26d993`)**。
    proof-use = (a) の二 core route と canonical mate の入力。結論相当で
    ない理由 = core fiber の regime / mate であり、geometry lift・
    段射影可換・障害 orbit naturality の
    いずれも含意しない。
    forward-only / inactive configuration を regime fixture で active
    にする経路は禁止。
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)(支える結論 = pointed square と
    reindexing の設定。結論相当でない理由 = 入力 square と reindexing
    の設定のみで上段 lift を含まない)。
  - `G-109 core pseudofunctor package`: `ambient-boundary`。参照のみ、
    改変しない(固定錨は G-110 カード ledger の G-109 錨を継承:
    final reviewed head `b5ca4630`。proof-use = (a)(b) の両立対象と
    (c) の上段接続点(`InUpperReselectionOrbit`)。結論相当でない理由
    = 比較対象と接続点であり上段 BC 構造を含まない)。
  - `G-108 GeometryTransport`: `ambient-boundary`。参照のみ、改変
    しない。**固定錨: 実装 PR #4015(final reviewed head `a1d70d01`、
    merge `12c3e6c2`)**(proof-use = `GeomReadCategory` /
    `geomTransportAlongHom`、`HGeom` の必要十分性、
    `GeometryTransport.FiniteWitnesses.not_hGeom` /
    `no_geometryLift_to_any_target` の実消費。結論相当でない理由 =
    geometry lift の判定語彙と単独 package hom の witness であり、G-114
    generated route への接続・exact regime・naturality を含まない)。
  - `G-106 TransportCoherence`: `ambient-boundary`。参照のみ、改変
    しない。**固定錨: PR #4004–#4009(fixed head `d7b1d488`、merge
    `ae1ba0ea`)**(proof-use = (c) の指示対象と adequacy bridge の
    同定先。結論相当でない理由 = raw cochain / orbit 語彙のみで
    geometry action に沿う naturality を
    含まない)。
  - `fiberwise input と既存 transport data への comparison`:
    `discharge-required`(支える結論 = (a)。raw input が target pointed
    fiber の内在射だけを持ち、lift 結論を field に持たないことを含む)。
  - `UpperRealizationCompatible`: `direction-hypothesis`(支える結論 =
    (a) の sufficiency 方向。discharge artifact ではない。necessity theorem
    と incompatibility witness により exact domain 条件であることを別に
    固定する)。
  - `exact upper-stage regime classification`: `discharge-required`
    (支える結論 = (a)。discharge artifact = liftability iff と、raw input+
    compatibility proof の subtype だけからなる `ActiveUpperStageRegime`。
    lift / mate / coherence field は不可)。
  - `geometry route・lifted mate・Gr3 接続`: `discharge-required`(支える
    結論 = (b)。discharge artifact = G-114 の二 route / mate から生成した
    functor・natural transformation・`IsHomLift` 等式・pseudonatural
    coherence・独立二経路の Gr3 bridge。caller 供給不可)。
  - `actual upper obstruction orbit と adequacy`: `discharge-required`
    (支える結論 = (c)。discharge artifact =
    `upperObstructionOrbit` と `InUpperReselectionOrbit` membership iff。
    proxy class / opaque membership への差し替え不可)。
  - `raw cochain commuting と orbit forward naturality`:
    `discharge-required`(支える結論 = (c)。proof-use = (b) の lifted
    geometry action の実消費。core pushforward だけでは放電しない)。
  - `IsIso conditional orbit equivalence`: `discharge-required`(支える
    結論 = (c) の条件付き corollary。`IsIso` 自体は仮定であり G-115 の
    無条件結論ではない。G-116 がその存否を決定する)。
  - `regime 正負と非退化発火 witness`: `discharge-required`(支える結論 =
    (d)。正例・負例とも raw fixture と性質を別宣言にし、負例では G-108
    witness を G-114 generated route へ接続する。正例では geometry action
    と raw cochain / orbit movement を別々に発火させる)。
- `target route integrity gate`: fiberwise problem は G-114 target pointed
  fiber 内で型付けし、lift・mate・naturality は G-108 の geometry
  transport 判定、G-109 の pseudofunctor 普遍性、G-114 の canonical
  mate から生成する。G-114 `ctx.mate` の proof-use と、G-108 `HGeom`
  必要十分性の両方を theorem body で確認する。orbit の指示対象は (c) の
  actual `InUpperReselectionOrbit` に固定する。witness fixture は F0 typing
  cycle で固定し、proof body で使用しない受け渡しは実消費と数えない。
  禁止経路 — 任意 `ctx` と任意 `TwoLayerTransportData` の無根拠な結合、
  base equality による lift 代用、lift / mate の regime field 化、core
  pushforward だけによる naturality、proxy class、片方向 adequacy の同値
  読み替え、空型 / 恒等への退化、class 構成の変更、`IsIso` の無条件化。
- `target anti-weakening rule`: revision 1 の universal upper lift へ戻さず、
  かつ単なる「compatible なら lift」を exact classification と呼ばない。
  `UpperRealizationCompatible` は G-108 realization supply のみを述べ、
  lift・mate・coherence・naturalityを field に持たない。
  `ActiveUpperStageRegime` は raw input と compatibility proof の subtype に
  限る。生成される lift・actual mate・Gr3 coherence・orbit map・cochain
  law・naturality・adequacy・witness 非退化性を theorem argument、
  typeclass、structure field、certificate fieldへ移して成功扱いしない。
- `target failure policy`: fail-closed を原則とする。target pointed fiber
  内の `FiberwiseTwoLayerTransportData`、G-114 generated route に対する
  compatibility、または actual upper orbit map のいずれかが statement
  として型付かない場合は `goal-defect` で停止する。exact classification、
  Gr3 bridge、raw-cochain commuting、forward naturality の concrete
  counterexample は `target-refuted` とする。G-115 の positive / negative
  named witness が既存有限素材から構成不能と確定した場合も
  `target-refuted` とし、単なる探索停滞は停止規律に従い
  `target-blocked` とする。lifted mate の `IsIso` 存否は G-116 の義務で
  あり、G-115 の failure ではない。fixed target の変更は人間の別判断と
  する。
