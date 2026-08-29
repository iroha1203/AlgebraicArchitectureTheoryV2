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
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 は revision 1 の設計元。proxy interface 部分は下記 revision 2 disposition で superseded)、
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
  Gr4 の水平 base change を接続し、G-116 の componentwise exchange
  exactness の存否決定へ actual lifted mate family を供給する。
- `core tension`: 上段作用は全 active refinement context に自動ではない。
  G-114 の `mateAtTarget` は `CoreFiber` の射である一方、G-108 の
  `HGeom` は指定 target への geometry lift に必要であり、canonical
  `pushGeometryPackage` target への lift には十分であるに留まる。
  `GeometryTransport.FiniteWitnesses.not_hGeom` /
  `no_geometryLift_to_any_target` がその条件を無条件には生成できないことを
  固定している。したがって `HGeom` を regime field に入れて universal
  lift と呼ぶのではなく、fiberwise finite problem 上の
  `UpperRouteTargetCompatible`、componentwise `HGeom`、field-level
  `UpperEdgeComponentCompatible` からなる
  `UpperRealizationCompatible` を exact domain 条件として necessity /
  sufficiency の両方向で特徴付ける。前者は各 mate component の source と
  指定 pulled-route target の間の `CoverageTransport`、`OverlapTransport`、
  coefficient hom、`raw_eq` だけを持つ `UpperRouteNonRealizationData` の
  inhabitationとする。`UpperEdgeComponentCompatible` は各 finite edge で
  coverage / overlap / coefficient / raw と support / axis / observable の
  comparison map が二 route に沿って一致する field-level 等式だけを述べる。
  完成済み `GeomReadHom`、`GeometryTotalHom` の等式、finite-diagram
  naturality 自体は premise にしない。`ObProblem` は代理 interface を新設せず、
  `InUpperReselectionOrbit` が定める actual orbit setを直接使う。もう一つの安価経路は底段の再包装であり、O11 の
  proof term に lifted geometry action の実消費を要求して防ぐ。
- `rival`: fibred 2-category の change of base・pseudofunctor の
  restriction 一般論。差は「AAT の具体塔の上で、診断障害類の
  naturality まで込みで Lean 固定する」点に置く。
- `claim boundary`: 固定した一般 carrier `U`、G-108 / G-109 で建設済み
  の塔の段(`GeomRead` 段・core 段)、G-114 の
  `ActiveRefinementBCContext`、その target pointed fiber 内に根付き、
  G-109 の local strong qualification / two-cell equality / authored
  comparator を備えた finite `FiberwiseTwoLayerTransportData` の上で語る。
  係数は動かさない。
  終対象・絶対積は導入しない。forward-only / inactive refinement は
  上段 mate の定義域に含めない。
  orbit の同値性は G-116 で `UpperStageExchangeExact` が得られた場合の
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
  構成、`UpperRealizationCompatible` を geometry hom / naturality field の包装に
  する構成、`ActiveUpperStageRegime` を caller-supplied lift certificate
  にする構成、G-109 local strong qualification / comparator を BC 結論として
  後付けする構成、離散段(`ExtInst -> Doct`)での vacuous 発火、orbit set の
  extent と定義的 membership iff だけを O11 の成果と数える構成、定数 orbit での vacuous
  naturality、**O11 の naturality を底段 (d1)–(d6) の restatement、
  または底段への pushforward 移送と既証明の底段 cochain 輸送
  (G-106 transition / G-113 O20 系)で立てる構成**(上段 lift の
  実消費を欠く形、pushforward で消える upper 成分に主張を持たない
  形)、G-109 pseudofunctor theorem の再証明、`Classical.em` だけによる
  regime 正負 witness の包装を成果と数える構成。
- `frontier`: `UpperStageExchangeExact` の場合の orbit equivalence の帰趨
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
     problem を `FiberwiseTwoLayerTransportData ctx` として固定する。この
     structure は既存 `TwoLayerTransportData P U` を raw authored data として
     持ち、各 vertex の geometry package が `GeomFiber X` にあること、
     distinguished root vertex の underlying `CoreFiber X` object が
     `ctx.targetPackage` と一致することを持つ。既存 data の
     `edgeGeometryStrong` / `edgeCoreStrong`、`twoCellBase`、comparator は
     G-109 obstruction problem の admissibility / authored datum として
     保持し、上段 BC lift の結論には数えない。`toTwoLayerTransportData` は
     この raw datum への definitional projection とし、任意 fiber morphism
     から strong qualification を生成するとは主張しない。

     G-114 の二つの canonical core route と `ctx.mate` を underlying core
     finite diagram の全 vertex / edgeへ評価し、G-108 canonical transport
     で base / pulled geometry route object と edge map を独立に生成する。
     `UpperRouteNonRealizationData ctx data i` は各 vertex の mate component
     source と指定 pulled-route target の間の `CoverageTransport`、
     `OverlapTransport`、coefficient hom、`raw_eq` だけを持つ。
     `UpperRouteTargetCompatible ctx data : Prop` は全 vertex でこの structure
     が inhabited であることを述べる。これと各 mate component の `HGeom`
     supply、および各 edge における low-level component map の commuting を
     全 field ごとに列挙する `UpperEdgeComponentCompatible ctx data` を合わせた
     `UpperRealizationCompatible ctx data : Prop` を exact 条件とする。
     geometry hom、`GeometryTotalHom` の edge naturality、coherence、orbit lawはこの predicate の
     field に持たせない。次の両方向を証明する:
     `UpperRealizationCompatible ctx data` から finite lifted BC diagram を
     構成でき、任意のそのような diagram から同じ low-level compatibility
     を回収できる。`ActiveUpperStageRegime` は compatible な raw input の
     subtype とし、diagram / mate / coherence を field に持たせない。
  2. **(b) finite lifted mate と Gr3 接続**: `ActiveUpperStageRegime` 上で
     G-114 の base route / pulled route に対応する geometry object family、
     edge map、path evaluatorと、`ctx.mate` の各 component から生成される
     actual lifted mate component family を構成する。成果物は未定義の
     global domain 上の `Functor` / `NatTrans` とは呼ばず、有限 presentation
     上の `FiniteUpperBCDiagram` とする。各 component の段射影との可換は
     `IsHomLift` 水準の等式、各 edge に対する mate naturality、nil / append
     path law、G-109 compositor / unitor に対応する coherence を証明する。
     diagram から base route / pulled route 側の
     `baseUpperData regime` / `pulledUpperData regime :
     TwoLayerTransportData P U` を構成し、その local strong qualification、
     two-cell equality、comparator の provenance を元の raw dataと G-108 /
     G-109 の生成 theorem へ戻す。
     「BC lift 後に Gr3 transport」と「Gr3 transport 後に BC lift」は
     finite path / two-cell ごとに独立生成した二経路として比較し、一方を
     他方の定義にしない。root component は root equality で transport
     した後に G-114 `ctx.mateAtTarget` へ射影されることを証明する。
     `UpperStageExchangeExact regime : Prop` は全 vertex の lifted mate
     component が `IsIso` であることと定義し、G-116 が消費する。
  3. **(c) actual obstruction-orbit naturality**: 新しい proxy class は
     導入せず、任意の既存 data に対する
     `upperObstructionOrbit data : Set (UpperDefectCochain data)` を
     `InUpperReselectionOrbit data` の extent として定義する。この
     definitional repackaging 自体は成果に数えない。(b) の finite lifted
     geometry diagramから `baseUpperData regime` の automorphism / upper
     cochain / edge reselection を `pulledUpperData regime` 側へ送る map を
     構成し、`upperRawDefectCochain` commuting と `Set.MapsTo` による二つの
     actual orbit 間の forward naturality を証明する。proof
     term は lifted geometry action を実消費し、core pushforward だけで
     閉じない。さらに `UpperStageExchangeExact regime` の場合に限り、
     inverse reselection map と両側 inverse lawを構成して direct image
     equality / orbit equivalence を与える。無条件の orbit equivalence は
     主張しない。
  4. **(d) regime 正負と非退化発火 witness**: 非恒等 G-114 active
     refinement 上で、root が `ctx.targetPackage` に一致し、nonidentity
     fiber isomorphism edge を含む `UpperRealizationCompatible` な
     nontrivial fiberwise problem と、active core context / nonempty geometry inputを
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
  `UpperStageExchangeExact` / orbit equivalence の無条件成立(G-116)は
  主張しない。
- `target proof artifacts`: G-109-qualified raw datum と root anchor を持つ
  `FiberwiseTwoLayerTransportData`、definitional
  `toTwoLayerTransportData`、`UpperRouteNonRealizationData`、
  `UpperRouteTargetCompatible` / `HGeom` /
  `UpperEdgeComponentCompatible` からなる
  `UpperRealizationCompatible`、exact liftability iff、
  `ActiveUpperStageRegime`、`FiniteUpperBCDiagram` と
  `baseUpperData` / `pulledUpperData`、lifted mate component family、edge /
  path / Gr3 coherence、二つの actual orbit 間の cochain / reselection
  map、raw-cochain commuting、orbit forward naturality、
  `UpperStageExchangeExact` conditional orbit equivalence、regime 正負
  witnessと非恒等発火 theorem、report
  `research/reports/G-115-aat-upper-stage-lift.md`。
- `target proof strategy`: F0 typing(G-109-qualified fiberwise input、root
  anchor、route-target compatibility、regime、finite geometry routes、lifted
  mate component、orbit map の signature と等式成分の
  列挙)→ K0 fiberwise input と exact regime classification → K1 geometry
  route / lifted mate と Gr3 bridge → K2 orbit map / raw-cochain
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
  `ActiveRefinementBCContext` と、G-109 admissibility / authored comparator /
  root anchor を含む raw `FiberwiseTwoLayerTransportData`、および
  sufficiency 方向だけに使う `UpperRealizationCompatible` を
  残せる。compatibility は `direction-hypothesis` であり、全 input への
  無条件供給や discharge 済み premise として扱わない。lift・mate・
  finite BC diagram・lifted mate・coherence・cochain law・naturality・
  非退化性の結論相当データの供給は
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
    `ae1ba0ea`)**(proof-use = (c) の raw cochain / orbit 指示対象の
    同定先。結論相当でない理由 = raw cochain / orbit 語彙のみで
    geometry action に沿う naturality を
    含まない)。
  - `G-109-qualified fiberwise input`: `ambient-boundary`(支える結論 =
    actual upper obstruction problem の入力。raw `TwoLayerTransportData` の
    local strong qualification / two-cell equality / authored comparator、
    全 vertex の target-fiber 条件、root / `ctx.targetPackage` equality を
    入力として許す。これらは G-109 admissibility と問題データであり、
    upper BC diagram / mate / naturality の結論を含まない)。
  - `FiberwiseTwoLayerTransportData` と projection / root comparison:
    `discharge-required`(支える結論 = (a) の型付け。discharge artifact =
    完全 signature、definitional `toTwoLayerTransportData`、root component の
    `ctx.mateAtTarget` comparison)。
  - `UpperRouteNonRealizationData` / `UpperRouteTargetCompatible`:
    `direction-hypothesis`(支える結論 = (a) の指定 target への sufficiency。
    `CoverageTransport`、`OverlapTransport`、coefficient hom、`raw_eq` だけを
    持ち、`GeomReadHom` / finite-diagram naturality は不可)。
  - `UpperEdgeComponentCompatible`: `direction-hypothesis`(支える結論 =
    (a)(b) の edge naturality sufficiency。各 raw edgeについて coverage /
    overlap / coefficient / raw / support / axis / observable comparison map の
    commuting 等式を完全列挙する。assembled `GeomReadHom` や
    `GeometryTotalHom` の等式、mate naturalityそのものは field にしない)。
  - `UpperRealizationCompatible`: `direction-hypothesis`(支える結論 =
    (a) の sufficiency 方向。discharge artifact ではない。necessity theorem
    と incompatibility witness により exact domain 条件であることを別に
    固定する)。
  - `exact upper-stage regime classification`: `discharge-required`
    (支える結論 = (a)。discharge artifact = liftability iff と、raw input+
    compatibility proof の subtype だけからなる `ActiveUpperStageRegime`。
    finite diagram / mate / coherence field は不可)。
  - `finite geometry route・lifted mate・Gr3 接続`:
    `discharge-required`(支える結論 = (b)。discharge artifact = G-114 の二
    route / mate から生成した object / edge / path family、二つの qualified
    `TwoLayerTransportData`、lifted component、`IsHomLift` 等式、edge
    naturality、path coherence、独立二経路の Gr3
    bridge。global `Functor` / `NatTrans` の無根拠な昇格と caller 供給は不可)。
  - `actual upper obstruction orbit`: `ambient-boundary`(支える結論 = (c) の
    指示対象。`InUpperReselectionOrbit` の extent は定義的読み替えに限り、
    それ自体を adequacy / discharge artifact と数えない)。
  - `raw cochain commuting と orbit forward naturality`:
    `discharge-required`(支える結論 = (c)。proof-use = (b) の lifted
    geometry action の実消費。core pushforward だけでは放電しない)。
  - `exchange-exact conditional orbit equivalence`: `discharge-required`
    (支える結論 = (c) の条件付き corollary。仮定は全 vertex component の
    `IsIso` を述べる `UpperStageExchangeExact` であり、inverse reselection
    map と inverse law の構成を要求する。G-116 がその存否を決定する)。
  - `regime 正負と非退化発火 witness`: `discharge-required`(支える結論 =
    (d)。正例・負例とも raw fixture と性質を別宣言にし、負例では G-108
    witness を G-114 generated route へ接続する。正例では geometry action
    と raw cochain / orbit movement を別々に発火させる)。
- `target route integrity gate`: fiberwise problem は G-114 target pointed
  fiber 内で型付けし、lift・mate・naturality は G-108 の geometry
  transport 判定、G-109 の local strong qualifications / path machinery、
  G-114 の canonical mate から生成する。G-114 `ctx.mate` / root での
  `ctx.mateAtTarget` の proof-use、G-108 `HGeom`、specified pulled target への
  `UpperRouteNonRealizationData`、raw edge field commuting の proof-useを
  theorem bodyで確認する。orbit の指示対象は (c) の
  actual `InUpperReselectionOrbit` に固定する。witness fixture は F0 typing
  cycle で固定し、proof body で使用しない受け渡しは実消費と数えない。
  禁止経路 — root anchor のない任意 `ctx` と任意
  `TwoLayerTransportData` の結合、任意 fiber morphism からの strong
  qualification 捏造、base equality による lift 代用、diagram / mate の
  regime field 化、core pushforward だけによる naturality、proxy class、
  orbit extent / membership iff だけによる O11 放電、空型 / 恒等への退化、
  class 構成の変更、componentwise `IsIso` の無条件化。
- `target anti-weakening rule`: revision 1 の universal upper lift へ戻さず、
  かつ単なる「compatible なら lift」を exact classification と呼ばない。
  `UpperRealizationCompatible` は G-108 realization supply、指定 target の
  non-realization component data、raw field-level edge commuting のみを述べ、
  geometry hom・mate・assembled edge naturality・coherence を field に
  持たない。
  `ActiveUpperStageRegime` は raw input と compatibility proof の subtype に
  限る。raw input の G-109 local qualifications / comparator は admissibility
  であって BC 結論に数えない。生成される finite diagram・actual mate
  component・Gr3 coherence・orbit map・cochain
  law・naturality・orbit equivalence・witness 非退化性を theorem argument、
  typeclass、structure field、certificate fieldへ移して成功扱いしない。
- `target failure policy`: fail-closed を原則とする。target pointed fiber
  内の `FiberwiseTwoLayerTransportData`、G-114 generated route に対する
  compatibility、または actual upper orbit map のいずれかが statement
  として型付かない場合は `goal-defect` で停止する。exact classification、
  Gr3 bridge、raw-cochain commuting、forward naturality の concrete
  counterexample は `target-refuted` とする。G-115 の positive / negative
  named witness が既存有限素材から構成不能と確定した場合も
  `target-refuted` とし、単なる探索停滞は停止規律に従い
  `target-blocked` とする。componentwise `UpperStageExchangeExact` の
  存否は G-116 の義務であり、G-115 の failure ではない。fixed target の変更は人間の別判断と
  する。
