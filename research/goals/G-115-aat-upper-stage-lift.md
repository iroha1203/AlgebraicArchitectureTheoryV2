# G-115-aat-upper-stage-lift — 上段 lift の非存在と最大 transport contract

- `id`: `G-115-aat-upper-stage-lift`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第三項(O10–O11)。義務台帳は G-116、
  source note は n1007 §3–§5。G-114 revision 3 の canonical core mate が
  geometry 段へ一様に持ち上がるという旧 target を、actual AAT data 上の
  no-go theorem と、持ち上がる問題に対する最大 transport contractへ改訂する。
  本カードは G-116 に named nonexact upper solution を供給し、upper summand の
  exchange-failure branch-selection evidence とする。
- `predecessor`: G-114 revision 3(完遂済み。active refinement context、二つの
  core route、canonical core mate)、G-109(完遂済み。two-layer transport、
  authored comparator、upper raw-defect cochain、reselection orbit)、
  G-108(完遂済み。geometry の共変 transport)、G-110(完遂済み。pointed
  pullback と reindexing)、G-106(完遂済み。defect / orbit 語彙)。
- `tracking issue`: [#4250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4250)
- `source note`: [n1007](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)
  (§3 義務台帳、§4 の global upper lift は下記 disposition で refuted)、
  [n1001](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§3.3 塔)、
  [G-109](G-109-aat-cross-stage-coherence.md)、
  [G-110](G-110-aat-doctrine-fiber-product.md)、
  [G-114](G-114-aat-refinement-base-change.md)。
- `research aim`: まず、G-114 の core mate と G-109-qualified routewise geometry
  data だけから上段 mate を全問題へ選ぶ uniform producer が存在しないことを、
  fixed active context 上の named geometry obstructionで証明する。次に actual
  solution がある問題について、非可逆 solution が full automorphism orbit の
  map を一般に誘導しないことを named counterexample で証明し、paired
  intertwining が無条件に残る最大の主張であることを固定する。最後に actual
  natural iso solution 上では conjugation が raw cochain と actual orbit の
  非退化な同値を与えることを示す。
- `core tension`: G-114 reverse refinement は cartesian reindexing に由来する
  反変作用だが、G-108 geometry transport は package hom に沿う共変作用である。
  従って target geometry から reverse-route geometry object を自動生成する射は
  ない。また core mate の geometry lift は存在・一意とも保証されず、一般の
  `η : G ⟶ H` は `Aut G → Aut H` を誘導しない。さらに G-109 の authored
  comparator は route ごとの独立入力なので、edge naturality だけでは raw-defect
  cochain の比較も従わない。この三点を premise で覆い隠さず、非存在・lax・exact
  の三 fixture で分離する。
- `rival`: fibred 2-category の lift obstruction と pseudonatural transformation。
  差は、抽象的な「lift があるなら」だけで終えず、AAT の actual active refinement、
  geometry package、authored comparator、upper orbit において uniform section の
  非存在と full-orbit transport の破れを有限 witnessで確定する点に置く。
- `claim scope`: 固定 carrier `U`、固定係数、G-114 active context、その target
  core fiber 内の finite directed root-connected presentation、二つの routewise
  `TwoLayerTransportData` の上で語る。carrier / 係数 base change、site / cover の
  変更、無限 diagram、component lift の canonical selection、全 solution 間の
  choice-independence は主張しない。
- `capability categories`: base-change、no-go、tower-lift、relational-naturality、
  counterexample。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に置き、
  fixed statement と completion criteria だけで完了判定する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、停滞なら
  `target-blocked`、反証なら `target-refuted`、全完了条件と final review を
  満たした場合だけ `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `frontier`: liftable problems の intrinsic classification、canonical selection、
  refinement geometry cleavage、係数 base change、無限 diagram。

- `revision disposition`:
  - revision 1 の arbitrary `ActiveRefinementBCContext` / arbitrary
    `TwoLayerTransportData` からの global `GeomRead` lift は、両者の semantic
    connection と reverse geometry primitive を欠くため `goal-defect` となった
    (Issue #4250 comment `5462812441`)。
  - revision 2 の regime 初稿は G-108 の共変 push を G-114 の反変 route に使用し、
    非可逆 mate から full orbit map を要求したため棄却した。
  - revision 2 の coherence-obstruction 案は component liftsを caller supply にし、
    canonical upper BC の存在問題を解かないまま Gr4 O10 と数えていた。また独立
    authored comparator を障害に含めず raw-cochain theoremが偽だったため棄却した。
  - 現 revision 2 は人間承認の negative branch として、旧 universal liftを
    **refuted** と確定し、solution-relative な最大 contractと exact / nonexact
    witnessを残す。旧 target と同じ強さだとは主張しない。

- `target theorem`: **Upper-Stage Lift No-Go and Maximal Transport Theorem**。
  G-114 の `ctx : ActiveRefinementBCContext` を使って次を構成・証明する。

  1. **(a) raw problem と actual solution**:
     `UpperLiftProblem ctx` は次だけを持つ。
     - finite presentation `P`、root、全 vertex への directed `P.Path root i`。
     - G-114 mate の domain fiber内の共通 source two-layer geometry diagram
       `sourceData`。その core diagramを `D` とし、root objectは
       `ctx.targetPackage` と一致する。
     - `D` を G-114 の二 core route functorで送った base / pulled core diagram。
     - 各 route core diagramを射影とする二つの G-109-qualified
       `TwoLayerTransportData P U`。各 route geometry diagramから
       `sourceData` への component familyを、G-114 の selected cartesian lift legへ
       射影する actual `GeometryTotalHom` として持ち、各 route内の edge
       naturalityを満たす。これは二つの reverse routeを個別に realizationする
       direction hypothesisであり、route間の mate componentを含まない。全三
       geometry diagramの係数を同じ objectへ同定し、全 raw edgeの coefficient
       homはidentityとする。

     raw problem は**route間**の geometry component lift、route間 edge
     naturality、route間 comparator compatibility、`IsIso`、reselection / orbit
     lawを持たない。個々の reverse legのrealizationと、二route間comparison
     solutionを混同しない。

     `UpperLiftSolution problem` は、各 vertex の `GeometryTotalHom` が
     `ctx.mate.app (D.package i)` へ射影すること、各 edge の mate naturality、
     G-109 authored comparatorを含む two-cell intertwining、nil / append / pasting
     coherenceを持つ actual finite upper mateとする。comparator intertwining を
     edge naturalityの系とはせず、solution の独立 equation として完全 signatureに
     列挙する。`UpperLiftable problem := Nonempty (UpperLiftSolution problem)` は
     domain predicateに過ぎず、その abbreviationや constructor / projectionを
     O10 の成果と数えない。

  2. **(b) uniform lift no-go (O10 negative branch)**:
     callerから不成立証明を受け取らず、named
     `upperNoLiftContext : ActiveRefinementBCContext` と
     `upperNoLiftProblem : UpperLiftProblem upperNoLiftContext` を構成する。
     fixture は fixed coefficient、nonempty geometry、directed root-connected、
     nonidentity active refinement / strong edgeと、個別にはrealizedされた二つの
     reverse geometry legsを持つ。root component
     の source / target geometry は同じ fixed coefficient上に置き、support / axis /
     observable の明示計算から、その core mateを射影とする
     `GeometryTotalHom` が存在しないことを証明する。G-108 の向きが異なる固定
     `not_hGeom` fixture を名前だけ再利用しない。

     これから `¬ UpperLiftable upperNoLiftProblem` と、全 active context / raw
     problemへ solutionを返す dependent section の非存在
     `¬ Nonempty (∀ ctx, (p : UpperLiftProblem ctx) → UpperLiftSolution p)` を証明する。
     これが revision 1 global upper lift の fixed refutationである。

  3. **(c) nonexact solution と maximal relational contract (O11 negative branch)**:
     別の named `upperLaxProblem` と actual `upperLaxSolution` を構成する。
     solution は root-connected、nonidentity edge / mate component / authored
     comparator / raw cochainを持ち、少なくとも一つの mate componentは
     `¬ IsIso` と具体評価する。

     solution に対し、base / pulled upper reselectionsが各 mate componentおよび
     authored comparatorと intertwineする paired relationを定義する。relationが
     identity、vertical composition、path concatenationで閉じ、relationを満たす
     pairについて `upperRawDefectCochain` が componentwise intertwineし、actual
     `InUpperReselectionOrbit` membershipがpairedに保存されることを証明する。

     さらに `upperLaxProblem` の固定 base reselection `rBad` を構成し、これと
     intertwineする pulled reselectionが存在しないことを証明する。従って全 base
     reselectionを送る relation-selector、full automorphism map、actual orbit間の
     `Set.MapsTo` はこの solutionに存在しない。単なる「一般の射から群準同型は
     作れない」という外部一般論ではなく、AAT の `CompositeFiberAut` と actual
     upper cochainを用いた有限計算で示す。

  4. **(d) exact solution と actual orbit equivalence**:
     第三の named `upperExactProblem` と `upperExactSolution` を構成する。全 mate
     componentsは `IsIso`、少なくとも一つは identityでなく、route edge、authored
     comparator、raw cochain、reselectionも非恒等とする。componentwise
     conjugation / inverse conjugation、両側 inverse law、solution の comparator
     equationを実消費する `upperRawDefectCochain` commuting、actual orbit の
     direct-image equality / equivalenceを証明する。

     `UpperStageExchangeExact solution : Prop` は全 component の `IsIso` と定義する。
     exactness は**選ばれた actual solution相対**であり、canonical core mateの
     choice-independent propertyとは呼ばない。`upperLaxSolution` はその否定、
     `upperExactSolution` はその肯定を供給する。

- `target theorem scope`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新 module。
  G-108〜G-110、G-114 の reviewed module は参照のみ。Research aggregate / full
  build は禁止し、direct dependency DAG と focused file checkだけを使う。
- `target proof artifacts`: `UpperLiftProblem`、`UpperLiftSolution`、
  `UpperLiftable`、named `upperNoLiftProblem` / `not_upperLiftable` / no-uniform-section、
  named `upperLaxSolution` / non-`IsIso` / `rBad` / no-selector、paired reselection・
  raw-cochain・actual orbit theorem、named `upperExactSolution` / nonidentity firing /
  conjugation orbit equivalence、`UpperStageExchangeExact`、report
  `research/reports/G-115-aat-upper-stage-lift.md`。
- `target proof strategy`: F0 で共通 source core diagram、二 functor image、二
  routewise G-109 data、solution equationsの完全signatureを固定する。K0 vertical
  geometry no-lift fixtureとuniform section反証、K1 nonexact solutionと unmatched
  automorphism、K2 paired cochain theorem、K3 exact solutionとconjugation equivalence、
  K4 declaration map・premise・proof-use・axiom・nonvacuity監査。
- `target theorem completion criteria`: 全 artifact が sorry なしで ResearchLeanに
  受理され、axiom / placeholder auditがcleanであること。material premise ledgerを
  放電し、三 fixtureの値と相互非同一性、G-114 mate / G-109 comparator / actual
  cochainのproof-useを監査すること。各実装PRのfixed-head `$review-pr` とcompletion
  candidateの独立 `$math-lean-review` 4査読全 `No major findings` を通過した場合だけ
  完了とする。

**Target material premise ledger**

| premise | class | provenance / proof-use / discharge |
|---|---|---|
| G-114 active context / mate | ambient | PR #4246 fixed head `8f7ad8bf`、merge `3d26d993`。共通sourceの二routeとcore mateに使用。geometry liftは含まない |
| G-109 routewise data | ambient | reviewed raw two-layer problem。strong edge、two-cell、authored comparatorの語彙。route間comparator equationは含まない |
| raw `UpperLiftProblem` | direction-hypothesis | common source geometry diagram、二functor image、各reverse legの個別geometry realization、fixed coefficientだけ。route間solution dataを持たず、個別legの存在はO10放電と数えない |
| `UpperLiftSolution` | conditional-domain | paired / exact theoremのactual input。solution existenceをO10放電とは数えない。comparator equationを明示する |
| named no-lift fixture / no uniform section | discharge-required | vertical geometry obstructionを具体評価し、旧global liftをrefuteする |
| named nonexact solution / no-selector | discharge-required | non-`IsIso` componentとunmatched actual automorphismを具体評価する |
| paired cochain / orbit theorem | discharge-required | solutionのedge equationとauthored comparator equationをproof bodyで別々に実消費する |
| named exact solution / orbit equivalence | discharge-required | nonidentity cochain上でconjugationとinverseを実計算する |

**受入禁止**

- geometry component lift、edge naturality、comparator equation、`IsIso`、no-lift証明、
  unmatched automorphismを raw problem の field に入れる。
- `UpperLiftable` の展開、solution constructor / projection、empty / discrete / identity-only
  fixtureだけで O10 / O11 を放電する。
- G-108 の共変 push を G-114 reverse routeの生成と呼ぶ、またはG-108の非vertical
  negative fixtureをG-114 vertical mateと同一視する。
- 非可逆 solutionからfull orbit mapを仮定する。exact solution相対の結論をcanonical
  core mateのchoice-independent exactnessと記録する。
- authored comparator equationをedge naturalityから自動生成する。

**停止条件**

- `goal-defect`: 共通 source diagramと二route image、またはsolutionのedge/comparator
  equationsが既存signatureで型付かない。
- `target-refuted`: named no-lift、nonexact no-selector、exact nontrivialのいずれかが
  構成不能、またはpaired/cochain/conjugation theoremに反例がある。
- `target-blocked`: direct dependencyの未port / 未証明によりfocused checkが停止し、
  exact declarationと最小dependency DAGをIssueに固定した場合。
- `target-theorem-proved`: 全artifact、三fixture、監査、PR merge、台帳同期、final
  4査読を完了した場合だけ。

- `stop reason`: なし(active)。
- `next action`: F0 で `UpperLiftProblem` / `UpperLiftSolution` のLean signatureを
  固定し、named vertical no-lift fixture、nonexact unmatched automorphism、exact
  solutionの三候補を既存finite witnessから探索する。
