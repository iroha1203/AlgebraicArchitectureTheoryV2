# G-115-aat-upper-stage-lift — geometry-refinement bridge と上段 BC contract

- `id`: `G-115-aat-upper-stage-lift`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第三項(O10–O11)。義務台帳は G-116、
  source note は n1007 §3–§5。G-114 revision 3 の reverse route は genuinely
  lax な `RefinementPackageHom` 上にあるが、G-108 `GeometryTotalHom` は exact
  `PackageTotalHom` 上にしかない。本カードはこの型の断絶を
  `RefinementGeometryHom` として埋め、G-114 canonical core mateを初めて
  geometry 段の有限 BC problemとして型付けする。G-112 / G-114の完了済みAPIは
  変更せず、後続で初めて必要になるgeometry-compatible cleavageは本カードで構成する。
- `predecessor`: G-114 revision 3(完遂済み。active refinement context、二 core
  route、canonical core mate)、G-109(完遂済み。two-layer transport、authored
  comparator、upper raw-defect cochain、reselection orbit)、G-108(完遂済み。
  exact geometry transport)、G-112(完遂済み。exact selected lift / reindexing)、
  G-110、G-106。
- `tracking issue`: [#4250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4250)
- `source note`: [n1007](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)
  (§3 義務台帳、§4 の旧 global upper lift は下記 disposition で superseded)、
  [n1001](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§3.3 塔)、
  [G-109](G-109-aat-cross-stage-coherence.md)、
  [G-114](G-114-aat-refinement-base-change.md)。
- `research aim`: (1) complete upper readingは保つがlower arrowはlax refinementである
  geometry morphismを定義し、圏構造、refinement packageへの射影、G-108 exact
  geometry morphismからのembeddingを構成する。(2) このbridge上でG-114の二
  reverse routeに対し、任意のauthored geometry direction dataへの一方向比較と、
  G-115が明示transportから生成するcartesian-compatible problem上の比較同型を分けて
  構成する。後者でfinite upper mate、solution-space同値、named decision / coherence-failure
  problemを固定する。(3) compatible locusのendpoint comparison isomorphismsからpaired
  upper-orbit intertwiningとrestricted reselectionの双方向conjugationを証明する。
  actual solutionの `IsIso` / `¬ IsIso` 評価はG-116 O12へ残す。
- `core tension`: `RefinementPackageHom` のlower fieldは
  `PointedRefinementHom`、`GeometryTotalHom.base` はexact `PackageTotalHom`であり、
  G-114 active witnessはexact comparison imageの外にある。coercionや`.upper`だけの
  一致ではroute provenanceを失う。新しいhomはlower lax refinementを実fieldに持ち、
  context/support/axis/observable transportをそのcomplete upper readingから定義し、
  lowerとupperのAtom equivalence一致を保持しなければならない。またG-109 authored
  comparatorはrouteごとの独立入力なので、上段solutionはedge naturalityとは別に
  comparator intertwiningを持つ必要がある。さらにG-112のselected strong liftは
  core-level universal propertyだけを公開し、local Support / Axis / Observableの
  realization transportを持たない。これはG-112の欠陥ではなく後続geometry段の
  新しい義務なので、完了済みGOALを遡及変更せずG-115-local cleavageとして補う。
  任意のauthored geometry legをgenerated cartesian legへ因子化して得る比較は、core
  射影がisoでもSupport / Axis / Observable写像まで可逆とは限らない。従ってraw problem
  全域では一方向比較だけを主張し、双方向transportは両route geometry leg自身を
  G-115の明示transportから生成してstrong cartesianであることを証明できるlocusで行う。
- `rival`: fibred 2-categoryのchange of baseとpseudonatural lift。差は、AATの
  `RefinementPackageHom` とgeometry reading dataに即したlax geometry categoryを
  構成し、actual upper cochain/orbitまで同じtyped routeで接続する点に置く。
- `claim boundary`: fixed carrierごとに構成する。G-115のupper problemでは係数objectを
  一つに固定し、全route legs、mate components、raw edges、comparators、reselectionの
  coefficient homをidentityに制限する。一般 `RefinementGeometryHom` の圏自体は通常の
  coefficient homを許す。carrier / coefficient base change、site / coverの変更、
  infinite diagram、全active contextへのupper solution、solutionのcanonicality、
  `IsIso` 存否決定は主張しない。任意の `UpperRefinementBCProblem` には一方向comparison
  と既存solution相対のpreservationだけを与える。solution-space同値、restricted
  reselectionの双方向transport、named decision solutionは、route geometry legsを
  caller certificateなしに生成する `GeometryCompatibleUpperRefinementBCProblem` に限る。
- `capability categories`: refinement-category、geometry-bridge、base-change、
  tower-lift、relational-naturality。
- `threshold policy`: SCORE は使わない。runtime stateはtracking Issueに置く。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、停滞なら
  `target-blocked`、反証なら `target-refuted`、全完了条件とfinal reviewを満たした
  場合だけ `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `frontier`: 全active contextでのliftability classification、raw authored problem全域の
  solution-space分類、solution choice-independence、carrier / coefficient base change、無限diagram。

- `revision disposition`:
  - revision 1 の arbitrary `ActiveRefinementBCContext` / arbitrary
    `TwoLayerTransportData` からのglobal `GeomRead` liftはsemantic connectionと
    geometry-over-refinement homを欠き `goal-defect` となった(Issue #4250 comment
    `5462812441`)。意味未確定だった旧claimをrefutedとは呼ばず、supersededと記録する。
  - revision 2 regime初稿はG-108の共変exact pushをG-114の反変lax routeに使用し、
    非可逆mateからfull orbit mapを要求したため棄却した。
  - revision 2 coherence/no-go案はlax refinement legをexact `GeometryTotalHom` として
    記述して型付かなかった。またG-115内で`¬ IsIso`を評価してO12を先取りしたため
    棄却する。
  - revision 2は欠落primitiveそのものをfixed targetとし、G-116へは評価前のactual
    `upperDecisionSolution`だけを供給する方針だったが、次項のK2b2 blockerにより
    revision 3へsupersedeされた。
  - revision 2のK2b2では、G-112のopaque selected lift上にgeneric `HGeom`を自動生成
    できないことが判明した。これはG-112を変更する理由ではない。revision 3は
    G-112 / G-114を不変の比較対象として保持し、明示的なcanonical strong liftと
    realized-refinement liftからgeometry-compatible cleavageをG-115内に構成する。
    G-114 mateとの接続はliteral endpoint equalityではなく、両universal propertyから
    生成される比較squareで固定する。caller-supplied realization fieldは追加しない。
  - revision 3 Cycle 28では、任意のraw authored geometry legから生成したendpoint
    comparisonはcore射影がisoでもgeometry-level inverse / cancellationを供給せず、
    raw solution space全体との双方向transportを構成できないことが判明した(Issue #4250
    comment `5469309646`)。一方向comparisonとcomparator preservationはPR #4279までに
    証明済みであり保持するが、raw全域のsolution-space同値要求は`goal-defect`として
    supersededする。
  - revision 4は、G-112 coverage locus、G-114 realized reverse locusと同じ分層を
    geometry段に導入する。raw authored domainには一方向comparisonを残し、明示exact /
    realized-refinement transportから両route legsを生成するcartesian-compatible locusでは
    endpoint comparison iso、solution / reselectionの双方向transport、IsIso不変性を証明する。
    `IsIso`、split、cartesianness、solutionをproblem input fieldとして受け取らない。

- `target theorem`: **Geometry-Refinement Bridge and Upper BC Relational
  Naturality Theorem**。次を構成・証明する。

  1. **(a) geometry-over-refinement category**:
     同じ `GeometryPackage U` をobjectとし、morphism
     `RefinementGeometryHom G H` が次を持つcategory
     `RefinementGeometryCategory U` を定義する。
     - `base : RefinementPackageHom ⟨G.core⟩ ⟨H.core⟩`。
     - coverage、overlap、coefficient hom、raw equality、support / axis /
       observable comparisonとreading preservation / naturality。index mapは
       `base.upper : SignedExactCoreReadingHom G.core H.core` から定義し、存在しない
       exact lower `ExtInstHom` を補わない。
     - geometry comparisonが使うAtom mapと`base.base.doctrineHom.atomEquiv`の一致。

     identity / composition / associativityを証明し、lower lax refinementを忘れる
     functor
     `refinementGeometryProjection : RefinementGeometryCategory U ⥤
       RefinementPackageTotalCategory U`
     を構成する。さらにG-108 exact morphismを
     `PointedRefinementHom.ofExact`経由で送るfaithful functor
     `exactGeometryToRefinementGeometry : GeomReadCategory U ⥤
       RefinementGeometryCategory U`
     を構成し、geometry fields、identity、composition、projection squareの可換を
     証明する。exact morphismの単なる別名や、無関係なexact lower legを追加する
     構成は禁止する。

  2. **(b) G-114 route上のfinite upper problemとactual solution**:
     まずG-115-localな `UpperGeometryCleavage` を構成する。exact側は既存の明示的
     `strongCartesianLiftOfTarget`、refinement側はrealized-locus conditionから生成される
     explicit inverse-package liftを用い、target geometry packageからsource geometry
     package、係数identityのgeometry hom、map-factor lawを構成する。Support / Axis /
     Observable comparisonとreading preservation / naturalityは各明示transportから証明し、
     `HGeom`やcompleted geometry liftを入力fieldにしない。このcleavageから二つの
     geometry-compatible reverse routeと `upperGeometryMate` を生成する。

     `upperGeometryMate` のcore projectionとG-114 `ctx.mate`の間には、exact/refinement
     cleavageのuniversal uniquenessからcomponentwise comparison isoと可換squareを
     構成する。さらに、このcore comparisonの各endpointに、上で生成したgeometry
     transportを載せたgeometry-level comparisonを構成する。任意のraw authored routeに
     対するcomparisonは一方向mapであり、geometry-level isoとは呼ばない。このcomparisonはfinite
     presentation上で自然で、両route leg、edge、G-109 authored comparatorと可換し、
     coefficient homを保つ。endpointを等しいとcastして同一視せず、geometry comparison、
     そのcore projection、両lift factor graph、mate equationを別々に実消費する。
     comparison dataはproblem入力ではなくtheorem artifactであり、G-114 actual routeから
     切り離された別fixtureを受理しない。

     `UpperRefinementBCProblem ctx` はfinite presentation `P`、root、全vertexへの
     directed `P.Path root i`、およびactual functor
     `sourceFiberDiagram : P ⥤ CoreFiber
     (ctx.configuration.targetPointAt ctx.source)`を持つ。common source
     two-layer geometry dataの各geometry package / edgeのcore projectionが、この
     fiber diagramのobject / morphismの忘却像と一致するdependent equationsを持つ。
     従って全source edgeのlower projectionは型としてfiber-verticalに固定される。
     source fiber diagramをG-114の二core routeで送ったbase / pulled route core diagramsと、
     それらを射影とする二つのG-109-qualified `TwoLayerTransportData`を持つ。
     各route geometry diagramからsource geometry diagramへのlegは
     `RefinementGeometryHom` familyとし、base legのlower射影はG-112 exact selected
     liftとG-114 base refinement liftの合成、pulled legのlower射影はG-114 pulled
     refinement liftとG-112 exact selected liftの合成に固定する。各route内の
     **full geometry naturality** はdirection-hypothesisとしてraw problemに明記し、
     その`RefinementPackageHom`射影がG-112 / G-114のmap-factor lawsと一致することを
     別theoremで証明する。core lawsだけからcoefficient / support / axis / observable
     comparisonの一致を生成しない。全係数identity条件を完全signatureに含める。
     raw problemはroute間component、route間naturality、
     comparator equation、`IsIso`、orbit lawを持たない。

     raw domainとは別に、`UpperGeometryCompatibleProblemInput ctx`を定義する。この入力は
     finite presentation、root / root paths、source fiber diagram、固定係数のsource
     geometry transport、および単一のsource
     `FixedCoefficientTwoLayerTransportOver`が持つauthored `comparator`（係数identity込み）だけを持つ。
     `UpperDefectCochain` / `upperRawDefectCochain`は別input fieldにせず各transportから導出する。
     base / pulled route comparatorを独立fieldとして持たない。G-109 pseudofunctorのmap、
     compositor / unitorはsource path / two-cell normalizationにだけ使う。反変lax refinement
     routeへG-109の共変mapを直接適用せず、G-115-local cartesian comparator pullback APIを構成する。
     具体的にはsource comparatorとinverseを各generated strong-cartesian legの
     `IsStronglyCartesian.map`でpull backし、vertical lower mapがexact identityの像であることを
     証明して`exactGeometryHomOfRefinement`でgeometry automorphismへ戻す。map-id / map-mul、
     two-stage compositor / unitor compatibilityを証明し、二route comparator / derived cochainを
     constructorが別々に生成する。route geometry legs、endpoint comparison、
     cartesianness / `IsIso` / split certificate、route-between component / equation、solutionを
     fieldに持たない。G-112 exact selected transportとG-114 realized-refinement inverse
     transportを二つの実route順序で合成してauthored-compatible route geometry / legsを生成し、
     `GeometryCompatibleUpperRefinementBCProblem ctx`を構成する。両route legのstrong
     cartesianness、finite edge naturality、係数identity、両pullback comparatorがcanonical mateと
     intertwineするglobal equationはこのconstructorからtheoremとして証明する。source two-cellから
     route comparatorを生成するcartesian pullback / exactification proofを単なるcaller equationで
     代用しない。source authored comparatorがG-109 canonical comparatorと等しいとは仮定しない。

     authored-compatible routeと`UpperGeometryCleavage`のcanonical generated routeは別構成とし、
     両lower arrowsがG-114の既存exact endpoint
     `RefinementPackageTotalCategory` isoとfactor triangleで対応する
     strong cartesian liftsであることから、`IsStronglyCartesian.domainIsoOfBaseIso`型の
     base-iso正規化を使って、既存の一方向comparisonを
     homとする `generatedBaseGeometryComparisonIsoAt` /
     `generatedPulledGeometryComparisonIsoAt` を構成する。hom / invをともにexactifyし、homが
     既存comparisonと一致することをuniversal uniquenessで証明する。inverseの
     core projection、両route factor law、hom-inv / inv-hom、coefficient identity、Support /
     Axis / Observable inverse law、edge naturality、literal authored comparatorとの
     conjugation compatibilityを別theoremで証明する。比較isoまたはそのlawsをproblem field、
     theorem argument、typeclass inputとして受け取らない。

     revision 2で構成済みの `UpperRefinementBCProblem` / `UpperRefinementBCSolution` contractは
     authored-compatible route側のcontractとして保持する。canonical generated route側に
     `GeometryCompatibleUpperRefinementBCSolution` を構成する。solutionはvertexごとのvertical
     `GeometryTotalHom` componentを持ち、そのbaseがG-115-local `upperGeometryMate`
     component、coefficient homがidentityであることを要求する。各componentを
     `exactGeometryToRefinementGeometry`でbridge categoryへ送り、geometry-level
     factorization triangle、route間edge naturality、literal authored comparatorをendpoint
     comparison isoでconjugateしたcomparatorとのintertwining、nil / append / two-cell pastingを
     独立equationsとして持つ。conjugated comparatorが元のauthored comparatorを実消費することと、
     comparison isoを戻したliteral equationを別theoremで証明する。

     endpoint comparison isosによるcomponentwise conjugationで、authored-compatible
     `UpperRefinementBCSolution`からgenerated solutionへのforward transportと、その逆向き
     transportを構成する。両transportはcomponent base、coefficient identity、triangle、edge
     naturality、authored comparator equationを別々に保存し、両側inverseを証明する。最終artifact
     は両contractのsolution typeの `Equiv` とし、元solutionをgenerated solutionのfieldに保存する
     sigma / wrapper、comparison squareへの単なる参照、proof irrelevanceだけのinverseを放電と
     数えない。named core-selected companion problem / solutionもこのequivalenceから構成する。
     canonical mate、生成した二route comparatorのglobal equation、route naturalityから
     generated solutionをconstructorとして構成し、caller-supplied solutionをO10放電と数えない。named
     `upperDecisionContext`、`upperDecisionProblem`、
     `upperDecisionSolution`をtheorem artifactとして構成する。fixtureはgenuinely lax
     active refinement(exact comparison image外)、root-connected、nonidentity
     refinement / strong edge、nonidentity comparator / raw cochain、係数成分identityを
     持つ。少なくとも一つのactual solution componentがidentity / equality transportと
     異なることをsupport / axis / observable componentの具体評価で証明し、既決core
     mateと既知の可逆twistの合成だけから従うfixtureは独立発火と数えない。ただし
     solution componentの`IsIso`または否定は本カードで証明しない。

     compatible locusの外に別のraw `ComparatorIncoherentUpperRefinementBCProblem`を置く。
     nonempty geometry endpoints、cartesianなindividual refinement-geometry legs、
     vertexwise local mate / triangleを持つが、nonidentity authored two-cell comparatorの
     global equationが成立しないnamed raw problemを構成する。comparator以外の全solution fields
     （component base、coefficient identity、triangle、edge naturality）を満たすpre-solutionを構成し、
     cartesian uniquenessから任意candidate componentがそのpre-solution componentに一致することを
     証明した上で、comparator作用のSupport / Axis / Observable具体評価から
     `UpperRefinementBCSolution` の不在を証明する。
     cartesiannessだけではcompatible locusのsource-generated comparator coherenceを含意しないことを
     示す分類負例であり、compatible solution `Equiv`をこのproblemへ適用しない。
     incoherence / non-liftability certificateをproblem fieldに持たせない。

  3. **(c) actual paired orbit intertwining**:
     `CoefficientTrivialUpperEdgeReselection` を、既存 `UpperEdgeReselection` と
     全edge automorphismのcoefficient hom = identityの証明から定義し、そのwitnessで
     生成される `InCoefficientTrivialUpperReselectionOrbit` を既存actual
     `InUpperReselectionOrbit` のsuborbitとして定義する。このsuborbitのextentや
     membership iff自体は成果に数えない。

     任意のgeometry-compatible actual solutionについて、base / pulled
     coefficient-trivial upper reselectionsがsolution
     components、factorization triangle、authored comparatorとintertwineし、かつ
     coefficient componentがidentityであるpaired relationを定義する。identity、
     vertical composition、path concatenationでの閉性、`upperRawDefectCochain`の
     componentwise intertwining、actual coefficient-trivial suborbit membershipのpaired
     preservationを証明する。compatible locusのendpoint comparison isomorphismsから
     coefficient-trivial reselectionのforward / backward conjugation transportを生成し、各edge automorphism、coefficient
     identity、solution intertwiningを保ち、実際に比較するrestricted reselection space上で
     両側inverseを証明する。このreselection transportを通じてcore-selected companionの
     cochain / paired relationへtransportし、componentwise cochainとsuborbit membershipの
     一致を導く。proof bodyはleg triangle、edge equation、comparator equation、comparison
     naturality / comparator compatibility、reselection transportを別々に実消費し、core-only
     transportで閉じない。

     `upperDecisionSolution` 上でnonidentity comparator / cochain / coefficient-trivial
     reselectionを持つnamed intertwined pairを構成し、relationとcochain theoremを
     非退化発火させる。full orbit map、selector、`Set.MapsTo`は無条件に主張しない。

  4. **(d) exchange-exactness decision interface**:
     generated geometry-compatible solutionに対し `UpperStageExchangeExact solution : Prop` を
     全vertical geometry componentsの `IsIso` と定義する。endpoint comparison
     isomorphismsによるconjugationとactual solution equationsを実消費し、これは
     core-selected companion **actual geometry solution**の
     `UpperRefinementBCSolution.component`が`IsIso`であることとpointwise iffであると証明する。
     G-114 core mateの`IsIso`とのreflectionは主張しない。
     このiffはpredicateの成立・不成立の決定とは数えない。`upperDecisionSolution`の
     canonical generated componentsについてpredicateも否定も証明せず、G-116 O12が
     actual component計算で決定する。既存full `InUpperReselectionOrbit`との一致は主張しない。

- `target theorem boundary`: Lean置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新module。
  G-108 / G-109 / G-112 / G-114 reviewed modulesは参照のみで変更しない。
  G-115-local cleavageはそれらのpublic constructors / universal propertiesから構成する。
  Research aggregate /
  full buildは禁止し、direct dependency DAGとfocused file checkだけを使う。
- `target proof artifacts`: `RefinementGeometryHom` / category / projection、exact
  faithful embeddingとprojection square、`UpperGeometryCleavage`、
  `upperGeometryMate`、任意のraw authored problemからcore-selected companionへの片方向comparison、
  `UpperGeometryCompatibleProblemInput`、G-112 / G-114から生成する二つのstrong cartesian route、
  endpoint comparison isomorphismsとcomponentwise conjugation solution equivalence、`UpperRefinementBCProblem` /
  `UpperRefinementBCSolution`、`GeometryCompatibleUpperRefinementBCProblem` /
  `GeometryCompatibleUpperRefinementBCSolution`、named `upperDecisionProblem` / solution、named
  global-comparator-incoherent problem、`CoefficientTrivialUpperEdgeReselection` / restricted actual
  suborbit、paired relation / cochain theorem、nonidentity intertwined firing、
  `UpperStageExchangeExact` companion iff、report
  `research/reports/G-115-aat-upper-stage-lift.md`。
- `target proof strategy`: F0で`RefinementPackageHom.upper`からgeometry index mapsを
  定義しhom/category/projection/exact embeddingをfocused checkする。K0 category lawsと
  exact comparison、K1 G-114 composite legs / factorization triangle、K2a raw problemと
  K2b1 core-selected solution contract、K2b2a 任意raw problemの片方向comparison、
  K2b2b certificate-free compatible inputから二つのcartesian route、endpoint isomorphisms、
  solution equivalence、K2b2c named decision / negative problems、K3 paired cochain theoremと
  conjugation、K4 premise / proof-use / axiom / nonvacuity監査。
- `target theorem completion criteria`: 全artifactがsorryなしでResearchLeanに受理され、
  axiom / placeholder auditがcleanであること。material premise / hypothesis dischargeと
  certificate provenance / proof-use / structure-field escapeを監査する。
  G-114 lower lax arrows、bridge projection、leg triangle、G-109 comparator、actual cochainの
  proof-useに加え、compatible inputからの両route生成とstrong cartesianness、endpoint inverseの
  universal uniqueness provenance、comparison isomorphismsとsolution equationsのproof-use、
  predecessor不変性を監査し、report / tracking Issueを同期する。各実装PRのfixed-head
  `$review-pr` とcompletion candidateのfinal review packetに対する独立
  `$math-lean-review` 4査読全 `No major findings` を通過した場合だけ完了とする。
- `target premise discharge policy`: `ambient-boundary`はreview済みpredecessorの入力data、
  `direction-hypothesis`はroute内naturalityに限って残す。`discharge-required`は入力からの
  Lean construction、具体finite witness、またはreview済みpredecessor theoremで放電する。
  caller-supplied argument / field / certificateだけでは放電と数えず、provenanceとproof-useを監査する。

**Target material premise ledger**

| premise | class | provenance / proof-use / discharge |
|---|---|---|
| G-114 active context / mate | ambient-boundary | PR #4246 fixed head `8f7ad8bf`、merge `3d26d993`。二lax route、composite lower legs、core mateに使用。geometry bridgeは含まない |
| G-108 geometry contract | ambient-boundary | exact geometry fieldsの語彙とlaws。lax lower homは含まないため、そのままroute legに使わない |
| G-109 two-layer / orbit data | ambient-boundary | strong edges、authored comparator、actual cochain / orbitの語彙。route間equationsは含まない |
| `RefinementGeometryHom` category / projection / exact embedding | discharge-required | 欠落primitive。lax lowerを実fieldに持ち、exact lowerを捏造しない。category lawsとfaithfulnessを証明する |
| arbitrary raw authored comparison | discharge-required | authored comparator / cochain direction dataからcore-selected companionへの片方向comparisonを構成し、route factor lawとcomparator preservationを証明する。support / axis / observable inverseやsolution-space equivalenceは主張しない |
| `UpperGeometryCompatibleProblemInput` / compatible route generation | discharge-required | route leg / comparator、comparison、`IsIso`、cartesianness certificate、solution、raw cochainをfieldに持たないsource finite dataと単一source transport comparatorから二routeを生成する。各legのstrong cartesiannessを使うG-115-local cartesian pullback / exactification APIで二comparatorを生成し、map-id / map-mul、G-109 compositor / unitor compatibility、canonical mateのglobal equation、derived cochainを証明する |
| endpoint comparison isomorphisms / solution equivalence | discharge-required | G-114 exact endpoint base iso / factor triangleで正規化したstrong-cartesian uniquenessからbase / pulled endpoint inverseを導出し、conjugation `b.inv ≫ s ≫ p.hom` と逆写像 `b.hom ≫ ĝ ≫ p.inv` が全solution fieldを保存し両側inverseであることを証明する。元solutionをwrapper / sigma fieldに保存しない |
| source fiber diagram / individual legs | direction-hypothesis | actual `CoreFiber` functorとsource data projection equations、bridge hom family、full route内geometry naturality。raw authored domainではroute間inverseを含まず、compatible inputの代替とは数えない |
| named decision / negative problems | discharge-required | source-generated comparator coherenceを含むcompatible constructorからactual `upperDecisionSolution`を構成する。別にcompatible locus外でlocal cartesian legs / local matesとcomparator以外の全solution fieldsを満たすrigid pre-solutionを持つが、global authored comparator equationが具体評価で破れるraw problemを構成する。cartesian uniquenessで任意candidateをpre-solutionへ固定してraw solution spaceの不在を示す。decision componentのIsIsoは決めずcertificate payload不可 |
| paired cochain / restricted orbit theorem | discharge-required | geometry-compatible solution上でleg triangle、edge equation、comparator equation、coefficient identityを実消費する。geometry comparisonからcoefficient-trivial reselectionの双方向transportとrestricted space上の両側inverseを生成し、そのedgewise compatibilityからcore-selected companion cochain / paired relation / suborbit membershipとの一致を導く。既存full orbitとの一致は主張しない |
| `UpperStageExchangeExact` companion iff | discharge-required | endpoint comparison isomorphismsからcanonical generated solutionとauthored-compatible companion actual geometry solutionのcomponentsについてpointwise `IsIso` iffを証明する。G-114 core mateへのreflectionは主張せず、predicateの成立証明またはO12放電とは数えない |

- `target anti-weakening rule`: 結論相当のgeometry bridge、route間solution、
  non-liftability、paired intertwiningを theorem argument、typeclass、structure /
  certificate field、opaque membershipへ移して成功扱いしない。exchange exactnessの真偽を
  theorem argument / fieldへ移さず、companion iffをpredicate成立またはO12放電と数えない。
  direction-hypothesisの各fieldはroute内naturalityだけを担い、route間結論を含めない。
  raw domainの片方向comparisonをsolution equivalenceと呼ばない。compatible inputにroute leg、
  base / pulled route comparator、comparison、`IsIso` / split、cartesianness certificate、元solutionを
  持たせない。raw cochainもinput fieldにせず、単一source transport comparatorからのcartesian
  pullback / exactificationによる二comparator生成、global equation、derived cochainを実証する。
  G-115-local cleavageをG-112/G-114 routeと無関係なparallel fixtureにせず、生成された
  geometry-level comparisonのpresentation naturality、leg / edge / authored-comparator
  compatibilityをsolution-space equivalence、restricted reselection spaceの双方向transport、
  cochain / paired relationの一致で実消費する。存在量化されたsuborbit membershipの一致だけを
  reselection witnessの対応とみなさない。
  core squareへの単なる参照や過去GOALのdefinition変更を放電扱いしない。
- `target route integrity gate`: G-115-local cleavage、selected lift、finite presentation、named decision / negative
  fixture、coefficient-trivial reselectionの出所を、certificate-free compatible input、
  G-112 / G-114 reviewed theorem、
  明示的canonical lift、または具体finite constructionに固定する。G-114とのcomparisonを
  欠くparallel route、target-fitting selection、結論側lawのfield化、
  empty / identity-only退化、片方向theoremの同値扱いを受理しない。

**受入禁止**

- lax refinement legを`GeometryTotalHom` / `PackageTotalHom`へcoerceする、`.upper`だけを
  合わせてlower provenanceを捨てる、無関係なexact lower legを追加する。
- raw problemにroute間component、triangle、edge/comparator equation、`IsIso`、
  non-liftability certificateを入れる。
- compatible inputにroute legs / comparison / `IsIso` / cartesianness certificateを入れる、
  またはsolution equivalenceの逆向きを元solution保存wrapperで定義する。
- coefficient typeの一致だけで「係数固定」とし、legs / components / edges /
  comparators / reselectionsのcoefficient homをidentityにしない。
- `upperDecisionSolution`の`IsIso` / `¬ IsIso`をG-115で決め、O12を先取りする。
- extent / membership iff、empty / discrete / identity-only fixture、solution projection、
  core-only theoremだけでO10 / O11を放電する。

- `target failure policy`:

  - `goal-defect`: certificate-free compatible inputとG-112 / G-114のpublic transport dataからも
    二つのstrong cartesian route、単一source transport comparatorからのcartesian pullback /
    exactificationによる二comparator / global equation / derived cochain、
    base-iso正規化されたendpoint comparison inverse、またはsolution / cochain
    transportを構成できず、新しいsemantic dataを人間判断なしに選ぶ必要がある。
  - `target-refuted`: category laws、named actual solution、global comparator incoherenceを持つnamed negative problem、
    paired/cochain theoremのいずれかに反例がある。
  - `target-blocked`: direct dependencyの未port / 未証明によりfocused checkが停止し、
    exact declarationと最小dependency DAGをIssueに固定した場合。
  - `target-theorem-proved`: 全artifact、正負problem、監査、PR merge、台帳同期、final
    4査読を完了した場合だけ。

- `stop reason`: なし(active)。revision 3 Cycle 28のgoal-defectは、raw authored domain全体に
  comparison isomorphismを要求したstatement defectとして確定した。人間承認revision 4は
  raw片方向comparisonを保存し、equivalenceを新しいgenerated cartesian-compatible locusへ限定する。
- `next action`: F0で`UpperGeometryCompatibleProblemInput`、二route constructor / strong
  cartesianness、二endpoint comparison isomorphisms、componentwise solution `Equiv`のLean
  signaturesを同時に固定する。その後K2b2c named positive / coherence-failure artifactへ戻る。
