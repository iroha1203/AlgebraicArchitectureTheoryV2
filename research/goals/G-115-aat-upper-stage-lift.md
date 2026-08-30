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
  reverse routeに対し、G-115内でgeometry-compatibleなexact/refinement cleavageと
  その間のfinite upper mateを構成し、G-114 canonical core mateとの生成比較を証明する
  named decision problemを固定する。(3) 非可逆時にも意味を持つpaired upper-orbit
  intertwiningを証明し、componentwise `IsIso` の場合だけconjugation orbit同値へ
  昇格する。actual solutionの `IsIso` / `¬ IsIso` 評価はG-116 O12へ残す。
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
- `rival`: fibred 2-categoryのchange of baseとpseudonatural lift。差は、AATの
  `RefinementPackageHom` とgeometry reading dataに即したlax geometry categoryを
  構成し、actual upper cochain/orbitまで同じtyped routeで接続する点に置く。
- `claim boundary`: fixed carrierごとに構成する。G-115のupper problemでは係数objectを
  一つに固定し、全route legs、mate components、raw edges、comparators、reselectionの
  coefficient homをidentityに制限する。一般 `RefinementGeometryHom` の圏自体は通常の
  coefficient homを許す。carrier / coefficient base change、site / coverの変更、
  infinite diagram、全active contextへのupper solution、solutionのcanonicality、
  `IsIso` 存否決定は主張しない。
- `capability categories`: refinement-category、geometry-bridge、base-change、
  tower-lift、relational-naturality。
- `threshold policy`: SCORE は使わない。runtime stateはtracking Issueに置く。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、停滞なら
  `target-blocked`、反証なら `target-refuted`、全完了条件とfinal reviewを満たした
  場合だけ `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `frontier`: 全active contextでのliftability classification、canonical cleavage、
  solution choice-independence、carrier / coefficient base change、無限diagram。

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
     transportを載せたgeometry-level comparisonを構成する。このcomparisonはfinite
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

     revision 2で構成済みのcore-selected `UpperRefinementBCProblem` /
     `UpperRefinementBCSolution` contractはG-114 routeの比較対象として保持する。
     named O10 artifactには `GeometryCompatibleUpperRefinementBCProblem` と
     `GeometryCompatibleUpperRefinementBCSolution` を構成する。solutionはvertexごとの
     vertical `GeometryTotalHom` componentを持ち、そのbaseがG-115-local
     `upperGeometryMate` component、coefficient homがidentityであることを要求する。
     各componentを
     `exactGeometryToRefinementGeometry`でbridge categoryへ送り、
     `ηᵢ ≫ pulledLegᵢ = baseLegᵢ` というgeometry-level factorization triangle、
     route間edge naturality、G-109 authored comparator intertwining、nil / append /
     two-cell pastingを独立equationsとして持つ。

     geometry-compatible contractをO10以降の主contractとする。上記geometry-level
     comparisonから、各solutionのtriangle、edge naturality、authored comparator
     intertwiningを保ってcore-selected companion solutionへ送るtransportと、その逆向き
     transportを構成し、両側inverseを証明する。従って両contractのsolution spaceは
     generated equivalenceで結ばれ、比較squareを単に参照するだけではO10放電と数えない。
     named core-selected companion problem / solutionもこのtransportから構成する。
     caller-supplied solutionをO10放電と数えない。named
     `upperDecisionContext`、`upperDecisionProblem`、
     `upperDecisionSolution`をtheorem artifactとして構成する。fixtureはgenuinely lax
     active refinement(exact comparison image外)、root-connected、nonidentity
     refinement / strong edge、nonidentity comparator / raw cochain、係数成分identityを
     持つ。少なくとも一つのactual solution componentがidentity / equality transportと
     異なることをsupport / axis / observable componentの具体評価で証明し、既決core
     mateと既知の可逆twistの合成だけから従うfixtureは独立発火と数えない。ただし
     solution componentの`IsIso`または否定は本カードで証明しない。

     別に、nonempty geometry endpointsとindividual refinement-geometry legsを持つが
     route間solutionを持たないnamed geometry-compatible problemを構成し、全active
     contextへのupper solutionを主張していないことをactual negative witnessで固定する。
     この負例は `GeometryCompatibleUpperRefinementBCSolution` の不在をsupport / axis /
     observableの具体評価で証明する。comparison equivalenceで生成したcore-selected
     companionについても `UpperRefinementBCSolution` の不在を導き、どちらか一方だけの
     no-goを成果に数えない。certificateをproblem fieldに持たせない。

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
     preservationを証明する。geometry-level comparisonからcoefficient-trivial
     reselectionのforward / backward transportを生成し、各edge automorphism、coefficient
     identity、solution intertwiningを保ち、実際に比較するrestricted reselection space上で
     両側inverseを証明する。このreselection transportを通じてcore-selected companionの
     cochain / paired relationへtransportし、componentwise cochainとsuborbit membershipの
     一致を導く。proof bodyはleg triangle、edge equation、comparator equation、comparison
     naturality / comparator compatibility、reselection transportを別々に実消費し、core-only
     transportで閉じない。

     `upperDecisionSolution` 上でnonidentity comparator / cochain / coefficient-trivial
     reselectionを持つnamed intertwined pairを構成し、relationとcochain theoremを
     非退化発火させる。full orbit map、selector、`Set.MapsTo`は無条件に主張しない。

  4. **(d) exchange-exactness conditional interface**:
     geometry-compatible solutionに対し `UpperStageExchangeExact solution : Prop` を
     全vertical geometry componentsの
     `IsIso` と定義する。これを仮定した場合だけ、coefficient-trivial reselectionの
     componentwise conjugation / inverse、両側inverse law、solution comparator
     equationを実消費するraw-cochain commuting、coefficient-trivial actual suborbitの
     direct-image equality / equivalenceを証明する。既存full
     `InUpperReselectionOrbit`との一致は主張しない。`upperDecisionSolution`について
     このpredicateも否定も
     証明せず、G-116 O12がactual component計算で決定する。

- `target theorem boundary`: Lean置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新module。
  G-108 / G-109 / G-112 / G-114 reviewed modulesは参照のみで変更しない。
  G-115-local cleavageはそれらのpublic constructors / universal propertiesから構成する。
  Research aggregate /
  full buildは禁止し、direct dependency DAGとfocused file checkだけを使う。
- `target proof artifacts`: `RefinementGeometryHom` / category / projection、exact
  faithful embeddingとprojection square、`UpperGeometryCleavage`、
  `upperGeometryMate`、G-114 mateへのgeometry-level comparisonとsolution-space equivalence、`UpperRefinementBCProblem` /
  `UpperRefinementBCSolution`、`GeometryCompatibleUpperRefinementBCProblem` /
  `GeometryCompatibleUpperRefinementBCSolution`、named `upperDecisionProblem` / solution、named
  non-liftable problem、`CoefficientTrivialUpperEdgeReselection` / restricted actual
  suborbit、paired relation / cochain theorem、nonidentity intertwined firing、
  `UpperStageExchangeExact`
  conditional conjugation/orbit equivalence、report
  `research/reports/G-115-aat-upper-stage-lift.md`。
- `target proof strategy`: F0で`RefinementPackageHom.upper`からgeometry index mapsを
  定義しhom/category/projection/exact embeddingをfocused checkする。K0 category lawsと
  exact comparison、K1 G-114 composite legs / factorization triangle、K2a raw problemと
  K2b1 core-selected solution contract、K2b2a G-115-local geometry cleavage / mate comparison、
  K2b2b named decision / negative problems、K3 paired cochain theoremとconditional
  conjugation、K4 premise / proof-use / axiom / nonvacuity監査。
- `target theorem completion criteria`: 全artifactがsorryなしでResearchLeanに受理され、
  axiom / placeholder auditがcleanであること。material premise / hypothesis dischargeと
  certificate provenance / proof-use / structure-field escapeを監査する。
  G-114 lower lax arrows、bridge projection、leg triangle、G-109 comparator、actual cochainの
  proof-useに加え、G-115-local cleavageのinput generation、G-114 mate comparison、
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
| G-115-local geometry cleavage / mate comparison | discharge-required | G-112 / G-114を変更せず、明示exact strong liftとrealized-refinement inverse liftからgeometry packages / homs / map lawsを生成する。G-114 actual mateとのcore comparisonにgeometry transportを載せ、presentation naturality、leg / edge / authored-comparator compatibility、solution-space equivalenceを証明する。caller-supplied `HGeom`やcomparison certificateを受け取らない |
| source fiber diagram / individual legs | direction-hypothesis | actual `CoreFiber` functorとsource data projection equations、bridge hom family、full route内geometry naturality。route間solutionを含まず、O10放電とは数えない。naturalityのcore射影だけを既存factor lawsで証明する |
| named decision / negative problems | discharge-required | active genuinely-lax routeから生成したG-115-local geometry-compatible route上でactual solutionとactual non-liftabilityを別々に構成し、G-114 mate comparisonを実消費する。decision component自身のnonidentityを具体評価するがIsIsoは決めない。certificate payload不可 |
| paired cochain / restricted orbit theorem | discharge-required | geometry-compatible solution上でleg triangle、edge equation、comparator equation、coefficient identityを実消費する。geometry comparisonからcoefficient-trivial reselectionの双方向transportとrestricted space上の両側inverseを生成し、そのedgewise compatibilityからcore-selected companion cochain / paired relation / suborbit membershipとの一致を導く。既存full orbitとの一致は主張しない |
| `UpperStageExchangeExact solution` | direction-hypothesis | (d)のconditional interfaceでのみ仮定し、componentwise `IsIso` をconjugation / inverse / cochain / restricted-suborbit各定理で実消費する。predicateの成立証明またはO12放電とは数えない |
| conditional orbit equivalence | discharge-required | `IsIso`仮定からconjugationを構成するが、その存否は決めない |

- `target anti-weakening rule`: 結論相当のgeometry bridge、route間solution、
  non-liftability、paired intertwiningを theorem argument、typeclass、structure /
  certificate field、opaque membershipへ移して成功扱いしない。exchange exactnessは
  (d)の明記したdirection-hypothesis以外へ移さず、その仮定をpredicate成立またはO12放電と数えない。
  direction-hypothesisの各fieldはroute内naturalityだけを担い、route間結論を含めない。
  G-115-local cleavageをG-112/G-114 routeと無関係なparallel fixtureにせず、生成された
  geometry-level comparisonのpresentation naturality、leg / edge / authored-comparator
  compatibilityをsolution-space equivalence、restricted reselection spaceの双方向transport、
  cochain / paired relationの一致で実消費する。存在量化されたsuborbit membershipの一致だけを
  reselection witnessの対応とみなさない。
  core squareへの単なる参照や過去GOALのdefinition変更を放電扱いしない。
- `target route integrity gate`: G-115-local cleavage、selected lift、finite presentation、named decision / negative
  fixture、coefficient-trivial reselectionの出所を、入力data、G-112 / G-114 reviewed theorem、
  明示的canonical lift、または具体finite constructionに固定する。G-114とのcomparisonを
  欠くparallel route、target-fitting selection、結論側lawのfield化、
  empty / identity-only退化、片方向theoremの同値扱いを受理しない。

**受入禁止**

- lax refinement legを`GeometryTotalHom` / `PackageTotalHom`へcoerceする、`.upper`だけを
  合わせてlower provenanceを捨てる、無関係なexact lower legを追加する。
- raw problemにroute間component、triangle、edge/comparator equation、`IsIso`、
  non-liftability certificateを入れる。
- coefficient typeの一致だけで「係数固定」とし、legs / components / edges /
  comparators / reselectionsのcoefficient homをidentityにしない。
- `upperDecisionSolution`の`IsIso` / `¬ IsIso`をG-115で決め、O12を先取りする。
- extent / membership iff、empty / discrete / identity-only fixture、solution projection、
  core-only theoremだけでO10 / O11を放電する。

- `target failure policy`:

  - `goal-defect`: 明示exact/refinement liftのpublic transport dataからもG-115-local
    geometry cleavage、G-114へのgeometry-level comparison、またはsolution / cochain
    transportを構成できず、新しいsemantic dataを人間判断なしに選ぶ必要がある。
  - `target-refuted`: category laws、named actual solution、named non-liftable problem、
    paired/cochain theoremのいずれかに反例がある。
  - `target-blocked`: direct dependencyの未port / 未証明によりfocused checkが停止し、
    exact declarationと最小dependency DAGをIssueに固定した場合。
  - `target-theorem-proved`: 全artifact、正負problem、監査、PR merge、台帳同期、final
    4査読を完了した場合だけ。

- `stop reason`: なし(active)。revision 2 K2b2のgoal-defect判定は、完了済みG-112の
  遡及変更を前提にしていたため撤回する。
- `next action`: K2b2aでG-112 / G-114を変更せず、明示exact/refinement liftから
  `UpperGeometryCleavage`、`upperGeometryMate`、G-114 mateへのgeometry-level comparisonと
  solution-space equivalenceのLean signatureを固定する。その後K2b2 named
  positive/negative artifactへ戻る。
