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
  構成する。後者では、G-112のopaque selected liftをrealization producerから除外し、
  `strongCartesianLiftOfTarget`のexplicit canonical exact transportとG-114
  realized-refinement transportのconcrete inverse-package constructorsから、Support / Axis / Observableを双方向に運び
  reading / restrictionを反映するrealization-exact upper equivalenceを定理として生成する。
  この生成結果でfinite upper mate、solution-space同値、named decision / coherence-failure
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
  G-115の明示transportから生成してstrong cartesianであることを証明でき、さらに
  concrete inverse-package upper pairのrealization-exactnessを定理生成できるcanonicalized locusで行う。
  G-112 selected lift / G-114 actual endpointとの接続はcore comparison squareに限定し、その
  opaque domain isoをgeometry isoへ昇格しない。
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
  caller certificateなしに生成し、endpoint realization-exactnessもtheorem artifactとして
  生成する `GeometryCompatibleUpperRefinementBCProblem` に限る。任意のcore isoから
  realization-exactnessが従うとは主張しない。
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
  - revision 4 Cycle 45では、generated core endpoint isoがSupport / Axis carrier mapsと
    reading / restriction lawsを持たず、`pullGeometryPackageAlongUpperPair`もgeometry objectと
    raw systemだけを再構築するため、literal G-114 endpointからのauthored route legを構成できない
    `goal-defect`が確定した(Issue #4250 comment `5471496128`)。任意のcore isoから`HGeom`を
    導く一般則はG-108のnon-realization witnessに反するため採用しない。
  - 人間承認revision 5は、G-112 / G-114のcompleted APIを変更せず、explicit canonical exact liftと
    realized-refinement liftのconcrete inverse-package constructorsの合成に対してのみ、双方向realization transportと
    componentwise inverse lawを生成するG-115-local `RealizationExactUpperEquivalence` primitiveを置く。
    endpoint別の`HGeom`、comparison hom / inv、inverse lawをinput field、theorem argument、
    typeclass instanceとして受け取らず、primitive自身とbase / pulled endpointのinhabitationを
    Lean theoremで構成する。G-112 selected inverseに含まれるopaque `StrongCartesianLift.domainIso`は
    producerに使わず、revision 4のraw一方向comparisonとcanonicalized compatible locusの区別は保持する。
  - revision 5 Cycle 45では、G-108 `NegativeGeometryWitness.coreHom.upper`のAtom mapはinvolutionでも、
    `objectMap`が同一configuration上の異なる`ArchitectureObject`をcanonical objectへcollapseするため
    非単射であり、`ExactUpperEquivalence.forward_backward`が要求する左逆を持てないことを
    `no_negativeExactUpperEquivalence`で固定した。これはG-108のlossy selected-lift負例としての役割を
    否定せず、G-115の可逆upper負例producerとしてだけ不適合である。
  - 人間承認revision 6は、正側の`RealizationExactUpperEquivalence`、canonical exact / realized-refinement
    endpoint producer、solution / reselection / cochain責務を変更しない。負側だけを役割分離し、同じ
    component A/B Atom involutionとcontext actionを持ちながら、任意の`ArchitectureObject`の
    `StructureMaps`、`SelectedQuantities`とその選択値を保存し、configurationだけをtransportする
    G-115-local structure-preserving exact upper automorphismへ差し替える。旧`coreHom.upper`のno-goは
    producer禁止境界として保持し、新automorphismのfull computational cancellationと具体的
    realization非実現を別々に証明する。

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

     Cycle 45で不足したrealization段には、まずG-115-local
     `ExactUpperEquivalence P Q`を定義する。これは
     `forward : SignedExactCoreReadingHom P Q`、`backward : SignedExactCoreReadingHom Q P`、
     `forward.comp backward = SignedExactCoreReadingHom.refl P`、
     `backward.comp forward = SignedExactCoreReadingHom.refl Q`だけを持ち、lower morphismを要求しない。
     次に `UpperRealizationTransportSupply P Q forward` を、既存
     `RealizationTransportSupply`と同じSupport / Axis / Observable comparison、reading preservation、
     restriction naturalityを持つupper-map-indexed構造として定義する。任意の
     `f : PackageTotalHom P Q`について
     `UpperRealizationTransportSupply P Q f.upper ≃ RealizationTransportSupply P Q f`を証明し、
     G-108との互換を固定する。

     G-115-local `RealizationExactUpperEquivalence (e : ExactUpperEquivalence P Q)`は
     `homSupply : UpperRealizationTransportSupply P Q e.forward`と
     `invSupply : UpperRealizationTransportSupply Q P e.backward`、および両supplyのSupport / Axis /
     Observable comparisonについてcomponentwise hom-inv / inv-hom lawだけをfieldに持つ。
     これら6本のlawは、`e.forward_backward` / `e.backward_forward`でcontext objectとcarrier typeを
     identity側へtransportした後の等式として完全signatureを固定し、必要箇所では`HEq`または
     `eqToHom`正規化を明示する。definitional equalityやunchecked castで型差を隠さない。
     reading preservationとrestriction naturalityは各upper supplyに既存なので重複fieldにせず、
     reading reflectionは逆向きpreservationとcomponentwise inverse lawから導出する。単なる
     `HGeom × HGeom`や`GeomReadHom`の保存wrapperにはせず、identity、symmetry、compositionは
     `ExactUpperEquivalence`とrealization structureのdefinition / theoremとして構成する。また
     `h : PackageTotalHom P Q`と`h.upper = e.forward`が与えられた場合に限り`homSupply`を
     `RealizationTransportSupply P Q h`へtransportし、coreが`P`の任意の`GeometryPackage`について
     `HGeom`として読むadapterを与える。逆向きも同様とする。lower morphismを捏造せず、
     `HGeom`はexact total homが実在する方向だけに接続する。

     このdataが任意のexact upper equivalenceに存在しないこともtarget artifactとしてLeanで固定する。
     G-108 `NegativeGeometryWitness.coreHom.upper`はlossy object normalizationを含みfull upper equivalenceに
     ならないため、Cycle 45 `no_negativeExactUpperEquivalence`をproducer禁止境界として保持する。
     代わりに、その公開Atom equivalenceと同じcontext actionを使い、任意の`ArchitectureObject`の
     configurationだけをtransportして`StructureMaps` / `SelectedQuantities` / 各選択値を保持する
     `structurePreservingSwapUpper`をG-115-localに構成する。全`SignedExactCoreReadingHom` computational
     fieldsについて自己合成がreflであることを証明し、同じmapをforward / backwardとする
     `structurePreservingSwapExactUpperEquivalence`を構成する。また既存exact doctrine homと組み合わせた
     matching total hom `structurePreservingSwapCoreHom`を構成し、G-108 obstruction contextの具体
     support-reading評価から
     `not_hGeom_structurePreservingSwap :
     ¬ Nonempty (HGeom NegativeGeometryWitness.package structurePreservingSwapCoreHom)`を独立に証明する。
     その上でforward supplyをmatching total-hom adapterへ移し、
     `not_realizationExact_structurePreservingSwap :
     ¬ Nonempty (RealizationExactUpperEquivalence structurePreservingSwapExactUpperEquivalence)`へ帰着する。
     旧`NegativeGeometryWitness.not_hGeom`の単なるrename、upper pairの非実現仮定、canonical objectだけへの
     量化制限は新primitiveの非実現性と数えない。生成locusが空でないことは下記base / pulled endpoint theoremで示す。

     `UpperGeometryCompatibleProblemInput`から生成済みの各vertexについて、
     `strongCartesianLiftOfTarget`が公開するexplicit canonical exact inverse-package upper pairと
     G-114 realized-refinement inverse-package upper pairを別々の
     `ExactUpperEquivalence`として組み、`canonicalExactRealizationExactAt` /
     `realizedRefinementRealizationExactAt`を構成する。各inhabitantは対応するconcrete forward / backwardの
     context equivalenceのunit / counit、実際のcontext restriction maps、observable ring equivalenceから
     Support / Axis / Observable comparisonを構成し、upper cancellationから両側inverse、reading
     preservationとrestriction naturalityを証明する。reflectionは逆向きpreservationから導く。
     identity / symmetry / composition APIで二routeの実順序に合成し、
     `generatedBaseRouteRealizationExactAt` /
     `generatedPulledRouteRealizationExactAt`をtheorem artifactとして構成する。

     G-112 `exact_bottom_semantic_global_selected_lift_upperInverse`はcanonical inverseに
     opaque selected-domain `StrongCartesianLift.domainIso`を合成したmapなので、この4 theoremの
     producerに使用しない。既存 `baseRouteComparisonCoreIso` /
     `pulledRouteComparisonCoreIso`はG-114 actual selected endpointとのcore comparison squareとして
     保持するが、そのhom / invまたは`.upper`をconcrete mapと同一視せず、
     `RealizationExactUpperEquivalence`へ昇格しない。任意の`SignedExactCoreReadingHom`、任意の
     upper pair、G-112 selected lift、またはG-114のopaqueなuniversal-property isoだけから
     inhabitationを導いてはならない。

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
     fieldに持たない。explicit canonical exact transportとG-114 realized-refinement inverse
     transportを二つの実route順序で合成してcanonical-authored route geometry / legsを生成し、
     `GeometryCompatibleUpperRefinementBCProblem ctx`を構成する。両route legのstrong
     cartesianness、finite edge naturality、係数identity、両pullback comparatorがcanonical mateと
     intertwineするglobal equationはこのconstructorからtheoremとして証明する。source two-cellから
     route comparatorを生成するcartesian pullback / exactification proofを単なるcaller equationで
     代用しない。source authored comparatorがG-109 canonical comparatorと等しいとは仮定しない。

     canonical-authored routeと`UpperGeometryCleavage`のcanonical generated routeは、同じ二つの
     explicit inverse-package transportを異なるpresentation normalizationで組む別構成とする。
     上記theorem-generated `generatedBaseRouteRealizationExactAt` /
     `generatedPulledRouteRealizationExactAt`から両方向のcomplete geometry homを構成し、
     normalizationのunit / associativityとstrong-cartesian uniquenessを使って
     `generatedBaseGeometryComparisonIsoAt` /
     `generatedPulledGeometryComparisonIsoAt` を構成する。hom / invのcore projection、両route factor law、
     hom-inv / inv-hom、coefficient identity、Support / Axis / Observable inverse law、edge naturality、
     literal authored comparatorとのconjugation compatibilityを別theoremで証明する。
     G-114 selected endpointへの既存一方向comparisonはraw側にのみ保持し、このisoのhomとはしない。
     比較isoまたはそのlawsをproblem field、theorem argument、typeclass inputとして受け取らない。
     `RealizationExactUpperEquivalence`についてもendpoint別inhabitationをfieldやargumentから取り出すだけのproofは
     受理しない。

     revision 2で構成済みのraw `UpperRefinementBCProblem` / `UpperRefinementBCSolution` contractは
     G-114 selected route側の一方向contractとして保持し、canonicalized solution equivalenceの対象にしない。
     canonical-authored route側に `CanonicalUpperRefinementBCSolution`、canonical generated route側に
     `GeometryCompatibleUpperRefinementBCSolution` を構成する。solutionはvertexごとのvertical
     `GeometryTotalHom` componentを持ち、そのbaseがG-115-local `upperGeometryMate`
     component、coefficient homがidentityであることを要求する。各componentを
     `exactGeometryToRefinementGeometry`でbridge categoryへ送り、geometry-level
     factorization triangle、route間edge naturality、literal authored comparatorをendpoint
     comparison isoでconjugateしたcomparatorとのintertwining、nil / append / two-cell pastingを
     独立equationsとして持つ。conjugated comparatorが元のauthored comparatorを実消費することと、
     comparison isoを戻したliteral equationを別theoremで証明する。

     endpoint comparison isosによるcomponentwise conjugationで、canonical-authored
     `CanonicalUpperRefinementBCSolution`からgenerated solutionへのforward transportと、その逆向き
     transportを構成する。両transportはcomponent base、coefficient identity、triangle、edge
     naturality、authored comparator equationを別々に保存し、両側inverseを証明する。最終artifact
     は両contractのsolution typeの `Equiv` とし、元solutionをgenerated solutionのfieldに保存する
     sigma / wrapper、comparison squareへの単なる参照、proof irrelevanceだけのinverseを放電と
     数えない。named canonical companion problem / solutionもこのequivalenceから構成する。
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
     両側inverseを証明する。このreselection transportを通じてcanonical companionの
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
     canonical companion **actual geometry solution**の
     `CanonicalUpperRefinementBCSolution.component`が`IsIso`であることとpointwise iffであると証明する。
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
  `UpperGeometryCompatibleProblemInput`、`ExactUpperEquivalence`、`UpperRealizationTransportSupply`と
  total-hom supply equivalence、`RealizationExactUpperEquivalence`とidentity / symmetry / composition /
  条件付き両方向`HGeom`接続、`structurePreservingSwapUpper` / matching total hom /
  `structurePreservingSwapExactUpperEquivalence`とそのrealization-exactness非実現 theorem、
  explicit canonical exact / realized-refinement inverse-package upper equivalenceのrealization-exactness theoremと、
  そのcompositionから生成するbase / pulled route realization-exactness theorem、
  canonicalized solution contracts、G-112 / G-114から生成する二つのstrong cartesian route、
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
  K2b2b certificate-free compatible inputから二つのcartesian route、K2b2b-rで
  upper supply / `RealizationExactUpperEquivalence`の最小algebra、structure-preserving negative upper equivalence非実現 witness、explicit canonical exact /
  realized-refinement inhabitantとconcrete base / pulled composition生成、K2b2b-iでその
  realization transportを実消費するendpoint isomorphismsとsolution equivalence、K2b2c named decision / negative problems、K3 paired cochain theoremと
  conjugation、K4 premise / proof-use / axiom / nonvacuity監査。
- `target theorem completion criteria`: 全artifactがsorryなしでResearchLeanに受理され、
  axiom / placeholder auditがcleanであること。material premise / hypothesis dischargeと
  certificate provenance / proof-use / structure-field escapeを監査する。
  G-114 lower lax arrows、bridge projection、leg triangle、G-109 comparator、actual cochainの
  proof-useに加え、compatible inputからの両route生成とstrong cartesianness、endpoint inverseの
  universal uniqueness provenance、realization-exactness primitiveの両方向生成provenanceと
  Support / Axis / Observable inverse lawのproof-use、structure-preserving negative upper equivalenceでの非実現性、selected-domain isoを
  producerに使っていないこと、canonical comparison isomorphismsとsolution equationsのproof-use、
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
| realization-exact upper equivalence / endpoint generation | discharge-required | `ExactUpperEquivalence`はforward / backward `SignedExactCoreReadingHom`と両側upper cancellationだけを持つ。`UpperRealizationTransportSupply`は既存total-hom supplyと同じ三carrier map・reading preservation・naturalityをupper map上に置き、任意のtotal homでは既存`RealizationTransportSupply`との`Equiv`を証明する。`RealizationExactUpperEquivalence`は両方向upper supplyと三carrierのcomponentwise両側inverse lawだけをfieldに持ち、identity / symmetry / composition、reading reflection、exact total homが存在する方向の`HGeom` adapterを導出する。負側はG-108の公開Atom involution / context actionを保ちつつ任意`ArchitectureObject`の非configuration fieldsを保存するG-115-local `structurePreservingSwapUpper`、matching total hom、full upper cancellation、`structurePreservingSwapExactUpperEquivalence`、具体support-reading非実現 theoremを証明する。Cycle 45 `no_negativeExactUpperEquivalence`により旧lossy `coreHom.upper`をproducerに使わない。正側は`strongCartesianLiftOfTarget`のexplicit canonical exact inverse-package upper equivalenceとG-114 realized-refinement inverse-package upper equivalenceを別々に構成し、そのcompositionからbase / pulled route inhabitantsを生成する。context equivalenceのunit / counit、restriction maps、observable equivalence、upper cancellationを実消費する。lower inverseの捏造、G-112 selected inverseのopaque domain iso、任意upper pair、`HGeom × HGeom`のrename、comparison certificate、canonical/reachable objectだけへの負例の量化制限は放電と数えない |
| endpoint comparison isomorphisms / solution equivalence | discharge-required | theorem-generated canonical route realization-exact upper equivalenceから両方向complete geometry homを構成し、normalization unit / associativityとstrong-cartesian uniquenessからbase / pulled endpoint inverseを導出する。exact lower homが必要な箇所では既存forward total homだけを使用し、backward upper mapにlower inverseを付加しない。conjugation `b.inv ≫ s ≫ p.hom` と逆写像 `b.hom ≫ ĝ ≫ p.inv` がcanonical-authored / generated solutionの全fieldを保存し両側inverseであることを証明する。raw G-114 selected solution contractとのEquivや、元solutionをwrapper / sigma fieldに保存する構成は主張しない |
| source fiber diagram / individual legs | direction-hypothesis | actual `CoreFiber` functorとsource data projection equations、bridge hom family、full route内geometry naturality。raw authored domainではroute間inverseを含まず、compatible inputの代替とは数えない |
| named decision / negative problems | discharge-required | source-generated comparator coherenceを含むcompatible constructorからactual `upperDecisionSolution`を構成する。別にcompatible locus外でlocal cartesian legs / local matesとcomparator以外の全solution fieldsを満たすrigid pre-solutionを持つが、global authored comparator equationが具体評価で破れるraw problemを構成する。cartesian uniquenessで任意candidateをpre-solutionへ固定してraw solution spaceの不在を示す。decision componentのIsIsoは決めずcertificate payload不可 |
| paired cochain / restricted orbit theorem | discharge-required | geometry-compatible solution上でleg triangle、edge equation、comparator equation、coefficient identityを実消費する。geometry comparisonからcoefficient-trivial reselectionの双方向transportとrestricted space上の両側inverseを生成し、そのedgewise compatibilityからcanonical companion cochain / paired relation / suborbit membershipとの一致を導く。既存full orbitとの一致は主張しない |
| `UpperStageExchangeExact` companion iff | discharge-required | endpoint comparison isomorphismsからcanonical generated solutionとcanonical-authored companion actual geometry solutionのcomponentsについてpointwise `IsIso` iffを証明する。G-114 core mateへのreflectionは主張せず、predicateの成立証明またはO12放電とは数えない |

- `target anti-weakening rule`: 結論相当のgeometry bridge、route間solution、
  non-liftability、paired intertwiningを theorem argument、typeclass、structure /
  certificate field、opaque membershipへ移して成功扱いしない。exchange exactnessの真偽を
  theorem argument / fieldへ移さず、companion iffをpredicate成立またはO12放電と数えない。
  direction-hypothesisの各fieldはroute内naturalityだけを担い、route間結論を含めない。
  raw domainの片方向comparisonをsolution equivalenceと呼ばない。compatible inputにroute leg、
  base / pulled route comparator、comparison、`IsIso` / split、cartesianness certificate、元solutionを
  持たせない。raw cochainもinput fieldにせず、単一source transport comparatorからのcartesian
  pullback / exactificationによる二comparator生成、global equation、derived cochainを実証する。
  endpoint別の`HGeom`、`RealizationExactUpperEquivalence` inhabitant、Support / Axis / Observable map、
  reading / naturality / inverse lawもcompatible input、theorem argument、typeclass、opaque membershipに
  移さない。primitiveのfield accessorだけでendpoint theoremを閉じず、concrete inverse-package
  constructorsからcanonical exact / realized-refinement inhabitantsを独立に生成し、composition APIで
  base / pulled route inhabitantを組む。そのproof termでunit / counit、restriction、observable equivalence、
  upper cancellationを実消費する。G-112 selected inverseに含まれるopaque domain isoやG-114 selected
  endpoint comparisonをrealization producerとして使用しない。
  G-115-local cleavageをG-112/G-114 routeと無関係なparallel fixtureにせず、生成された
  geometry-level comparisonのpresentation naturality、leg / edge / authored-comparator
  compatibilityをsolution-space equivalence、restricted reselection spaceの双方向transport、
  cochain / paired relationの一致で実消費する。存在量化されたsuborbit membershipの一致だけを
  reselection witnessの対応とみなさない。
  core squareへの単なる参照や過去GOALのdefinition変更を放電扱いしない。
- `target route integrity gate`: G-115-local cleavage、selected lift、finite presentation、named decision / negative
  fixture、coefficient-trivial reselectionの出所を、certificate-free compatible input、
  G-112 / G-114 reviewed theorem、
  明示的canonical lift、concrete inverse-package realization-exactness theorem、または具体finite
  constructionに固定する。realization-exactnessは任意upper pairから選ばず、base / pulledの各生成
  declaration、canonical exact / realized-refinementの各inhabitantとそのconstructor-level dependencyを
  固定する。負側もG-108のlossy core homをupper equivalenceと呼ばず、同じAtom/context firingを持つ
  structure-preserving explicit upper equivalence、matching total hom、primitive非実現 theoremで固定する。
  G-114とのcore comparison squareを
  欠くparallel route、target-fitting selection、結論側lawのfield化、
  empty / identity-only退化、片方向theoremの同値扱いを受理しない。

**受入禁止**

- lax refinement legを`GeometryTotalHom` / `PackageTotalHom`へcoerceする、`.upper`だけを
  合わせてlower provenanceを捨てる、無関係なexact lower legを追加する。
- raw problemにroute間component、triangle、edge/comparator equation、`IsIso`、
  non-liftability certificateを入れる。
- compatible inputにroute legs / comparison / `IsIso` / cartesianness certificateを入れる、
  またはsolution equivalenceの逆向きを元solution保存wrapperで定義する。
- compatible input、theorem引数、typeclassに`HGeom`、`RealizationExactUpperEquivalence`、endpoint realization
  maps / inverse lawsを入れる、またはそれらを格納したcertificateのfield projectionだけで
  authored route legを構成する。
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
    transportを構成できず、新しいsemantic dataを人間判断なしに選ぶ必要がある。revision 6では、
    explicit canonical exact / realized-refinement inverse-package constructorsからbase / pulled
    `RealizationExactUpperEquivalence`を生成できない、selected-domain isoを使わずcanonicalized solutionを構成できない、
    structure-preserving swap upperのfull cancellationまたはmatching total homの具体support-reading非実現を
    public dataから構成できない場合もこの判定にする。旧lossy `coreHom.upper`の再利用は解消と数えない。
  - `target-refuted`: category laws、named actual solution、global comparator incoherenceを持つnamed negative problem、
    paired/cochain theoremのいずれかに反例がある。
  - `target-blocked`: direct dependencyの未port / 未証明によりfocused checkが停止し、
    exact declarationと最小dependency DAGをIssueに固定した場合。
  - `target-theorem-proved`: 全artifact、正負problem、監査、PR merge、台帳同期、final
    4査読を完了した場合だけ。

- `stop reason`: なし(active)。revision 5 Cycle 45のgoal-defectは、G-108のlossy
  `coreHom.upper`がfull upper equivalenceでないこととして確定した。人間承認revision 6は
  正側canonicalized locusを変更せず、負側だけを同じAtom/context firingを持つ
  structure-preserving exact upper automorphismへ差し替える。旧no-go theoremはproducer禁止境界として保持する。
- `next action`: K2b2b-rで`ExactUpperEquivalence` / `UpperRealizationTransportSupply` /
  `RealizationExactUpperEquivalence`、identity / symmetry / composition、条件付き`HGeom`接続、
  structure-preserving swap upper / matching total hom / exact upper equivalenceと非実現 witness、
  canonical exact / realized-refinement inhabitants、
  base / pulled composition inhabitantの完全Lean signaturesとconstructor dependencyを同時に固定する。
  その後、authored route legs / endpoint comparison isomorphismsへ進む。
