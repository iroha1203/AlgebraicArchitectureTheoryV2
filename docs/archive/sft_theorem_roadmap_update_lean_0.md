# SFT Theorem Roadmap Lean 実装計画アーカイブ

この文書は、`docs/sft/sft_theorem_roadmap_and_research_vision.md` から分離した
Lean 実装計画の履歴である。現在の実装状態の source of truth は
`Formal/Arch/Evolution/`, `docs/aat/lean_theorem_index.md`,
`docs/aat/proof_obligations.md` を見る。

## 12. LEAN 実装計画

この節は、上の theorem roadmap を Lean 実装へ落とすための計画である。
ここでいう実装は、未証明の `theorem` を `sorry` で置くことではない。
まず carrier、boundary、compatibility predicate、theorem package を定義し、
証明できる accessor / projection / preservation theorem から積み上げる。
大きな定理は、必要な前提を `structure ... : Prop` として明示し、各 proof obligation を
小さな Lean theorem に分解してから、最終 theorem package として束ねる。

### 12.1 実装方針

基本方針:

```text
definition first
  -> boundary predicate
  -> projection / restriction theorem
  -> binary theorem
  -> finite-cover theorem
  -> theorem-package entrypoint
  -> docs / theorem index sync
```

claim boundary:

- `ForecastCone` は bounded finite path membership であり、確率、予測精度、因果証明ではない。
- `ClockedForecastCone` は global/local clock alignment のための path model であり、全実時間や scheduler completeness を主張しない。
- descent theorem は明示された cover、restriction、step-gluing、policy compatibility、observation boundary に相対化する。
- obstruction theorem は typed witness を返すが、tool extractor がすべての witness を発見するとは主張しない。
- cohomology、Yoneda、fixed point、bifurcation は、必要な algebraic / order-theoretic 前提を明示した後にだけ theorem として読む。

実装上の制約:

- `axiom`, `admit`, `sorry`, `unsafe` は導入しない。
- 証明がまだ遠い主張は、Lean theorem stub ではなく theorem package の field として置く。
- 既存の `SFTForecastCone`, `SFTConeProjection`, `SFTReachability`, `SFTEnvelope`,
  `SFTPolicy`, `SFTFieldUpdate`, `SFTArtifactAction`, `SFTInterfaceBoundary` を再利用する。
- 汎用 category / limit が必要になるまでは、まず binary cover と finite cover の concrete API で進める。
- mathlib の category theory / order theory は、内部 API が固まった後に bridge として導入する。

### 12.2 追加予定 Lean module

第一波で追加する module:

```text
Formal/Arch/Evolution/SFTClockedCone.lean
Formal/Arch/Evolution/SFTFieldCover.lean
Formal/Arch/Evolution/SFTDescent.lean
```

現時点の Lean surface では、`SFTClockedCone.lean` が exact shared-clock cone core、
`SFTFieldCover.lean` が binary cover API、`SFTDescent.lean` が exact clocked cone 上の
binary descent surface を持つ。no-lift / local-identification から typed obstruction へ接続する
最小 bridge は `SFTTheoremRoadmap.lean` に置き、独立 module への分割は後続作業とする。

第二波で追加する module:

```text
Formal/Arch/Evolution/SFTMinimalEnvelope.lean
Formal/Arch/Evolution/SFTAttractorGluing.lean
Formal/Arch/Evolution/SFTGovernanceSynthesis.lean
Formal/Arch/Evolution/SFTAgenticConfluence.lean
Formal/Arch/Evolution/SFTEvolutionaryEquivalence.lean
```

第三波で追加する module:

```text
Formal/Arch/Evolution/SFTConeCohomology.lean
Formal/Arch/Evolution/SFTArtifactYoneda.lean
Formal/Arch/Evolution/SFTCalibrationFixedPoint.lean
Formal/Arch/Evolution/SFTLifecycleBifurcation.lean
Formal/Arch/Evolution/SFTFieldShapingFixedPoint.lean
Formal/Arch/Evolution/SFTFundamentalModularity.lean
```

各波の最後に更新する入口:

```text
Formal.lean
Formal/Arch/Evolution/SFTTheoremPackages.lean
docs/aat/lean_theorem_index.md
docs/aat/proof_obligations.md
```

### 12.3 ForecastCone Descent Theorem

Lean anchors:

```text
ClockedFieldStep
IdleSupportedStep
ClockedFieldPath
ClockedForecastCone
BinaryFieldCover
FieldCover
CompatibleLocalConeFamily
ForecastConeDescent
forecastCone_descent_binary
forecastCone_descent_finiteCover
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTClockedCone.lean
Formal/Arch/Evolution/SFTFieldCover.lean
Formal/Arch/Evolution/SFTDescent.lean
```

第一段階では、clocked path を既存の `ArchitecturePath` 上に定義する。

```text
ClockedFieldStep support relation source target
  = active supported step
  | idle stutter step

ClockedFieldPath support relation source target
  = ArchitecturePath (ClockedFieldStep support relation) source target

ClockedForecastCone support relation source horizon target path
  = ArchitecturePath.length path = horizon
```

`ClockedForecastCone` は、通常の `ForecastCone` の `<= horizon` と異なり、
共有 clock 上の tick 数をそろえるために最初は exact horizon として扱う。
そのうえで次を証明する。

```text
ClockedForecastCone.length_eq_horizon
ClockedForecastCone.length_le_horizon
BoundedClockedForecastCone.of_clockedForecastCone
BoundedClockedForecastCone.monotone_horizon
boundedClockedForecastCone_of_forecastCone
clockedForecastCone_of_forecastCone
```

`ClockedForecastCone` 自体は exact horizon を保持し、horizon extension の monotonicity は
`BoundedClockedForecastCone` または explicit idle-padding bridge として読む。

第二段階では binary cover を concrete に定義する。

```text
BinaryFieldCover Global Left Right Interface where
  restrictLeft  : Global -> Left
  restrictRight : Global -> Right
  leftInterface : Left -> Interface
  rightInterface : Right -> Interface
  compatible    : Left -> Right -> Prop
  glue          : (l : Left) -> (r : Right) -> compatible l r -> Global
  glue_left     : ...
  glue_right    : ...
  global_ext    : ...
```

support、policy、step relation は cover と独立に持たせず、restriction compatibility
を theorem-bearing premise として分ける。

```text
RestrictsSupport
RestrictsStepRelation
PreservesPolicy
PreservesObservationBoundary
GlobalStepProjects
CompatibleLocalStepGlues
IdleStepProjects
IdleStepGlues
```

第三段階で、cone object を sigma type として固定する。

```text
ClockedConeObject support relation source horizon :=
  Sigma fun target =>
    Sigma fun path =>
      ClockedForecastCone support relation source horizon target path

CompatibleBinaryConeFamily cover leftModel rightModel interfaceModel horizon :=
  compatible pair of local ClockedConeObject values
```

binary descent の statement は、まず `Equiv` として実装する。

```text
forecastCone_descent_binary :
  BinaryDescentAssumptions cover globalModel localModels source horizon ->
    ClockedConeObject globalSupport globalRelation source horizon
      ≃
    CompatibleBinaryConeFamily cover localModels source horizon
```

証明戦略:

1. global clocked path を各 region へ射影する。
2. active step は local active または local idle へ写す。
3. local pair の interface projection が tick ごとに一致することを induction で示す。
4. 逆向きは compatible local tick pair を global tick に glue する。
5. `glue_unique` と step-gluing assumption で左右逆写像を証明する。

finite cover 版は binary 版の後に進める。
最初は full category-theoretic limit ではなく、finite index と Cech simplex を concrete に定義する。

```text
FiniteFieldCover
CechSimplex
LocalConeOnSimplex
CompatibleLocalConeFamily
forecastCone_descent_finiteCover
```

proof obligation:

- clocked path の exact horizon と unclocked cone の bounded horizon の bridge。
- stutter step が observation boundary と policy boundary を破らないこと。
- local operation family の tick alignment。
- interface overlap 上の endpoint compatibility。
- finite cover の Cech compatibility を binary overlap と一致させる補題。

最初の Issue 単位:

```text
Issue A: ClockedFieldStep / ClockedForecastCone core
Issue B: BinaryFieldCover and compatible local cone family
Issue C: forecastCone_descent_binary
Issue D: finite cover Cech compatibility skeleton
Issue E: forecastCone_descent_finiteCover theorem package
```

### 12.4 Modularity Representation Theorem

Lean anchors:

```text
SFTModuleBoundary
ForecastConeSheafCondition
GlobalEvolutionRepresentation
modularity_representation
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTDescent.lean
```

`SFTModuleBoundary` は最初から直観的な言葉で定義しない。
まず theorem-bearing definition として、descent 条件を module boundary の意味にする。

```text
SFTModuleBoundary cover :=
  forall admissibleModel horizon source,
    ForecastConeDescent cover admissibleModel source horizon
```

次に、global path representation を別 predicate にする。

```text
GlobalEvolutionRepresentable cover model :=
  forall horizon source,
    ClockedConeObject global source horizon
      ≃ CompatibleLocalConeFamily cover model source horizon
```

定理は二段階に分ける。

```text
moduleBoundary_iff_forecastConeDescent
forecastConeDescent_iff_globalEvolutionRepresentable
modularity_representation
```

最初の定理は、定義の選び方により短い証明になる。
二番目の定理は、`ForecastConeDescent` の内部表現を `Equiv` にした場合は accessor theorem、
`map + inverse + laws` にした場合は `Equiv` への packaging theorem になる。

proof obligation:

- "all admissible bounded fields" の Lean 上の index を `AdmissibleSFTModel` として定義する。
- unique representability を `Equiv` の left/right inverse として読む。
- cover が module boundary であることを static API cleanliness ではなく future-gluing boundary として記録する。

### 12.5 Descent Obstruction Theorem

Lean anchors:

```text
DescentFailureKind
DescentFailure
DescentObstruction
DescentGap
LocalFamilyDoesNotLift
GlobalPathsLocallyIdentified
descent_obstruction_of_surjectivity_failure
descent_obstruction_of_injectivity_failure
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTDescentObstruction.lean
```

failure kind は inductive type として置く。

```text
inductive DescentFailureKind where
  | hiddenCoupling
  | missingInterfaceInvariant
  | unsupportedGlobalOperation
  | policyConflict
  | observationBoundaryLeak
  | unknownRemainderExpansion
```

obstruction witness は、failure kind と evidence boundary を分けて持つ。

```text
structure DescentObstruction where
  kind : DescentFailureKind
  localWitness : Prop
  globalWitness : Prop
  interfaceWitness : Prop
  theoremBoundary : Prop
  observationBoundary : Prop
  nonConclusions : Prop
```

surjectivity failure と injectivity failure は、descent map を明示して定義する。

```text
GlobalToCompatibleLocal :
  ClockedConeObject global source h ->
  CompatibleLocalConeFamily cover model source h

LocalFamilyDoesNotLift family :=
  not exists globalCone, GlobalToCompatibleLocal globalCone = family

GlobalPathsLocallyIdentified p q :=
  p != q and GlobalToCompatibleLocal p = GlobalToCompatibleLocal q
```

主要 theorem は、obstruction classifier の completeness を前提にする。

```text
DescentObstructionClassifierComplete classifier :=
  forall failure, exists obstruction, classifier failure obstruction

descent_obstruction_of_surjectivity_failure :
  DescentObstructionClassifierComplete classifier ->
  LocalFamilyDoesNotLift family ->
    exists obstruction, classifier (.surjectivity family) obstruction

descent_obstruction_of_injectivity_failure :
  DescentObstructionClassifierComplete classifier ->
  GlobalPathsLocallyIdentified p q ->
    exists obstruction, classifier (.injectivity p q) obstruction
```

proof obligation:

- classifier completeness は theorem の前提であり、tooling が完全に分類できるとは読まない。
- `DescentGap` と `ConsequenceEnvelope.obstructionCandidates` の bridge を後続で追加する。
- finite counterexample を一つ作り、hidden coupling と unsupported global operation の witness が別物であることを示す。

### 12.6 Cone Cohomology Theorem

Lean anchors:

```text
ForecastConePresheaf
CechCone0
CechCone1
CechConeCocycle
CechConeCoboundary
ConeH1Vanishes
cone_h1_vanishes_iff_local_futures_glue
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTConeCohomology.lean
```

この theorem は最初から一般の sheaf cohomology として実装しない。
ForecastCone は path family であり、自然に abelian group とは限らない。
第一段階では、local-to-global obstruction を Čech-style complex に似た concrete witness API として実装する。

```text
ForecastConePresheaf cover model horizon
Cech0 := compatible local 0-cochains
Cech1 := overlap disagreement witnesses
Cech1Cocycle := triple-overlap compatibility
Cech1Coboundary := disagreement explained by local reindexing
ConeH1Vanishes := forall cocycle, exists coboundary explanation
```

主要 theorem:

```text
cone_h1_vanishes_of_forecastConeDescent :
  ForecastConeDescent cover model source h ->
    ConeH1Vanishes cover model source h

forecastConeDescent_of_cone_h1_vanishes
  : ConeH1Vanishes cover model source h ->
    EffectiveLocalLift cover model source h ->
      ForecastConeDescent cover model source h
```

`H0` は global reachable futures と一致させる。

```text
cone_h0_equiv_globalCone :
  ForecastConeDescent cover model source h ->
    CechCone0 cover model source h ≃ ClockedConeObject global source h
```

第二段階で、必要なら mathlib の algebraic topology / category theory へ bridge する。
その場合も、`ConeH1Vanishes` を formal anchor として残し、一般 cohomology は追加 theorem にする。

proof obligation:

- path family を quotient / setoid にするか、raw dependent path のまま扱うかを決める。
- triple overlap を finite cover の Cech simplex と接続する。
- obstruction witness と `H1` nonzero の対応は、classifier completeness を前提にする。

### 12.7 Evolutionary Normal Form Theorem

Lean anchors:

```text
StepRegion
IndependentClockedStep
CommutingClockedSteps
EvolutionPathRewrite
EvolutionaryNormalForm
evolutionary_normal_form
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTAgenticConfluence.lean
```

normal form は clocked path 上の rewrite として扱う。

```text
IndependentClockedStep s1 s2 :=
  disjoint affected regions
  + compatible interface effects
  + policy commutation

CommutingClockedSteps s1 s2 :=
  exists square filler, applying s1 then s2 equals applying s2 then s1

EvolutionPathRewrite :=
  adjacent independent steps may be swapped
```

normal form:

```text
interface synchronization
  ; local block for U_i
  ; local block for U_j
  ; ...
  ; interface synchronization
```

Lean では、最初に binary / finite ordered regions に対して block ordering を定義する。

```text
RegionOrderedPath
BlockNormalForm
PathEquivalentByIndependentSwaps
```

主要 theorem:

```text
independent_swap_preserves_clockedCone :
  CommutingClockedSteps s1 s2 ->
    PathEquivalentByIndependentSwaps p q ->
      ClockedForecastCone ... p ->
        ClockedForecastCone ... q

evolutionary_normal_form :
  ForecastConeDescent cover model source h ->
  LocalConfluenceOfIndependentSteps model ->
  TerminatingRewriteMeasure model ->
    exists nf, BlockNormalForm nf and PathEquivalentByIndependentSwaps path nf
```

proof obligation:

- adjacent swap が dependent endpoints を保つための square filler API。
- termination measure は path length ではなく inversion count で定義する。
- confluence は全 step ではなく independent local steps に限定する。

### 12.8 Cone-Conservative Observation Theorem

Lean anchors:

```text
ConeObservation
ConeEquivalentAt
ConeConservativeObservation
coneConservativeObservation
not_coneConservative_counterexample
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTMinimalEnvelope.lean
```

定義:

```text
ConeObservation Field Obs :=
  Field -> Obs

ConeEquivalentAt F G :=
  forall horizon support relation source,
    ClockedConeObject F source horizon ≃ ClockedConeObject G source horizon

ConeConservativeObservation O :=
  forall F G, O F = O G -> ConeEquivalentAt F G
```

主要 theorem:

```text
coneConservativeObservation_preserves_cones :
  ConeConservativeObservation O ->
  O F = O G ->
    ConeEquivalentAt F G

not_coneConservative_counterexample :
  not ConeConservativeObservation O ->
    exists F G, O F = O G and not ConeEquivalentAt F G
```

二番目は classical logic を使えば定義展開から証明できる。
実務上重要なのは、`ObservationBoundary` と `ConsequenceEnvelope` への bridge である。

```text
EnvelopeProjectionConeConservative
coneConservative_envelope_projection_preserves_decision_surface
```

proof obligation:

- `ConeEquivalentAt` の horizon / support / relation の quantification を広くしすぎない。
- observation equality は selected observation universe に相対化する。
- "metric adequacy" は empirical claim ではなく cone distinction preservation として読む。

### 12.9 Minimal ConsequenceEnvelope Theorem

Lean anchors:

```text
ReviewDecisionClass
PathIndistinguishableFor
DecisionSoundEnvelope
MinimalConsequenceEnvelope
minimalConsequenceEnvelope
minimalEnvelope_factors
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTMinimalEnvelope.lean
```

review decision class を predicate として置く。

```text
ReviewDecisionClass ConePath Decision :=
  ConePath -> Decision -> Prop
```

path indistinguishability は setoid にする。

```text
PathIndistinguishableFor Q p q :=
  forall decision, Q p decision <-> Q q decision
```

`Setoid` にするため、反射、対称、推移を証明する。

```text
pathIndistinguishableSetoid Q
MinimalEnvelope Q cone := Quot (pathIndistinguishableSetoid Q)
```

sound envelope projection:

```text
DecisionSoundEnvelope Q projection :=
  forall p q, projection p = projection q -> PathIndistinguishableFor Q p q
```

主要 theorem:

```text
minimalEnvelope_sound :
  DecisionSoundEnvelope Q (Quot.mk _)

minimalEnvelope_factors :
  DecisionSoundEnvelope Q projection ->
    exists factor,
      forall p, factor (Quot.mk _ p) = projection p
```

ここで向きに注意する。
`ForecastCone / approx_Q` は decision distinction を潰さない最小 quotient である。
任意の sound envelope が同じ indistinguishable path を同一視する場合、factorization が成立する。
Lean 上では、soundness だけでなく quotient-respecting 条件を分ける。

```text
EnvelopeRespectsDecisionEquivalence Q projection :=
  forall p q, PathIndistinguishableFor Q p q -> projection p = projection q
```

proof obligation:

- `ConsequenceEnvelope` 既存構造と quotient object の bridge。
- selected cone family が finite list の場合の executable quotient approximation。
- review decision が partial / unknown の場合の three-valued decision class。

### 12.10 Modular Attractor Theorem

Lean anchors:

```text
CompatibleRegionFamily
GluedStableRegion
AttractorGluing
BasinGluing
modular_attractor
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTAttractorGluing.lean
```

既存の `StableRegion`, `ReachablePreimage`, `MayReach`, `MustReach` を使う。

```text
CompatibleRegionFamily cover localRegions :=
  forall overlap, local regions agree on overlap

GluedRegion global :=
  forall i, localRegion i (restrict i global)
```

主要 theorem:

```text
stableRegion_glued_of_local :
  ForecastConeDescent cover model source h ->
  CompatibleRegionFamily cover localRegions ->
  (forall i, StableRegion localSupport_i localRelation_i localRegion_i) ->
    StableRegion globalSupport globalRelation (GluedRegion cover localRegions)

basin_gluing :
  ForecastConeDescent cover model source h ->
    ReachablePreimage globalSupport globalRelation h gluedRegion
      ≃
    CompatibleLocalBasinFamily cover localRegions h
```

証明戦略:

1. global supported step を local step family に射影する。
2. local stable closure を各 region で適用する。
3. overlap compatibility から glued region に戻す。
4. basin は `ReachablePreimage = MayReach` と descent equivalence を使って示す。

proof obligation:

- target region の overlap compatibility。
- local stable region が idle step に閉じていること。
- basin equivalence では existential witness の transport が必要。

### 12.11 Governance Synthesis Theorem

Lean anchors:

```text
PathFamily
BadPathFamily
DesiredPathFamily
GuardBasis
GuardSet
HitsBadWitnesses
MissesDesiredWitnesses
GovernanceSynthesisComplete
governance_synthesis
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTGovernanceSynthesis.lean
```

既存の `GovernanceIntervention`, `SupportTransformation`,
`PointwiseSupportInclusion`, `ForecastConeProjection` を再利用する。

定義:

```text
PathFamily support relation source h :=
  forall target path, ForecastCone support relation source h target path -> Prop

Guard guardBasis :=
  operation / path witness を許可または除外する predicate

GuardSetHits B guards :=
  forall badPath in B, exists guard in guards, guard excludes badPath

GuardSetMisses D guards :=
  forall desiredPath in D, forall guard in guards, not guard excludes desiredPath
```

governance intervention と guard set の対応は、complete basis を前提にする。

```text
GuardBasisComplete basis :=
  guard sets correspond to support transformations

governance_synthesis :
  GuardBasisComplete basis ->
    (exists intervention,
      PreservesDesiredPaths intervention D
        and ExcludesBadPaths intervention B)
    <->
    (exists guards,
      GuardSetHits B guards
        and GuardSetMisses D guards)
```

proof obligation:

- "preserves desired" は same path witness を保存するのか、projected path を保存するのかを分ける。
- restrictive intervention は support narrowing なので、bad path removal と desired path preservation の両方に exact support characterization が必要。
- governance effectiveness、incident reduction、human compliance は non-conclusion として残す。

### 12.12 Closed-Loop Calibration Fixed Point Theorem

Lean anchors:

```text
FieldEstimateRefinement
PosteriorUpdateOperator
ForecastErrorRefining
BoundaryExpansionRequired
ClosedLoopCalibrationRun
closedLoopCalibration_fixedPoint
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTCalibrationFixedPoint.lean
```

既存の `FieldUpdate`, `ObservedOutcome`, `PosteriorFieldRecord`, `UpdateSound` を使う。

refinement order:

```text
FieldEstimateRefinement E1 E2 :=
  E2 preserves selected evidence of E1
  + E2 refines forecast error records
  + E2 preserves non-conclusions
```

update operator:

```text
PosteriorUpdateOperator Estimate :=
  Estimate -> Estimate

MonotoneUpdate U :=
  forall E1 E2, FieldEstimateRefinement E1 E2 ->
    FieldEstimateRefinement (U E1) (U E2)
```

fixed point theorem は、finite height か well-founded strict refinement を前提にする。

```text
FiniteRefinementHeight Estimate
BoundaryExpansionTrigger U

closedLoopCalibration_fixedPoint :
  FiniteRefinementHeight Estimate ->
  MonotoneUpdate U ->
  EvidencePreserving U ->
  BoundaryExplicit U ->
  NonConclusionPreserving U ->
  ForecastErrorRefining U ->
    exists n,
      FixedPoint U (iterate U n E0)
        or BoundaryExpansionRequired U (iterate U n E0)
```

proof obligation:

- monotone だけでは有限時間 fixed point は出ないため、finite height / no infinite strict refinement を明示する。
- boundary expansion requirement は failure ではなく、modeling boundary を広げる必要があるという typed outcome。
- calibration は accuracy improvement ではなく record refinement として読む。

### 12.13 Artifact Yoneda Theorem

Lean anchors:

```text
ArtifactProbe
ArtifactProbeCategory
ArtifactResponse
ArtifactResponseFunctor
SFTSeparatingProbeFamily
SFTFieldEquivalence
artifact_yoneda
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTArtifactYoneda.lean
```

第一段階では、full Yoneda lemma を使わず、separating probes の theorem として実装する。

```text
ArtifactResponse F probe :=
  ForecastConeFamilyAfterAction probe F

ResponsesEquivalent F G :=
  forall probe, ArtifactResponse F probe ≃ ArtifactResponse G probe

SFTSeparatingProbeFamily probes :=
  forall F G, ResponsesEquivalentOn probes F G -> SFTFieldEquivalence F G
```

主要 theorem:

```text
artifact_yoneda :
  SFTSeparatingProbeFamily probes ->
  ResponsesEquivalentOn probes F G ->
    SFTFieldEquivalence F G
```

第二段階で、`ArtifactProbeCategory` と contravariant response functor を定義する。

```text
Phi F : Artᵒᵖ -> ConeCat
```

mathlib の category theory へ接続する場合は、次を別 theorem とする。

```text
artifact_response_functor_natural_equiv_of_field_equiv
field_equiv_of_artifact_response_natural_equiv
```

proof obligation:

- probe family が "sufficiently separating" であることは強い前提として明示する。
- artifact response は human intention や market outcome ではなく candidate update / cone family。
- `F ≃_SFT G` は field state equality ではなく selected SFT observable/evolutionary equivalence。

### 12.14 Agentic Confluence Theorem

Lean anchors:

```text
AgentProposalSystem
AcceptedProposalStep
LocalProposalTerminates
LocalProposalConfluent
PolicyCommutationInvariant
FairInterleaving
GlobalConeQuotient
agentic_confluence
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTAgenticConfluence.lean
```

proposal system は rewriting system として扱う。

```text
AgentProposalSystem region :=
  proposal step relation
  + acceptance policy
  + interface preservation predicate
```

local confluence:

```text
LocalConfluent step :=
  forall a b c, step a b -> step a c ->
    exists d, Reaches step b d and Reaches step c d
```

termination:

```text
Terminates step :=
  WellFounded inverseStep
```

主要 theorem は Newman-style lemma を local proposal system に適用し、
descent で global quotient へ持ち上げる。

```text
local_confluence_unique_normal_form :
  Terminates step ->
  LocalConfluent step ->
    UniqueNormalForm step

agentic_confluence :
  (forall i, LocalProposalTerminates agent_i) ->
  (forall i, LocalProposalConfluent agent_i) ->
  ForecastConeDescent cover model source h ->
  InterfaceConstraintsPreserved agents ->
  PolicyCommutationInvariant policies ->
    forall fair1 fair2,
      EquivalentInGlobalConeQuotient fair1 fair2
```

proof obligation:

- fairness は scheduler completeness ではなく、accepted local proposal が無限に無視されない条件。
- local normal form と global cone quotient の bridge。
- policy commutation invariant は review/CI order の差が accepted quotient を変えないこととして定義する。

### 12.15 Lifecycle Bifurcation Theorem

Lean anchors:

```text
LifecycleInterventionKind
ObstructionMeasure
RepairFeasible
RepairOnlyPreserves
LifecyclePressureRegime
lifecycle_bifurcation
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTLifecycleBifurcation.lean
```

measure は最初は `Nat` または `WithTop Nat` にする。

```text
ObstructionMeasure Field := Field -> Nat

LifecycleInterventionKind :=
  repair | migration | contraction | deletion | endOfLife
```

threshold theorem は、measure の soundness premise を明示する。

```text
RepairFeasibilitySound Omega threshold :=
  forall F, Omega F < threshold -> RepairFeasible F

RepairFailureSound Omega threshold :=
  forall F, threshold <= Omega F -> not RepairOnlyPreserves F targetRegion

lifecycle_bifurcation :
  RepairFeasibilitySound Omega threshold ->
  RepairFailureSound Omega threshold ->
    (Omega F < threshold -> RepairFeasible F)
      and
    (threshold <= Omega F -> exists regime,
      LifecyclePressureRegime regime F)
```

proof obligation:

- threshold は empirical calibration ではなく、選択された measure/premise に相対化した formal threshold。
- repair failure から migration/deletion/end-of-life のどれを選ぶかは、追加 classifier が必要。
- operational cost、組織判断、business lifecycle は non-conclusion。

### 12.16 Field-Shaping Fixed Point Theorem

Lean anchors:

```text
SupportTransformationOrder
FieldShapingOperator
DesiredPathPreserving
BadWitnessExcluding
MinimalFieldShaping
fieldShaping_fixedPoint
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTFieldShapingFixedPoint.lean
```

support transformation に order を入れる。

```text
T1 <= T2 :=
  T1 excludes at least the bad paths excluded by T2
  + T1 preserves at least the desired paths preserved by T2
```

complete lattice はいきなり全 support transformation に主張しない。
選択された bounded transformation universe を定義する。

```text
BoundedSupportTransformationUniverse
CompleteLattice selectedTransformations
FieldShapingOperator S : T -> T
Monotone S
```

主要 theorem:

```text
fieldShaping_fixedPoint :
  CompleteLattice T ->
  Monotone S ->
    exists lfp, LeastFixedPoint S lfp

minimal_field_shaping_preserves_desired_excludes_bad :
  LeastFixedPoint S lfp ->
  DesiredPreservationEncoded S D ->
  BadExclusionEncoded S B ->
    DesiredPathPreserving lfp D and BadWitnessExcluding lfp B
```

mathlib の `OrderHom`, `lfp`, complete lattice theorem を使える場合は、それに bridge する。
使わない場合は finite lattice 版から始める。

proof obligation:

- support transformation order の向き。
- desired path preservation と bad witness exclusion が単調条件として表現できること。
- fixed point は governance が実効的に成功したという empirical claim ではない。

### 12.17 Evolutionary Invariance Theorem

Lean anchors:

```text
ConeFunctor
ForecastConeNaturallyEquivalent
EvolutionaryEquivalence
ForecastConePreservingTransformation
evolutionary_invariance
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTEvolutionaryEquivalence.lean
```

第一段階では、natural equivalence を concrete family として定義する。

```text
ForecastConeEquivalentAcrossHorizons F G :=
  forall artifact support policy observation horizon,
    ClockedConeObject F artifact support policy observation horizon
      ≃
    ClockedConeObject G artifact support policy observation horizon

EvolutionaryEquivalence F G :=
  ForecastConeEquivalentAcrossHorizons F G
```

この定義を採用する場合、主 theorem は introduction theorem になる。

```text
evolutionary_invariance :
  ForecastConeEquivalentAcrossHorizons F G ->
    EvolutionaryEquivalence F G
```

第二段階で、field transformation を追加する。

```text
ForecastConePreservingTransformation T :=
  forall F, EvolutionaryEquivalence F (T F)

refactoring_preserves_evolutionary_equivalence :
  ForecastConePreservingTransformation T ->
    EvolutionaryEquivalence F (T F)
```

proof obligation:

- "relevant horizons, artifact actions, support relations, policies, observation boundaries" を `EvolutionaryContext` として束ねる。
- naturality は artifact action composition に対して後から追加する。
- external behavior preservation と future preservation を混同しない。

### 12.18 Fundamental Modularity Theorem of Software Evolution

Lean anchors:

```text
FundamentalModularityHypotheses
FundamentalModularityPackage
ComputablyGoverned
TypedComputationBoundaryFailure
fundamental_modularity
```

実装ファイル:

```text
Formal/Arch/Evolution/SFTFundamentalModularity.lean
```

この theorem は最後に証明する統合 theorem であり、初期段階では theorem package として置く。

```text
structure FundamentalModularityPackage where
  modularityDescent :
    ForecastConeDescent cover model source h
  obstructionCompleteness :
    DescentObstructionClassifierComplete classifier
  minimalEnvelope :
    MinimalConsequenceEnvelope Q cone
  governanceComplete :
    GovernanceSynthesisComplete basis
  closedLoopOutcome :
    ClosedLoopFixedPointOrBoundaryExpansion U E0
  nonConclusions : Prop
```

grand theorem の形:

```text
fundamental_modularity :
  FundamentalModularityHypotheses data ->
    ComputablyGoverned data
      or
    exists failure : TypedComputationBoundaryFailure data,
      failure.ExplainsBrokenBoundary
```

証明戦略:

1. descent がある場合は local-to-global computation を得る。
2. descent が壊れる場合は obstruction classifier で typed witness を得る。
3. review decision は minimal envelope へ落とす。
4. bad witness を切れる場合は governance synthesis を適用する。
5. feedback loop は fixed point または boundary expansion へ進む。
6. どこかの前提が欠ける場合は `TypedComputationBoundaryFailure` に分類する。

proof obligation:

- theorem family 間の data shape をそろえる。
- "computably governed" を過剰に強くしない。bounded, selected, boundary-explicit computation として定義する。
- failure witness は mathematical failure と tooling failure を分ける。

### 12.19 実装順序

Phase A: Clocked descent core

```text
1. SFTClockedCone.lean
2. SFTFieldCover.lean
3. SFTDescent.lean binary theorem
4. theorem index / proof obligations update
```

Current Lean status: Phase A の core は `Formal/Arch/Evolution/SFTClockedCone.lean`,
`Formal/Arch/Evolution/SFTFieldCover.lean`, `Formal/Arch/Evolution/SFTDescent.lean` に分割済み。
`forecastCone_descent_binary` は `BinaryDescentAssumptions` から selected `ConeEquivalence` を
構成する theorem-package surface である。`ConeEquivalence` の global/local relatedness は
reflexive / symmetric / transitive laws を持つ selected equivalence relation として要求される。
local-to-global path gluing は `BinaryClockedStepGluingData` から
`glueCompatibleLocalClockedPath` と `glueCompatibleBinaryClockedConeFamily` として構成される。
`BinaryDescentAssumptions.ofStepGluing` はこの concrete glue function を使って descent assumptions
を組み立てる。さらに `BinaryProjectionGluingLaws` による endpoint projection/glue laws から
`BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws` と
`forecastCone_descent_binary_of_endpoint_laws` を構成できる。
加えて `BinaryProjectionGluingPathLaws` によって、explicit selected path-level equivalence data
に相対化した `forecastCone_descent_binary_of_path_laws` と path-law package accessor も構成できる。
これは dependent path の definitional equality ではなく selected path equivalence である。
`SFTFiniteCover.lean` では `UniformFiniteFieldCover`、Cech-style 0/1/2 simplex、`FiniteSFTModel`、
finite local projection、`FiniteLocalClockedConeFamily`、`FiniteClockedGluingData`、
`FiniteProjectionGluingLaws`、`forecastCone_descent_finite_of_laws` を追加した。finite-cover
ForecastCone descent は、explicit finite gluing と Cech-style compatibility laws に相対化された
selected skeleton として表現できる。`SFTDescentObstruction.lean` では selected finite descent
failure を typed obstruction witness へ分類する explicit classifier package と、selected bad
obstruction witness を governance package で cut する checked accessor surface を追加した。
`SFTFundamentalModularity.lean` では final conservative assembly surface を追加した。explicit
descent、obstruction、minimal-envelope、governance、calibration、agentic confluence assumptions
の下で、bounded selected evolution が governed であるか typed boundary failure を露出することを、
既存 `SFTTheoremRoadmap.FundamentalModularityConclusion` / `FundamentalModularityTheoremPackage`
へ bridge する checked theorem-package assembly として読める。agentic component は
`hAgentic` と governed-side `agenticConfluenceAvailable` bridge として final hypotheses に接続され、
agentic non-conclusions も roadmap conclusion の boundary に残る。agentic bridge は
`localConfluence` 単体ではなく、`AgenticConfluencePackage.agentic_confluence` の conclusion である
`FairInterleavingsConverge package.landing` を final component として読む。
definitional path equality / transport-normalized path equality、all finite covers satisfying descent、
all descent failures are completely classified、full Cech cohomology theorem、operational governance
effectiveness、empirical calibration correctness、global agentic safety / confluence、assumption-free
Fundamental Modularity theorem はまだ無条件には主張しない。

Phase B: Obstruction and review surface

```text
1. SFTDescentObstruction.lean
2. SFTMinimalEnvelope.lean
3. ConsequenceEnvelope bridge
4. DescentGap -> obstructionCandidates bridge
```

Phase C: Governance, attractor, confluence

```text
1. SFTAttractorGluing.lean
2. SFTGovernanceSynthesis.lean
3. SFTAgenticConfluence.lean
4. website / workbench-facing theorem package metadata
```

Phase D: Higher theory

```text
1. SFTConeCohomology.lean
2. SFTArtifactYoneda.lean
3. SFTEvolutionaryEquivalence.lean
```

Phase E: Closed-loop and lifecycle theory

```text
1. SFTCalibrationFixedPoint.lean
2. SFTFieldShapingFixedPoint.lean
3. SFTLifecycleBifurcation.lean
```

Phase F: Grand theorem package

```text
1. SFTFundamentalModularity.lean
2. SFTTheoremPackages metadata update
3. docs/aat/proof_obligations.md update
4. docs/aat/lean_theorem_index.md update
```

### 12.20 PR ごとの検証

Lean 変更を含む PR では、最低限次を実行する。

```text
lake build
git diff --check
hidden / bidirectional Unicode scan
axiom / admit / sorry / unsafe scan
```

docs-only の段階でも、claim boundary が変わる場合は次を確認する。

```text
docs/sft/software_field_theory.md
docs/sft/aat_interface.md
docs/aat/proof_obligations.md
docs/aat/lean_theorem_index.md
Formal/Arch/Evolution/SFTTheoremPackages.lean
```

この実装計画の最初の実作業は、`ClockedForecastCone`、`BinaryFieldCover`、exact cone projection、
binary descent assumptions の concrete API である。ここが通ると、SFT の中心命題である

```text
architecture boundary
  =
future-gluing boundary
```

を Lean 上の具体的な theorem package に変換する土台ができる。
