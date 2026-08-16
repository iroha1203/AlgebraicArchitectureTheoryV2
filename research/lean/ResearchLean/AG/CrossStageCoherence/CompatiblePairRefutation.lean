import ResearchLean.AG.CrossStageCoherence.FiniteWitnesses

/-!
# Low-level compatible-pair gluing counterexample

This finite AAT fixture reuses the nontrivial composite, core, and inner
automorphisms from `FiniteCrossStageWitness`.  Two non-strict cells have the
same boundary and different authored comparators.  A coherent core
trivializer, its fixed-endpoint lift, and a nondegenerate absolute strict
trivializer all exist and satisfy the shared edge restriction, but no one
total edge gauge can satisfy both non-strict cells.

## Implementation notes

The two active cells deliberately share one typed path boundary, so a single
edge gauge must solve both equations.  The fixture has no 3-cells because the
gluing implication has no syzygy premise; adding an all-cell coherence field
to `CompatiblePairs` was rejected because it would encode the conclusion.
-/

namespace AAT.AG.CrossStageCoherence

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

namespace CompatiblePairRefutation

open FiniteCrossStageWitness

/-- The active counterexample boundary uses its loop once. -/
def activePath :
    PresentedPath WitnessEdgeFamily PUnit.unit PUnit.unit :=
  .cons .active witnessNilPath

/-- The two active faces share one boundary; the third face is genuinely strict. -/
noncomputable def twoPresentation : FiniteTransportTwoPresentation where
  Vertex := WitnessVertex
  vertexFintype := inferInstance
  Edge := WitnessEdgeFamily
  edgeFintype := fun _ _ => witnessEdgeFintype
  TwoCell := WitnessTwoCell
  twoCellFintype := witnessTwoCellFintype
  twoSource := fun _ => PUnit.unit
  twoTarget := fun _ => PUnit.unit
  twoLeft := fun _ => witnessNilPath
  twoRight
    | .activeFirst => activePath
    | .activeSecond => activePath
    | .strict => witnessStrictPath

/-- A finite presentation is enough for the universally quantified gluing claim. -/
noncomputable def presentation : FiniteTransportPresentation where
  toFiniteTransportTwoPresentation := twoPresentation
  ThreeCell := PEmpty
  threeCellFintype := inferInstance
  threeSource := fun cell => nomatch cell
  threeTarget := fun cell => nomatch cell
  threeStart := fun cell => nomatch cell
  threeFinish := fun cell => nomatch cell
  threeLeft := fun cell => nomatch cell
  threeRight := fun cell => nomatch cell

/-- Both loops retain independent geometry- and core-strong certificates. -/
noncomputable def liftData :
    TwoLayerLiftData presentation FiniteModel.carrier where
  geometry _ := package
  edgeLift _ := GeometryTotalHom.id package
  edgeGeometryStrong _ := geometryIdentityStrong
  edgeCoreStrong _ := coreIdentityStrong

/-- Every selected path evaluates to the identity before edge reselection. -/
theorem pathLift_eq_id {i j : presentation.Vertex}
    (path : presentation.Path i j) :
    liftData.pathLift path = GeometryTotalHom.id package := by
  induction path with
  | nil => rfl
  | cons edge tail inductionHypothesis =>
      change (GeometryTotalHom.id package).comp
          (liftData.pathLift tail) = GeometryTotalHom.id package
      rw [inductionHypothesis]
      exact Category.comp_id
        (self := geometryTotalCategory FiniteModel.carrier)
        (GeometryTotalHom.id package)

/-- The second active comparator differs by the nontrivial inner element. -/
noncomputable def shiftedVisibleComposite : CompositeFiberAut package :=
  innerFiberInclusion package innerSwap * visibleComposite

/-- Same-boundary active cells carry different lifts of the same core value. -/
noncomputable def data :
    TwoLayerTransportData presentation FiniteModel.carrier where
  lift := liftData
  twoCellBase := by
    intro cell
    rw [pathLift_eq_id, pathLift_eq_id]
  comparator
    | .activeFirst => visibleComposite
    | .activeSecond => shiftedVisibleComposite
    | .strict => innerFiberInclusion package innerSwap

/-- The shifted active comparator still projects to `visibleCore`. -/
theorem shiftedVisibleComposite_pushforward :
    compositeFiberPushforward package shiftedVisibleComposite = visibleCore := by
  rw [shiftedVisibleComposite, map_mul]
  have innerIdentity : compositeFiberPushforward package
      (innerFiberInclusion package innerSwap) = 1 :=
    (compositeFiberPushforward_eq_one_iff innerSwap.1).2 innerSwap.2
  rw [innerIdentity, one_mul, visibleComposite_pushforward]

/-- The two active authored comparators are genuinely different. -/
theorem shiftedVisibleComposite_ne_visible :
    shiftedVisibleComposite ≠ visibleComposite := by
  intro equality
  have inclusionIdentity : innerFiberInclusion package innerSwap = 1 := by
    apply mul_right_cancel (b := visibleComposite)
    simpa [shiftedVisibleComposite] using equality
  apply innerSwap_ne_one
  apply innerFiberInclusion_injective package
  simpa using inclusionIdentity

/-- The core coordinate selects the liftable visible involution on the active edge. -/
noncomputable def coreReselection : EdgeReselection data.coreData.lift :=
  fun _ _ edge =>
    match edge with
    | .active => visibleCore
    | .strict => 1

/-- One core edge coordinate coheres with all three projected comparators. -/
theorem coreReselection_coherent :
    CoherentAt data.coreData coreReselection := by
  intro cell
  cases cell
  all_goals simp only [presentation, twoPresentation, activePath, witnessNilPath,
      witnessStrictPath, reselectedPathLift, reselectLiftData,
      AdmissibleLiftData.pathLift, reselectedEdgeLift, data,
      TwoLayerTransportData.coreData, TwoLayerLiftData.coreLiftData,
      liftData, coreReselection, visibleComposite_pushforward,
      shiftedVisibleComposite_pushforward]
  case activeFirst =>
    change
      (PackageTotalHom.id package.core).comp
          (PackageFiberAut.hom visibleCore) =
        ((PackageTotalHom.id package.core).comp
          (PackageFiberAut.hom visibleCore)).comp
            (PackageTotalHom.id package.core)
    exact (Category.comp_id
      (self := PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      ((PackageTotalHom.id package.core).comp
        (PackageFiberAut.hom visibleCore))).symm
  case activeSecond =>
    change
      (PackageTotalHom.id package.core).comp
          (PackageFiberAut.hom visibleCore) =
        ((PackageTotalHom.id package.core).comp
          (PackageFiberAut.hom visibleCore)).comp
            (PackageTotalHom.id package.core)
    exact (Category.comp_id
      (self := PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      ((PackageTotalHom.id package.core).comp
        (PackageFiberAut.hom visibleCore))).symm
  case strict =>
    have innerIdentity :
        compositeFiberPushforward package
            (innerFiberInclusion package innerSwap) = 1 :=
      (compositeFiberPushforward_eq_one_iff innerSwap.1).2 innerSwap.2
    rw [innerIdentity]
    change
      (PackageTotalHom.id package.core).comp
          (PackageFiberAut.hom (1 : PackageFiberAut package.core)) =
        ((PackageTotalHom.id package.core).comp
          (PackageFiberAut.hom (1 : PackageFiberAut package.core))).comp
            (PackageTotalHom.id package.core)
    exact (Category.comp_id
      (self := PackageTotalHom.packageTotalCategory FiniteModel.carrier)
      ((PackageTotalHom.id package.core).comp
        (PackageFiberAut.hom (1 : PackageFiberAut package.core)))).symm

/-- The projected coordinate is an actual core trivializer. -/
noncomputable def coreTrivializer : CoreTrivializer data where
  reselection := coreReselection
  coherent := coreReselection_coherent

/-- The visible composite supplies the fixed-endpoint lift of the core coordinate. -/
noncomputable def edgeSection : EdgeSectionFamily data where
  core := coreReselection
  lift := fun _ _ edge =>
    match edge with
    | .active => visibleComposite
    | .strict => 1
  projects := by
    intro i j edge
    cases edge
    · exact visibleComposite_pushforward
    · exact map_one _

/-- Core alignment is the already proved core trivializer equation. -/
theorem edgeSection_alignment : CoreAlignmentAt data edgeSection :=
  coreReselection_coherent

/-- The strict cell satisfies the maximal strict qualification. -/
theorem strict_qualified : StrictCellQualified data .strict := by
  constructor
  · have pathEquality :=
      (pathLift_eq_id (presentation.twoLeft WitnessTwoCell.strict)).trans
        (pathLift_eq_id (presentation.twoRight WitnessTwoCell.strict)).symm
    exact congrArg GeometryTotalHom.base pathEquality
  · change compositeFiberPushforward package
      (innerFiberInclusion package innerSwap) = 1
    exact (compositeFiberPushforward_eq_one_iff innerSwap.1).2 innerSwap.2

/-- The first active face is not strict because its core component is visible. -/
theorem activeFirst_not_qualified :
    ¬ StrictCellQualified data .activeFirst := by
  intro qualified
  have pushed := qualified.2
  change compositeFiberPushforward package visibleComposite = 1 at pushed
  rw [visibleComposite_pushforward] at pushed
  exact visibleCore_ne_one pushed

/-- The shifted active face has the same nonidentity core component. -/
theorem activeSecond_not_qualified :
    ¬ StrictCellQualified data .activeSecond := by
  intro qualified
  have pushed := qualified.2
  change compositeFiberPushforward package shiftedVisibleComposite = 1 at pushed
  rw [shiftedVisibleComposite_pushforward] at pushed
  exact visibleCore_ne_one pushed

/-- Every qualified cell is the intended nondegenerate strict face. -/
theorem strictTwoCell_eq_strict (cell : StrictTwoCell data) :
    cell.1 = .strict := by
  rcases cell with ⟨cell, qualified⟩
  cases cell
  · exact False.elim (activeFirst_not_qualified qualified)
  · exact False.elim (activeSecond_not_qualified qualified)
  · rfl

/-- The strict coordinate uses the actual nonidentity inner automorphism. -/
noncomputable def strictReselection : StrictEdgeReselection data.lift :=
  fun _ _ edge =>
    match edge with
    | .active => 1
    | .strict => innerSwap

/-- The absolute strict coordinate coheres on the complete qualified subtype. -/
theorem strictReselection_coherent : StrictCoherentAt data strictReselection := by
  intro cell
  rcases cell with ⟨cell, qualified⟩
  cases cell
  · exact False.elim (activeFirst_not_qualified qualified)
  · exact False.elim (activeSecond_not_qualified qualified)
  · change (upperReselectedPathLift liftData
        (strictToUpperReselection liftData strictReselection)
        witnessNilPath).comp
        (CompositeFiberAut.hom (innerFiberInclusion package innerSwap)) =
      upperReselectedPathLift liftData
        (strictToUpperReselection liftData strictReselection)
        witnessStrictPath
    simp only [upperReselectedPathLift, upperReselectLiftData,
      TwoLayerLiftData.pathLift, upperReselectedEdgeLift,
      strictToUpperReselection, strictReselection, witnessNilPath,
      witnessStrictPath, liftData]
    exact Category.comp_id
      (self := geometryTotalCategory FiniteModel.carrier)
      (CompositeFiberAut.hom (innerFiberInclusion package innerSwap))

/-- The strict coordinate is an actual absolute strict trivializer. -/
noncomputable def strictTrivializer : StrictTrivializer data where
  reselection := strictReselection
  coherent := strictReselection_coherent

/-- The maximal strict sub-presentation is inhabited by the strict face. -/
theorem strict_sector_nonempty : Nonempty (StrictTwoCell data) :=
  ⟨⟨.strict, strict_qualified⟩⟩

/-- The two active faces make the maximal strict sub-presentation proper. -/
theorem strict_sector_proper :
    ¬ Function.Surjective (strictTwoCellEmbedding data) := by
  intro surjective
  obtain ⟨cell, equality⟩ := surjective WitnessTwoCell.activeFirst
  change cell.1 = WitnessTwoCell.activeFirst at equality
  have qualified := cell.property
  rw [equality] at qualified
  exact activeFirst_not_qualified qualified

/-- The strict trivializer performs nonidentity inner work on its qualified face. -/
theorem strict_reselection_nonidentity :
    strictReselection PUnit.unit PUnit.unit .strict ≠ 1 := by
  change innerSwap ≠ 1
  exact innerSwap_ne_one

/-- The lifted core coordinate and strict trivializer agree on every strict face. -/
theorem shared_restriction :
    SharedBoundaryCompatible edgeSection strictTrivializer := by
  intro cell
  rcases cell with ⟨cell, qualified⟩
  cases cell
  · exact False.elim (activeFirst_not_qualified qualified)
  · exact False.elim (activeSecond_not_qualified qualified)
  · change (upperReselectedPathLift liftData
        (relativeUpperReselection edgeSection strictReselection)
        witnessNilPath).comp
        (CompositeFiberAut.hom (innerFiberInclusion package innerSwap)) =
      upperReselectedPathLift liftData
        (relativeUpperReselection edgeSection strictReselection)
        witnessStrictPath
    simp only [upperReselectedPathLift, upperReselectLiftData,
      TwoLayerLiftData.pathLift, upperReselectedEdgeLift,
      relativeUpperReselection, edgeSection, witnessNilPath, witnessStrictPath,
      liftData]
    exact Category.comp_id
      (self := geometryTotalCategory FiniteModel.carrier)
      (CompositeFiberAut.hom (innerFiberInclusion package innerSwap))

/-- A second lift of the same core coordinate cancels the strict gauge on its edge. -/
noncomputable def incompatibleEdgeSection : EdgeSectionFamily data where
  core := coreReselection
  lift := fun _ _ edge =>
    match edge with
    | .active => visibleComposite
    | .strict => innerFiberInclusion package (innerSwap⁻¹)
  projects := by
    intro i j edge
    cases edge
    · exact visibleComposite_pushforward
    · exact (compositeFiberPushforward_eq_one_iff (innerSwap⁻¹).1).2
        (innerSwap⁻¹).2

/-- Shared strict-face compatibility is a genuine condition, not a tautology. -/
theorem incompatibleEdgeSection_not_shared :
    ¬ SharedBoundaryCompatible incompatibleEdgeSection strictTrivializer := by
  intro compatible
  have equation := compatible
    (⟨.strict, strict_qualified⟩ : StrictTwoCell data)
  change (upperReselectedPathLift liftData
        (relativeUpperReselection incompatibleEdgeSection strictReselection)
        witnessNilPath).comp
        (CompositeFiberAut.hom (innerFiberInclusion package innerSwap)) =
      upperReselectedPathLift liftData
        (relativeUpperReselection incompatibleEdgeSection strictReselection)
        witnessStrictPath at equation
  simp only [upperReselectedPathLift, upperReselectLiftData,
    TwoLayerLiftData.pathLift, upperReselectedEdgeLift,
    relativeUpperReselection, incompatibleEdgeSection, witnessNilPath,
    witnessStrictPath, liftData, map_inv] at equation
  have inclusionIdentity : innerFiberInclusion package innerSwap = 1 := by
    letI : (crossStageProjection.{0, 0} FiniteModel.carrier).IsStronglyCocartesian
        (GeometryTotalHom.id package).base.base (GeometryTotalHom.id package) :=
      by
        simpa only [upperReselectedPathLift, upperReselectLiftData,
          TwoLayerLiftData.pathLift, witnessNilPath] using
          (upperReselectLiftData liftData
            (relativeUpperReselection incompatibleEdgeSection
              strictReselection)).pathLift_compositeStrong witnessNilPath
    apply CompositeFiberAut.ext_of_strong_fac (GeometryTotalHom.id package)
    simpa using equation
  apply innerSwap_ne_one
  apply innerFiberInclusion_injective package
  simpa using inclusionIdentity

/-- All fixed low-level Sigma/pullback fields, including strict restriction, exist. -/
noncomputable def compatiblePair : CompatiblePairs data where
  coreTrivializer := coreTrivializer
  edgeSection := edgeSection
  core_restriction := rfl
  alignment := edgeSection_alignment
  strictTrivializer := strictTrivializer
  restriction := shared_restriction

/-- The low-level compatible-pair predicate is inhabited. -/
theorem compatiblePairwiseVanishes : CompatiblePairwiseVanishes data :=
  ⟨compatiblePair⟩

/-- The two same-boundary active cells prevent every global joint gauge. -/
theorem not_joint : ¬ JointVanishes data := by
  intro joint
  obtain ⟨reselection, coherent⟩ :=
    (jointVanishes_iff_crossStageCoherentizable data).1 joint
  let left := upperReselectedPathLift data.lift reselection witnessNilPath
  letI : (crossStageProjection.{0, 0} FiniteModel.carrier).IsStronglyCocartesian
      left.base.base left :=
    (upperReselectLiftData data.lift reselection).pathLift_compositeStrong
      witnessNilPath
  have comparatorEquality : visibleComposite = shiftedVisibleComposite := by
    apply CompositeFiberAut.ext_of_strong_fac left
    exact (coherent .activeFirst).trans (coherent .activeSecond).symm
  exact shiftedVisibleComposite_ne_visible comparatorEquality.symm

/-- A low-level compatible pair does not imply joint vanishing. -/
theorem compatiblePairwise_not_implies_joint :
    ¬ (CompatiblePairwiseVanishes data → JointVanishes data) := by
  intro implication
  exact not_joint (implication compatiblePairwiseVanishes)

/-- The synthesized gauge from the low-level pair fails total coherence. -/
theorem compatiblePairGauge_not_coherent :
    ¬ CrossStageCoherentAt data (compatiblePairsToJointGauge compatiblePair) := by
  intro coherent
  exact not_joint ((jointVanishes_iff_crossStageCoherentizable data).2
    ⟨compatiblePairsToJointGauge compatiblePair, coherent⟩)

end CompatiblePairRefutation

/-! ## Positive and negative instance matrix

The declarations below discharge the quality-standard instance obligation for
every new cross-stage `Prop` predicate and for the three certificate structures
`CoreTrivializer`, `StrictTrivializer`, and `CompatiblePairs`.  The remaining
new structures are construction data: `TwoLayerLiftData` and
`TwoLayerTransportData` are inputs, while `EdgeSectionFamily` and
`PathBaseSplit` are inhabited for every input by canonical constructors.
-/

namespace QualityInstances

universe u v

open FiniteCrossStageWitness

/-! ### Independent core and strict failures -/

/-- Two equal path boundaries with different projected comparators obstruct
every core reselection. -/
noncomputable def coreIncompatibleData :
    TwoLayerTransportData CompatiblePairRefutation.presentation
      FiniteModel.carrier where
  lift := CompatiblePairRefutation.liftData
  twoCellBase := by
    intro cell
    rw [CompatiblePairRefutation.pathLift_eq_id,
      CompatiblePairRefutation.pathLift_eq_id]
  comparator
    | .activeFirst => visibleComposite
    | .activeSecond => 1
    | .strict => 1

/-- The core-incompatible finite data has no core trivializer. -/
theorem coreIncompatibleData_not_coreVanishes :
    ¬ CoreVanishes coreIncompatibleData := by
  intro vanishes
  obtain ⟨trivializer⟩ :=
    (coreVanishes_iff_nonempty_trivializer coreIncompatibleData).1 vanishes
  let left := reselectedPathLift coreIncompatibleData.coreData.lift
    trivializer.reselection witnessNilPath
  letI : (packageProjection FiniteModel.carrier).IsStronglyCocartesian
      left.base left :=
    reselectedPathLift_isStronglyCocartesian
      coreIncompatibleData.coreData.lift trivializer.reselection witnessNilPath
  have comparatorEquality : visibleCore = 1 := by
    apply PackageFiberAut.ext_of_strong_fac left
    simpa only [coreIncompatibleData, TwoLayerTransportData.coreData,
      CompatiblePairRefutation.presentation,
      CompatiblePairRefutation.twoPresentation, visibleComposite_pushforward,
      map_one] using
      (trivializer.coherent WitnessTwoCell.activeFirst).trans
        (trivializer.coherent WitnessTwoCell.activeSecond).symm
  exact visibleCore_ne_one comparatorEquality

/-- The core vanishing predicate has direct satisfying and non-satisfying data. -/
theorem coreVanishes_instances :
    CoreVanishes witnessData ∧ ¬ CoreVanishes coreIncompatibleData :=
  ⟨witness_core_vanishes, coreIncompatibleData_not_coreVanishes⟩

/-- Independent local vanishing has direct satisfying and non-satisfying data. -/
theorem localPairwiseVanishes_instances :
    LocalPairwiseVanishes witnessData ∧
      ¬ LocalPairwiseVanishes coreIncompatibleData := by
  refine ⟨witness_local_pairwise_vanishes, ?_⟩
  intro pairwise
  exact coreIncompatibleData_not_coreVanishes
    ((coreVanishes_iff_nonempty_trivializer coreIncompatibleData).2 pairwise.1)

/-- Core-trivializer certificates are inhabited on one fixture and empty on
the core-incompatible fixture. -/
theorem coreTrivializer_instances :
    Nonempty (CoreTrivializer witnessData) ∧
      IsEmpty (CoreTrivializer coreIncompatibleData) := by
  refine ⟨⟨witnessCoreTrivializer⟩, ⟨?_⟩⟩
  intro trivializer
  exact coreIncompatibleData_not_coreVanishes
    ((coreVanishes_iff_nonempty_trivializer coreIncompatibleData).2
      ⟨trivializer⟩)

/-- Two qualified faces with one boundary and distinct inner comparators
obstruct every strict reselection. -/
noncomputable def strictIncompatibleData :
    TwoLayerTransportData CompatiblePairRefutation.presentation
      FiniteModel.carrier where
  lift := CompatiblePairRefutation.liftData
  twoCellBase := by
    intro cell
    rw [CompatiblePairRefutation.pathLift_eq_id,
      CompatiblePairRefutation.pathLift_eq_id]
  comparator
    | .activeFirst => 1
    | .activeSecond => innerFiberInclusion package innerSwap
    | .strict => 1

/-- The first active face belongs to the strict sector of the strict-failure data. -/
theorem strictIncompatible_activeFirst_qualified :
    StrictCellQualified strictIncompatibleData .activeFirst := by
  constructor
  · have pathEquality :=
      (CompatiblePairRefutation.pathLift_eq_id
        (CompatiblePairRefutation.presentation.twoLeft
          WitnessTwoCell.activeFirst)).trans
      (CompatiblePairRefutation.pathLift_eq_id
        (CompatiblePairRefutation.presentation.twoRight
          WitnessTwoCell.activeFirst)).symm
    exact congrArg GeometryTotalHom.base pathEquality
  · exact map_one _

/-- The second active face belongs to the strict sector of the strict-failure data. -/
theorem strictIncompatible_activeSecond_qualified :
    StrictCellQualified strictIncompatibleData .activeSecond := by
  constructor
  · have pathEquality :=
      (CompatiblePairRefutation.pathLift_eq_id
        (CompatiblePairRefutation.presentation.twoLeft
          WitnessTwoCell.activeSecond)).trans
      (CompatiblePairRefutation.pathLift_eq_id
        (CompatiblePairRefutation.presentation.twoRight
          WitnessTwoCell.activeSecond)).symm
    exact congrArg GeometryTotalHom.base pathEquality
  · exact (compositeFiberPushforward_eq_one_iff innerSwap.1).2 innerSwap.2

/-- The strict-incompatible data admits no global strict coordinate. -/
theorem strictIncompatibleData_not_strictCoherentizable :
    ¬ StrictCoherentizable strictIncompatibleData := by
  rintro ⟨reselection, coherent⟩
  let first : StrictTwoCell strictIncompatibleData :=
    ⟨.activeFirst, strictIncompatible_activeFirst_qualified⟩
  let second : StrictTwoCell strictIncompatibleData :=
    ⟨.activeSecond, strictIncompatible_activeSecond_qualified⟩
  let left := upperReselectedPathLift strictIncompatibleData.lift
    (strictToUpperReselection strictIncompatibleData.lift reselection)
    witnessNilPath
  letI : (crossStageProjection.{0, 0} FiniteModel.carrier).IsStronglyCocartesian
      left.base.base left :=
    (upperReselectLiftData strictIncompatibleData.lift
      (strictToUpperReselection strictIncompatibleData.lift reselection)).pathLift_compositeStrong
        witnessNilPath
  have comparatorEquality :
      (1 : CompositeFiberAut package) =
        innerFiberInclusion package innerSwap := by
    apply CompositeFiberAut.ext_of_strong_fac left
    simpa only [first, second, strictAuthoredComparator,
      innerFiberInclusion_ofPushforwardEqOne, strictIncompatibleData,
      CompatiblePairRefutation.presentation,
      CompatiblePairRefutation.twoPresentation] using
      (coherent first).trans (coherent second).symm
  apply innerSwap_ne_one
  apply innerFiberInclusion_injective package
  exact comparatorEquality.symm

/-- Strict coherentizability has direct satisfying and non-satisfying data. -/
theorem strictCoherentizable_instances :
    StrictCoherentizable witnessData ∧
      ¬ StrictCoherentizable strictIncompatibleData :=
  ⟨⟨witnessStrictReselection, witnessStrictReselection_coherent⟩,
    strictIncompatibleData_not_strictCoherentizable⟩

/-- Pointed strict coherence has direct satisfying and non-satisfying instances. -/
theorem strictCoherentAt_instances :
    StrictCoherentAt witnessData witnessStrictReselection ∧
      ¬ StrictCoherentAt strictIncompatibleData 1 := by
  refine ⟨witnessStrictReselection_coherent, ?_⟩
  intro coherent
  exact strictIncompatibleData_not_strictCoherentizable ⟨1, coherent⟩

/-- Strict obstruction vanishing has direct satisfying and non-satisfying data. -/
theorem strictTransportObstructionVanishes_instances :
    StrictTransportObstructionVanishes witnessData ∧
      ¬ StrictTransportObstructionVanishes strictIncompatibleData := by
  refine ⟨witness_strict_vanishes, ?_⟩
  intro vanishes
  exact strictIncompatibleData_not_strictCoherentizable
    ((strictTransportObstructionVanishes_iff_coherentizable
      strictIncompatibleData).1 vanishes)

/-- Strict-trivializer certificates are inhabited on one fixture and empty on
the strict-incompatible fixture. -/
theorem strictTrivializer_instances :
    Nonempty (StrictTrivializer witnessData) ∧
      IsEmpty (StrictTrivializer strictIncompatibleData) := by
  refine ⟨⟨witnessStrictTrivializer⟩, ⟨?_⟩⟩
  intro trivializer
  exact strictIncompatibleData_not_strictCoherentizable
    ⟨trivializer.reselection, trivializer.coherent⟩

/-! ### Global, section-relative, and pullback instances -/

/-- Total coherence at a chosen coordinate has direct positive and negative data. -/
theorem crossStageCoherentAt_instances :
    CrossStageCoherentAt canonicalWitnessData 1 ∧
      ¬ CrossStageCoherentAt CompatiblePairRefutation.data
        (compatiblePairsToJointGauge CompatiblePairRefutation.compatiblePair) :=
  ⟨canonicalWitness_coherentAt_identity,
    CompatiblePairRefutation.compatiblePairGauge_not_coherent⟩

/-- Total coherentizability has direct positive and negative data. -/
theorem crossStageCoherentizable_instances :
    CrossStageCoherentizable canonicalWitnessData ∧
      ¬ CrossStageCoherentizable CompatiblePairRefutation.data := by
  refine ⟨canonicalWitness_categorical_anchor_fires, ?_⟩
  intro coherentizable
  exact CompatiblePairRefutation.not_joint
    ((jointVanishes_iff_crossStageCoherentizable
      CompatiblePairRefutation.data).2 coherentizable)

/-- Joint vanishing has direct positive and negative data. -/
theorem jointVanishes_instances :
    JointVanishes canonicalWitnessData ∧
      ¬ JointVanishes CompatiblePairRefutation.data :=
  ⟨canonicalWitness_joint_vanishes, CompatiblePairRefutation.not_joint⟩

/-- Upper-orbit membership has direct positive and negative data. -/
theorem inUpperReselectionOrbit_instances :
    InUpperReselectionOrbit canonicalWitnessData
        (upperIdentityDefectCochain canonicalWitnessData) ∧
      ¬ InUpperReselectionOrbit CompatiblePairRefutation.data
        (upperIdentityDefectCochain CompatiblePairRefutation.data) :=
  ⟨canonicalWitness_joint_vanishes, CompatiblePairRefutation.not_joint⟩

/-- Upper obstruction vanishing has direct positive and negative data. -/
theorem upperTransportObstructionVanishes_instances :
    UpperTransportObstructionVanishes canonicalWitnessData ∧
      ¬ UpperTransportObstructionVanishes CompatiblePairRefutation.data :=
  ⟨canonicalWitness_joint_vanishes, CompatiblePairRefutation.not_joint⟩

/-- The identity core section is not aligned on the negative finite witness. -/
theorem witness_identityEdgeSection_not_aligned :
    ¬ CoreAlignmentAt witnessData (identityEdgeSection witnessData) := by
  rw [coreAlignmentAt_identity_iff]
  intro coherent
  exact witness_identity_core_active_not_coherent
    (coherent WitnessTwoCell.activeFirst)

/-- Core alignment has direct positive and negative section instances. -/
theorem coreAlignmentAt_instances :
    CoreAlignmentAt canonicalWitnessData canonicalWitnessEdgeSection ∧
      ¬ CoreAlignmentAt witnessData (identityEdgeSection witnessData) :=
  ⟨canonicalWitness_alignment, witness_identityEdgeSection_not_aligned⟩

/-- The canonical section and identity inner gauge satisfy every total face. -/
theorem canonicalWitness_sectionRelativeCoherentAt :
    SectionRelativeCoherentAt canonicalWitnessData
      canonicalWitnessEdgeSection 1 := by
  have gaugeIdentity :
      relativeUpperReselection canonicalWitnessEdgeSection
          (1 : StrictEdgeReselection canonicalWitnessData.lift) = 1 := by
    funext i j edge
    change innerFiberInclusion (canonicalWitnessData.lift.geometry j) 1 * 1 = 1
    rw [map_one, one_mul]
  intro cell
  rw [gaugeIdentity]
  exact canonicalWitness_coherentAt_identity cell

/-- The refuting compatible pair's chosen relative gauge fails an active face. -/
theorem compatiblePair_sectionRelative_not_coherentAt :
    ¬ SectionRelativeCoherentAt CompatiblePairRefutation.data
      CompatiblePairRefutation.edgeSection
      CompatiblePairRefutation.strictReselection := by
  change ¬ CrossStageCoherentAt CompatiblePairRefutation.data
    (compatiblePairsToJointGauge CompatiblePairRefutation.compatiblePair)
  exact CompatiblePairRefutation.compatiblePairGauge_not_coherent

/-- Section-relative coherence at a chosen gauge has direct positive and negative
instances. -/
theorem sectionRelativeCoherentAt_instances :
    SectionRelativeCoherentAt canonicalWitnessData
        canonicalWitnessEdgeSection 1 ∧
      ¬ SectionRelativeCoherentAt CompatiblePairRefutation.data
        CompatiblePairRefutation.edgeSection
        CompatiblePairRefutation.strictReselection :=
  ⟨canonicalWitness_sectionRelativeCoherentAt,
    compatiblePair_sectionRelative_not_coherentAt⟩

/-- No inner gauge over the refuting section can solve both active faces. -/
theorem compatiblePair_sectionRelative_not_coherentizable :
    ¬ SectionRelativeCoherentizable CompatiblePairRefutation.data
      CompatiblePairRefutation.edgeSection := by
  rintro ⟨gauge, coherent⟩
  exact CompatiblePairRefutation.not_joint
    ((jointVanishes_iff_crossStageCoherentizable
      CompatiblePairRefutation.data).2
      ⟨relativeUpperReselection CompatiblePairRefutation.edgeSection gauge,
        coherent⟩)

/-- Section-relative coherentizability has direct positive and negative data. -/
theorem sectionRelativeCoherentizable_instances :
    SectionRelativeCoherentizable canonicalWitnessData
        canonicalWitnessEdgeSection ∧
      ¬ SectionRelativeCoherentizable CompatiblePairRefutation.data
        CompatiblePairRefutation.edgeSection :=
  ⟨⟨1, canonicalWitness_sectionRelativeCoherentAt⟩,
    compatiblePair_sectionRelative_not_coherentizable⟩

/-- Relative inner vanishing has direct positive and negative section instances. -/
theorem innerVanishesAt_instances :
    InnerVanishesAt canonicalWitnessData canonicalWitnessEdgeSection
        canonicalWitness_alignment ∧
      ¬ InnerVanishesAt CompatiblePairRefutation.data
        CompatiblePairRefutation.edgeSection
        CompatiblePairRefutation.edgeSection_alignment := by
  constructor
  · exact (innerVanishesAt_iff_sectionRelativeCoherentizable
      canonicalWitnessData canonicalWitnessEdgeSection
      canonicalWitness_alignment).2
      ⟨1, canonicalWitness_sectionRelativeCoherentAt⟩
  · intro vanishes
    exact compatiblePair_sectionRelative_not_coherentizable
      ((innerVanishesAt_iff_sectionRelativeCoherentizable
        CompatiblePairRefutation.data CompatiblePairRefutation.edgeSection
        CompatiblePairRefutation.edgeSection_alignment).1 vanishes)

/-- Aligned-section vanishing has direct positive and negative data. -/
theorem alignedSectionVanishes_instances :
    AlignedSectionVanishes canonicalWitnessData ∧
      ¬ AlignedSectionVanishes CompatiblePairRefutation.data := by
  constructor
  · exact (jointVanishes_iff_alignedSectionVanishes canonicalWitnessData).1
      canonicalWitness_joint_vanishes
  · intro aligned
    exact CompatiblePairRefutation.not_joint
      ((jointVanishes_iff_alignedSectionVanishes
        CompatiblePairRefutation.data).2 aligned)

/-- Strict qualification has direct positive and negative cell instances. -/
theorem strictCellQualified_instances :
    StrictCellQualified CompatiblePairRefutation.data .strict ∧
      ¬ StrictCellQualified CompatiblePairRefutation.data .activeFirst :=
  ⟨CompatiblePairRefutation.strict_qualified,
    CompatiblePairRefutation.activeFirst_not_qualified⟩

/-- Shared restriction compatibility has direct positive and negative sections. -/
theorem sharedBoundaryCompatible_instances :
    SharedBoundaryCompatible CompatiblePairRefutation.edgeSection
        CompatiblePairRefutation.strictTrivializer ∧
      ¬ SharedBoundaryCompatible
        CompatiblePairRefutation.incompatibleEdgeSection
        CompatiblePairRefutation.strictTrivializer :=
  ⟨CompatiblePairRefutation.shared_restriction,
    CompatiblePairRefutation.incompatibleEdgeSection_not_shared⟩

/-- Compatible-pair vanishing has direct positive and negative data. -/
theorem compatiblePairwiseVanishes_instances :
    CompatiblePairwiseVanishes CompatiblePairRefutation.data ∧
      ¬ CompatiblePairwiseVanishes witnessData := by
  refine ⟨CompatiblePairRefutation.compatiblePairwiseVanishes, ?_⟩
  rintro ⟨pair⟩
  exact witness_compatiblePairs_empty.false pair

/-- Compatible-pair certificates are inhabited on the refuting fixture and
empty on the original finite witness. -/
theorem compatiblePairs_instances :
    Nonempty (CompatiblePairs CompatiblePairRefutation.data) ∧
      IsEmpty (CompatiblePairs witnessData) :=
  ⟨⟨CompatiblePairRefutation.compatiblePair⟩,
    witness_compatiblePairs_empty⟩

/-- Pseudofunctor obstruction vanishing has direct positive and negative data. -/
theorem pseudofunctorObstructionVanishes_instances :
    PseudofunctorObstructionVanishes canonicalWitnessData ∧
      ¬ PseudofunctorObstructionVanishes witnessData :=
  ⟨canonicalWitness_pseudofunctor_obstruction_vanishes,
    witness_pseudofunctor_obstruction_does_not_vanish⟩

/-! ### Finite support predicates -/

/-- The selected-axis predicate has direct positive and negative axes. -/
theorem selectedAxis_instances :
    SelectedAxis (0 : Fin 4) ∧ ¬ SelectedAxis (2 : Fin 4) := by
  simp [SelectedAxis]

/-- The empty typed pasting used for negative support instances. -/
noncomputable def emptyPasting :
    RewritePasting witnessTwoPresentation witnessNilPath witnessNilPath :=
  @RewritePasting.nil witnessTwoPresentation PUnit.unit PUnit.unit witnessNilPath

/-- Pasting nonemptiness has direct positive and negative typed pastings. -/
theorem rewritePastingHasFace_instances :
    RewritePastingHasFace (P := witnessPresentation)
        (witnessPasting .activeFirst) ∧
      ¬ RewritePastingHasFace (P := witnessPresentation) emptyPasting := by
  simp [witnessPasting, emptyPasting, RewritePastingHasFace]

/-- Pasting support membership has direct positive and negative typed pastings. -/
theorem rewritePastingUsesCell_instances :
    RewritePastingUsesCell (P := witnessPresentation)
        WitnessTwoCell.activeFirst (witnessPasting .activeFirst) ∧
      ¬ RewritePastingUsesCell (P := witnessPresentation)
        WitnessTwoCell.activeFirst emptyPasting := by
  simp [witnessPasting, witnessStep, witnessFace, emptyPasting,
    RewritePastingUsesCell]

/-- A reflexive 3-cell supplies the negative nontrivial-syzygy instance. -/
noncomputable def reflexivePresentation : FiniteTransportPresentation where
  toFiniteTransportTwoPresentation := witnessTwoPresentation
  ThreeCell := PUnit
  threeCellFintype := inferInstance
  threeSource := fun _ => PUnit.unit
  threeTarget := fun _ => PUnit.unit
  threeStart := fun _ => witnessNilPath
  threeFinish := fun _ => witnessNilPath
  threeLeft := fun _ => emptyPasting
  threeRight := fun _ => emptyPasting

/-- Nontrivial syzygy support has direct positive and negative 3-cells. -/
theorem nontrivialSyzygyAt_instances :
    NontrivialSyzygyAt (P := witnessPresentation)
        WitnessThreeCell.comparison ∧
      ¬ NontrivialSyzygyAt (P := reflexivePresentation) PUnit.unit := by
  refine ⟨witness_nontrivial_syzygy, ?_⟩
  intro nontrivial
  exact nontrivial.1 rfl

/-- Distinct authored singleton faces on the existing closed presentation. -/
noncomputable def syzygyIncompatibleData :
    TwoLayerTransportData witnessPresentation FiniteModel.carrier where
  lift := witnessLiftData
  twoCellBase := by
    intro cell
    rw [witnessPathLift_eq_id, witnessPathLift_eq_id]
  comparator
    | .activeFirst => visibleComposite
    | .activeSecond => CompatiblePairRefutation.shiftedVisibleComposite
    | .strict => innerFiberInclusion package innerSwap

/-- The two authored singleton routes in the syzygy-incompatible data disagree. -/
theorem syzygyIncompatibleData_not_upperSyzygyCompatible :
    ¬ UpperSyzygyCompatible syzygyIncompatibleData 1 := by
  intro compatible
  have pastingEquality := compatible WitnessThreeCell.comparison
  have whiskerEquality :
      upperWhiskerCompositeFiberAut witnessLiftData 1 visibleComposite
          witnessNilPath =
        upperWhiskerCompositeFiberAut witnessLiftData 1
          CompatiblePairRefutation.shiftedVisibleComposite witnessNilPath := by
    simpa only [witnessPresentation, witnessPasting,
      upperAuthoredPastingComparator, upperPastingComparator,
      upperAuthoredComparatorFamily, upperOrientedFaceComparator,
      witnessStep, witnessFace, syzygyIncompatibleData, one_mul] using
      pastingEquality
  have transportedEquality :
      upperFiberAutThenPath witnessLiftData 1 visibleComposite witnessNilPath =
        upperFiberAutThenPath witnessLiftData 1
          CompatiblePairRefutation.shiftedVisibleComposite witnessNilPath := by
    calc
      upperFiberAutThenPath witnessLiftData 1 visibleComposite witnessNilPath =
          (upperReselectedPathLift witnessLiftData 1 witnessNilPath).comp
            (CompositeFiberAut.hom
              (upperWhiskerCompositeFiberAut witnessLiftData 1
                visibleComposite witnessNilPath)) :=
        (upperWhiskerCompositeFiberAut_fac witnessLiftData 1
          visibleComposite witnessNilPath).symm
      _ = (upperReselectedPathLift witnessLiftData 1 witnessNilPath).comp
            (CompositeFiberAut.hom
              (upperWhiskerCompositeFiberAut witnessLiftData 1
                CompatiblePairRefutation.shiftedVisibleComposite
                witnessNilPath)) := by rw [whiskerEquality]
      _ = upperFiberAutThenPath witnessLiftData 1
          CompatiblePairRefutation.shiftedVisibleComposite witnessNilPath :=
        upperWhiskerCompositeFiberAut_fac witnessLiftData 1
          CompatiblePairRefutation.shiftedVisibleComposite witnessNilPath
  have homEquality :
      CompositeFiberAut.hom visibleComposite =
        CompositeFiberAut.hom
          CompatiblePairRefutation.shiftedVisibleComposite := by
    simpa only [upperFiberAutThenPath, witnessNilPath,
      upperReselectedPathLift, upperReselectLiftData,
      TwoLayerLiftData.pathLift, Category.comp_id] using transportedEquality
  have comparatorEquality :
      visibleComposite = CompatiblePairRefutation.shiftedVisibleComposite := by
    apply Subtype.ext
    apply Iso.ext
    exact homEquality
  exact CompatiblePairRefutation.shiftedVisibleComposite_ne_visible
    comparatorEquality.symm

/-- Upper syzygy compatibility has direct positive and negative data. -/
theorem upperSyzygyCompatible_instances :
    UpperSyzygyCompatible witnessData 1 ∧
      ¬ UpperSyzygyCompatible syzygyIncompatibleData 1 :=
  ⟨witness_upper_syzygyCompatible,
    syzygyIncompatibleData_not_upperSyzygyCompatible⟩

/-- Canonical total coherence makes every supported raw face trivial. -/
theorem canonicalWitness_not_syzygySupportHasNonidentityRaw :
    ¬ SyzygySupportHasNonidentityRaw canonicalWitnessData 1
      WitnessThreeCell.comparison := by
  rintro ⟨face, _support, rawNonidentity⟩
  have rawIdentity := congrFun
    ((crossStageCoherentAt_iff_rawCochain_identity canonicalWitnessData 1).1
      canonicalWitness_coherentAt_identity) face
  exact rawNonidentity rawIdentity

/-- Nonidentity raw syzygy support has direct positive and negative data. -/
theorem syzygySupportHasNonidentityRaw_instances :
    SyzygySupportHasNonidentityRaw witnessData 1
        WitnessThreeCell.comparison ∧
      ¬ SyzygySupportHasNonidentityRaw canonicalWitnessData 1
        WitnessThreeCell.comparison :=
  ⟨witness_syzygy_support_has_nonidentity_raw,
    canonicalWitness_not_syzygySupportHasNonidentityRaw⟩

/-! ### Construction structures with no negative instance -/

/-- An edge-section negative instance is impossible: the identity section
inhabits this pure construction structure for every transport datum. -/
theorem edgeSectionFamily_always_inhabited
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    Nonempty (EdgeSectionFamily data) :=
  ⟨identityEdgeSection data⟩

/-- A path-split negative instance is impossible: `pathBaseSplit` constructs
one for every selected path. -/
theorem pathBaseSplit_always_inhabited
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    {i j : P.Vertex} (path : P.Path i j) :
    Nonempty (PathBaseSplit data path) :=
  ⟨pathBaseSplit data path⟩

end QualityInstances

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
