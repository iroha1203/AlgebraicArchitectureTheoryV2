import ResearchLean.AG.CrossStageCoherence.FiniteWitnesses

/-!
# Low-level compatible-pair gluing counterexample

This finite AAT fixture reuses the nontrivial composite, core, and inner
automorphisms from `FiniteCrossStageWitness`.  Two non-strict cells have the
same boundary and different authored comparators.  A coherent core
trivializer, its fixed-endpoint lift, and a nondegenerate absolute strict
trivializer all exist and satisfy the shared edge restriction, but no one
total edge gauge can satisfy both non-strict cells.
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

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
