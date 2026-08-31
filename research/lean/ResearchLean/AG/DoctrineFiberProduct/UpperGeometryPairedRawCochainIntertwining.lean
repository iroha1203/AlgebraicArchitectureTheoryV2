import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryPairedCoefficientTrivialReselection

/-!
# Paired upper raw-cochain intertwining for G-115

This module advances G-115 revision 8 clause (c) from edge and path
intertwining to the actual G-109 canonical comparator and raw defect cochain.
It introduces no replacement cochain and assumes no invertibility of the
solution component.

## Implementation notes

Canonical-comparator naturality is derived by strong-cocartesian uniqueness
along the actual reselected base left path.  The inverse equation is then
proved by categorical cancellation with the two automorphism inverses.  The
raw-cochain theorem separately consumes that inverse equation and the actual
solution authored-comparator equation.  Triangle and coefficient-component
use remain explicit obligations of the subsequent full paired contract.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 20000000

namespace UpperGeometryCompatibleProblemInputData

/-- Postcomposition preserves equality of complete geometry morphisms. -/
private theorem geometryTotalHom_comp_congr
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    {left right : GeometryTotalHom G H} (equality : left = right)
    (tail : GeometryTotalHom H K) :
    left.comp tail = right.comp tail := by
  cases equality
  rfl

/-- Canonical comparators of an endpoint-intertwined coefficient-trivial pair
intertwine the actual solution component. -/
theorem CoefficientTrivialUpperReselectionEndpointIntertwining.canonicalComparator_intertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : CoefficientTrivialUpperReselectionEndpointIntertwining
      solution base pulled)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (upperCanonicalTwoCellComparator input.generatedBaseRouteData
        base.toUpperEdgeReselection cell)).comp
        (solution.component (P.twoTarget cell)) =
      (solution.component (P.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (upperCanonicalTwoCellComparator input.generatedPulledRouteData
            pulled.toUpperEdgeReselection cell)) := by
  let source := P.twoSource cell
  let target := P.twoTarget cell
  let baseLeft := upperReselectedPathLift input.generatedBaseRouteLiftData
    base.toUpperEdgeReselection (P.twoLeft cell)
  let baseRight := upperReselectedPathLift input.generatedBaseRouteLiftData
    base.toUpperEdgeReselection (P.twoRight cell)
  let pulledLeft := upperReselectedPathLift input.generatedPulledRouteLiftData
    pulled.toUpperEdgeReselection (P.twoLeft cell)
  let pulledRight := upperReselectedPathLift input.generatedPulledRouteLiftData
    pulled.toUpperEdgeReselection (P.twoRight cell)
  let baseCanonical := upperCanonicalTwoCellComparator
    input.generatedBaseRouteData base.toUpperEdgeReselection cell
  let pulledCanonical := upperCanonicalTwoCellComparator
    input.generatedPulledRouteData pulled.toUpperEdgeReselection cell
  have baseCanonical_fac :
      baseLeft.comp (CompositeFiberAut.hom baseCanonical) = baseRight := by
    simpa only [baseLeft, baseRight, baseCanonical] using
      upperCanonicalTwoCellComparator_fac input.generatedBaseRouteData
        base.toUpperEdgeReselection cell
  have pulledCanonical_fac :
      pulledLeft.comp (CompositeFiberAut.hom pulledCanonical) = pulledRight := by
    simpa only [pulledLeft, pulledRight, pulledCanonical] using
      upperCanonicalTwoCellComparator_fac input.generatedPulledRouteData
        pulled.toUpperEdgeReselection cell
  have baseLeft_naturality :
      baseLeft.comp (solution.component target) =
        (solution.component source).comp pulledLeft := by
    simpa only [baseLeft, pulledLeft, source, target] using
      paired.reselectedPath_naturality (P.twoLeft cell)
  have baseRight_naturality :
      baseRight.comp (solution.component target) =
        (solution.component source).comp pulledRight := by
    simpa only [baseRight, pulledRight, source, target] using
      paired.reselectedPath_naturality (P.twoRight cell)
  let component : GeometryTotalHom
      (input.generatedBaseRouteGeometryAt target)
      (input.generatedPulledRouteGeometryAt target) :=
    solution.component target
  let left : GeometryTotalHom
      (input.generatedBaseRouteGeometryAt target)
      (input.generatedPulledRouteGeometryAt target) :=
    (CompositeFiberAut.hom baseCanonical).comp component
  let right : GeometryTotalHom
      (input.generatedBaseRouteGeometryAt target)
      (input.generatedPulledRouteGeometryAt target) :=
    component.comp (CompositeFiberAut.hom pulledCanonical)
  have hfac : baseLeft.comp left = baseLeft.comp right := by
    dsimp only [left, right, component]
    have step1 :
        baseLeft.comp ((CompositeFiberAut.hom baseCanonical).comp
          (solution.component target)) =
        (baseLeft.comp (CompositeFiberAut.hom baseCanonical)).comp
          (solution.component target) :=
      (@Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ baseLeft (CompositeFiberAut.hom baseCanonical)
        (solution.component target)).symm
    have step2 :
        (baseLeft.comp (CompositeFiberAut.hom baseCanonical)).comp
          (solution.component target) =
        baseRight.comp (solution.component target) :=
      congrArg (fun hom => hom.comp (solution.component target))
        baseCanonical_fac
    have step3 :
        baseRight.comp (solution.component target) =
        (solution.component source).comp pulledRight :=
      baseRight_naturality
    have step4 :
        (solution.component source).comp pulledRight =
        (solution.component source).comp
          (pulledLeft.comp (CompositeFiberAut.hom pulledCanonical)) :=
      congrArg (fun hom => (solution.component source).comp hom)
        pulledCanonical_fac.symm
    have step5 :
        (solution.component source).comp
          (pulledLeft.comp (CompositeFiberAut.hom pulledCanonical)) =
        ((solution.component source).comp pulledLeft).comp
          (CompositeFiberAut.hom pulledCanonical) :=
      (@Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ (solution.component source) pulledLeft
        (CompositeFiberAut.hom pulledCanonical)).symm
    have step7 :
        (baseLeft.comp (solution.component target)).comp
          (CompositeFiberAut.hom pulledCanonical) =
        baseLeft.comp ((solution.component target).comp
          (CompositeFiberAut.hom pulledCanonical)) :=
      @Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ baseLeft (solution.component target)
        (CompositeFiberAut.hom pulledCanonical)
    exact step1.trans (step2.trans (step3.trans
      (step4.trans (step5.trans
        ((geometryTotalHom_comp_congr baseLeft_naturality.symm
          (CompositeFiberAut.hom pulledCanonical)).trans step7)))))
  letI hleftLift :
      (crossStageProjection.{u, v} U).IsHomLift component.base.base left := by
    refine CategoryTheory.IsHomLift.of_fac
      (crossStageProjection.{u, v} U) component.base.base left rfl rfl ?_
    change component.base.base =
      (CompositeFiberAut.hom baseCanonical).base.base.comp component.base.base
    rw [CompositeFiberAut.hom_base_base_eq]
    exact (@Category.id_comp
      (ExtInstCategory U) (ExtInstHom.extractionInstanceCategory U)
      _ _ component.base.base).symm
  letI hrightLift :
      (crossStageProjection.{u, v} U).IsHomLift component.base.base right := by
    refine CategoryTheory.IsHomLift.of_fac
      (crossStageProjection.{u, v} U) component.base.base right rfl rfl ?_
    change component.base.base = component.base.base.comp
      (CompositeFiberAut.hom pulledCanonical).base.base
    rw [CompositeFiberAut.hom_base_base_eq]
    exact (@Category.comp_id
      (ExtInstCategory U) (ExtInstHom.extractionInstanceCategory U)
      _ _ component.base.base).symm
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      baseLeft.base.base baseLeft :=
    (upperReselectLiftData input.generatedBaseRouteLiftData
      base.toUpperEdgeReselection).pathLift_compositeStrong (P.twoLeft cell)
  change left = right
  exact CategoryTheory.Functor.IsStronglyCocartesian.ext
    (crossStageProjection.{u, v} U) baseLeft.base.base baseLeft
    component.base.base hfac

/-- The inverse canonical comparators satisfy the same componentwise
intertwining equation. -/
theorem CoefficientTrivialUpperReselectionEndpointIntertwining.canonicalComparator_inv_intertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : CoefficientTrivialUpperReselectionEndpointIntertwining
      solution base pulled)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (upperCanonicalTwoCellComparator input.generatedBaseRouteData
        base.toUpperEdgeReselection cell)⁻¹).comp
        (solution.component (P.twoTarget cell)) =
      (solution.component (P.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (upperCanonicalTwoCellComparator input.generatedPulledRouteData
            pulled.toUpperEdgeReselection cell)⁻¹) := by
  let baseCanonical := upperCanonicalTwoCellComparator
    input.generatedBaseRouteData base.toUpperEdgeReselection cell
  let pulledCanonical := upperCanonicalTwoCellComparator
    input.generatedPulledRouteData pulled.toUpperEdgeReselection cell
  let component := solution.component (P.twoTarget cell)
  have naturality :
      (CompositeFiberAut.hom baseCanonical).comp component =
        component.comp (CompositeFiberAut.hom pulledCanonical) := by
    simpa only [baseCanonical, pulledCanonical, component] using
      paired.canonicalComparator_intertwining cell
  have pulled_hom_inv :
      (CompositeFiberAut.hom pulledCanonical).comp
          (CompositeFiberAut.hom pulledCanonical⁻¹) =
        GeometryTotalHom.id _ := by
    change pulledCanonical.1.hom.comp pulledCanonical.1.inv =
      GeometryTotalHom.id _
    exact pulledCanonical.1.hom_inv_id
  have base_inv_hom :
      (CompositeFiberAut.hom baseCanonical⁻¹).comp
          (CompositeFiberAut.hom baseCanonical) =
        GeometryTotalHom.id _ := by
    change baseCanonical.1.inv.comp baseCanonical.1.hom =
      GeometryTotalHom.id _
    exact baseCanonical.1.inv_hom_id
  calc
    (CompositeFiberAut.hom baseCanonical⁻¹).comp component =
      ((CompositeFiberAut.hom baseCanonical⁻¹).comp component).comp
        (GeometryTotalHom.id _) :=
      (@Category.comp_id (GeomReadCategory.{u, v} U)
        (geometryTotalCategory U) _ _ _).symm
    _ = ((CompositeFiberAut.hom baseCanonical⁻¹).comp component).comp
        ((CompositeFiberAut.hom pulledCanonical).comp
          (CompositeFiberAut.hom pulledCanonical⁻¹)) :=
      congrArg (fun hom =>
        ((CompositeFiberAut.hom baseCanonical⁻¹).comp component).comp hom)
        pulled_hom_inv.symm
    _ = (((CompositeFiberAut.hom baseCanonical⁻¹).comp component).comp
          (CompositeFiberAut.hom pulledCanonical)).comp
        (CompositeFiberAut.hom pulledCanonical⁻¹) :=
      (@Category.assoc (GeomReadCategory.{u, v} U)
        (geometryTotalCategory U) _ _ _ _ _ _ _).symm
    _ = ((CompositeFiberAut.hom baseCanonical⁻¹).comp
          (component.comp (CompositeFiberAut.hom pulledCanonical))).comp
        (CompositeFiberAut.hom pulledCanonical⁻¹) :=
      congrArg (fun hom => hom.comp
        (CompositeFiberAut.hom pulledCanonical⁻¹))
        (@Category.assoc (GeomReadCategory.{u, v} U)
          (geometryTotalCategory U) _ _ _ _
          (CompositeFiberAut.hom baseCanonical⁻¹) component
          (CompositeFiberAut.hom pulledCanonical))
    _ = ((CompositeFiberAut.hom baseCanonical⁻¹).comp
          ((CompositeFiberAut.hom baseCanonical).comp component)).comp
        (CompositeFiberAut.hom pulledCanonical⁻¹) :=
      congrArg (fun hom =>
        ((CompositeFiberAut.hom baseCanonical⁻¹).comp hom).comp
          (CompositeFiberAut.hom pulledCanonical⁻¹)) naturality.symm
    _ = (((CompositeFiberAut.hom baseCanonical⁻¹).comp
          (CompositeFiberAut.hom baseCanonical)).comp component).comp
        (CompositeFiberAut.hom pulledCanonical⁻¹) :=
      congrArg (fun hom => hom.comp
        (CompositeFiberAut.hom pulledCanonical⁻¹))
        (@Category.assoc (GeomReadCategory.{u, v} U)
          (geometryTotalCategory U) _ _ _ _
          (CompositeFiberAut.hom baseCanonical⁻¹)
          (CompositeFiberAut.hom baseCanonical) component).symm
    _ = ((GeometryTotalHom.id _).comp component).comp
        (CompositeFiberAut.hom pulledCanonical⁻¹) :=
      congrArg (fun hom => (hom.comp component).comp
        (CompositeFiberAut.hom pulledCanonical⁻¹)) base_inv_hom
    _ = component.comp (CompositeFiberAut.hom pulledCanonical⁻¹) :=
      congrArg (fun hom => hom.comp
        (CompositeFiberAut.hom pulledCanonical⁻¹))
        (@Category.id_comp (GeomReadCategory.{u, v} U)
          (geometryTotalCategory U) _ _ component)

/-- The actual G-109 raw defect cochains of an endpoint-intertwined pair
intertwine componentwise. -/
theorem CoefficientTrivialUpperReselectionEndpointIntertwining.upperRawDefectCochain_intertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (paired : CoefficientTrivialUpperReselectionEndpointIntertwining
      solution base pulled)
    (cell : P.TwoCell) :
    (CompositeFiberAut.hom
      (upperRawDefectCochain input.generatedBaseRouteData
        base.toUpperEdgeReselection cell)).comp
        (solution.component (P.twoTarget cell)) =
      (solution.component (P.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (upperRawDefectCochain input.generatedPulledRouteData
            pulled.toUpperEdgeReselection cell)) := by
  let baseCanonical := upperCanonicalTwoCellComparator
    input.generatedBaseRouteData base.toUpperEdgeReselection cell
  let pulledCanonical := upperCanonicalTwoCellComparator
    input.generatedPulledRouteData pulled.toUpperEdgeReselection cell
  let component := solution.component (P.twoTarget cell)
  have inverseNaturality :
      (CompositeFiberAut.hom baseCanonical⁻¹).comp component =
        component.comp (CompositeFiberAut.hom pulledCanonical⁻¹) := by
    simpa only [baseCanonical, pulledCanonical, component] using
      paired.canonicalComparator_inv_intertwining cell
  have authoredIntertwining :
      (CompositeFiberAut.hom
          (input.generatedBaseRouteTransport.comparator cell)).comp component =
        component.comp (CompositeFiberAut.hom
          (input.generatedPulledRouteTransport.comparator cell)) := by
    simpa only [component] using solution.comparator_intertwining cell
  simp only [upperRawDefectCochain, upperRawTwoCellDefect,
    compositeFiberAut_hom_mul]
  change ((CompositeFiberAut.hom baseCanonical⁻¹).comp
      (CompositeFiberAut.hom
        (input.generatedBaseRouteTransport.comparator cell))).comp component =
    component.comp ((CompositeFiberAut.hom pulledCanonical⁻¹).comp
      (CompositeFiberAut.hom
        (input.generatedPulledRouteTransport.comparator cell)))
  calc
    _ = (CompositeFiberAut.hom baseCanonical⁻¹).comp
        ((CompositeFiberAut.hom
          (input.generatedBaseRouteTransport.comparator cell)).comp
            component) :=
      @Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ _ _ _
    _ = (CompositeFiberAut.hom baseCanonical⁻¹).comp
        (component.comp (CompositeFiberAut.hom
          (input.generatedPulledRouteTransport.comparator cell))) := by
      rw [authoredIntertwining]
    _ = ((CompositeFiberAut.hom baseCanonical⁻¹).comp component).comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteTransport.comparator cell)) :=
      (@Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ _ _ _).symm
    _ = (component.comp (CompositeFiberAut.hom pulledCanonical⁻¹)).comp
        (CompositeFiberAut.hom
          (input.generatedPulledRouteTransport.comparator cell)) := by
      rw [inverseNaturality]
    _ = _ :=
      @Category.assoc (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ _ _ _ _ _

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- The named nonidentity comparator reselection pair fires the actual
raw-cochain intertwining theorem. -/
theorem generatedComparatorUpperReselections_rawCochainIntertwining_fires
    (cell : problem.presentation.TwoCell) :
    (CompositeFiberAut.hom
      (upperRawDefectCochain problem.data.generatedBaseRouteData
        generatedBaseComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
          cell)).comp
        (solution.component (problem.presentation.twoTarget cell)) =
      (solution.component (problem.presentation.twoTarget cell)).comp
        (CompositeFiberAut.hom
          (upperRawDefectCochain problem.data.generatedPulledRouteData
            generatedPulledComparatorCoefficientTrivialUpperReselection.toUpperEdgeReselection
              cell)) :=
  generatedComparatorUpperReselections_endpointIntertwining_fires.upperRawDefectCochain_intertwining
    cell

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
