import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredPairedRestrictedOrbitTransport

/-!
# Upper-stage exchange exactness for G-115

Exchange exactness is the pointwise invertibility predicate on the actual
generated geometry-compatible solution.  Exact endpoint comparison
isomorphisms identify each generated component with the corresponding
component of its actual canonical-authored backward companion up to
composition by isomorphisms on the left and right.  Hence invertibility is
preserved and reflected without deciding either side for the named fixture.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

namespace UpperGeometryCompatibleProblemInputData

/-- Every actual vertical component of a generated geometry-compatible
solution is invertible.  The predicate stores no certificate in the problem
input and does not assert its truth for the named decision fixture. -/
def UpperStageExchangeExact
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input) : Prop :=
  ∀ i : P.Vertex,
    @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ (solution.component i)

/-- At every vertex, an arbitrary generated solution component is invertible
iff the corresponding component of its actual backward canonical companion
is invertible.  The proof cancels the two exact endpoint isomorphisms in the
complete geometry category. -/
theorem generatedComponent_isIso_iff_backwardCompanion
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (i : P.Vertex) :
    (@IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ (solution.component i)) ↔
      (@IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ ((input.generatedSolutionBackward solution).component i)) := by
  let baseHom :=
    input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i
  let pulledInv :=
    input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i
  letI : @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ baseHom := by
    change @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i).hom
    infer_instance
  letI : @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ pulledInv := by
    change @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i).inv
    infer_instance
  constructor
  · intro componentIso
    letI : @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (solution.component i) := componentIso
    rw [show (input.generatedSolutionBackward solution).component i =
        input.generatedSolutionBackwardAt solution i from rfl,
      input.generatedSolutionBackwardAt_exact_normalization]
    change @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ ((baseHom ≫ solution.component i) ≫ pulledInv)
    infer_instance
  · intro companionIso
    rw [show (input.generatedSolutionBackward solution).component i =
        input.generatedSolutionBackwardAt solution i from rfl,
      input.generatedSolutionBackwardAt_exact_normalization] at companionIso
    change @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ ((baseHom ≫ solution.component i) ≫ pulledInv) at companionIso
    letI : @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ ((baseHom ≫ solution.component i) ≫ pulledInv) :=
      companionIso
    haveI : @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (baseHom ≫ solution.component i) :=
      CategoryTheory.IsIso.of_isIso_comp_right _ pulledInv
    exact @CategoryTheory.IsIso.of_isIso_comp_left
      (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
      _ _ _ baseHom (solution.component i) _ _

/-- Exchange exactness of an arbitrary generated solution is equivalent to
pointwise invertibility of its actual canonical-authored backward companion. -/
theorem upperStageExchangeExact_iff_backwardCompanion
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (solution : GeometryCompatibleUpperRefinementBCSolution input) :
    UpperStageExchangeExact solution ↔
      ∀ i : P.Vertex,
        @IsIso (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
          _ _ ((input.generatedSolutionBackward solution).component i) := by
  constructor
  · intro exactness i
    exact (input.generatedComponent_isIso_iff_backwardCompanion solution i).mp
      (exactness i)
  · intro companionExactness i
    exact (input.generatedComponent_isIso_iff_backwardCompanion solution i).mpr
      (companionExactness i)

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- The named generated decision component is invertible exactly when the
actual component of its named canonical companion is invertible.  This is a
pointwise iff only; neither side is decided here. -/
theorem solution_component_isIso_iff_canonicalCompanion
    (i : presentation.Vertex) :
    (@IsIso (GeomReadCategory FiniteModel.carrier)
      (geometryTotalCategory FiniteModel.carrier)
      _ _ (solution.component i)) ↔
      (@IsIso (GeomReadCategory FiniteModel.carrier)
        (geometryTotalCategory FiniteModel.carrier)
        _ _ (canonicalCompanionSolution.component i)) := by
  exact problem.data.generatedComponent_isIso_iff_backwardCompanion solution i

/-- The named upper-stage exchange predicate is equivalent to pointwise
invertibility of the actual named canonical companion solution. -/
theorem upperStageExchangeExact_iff_canonicalCompanion :
    UpperGeometryCompatibleProblemInputData.UpperStageExchangeExact solution ↔
      ∀ i : presentation.Vertex,
        @IsIso (GeomReadCategory FiniteModel.carrier)
          (geometryTotalCategory FiniteModel.carrier)
          _ _ (canonicalCompanionSolution.component i) := by
  exact problem.data.upperStageExchangeExact_iff_backwardCompanion solution

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
