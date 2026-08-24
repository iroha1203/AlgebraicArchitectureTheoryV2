import ResearchLean.AG.DoctrineFiberProduct.BCVerticalPastingNormalizedFactorization

/-!
# Vertical exact-boundary comparison factorization
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- G-110(E) vertical covariant-square predecessor API: the named generated
exact-boundary route has the normalized outer lift factorization.  The initial
right-edge transport comes from finite-presentation realization and the
remaining route from the component squares. -/
theorem verticalBCPastingOuterBoundaryRouteHom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    coreFiberIteratedLift
          (normalizedNestedPasteSquare (.vertical data)).top
          (normalizedNestedPasteSquare (.vertical data)).right
          sourcePackage ≫
        (verticalBCPastingOuterBoundaryRouteHom data sourcePackage).1 =
      coreFiberIteratedLift
        (normalizedNestedPasteSquare (.vertical data)).left
        (normalizedNestedPasteSquare (.vertical data)).bottom
        sourcePackage := by
  unfold verticalBCPastingOuterBoundaryRouteHom
  simp only [coreFiber_comp_val]
  rw [coreFiber_isoWhiskerLeft_hom_app_val]
  simp only [← Category.assoc]
  rw [coreFiberIteratedLift_transportEqIso_fac]
  exact verticalBCPastingNormalizedComponentComparison_hom_fac
    data sourcePackage

/-- G-110(E) vertical covariant-square predecessor API: transfer the named
route factorization to the generated exact-boundary comparison.  The route
equality is definitional and no comparison or lift certificate is assumed. -/
theorem verticalBCPastingOuterBoundaryComparison_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    coreFiberIteratedLift
          (normalizedNestedPasteSquare (.vertical data)).top
          (normalizedNestedPasteSquare (.vertical data)).right
          sourcePackage ≫
        ((verticalBCPastingOuterBoundaryComparison data).hom.app
          sourcePackage).1 =
      coreFiberIteratedLift
        (normalizedNestedPasteSquare (.vertical data)).left
        (normalizedNestedPasteSquare (.vertical data)).bottom
        sourcePackage := by
  have hroute :
      ((verticalBCPastingOuterBoundaryComparison data).hom.app
        sourcePackage).1 =
        (verticalBCPastingOuterBoundaryRouteHom data sourcePackage).1 := by
    exact congrArg (fun q => q.1)
      (verticalBCPastingOuterBoundaryComparison_hom_app_eq_route
        data sourcePackage)
  rw [hroute]
  exact verticalBCPastingOuterBoundaryRouteHom_fac data sourcePackage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
