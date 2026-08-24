import ResearchLean.AG.DoctrineFiberProduct.BCVerticalPastingComparisonEqualityRoutes

/-!
# Vertical pasted-comparison normalized component split
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

/-- The normalized component comparison splits into top normalization and its
remaining inner route. -/
theorem verticalBCPastingNormalizedComponentComparison_hom_app_split
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    ((verticalBCPastingNormalizedComponentComparison data).hom.app
        sourcePackage).1 =
      ((Functor.isoWhiskerRight
        (verticalBCPastingNormalizedTopCompositor data)
        (coreFiberTransportFunctor
          ((toSemanticBC data.upperPresentation).square.right ≫
            (toSemanticBC data.lowerPresentation).square.right))).hom.app
              sourcePackage).1 ≫
      ((((coreFiberTransportFunctor
        (bcPastingNorthwestIso (.vertical data)).inv).isoWhiskerLeft
          (verticalBCPastingComponentComparison data)).trans
        (Functor.isoWhiskerRight
          (verticalBCPastingNormalizedLeftCompositor data).symm
          (coreFiberTransportFunctor
            (toSemanticBC data.lowerPresentation).square.bottom))).hom.app
                sourcePackage).1 := by
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
