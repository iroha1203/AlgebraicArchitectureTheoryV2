import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingComparisonEqualityRoutes

/-!
# Horizontal pasted-comparison normalized component split

This module exposes the top-normalization component independently of the
remaining normalized comparison route.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

/-- The normalized component comparison splits into top normalization and its
remaining inner route. -/
theorem horizontalBCPastingNormalizedComponentComparison_hom_app_split
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    ((horizontalBCPastingNormalizedComponentComparison data).hom.app
        sourcePackage).1 =
      ((Functor.isoWhiskerRight
        (horizontalBCPastingNormalizedTopCompositor data)
        (coreFiberTransportFunctor
          (toSemanticBC data.rightPresentation).square.right)).hom.app
            sourcePackage).1 ≫
      ((((coreFiberTransportFunctor
        (bcPastingNorthwestIso (.horizontal data)).inv).isoWhiskerLeft
          (horizontalBCPastingComponentComparison data)).trans
        (Functor.isoWhiskerRight
          (horizontalBCPastingNormalizedLeftCompositor data).symm
          (coreFiberTransportFunctor
            ((toSemanticBC data.leftPresentation).square.bottom ≫
              (toSemanticBC data.rightPresentation).square.bottom)))).hom.app
                sourcePackage).1 := by
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
