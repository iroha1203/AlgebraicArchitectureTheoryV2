import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingComparisonInnerSplit

/-!
# Horizontal normalized comparison factorization

The normalized component comparison is shown to carry the outer top-right
lift to the normalized-left lift along the literal composite bottom edge.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- The normalized component comparison has the expected composite-bottom
lift factorization. -/
theorem horizontalBCPastingNormalizedComponentComparison_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    coreFiberIteratedLift
          (normalizedNestedPasteSquare (.horizontal data)).top
          (normalizedNestedPasteSquare (.horizontal data)).right
          sourcePackage ≫
        ((horizontalBCPastingNormalizedComponentComparison data).hom.app
          sourcePackage).1 =
      coreFiberIteratedLift
        (normalizedNestedPasteSquare (.horizontal data)).left
        ((toSemanticBC data.leftPresentation).square.bottom ≫
          (toSemanticBC data.rightPresentation).square.bottom)
        sourcePackage := by
  rw [horizontalBCPastingNormalizedSourceLift_eq]
  rw [horizontalBCPastingNormalizedComponentComparison_hom_app_split]
  rw [horizontalBCPastingNormalizedInner_hom_app_split]
  rw [horizontalBCPastingNormalizedTop_hom_app]
  simp only [← Category.assoc]
  rw [horizontalBCPastingTopComponentRoute_hom_fac]
  rw [horizontalBCPastingLeftRoute_hom_fac]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
