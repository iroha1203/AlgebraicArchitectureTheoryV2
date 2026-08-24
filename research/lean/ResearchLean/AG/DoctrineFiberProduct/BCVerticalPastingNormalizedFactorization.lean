import ResearchLean.AG.DoctrineFiberProduct.BCVerticalPastingComparisonInnerSplit

/-!
# Vertical normalized comparison factorization
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- The normalized vertical component comparison has the expected
composite-right lift factorization. -/
theorem verticalBCPastingNormalizedComponentComparison_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    coreFiberIteratedLift
          (normalizedNestedPasteSquare (.vertical data)).top
          ((toSemanticBC data.upperPresentation).square.right ≫
            (toSemanticBC data.lowerPresentation).square.right)
          sourcePackage ≫
        ((verticalBCPastingNormalizedComponentComparison data).hom.app
          sourcePackage).1 =
      coreFiberIteratedLift
        (normalizedNestedPasteSquare (.vertical data)).left
        (toSemanticBC data.lowerPresentation).square.bottom
        sourcePackage := by
  rw [verticalBCPastingNormalizedSourceLift_eq]
  rw [verticalBCPastingNormalizedComponentComparison_hom_app_split]
  rw [verticalBCPastingNormalizedInner_hom_app_split]
  rw [verticalBCPastingNormalizedTop_hom_app]
  simp only [← Category.assoc]
  rw [verticalBCPastingTopComponentRoute_hom_fac]
  rw [verticalBCPastingLeftRoute_hom_fac]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
