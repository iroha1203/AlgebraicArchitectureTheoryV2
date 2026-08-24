import ResearchLean.AG.DoctrineFiberProduct.BCVerticalPastingComparisonNormalizedSplit

/-!
# Vertical pasted-comparison inner component split
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- The inner normalized route splits into component comparison and left
normalization. -/
theorem verticalBCPastingNormalizedInner_hom_app_split
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    ((((coreFiberTransportFunctor
      (bcPastingNorthwestIso (.vertical data)).inv).isoWhiskerLeft
        (verticalBCPastingComponentComparison data)).trans
      (Functor.isoWhiskerRight
        (verticalBCPastingNormalizedLeftCompositor data).symm
        (coreFiberTransportFunctor
          (toSemanticBC data.lowerPresentation).square.bottom))).hom.app
              sourcePackage).1 =
      ((verticalBCPastingComponentComparison data).hom.app
        ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
          sourcePackage)).1 ≫
      ((coreFiberTransportFunctor
        (toSemanticBC data.lowerPresentation).square.bottom).map
        (coreFiberCompositorApp data.pasteNorthwestIso.inv
          ((toSemanticBC data.upperPresentation).square.left ≫
            (toSemanticBC data.lowerPresentation).square.left)
          sourcePackage).inv).1 := by
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
