import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingComparisonNormalizedSplit

/-!
# Horizontal pasted-comparison inner component split

The literal component comparison and the normalized-left compositor are
separated at object level for the final factorization proof.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

/-- The inner normalized route splits into component comparison and left
normalization. -/
theorem horizontalBCPastingNormalizedInner_hom_app_split
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    ((((coreFiberTransportFunctor
      (bcPastingNorthwestIso (.horizontal data)).inv).isoWhiskerLeft
        (horizontalBCPastingComponentComparison data)).trans
      (Functor.isoWhiskerRight
        (horizontalBCPastingNormalizedLeftCompositor data).symm
        (coreFiberTransportFunctor
          ((toSemanticBC data.leftPresentation).square.bottom ≫
            (toSemanticBC data.rightPresentation).square.bottom)))).hom.app
              sourcePackage).1 =
      ((horizontalBCPastingComponentComparison data).hom.app
        ((coreFiberTransportFunctor data.pasteNorthwestIso.inv).obj
          sourcePackage)).1 ≫
      ((coreFiberTransportFunctor
        ((toSemanticBC data.leftPresentation).square.bottom ≫
          (toSemanticBC data.rightPresentation).square.bottom)).map
        (coreFiberCompositorApp data.pasteNorthwestIso.inv
          (toSemanticBC data.leftPresentation).square.left
          sourcePackage).inv).1 := by
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
