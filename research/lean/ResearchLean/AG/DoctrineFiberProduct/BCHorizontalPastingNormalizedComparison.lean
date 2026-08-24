import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingComparisonRoute

/-!
# Northwest-normalized horizontal Beck--Chevalley comparison route

The literal horizontal component route starts at the iterated pullback.  This
module conjugates it by the canonical northwest inverse so that its source and
left target edge are the ones used by the normalized outer square.  The final
bottom-edge presentation equality and equality with the outer semantic
comparison remain subsequent coherence steps.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- The horizontal component comparison transported onto the canonical
northwest-normalized source and left edge. -/
noncomputable def horizontalBCPastingNormalizedComponentComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).top ⋙
        coreFiberTransportFunctor data.nestedSquare.right ≅
      coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).left ⋙
        coreFiberTransportFunctor
          ((toSemanticBC data.leftPresentation).square.bottom ≫
            (toSemanticBC data.rightPresentation).square.bottom) :=
  (Functor.isoWhiskerRight
      (horizontalBCPastingNormalizedTopCompositor data)
      (coreFiberTransportFunctor data.nestedSquare.right)).trans
    ((Functor.isoWhiskerLeft
        (coreFiberTransportFunctor
          (bcPastingNorthwestIso (.horizontal data)).inv)
        (horizontalBCPastingComponentComparison data)).trans
      (Functor.isoWhiskerRight
        (horizontalBCPastingNormalizedLeftCompositor data).symm
        (coreFiberTransportFunctor
          ((toSemanticBC data.leftPresentation).square.bottom ≫
            (toSemanticBC data.rightPresentation).square.bottom))))

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
