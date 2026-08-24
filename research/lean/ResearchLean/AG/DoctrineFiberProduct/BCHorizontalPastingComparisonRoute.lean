import ResearchLean.AG.DoctrineFiberProduct.BCPastingComparisonNormalization

/-!
# Horizontal componentwise Beck--Chevalley comparison route

This module composes the covariant semantic comparisons of the generated left
and right component squares.  G-109 compositors place that composite on the
literal outer horizontal boundary.  Equality with the independently generated
outer comparison is a subsequent coherence theorem.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

/-- The componentwise horizontal covariant comparison, with both ends aligned
to the literal outer rectangle by generated G-109 compositors. -/
noncomputable def horizontalBCPastingComponentComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    coreFiberTransportFunctor
          ((toSemanticBC data.leftPresentation).square.top ≫
            (toSemanticBC data.rightPresentation).square.top) ⋙
        coreFiberTransportFunctor
          (toSemanticBC data.rightPresentation).square.right ≅
      coreFiberTransportFunctor
          (toSemanticBC data.leftPresentation).square.left ⋙
        coreFiberTransportFunctor
          ((toSemanticBC data.leftPresentation).square.bottom ≫
            (toSemanticBC data.rightPresentation).square.bottom) :=
  (Functor.isoWhiskerRight
      (coreFiberCompositor
        (toSemanticBC data.leftPresentation).square.top
        (toSemanticBC data.rightPresentation).square.top)
      (coreFiberTransportFunctor
        (toSemanticBC data.rightPresentation).square.right)).trans
    ((Functor.isoWhiskerLeft
        (coreFiberTransportFunctor
          (toSemanticBC data.leftPresentation).square.top)
        (bcSemanticCoreTransportSquareIso
          (toSemanticBC data.rightPresentation))).trans
      ((Functor.isoWhiskerRight
          (bcSemanticCoreTransportSquareIso
            (toSemanticBC data.leftPresentation))
          (coreFiberTransportFunctor
            (toSemanticBC data.rightPresentation).square.bottom)).trans
        (Functor.isoWhiskerLeft
          (coreFiberTransportFunctor
            (toSemanticBC data.leftPresentation).square.left)
          (coreFiberCompositor
            (toSemanticBC data.leftPresentation).square.bottom
            (toSemanticBC data.rightPresentation).square.bottom).symm)))

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
