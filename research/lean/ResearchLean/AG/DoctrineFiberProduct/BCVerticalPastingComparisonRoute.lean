import ResearchLean.AG.DoctrineFiberProduct.BCPastingComparisonNormalization

/-!
# Vertical componentwise Beck--Chevalley comparison route

This module composes the covariant semantic comparisons of the generated upper
and lower component squares.  G-109 compositors place that composite on the
literal outer vertical boundary.  Equality with the independently generated
outer comparison is a subsequent coherence theorem.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- The componentwise vertical covariant comparison, with both ends aligned to
the literal outer rectangle by generated G-109 compositors. -/
noncomputable def verticalBCPastingComponentComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    coreFiberTransportFunctor
          (toSemanticBC data.upperPresentation).square.top ⋙
        coreFiberTransportFunctor
          ((toSemanticBC data.upperPresentation).square.right ≫
            (toSemanticBC data.lowerPresentation).square.right) ≅
      coreFiberTransportFunctor
          ((toSemanticBC data.upperPresentation).square.left ≫
            (toSemanticBC data.lowerPresentation).square.left) ⋙
        coreFiberTransportFunctor
          (toSemanticBC data.lowerPresentation).square.bottom :=
  (Functor.isoWhiskerLeft
      (coreFiberTransportFunctor
        (toSemanticBC data.upperPresentation).square.top)
      (coreFiberCompositor
        (toSemanticBC data.upperPresentation).square.right
        (toSemanticBC data.lowerPresentation).square.right)).trans
    ((Functor.isoWhiskerRight
        (bcSemanticCoreTransportSquareIso
          (toSemanticBC data.upperPresentation))
        (coreFiberTransportFunctor
          (toSemanticBC data.lowerPresentation).square.right)).trans
      ((Functor.isoWhiskerLeft
          (coreFiberTransportFunctor
            (toSemanticBC data.upperPresentation).square.left)
          (bcSemanticCoreTransportSquareIso
            (toSemanticBC data.lowerPresentation))).trans
        (Functor.isoWhiskerRight
          (coreFiberCompositor
            (toSemanticBC data.upperPresentation).square.left
            (toSemanticBC data.lowerPresentation).square.left).symm
          (coreFiberTransportFunctor
            (toSemanticBC data.lowerPresentation).square.bottom))))

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
