import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingNormalizedComparison

/-!
# Horizontal pasted-comparison bottom alignment

The normalized outer bottom edge is decoded from the finite composition
constructor, while the component route ends in the categorical composite of
the two decoded bottom edges.  This module exposes their generated equality
and uses equality transport to put the normalized component comparison on the
exact outer-square functor boundary.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- The normalized horizontal outer bottom edge is the categorical composite
of the two generated component bottom edges. -/
theorem horizontalBCPastingNormalizedBottom_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    (normalizedNestedPasteSquare (.horizontal data)).bottom =
      (toSemanticBC data.leftPresentation).square.bottom ≫
        (toSemanticBC data.rightPresentation).square.bottom := by
  exact toSemanticCart_compPresentation_hom data.bottomLeft data.bottomRight

/-- The normalized horizontal component comparison with its bottom transport
identified with the exact normalized outer bottom transport. -/
noncomputable def horizontalBCPastingOuterBoundaryComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).top ⋙
        coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).right ≅
      coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).left ⋙
        coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).bottom :=
  (horizontalBCPastingNormalizedComponentComparison data).trans
    (Functor.isoWhiskerLeft
      (coreFiberTransportFunctor
        (normalizedNestedPasteSquare (.horizontal data)).left)
      (eqToIso (congrArg coreFiberTransportFunctor
        (horizontalBCPastingNormalizedBottom_eq data))).symm)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
