import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingComparisonEquality
import ResearchLean.AG.DoctrineFiberProduct.BCVerticalPastingComparisonRoute

/-!
# Vertical pasted-comparison normalization

The generated vertical componentwise covariant comparison is transported
through the canonical northwest isomorphism, and its right edge is aligned
with the independently generated normalized outer square.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- G-110(E) vertical covariant-square predecessor: transport the generated
component comparison through the canonical northwest normalization.  This is
an API definition for the later equality theorem; its presentations,
comparisons, and northwest isomorphism are generated from
`VerticalBCPastingData`.

Implementation notes: conjugating the reviewed component route preserves both
square comparisons.  A newly authored normalized comparison field was rejected
because it would bypass their provenance. -/
noncomputable def verticalBCPastingNormalizedComponentComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical data)).top ⋙
        coreFiberTransportFunctor
          ((toSemanticBC data.upperPresentation).square.right ≫
            (toSemanticBC data.lowerPresentation).square.right) ≅
      coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical data)).left ⋙
        coreFiberTransportFunctor
          (toSemanticBC data.lowerPresentation).square.bottom :=
  (Functor.isoWhiskerRight
      (verticalBCPastingNormalizedTopCompositor data)
      (coreFiberTransportFunctor
        ((toSemanticBC data.upperPresentation).square.right ≫
          (toSemanticBC data.lowerPresentation).square.right))).trans
    ((Functor.isoWhiskerLeft
        (coreFiberTransportFunctor
          (bcPastingNorthwestIso (.vertical data)).inv)
        (verticalBCPastingComponentComparison data)).trans
      (Functor.isoWhiskerRight
        (verticalBCPastingNormalizedLeftCompositor data).symm
        (coreFiberTransportFunctor
          (toSemanticBC data.lowerPresentation).square.bottom)))

/-- G-110(E) vertical covariant-square predecessor API: the normalized outer
right edge is the decoded composite of the two generated right presentations.
The equality is produced by finite-presentation realization, not supplied by
the caller. -/
theorem verticalBCPastingNormalizedRight_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    (normalizedNestedPasteSquare (.vertical data)).right =
      (toSemanticBC data.upperPresentation).square.right ≫
        (toSemanticBC data.lowerPresentation).square.right := by
  exact toSemanticCart_compPresentation_hom data.rightTop data.rightBottom

/-- G-110(E) vertical covariant-square predecessor API: the objectwise route
first consumes the generated right-edge realization equality and then the
normalized component comparison.  All data come from `VerticalBCPastingData`.

Implementation notes: naming this component prevents elaboration from
re-expanding the entire natural-isomorphism composite.  An opaque caller-given
component was rejected because it would erase route provenance. -/
noncomputable def verticalBCPastingOuterBoundaryRouteHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    ((coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical data)).top ⋙
        coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical data)).right).obj
      sourcePackage) ⟶
    ((coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical data)).left ⋙
        coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical data)).bottom).obj
      sourcePackage) :=
  ((coreFiberTransportFunctor
    (normalizedNestedPasteSquare (.vertical data)).top).isoWhiskerLeft
      (coreFiberTransportEqIso
        (verticalBCPastingNormalizedRight_eq data))).hom.app sourcePackage ≫
    (verticalBCPastingNormalizedComponentComparison data).hom.app sourcePackage

/-- G-110(E) vertical covariant-square predecessor API: place the generated
component route on the exact normalized outer-square functor boundary.  The
right transport is derived from finite-presentation realization and the
remaining comparison is generated from the component squares.

Implementation notes: the source is aligned before applying the component
comparison because the normalized right edge decodes to the component
composite.  Reversing the equality transport or accepting an aligned Iso as
input was rejected. -/
noncomputable def verticalBCPastingOuterBoundaryComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical data)).top ⋙
        coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical data)).right ≅
      coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical data)).left ⋙
        coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical data)).bottom :=
  ((coreFiberTransportFunctor
      (normalizedNestedPasteSquare (.vertical data)).top).isoWhiskerLeft
        (coreFiberTransportEqIso
          (verticalBCPastingNormalizedRight_eq data))).trans
    (verticalBCPastingNormalizedComponentComparison data)

/-- G-110(E) vertical covariant-square predecessor API: identify the hom
component of the exact-boundary comparison with its named generated route.
The only premise is generated vertical pasting data; this lemma exposes the
definition without introducing a comparison certificate. -/
theorem verticalBCPastingOuterBoundaryComparison_hom_app_eq_route
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.vertical data)).northwest) :
    (verticalBCPastingOuterBoundaryComparison data).hom.app sourcePackage =
      verticalBCPastingOuterBoundaryRouteHom data sourcePackage := by
  unfold verticalBCPastingOuterBoundaryComparison
  unfold verticalBCPastingOuterBoundaryRouteHom
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
