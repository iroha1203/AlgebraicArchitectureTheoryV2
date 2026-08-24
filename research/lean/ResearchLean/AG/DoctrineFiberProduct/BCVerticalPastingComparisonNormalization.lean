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

/-- The vertical component comparison transported through the canonical
northwest normalization. -/
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

/-- The normalized vertical outer right edge is the decoded composite of the
two generated component right edges. -/
theorem verticalBCPastingNormalizedRight_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    (normalizedNestedPasteSquare (.vertical data)).right =
      (toSemanticBC data.upperPresentation).square.right ≫
        (toSemanticBC data.lowerPresentation).square.right := by
  exact toSemanticCart_compPresentation_hom data.rightTop data.rightBottom

/-- The objectwise vertical route after its initial right-edge equality
transport. -/
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

/-- The vertical route on the exact normalized outer-square functor
boundary. -/
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

/-- The exact-boundary comparison has the named objectwise route as its hom
component. -/
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
