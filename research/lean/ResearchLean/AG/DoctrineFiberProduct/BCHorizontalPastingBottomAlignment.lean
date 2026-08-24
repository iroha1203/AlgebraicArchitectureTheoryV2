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

/-- The functor isomorphism induced by equality of two core transport edges. -/
noncomputable def coreFiberTransportEqIso
    {U : AtomCarrier.{u}} {W X : ExtractionInstance U}
    {first second : W ⟶ X} (edge_eq : first = second) :
    coreFiberTransportFunctor first ≅ coreFiberTransportFunctor second :=
  eqToIso (congrArg coreFiberTransportFunctor edge_eq)

/-- Append a transport-functor isomorphism on the right of an existing
core-fiber functor isomorphism. -/
noncomputable def coreFiberIsoTransWhiskerLeft
    {U : AtomCarrier.{u}} {W X Y : ExtractionInstance U}
    {F : CoreFiber W ⥤ CoreFiber Y}
    (L : CoreFiber W ⥤ CoreFiber X) {H K : CoreFiber X ⥤ CoreFiber Y}
    (e : F ≅ L ⋙ H) (d : H ≅ K) : F ≅ L ⋙ K :=
  e.trans (L.isoWhiskerLeft d)

/-- The objectwise horizontal route after its final bottom equality
transport. -/
noncomputable def horizontalBCPastingOuterBoundaryRouteHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    ((coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).top ⋙
        coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).right).obj
      sourcePackage) ⟶
    ((coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).left ⋙
        coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal data)).bottom).obj
      sourcePackage) :=
  (horizontalBCPastingNormalizedComponentComparison data).hom.app
      sourcePackage ≫
    ((coreFiberTransportFunctor
      (normalizedNestedPasteSquare (.horizontal data)).left).isoWhiskerLeft
        (coreFiberTransportEqIso
          (horizontalBCPastingNormalizedBottom_eq data).symm)).hom.app
      sourcePackage

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
  coreFiberIsoTransWhiskerLeft
    (coreFiberTransportFunctor
      (normalizedNestedPasteSquare (.horizontal data)).left)
    (horizontalBCPastingNormalizedComponentComparison data)
    (coreFiberTransportEqIso
      (horizontalBCPastingNormalizedBottom_eq data).symm)

/-- The exact-boundary comparison has the named objectwise route as its hom
component. -/
theorem horizontalBCPastingOuterBoundaryComparison_hom_app_eq_route
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    (horizontalBCPastingOuterBoundaryComparison data).hom.app sourcePackage =
      horizontalBCPastingOuterBoundaryRouteHom data sourcePackage := by
  unfold horizontalBCPastingOuterBoundaryComparison
  unfold coreFiberIsoTransWhiskerLeft
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
