import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingNormalizedFactorization

/-!
# Horizontal pasted-comparison equality

The factorized horizontal route is identified with the independently generated
outer semantic comparison by strong-cocartesian uniqueness.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- The named exact-boundary horizontal route carries the normalized outer
top-right lift to the normalized outer left-bottom lift. -/
theorem horizontalBCPastingOuterBoundaryRouteHom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    coreFiberIteratedLift
          (normalizedNestedPasteSquare (.horizontal data)).top
          (normalizedNestedPasteSquare (.horizontal data)).right
          sourcePackage ≫
        (horizontalBCPastingOuterBoundaryRouteHom data sourcePackage).1 =
      coreFiberIteratedLift
        (normalizedNestedPasteSquare (.horizontal data)).left
        (normalizedNestedPasteSquare (.horizontal data)).bottom
        sourcePackage := by
  unfold horizontalBCPastingOuterBoundaryRouteHom
  simp only [coreFiber_comp_val]
  rw [coreFiber_isoWhiskerLeft_hom_app_val]
  simp only [← Category.assoc]
  rw [horizontalBCPastingNormalizedComponentComparison_hom_fac]
  rw [coreFiberIteratedLift_transportEqIso_fac]

/-- The exact-boundary normalized horizontal route carries the normalized
outer top-right lift to the normalized outer left-bottom lift. -/
theorem horizontalBCPastingOuterBoundaryComparison_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U)
    (sourcePackage : CoreFiber
      (normalizedNestedPasteSquare (.horizontal data)).northwest) :
    coreFiberIteratedLift
          (normalizedNestedPasteSquare (.horizontal data)).top
          (normalizedNestedPasteSquare (.horizontal data)).right
          sourcePackage ≫
        ((horizontalBCPastingOuterBoundaryComparison data).hom.app
          sourcePackage).1 =
      coreFiberIteratedLift
        (normalizedNestedPasteSquare (.horizontal data)).left
        (normalizedNestedPasteSquare (.horizontal data)).bottom
        sourcePackage := by
  have hroute :
      ((horizontalBCPastingOuterBoundaryComparison data).hom.app
        sourcePackage).1 =
        (horizontalBCPastingOuterBoundaryRouteHom data sourcePackage).1 := by
    exact congrArg (fun q => q.1)
      (horizontalBCPastingOuterBoundaryComparison_hom_app_eq_route
        data sourcePackage)
  rw [hroute]
  exact horizontalBCPastingOuterBoundaryRouteHom_fac data sourcePackage

/-- Horizontal pasting agrees with the independently generated comparison of
the normalized outer semantic square. -/
theorem horizontalBCPastingComparison_eq_outer
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    horizontalBCPastingOuterBoundaryComparison data =
      bcSemanticCoreTransportSquareIso
        (normalizedNestedPasteSemanticInput (.horizontal data)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext sourcePackage
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian
      ((normalizedNestedPasteSquare (.horizontal data)).top ≫
        (normalizedNestedPasteSquare (.horizontal data)).right)
      (coreFiberIteratedLift
        (normalizedNestedPasteSquare (.horizontal data)).top
        (normalizedNestedPasteSquare (.horizontal data)).right
        sourcePackage) :=
    coreFiberIteratedLift_isStronglyCocartesian
      (normalizedNestedPasteSquare (.horizontal data)).top
      (normalizedNestedPasteSquare (.horizontal data)).right sourcePackage
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U)
    ((normalizedNestedPasteSquare (.horizontal data)).top ≫
      (normalizedNestedPasteSquare (.horizontal data)).right)
    (coreFiberIteratedLift
      (normalizedNestedPasteSquare (.horizontal data)).top
      (normalizedNestedPasteSquare (.horizontal data)).right sourcePackage)
    (𝟙 (normalizedNestedPasteSquare (.horizontal data)).southeast)
  change coreFiberIteratedLift
        (normalizedNestedPasteSquare (.horizontal data)).top
        (normalizedNestedPasteSquare (.horizontal data)).right sourcePackage ≫
      ((horizontalBCPastingOuterBoundaryComparison data).hom.app
        sourcePackage).1 =
    coreFiberIteratedLift
        (normalizedNestedPasteSquare (.horizontal data)).top
        (normalizedNestedPasteSquare (.horizontal data)).right sourcePackage ≫
      ((bcSemanticCoreTransportSquareIso
        (normalizedNestedPasteSemanticInput (.horizontal data))).hom.app
          sourcePackage).1
  rw [horizontalBCPastingOuterBoundaryComparison_hom_fac]
  exact (bcSemanticCoreTransportSquareIso_hom_fac
    (normalizedNestedPasteSemanticInput (.horizontal data))
    sourcePackage).symm



end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
