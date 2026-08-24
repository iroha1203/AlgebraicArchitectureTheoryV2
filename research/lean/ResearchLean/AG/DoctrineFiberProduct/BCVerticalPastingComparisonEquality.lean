import ResearchLean.AG.DoctrineFiberProduct.BCVerticalPastingOuterFactorization

/-!
# Vertical pasted covariant-square comparison equality

The normalized vertical component route is identified with the independently
generated outer semantic comparison by strong-cocartesian uniqueness.  This
is a predecessor of canonical Beck--Chevalley mate pasting; it does not
construct or identify the reindexing/unit/counit mate.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 2000000

/-- G-110(E) vertical covariant-square predecessor checkpoint: generated
vertical pasting agrees with the independently generated covariant comparison
of the normalized outer semantic square.  `VerticalBCPastingData` supplies only
finite presentations; the comparison and strong-cocartesian certificate are
generated internally.  This is not the canonical `coreBeckChevalleyMate`
pasting theorem, whose reindexing and unit/counit coherence remain open. -/
theorem verticalBCPastingComparison_eq_outer
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    verticalBCPastingOuterBoundaryComparison data =
      bcSemanticCoreTransportSquareIso
        (normalizedNestedPasteSemanticInput (.vertical data)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext sourcePackage
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian
      ((normalizedNestedPasteSquare (.vertical data)).top ≫
        (normalizedNestedPasteSquare (.vertical data)).right)
      (coreFiberIteratedLift
        (normalizedNestedPasteSquare (.vertical data)).top
        (normalizedNestedPasteSquare (.vertical data)).right
        sourcePackage) :=
    coreFiberIteratedLift_isStronglyCocartesian
      (normalizedNestedPasteSquare (.vertical data)).top
      (normalizedNestedPasteSquare (.vertical data)).right sourcePackage
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U)
    ((normalizedNestedPasteSquare (.vertical data)).top ≫
      (normalizedNestedPasteSquare (.vertical data)).right)
    (coreFiberIteratedLift
      (normalizedNestedPasteSquare (.vertical data)).top
      (normalizedNestedPasteSquare (.vertical data)).right sourcePackage)
    (𝟙 (normalizedNestedPasteSquare (.vertical data)).southeast)
  change coreFiberIteratedLift
        (normalizedNestedPasteSquare (.vertical data)).top
        (normalizedNestedPasteSquare (.vertical data)).right sourcePackage ≫
      ((verticalBCPastingOuterBoundaryComparison data).hom.app
        sourcePackage).1 =
    coreFiberIteratedLift
        (normalizedNestedPasteSquare (.vertical data)).top
        (normalizedNestedPasteSquare (.vertical data)).right sourcePackage ≫
      ((bcSemanticCoreTransportSquareIso
        (normalizedNestedPasteSemanticInput (.vertical data))).hom.app
          sourcePackage).1
  rw [verticalBCPastingOuterBoundaryComparison_hom_fac]
  exact (bcSemanticCoreTransportSquareIso_hom_fac
    (normalizedNestedPasteSemanticInput (.vertical data))
    sourcePackage).symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
