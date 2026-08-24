import ResearchLean.AG.DoctrineFiberProduct.BCHorizontalPastingComparisonEquality
import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMate

/-!
# Horizontal composition of generated Beck--Chevalley mates

This module specializes mathlib's mates-composition theorem to the two
generated component squares of a horizontal G-110 pasting input.  It records
the unit/counit coherence of the component mate route before the remaining
northwest and reindexing alignment with the independently generated outer
presentation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence
open CategoryTheory.NatTrans CategoryTheory.TwoSquare

set_option maxHeartbeats 2000000

/-- G-110(E) horizontal canonical-mate predecessor: the mate of the generated
horizontal composite of the two covariant component squares is the vertical
composition of their generated canonical mates.  The three adjunctions,
covariant comparisons, units, and counits are generated from
`HorizontalBCPastingData`; no mate or coherence equality is caller-supplied.
This is an API theorem before alignment with the normalized outer
presentation. -/
theorem horizontalBCPasting_mateEquiv_vcomp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    (mateEquiv
      (bcLeftAdjunction data.leftPresentation)
      (bcRightAdjunction data.rightPresentation)
      ((bcCoreTransportSquareIso data.leftPresentation).hom ≫ₕ
        (bcCoreTransportSquareIso data.rightPresentation).hom)) =
      (mateEquiv
        (bcLeftAdjunction data.leftPresentation)
        (bcRightAdjunction data.leftPresentation)
        (bcCoreTransportSquareIso data.leftPresentation).hom) ≫ᵥ
      (mateEquiv
        (bcLeftAdjunction data.rightPresentation)
        (bcRightAdjunction data.rightPresentation)
        (bcCoreTransportSquareIso data.rightPresentation).hom) := by
  exact mateEquiv_vcomp
    (bcLeftAdjunction data.leftPresentation)
    (bcRightAdjunction data.leftPresentation)
    (bcRightAdjunction data.rightPresentation)
    (bcCoreTransportSquareIso data.leftPresentation).hom
    (bcCoreTransportSquareIso data.rightPresentation).hom

/-- G-110(E) horizontal canonical-mate predecessor API: restate the generated
component route using the public `coreBeckChevalleyMate` declarations.  The
outer side remains the mate of the horizontally composed covariant squares;
northwest and reindexing alignment with `data.pastePresentation` is a later
obligation. -/
theorem horizontalBCPasting_coreBeckChevalleyMate_vcomp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : HorizontalBCPastingData U) :
    (mateEquiv
      (bcLeftAdjunction data.leftPresentation)
      (bcRightAdjunction data.rightPresentation)
      ((bcCoreTransportSquareIso data.leftPresentation).hom ≫ₕ
        (bcCoreTransportSquareIso data.rightPresentation).hom)) =
      (TwoSquare.mk _ _ _ _
        (coreBeckChevalleyMate data.leftPresentation)) ≫ᵥ
      (TwoSquare.mk _ _ _ _
        (coreBeckChevalleyMate data.rightPresentation)) := by
  simpa only [coreBeckChevalleyMate] using
    horizontalBCPasting_mateEquiv_vcomp data

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
