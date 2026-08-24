import ResearchLean.AG.DoctrineFiberProduct.BCVerticalPastingComparisonEquality
import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMate

/-!
# Vertical composition of generated Beck--Chevalley mates

This module specializes mathlib's horizontal mates-composition theorem to the
generated upper and lower component squares of a vertical G-110 pasting input.
It records the unit/counit coherence for the composed adjunctions before their
remaining alignment with the independently generated outer presentation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence
open CategoryTheory.NatTrans CategoryTheory.TwoSquare

set_option maxHeartbeats 2000000

/-- G-110(E) vertical canonical-mate predecessor: the mate of the generated
vertical composite of the two covariant component squares is the horizontal
composition of their generated mates, with the required reversal on the right
adjoint side.  The four adjunctions, comparisons, units, and counits are
generated from `VerticalBCPastingData`; no mate equality is caller-supplied.
This is an API theorem before composite-adjunction alignment with the outer
presentation. -/
theorem verticalBCPasting_mateEquiv_hcomp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    (mateEquiv
      ((bcLeftAdjunction data.upperPresentation).comp
        (bcLeftAdjunction data.lowerPresentation))
      ((bcRightAdjunction data.upperPresentation).comp
        (bcRightAdjunction data.lowerPresentation))
      ((bcCoreTransportSquareIso data.upperPresentation).hom ≫ᵥ
        (bcCoreTransportSquareIso data.lowerPresentation).hom)) =
      (mateEquiv
        (bcLeftAdjunction data.lowerPresentation)
        (bcRightAdjunction data.lowerPresentation)
        (bcCoreTransportSquareIso data.lowerPresentation).hom) ≫ₕ
      (mateEquiv
        (bcLeftAdjunction data.upperPresentation)
        (bcRightAdjunction data.upperPresentation)
        (bcCoreTransportSquareIso data.upperPresentation).hom) := by
  exact mateEquiv_hcomp
    (bcLeftAdjunction data.upperPresentation)
    (bcRightAdjunction data.upperPresentation)
    (bcLeftAdjunction data.lowerPresentation)
    (bcRightAdjunction data.lowerPresentation)
    (bcCoreTransportSquareIso data.upperPresentation).hom
    (bcCoreTransportSquareIso data.lowerPresentation).hom

/-- G-110(E) vertical canonical-mate predecessor API: restate the generated
component route using the public `coreBeckChevalleyMate` declarations.  The
outer side still uses composed adjunctions; comparison with the adjunctions of
`data.pastePresentation` remains open. -/
theorem verticalBCPasting_coreBeckChevalleyMate_hcomp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (data : VerticalBCPastingData U) :
    (mateEquiv
      ((bcLeftAdjunction data.upperPresentation).comp
        (bcLeftAdjunction data.lowerPresentation))
      ((bcRightAdjunction data.upperPresentation).comp
        (bcRightAdjunction data.lowerPresentation))
      ((bcCoreTransportSquareIso data.upperPresentation).hom ≫ᵥ
        (bcCoreTransportSquareIso data.lowerPresentation).hom)) =
      (TwoSquare.mk _ _ _ _
        (coreBeckChevalleyMate data.lowerPresentation)) ≫ₕ
      (TwoSquare.mk _ _ _ _
        (coreBeckChevalleyMate data.upperPresentation)) := by
  simpa only [coreBeckChevalleyMate] using
    verticalBCPasting_mateEquiv_hcomp data

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
