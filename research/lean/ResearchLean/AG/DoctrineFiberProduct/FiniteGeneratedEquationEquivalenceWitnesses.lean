import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationIndexDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObservableEquivalenceDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedReflectedContextEquivalenceWitnesses

/-!
# Concrete witnesses for generated equation equivalence descent

This module fires the reflected equation-index and equation-observable
producers on the existing selective-two generated-factor fixture.  The prefix
in that fixture is noninvertible, while the high factor is obtained from the
supplied high strong-cartesian lift.  No low equation equivalence or image
graph is supplied by a caller.

The selected finite-model equation index is `PUnit`, so the actual index
witness below establishes use of both directions and their high-image graphs,
but deliberately makes no sensitivity claim for that singleton family.  The
final section fires the same transparent conjugation primitives used by the
actual producers on nontrivial finite types and rings.  Those primitive checks
do not claim that the selected singleton index itself is nontrivial.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## The noninvertible selective-two actual producer -/

/--
The concrete source equation index in the outer generated domain.  Its
singleton value is used only to fire the actual forward and inverse graphs.
-/
noncomputable def finiteSelectiveTwoEquationSourceIndex :
    finiteSelectiveTwoContextEquivalenceOuterInput.lowGeneratedLift.domain.algebra.equationSystem.Index :=
  (inverseCorePackageForwardUpper FiniteModel.corePackage
    finiteSelectiveTwoContextEquivalenceOuterInput.hom).equationTransport.equationEquiv.symm
      PUnit.unit

/--
The concrete target index obtained by applying the reflected equivalence read
from the actual normalized high factor.
-/
noncomputable def finiteSelectiveTwoReflectedEquationTargetIndex :
    finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.algebra.equationSystem.Index :=
  finiteGeneratedReflectedEquationIndexEquiv.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoEquationSourceIndex

/--
At the concrete singleton index, the reflected forward map has exactly the
forward image of the actual normalized high equation-index equivalence.
-/
theorem finiteSelectiveTwoReflectedEquationIndex_forward_high_image :
    finiteGeneratedDomainEquationIndexEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoReflectedEquationTargetIndex.{u} =
      finiteGeneratedActualHighEquationIndexEquiv
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        (finiteGeneratedDomainEquationIndexEquiv.{u}
          finiteSelectiveTwoContextEquivalenceOuterInput
          finiteSelectiveTwoEquationSourceIndex) := by
  exact finiteGeneratedReflectedEquationIndex_forward_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoEquationSourceIndex

/--
At the concrete reflected target index, the reflected inverse has exactly the
inverse image of the actual normalized high equation-index equivalence.
-/
theorem finiteSelectiveTwoReflectedEquationIndex_inverse_high_image :
    finiteGeneratedDomainEquationIndexEquiv.{u}
        finiteSelectiveTwoContextEquivalenceOuterInput
        ((finiteGeneratedReflectedEquationIndexEquiv.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase).symm
            finiteSelectiveTwoReflectedEquationTargetIndex.{u}) =
      (finiteGeneratedActualHighEquationIndexEquiv
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase).symm
        (finiteGeneratedDomainEquationIndexEquiv.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoReflectedEquationTargetIndex.{u}) := by
  exact finiteGeneratedReflectedEquationIndex_inverse_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoReflectedEquationTargetIndex.{u}

/-- The concrete reflected target index lowers back to its concrete source. -/
@[simp]
theorem finiteSelectiveTwoReflectedEquationIndex_roundtrip :
    (finiteGeneratedReflectedEquationIndexEquiv.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase).symm
        finiteSelectiveTwoReflectedEquationTargetIndex.{u} =
      finiteSelectiveTwoEquationSourceIndex := by
  exact finiteGeneratedReflectedEquationIndex_symm_apply_apply.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoEquationSourceIndex

/-! ## A concrete equation-observable value -/

/-- The integer `3` in the outer generated equation-observable ring at `W`. -/
noncomputable def finiteSelectiveTwoEquationObservableThree :
    finiteSelectiveTwoContextEquivalenceOuterInput.lowGeneratedLift.domain.algebra.equationSystem.Observable
      finiteSelectiveTwoContextEquivalenceW :=
  ((inverseCorePackageForwardUpper FiniteModel.corePackage
    finiteSelectiveTwoContextEquivalenceOuterInput.hom).equationTransport.observableEquiv
      finiteSelectiveTwoContextEquivalenceW).symm (3 : Int)

/--
The reflected observable value obtained from `3` through the actual normalized
high observable equivalence.
-/
noncomputable def finiteSelectiveTwoReflectedEquationObservableThree :
    finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.algebra.equationSystem.Observable
      (finiteGeneratedReflectedForwardObject.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoContextEquivalenceW) :=
  finiteGeneratedReflectedEquationObservableEquiv.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoContextEquivalenceW
    finiteSelectiveTwoEquationObservableThree

/--
The generated high image of reflected `3` is the actual normalized high
observable image, with only the generated target-context cast inserted.
-/
theorem finiteSelectiveTwoReflectedEquationObservableThree_forward_high_image :
    finiteGeneratedEquationObservableEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        (finiteGeneratedReflectedForwardObject.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoContextEquivalenceW)
        finiteSelectiveTwoReflectedEquationObservableThree.{u} =
      finiteGeneratedReflectedEquationObservableTargetCast.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoContextEquivalenceW
        (finiteGeneratedActualHighEquationObservableEquiv.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          ((finiteGeneratedContextImageFunctor.{u}
            finiteSelectiveTwoContextEquivalenceOuterInput).obj
              finiteSelectiveTwoContextEquivalenceW)
          (finiteGeneratedEquationObservableEquiv.{u}
            finiteSelectiveTwoContextEquivalenceOuterInput
            finiteSelectiveTwoContextEquivalenceW
            finiteSelectiveTwoEquationObservableThree)) := by
  exact
    finiteGeneratedReflectedEquationObservableEquiv_apply_high_image.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase
      finiteSelectiveTwoContextEquivalenceW
      finiteSelectiveTwoEquationObservableThree

/--
The generated high image of the inverse at reflected `3` is computed by the
inverse actual high observable equivalence after undoing the endpoint cast.
-/
theorem finiteSelectiveTwoReflectedEquationObservableThree_inverse_high_image :
    finiteGeneratedEquationObservableEquiv.{u}
        finiteSelectiveTwoContextEquivalenceOuterInput
        finiteSelectiveTwoContextEquivalenceW
        ((finiteGeneratedReflectedEquationObservableEquiv.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoContextEquivalenceW).symm
            finiteSelectiveTwoReflectedEquationObservableThree.{u}) =
      (finiteGeneratedActualHighEquationObservableEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        ((finiteGeneratedContextImageFunctor.{u}
          finiteSelectiveTwoContextEquivalenceOuterInput).obj
            finiteSelectiveTwoContextEquivalenceW)).symm
        ((finiteGeneratedReflectedEquationObservableTargetCast.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoContextEquivalenceW).symm
          (finiteGeneratedEquationObservableEquiv.{u}
            finiteSelectiveTwoObjectContextWitnessInput
            (finiteGeneratedReflectedForwardObject.{u}
              finiteSelectiveTwoObjectContextWitnessInput
              finiteSelectiveTwoObjectContextWitnessLift.{u}
              finiteSelectiveTwoObjectContextWitnessBase
              finiteSelectiveTwoContextEquivalenceW)
            finiteSelectiveTwoReflectedEquationObservableThree.{u})) := by
  exact
    finiteGeneratedReflectedEquationObservableEquiv_symm_apply_high_image.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase
      finiteSelectiveTwoContextEquivalenceW
      finiteSelectiveTwoReflectedEquationObservableThree.{u}

/-- Reflected `3` returns to the concrete outer observable value `3`. -/
@[simp]
theorem finiteSelectiveTwoReflectedEquationObservableThree_roundtrip :
    (finiteGeneratedReflectedEquationObservableEquiv.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase
      finiteSelectiveTwoContextEquivalenceW).symm
        finiteSelectiveTwoReflectedEquationObservableThree.{u} =
      finiteSelectiveTwoEquationObservableThree := by
  exact
    (finiteGeneratedReflectedEquationObservableEquiv.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase
      finiteSelectiveTwoContextEquivalenceW).symm_apply_apply
        finiteSelectiveTwoEquationObservableThree

/-- The actual equation witnesses use the existing genuinely noninvertible prefix. -/
theorem finiteSelectiveTwoEquationEquivalenceWitness_base_not_isIso :
    ¬ IsIso finiteSelectiveTwoObjectContextWitnessBase :=
  finiteSelectiveTwoObjectContextWitnessBase_not_isIso

/-! ## Proof-used primitive sensitivity checks -/

private def primitiveBoolSwap : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := by
    intro value
    cases value <;> rfl
  right_inv := by
    intro value
    cases value <;> rfl

/--
The proof-used ordinary-equivalence conjugation is sensitive to its middle map:
replacing identity by Boolean swap changes the image of `false`.

This finite check supplements the actual singleton fixture without pretending
that its `PUnit` index family is itself sensitive.
-/
theorem primitiveEquationIndexConjugation_middle_sensitive :
    generatedEquationIndexEquivConjugation
        (Equiv.refl Bool) (Equiv.refl Bool) (Equiv.refl Bool) false ≠
      generatedEquationIndexEquivConjugation
        (Equiv.refl Bool) primitiveBoolSwap (Equiv.refl Bool) false := by
  intro equality
  change false = true at equality
  cases equality

/--
The proof-used ring-equivalence conjugation is sensitive to its middle map:
replacing identity by `RingEquiv.prodComm` changes `(0, 1)` to `(1, 0)`.

The generated producer calls this same primitive with internally generated
legs; this finite product-ring instance supplies none of those legs to it.
-/
theorem primitiveEquationObservableConjugation_middle_sensitive :
    generatedEquationObservableRingEquivConjugation
        (RingEquiv.refl (Int × Int))
        (RingEquiv.refl (Int × Int))
        (RingEquiv.refl (Int × Int)) ((0 : Int), (1 : Int)) ≠
      generatedEquationObservableRingEquivConjugation
        (RingEquiv.refl (Int × Int))
        (RingEquiv.prodComm : (Int × Int) ≃+* (Int × Int))
        (RingEquiv.refl (Int × Int)) ((0 : Int), (1 : Int)) := by
  intro equality
  have firstCoordinate := congrArg Prod.fst equality
  change (0 : Int) = 1 at firstCoordinate
  exact zero_ne_one firstCoordinate

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
