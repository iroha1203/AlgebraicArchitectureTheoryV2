import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedReflectedContextEquivalence

/-!
# Reflection of generated equation-index equivalences

This module reflects the equation-index equivalence read directly from an
actual normalized high factor.  The two comparison equivalences are generated
from the low and high inverse-package uppers and the canonical finite-model
`ULift` index equivalence.  The resulting producer covers the complete index
families; the remaining fields of `EquationSystemExactTransport` are separate
proof obligations.

The producer accepts only the finite generated input, the supplied high strong
cartesian lift, and the ambient prefix.  In particular, it does not accept a
low equation equivalence or an index graph.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## The proof-used index-conjugation primitive -/

/--
Conjugate an actual equation-index equivalence through generated source and
target image equivalences.  This low-level primitive is used transparently by
the actual reflected producer below; it is not an additional producer input.
-/
def generatedEquationIndexEquivConjugation
    {L₀ H₀ H₁ L₁ : Type*}
    (sourceImage : L₀ ≃ H₀)
    (actual : H₀ ≃ H₁)
    (targetImage : L₁ ≃ H₁) : L₀ ≃ L₁ :=
  sourceImage.trans (actual.trans targetImage.symm)

/--
For fixed generated images, index conjugation is injective in the actual
middle equivalence.
-/
theorem generatedEquationIndexEquivConjugation_actual_injective
    {L₀ H₀ H₁ L₁ : Type*}
    (sourceImage : L₀ ≃ H₀)
    (targetImage : L₁ ≃ H₁) :
    Function.Injective (fun actual : H₀ ≃ H₁ =>
      generatedEquationIndexEquivConjugation sourceImage actual targetImage) := by
  intro first second equality
  apply Equiv.ext
  intro value
  have pointEquality := congrArg
    (fun output : L₀ ≃ L₁ =>
      targetImage (output (sourceImage.symm value))) equality
  simpa [generatedEquationIndexEquivConjugation] using pointEquality

/-! ## The selected target index equivalence -/

/-- Reflect an equation index of the selected lifted target through `ULift`. -/
def finiteModelTargetEquationIndexReflect
    (index : finiteModelLiftCorePackage.{u}.algebra.equationSystem.Index) :
    FiniteModel.corePackage.algebra.equationSystem.Index := by
  change ULift.{u} FiniteModel.corePackage.algebra.equationSystem.Index at index
  exact index.down

/--
The complete finite-model target index family is canonically equivalent to its
lifted target index family.
-/
def finiteModelTargetEquationIndexEquiv :
    FiniteModel.corePackage.algebra.equationSystem.Index ≃
      finiteModelLiftCorePackage.{u}.algebra.equationSystem.Index where
  toFun := FiniteGeneratedLiftInput.targetEquationIndexLift.{u}
  invFun := finiteModelTargetEquationIndexReflect.{u}
  left_inv := by
    intro index
    rfl
  right_inv := by
    intro index
    change ULift.{u} FiniteModel.corePackage.algebra.equationSystem.Index at index
    cases index
    rfl

/-- The target index equivalence computes by the existing canonical lift. -/
@[simp]
theorem finiteModelTargetEquationIndexEquiv_apply
    (index : FiniteModel.corePackage.algebra.equationSystem.Index) :
    finiteModelTargetEquationIndexEquiv.{u} index =
      FiniteGeneratedLiftInput.targetEquationIndexLift.{u} index :=
  rfl

/-- The inverse target index equivalence computes by `ULift` reflection. -/
@[simp]
theorem finiteModelTargetEquationIndexEquiv_symm_apply
    (index : finiteModelLiftCorePackage.{u}.algebra.equationSystem.Index) :
    finiteModelTargetEquationIndexEquiv.{u}.symm index =
      finiteModelTargetEquationIndexReflect.{u} index :=
  rfl

/-! ## Complete generated-domain index images -/

/--
Canonical equivalence from every low generated-domain equation index to the
corresponding high generated-domain index.

Implementation notes: the low upper first maps to the selected low target,
`finiteModelTargetEquationIndexEquiv` raises the universe, and the inverse high
upper returns to the high generated domain.  This is the equivalence completion
of the existing `generatedDomainEquationIndexLift` map.
-/
noncomputable def finiteGeneratedDomainEquationIndexEquiv
    (input : FiniteGeneratedLiftInput) :
    input.lowGeneratedLift.domain.algebra.equationSystem.Index ≃
      input.highGeneratedLift.domain.algebra.equationSystem.Index := by
  change
    (inverseCorePackage FiniteModel.corePackage
      input.hom).algebra.equationSystem.Index ≃
      input.highPackageFromLowData.algebra.equationSystem.Index
  exact
    (inverseCorePackageForwardUpper FiniteModel.corePackage
      input.hom).equationEquiv |>.trans
      (finiteModelTargetEquationIndexEquiv.{u}.trans
        input.highPackageHomFromLowData.upper.equationEquiv.symm)

/-- The generated-domain equivalence has the existing generated lift as its map. -/
@[simp]
theorem finiteGeneratedDomainEquationIndexEquiv_apply
    (input : FiniteGeneratedLiftInput)
    (index : input.lowGeneratedLift.domain.algebra.equationSystem.Index) :
    finiteGeneratedDomainEquationIndexEquiv.{u} input index =
      input.generatedDomainEquationIndexLift index :=
  rfl

/-- Reflect a high generated-domain equation index through the canonical image. -/
noncomputable def finiteGeneratedDomainEquationIndexReflect
    (input : FiniteGeneratedLiftInput)
    (index : input.highGeneratedLift.domain.algebra.equationSystem.Index) :
    input.lowGeneratedLift.domain.algebra.equationSystem.Index :=
  (finiteGeneratedDomainEquationIndexEquiv.{u} input).symm index

/-- The inverse generated-domain equivalence computes by the named reflector. -/
@[simp]
theorem finiteGeneratedDomainEquationIndexEquiv_symm_apply
    (input : FiniteGeneratedLiftInput)
    (index : input.highGeneratedLift.domain.algebra.equationSystem.Index) :
    (finiteGeneratedDomainEquationIndexEquiv.{u} input).symm index =
      finiteGeneratedDomainEquationIndexReflect.{u} input index :=
  rfl

/-- Reflecting a canonically lifted generated-domain index recovers the source. -/
@[simp]
theorem finiteGeneratedDomainEquationIndex_reflect_lift
    (input : FiniteGeneratedLiftInput)
    (index : input.lowGeneratedLift.domain.algebra.equationSystem.Index) :
    finiteGeneratedDomainEquationIndexReflect.{u} input
        (input.generatedDomainEquationIndexLift index) = index := by
  unfold finiteGeneratedDomainEquationIndexReflect
  rw [← finiteGeneratedDomainEquationIndexEquiv_apply]
  exact (finiteGeneratedDomainEquationIndexEquiv.{u} input).symm_apply_apply index

/-- Lifting a reflected high generated-domain index recovers the target. -/
@[simp]
theorem finiteGeneratedDomainEquationIndex_lift_reflect
    (input : FiniteGeneratedLiftInput)
    (index : input.highGeneratedLift.domain.algebra.equationSystem.Index) :
    input.generatedDomainEquationIndexLift
        (finiteGeneratedDomainEquationIndexReflect.{u} input index) = index := by
  unfold finiteGeneratedDomainEquationIndexReflect
  rw [← finiteGeneratedDomainEquationIndexEquiv_apply]
  exact (finiteGeneratedDomainEquationIndexEquiv.{u} input).apply_symm_apply index

/-! ## Reflection of the actual normalized high index equivalence -/

/--
The equation-index equivalence projected directly from the actual normalized
high factor supplied by its strong-cartesian universal property.
-/
noncomputable def finiteGeneratedActualHighEquationIndexEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedOuterInput input base).highGeneratedLift.domain.algebra.equationSystem.Index ≃
      input.highGeneratedLift.domain.algebra.equationSystem.Index :=
  (finiteGeneratedNormalizedHighFactor input lift base).upper.equationTransport.equationEquiv

/-- The low index-equivalence type reflected across the two generated images. -/
abbrev FiniteGeneratedReflectedEquationIndexEquivOutput
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :=
  (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index ≃
    input.lowGeneratedLift.domain.algebra.equationSystem.Index

/--
Reflect the actual normalized high equation-index equivalence through the two
canonical generated-domain index images.

The actual high field occurs transparently in the definition body; no equality
with a canonical factor and no pre-existing low factor is used.
-/
noncomputable def finiteGeneratedReflectedEquationIndexEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    FiniteGeneratedReflectedEquationIndexEquivOutput input base :=
  generatedEquationIndexEquivConjugation
    (finiteGeneratedDomainEquationIndexEquiv.{u}
      (finiteGeneratedOuterInput input base))
    (finiteGeneratedActualHighEquationIndexEquiv input lift base)
    (finiteGeneratedDomainEquationIndexEquiv.{u} input)

/--
The reflected forward map reproduces the actual normalized high forward map
after applying the canonical generated-domain images.
-/
theorem finiteGeneratedReflectedEquationIndex_forward_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index) :
    finiteGeneratedDomainEquationIndexEquiv.{u} input
        (finiteGeneratedReflectedEquationIndexEquiv input lift base index) =
      finiteGeneratedActualHighEquationIndexEquiv input lift base
        (finiteGeneratedDomainEquationIndexEquiv.{u}
          (finiteGeneratedOuterInput input base) index) := by
  change
    finiteGeneratedDomainEquationIndexEquiv.{u} input
        ((finiteGeneratedDomainEquationIndexEquiv.{u} input).symm
          (finiteGeneratedActualHighEquationIndexEquiv input lift base
            (finiteGeneratedDomainEquationIndexEquiv.{u}
              (finiteGeneratedOuterInput input base) index))) = _
  exact (finiteGeneratedDomainEquationIndexEquiv.{u} input).apply_symm_apply _

/--
The reflected inverse map reproduces the inverse actual high map after applying
the canonical generated-domain images.
-/
theorem finiteGeneratedReflectedEquationIndex_inverse_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : input.lowGeneratedLift.domain.algebra.equationSystem.Index) :
    finiteGeneratedDomainEquationIndexEquiv.{u}
        (finiteGeneratedOuterInput input base)
        ((finiteGeneratedReflectedEquationIndexEquiv
          input lift base).symm index) =
      (finiteGeneratedActualHighEquationIndexEquiv
        input lift base).symm
        (finiteGeneratedDomainEquationIndexEquiv.{u} input index) := by
  change
    finiteGeneratedDomainEquationIndexEquiv.{u}
        (finiteGeneratedOuterInput input base)
        ((finiteGeneratedDomainEquationIndexEquiv.{u}
          (finiteGeneratedOuterInput input base)).symm
          ((finiteGeneratedActualHighEquationIndexEquiv
            input lift base).symm
            (finiteGeneratedDomainEquationIndexEquiv.{u} input index))) = _
  exact
    (finiteGeneratedDomainEquationIndexEquiv.{u}
      (finiteGeneratedOuterInput input base)).apply_symm_apply _

/-- The reflected inverse followed by the reflected forward map is identity. -/
@[simp]
theorem finiteGeneratedReflectedEquationIndex_symm_apply_apply
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index) :
    (finiteGeneratedReflectedEquationIndexEquiv input lift base).symm
        (finiteGeneratedReflectedEquationIndexEquiv input lift base index) =
      index :=
  (finiteGeneratedReflectedEquationIndexEquiv input lift base).symm_apply_apply index

/-- The reflected forward map followed by its inverse is identity. -/
@[simp]
theorem finiteGeneratedReflectedEquationIndex_apply_symm_apply
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : input.lowGeneratedLift.domain.algebra.equationSystem.Index) :
    finiteGeneratedReflectedEquationIndexEquiv input lift base
        ((finiteGeneratedReflectedEquationIndexEquiv
          input lift base).symm index) = index :=
  (finiteGeneratedReflectedEquationIndexEquiv input lift base).apply_symm_apply index

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
