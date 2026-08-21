import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObservableNaturalityDescent

/-!
# Generated invariant and signature map descent

This module reflects the invariant-index map, signature-axis map, and
dependent signature-coordinate equivalence of the actual normalized high
prefix factor.  Canonical generated-domain equivalences identify the finite
indices, axes, and coordinates with their `ULift` images.  The dependent
coordinate target is aligned by the equality generated from the reflected
axis map itself.

No low upper morphism, image certificate, or whole signed morphism is supplied
or reconstructed here.  In particular, this module makes no invariant-law,
selected-axis, coordinate-read, or whole-`SignedExactCoreReadingHom` claim.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Proof-used conjugation primitives -/

/-- Conjugate a map through generated source and target equivalences. -/
def generatedIndexMapConjugation
    {L₀ H₀ L₁ H₁ : Type*}
    (sourceImage : L₀ ≃ H₀) (actual : H₀ → H₁)
    (targetImage : L₁ ≃ H₁) : L₀ → L₁ :=
  fun value => targetImage.symm (actual (sourceImage value))

/--
For fixed generated images, map conjugation is injective in its actual middle
map.  Thus the reflected singleton maps still retain their actual-high
provenance.
-/
theorem generatedIndexMapConjugation_actual_injective
    {L₀ H₀ L₁ H₁ : Type*}
    (sourceImage : L₀ ≃ H₀) (targetImage : L₁ ≃ H₁) :
    Function.Injective (fun actual : H₀ → H₁ =>
      generatedIndexMapConjugation sourceImage actual targetImage) := by
  intro first second equality
  funext value
  have pointEquality := congrFun equality (sourceImage.symm value)
  have highEquality := congrArg targetImage pointEquality
  simpa [generatedIndexMapConjugation] using highEquality

/--
Conjugate an equivalence through generated source and target images with one
explicit equivalence aligning its actual dependent target to the canonical
generated target.
-/
def generatedDependentEquivConjugation
    {L₀ H₀ H₁ H₁' L₁ : Type*}
    (sourceImage : L₀ ≃ H₀) (actual : H₀ ≃ H₁)
    (landing : H₁ ≃ H₁') (targetImage : L₁ ≃ H₁') : L₀ ≃ L₁ :=
  sourceImage.trans (actual.trans (landing.trans targetImage.symm))

/-- The target high image of dependent conjugation is its actual landed image. -/
theorem generatedDependentEquivConjugation_apply_high_image
    {L₀ H₀ H₁ H₁' L₁ : Type*}
    (sourceImage : L₀ ≃ H₀) (actual : H₀ ≃ H₁)
    (landing : H₁ ≃ H₁') (targetImage : L₁ ≃ H₁')
    (value : L₀) :
    targetImage
        (generatedDependentEquivConjugation sourceImage actual landing
          targetImage value) =
      landing (actual (sourceImage value)) := by
  change targetImage (targetImage.symm _) = _
  exact targetImage.apply_symm_apply _

/-- The source high image of inverse dependent conjugation is the inverse actual image. -/
theorem generatedDependentEquivConjugation_symm_apply_high_image
    {L₀ H₀ H₁ H₁' L₁ : Type*}
    (sourceImage : L₀ ≃ H₀) (actual : H₀ ≃ H₁)
    (landing : H₁ ≃ H₁') (targetImage : L₁ ≃ H₁')
    (value : L₁) :
    sourceImage
        ((generatedDependentEquivConjugation sourceImage actual landing
          targetImage).symm value) =
      actual.symm (landing.symm (targetImage value)) := by
  change sourceImage (sourceImage.symm _) = _
  exact sourceImage.apply_symm_apply _

/-! ## Generated-domain invariant indices -/

/-- The genuine equivalence from every generated low invariant index to its high image. -/
def finiteGeneratedInvariantIndexEquiv
    (input : FiniteGeneratedLiftInput) :
    input.lowGeneratedLift.domain.reading.invariantReading.Index ≃
      input.highGeneratedLift.domain.reading.invariantReading.Index := by
  change PUnit ≃ ULift.{u} PUnit
  exact Equiv.ulift.symm

/-- The named inverse of the generated invariant-index equivalence. -/
def finiteGeneratedInvariantIndexInverseEquiv
    (input : FiniteGeneratedLiftInput) :
    input.highGeneratedLift.domain.reading.invariantReading.Index ≃
      input.lowGeneratedLift.domain.reading.invariantReading.Index :=
  (finiteGeneratedInvariantIndexEquiv.{u} input).symm

/-- Every low invariant index maps to its canonical generated high lift. -/
@[simp]
theorem finiteGeneratedInvariantIndexEquiv_apply
    (input : FiniteGeneratedLiftInput)
    (index : input.lowGeneratedLift.domain.reading.invariantReading.Index) :
    finiteGeneratedInvariantIndexEquiv.{u} input index =
      input.generatedDomainInvariantIndexLift index :=
  rfl

/-- Every high invariant index maps back by `ULift.down`. -/
@[simp]
theorem finiteGeneratedInvariantIndexInverseEquiv_apply
    (input : FiniteGeneratedLiftInput)
    (index : input.highGeneratedLift.domain.reading.invariantReading.Index) :
    finiteGeneratedInvariantIndexInverseEquiv.{u} input index = ULift.down index :=
  rfl

/-- Invariant-index lifting followed by its named inverse is the identity. -/
@[simp]
theorem finiteGeneratedInvariantIndexInverseEquiv_apply_apply
    (input : FiniteGeneratedLiftInput)
    (index : input.lowGeneratedLift.domain.reading.invariantReading.Index) :
    finiteGeneratedInvariantIndexInverseEquiv.{u} input
        (finiteGeneratedInvariantIndexEquiv.{u} input index) = index :=
  (finiteGeneratedInvariantIndexEquiv.{u} input).symm_apply_apply index

/-- The named inverse followed by invariant-index lifting is the identity. -/
@[simp]
theorem finiteGeneratedInvariantIndexEquiv_apply_inverse_apply
    (input : FiniteGeneratedLiftInput)
    (index : input.highGeneratedLift.domain.reading.invariantReading.Index) :
    finiteGeneratedInvariantIndexEquiv.{u} input
        (finiteGeneratedInvariantIndexInverseEquiv.{u} input index) = index :=
  (finiteGeneratedInvariantIndexEquiv.{u} input).apply_symm_apply index

/-! ## Generated-domain signature axes and coordinates -/

/-- The genuine equivalence from every generated low signature axis to its high image. -/
def finiteGeneratedSignatureAxisEquiv
    (input : FiniteGeneratedLiftInput) :
    input.lowGeneratedLift.domain.reading.signatureReading.Axis ≃
      input.highGeneratedLift.domain.reading.signatureReading.Axis := by
  change PUnit ≃ ULift.{u} PUnit
  exact Equiv.ulift.symm

/-- The named inverse of the generated signature-axis equivalence. -/
def finiteGeneratedSignatureAxisInverseEquiv
    (input : FiniteGeneratedLiftInput) :
    input.highGeneratedLift.domain.reading.signatureReading.Axis ≃
      input.lowGeneratedLift.domain.reading.signatureReading.Axis :=
  (finiteGeneratedSignatureAxisEquiv.{u} input).symm

/-- Every low signature axis maps to its canonical generated high lift. -/
@[simp]
theorem finiteGeneratedSignatureAxisEquiv_apply
    (input : FiniteGeneratedLiftInput)
    (axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis) :
    finiteGeneratedSignatureAxisEquiv.{u} input axis =
      input.generatedDomainSignatureAxisLift axis :=
  rfl

/-- Every high signature axis maps back by `ULift.down`. -/
@[simp]
theorem finiteGeneratedSignatureAxisInverseEquiv_apply
    (input : FiniteGeneratedLiftInput)
    (axis : input.highGeneratedLift.domain.reading.signatureReading.Axis) :
    finiteGeneratedSignatureAxisInverseEquiv.{u} input axis = ULift.down axis :=
  rfl

/-- Signature-axis lifting followed by its named inverse is the identity. -/
@[simp]
theorem finiteGeneratedSignatureAxisInverseEquiv_apply_apply
    (input : FiniteGeneratedLiftInput)
    (axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis) :
    finiteGeneratedSignatureAxisInverseEquiv.{u} input
        (finiteGeneratedSignatureAxisEquiv.{u} input axis) = axis :=
  (finiteGeneratedSignatureAxisEquiv.{u} input).symm_apply_apply axis

/-- The named inverse followed by signature-axis lifting is the identity. -/
@[simp]
theorem finiteGeneratedSignatureAxisEquiv_apply_inverse_apply
    (input : FiniteGeneratedLiftInput)
    (axis : input.highGeneratedLift.domain.reading.signatureReading.Axis) :
    finiteGeneratedSignatureAxisEquiv.{u} input
        (finiteGeneratedSignatureAxisInverseEquiv.{u} input axis) = axis :=
  (finiteGeneratedSignatureAxisEquiv.{u} input).apply_symm_apply axis

/--
The dependent equivalence between every generated low coordinate carrier and
the high coordinate carrier over its canonically lifted axis.
-/
def finiteGeneratedSignatureCoordinateEquiv
    (input : FiniteGeneratedLiftInput)
    (axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis) :
    input.lowGeneratedLift.domain.reading.signatureReading.Coordinate axis ≃
      input.highGeneratedLift.domain.reading.signatureReading.Coordinate
        (finiteGeneratedSignatureAxisEquiv.{u} input axis) := by
  change Nat ≃ ULift.{u} Nat
  exact Equiv.ulift.symm

/-- The named inverse of the generated dependent coordinate equivalence. -/
def finiteGeneratedSignatureCoordinateInverseEquiv
    (input : FiniteGeneratedLiftInput)
    (axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis) :
    input.highGeneratedLift.domain.reading.signatureReading.Coordinate
        (finiteGeneratedSignatureAxisEquiv.{u} input axis) ≃
      input.lowGeneratedLift.domain.reading.signatureReading.Coordinate axis :=
  (finiteGeneratedSignatureCoordinateEquiv.{u} input axis).symm

/-- Every low coordinate maps to its canonical generated high lift. -/
@[simp]
theorem finiteGeneratedSignatureCoordinateEquiv_apply
    (input : FiniteGeneratedLiftInput)
    (axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis)
    (coordinate : input.lowGeneratedLift.domain.reading.signatureReading.Coordinate axis) :
    finiteGeneratedSignatureCoordinateEquiv.{u} input axis coordinate =
      input.generatedDomainSignatureCoordinateLift axis coordinate :=
  rfl

/-- Every high coordinate over a generated axis maps back by `ULift.down`. -/
@[simp]
theorem finiteGeneratedSignatureCoordinateInverseEquiv_apply
    (input : FiniteGeneratedLiftInput)
    (axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis)
    (coordinate : input.highGeneratedLift.domain.reading.signatureReading.Coordinate
      (finiteGeneratedSignatureAxisEquiv.{u} input axis)) :
    finiteGeneratedSignatureCoordinateInverseEquiv.{u} input axis coordinate =
      ULift.down coordinate :=
  rfl

/-- Coordinate lifting followed by its named inverse is the identity. -/
@[simp]
theorem finiteGeneratedSignatureCoordinateInverseEquiv_apply_apply
    (input : FiniteGeneratedLiftInput)
    (axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis)
    (coordinate : input.lowGeneratedLift.domain.reading.signatureReading.Coordinate axis) :
    finiteGeneratedSignatureCoordinateInverseEquiv.{u} input axis
        (finiteGeneratedSignatureCoordinateEquiv.{u} input axis coordinate) = coordinate :=
  (finiteGeneratedSignatureCoordinateEquiv.{u} input axis).symm_apply_apply coordinate

/-- The named inverse followed by coordinate lifting is the identity. -/
@[simp]
theorem finiteGeneratedSignatureCoordinateEquiv_apply_inverse_apply
    (input : FiniteGeneratedLiftInput)
    (axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis)
    (coordinate : input.highGeneratedLift.domain.reading.signatureReading.Coordinate
      (finiteGeneratedSignatureAxisEquiv.{u} input axis)) :
    finiteGeneratedSignatureCoordinateEquiv.{u} input axis
        (finiteGeneratedSignatureCoordinateInverseEquiv.{u} input axis coordinate) = coordinate :=
  (finiteGeneratedSignatureCoordinateEquiv.{u} input axis).apply_symm_apply coordinate

/-! ## Actual-derived reflected maps -/

/--
Reflect the actual normalized high invariant-index map through the two
generated invariant-index equivalences.
-/
noncomputable def finiteGeneratedReflectedInvariantMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.invariantReading.Index →
      input.lowGeneratedLift.domain.reading.invariantReading.Index :=
  generatedIndexMapConjugation
    (finiteGeneratedInvariantIndexEquiv.{u}
      (finiteGeneratedOuterInput input base))
    (finiteGeneratedNormalizedHighFactor input lift base).upper.invariantMap
    (finiteGeneratedInvariantIndexEquiv.{u} input)

/-- The reflected invariant map is the inverse generated image of the actual map. -/
theorem finiteGeneratedReflectedInvariantMap_inverse_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.invariantReading.Index) :
    finiteGeneratedReflectedInvariantMap input lift base index =
      finiteGeneratedInvariantIndexInverseEquiv.{u} input
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.invariantMap
          (finiteGeneratedInvariantIndexEquiv.{u}
            (finiteGeneratedOuterInput input base) index)) :=
  rfl

/-- The high image of every reflected invariant index is the actual high image. -/
theorem finiteGeneratedReflectedInvariantMap_high_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.invariantReading.Index) :
    finiteGeneratedInvariantIndexEquiv.{u} input
        (finiteGeneratedReflectedInvariantMap input lift base index) =
      (finiteGeneratedNormalizedHighFactor input lift base).upper.invariantMap
        (finiteGeneratedInvariantIndexEquiv.{u}
          (finiteGeneratedOuterInput input base) index) := by
  change (finiteGeneratedInvariantIndexEquiv.{u} input)
      ((finiteGeneratedInvariantIndexEquiv.{u} input).symm _) = _
  exact (finiteGeneratedInvariantIndexEquiv.{u} input).apply_symm_apply _

/--
For every actual high source invariant index, reflecting its generated inverse
image and lifting the result recovers the actual high invariant-map value.
-/
theorem finiteGeneratedReflectedInvariantMap_inverse_source_high_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (highIndex : (finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.invariantReading.Index) :
    finiteGeneratedInvariantIndexEquiv.{u} input
        (finiteGeneratedReflectedInvariantMap input lift base
          ((finiteGeneratedInvariantIndexEquiv.{u}
            (finiteGeneratedOuterInput input base)).symm highIndex)) =
      (finiteGeneratedNormalizedHighFactor input lift base).upper.invariantMap
        highIndex := by
  rw [finiteGeneratedReflectedInvariantMap_high_image]
  rw [(finiteGeneratedInvariantIndexEquiv.{u}
    (finiteGeneratedOuterInput input base)).apply_symm_apply]

/--
Reflect the actual normalized high signature-axis map through the two
generated signature-axis equivalences.
-/
noncomputable def finiteGeneratedReflectedAxisMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis →
      input.lowGeneratedLift.domain.reading.signatureReading.Axis :=
  generatedIndexMapConjugation
    (finiteGeneratedSignatureAxisEquiv.{u}
      (finiteGeneratedOuterInput input base))
    (finiteGeneratedNormalizedHighFactor input lift base).upper.axisMap
    (finiteGeneratedSignatureAxisEquiv.{u} input)

/-- The reflected axis map is the inverse generated image of the actual map. -/
theorem finiteGeneratedReflectedAxisMap_inverse_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis) :
    finiteGeneratedReflectedAxisMap input lift base axis =
      finiteGeneratedSignatureAxisInverseEquiv.{u} input
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.axisMap
          (finiteGeneratedSignatureAxisEquiv.{u}
            (finiteGeneratedOuterInput input base) axis)) :=
  rfl

/-- The high image of every reflected signature axis is the actual high image. -/
theorem finiteGeneratedReflectedAxisMap_high_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis) :
    finiteGeneratedSignatureAxisEquiv.{u} input
        (finiteGeneratedReflectedAxisMap input lift base axis) =
      (finiteGeneratedNormalizedHighFactor input lift base).upper.axisMap
        (finiteGeneratedSignatureAxisEquiv.{u}
          (finiteGeneratedOuterInput input base) axis) := by
  change (finiteGeneratedSignatureAxisEquiv.{u} input)
      ((finiteGeneratedSignatureAxisEquiv.{u} input).symm _) = _
  exact (finiteGeneratedSignatureAxisEquiv.{u} input).apply_symm_apply _

/--
For every actual high source signature axis, reflecting its generated inverse
image and lifting the result recovers the actual high axis-map value.
-/
theorem finiteGeneratedReflectedAxisMap_inverse_source_high_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (highAxis : (finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.signatureReading.Axis) :
    finiteGeneratedSignatureAxisEquiv.{u} input
        (finiteGeneratedReflectedAxisMap input lift base
          ((finiteGeneratedSignatureAxisEquiv.{u}
            (finiteGeneratedOuterInput input base)).symm highAxis)) =
      (finiteGeneratedNormalizedHighFactor input lift base).upper.axisMap
        highAxis := by
  rw [finiteGeneratedReflectedAxisMap_high_image]
  rw [(finiteGeneratedSignatureAxisEquiv.{u}
    (finiteGeneratedOuterInput input base)).apply_symm_apply]

/--
The dependent cast from the actual high coordinate target to the canonical
generated high target selected by the reflected axis map.
-/
noncomputable def finiteGeneratedReflectedCoordinateLandingEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis) :
    input.highGeneratedLift.domain.reading.signatureReading.Coordinate
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.axisMap
          (finiteGeneratedSignatureAxisEquiv.{u}
            (finiteGeneratedOuterInput input base) axis)) ≃
      input.highGeneratedLift.domain.reading.signatureReading.Coordinate
        (finiteGeneratedSignatureAxisEquiv.{u} input
          (finiteGeneratedReflectedAxisMap input lift base axis)) :=
  Equiv.cast (congrArg
    input.highGeneratedLift.domain.reading.signatureReading.Coordinate
    (finiteGeneratedReflectedAxisMap_high_image input lift base axis).symm)

/--
Reflect the actual normalized high coordinate equivalence, including the
dependent landing cast generated from its reflected axis image.
-/
noncomputable def finiteGeneratedReflectedCoordinateEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis) :
    (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Coordinate axis ≃
      input.lowGeneratedLift.domain.reading.signatureReading.Coordinate
        (finiteGeneratedReflectedAxisMap input lift base axis) :=
  generatedDependentEquivConjugation
    (finiteGeneratedSignatureCoordinateEquiv.{u}
      (finiteGeneratedOuterInput input base) axis)
    ((finiteGeneratedNormalizedHighFactor input lift base).upper.coordinateEquiv
      (finiteGeneratedSignatureAxisEquiv.{u}
        (finiteGeneratedOuterInput input base) axis))
    (finiteGeneratedReflectedCoordinateLandingEquiv input lift base axis)
    (finiteGeneratedSignatureCoordinateEquiv.{u} input
      (finiteGeneratedReflectedAxisMap input lift base axis))

/--
The target high image of every reflected coordinate is the landed actual high
coordinate image.
-/
theorem finiteGeneratedReflectedCoordinateEquiv_apply_high_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis)
    (coordinate : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Coordinate axis) :
    finiteGeneratedSignatureCoordinateEquiv.{u} input
        (finiteGeneratedReflectedAxisMap input lift base axis)
        (finiteGeneratedReflectedCoordinateEquiv input lift base axis coordinate) =
      finiteGeneratedReflectedCoordinateLandingEquiv input lift base axis
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.coordinateEquiv
          (finiteGeneratedSignatureAxisEquiv.{u}
            (finiteGeneratedOuterInput input base) axis)
          (finiteGeneratedSignatureCoordinateEquiv.{u}
            (finiteGeneratedOuterInput input base) axis coordinate)) :=
  generatedDependentEquivConjugation_apply_high_image _ _ _ _ _

/--
The source high image of every inverse reflected coordinate is the inverse
actual image after undoing the dependent landing cast.
-/
theorem finiteGeneratedReflectedCoordinateEquiv_symm_apply_high_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis)
    (coordinate : input.lowGeneratedLift.domain.reading.signatureReading.Coordinate
      (finiteGeneratedReflectedAxisMap input lift base axis)) :
    finiteGeneratedSignatureCoordinateEquiv.{u}
        (finiteGeneratedOuterInput input base) axis
        ((finiteGeneratedReflectedCoordinateEquiv input lift base axis).symm coordinate) =
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.coordinateEquiv
        (finiteGeneratedSignatureAxisEquiv.{u}
          (finiteGeneratedOuterInput input base) axis)).symm
        ((finiteGeneratedReflectedCoordinateLandingEquiv input lift base axis).symm
          (finiteGeneratedSignatureCoordinateEquiv.{u} input
            (finiteGeneratedReflectedAxisMap input lift base axis) coordinate)) :=
  generatedDependentEquivConjugation_symm_apply_high_image _ _ _ _ _

/-- Reflected coordinate forward transport followed by its inverse is the identity. -/
@[simp]
theorem finiteGeneratedReflectedCoordinateEquiv_symm_apply_apply
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis)
    (coordinate : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Coordinate axis) :
    (finiteGeneratedReflectedCoordinateEquiv input lift base axis).symm
        (finiteGeneratedReflectedCoordinateEquiv input lift base axis coordinate) = coordinate :=
  (finiteGeneratedReflectedCoordinateEquiv input lift base axis).symm_apply_apply coordinate

/-- Reflected coordinate inverse transport followed by its forward map is the identity. -/
@[simp]
theorem finiteGeneratedReflectedCoordinateEquiv_apply_symm_apply
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis)
    (coordinate : input.lowGeneratedLift.domain.reading.signatureReading.Coordinate
      (finiteGeneratedReflectedAxisMap input lift base axis)) :
    finiteGeneratedReflectedCoordinateEquiv input lift base axis
        ((finiteGeneratedReflectedCoordinateEquiv input lift base axis).symm coordinate) =
      coordinate :=
  (finiteGeneratedReflectedCoordinateEquiv input lift base axis).apply_symm_apply coordinate

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
