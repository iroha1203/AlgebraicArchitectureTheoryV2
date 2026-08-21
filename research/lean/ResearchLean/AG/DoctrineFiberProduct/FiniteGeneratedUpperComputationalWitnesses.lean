import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedOperationMapDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedInvariantSignatureMapDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObjectContextImageWitnesses

/-!
# Concrete witnesses for generated upper computational descent

This module fires the operation, invariant-index, signature-axis, and
signature-coordinate producers on the existing selective-two noninvertible
fixture.  The operation witness transports the reviewed finite collapse into
the outer generated domain and retains its visibly moved Atom.  The invariant
and axis witnesses exercise both generated image directions, while the
coordinate witness sends the concrete value `3` through the actual-derived
dependent equivalence and back.

The selected invariant and axis carriers are singleton types.  The final
finite checks therefore exercise the exact transparent conjugation primitives
on `Bool`; they do not claim that the selected `PUnit` families are themselves
sensitive.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Shared selective-two input -/

/-- The outer generated input determined by the existing selective-two prefix. -/
noncomputable def finiteSelectiveTwoUpperComputationalOuterInput :
    FiniteGeneratedLiftInput :=
  finiteGeneratedOuterInput finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessBase

/-- The selective-two prefix used by all upper computational witnesses is noninvertible. -/
theorem finiteSelectiveTwoUpperComputationalBase_not_isIso :
    ¬ IsIso finiteSelectiveTwoObjectContextWitnessBase :=
  finiteSelectiveTwoObjectContextWitnessBase_not_isIso

/-! ## A genuinely nonidentity operation -/

/--
The generated backward upper from the finite core into the outer inverse
package.  It is used only to move the existing collapse operation into the
source type required by the actual reflected operation producer.
-/
noncomputable def finiteSelectiveTwoCollapseBackwardUpper :
    SignedExactCoreReadingHom FiniteModel.corePackage
      finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain :=
  inverseCorePackageBackwardUpper FiniteModel.corePackage
    finiteSelectiveTwoUpperComputationalOuterInput.hom

/-- The outer generated-domain source object of the transported collapse. -/
noncomputable def finiteSelectiveTwoCollapseSourceObject :
    ArchitectureObject FiniteModel.carrier :=
  finiteSelectiveTwoCollapseBackwardUpper.objectMap
    FiniteModel.corePackage.object

/-- The outer generated-domain target object of the transported collapse. -/
noncomputable def finiteSelectiveTwoCollapseTargetObject :
    ArchitectureObject FiniteModel.carrier :=
  finiteSelectiveTwoCollapseBackwardUpper.objectMap
    FiniteModel.collapsedObject

/--
The reviewed nonidentity finite collapse transported into the outer low
generated domain.
-/
noncomputable def finiteSelectiveTwoOuterCollapseOperation :
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.operationReading.Op
      finiteSelectiveTwoCollapseSourceObject
      finiteSelectiveTwoCollapseTargetObject :=
  finiteSelectiveTwoCollapseBackwardUpper.operationMap
    FiniteModel.collapseOperation

/-- The transported collapse sends the transported `componentA` to `componentB`. -/
theorem finiteSelectiveTwoOuterCollapseOperation_atom_graph :
    let e := finiteSelectiveTwoUpperComputationalOuterInput.hom.doctrineHom.atomEquiv
    (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.operationReading.configurationMap
      finiteSelectiveTwoOuterCollapseOperation).atomMap
        (e.symm FiniteModel.FiniteAtom.componentA) =
      e.symm FiniteModel.FiniteAtom.componentB := by
  let e := finiteSelectiveTwoUpperComputationalOuterInput.hom.doctrineHom.atomEquiv
  have htransport := congrFun
    (transportOperation_configurationMap_atomMap e.symm
      FiniteModel.corePackage.reading.operationReading
      FiniteModel.collapseOperation)
    (e.symm FiniteModel.FiniteAtom.componentA)
  simpa [finiteSelectiveTwoOuterCollapseOperation,
    finiteSelectiveTwoCollapseBackwardUpper, e, Function.comp_def,
    FiniteModel.collapseOperation_atomMap_nonidentity.1] using htransport

/-- The transported collapse genuinely moves its selected source Atom. -/
theorem finiteSelectiveTwoOuterCollapseOperation_nonidentity :
    let e := finiteSelectiveTwoUpperComputationalOuterInput.hom.doctrineHom.atomEquiv
    (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.operationReading.configurationMap
      finiteSelectiveTwoOuterCollapseOperation).atomMap
        (e.symm FiniteModel.FiniteAtom.componentA) ≠
      e.symm FiniteModel.FiniteAtom.componentA := by
  change
    (finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.operationReading.configurationMap
      finiteSelectiveTwoOuterCollapseOperation).atomMap
        (finiteSelectiveTwoUpperComputationalOuterInput.hom.doctrineHom.atomEquiv.symm
          FiniteModel.FiniteAtom.componentA) ≠
      finiteSelectiveTwoUpperComputationalOuterInput.hom.doctrineHom.atomEquiv.symm
        FiniteModel.FiniteAtom.componentA
  rw [finiteSelectiveTwoOuterCollapseOperation_atom_graph]
  intro equality
  exact FiniteModel.collapseOperation_atomMap_nonidentity.2
    (finiteSelectiveTwoUpperComputationalOuterInput.hom.doctrineHom.atomEquiv.symm.injective
      equality).symm

/--
The collapse operation reflected from the actual normalized high factor, with
both endpoints generated internally from its complete object images.
-/
noncomputable def finiteSelectiveTwoActualReflectedCollapseOperation :=
  finiteGeneratedReflectedOperationMap.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoOuterCollapseOperation

/-- The concrete reflected collapse has the actual normalized high forward image. -/
theorem finiteSelectiveTwoActualReflectedCollapseOperation_forward_image :
    finiteGeneratedDomainOperationEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        (finiteGeneratedReflectedArchitectureObject.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoCollapseSourceObject)
        (finiteGeneratedReflectedArchitectureObject.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoCollapseTargetObject)
        finiteSelectiveTwoActualReflectedCollapseOperation.{u} =
      castOperation
        finiteSelectiveTwoObjectContextWitnessInput.highGeneratedLift.domain.reading.operationReading
        (finiteGeneratedReflectedArchitectureObject_high_image.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoCollapseSourceObject).symm
        (finiteGeneratedReflectedArchitectureObject_high_image.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoCollapseTargetObject).symm
        (finiteSelectiveTwoObjectContextActualHighFactor.{u}.upper.operationMap
          (finiteGeneratedDomainOperationEquiv.{u}
            finiteSelectiveTwoUpperComputationalOuterInput
            finiteSelectiveTwoCollapseSourceObject
            finiteSelectiveTwoCollapseTargetObject
            finiteSelectiveTwoOuterCollapseOperation)) := by
  exact finiteGeneratedReflectedOperationMap_forward_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoOuterCollapseOperation

/--
Every high operation at the concrete source endpoints fires the inverse-source
image theorem; the source need not be supplied as a low image certificate.
-/
theorem finiteSelectiveTwoActualReflectedCollapseOperation_inverse_image
    (operation :
      finiteSelectiveTwoUpperComputationalOuterInput.highGeneratedLift.domain.reading.operationReading.Op
        (finiteModelLiftArchitectureObject.{u}
          finiteSelectiveTwoCollapseSourceObject)
        (finiteModelLiftArchitectureObject.{u}
          finiteSelectiveTwoCollapseTargetObject)) :
    finiteGeneratedDomainOperationEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        (finiteGeneratedReflectedArchitectureObject.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoCollapseSourceObject)
        (finiteGeneratedReflectedArchitectureObject.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoCollapseTargetObject)
        (finiteGeneratedReflectedOperationMap.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          ((finiteGeneratedDomainOperationEquiv.{u}
            finiteSelectiveTwoUpperComputationalOuterInput
            finiteSelectiveTwoCollapseSourceObject
            finiteSelectiveTwoCollapseTargetObject).symm operation)) =
      castOperation
        finiteSelectiveTwoObjectContextWitnessInput.highGeneratedLift.domain.reading.operationReading
        (finiteGeneratedReflectedArchitectureObject_high_image.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoCollapseSourceObject).symm
        (finiteGeneratedReflectedArchitectureObject_high_image.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoCollapseTargetObject).symm
        (finiteSelectiveTwoObjectContextActualHighFactor.{u}.upper.operationMap
          operation) := by
  exact finiteGeneratedReflectedOperationMap_inverse_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase operation

/--
The concrete reflected Atom map is read pointwise from the actual normalized
high operation-map field.
-/
theorem finiteSelectiveTwoActualReflectedCollapseOperation_atom_graph :
    let e := (finiteGeneratedOuterInput
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessBase).hom.doctrineHom.atomEquiv
    (finiteSelectiveTwoObjectContextWitnessInput.lowGeneratedLift.domain.reading.operationReading.configurationMap
      (finiteGeneratedReflectedOperationMap.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoOuterCollapseOperation)).atomMap
        (e.symm FiniteModel.FiniteAtom.componentA) =
      finiteModelLiftCarrierEquiv.{u}.atom.symm
        ((finiteSelectiveTwoObjectContextWitnessInput.highGeneratedLift.domain.reading.operationReading.configurationMap
            ((finiteGeneratedNormalizedHighFactor.{u}
              finiteSelectiveTwoObjectContextWitnessInput
              finiteSelectiveTwoObjectContextWitnessLift.{u}
              finiteSelectiveTwoObjectContextWitnessBase).upper.operationMap
              (finiteGeneratedDomainOperationEquiv.{u}
                (finiteGeneratedOuterInput
                  finiteSelectiveTwoObjectContextWitnessInput
                  finiteSelectiveTwoObjectContextWitnessBase)
                finiteSelectiveTwoCollapseSourceObject
                finiteSelectiveTwoCollapseTargetObject
                finiteSelectiveTwoOuterCollapseOperation))).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom
            (e.symm FiniteModel.FiniteAtom.componentA))) := by
  exact finiteGeneratedReflectedOperationMap_atom_graph.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoOuterCollapseOperation
    ((finiteGeneratedOuterInput
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessBase).hom.doctrineHom.atomEquiv.symm
        FiniteModel.FiniteAtom.componentA)

/-! ## Invariant and signature singleton images -/

/-- The concrete invariant index in the outer generated singleton family. -/
def finiteSelectiveTwoUpperInvariantIndex :
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.invariantReading.Index := by
  change PUnit
  exact PUnit.unit

/-- The actual-derived reflected invariant index. -/
noncomputable def finiteSelectiveTwoActualReflectedInvariantIndex :=
  finiteGeneratedReflectedInvariantMap.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoUpperInvariantIndex

/-- The reflected invariant index has exactly the actual normalized high image. -/
theorem finiteSelectiveTwoActualReflectedInvariantIndex_high_image :
    finiteGeneratedInvariantIndexEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoActualReflectedInvariantIndex.{u} =
      finiteSelectiveTwoObjectContextActualHighFactor.{u}.upper.invariantMap
        (finiteGeneratedInvariantIndexEquiv.{u}
          finiteSelectiveTwoUpperComputationalOuterInput
          finiteSelectiveTwoUpperInvariantIndex) := by
  exact finiteGeneratedReflectedInvariantMap_high_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoUpperInvariantIndex

/-- Every high source invariant index fires the actual inverse-source image graph. -/
theorem finiteSelectiveTwoActualReflectedInvariantIndex_inverse_source_high_image
    (highIndex :
      finiteSelectiveTwoUpperComputationalOuterInput.highGeneratedLift.domain.reading.invariantReading.Index) :
    finiteGeneratedInvariantIndexEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        (finiteGeneratedReflectedInvariantMap.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          ((finiteGeneratedInvariantIndexEquiv.{u}
            finiteSelectiveTwoUpperComputationalOuterInput).symm highIndex)) =
      finiteSelectiveTwoObjectContextActualHighFactor.{u}.upper.invariantMap
        highIndex := by
  exact finiteGeneratedReflectedInvariantMap_inverse_source_high_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase highIndex

/-- The concrete signature axis in the outer generated singleton family. -/
def finiteSelectiveTwoUpperSignatureAxis :
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.signatureReading.Axis := by
  change PUnit
  exact PUnit.unit

/-- The actual-derived reflected signature axis. -/
noncomputable def finiteSelectiveTwoActualReflectedSignatureAxis :=
  finiteGeneratedReflectedAxisMap.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoUpperSignatureAxis

/-- The reflected signature axis has exactly the actual normalized high image. -/
theorem finiteSelectiveTwoActualReflectedSignatureAxis_high_image :
    finiteGeneratedSignatureAxisEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoActualReflectedSignatureAxis.{u} =
      finiteSelectiveTwoObjectContextActualHighFactor.{u}.upper.axisMap
        (finiteGeneratedSignatureAxisEquiv.{u}
          finiteSelectiveTwoUpperComputationalOuterInput
          finiteSelectiveTwoUpperSignatureAxis) := by
  exact finiteGeneratedReflectedAxisMap_high_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoUpperSignatureAxis

/-- Every high source axis fires the actual inverse-source image graph. -/
theorem finiteSelectiveTwoActualReflectedSignatureAxis_inverse_source_high_image
    (highAxis :
      finiteSelectiveTwoUpperComputationalOuterInput.highGeneratedLift.domain.reading.signatureReading.Axis) :
    finiteGeneratedSignatureAxisEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        (finiteGeneratedReflectedAxisMap.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          ((finiteGeneratedSignatureAxisEquiv.{u}
            finiteSelectiveTwoUpperComputationalOuterInput).symm highAxis)) =
      finiteSelectiveTwoObjectContextActualHighFactor.{u}.upper.axisMap
        highAxis := by
  exact finiteGeneratedReflectedAxisMap_inverse_source_high_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase highAxis

/-! ## The concrete coordinate value three -/

/-- The value `3` in the outer generated coordinate carrier. -/
def finiteSelectiveTwoUpperSignatureCoordinateThree :
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.signatureReading.Coordinate
      finiteSelectiveTwoUpperSignatureAxis := by
  change Nat
  exact 3

/-- The zero value in the same dependent outer generated coordinate carrier. -/
def finiteSelectiveTwoUpperSignatureCoordinateZero :
    finiteSelectiveTwoUpperComputationalOuterInput.lowGeneratedLift.domain.reading.signatureReading.Coordinate
      finiteSelectiveTwoUpperSignatureAxis := by
  change Nat
  exact 0

/-- The source coordinate value is genuinely nonzero. -/
theorem finiteSelectiveTwoUpperSignatureCoordinateThree_ne_zero :
    finiteSelectiveTwoUpperSignatureCoordinateThree ≠
      finiteSelectiveTwoUpperSignatureCoordinateZero := by
  change (3 : Nat) ≠ 0
  decide

/-- The actual-derived reflected target coordinate of the concrete value `3`. -/
noncomputable def finiteSelectiveTwoActualReflectedSignatureCoordinateThree :=
  finiteGeneratedReflectedCoordinateEquiv.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoUpperSignatureAxis
    finiteSelectiveTwoUpperSignatureCoordinateThree

/-- The reflected coordinate has the landed forward image of the actual high field. -/
theorem finiteSelectiveTwoActualReflectedSignatureCoordinateThree_forward_high_image :
    finiteGeneratedSignatureCoordinateEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoActualReflectedSignatureAxis.{u}
        finiteSelectiveTwoActualReflectedSignatureCoordinateThree.{u} =
      finiteGeneratedReflectedCoordinateLandingEquiv.{u}
        finiteSelectiveTwoObjectContextWitnessInput
        finiteSelectiveTwoObjectContextWitnessLift.{u}
        finiteSelectiveTwoObjectContextWitnessBase
        finiteSelectiveTwoUpperSignatureAxis
        (finiteSelectiveTwoObjectContextActualHighFactor.{u}.upper.coordinateEquiv
          (finiteGeneratedSignatureAxisEquiv.{u}
            finiteSelectiveTwoUpperComputationalOuterInput
            finiteSelectiveTwoUpperSignatureAxis)
          (finiteGeneratedSignatureCoordinateEquiv.{u}
            finiteSelectiveTwoUpperComputationalOuterInput
            finiteSelectiveTwoUpperSignatureAxis
            finiteSelectiveTwoUpperSignatureCoordinateThree)) := by
  exact finiteGeneratedReflectedCoordinateEquiv_apply_high_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoUpperSignatureAxis
    finiteSelectiveTwoUpperSignatureCoordinateThree

/--
The inverse high image of reflected `3` is computed by the inverse actual high
coordinate equivalence after undoing the generated landing cast.
-/
theorem finiteSelectiveTwoActualReflectedSignatureCoordinateThree_inverse_high_image :
    finiteGeneratedSignatureCoordinateEquiv.{u}
        finiteSelectiveTwoUpperComputationalOuterInput
        finiteSelectiveTwoUpperSignatureAxis
        ((finiteGeneratedReflectedCoordinateEquiv.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoUpperSignatureAxis).symm
            finiteSelectiveTwoActualReflectedSignatureCoordinateThree.{u}) =
      (finiteSelectiveTwoObjectContextActualHighFactor.{u}.upper.coordinateEquiv
        (finiteGeneratedSignatureAxisEquiv.{u}
          finiteSelectiveTwoUpperComputationalOuterInput
          finiteSelectiveTwoUpperSignatureAxis)).symm
        ((finiteGeneratedReflectedCoordinateLandingEquiv.{u}
          finiteSelectiveTwoObjectContextWitnessInput
          finiteSelectiveTwoObjectContextWitnessLift.{u}
          finiteSelectiveTwoObjectContextWitnessBase
          finiteSelectiveTwoUpperSignatureAxis).symm
          (finiteGeneratedSignatureCoordinateEquiv.{u}
            finiteSelectiveTwoObjectContextWitnessInput
            finiteSelectiveTwoActualReflectedSignatureAxis.{u}
            finiteSelectiveTwoActualReflectedSignatureCoordinateThree.{u})) := by
  exact finiteGeneratedReflectedCoordinateEquiv_symm_apply_high_image.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoUpperSignatureAxis
    finiteSelectiveTwoActualReflectedSignatureCoordinateThree.{u}

/-- Reflected `3` returns to the concrete source coordinate value `3`. -/
@[simp]
theorem finiteSelectiveTwoActualReflectedSignatureCoordinateThree_roundtrip :
    (finiteGeneratedReflectedCoordinateEquiv.{u}
      finiteSelectiveTwoObjectContextWitnessInput
      finiteSelectiveTwoObjectContextWitnessLift.{u}
      finiteSelectiveTwoObjectContextWitnessBase
      finiteSelectiveTwoUpperSignatureAxis).symm
        finiteSelectiveTwoActualReflectedSignatureCoordinateThree.{u} =
      finiteSelectiveTwoUpperSignatureCoordinateThree := by
  exact finiteGeneratedReflectedCoordinateEquiv_symm_apply_apply.{u}
    finiteSelectiveTwoObjectContextWitnessInput
    finiteSelectiveTwoObjectContextWitnessLift.{u}
    finiteSelectiveTwoObjectContextWitnessBase
    finiteSelectiveTwoUpperSignatureAxis
    finiteSelectiveTwoUpperSignatureCoordinateThree

/-! ## Sensitivity of the proof-used primitives -/

private def upperComputationalBoolSwap : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := by
    intro value
    cases value <;> rfl
  right_inv := by
    intro value
    cases value <;> rfl

/--
The proof-used map conjugation changes when its actual middle map changes from
identity to Boolean negation.  This supplements, but does not alter, the
selected singleton invariant and axis witnesses.
-/
theorem primitiveGeneratedIndexMapConjugation_middle_sensitive :
    generatedIndexMapConjugation
        (Equiv.refl Bool) id (Equiv.refl Bool) false ≠
      generatedIndexMapConjugation
        (Equiv.refl Bool) Bool.not (Equiv.refl Bool) false := by
  intro equality
  change false = true at equality
  cases equality

/--
The exact dependent-equivalence conjugation used by the coordinate producer is
sensitive to its actual middle equivalence on a nontrivial finite carrier.
-/
theorem primitiveGeneratedDependentEquivConjugation_middle_sensitive :
    generatedDependentEquivConjugation
        (Equiv.refl Bool) (Equiv.refl Bool)
        (Equiv.refl Bool) (Equiv.refl Bool) false ≠
      generatedDependentEquivConjugation
        (Equiv.refl Bool) upperComputationalBoolSwap
        (Equiv.refl Bool) (Equiv.refl Bool) false := by
  intro equality
  change false = true at equality
  cases equality

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
