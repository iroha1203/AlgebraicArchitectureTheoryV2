import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObjectImageDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationIndexDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObservableEquivalenceDescent

/-!
# Generated equation-coordinate and residual descent

This module proves the canonical generated-domain image laws for equation
violation coordinates and residuals.  It then combines those laws with the
actual normalized high equation transport.  Context endpoints use the
generated landing equality, while residual objects use the complete reflected
architecture-object image equality.

No image certificate, low equation transport, or preselected low factor is an
input to these constructions.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## The selected finite-model target generators -/

/-- Canonical target lifting carries every finite violation coordinate to its lifted value. -/
theorem finiteModelTargetEquationViolationCoordinate_image
    (W : Site.ContextCategoryObject
      FiniteModel.corePackage.algebra.contextPreorder)
    (V : Site.ContextCategoryObject
      finiteModelLiftCorePackage.{u}.algebra.contextPreorder)
    (index : FiniteModel.corePackage.algebra.equationSystem.Index)
    (atom : FiniteModel.carrier.Atom) :
    finiteModelTargetEquationObservableEquiv.{u} W V
        (FiniteModel.corePackage.algebra.equationSystem.violationCoordinate
          W index atom) =
      finiteModelLiftCorePackage.{u}.algebra.equationSystem.violationCoordinate
        V (finiteModelTargetEquationIndexEquiv.{u} index)
        (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
  cases index
  rfl

/-- Canonical target lifting carries every finite residual to the residual of the lifted object. -/
theorem finiteModelTargetEquationResidual_image
    (W : Site.ContextCategoryObject
      FiniteModel.corePackage.algebra.contextPreorder)
    (V : Site.ContextCategoryObject
      finiteModelLiftCorePackage.{u}.algebra.contextPreorder)
    (object : ArchitectureObject FiniteModel.carrier)
    (index : FiniteModel.corePackage.algebra.equationSystem.Index)
    (atom : FiniteModel.carrier.Atom) :
    finiteModelTargetEquationObservableEquiv.{u} W V
        (FiniteModel.corePackage.algebra.equationSystem.equationResidual
          W object index atom) =
      finiteModelLiftCorePackage.{u}.algebra.equationSystem.equationResidual
        V (finiteModelLiftArchitectureObject.{u} object)
        (finiteModelTargetEquationIndexEquiv.{u} index)
        (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
  cases index
  change ULift.up (FiniteModel.noCycleResidual object) =
    ULift.up (FiniteModel.noCycleResidual
      (finiteModelSemanticDescent.{u}
        (finiteModelLiftArchitectureObject.{u} object)))
  apply congrArg ULift.up
  unfold FiniteModel.noCycleResidual
  have hcycle :
      FiniteModel.hasDependencyCycle
          (finiteModelSemanticDescent.{u}
            (finiteModelLiftArchitectureObject.{u} object)) ↔
        FiniteModel.hasDependencyCycle object := by
    change FiniteModel.hasDependencyCycle
        (FiniteModel.objectOfConfiguration object.configuration) ↔
      FiniteModel.hasDependencyCycle object
    rfl
  rw [hcycle]

/-! ## Canonical generated-domain image laws -/

/--
The generated-domain observable lift carries every low violation coordinate
to the corresponding high generated-domain coordinate.
-/
theorem finiteGeneratedEquationViolationCoordinate_image
    (input : FiniteGeneratedLiftInput)
    (W : Site.ContextCategoryObject
      input.lowGeneratedLift.domain.algebra.contextPreorder)
    (index : input.lowGeneratedLift.domain.algebra.equationSystem.Index)
    (atom : FiniteModel.carrier.Atom) :
    finiteGeneratedEquationObservableEquiv.{u} input W
        (input.lowGeneratedLift.domain.algebra.equationSystem.violationCoordinate
          W index atom) =
      input.highGeneratedLift.domain.algebra.equationSystem.violationCoordinate
        ((finiteGeneratedContextImageFunctor.{u} input).obj W)
        (finiteGeneratedDomainEquationIndexEquiv.{u} input index)
        (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
  let lowUpper := inverseCorePackageForwardUpper FiniteModel.corePackage input.hom
  let lowTransport := lowUpper.equationTransport
  let highUpper := input.highPackageHomFromLowData.upper
  let highTransport := highUpper.equationTransport
  let highContext := (finiteGeneratedContextImageFunctor.{u} input).obj W
  let targetEquiv := finiteModelTargetEquationObservableEquiv.{u}
    (lowTransport.contextForward W)
    (highTransport.contextForward highContext)
  have hEquation :
      highTransport.equationEquiv
          (input.generatedDomainEquationIndexLift index) =
        finiteModelTargetEquationIndexEquiv.{u}
          (lowTransport.equationEquiv index) := by
    change input.highPackageHomFromLowData.upper.equationMap
        (input.generatedDomainEquationIndexLift index) =
      FiniteGeneratedLiftInput.targetEquationIndexLift.{u}
        (lowUpper.equationMap index)
    exact input.generatedUpper_equationMap_graph index
  have hAtom :
      highUpper.atomEquiv (finiteModelLiftCarrierEquiv.{u}.atom atom) =
        finiteModelLiftCarrierEquiv.{u}.atom
          (lowUpper.atomEquiv atom) := by
    change input.highPackageHomFromLowData.upper.atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      finiteModelLiftCarrierEquiv.{u}.atom
        (input.hom.doctrineHom.atomEquiv atom)
    exact input.highPackageHomFromLowData_upper_atom_graph atom
  have hLow := lowTransport.violationCoordinate_eq W index atom
  have hLowTarget := congrArg targetEquiv hLow
  have hHigh := highTransport.violationCoordinate_eq highContext
    (input.generatedDomainEquationIndexLift index)
    (finiteModelLiftCarrierEquiv.{u}.atom atom)
  apply (highTransport.observableEquiv highContext).injective
  change highTransport.observableEquiv highContext
      ((highTransport.observableEquiv highContext).symm _) =
    highTransport.observableEquiv highContext _
  rw [RingEquiv.apply_symm_apply]
  calc
    _ = targetEquiv
        (FiniteModel.corePackage.algebra.equationSystem.violationCoordinate
          (lowTransport.contextForward W)
          (lowTransport.equationEquiv index)
          (lowUpper.atomEquiv atom)) := hLowTarget
    _ = finiteModelLiftCorePackage.{u}.algebra.equationSystem.violationCoordinate
        (highTransport.contextForward highContext)
        (finiteModelTargetEquationIndexEquiv.{u}
          (lowTransport.equationEquiv index))
        (finiteModelLiftCarrierEquiv.{u}.atom
          (lowUpper.atomEquiv atom)) :=
      finiteModelTargetEquationViolationCoordinate_image _ _ _ _
    _ = finiteModelLiftCorePackage.{u}.algebra.equationSystem.violationCoordinate
        (highTransport.contextForward highContext)
        (highTransport.equationEquiv
          (input.generatedDomainEquationIndexLift index))
        (highUpper.atomEquiv
          (finiteModelLiftCarrierEquiv.{u}.atom atom)) := by
      rw [hEquation.symm, hAtom.symm]
    _ = highTransport.observableEquiv highContext
        (input.highGeneratedLift.domain.algebra.equationSystem.violationCoordinate
          highContext
          (input.generatedDomainEquationIndexLift index)
          (finiteModelLiftCarrierEquiv.{u}.atom atom)) := hHigh.symm

/--
The generated-domain observable lift carries every low residual to the high
residual of the complete canonically lifted architecture object.
-/
theorem finiteGeneratedEquationResidual_image
    (input : FiniteGeneratedLiftInput)
    (W : Site.ContextCategoryObject
      input.lowGeneratedLift.domain.algebra.contextPreorder)
    (object : ArchitectureObject FiniteModel.carrier)
    (index : input.lowGeneratedLift.domain.algebra.equationSystem.Index)
    (atom : FiniteModel.carrier.Atom) :
    finiteGeneratedEquationObservableEquiv.{u} input W
        (input.lowGeneratedLift.domain.algebra.equationSystem.equationResidual
          W object index atom) =
      input.highGeneratedLift.domain.algebra.equationSystem.equationResidual
        ((finiteGeneratedContextImageFunctor.{u} input).obj W)
        (finiteModelLiftArchitectureObject.{u} object)
        (finiteGeneratedDomainEquationIndexEquiv.{u} input index)
        (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
  let lowUpper := inverseCorePackageForwardUpper FiniteModel.corePackage input.hom
  let lowTransport := lowUpper.equationTransport
  let highUpper := input.highPackageHomFromLowData.upper
  let highTransport := highUpper.equationTransport
  let highContext := (finiteGeneratedContextImageFunctor.{u} input).obj W
  let targetEquiv := finiteModelTargetEquationObservableEquiv.{u}
    (lowTransport.contextForward W)
    (highTransport.contextForward highContext)
  have hEquation :
      highTransport.equationEquiv
          (input.generatedDomainEquationIndexLift index) =
        finiteModelTargetEquationIndexEquiv.{u}
          (lowTransport.equationEquiv index) := by
    change input.highPackageHomFromLowData.upper.equationMap
        (input.generatedDomainEquationIndexLift index) =
      FiniteGeneratedLiftInput.targetEquationIndexLift.{u}
        (lowUpper.equationMap index)
    exact input.generatedUpper_equationMap_graph index
  have hAtom :
      highUpper.atomEquiv (finiteModelLiftCarrierEquiv.{u}.atom atom) =
        finiteModelLiftCarrierEquiv.{u}.atom
          (lowUpper.atomEquiv atom) := by
    change input.highPackageHomFromLowData.upper.atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      finiteModelLiftCarrierEquiv.{u}.atom
        (input.hom.doctrineHom.atomEquiv atom)
    exact input.highPackageHomFromLowData_upper_atom_graph atom
  have hObject :
      highUpper.objectMap (finiteModelLiftArchitectureObject.{u} object) =
        finiteModelLiftArchitectureObject.{u}
          (lowUpper.objectMap object) := by
    change input.highPackageHomFromLowData.upper.objectMap
        (finiteModelLiftArchitectureObject.{u} object) =
      finiteModelLiftArchitectureObject.{u}
        (input.lowGeneratedLift.hom.upper.objectMap object)
    exact input.highPackageHomFromLowData_upper_objectMap_lift object
  have hLow := lowTransport.equationResidual_eq W object index atom
  have hLowTarget := congrArg targetEquiv hLow
  have hHigh := highTransport.equationResidual_eq highContext
    (finiteModelLiftArchitectureObject.{u} object)
    (input.generatedDomainEquationIndexLift index)
    (finiteModelLiftCarrierEquiv.{u}.atom atom)
  apply (highTransport.observableEquiv highContext).injective
  change highTransport.observableEquiv highContext
      ((highTransport.observableEquiv highContext).symm _) =
    highTransport.observableEquiv highContext _
  rw [RingEquiv.apply_symm_apply]
  calc
    _ = targetEquiv
        (FiniteModel.corePackage.algebra.equationSystem.equationResidual
          (lowTransport.contextForward W) (lowUpper.objectMap object)
          (lowTransport.equationEquiv index)
          (lowUpper.atomEquiv atom)) := hLowTarget
    _ = finiteModelLiftCorePackage.{u}.algebra.equationSystem.equationResidual
        (highTransport.contextForward highContext)
        (finiteModelLiftArchitectureObject.{u}
          (lowUpper.objectMap object))
        (finiteModelTargetEquationIndexEquiv.{u}
          (lowTransport.equationEquiv index))
        (finiteModelLiftCarrierEquiv.{u}.atom
          (lowUpper.atomEquiv atom)) :=
      finiteModelTargetEquationResidual_image _ _ _ _ _
    _ = finiteModelLiftCorePackage.{u}.algebra.equationSystem.equationResidual
        (highTransport.contextForward highContext)
        (highUpper.objectMap
          (finiteModelLiftArchitectureObject.{u} object))
        (highTransport.equationEquiv
          (input.generatedDomainEquationIndexLift index))
        (highUpper.atomEquiv
          (finiteModelLiftCarrierEquiv.{u}.atom atom)) := by
      rw [hEquation.symm, hAtom.symm, hObject.symm]
    _ = highTransport.observableEquiv highContext
        (input.highGeneratedLift.domain.algebra.equationSystem.equationResidual
          highContext (finiteModelLiftArchitectureObject.{u} object)
          (input.generatedDomainEquationIndexLift index)
          (finiteModelLiftCarrierEquiv.{u}.atom atom)) := hHigh.symm

/-! ## Endpoint casts for actual high generators -/

private theorem equationObservableCast_violation
    {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : Site.ContextPreorderCategory A}
    (E : ArchitecturalEquationSystem C)
    {W W' : Site.ContextCategoryObject C} (hW : W' = W)
    (index : E.Index) (atom : U.Atom) :
    RingEquiv.cast
        (R := fun X : Site.ContextCategoryObject C => E.Observable X)
        hW.symm (E.violationCoordinate W index atom) =
      E.violationCoordinate W' index atom := by
  cases hW
  rfl

private theorem equationObservableCast_residual
    {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : Site.ContextPreorderCategory A}
    (E : ArchitecturalEquationSystem C)
    {W W' : Site.ContextCategoryObject C} (hW : W' = W)
    {object object' : ArchitectureObject U} (hobject : object' = object)
    (index : E.Index) (atom : U.Atom) :
    RingEquiv.cast
        (R := fun X : Site.ContextCategoryObject C => E.Observable X)
        hW.symm (E.equationResidual W object index atom) =
      E.equationResidual W' object' index atom := by
  cases hW
  cases hobject
  rfl

/-- The generated target-context cast carries actual high violation coordinates exactly. -/
theorem finiteGeneratedReflectedEquationObservableTargetCast_violation
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder))
    (index : input.highGeneratedLift.domain.algebra.equationSystem.Index)
    (atom : finiteModelLiftCarrier.{u}.Atom) :
    finiteGeneratedReflectedEquationObservableTargetCast input lift base W
        (input.highGeneratedLift.domain.algebra.equationSystem.violationCoordinate
          ((finiteGeneratedActualHighContextEquivalence input lift base).functor.obj
            ((finiteGeneratedContextImageFunctor.{u}
              (finiteGeneratedOuterInput input base)).obj W))
          index atom) =
      input.highGeneratedLift.domain.algebra.equationSystem.violationCoordinate
        ((finiteGeneratedContextImageFunctor.{u} input).obj
          (finiteGeneratedReflectedForwardObject input lift base W))
        index atom :=
  equationObservableCast_violation _
    (finiteGeneratedReflectedForwardObject_image_eq input lift base W)
    index atom

/--
The generated target-context cast and the complete reflected object image
carry actual high residuals exactly.
-/
theorem finiteGeneratedReflectedEquationObservableTargetCast_residual
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder))
    (object : ArchitectureObject FiniteModel.carrier)
    (index : input.highGeneratedLift.domain.algebra.equationSystem.Index)
    (atom : finiteModelLiftCarrier.{u}.Atom) :
    finiteGeneratedReflectedEquationObservableTargetCast input lift base W
        (input.highGeneratedLift.domain.algebra.equationSystem.equationResidual
          ((finiteGeneratedActualHighContextEquivalence input lift base).functor.obj
            ((finiteGeneratedContextImageFunctor.{u}
              (finiteGeneratedOuterInput input base)).obj W))
          ((finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
            (finiteModelLiftArchitectureObject.{u} object))
          index atom) =
      input.highGeneratedLift.domain.algebra.equationSystem.equationResidual
        ((finiteGeneratedContextImageFunctor.{u} input).obj
          (finiteGeneratedReflectedForwardObject input lift base W))
        (finiteModelLiftArchitectureObject.{u}
          (finiteGeneratedReflectedArchitectureObject input lift base object))
        index atom :=
  equationObservableCast_residual _
    (finiteGeneratedReflectedForwardObject_image_eq input lift base W)
    (finiteGeneratedReflectedArchitectureObject_high_image
      input lift base object)
    index atom

/-! ## Actual-high-derived low generator laws -/

/--
The reflected observable, context, index, and Atom maps preserve every
violation coordinate.  The proof consumes the actual normalized high
`violationCoordinate_eq` field.
-/
theorem finiteGeneratedReflectedViolationCoordinate_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder))
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index)
    (atom : FiniteModel.carrier.Atom) :
    finiteGeneratedReflectedEquationObservableEquiv input lift base W
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.violationCoordinate
          W index atom) =
      input.lowGeneratedLift.domain.algebra.equationSystem.violationCoordinate
        (finiteGeneratedReflectedForwardObject input lift base W)
        (finiteGeneratedReflectedEquationIndexEquiv input lift base index)
        (finiteGeneratedReflectedUpperAtomEquiv input lift base atom) := by
  let outer := finiteGeneratedOuterInput input base
  let sourceImage := finiteGeneratedContextImageFunctor.{u} outer
  let sourceContext := sourceImage.obj W
  let actualTransport :=
    (finiteGeneratedNormalizedHighFactor input lift base).upper.equationTransport
  let targetCast := finiteGeneratedReflectedEquationObservableTargetCast
    input lift base W
  let targetLift := finiteGeneratedEquationObservableEquiv.{u} input
    (finiteGeneratedReflectedForwardObject input lift base W)
  have hActual := actualTransport.violationCoordinate_eq sourceContext
    (finiteGeneratedDomainEquationIndexEquiv.{u} outer index)
    (finiteModelLiftCarrierEquiv.{u}.atom atom)
  have hActualCast := congrArg targetCast hActual
  have hIndex :
      actualTransport.equationEquiv
          (finiteGeneratedDomainEquationIndexEquiv.{u} outer index) =
        finiteGeneratedDomainEquationIndexEquiv.{u} input
          (finiteGeneratedReflectedEquationIndexEquiv
            input lift base index) := by
    change finiteGeneratedActualHighEquationIndexEquiv input lift base
        (finiteGeneratedDomainEquationIndexEquiv.{u} outer index) = _
    exact (finiteGeneratedReflectedEquationIndex_forward_image
      input lift base index).symm
  have hAtom :
      (finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv
          (finiteModelLiftCarrierEquiv.{u}.atom atom) =
        finiteModelLiftCarrierEquiv.{u}.atom
          (finiteGeneratedReflectedUpperAtomEquiv input lift base atom) :=
    (finiteGeneratedReflectedUpperAtomEquiv_high_graph
      input lift base atom).symm
  apply targetLift.injective
  rw [finiteGeneratedReflectedEquationObservableEquiv_apply_high_image]
  rw [finiteGeneratedEquationViolationCoordinate_image]
  change targetCast
      (actualTransport.observableEquiv sourceContext
        (outer.highGeneratedLift.domain.algebra.equationSystem.violationCoordinate
          sourceContext
          (finiteGeneratedDomainEquationIndexEquiv.{u} outer index)
          (finiteModelLiftCarrierEquiv.{u}.atom atom))) = _
  rw [hActualCast]
  rw [hIndex]
  rw [hAtom]
  calc
    _ = input.highGeneratedLift.domain.algebra.equationSystem.violationCoordinate
        ((finiteGeneratedContextImageFunctor.{u} input).obj
          (finiteGeneratedReflectedForwardObject input lift base W))
        (finiteGeneratedDomainEquationIndexEquiv.{u} input
          (finiteGeneratedReflectedEquationIndexEquiv
            input lift base index))
        (finiteModelLiftCarrierEquiv.{u}.atom
          (finiteGeneratedReflectedUpperAtomEquiv
            input lift base atom)) :=
      finiteGeneratedReflectedEquationObservableTargetCast_violation
        input lift base W
        (finiteGeneratedDomainEquationIndexEquiv.{u} input
          (finiteGeneratedReflectedEquationIndexEquiv
            input lift base index))
        (finiteModelLiftCarrierEquiv.{u}.atom
          (finiteGeneratedReflectedUpperAtomEquiv
            input lift base atom))
    _ = targetLift
        (input.lowGeneratedLift.domain.algebra.equationSystem.violationCoordinate
          (finiteGeneratedReflectedForwardObject input lift base W)
          (finiteGeneratedReflectedEquationIndexEquiv
            input lift base index)
          (finiteGeneratedReflectedUpperAtomEquiv
            input lift base atom)) :=
      (finiteGeneratedEquationViolationCoordinate_image input
        (finiteGeneratedReflectedForwardObject input lift base W)
        (finiteGeneratedReflectedEquationIndexEquiv input lift base index)
        (finiteGeneratedReflectedUpperAtomEquiv input lift base atom)).symm

/--
The reflected observable, context, complete object, index, and Atom maps
preserve every equation residual.  The proof consumes the actual normalized
high `equationResidual_eq` field and the complete Cycle 19 object image.
-/
theorem finiteGeneratedReflectedEquationResidual_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder))
    (object : ArchitectureObject FiniteModel.carrier)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index)
    (atom : FiniteModel.carrier.Atom) :
    finiteGeneratedReflectedEquationObservableEquiv input lift base W
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.equationResidual
          W object index atom) =
      input.lowGeneratedLift.domain.algebra.equationSystem.equationResidual
        (finiteGeneratedReflectedForwardObject input lift base W)
        (finiteGeneratedReflectedArchitectureObject input lift base object)
        (finiteGeneratedReflectedEquationIndexEquiv input lift base index)
        (finiteGeneratedReflectedUpperAtomEquiv input lift base atom) := by
  let outer := finiteGeneratedOuterInput input base
  let sourceImage := finiteGeneratedContextImageFunctor.{u} outer
  let sourceContext := sourceImage.obj W
  let actualTransport :=
    (finiteGeneratedNormalizedHighFactor input lift base).upper.equationTransport
  let targetCast := finiteGeneratedReflectedEquationObservableTargetCast
    input lift base W
  let targetLift := finiteGeneratedEquationObservableEquiv.{u} input
    (finiteGeneratedReflectedForwardObject input lift base W)
  have hActual := actualTransport.equationResidual_eq sourceContext
    (finiteModelLiftArchitectureObject.{u} object)
    (finiteGeneratedDomainEquationIndexEquiv.{u} outer index)
    (finiteModelLiftCarrierEquiv.{u}.atom atom)
  have hActualCast := congrArg targetCast hActual
  have hIndex :
      actualTransport.equationEquiv
          (finiteGeneratedDomainEquationIndexEquiv.{u} outer index) =
        finiteGeneratedDomainEquationIndexEquiv.{u} input
          (finiteGeneratedReflectedEquationIndexEquiv
            input lift base index) := by
    change finiteGeneratedActualHighEquationIndexEquiv input lift base
        (finiteGeneratedDomainEquationIndexEquiv.{u} outer index) = _
    exact (finiteGeneratedReflectedEquationIndex_forward_image
      input lift base index).symm
  have hAtom :
      (finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv
          (finiteModelLiftCarrierEquiv.{u}.atom atom) =
        finiteModelLiftCarrierEquiv.{u}.atom
          (finiteGeneratedReflectedUpperAtomEquiv input lift base atom) :=
    (finiteGeneratedReflectedUpperAtomEquiv_high_graph
      input lift base atom).symm
  have hObject :
      (finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
          (finiteModelLiftArchitectureObject.{u} object) =
        finiteModelLiftArchitectureObject.{u}
          (finiteGeneratedReflectedArchitectureObject
            input lift base object) :=
    (finiteGeneratedReflectedArchitectureObject_high_image
      input lift base object).symm
  apply targetLift.injective
  rw [finiteGeneratedReflectedEquationObservableEquiv_apply_high_image]
  rw [finiteGeneratedEquationResidual_image]
  change targetCast
      (actualTransport.observableEquiv sourceContext
        (outer.highGeneratedLift.domain.algebra.equationSystem.equationResidual
          sourceContext (finiteModelLiftArchitectureObject.{u} object)
          (finiteGeneratedDomainEquationIndexEquiv.{u} outer index)
          (finiteModelLiftCarrierEquiv.{u}.atom atom))) = _
  rw [hActualCast]
  rw [hIndex]
  rw [hAtom]
  rw [hObject]
  calc
    _ = targetCast
        (input.highGeneratedLift.domain.algebra.equationSystem.equationResidual
          ((finiteGeneratedActualHighContextEquivalence
            input lift base).functor.obj sourceContext)
          ((finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
            (finiteModelLiftArchitectureObject.{u} object))
          (finiteGeneratedDomainEquationIndexEquiv.{u} input
            (finiteGeneratedReflectedEquationIndexEquiv
              input lift base index))
          (finiteModelLiftCarrierEquiv.{u}.atom
            (finiteGeneratedReflectedUpperAtomEquiv
              input lift base atom))) := by
      rw [hObject]
      rfl
    _ = input.highGeneratedLift.domain.algebra.equationSystem.equationResidual
        ((finiteGeneratedContextImageFunctor.{u} input).obj
          (finiteGeneratedReflectedForwardObject input lift base W))
        (finiteModelLiftArchitectureObject.{u}
          (finiteGeneratedReflectedArchitectureObject input lift base object))
        (finiteGeneratedDomainEquationIndexEquiv.{u} input
          (finiteGeneratedReflectedEquationIndexEquiv
            input lift base index))
        (finiteModelLiftCarrierEquiv.{u}.atom
          (finiteGeneratedReflectedUpperAtomEquiv
            input lift base atom)) :=
      finiteGeneratedReflectedEquationObservableTargetCast_residual
        input lift base W
        object
        (finiteGeneratedDomainEquationIndexEquiv.{u} input
          (finiteGeneratedReflectedEquationIndexEquiv
            input lift base index))
        (finiteModelLiftCarrierEquiv.{u}.atom
          (finiteGeneratedReflectedUpperAtomEquiv
            input lift base atom))
    _ = targetLift
        (input.lowGeneratedLift.domain.algebra.equationSystem.equationResidual
          (finiteGeneratedReflectedForwardObject input lift base W)
          (finiteGeneratedReflectedArchitectureObject input lift base object)
          (finiteGeneratedReflectedEquationIndexEquiv
            input lift base index)
          (finiteGeneratedReflectedUpperAtomEquiv
            input lift base atom)) :=
      (finiteGeneratedEquationResidual_image input
        (finiteGeneratedReflectedForwardObject input lift base W)
        (finiteGeneratedReflectedArchitectureObject input lift base object)
        (finiteGeneratedReflectedEquationIndexEquiv input lift base index)
        (finiteGeneratedReflectedUpperAtomEquiv input lift base atom)).symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
