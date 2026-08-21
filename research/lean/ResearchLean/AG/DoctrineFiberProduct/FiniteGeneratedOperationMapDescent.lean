import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObjectImageDescent

/-!
# Reflection of generated operation maps

This module constructs a genuine equivalence between operations in the low and
high inverse-generated finite-model domains.  Its two functions are the
canonical lift and reflection of the underlying configuration homomorphism;
the only endpoint casts come from the proved cross-carrier object-transport
graph.

The actual reflected operation map then conjugates the `operationMap` field
read directly from `finiteGeneratedNormalizedHighFactor` through those domain
equivalences.  Complete reflected-object landing is used only to align the two
dependent operation endpoints.  No known low upper or factor, canonical
whole-factor value, caller image certificate, or complete signed-reading hom
is supplied or asserted here.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Complete generated-domain operation images -/

/--
The lifted configuration of a transported low object is the configuration of
the correspondingly transported lifted object.
-/
private theorem finiteGeneratedOperationEndpoint_lift
    (input : FiniteGeneratedLiftInput)
    (object : ArchitectureObject FiniteModel.carrier) :
    (finiteModelLiftArchitectureObject.{u}
        (transportArchitectureObject input.hom.doctrineHom.atomEquiv
          object)).configuration =
      (transportArchitectureObject
        (finiteModelLiftExactDoctrineHom.{u} input.hom.doctrineHom).atomEquiv
        (finiteModelLiftArchitectureObject.{u} object)).configuration :=
  congrArg ArchitectureObject.configuration
    (finiteModelLiftArchitectureObject_transport.{u}
      input.hom.doctrineHom object).symm

/--
Lift an operation in a low inverse-generated domain to the corresponding high
inverse-generated domain.

The definition lifts the operation's actual configuration homomorphism and
casts only its two endpoints along the generated object-transport graph.
-/
noncomputable def finiteGeneratedDomainOperationLift
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.lowGeneratedLift.domain.reading.operationReading.Op
      source target) :
    input.highGeneratedLift.domain.reading.operationReading.Op
      (finiteModelLiftArchitectureObject.{u} source)
      (finiteModelLiftArchitectureObject.{u} target) := by
  change ConfigurationHom
    (transportArchitectureObject
      (finiteModelLiftExactDoctrineHom.{u} input.hom.doctrineHom).atomEquiv
      (finiteModelLiftArchitectureObject.{u} source)).configuration
    (transportArchitectureObject
      (finiteModelLiftExactDoctrineHom.{u} input.hom.doctrineHom).atomEquiv
      (finiteModelLiftArchitectureObject.{u} target)).configuration
  change ConfigurationHom
    (transportArchitectureObject input.hom.doctrineHom.atomEquiv
      source).configuration
    (transportArchitectureObject input.hom.doctrineHom.atomEquiv
      target).configuration at operation
  exact castConfigurationHom
    (finiteGeneratedOperationEndpoint_lift.{u} input source)
    (finiteGeneratedOperationEndpoint_lift.{u} input target)
    (finiteModelLiftConfigurationHom.{u} operation)

/--
Reflect an operation in a high inverse-generated domain to the corresponding
low inverse-generated domain.

The high endpoints are first returned to canonical lifted configurations;
configuration-hom reflection then removes the carrier lift.
-/
noncomputable def finiteGeneratedDomainOperationReflect
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.highGeneratedLift.domain.reading.operationReading.Op
      (finiteModelLiftArchitectureObject.{u} source)
      (finiteModelLiftArchitectureObject.{u} target)) :
    input.lowGeneratedLift.domain.reading.operationReading.Op source target := by
  change ConfigurationHom
    (transportArchitectureObject input.hom.doctrineHom.atomEquiv
      source).configuration
    (transportArchitectureObject input.hom.doctrineHom.atomEquiv
      target).configuration
  change ConfigurationHom
    (transportArchitectureObject
      (finiteModelLiftExactDoctrineHom.{u} input.hom.doctrineHom).atomEquiv
      (finiteModelLiftArchitectureObject.{u} source)).configuration
    (transportArchitectureObject
      (finiteModelLiftExactDoctrineHom.{u} input.hom.doctrineHom).atomEquiv
      (finiteModelLiftArchitectureObject.{u} target)).configuration at operation
  exact castConfigurationHom
    (finiteModelReflectAtomConfiguration_lift.{u}
      (transportArchitectureObject input.hom.doctrineHom.atomEquiv
        source).configuration)
    (finiteModelReflectAtomConfiguration_lift.{u}
      (transportArchitectureObject input.hom.doctrineHom.atomEquiv
        target).configuration)
    (finiteModelReflectConfigurationHom.{u}
      (castConfigurationHom
        (finiteGeneratedOperationEndpoint_lift.{u} input source).symm
        (finiteGeneratedOperationEndpoint_lift.{u} input target).symm
        operation))

/-- Reflecting a canonically lifted generated-domain operation recovers it. -/
@[simp]
theorem finiteGeneratedDomainOperation_reflect_lift
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.lowGeneratedLift.domain.reading.operationReading.Op
      source target) :
    finiteGeneratedDomainOperationReflect.{u} input
        (finiteGeneratedDomainOperationLift.{u} input operation) = operation := by
  apply ConfigurationHom.ext
  simp [finiteGeneratedDomainOperationReflect,
    finiteGeneratedDomainOperationLift, Function.comp_def]

/-- Lifting a reflected generated-domain operation recovers it. -/
@[simp]
theorem finiteGeneratedDomainOperation_lift_reflect
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.highGeneratedLift.domain.reading.operationReading.Op
      (finiteModelLiftArchitectureObject.{u} source)
      (finiteModelLiftArchitectureObject.{u} target)) :
    finiteGeneratedDomainOperationLift.{u} input
        (finiteGeneratedDomainOperationReflect.{u} input operation) = operation := by
  apply ConfigurationHom.ext
  simp [finiteGeneratedDomainOperationReflect,
    finiteGeneratedDomainOperationLift, Function.comp_def]

/--
All operations between two low generated-domain objects are canonically
equivalent to operations between their lifted high generated-domain images.
-/
noncomputable def finiteGeneratedDomainOperationEquiv
    (input : FiniteGeneratedLiftInput)
    (source target : ArchitectureObject FiniteModel.carrier) :
    input.lowGeneratedLift.domain.reading.operationReading.Op source target ≃
      input.highGeneratedLift.domain.reading.operationReading.Op
        (finiteModelLiftArchitectureObject.{u} source)
        (finiteModelLiftArchitectureObject.{u} target) where
  toFun := finiteGeneratedDomainOperationLift.{u} input
  invFun := finiteGeneratedDomainOperationReflect.{u} input
  left_inv := finiteGeneratedDomainOperation_reflect_lift.{u} input
  right_inv := finiteGeneratedDomainOperation_lift_reflect.{u} input

/-- The forward operation equivalence computes by configuration-hom lifting. -/
@[simp]
theorem finiteGeneratedDomainOperationEquiv_apply
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.lowGeneratedLift.domain.reading.operationReading.Op
      source target) :
    finiteGeneratedDomainOperationEquiv.{u} input source target operation =
      finiteGeneratedDomainOperationLift.{u} input operation :=
  rfl

/-- The inverse operation equivalence computes by configuration-hom reflection. -/
@[simp]
theorem finiteGeneratedDomainOperationEquiv_symm_apply
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.highGeneratedLift.domain.reading.operationReading.Op
      (finiteModelLiftArchitectureObject.{u} source)
      (finiteModelLiftArchitectureObject.{u} target)) :
    (finiteGeneratedDomainOperationEquiv.{u} input source target).symm operation =
      finiteGeneratedDomainOperationReflect.{u} input operation :=
  rfl

/-- The forward generated-domain operation image has the lifted Atom map. -/
@[simp]
theorem finiteGeneratedDomainOperationLift_atomMap
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.lowGeneratedLift.domain.reading.operationReading.Op
      source target) :
    (finiteGeneratedDomainOperationLift.{u} input operation).atomMap =
      finiteModelLiftCarrierEquiv.{u}.atom ∘ operation.atomMap ∘
        finiteModelLiftCarrierEquiv.{u}.atom.symm := by
  simp [finiteGeneratedDomainOperationLift]

/-- The inverse generated-domain operation image has the reflected Atom map. -/
@[simp]
theorem finiteGeneratedDomainOperationReflect_atomMap
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.highGeneratedLift.domain.reading.operationReading.Op
      (finiteModelLiftArchitectureObject.{u} source)
      (finiteModelLiftArchitectureObject.{u} target)) :
    (finiteGeneratedDomainOperationReflect.{u} input operation).atomMap =
      finiteModelLiftCarrierEquiv.{u}.atom.symm ∘ operation.atomMap ∘
        finiteModelLiftCarrierEquiv.{u}.atom := by
  simp [finiteGeneratedDomainOperationReflect]

/--
The configuration map read from a lifted generated-domain operation is the
canonical lift of the configuration map read at the low generated domain.
-/
theorem finiteGeneratedDomainOperation_configurationMap_graph
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.lowGeneratedLift.domain.reading.operationReading.Op
      source target) :
    input.highGeneratedLift.domain.reading.operationReading.configurationMap
        (finiteGeneratedDomainOperationEquiv.{u} input source target operation) =
      finiteModelLiftConfigurationHom.{u}
        (input.lowGeneratedLift.domain.reading.operationReading.configurationMap
          operation) := by
  apply ConfigurationHom.ext
  funext atom
  rcases atom with ⟨atom⟩
  simp [finiteGeneratedDomainOperationEquiv,
    finiteGeneratedDomainOperationLift, inverseCorePackage,
    inverseCoreReading, FiniteGeneratedLiftInput.lowGeneratedLift,
    FiniteGeneratedLiftInput.highGeneratedLift, strongCartesianLiftOfTarget,
    FiniteGeneratedLiftInput.lowInput, FiniteGeneratedLiftInput.highInput,
    FiniteGeneratedLiftInput.lowTarget, FiniteGeneratedLiftInput.highTarget,
    transportOperationReading, finiteModelLiftExactDoctrineHom,
    finiteModelLiftExtInstHom, finiteModelLiftExtractionInstance,
    Function.comp_def]
  change finiteModelLiftCarrierEquiv.{u}.atom.symm
      ((castConfigurationHom
        (finiteGeneratedOperationEndpoint_lift.{u} input source)
        (finiteGeneratedOperationEndpoint_lift.{u} input target)
        (finiteModelLiftConfigurationHom.{u} operation)).atomMap
        (finiteModelLiftCarrierEquiv.{u}.atom
          (input.hom.doctrineHom.atomEquiv
            (finiteModelLiftCarrierEquiv.{u}.atom.symm ⟨atom⟩)))) =
    operation.atomMap
      (input.hom.doctrineHom.atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom.symm ⟨atom⟩))
  rw [castConfigurationHom_atomMap, finiteModelLiftConfigurationHom_atomMap]
  exact finiteModelLiftCarrierEquiv.{u}.atom.symm_apply_apply _

/-- The configuration-map graph evaluates pointwise on every source Atom. -/
@[simp]
theorem finiteGeneratedDomainOperation_configurationMap_atom_graph
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.lowGeneratedLift.domain.reading.operationReading.Op
      source target)
    (atom : FiniteModel.carrier.Atom) :
    (input.highGeneratedLift.domain.reading.operationReading.configurationMap
      (finiteGeneratedDomainOperationEquiv.{u} input source target operation)).atomMap
        (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      finiteModelLiftCarrierEquiv.{u}.atom
        ((input.lowGeneratedLift.domain.reading.operationReading.configurationMap
          operation).atomMap atom) := by
  rw [finiteGeneratedDomainOperation_configurationMap_graph]
  rfl

/--
The inverse image recovers the complete configuration map by reflecting the
high configuration map and casting the two canonical reflected endpoints.
-/
theorem finiteGeneratedDomainOperation_inverse_configurationMap_graph
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.highGeneratedLift.domain.reading.operationReading.Op
      (finiteModelLiftArchitectureObject.{u} source)
      (finiteModelLiftArchitectureObject.{u} target)) :
    input.lowGeneratedLift.domain.reading.operationReading.configurationMap
        ((finiteGeneratedDomainOperationEquiv.{u}
          input source target).symm operation) =
      castConfigurationHom
        (finiteModelReflectAtomConfiguration_lift.{u} source.configuration)
        (finiteModelReflectAtomConfiguration_lift.{u} target.configuration)
        (finiteModelReflectConfigurationHom.{u}
          (input.highGeneratedLift.domain.reading.operationReading.configurationMap
            operation)) := by
  apply ConfigurationHom.ext
  have hforward := finiteGeneratedDomainOperation_configurationMap_graph.{u}
    input ((finiteGeneratedDomainOperationEquiv.{u}
      input source target).symm operation)
  rw [(finiteGeneratedDomainOperationEquiv.{u}
    input source target).apply_symm_apply] at hforward
  funext atom
  have hatom := congrFun (congrArg ConfigurationHom.atomMap hforward)
    (finiteModelLiftCarrierEquiv.{u}.atom atom)
  rw [castConfigurationHom_atomMap,
    finiteModelReflectConfigurationHom_atomMap]
  simpa [Function.comp_def] using
    congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm hatom.symm

/-- The inverse configuration-map graph evaluates on every high-image Atom. -/
@[simp]
theorem finiteGeneratedDomainOperation_inverse_configurationMap_atom_graph
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : input.highGeneratedLift.domain.reading.operationReading.Op
      (finiteModelLiftArchitectureObject.{u} source)
      (finiteModelLiftArchitectureObject.{u} target))
    (atom : FiniteModel.carrier.Atom) :
    (input.lowGeneratedLift.domain.reading.operationReading.configurationMap
      ((finiteGeneratedDomainOperationEquiv.{u}
        input source target).symm operation)).atomMap atom =
      finiteModelLiftCarrierEquiv.{u}.atom.symm
        ((input.highGeneratedLift.domain.reading.operationReading.configurationMap
          operation).atomMap (finiteModelLiftCarrierEquiv.{u}.atom atom)) := by
  rw [finiteGeneratedDomainOperation_inverse_configurationMap_graph,
    castConfigurationHom_atomMap,
    finiteModelReflectConfigurationHom_atomMap]
  rfl

/-! ## Reflection of the actual normalized high operation map -/

/--
Reflect the operation map of the actual normalized high factor between the two
generated low domains.

The definition visibly projects `upper.operationMap` from the supplied high
factor.  The source operation is raised through the outer generated-domain
equivalence, while complete reflected-object landing supplies exactly the two
dependent endpoint casts before the result is reflected through the target
generated-domain equivalence.
-/
noncomputable def finiteGeneratedReflectedOperationMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.Op
      source target) :
    input.lowGeneratedLift.domain.reading.operationReading.Op
      (finiteGeneratedReflectedArchitectureObject input lift base source)
      (finiteGeneratedReflectedArchitectureObject input lift base target) :=
  (finiteGeneratedDomainOperationEquiv.{u} input
      (finiteGeneratedReflectedArchitectureObject input lift base source)
      (finiteGeneratedReflectedArchitectureObject input lift base target)).symm
    (castOperation input.highGeneratedLift.domain.reading.operationReading
      (finiteGeneratedReflectedArchitectureObject_high_image
        input lift base source).symm
      (finiteGeneratedReflectedArchitectureObject_high_image
        input lift base target).symm
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
        (finiteGeneratedDomainOperationEquiv.{u}
          (finiteGeneratedOuterInput input base) source target operation)))

/--
After canonical high imaging, the reflected operation is exactly the actual
normalized high factor's operation-map value with its endpoints landed on the
complete reflected objects.
-/
theorem finiteGeneratedReflectedOperationMap_forward_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.Op
      source target) :
    finiteGeneratedDomainOperationEquiv.{u} input
        (finiteGeneratedReflectedArchitectureObject input lift base source)
        (finiteGeneratedReflectedArchitectureObject input lift base target)
        (finiteGeneratedReflectedOperationMap input lift base operation) =
      castOperation input.highGeneratedLift.domain.reading.operationReading
        (finiteGeneratedReflectedArchitectureObject_high_image
          input lift base source).symm
        (finiteGeneratedReflectedArchitectureObject_high_image
          input lift base target).symm
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
          (finiteGeneratedDomainOperationEquiv.{u}
            (finiteGeneratedOuterInput input base) source target operation)) := by
  exact (finiteGeneratedDomainOperationEquiv.{u} input
    (finiteGeneratedReflectedArchitectureObject input lift base source)
    (finiteGeneratedReflectedArchitectureObject input lift base target)).apply_symm_apply _

/--
The inverse source image also feeds every high generated-domain operation into
the actual high `operationMap`, with no restriction to a caller-supplied image.
-/
theorem finiteGeneratedReflectedOperationMap_inverse_image
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : (finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.operationReading.Op
      (finiteModelLiftArchitectureObject.{u} source)
      (finiteModelLiftArchitectureObject.{u} target)) :
    finiteGeneratedDomainOperationEquiv.{u} input
        (finiteGeneratedReflectedArchitectureObject input lift base source)
        (finiteGeneratedReflectedArchitectureObject input lift base target)
        (finiteGeneratedReflectedOperationMap input lift base
          ((finiteGeneratedDomainOperationEquiv.{u}
            (finiteGeneratedOuterInput input base) source target).symm operation)) =
      castOperation input.highGeneratedLift.domain.reading.operationReading
        (finiteGeneratedReflectedArchitectureObject_high_image
          input lift base source).symm
        (finiteGeneratedReflectedArchitectureObject_high_image
          input lift base target).symm
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
          operation) := by
  rw [finiteGeneratedReflectedOperationMap_forward_image]
  rw [(finiteGeneratedDomainOperationEquiv.{u}
    (finiteGeneratedOuterInput input base) source target).apply_symm_apply]

/--
The reflected map's configuration Atom map is the inverse carrier image of the
actual normalized high operation map, after evaluating the actual high field
on the canonical source operation image.
-/
@[simp]
theorem finiteGeneratedReflectedOperationMap_atom_graph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.Op
      source target)
    (atom : FiniteModel.carrier.Atom) :
    (input.lowGeneratedLift.domain.reading.operationReading.configurationMap
      (finiteGeneratedReflectedOperationMap input lift base operation)).atomMap atom =
      finiteModelLiftCarrierEquiv.{u}.atom.symm
        ((input.highGeneratedLift.domain.reading.operationReading.configurationMap
          ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
            (finiteGeneratedDomainOperationEquiv.{u}
              (finiteGeneratedOuterInput input base) source target operation))).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom)) := by
  have himage := finiteGeneratedReflectedOperationMap_forward_image.{u}
    input lift base operation
  have hatomImage := congrArg
    (fun mapped =>
      (input.highGeneratedLift.domain.reading.operationReading.configurationMap
        mapped).atomMap (finiteModelLiftCarrierEquiv.{u}.atom atom))
    himage
  change
    (input.highGeneratedLift.domain.reading.operationReading.configurationMap
      (finiteGeneratedDomainOperationEquiv.{u} input
        (finiteGeneratedReflectedArchitectureObject input lift base source)
        (finiteGeneratedReflectedArchitectureObject input lift base target)
        (finiteGeneratedReflectedOperationMap input lift base operation))).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      (input.highGeneratedLift.domain.reading.operationReading.configurationMap
        (castOperation input.highGeneratedLift.domain.reading.operationReading
          (finiteGeneratedReflectedArchitectureObject_high_image
            input lift base source).symm
          (finiteGeneratedReflectedArchitectureObject_high_image
            input lift base target).symm
          ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
            (finiteGeneratedDomainOperationEquiv.{u}
              (finiteGeneratedOuterInput input base) source target
              operation)))).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom) at hatomImage
  rw [castOperation_configurationMap_atomMap] at hatomImage
  have hdomain := finiteGeneratedDomainOperation_configurationMap_graph.{u}
    input (finiteGeneratedReflectedOperationMap input lift base operation)
  have hatomDomain := congrFun (congrArg ConfigurationHom.atomMap hdomain)
    (finiteModelLiftCarrierEquiv.{u}.atom atom)
  have hatom := hatomImage.symm.trans hatomDomain
  simpa [Function.comp_def] using
    (congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm hatom).symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
