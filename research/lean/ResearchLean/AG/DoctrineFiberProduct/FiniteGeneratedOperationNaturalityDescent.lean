import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedOperationMapDescent

/-!
# Generated operation naturality descent

This module proves the exact operation-naturality equation for the reflected
low operation map.  Both low composites are lifted through the canonical
finite configuration-hom lift.  Their high images are identified with the two
sides of the actual normalized high `upper.operation_naturality`, which is the
central equality of the proof.

No low factor upper, known low naturality, canonical-factor equality, caller
certificate, global instance, choice, or empty-type elimination is used.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Configuration-hom lift reflection -/

/--
Canonical finite configuration-hom lifting is injective for every pair of
finite configurations.
-/
theorem finiteModelLiftConfigurationHom_injective
    {source target : AtomConfiguration FiniteModel.carrier} :
    Function.Injective
      (finiteModelLiftConfigurationHom.{u} (source := source) (target := target)) := by
  intro first second equality
  apply ConfigurationHom.ext
  funext atom
  have pointEquality := congrFun (congrArg ConfigurationHom.atomMap equality)
    (finiteModelLiftCarrierEquiv.{u}.atom atom)
  exact finiteModelLiftCarrierEquiv.{u}.atom.injective pointEquality

/--
The lifted reflected configuration map is pointwise the actual normalized
high configuration map on every canonical high Atom.
-/
theorem finiteGeneratedReflectedConfigurationMap_high_atom_graph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier)
    (atom : FiniteModel.carrier.Atom) :
    finiteModelLiftCarrierEquiv.{u}.atom
        ((finiteGeneratedReflectedConfigurationMap input lift base object).atomMap atom) =
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
        (finiteModelLiftArchitectureObject.{u} object)).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
  rw [finiteGeneratedReflectedConfigurationMap_atom_graph]
  rw [finiteGeneratedReflectedUpperAtomEquiv_high_graph]
  rw [(finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap_atomMap]

/-! ## High images of the two naturality composites -/

/--
The lifted left low composite is pointwise the left composite of the actual
normalized high operation-naturality equation.
-/
theorem finiteGeneratedReflectedOperationNaturality_left_high_graph
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
    (finiteModelLiftConfigurationHom.{u}
      (ConfigurationHom.comp
        (input.lowGeneratedLift.domain.reading.operationReading.configurationMap
          (finiteGeneratedReflectedOperationMap input lift base operation))
        (finiteGeneratedReflectedConfigurationMap input lift base source))).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      (ConfigurationHom.comp
        (input.highGeneratedLift.domain.reading.operationReading.configurationMap
          ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
            (finiteGeneratedDomainOperationEquiv.{u}
              (finiteGeneratedOuterInput input base) source target operation)))
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
          (finiteModelLiftArchitectureObject.{u} source))).atomMap
            (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
  change finiteModelLiftCarrierEquiv.{u}.atom
      ((input.lowGeneratedLift.domain.reading.operationReading.configurationMap
        (finiteGeneratedReflectedOperationMap input lift base operation)).atomMap
        ((finiteGeneratedReflectedConfigurationMap input lift base source).atomMap atom)) =
    (input.highGeneratedLift.domain.reading.operationReading.configurationMap
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
        (finiteGeneratedDomainOperationEquiv.{u}
          (finiteGeneratedOuterInput input base) source target operation))).atomMap
      (((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
        (finiteModelLiftArchitectureObject.{u} source)).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom))
  calc
    finiteModelLiftCarrierEquiv.{u}.atom
        ((input.lowGeneratedLift.domain.reading.operationReading.configurationMap
          (finiteGeneratedReflectedOperationMap input lift base operation)).atomMap
          ((finiteGeneratedReflectedConfigurationMap input lift base source).atomMap atom)) =
      (input.highGeneratedLift.domain.reading.operationReading.configurationMap
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
          (finiteGeneratedDomainOperationEquiv.{u}
            (finiteGeneratedOuterInput input base) source target operation))).atomMap
        (finiteModelLiftCarrierEquiv.{u}.atom
          ((finiteGeneratedReflectedConfigurationMap input lift base source).atomMap atom)) := by
      have operationGraph := finiteGeneratedReflectedOperationMap_atom_graph.{u}
        input lift base operation
        ((finiteGeneratedReflectedConfigurationMap input lift base source).atomMap atom)
      simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom operationGraph
    _ = (input.highGeneratedLift.domain.reading.operationReading.configurationMap
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
          (finiteGeneratedDomainOperationEquiv.{u}
            (finiteGeneratedOuterInput input base) source target operation))).atomMap
      (((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
        (finiteModelLiftArchitectureObject.{u} source)).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom)) := by
      exact congrArg
        (input.highGeneratedLift.domain.reading.operationReading.configurationMap
          ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
            (finiteGeneratedDomainOperationEquiv.{u}
              (finiteGeneratedOuterInput input base) source target operation))).atomMap
        (finiteGeneratedReflectedConfigurationMap_high_atom_graph
          input lift base source atom)

/--
The lifted right low composite is pointwise the right composite of the actual
normalized high operation-naturality equation.
-/
theorem finiteGeneratedReflectedOperationNaturality_right_high_graph
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
    (finiteModelLiftConfigurationHom.{u}
      (ConfigurationHom.comp
        (finiteGeneratedReflectedConfigurationMap input lift base target)
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.configurationMap
          operation))).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      (ConfigurationHom.comp
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
          (finiteModelLiftArchitectureObject.{u} target))
        ((finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.operationReading.configurationMap
            (finiteGeneratedDomainOperationEquiv.{u}
              (finiteGeneratedOuterInput input base) source target operation))).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
  change finiteModelLiftCarrierEquiv.{u}.atom
      ((finiteGeneratedReflectedConfigurationMap input lift base target).atomMap
        (((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.configurationMap
          operation).atomMap atom)) =
    ((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
      (finiteModelLiftArchitectureObject.{u} target)).atomMap
      (((finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.operationReading.configurationMap
          (finiteGeneratedDomainOperationEquiv.{u}
            (finiteGeneratedOuterInput input base) source target operation)).atomMap
        (finiteModelLiftCarrierEquiv.{u}.atom atom))
  calc
    finiteModelLiftCarrierEquiv.{u}.atom
        ((finiteGeneratedReflectedConfigurationMap input lift base target).atomMap
          (((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.configurationMap
            operation).atomMap atom)) =
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
        (finiteModelLiftArchitectureObject.{u} target)).atomMap
        (finiteModelLiftCarrierEquiv.{u}.atom
          (((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.configurationMap
            operation).atomMap atom)) :=
      finiteGeneratedReflectedConfigurationMap_high_atom_graph
        input lift base target _
    _ = ((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
        (finiteModelLiftArchitectureObject.{u} target)).atomMap
      (((finiteGeneratedOuterInput input base).highGeneratedLift.domain.reading.operationReading.configurationMap
          (finiteGeneratedDomainOperationEquiv.{u}
            (finiteGeneratedOuterInput input base) source target operation)).atomMap
        (finiteModelLiftCarrierEquiv.{u}.atom atom)) := by
      apply congrArg
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
          (finiteModelLiftArchitectureObject.{u} target)).atomMap
      have operationGraph := finiteGeneratedDomainOperation_configurationMap_graph.{u}
        (finiteGeneratedOuterInput input base) operation
      exact congrFun (congrArg ConfigurationHom.atomMap operationGraph).symm
        (finiteModelLiftCarrierEquiv.{u}.atom atom)

/-! ## Actual-derived low operation naturality -/

/--
The reflected configuration and operation maps satisfy the exact low
operation-naturality equation for every generated-domain operation.  The
middle equality is the actual normalized high upper's
`operation_naturality` field on the canonical high operation image.
-/
theorem finiteGeneratedReflectedOperationMap_naturality
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.Op
      source target) :
    ConfigurationHom.comp
        (input.lowGeneratedLift.domain.reading.operationReading.configurationMap
          (finiteGeneratedReflectedOperationMap input lift base operation))
        (finiteGeneratedReflectedConfigurationMap input lift base source) =
      ConfigurationHom.comp
        (finiteGeneratedReflectedConfigurationMap input lift base target)
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.configurationMap
          operation) := by
  let outer := finiteGeneratedOuterInput input base
  let highOperation := finiteGeneratedDomainOperationEquiv.{u}
    outer source target operation
  have actualNaturality :=
    (finiteGeneratedNormalizedHighFactor input lift base).upper.operation_naturality
      highOperation
  apply finiteModelLiftConfigurationHom_injective.{u}
  apply ConfigurationHom.ext
  funext highAtom
  rcases highAtom with ⟨atom⟩
  calc
    (finiteModelLiftConfigurationHom.{u}
      (ConfigurationHom.comp
        (input.lowGeneratedLift.domain.reading.operationReading.configurationMap
          (finiteGeneratedReflectedOperationMap input lift base operation))
        (finiteGeneratedReflectedConfigurationMap input lift base source))).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      (ConfigurationHom.comp
        (input.highGeneratedLift.domain.reading.operationReading.configurationMap
          ((finiteGeneratedNormalizedHighFactor input lift base).upper.operationMap
            highOperation))
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
          (finiteModelLiftArchitectureObject.{u} source))).atomMap
            (finiteModelLiftCarrierEquiv.{u}.atom atom) :=
      finiteGeneratedReflectedOperationNaturality_left_high_graph
        input lift base operation atom
    _ = (ConfigurationHom.comp
        ((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
          (finiteModelLiftArchitectureObject.{u} target))
        (outer.highGeneratedLift.domain.reading.operationReading.configurationMap
          highOperation)).atomMap
            (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
      exact congrFun (congrArg ConfigurationHom.atomMap actualNaturality)
        (finiteModelLiftCarrierEquiv.{u}.atom atom)
    _ = (finiteModelLiftConfigurationHom.{u}
      (ConfigurationHom.comp
        (finiteGeneratedReflectedConfigurationMap input lift base target)
        (outer.lowGeneratedLift.domain.reading.operationReading.configurationMap
          operation))).atomMap
            (finiteModelLiftCarrierEquiv.{u}.atom atom) :=
      (finiteGeneratedReflectedOperationNaturality_right_high_graph
        input lift base operation atom).symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
