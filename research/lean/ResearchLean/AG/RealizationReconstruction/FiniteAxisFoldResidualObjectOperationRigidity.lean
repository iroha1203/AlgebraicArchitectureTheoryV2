import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualAtomRigidity
import ResearchLean.AG.DoctrineFiberProduct.CanonicalObjectNormalizationAPI
import Formal.Util.AssertStandardAxioms

/-!
# Object and operation constraints in the finite-axis-fold residual kernel

Cycle 73 proves that the primitive Atom equivalence of every residual element
is the identity.  This module uses that result, rather than adding an object or
operation certificate, to identify every transported configuration, every
canonically normalized object, and the complete configuration homomorphism of
every selected operation.

The raw `ArchitectureObject` also contains auxiliary type-valued structure-map
and selected-quantity data.  Canonical normalization deliberately forgets that
data, so the raw object map is identified with canonical normalization rather
than incorrectly identified with the identity function.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport

noncomputable section

private noncomputable abbrev FiniteAxisFoldResidualEndpointCore :=
  finiteAxisFoldActualDirectAdmissibleGeometry.obj.core

private noncomputable abbrev ResidualUpper
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel) :
    SignedExactCoreReadingHom FiniteAxisFoldResidualEndpointCore
      FiniteAxisFoldResidualEndpointCore :=
  remainder.1.1.hom.f.hom.base.upper

private noncomputable abbrev ResidualCanonicalUpper :
    SignedExactCoreReadingHom FiniteAxisFoldResidualEndpointCore
      FiniteAxisFoldResidualEndpointCore :=
  canonicalObjectNormalizationUpper FiniteAxisFoldResidualEndpointCore
    finiteAxisFoldActualDirectAdmissibleGeometry.property

private def OperationAtomMapFaithful {U : AtomCarrier.{u}}
    (reading : OperationReading U) : Prop :=
  ∀ {source target}, Function.Injective
    (fun operation : reading.Op source target =>
      (reading.configurationMap operation).atomMap)

private theorem transportOperationReading_atomMapFaithful
    {U : AtomCarrier.{u}} (equivalence : U.Atom ≃ U.Atom)
    (reading : OperationReading U)
    (faithful : OperationAtomMapFaithful reading) :
    OperationAtomMapFaithful
      (AtomFoundation.transportOperationReading equivalence reading) := by
  intro source target first second equality
  apply faithful
  funext atom
  apply equivalence.injective
  have evaluated := congrFun equality (equivalence atom)
  simpa [AtomFoundation.transportOperationReading,
    AtomFoundation.castConfigurationHom_atomMap,
    AtomFoundation.transportConfigurationHom_atomMap,
    Function.comp_apply] using evaluated

private theorem finiteModel_operationReading_atomMapFaithful :
    OperationAtomMapFaithful FiniteModel.operationReading := by
  intro source target first second equality
  apply ConfigurationHom.ext
  exact equality

private theorem finiteAxisFoldResidualEndpoint_operationAtomMapFaithful :
    OperationAtomMapFaithful
      FiniteAxisFoldResidualEndpointCore.reading.operationReading := by
  change OperationAtomMapFaithful
    (AtomFoundation.transportOperationReading _
      (AtomFoundation.transportOperationReading _
        (AtomFoundation.transportOperationReading _ FiniteModel.operationReading)))
  apply transportOperationReading_atomMapFaithful
  apply transportOperationReading_atomMapFaithful
  apply transportOperationReading_atomMapFaithful
  apply finiteModel_operationReading_atomMapFaithful

/-- The Karoubi sandwich equation upgrades exact object formation on selected
objects to a pointwise formula on every raw architecture object.  After Cycle
73's Atom rigidity, the formula says that the residual object map is exactly
the fixed canonical normalization, not the raw identity. -/
theorem finiteAxisFoldResidual_objectMap_apply
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel)
    (object : ArchitectureObject FiniteModel.carrier) :
    (ResidualUpper remainder).objectMap object =
      canonicalObjectNormalization FiniteAxisFoldResidualEndpointCore object := by
  have totalEquality := congrArg (fun hom => hom.hom) remainder.1.1.hom.comm
  have objectMapEquality :=
    congrArg (fun hom => hom.base.upper.objectMap) totalEquality
  have pointEquality := congrFun objectMapEquality object
  change canonicalObjectNormalization FiniteAxisFoldResidualEndpointCore
      ((ResidualUpper remainder).objectMap
        (canonicalObjectNormalization FiniteAxisFoldResidualEndpointCore object)) =
    (ResidualUpper remainder).objectMap object at pointEquality
  rw [canonicalObjectNormalization_apply] at pointEquality
  rw [(ResidualUpper remainder).configuration_eq,
    canonicalObjectNormalization_configuration] at pointEquality
  calc
    (ResidualUpper remainder).objectMap object =
        FiniteAxisFoldResidualEndpointCore.reading.objectReading.object
          (object.configuration.transport (ResidualUpper remainder).atomEquiv) :=
      pointEquality.symm
    _ = FiniteAxisFoldResidualEndpointCore.reading.objectReading.object
          object.configuration := by
      rw [finiteAxisFoldResidual_atomEquiv_eq_refl remainder]
      exact congrArg _
        (AtomFoundation.atomConfiguration_transport_id object.configuration)
    _ = canonicalObjectNormalization FiniteAxisFoldResidualEndpointCore object := rfl

/-- Function-level form of residual object-map rigidity. -/
theorem finiteAxisFoldResidual_objectMap_eq_canonicalObjectNormalization
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel) :
    (ResidualUpper remainder).objectMap =
      canonicalObjectNormalization FiniteAxisFoldResidualEndpointCore := by
  funext object
  exact finiteAxisFoldResidual_objectMap_apply remainder object

/-- Every residual object map preserves the complete Atom configuration, not
only its selected family. -/
theorem finiteAxisFoldResidual_object_configuration_eq
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel)
    (object : ArchitectureObject FiniteModel.carrier) :
    ((ResidualUpper remainder).objectMap object).configuration =
      object.configuration := by
  rw [(ResidualUpper remainder).configuration_eq,
    finiteAxisFoldResidual_atomEquiv_eq_refl remainder]
  simp

/-- After the fixed canonical object normalization, every residual object map
is pointwise invisible.  This is the exact conclusion available for raw
objects with arbitrary auxiliary decorations. -/
theorem finiteAxisFoldResidual_canonicalObjectNormalization_objectMap
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel)
    (object : ArchitectureObject FiniteModel.carrier) :
    canonicalObjectNormalization FiniteAxisFoldResidualEndpointCore
        ((ResidualUpper remainder).objectMap object) =
      canonicalObjectNormalization FiniteAxisFoldResidualEndpointCore object :=
  canonicalObjectNormalization_eq_of_configuration_eq
    FiniteAxisFoldResidualEndpointCore
    (finiteAxisFoldResidual_object_configuration_eq remainder object)

/-- The configuration comparison attached to every residual object is the
identity after transporting its target along the proved configuration
equality. -/
theorem finiteAxisFoldResidual_configurationMap_eq_id
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel)
    (object : ArchitectureObject FiniteModel.carrier) :
    cast
        (congrArg (ConfigurationHom object.configuration)
          (finiteAxisFoldResidual_object_configuration_eq remainder object))
        ((ResidualUpper remainder).configurationMap object) =
      ConfigurationHom.id object.configuration := by
  apply ConfigurationHom.ext
  rw [castConfigurationHomType_atomMap rfl
    (finiteAxisFoldResidual_object_configuration_eq remainder object)]
  rw [(ResidualUpper remainder).configurationMap_atomMap,
    finiteAxisFoldResidual_atomEquiv_eq_refl remainder]
  rfl

/-- Naturality plus Atom rigidity fixes the underlying Atom map of every
selected operation, for all source and target architecture objects. -/
theorem finiteAxisFoldResidual_operation_configurationMap_atomMap
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : FiniteAxisFoldResidualEndpointCore.reading.operationReading.Op
      source target) :
    (FiniteAxisFoldResidualEndpointCore.reading.operationReading.configurationMap
      ((ResidualUpper remainder).operationMap operation)).atomMap =
    (FiniteAxisFoldResidualEndpointCore.reading.operationReading.configurationMap
      operation).atomMap := by
  have naturality := congrArg ConfigurationHom.atomMap
    ((ResidualUpper remainder).operation_naturality operation)
  simp only [ConfigurationHom.comp] at naturality
  rw [(ResidualUpper remainder).configurationMap_atomMap,
    (ResidualUpper remainder).configurationMap_atomMap,
    finiteAxisFoldResidual_atomEquiv_eq_refl remainder] at naturality
  simpa only [Function.comp_id, Function.id_comp] using naturality

/-- After casting both mapped endpoints along the independently proved object
configuration equalities, every residual operation has exactly its original
configuration homomorphism. -/
theorem finiteAxisFoldResidual_operation_configurationMap_eq
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : FiniteAxisFoldResidualEndpointCore.reading.operationReading.Op
      source target) :
    cast
        (congrArg₂ ConfigurationHom
          (finiteAxisFoldResidual_object_configuration_eq remainder source)
          (finiteAxisFoldResidual_object_configuration_eq remainder target))
        (FiniteAxisFoldResidualEndpointCore.reading.operationReading.configurationMap
          ((ResidualUpper remainder).operationMap operation)) =
      FiniteAxisFoldResidualEndpointCore.reading.operationReading.configurationMap
        operation := by
  apply ConfigurationHom.ext
  rw [castConfigurationHomType_atomMap
    (finiteAxisFoldResidual_object_configuration_eq remainder source)
    (finiteAxisFoldResidual_object_configuration_eq remainder target)]
  exact finiteAxisFoldResidual_operation_configurationMap_atomMap
    remainder operation

/-- The fixed endpoint operation reading is faithful, so the equality of
realized configuration Atom maps upgrades to equality with the canonical
normalization operation.  The cast changes only the dependent raw-object
endpoints, using the separately proved object-map formula. -/
theorem finiteAxisFoldResidual_operationMap_eq_canonicalNormalization
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : FiniteAxisFoldResidualEndpointCore.reading.operationReading.Op
      source target) :
    AtomFoundation.castOperation
        FiniteAxisFoldResidualEndpointCore.reading.operationReading
        (finiteAxisFoldResidual_objectMap_apply remainder source)
        (finiteAxisFoldResidual_objectMap_apply remainder target)
        ((ResidualUpper remainder).operationMap operation) =
      ResidualCanonicalUpper.operationMap operation := by
  apply finiteAxisFoldResidualEndpoint_operationAtomMapFaithful
  change
    (FiniteAxisFoldResidualEndpointCore.reading.operationReading.configurationMap
      (AtomFoundation.castOperation
        FiniteAxisFoldResidualEndpointCore.reading.operationReading
        (finiteAxisFoldResidual_objectMap_apply remainder source)
        (finiteAxisFoldResidual_objectMap_apply remainder target)
        ((ResidualUpper remainder).operationMap operation))).atomMap =
      (FiniteAxisFoldResidualEndpointCore.reading.operationReading.configurationMap
        (ResidualCanonicalUpper.operationMap operation)).atomMap
  rw [AtomFoundation.castOperation_configurationMap_atomMap]
  exact operationConfigurationMap_atomMap_eq_of_atomEquiv_eq
    (ResidualUpper remainder) ResidualCanonicalUpper
    (finiteAxisFoldResidual_atomEquiv_eq_refl remainder) operation

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
