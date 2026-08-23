import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredCanonicalObjectNormalization

/-!
# Finite witness for canonical object normalization

On the reviewed finite authored support, the package-selected object on a
configuration is exactly the Cycle 63 auxiliary-reading erasure.  The existing
exactness proof therefore discharges the general normalization laws without
choosing an arbitrary endomorphism.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

/-- The general package-selected normalization specializes to the reviewed
finite object erasure. -/
theorem finiteCanonicalObjectNormalization_eq_erase
    (object : ArchitectureObject FiniteModel.carrier) :
    canonicalObjectNormalization finiteAxisFoldSupportPackage object =
      finiteAxisFoldEraseObject object := by
  simp [canonicalObjectNormalization, finiteAxisFoldEraseObject,
    finiteAxisFoldSupportPackage, AtomFoundation.transportAlong,
    AtomFoundation.transportCoreReading,
    AtomFoundation.transportObjectReading,
    AATCorePackage.generate,
    TransportCoherence.finiteWitnessSourcePackage,
    TransportCoherence.finiteWitnessSourceReading,
    FiniteModel.coreReading, FiniteModel.coreReadingFor,
    FiniteModel.objectReading, FiniteModel.objectOfConfiguration]

/-- Inverse Atom transport sees the same configuration after canonical
normalization. -/
theorem finiteCanonicalObjectNormalization_inverse_configuration
    (object : ArchitectureObject FiniteModel.carrier) :
    (transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv.symm
      (canonicalObjectNormalization finiteAxisFoldSupportPackage object)).configuration =
    (transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv.symm
      object).configuration := by
  rw [finiteCanonicalObjectNormalization_eq_erase]
  exact finiteAxisFoldEraseObject_inverse_configuration object

/-- The finite operation family depends only on the retained configurations. -/
theorem finiteCanonicalObjectNormalization_operationTypeEq
    (first second : ArchitectureObject FiniteModel.carrier) :
    finiteAxisFoldSupportPackage.reading.operationReading.Op first second =
      finiteAxisFoldSupportPackage.reading.operationReading.Op
        (canonicalObjectNormalization finiteAxisFoldSupportPackage first)
        (canonicalObjectNormalization finiteAxisFoldSupportPackage second) := by
  change ConfigurationHom
      (transportArchitectureObject
        finiteModelDoctrineFromFixture.atomEquiv.symm first).configuration
      (transportArchitectureObject
        finiteModelDoctrineFromFixture.atomEquiv.symm second).configuration =
    ConfigurationHom
      (transportArchitectureObject
        finiteModelDoctrineFromFixture.atomEquiv.symm
          (canonicalObjectNormalization
            finiteAxisFoldSupportPackage first)).configuration
      (transportArchitectureObject
        finiteModelDoctrineFromFixture.atomEquiv.symm
          (canonicalObjectNormalization
            finiteAxisFoldSupportPackage second)).configuration
  exact congrArg₂ ConfigurationHom
    (finiteCanonicalObjectNormalization_inverse_configuration first).symm
    (finiteCanonicalObjectNormalization_inverse_configuration second).symm

/-- Casting a finite operation along the normalization endpoint equalities
retains its Atom map. -/
theorem finiteCanonicalObjectNormalization_operationCast_atomMap
    {first second : ArchitectureObject FiniteModel.carrier}
    (operation : finiteAxisFoldSupportPackage.reading.operationReading.Op
      first second) :
    (cast (finiteCanonicalObjectNormalization_operationTypeEq first second)
      operation).atomMap = operation.atomMap := by
  let source_eq :=
    (finiteCanonicalObjectNormalization_inverse_configuration first).symm
  let target_eq :=
    (finiteCanonicalObjectNormalization_inverse_configuration second).symm
  have type_eq :
      finiteCanonicalObjectNormalization_operationTypeEq first second =
        congrArg₂ ConfigurationHom source_eq target_eq :=
    Subsingleton.elim _ _
  rw [type_eq]
  exact castConfigurationHomType_atomMap source_eq target_eq operation

/-- The reviewed finite support readings are insensitive to canonical removal
of auxiliary object decorations. -/
theorem finiteCanonicalObjectNormalization_admissible :
    CanonicalObjectNormalizationAdmissible
      finiteAxisFoldSupportPackage where
  equationResidual_eq := by
    intro W object index atom
    apply finiteAxisFoldSupportPackage_equationResidual_configurationInvariant
    exact (canonicalObjectNormalization_configuration
      finiteAxisFoldSupportPackage object).symm
  operation_type_eq :=
    finiteCanonicalObjectNormalization_operationTypeEq
  operation_naturality := by
    intro first second operation
    apply ConfigurationHom.ext
    funext atom
    simp [canonicalObjectNormalizationConfigurationHom,
      finiteAxisFoldSupportPackage, AtomFoundation.transportAlong,
      AtomFoundation.transportCoreReading,
      AtomFoundation.transportOperationReading,
      AATCorePackage.generate,
      TransportCoherence.finiteWitnessSourcePackage,
      TransportCoherence.finiteWitnessSourceReading,
      FiniteModel.coreReading, FiniteModel.coreReadingFor,
      FiniteModel.operationReading, ConfigurationHom.comp,
      ConfigurationHom.id]
    rw [finiteCanonicalObjectNormalization_operationCast_atomMap]
  invariant_transport := by
    intro index
    simpa only [finiteCanonicalObjectNormalization_eq_erase] using
      finiteAxisFoldEraseUpper.invariant_transport index
  coordinate_eq := by
    intro object axis
    simpa only [finiteCanonicalObjectNormalization_eq_erase] using
      finiteAxisFoldEraseUpper.coordinate_eq object axis

/-- The package-forced canonical normalization is genuinely noninvertible. -/
theorem finiteCanonicalObjectNormalizationTotal_not_isIso :
    ¬ IsIso (show finiteAxisFoldSupportPackage ⟶
      finiteAxisFoldSupportPackage from
        canonicalObjectNormalizationTotal finiteAxisFoldSupportPackage
          finiteCanonicalObjectNormalization_admissible) := by
  apply canonicalObjectNormalizationTotal_not_isIso
  intro injective
  apply finiteAxisFoldEraseObject_not_injective
  intro first second equality
  apply injective
  simpa only [finiteCanonicalObjectNormalization_eq_erase] using equality

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
