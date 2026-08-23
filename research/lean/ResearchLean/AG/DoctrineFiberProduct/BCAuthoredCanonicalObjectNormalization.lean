import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredObjectCollapse

/-!
# Canonical object normalization inside an authored support package

Every core package already selects one architecture object for each Atom
configuration through its `objectReading`.  This module fixes the only
configuration-retaining normalization available from that existing reading:
send an arbitrary architecture object to the package-selected object on the
same configuration.  No endomorphism is chosen from an existential.

The normalization becomes an exact package endomorphism when the remaining
equation, operation, invariant, and signature readings are insensitive to that
normalization.  Those laws form a Prop-valued admissibility predicate; the
resulting morphism data are then definitionally determined by the package and
the equality proofs are proof-irrelevant.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-- Normalize an object to the package's selected object on its existing Atom
configuration. -/
noncomputable def canonicalObjectNormalization
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (object : ArchitectureObject U) : ArchitectureObject U :=
  P.reading.objectReading.object object.configuration

/-- Canonical normalization retains the complete Atom configuration. -/
theorem canonicalObjectNormalization_configuration
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (object : ArchitectureObject U) :
    (canonicalObjectNormalization P object).configuration =
      object.configuration :=
  P.reading.objectReading.configuration_eq object.configuration

/-- The package-selected object on a configuration is fixed by normalization. -/
theorem canonicalObjectNormalization_selected
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (configuration : AtomConfiguration U) :
    canonicalObjectNormalization P
        (P.reading.objectReading.object configuration) =
      P.reading.objectReading.object configuration := by
  unfold canonicalObjectNormalization
  rw [P.reading.objectReading.configuration_eq]

/-- Canonical normalization is idempotent. -/
theorem canonicalObjectNormalization_idempotent
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (object : ArchitectureObject U) :
    canonicalObjectNormalization P
        (canonicalObjectNormalization P object) =
      canonicalObjectNormalization P object := by
  unfold canonicalObjectNormalization
  rw [P.reading.objectReading.configuration_eq]

/-- The identity-Atom configuration hom from an object to its canonical
normalization. -/
def canonicalObjectNormalizationConfigurationHom
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (object : ArchitectureObject U) :
    ConfigurationHom object.configuration
      (canonicalObjectNormalization P object).configuration :=
  castConfigurationHom rfl
    (canonicalObjectNormalization_configuration P object).symm
    (ConfigurationHom.id object.configuration)

@[simp]
theorem canonicalObjectNormalizationConfigurationHom_atomMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (object : ArchitectureObject U) :
    (canonicalObjectNormalizationConfigurationHom P object).atomMap =
      _root_.id := by
  apply castConfigurationHom_atomMap

/-- Casting a configuration hom along endpoint-induced equality of its indexed
type retains the underlying Atom map. -/
theorem castConfigurationHomType_atomMap
    {U : AtomCarrier.{u}}
    {firstSource secondSource firstTarget secondTarget : AtomConfiguration U}
    (source_eq : firstSource = secondSource)
    (target_eq : firstTarget = secondTarget)
    (hom : ConfigurationHom firstSource firstTarget) :
    (cast (congrArg₂ ConfigurationHom source_eq target_eq) hom).atomMap =
      hom.atomMap := by
  cases source_eq
  cases target_eq
  rfl

/-- Exactness laws saying that every non-object reading ignores replacement of
auxiliary object data by the package-selected object on the same configuration.
The predicate contains laws only; it does not contain a comparison or collapse
morphism. -/
structure CanonicalObjectNormalizationAdmissible
    {U : AtomCarrier.{u}} (P : AATCorePackage U) : Prop where
  equationResidual_eq : ∀ W object index atom,
    P.algebra.equationSystem.equationResidual W object index atom =
      P.algebra.equationSystem.equationResidual W
        (canonicalObjectNormalization P object) index atom
  operation_type_eq : ∀ first second,
    P.reading.operationReading.Op first second =
      P.reading.operationReading.Op
        (canonicalObjectNormalization P first)
        (canonicalObjectNormalization P second)
  operation_naturality : ∀ first second
      (operation : P.reading.operationReading.Op first second),
    ConfigurationHom.comp
        (P.reading.operationReading.configurationMap
          (cast (operation_type_eq first second) operation))
        (canonicalObjectNormalizationConfigurationHom P first) =
      ConfigurationHom.comp
        (canonicalObjectNormalizationConfigurationHom P second)
        (P.reading.operationReading.configurationMap operation)
  invariant_transport : ∀ index,
    Invariant.TransportedAlong
      (P.reading.invariantReading.invariant index)
      (P.reading.invariantReading.invariant index)
      _root_.id (canonicalObjectNormalization P)
  coordinate_eq : ∀ object axis,
    P.reading.signatureReading.coordinate object axis =
      P.reading.signatureReading.coordinate
        (canonicalObjectNormalization P object) axis

/-- Admissibility entails the previously audited configuration-invariance law
for equation residuals.  The existing auxiliary-sensitive equation system
refutes that law, so this premise is substantive rather than automatic. -/
theorem CanonicalObjectNormalizationAdmissible.equationResidual_configurationInvariant
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    EquationResidualConfigurationInvariant P.algebra.equationSystem := by
  intro W first second index atom configuration_eq
  calc
    P.algebra.equationSystem.equationResidual W first index atom =
        P.algebra.equationSystem.equationResidual W
          (canonicalObjectNormalization P first) index atom :=
      admissible.equationResidual_eq W first index atom
    _ = P.algebra.equationSystem.equationResidual W
          (canonicalObjectNormalization P second) index atom := by
      rw [show canonicalObjectNormalization P first =
          canonicalObjectNormalization P second by
        unfold canonicalObjectNormalization
        rw [configuration_eq]]
    _ = P.algebra.equationSystem.equationResidual W second index atom :=
      (admissible.equationResidual_eq W second index atom).symm

/-- Exact equation transport for the canonical normalization. -/
noncomputable def canonicalObjectNormalizationEquationTransport
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    EquationSystemExactTransport
      P.algebra.equationSystem P.algebra.equationSystem
      (Equiv.refl U.Atom) (canonicalObjectNormalization P) where
  contextEquivalence := CategoryTheory.Equivalence.refl
  equationEquiv := Equiv.refl _
  role_eq := by intros; rfl
  observableEquiv := fun _ => RingEquiv.refl _
  observable_naturality := by intros; rfl
  violationCoordinate_eq := by intros; rfl
  equationResidual_eq := by
    intro W object index atom
    exact admissible.equationResidual_eq W object index atom

/-- The canonical normalization as an exact endomorphism of a package whose
readings satisfy the normalization laws. -/
noncomputable def canonicalObjectNormalizationUpper
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    SignedExactCoreReadingHom P P where
  atomEquiv := Equiv.refl _
  extraction_eq := by simp
  composition_eq := by intros; simp
  objectMap := canonicalObjectNormalization P
  object_formation_eq := by
    intro configuration
    simpa using canonicalObjectNormalization_selected P configuration
  configurationMap := canonicalObjectNormalizationConfigurationHom P
  configurationMap_atomMap :=
    canonicalObjectNormalizationConfigurationHom_atomMap P
  configuration_eq := by
    intro object
    rw [canonicalObjectNormalization_configuration]
    exact (AtomFoundation.atomConfiguration_transport_id
      object.configuration).symm
  equationTransport :=
    canonicalObjectNormalizationEquationTransport P admissible
  detectorCode_eq := by
    intro index
    exact (CircuitDetectorCode.transport_refl _).symm
  operationMap := by
    intro first second operation
    exact cast (admissible.operation_type_eq first second) operation
  operation_naturality := by
    intro first second operation
    exact admissible.operation_naturality first second operation
  invariantMap := _root_.id
  invariant_transport := admissible.invariant_transport
  axisMap := _root_.id
  coordinateEquiv := fun _ => Equiv.refl _
  axis_selected_iff := fun _ => Iff.rfl
  coordinate_eq := admissible.coordinate_eq

/-- The canonical normalization as a total package endomorphism over the
identity point. -/
noncomputable def canonicalObjectNormalizationTotal
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    PackageTotalHom P P where
  base := ExtInstHom.id (packagePoint P)
  upper := canonicalObjectNormalizationUpper P admissible
  atomEquiv_eq := by
    apply Equiv.ext
    intro atom
    rfl

/-- Admissibility proofs cannot change the canonical normalization morphism. -/
theorem canonicalObjectNormalizationTotal_proof_irrel
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (first second : CanonicalObjectNormalizationAdmissible P) :
    canonicalObjectNormalizationTotal P first =
      canonicalObjectNormalizationTotal P second := by
  rw [Subsingleton.elim first second]

/-- Noninjectivity of the fixed normalization object map forces the canonical
total endomorphism to be noninvertible. -/
theorem canonicalObjectNormalizationTotal_not_isIso
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (not_injective : ¬ Function.Injective (canonicalObjectNormalization P)) :
    ¬ IsIso (show P ⟶ P from
      canonicalObjectNormalizationTotal P admissible) := by
  intro isIso
  letI : IsIso (show P ⟶ P from
      canonicalObjectNormalizationTotal P admissible) := isIso
  apply not_injective
  exact packageTotalHom_objectMap_injective_of_isIso
    (canonicalObjectNormalizationTotal P admissible)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
