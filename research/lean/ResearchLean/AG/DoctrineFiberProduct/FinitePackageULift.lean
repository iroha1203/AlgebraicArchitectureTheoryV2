import ResearchLean.AG.DoctrineFiberProduct.FiniteCodeULift

/-!
# Canonical finite-package universe-lift foundation

This module supplies the object-level foundation needed to rebase finite-model
core packages from `FiniteModel.carrier` to `finiteModelLiftCarrier`.  Every
construction is generated from the source datum and the canonical Atom
equivalence.  No package morphism, cartesian lift, reflection certificate, or
nonexistence conclusion is accepted as an input.

The present layer stops after families, configurations, configuration maps,
architecture objects, extraction doctrines, Atom axioms, and the finite
model's composition, object, invariant, signature, and operation readings.
Equation, complete `CoreReading`, and `AATCorePackage` rebasing are
intentionally deferred to the next layer.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open AtomFoundation

/-! ## Atom families -/

/-- Rebase a finite-model Atom family along the canonical universe lift. -/
def finiteModelLiftAtomFamily
    (family : AtomFamily FiniteModel.carrier) :
    AtomFamily finiteModelLiftCarrier.{u} where
  mem atom := family.mem (finiteModelLiftCarrierEquiv.atom.symm atom)

/-- Reflect a family on the lifted finite carrier back to the base carrier. -/
def finiteModelReflectAtomFamily
    (family : AtomFamily finiteModelLiftCarrier.{u}) :
    AtomFamily FiniteModel.carrier where
  mem atom := family.mem (finiteModelLiftCarrierEquiv.atom atom)

/-- Reflecting a canonically lifted family recovers the original family. -/
@[simp]
theorem finiteModelReflectAtomFamily_lift
    (family : AtomFamily FiniteModel.carrier) :
    finiteModelReflectAtomFamily.{u} (finiteModelLiftAtomFamily.{u} family) = family := by
  ext atom
  simp [finiteModelReflectAtomFamily, finiteModelLiftAtomFamily]

/-- Lifting a reflected family recovers the original lifted-carrier family. -/
@[simp]
theorem finiteModelLiftAtomFamily_reflect
    (family : AtomFamily finiteModelLiftCarrier.{u}) :
    finiteModelLiftAtomFamily.{u}
        (finiteModelReflectAtomFamily.{u} family) = family := by
  ext atom
  simp [finiteModelReflectAtomFamily, finiteModelLiftAtomFamily]

/-- Explicit list-finiteness is preserved by canonical family rebasing. -/
theorem finiteModelLiftAtomFamily_listFinite
    {family : AtomFamily FiniteModel.carrier}
    (hfinite : family.ListFinite) :
    (finiteModelLiftAtomFamily.{u} family).ListFinite := by
  rcases hfinite with ⟨atoms, hatoms⟩
  refine ⟨atoms.map finiteModelLiftCarrierEquiv.atom, ?_⟩
  intro atom hmem
  have hbase : finiteModelLiftCarrierEquiv.atom.symm atom ∈ atoms :=
    hatoms _ (by
      simpa [finiteModelLiftAtomFamily] using hmem)
  exact List.mem_map.mpr
    ⟨finiteModelLiftCarrierEquiv.atom.symm atom, hbase,
      finiteModelLiftCarrierEquiv.atom.apply_symm_apply atom⟩

/-- Explicit list-finiteness is preserved by reflection to the base carrier. -/
theorem finiteModelReflectAtomFamily_listFinite
    {family : AtomFamily finiteModelLiftCarrier.{u}}
    (hfinite : family.ListFinite) :
    (finiteModelReflectAtomFamily.{u} family).ListFinite := by
  rcases hfinite with ⟨atoms, hatoms⟩
  refine ⟨atoms.map finiteModelLiftCarrierEquiv.{u}.atom.symm, ?_⟩
  intro atom hmem
  have hlift : finiteModelLiftCarrierEquiv.{u}.atom atom ∈ atoms :=
    hatoms _ (by
      simpa [finiteModelReflectAtomFamily] using hmem)
  exact List.mem_map.mpr
    ⟨finiteModelLiftCarrierEquiv.{u}.atom atom, hlift,
      finiteModelLiftCarrierEquiv.{u}.atom.symm_apply_apply atom⟩

/-! ## Atom configurations -/

/-- Rebase every Atom-dependent field of a finite-model configuration. -/
def finiteModelLiftAtomConfiguration
    (configuration : AtomConfiguration FiniteModel.carrier) :
    AtomConfiguration finiteModelLiftCarrier.{u} where
  family := finiteModelLiftAtomFamily.{u} configuration.family
  relation first second := configuration.relation
    (finiteModelLiftCarrierEquiv.atom.symm first)
    (finiteModelLiftCarrierEquiv.atom.symm second)
  identification first second := configuration.identification
    (finiteModelLiftCarrierEquiv.atom.symm first)
    (finiteModelLiftCarrierEquiv.atom.symm second)

/-- Reflect a lifted finite-carrier configuration to the base carrier. -/
def finiteModelReflectAtomConfiguration
    (configuration : AtomConfiguration finiteModelLiftCarrier.{u}) :
    AtomConfiguration FiniteModel.carrier where
  family := finiteModelReflectAtomFamily.{u} configuration.family
  relation first second := configuration.relation
    (finiteModelLiftCarrierEquiv.atom first)
    (finiteModelLiftCarrierEquiv.atom second)
  identification first second := configuration.identification
    (finiteModelLiftCarrierEquiv.atom first)
    (finiteModelLiftCarrierEquiv.atom second)

/-- Configuration reflection is a left inverse to canonical rebasing. -/
@[simp]
theorem finiteModelReflectAtomConfiguration_lift
    (configuration : AtomConfiguration FiniteModel.carrier) :
    finiteModelReflectAtomConfiguration.{u}
        (finiteModelLiftAtomConfiguration.{u} configuration) = configuration := by
  apply AtomConfiguration.ext
  · exact finiteModelReflectAtomFamily_lift.{u} configuration.family
  · intro first second
    simp [finiteModelReflectAtomConfiguration,
      finiteModelLiftAtomConfiguration]
  · intro first second
    simp [finiteModelReflectAtomConfiguration,
      finiteModelLiftAtomConfiguration]

/-- Configuration reflection is also a right inverse on the lifted carrier. -/
@[simp]
theorem finiteModelLiftAtomConfiguration_reflect
    (configuration : AtomConfiguration finiteModelLiftCarrier.{u}) :
    finiteModelLiftAtomConfiguration.{u}
        (finiteModelReflectAtomConfiguration.{u} configuration) = configuration := by
  apply AtomConfiguration.ext
  · exact finiteModelLiftAtomFamily_reflect.{u} configuration.family
  · intro first second
    simp [finiteModelReflectAtomConfiguration,
      finiteModelLiftAtomConfiguration]
  · intro first second
    simp [finiteModelReflectAtomConfiguration,
      finiteModelLiftAtomConfiguration]

/-- Canonical configuration rebasing is injective. -/
theorem finiteModelLiftAtomConfiguration_injective :
    Function.Injective (finiteModelLiftAtomConfiguration.{u}) :=
  Function.LeftInverse.injective finiteModelReflectAtomConfiguration_lift.{u}

/-- Family support is preserved when a base configuration is lifted. -/
theorem finiteModelLiftAtomConfiguration_familySupported
    {configuration : AtomConfiguration FiniteModel.carrier}
    (hsupported : configuration.FamilySupported) :
    (finiteModelLiftAtomConfiguration.{u} configuration).FamilySupported := by
  constructor
  · intro first second hrelation
    have hbase := hsupported.1 hrelation
    exact ⟨hbase.1, hbase.2⟩
  · intro first second hidentification
    have hbase := hsupported.2 hidentification
    exact ⟨hbase.1, hbase.2⟩

/-- Family support is preserved when a lifted configuration is reflected. -/
theorem finiteModelReflectAtomConfiguration_familySupported
    {configuration : AtomConfiguration finiteModelLiftCarrier.{u}}
    (hsupported : configuration.FamilySupported) :
    (finiteModelReflectAtomConfiguration.{u} configuration).FamilySupported := by
  constructor
  · intro first second hrelation
    have hlift := hsupported.1 hrelation
    exact ⟨hlift.1, hlift.2⟩
  · intro first second hidentification
    have hlift := hsupported.2 hidentification
    exact ⟨hlift.1, hlift.2⟩

/-! ## Configuration homomorphisms -/

/--
Rebase a configuration homomorphism by conjugating its Atom map with the
canonical finite-model carrier equivalence.
-/
def finiteModelLiftConfigurationHom
    {source target : AtomConfiguration FiniteModel.carrier}
    (hom : ConfigurationHom source target) :
    ConfigurationHom (finiteModelLiftAtomConfiguration.{u} source)
      (finiteModelLiftAtomConfiguration.{u} target) where
  atomMap atom := finiteModelLiftCarrierEquiv.atom
    (hom.atomMap (finiteModelLiftCarrierEquiv.atom.symm atom))
  maps_family := by
    intro atom hmem
    simpa [finiteModelLiftAtomConfiguration, finiteModelLiftAtomFamily] using
      hom.maps_family hmem
  maps_relation := by
    intro first second hrelation
    simpa [finiteModelLiftAtomConfiguration] using
      hom.maps_relation hrelation
  maps_identification := by
    intro first second hidentification
    simpa [finiteModelLiftAtomConfiguration] using
      hom.maps_identification hidentification

/--
Reflect a lifted-carrier configuration homomorphism by inverse conjugation of
its Atom map.
-/
def finiteModelReflectConfigurationHom
    {source target : AtomConfiguration finiteModelLiftCarrier.{u}}
    (hom : ConfigurationHom source target) :
    ConfigurationHom (finiteModelReflectAtomConfiguration.{u} source)
      (finiteModelReflectAtomConfiguration.{u} target) where
  atomMap atom := finiteModelLiftCarrierEquiv.atom.symm
    (hom.atomMap (finiteModelLiftCarrierEquiv.atom atom))
  maps_family := by
    intro atom hmem
    simpa [finiteModelReflectAtomConfiguration, finiteModelReflectAtomFamily] using
      hom.maps_family hmem
  maps_relation := by
    intro first second hrelation
    simpa [finiteModelReflectAtomConfiguration] using
      hom.maps_relation hrelation
  maps_identification := by
    intro first second hidentification
    simpa [finiteModelReflectAtomConfiguration] using
      hom.maps_identification hidentification

/-- A lifted configuration hom has the expected conjugated Atom map. -/
@[simp]
theorem finiteModelLiftConfigurationHom_atomMap
    {source target : AtomConfiguration FiniteModel.carrier}
    (hom : ConfigurationHom source target) :
    (finiteModelLiftConfigurationHom.{u} hom).atomMap =
      finiteModelLiftCarrierEquiv.atom ∘ hom.atomMap ∘
        finiteModelLiftCarrierEquiv.atom.symm :=
  rfl

/-- A reflected configuration hom has the expected inverse-conjugated Atom map. -/
@[simp]
theorem finiteModelReflectConfigurationHom_atomMap
    {source target : AtomConfiguration finiteModelLiftCarrier.{u}}
    (hom : ConfigurationHom source target) :
    (finiteModelReflectConfigurationHom.{u} hom).atomMap =
      finiteModelLiftCarrierEquiv.atom.symm ∘ hom.atomMap ∘
        finiteModelLiftCarrierEquiv.atom :=
  rfl

/-- Reflecting a lifted base configuration hom recovers the original hom. -/
@[simp]
theorem finiteModelReflectConfigurationHom_lift
    {source target : AtomConfiguration FiniteModel.carrier}
    (hom : ConfigurationHom source target) :
    castConfigurationHom
        (finiteModelReflectAtomConfiguration_lift.{u} source)
        (finiteModelReflectAtomConfiguration_lift.{u} target)
        (finiteModelReflectConfigurationHom.{u}
          (finiteModelLiftConfigurationHom.{u} hom)) = hom := by
  apply ConfigurationHom.ext
  simp [Function.comp_def]

/-- Lifting a reflected lifted-carrier hom recovers the original hom. -/
@[simp]
theorem finiteModelLiftConfigurationHom_reflect
    {source target : AtomConfiguration finiteModelLiftCarrier.{u}}
    (hom : ConfigurationHom source target) :
    castConfigurationHom
        (finiteModelLiftAtomConfiguration_reflect.{u} source)
        (finiteModelLiftAtomConfiguration_reflect.{u} target)
        (finiteModelLiftConfigurationHom.{u}
          (finiteModelReflectConfigurationHom.{u} hom)) = hom := by
  apply ConfigurationHom.ext
  simp [Function.comp_def]

/-- Canonical configuration-hom rebasing preserves identity homomorphisms. -/
@[simp]
theorem finiteModelLiftConfigurationHom_id
    (configuration : AtomConfiguration FiniteModel.carrier) :
    finiteModelLiftConfigurationHom.{u} (ConfigurationHom.id configuration) =
      ConfigurationHom.id
        (finiteModelLiftAtomConfiguration.{u} configuration) := by
  apply ConfigurationHom.ext
  funext atom
  simp [finiteModelLiftConfigurationHom, ConfigurationHom.id]

/-- Configuration-hom reflection preserves identity homomorphisms. -/
@[simp]
theorem finiteModelReflectConfigurationHom_id
    (configuration : AtomConfiguration finiteModelLiftCarrier.{u}) :
    finiteModelReflectConfigurationHom.{u} (ConfigurationHom.id configuration) =
      ConfigurationHom.id
        (finiteModelReflectAtomConfiguration.{u} configuration) := by
  apply ConfigurationHom.ext
  funext atom
  simp [finiteModelReflectConfigurationHom, ConfigurationHom.id]

/--
Canonical configuration-hom rebasing preserves `ConfigurationHom.comp`, whose
first argument is the later map and whose second argument is the earlier map.
-/
@[simp]
theorem finiteModelLiftConfigurationHom_comp
    {first second third : AtomConfiguration FiniteModel.carrier}
    (later : ConfigurationHom second third)
    (earlier : ConfigurationHom first second) :
    finiteModelLiftConfigurationHom.{u}
        (ConfigurationHom.comp later earlier) =
      ConfigurationHom.comp
        (finiteModelLiftConfigurationHom.{u} later)
        (finiteModelLiftConfigurationHom.{u} earlier) := by
  apply ConfigurationHom.ext
  funext atom
  simp [finiteModelLiftConfigurationHom, ConfigurationHom.comp,
    Function.comp_def]

/--
Configuration-hom reflection preserves `ConfigurationHom.comp`, with the
later map retained as the first argument.
-/
@[simp]
theorem finiteModelReflectConfigurationHom_comp
    {first second third : AtomConfiguration finiteModelLiftCarrier.{u}}
    (later : ConfigurationHom second third)
    (earlier : ConfigurationHom first second) :
    finiteModelReflectConfigurationHom.{u}
        (ConfigurationHom.comp later earlier) =
      ConfigurationHom.comp
        (finiteModelReflectConfigurationHom.{u} later)
        (finiteModelReflectConfigurationHom.{u} earlier) := by
  apply ConfigurationHom.ext
  funext atom
  simp [finiteModelReflectConfigurationHom, ConfigurationHom.comp,
    Function.comp_def]

/-! ## Architecture objects -/

/--
Rebase an architecture object by rebasing its Atom configuration and lifting
its two opaque carrier types and selected values.  This is intentionally a
one-way construction: no full-field inverse or equivalence for an arbitrary
lifted object is claimed.
-/
def finiteModelLiftArchitectureObject
    (object : ArchitectureObject FiniteModel.carrier) :
    ArchitectureObject finiteModelLiftCarrier.{u} where
  configuration := finiteModelLiftAtomConfiguration.{u} object.configuration
  StructureMaps := ULift.{u} object.StructureMaps
  SelectedQuantities := ULift.{u} object.SelectedQuantities
  structureMaps := ULift.up object.structureMaps
  selectedQuantities := ULift.up object.selectedQuantities

/-! ## Extraction doctrines -/

/-- Rebase every carrier of a finite-model extraction doctrine through `ULift`. -/
def finiteModelLiftExtractionDoctrine
    (doctrine : ExtractionDoctrine FiniteModel.carrier) :
    ExtractionDoctrine finiteModelLiftCarrier.{u} where
  Source := ULift.{u} doctrine.Source
  Vocabulary := ULift.{u} doctrine.Vocabulary
  SemanticReading := ULift.{u} doctrine.SemanticReading
  Resolution := ULift.{u} doctrine.Resolution
  vocabulary := ULift.up doctrine.vocabulary
  semanticReading := ULift.up doctrine.semanticReading
  resolution := ULift.up doctrine.resolution
  vocabularyAllows vocabulary atom := doctrine.vocabularyAllows vocabulary.down
    (finiteModelLiftCarrierEquiv.atom.symm atom)
  semanticAllows semantic source atom := doctrine.semanticAllows semantic.down
    source.down (finiteModelLiftCarrierEquiv.atom.symm atom)
  resolutionAllows resolution source atom := doctrine.resolutionAllows resolution.down
    source.down (finiteModelLiftCarrierEquiv.atom.symm atom)
  sourceSemantics source atom := doctrine.sourceSemantics source.down
    (finiteModelLiftCarrierEquiv.atom.symm atom)
  normalize source := ULift.up (doctrine.normalize source.down)

/-- Extraction is unchanged on corresponding source and Atom cells. -/
@[simp]
theorem finiteModelLiftExtractionDoctrine_extracts_iff
    (doctrine : ExtractionDoctrine FiniteModel.carrier)
    (source : doctrine.Source) (atom : FiniteModel.carrier.Atom) :
    (finiteModelLiftExtractionDoctrine.{u} doctrine).extracts
        (ULift.up source) (finiteModelLiftCarrierEquiv.atom atom) ↔
      doctrine.extracts source atom := by
  change doctrine.extracts source atom ↔ doctrine.extracts source atom
  rfl

/-- Canonical atomization commutes with finite-model doctrine rebasing. -/
@[simp]
theorem finiteModelLiftExtractionDoctrine_atomize
    (doctrine : ExtractionDoctrine FiniteModel.carrier)
    (source : doctrine.Source) :
    (finiteModelLiftExtractionDoctrine.{u} doctrine).atomize (ULift.up source) =
      finiteModelLiftAtomFamily.{u} (doctrine.atomize source) := by
  ext atom
  rcases atom with ⟨atom⟩
  change doctrine.extracts source atom ↔ doctrine.extracts source atom
  rfl

/-! ## Atom axioms -/

/-- Rebase the finite-model Atom axioms along the canonical carrier equivalence. -/
def finiteModelLiftAtomAxiomSystem
    (axioms : AtomAxiomSystem FiniteModel.carrier) :
    AtomAxiomSystem finiteModelLiftCarrier.{u} where
  primitiveExistence := axioms.primitiveExistence.map
    finiteModelLiftCarrierEquiv.atom
  predicateStability := by
    intro first second
    rcases first with ⟨first⟩
    rcases second with ⟨second⟩
    constructor
    · intro hcoordinates
      have hbase : first = second :=
        (axioms.predicateStability first second).mp
          ⟨congrArg ULift.down hcoordinates.1,
            congrArg ULift.down hcoordinates.2.1,
            congrArg ULift.down hcoordinates.2.2.1,
            congrArg ULift.down hcoordinates.2.2.2.1,
            congrArg ULift.down hcoordinates.2.2.2.2⟩
      exact congrArg finiteModelLiftCarrierEquiv.{u}.atom hbase
    · intro heq
      have hbase : first = second :=
        finiteModelLiftCarrierEquiv.{u}.atom.injective heq
      have hcoordinates :=
        (axioms.predicateStability first second).mpr hbase
      exact
        ⟨congrArg ULift.up hcoordinates.1,
          congrArg ULift.up hcoordinates.2.1,
          congrArg ULift.up hcoordinates.2.2.1,
          congrArg ULift.up hcoordinates.2.2.2.1,
          congrArg ULift.up hcoordinates.2.2.2.2⟩

/-! ## Composition and object readings -/

/-- Generate a lifted composition reading by reflecting its input family. -/
def finiteModelLiftCompositionReading
    (reading : CompositionReading FiniteModel.carrier) :
    CompositionReading finiteModelLiftCarrier.{u} where
  compose family hfinite :=
    finiteModelLiftAtomConfiguration.{u}
      (reading.compose (finiteModelReflectAtomFamily.{u} family)
        (finiteModelReflectAtomFamily_listFinite.{u} hfinite))
  family_eq := by
    intro family hfinite
    change finiteModelLiftAtomFamily.{u}
        (reading.compose (finiteModelReflectAtomFamily.{u} family)
          (finiteModelReflectAtomFamily_listFinite.{u} hfinite)).family = family
    rw [reading.family_eq]
    exact finiteModelLiftAtomFamily_reflect.{u} family
  family_supported := by
    intro family hfinite
    exact finiteModelLiftAtomConfiguration_familySupported.{u}
      (reading.family_supported (finiteModelReflectAtomFamily.{u} family)
        (finiteModelReflectAtomFamily_listFinite.{u} hfinite))

/-- Lifted composition agrees with source composition on every lifted family. -/
@[simp]
theorem finiteModelLiftCompositionReading_compose
    (reading : CompositionReading FiniteModel.carrier)
    (family : AtomFamily FiniteModel.carrier)
    (hfinite : family.ListFinite) :
    (finiteModelLiftCompositionReading.{u} reading).compose
        (finiteModelLiftAtomFamily.{u} family)
        (finiteModelLiftAtomFamily_listFinite.{u} hfinite) =
      finiteModelLiftAtomConfiguration.{u} (reading.compose family hfinite) := by
  simp [finiteModelLiftCompositionReading]

/-- Generate a lifted object reading by reflecting its input configuration. -/
def finiteModelLiftObjectReading
    (reading : ObjectReading FiniteModel.carrier) :
    ObjectReading finiteModelLiftCarrier.{u} where
  object configuration :=
    finiteModelLiftArchitectureObject.{u}
      (reading.object (finiteModelReflectAtomConfiguration.{u} configuration))
  configuration_eq := by
    intro configuration
    change finiteModelLiftAtomConfiguration.{u}
        (reading.object
          (finiteModelReflectAtomConfiguration.{u} configuration)).configuration =
      configuration
    rw [reading.configuration_eq]
    exact finiteModelLiftAtomConfiguration_reflect.{u} configuration

/-- Lifted object formation agrees with source formation on lifted configurations. -/
@[simp]
theorem finiteModelLiftObjectReading_object
    (reading : ObjectReading FiniteModel.carrier)
    (configuration : AtomConfiguration FiniteModel.carrier) :
    (finiteModelLiftObjectReading.{u} reading).object
        (finiteModelLiftAtomConfiguration.{u} configuration) =
      finiteModelLiftArchitectureObject.{u} (reading.object configuration) := by
  simp [finiteModelLiftObjectReading]

/-! ## Finite-model invariant reading -/

/--
The lifted finite-model invariant family is the generated singleton family of
the always-true predicate invariant.  This definition is specific to
`FiniteModel.invariantFamily`.
-/
def finiteModelLiftInvariantFamily :
    InvariantFamily finiteModelLiftCarrier.{u} where
  Index := ULift.{u} PUnit.{1}
  invariant _ := Invariant.predicate { holds := fun _ => True }

/-- The lifted invariant at a source index is exactly the always-true predicate. -/
@[simp]
theorem finiteModelLiftInvariantFamily_invariant
    (index : FiniteModel.invariantFamily.Index) :
    finiteModelLiftInvariantFamily.{u}.invariant (ULift.up index) =
      Invariant.predicate { holds := fun _ => True } :=
  rfl

/--
The source and lifted singleton invariants have the same truth value on every
base object and its canonical architecture-object lift.
-/
@[simp]
theorem finiteModelLiftInvariantFamily_holds_iff
    (index : FiniteModel.invariantFamily.Index)
    (object : ArchitectureObject FiniteModel.carrier) :
    (match FiniteModel.invariantFamily.invariant index with
      | .function _ => False
      | .predicate predicate => predicate.holds object) ↔
      (match finiteModelLiftInvariantFamily.{u}.invariant (ULift.up index) with
        | .function _ => False
        | .predicate predicate =>
            predicate.holds (finiteModelLiftArchitectureObject.{u} object)) :=
  Iff.rfl

/--
Every pair of lifted finite-model object families transports the selected
always-true invariant exactly in the sense of `Invariant.TransportedAlong`.
-/
theorem finiteModelLiftInvariantFamily_transportedAlong
    (index : finiteModelLiftInvariantFamily.{u}.Index)
    {parameter : Type v}
    (source target : parameter →
      ArchitectureObject finiteModelLiftCarrier.{u}) :
    Invariant.TransportedAlong
      (finiteModelLiftInvariantFamily.{u}.invariant index)
      (finiteModelLiftInvariantFamily.{u}.invariant index)
      source target := by
  rcases index with ⟨index⟩
  change ∀ _, True ↔ True
  exact fun _ => Iff.rfl

/-! ## Finite-model signature reading -/

/--
The lifted finite-model signature has the lifted singleton axis, lifted
natural-number coordinate, universally selected axis, and constant zero read.
-/
def finiteModelLiftArchitectureSignature :
    ArchitectureSignature finiteModelLiftCarrier.{u} where
  Axis := ULift.{u} PUnit.{1}
  Coordinate _ := ULift.{u} Nat
  selected _ := True
  coordinate _ _ := ULift.up 0

/-- Source and lifted finite-model axes have exactly the same selected status. -/
@[simp]
theorem finiteModelLiftArchitectureSignature_selected_iff
    (axis : FiniteModel.signature.Axis) :
    FiniteModel.signature.selected axis ↔
      finiteModelLiftArchitectureSignature.{u}.selected (ULift.up axis) :=
  Iff.rfl

/--
The lifted finite-model signature coordinate is the universe lift of the
source coordinate on every canonically lifted object and axis.
-/
@[simp]
theorem finiteModelLiftArchitectureSignature_coordinate
    (object : ArchitectureObject FiniteModel.carrier)
    (axis : FiniteModel.signature.Axis) :
    finiteModelLiftArchitectureSignature.{u}.coordinate
        (finiteModelLiftArchitectureObject.{u} object) (ULift.up axis) =
      ULift.up (FiniteModel.signature.coordinate object axis) :=
  rfl

/-! ## Finite-model operation reading -/

/--
The lifted finite-model operation reading selects every actual configuration
homomorphism, exactly as `FiniteModel.operationReading` does at the base
carrier.
-/
def finiteModelLiftOperationReading :
    OperationReading finiteModelLiftCarrier.{u} where
  Op source target :=
    ConfigurationHom source.configuration target.configuration
  configurationMap operation := operation

/--
Map a selected finite-model source operation to the lifted operation reading
using canonical configuration-hom rebasing.
-/
def finiteModelLiftOperation
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : FiniteModel.operationReading.Op source target) :
    finiteModelLiftOperationReading.{u}.Op
      (finiteModelLiftArchitectureObject.{u} source)
      (finiteModelLiftArchitectureObject.{u} target) :=
  finiteModelLiftConfigurationHom.{u}
    (FiniteModel.operationReading.configurationMap operation)

/--
The configuration map read from a lifted finite-model operation is exactly the
canonical lift of its source configuration map.
-/
@[simp]
theorem finiteModelLiftOperation_configurationMap
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : FiniteModel.operationReading.Op source target) :
    finiteModelLiftOperationReading.{u}.configurationMap
        (finiteModelLiftOperation.{u} operation) =
      finiteModelLiftConfigurationHom.{u}
        (FiniteModel.operationReading.configurationMap operation) :=
  rfl

/-! ## Finite-model semantic descent -/

/--
Read an arbitrary lifted architecture object through its complete reflected
configuration and rebuild the selected finite-model generated object.  Its
opaque auxiliary object fields are deliberately ignored.
-/
def finiteModelSemanticDescent
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    ArchitectureObject FiniteModel.carrier :=
  FiniteModel.objectOfConfiguration
    (finiteModelReflectAtomConfiguration.{u} object.configuration)

/-- Semantic descent exposes exactly the reflected lifted configuration. -/
@[simp]
theorem finiteModelSemanticDescent_configuration
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    (finiteModelSemanticDescent.{u} object).configuration =
      finiteModelReflectAtomConfiguration.{u} object.configuration :=
  rfl

/--
Descending a lifted finite-model generated object recovers its source
configuration exactly.
-/
@[simp]
theorem finiteModelSemanticDescent_liftObjectOfConfiguration_configuration
    (configuration : AtomConfiguration FiniteModel.carrier) :
    (finiteModelSemanticDescent.{u}
      (finiteModelLiftArchitectureObject.{u}
        (FiniteModel.objectOfConfiguration configuration))).configuration =
      configuration := by
  change finiteModelReflectAtomConfiguration.{u}
      (finiteModelLiftAtomConfiguration.{u} configuration) = configuration
  exact finiteModelReflectAtomConfiguration_lift.{u} configuration

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
