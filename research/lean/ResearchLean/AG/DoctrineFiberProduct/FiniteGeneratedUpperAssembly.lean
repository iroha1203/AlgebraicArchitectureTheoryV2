import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperStructuralLawDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedDetectorLawDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedOperationNaturalityDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedInvariantSignatureLawDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationTransportDescent

/-!
# Complete generated upper assembly

This module assembles the exact low `SignedExactCoreReadingHom` between the
outer and inner generated domains.  Its eight data fields are the accepted
Cycle 18--23 reflected producers, and its ten proof fields are the accepted
pointwise Atom graph and the nine actual-high-derived Cycle 24 laws.

The output alias contains only the two low endpoints.  The supplied high lift
occurs on the producer because it generates every reflected field, but it is
not an index of the existing `SignedExactCoreReadingHom` output type.  No
additional law packet, image certificate, or completed low upper is accepted.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Exact output and producer -/

/--
The existing exact signed-reading hom type between the two generated low
domains.  This alias records the required output without adding a certificate
or placing the supplied high lift in a type that does not depend on it.
-/
abbrev FiniteGeneratedReflectedSignedExactCoreReadingHomOutput
    (input : FiniteGeneratedLiftInput)
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :=
  SignedExactCoreReadingHom
    (finiteGeneratedOuterInput input base).lowGeneratedLift.domain
    input.lowGeneratedLift.domain

/--
Assemble all eighteen fields of the generated low signed-reading hom directly
from the reflected actual-high producers.  The sole function-level conversion
is `funext` from the accepted pointwise configuration Atom graph.
-/
noncomputable def finiteGeneratedReflectedSignedExactCoreReadingHom
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    FiniteGeneratedReflectedSignedExactCoreReadingHomOutput input base where
  atomEquiv :=
    finiteGeneratedReflectedUpperAtomEquiv input lift base
  extraction_eq :=
    finiteGeneratedReflectedExtraction_eq input lift base
  composition_eq :=
    finiteGeneratedReflectedComposition_eq input lift base
  objectMap :=
    finiteGeneratedReflectedArchitectureObject input lift base
  object_formation_eq :=
    finiteGeneratedReflectedObjectFormation_eq input lift base
  configurationMap :=
    finiteGeneratedReflectedConfigurationMap input lift base
  configurationMap_atomMap object := by
    funext atom
    exact finiteGeneratedReflectedConfigurationMap_atom_graph
      input lift base object atom
  configuration_eq :=
    finiteGeneratedReflectedConfiguration_eq input lift base
  equationTransport :=
    finiteGeneratedReflectedEquationSystemExactTransport input lift base
  detectorCode_eq :=
    finiteGeneratedReflectedDetectorCode_eq input lift base
  operationMap :=
    finiteGeneratedReflectedOperationMap input lift base
  operation_naturality :=
    finiteGeneratedReflectedOperationMap_naturality input lift base
  invariantMap :=
    finiteGeneratedReflectedInvariantMap input lift base
  invariant_transport :=
    finiteGeneratedReflectedInvariant_transport input lift base
  axisMap :=
    finiteGeneratedReflectedAxisMap input lift base
  coordinateEquiv :=
    finiteGeneratedReflectedCoordinateEquiv input lift base
  axis_selected_iff :=
    finiteGeneratedReflectedAxis_selected_iff input lift base
  coordinate_eq :=
    finiteGeneratedReflectedCoordinate_eq input lift base

/-! ## Public data-field projections -/

/-- The assembled Atom equivalence is the reflected actual-high Atom field. -/
@[simp]
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_atomEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).atomEquiv =
      finiteGeneratedReflectedUpperAtomEquiv input lift base :=
  rfl

/-- The assembled hom carries the reflected complete architecture-object map. -/
@[simp]
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_objectMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).objectMap object =
      finiteGeneratedReflectedArchitectureObject input lift base object :=
  rfl

/-- The assembled configuration component is the reflected actual-high map. -/
@[simp]
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_configurationMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).configurationMap object =
      finiteGeneratedReflectedConfigurationMap input lift base object :=
  rfl

/-- The assembled equation component is the complete reflected exact transport. -/
@[simp]
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_equationTransport
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).equationTransport =
      finiteGeneratedReflectedEquationSystemExactTransport input lift base :=
  rfl

/-- The assembled operation component is the reflected actual-high operation map. -/
@[simp]
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_operationMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.Op
      source target) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).operationMap operation =
      finiteGeneratedReflectedOperationMap input lift base operation :=
  rfl

/-- The assembled invariant-index component is the reflected actual-high map. -/
@[simp]
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_invariantMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.invariantReading.Index) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).invariantMap index =
      finiteGeneratedReflectedInvariantMap input lift base index :=
  rfl

/-- The assembled signature-axis component is the reflected actual-high map. -/
@[simp]
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_axisMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).axisMap axis =
      finiteGeneratedReflectedAxisMap input lift base axis :=
  rfl

/-- The assembled dependent coordinate component is the reflected equivalence. -/
@[simp]
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_coordinateEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).coordinateEquiv axis =
      finiteGeneratedReflectedCoordinateEquiv input lift base axis :=
  rfl

/-! ## Public proof-field projections -/

/-- The assembled hom exposes exact generated-family transport. -/
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_extraction_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    input.lowGeneratedLift.domain.family =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.family.transport
        (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).atomEquiv :=
  (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).extraction_eq

/-- The assembled hom exposes composition transport for every finite family. -/
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_composition_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (family : AtomFamily FiniteModel.carrier)
    (hfinite : family.ListFinite) :
    input.lowGeneratedLift.domain.reading.composition.compose
        (family.transport
          (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).atomEquiv)
        (hfinite.transport
          (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).atomEquiv) =
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.composition.compose
        family hfinite).transport
          (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).atomEquiv :=
  (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).composition_eq
    family hfinite

/-- The assembled complete object map commutes with generated object formation. -/
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_object_formation_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (configuration : AtomConfiguration FiniteModel.carrier) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).objectMap
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.objectReading.object
          configuration) =
      input.lowGeneratedLift.domain.reading.objectReading.object
        (configuration.transport
          (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).atomEquiv) :=
  (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).object_formation_eq
    configuration

/-- Every assembled configuration map uses the assembled Atom equivalence. -/
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_configurationMap_atomMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).configurationMap
      object).atomMap =
        (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).atomEquiv :=
  (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).configurationMap_atomMap
    object

/-- The assembled object configuration is exact transport along its Atom field. -/
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_configuration_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).objectMap
      object).configuration =
        object.configuration.transport
          (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).atomEquiv :=
  (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).configuration_eq
    object

/-- The assembled equation map transports every generated detector code. -/
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_detectorCode_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index) :
    input.lowGeneratedLift.domain.algebra.circuits.code
        ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).equationMap index) =
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.circuits.code
        index).transport
          (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).atomEquiv :=
  (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).detectorCode_eq
    index

/-- The assembled operation map is natural with respect to configuration maps. -/
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_operation_naturality
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
          ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).operationMap operation))
        ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).configurationMap source) =
      ConfigurationHom.comp
        ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).configurationMap target)
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.operationReading.configurationMap
          operation) :=
  (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).operation_naturality
    operation

/-- The assembled invariant map transports every generated invariant. -/
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_invariant_transport
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.invariantReading.Index) :
    Invariant.TransportedAlong
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.invariantReading.invariant
        index)
      (input.lowGeneratedLift.domain.reading.invariantReading.invariant
        ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).invariantMap index))
      _root_.id
      (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).objectMap :=
  (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).invariant_transport
    index

/-- The assembled axis map preserves and reflects selected status. -/
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_axis_selected_iff
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis) :
    (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.selected
        axis ↔
      input.lowGeneratedLift.domain.reading.signatureReading.selected
        ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).axisMap axis) :=
  (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).axis_selected_iff
    axis

/-- The assembled coordinate equivalence commutes with every generated read. -/
theorem finiteGeneratedReflectedSignedExactCoreReadingHom_coordinate_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier)
    (axis : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.Axis) :
    (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).coordinateEquiv axis
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.signatureReading.coordinate
          object axis) =
      input.lowGeneratedLift.domain.reading.signatureReading.coordinate
        ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).objectMap object)
        ((finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).axisMap axis) :=
  (finiteGeneratedReflectedSignedExactCoreReadingHom input lift base).coordinate_eq
    object axis

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
