import ResearchLean.AG.RealizationReconstruction.CSAATGeneratedEquationTransport
import Formal.Util.AssertStandardAxioms

/-!
# Complete signed exact cores for genuine CS isomorphisms

For both lens and protocol semantics, every field of `SignedExactCoreReadingHom`
is constructed from the fixed input and a genuine semantic isomorphism.  The
construction preserves extraction and composition; arbitrary-object formation,
configuration, equations, and operations; reject detectors; empty invariants;
and the complete signature axes and coordinates.

Detector and signature facts are projected from the dependent Sigma equality
between source-generated and endpoint geometry data.  The generic signature
cast helper is conditional on a canonical signature transport; the exported CS
constructors build and supply that transport and accept no completed core hom,
base hom, or certificate.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

def lensIsoConfigurationMap
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (A : ArchitectureObject (lensAATCarrier input)) :
    ConfigurationHom A.configuration (lensIsoObjectMap e A).configuration where
  atomMap := id
  maps_family h := by
    rw [lensIsoObjectMap_configuration_eq e A]
    exact h
  maps_relation h := by
    rw [lensIsoObjectMap_configuration_eq e A]
    exact h
  maps_identification h := by
    rw [lensIsoObjectMap_configuration_eq e A]
    exact h

def lensIsoOperationMap
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    {A B : ArchitectureObject (lensAATCarrier input)}
    (op : ConfigurationHom A.configuration B.configuration) :
    ConfigurationHom (lensIsoObjectMap e A).configuration
      (lensIsoObjectMap e B).configuration where
  atomMap := op.atomMap
  maps_family h := by
    rw [lensIsoObjectMap_configuration_eq e A] at h
    rw [lensIsoObjectMap_configuration_eq e B]
    exact op.maps_family h
  maps_relation h := by
    rw [lensIsoObjectMap_configuration_eq e A] at h
    rw [lensIsoObjectMap_configuration_eq e B]
    exact op.maps_relation h
  maps_identification h := by
    rw [lensIsoObjectMap_configuration_eq e A] at h
    rw [lensIsoObjectMap_configuration_eq e B]
    exact op.maps_identification h

theorem lensIsoConfigurationMap_atomMap
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (A : ArchitectureObject (lensAATCarrier input)) :
    (lensIsoConfigurationMap e A).atomMap = id := by
  rfl

theorem lensIsoOperationMap_atomMap
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    {A B : ArchitectureObject (lensAATCarrier input)}
    (op : ConfigurationHom A.configuration B.configuration) :
    (lensIsoOperationMap e op).atomMap = op.atomMap := by
  rfl

theorem lensCoreGeometrySigma_eq
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    Sigma.mk _ (lensAATCoreGeneratedGeometryData input X) =
      Sigma.mk _ (lensAATCoreEndpointGeometryData input X) :=
  Sigma.ext (lensCoreGeneratedObject_eq_lawObject input X)
    (lensAATCoreGeneratedGeometryData_heq input X)

theorem lensCoreCircuitCode_reject
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference)
    (index : (lensAATCorePackage input X).algebra.equationSystem.Index) :
    (lensAATCorePackage input X).algebra.circuits.code index = .reject := by
  change (lensAATCoreGeneratedGeometryData input X).equationReading.circuits.code index =
    .reject
  have property_eq := congrArg
    (fun pair : Σ A, CSAATCoreGeometryData A =>
      ∀ i, pair.2.equationReading.circuits.code i = CircuitDetectorCode.reject)
    (lensCoreGeometrySigma_eq input X)
  have endpoint_property :
      ∀ i, (lensAATCoreEndpointGeometryData input X).equationReading.circuits.code i =
        CircuitDetectorCode.reject := by
    intro i
    rfl
  exact (Eq.mpr property_eq endpoint_property) index

theorem lensCoreSignature_eq
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensAATCorePackage input X).reading.signatureReading =
      lensAATGeometrySignature input := by
  change (lensAATCoreGeneratedGeometryData input X).signature =
    (lensAATCoreEndpointGeometryData input X).signature
  exact congrArg
    (fun pair : Σ A, CSAATCoreGeometryData A => pair.2.signature)
    (lensCoreGeometrySigma_eq input X)

structure SignatureExactTransport {U : AtomCarrier.{u}}
    (source target : ArchitectureSignature U) where
  axisMap : source.Axis → target.Axis
  coordinateEquiv : ∀ axis,
    source.Coordinate axis ≃ target.Coordinate (axisMap axis)
  axis_selected_iff : ∀ axis,
    source.selected axis ↔ target.selected (axisMap axis)
  coordinate_eq : ∀ A B axis,
    coordinateEquiv axis (source.coordinate A axis) =
      target.coordinate B (axisMap axis)

def signatureExactTransportCast {U : AtomCarrier.{u}}
    {source target canonical : ArchitectureSignature U}
    (source_eq : source = canonical) (target_eq : target = canonical)
    (canonicalTransport : SignatureExactTransport canonical canonical) :
    SignatureExactTransport source target := by
  cases source_eq
  cases target_eq
  exact canonicalTransport

def lensCanonicalSignatureTransport (input : LensFamilyInput.{u}) :
    SignatureExactTransport (lensAATGeometrySignature input)
      (lensAATGeometrySignature input) where
  axisMap := id
  coordinateEquiv := fun _ => Equiv.refl _
  axis_selected_iff := fun _ => Iff.rfl
  coordinate_eq := fun _ _ _ => rfl

def lensIsoSignatureTransport
    {input : LensFamilyInput.{u}}
    (X Y : LensRealization input.View input.reference) :
    SignatureExactTransport
      (lensAATCorePackage input X).reading.signatureReading
      (lensAATCorePackage input Y).reading.signatureReading :=
  signatureExactTransportCast
    (lensCoreSignature_eq input X) (lensCoreSignature_eq input Y)
    (lensCanonicalSignatureTransport input)

noncomputable def lensIsoSignedExactCoreReadingHom
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    SignedExactCoreReadingHom
      (lensAATCorePackage input X) (lensAATCorePackage input Y) where
  atomEquiv := Equiv.refl _
  extraction_eq := lensCore_extraction_eq X Y
  composition_eq := lensCore_composition_eq X Y
  objectMap := lensIsoObjectMap e
  object_formation_eq := by
    intro C
    simpa using lensIsoObjectMap_object_formation_eq e C
  configurationMap := lensIsoConfigurationMap e
  configurationMap_atomMap := by
    intro A
    exact lensIsoConfigurationMap_atomMap e A
  configuration_eq := by
    intro A
    simpa using lensIsoObjectMap_configuration_eq e A
  equationTransport := lensIsoGeneratedEquationTransport e
  detectorCode_eq := by
    intro index
    rw [lensCoreCircuitCode_reject, lensCoreCircuitCode_reject]
    rfl
  operationMap := fun op => lensIsoOperationMap e op
  operation_naturality := by
    intro A B op
    apply ConfigurationHom.ext
    change (lensIsoOperationMap e op).atomMap ∘
        (lensIsoConfigurationMap e A).atomMap =
      (lensIsoConfigurationMap e B).atomMap ∘ op.atomMap
    rw [lensIsoOperationMap_atomMap,
      lensIsoConfigurationMap_atomMap, lensIsoConfigurationMap_atomMap]
    rfl
  invariantMap := fun index => PEmpty.elim index
  invariant_transport := by
    intro index
    exact PEmpty.elim index
  axisMap := (lensIsoSignatureTransport X Y).axisMap
  coordinateEquiv := (lensIsoSignatureTransport X Y).coordinateEquiv
  axis_selected_iff := (lensIsoSignatureTransport X Y).axis_selected_iff
  coordinate_eq := by
    intro A axis
    exact (lensIsoSignatureTransport X Y).coordinate_eq A (lensIsoObjectMap e A) axis

theorem protocolCore_extraction_eq
    {input : ProtocolFamilyInput.{u}}
    (X Y : ProtocolRealization input.schema input.observation) :
    (protocolAATCorePackage input Y).family =
      (protocolAATCorePackage input X).family.transport (Equiv.refl _) := by
  apply AtomFamily.ext
  intro atom
  dsimp only [protocolAATCorePackage, AATCorePackage.generate,
    AATCorePackage.family, protocolAATCoreReading,
    ExtractionDoctrine.atomize, AtomFamily.transport]
  simp [ExtractionDoctrine.extracts, protocolAATExtractionDoctrine,
    protocolAATExtracts]

theorem protocolCore_composition_eq
    {input : ProtocolFamilyInput.{u}}
    (X Y : ProtocolRealization input.schema input.observation)
    (F : AtomFamily (protocolAATCarrier input)) (hF : F.ListFinite) :
    (protocolAATCorePackage input Y).reading.composition.compose
        (F.transport (Equiv.refl _)) (hF.transport (Equiv.refl _)) =
      ((protocolAATCorePackage input X).reading.composition.compose F hF).transport
        (Equiv.refl _) := by
  change supportedPointConfiguration (F.transport (Equiv.refl _)) .point =
    (supportedPointConfiguration F .point).transport (Equiv.refl _)
  apply AtomConfiguration.ext
  · apply AtomFamily.ext
    intro atom
    simp [AtomFamily.transport]
  · intro source target
    simp [supportedPointConfiguration, AtomConfiguration.transport,
      AtomFamily.transport]
  · intro source target
    simp [supportedPointConfiguration, AtomConfiguration.transport]

def protocolIsoConfigurationMap
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (A : ArchitectureObject (protocolAATCarrier input)) :
    ConfigurationHom A.configuration (protocolIsoObjectMap e A).configuration where
  atomMap := id
  maps_family h := by rw [protocolIsoObjectMap_configuration_eq e A]; exact h
  maps_relation h := by rw [protocolIsoObjectMap_configuration_eq e A]; exact h
  maps_identification h := by rw [protocolIsoObjectMap_configuration_eq e A]; exact h

def protocolIsoOperationMap
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    {A B : ArchitectureObject (protocolAATCarrier input)}
    (op : ConfigurationHom A.configuration B.configuration) :
    ConfigurationHom (protocolIsoObjectMap e A).configuration
      (protocolIsoObjectMap e B).configuration where
  atomMap := op.atomMap
  maps_family h := by
    rw [protocolIsoObjectMap_configuration_eq e A] at h
    rw [protocolIsoObjectMap_configuration_eq e B]
    exact op.maps_family h
  maps_relation h := by
    rw [protocolIsoObjectMap_configuration_eq e A] at h
    rw [protocolIsoObjectMap_configuration_eq e B]
    exact op.maps_relation h
  maps_identification h := by
    rw [protocolIsoObjectMap_configuration_eq e A] at h
    rw [protocolIsoObjectMap_configuration_eq e B]
    exact op.maps_identification h

theorem protocolCoreGeometrySigma_eq
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    Sigma.mk _ (protocolAATCoreGeneratedGeometryData input X) =
      Sigma.mk _ (protocolAATCoreEndpointGeometryData input X) :=
  Sigma.ext (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolAATCoreGeneratedGeometryData_heq input X)

theorem protocolCoreCircuitCode_reject
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    (index : (protocolAATCorePackage input X).algebra.equationSystem.Index) :
    (protocolAATCorePackage input X).algebra.circuits.code index = .reject := by
  change (protocolAATCoreGeneratedGeometryData input X).equationReading.circuits.code
    index = .reject
  have property_eq := congrArg
    (fun pair : Σ A, CSAATCoreGeometryData A =>
      ∀ i, pair.2.equationReading.circuits.code i = CircuitDetectorCode.reject)
    (protocolCoreGeometrySigma_eq input X)
  have endpoint_property :
      ∀ i, (protocolAATCoreEndpointGeometryData input X).equationReading.circuits.code
        i = CircuitDetectorCode.reject := by intro i; rfl
  exact (Eq.mpr property_eq endpoint_property) index

theorem protocolCoreSignature_eq
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    (protocolAATCorePackage input X).reading.signatureReading =
      protocolAATGeometrySignature input := by
  change (protocolAATCoreGeneratedGeometryData input X).signature =
    (protocolAATCoreEndpointGeometryData input X).signature
  exact congrArg (fun pair : Σ A, CSAATCoreGeometryData A => pair.2.signature)
    (protocolCoreGeometrySigma_eq input X)

def protocolCanonicalSignatureTransport (input : ProtocolFamilyInput.{u}) :
    SignatureExactTransport (protocolAATGeometrySignature input)
      (protocolAATGeometrySignature input) where
  axisMap := id
  coordinateEquiv := fun _ => Equiv.refl _
  axis_selected_iff := fun _ => Iff.rfl
  coordinate_eq := fun _ _ _ => rfl

def protocolIsoSignatureTransport
    {input : ProtocolFamilyInput.{u}}
    (X Y : ProtocolRealization input.schema input.observation) :
    SignatureExactTransport
      (protocolAATCorePackage input X).reading.signatureReading
      (protocolAATCorePackage input Y).reading.signatureReading :=
  signatureExactTransportCast
    (protocolCoreSignature_eq input X) (protocolCoreSignature_eq input Y)
    (protocolCanonicalSignatureTransport input)

noncomputable def protocolIsoSignedExactCoreReadingHom
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    SignedExactCoreReadingHom
      (protocolAATCorePackage input X) (protocolAATCorePackage input Y) where
  atomEquiv := Equiv.refl _
  extraction_eq := protocolCore_extraction_eq X Y
  composition_eq := protocolCore_composition_eq X Y
  objectMap := protocolIsoObjectMap e
  object_formation_eq := by
    intro C
    simpa using protocolIsoObjectMap_object_formation_eq e C
  configurationMap := protocolIsoConfigurationMap e
  configurationMap_atomMap := by intro A; rfl
  configuration_eq := by
    intro A
    simpa using protocolIsoObjectMap_configuration_eq e A
  equationTransport := protocolIsoGeneratedEquationTransport e
  detectorCode_eq := by
    intro index
    rw [protocolCoreCircuitCode_reject, protocolCoreCircuitCode_reject]
    rfl
  operationMap := fun op => protocolIsoOperationMap e op
  operation_naturality := by
    intro A B op
    apply ConfigurationHom.ext
    change (protocolIsoOperationMap e op).atomMap ∘
        (protocolIsoConfigurationMap e A).atomMap =
      (protocolIsoConfigurationMap e B).atomMap ∘ op.atomMap
    rfl
  invariantMap := fun index => PEmpty.elim index
  invariant_transport := by intro index; exact PEmpty.elim index
  axisMap := (protocolIsoSignatureTransport X Y).axisMap
  coordinateEquiv := (protocolIsoSignatureTransport X Y).coordinateEquiv
  axis_selected_iff := (protocolIsoSignatureTransport X Y).axis_selected_iff
  coordinate_eq := by
    intro A axis
    exact (protocolIsoSignatureTransport X Y).coordinate_eq A
      (protocolIsoObjectMap e A) axis

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
