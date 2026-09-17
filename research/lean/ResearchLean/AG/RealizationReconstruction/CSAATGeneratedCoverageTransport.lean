import ResearchLean.AG.RealizationReconstruction.CSAATEndpointCoverageTransport
import ResearchLean.AG.RealizationReconstruction.CSAATExactOverlapTransport
import Formal.Util.AssertStandardAxioms

/-!
# Generated and package-level coverage transport

This file transports the concrete endpoint coverage proof through the same
generated-object provenance as the exact equation transport.  The only
non-definitional point is the global signature-axis action: it is represented
by two equality recursors.  We factor both through the signature `Axis` type
and use proof irrelevance only to identify equality proofs with identical
signature endpoints.  No coverage or coherence certificate is an input to the
final lens and protocol constructors.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u

def coreGeometrySignatureEq
    {U : AtomCarrier.{u}} {generated endpoint : ArchitectureObject U}
    (object_eq : generated = endpoint)
    (data : CSAATCoreGeometryData endpoint) :
    (object_eq.symm ▸ data).signature = data.signature := by
  cases object_eq
  rfl

def architectureSignatureAxisMapCast
    {U : AtomCarrier.{u}}
    {source sourceEndpoint target targetEndpoint : ArchitectureSignature U}
    (source_eq : source = sourceEndpoint)
    (target_eq : target = targetEndpoint)
    (axisMap : sourceEndpoint.Axis → targetEndpoint.Axis) :
    source.Axis → target.Axis := by
  cases source_eq
  cases target_eq
  exact axisMap

def coreGeometryAxisMapCast
    {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (sourceData : CSAATCoreGeometryData sourceEndpoint)
    (targetData : CSAATCoreGeometryData targetEndpoint)
    (axisMap : sourceData.signature.Axis → targetData.signature.Axis) :
    (source_eq.symm ▸ sourceData).signature.Axis →
      (target_eq.symm ▸ targetData).signature.Axis :=
  architectureSignatureAxisMapCast
    (coreGeometrySignatureEq source_eq sourceData)
    (coreGeometrySignatureEq target_eq targetData) axisMap

theorem signatureExactTransportCast_axisMap_eq_axisCast
    {U : AtomCarrier.{u}} {source target canonical : ArchitectureSignature U}
    (source_eq : source = canonical) (target_eq : target = canonical)
    (canonicalTransport : SignatureExactTransport canonical canonical) :
    (signatureExactTransportCast source_eq target_eq canonicalTransport).axisMap =
      architectureSignatureAxisMapCast source_eq target_eq
        canonicalTransport.axisMap := by
  cases source_eq
  cases target_eq
  rfl

noncomputable def coreGeometryCoverageTransportCast
    {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (sourceData : CSAATCoreGeometryData sourceEndpoint)
    (targetData : CSAATCoreGeometryData targetEndpoint)
    (atomEquiv : U.Atom ≃ U.Atom)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (axisMap : sourceData.signature.Axis → targetData.signature.Axis)
    (T : EquationSystemExactTransport
      sourceData.equationReading.equationSystem
      targetData.equationReading.equationSystem atomEquiv objectMap)
    (coverage : CoreGeometryCoverageTransport sourceData targetData axisMap T) :
    CoreGeometryCoverageTransport
      (source_eq.symm ▸ sourceData) (target_eq.symm ▸ targetData)
      (coreGeometryAxisMapCast source_eq target_eq sourceData targetData axisMap)
      (coreGeometryEquationTransportCast source_eq target_eq sourceData targetData
        atomEquiv objectMap T) := by
  cases source_eq
  cases target_eq
  exact coverage

noncomputable def lensIsoGeneratedCoreGeometryCoverageTransport
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    CoreGeometryCoverageTransport
      (lensAATCoreGeneratedGeometryData input X)
      (lensAATCoreGeneratedGeometryData input Y)
      (coreGeometryAxisMapCast
        (lensCoreGeneratedObject_eq_lawObject input X)
        (lensCoreGeneratedObject_eq_lawObject input Y)
        (lensAATCoreEndpointGeometryData input X)
        (lensAATCoreEndpointGeometryData input Y) id)
      (lensIsoGeneratedEquationTransport e) := by
  unfold lensAATCoreGeneratedGeometryData lensIsoGeneratedEquationTransport
  exact coreGeometryCoverageTransportCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    _ _ _ _ _ _ (lensIsoEndpointCoreGeometryCoverageTransport e)

noncomputable def protocolIsoGeneratedCoreGeometryCoverageTransport
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    CoreGeometryCoverageTransport
      (protocolAATCoreGeneratedGeometryData input X)
      (protocolAATCoreGeneratedGeometryData input Y)
      (coreGeometryAxisMapCast
        (protocolCoreGeneratedObject_eq_lawObject input X)
        (protocolCoreGeneratedObject_eq_lawObject input Y)
        (protocolAATCoreEndpointGeometryData input X)
        (protocolAATCoreEndpointGeometryData input Y) id)
      (protocolIsoGeneratedEquationTransport e) := by
  unfold protocolAATCoreGeneratedGeometryData protocolIsoGeneratedEquationTransport
  exact coreGeometryCoverageTransportCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    _ _ _ _ _ _ (protocolIsoEndpointCoreGeometryCoverageTransport e)

theorem lensIsoGeneratedAxisMap_eq
    {input : LensFamilyInput.{u}}
    (X Y : LensRealization input.View input.reference) :
    coreGeometryAxisMapCast
        (lensCoreGeneratedObject_eq_lawObject input X)
        (lensCoreGeneratedObject_eq_lawObject input Y)
        (lensAATCoreEndpointGeometryData input X)
        (lensAATCoreEndpointGeometryData input Y) id =
      (lensIsoSignatureTransport X Y).axisMap := by
  unfold coreGeometryAxisMapCast lensIsoSignatureTransport
  rw [signatureExactTransportCast_axisMap_eq_axisCast]
  have hs : coreGeometrySignatureEq
      (lensCoreGeneratedObject_eq_lawObject input X)
      (lensAATCoreEndpointGeometryData input X) =
      lensCoreSignature_eq input X := Subsingleton.elim _ _
  have ht : coreGeometrySignatureEq
      (lensCoreGeneratedObject_eq_lawObject input Y)
      (lensAATCoreEndpointGeometryData input Y) =
      lensCoreSignature_eq input Y := Subsingleton.elim _ _
  rw [hs, ht]
  rfl

theorem protocolIsoGeneratedAxisMap_eq
    {input : ProtocolFamilyInput.{u}}
    (X Y : ProtocolRealization input.schema input.observation) :
    coreGeometryAxisMapCast
        (protocolCoreGeneratedObject_eq_lawObject input X)
        (protocolCoreGeneratedObject_eq_lawObject input Y)
        (protocolAATCoreEndpointGeometryData input X)
        (protocolAATCoreEndpointGeometryData input Y) id =
      (protocolIsoSignatureTransport X Y).axisMap := by
  unfold coreGeometryAxisMapCast protocolIsoSignatureTransport
  rw [signatureExactTransportCast_axisMap_eq_axisCast]
  have hs : coreGeometrySignatureEq
      (protocolCoreGeneratedObject_eq_lawObject input X)
      (protocolAATCoreEndpointGeometryData input X) =
      protocolCoreSignature_eq input X := Subsingleton.elim _ _
  have ht : coreGeometrySignatureEq
      (protocolCoreGeneratedObject_eq_lawObject input Y)
      (protocolAATCoreEndpointGeometryData input Y) =
      protocolCoreSignature_eq input Y := Subsingleton.elim _ _
  rw [hs, ht]
  rfl

noncomputable def lensIsoGeneratedCoreGeometryCoverageTransportAuthoritative
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    CoreGeometryCoverageTransport
      (lensAATCoreGeneratedGeometryData input X)
      (lensAATCoreGeneratedGeometryData input Y)
      (lensIsoSignatureTransport X Y).axisMap
      (lensIsoGeneratedEquationTransport e) := by
  rw [← lensIsoGeneratedAxisMap_eq X Y]
  exact lensIsoGeneratedCoreGeometryCoverageTransport e

noncomputable def protocolIsoGeneratedCoreGeometryCoverageTransportAuthoritative
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    CoreGeometryCoverageTransport
      (protocolAATCoreGeneratedGeometryData input X)
      (protocolAATCoreGeneratedGeometryData input Y)
      (protocolIsoSignatureTransport X Y).axisMap
      (protocolIsoGeneratedEquationTransport e) := by
  rw [← protocolIsoGeneratedAxisMap_eq X Y]
  exact protocolIsoGeneratedCoreGeometryCoverageTransport e

/-- Authoritative package-level lens coverage, constructed from the primitive
isomorphism and the concrete endpoint proof. -/
noncomputable def lensIsoCoverageTransport
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    CoverageTransport (lensAATReadingCore input X) (lensAATReadingCore input Y)
      (lensIsoPackageTotalHom e) where
  requiredSupport :=
    (lensIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).requiredSupport
  requiredEquationCoordinate :=
    (lensIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).requiredEquationCoordinate
  selectedViolationWitness :=
    (lensIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).selectedViolationWitness
  requiredAxis :=
    (lensIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).requiredAxis
  supportVisibleOn :=
    (lensIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).supportVisibleOn
  equationCoordinateVisibleOn :=
    (lensIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).equationCoordinateVisibleOn
  violationWitnessVisibleOn :=
    (lensIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).violationWitnessVisibleOn
  axisReadableOn :=
    (lensIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).axisReadableOn
  boundaryVisibleOn :=
    (lensIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).boundaryVisibleOn

/-- Authoritative package-level protocol coverage, constructed from the
primitive isomorphism and the concrete endpoint proof. -/
noncomputable def protocolIsoCoverageTransport
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    CoverageTransport (protocolAATReadingCore input X)
      (protocolAATReadingCore input Y) (protocolIsoPackageTotalHom e) where
  requiredSupport :=
    (protocolIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).requiredSupport
  requiredEquationCoordinate :=
    (protocolIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).requiredEquationCoordinate
  selectedViolationWitness :=
    (protocolIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).selectedViolationWitness
  requiredAxis :=
    (protocolIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).requiredAxis
  supportVisibleOn :=
    (protocolIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).supportVisibleOn
  equationCoordinateVisibleOn :=
    (protocolIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).equationCoordinateVisibleOn
  violationWitnessVisibleOn :=
    (protocolIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).violationWitnessVisibleOn
  axisReadableOn :=
    (protocolIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).axisReadableOn
  boundaryVisibleOn :=
    (protocolIsoGeneratedCoreGeometryCoverageTransportAuthoritative e).boundaryVisibleOn

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
