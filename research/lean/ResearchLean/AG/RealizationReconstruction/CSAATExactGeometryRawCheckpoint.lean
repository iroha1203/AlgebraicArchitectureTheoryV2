import ResearchLean.AG.RealizationReconstruction.CSAATPackageTotalIso
import ResearchLean.AG.RealizationReconstruction.CSAATReadingCoreRawAgainst
import ResearchLean.AG.RealizationReconstruction.CSAATExactGeometryMorphisms
import Formal.Util.AssertStandardAxioms

/-!
# Exact-geometry base, coefficient, and typed-raw checkpoint

For both genuine CS isomorphisms, the complete package base, coefficient map,
and full typed raw action are now constructed from the fixed inputs.  This
checkpoint deliberately does not contain coverage, overlap, or realization
fields: those remain proof obligations whose generated-geometry provenance
must be exposed before an `ExactGeomReadHom` can be assembled.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u v

/-- The three already constructed computational components of an exact
geometry morphism.  No missing geometry component is accepted as a field. -/
structure ExactGeometryRawCheckpoint {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  base : PackageTotalHom G.core H.core
  coefficientHom : G.Coefficient →+* H.Coefficient
  raw : RawAmbientRestrictionSystemExactMapAgainst G.site H.site
    (coreContextInverse base) coefficientHom G.raw H.raw

/-- Lens checkpoint with the genuine package base, identity integer
coefficient action, and complete Law-index-times-Atom raw action. -/
noncomputable def lensIsoExactGeometryRawCheckpoint
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    ExactGeometryRawCheckpoint (lensAATReadingCore input X)
      (lensAATReadingCore input Y) where
  base := lensIsoPackageTotalHom e
  coefficientHom := RingHom.id Int
  raw := lensIsoReadingCoreRawExactMapAgainst e (lensIsoPackageTotalHom e)

/-- Protocol checkpoint with the genuine package base, identity integer
coefficient action, and complete relation/observation-index-times-Atom raw
action. -/
noncomputable def protocolIsoExactGeometryRawCheckpoint
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    ExactGeometryRawCheckpoint (protocolAATReadingCore input X)
      (protocolAATReadingCore input Y) where
  base := protocolIsoPackageTotalHom e
  coefficientHom := RingHom.id Int
  raw := protocolIsoReadingCoreRawExactMapAgainst e (protocolIsoPackageTotalHom e)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
