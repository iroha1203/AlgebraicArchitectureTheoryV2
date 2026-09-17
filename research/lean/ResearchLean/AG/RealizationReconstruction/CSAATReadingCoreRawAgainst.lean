import ResearchLean.AG.RealizationReconstruction.CSAATGenuineIsoRawAgainst
import Formal.Util.AssertStandardAxioms

/-!
# Genuine-CS raw maps on source-generated ReadingCores

This module projects the dependent endpoint provenance stored by the generated
lens and protocol cores into equivalences of their complete equation-coordinate
types.  It conjugates genuine semantic Law-coordinate transport by those
endpoint equivalences and instantiates the target-indexed exact raw map against
the inverse context functor of any subsequently constructed core-package map.

No core map, coverage, overlap, realization supply, or completed geometry map
is constructed or claimed here.  The `baseHom` parameter only supplies the
inverse context functor required by the exact-geometry raw interface.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u

/-! ## Project generated endpoint provenance to complete coordinates -/

/-- The equation coordinates of the source-generated lens ReadingCore are
equivalent to the complete Law-index/Atom family of the original lens. -/
noncomputable def lensReadingCoreCoordinateEquivEndpoint
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensAATReadingCore input X).site.equationSystem.Coordinate ≃
      (ULift.{u + 1, u} (LensLawIndex input.View X.Carrier) ×
        LensAATAtom input) := by
  have hSigma :
      Sigma.mk _ (lensAATCoreGeneratedGeometryData input X) =
        Sigma.mk _ (lensAATCoreEndpointGeometryData input X) :=
    Sigma.ext (lensCoreGeneratedObject_eq_lawObject input X)
      (lensAATCoreGeneratedGeometryData_heq input X)
  have hIndex := congrArg
    (fun pair : Σ A, CSAATCoreGeometryData A =>
      pair.2.equationReading.equationSystem.Index) hSigma
  exact Equiv.cast
    (congrArg (fun Index => Index × LensAATAtom input) hIndex)

/-- The equation coordinates of the source-generated protocol ReadingCore are
equivalent to every relation/observation Law index paired with every Atom. -/
noncomputable def protocolReadingCoreCoordinateEquivEndpoint
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    (protocolAATReadingCore input X).site.equationSystem.Coordinate ≃
      (ULift.{u + 1, u} (ProtocolLawIndex X.State) ×
        ProtocolAATAtom input) := by
  have hSigma :
      Sigma.mk _ (protocolAATCoreGeneratedGeometryData input X) =
        Sigma.mk _ (protocolAATCoreEndpointGeometryData input X) :=
    Sigma.ext (protocolCoreGeneratedObject_eq_lawObject input X)
      (protocolAATCoreGeneratedGeometryData_heq input X)
  have hIndex := congrArg
    (fun pair : Σ A, CSAATCoreGeometryData A =>
      pair.2.equationReading.equationSystem.Index) hSigma
  exact Equiv.cast
    (congrArg (fun Index => Index × ProtocolAATAtom input) hIndex)

/-! ## Genuine isomorphism action on generated ReadingCore coordinates -/

/-- Genuine lens transport on generated ReadingCore coordinates, obtained by
conjugating the complete semantic Law-coordinate action by endpoint provenance. -/
noncomputable def lensIsoReadingCoreCoordinateEquiv
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    (lensAATReadingCore input X).site.equationSystem.Coordinate ≃
      (lensAATReadingCore input Y).site.equationSystem.Coordinate :=
  (lensReadingCoreCoordinateEquivEndpoint input X).trans
    ((lensIsoLawCoordinateIndexEquiv e).trans
      (lensReadingCoreCoordinateEquivEndpoint input Y).symm)

/-- Genuine protocol transport on generated ReadingCore coordinates, retaining
every relation/observation index and every Atom. -/
noncomputable def protocolIsoReadingCoreCoordinateEquiv
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    (protocolAATReadingCore input X).site.equationSystem.Coordinate ≃
      (protocolAATReadingCore input Y).site.equationSystem.Coordinate :=
  (protocolReadingCoreCoordinateEquivEndpoint input X).trans
    ((protocolIsoLawCoordinateIndexEquiv e).trans
      (protocolReadingCoreCoordinateEquivEndpoint input Y).symm)

/-! ## Exact raw maps against a later constructed core base -/

/-- The actual source-generated lens ReadingCores carry the genuine coordinate
action against the inverse context functor selected by a core base. -/
noncomputable def lensIsoReadingCoreRawExactMapAgainst
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (baseHom : PackageTotalHom
      (lensAATReadingCore input X).core
      (lensAATReadingCore input Y).core) :
    RawAmbientRestrictionSystemExactMapAgainst
      (lensAATReadingCore input X).site
      (lensAATReadingCore input Y).site
      (coreContextInverse baseHom) (RingHom.id Int)
      (lensAATReadingCore input X).raw
      (lensAATReadingCore input Y).raw :=
  equationCoordinateRawExactMapAgainst _ _ _
    (lensIsoReadingCoreCoordinateEquiv e)

/-- The actual source-generated protocol ReadingCores carry the genuine
relation/observation coordinate action against the selected core base. -/
noncomputable def protocolIsoReadingCoreRawExactMapAgainst
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y)
    (baseHom : PackageTotalHom
      (protocolAATReadingCore input X).core
      (protocolAATReadingCore input Y).core) :
    RawAmbientRestrictionSystemExactMapAgainst
      (protocolAATReadingCore input X).site
      (protocolAATReadingCore input Y).site
      (coreContextInverse baseHom) (RingHom.id Int)
      (protocolAATReadingCore input X).raw
      (protocolAATReadingCore input Y).raw :=
  equationCoordinateRawExactMapAgainst _ _ _
    (protocolIsoReadingCoreCoordinateEquiv e)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
