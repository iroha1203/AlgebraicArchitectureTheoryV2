import ResearchLean.AG.RealizationReconstruction.CSAATGeneratedDirectedCoverageOverlap
import ResearchLean.AG.RealizationReconstruction.CSAATGeneratedSelectedExtension
import Formal.Util.AssertStandardAxioms

/-!
# One-way generated ReadingCore packages for the two CS semantics

All geometry fields below are typed on the same generated source and target
cores and are constructed from one primitive CS morphism.  The package remains
directed: it has no inverse, target-wide coverage, or whole-Extension map.  It
also does not claim independent readback; the structure is still indexed by
the primitive morphism whose fields will be separated in the next layer.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

structure LensAATGeneratedDirectedPackage
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) where
  equation : GeneratedEquationForwardTransport
    (lensAATReadingCore input X).site.equationSystem
    (lensAATReadingCore input Y).site.equationSystem
  raw : (lensAATReadingCore input X).raw.toPresheaf ⟶
    (lensAATReadingCoreForwardContextFunctor input f).op ⋙
      (lensAATReadingCore input Y).raw.toPresheaf
  coverage : GeneratedForwardCoverageImage
    (lensAATCoreGeneratedGeometryData input X)
    (lensAATCoreGeneratedGeometryData input Y)
    (lensAATReadingCoreForwardContextFunctor input f)
    (lensAATReadingCoreForwardCoverageLabels input f)
  overlap : GeneratedForwardOverlapReadable
    (lensAATCoreGeneratedGeometryData input X)
    (lensAATCoreGeneratedGeometryData input Y)
    (lensAATReadingCoreForwardContextFunctor input f)
  extension : LensAATGeneratedExtensionCoherence input f

/-- Construct the whole generated lens package from the same primitive
state/get/put-preserving morphism. -/
noncomputable def lensAATGeneratedDirectedPackage
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensAATGeneratedDirectedPackage input f where
  equation := lensAATReadingCoreEquationForwardTransport input f
  raw := lensAATReadingCoreRawForwardHom input f
  coverage := lensAATReadingCoreForwardCoverageImageGeneric input f
  overlap := lensAATReadingCoreForwardOverlapReadable input f
  extension := lensAATGeneratedExtensionCoherence input f

structure ProtocolAATGeneratedDirectedPackage
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) where
  equation : GeneratedEquationForwardTransport
    (protocolAATReadingCore input X).site.equationSystem
    (protocolAATReadingCore input Y).site.equationSystem
  raw : (protocolAATReadingCore input X).raw.toPresheaf ⟶
    (protocolAATReadingCoreForwardContextFunctor input f).op ⋙
      (protocolAATReadingCore input Y).raw.toPresheaf
  coverage : GeneratedForwardCoverageImage
    (protocolAATCoreGeneratedGeometryData input X)
    (protocolAATCoreGeneratedGeometryData input Y)
    (protocolAATReadingCoreForwardContextFunctor input f)
    (protocolAATReadingCoreForwardCoverageLabels input f)
  overlap : GeneratedForwardOverlapReadable
    (protocolAATCoreGeneratedGeometryData input X)
    (protocolAATCoreGeneratedGeometryData input Y)
    (protocolAATReadingCoreForwardContextFunctor input f)
  extension : ProtocolAATGeneratedExtensionCoherence input f

/-- Construct the whole generated protocol package from the same primitive
vertexwise state map and all named edge/observation squares. -/
noncomputable def protocolAATGeneratedDirectedPackage
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    ProtocolAATGeneratedDirectedPackage input f where
  equation := protocolAATReadingCoreEquationForwardTransport input f
  raw := protocolAATReadingCoreRawForwardHom input f
  coverage := protocolAATReadingCoreForwardCoverageImageGeneric input f
  overlap := protocolAATReadingCoreForwardOverlapReadable input f
  extension := protocolAATGeneratedExtensionCoherence input f

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
