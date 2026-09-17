import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardOverlapExtension
import ResearchLean.AG.RealizationReconstruction.CSAATReadingCoreProvenance
import Formal.Util.AssertStandardAxioms

/-!
# Directed forward data on generated ReadingCores

The existing directed endpoint transport is generalized, without increasing
its strength, to the context preorders carried by generated cores.  Equality
transport then places the context, equation, and raw maps on the actual lens
and protocol `ReadingCore`s.  Endpoint-typed source-image coverage, readable
overlap, and selected Extension equations are retained with their constructed
Sigma provenance; they are not renamed as target-wide generated coverage.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- The AAT site carried by one dependent core-geometry provenance bundle. -/
def coreGeometryDataSite {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (data : CSAATCoreGeometryData A) : Site.AATSite A where
  contextPreorder := data.equationReading.contextPreorder
  equationSystem := data.equationReading.equationSystem
  signature := data.signature
  requirements := data.requirements
  overlap := data.overlap

/-- Transport a directed endpoint context functor across the two constructed
generated-object equalities. -/
noncomputable def coreGeometryContextFunctorCast {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (sourceData : CSAATCoreGeometryData sourceEndpoint)
    (targetData : CSAATCoreGeometryData targetEndpoint)
    (F : (coreGeometryDataSite sourceData).category ⥤
      (coreGeometryDataSite targetData).category) :
    (coreGeometryDataSite (source_eq.symm ▸ sourceData)).category ⥤
      (coreGeometryDataSite (target_eq.symm ▸ targetData)).category := by
  cases source_eq
  cases target_eq
  exact F

/-- The same genuinely directed equation contract as the existing endpoint
type, generalized only from the full context preorder to the context preorders
already carried by generated cores. -/
structure GeneratedEquationForwardTransport {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    {sourceContext : Site.ContextPreorderCategory sourceObject}
    {targetContext : Site.ContextPreorderCategory targetObject}
    (sourceEquation : ArchitecturalEquationSystem sourceContext)
    (targetEquation : ArchitecturalEquationSystem targetContext) where
  contextFunctor : Site.ContextCategoryObject sourceContext ⥤
    Site.ContextCategoryObject targetContext
  equationMap : sourceEquation.Index → targetEquation.Index
  role_eq : ∀ index,
    targetEquation.role (equationMap index) = sourceEquation.role index
  observableHom : ∀ W,
    sourceEquation.Observable W →+* targetEquation.Observable (contextFunctor.obj W)
  observable_naturality : ∀ {W V} (f : W ⟶ V)
      (observable : sourceEquation.Observable V),
    observableHom W (sourceEquation.restrict f observable) =
      targetEquation.restrict (contextFunctor.map f) (observableHom V observable)
  violationCoordinate_map : ∀ W index atom,
    observableHom W (sourceEquation.violationCoordinate W index atom) =
      targetEquation.violationCoordinate (contextFunctor.obj W)
        (equationMap index) atom
  endpointResidual_zero_map : ∀ W index atom,
    sourceEquation.equationResidual W sourceObject index atom = 0 →
      targetEquation.equationResidual (contextFunctor.obj W)
        targetObject (equationMap index) atom = 0

/-- The accepted endpoint contract embeds strictly in the generated-core
variant without changing any computational field. -/
def GeneratedEquationForwardTransport.ofEndpoint {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    {sourceEquation : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory sourceObject)}
    {targetEquation : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory targetObject)}
    (T : EndpointEquationForwardTransport sourceEquation targetEquation) :
    GeneratedEquationForwardTransport sourceEquation targetEquation where
  contextFunctor := T.contextFunctor
  equationMap := T.equationMap
  role_eq := T.role_eq
  observableHom := T.observableHom
  observable_naturality := T.observable_naturality
  violationCoordinate_map := T.violationCoordinate_map
  endpointResidual_zero_map := T.endpointResidual_zero_map

/-- Transport a one-way equation map to the source-generated equation systems.
No inverse or target-surjectivity field is introduced. -/
noncomputable def coreGeometryEquationForwardCast {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (sourceData : CSAATCoreGeometryData sourceEndpoint)
    (targetData : CSAATCoreGeometryData targetEndpoint)
    (transport : GeneratedEquationForwardTransport
      sourceData.equationReading.equationSystem
      targetData.equationReading.equationSystem) :
    GeneratedEquationForwardTransport
      (source_eq.symm ▸ sourceData).equationReading.equationSystem
      (target_eq.symm ▸ targetData).equationReading.equationSystem := by
  cases source_eq
  cases target_eq
  exact transport

/-- Transport the actual directed raw-presheaf map to the generated sites. -/
noncomputable def coreGeometryRawForwardCast {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (sourceData : CSAATCoreGeometryData sourceEndpoint)
    (targetData : CSAATCoreGeometryData targetEndpoint)
    (F : (coreGeometryDataSite sourceData).category ⥤
      (coreGeometryDataSite targetData).category)
    (raw : (equationCoordinateRawSystemOn
        (coreGeometryDataSite sourceData)).toPresheaf ⟶
      F.op ⋙ (equationCoordinateRawSystemOn
        (coreGeometryDataSite targetData)).toPresheaf) :
    (equationCoordinateRawSystemOn
        (coreGeometryDataSite (source_eq.symm ▸ sourceData))).toPresheaf ⟶
      (coreGeometryContextFunctorCast source_eq target_eq sourceData targetData F).op ⋙
        (equationCoordinateRawSystemOn
          (coreGeometryDataSite (target_eq.symm ▸ targetData))).toPresheaf := by
  cases source_eq
  cases target_eq
  exact raw

/-- The context functor of an arbitrary primitive lens morphism, now typed on
the source-generated ReadingCore context categories. -/
noncomputable def lensAATReadingCoreForwardContextFunctor
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    (lensAATReadingCore input X).site.category ⥤
      (lensAATReadingCore input Y).site.category := by
  change
    (coreGeometryDataSite (lensAATCoreGeneratedGeometryData input X)).category ⥤
      (coreGeometryDataSite (lensAATCoreGeneratedGeometryData input Y)).category
  unfold lensAATCoreGeneratedGeometryData
  exact coreGeometryContextFunctorCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    (lensAATCoreEndpointGeometryData input X)
    (lensAATCoreEndpointGeometryData input Y)
    f.lawContextFunctor

/-- Existing one-way endpoint equation data transported to the generated core. -/
noncomputable def lensAATReadingCoreEquationForwardTransport
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    GeneratedEquationForwardTransport
      (lensAATReadingCore input X).site.equationSystem
      (lensAATReadingCore input Y).site.equationSystem := by
  change GeneratedEquationForwardTransport
    (lensAATCoreGeneratedGeometryData input X).equationReading.equationSystem
    (lensAATCoreGeneratedGeometryData input Y).equationReading.equationSystem
  unfold lensAATCoreGeneratedGeometryData
  exact coreGeometryEquationForwardCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    (lensAATCoreEndpointGeometryData input X)
    (lensAATCoreEndpointGeometryData input Y)
    (GeneratedEquationForwardTransport.ofEndpoint
      (lensAATEndpointEquationForwardTransport input f))

/-- Existing one-way raw action transported to the generated ReadingCore raw
presheaves. -/
noncomputable def lensAATReadingCoreRawForwardHom
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    (lensAATReadingCore input X).raw.toPresheaf ⟶
      (lensAATReadingCoreForwardContextFunctor input f).op ⋙
        (lensAATReadingCore input Y).raw.toPresheaf := by
  change
    (equationCoordinateRawSystemOn
      (coreGeometryDataSite (lensAATCoreGeneratedGeometryData input X))).toPresheaf ⟶
    (lensAATReadingCoreForwardContextFunctor input f).op ⋙
      (equationCoordinateRawSystemOn
        (coreGeometryDataSite (lensAATCoreGeneratedGeometryData input Y))).toPresheaf
  unfold lensAATCoreGeneratedGeometryData
  exact coreGeometryRawForwardCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    (lensAATCoreEndpointGeometryData input X)
    (lensAATCoreEndpointGeometryData input Y)
    f.lawContextFunctor
    (lensAATGeometryReadingRawForwardHom input f)

/-- Minimal directed generated-core aggregate.  Equation and raw data are
actually typed on the generated ReadingCores.  Coverage, readable overlap,
and distinguished Extension equations retain their original one-way endpoint
strength, while the two Sigma equalities record that those endpoints are
exactly the geometry data transported into the generated cores. -/
structure LensAATReadingCoreForwardImage
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) where
  equation : GeneratedEquationForwardTransport
    (lensAATReadingCore input X).site.equationSystem
    (lensAATReadingCore input Y).site.equationSystem
  raw : (lensAATReadingCore input X).raw.toPresheaf ⟶
    (lensAATReadingCoreForwardContextFunctor input f).op ⋙
      (lensAATReadingCore input Y).raw.toPresheaf
  coverage : LensAATForwardCoverageImage input f
  overlap : ∀ base left right,
    Site.ReadableEquivalent
      (Site.contextMorphismPreorderCategory
        (lensLawObject input Y.Carrier Y.toLensData.toLawStructure))
      ((f.lawContextFunctor).obj
        ⟨(completeLawOverlap
          (lensLawObject input X.Carrier X.toLensData.toLawStructure)).overlap
            base left right⟩).ctx
      ((completeLawOverlap
        (lensLawObject input Y.Carrier Y.toLensData.toLawStructure)).overlap
          ((f.lawContextFunctor).obj ⟨base⟩).ctx
          ((f.lawContextFunctor).obj ⟨left⟩).ctx
          ((f.lawContextFunctor).obj ⟨right⟩).ctx)
  extension : LensAATForwardExtensionCoherence input f
  source_provenance :
    Sigma.mk _ (lensAATCoreGeneratedGeometryData input X) =
      Sigma.mk _ (lensAATCoreEndpointGeometryData input X)
  target_provenance :
    Sigma.mk _ (lensAATCoreGeneratedGeometryData input Y) =
      Sigma.mk _ (lensAATCoreEndpointGeometryData input Y)

/-- Construct the whole minimal directed aggregate from the same primitive
get/put morphism. -/
noncomputable def lensAATReadingCoreForwardImage
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensAATReadingCoreForwardImage input f where
  equation := lensAATReadingCoreEquationForwardTransport input f
  raw := lensAATReadingCoreRawForwardHom input f
  coverage := lensAATForwardCoverageImage input f
  overlap := lensAATForwardCompleteLawOverlap_readableEquivalent input f
  extension := lensAATForwardExtensionCoherence input f
  source_provenance := Sigma.ext
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensAATCoreGeneratedGeometryData_heq input X)
  target_provenance := Sigma.ext
    (lensCoreGeneratedObject_eq_lawObject input Y)
    (lensAATCoreGeneratedGeometryData_heq input Y)

/-! ## Protocol generated-core specialization -/

/-- The context functor of an arbitrary primitive protocol morphism, typed on
the generated protocol ReadingCore context categories. -/
noncomputable def protocolAATReadingCoreForwardContextFunctor
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    (protocolAATReadingCore input X).site.category ⥤
      (protocolAATReadingCore input Y).site.category := by
  change
    (coreGeometryDataSite
      (protocolAATCoreGeneratedGeometryData input X)).category ⥤
      (coreGeometryDataSite
        (protocolAATCoreGeneratedGeometryData input Y)).category
  unfold protocolAATCoreGeneratedGeometryData
  exact coreGeometryContextFunctorCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    (protocolAATCoreEndpointGeometryData input X)
    (protocolAATCoreEndpointGeometryData input Y)
    f.lawContextFunctor

/-- Existing one-way protocol equation data transported to the generated
core equation systems. -/
noncomputable def protocolAATReadingCoreEquationForwardTransport
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    GeneratedEquationForwardTransport
      (protocolAATReadingCore input X).site.equationSystem
      (protocolAATReadingCore input Y).site.equationSystem := by
  change GeneratedEquationForwardTransport
    (protocolAATCoreGeneratedGeometryData input X).equationReading.equationSystem
    (protocolAATCoreGeneratedGeometryData input Y).equationReading.equationSystem
  unfold protocolAATCoreGeneratedGeometryData
  exact coreGeometryEquationForwardCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    (protocolAATCoreEndpointGeometryData input X)
    (protocolAATCoreEndpointGeometryData input Y)
    (GeneratedEquationForwardTransport.ofEndpoint
      (protocolAATEndpointEquationForwardTransport input f))

/-- Existing one-way protocol raw action transported to the generated
ReadingCore raw presheaves. -/
noncomputable def protocolAATReadingCoreRawForwardHom
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    (protocolAATReadingCore input X).raw.toPresheaf ⟶
      (protocolAATReadingCoreForwardContextFunctor input f).op ⋙
        (protocolAATReadingCore input Y).raw.toPresheaf := by
  change
    (equationCoordinateRawSystemOn
      (coreGeometryDataSite
        (protocolAATCoreGeneratedGeometryData input X))).toPresheaf ⟶
    (protocolAATReadingCoreForwardContextFunctor input f).op ⋙
      (equationCoordinateRawSystemOn
        (coreGeometryDataSite
          (protocolAATCoreGeneratedGeometryData input Y))).toPresheaf
  unfold protocolAATCoreGeneratedGeometryData
  exact coreGeometryRawForwardCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    (protocolAATCoreEndpointGeometryData input X)
    (protocolAATCoreEndpointGeometryData input Y)
    f.lawContextFunctor
    (protocolAATGeometryReadingRawForwardHom input f)

/-- Minimal protocol directed aggregate with equation and raw data actually
typed on generated ReadingCores.  The remaining one-way data retain their
honest endpoint strength together with both constructed provenance paths. -/
structure ProtocolAATReadingCoreForwardImage
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) where
  equation : GeneratedEquationForwardTransport
    (protocolAATReadingCore input X).site.equationSystem
    (protocolAATReadingCore input Y).site.equationSystem
  raw : (protocolAATReadingCore input X).raw.toPresheaf ⟶
    (protocolAATReadingCoreForwardContextFunctor input f).op ⋙
      (protocolAATReadingCore input Y).raw.toPresheaf
  coverage : ProtocolAATForwardCoverageImage input f
  overlap : ∀ base left right,
    Site.ReadableEquivalent
      (Site.contextMorphismPreorderCategory
        (protocolLawObject input Y.State Y.toLawStructure))
      ((f.lawContextFunctor).obj
        ⟨(completeLawOverlap
          (protocolLawObject input X.State X.toLawStructure)).overlap
            base left right⟩).ctx
      ((completeLawOverlap
        (protocolLawObject input Y.State Y.toLawStructure)).overlap
          ((f.lawContextFunctor).obj ⟨base⟩).ctx
          ((f.lawContextFunctor).obj ⟨left⟩).ctx
          ((f.lawContextFunctor).obj ⟨right⟩).ctx)
  extension : ProtocolAATForwardExtensionCoherence input f
  source_provenance :
    Sigma.mk _ (protocolAATCoreGeneratedGeometryData input X) =
      Sigma.mk _ (protocolAATCoreEndpointGeometryData input X)
  target_provenance :
    Sigma.mk _ (protocolAATCoreGeneratedGeometryData input Y) =
      Sigma.mk _ (protocolAATCoreEndpointGeometryData input Y)

/-- Construct the protocol aggregate from the same primitive edge and
observation morphism. -/
noncomputable def protocolAATReadingCoreForwardImage
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    ProtocolAATReadingCoreForwardImage input f where
  equation := protocolAATReadingCoreEquationForwardTransport input f
  raw := protocolAATReadingCoreRawForwardHom input f
  coverage := protocolAATForwardCoverageImage input f
  overlap := protocolAATForwardCompleteLawOverlap_readableEquivalent input f
  extension := protocolAATForwardExtensionCoherence input f
  source_provenance := Sigma.ext
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolAATCoreGeneratedGeometryData_heq input X)
  target_provenance := Sigma.ext
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    (protocolAATCoreGeneratedGeometryData_heq input Y)

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
