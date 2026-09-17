import ResearchLean.AG.RealizationReconstruction.CSAATGeneratedDirectedForward
import Formal.Util.AssertStandardAxioms

/-!
# Directed coverage and overlap on generated ReadingCores

The existing source-image coverage strength is stated for arbitrary carried
core-geometry data.  Primitive maps and selected readings are separated from
the proof-bearing layer: lens and protocol constructors build target full-family
membership and all nine coverage clauses from the same primitive CS morphism.
Equality transport then places coverage and
readable overlap on the actual generated core data.  No target-wide coverage,
inverse, or equivalence of the ambient directed map is introduced.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- Primitive labels needed to state directed source-image coverage on
arbitrary core-geometry packages.  These are maps and selected readings, not
visibility certificates. -/
structure GeneratedForwardCoverageLabels {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (sourceData : CSAATCoreGeometryData sourceObject)
    (targetData : CSAATCoreGeometryData targetObject) where
  sourceReading : Site.ArchCtx sourceObject
  targetReading : Site.ArchCtx targetObject
  requiredCoordinateMap :
    sourceData.equationReading.equationSystem.RequiredCoordinate →
      targetData.equationReading.equationSystem.RequiredCoordinate
  coordinateMap : sourceData.equationReading.equationSystem.Coordinate →
    targetData.equationReading.equationSystem.Coordinate
  axisMap : sourceData.signature.Axis → targetData.signature.Axis
  forwardObservable : sourceReading.Observable → targetReading.Observable
  sourceRequiredObservable :
    sourceData.equationReading.equationSystem.RequiredCoordinate →
      sourceReading.Observable
  targetRequiredObservable :
    targetData.equationReading.equationSystem.RequiredCoordinate →
      targetReading.Observable
  sourceCoordinateObservable :
    sourceData.equationReading.equationSystem.Coordinate → sourceReading.Observable
  targetCoordinateObservable :
    targetData.equationReading.equationSystem.Coordinate → targetReading.Observable
  axisForward : sourceReading.Axis → targetReading.Axis
  targetAxis : targetData.signature.Axis → targetReading.Axis

/-- The complete source-role image contract, retaining the exact coherent
observable and covariant-axis witnesses of the endpoint construction. -/
structure GeneratedForwardCoverageImage {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (sourceData : CSAATCoreGeometryData sourceObject)
    (targetData : CSAATCoreGeometryData targetObject)
    (F : (coreGeometryDataSite sourceData).category ⥤
      (coreGeometryDataSite targetData).category)
    (labels : GeneratedForwardCoverageLabels sourceData targetData) : Prop where
  target_all : ∀ atom, targetObject.configuration.family.mem atom
  requiredSupport : ∀ atom,
    sourceData.requirements.requiredSupport atom →
      targetData.requirements.requiredSupport atom
  requiredEquationCoordinate : ∀ coordinate,
    sourceData.requirements.requiredEquationCoordinate coordinate →
      targetData.requirements.requiredEquationCoordinate
        (labels.requiredCoordinateMap coordinate)
  selectedViolationWitness : ∀ coordinate,
    sourceData.requirements.selectedViolationWitness coordinate →
      targetData.requirements.selectedViolationWitness
        (labels.coordinateMap coordinate)
  requiredAxis : ∀ axis,
    sourceData.requirements.requiredAxis axis →
      targetData.requirements.requiredAxis (labels.axisMap axis)
  supportVisibleOn : ∀ W atom,
    sourceData.requirements.supportVisibleOn W atom →
      targetData.requirements.supportVisibleOn (F.obj ⟨W⟩).ctx atom
  equationCoordinateVisibleOn : ∀ W coordinate,
    sourceData.requirements.equationCoordinateVisibleOn W coordinate →
      ForwardObservableVisibility (W := W) target_all
        labels.sourceReading labels.targetReading labels.forwardObservable
        (labels.sourceRequiredObservable coordinate)
        (labels.targetRequiredObservable (labels.requiredCoordinateMap coordinate))
  violationWitnessVisibleOn : ∀ W coordinate,
    sourceData.requirements.violationWitnessVisibleOn W coordinate →
      ForwardObservableVisibility (W := W) target_all
        labels.sourceReading labels.targetReading labels.forwardObservable
        (labels.sourceCoordinateObservable coordinate)
        (labels.targetCoordinateObservable (labels.coordinateMap coordinate))
  axisReadableOn : ∀ W axis,
    sourceData.requirements.axisReadableOn W axis →
      ForwardAxisVisibility (W := W) target_all labels.sourceReading
        labels.targetReading labels.axisForward
        (labels.targetAxis (labels.axisMap axis))
  boundaryVisibleOn : ∀ W base,
    sourceData.requirements.boundaryVisibleOn W base →
      targetData.requirements.boundaryVisibleOn
        (F.obj ⟨W⟩).ctx (F.obj ⟨base⟩).ctx

noncomputable def coreGeometryCoverageLabelsCast {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (sourceData : CSAATCoreGeometryData sourceEndpoint)
    (targetData : CSAATCoreGeometryData targetEndpoint)
    (labels : GeneratedForwardCoverageLabels sourceData targetData) :
    GeneratedForwardCoverageLabels
      (source_eq.symm ▸ sourceData) (target_eq.symm ▸ targetData) := by
  cases source_eq
  cases target_eq
  exact labels

noncomputable def coreGeometryCoverageForwardCast {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (sourceData : CSAATCoreGeometryData sourceEndpoint)
    (targetData : CSAATCoreGeometryData targetEndpoint)
    (F : (coreGeometryDataSite sourceData).category ⥤
      (coreGeometryDataSite targetData).category)
    (labels : GeneratedForwardCoverageLabels sourceData targetData)
    (coverage : GeneratedForwardCoverageImage sourceData targetData F labels) :
    GeneratedForwardCoverageImage
      (source_eq.symm ▸ sourceData) (target_eq.symm ▸ targetData)
      (coreGeometryContextFunctorCast source_eq target_eq sourceData targetData F)
      (coreGeometryCoverageLabelsCast source_eq target_eq sourceData targetData
        labels) := by
  cases source_eq
  cases target_eq
  exact coverage

/-- Preservation of the selected overlap carried by two arbitrary geometry
bundles, up to mutual readable refinement. -/
structure GeneratedForwardOverlapReadable {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (sourceData : CSAATCoreGeometryData sourceObject)
    (targetData : CSAATCoreGeometryData targetObject)
    (F : (coreGeometryDataSite sourceData).category ⥤
      (coreGeometryDataSite targetData).category) : Prop where
  readable : ∀ base left right,
    Site.ReadableEquivalent targetData.equationReading.contextPreorder
      (F.obj ⟨sourceData.overlap.overlap base left right⟩).ctx
      (targetData.overlap.overlap
        (F.obj ⟨base⟩).ctx (F.obj ⟨left⟩).ctx (F.obj ⟨right⟩).ctx)

noncomputable def coreGeometryOverlapForwardCast {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (sourceData : CSAATCoreGeometryData sourceEndpoint)
    (targetData : CSAATCoreGeometryData targetEndpoint)
    (F : (coreGeometryDataSite sourceData).category ⥤
      (coreGeometryDataSite targetData).category)
    (overlap : GeneratedForwardOverlapReadable sourceData targetData F) :
    GeneratedForwardOverlapReadable
      (source_eq.symm ▸ sourceData) (target_eq.symm ▸ targetData)
      (coreGeometryContextFunctorCast source_eq target_eq sourceData targetData F) := by
  cases source_eq
  cases target_eq
  exact overlap

/-! ## Lens specialization -/

noncomputable def lensAATEndpointForwardCoverageLabels
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    GeneratedForwardCoverageLabels
      (lensAATCoreEndpointGeometryData input X)
      (lensAATCoreEndpointGeometryData input Y) where
  sourceReading := lensAATGeometryReadingContext input X
  targetReading := lensAATGeometryReadingContext input Y
  requiredCoordinateMap := lensAATForwardRequiredCoordinate input f
  coordinateMap := lensAATForwardCoordinate input f
  axisMap := _root_.id
  forwardObservable := f.lawCoordinateMap
  sourceRequiredObservable := fun coordinate =>
    MvPolynomial.X (coordinate.1.1, coordinate.2)
  targetRequiredObservable := fun coordinate =>
    MvPolynomial.X (coordinate.1.1, coordinate.2)
  sourceCoordinateObservable := MvPolynomial.X
  targetCoordinateObservable := MvPolynomial.X
  axisForward := _root_.id
  targetAxis := _root_.id

def lensAATEndpointForwardCoverageImageGeneric
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    GeneratedForwardCoverageImage
      (lensAATCoreEndpointGeometryData input X)
      (lensAATCoreEndpointGeometryData input Y) f.lawContextFunctor
      (lensAATEndpointForwardCoverageLabels input f) where
  target_all := fun atom => typedRoleConfiguration_mem
    (U := lensAATCarrier input) (.point) atom
  requiredSupport := (lensAATForwardCoverageImage input f).requiredSupport
  requiredEquationCoordinate :=
    (lensAATForwardCoverageImage input f).requiredEquationCoordinate
  selectedViolationWitness :=
    (lensAATForwardCoverageImage input f).selectedViolationWitness
  requiredAxis := (lensAATForwardCoverageImage input f).requiredAxis
  supportVisibleOn := (lensAATForwardCoverageImage input f).supportVisibleOn
  equationCoordinateVisibleOn :=
    (lensAATForwardCoverageImage input f).equationCoordinateVisibleOn
  violationWitnessVisibleOn :=
    (lensAATForwardCoverageImage input f).violationWitnessVisibleOn
  axisReadableOn := (lensAATForwardCoverageImage input f).axisReadableOn
  boundaryVisibleOn := (lensAATForwardCoverageImage input f).boundaryVisibleOn

noncomputable def lensAATReadingCoreForwardCoverageLabels
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    GeneratedForwardCoverageLabels
      (lensAATCoreGeneratedGeometryData input X)
      (lensAATCoreGeneratedGeometryData input Y) :=
  coreGeometryCoverageLabelsCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    (lensAATCoreEndpointGeometryData input X)
    (lensAATCoreEndpointGeometryData input Y)
    (lensAATEndpointForwardCoverageLabels input f)

noncomputable def lensAATReadingCoreForwardCoverageImageGeneric
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    GeneratedForwardCoverageImage
      (lensAATCoreGeneratedGeometryData input X)
      (lensAATCoreGeneratedGeometryData input Y)
      (lensAATReadingCoreForwardContextFunctor input f)
      (lensAATReadingCoreForwardCoverageLabels input f) := by
  unfold lensAATCoreGeneratedGeometryData
  exact coreGeometryCoverageForwardCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    (lensAATCoreEndpointGeometryData input X)
    (lensAATCoreEndpointGeometryData input Y) f.lawContextFunctor
    (lensAATEndpointForwardCoverageLabels input f)
    (lensAATEndpointForwardCoverageImageGeneric input f)

def lensAATEndpointForwardOverlapReadable
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    GeneratedForwardOverlapReadable
      (lensAATCoreEndpointGeometryData input X)
      (lensAATCoreEndpointGeometryData input Y) f.lawContextFunctor where
  readable := lensAATForwardCompleteLawOverlap_readableEquivalent input f

noncomputable def lensAATReadingCoreForwardOverlapReadable
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    GeneratedForwardOverlapReadable
      (lensAATCoreGeneratedGeometryData input X)
      (lensAATCoreGeneratedGeometryData input Y)
      (lensAATReadingCoreForwardContextFunctor input f) := by
  unfold lensAATCoreGeneratedGeometryData
  exact coreGeometryOverlapForwardCast
    (lensCoreGeneratedObject_eq_lawObject input X)
    (lensCoreGeneratedObject_eq_lawObject input Y)
    (lensAATCoreEndpointGeometryData input X)
    (lensAATCoreEndpointGeometryData input Y) f.lawContextFunctor
    (lensAATEndpointForwardOverlapReadable input f)

/-! ## Protocol specialization -/

noncomputable def protocolAATEndpointForwardCoverageLabels
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    GeneratedForwardCoverageLabels
      (protocolAATCoreEndpointGeometryData input X)
      (protocolAATCoreEndpointGeometryData input Y) where
  sourceReading := protocolAATGeometryReadingContext input X
  targetReading := protocolAATGeometryReadingContext input Y
  requiredCoordinateMap := protocolAATForwardRequiredCoordinate input f
  coordinateMap := protocolAATForwardCoordinate input f
  axisMap := _root_.id
  forwardObservable := f.lawCoordinateMap
  sourceRequiredObservable := fun coordinate =>
    MvPolynomial.X (coordinate.1.1, coordinate.2)
  targetRequiredObservable := fun coordinate =>
    MvPolynomial.X (coordinate.1.1, coordinate.2)
  sourceCoordinateObservable := MvPolynomial.X
  targetCoordinateObservable := MvPolynomial.X
  axisForward := _root_.id
  targetAxis := _root_.id

def protocolAATEndpointForwardCoverageImageGeneric
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    GeneratedForwardCoverageImage
      (protocolAATCoreEndpointGeometryData input X)
      (protocolAATCoreEndpointGeometryData input Y) f.lawContextFunctor
      (protocolAATEndpointForwardCoverageLabels input f) where
  target_all := fun atom => typedRoleConfiguration_mem
    (U := protocolAATCarrier input) (.point) atom
  requiredSupport := (protocolAATForwardCoverageImage input f).requiredSupport
  requiredEquationCoordinate :=
    (protocolAATForwardCoverageImage input f).requiredEquationCoordinate
  selectedViolationWitness :=
    (protocolAATForwardCoverageImage input f).selectedViolationWitness
  requiredAxis := (protocolAATForwardCoverageImage input f).requiredAxis
  supportVisibleOn := (protocolAATForwardCoverageImage input f).supportVisibleOn
  equationCoordinateVisibleOn :=
    (protocolAATForwardCoverageImage input f).equationCoordinateVisibleOn
  violationWitnessVisibleOn :=
    (protocolAATForwardCoverageImage input f).violationWitnessVisibleOn
  axisReadableOn := (protocolAATForwardCoverageImage input f).axisReadableOn
  boundaryVisibleOn := (protocolAATForwardCoverageImage input f).boundaryVisibleOn

noncomputable def protocolAATReadingCoreForwardCoverageLabels
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    GeneratedForwardCoverageLabels
      (protocolAATCoreGeneratedGeometryData input X)
      (protocolAATCoreGeneratedGeometryData input Y) :=
  coreGeometryCoverageLabelsCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    (protocolAATCoreEndpointGeometryData input X)
    (protocolAATCoreEndpointGeometryData input Y)
    (protocolAATEndpointForwardCoverageLabels input f)

noncomputable def protocolAATReadingCoreForwardCoverageImageGeneric
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    GeneratedForwardCoverageImage
      (protocolAATCoreGeneratedGeometryData input X)
      (protocolAATCoreGeneratedGeometryData input Y)
      (protocolAATReadingCoreForwardContextFunctor input f)
      (protocolAATReadingCoreForwardCoverageLabels input f) := by
  unfold protocolAATCoreGeneratedGeometryData
  exact coreGeometryCoverageForwardCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    (protocolAATCoreEndpointGeometryData input X)
    (protocolAATCoreEndpointGeometryData input Y) f.lawContextFunctor
    (protocolAATEndpointForwardCoverageLabels input f)
    (protocolAATEndpointForwardCoverageImageGeneric input f)

def protocolAATEndpointForwardOverlapReadable
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    GeneratedForwardOverlapReadable
      (protocolAATCoreEndpointGeometryData input X)
      (protocolAATCoreEndpointGeometryData input Y) f.lawContextFunctor where
  readable := protocolAATForwardCompleteLawOverlap_readableEquivalent input f

noncomputable def protocolAATReadingCoreForwardOverlapReadable
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    GeneratedForwardOverlapReadable
      (protocolAATCoreGeneratedGeometryData input X)
      (protocolAATCoreGeneratedGeometryData input Y)
      (protocolAATReadingCoreForwardContextFunctor input f) := by
  unfold protocolAATCoreGeneratedGeometryData
  exact coreGeometryOverlapForwardCast
    (protocolCoreGeneratedObject_eq_lawObject input X)
    (protocolCoreGeneratedObject_eq_lawObject input Y)
    (protocolAATCoreEndpointGeometryData input X)
    (protocolAATCoreEndpointGeometryData input Y) f.lawContextFunctor
    (protocolAATEndpointForwardOverlapReadable input f)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
