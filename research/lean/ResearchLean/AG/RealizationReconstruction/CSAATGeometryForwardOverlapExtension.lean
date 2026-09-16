import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardImage
import Formal.Util.AssertStandardAxioms

/-!
# Forward overlap and Extension coherence for arbitrary CS morphisms

Full-family rebasing and the canonical product overlap carry the same support,
axis, observable, and Extension data, but their proof fields are not
definitionally equal.  We therefore prove the mathematically relevant claim:
the rebased source overlap and the overlap of the rebased contexts refine each
other by explicit selected restrictions.

An arbitrary non-surjective state map cannot push every possible value of the
source Extension carrier to the independently constructed target Extension
carrier.  The concrete readings nevertheless retain distinguished raw Law
operations and the A1 point.  The lens and protocol coherence records below
are generated from the primitive morphism and compare exactly those selected
values and every named operation.  No whole-Extension map, inverse, target
answer, `ReadingCore`, or `GeometryTotalHom` is assumed.
-/

namespace AAT.AG.RealizationReconstruction

universe u

/-! ## Product-overlap comparison under full-family rebase -/

/-- Identity-on-data comparison from the rebase of a product context to the
product of the rebased contexts. -/
def fullFamilyProductComparisonForward {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (W V : Site.ArchCtx sourceObject) :
    Site.ContextMorphism
      (fullFamilyContextRebase targetObject target_all (Site.productContext W V))
      (Site.productContext
        (fullFamilyContextRebase targetObject target_all W)
        (fullFamilyContextRebase targetObject target_all V)) where
  supportMap := _root_.id
  axisMap := _root_.id
  observableRestrict := _root_.id

/-- The forward product comparison is an actual selected restriction. -/
theorem fullFamilyProductComparisonForward_isRestriction
    {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (W V : Site.ArchCtx sourceObject) :
    (fullFamilyProductComparisonForward target_all W V).IsRestriction := by
  refine ⟨fun h => h, fun h => h, ?_, fun _ => target_all _⟩
  intro observable h
  cases observable <;> exact h

/-- Identity-on-data comparison in the reverse refinement direction. -/
def fullFamilyProductComparisonBackward {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (W V : Site.ArchCtx sourceObject) :
    Site.ContextMorphism
      (Site.productContext
        (fullFamilyContextRebase targetObject target_all W)
        (fullFamilyContextRebase targetObject target_all V))
      (fullFamilyContextRebase targetObject target_all (Site.productContext W V)) where
  supportMap := _root_.id
  axisMap := _root_.id
  observableRestrict := _root_.id

/-- The backward product comparison is also a selected restriction. -/
theorem fullFamilyProductComparisonBackward_isRestriction
    {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (W V : Site.ArchCtx sourceObject) :
    (fullFamilyProductComparisonBackward target_all W V).IsRestriction := by
  refine ⟨fun h => h, fun h => h, ?_, fun _ => target_all _⟩
  intro observable h
  cases observable <;> exact h

/-- Product context and full-family rebase commute up to mutual readable
refinement.  This avoids identifying proof fields by an artificial equality. -/
theorem fullFamilyProductComparison_readableEquivalent
    {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (W V : Site.ArchCtx sourceObject) :
    Site.ReadableEquivalent (Site.contextMorphismPreorderCategory targetObject)
      (fullFamilyContextRebase targetObject target_all (Site.productContext W V))
      (Site.productContext
        (fullFamilyContextRebase targetObject target_all W)
        (fullFamilyContextRebase targetObject target_all V)) :=
  ⟨⟨fullFamilyProductComparisonForward target_all W V,
      fullFamilyProductComparisonForward_isRestriction target_all W V⟩,
    ⟨fullFamilyProductComparisonBackward target_all W V,
      fullFamilyProductComparisonBackward_isRestriction target_all W V⟩⟩

/-- The comparison retains the product Extension carrier exactly. -/
@[simp] theorem fullFamilyProductComparison_extensionType
    {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (W V : Site.ArchCtx sourceObject) :
    (fullFamilyContextRebase targetObject target_all
      (Site.productContext W V)).Extension =
      (Site.productContext
        (fullFamilyContextRebase targetObject target_all W)
        (fullFamilyContextRebase targetObject target_all V)).Extension :=
  rfl

/-- The distinguished product Extension value is retained exactly. -/
@[simp] theorem fullFamilyProductComparison_extension
    {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (W V : Site.ArchCtx sourceObject) :
    HEq
      (fullFamilyContextRebase targetObject target_all
        (Site.productContext W V)).extension
      (Site.productContext
        (fullFamilyContextRebase targetObject target_all W)
        (fullFamilyContextRebase targetObject target_all V)).extension :=
  HEq.rfl

/-- The canonical complete-Law overlap is preserved up to mutual readable
refinement on every source-generated triple. -/
theorem fullFamilyCompleteLawOverlap_readableEquivalent
    {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (base left right : Site.ArchCtx sourceObject) :
    Site.ReadableEquivalent (Site.contextMorphismPreorderCategory targetObject)
      (fullFamilyContextRebase targetObject target_all
        ((completeLawOverlap sourceObject).overlap base left right))
      ((completeLawOverlap targetObject).overlap
        (fullFamilyContextRebase targetObject target_all base)
        (fullFamilyContextRebase targetObject target_all left)
        (fullFamilyContextRebase targetObject target_all right)) := by
  change Site.ReadableEquivalent _
    (fullFamilyContextRebase targetObject target_all
      (Site.productContext left right))
    (Site.productContext
      (fullFamilyContextRebase targetObject target_all left)
      (fullFamilyContextRebase targetObject target_all right))
  exact fullFamilyProductComparison_readableEquivalent target_all left right

/-! ## Lens and protocol overlap specializations -/

/-- Every lens forward context functor preserves the selected complete-Law
overlap up to the explicit readable equivalence above. -/
theorem lensAATForwardCompleteLawOverlap_readableEquivalent
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
    (base left right : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)) :
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
          ((f.lawContextFunctor).obj ⟨right⟩).ctx) :=
  fullFamilyCompleteLawOverlap_readableEquivalent
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom)
    base left right

/-- Every protocol forward context functor preserves the selected complete-Law
overlap up to mutual readable refinement. -/
theorem protocolAATForwardCompleteLawOverlap_readableEquivalent
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (base left right : Site.ArchCtx
      (protocolLawObject input X.State X.toLawStructure)) :
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
          ((f.lawContextFunctor).obj ⟨right⟩).ctx) :=
  fullFamilyCompleteLawOverlap_readableEquivalent
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom)
    base left right

/-! ## Distinguished Extension coherence -/

/-- The selected lens Extension data commute with the primitive state map.
No map on arbitrary values of the whole Extension carrier is asserted. -/
structure LensAATForwardExtensionCoherence
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) : Prop where
  point_map : f.sourceMap
      (lensAATGeometryReadingContext input X).extension.2 =
    (lensAATGeometryReadingContext input Y).extension.2
  get_map : ∀ state,
    (lensAATGeometryReadingContext input Y).extension.1.down.get
        (f.stateMap state) =
      (lensAATGeometryReadingContext input X).extension.1.down.get state
  put_map : ∀ state view,
    f.stateMap
        ((lensAATGeometryReadingContext input X).extension.1.down.put state view) =
      (lensAATGeometryReadingContext input Y).extension.1.down.put
        (f.stateMap state) view

/-- Construct all selected lens Extension equations from the named get/put
squares of the same primitive morphism. -/
def lensAATForwardExtensionCoherence
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensAATForwardExtensionCoherence input f where
  point_map := rfl
  get_map := f.get_naturality
  put_map := f.put_naturality

/-- The selected protocol Extension data commute with every named edge and
observation map of the primitive morphism. -/
structure ProtocolAATForwardExtensionCoherence
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) : Prop where
  point_map : f.sourceMap
      (protocolAATGeometryReadingContext input X).extension.2 =
    (protocolAATGeometryReadingContext input Y).extension.2
  edge_map : ∀ {source target} (edge : input.schema.Edge source target)
      (state : X.State source),
    f.stateMap target
        ((protocolAATGeometryReadingContext input X).extension.1.down.edgeAction
          edge state) =
      (protocolAATGeometryReadingContext input Y).extension.1.down.edgeAction
        edge (f.stateMap source state)
  observation_map : ∀ vertex (state : X.State vertex),
    (protocolAATGeometryReadingContext input Y).extension.1.down.observe
        vertex (f.stateMap vertex state) =
      (protocolAATGeometryReadingContext input X).extension.1.down.observe
        vertex state

/-- Construct all selected protocol Extension equations from the same named
edge and observation squares. -/
def protocolAATForwardExtensionCoherence
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    ProtocolAATForwardExtensionCoherence input f where
  point_map := rfl
  edge_map := f.edge_naturality
  observation_map := f.observation_naturality

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
