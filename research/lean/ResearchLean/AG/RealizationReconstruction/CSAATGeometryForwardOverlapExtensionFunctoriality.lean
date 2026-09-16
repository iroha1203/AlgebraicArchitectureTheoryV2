import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardCoverageAggregate
import Formal.Util.AssertStandardAxioms

/-!
# Semantic overlap and Extension functoriality

This file retains the actual forward and backward product-overlap comparisons,
their restriction proofs, and their direct-versus-successive component laws.
It then packages overlap and selected Extension identity/composition for both
CS translations.  Compositor constructors take only primitive morphisms and
derive both stages and the direct composite laws from them.

No equality of proof-bearing context records, whole-Extension map, inverse,
surjectivity, `ReadingCore`, or completed geometry morphism is asserted.

Every proposition-valued law structure below has a canonical theorem for all
of its admissible inputs.  Consequently no negative instance exists: such an
instance would contradict the corresponding universal constructor.
-/

namespace AAT.AG.RealizationReconstruction

universe u

/-! ## Exact product-overlap comparison laws -/

/-- The forward/backward comparison maps are identity on all semantic data,
compose through an arbitrary full-family middle endpoint, and retain the
selected Extension carrier and value. -/
structure FullFamilyProductComparisonSemanticLaws {U : AtomCarrier.{u}}
    {sourceObject middleObject targetObject : ArchitectureObject U}
    (middle_all : ∀ atom, middleObject.configuration.family.mem atom)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (W V : Site.ArchCtx sourceObject) : Prop where
  forward_support_id : ∀ x,
    (fullFamilyProductComparisonForward target_all W V).supportMap x = x
  forward_axis_id : ∀ x,
    (fullFamilyProductComparisonForward target_all W V).axisMap x = x
  forward_observable_id : ∀ x,
    (fullFamilyProductComparisonForward target_all W V).observableRestrict x = x
  backward_support_id : ∀ x,
    (fullFamilyProductComparisonBackward target_all W V).supportMap x = x
  backward_axis_id : ∀ x,
    (fullFamilyProductComparisonBackward target_all W V).axisMap x = x
  backward_observable_id : ∀ x,
    (fullFamilyProductComparisonBackward target_all W V).observableRestrict x = x
  forward_support_comp : ∀ x,
    (fullFamilyProductComparisonForward target_all W V).supportMap x =
      (fullFamilyProductComparisonForward target_all
        (fullFamilyContextRebase middleObject middle_all W)
        (fullFamilyContextRebase middleObject middle_all V)).supportMap
      ((fullFamilyProductComparisonForward middle_all W V).supportMap x)
  forward_axis_comp : ∀ x,
    (fullFamilyProductComparisonForward target_all W V).axisMap x =
      (fullFamilyProductComparisonForward target_all
        (fullFamilyContextRebase middleObject middle_all W)
        (fullFamilyContextRebase middleObject middle_all V)).axisMap
      ((fullFamilyProductComparisonForward middle_all W V).axisMap x)
  forward_observable_comp : ∀ x,
    (fullFamilyProductComparisonForward target_all W V).observableRestrict x =
      (fullFamilyProductComparisonForward middle_all W V).observableRestrict
      ((fullFamilyProductComparisonForward target_all
        (fullFamilyContextRebase middleObject middle_all W)
        (fullFamilyContextRebase middleObject middle_all V)).observableRestrict x)
  backward_support_comp : ∀ x,
    (fullFamilyProductComparisonBackward target_all W V).supportMap x =
      (fullFamilyProductComparisonBackward middle_all W V).supportMap
      ((fullFamilyProductComparisonBackward target_all
        (fullFamilyContextRebase middleObject middle_all W)
        (fullFamilyContextRebase middleObject middle_all V)).supportMap x)
  backward_axis_comp : ∀ x,
    (fullFamilyProductComparisonBackward target_all W V).axisMap x =
      (fullFamilyProductComparisonBackward middle_all W V).axisMap
      ((fullFamilyProductComparisonBackward target_all
        (fullFamilyContextRebase middleObject middle_all W)
        (fullFamilyContextRebase middleObject middle_all V)).axisMap x)
  backward_observable_comp : ∀ x,
    (fullFamilyProductComparisonBackward target_all W V).observableRestrict x =
      (fullFamilyProductComparisonBackward target_all
        (fullFamilyContextRebase middleObject middle_all W)
        (fullFamilyContextRebase middleObject middle_all V)).observableRestrict
      ((fullFamilyProductComparisonBackward middle_all W V).observableRestrict x)
  forward_restriction :
    (fullFamilyProductComparisonForward target_all W V).IsRestriction
  backward_restriction :
    (fullFamilyProductComparisonBackward target_all W V).IsRestriction
  readable_equivalent : Site.ReadableEquivalent
    (Site.contextMorphismPreorderCategory targetObject)
    (fullFamilyContextRebase targetObject target_all (Site.productContext W V))
    (Site.productContext
      (fullFamilyContextRebase targetObject target_all W)
      (fullFamilyContextRebase targetObject target_all V))
  extension_type :
    (fullFamilyContextRebase targetObject target_all
      (Site.productContext W V)).Extension =
    (Site.productContext
      (fullFamilyContextRebase targetObject target_all W)
      (fullFamilyContextRebase targetObject target_all V)).Extension
  extension_value : HEq
    (fullFamilyContextRebase targetObject target_all
      (Site.productContext W V)).extension
    (Site.productContext
      (fullFamilyContextRebase targetObject target_all W)
      (fullFamilyContextRebase targetObject target_all V)).extension

/-- Construct the complete comparison law from full-family endpoint data. -/
theorem fullFamilyProductComparisonSemanticLaws {U : AtomCarrier.{u}}
    {sourceObject middleObject targetObject : ArchitectureObject U}
    (middle_all : ∀ atom, middleObject.configuration.family.mem atom)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (W V : Site.ArchCtx sourceObject) :
    FullFamilyProductComparisonSemanticLaws middle_all target_all W V where
  forward_support_id _ := rfl
  forward_axis_id _ := rfl
  forward_observable_id _ := rfl
  backward_support_id _ := rfl
  backward_axis_id _ := rfl
  backward_observable_id _ := rfl
  forward_support_comp _ := rfl
  forward_axis_comp _ := rfl
  forward_observable_comp _ := rfl
  backward_support_comp _ := rfl
  backward_axis_comp _ := rfl
  backward_observable_comp _ := rfl
  forward_restriction :=
    fullFamilyProductComparisonForward_isRestriction target_all W V
  backward_restriction :=
    fullFamilyProductComparisonBackward_isRestriction target_all W V
  readable_equivalent :=
    fullFamilyProductComparison_readableEquivalent target_all W V
  extension_type := fullFamilyProductComparison_extensionType target_all W V
  extension_value := fullFamilyProductComparison_extension target_all W V

/-! ## Lens overlap and selected Extension laws -/

/-- Identity law for every source overlap and all selected lens Extension
operations. -/
structure LensAATForwardOverlapExtensionSemanticUnit
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) : Prop
    extends LensAATForwardExtensionCoherence input
      (LensAATForwardMorphism.id X) where
  comparison : ∀ (W V : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)),
    FullFamilyProductComparisonSemanticLaws
      (sourceObject := lensLawObject input X.Carrier X.toLensData.toLawStructure)
      (middleObject := lensLawObject input X.Carrier X.toLensData.toLawStructure)
      (targetObject := lensLawObject input X.Carrier X.toLensData.toLawStructure)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom) W V
  overlap : ∀ base left right,
    Site.ReadableEquivalent
      (Site.contextMorphismPreorderCategory
        (lensLawObject input X.Carrier X.toLensData.toLawStructure))
      (((LensAATForwardMorphism.id X).lawContextFunctor).obj
        ⟨(completeLawOverlap
          (lensLawObject input X.Carrier X.toLensData.toLawStructure)).overlap
            base left right⟩).ctx
      ((completeLawOverlap
        (lensLawObject input X.Carrier X.toLensData.toLawStructure)).overlap
          (((LensAATForwardMorphism.id X).lawContextFunctor).obj ⟨base⟩).ctx
          (((LensAATForwardMorphism.id X).lawContextFunctor).obj ⟨left⟩).ctx
          (((LensAATForwardMorphism.id X).lawContextFunctor).obj ⟨right⟩).ctx)

/-- Construct the lens overlap/Extension unit from the primitive identity. -/
theorem lensAATForwardOverlapExtensionSemanticUnit
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    LensAATForwardOverlapExtensionSemanticUnit input X where
  toLensAATForwardExtensionCoherence :=
    lensAATForwardExtensionCoherence input (LensAATForwardMorphism.id X)
  comparison W V := fullFamilyProductComparisonSemanticLaws
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom)
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom) W V
  overlap := lensAATForwardCompleteLawOverlap_readableEquivalent input
    (LensAATForwardMorphism.id X)

/-- Direct and staged overlap/Extension composition for arbitrary composable
lens morphisms. -/
structure LensAATForwardOverlapExtensionSemanticCompositor
    (input : LensFamilyInput.{u})
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
    (g : LensAATForwardMorphism Y Z) : Prop where
  comparison : ∀ (W V : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)),
    FullFamilyProductComparisonSemanticLaws
      (sourceObject := lensLawObject input X.Carrier X.toLensData.toLawStructure)
      (middleObject := lensLawObject input Y.Carrier Y.toLensData.toLawStructure)
      (targetObject := lensLawObject input Z.Carrier Z.toLensData.toLawStructure)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom) W V
  direct_overlap : ∀ base left right,
    Site.ReadableEquivalent
      (Site.contextMorphismPreorderCategory
        (lensLawObject input Z.Carrier Z.toLensData.toLawStructure))
      (((LensAATForwardMorphism.comp f g).lawContextFunctor).obj
        ⟨(completeLawOverlap
          (lensLawObject input X.Carrier X.toLensData.toLawStructure)).overlap
            base left right⟩).ctx
      ((completeLawOverlap
        (lensLawObject input Z.Carrier Z.toLensData.toLawStructure)).overlap
          (((LensAATForwardMorphism.comp f g).lawContextFunctor).obj ⟨base⟩).ctx
          (((LensAATForwardMorphism.comp f g).lawContextFunctor).obj ⟨left⟩).ctx
          (((LensAATForwardMorphism.comp f g).lawContextFunctor).obj ⟨right⟩).ctx)
  first_overlap : ∀ base left right,
    Site.ReadableEquivalent
      (Site.contextMorphismPreorderCategory
        (lensLawObject input Y.Carrier Y.toLensData.toLawStructure))
      ((f.lawContextFunctor.obj
        ⟨(completeLawOverlap
          (lensLawObject input X.Carrier X.toLensData.toLawStructure)).overlap
            base left right⟩).ctx)
      ((completeLawOverlap
        (lensLawObject input Y.Carrier Y.toLensData.toLawStructure)).overlap
          (f.lawContextFunctor.obj ⟨base⟩).ctx
          (f.lawContextFunctor.obj ⟨left⟩).ctx
          (f.lawContextFunctor.obj ⟨right⟩).ctx)
  second_overlap : ∀ base left right,
    Site.ReadableEquivalent
      (Site.contextMorphismPreorderCategory
        (lensLawObject input Z.Carrier Z.toLensData.toLawStructure))
      ((g.lawContextFunctor.obj
        ⟨(completeLawOverlap
          (lensLawObject input Y.Carrier Y.toLensData.toLawStructure)).overlap
            (f.lawContextFunctor.obj ⟨base⟩).ctx
            (f.lawContextFunctor.obj ⟨left⟩).ctx
            (f.lawContextFunctor.obj ⟨right⟩).ctx⟩).ctx)
      ((completeLawOverlap
        (lensLawObject input Z.Carrier Z.toLensData.toLawStructure)).overlap
          (g.lawContextFunctor.obj ⟨(f.lawContextFunctor.obj ⟨base⟩).ctx⟩).ctx
          (g.lawContextFunctor.obj ⟨(f.lawContextFunctor.obj ⟨left⟩).ctx⟩).ctx
          (g.lawContextFunctor.obj ⟨(f.lawContextFunctor.obj ⟨right⟩).ctx⟩).ctx)
  first_extension : LensAATForwardExtensionCoherence input f
  second_extension : LensAATForwardExtensionCoherence input g
  point_map : (LensAATForwardMorphism.comp f g).sourceMap
      (lensAATGeometryReadingContext input X).extension.2 =
    (lensAATGeometryReadingContext input Z).extension.2
  get_map : ∀ state,
    (lensAATGeometryReadingContext input Z).extension.1.down.get
        ((LensAATForwardMorphism.comp f g).stateMap state) =
      (lensAATGeometryReadingContext input X).extension.1.down.get state
  put_map : ∀ state view,
    (LensAATForwardMorphism.comp f g).stateMap
        ((lensAATGeometryReadingContext input X).extension.1.down.put state view) =
      (lensAATGeometryReadingContext input Z).extension.1.down.put
        ((LensAATForwardMorphism.comp f g).stateMap state) view

/-- Construct every lens compositor field from the same primitive `f,g`. -/
theorem lensAATForwardOverlapExtensionSemanticCompositor
    (input : LensFamilyInput.{u})
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
    (g : LensAATForwardMorphism Y Z) :
    LensAATForwardOverlapExtensionSemanticCompositor input f g where
  comparison W V := fullFamilyProductComparisonSemanticLaws
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom)
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom) W V
  direct_overlap := lensAATForwardCompleteLawOverlap_readableEquivalent input
    (LensAATForwardMorphism.comp f g)
  first_overlap := lensAATForwardCompleteLawOverlap_readableEquivalent input f
  second_overlap base left right :=
    lensAATForwardCompleteLawOverlap_readableEquivalent input g
      (f.lawContextFunctor.obj ⟨base⟩).ctx
      (f.lawContextFunctor.obj ⟨left⟩).ctx
      (f.lawContextFunctor.obj ⟨right⟩).ctx
  first_extension := lensAATForwardExtensionCoherence input f
  second_extension := lensAATForwardExtensionCoherence input g
  point_map := congrArg g.sourceMap
    (lensAATForwardExtensionCoherence input f).point_map |>.trans
      (lensAATForwardExtensionCoherence input g).point_map
  get_map state := Eq.trans
    ((lensAATForwardExtensionCoherence input g).get_map (f.stateMap state))
    ((lensAATForwardExtensionCoherence input f).get_map state)
  put_map state view := Eq.trans
    (congrArg g.stateMap
      ((lensAATForwardExtensionCoherence input f).put_map state view))
    ((lensAATForwardExtensionCoherence input g).put_map (f.stateMap state) view)

/-! ## Protocol overlap and selected Extension laws -/

/-- Identity law for every source overlap and all named protocol operations. -/
structure ProtocolAATForwardOverlapExtensionSemanticUnit
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) : Prop
    extends ProtocolAATForwardExtensionCoherence input
      (ProtocolAATForwardMorphism.id X) where
  comparison : ∀ (W V : Site.ArchCtx
      (protocolLawObject input X.State X.toLawStructure)),
    FullFamilyProductComparisonSemanticLaws
      (sourceObject := protocolLawObject input X.State X.toLawStructure)
      (middleObject := protocolLawObject input X.State X.toLawStructure)
      (targetObject := protocolLawObject input X.State X.toLawStructure)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom) W V
  overlap : ∀ base left right,
    Site.ReadableEquivalent
      (Site.contextMorphismPreorderCategory
        (protocolLawObject input X.State X.toLawStructure))
      (((ProtocolAATForwardMorphism.id X).lawContextFunctor).obj
        ⟨(completeLawOverlap
          (protocolLawObject input X.State X.toLawStructure)).overlap
            base left right⟩).ctx
      ((completeLawOverlap
        (protocolLawObject input X.State X.toLawStructure)).overlap
          (((ProtocolAATForwardMorphism.id X).lawContextFunctor).obj ⟨base⟩).ctx
          (((ProtocolAATForwardMorphism.id X).lawContextFunctor).obj ⟨left⟩).ctx
          (((ProtocolAATForwardMorphism.id X).lawContextFunctor).obj ⟨right⟩).ctx)

/-- Construct the protocol overlap/Extension unit. -/
theorem protocolAATForwardOverlapExtensionSemanticUnit
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    ProtocolAATForwardOverlapExtensionSemanticUnit input X where
  toProtocolAATForwardExtensionCoherence :=
    protocolAATForwardExtensionCoherence input (ProtocolAATForwardMorphism.id X)
  comparison W V := fullFamilyProductComparisonSemanticLaws
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom)
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom) W V
  overlap := protocolAATForwardCompleteLawOverlap_readableEquivalent input
    (ProtocolAATForwardMorphism.id X)

/-- Direct and staged overlap/Extension composition for arbitrary composable
protocol morphisms. -/
structure ProtocolAATForwardOverlapExtensionSemanticCompositor
    (input : ProtocolFamilyInput.{u})
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z) : Prop where
  comparison : ∀ (W V : Site.ArchCtx
      (protocolLawObject input X.State X.toLawStructure)),
    FullFamilyProductComparisonSemanticLaws
      (sourceObject := protocolLawObject input X.State X.toLawStructure)
      (middleObject := protocolLawObject input Y.State Y.toLawStructure)
      (targetObject := protocolLawObject input Z.State Z.toLawStructure)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom) W V
  direct_overlap : ∀ base left right,
    Site.ReadableEquivalent
      (Site.contextMorphismPreorderCategory
        (protocolLawObject input Z.State Z.toLawStructure))
      (((ProtocolAATForwardMorphism.comp f g).lawContextFunctor).obj
        ⟨(completeLawOverlap
          (protocolLawObject input X.State X.toLawStructure)).overlap
            base left right⟩).ctx
      ((completeLawOverlap
        (protocolLawObject input Z.State Z.toLawStructure)).overlap
          (((ProtocolAATForwardMorphism.comp f g).lawContextFunctor).obj ⟨base⟩).ctx
          (((ProtocolAATForwardMorphism.comp f g).lawContextFunctor).obj ⟨left⟩).ctx
          (((ProtocolAATForwardMorphism.comp f g).lawContextFunctor).obj ⟨right⟩).ctx)
  first_overlap : ∀ base left right,
    Site.ReadableEquivalent
      (Site.contextMorphismPreorderCategory
        (protocolLawObject input Y.State Y.toLawStructure))
      ((f.lawContextFunctor.obj
        ⟨(completeLawOverlap
          (protocolLawObject input X.State X.toLawStructure)).overlap
            base left right⟩).ctx)
      ((completeLawOverlap
        (protocolLawObject input Y.State Y.toLawStructure)).overlap
          (f.lawContextFunctor.obj ⟨base⟩).ctx
          (f.lawContextFunctor.obj ⟨left⟩).ctx
          (f.lawContextFunctor.obj ⟨right⟩).ctx)
  second_overlap : ∀ base left right,
    Site.ReadableEquivalent
      (Site.contextMorphismPreorderCategory
        (protocolLawObject input Z.State Z.toLawStructure))
      ((g.lawContextFunctor.obj
        ⟨(completeLawOverlap
          (protocolLawObject input Y.State Y.toLawStructure)).overlap
            (f.lawContextFunctor.obj ⟨base⟩).ctx
            (f.lawContextFunctor.obj ⟨left⟩).ctx
            (f.lawContextFunctor.obj ⟨right⟩).ctx⟩).ctx)
      ((completeLawOverlap
        (protocolLawObject input Z.State Z.toLawStructure)).overlap
          (g.lawContextFunctor.obj ⟨(f.lawContextFunctor.obj ⟨base⟩).ctx⟩).ctx
          (g.lawContextFunctor.obj ⟨(f.lawContextFunctor.obj ⟨left⟩).ctx⟩).ctx
          (g.lawContextFunctor.obj ⟨(f.lawContextFunctor.obj ⟨right⟩).ctx⟩).ctx)
  first_extension : ProtocolAATForwardExtensionCoherence input f
  second_extension : ProtocolAATForwardExtensionCoherence input g
  point_map : (ProtocolAATForwardMorphism.comp f g).sourceMap
      (protocolAATGeometryReadingContext input X).extension.2 =
    (protocolAATGeometryReadingContext input Z).extension.2
  edge_map : ∀ {source target} (edge : input.schema.Edge source target)
      (state : X.State source),
    (ProtocolAATForwardMorphism.comp f g).stateMap target
        ((protocolAATGeometryReadingContext input X).extension.1.down.edgeAction
          edge state) =
      (protocolAATGeometryReadingContext input Z).extension.1.down.edgeAction edge
        ((ProtocolAATForwardMorphism.comp f g).stateMap source state)
  observation_map : ∀ vertex (state : X.State vertex),
    (protocolAATGeometryReadingContext input Z).extension.1.down.observe vertex
        ((ProtocolAATForwardMorphism.comp f g).stateMap vertex state) =
      (protocolAATGeometryReadingContext input X).extension.1.down.observe
        vertex state

/-- Construct every protocol compositor field from the same primitive `f,g`. -/
theorem protocolAATForwardOverlapExtensionSemanticCompositor
    (input : ProtocolFamilyInput.{u})
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z) :
    ProtocolAATForwardOverlapExtensionSemanticCompositor input f g where
  comparison W V := fullFamilyProductComparisonSemanticLaws
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom)
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom) W V
  direct_overlap := protocolAATForwardCompleteLawOverlap_readableEquivalent input
    (ProtocolAATForwardMorphism.comp f g)
  first_overlap :=
    protocolAATForwardCompleteLawOverlap_readableEquivalent input f
  second_overlap base left right :=
    protocolAATForwardCompleteLawOverlap_readableEquivalent input g
      (f.lawContextFunctor.obj ⟨base⟩).ctx
      (f.lawContextFunctor.obj ⟨left⟩).ctx
      (f.lawContextFunctor.obj ⟨right⟩).ctx
  first_extension := protocolAATForwardExtensionCoherence input f
  second_extension := protocolAATForwardExtensionCoherence input g
  point_map := congrArg g.sourceMap
    (protocolAATForwardExtensionCoherence input f).point_map |>.trans
      (protocolAATForwardExtensionCoherence input g).point_map
  edge_map edge state := Eq.trans
    (congrArg (g.stateMap _)
      ((protocolAATForwardExtensionCoherence input f).edge_map edge state))
    ((protocolAATForwardExtensionCoherence input g).edge_map edge
      (f.stateMap _ state))
  observation_map vertex state := Eq.trans
    ((protocolAATForwardExtensionCoherence input g).observation_map vertex
      (f.stateMap vertex state))
    ((protocolAATForwardExtensionCoherence input f).observation_map vertex state)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
