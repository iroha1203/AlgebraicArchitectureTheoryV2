import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardEquationAggregate
import Formal.Util.AssertStandardAxioms

/-!
# Semantic forward-coverage functoriality for CS geometry

This file proves identity and composition for the generated required and
violation coordinate maps, then composes the corresponding visibility
witnesses through the actual intermediate restriction.  It does not identify
proof records by proof irrelevance.

The composite visibility constructor accepts only the first witness and the
second primitive observable equation.  It builds the second restriction from
the first target restriction, so the intermediate local value is retained
rather than replaced by an unrelated existential witness.
-/

namespace AAT.AG.RealizationReconstruction

universe u

/-! ## Honest direct-versus-successive restriction transport -/

/-- Forget the intermediate full-family rebase while retaining every map
component of a restriction into the final reading. -/
def flattenSuccessiveFullFamilyContextMap {U : AtomCarrier.{u}}
    {sourceObject middleObject targetObject : ArchitectureObject U}
    (middle_all : ∀ atom, middleObject.configuration.family.mem atom)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    {W : Site.ArchCtx sourceObject} {targetReading : Site.ArchCtx targetObject}
    (f : Site.ContextMorphism
      (fullFamilyContextRebase targetObject target_all
        (fullFamilyContextRebase middleObject middle_all W)) targetReading) :
    Site.ContextMorphism
      (fullFamilyContextRebase targetObject target_all W) targetReading where
  supportMap := f.supportMap
  axisMap := f.axisMap
  observableRestrict := f.observableRestrict

/-- Flattening preserves the complete restriction predicate fieldwise. -/
theorem flattenSuccessiveFullFamilyContextMap_isRestriction
    {U : AtomCarrier.{u}}
    {sourceObject middleObject targetObject : ArchitectureObject U}
    (middle_all : ∀ atom, middleObject.configuration.family.mem atom)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    {W : Site.ArchCtx sourceObject} {targetReading : Site.ArchCtx targetObject}
    (f : Site.ContextMorphism
      (fullFamilyContextRebase targetObject target_all
        (fullFamilyContextRebase middleObject middle_all W)) targetReading)
    (hf : f.IsRestriction) :
    (flattenSuccessiveFullFamilyContextMap middle_all target_all f).IsRestriction :=
  hf

/-- Compose visibility through the first witness's actual target restriction.
The second target restriction is constructed internally and flattened from
the successive rebase to the direct final rebase. -/
theorem ForwardObservableVisibility.compOfForwardEquation
    {U : AtomCarrier.{u}}
    {sourceObject middleObject targetObject : ArchitectureObject U}
    (middle_all : ∀ atom, middleObject.configuration.family.mem atom)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (sourceReading : Site.ArchCtx sourceObject)
    (middleReading : Site.ArchCtx middleObject)
    (targetReading : Site.ArchCtx targetObject)
    (middleTargetSupport : middleReading.Support → targetReading.Support)
    (middleTargetAxis : middleReading.Axis → targetReading.Axis)
    (middleTargetSupport_reads : ∀ {support atom},
      middleReading.minimal.supportReads support atom →
        targetReading.minimal.supportReads (middleTargetSupport support) atom)
    (middleTargetAxis_reads : ∀ {axis},
      middleReading.minimal.axisReads axis →
        targetReading.minimal.axisReads (middleTargetAxis axis))
    (firstForward : sourceReading.Observable → middleReading.Observable)
    (secondForward : middleReading.Observable → targetReading.Observable)
    {W : Site.ArchCtx sourceObject}
    (sourceObservable : sourceReading.Observable)
    (middleObservable : middleReading.Observable)
    (targetObservable : targetReading.Observable)
    (hFirst : ForwardObservableVisibility (W := W) middle_all sourceReading
      middleReading firstForward sourceObservable middleObservable)
    (hSecondForward : secondForward middleObservable = targetObservable) :
    ForwardObservableVisibility (W := W) target_all sourceReading targetReading
      (secondForward ∘ firstForward) sourceObservable targetObservable := by
  rcases hFirst with
    ⟨sourceMap, hSource, hSourceLocal, middleMap, hMiddle,
      hMiddleLocal, hFirstForward, hMiddleSource⟩
  let targetMap := fullFamilyContextToTargetReadingAt target_all
    middleReading targetReading middleTargetSupport middleTargetAxis
    middleMap middleObservable
  have hTarget : targetMap.IsRestriction :=
    fullFamilyContextToTargetReadingAt_isRestriction target_all middleReading
      targetReading middleTargetSupport middleTargetAxis
      middleTargetSupport_reads middleTargetAxis_reads middleMap hMiddle
      middleObservable hMiddleLocal
  refine ⟨sourceMap, hSource, hSourceLocal,
    flattenSuccessiveFullFamilyContextMap middle_all target_all targetMap,
    flattenSuccessiveFullFamilyContextMap_isRestriction
      middle_all target_all targetMap hTarget, hMiddleLocal, ?_, ?_⟩
  · exact congrArg secondForward hFirstForward |>.trans hSecondForward
  · exact hMiddleSource

/-! ## Lens coordinate laws -/

namespace LensAATForwardMorphism

/-- The generated required-coordinate map is the identity at a primitive
identity morphism. -/
@[simp] theorem forwardRequiredCoordinate_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference)
    (coordinate : (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).RequiredCoordinate) :
    lensAATForwardRequiredCoordinate input (id X) coordinate = coordinate := by
  rcases coordinate with ⟨⟨⟨index⟩, required⟩, atom⟩
  simp [lensAATForwardRequiredCoordinate, lawIndexMap_id]

/-- The generated required-coordinate map preserves primitive composition. -/
@[simp] theorem forwardRequiredCoordinate_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    (coordinate : (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).RequiredCoordinate) :
    lensAATForwardRequiredCoordinate input (comp f g) coordinate =
      lensAATForwardRequiredCoordinate input g
        (lensAATForwardRequiredCoordinate input f coordinate) := by
  rcases coordinate with ⟨⟨⟨index⟩, required⟩, atom⟩
  simp [lensAATForwardRequiredCoordinate, lawIndexMap_comp]

/-- The generated violation-coordinate map is the identity at a primitive
identity morphism. -/
@[simp] theorem forwardCoordinate_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference)
    (coordinate : (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).Coordinate) :
    lensAATForwardCoordinate input (id X) coordinate = coordinate := by
  rcases coordinate with ⟨⟨index⟩, atom⟩
  simp [lensAATForwardCoordinate, lawIndexMap_id]

/-- The generated violation-coordinate map preserves primitive composition. -/
@[simp] theorem forwardCoordinate_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    (coordinate : (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).Coordinate) :
    lensAATForwardCoordinate input (comp f g) coordinate =
      lensAATForwardCoordinate input g
        (lensAATForwardCoordinate input f coordinate) := by
  rcases coordinate with ⟨⟨index⟩, atom⟩
  simp [lensAATForwardCoordinate, lawIndexMap_comp]

/-- Required-coordinate visibility at identity retains the exact coordinate
and constructs its direct identity target restriction. -/
theorem forwardEquationCoordinateCoherent_id
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference)
    {W : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (coordinate : (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).RequiredCoordinate)
    (hvisible : (lensAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
      W coordinate) :
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom)
      (lensAATGeometryReadingContext input X)
      (lensAATGeometryReadingContext input X)
      (id X).lawCoordinateMap
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        LensLawCoordinateRing input X.Carrier)
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        LensLawCoordinateRing input X.Carrier) := by
  simpa only [lawIndexMap_id] using
    lensAATForwardEquationCoordinateCoherent input (id X) coordinate hvisible

/-- Violation-coordinate visibility at identity retains the exact coordinate
and constructs its direct identity target restriction. -/
theorem forwardViolationCoordinateCoherent_id
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference)
    {W : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (coordinate : (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).Coordinate)
    (hvisible : (lensAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
      W coordinate) :
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom)
      (lensAATGeometryReadingContext input X)
      (lensAATGeometryReadingContext input X)
      (id X).lawCoordinateMap
      (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier)
      (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier) := by
  simpa only [forwardCoordinate_id] using
    lensAATForwardViolationCoordinateCoherent input (id X) coordinate hvisible

/-- Canonical lens required-coordinate visibility for a composite is
constructed through the same intermediate restriction and flattened to the
direct target rebase. -/
theorem forwardEquationCoordinateCoherent_comp
    (input : LensFamilyInput.{u})
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    {W : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (coordinate : (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).RequiredCoordinate)
    (hvisible : (lensAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
      W coordinate) :
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom)
      (lensAATGeometryReadingContext input X)
      (lensAATGeometryReadingContext input Z)
      (comp f g).lawCoordinateMap
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        LensLawCoordinateRing input X.Carrier)
      (MvPolynomial.X
        ((lensAATForwardRequiredCoordinate input (comp f g) coordinate).1.1,
          (lensAATForwardRequiredCoordinate input (comp f g) coordinate).2) :
        LensLawCoordinateRing input Z.Carrier) := by
  have hFirst := lensAATForwardEquationCoordinateCoherent input f coordinate hvisible
  have hSecond :
      g.lawCoordinateMap
          (MvPolynomial.X
            ((lensAATForwardRequiredCoordinate input f coordinate).1.1,
              (lensAATForwardRequiredCoordinate input f coordinate).2)) =
        MvPolynomial.X
          ((lensAATForwardRequiredCoordinate input g
            (lensAATForwardRequiredCoordinate input f coordinate)).1.1,
           (lensAATForwardRequiredCoordinate input g
            (lensAATForwardRequiredCoordinate input f coordinate)).2) := by
    rcases coordinate with ⟨⟨⟨index⟩, required⟩, atom⟩
    exact lensLawCoordinateMap_violation input g.lawHom
      (f.lawIndexMap index) atom
  have hComp := ForwardObservableVisibility.compOfForwardEquation
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom)
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom)
    (lensAATGeometryReadingContext input X)
    (lensAATGeometryReadingContext input Y)
    (lensAATGeometryReadingContext input Z)
    _root_.id _root_.id (fun h => h)
    (fun {axis} _ => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point)
        (show LensAATAtom input from axis))
    f.lawCoordinateMap g.lawCoordinateMap
    (MvPolynomial.X (coordinate.1.1, coordinate.2) :
      LensLawCoordinateRing input X.Carrier)
    (MvPolynomial.X
      ((lensAATForwardRequiredCoordinate input f coordinate).1.1,
        (lensAATForwardRequiredCoordinate input f coordinate).2) :
      LensLawCoordinateRing input Y.Carrier)
    (MvPolynomial.X
      ((lensAATForwardRequiredCoordinate input g
        (lensAATForwardRequiredCoordinate input f coordinate)).1.1,
       (lensAATForwardRequiredCoordinate input g
        (lensAATForwardRequiredCoordinate input f coordinate)).2) :
      LensLawCoordinateRing input Z.Carrier)
    hFirst hSecond
  simpa only [lawCoordinateMap_comp, RingHom.coe_comp, Function.comp_apply,
    forwardRequiredCoordinate_comp] using hComp

/-- Canonical lens violation visibility for a composite is constructed
successively through the same intermediate restriction and then flattened to
the direct target rebase. -/
theorem forwardViolationCoordinateCoherent_comp
    (input : LensFamilyInput.{u})
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    {W : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (coordinate : (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).Coordinate)
    (hvisible : (lensAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
      W coordinate) :
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom)
      (lensAATGeometryReadingContext input X)
      (lensAATGeometryReadingContext input Z)
      (comp f g).lawCoordinateMap
      (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier)
      (MvPolynomial.X
        (lensAATForwardCoordinate input (comp f g) coordinate) :
          LensLawCoordinateRing input Z.Carrier) := by
  have hFirst := lensAATForwardViolationCoordinateCoherent input f coordinate hvisible
  have hSecond :
      g.lawCoordinateMap
          (MvPolynomial.X (lensAATForwardCoordinate input f coordinate)) =
        MvPolynomial.X (lensAATForwardCoordinate input g
          (lensAATForwardCoordinate input f coordinate)) := by
    rcases coordinate with ⟨⟨index⟩, atom⟩
    exact lensLawCoordinateMap_violation input g.lawHom
      (f.lawIndexMap index) atom
  have hComp := ForwardObservableVisibility.compOfForwardEquation
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom)
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom)
    (lensAATGeometryReadingContext input X)
    (lensAATGeometryReadingContext input Y)
    (lensAATGeometryReadingContext input Z)
    _root_.id _root_.id (fun h => h)
    (fun {axis} _ => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point)
        (show LensAATAtom input from axis))
    f.lawCoordinateMap g.lawCoordinateMap
    (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier)
    (MvPolynomial.X (lensAATForwardCoordinate input f coordinate) :
      LensLawCoordinateRing input Y.Carrier)
    (MvPolynomial.X (lensAATForwardCoordinate input g
      (lensAATForwardCoordinate input f coordinate)) :
        LensLawCoordinateRing input Z.Carrier)
    hFirst hSecond
  simpa only [lawCoordinateMap_comp, RingHom.coe_comp, Function.comp_apply,
    forwardCoordinate_comp] using hComp

/-- Support visibility transported successively by two lens morphisms agrees
with visibility in the direct composite target context. -/
theorem forwardSupportVisible_comp
    (input : LensFamilyInput.{u})
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    {W : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (atom : LensAATAtom input)
    (hvisible : (lensAATGeometryCoverageRequirements input X).supportVisibleOn
      W atom) :
    (lensAATGeometryCoverageRequirements input Z).supportVisibleOn
      (((comp f g).lawContextFunctor).obj ⟨W⟩).ctx atom := by
  have hMiddle := lensAATForwardSupportVisible input f atom hvisible
  have hTarget := lensAATForwardSupportVisible input g atom hMiddle
  rw [lawContextFunctor_comp_obj]
  exact hTarget

/-- Boundary visibility transported successively by two lens morphisms agrees
with visibility between the direct composite target contexts. -/
theorem forwardBoundaryVisible_comp
    (input : LensFamilyInput.{u})
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z)
    {W base : Site.ArchCtx
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)}
    (hvisible : (lensAATGeometryCoverageRequirements input X).boundaryVisibleOn
      W base) :
    (lensAATGeometryCoverageRequirements input Z).boundaryVisibleOn
      (((comp f g).lawContextFunctor).obj ⟨W⟩).ctx
      (((comp f g).lawContextFunctor).obj ⟨base⟩).ctx := by
  have hMiddle := lensAATForwardBoundaryVisible input f hvisible
  have hTarget := lensAATForwardBoundaryVisible input g hMiddle
  rw [lawContextFunctor_comp_obj, lawContextFunctor_comp_obj]
  exact hTarget

end LensAATForwardMorphism

/-! ## Protocol coordinate laws -/

namespace ProtocolAATForwardMorphism

/-- The generated protocol required-coordinate map is identity at a primitive
identity morphism. -/
@[simp] theorem forwardRequiredCoordinate_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (coordinate : (protocolLawEquationSystem input X.State
      X.toLawStructure).RequiredCoordinate) :
    protocolAATForwardRequiredCoordinate input (id X) coordinate = coordinate := by
  rcases coordinate with ⟨⟨⟨index⟩, required⟩, atom⟩
  simp [protocolAATForwardRequiredCoordinate, lawIndexMap_id]

/-- The generated protocol required-coordinate map preserves composition. -/
@[simp] theorem forwardRequiredCoordinate_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) (g : ProtocolAATForwardMorphism Y Z)
    (coordinate : (protocolLawEquationSystem input X.State
      X.toLawStructure).RequiredCoordinate) :
    protocolAATForwardRequiredCoordinate input (comp f g) coordinate =
      protocolAATForwardRequiredCoordinate input g
        (protocolAATForwardRequiredCoordinate input f coordinate) := by
  rcases coordinate with ⟨⟨⟨index⟩, required⟩, atom⟩
  simp [protocolAATForwardRequiredCoordinate, lawIndexMap_comp]

/-- The generated protocol violation-coordinate map is identity at a
primitive identity morphism. -/
@[simp] theorem forwardCoordinate_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    (coordinate : (protocolLawEquationSystem input X.State
      X.toLawStructure).Coordinate) :
    protocolAATForwardCoordinate input (id X) coordinate = coordinate := by
  rcases coordinate with ⟨⟨index⟩, atom⟩
  simp [protocolAATForwardCoordinate, lawIndexMap_id]

/-- The generated protocol violation-coordinate map preserves composition. -/
@[simp] theorem forwardCoordinate_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z)
    (coordinate : (protocolLawEquationSystem input X.State
      X.toLawStructure).Coordinate) :
    protocolAATForwardCoordinate input (comp f g) coordinate =
      protocolAATForwardCoordinate input g
        (protocolAATForwardCoordinate input f coordinate) := by
  rcases coordinate with ⟨⟨index⟩, atom⟩
  simp [protocolAATForwardCoordinate, lawIndexMap_comp]

/-- Protocol required-coordinate visibility at identity retains the exact
coordinate and constructs its direct identity target restriction. -/
theorem forwardEquationCoordinateCoherent_id
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    {W : Site.ArchCtx
      (protocolLawObject input X.State X.toLawStructure)}
    (coordinate : (protocolLawEquationSystem input X.State
      X.toLawStructure).RequiredCoordinate)
    (hvisible : (protocolAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
      W coordinate) :
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (protocolAATGeometryReadingContext input X)
      (protocolAATGeometryReadingContext input X)
      (id X).lawCoordinateMap
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        ProtocolLawCoordinateRing input X.State)
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        ProtocolLawCoordinateRing input X.State) := by
  simpa only [lawIndexMap_id] using
    protocolAATForwardEquationCoordinateCoherent input (id X) coordinate hvisible

/-- Protocol violation-coordinate visibility at identity retains the exact
coordinate and constructs its direct identity target restriction. -/
theorem forwardViolationCoordinateCoherent_id
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    {W : Site.ArchCtx
      (protocolLawObject input X.State X.toLawStructure)}
    (coordinate : (protocolLawEquationSystem input X.State
      X.toLawStructure).Coordinate)
    (hvisible : (protocolAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
      W coordinate) :
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (protocolAATGeometryReadingContext input X)
      (protocolAATGeometryReadingContext input X)
      (id X).lawCoordinateMap
      (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State)
      (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State) := by
  simpa only [forwardCoordinate_id] using
    protocolAATForwardViolationCoordinateCoherent input (id X) coordinate hvisible

/-- Canonical protocol required-coordinate visibility for a composite is
constructed through the same intermediate restriction and flattened to the
direct target rebase. -/
theorem forwardEquationCoordinateCoherent_comp
    (input : ProtocolFamilyInput.{u})
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z)
    {W : Site.ArchCtx (protocolLawObject input X.State X.toLawStructure)}
    (coordinate : (protocolLawEquationSystem input X.State
      X.toLawStructure).RequiredCoordinate)
    (hvisible : (protocolAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
      W coordinate) :
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (protocolAATGeometryReadingContext input X)
      (protocolAATGeometryReadingContext input Z)
      (comp f g).lawCoordinateMap
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        ProtocolLawCoordinateRing input X.State)
      (MvPolynomial.X
        ((protocolAATForwardRequiredCoordinate input (comp f g) coordinate).1.1,
          (protocolAATForwardRequiredCoordinate input (comp f g) coordinate).2) :
        ProtocolLawCoordinateRing input Z.State) := by
  have hFirst := protocolAATForwardEquationCoordinateCoherent input f coordinate hvisible
  have hSecond :
      g.lawCoordinateMap
          (MvPolynomial.X
            ((protocolAATForwardRequiredCoordinate input f coordinate).1.1,
              (protocolAATForwardRequiredCoordinate input f coordinate).2)) =
        MvPolynomial.X
          ((protocolAATForwardRequiredCoordinate input g
            (protocolAATForwardRequiredCoordinate input f coordinate)).1.1,
           (protocolAATForwardRequiredCoordinate input g
            (protocolAATForwardRequiredCoordinate input f coordinate)).2) := by
    rcases coordinate with ⟨⟨⟨index⟩, required⟩, atom⟩
    exact protocolLawCoordinateMap_violation input g.lawHom
      (f.lawIndexMap index) atom
  have hComp := ForwardObservableVisibility.compOfForwardEquation
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom)
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom)
    (protocolAATGeometryReadingContext input X)
    (protocolAATGeometryReadingContext input Y)
    (protocolAATGeometryReadingContext input Z)
    _root_.id _root_.id (fun h => h)
    (fun {axis} _ => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point)
        (show ProtocolAATAtom input from axis))
    f.lawCoordinateMap g.lawCoordinateMap
    (MvPolynomial.X (coordinate.1.1, coordinate.2) :
      ProtocolLawCoordinateRing input X.State)
    (MvPolynomial.X
      ((protocolAATForwardRequiredCoordinate input f coordinate).1.1,
        (protocolAATForwardRequiredCoordinate input f coordinate).2) :
      ProtocolLawCoordinateRing input Y.State)
    (MvPolynomial.X
      ((protocolAATForwardRequiredCoordinate input g
        (protocolAATForwardRequiredCoordinate input f coordinate)).1.1,
       (protocolAATForwardRequiredCoordinate input g
        (protocolAATForwardRequiredCoordinate input f coordinate)).2) :
      ProtocolLawCoordinateRing input Z.State)
    hFirst hSecond
  simpa only [lawCoordinateMap_comp, RingHom.coe_comp, Function.comp_apply,
    forwardRequiredCoordinate_comp] using hComp

/-- Canonical protocol violation visibility for a composite is constructed
through the same intermediate restriction and flattened to the direct target
rebase. -/
theorem forwardViolationCoordinateCoherent_comp
    (input : ProtocolFamilyInput.{u})
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z)
    {W : Site.ArchCtx (protocolLawObject input X.State X.toLawStructure)}
    (coordinate : (protocolLawEquationSystem input X.State
      X.toLawStructure).Coordinate)
    (hvisible : (protocolAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
      W coordinate) :
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (protocolAATGeometryReadingContext input X)
      (protocolAATGeometryReadingContext input Z)
      (comp f g).lawCoordinateMap
      (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State)
      (MvPolynomial.X
        (protocolAATForwardCoordinate input (comp f g) coordinate) :
          ProtocolLawCoordinateRing input Z.State) := by
  have hFirst := protocolAATForwardViolationCoordinateCoherent input f coordinate hvisible
  have hSecond :
      g.lawCoordinateMap
          (MvPolynomial.X (protocolAATForwardCoordinate input f coordinate)) =
        MvPolynomial.X (protocolAATForwardCoordinate input g
          (protocolAATForwardCoordinate input f coordinate)) := by
    rcases coordinate with ⟨⟨index⟩, atom⟩
    exact protocolLawCoordinateMap_violation input g.lawHom
      (f.lawIndexMap index) atom
  have hComp := ForwardObservableVisibility.compOfForwardEquation
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom)
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom)
    (protocolAATGeometryReadingContext input X)
    (protocolAATGeometryReadingContext input Y)
    (protocolAATGeometryReadingContext input Z)
    _root_.id _root_.id (fun h => h)
    (fun {axis} _ => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point)
        (show ProtocolAATAtom input from axis))
    f.lawCoordinateMap g.lawCoordinateMap
    (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State)
    (MvPolynomial.X (protocolAATForwardCoordinate input f coordinate) :
      ProtocolLawCoordinateRing input Y.State)
    (MvPolynomial.X (protocolAATForwardCoordinate input g
      (protocolAATForwardCoordinate input f coordinate)) :
        ProtocolLawCoordinateRing input Z.State)
    hFirst hSecond
  simpa only [lawCoordinateMap_comp, RingHom.coe_comp, Function.comp_apply,
    forwardCoordinate_comp] using hComp

/-- Support visibility transported successively by two protocol morphisms
agrees with visibility in the direct composite target context. -/
theorem forwardSupportVisible_comp
    (input : ProtocolFamilyInput.{u})
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z)
    {W : Site.ArchCtx (protocolLawObject input X.State X.toLawStructure)}
    (atom : ProtocolAATAtom input)
    (hvisible : (protocolAATGeometryCoverageRequirements input X).supportVisibleOn
      W atom) :
    (protocolAATGeometryCoverageRequirements input Z).supportVisibleOn
      (((comp f g).lawContextFunctor).obj ⟨W⟩).ctx atom := by
  have hMiddle := protocolAATForwardSupportVisible input f atom hvisible
  have hTarget := protocolAATForwardSupportVisible input g atom hMiddle
  rw [lawContextFunctor_comp_obj]
  exact hTarget

/-- Boundary visibility transported successively by two protocol morphisms
agrees with visibility between the direct composite target contexts. -/
theorem forwardBoundaryVisible_comp
    (input : ProtocolFamilyInput.{u})
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z)
    {W base : Site.ArchCtx
      (protocolLawObject input X.State X.toLawStructure)}
    (hvisible :
      (protocolAATGeometryCoverageRequirements input X).boundaryVisibleOn
        W base) :
    (protocolAATGeometryCoverageRequirements input Z).boundaryVisibleOn
      (((comp f g).lawContextFunctor).obj ⟨W⟩).ctx
      (((comp f g).lawContextFunctor).obj ⟨base⟩).ctx := by
  have hMiddle := protocolAATForwardBoundaryVisible input f hvisible
  have hTarget := protocolAATForwardBoundaryVisible input g hMiddle
  rw [lawContextFunctor_comp_obj, lawContextFunctor_comp_obj]
  exact hTarget

end ProtocolAATForwardMorphism

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
