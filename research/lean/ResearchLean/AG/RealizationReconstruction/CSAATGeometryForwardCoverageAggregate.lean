import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardCoverageFunctoriality
import Formal.Util.AssertStandardAxioms

/-!
# Canonical semantic coverage aggregate laws

This file packages all nine source-role coverage conclusions for identity and
composition in the lens and protocol translations.  The structures are
outputs: their constructors accept only a realization or composable primitive
morphisms and generate every field from the canonical forward construction.

No equality between proposition-valued coverage records is asserted.  For
composition, coordinate visibility reuses the actual intermediate restriction
constructed in the preceding module; support and boundary use their staged
transport laws; required markers are chained through both canonical maps.
-/

namespace AAT.AG.RealizationReconstruction

universe u

/-! ## Explicit intermediate visibility chains -/

/-- A two-stage observable-visibility witness retaining the actual source,
middle, and direct-target restrictions and both local-value equations.  This
is stronger than the collapsed direct visibility proposition because the
intermediate witness is part of the conclusion. -/
structure ForwardObservableVisibilityChainData {U : AtomCarrier.{u}}
    {sourceObject middleObject targetObject : ArchitectureObject U}
    (middle_all : ∀ atom, middleObject.configuration.family.mem atom)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (sourceReading : Site.ArchCtx sourceObject)
    (middleReading : Site.ArchCtx middleObject)
    (targetReading : Site.ArchCtx targetObject)
    (firstForward : sourceReading.Observable → middleReading.Observable)
    (secondForward : middleReading.Observable → targetReading.Observable)
    {W : Site.ArchCtx sourceObject}
    (sourceObservable : sourceReading.Observable)
    (middleObservable : middleReading.Observable)
    (targetObservable : targetReading.Observable) where
  sourceMap : Site.ContextMorphism W sourceReading
  sourceMap_restriction : sourceMap.IsRestriction
  source_readable : W.minimal.observableReads
    (sourceMap.observableRestrict sourceObservable)
  middleMap : Site.ContextMorphism
    (fullFamilyContextRebase middleObject middle_all W) middleReading
  middleMap_restriction : middleMap.IsRestriction
  middle_readable : W.minimal.observableReads
    (middleMap.observableRestrict middleObservable)
  targetMap : Site.ContextMorphism
    (fullFamilyContextRebase targetObject target_all W) targetReading
  targetMap_restriction : targetMap.IsRestriction
  target_readable : W.minimal.observableReads
    (targetMap.observableRestrict targetObservable)
  firstForward_eq : firstForward sourceObservable = middleObservable
  secondForward_eq : secondForward middleObservable = targetObservable
  middle_local_eq_source :
    middleMap.observableRestrict middleObservable =
      sourceMap.observableRestrict sourceObservable
  target_local_eq_middle :
    targetMap.observableRestrict targetObservable =
      middleMap.observableRestrict middleObservable

/-- Build an explicit visibility chain from the first canonical witness and a
second primitive observable equation.  The second restriction is constructed
from the retained middle map and then flattened to the direct target rebase. -/
theorem ForwardObservableVisibility.explicitChain
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
    Nonempty (ForwardObservableVisibilityChainData (W := W) middle_all
      target_all sourceReading middleReading targetReading firstForward
      secondForward sourceObservable middleObservable targetObservable) := by
  rcases hFirst with
    ⟨sourceMap, hSource, hSourceLocal, middleMap, hMiddle,
      hMiddleLocal, hFirstForward, hMiddleSource⟩
  let successiveTargetMap := fullFamilyContextToTargetReadingAt target_all
    middleReading targetReading middleTargetSupport middleTargetAxis
    middleMap middleObservable
  have hSuccessiveTarget : successiveTargetMap.IsRestriction :=
    fullFamilyContextToTargetReadingAt_isRestriction target_all middleReading
      targetReading middleTargetSupport middleTargetAxis
      middleTargetSupport_reads middleTargetAxis_reads middleMap hMiddle
      middleObservable hMiddleLocal
  let directTargetMap := flattenSuccessiveFullFamilyContextMap
    middle_all target_all successiveTargetMap
  exact ⟨{
    sourceMap := sourceMap
    sourceMap_restriction := hSource
    source_readable := hSourceLocal
    middleMap := middleMap
    middleMap_restriction := hMiddle
    middle_readable := hMiddleLocal
    targetMap := directTargetMap
    targetMap_restriction :=
      flattenSuccessiveFullFamilyContextMap_isRestriction
        middle_all target_all successiveTargetMap hSuccessiveTarget
    target_readable := hMiddleLocal
    firstForward_eq := hFirstForward
    secondForward_eq := hSecondForward
    middle_local_eq_source := hMiddleSource
    target_local_eq_middle := rfl
  }⟩

/-! ## Lens semantic unit and compositor -/

/-- All nine canonical lens coverage conclusions at identity, together with
the exact unchanged coordinate and visibility laws.  No negative instance
exists because the theorem below constructs this proposition for every lens
realization from the primitive identity. -/
structure LensAATForwardCoverageSemanticUnit
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) : Prop
    extends LensAATForwardCoverageImage input
      (LensAATForwardMorphism.id X) where
  requiredCoordinate_id : ∀ coordinate,
    lensAATForwardRequiredCoordinate input
      (LensAATForwardMorphism.id X) coordinate = coordinate
  violationCoordinate_id : ∀ coordinate,
    lensAATForwardCoordinate input
      (LensAATForwardMorphism.id X) coordinate = coordinate
  equationVisibility_id : ∀ W coordinate,
    (lensAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
      W coordinate →
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom)
      (lensAATGeometryReadingContext input X)
      (lensAATGeometryReadingContext input X)
      (LensAATForwardMorphism.id X).lawCoordinateMap
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        LensLawCoordinateRing input X.Carrier)
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        LensLawCoordinateRing input X.Carrier)
  violationVisibility_id : ∀ W coordinate,
    (lensAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
      W coordinate →
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := lensAATCarrier input) (.point) atom)
      (lensAATGeometryReadingContext input X)
      (lensAATGeometryReadingContext input X)
      (LensAATForwardMorphism.id X).lawCoordinateMap
      (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier)
      (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier)

/-- Construct the lens semantic coverage unit from the primitive identity. -/
theorem lensAATForwardCoverageSemanticUnit
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    LensAATForwardCoverageSemanticUnit input X where
  toLensAATForwardCoverageImage :=
    lensAATForwardCoverageImage input (LensAATForwardMorphism.id X)
  requiredCoordinate_id :=
    LensAATForwardMorphism.forwardRequiredCoordinate_id X
  violationCoordinate_id :=
    LensAATForwardMorphism.forwardCoordinate_id X
  equationVisibility_id := by
    intro W coordinate
    exact LensAATForwardMorphism.forwardEquationCoordinateCoherent_id
      input X coordinate
  violationVisibility_id := by
    intro W coordinate
    exact LensAATForwardMorphism.forwardViolationCoordinateCoherent_id
      input X coordinate

/-- All nine direct-composite lens coverage conclusions, with exact successive
coordinate laws.  The constructor below builds required/support/boundary and
visibility fields through the two primitive morphisms.  No negative instance
exists because it constructs this proposition for every composable pair. -/
structure LensAATForwardCoverageSemanticCompositor
    (input : LensFamilyInput.{u})
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
    (g : LensAATForwardMorphism Y Z) : Prop
    extends LensAATForwardCoverageImage input
      (LensAATForwardMorphism.comp f g) where
  requiredCoordinate_comp : ∀ coordinate,
    lensAATForwardRequiredCoordinate input
      (LensAATForwardMorphism.comp f g) coordinate =
    lensAATForwardRequiredCoordinate input g
      (lensAATForwardRequiredCoordinate input f coordinate)
  violationCoordinate_comp : ∀ coordinate,
    lensAATForwardCoordinate input
      (LensAATForwardMorphism.comp f g) coordinate =
    lensAATForwardCoordinate input g
      (lensAATForwardCoordinate input f coordinate)
  requiredSupport_stage : ∀ atom,
    (lensAATGeometryCoverageRequirements input X).requiredSupport atom →
      (lensAATGeometryCoverageRequirements input Y).requiredSupport atom
  requiredEquationCoordinate_stage : ∀ coordinate,
    (lensAATGeometryCoverageRequirements input X).requiredEquationCoordinate
        coordinate →
      (lensAATGeometryCoverageRequirements input Y).requiredEquationCoordinate
        (lensAATForwardRequiredCoordinate input f coordinate)
  selectedViolationWitness_stage : ∀ coordinate,
    (lensAATGeometryCoverageRequirements input X).selectedViolationWitness
        coordinate →
      (lensAATGeometryCoverageRequirements input Y).selectedViolationWitness
        (lensAATForwardCoordinate input f coordinate)
  requiredAxis_stage : ∀ axis,
    (lensAATGeometryCoverageRequirements input X).requiredAxis axis →
      (lensAATGeometryCoverageRequirements input Y).requiredAxis axis
  supportVisibleOn_stage : ∀ W atom,
    (lensAATGeometryCoverageRequirements input X).supportVisibleOn W atom →
      (lensAATGeometryCoverageRequirements input Y).supportVisibleOn
        ((f.lawContextFunctor).obj ⟨W⟩).ctx atom
  equationCoordinateVisibility_chain : ∀ W coordinate,
    (lensAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
        W coordinate →
      Nonempty (ForwardObservableVisibilityChainData (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := lensAATCarrier input) (.point) atom)
        (fun atom => typedRoleConfiguration_mem
          (U := lensAATCarrier input) (.point) atom)
        (lensAATGeometryReadingContext input X)
        (lensAATGeometryReadingContext input Y)
        (lensAATGeometryReadingContext input Z)
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
          LensLawCoordinateRing input Z.Carrier))
  violationWitnessVisibility_chain : ∀ W coordinate,
    (lensAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
        W coordinate →
      Nonempty (ForwardObservableVisibilityChainData (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := lensAATCarrier input) (.point) atom)
        (fun atom => typedRoleConfiguration_mem
          (U := lensAATCarrier input) (.point) atom)
        (lensAATGeometryReadingContext input X)
        (lensAATGeometryReadingContext input Y)
        (lensAATGeometryReadingContext input Z)
        f.lawCoordinateMap g.lawCoordinateMap
        (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier)
        (MvPolynomial.X (lensAATForwardCoordinate input f coordinate) :
          LensLawCoordinateRing input Y.Carrier)
        (MvPolynomial.X (lensAATForwardCoordinate input g
          (lensAATForwardCoordinate input f coordinate)) :
          LensLawCoordinateRing input Z.Carrier))
  axisReadableOn_stage : ∀ W axis,
    (lensAATGeometryCoverageRequirements input X).axisReadableOn W axis →
      ForwardAxisVisibility (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := lensAATCarrier input) (.point) atom)
        (lensAATGeometryReadingContext input X)
        (lensAATGeometryReadingContext input Y) _root_.id axis
  boundaryVisibleOn_stage : ∀ W base,
    (lensAATGeometryCoverageRequirements input X).boundaryVisibleOn W base →
      (lensAATGeometryCoverageRequirements input Y).boundaryVisibleOn
        ((f.lawContextFunctor).obj ⟨W⟩).ctx
        ((f.lawContextFunctor).obj ⟨base⟩).ctx

/-- Construct the lens semantic coverage compositor fieldwise from `f` and
`g`; no coverage record or compositor certificate is an input. -/
theorem lensAATForwardCoverageSemanticCompositor
    (input : LensFamilyInput.{u})
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    LensAATForwardCoverageSemanticCompositor input f g where
  toLensAATForwardCoverageImage := {
    requiredSupport := by
      intro atom h
      exact (lensAATForwardCoverageImage input g).requiredSupport atom
        ((lensAATForwardCoverageImage input f).requiredSupport atom h)
    requiredEquationCoordinate := by
      intro coordinate h
      have hMiddle :=
        (lensAATForwardCoverageImage input f).requiredEquationCoordinate
          coordinate h
      have hTarget :=
        (lensAATForwardCoverageImage input g).requiredEquationCoordinate
          (lensAATForwardRequiredCoordinate input f coordinate) hMiddle
      rw [LensAATForwardMorphism.forwardRequiredCoordinate_comp]
      exact hTarget
    selectedViolationWitness := by
      intro coordinate h
      have hMiddle :=
        (lensAATForwardCoverageImage input f).selectedViolationWitness
          coordinate h
      have hTarget :=
        (lensAATForwardCoverageImage input g).selectedViolationWitness
          (lensAATForwardCoordinate input f coordinate) hMiddle
      rw [LensAATForwardMorphism.forwardCoordinate_comp]
      exact hTarget
    requiredAxis := by
      intro axis h
      exact (lensAATForwardCoverageImage input g).requiredAxis axis
        ((lensAATForwardCoverageImage input f).requiredAxis axis h)
    supportVisibleOn := by
      intro W atom
      exact LensAATForwardMorphism.forwardSupportVisible_comp input f g atom
    equationCoordinateVisibleOn := by
      intro W coordinate
      exact LensAATForwardMorphism.forwardEquationCoordinateCoherent_comp
        input f g coordinate
    violationWitnessVisibleOn := by
      intro W coordinate
      exact LensAATForwardMorphism.forwardViolationCoordinateCoherent_comp
        input f g coordinate
    axisReadableOn := by
      intro W axis
      exact lensAATForwardAxisCoherent input
        (LensAATForwardMorphism.comp f g) axis
    boundaryVisibleOn := by
      intro W base
      exact LensAATForwardMorphism.forwardBoundaryVisible_comp input f g
  }
  requiredCoordinate_comp :=
    LensAATForwardMorphism.forwardRequiredCoordinate_comp f g
  violationCoordinate_comp :=
    LensAATForwardMorphism.forwardCoordinate_comp f g
  requiredSupport_stage :=
    (lensAATForwardCoverageImage input f).requiredSupport
  requiredEquationCoordinate_stage :=
    (lensAATForwardCoverageImage input f).requiredEquationCoordinate
  selectedViolationWitness_stage :=
    (lensAATForwardCoverageImage input f).selectedViolationWitness
  requiredAxis_stage :=
    (lensAATForwardCoverageImage input f).requiredAxis
  supportVisibleOn_stage :=
    (lensAATForwardCoverageImage input f).supportVisibleOn
  equationCoordinateVisibility_chain := by
    intro W coordinate hvisible
    have hFirst := lensAATForwardEquationCoordinateCoherent
      input f coordinate hvisible
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
    exact ForwardObservableVisibility.explicitChain
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
  violationWitnessVisibility_chain := by
    intro W coordinate hvisible
    have hFirst := lensAATForwardViolationCoordinateCoherent
      input f coordinate hvisible
    have hSecond :
        g.lawCoordinateMap
            (MvPolynomial.X (lensAATForwardCoordinate input f coordinate)) =
          MvPolynomial.X (lensAATForwardCoordinate input g
            (lensAATForwardCoordinate input f coordinate)) := by
      rcases coordinate with ⟨⟨index⟩, atom⟩
      exact lensLawCoordinateMap_violation input g.lawHom
        (f.lawIndexMap index) atom
    exact ForwardObservableVisibility.explicitChain
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
  axisReadableOn_stage :=
    (lensAATForwardCoverageImage input f).axisReadableOn
  boundaryVisibleOn_stage :=
    (lensAATForwardCoverageImage input f).boundaryVisibleOn

/-! ## Protocol semantic unit and compositor -/

/-- All nine canonical protocol coverage conclusions at identity, together
with the exact unchanged coordinate and visibility laws.  No negative instance
exists because the theorem below constructs this proposition for every
protocol realization from the primitive identity. -/
structure ProtocolAATForwardCoverageSemanticUnit
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) : Prop
    extends ProtocolAATForwardCoverageImage input
      (ProtocolAATForwardMorphism.id X) where
  requiredCoordinate_id : ∀ coordinate,
    protocolAATForwardRequiredCoordinate input
      (ProtocolAATForwardMorphism.id X) coordinate = coordinate
  violationCoordinate_id : ∀ coordinate,
    protocolAATForwardCoordinate input
      (ProtocolAATForwardMorphism.id X) coordinate = coordinate
  equationVisibility_id : ∀ W coordinate,
    (protocolAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
      W coordinate →
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (protocolAATGeometryReadingContext input X)
      (protocolAATGeometryReadingContext input X)
      (ProtocolAATForwardMorphism.id X).lawCoordinateMap
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        ProtocolLawCoordinateRing input X.State)
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        ProtocolLawCoordinateRing input X.State)
  violationVisibility_id : ∀ W coordinate,
    (protocolAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
      W coordinate →
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (protocolAATGeometryReadingContext input X)
      (protocolAATGeometryReadingContext input X)
      (ProtocolAATForwardMorphism.id X).lawCoordinateMap
      (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State)
      (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State)

/-- Construct the protocol semantic coverage unit from the primitive
identity. -/
theorem protocolAATForwardCoverageSemanticUnit
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    ProtocolAATForwardCoverageSemanticUnit input X where
  toProtocolAATForwardCoverageImage :=
    protocolAATForwardCoverageImage input (ProtocolAATForwardMorphism.id X)
  requiredCoordinate_id :=
    ProtocolAATForwardMorphism.forwardRequiredCoordinate_id X
  violationCoordinate_id :=
    ProtocolAATForwardMorphism.forwardCoordinate_id X
  equationVisibility_id := by
    intro W coordinate
    exact ProtocolAATForwardMorphism.forwardEquationCoordinateCoherent_id
      input X coordinate
  violationVisibility_id := by
    intro W coordinate
    exact ProtocolAATForwardMorphism.forwardViolationCoordinateCoherent_id
      input X coordinate

/-- All nine direct-composite protocol coverage conclusions, with exact
successive coordinate laws.  The constructor below builds every field from
the primitive morphisms.  No negative instance exists because it constructs
this proposition for every composable pair. -/
structure ProtocolAATForwardCoverageSemanticCompositor
    (input : ProtocolFamilyInput.{u})
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z) : Prop
    extends ProtocolAATForwardCoverageImage input
      (ProtocolAATForwardMorphism.comp f g) where
  requiredCoordinate_comp : ∀ coordinate,
    protocolAATForwardRequiredCoordinate input
      (ProtocolAATForwardMorphism.comp f g) coordinate =
    protocolAATForwardRequiredCoordinate input g
      (protocolAATForwardRequiredCoordinate input f coordinate)
  violationCoordinate_comp : ∀ coordinate,
    protocolAATForwardCoordinate input
      (ProtocolAATForwardMorphism.comp f g) coordinate =
    protocolAATForwardCoordinate input g
      (protocolAATForwardCoordinate input f coordinate)
  requiredSupport_stage : ∀ atom,
    (protocolAATGeometryCoverageRequirements input X).requiredSupport atom →
      (protocolAATGeometryCoverageRequirements input Y).requiredSupport atom
  requiredEquationCoordinate_stage : ∀ coordinate,
    (protocolAATGeometryCoverageRequirements input X).requiredEquationCoordinate
        coordinate →
      (protocolAATGeometryCoverageRequirements input Y).requiredEquationCoordinate
        (protocolAATForwardRequiredCoordinate input f coordinate)
  selectedViolationWitness_stage : ∀ coordinate,
    (protocolAATGeometryCoverageRequirements input X).selectedViolationWitness
        coordinate →
      (protocolAATGeometryCoverageRequirements input Y).selectedViolationWitness
        (protocolAATForwardCoordinate input f coordinate)
  requiredAxis_stage : ∀ axis,
    (protocolAATGeometryCoverageRequirements input X).requiredAxis axis →
      (protocolAATGeometryCoverageRequirements input Y).requiredAxis axis
  supportVisibleOn_stage : ∀ W atom,
    (protocolAATGeometryCoverageRequirements input X).supportVisibleOn W atom →
      (protocolAATGeometryCoverageRequirements input Y).supportVisibleOn
        ((f.lawContextFunctor).obj ⟨W⟩).ctx atom
  equationCoordinateVisibility_chain : ∀ W coordinate,
    (protocolAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
        W coordinate →
      Nonempty (ForwardObservableVisibilityChainData (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := protocolAATCarrier input) (.point) atom)
        (fun atom => typedRoleConfiguration_mem
          (U := protocolAATCarrier input) (.point) atom)
        (protocolAATGeometryReadingContext input X)
        (protocolAATGeometryReadingContext input Y)
        (protocolAATGeometryReadingContext input Z)
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
          ProtocolLawCoordinateRing input Z.State))
  violationWitnessVisibility_chain : ∀ W coordinate,
    (protocolAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
        W coordinate →
      Nonempty (ForwardObservableVisibilityChainData (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := protocolAATCarrier input) (.point) atom)
        (fun atom => typedRoleConfiguration_mem
          (U := protocolAATCarrier input) (.point) atom)
        (protocolAATGeometryReadingContext input X)
        (protocolAATGeometryReadingContext input Y)
        (protocolAATGeometryReadingContext input Z)
        f.lawCoordinateMap g.lawCoordinateMap
        (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State)
        (MvPolynomial.X (protocolAATForwardCoordinate input f coordinate) :
          ProtocolLawCoordinateRing input Y.State)
        (MvPolynomial.X (protocolAATForwardCoordinate input g
          (protocolAATForwardCoordinate input f coordinate)) :
          ProtocolLawCoordinateRing input Z.State))
  axisReadableOn_stage : ∀ W axis,
    (protocolAATGeometryCoverageRequirements input X).axisReadableOn W axis →
      ForwardAxisVisibility (W := W)
        (fun atom => typedRoleConfiguration_mem
          (U := protocolAATCarrier input) (.point) atom)
        (protocolAATGeometryReadingContext input X)
        (protocolAATGeometryReadingContext input Y) _root_.id axis
  boundaryVisibleOn_stage : ∀ W base,
    (protocolAATGeometryCoverageRequirements input X).boundaryVisibleOn W base →
      (protocolAATGeometryCoverageRequirements input Y).boundaryVisibleOn
        ((f.lawContextFunctor).obj ⟨W⟩).ctx
        ((f.lawContextFunctor).obj ⟨base⟩).ctx

/-- Construct the protocol semantic coverage compositor fieldwise from `f`
and `g`; no coverage record or compositor certificate is an input. -/
theorem protocolAATForwardCoverageSemanticCompositor
    (input : ProtocolFamilyInput.{u})
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z) :
    ProtocolAATForwardCoverageSemanticCompositor input f g where
  toProtocolAATForwardCoverageImage := {
    requiredSupport := by
      intro atom h
      exact (protocolAATForwardCoverageImage input g).requiredSupport atom
        ((protocolAATForwardCoverageImage input f).requiredSupport atom h)
    requiredEquationCoordinate := by
      intro coordinate h
      have hMiddle :=
        (protocolAATForwardCoverageImage input f).requiredEquationCoordinate
          coordinate h
      have hTarget :=
        (protocolAATForwardCoverageImage input g).requiredEquationCoordinate
          (protocolAATForwardRequiredCoordinate input f coordinate) hMiddle
      rw [ProtocolAATForwardMorphism.forwardRequiredCoordinate_comp]
      exact hTarget
    selectedViolationWitness := by
      intro coordinate h
      have hMiddle :=
        (protocolAATForwardCoverageImage input f).selectedViolationWitness
          coordinate h
      have hTarget :=
        (protocolAATForwardCoverageImage input g).selectedViolationWitness
          (protocolAATForwardCoordinate input f coordinate) hMiddle
      rw [ProtocolAATForwardMorphism.forwardCoordinate_comp]
      exact hTarget
    requiredAxis := by
      intro axis h
      exact (protocolAATForwardCoverageImage input g).requiredAxis axis
        ((protocolAATForwardCoverageImage input f).requiredAxis axis h)
    supportVisibleOn := by
      intro W atom
      exact ProtocolAATForwardMorphism.forwardSupportVisible_comp input f g atom
    equationCoordinateVisibleOn := by
      intro W coordinate
      exact ProtocolAATForwardMorphism.forwardEquationCoordinateCoherent_comp
        input f g coordinate
    violationWitnessVisibleOn := by
      intro W coordinate
      exact ProtocolAATForwardMorphism.forwardViolationCoordinateCoherent_comp
        input f g coordinate
    axisReadableOn := by
      intro W axis
      exact protocolAATForwardAxisCoherent input
        (ProtocolAATForwardMorphism.comp f g) axis
    boundaryVisibleOn := by
      intro W base
      exact ProtocolAATForwardMorphism.forwardBoundaryVisible_comp input f g
  }
  requiredCoordinate_comp :=
    ProtocolAATForwardMorphism.forwardRequiredCoordinate_comp f g
  violationCoordinate_comp :=
    ProtocolAATForwardMorphism.forwardCoordinate_comp f g
  requiredSupport_stage :=
    (protocolAATForwardCoverageImage input f).requiredSupport
  requiredEquationCoordinate_stage :=
    (protocolAATForwardCoverageImage input f).requiredEquationCoordinate
  selectedViolationWitness_stage :=
    (protocolAATForwardCoverageImage input f).selectedViolationWitness
  requiredAxis_stage :=
    (protocolAATForwardCoverageImage input f).requiredAxis
  supportVisibleOn_stage :=
    (protocolAATForwardCoverageImage input f).supportVisibleOn
  equationCoordinateVisibility_chain := by
    intro W coordinate hvisible
    have hFirst := protocolAATForwardEquationCoordinateCoherent
      input f coordinate hvisible
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
    exact ForwardObservableVisibility.explicitChain
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
  violationWitnessVisibility_chain := by
    intro W coordinate hvisible
    have hFirst := protocolAATForwardViolationCoordinateCoherent
      input f coordinate hvisible
    have hSecond :
        g.lawCoordinateMap
            (MvPolynomial.X (protocolAATForwardCoordinate input f coordinate)) =
          MvPolynomial.X (protocolAATForwardCoordinate input g
            (protocolAATForwardCoordinate input f coordinate)) := by
      rcases coordinate with ⟨⟨index⟩, atom⟩
      exact protocolLawCoordinateMap_violation input g.lawHom
        (f.lawIndexMap index) atom
    exact ForwardObservableVisibility.explicitChain
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
  axisReadableOn_stage :=
    (protocolAATForwardCoverageImage input f).axisReadableOn
  boundaryVisibleOn_stage :=
    (protocolAATForwardCoverageImage input f).boundaryVisibleOn

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
