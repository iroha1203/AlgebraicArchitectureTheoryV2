import ResearchLean.AG.RealizationReconstruction.CSAATGeometryRawForward
import Formal.Util.AssertStandardAxioms

/-!
# Coordinate-specific forward coverage for the concrete CS readings

For a non-surjective coordinate map there is no honest inverse from every
target observable to a source observable.  The existing coverage visibility
predicate alone also does not remember which target observable produced a
readable local value.  This file therefore uses a stronger forward witness: it
stores the source and target restrictions, equality of their selected local
values, and the equation saying that the generated coordinate map sends the
source variable to the named target variable.

The construction does not claim visibility of target-only coordinates.  It
does not adjoin target observables to the source context, and it does not yet
discharge signature-axis visibility or overlap/Extension coherence.
-/

namespace AAT.AG.RealizationReconstruction

universe u

/-! ## Generic selected-observable restriction and coherent witness -/

/-- Rebase a source context and map it to an independently constructed target
reading by reusing one selected readable source-local observable.  The target
observable argument is intentionally ignored at the carrier level; the
coordinate-specific theorem below records the exact selected value that is
used. -/
def fullFamilyContextToTargetReadingAt {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (sourceReading : Site.ArchCtx sourceObject)
    (targetReading : Site.ArchCtx targetObject)
    (supportForward : sourceReading.Support → targetReading.Support)
    (axisForward : sourceReading.Axis → targetReading.Axis)
    {W : Site.ArchCtx sourceObject}
    (g : Site.ContextMorphism W sourceReading)
    (sourceObservable : sourceReading.Observable) :
    Site.ContextMorphism
      (fullFamilyContextRebase targetObject target_all W) targetReading where
  supportMap := supportForward ∘ g.supportMap
  axisMap := axisForward ∘ g.axisMap
  observableRestrict _ := g.observableRestrict sourceObservable

/-- A selected readable source-local value makes the coordinate-specific map
an actual restriction; no reverse coordinate map is required. -/
theorem fullFamilyContextToTargetReadingAt_isRestriction
    {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (sourceReading : Site.ArchCtx sourceObject)
    (targetReading : Site.ArchCtx targetObject)
    (supportForward : sourceReading.Support → targetReading.Support)
    (axisForward : sourceReading.Axis → targetReading.Axis)
    (supportForward_reads : ∀ {support atom},
      sourceReading.minimal.supportReads support atom →
        targetReading.minimal.supportReads (supportForward support) atom)
    (axisForward_reads : ∀ {axis},
      sourceReading.minimal.axisReads axis →
        targetReading.minimal.axisReads (axisForward axis))
    {W : Site.ArchCtx sourceObject}
    (g : Site.ContextMorphism W sourceReading) (hg : g.IsRestriction)
    (sourceObservable : sourceReading.Observable)
    (hlocal : W.minimal.observableReads
      (g.observableRestrict sourceObservable)) :
    (fullFamilyContextToTargetReadingAt target_all sourceReading targetReading
      supportForward axisForward g sourceObservable).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom h
    exact supportForward_reads (hg.1 h)
  · intro axis h
    exact axisForward_reads (hg.2.1 h)
  · intro _ _
    exact hlocal
  · intro support atom _
    exact target_all atom

/-- The induced target restriction sends every target observable to the exact
selected source-local value.  Later coverage uses this only at the mapped
coordinate named in the theorem statement. -/
@[simp] theorem fullFamilyContextToTargetReadingAt_selected
    {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (sourceReading : Site.ArchCtx sourceObject)
    (targetReading : Site.ArchCtx targetObject)
    (supportForward : sourceReading.Support → targetReading.Support)
    (axisForward : sourceReading.Axis → targetReading.Axis)
    {W : Site.ArchCtx sourceObject}
    (g : Site.ContextMorphism W sourceReading)
    (sourceObservable : sourceReading.Observable)
    (targetObservable : targetReading.Observable) :
    (fullFamilyContextToTargetReadingAt target_all sourceReading targetReading
      supportForward axisForward g sourceObservable).observableRestrict
        targetObservable = g.observableRestrict sourceObservable :=
  rfl

/-- Coordinate-sensitive forward visibility.  Besides source and target
readability, it records the generated forward-observable equation and equality
of the selected local values.  Ordinary target visibility is only a projection
of this stronger witness. -/
def ForwardObservableVisibility {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (sourceReading : Site.ArchCtx sourceObject)
    (targetReading : Site.ArchCtx targetObject)
    (forwardObservable : sourceReading.Observable → targetReading.Observable)
    {W : Site.ArchCtx sourceObject}
    (sourceObservable : sourceReading.Observable)
    (targetObservable : targetReading.Observable) : Prop :=
  ∃ sourceMap : Site.ContextMorphism W sourceReading,
    sourceMap.IsRestriction ∧
    W.minimal.observableReads
      (sourceMap.observableRestrict sourceObservable) ∧
    ∃ targetMap : Site.ContextMorphism
        (fullFamilyContextRebase targetObject target_all W) targetReading,
      targetMap.IsRestriction ∧
      W.minimal.observableReads
        (targetMap.observableRestrict targetObservable) ∧
      forwardObservable sourceObservable = targetObservable ∧
      targetMap.observableRestrict targetObservable =
        sourceMap.observableRestrict sourceObservable

/-- Build the coherent witness from an actual source restriction and an exact
forward-observable equation.  The auxiliary target restriction is constant on
observables, so its only semantic use is the stored equality at the named
target observable; the forward equation rules out arbitrary target labels. -/
theorem fullFamilyForwardObservableVisibility {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (sourceReading : Site.ArchCtx sourceObject)
    (targetReading : Site.ArchCtx targetObject)
    (supportForward : sourceReading.Support → targetReading.Support)
    (axisForward : sourceReading.Axis → targetReading.Axis)
    (supportForward_reads : ∀ {support atom},
      sourceReading.minimal.supportReads support atom →
        targetReading.minimal.supportReads (supportForward support) atom)
    (axisForward_reads : ∀ {axis},
      sourceReading.minimal.axisReads axis →
        targetReading.minimal.axisReads (axisForward axis))
    (forwardObservable : sourceReading.Observable → targetReading.Observable)
    {W : Site.ArchCtx sourceObject}
    (sourceObservable : sourceReading.Observable)
    (targetObservable : targetReading.Observable)
    (hforward : forwardObservable sourceObservable = targetObservable)
    (g : Site.ContextMorphism W sourceReading) (hg : g.IsRestriction)
    (hlocal : W.minimal.observableReads
      (g.observableRestrict sourceObservable)) :
    ForwardObservableVisibility (W := W) target_all sourceReading targetReading
      forwardObservable sourceObservable targetObservable := by
  let targetMap := fullFamilyContextToTargetReadingAt target_all sourceReading
    targetReading supportForward axisForward g sourceObservable
  refine ⟨g, hg, hlocal, targetMap, ?_, hlocal, hforward, rfl⟩
  exact fullFamilyContextToTargetReadingAt_isRestriction target_all sourceReading
    targetReading supportForward axisForward supportForward_reads
    axisForward_reads g hg sourceObservable hlocal

/-! ## Mapped lens coordinates -/

/-- Map a required lens equation coordinate without adding injectivity or
surjectivity. -/
def lensAATForwardRequiredCoordinate
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).RequiredCoordinate →
      (lensLawEquationSystem input Y.Carrier
        Y.toLensData.toLawStructure).RequiredCoordinate :=
  fun coordinate =>
    (⟨ULift.up (f.lawIndexMap coordinate.1.1.down), rfl⟩, coordinate.2)

/-- Map every lens violation coordinate by the same complete Law-index map. -/
def lensAATForwardCoordinate
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).Coordinate →
      (lensLawEquationSystem input Y.Carrier
        Y.toLensData.toLawStructure).Coordinate :=
  fun coordinate =>
    (ULift.up (f.lawIndexMap coordinate.1.down), coordinate.2)

/-- Every required source lens coordinate has a coherent forward-visibility
witness at the exact coordinate selected by the generated Law map. -/
theorem lensAATForwardEquationCoordinateCoherent
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
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
      (lensAATGeometryReadingContext input Y)
      f.lawCoordinateMap
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        LensLawCoordinateRing input X.Carrier)
      (MvPolynomial.X
        (ULift.up (f.lawIndexMap coordinate.1.1.down), coordinate.2) :
        LensLawCoordinateRing input Y.Carrier) := by
  rcases hvisible with ⟨g, hg, hlocal⟩
  have hforward :
      f.lawCoordinateMap
        (MvPolynomial.X (coordinate.1.1, coordinate.2)) =
          MvPolynomial.X
            (ULift.up (f.lawIndexMap coordinate.1.1.down), coordinate.2) := by
    change lensLawCoordinateMap input f.lawHom
      (MvPolynomial.X (coordinate.1.1, coordinate.2)) =
        MvPolynomial.X
          (ULift.up (lensLawIndexMap f.lawHom coordinate.1.1.down), coordinate.2)
    exact lensLawCoordinateMap_violation input f.lawHom
      coordinate.1.1.down coordinate.2
  exact fullFamilyForwardObservableVisibility
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom)
    (lensAATGeometryReadingContext input X)
    (lensAATGeometryReadingContext input Y)
    _root_.id _root_.id (fun h => h)
    (fun {axis} _ => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point)
        (show LensAATAtom input from axis))
    f.lawCoordinateMap
    (MvPolynomial.X (coordinate.1.1, coordinate.2) :
      LensLawCoordinateRing input X.Carrier)
    (MvPolynomial.X
      (ULift.up (f.lawIndexMap coordinate.1.1.down), coordinate.2) :
      LensLawCoordinateRing input Y.Carrier)
    hforward g hg hlocal

/-- Every source lens violation coordinate has the corresponding coherent
forward-visibility witness. -/
theorem lensAATForwardViolationCoordinateCoherent
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
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
      (lensAATGeometryReadingContext input Y)
      f.lawCoordinateMap
      (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier)
      (MvPolynomial.X (lensAATForwardCoordinate input f coordinate) :
        LensLawCoordinateRing input Y.Carrier) := by
  rcases hvisible with ⟨g, hg, hlocal⟩
  have hforward :
      f.lawCoordinateMap (MvPolynomial.X coordinate) =
        MvPolynomial.X (lensAATForwardCoordinate input f coordinate) := by
    change lensLawCoordinateMap input f.lawHom (MvPolynomial.X coordinate) =
      MvPolynomial.X
        (ULift.up (lensLawIndexMap f.lawHom coordinate.1.down), coordinate.2)
    exact lensLawCoordinateMap_violation input f.lawHom
      coordinate.1.down coordinate.2
  exact fullFamilyForwardObservableVisibility
    (fun atom => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point) atom)
    (lensAATGeometryReadingContext input X)
    (lensAATGeometryReadingContext input Y)
    _root_.id _root_.id (fun h => h)
    (fun {axis} _ => typedRoleConfiguration_mem
      (U := lensAATCarrier input) (.point)
        (show LensAATAtom input from axis))
    f.lawCoordinateMap
    (MvPolynomial.X coordinate : LensLawCoordinateRing input X.Carrier)
    (MvPolynomial.X (lensAATForwardCoordinate input f coordinate) :
      LensLawCoordinateRing input Y.Carrier)
    hforward g hg hlocal

/-! ## Mapped protocol coordinates -/

/-- Map a required protocol equation coordinate by the complete relation and
observation index map. -/
def protocolAATForwardRequiredCoordinate
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    (protocolLawEquationSystem input X.State X.toLawStructure).RequiredCoordinate →
      (protocolLawEquationSystem input Y.State Y.toLawStructure).RequiredCoordinate :=
  fun coordinate =>
    (⟨ULift.up (f.lawIndexMap coordinate.1.1.down), rfl⟩, coordinate.2)

/-- Map every protocol violation coordinate by the same complete index map. -/
def protocolAATForwardCoordinate
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    (protocolLawEquationSystem input X.State X.toLawStructure).Coordinate →
      (protocolLawEquationSystem input Y.State Y.toLawStructure).Coordinate :=
  fun coordinate =>
    (ULift.up (f.lawIndexMap coordinate.1.down), coordinate.2)

/-- Every required source protocol coordinate has a coherent forward-visibility
witness at the exact coordinate selected by the generated Law map. -/
theorem protocolAATForwardEquationCoordinateCoherent
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    {W : Site.ArchCtx (protocolLawObject input X.State X.toLawStructure)}
    (coordinate : (protocolLawEquationSystem input X.State
      X.toLawStructure).RequiredCoordinate)
    (hvisible : (protocolAATGeometryCoverageRequirements input X).equationCoordinateVisibleOn
      W coordinate) :
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (protocolAATGeometryReadingContext input X)
      (protocolAATGeometryReadingContext input Y)
      f.lawCoordinateMap
      (MvPolynomial.X (coordinate.1.1, coordinate.2) :
        ProtocolLawCoordinateRing input X.State)
      (MvPolynomial.X
        (ULift.up (f.lawIndexMap coordinate.1.1.down), coordinate.2) :
        ProtocolLawCoordinateRing input Y.State) := by
  rcases hvisible with ⟨g, hg, hlocal⟩
  have hforward :
      f.lawCoordinateMap
        (MvPolynomial.X (coordinate.1.1, coordinate.2)) =
          MvPolynomial.X
            (ULift.up (f.lawIndexMap coordinate.1.1.down), coordinate.2) := by
    change protocolLawCoordinateMap input f.lawHom
      (MvPolynomial.X (coordinate.1.1, coordinate.2)) =
        MvPolynomial.X
          (ULift.up (protocolLawIndexMap f.lawHom coordinate.1.1.down), coordinate.2)
    exact protocolLawCoordinateMap_violation input f.lawHom
      coordinate.1.1.down coordinate.2
  exact fullFamilyForwardObservableVisibility
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom)
    (protocolAATGeometryReadingContext input X)
    (protocolAATGeometryReadingContext input Y)
    _root_.id _root_.id (fun h => h)
    (fun {axis} _ => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point)
        (show ProtocolAATAtom input from axis))
    f.lawCoordinateMap
    (MvPolynomial.X (coordinate.1.1, coordinate.2) :
      ProtocolLawCoordinateRing input X.State)
    (MvPolynomial.X
      (ULift.up (f.lawIndexMap coordinate.1.1.down), coordinate.2) :
      ProtocolLawCoordinateRing input Y.State)
    hforward g hg hlocal

/-- Every source protocol violation coordinate has the corresponding coherent
forward-visibility witness. -/
theorem protocolAATForwardViolationCoordinateCoherent
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    {W : Site.ArchCtx (protocolLawObject input X.State X.toLawStructure)}
    (coordinate : (protocolLawEquationSystem input X.State
      X.toLawStructure).Coordinate)
    (hvisible : (protocolAATGeometryCoverageRequirements input X).violationWitnessVisibleOn
      W coordinate) :
    ForwardObservableVisibility (W := W)
      (fun atom => typedRoleConfiguration_mem
        (U := protocolAATCarrier input) (.point) atom)
      (protocolAATGeometryReadingContext input X)
      (protocolAATGeometryReadingContext input Y)
      f.lawCoordinateMap
      (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State)
      (MvPolynomial.X (protocolAATForwardCoordinate input f coordinate) :
        ProtocolLawCoordinateRing input Y.State) := by
  rcases hvisible with ⟨g, hg, hlocal⟩
  have hforward :
      f.lawCoordinateMap (MvPolynomial.X coordinate) =
        MvPolynomial.X (protocolAATForwardCoordinate input f coordinate) := by
    change protocolLawCoordinateMap input f.lawHom (MvPolynomial.X coordinate) =
      MvPolynomial.X
        (ULift.up (protocolLawIndexMap f.lawHom coordinate.1.down), coordinate.2)
    exact protocolLawCoordinateMap_violation input f.lawHom
      coordinate.1.down coordinate.2
  exact fullFamilyForwardObservableVisibility
    (fun atom => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point) atom)
    (protocolAATGeometryReadingContext input X)
    (protocolAATGeometryReadingContext input Y)
    _root_.id _root_.id (fun h => h)
    (fun {axis} _ => typedRoleConfiguration_mem
      (U := protocolAATCarrier input) (.point)
        (show ProtocolAATAtom input from axis))
    f.lawCoordinateMap
    (MvPolynomial.X coordinate : ProtocolLawCoordinateRing input X.State)
    (MvPolynomial.X (protocolAATForwardCoordinate input f coordinate) :
      ProtocolLawCoordinateRing input Y.State)
    hforward g hg hlocal

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
