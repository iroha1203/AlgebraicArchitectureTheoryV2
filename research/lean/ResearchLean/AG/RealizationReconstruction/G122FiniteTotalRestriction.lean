import ResearchLean.AG.RealizationReconstruction.G122FiniteEquationTransportProbe
import Formal.Util.AssertStandardAxioms

/-!
# Combined finite restrictions for G-122 total geometry morphisms

Cycles 46--48 separately selected finite source points for the geometry,
outer-core, and equation-transport maps.  This module bundles only those probe
choices and defines what it means for two arbitrary complete morphisms to agree
at every selected point.  No observed target value and no completed morphism is
stored in the bundle.

Finite separation is kept as an external proposition, not a structure field.
The empty probe is proved unable to separate the two fixed, distinct
finite-axis-fold comparisons.  Conversely, a conditional positive theorem is
given only when the complete Hom type is already subsingleton.  Neither result
discharges the fixed G-123 source-generated coverage obligation.

## Implementation notes

Agreement is stated pointwise, using heterogeneous equality exactly where the
target type depends on a morphism component.  It covers the maps sampled in
Cycles 46--48, but not the unsampled unit/counit data of the context equivalence.
Consequently `Separates` is an explicit future proof obligation rather than a
finite reconstruction theorem.  The positive `Agreement` witness below is
deliberately vacuous: this cycle has no negative `Agreement` witness because
exhibiting one requires a nonempty probe that detects a difference between two
complete morphisms, and constructing such a source-generated probe is exactly
the next open obligation.  Likewise, the only positive `Separates` theorem is
conditional on an already-subsingleton Hom type; a concrete positive instance
for the required nontrivial Hom range would itself discharge the separation
obligation and is not available in this cycle.
-/

namespace AAT.AG.RealizationReconstruction

universe u v

/-- A combined selection of finite source/target probe points for one complete
generated-object Hom type.  The fields contain probe choices only. -/
structure G122FiniteTotalHomProbe (Θ : G122FamilyInput.{u, v})
    (X Y : G122GeneratedGeometryObject Θ) where
  /-- Source points for the lower and outer-core maps. -/
  core : G122FiniteCoreProbe Θ X
  /-- Source-package context and observable points for forward equation transport. -/
  equationSource : G122FiniteEquationTransportProbe Θ X
  /-- Target-package context points for inverse equation transport. -/
  equationTarget : G122FiniteEquationTransportProbe Θ Y
  /-- Source points for the four geometry maps used by `GeomReadHom.ext`. -/
  geometry : G122FiniteGeometryProbe Θ X

namespace G122FiniteTotalHomProbe

/-- The probe with no selected source or target points.  It is useful only as
the explicit negative instance for separation and carries no coverage. -/
noncomputable def empty (Θ : G122FamilyInput.{u, v})
    (X Y : G122GeneratedGeometryObject Θ) : G122FiniteTotalHomProbe Θ X Y where
  core := {
    sourceCard := 0
    sourceValue := Fin.elim0
    atomCard := 0
    atomValue := Fin.elim0
    objectCard := 0
    objectValue := Fin.elim0
    equationCard := 0
    equationValue := Fin.elim0
    operationCard := 0
    operationSource := Fin.elim0
    operationTarget := Fin.elim0
    operationValue := fun i => Fin.elim0 i
    invariantCard := 0
    invariantValue := Fin.elim0
    axisCard := 0
    axisValue := Fin.elim0
    coordinateCard := Fin.elim0
    coordinateValue := fun i => Fin.elim0 i }
  equationSource := {
    contextCard := 0
    contextValue := Fin.elim0
    arrowCard := 0
    arrowSource := Fin.elim0
    arrowTarget := Fin.elim0
    arrowValue := fun i => Fin.elim0 i
    observableCard := Fin.elim0
    observableValue := fun i => Fin.elim0 i }
  equationTarget := {
    contextCard := 0
    contextValue := Fin.elim0
    arrowCard := 0
    arrowSource := Fin.elim0
    arrowTarget := Fin.elim0
    arrowValue := fun i => Fin.elim0 i
    observableCard := Fin.elim0
    observableValue := fun i => Fin.elim0 i }
  geometry := {
    coefficientCard := 0
    coefficientValue := Fin.elim0
    contextCard := 0
    contextValue := Fin.elim0
    supportCard := Fin.elim0
    supportValue := fun i => Fin.elim0 i
    axisCard := Fin.elim0
    axisValue := fun i => Fin.elim0 i
    observableCard := Fin.elim0
    observableValue := fun i => Fin.elim0 i }

/-- Pointwise equality of every target value sampled by a combined probe.
Dependent operation, coordinate, context-arrow, observable, support, axis, and
observable outputs use heterogeneous equality. -/
structure Agreement
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteTotalHomProbe Θ X Y)
    (first second : G122GeneratedGeometryObject.Hom Θ X Y) : Prop where
  /-- Agreement of lower doctrine source images. -/
  source : ∀ i, probe.core.sourceRestriction first i =
    probe.core.sourceRestriction second i
  /-- Agreement of lower Atom images. -/
  lowerAtom : ∀ i, probe.core.lowerAtomRestriction first i =
    probe.core.lowerAtomRestriction second i
  /-- Agreement of upper Atom images. -/
  upperAtom : ∀ i, probe.core.upperAtomRestriction first i =
    probe.core.upperAtomRestriction second i
  /-- Agreement of upper object images. -/
  object : ∀ i, probe.core.objectRestriction first i =
    probe.core.objectRestriction second i
  /-- Agreement of equation-index images. -/
  equation : ∀ i, probe.core.equationRestriction first i =
    probe.core.equationRestriction second i
  /-- Agreement of endpoint-dependent operation images. -/
  operation : ∀ i, HEq (probe.core.operationRestriction first i)
    (probe.core.operationRestriction second i)
  /-- Agreement of invariant-index images. -/
  invariant : ∀ i, probe.core.invariantRestriction first i =
    probe.core.invariantRestriction second i
  /-- Agreement of signature-axis images. -/
  axis : ∀ i, probe.core.axisRestriction first i =
    probe.core.axisRestriction second i
  /-- Agreement of axis-dependent coordinate images. -/
  coordinate : ∀ i j, HEq (probe.core.coordinateRestriction first i j)
    (probe.core.coordinateRestriction second i j)
  /-- Agreement of forward context-object images. -/
  forwardContext : ∀ i,
    probe.equationSource.forwardContextRestriction first i =
      probe.equationSource.forwardContextRestriction second i
  /-- Agreement of forward context-arrow images. -/
  forwardArrow : ∀ i,
    HEq (probe.equationSource.forwardArrowRestriction first i)
      (probe.equationSource.forwardArrowRestriction second i)
  /-- Agreement of inverse context-object images. -/
  backwardContext : ∀ i,
    probe.equationTarget.backwardContextRestriction first i =
      probe.equationTarget.backwardContextRestriction second i
  /-- Agreement of inverse context-arrow images. -/
  backwardArrow : ∀ i,
    HEq (probe.equationTarget.backwardArrowRestriction first i)
      (probe.equationTarget.backwardArrowRestriction second i)
  /-- Agreement of context-dependent equation observable images. -/
  equationObservable : ∀ i j,
    HEq (probe.equationSource.observableRestriction first i j)
      (probe.equationSource.observableRestriction second i j)
  /-- Agreement of geometry coefficient images. -/
  geometryCoefficient : ∀ i,
    probe.geometry.coefficientRestriction first i =
      probe.geometry.coefficientRestriction second i
  /-- Agreement of geometry support images. -/
  geometrySupport : ∀ i j,
    HEq (probe.geometry.supportRestriction first i j)
      (probe.geometry.supportRestriction second i j)
  /-- Agreement of geometry-axis images. -/
  geometryAxis : ∀ i j,
    HEq (probe.geometry.axisRestriction first i j)
      (probe.geometry.axisRestriction second i j)
  /-- Agreement of geometry-observable images. -/
  geometryObservable : ∀ i j,
    HEq (probe.geometry.observableRestriction first i j)
      (probe.geometry.observableRestriction second i j)

/-- A combined probe separates its complete Hom type when pointwise agreement
on all selected source values forces equality of arbitrary morphisms.  This is
an external property to be discharged, never a probe field. -/
def Separates
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteTotalHomProbe Θ X Y) : Prop :=
  ∀ first second : G122GeneratedGeometryObject.Hom Θ X Y,
    Agreement probe first second → first = second

/-- Empty probes make every two complete morphisms observationally agree. -/
theorem empty_agreement
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (first second : G122GeneratedGeometryObject.Hom Θ X Y) :
    Agreement (empty Θ X Y) first second := by
  refine {
    source := ?_, lowerAtom := ?_, upperAtom := ?_, object := ?_,
    equation := ?_, operation := ?_, invariant := ?_, axis := ?_,
    coordinate := ?_, forwardContext := ?_, forwardArrow := ?_,
    backwardContext := ?_, backwardArrow := ?_, equationObservable := ?_,
    geometryCoefficient := ?_, geometrySupport := ?_, geometryAxis := ?_,
    geometryObservable := ?_ }
  all_goals simp only [empty]
  all_goals intro i
  all_goals exact Fin.elim0 i

/-- Conditional positive separation when the entire semantic Hom type is
already subsingleton.  This does not establish that hypothesis for G-123. -/
theorem separates_of_subsingleton
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteTotalHomProbe Θ X Y)
    [Subsingleton (G122GeneratedGeometryObject.Hom Θ X Y)] :
    Separates probe := by
  intro first second _
  exact Subsingleton.elim first second

/-- An empty probe cannot separate a Hom type containing two distinct
morphisms. -/
theorem empty_not_separates_of_ne
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    {first second : G122GeneratedGeometryObject.Hom Θ X Y}
    (different : first ≠ second) : ¬ Separates (empty Θ X Y) := by
  intro separates
  exact different (separates first second (empty_agreement first second))

end G122FiniteTotalHomProbe

/-- The empty combined probe on the fixed finite-axis-fold comparison Hom. -/
noncomputable def finiteAxisFoldEmptyTotalHomProbe : G122FiniteTotalHomProbe
    finiteAxisFoldG122FamilyInput
    (.direct finiteAxisFoldG122CellInput)
    (.viaBase finiteAxisFoldG122CellInput) :=
  G122FiniteTotalHomProbe.empty _ _ _

/-- The fixed empty probe fails separation because the actual generated
`barBeta` and actual five-factor `barAlpha` are distinct complete morphisms. -/
theorem finiteAxisFoldEmptyTotalHomProbe_not_separates :
    ¬ G122FiniteTotalHomProbe.Separates finiteAxisFoldEmptyTotalHomProbe :=
  G122FiniteTotalHomProbe.empty_not_separates_of_ne
    FiniteAxisFoldComparisonCode.generatedBarBeta_ne_barAlpha

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
